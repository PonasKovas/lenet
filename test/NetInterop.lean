/-
Lenet.Net against real ENet: the Lean side of the test whose ENet side is
test/c/echo.c, run by `make -C test net-interop` in two processes over real
UDP sockets.

  netinterop client <port>   connects to the ENet echo server, sends the
                             packet set, checks every reliable packet comes
                             back once, in order and intact, then disconnects
  netinterop server <port>   echoes every packet back on its channel, with
                             its delivery mode, until the peer disconnects

The packet set is described in test/c/echo.c. Exit code 0 = passed; both
give up after 10 s.
-/
import Lenet.Net

open Lenet.Net Std.Net

namespace NetInterop

def reliableCount : Nat := 31
def giveUpMs : Nat := 10000

def packetSize (i : Nat) : Nat := if i == 30 then 20000 else 1 + (i * 97) % 3000

def packet (i : Nat) (size : Nat := packetSize i) : ByteArray :=
  ⟨(Array.range size).map fun j => ((j * 31 + i) % 251).toUInt8⟩

def loopback (port : UInt16) : SocketAddress := .v4 { addr := IPv4Addr.ofParts 127 0 0 1, port }

partial def client (port : UInt16) : IO UInt32 := do
  let host ← Endpoint.bind (loopback 0)
  let server ← match ← host.connect (loopback port) 2 7 with
    | .ok p => pure p
    | .error e => IO.eprintln s!"FAIL: connect: {e}"; return 1
  let deadline := (← IO.monoMsNow) + giveUpMs
  let rec loop (back : Nat) (disconnecting : Bool) : IO UInt32 := do
    if (← IO.monoMsNow) ≥ deadline then
      IO.eprintln s!"FAIL: lenet client gave up ({back} of {reliableCount} echoes)"
      return 1
    match ← host.service 5 with
    | some (.connect conn _) =>
      IO.println "  lenet: CONNECT"
      let some ch1 := conn.channel? 1
        | IO.eprintln s!"FAIL: the connection has {conn.channelCount} channels"; return 1
      for i in [0:reliableCount] do
        let _ ← host.send conn conn.first (.reliable (packet i))
      for i in [0:5] do
        let _ ← host.send conn ch1 (.unsequenced (packet i 64))
      loop back disconnecting
    | some (.receive _ ⟨0, _⟩ pk) =>
      if back ≥ reliableCount then
        IO.eprintln "FAIL: more echoes than packets sent"; return 1
      if pk.data != packet back then
        IO.eprintln s!"FAIL: echo {back} is not packet {back} ({pk.data.size} bytes)"; return 1
      let back := back + 1
      if back == reliableCount && !disconnecting then
        host.disconnect server 9
        loop back true
      else loop back disconnecting
    | some (.receive ..) => loop back disconnecting
    | some (.disconnect _ _) =>
      if !disconnecting then
        IO.eprintln s!"FAIL: disconnected after {back} of {reliableCount} echoes"; return 1
      IO.println s!"  lenet: all {back} reliable echoes back in order; DISCONNECT"
      return 0
    | none => loop back disconnecting
  loop 0 false

partial def server (port : UInt16) : IO UInt32 := do
  let host ← Endpoint.bind (loopback port)
  let deadline := (← IO.monoMsNow) + giveUpMs
  let rec loop (echoed : Nat) : IO UInt32 := do
    if (← IO.monoMsNow) ≥ deadline then
      IO.eprintln "FAIL: lenet echo server: no disconnect within 10 s"; return 1
    match ← host.service 5 with
    | some (.connect _ data) => IO.println s!"  lenet: CONNECT data={data}"; loop echoed
    | some (.receive peer ch pk) =>
      let _ ← host.send peer ch pk
      loop (echoed + 1)
    | some (.disconnect _ data) =>
      IO.println s!"  lenet: DISCONNECT data={data} after {echoed} echoes"
      -- let the ACK of the DISCONNECT go out
      let _ ← host.serviceFor 100
      return 0
    | none => loop echoed
  loop 0

end NetInterop

def main (args : List String) : IO UInt32 := do
  match args with
  | ["client", port] => NetInterop.client port.toNat!.toUInt16
  | ["server", port] => NetInterop.server port.toNat!.toUInt16
  | _ => IO.eprintln "usage: netinterop client|server <port>"; return 2
