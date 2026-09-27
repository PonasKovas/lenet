# lenet

A Lean 4 implementation of the [ENet](https://github.com/lsalzman/enet)
protocol, wire compatible with ENet 1.3.x, with a plain C API.

- **Sans-I/O.** The protocol engine opens no sockets and reads no clocks.
  The driver owns the UDP socket and the time, feeds datagrams in and sends
  what comes out. That works the same for a C loop, a thread, or an async
  runtime such as Tokio.
- **Checked against real ENet.** Golden traces recorded from the C library
  are replayed through Lenet and diffed, and a live test runs Lenet against
  ENet over real UDP sockets.
- **Partly proven.** Codec roundtrip, fragment reassembly, reliable
  delivery across sequence wrap, timer scheduling, resource bounds and a
  build-time no-panic audit are machine-checked Lean proofs.
- **Correct before compatible.** Where ENet has a bug, Lenet does the right
  thing instead of copying it; every such divergence is written down.
- **One static library.** The C build is a single `liblenet.a` with the Lean
  runtime inside; users see only `lenet.h`.

ENet's optional packet compression is not implemented: compressed
datagrams are dropped. See [DESIGN.md](DESIGN.md) for why.

## Building

Needs [Lean 4](https://lean-lang.org/) (through elan) and a C compiler.

```sh
lake build                 # the library and the proofs
make -C csrc               # -> csrc/build/liblenet.a
make -C csrc check         # a C program using only lenet.h links and runs
```

Link your program with the header and the archive:

```sh
cc app.c -Ipath/to/csrc/include -Lpath/to/csrc/build -llenet -lpthread -ldl -lm
```

A shared library is not possible yet: the Lean runtime archive is built
without `-fPIC`.

## Using it from C

```c
lenet_host *host = lenet_host_create(0, 0, 32, 2, 0, 0, 0);
for (;;) {
    /* for every datagram your socket receives: */
    lenet_host_handle_datagram(host, now_ms(), ip, port, buf, len);

    lenet_host_service(host, now_ms());          /* timers + packing */

    lenet_datagram out;
    while (lenet_host_poll_outgoing(host, &out) == 1)
        sendto(sock, out.data, out.len, ...);    /* to out.ip:out.port */

    lenet_event ev;
    while (lenet_host_poll_event(host, &ev, payload, sizeof payload, &plen) == 1)
        handle(&ev);

    /* sleep until the next datagram or lenet_host_next_deadline() */
}
```

The full API, with the rules a driver has to follow, is documented in
[csrc/include/lenet.h](csrc/include/lenet.h). Async Rust bindings live in a
separate repository (`lenet-rs`).

## Using it from Lean

`Lenet.Net` (library `LenetNet`) runs a host over a UDP socket, the way
ENet's own API does. Connections are `PeerHandle`s, which stop working
when their connection ends, so a reused peer slot is never mistaken for the
old connection. Once a connection is up, `service` reports it as a
`Connection`, whose channels are `Fin`s of the count both sides agreed on,
so a send cannot name a channel the connection does not have.

```lean
import Lenet.Net
open Lenet.Net Std.Net

/-- An echo server on port 7777. -/
def serve : IO Unit := do
  let host ← Endpoint.bind (.v4 ⟨.ofParts 0 0 0 0, 7777⟩)
  repeat
    match ← host.service 1000 with
    | some (.connect peer data) => IO.println s!"{peer} connected, data {data}"
    | some (.receive peer channel packet) => discard <| host.send peer channel packet
    | some (.disconnect peer _) => IO.println s!"{peer} left"
    | none => pure ()

/-- Sends one packet and waits for the echo. -/
def ask (text : String) : IO Unit := do
  let host ← Endpoint.bind (.v4 ⟨.ofParts 0 0 0 0, 0⟩)
  let .ok server ← host.connect (.v4 ⟨.ofParts 127 0 0 1, 7777⟩) | throw (.userError "no free slot")
  repeat
    match ← host.service 1000 with
    | some (.connect conn _) => discard <| host.send conn conn.first (.reliable text.toUTF8)
    | some (.receive _ _ packet) =>
      IO.println (String.fromUTF8! packet.data)
      host.disconnect server
    | some (.disconnect _ _) => return
    | none => pure ()
```

`service timeout` returns the next event, waiting up to `timeout`
milliseconds; `service 0` only checks, for a program with its own loop.
The pure engine (`Lenet.Host`) is there too, for a driver of your own.

## Testing

```sh
lake build replay && ./.lake/build/bin/replay test/traces   # golden-trace replay
lake build unit && ./.lake/build/bin/unit                   # unit tests
lake build net && ./.lake/build/bin/net                     # Lenet.Net over UDP on 127.0.0.1
make -C csrc check                                          # C API smoke test
make -C test interop                                        # live interop (needs ENet in ../enet)
make -C test net-interop                                    # Lenet.Net against ENet, two processes
lake build bench && ./.lake/build/bin/bench                 # benchmark
```

CI runs all of it except the benchmark, which it only builds. How the ENet
comparison works is explained in [test/README.md](test/README.md).

## Layout

| path                  | what                                                     |
|-----------------------|----------------------------------------------------------|
| `Lenet/`              | the protocol engine (pure Lean); `Lenet/Host.lean` is the entry point |
| `Lenet/Protocol/`     | the wire format: header, commands, datagrams             |
| `Lenet/Proofs/`       | the proofs (library `LenetProofs`, never linked into C)  |
| `Lenet/FFI.lean`      | the exports the C shim wraps                             |
| `Lenet/Net.lean`      | the engine over a UDP socket, for Lean programs (library `LenetNet`) |
| `csrc/`               | the C distribution: `include/lenet.h`, the shim, the build |
| `test/`               | ENet comparison: trace recorder, replayer, live interop  |
| `bench/`              | throughput and service-cost benchmark                    |

## Documents

- [DESIGN.md](DESIGN.md): principles, architecture, code rules, what is
  proven, and the scope decisions.
- [test/README.md](test/README.md): the test setup, every scenario, and the
  record of where Lenet differs from ENet and why.
- [TODO.md](TODO.md): open work.
