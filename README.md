# lenet

A Lean 4 implementation of the [ENet](https://github.com/lsalzman/enet)
protocol: reliable, ordered and unreliable packets over UDP. It speaks ENet
1.3.x on the wire, so Lenet and ENet hosts talk to each other.

## Features

- **Everything ENet's protocol does except compression.** Reliable,
  unreliable and unsequenced packets, fragmentation of large packets, up to
  255 channels, checksums, bandwidth limits and throttling, pings,
  timeouts and graceful disconnects. Compressed datagrams are dropped.
- **Sans-I/O engine.** The core is pure: you feed it datagrams and the
  time, and it hands back datagrams to send and events. It fits a plain C
  loop, a thread or an async runtime alike.
- **C API.** One static library, `liblenet.a`, with the Lean runtime
  inside and only the `lenet_*` functions exported. See
  [`csrc/include/lenet.h`](csrc/include/lenet.h).
- **Lean API.** `Lenet.Net` runs a host over a UDP socket with ENet's
  calls (`connect`, `send`, `service`, ...), with typed peer and channel
  handles. See [`Lenet/Net.lean`](Lenet/Net.lean).
- **Safe against hostile peers.** Every wire value is checked, and the
  memory a peer can make a host hold is bounded.
- **Proven in part.** Lean proofs cover the wire codec, fragment
  reassembly, reliable in-order delivery over a lossy network, timers,
  memory bounds and peer events. A build-time check rejects any code that
  could panic.
- **Tested against real ENet.** Recorded ENet traffic is replayed through
  Lenet, and live tests run Lenet against ENet over UDP, over lossy links
  too.

Where ENet has a bug, Lenet does not copy it. [DIFFERENCES.md](DIFFERENCES.md)
lists every place Lenet behaves differently from ENet.

The C library builds on Linux only.

## Building

Needs [Lean 4](https://lean-lang.org/) (through elan) and a C compiler.

```sh
lake build           # the library and the proofs
make -C csrc         # csrc/build/liblenet.a
```

Link a C program with:

```sh
cc app.c -Icsrc/include -Lcsrc/build -llenet -lpthread -ldl -lm
```

## Testing

```sh
lake build unit && ./.lake/build/bin/unit                   # unit tests
lake build replay && ./.lake/build/bin/replay test/traces   # replay of recorded ENet traffic
lake build net && ./.lake/build/bin/net                     # Lenet.Net over UDP on 127.0.0.1
make -C csrc check                                          # C API
make -C test interop net-interop lossy-interop              # against ENet (needs ENet in ../enet)
lake build bench && ./.lake/build/bin/bench                 # benchmark
```

See [test/README.md](test/README.md) for how the ENet tests work.
