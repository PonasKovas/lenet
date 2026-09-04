# lenet

A Lean 4, sans-I/O reimplementation of the [ENet](https://github.com/lsalzman/enet)
protocol (1.3.x wire-compatible), with a plain C API.

- **Wire compatible** with ENet 1.3.x — validated against the real C library
  (golden-trace replay + live UDP interop, see `test/README.md`).
- **Sans-I/O core** — the protocol engine opens no sockets and reads no
  clocks; the driver supplies time and datagrams. Works for sync or async
  runtimes (e.g. Rust/Tokio).
- **Clean C distribution** — builds to a single self-contained
  `liblenet.a`; nothing Lean is visible to consumers.
- **Correctness over compatibility** — where ENet is buggy, lenet implements
  the correct behavior instead of mirroring the bug (see `DESIGN.md`).
- **Not implemented**: ENet's optional compression (order-2 PPM range coder)
  is explicitly descoped; compressed datagrams are rejected. See `DESIGN.md`
  and `TODO.md` for the roadmap (code quality, formal proofs, performance,
  and async Rust bindings are the planned next phases).

## Building the C library

Requires: [Lean 4](https://lean-lang.org/) (via elan) and a C compiler.

```sh
lake build Lenet:static   # compile the Lean core
make -C csrc              # -> csrc/build/liblenet.a (self-contained)
```

This produces `csrc/build/liblenet.a` with the Lean runtime baked in.
Consumers need only the header and one archive:

```sh
cc myapp.c -Ipath/to/lenet/include -Lpath/to/csrc/build -llenet \
    -lpthread -ldl -lm
```

Smoke-check the build (compiles a public-header-only program and runs it):

```sh
make -C csrc check
```

See `include/lenet.h` for the API and `csrc/check.c` for a minimal example.
A shared library is not currently possible: Lean's runtime archive is built
without `-fPIC`.

## Testing

```sh
lake build replay && ./.lake/build/bin/replay test/traces   # golden-trace replay
make -C csrc check                       # C API smoke test
make -C test interop                     # live interop vs real ENet (needs ../enet)
```

Details, including how the compatibility tests obtain real ENet, are in
`test/README.md`. CI runs all three layers (`.github/workflows/`).
