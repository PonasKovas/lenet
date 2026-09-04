# Builds the Lenet C distribution: one self-contained static archive plus
# the public header ../include/lenet.h. The Lean runtime is baked into the
# archive; nothing Lean is visible to users of the API.
#
#   make           -> build/liblenet.a (merged: lenet + shim + Lean runtime)
#   make check     -> compiles check.c (public header only) and runs it
#   make clean
#
# Note: a shared liblenet.so is not possible with a stock Lean toolchain
# because libleanrt.a is built without -fPIC (TLS relocations).

TOOLCHAIN := $(patsubst %/bin/leanc,%,$(shell ls $(HOME)/.elan/toolchains/*/bin/leanc | head -1))
LEANLIB   := $(TOOLCHAIN)/lib/lean
LEANC     := $(TOOLCHAIN)/bin/leanc

LEAN_STATIC := $(abspath ../.lake/build/lib/liblenet_Lenet.a)

.PHONY: all check clean

all: build/liblenet.a

$(LEAN_STATIC):
	lake build Lenet:static

build:
	mkdir -p build

build/lenet_capi.o: lenet_capi.c ../include/lenet.h | build
	$(LEANC) -O2 -I../include -c lenet_capi.c -o $@

# Merge everything into one archive: the Lean-compiled library, this shim,
# the Lean runtime (libInit, leanrt), bundled GMP, and the bundled libc++
# (the Lean runtime is C++ and compiled against LLVM libc++). Members must
# be copied via `ar p` because Lean module paths flatten to colliding
# basenames, which makes plain `ar x` silently drop archive members.
build/liblenet.a: $(LEAN_STATIC) build/lenet_capi.o merge-ar.sh
	./merge-ar.sh $@ $(LEAN_STATIC) build/lenet_capi.o \
	    $(LEANLIB)/libInit.a $(LEANLIB)/libleanrt.a \
	    $(TOOLCHAIN)/lib/libgmp.a $(TOOLCHAIN)/lib/libc++.a $(TOOLCHAIN)/lib/libc++abi.a \
	    $(TOOLCHAIN)/lib/libuv.a $(TOOLCHAIN)/lib/libssl.a $(TOOLCHAIN)/lib/libcrypto.a \
	    $(TOOLCHAIN)/lib/libunwind.a

# Smoke check: a program that includes only the public header links and runs.
check: build/liblenet.a
	$(CC) -O1 -I../include check.c -Lbuild -llenet \
	    -lpthread -ldl -lm -o build/check
	./build/check

clean:
	rm -rf build