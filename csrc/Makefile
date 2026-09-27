# Builds the Lenet C distribution: one self-contained static archive plus
# the public header include/lenet.h. The Lean runtime is baked into the
# archive; nothing Lean is visible to users of the API.
#
#   make           -> build/liblenet.a (lenet + shim + Lean runtime, one
#                     object exporting only lenet_*)
#   make check     -> compiles check.c (public header only) and runs it
#   make clean
#
# Note: a shared liblenet.so is not possible with a stock Lean toolchain
# because libleanrt.a is built without -fPIC (TLS relocations).

# The toolchain lean-toolchain names (elan resolves it from the repo root),
# so the shim and the runtime match what lake builds the library with.
TOOLCHAIN := $(shell cd .. && lean --print-prefix)
ifeq ($(TOOLCHAIN),)
$(error no Lean toolchain: `lean --print-prefix` failed in the repo root)
endif
LEAN_INC  := $(TOOLCHAIN)/include
LEANLIB   := $(TOOLCHAIN)/lib/lean

LEAN_STATIC := $(abspath ../.lake/build/lib/liblenet_Lenet.a)

.PHONY: all check clean FORCE

all: build/liblenet.a

# Always ask lake: it rebuilds the Lean archive only when a source changed,
# and a stale archive would silently ship old code.
$(LEAN_STATIC): FORCE
	lake -d .. build Lenet:static

build:
	mkdir -p build

build/lenet_capi.o: lenet_capi.c include/lenet.h | build
	$(CC) -O2 -Iinclude -I$(LEAN_INC) -c lenet_capi.c -o $@

# Merge everything into one archive: the Lean-compiled library, this shim,
# the Lean runtime (libInit, libStd for the hash maps, leanrt), bundled GMP, and the bundled libc++
# (the Lean runtime is C++ and compiled against LLVM libc++). Members must
# be copied via `ar p` because Lean module paths flatten to colliding
# basenames, which makes plain `ar x` silently drop archive members.
build/merged.a: $(LEAN_STATIC) build/lenet_capi.o merge-ar.sh
	./merge-ar.sh $@ $(LEAN_STATIC) build/lenet_capi.o \
	    $(LEANLIB)/libInit.a $(LEANLIB)/libStd.a $(LEANLIB)/libleanrt.a \
	    $(TOOLCHAIN)/lib/libgmp.a $(TOOLCHAIN)/lib/libc++.a $(TOOLCHAIN)/lib/libc++abi.a \
	    $(TOOLCHAIN)/lib/libuv.a $(TOOLCHAIN)/lib/libssl.a $(TOOLCHAIN)/lib/libcrypto.a \
	    $(TOOLCHAIN)/lib/libunwind.a

# The distribution: one object holding what the API reaches (section GC from
# the lenet_* entry points), every symbol but lenet_* made local, so the
# bundled runtime (mimalloc, libuv, GMP, libc++, ...) cannot clash with an
# application's own copies.
build/api.syms: include/lenet.h | build
	grep -oE '\blenet_[a-z_]+\(' include/lenet.h | tr -d '(' | sort -u > $@

build/liblenet.a: build/merged.a build/api.syms
	ld -r --gc-sections $$(sed 's/^/-u /' build/api.syms) \
	    --whole-archive build/merged.a -o build/lenet_all.o
	objcopy --keep-global-symbols=build/api.syms build/lenet_all.o build/lenet.o
	rm -f $@ build/lenet_all.o
	ar rcs $@ build/lenet.o

# Smoke checks: programs that include only the public header link and run,
# one of them C++ with its own copies of bundled names.
check: build/liblenet.a
	$(CC) -O1 -Iinclude check.c -Lbuild -llenet \
	    -lpthread -ldl -lm -o build/check
	./build/check
	$(CXX) -O1 -Iinclude check_cxx.cc -Lbuild -llenet \
	    -lpthread -ldl -lm -o build/check_cxx
	./build/check_cxx

clean:
	rm -rf build