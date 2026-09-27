# Builds the ENet compatibility test programs against the real ENet sources
# (out-of-tree; the ENet checkout is never modified).
#
#   make               -> builds c/harness (the trace recorder)
#   make c/interop     -> builds the live interop runner
#   make interop       -> runs every interop scenario
#   make net-interop   -> Lenet.Net (Lean, own process) against ENet, both ways
#   make lossy-interop -> the same through a lossy proxy, every profile, both
#                         ways (ROUNDS, PER, SEEDS, PROFILES to run longer;
#                         PORT and PORT+1 are used)
#   make lossy-enet    -> ENet against ENet through the same proxy: when a
#                         lossy-interop run fails, does ENet fail alone too?
#   make traces        -> records all scenario traces into traces/, once
#                         with ENet's clock at 0 and once per CLOCK_OFFSETS
#   make record SCENARIO=connect
#   make clean

ENET_DIR ?= ../../enet
BUILD    := .build
HARNESS  := c/harness
HARNESS_SRC := c/harness.c

ENET_SRCS := callbacks.c compress.c host.c list.c packet.c peer.c protocol.c unix.c win32.c
ENET_OBJS := $(addprefix $(BUILD)/enet-,$(ENET_SRCS:.c=.o))
ENET_LIB  := $(BUILD)/libenet.a

CFLAGS := -O1 -g -Wall -DHAS_FCNTL=1 -DHAS_POLL=1 -DHAS_GETADDRINFO=1 \
          -DHAS_GETNAMEINFO=1 -DHAS_INET_PTON=1 -DHAS_INET_NTOP=1 \
          -DHAS_SOCKLEN_T=1 -DHAS_MSGHDR_FLAGS=1 -I$(ENET_DIR)/include

SCENARIOS := connect send_c2s send_s2c frag fragthen disc_client disc_server idle timeout checksum bandwidth unfrag disclater multip inject multichannel dup reconnect retimeout mtu576 throttleconf
# ENet clock start times (ms) for the extra recordings: just before the
# 16-bit sent-time wrap and just before the 32-bit clock wrap. Must match
# Replay.clockOffsets.
CLOCK_OFFSETS := 65203 4294966963
INTEROP_SCENARIOS := connect connect_r send frag disconnect disconnect_r timeout checksum bandwidth disclater multip unfrag

.PHONY: all traces record interop net-interop lossy-interop lossy-enet clean FORCE

all: $(HARNESS)

$(BUILD):
	mkdir -p $(BUILD)

$(BUILD)/enet-%.o: $(ENET_DIR)/%.c | $(BUILD)
	$(CC) $(CFLAGS) -c $< -o $@

$(ENET_LIB): $(ENET_OBJS)
	ar rcs $@ $^

$(HARNESS): $(HARNESS_SRC) $(ENET_LIB)
	$(CC) $(CFLAGS) $(HARNESS_SRC) $(ENET_LIB) -o $@ -lm

c/interop: c/interop.c $(ENET_LIB) ../csrc/build/liblenet.a
	$(CC) $(CFLAGS) -I../csrc/include c/interop.c $(ENET_LIB) ../csrc/build/liblenet.a \
	    -o $@ -lpthread -ldl -lm

# Delegate to csrc's Makefile every time; it knows when the archive is stale.
../csrc/build/liblenet.a: FORCE
	$(MAKE) -C ../csrc

traces: $(HARNESS)
	@mkdir -p traces
	@for s in $(SCENARIOS); do ./$(HARNESS) record $$s; \
	  for o in $(CLOCK_OFFSETS); do ./$(HARNESS) record $$s $$o; done; done

record: $(HARNESS)
	@mkdir -p traces
	./$(HARNESS) record $(SCENARIO)

interop: c/interop
	@for s in $(INTEROP_SCENARIOS); do ./c/interop $$s || exit 1; done

c/echo: c/echo.c $(ENET_LIB)
	$(CC) $(CFLAGS) c/echo.c $(ENET_LIB) -o $@ -lm

NETINTEROP := ../.lake/build/bin/netinterop

# Two processes each way: the ENet echo peer and the Lean program. The
# server starts first; a CONNECT sent before it binds is retransmitted.
net-interop: c/echo FORCE
	cd .. && lake build netinterop
	@echo "net-interop: lenet client, enet server"
	@./c/echo server 40020 & s=$$!; sleep 0.2; \
	  $(NETINTEROP) client 40020; c=$$?; wait $$s; e=$$?; \
	  test $$c -eq 0 -a $$e -eq 0 || { echo "FAIL net-interop (lenet client)"; exit 1; }
	@echo "net-interop: enet client, lenet server"
	@$(NETINTEROP) server 40021 & s=$$!; sleep 0.2; \
	  ./c/echo client 40021; c=$$?; wait $$s; e=$$?; \
	  test $$c -eq 0 -a $$e -eq 0 || { echo "FAIL net-interop (lenet server)"; exit 1; }
	@echo "PASS net-interop"

c/stream: c/stream.c $(ENET_LIB)
	$(CC) $(CFLAGS) c/stream.c $(ENET_LIB) -o $@ -lm

c/proxy: c/proxy.c
	$(CC) -O1 -g -Wall c/proxy.c -o $@

NETSTREAM := ../.lake/build/bin/netstream
ROUNDS   ?= 200
PER      ?= 2
SEEDS    ?= 1
PROFILES ?= light heavy burst
PORT     ?= 40030

# Server, proxy in front of it, client through the proxy; each side checks
# the other's stream (c/stream.c). A failure prints the seed that replays it.
# The heavy profile needs longer timeouts than ENet's defaults (c/proxy.c).
# $(1) = label, $(2) = server command, $(3) = client command
define lossy_run
	@for p in $(PROFILES); do for seed in $(SEEDS); do \
	  echo "lossy-interop: $(1), $$p, seed $$seed"; \
	  t=; test $$p = heavy && t=long; \
	  $(2) server $(PORT) $(ROUNDS) $(PER) $$t & s=$$!; \
	  ./c/proxy $$(($(PORT) + 1)) $(PORT) $$seed $$p & x=$$!; sleep 0.2; \
	  $(3) client $$(($(PORT) + 1)) $(ROUNDS) $(PER) $$t; c=$$?; wait $$s; e=$$?; \
	  kill $$x; wait $$x; \
	  test $$c -eq 0 -a $$e -eq 0 || { echo "FAIL lossy-interop ($(1), $$p, seed $$seed)"; exit 1; }; \
	done; done
endef

lossy-interop: c/stream c/proxy FORCE
	cd .. && lake build netstream
	$(call lossy_run,lenet client enet server,./c/stream,$(NETSTREAM))
	$(call lossy_run,enet client lenet server,$(NETSTREAM),./c/stream)
	@echo "PASS lossy-interop"

lossy-enet: c/stream c/proxy FORCE
	$(call lossy_run,enet client enet server,./c/stream,./c/stream)
	@echo "PASS lossy-enet"

clean:
	rm -rf $(BUILD) $(HARNESS) c/interop c/echo c/stream c/proxy
