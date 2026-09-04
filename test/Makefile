# Builds the ENet compatibility recorder harness against the real enet
# sources (out-of-tree; ../enet is never modified).
#
#   make               -> builds c/harness
#   make traces        -> records all scenario traces into traces/
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

SCENARIOS := connect send_c2s send_s2c frag disc_client disc_server idle timeout

.PHONY: all traces record clean

all: $(HARNESS)

$(BUILD):
	mkdir -p $(BUILD)

$(BUILD)/enet-%.o: $(ENET_DIR)/%.c | $(BUILD)
	$(CC) $(CFLAGS) -c $< -o $@

$(ENET_LIB): $(ENET_OBJS)
	ar rcs $@ $^

$(HARNESS): $(HARNESS_SRC) $(ENET_LIB)
	$(CC) $(CFLAGS) $(HARNESS_SRC) $(ENET_LIB) -o $@ -lm

traces: $(HARNESS)
	@mkdir -p traces
	@for s in $(SCENARIOS); do ./$(HARNESS) record $$s; done

record: $(HARNESS)
	@mkdir -p traces
	./$(HARNESS) record $(SCENARIO)

clean:
	rm -rf $(BUILD) $(HARNESS)
