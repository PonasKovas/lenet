// The C API from C++, in a program that brings its own copies of names the
// Lean runtime bundles (mimalloc, libuv): liblenet.a exports only lenet_*,
// so they do not clash, and the program's exceptions still work.
#include <lenet.h>
#include <stdexcept>
#include <cstdio>
#include <string>
extern "C" void *mi_malloc(size_t n) { (void)n; return nullptr; }   // an app's own copies
extern "C" int uv_loop_init(void *l) { (void)l; return 42; }
int main() {
    lenet_host *h = lenet_host_create(0, 0, 4, 2, 0, 0, 0);
    if (!h) { std::puts("create failed"); return 1; }
    try { throw std::runtime_error("app exception"); }
    catch (const std::exception &e) { if (std::string(e.what()) != "app exception") return 1; }
    int32_t p = lenet_host_connect(h, 0x0100007F, 40000, 2, 0);
    lenet_host_service(h, 0);
    lenet_datagram d; int n = 0;
    while (lenet_host_poll_outgoing(h, &d) == 1) n++;
    lenet_host_destroy(h);
    std::printf("cpp ok peer=%d datagrams=%d uv=%d\n", p, n, uv_loop_init(nullptr));
    return n == 1 ? 0 : 1;
}
