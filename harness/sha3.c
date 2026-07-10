#include <stdint.h>
#include <stddef.h>

#include "sha3.h"

static long sys_write(int fd, const void *buf, size_t len)
{
    register long a0 asm("a0") = fd;
    register long a1 asm("a1") = (long)buf;
    register long a2 asm("a2") = (long)len;
    register long a7 asm("a7") = 64;

    asm volatile("ecall" : "+r"(a0) : "r"(a1), "r"(a2), "r"(a7) : "memory");
    return a0;
}

static void write_all(int fd, const void *buf, size_t len)
{
    const uint8_t *p = buf;

    while (len != 0) {
        long n = sys_write(fd, p, len);
        if (n <= 0) {
            return;
        }
        p += (size_t)n;
        len -= (size_t)n;
    }
}

static size_t cstr_len(const char *s)
{
    size_t len = 0;

    while (s[len] != '\0') {
        len++;
    }
    return len;
}

static void print_hex(const uint8_t *bytes, size_t len)
{
    static const char hex[] = "0123456789abcdef";
    char line[65];

    for (size_t i = 0; i < len; i++) {
        line[i * 2] = hex[bytes[i] >> 4];
        line[i * 2 + 1] = hex[bytes[i] & 0x0f];
    }
    line[len * 2] = '\n';
    write_all(1, line, len * 2 + 1);
}

int main(int argc, char **argv)
{
    uint8_t out[32];

    if (argc != 2) {
        static const char usage[] = "usage: sha3 MESSAGE\n";
        write_all(2, usage, sizeof(usage) - 1);
        return 2;
    }

    sha3(argv[1], cstr_len(argv[1]), out, sizeof(out));
    print_hex(out, sizeof(out));
    return 0;
}
