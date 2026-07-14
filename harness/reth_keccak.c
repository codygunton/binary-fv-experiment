#include <stddef.h>
#include <stdint.h>

int reth_keccak256(const uint8_t *input, size_t len, uint8_t *out);

#define INPUT_CAPACITY 4096

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

static int hex_digit(char c)
{
    if (c >= '0' && c <= '9') {
        return c - '0';
    }
    if (c >= 'a' && c <= 'f') {
        return c - 'a' + 10;
    }
    if (c >= 'A' && c <= 'F') {
        return c - 'A' + 10;
    }
    return -1;
}

static int decode_hex(const char *text, uint8_t *out, size_t *out_len)
{
    size_t len = 0;

    while (text[len] != '\0') {
        len++;
    }
    if (len % 2 != 0 || len / 2 > INPUT_CAPACITY) {
        return -1;
    }
    for (size_t i = 0; i < len; i += 2) {
        int high = hex_digit(text[i]);
        int low = hex_digit(text[i + 1]);

        if (high < 0 || low < 0) {
            return -1;
        }
        out[i / 2] = (uint8_t)((high << 4) | low);
    }
    *out_len = len / 2;
    return 0;
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
    uint8_t message[INPUT_CAPACITY];
    uint8_t digest[32];
    size_t length;

    if (argc != 2 || decode_hex(argv[1], message, &length) != 0) {
        static const char usage[] = "usage: reth-keccak HEX\n";
        write_all(2, usage, sizeof(usage) - 1);
        return 2;
    }
    if (reth_keccak256(message, length, digest) != 0) {
        return 1;
    }
    print_hex(digest, sizeof(digest));
    return 0;
}
