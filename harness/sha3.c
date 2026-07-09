#include <stdint.h>
#include <stddef.h>
#include <stdio.h>
#include <string.h>

#include "sha3.h"

static void print_hex(const uint8_t *bytes, size_t len)
{
    static const char hex[] = "0123456789abcdef";

    for (size_t i = 0; i < len; i++) {
        putchar(hex[bytes[i] >> 4]);
        putchar(hex[bytes[i] & 0x0f]);
    }
    putchar('\n');
}

int main(int argc, char **argv)
{
    uint8_t out[32];

    if (argc != 2) {
        fprintf(stderr, "usage: %s MESSAGE\n", argv[0]);
        return 2;
    }

    sha3(argv[1], strlen(argv[1]), out, sizeof(out));
    print_hex(out, sizeof(out));
    return 0;
}
