#include <stdint.h>
#include <stddef.h>

#include "sha3.h"

volatile uint8_t sha3_sink;

int main(void)
{
    static const uint8_t input[] = {
        0x66, 0x6f, 0x72, 0x6d, 0x61, 0x6c, 0x2d, 0x62,
        0x69, 0x6e, 0x61, 0x72, 0x79, 0x2d, 0x70, 0x72,
        0x6f, 0x62, 0x65
    };
    uint8_t out[32];

    sha3(input, sizeof(input), out, sizeof(out));
    sha3_sink = out[0];
    return 0;
}
