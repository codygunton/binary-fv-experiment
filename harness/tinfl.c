#include <stdint.h>
#include <stddef.h>

#include "miniz_tinfl.h"

volatile uint8_t tinfl_sink;

int main(int argc, char **argv)
{
    static const uint8_t raw_deflate_hello[] = {
        0x01, 0x05, 0x00, 0xfa, 0xff, 0x68, 0x65, 0x6c, 0x6c, 0x6f
    };
    uint8_t out[16];

    (void)argc;
    (void)argv;

    size_t n = tinfl_decompress_mem_to_mem(
        out,
        sizeof(out),
        raw_deflate_hello,
        sizeof(raw_deflate_hello),
        TINFL_FLAG_USING_NON_WRAPPING_OUTPUT_BUF);
    tinfl_sink = (n == 5) ? out[0] : 0xff;
    return n == 5 ? 0 : 1;
}
