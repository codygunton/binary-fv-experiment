#include <stddef.h>
#include <stdint.h>

int32_t zesu_decode_raw(const uint8_t *input, size_t input_len);
uint64_t zesu_raw_sink_checksum(void);

#define INPUT_CAPACITY (2U * 1024U * 1024U)
#define HEAP_CAPACITY (64U * 1024U * 1024U)

static uint8_t input[INPUT_CAPACITY];
static uint8_t heap[HEAP_CAPACITY] __attribute__((aligned(16)));

uintptr_t ZKVM_HEAP_POS;
uintptr_t ZKVM_HEAP_TOP;

static long sys_read(int fd, void *buf, size_t len)
{
    register long a0 asm("a0") = fd;
    register long a1 asm("a1") = (long)buf;
    register long a2 asm("a2") = (long)len;
    register long a7 asm("a7") = 63;

    asm volatile("ecall" : "+r"(a0) : "r"(a1), "r"(a2), "r"(a7) : "memory");
    return a0;
}

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

static int read_all(size_t *out_len)
{
    size_t len = 0;

    while (len < sizeof(input)) {
        long n = sys_read(0, input + len, sizeof(input) - len);
        if (n == 0) {
            *out_len = len;
            return 0;
        }
        if (n < 0) {
            return -1;
        }
        len += (size_t)n;
    }
    return -1;
}

static void write_checksum(uint64_t checksum)
{
    static const char digits[] = "0123456789abcdef";
    char rendered[16];
    size_t index;

    for (index = 0; index < sizeof(rendered); ++index) {
        unsigned int shift = (unsigned int)((sizeof(rendered) - 1U - index) * 4U);
        rendered[index] = digits[(checksum >> shift) & 0x0fU];
    }
    write_all(1, rendered, sizeof(rendered));
}

int main(void)
{
    size_t input_len;

    if (read_all(&input_len) != 0) {
        static const char too_large[] = "input-too-large\n";
        write_all(2, too_large, sizeof(too_large) - 1);
        return 2;
    }
    ZKVM_HEAP_POS = (uintptr_t)heap;
    ZKVM_HEAP_TOP = (uintptr_t)(heap + sizeof(heap));
    if (zesu_decode_raw(input, input_len) == 0) {
        static const char invalid[] = "invalid\n";
        write_all(1, invalid, sizeof(invalid) - 1);
        return 1;
    }
    {
        static const char ok[] = "ok ";
        static const char newline[] = "\n";
        write_all(1, ok, sizeof(ok) - 1);
        write_checksum(zesu_raw_sink_checksum());
        write_all(1, newline, sizeof(newline) - 1);
    }
    return 0;
}
