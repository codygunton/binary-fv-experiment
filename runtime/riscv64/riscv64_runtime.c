#include <stddef.h>
#include <stdint.h>

enum {
    SYS_read = 63,
    SYS_write = 64,
    SYS_exit = 93,
    INPUT_CAPACITY = 64 * 1024 * 1024,
    HEAP_CAPACITY = 512 * 1024 * 1024,
};

static unsigned char input_buffer[INPUT_CAPACITY];
static unsigned char heap_buffer[HEAP_CAPACITY] __attribute__((aligned(4096)));

uintptr_t ZKVM_HEAP_POS = (uintptr_t)heap_buffer;
uintptr_t ZKVM_HEAP_TOP = (uintptr_t)heap_buffer + sizeof(heap_buffer);

static long syscall3(long number, long first, long second, long third)
{
    register long a0 __asm__("a0") = first;
    register long a1 __asm__("a1") = second;
    register long a2 __asm__("a2") = third;
    register long a7 __asm__("a7") = number;
    __asm__ volatile("ecall" : "+r"(a0) : "r"(a1), "r"(a2), "r"(a7) : "memory");
    return a0;
}

void read_input(const unsigned char **buffer, size_t *size)
{
    size_t used = 0;
    while (used < sizeof(input_buffer)) {
        long got = syscall3(SYS_read, 0, (long)(input_buffer + used), sizeof(input_buffer) - used);
        if (got == 0) {
            break;
        }
        if (got < 0) {
            used = 0;
            break;
        }
        used += (size_t)got;
    }
    *buffer = input_buffer;
    *size = used;
}

void write_output(const unsigned char *buffer, size_t size)
{
    size_t written = 0;
    while (written < size) {
        long result = syscall3(SYS_write, 1, (long)(buffer + written), size - written);
        if (result <= 0) {
            break;
        }
        written += (size_t)result;
    }
}

__attribute__((noreturn)) void zkvm_exit(int code)
{
    syscall3(SYS_exit, code, 0, 0);
    __builtin_unreachable();
}

void *memcpy(void *restrict dst, const void *restrict src, size_t n)
{
    unsigned char *d = dst;
    const unsigned char *s = src;

    for (size_t i = 0; i < n; i++) {
        d[i] = s[i];
    }
    return dst;
}

void *memmove(void *dst, const void *src, size_t n)
{
    unsigned char *d = dst;
    const unsigned char *s = src;

    if (d < s) {
        for (size_t i = 0; i < n; i++) {
            d[i] = s[i];
        }
    } else if (d > s) {
        while (n != 0) {
            n--;
            d[n] = s[n];
        }
    }
    return dst;
}

void *memset(void *dst, int c, size_t n)
{
    unsigned char *d = dst;

    for (size_t i = 0; i < n; i++) {
        d[i] = (unsigned char)c;
    }
    return dst;
}

int memcmp(const void *lhs, const void *rhs, size_t n)
{
    const unsigned char *l = lhs;
    const unsigned char *r = rhs;

    for (size_t i = 0; i < n; i++) {
        if (l[i] != r[i]) {
            return (int)l[i] - (int)r[i];
        }
    }
    return 0;
}
