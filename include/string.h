#ifndef SHA_FV_STRING_H
#define SHA_FV_STRING_H

#include <stddef.h>

void *memcpy(void *restrict dst, const void *restrict src, size_t n);
void *memmove(void *dst, const void *src, size_t n);
void *memset(void *dst, int c, size_t n);
int memcmp(const void *lhs, const void *rhs, size_t n);

#endif
