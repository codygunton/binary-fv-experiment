    .file 1 "runtime/riscv64/riscv64_start.S"
    .section .text.start
    .globl _start
    .type _start, @function
_start:
    .loc 1 8 1
    .option push
    .option norelax
    la gp, __global_pointer$
    .option pop

    ld a0, 0(sp)
    addi a1, sp, 8
    call main

    li a7, 93
    ecall
1:
    j 1b
    .size _start, . - _start
