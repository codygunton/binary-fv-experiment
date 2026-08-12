    .file 1 "runtime/riscv64/riscv64_baremetal_start.S"
    .section .text.start,"ax",@progbits
    .globl _start
    .type _start, @function
_start:
    .option push
    .option norelax
    la gp, __global_pointer$
    .option pop
    call main
1:
    j 1b
    .fill 4, 4, 0x00000013
    .size _start, . - _start
