    .file 1 "runtime/riscv64/riscv64_baremetal_host.S"
    .section .text.read_input,"ax",@progbits
    .globl read_input
    .type read_input, @function
read_input:
    lla t0, input_buffer
    sd t0, 0(a0)
    lla t0, binary_fv_io_context
    ld t1, 0(t0)
    sd t1, 0(a1)
    ret
    .fill 12, 4, 0x00000013
    .size read_input, . - read_input

    .section .text.write_output,"ax",@progbits
    .globl write_output
    .type write_output, @function
write_output:
    lla t0, binary_fv_io_context
    sd a0, 8(t0)
    sd a1, 16(t0)
    ret
    .fill 8, 4, 0x00000013
    .size write_output, . - write_output

    .section .text.zkvm_exit,"ax",@progbits
    .globl zkvm_exit
    .type zkvm_exit, @function
zkvm_exit:
    lla t0, binary_fv_io_context
    sd a0, 24(t0)
1:
    j 1b
    .size zkvm_exit, . - zkvm_exit
