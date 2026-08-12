    .section .binary_fv_io_context,"aw",@nobits
    .balign 8
    .globl binary_fv_io_context
    .type binary_fv_io_context, @object
binary_fv_io_context:
    .zero 32
    .size binary_fv_io_context, . - binary_fv_io_context
