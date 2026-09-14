OUTPUT_ARCH(riscv)
ENTRY(_start)
MEMORY {
  ROM (rx) : ORIGIN = 0x80000000, LENGTH = 128M
  STACK (rw) : ORIGIN = 0xA0000000, LENGTH = 4M
  RAM (rw) : ORIGIN = 0xA0430000, LENGTH = 0x1FBC0000
}
PHDRS {
  text PT_LOAD FLAGS(5);
  rodata PT_LOAD FLAGS(4);
  data PT_LOAD FLAGS(6);
  stack PT_LOAD FLAGS(6);
}
SECTIONS {
  .text ORIGIN(ROM) : SUBALIGN(4) {
    KEEP(*(.text.start))
    *(.text .text.*)
  } > ROM :text
  .rodata ALIGN(4096) : { *(.rodata .rodata.*) } > ROM :rodata
  .eh_frame ALIGN(8) : { *(.eh_frame .eh_frame.*) } > ROM :rodata
  .stack ORIGIN(STACK) (NOLOAD) : { . += LENGTH(STACK); } > STACK :stack
  .sdata ORIGIN(RAM) : {
    __global_pointer$ = . + 0x800;
    *(.sdata .sdata.*)
  } > RAM :data
  .data ALIGN(8) : { *(.data .data.*) } > RAM :data
  .bss ALIGN(4096) (NOLOAD) : {
    *(.sbss .sbss.*) *(.bss .bss.*) *(COMMON)
  } > RAM :data
  .binary_fv_io_context ALIGN(8) (NOLOAD) : {
    KEEP(*(.binary_fv_io_context))
  } > RAM :data
  _end = .;
  _stack_top = ORIGIN(STACK) + LENGTH(STACK);
  /DISCARD/ : { *(.comment) *(.note.GNU-stack) }
}
ASSERT(_start == 0x80000000, "_start moved")
ASSERT((_end <= 0xBFFF0000), "RAM exceeds the ZisK heap bound")
ASSERT(read_input == 0x80000028, "read_input moved")
ASSERT(write_output == 0x80000078, "write_output moved")
ASSERT(zkvm_exit == 0x800000ac, "zkvm_exit moved")
ASSERT(memcpy == 0x800000bc, "memcpy moved")
ASSERT(main == 0x80004b98, "main moved")
ASSERT(ZKVM_HEAP_TOP == 0xa0430000, "ZKVM_HEAP_TOP moved")
ASSERT(ZKVM_HEAP_POS == 0xa0430008, "ZKVM_HEAP_POS moved")
ASSERT(input_buffer == 0xb8431000, "input_buffer moved")
ASSERT(binary_fv_io_context == 0xbc4310b8, "binary_fv_io_context moved")
