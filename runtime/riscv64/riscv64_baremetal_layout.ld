SECTIONS
{
  .binary_fv_io_context (NOLOAD) : { KEEP(*(.binary_fv_io_context)) }
}
INSERT AFTER .bss;

ASSERT(_start == 0x10120, "_start moved")
ASSERT(read_input == 0x10140, "read_input moved")
ASSERT(write_output == 0x10190, "write_output moved")
ASSERT(zkvm_exit == 0x101c4, "zkvm_exit moved")
ASSERT(memcpy == 0x101d4, "memcpy moved")
ASSERT(main == 0x14cb0, "main moved")
ASSERT(ZKVM_HEAP_TOP == 0x19000, "ZKVM_HEAP_TOP moved")
ASSERT(ZKVM_HEAP_POS == 0x19008, "ZKVM_HEAP_POS moved")
ASSERT(input_buffer == 0x2001a000, "input_buffer moved")
ASSERT(binary_fv_io_context == 0x2401a0b8, "I/O context is not trailing")
