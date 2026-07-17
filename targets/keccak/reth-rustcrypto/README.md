# Reth RustCrypto Keccak-256

`wrapper/` pins the portable RustCrypto `Keccak256` dependency versions found in the selected Reth
lockfile and exports `reth_keccak256`. `adapter/main.c` converts a hexadecimal CLI message into that
C ABI so the linked RV64 ELF can be run and measured. `tests/` holds independent Ethereum Keccak
vectors and their QEMU checker.

The adapter is not part of the functional theorem. The proof enters `reth_keccak256` with message,
length, and output pointers and reasons about the exact linked ELF.
