import ZesuExec.Service.Basic

/-!
# CSR `0x805`: ZisK SHA-256 compression (`SYSCALL_SHA256F_ID`, `definitions/src/syscall.rs:10`)

`csrs 0x805, rp` becomes the `sha256` precompile (`core/src/riscv2zisk_context.rs:1349-1385`:
`b = rp`, continue 4 bytes later, nothing stored). `opc_sha256` (`core/src/zisk_ops.rs:1351-1377`)
reads the parameter block at `rp` (`SyscallSha256Params`, `ziskos/entrypoint/src/syscalls/sha256f.rs`:
a pointer to the state `[u64; 4]` and a pointer to the block `[u64; 8]`), applies
`sha2::compress256` to the state viewed as eight `u32` (`core/src/helpers.rs:9-14`, little-endian
memory) and the 64-byte block, and writes the new state back over the old.
`precompiled_load_data` requires `rp` 8-aligned (`zisk_ops.rs:1588-1593`); the pointers are
required 8-aligned here as well.

`sha256Compress` is the compression function of FIPS 180-4 §6.2.2.
-/

namespace ZesuExec
open Machine

namespace Sha256

abbrev W32 := BitVec 32

def K : List W32 :=
  [0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
   0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
   0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
   0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
   0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
   0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
   0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
   0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

def rotr (x : W32) (n : Nat) : W32 := x.rotateRight n

def bsig0 (x : W32) : W32 := rotr x 2 ^^^ rotr x 13 ^^^ rotr x 22
def bsig1 (x : W32) : W32 := rotr x 6 ^^^ rotr x 11 ^^^ rotr x 25
def ssig0 (x : W32) : W32 := rotr x 7 ^^^ rotr x 18 ^^^ (x >>> 3)
def ssig1 (x : W32) : W32 := rotr x 17 ^^^ rotr x 19 ^^^ (x >>> 10)

/-- Big-endian word `i` of a block. -/
def beWord (blk : List Byte) (i : Nat) : W32 :=
  (blk.getD (4 * i) 0 ++ blk.getD (4 * i + 1) 0) ++ (blk.getD (4 * i + 2) 0 ++ blk.getD (4 * i + 3) 0)

/-- Message schedule `W₀ … W₆₃`. -/
def schedule (blk : List Byte) : List W32 :=
  (List.range 48).foldl (fun w t =>
    let j := t + 16
    w ++ [ssig1 (w.getD (j - 2) 0) + w.getD (j - 7) 0 + ssig0 (w.getD (j - 15) 0) +
      w.getD (j - 16) 0]) ((List.range 16).map (beWord blk))

/-- One compression of the 64-byte block `blk` into the eight-word state `H`. -/
def sha256Compress (H : List W32) (blk : List Byte) : List W32 :=
  let w := schedule blk
  let r := (List.range 64).foldl (fun (s : List W32) t =>
    let a := s.getD 0 0; let b := s.getD 1 0; let c := s.getD 2 0; let d := s.getD 3 0
    let e := s.getD 4 0; let f := s.getD 5 0; let g := s.getD 6 0; let h := s.getD 7 0
    let t1 := h + bsig1 e + ((e &&& f) ^^^ (~~~e &&& g)) + K.getD t 0 + w.getD t 0
    let t2 := bsig0 a + ((a &&& b) ^^^ (a &&& c) ^^^ (b &&& c))
    [t1 + t2, a, b, c, d + t1, e, f, g]) H
  (List.range 8).map fun i => H.getD i 0 + r.getD i 0

/-- Little-endian bytes of the state words. -/
def leBytes (H : List W32) : List Byte :=
  H.flatMap fun x => (List.range 4).map fun j => x.extractLsb' (8 * j) 8

/-- Little-endian `u32` word `i` of the state bytes. -/
def leWord (st : List Byte) (i : Nat) : W32 :=
  (st.getD (4 * i + 3) 0 ++ st.getD (4 * i + 2) 0) ++ (st.getD (4 * i + 1) 0 ++ st.getD (4 * i) 0)

/-- Initial hash value (FIPS 180-4 §5.3.3). -/
def H0 : List W32 :=
  [0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]

/-- Padded message (FIPS 180-4 §5.1.1): `0x80`, zeros, the bit length big-endian. -/
def pad (msg : List Byte) : List Byte :=
  let k := (119 - msg.length % 64) % 64
  msg ++ [0x80] ++ List.replicate k 0 ++
    (List.range 8).reverse.map fun j => BitVec.ofNat 8 ((8 * msg.length) / 256 ^ j)

/-- SHA-256 of `msg`: the eight words of the final state, big-endian. -/
def hash (msg : List Byte) : List Byte :=
  let p := pad msg
  let H := (List.range (p.length / 64)).foldl
    (fun H i => sha256Compress H ((p.drop (64 * i)).take 64)) H0
  H.flatMap fun x => (List.range 4).reverse.map fun j => x.extractLsb' (8 * j) 8

end Sha256

/-- The CSR `0x805` service step at `m.pc`. -/
def csr805 (img : Image) (m : Machine) : Option SvcEffect :=
  match Svc.fetch img m.pc.toNat with
  | some w0 =>
    if Svc.isCsrs w0 0x805 then
      let p := (m.reg (Decode.reg w0 15)).toNat
      if p % 8 = 0 ∧ srcOk m.mem p 16 then
        match readBytes m.mem p 8, readBytes m.mem (p + 8) 8 with
        | some sp, some ip =>
          let st := (ofBytesLE sp).toNat
          let inp := (ofBytesLE ip).toNat
          if st % 8 = 0 ∧ inp % 8 = 0 ∧ dstOk m.mem st 32 ∧ srcOk m.mem inp 64 then
            match readBytes m.mem st 32, readBytes m.mem inp 64 with
            | some sb, some blk =>
              let out := Sha256.leBytes
                (Sha256.sha256Compress ((List.range 8).map (Sha256.leWord sb)) blk)
              some { addrs := (List.range 32).map (st + ·), mem := putBytes m.mem st 32 out,
                     pc := m.pc + 4, cost := 1 }
            | _, _ => none
          else none
        | _, _ => none
      else none
    else none
  | none => none

end ZesuExec
