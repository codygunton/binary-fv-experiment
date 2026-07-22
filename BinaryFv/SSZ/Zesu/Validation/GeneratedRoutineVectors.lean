-- GENERATED FILE: produced by targets/ssz/zesu/tests/ssz_routine_vectors.py --out-lean. DO NOT EDIT.
-- Typed per-routine leaf vectors baked for the handwritten-meaning agreement check
-- (BinaryFv/SSZ/Zesu/Validation/RoutineMeaningVectors.lean). `some`=expected value, `none`=invalidSsz.
namespace BinaryFv.SSZ.Zesu.Validation.GeneratedRoutineVectors
def scalarVectors : List (String × String × String × Nat × Option Nat) :=
  [("ssz_raw.readU32", "ssz_raw.readU32/endian-pattern/0", "1122334455667788", 0, some 1144201745),
   ("ssz_raw.readU32", "ssz_raw.readU32/endian-pattern/1", "1122334455667788", 4, some 2289526357),
   ("ssz_raw.readU32", "ssz_raw.readU32/boundary-length/2", "00000000", 0, some 0),
   ("ssz_raw.readU32", "ssz_raw.readU32/boundary-length/3", "ffffffff", 0, some 4294967295),
   ("ssz_raw.readU32", "ssz_raw.readU32/offset-failure/4", "010203", 0, none),
   ("ssz_raw.readU32", "ssz_raw.readU32/offset-failure/5", "1122334455667788", 5, none),
   ("ssz_raw.readOffset", "ssz_raw.readOffset/endian-pattern/6", "1122334455667788", 0, some 1144201745),
   ("ssz_raw.readOffset", "ssz_raw.readOffset/endian-pattern/7", "1122334455667788", 4, some 2289526357),
   ("ssz_raw.readOffset", "ssz_raw.readOffset/boundary-length/8", "00000000", 0, some 0),
   ("ssz_raw.readOffset", "ssz_raw.readOffset/boundary-length/9", "ffffffff", 0, some 4294967295),
   ("ssz_raw.readOffset", "ssz_raw.readOffset/offset-failure/10", "010203", 0, none),
   ("ssz_raw.readOffset", "ssz_raw.readOffset/offset-failure/11", "1122334455667788", 5, none),
   ("ssz_raw.readU64", "ssz_raw.readU64/endian-pattern/12", "1122334455667788", 0, some 9833440827789222417),
   ("ssz_raw.readU64", "ssz_raw.readU64/boundary-length/13", "0000000000000000", 0, some 0),
   ("ssz_raw.readU64", "ssz_raw.readU64/boundary-length/14", "ffffffffffffffff", 0, some 18446744073709551615),
   ("ssz_raw.readU64", "ssz_raw.readU64/offset-failure/15", "01010101010101", 0, none),
   ("ssz_raw.readU64", "ssz_raw.readU64/offset-failure/16", "1122334455667788", 1, none),
   ("ssz_raw.readU256", "ssz_raw.readU256/endian-pattern/17", "030a11181f262d343b424950575e656c737a81888f969da4abb2b9c0c7ced5dc", 0, some 99886592258189578621981811027948186316239496345248383831838435367256765565443),
   ("ssz_raw.readU256", "ssz_raw.readU256/endian-pattern/18", "5859030a11181f262d343b424950575e656c737a81888f969da4abb2b9c0c7ced5dc", 2, some 99886592258189578621981811027948186316239496345248383831838435367256765565443),
   ("ssz_raw.readU256", "ssz_raw.readU256/boundary-length/19", "0000000000000000000000000000000000000000000000000000000000000000", 0, some 0),
   ("ssz_raw.readU256", "ssz_raw.readU256/boundary-length/20", "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff", 0, some 115792089237316195423570985008687907853269984665640564039457584007913129639935),
   ("ssz_raw.readU256", "ssz_raw.readU256/offset-failure/21", "00000000000000000000000000000000000000000000000000000000000000", 0, none),
   ("ssz_raw.readU256", "ssz_raw.readU256/offset-failure/22", "111111111111111111111111111111111111111111111111111111111111111111", 2, none)]

def sliceVectors : List (String × String × String × Nat × Nat × Option String) :=
  [("ssz_raw.readArray[20]", "ssz_raw.readArray[20]/boundary-length/23", "030a11181f262d343b424950575e656c737a8188", 0, 20, some "030a11181f262d343b424950575e656c737a8188"),
   ("ssz_raw.readArray[20]", "ssz_raw.readArray[20]/boundary-length/24", "030a11181f262d343b424950575e656c737a81885859", 2, 20, some "11181f262d343b424950575e656c737a81885859"),
   ("ssz_raw.readArray[20]", "ssz_raw.readArray[20]/offset-failure/25", "030a11181f262d343b424950575e656c737a81", 0, 20, none),
   ("ssz_raw.readArray[32]", "ssz_raw.readArray[32]/boundary-length/26", "030a11181f262d343b424950575e656c737a81888f969da4abb2b9c0c7ced5dc", 0, 32, some "030a11181f262d343b424950575e656c737a81888f969da4abb2b9c0c7ced5dc"),
   ("ssz_raw.readArray[32]", "ssz_raw.readArray[32]/boundary-length/27", "030a11181f262d343b424950575e656c737a81888f969da4abb2b9c0c7ced5dc5859", 2, 32, some "11181f262d343b424950575e656c737a81888f969da4abb2b9c0c7ced5dc5859"),
   ("ssz_raw.readArray[32]", "ssz_raw.readArray[32]/offset-failure/28", "030a11181f262d343b424950575e656c737a81888f969da4abb2b9c0c7ced5", 0, 32, none),
   ("ssz_raw.readArray[48]", "ssz_raw.readArray[48]/boundary-length/29", "030a11181f262d343b424950575e656c737a81888f969da4abb2b9c0c7ced5dce3eaf1f8ff060d141b222930373e454c", 0, 48, some "030a11181f262d343b424950575e656c737a81888f969da4abb2b9c0c7ced5dce3eaf1f8ff060d141b222930373e454c"),
   ("ssz_raw.readArray[48]", "ssz_raw.readArray[48]/boundary-length/30", "030a11181f262d343b424950575e656c737a81888f969da4abb2b9c0c7ced5dce3eaf1f8ff060d141b222930373e454c5859", 2, 48, some "11181f262d343b424950575e656c737a81888f969da4abb2b9c0c7ced5dce3eaf1f8ff060d141b222930373e454c5859"),
   ("ssz_raw.readArray[48]", "ssz_raw.readArray[48]/offset-failure/31", "030a11181f262d343b424950575e656c737a81888f969da4abb2b9c0c7ced5dce3eaf1f8ff060d141b222930373e45", 0, 48, none),
   ("ssz_raw.readArray[65]", "ssz_raw.readArray[65]/boundary-length/32", "030a11181f262d343b424950575e656c737a81888f969da4abb2b9c0c7ced5dce3eaf1f8ff060d141b222930373e454c535a61686f767d848b9299a0a7aeb5bcc3", 0, 65, some "030a11181f262d343b424950575e656c737a81888f969da4abb2b9c0c7ced5dce3eaf1f8ff060d141b222930373e454c535a61686f767d848b9299a0a7aeb5bcc3"),
   ("ssz_raw.readArray[65]", "ssz_raw.readArray[65]/boundary-length/33", "030a11181f262d343b424950575e656c737a81888f969da4abb2b9c0c7ced5dce3eaf1f8ff060d141b222930373e454c535a61686f767d848b9299a0a7aeb5bcc35859", 2, 65, some "11181f262d343b424950575e656c737a81888f969da4abb2b9c0c7ced5dce3eaf1f8ff060d141b222930373e454c535a61686f767d848b9299a0a7aeb5bcc35859"),
   ("ssz_raw.readArray[65]", "ssz_raw.readArray[65]/offset-failure/34", "030a11181f262d343b424950575e656c737a81888f969da4abb2b9c0c7ced5dce3eaf1f8ff060d141b222930373e454c535a61686f767d848b9299a0a7aeb5bc", 0, 65, none),
   ("ssz_raw.readArray[96]", "ssz_raw.readArray[96]/boundary-length/35", "030a11181f262d343b424950575e656c737a81888f969da4abb2b9c0c7ced5dce3eaf1f8ff060d141b222930373e454c535a61686f767d848b9299a0a7aeb5bcc3cad1d8dfe6edf4fb020910171e252c333a41484f565d646b727980878e959c", 0, 96, some "030a11181f262d343b424950575e656c737a81888f969da4abb2b9c0c7ced5dce3eaf1f8ff060d141b222930373e454c535a61686f767d848b9299a0a7aeb5bcc3cad1d8dfe6edf4fb020910171e252c333a41484f565d646b727980878e959c"),
   ("ssz_raw.readArray[96]", "ssz_raw.readArray[96]/boundary-length/36", "030a11181f262d343b424950575e656c737a81888f969da4abb2b9c0c7ced5dce3eaf1f8ff060d141b222930373e454c535a61686f767d848b9299a0a7aeb5bcc3cad1d8dfe6edf4fb020910171e252c333a41484f565d646b727980878e959c5859", 2, 96, some "11181f262d343b424950575e656c737a81888f969da4abb2b9c0c7ced5dce3eaf1f8ff060d141b222930373e454c535a61686f767d848b9299a0a7aeb5bcc3cad1d8dfe6edf4fb020910171e252c333a41484f565d646b727980878e959c5859"),
   ("ssz_raw.readArray[96]", "ssz_raw.readArray[96]/offset-failure/37", "030a11181f262d343b424950575e656c737a81888f969da4abb2b9c0c7ced5dce3eaf1f8ff060d141b222930373e454c535a61686f767d848b9299a0a7aeb5bcc3cad1d8dfe6edf4fb020910171e252c333a41484f565d646b727980878e95", 0, 96, none),
   ("ssz_raw.readArray[256]", "ssz_raw.readArray[256]/boundary-length/38", "030a11181f262d343b424950575e656c737a81888f969da4abb2b9c0c7ced5dce3eaf1f8ff060d141b222930373e454c535a61686f767d848b9299a0a7aeb5bcc3cad1d8dfe6edf4fb020910171e252c333a41484f565d646b727980878e959ca3aab1b8bfc6cdd4dbe2e9f0f7fe050c131a21282f363d444b525960676e757c838a91989fa6adb4bbc2c9d0d7dee5ecf3fa01080f161d242b323940474e555c636a71787f868d949ba2a9b0b7bec5ccd3dae1e8eff6fd040b121920272e353c434a51585f666d747b828990979ea5acb3bac1c8cfd6dde4ebf2f900070e151c232a31383f464d545b626970777e858c939aa1a8afb6bdc4cbd2d9e0e7eef5fc", 0, 256, some "030a11181f262d343b424950575e656c737a81888f969da4abb2b9c0c7ced5dce3eaf1f8ff060d141b222930373e454c535a61686f767d848b9299a0a7aeb5bcc3cad1d8dfe6edf4fb020910171e252c333a41484f565d646b727980878e959ca3aab1b8bfc6cdd4dbe2e9f0f7fe050c131a21282f363d444b525960676e757c838a91989fa6adb4bbc2c9d0d7dee5ecf3fa01080f161d242b323940474e555c636a71787f868d949ba2a9b0b7bec5ccd3dae1e8eff6fd040b121920272e353c434a51585f666d747b828990979ea5acb3bac1c8cfd6dde4ebf2f900070e151c232a31383f464d545b626970777e858c939aa1a8afb6bdc4cbd2d9e0e7eef5fc"),
   ("ssz_raw.readArray[256]", "ssz_raw.readArray[256]/boundary-length/39", "030a11181f262d343b424950575e656c737a81888f969da4abb2b9c0c7ced5dce3eaf1f8ff060d141b222930373e454c535a61686f767d848b9299a0a7aeb5bcc3cad1d8dfe6edf4fb020910171e252c333a41484f565d646b727980878e959ca3aab1b8bfc6cdd4dbe2e9f0f7fe050c131a21282f363d444b525960676e757c838a91989fa6adb4bbc2c9d0d7dee5ecf3fa01080f161d242b323940474e555c636a71787f868d949ba2a9b0b7bec5ccd3dae1e8eff6fd040b121920272e353c434a51585f666d747b828990979ea5acb3bac1c8cfd6dde4ebf2f900070e151c232a31383f464d545b626970777e858c939aa1a8afb6bdc4cbd2d9e0e7eef5fc5859", 2, 256, some "11181f262d343b424950575e656c737a81888f969da4abb2b9c0c7ced5dce3eaf1f8ff060d141b222930373e454c535a61686f767d848b9299a0a7aeb5bcc3cad1d8dfe6edf4fb020910171e252c333a41484f565d646b727980878e959ca3aab1b8bfc6cdd4dbe2e9f0f7fe050c131a21282f363d444b525960676e757c838a91989fa6adb4bbc2c9d0d7dee5ecf3fa01080f161d242b323940474e555c636a71787f868d949ba2a9b0b7bec5ccd3dae1e8eff6fd040b121920272e353c434a51585f666d747b828990979ea5acb3bac1c8cfd6dde4ebf2f900070e151c232a31383f464d545b626970777e858c939aa1a8afb6bdc4cbd2d9e0e7eef5fc5859"),
   ("ssz_raw.readArray[256]", "ssz_raw.readArray[256]/offset-failure/40", "030a11181f262d343b424950575e656c737a81888f969da4abb2b9c0c7ced5dce3eaf1f8ff060d141b222930373e454c535a61686f767d848b9299a0a7aeb5bcc3cad1d8dfe6edf4fb020910171e252c333a41484f565d646b727980878e959ca3aab1b8bfc6cdd4dbe2e9f0f7fe050c131a21282f363d444b525960676e757c838a91989fa6adb4bbc2c9d0d7dee5ecf3fa01080f161d242b323940474e555c636a71787f868d949ba2a9b0b7bec5ccd3dae1e8eff6fd040b121920272e353c434a51585f666d747b828990979ea5acb3bac1c8cfd6dde4ebf2f900070e151c232a31383f464d545b626970777e858c939aa1a8afb6bdc4cbd2d9e0e7eef5", 0, 256, none),
   ("ssz_raw.bytesAt", "ssz_raw.bytesAt/boundary-length/41", "0102030405060708", 0, 8, some "0102030405060708"),
   ("ssz_raw.bytesAt", "ssz_raw.bytesAt/boundary-length/42", "0102030405060708", 2, 4, some "03040506"),
   ("ssz_raw.bytesAt", "ssz_raw.bytesAt/boundary-length/43", "0102030405060708", 0, 0, some ""),
   ("ssz_raw.bytesAt", "ssz_raw.bytesAt/boundary-length/44", "0102030405060708", 8, 0, some ""),
   ("ssz_raw.bytesAt", "ssz_raw.bytesAt/offset-failure/45", "0102030405060708", 4, 5, none),
   ("ssz_raw.bytesAt", "ssz_raw.bytesAt/offset-failure/46", "0102030405060708", 9, 0, none),
   ("ssz_raw.bytesAt", "ssz_raw.bytesAt/boundary-length/47", "", 0, 0, some "")]

def requireU32Vectors : List (String × String × Bool) :=
  [("ssz_raw.requireU32Length/boundary-length/48", "", true),
   ("ssz_raw.requireU32Length/boundary-length/49", "00", true),
   ("ssz_raw.requireU32Length/boundary-length/50", "00000000", true),
   ("ssz_raw.requireU32Length/boundary-length/51", "00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000", true)]

def canonicalOffsetsVectors : List (String × String × Nat × List Nat × Bool) :=
  [("ssz_raw.requireCanonicalOffsets/offset-canonical/57", "00000000000000000000000000000000", 8, [8], true),
   ("ssz_raw.requireCanonicalOffsets/offset-canonical/58", "00000000000000000000000000000000", 8, [8, 12, 16], true),
   ("ssz_raw.requireCanonicalOffsets/offset-canonical/59", "00000000000000000000000000000000", 8, [8, 8], true),
   ("ssz_raw.requireCanonicalOffsets/offset-wrong-first/60", "00000000000000000000000000000000", 8, [12], false),
   ("ssz_raw.requireCanonicalOffsets/offset-descending/61", "00000000000000000000000000000000", 8, [8, 12, 10], false),
   ("ssz_raw.requireCanonicalOffsets/offset-out-of-range/62", "00000000000000000000000000000000", 8, [8, 20], false),
   ("ssz_raw.requireCanonicalOffsets/offset-short-slice/63", "00000000", 8, [8], false),
   ("ssz_raw.requireCanonicalOffsets/offset-empty-table/64", "00000000000000000000000000000000", 8, [], false)]

def erePrefixVectors : List (String × String × Bool) :=
  [("ssz_raw.hasExactErePrefix/raw-ere/53", "", false),
   ("ssz_raw.hasExactErePrefix/raw-ere/54", "010203", false),
   ("ssz_raw.hasExactErePrefix/raw-ere/55", "0400000041424344", true),
   ("ssz_raw.hasExactErePrefix/raw-ere/56", "0700000041424344", false)]

def optionalU64Vectors : List (String × String × Option (Option Nat)) :=
  [("ssz_raw.decodeOptionalU64/option-absent/65", "", some none),
   ("ssz_raw.decodeOptionalU64/option-present/66", "1122334455667788", some (some 9833440827789222417)),
   ("ssz_raw.decodeOptionalU64/option-present/67", "0000000000000000", some (some 0)),
   ("ssz_raw.decodeOptionalU64/option-present/68", "ffffffffffffffff", some (some 18446744073709551615)),
   ("ssz_raw.decodeOptionalU64/option-malformed/69", "11111111111111", none),
   ("ssz_raw.decodeOptionalU64/option-malformed/70", "111111111111111111", none)]

def optionalBlobVectors : List (String × String × Option (Option (Nat × Nat × Nat))) :=
  [("ssz_raw.decodeOptionalBlobSchedule/option-absent/71", "", some none),
   ("ssz_raw.decodeOptionalBlobSchedule/option-present/72", "01060b10151a1f24292e33383d42474c51565b60656a6f74", some (some (2602827787409229313, 5496434700932296233, 8390041614455363153))),
   ("ssz_raw.decodeOptionalBlobSchedule/option-present/73", "000000000000000000000000000000000000000000000000", some (some (0, 0, 0))),
   ("ssz_raw.decodeOptionalBlobSchedule/option-present/74", "ffffffffffffffffffffffffffffffffffffffffffffffff", some (some (18446744073709551615, 18446744073709551615, 18446744073709551615))),
   ("ssz_raw.decodeOptionalBlobSchedule/option-malformed/75", "2222222222222222222222222222222222222222222222", none),
   ("ssz_raw.decodeOptionalBlobSchedule/option-malformed/76", "22222222222222222222222222222222222222222222222222", none),
   ("ssz_raw.decodeOptionalBlobSchedule/option-malformed/77", "22222222222222222222222222222222", none)]

end BinaryFv.SSZ.Zesu.Validation.GeneratedRoutineVectors
