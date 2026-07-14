# Amsterdam `SszStatelessInput` field contract

This is the semantic contract for the corrected Zesu raw-SSZ candidate. The authoritative source is
`ethereum/execution-specs@bd8c673552d957dbe9c9f3f2656b87201f5ae646`,
`src/ethereum/forks/amsterdam/stateless_ssz.py`. It covers V4/Amsterdam only. Zesu's V3 input
support remains executable compatibility only until a matching independently pinned reference is
audited; it is excluded from the strict three-way conformance gate.

## Top-level schema and bounds

`SszStatelessInput` has schema prefix `0x0001` (big-endian) and four variable fields in this
order: `new_payload_request`, `witness`, `chain_config`, and `public_keys`. Its fixed section is
16 bytes, so the first offset must be 16; every container and variable list below uses canonical,
nondecreasing, in-range offsets relative to its own byte slice.

All SSZ integers and `uint32` offsets below are little-endian. In each variable container, the
first offset equals that container's fixed-section size, later offsets are nondecreasing and at
most the container length, and equal offsets encode empty fields. `decodeRaw` consumes the full raw
V4 input. Its framing wrapper retries as ERE only after `InvalidSsz` and only when the leading
little-endian four-byte length exactly equals the remaining byte count; `UnknownFork` is not
reinterpreted as ERE.

| Path | SSZ form | Bound / fixed size | Raw candidate representation |
|---|---|---:|---|
| `new_payload_request` | variable container | fixed section 44 B | `RawNewPayloadRequest` |
| `witness` | variable container | fixed section 12 B | `RawExecutionWitness` |
| `chain_config` | variable container | fixed section 12 B | `RawChainConfig` |
| `public_keys` | `List[ByteVector[65]]` | at most `2^15` | `[][65]u8` |
| `execution_payload.extra_data` | `ByteList` | at most 32 B | byte slice |
| `execution_payload.transactions` | `List[ByteList]` | at most `2^20` items, `2^30` B/item | byte-slice list |
| `execution_payload.withdrawals` | fixed-record list | at most 16, 44 B/item | `[]RawWithdrawal` |
| `execution_payload.block_access_list` | `ByteList` | at most `2^30` B | byte slice |
| `versioned_hashes` | `List[Bytes32]` | at most 4096 | `[][32]u8` |
| `requests.deposits` | fixed-record list | at most `2^13`, 192 B/item | `[]RawDepositRequest` |
| `requests.withdrawals` | fixed-record list | at most 16, 76 B/item | `[]RawWithdrawalRequest` |
| `requests.consolidations` | fixed-record list | at most 2, 116 B/item | `[]RawConsolidationRequest` |
| `witness.state` | `List[ByteList]` | at most `2^22` items, `2^10` B/item | byte-slice list |
| `witness.codes` | `List[ByteList]` | at most `2^18` items, `2^16` B/item | byte-slice list |
| `witness.headers` | `List[ByteList]` | at most 256 items, `2^10` B/item | byte-slice list |
| `activation.block_number` | `List[uint64]` optional | zero or one item | `?u64` |
| `activation.timestamp` | `List[uint64]` optional | zero or one item | `?u64` |
| `blob_schedule` | `List[BlobSchedule]` optional | zero or one 24 B item | `?RawBlobSchedule` |

## Fixed layouts and offset tables

| Container | Fixed layout / variable offsets |
|---|---|
| `SszStatelessInput` body | 16 B: `new_payload_request` offset @0, `witness` @4, `chain_config` @8, `public_keys` @12 |
| `SszNewPayloadRequest` | 44 B: `execution_payload` offset @0; `versioned_hashes` offset @4; `parent_beacon_block_root` `[8,40)`; `execution_requests` offset @40 |
| `SszExecutionPayload` | 540 B: `parent_hash` `[0,32)`; `fee_recipient` `[32,52)`; `state_root` `[52,84)`; `receipts_root` `[84,116)`; `logs_bloom` `[116,372)`; `prev_randao` `[372,404)`; `block_number`/`gas_limit`/`gas_used`/`timestamp` `u64` @404/@412/@420/@428; `extra_data` offset @436; `base_fee_per_gas` `uint256` `[440,472)`; `block_hash` `[472,504)`; `transactions` offset @504; `withdrawals` offset @508; `blob_gas_used`/`excess_blob_gas` `u64` @512/@520; `block_access_list` offset @528; `slot_number` `u64` @532 |
| `SszExecutionRequests` | 12 B: `deposits`/`withdrawals`/`consolidations` offsets @0/@4/@8 |
| `SszExecutionWitness` | 12 B: `state`/`codes`/`headers` offsets @0/@4/@8 |
| `SszChainConfig` | 12 B: `chain_id` `u64` `[0,8)`; `active_fork` offset @8 |
| `SszForkConfig` | 16 B: `fork` `u64` `[0,8)`; `activation`/`blob_schedule` offsets @8/@12 |
| `SszForkActivation` | 8 B: `block_number`/`timestamp` offsets @0/@4; each target is exactly 0 or 8 bytes |
| Optional blob schedule | exactly 0 or 24 B; `target`/`max`/`base_fee_update_fraction` `u64` @0/@8/@16 |
| `List[ByteList]` | empty is 0 B; otherwise the first `u32` offset is `4 × item count`, followed by a nondecreasing, in-range `u32` offset table; every byte slice obeys its listed cap |

### Fixed-record list elements

All fixed-record list payloads must have length divisible by their record width.

| List | Record layout |
|---|---|
| Payload withdrawals | 44 B: `index` `u64` @0, `validator_index` `u64` @8, `address[20]` @16, `amount` `u64` @36 |
| Deposit requests | 192 B: `pubkey[48]` @0, `withdrawal_credentials[32]` @48, `amount` `u64` @80, `signature[96]` @88, `index` `u64` @184 |
| Withdrawal requests | 76 B: `source_address[20]` @0, `validator_pubkey[48]` @20, `amount` `u64` @68 |
| Consolidation requests | 116 B: `source_address[20]` @0, `source_pubkey[48]` @20, `target_pubkey[48]` @68 |
| Versioned hashes | 32 B fixed elements |
| Public keys | 65 B fixed elements |

## Complete field correspondence

The corrected raw type owns every field below. The runtime adapter is deliberately separate: it
may perform RLP transaction decoding or reject an execution value it cannot represent, but it may
not alter this raw value.

| Schema path | Raw field | Previous Zesu runtime result | Corrected rule |
|---|---|---|---|
| Payload hashes: `parent_hash`, `state_root`, `receipts_root`, `prev_randao`, `block_hash` | `[32]u8` each | preserved | retain exactly |
| `fee_recipient` | `[20]u8` | preserved | retain exactly |
| `logs_bloom` | `[256]u8` | preserved | retain exactly |
| `block_number`, `gas_limit`, `gas_used`, `timestamp`, `blob_gas_used`, `excess_blob_gas`, `slot_number` | `u64` each | preserved for V4 | retain exactly |
| `extra_data`, transactions, block-access-list | byte slices / list of slices | values retained but bounds incomplete | enforce bounds and retain bytes |
| `base_fee_per_gas` | `u256` | silently narrowed to `u64` | retain all 256 bits; adapter rejects unrepresentable execution values rather than truncating |
| Payload withdrawals | `RawWithdrawal { index, validator_index, address, amount }` | preserved but count unchecked | enforce 16-item bound |
| `parent_beacon_block_root` | `[32]u8` | preserved | retain exactly |
| Versioned hashes | `[][32]u8` | preserved but count unchecked | enforce 4096-item bound |
| Deposit requests | typed five-field records | opaque 192-byte bytes | decode all fields and enforce record/count constraints |
| Withdrawal requests | typed three-field records | opaque 76-byte bytes | decode all fields and enforce record/count constraints |
| Consolidation requests | typed three-field records | opaque 116-byte bytes | decode all fields and enforce record/count constraints |
| Witness state, codes, headers | byte-slice lists | values retained but bounds incomplete | enforce list and item limits |
| `chain_id` | `u64` | zero rewritten to one | retain exactly, including zero |
| `active_fork.fork` | `u64` | unknown value silently became no name | reject unknown index for the V4 reference contract |
| Activation optionals | `?u64` each | permissively sampled | require canonical zero-or-one `uint64` lists |
| Blob schedule | `?RawBlobSchedule { target, max, base_fee_update_fraction }` | discarded | decode and retain exactly |
| Public keys | `[][65]u8` | values retained but max unchecked | enforce `2^15` item bound |

Schema/raw decoding treats each public key as an opaque 65-byte vector. Separately, Amsterdam
stateless execution requires exactly one uncompressed `0x04 || X || Y` key per decoded
transaction, byte-identical to that transaction's recovered public key. This execution validation
is outside raw decoding, the value differential, and parser metrics.

## `ssz-value-v1` differential protocol

All three implementations emit one UTF-8, LF-terminated record stream. The first record is exactly
`version\tssz-value-v1`. Subsequent records are in schema order and have exactly three
tab-separated fields:

```text
<path>\t<kind>\t<value>
```

`kind` is one of:

- `scalar`: a nonnegative base-10 integer with no leading zero except `0`;
- `bytes`: lowercase `0x` hexadecimal with exactly two digits per byte;
- `count`: a nonnegative base-10 list length;
- `option`: exactly `none` or `some`.

Every fixed byte vector is a `bytes` record. Every SSZ unsigned integer, including the full
`uint256` base fee, is a `scalar` record. A list is emitted as its `count` record followed by
zero-based indexed paths, for example `new_payload_request.execution_payload.transactions[0]`.
An optional is emitted as its `option` record; a `some` value is then emitted at `.value` using its
ordinary scalar or field records. Container names themselves have no records, so ordering is
defined solely by the table/schema field order and each list's increasing index.

The protocol emits all request fields, blob-schedule fields, activation optionals, raw transaction
bytes, all witness byte lists, and public keys. It uses no hashes, summaries, or collision-prone
normalization. Valid V4 inputs must produce byte-for-byte identical streams from Python,
Lean/SizzLean, and the Zesu host-only formatter; malformed V4 inputs must be rejected by all three.
