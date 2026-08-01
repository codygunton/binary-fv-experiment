// ============================================================================================
// VALIDATION-ONLY OVERLAY (Row B, PR #45) — appended by the `zesuContractProbe` nix derivation.
//
// This block is APPENDED to a byte-identical, sha256-verified copy of the pinned zesuRepaired
// `src/stateless/stateless/ssz_raw.zig` *inside the host contract-probe derivation only*. Every line
// of the pinned source above this marker is unchanged — the derivation verifies the original file's
// sha256 BEFORE appending, and verifies each `fn` named below actually exists in that source.
//
// It re-exports the file-private catalog routines under `probe_*` names so the host contract probe
// can test each source_function DIRECTLY, rather than only through the composed public `decode`. Because these
// are plain `pub const alias = privateFn;` bindings in the same file scope, they reach the private
// `fn`s without editing any existing declaration.
//
// It is compiled ONLY into the host-only `ssz-contract-probe` executable and is NEVER part of any
// production RV64 object derivation (`zesuSsz`, `zesuRawObject`, …), which each compile their own
// unpatched copy of the pinned source. This overlay therefore cannot change the shipped binary.
// ============================================================================================

// Containers
pub const probe_decodeNewPayloadRequest = decodeNewPayloadRequest;
pub const probe_decodeExecutionPayload = decodeExecutionPayload;
pub const probe_decodeExecutionRequests = decodeExecutionRequests;
pub const probe_decodeExecutionWitness = decodeExecutionWitness;
pub const probe_decodeChainConfig = decodeChainConfig;
pub const probe_decodeForkConfig = decodeForkConfig;
pub const probe_decodeForkActivation = decodeForkActivation;

// Options
pub const probe_decodeOptionalU64 = decodeOptionalU64;
pub const probe_decodeOptionalBlobSchedule = decodeOptionalBlobSchedule;

// Collections
pub const probe_decodeVersionedHashes = decodeVersionedHashes;
pub const probe_decodeWithdrawals = decodeWithdrawals;
pub const probe_decodeDepositRequests = decodeDepositRequests;
pub const probe_decodeWithdrawalRequests = decodeWithdrawalRequests;
pub const probe_decodeConsolidationRequests = decodeConsolidationRequests;
pub const probe_decodePublicKeys = decodePublicKeys;
pub const probe_decodeByteListList = decodeByteListList;

// Leaves
pub const probe_requireCanonicalOffsets = requireCanonicalOffsets;
pub const probe_requireU32Length = requireU32Length;
pub const probe_readOffset = readOffset;
pub const probe_readU32 = readU32;
pub const probe_readU64 = readU64;
pub const probe_readU256 = readU256;
pub const probe_readArray = readArray; // generic over comptime N (widths 20/32/48/65/96/256)
pub const probe_bytesAt = bytesAt;
pub const probe_hasExactErePrefix = hasExactErePrefix;
