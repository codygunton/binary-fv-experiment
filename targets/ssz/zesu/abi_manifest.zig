// This module is evaluated by the Nix ABI-manifest derivation for the pinned RV64 target.
const raw = @import("ssz_raw");

comptime {
    @compileLog(
        "RawStatelessInput",
        @sizeOf(raw.RawStatelessInput),
        @alignOf(raw.RawStatelessInput),
        @offsetOf(raw.RawStatelessInput, "new_payload_request"),
        @offsetOf(raw.RawStatelessInput, "witness"),
        @offsetOf(raw.RawStatelessInput, "chain_config"),
        @offsetOf(raw.RawStatelessInput, "public_keys"),
    );
    inline for (.{
        raw.RawNewPayloadRequest,
        raw.RawExecutionPayload,
        raw.RawExecutionRequests,
        raw.RawExecutionWitness,
        raw.RawChainConfig,
        raw.RawForkConfig,
        raw.RawForkActivation,
        raw.RawBlobSchedule,
        raw.RawWithdrawal,
        raw.RawDepositRequest,
        raw.RawWithdrawalRequest,
        raw.RawConsolidationRequest,
    }) |T| {
        @compileLog(@typeName(T), @sizeOf(T), @alignOf(T));
    }
}
