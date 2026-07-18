// This module is evaluated by the Nix ABI-manifest derivation for the pinned RV64 target.
const raw = @import("ssz_raw");

fn logLayout(comptime T: type) void {
    @compileLog(@typeName(T) ++ "|size", @sizeOf(T));
    @compileLog(@typeName(T) ++ "|align", @alignOf(T));
    inline for (@typeInfo(T).@"struct".fields) |field| {
        @compileLog(@typeName(T) ++ "|" ++ field.name, @offsetOf(T, field.name));
    }
}

fn logScalarLayout(comptime T: type) void {
    @compileLog(@typeName(T) ++ "|size", @sizeOf(T));
    @compileLog(@typeName(T) ++ "|align", @alignOf(T));
}

comptime {
    inline for (.{
        raw.RawStatelessInput,
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
    }) |T| logLayout(T);
    logScalarLayout(?u64);
}
