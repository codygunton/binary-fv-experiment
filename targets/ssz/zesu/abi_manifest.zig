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

/// The discriminant (`tag`) byte offset of a non-pointer optional. Zig lays such an optional out as
/// payload-then-discriminant, so the tag byte sits immediately after the payload at `@sizeOf(Child)`.
/// The guard keeps this honest: it fires (rather than reporting a wrong offset) if the optional is
/// ever not larger than its payload, i.e. if there is no separate tag to point at.
fn optionalTagOffset(comptime Opt: type) comptime_int {
    const Child = @typeInfo(Opt).optional.child;
    if (@sizeOf(Opt) <= @sizeOf(Child))
        @compileError("optional " ++ @typeName(Opt) ++ " has no separate discriminant byte");
    return @sizeOf(Child);
}

/// Emit the full compiler-reflected layout of a non-pointer optional: total size/alignment, the
/// payload offset (0 — Zig places the payload first, and the reflected tag sits past the payload),
/// and the reflected discriminant offset.
fn logOptionalLayout(comptime Opt: type) void {
    @compileLog(@typeName(Opt) ++ "|size", @sizeOf(Opt));
    @compileLog(@typeName(Opt) ++ "|align", @alignOf(Opt));
    @compileLog(@typeName(Opt) ++ "|payload", @as(comptime_int, 0));
    @compileLog(@typeName(Opt) ++ "|tag", optionalTagOffset(Opt));
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
    logOptionalLayout(?u64);
    logOptionalLayout(?raw.RawBlobSchedule);
}
