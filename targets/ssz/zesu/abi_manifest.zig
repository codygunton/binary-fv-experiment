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

/// The discriminant (`tag`) byte offset of an optional laid out with a *separate* discriminant.
///
/// Zig exposes `@offsetOf`/`@bitOffsetOf` only for struct/union fields, not for an optional's
/// synthetic discriminant, so the offset cannot be read back by reflection directly. It is instead
/// *derived* from the ABI, and the guard is what makes the derivation sound rather than a guess:
///
///   - `@sizeOf(Opt) <= @sizeOf(Child)` means the optional is niche-optimized (the discriminant is
///     folded into a spare bit pattern of the payload — e.g. pointer/error/enum optionals). There is
///     no separate tag byte to point at, so we `@compileError` rather than report a wrong offset.
///   - Passing the guard therefore witnesses a *non-niche* optional. For those Zig's layout is fixed:
///     the payload occupies `[0, @sizeOf(Child))` and the one-byte discriminant is placed at the next
///     naturally-aligned offset, which for a 1-byte flag is exactly `@sizeOf(Child)` (`@sizeOf` is a
///     multiple of the payload's alignment). So `@sizeOf(Child)` is the true discriminant offset for
///     every optional this function accepts.
///
/// This is still tied to the pinned compiler: the same `zig` that builds the production decoder emits
/// this manifest, so the derived offset is the one the decoder actually uses.
fn optionalTagOffset(comptime Opt: type) comptime_int {
    const Child = @typeInfo(Opt).optional.child;
    if (@sizeOf(Opt) <= @sizeOf(Child))
        @compileError("optional " ++ @typeName(Opt) ++ " has no separate discriminant byte");
    return @sizeOf(Child);
}

/// Emit the layout of a non-pointer optional: total size/alignment (both genuinely reflected), the
/// payload offset (`0` — Zig places a non-niche optional's payload first), and the discriminant
/// offset derived-and-guarded by `optionalTagOffset`.
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
    // The `stored_result` global is `?RawStatelessInput`: an inline optional result object, not a
    // pointer slot. Reflect its size and discriminant offset so the exported accessor's model is
    // pinned to the real 848-byte layout.
    logOptionalLayout(?raw.RawStatelessInput);
}
