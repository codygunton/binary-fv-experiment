//! Row B host contract probe over the pinned *private* decoder routine `ssz_raw.decode`.
//!
//! This executable imports only the `ssz_raw` module (the same source that compiles to the RV64
//! production decoder object) and drives it over the shared `ssz-contract-corpus-v1` JSONL corpus.
//! For every `ssz_raw.decode` case it:
//!
//!   * runs the real private `raw.decode` under a recording allocator and emits a *canonical
//!     outcome* to stdout — `{"id","routine","outcome"[,"error"]}` — matching the Lean
//!     `ssz_contract_runner` outcome (minus `value`; see below);
//!   * emits an *allocation ledger* to the ledger stream (a `--ledger` file, else stderr): the exact
//!     allocation count / bytes, an error-path leak check, and a single-point out-of-memory
//!     robustness sweep (inject a failure at each allocation index and require the decoder to
//!     surface a clean `error.OutOfMemory` with no leak).
//!
//! Item 1 (Row B): the file-private catalog routines ARE now reachable for direct per-routine testing
//! through the validation-only overlay (`overlay_exports.zig`), which the `zesuContractProbe`
//! derivation appends to a sha256-verified copy of the pinned source (production object derivations
//! are untouched). The `comptime` block below references every `raw.probe_*` re-export, so this exe
//! fails to build unless all are exposed; `--list-routines` prints the reachable routine identities.
//! The whole-input `raw.decode` decision + allocation lane below is preserved; the per-routine typed
//! vectors and Zig-vs-Lean-meaning value/error comparison build on this exposure. *Value* fidelity of
//! `raw.decode` itself remains additionally certified by the three-way `ssz-value-v1` audit.
//!
//! Exit status is nonzero if any case leaks or is out-of-memory-unsafe (both real defects).

const std = @import("std");
const raw = @import("ssz_raw");

const Writer = std.Io.Writer;

/// Item 1 (Row B): the file-private catalog routines the validation-only overlay
/// (`overlay_exports.zig`, appended inside the `zesuContractProbe` derivation) exposes for direct
/// testing. `readArray` is listed once per concrete width the decoder instantiates.
const exposed_routines = [_][]const u8{
    "ssz_raw.decodeNewPayloadRequest", "ssz_raw.decodeExecutionPayload",
    "ssz_raw.decodeExecutionRequests", "ssz_raw.decodeExecutionWitness",
    "ssz_raw.decodeChainConfig",       "ssz_raw.decodeForkConfig",
    "ssz_raw.decodeForkActivation",    "ssz_raw.decodeOptionalU64",
    "ssz_raw.decodeOptionalBlobSchedule", "ssz_raw.decodeVersionedHashes",
    "ssz_raw.decodeWithdrawals",       "ssz_raw.decodeDepositRequests",
    "ssz_raw.decodeWithdrawalRequests", "ssz_raw.decodeConsolidationRequests",
    "ssz_raw.decodePublicKeys",        "ssz_raw.decodeByteListList",
    "ssz_raw.requireCanonicalOffsets", "ssz_raw.requireU32Length",
    "ssz_raw.readOffset",              "ssz_raw.readU32",
    "ssz_raw.readU64",                 "ssz_raw.readU256",
    "ssz_raw.bytesAt",                 "ssz_raw.hasExactErePrefix",
    "ssz_raw.readArray[20]", "ssz_raw.readArray[32]", "ssz_raw.readArray[48]",
    "ssz_raw.readArray[65]", "ssz_raw.readArray[96]", "ssz_raw.readArray[256]",
};

// Compile-time proof that the overlay exposes every private catalog routine: referencing each
// `probe_*` re-export forces the compiler to resolve it against the private `fn` in the overlaid
// pinned source. If the overlay were missing (or a routine renamed) this executable would not build.
comptime {
    _ = raw.probe_decodeNewPayloadRequest;
    _ = raw.probe_decodeExecutionPayload;
    _ = raw.probe_decodeExecutionRequests;
    _ = raw.probe_decodeExecutionWitness;
    _ = raw.probe_decodeChainConfig;
    _ = raw.probe_decodeForkConfig;
    _ = raw.probe_decodeForkActivation;
    _ = raw.probe_decodeOptionalU64;
    _ = raw.probe_decodeOptionalBlobSchedule;
    _ = raw.probe_decodeVersionedHashes;
    _ = raw.probe_decodeWithdrawals;
    _ = raw.probe_decodeDepositRequests;
    _ = raw.probe_decodeWithdrawalRequests;
    _ = raw.probe_decodeConsolidationRequests;
    _ = raw.probe_decodePublicKeys;
    _ = raw.probe_decodeByteListList;
    _ = raw.probe_requireCanonicalOffsets;
    _ = raw.probe_requireU32Length;
    _ = raw.probe_readOffset;
    _ = raw.probe_readU32;
    _ = raw.probe_readU64;
    _ = raw.probe_readU256;
    _ = raw.probe_readArray;
    _ = raw.probe_bytesAt;
    _ = raw.probe_hasExactErePrefix;
}

/// The generous read limit for the corpus file itself (not a single decode input).
const max_corpus_bytes: usize = 1 << 30;
/// Default cap on how many allocation indices the OOM sweep probes per case; the rest are sampled at
/// a fixed stride and the ledger records `oom_sampled=true` so coverage is never silently bounded.
const default_max_inject: usize = 256;

const Outcome = enum { accept, reject };

// ============================================================================================
// Recording allocator — shared Row B item-5 infrastructure.
//
// A `std.mem.Allocator` that records ONE event per allocation with the final required event format:
// ordinal, requested size, alignment, a normalized returned-block id, whether the block aliased a
// live block, and whether it was freed before teardown. It supports single-point failure injection
// (fail the allocation at a chosen ordinal) and detects leaks (any block still live at teardown).
//
// Host addresses are NEVER emitted: the "returned block" is a stable ordinal-derived id, and
// `aliases` is computed from real addresses at record time but only the boolean survives — so the
// ledger is byte-identical across runs. Backed by a `DebugAllocator` for real memory + double-free
// detection; bookkeeping arrays use a separate `meta` allocator so they are not self-counted.
//
// This one allocator is used by BOTH the whole-input `raw.decode` ledger and the per-routine
// allocating vectors (collections / containers / entry), so every allocating routine shares one
// event format. It is NOT a temporary aggregate to be replaced later.
// ============================================================================================

const AllocEvent = struct {
    ordinal: usize, // 0-based allocation sequence number
    size: usize, // requested byte length
    alignment: usize, // requested alignment in bytes
    block: usize, // stable returned-block id (== ordinal); host address never emitted
    aliases: bool, // whether [addr, addr+size) overlapped a live block at allocation time
    freed: bool, // whether this block was freed before teardown (false at teardown => leak)
};

const Recording = struct {
    backing: std.mem.Allocator,
    meta: std.mem.Allocator,
    events: std.ArrayListUnmanaged(AllocEvent) = .empty,
    live: std.ArrayListUnmanaged(LiveBlock) = .empty,
    fail_at: usize, // inject an allocation failure at this ordinal (maxInt = never)
    injected_fired: bool = false,

    const LiveBlock = struct { addr: usize, len: usize, ordinal: usize };

    fn init(backing: std.mem.Allocator, meta: std.mem.Allocator, fail_at: usize) Recording {
        return .{ .backing = backing, .meta = meta, .fail_at = fail_at };
    }

    fn deinit(self: *Recording) void {
        self.events.deinit(self.meta);
        self.live.deinit(self.meta);
    }

    fn allocator(self: *Recording) std.mem.Allocator {
        return .{ .ptr = self, .vtable = &vtable };
    }

    /// A block is leaked iff it was allocated and never freed by teardown.
    fn leaked(self: *const Recording) bool {
        return self.live.items.len != 0;
    }

    fn overlapsLive(self: *const Recording, addr: usize, len: usize) bool {
        for (self.live.items) |b| {
            if (addr < b.addr + b.len and b.addr < addr + len) return true;
        }
        return false;
    }

    const vtable: std.mem.Allocator.VTable = .{
        .alloc = allocFn,
        .resize = resizeFn,
        .remap = remapFn,
        .free = freeFn,
    };

    fn allocFn(ctx: *anyopaque, len: usize, alignment: std.mem.Alignment, ret_addr: usize) ?[*]u8 {
        const self: *Recording = @ptrCast(@alignCast(ctx));
        const ordinal = self.events.items.len;
        if (ordinal == self.fail_at) {
            self.injected_fired = true;
            return null; // injected out-of-memory at this ordinal
        }
        const ptr = self.backing.rawAlloc(len, alignment, ret_addr) orelse return null;
        const addr = @intFromPtr(ptr);
        const aliases = self.overlapsLive(addr, len);
        self.events.append(self.meta, .{
            .ordinal = ordinal,
            .size = len,
            .alignment = alignment.toByteUnits(),
            .block = ordinal,
            .aliases = aliases,
            .freed = false,
        }) catch {
            self.backing.rawFree(ptr[0..len], alignment, ret_addr);
            return null;
        };
        self.live.append(self.meta, .{ .addr = addr, .len = len, .ordinal = ordinal }) catch {};
        return ptr;
    }

    fn resizeFn(ctx: *anyopaque, memory: []u8, alignment: std.mem.Alignment, new_len: usize, ret_addr: usize) bool {
        const self: *Recording = @ptrCast(@alignCast(ctx));
        if (!self.backing.rawResize(memory, alignment, new_len, ret_addr)) return false;
        const addr = @intFromPtr(memory.ptr);
        for (self.live.items) |*b| {
            if (b.addr == addr) {
                b.len = new_len;
                break;
            }
        }
        return true;
    }

    fn remapFn(ctx: *anyopaque, memory: []u8, alignment: std.mem.Alignment, new_len: usize, ret_addr: usize) ?[*]u8 {
        const self: *Recording = @ptrCast(@alignCast(ctx));
        const np = self.backing.rawRemap(memory, alignment, new_len, ret_addr) orelse return null;
        const old_addr = @intFromPtr(memory.ptr);
        const new_addr = @intFromPtr(np);
        for (self.live.items) |*b| {
            if (b.addr == old_addr) {
                b.addr = new_addr;
                b.len = new_len;
                break;
            }
        }
        return np;
    }

    fn freeFn(ctx: *anyopaque, memory: []u8, alignment: std.mem.Alignment, ret_addr: usize) void {
        const self: *Recording = @ptrCast(@alignCast(ctx));
        const addr = @intFromPtr(memory.ptr);
        for (self.live.items, 0..) |b, i| {
            if (b.addr == addr) {
                self.events.items[b.ordinal].freed = true;
                _ = self.live.swapRemove(i);
                break;
            }
        }
        self.backing.rawFree(memory, alignment, ret_addr);
    }
};

/// Run `raw.decode` once under a recording allocator that fails at `fail_at` (maxInt = never), and
/// classify the outcome for the OOM sweep: `""` = clean (rejected with OutOfMemory, no leak), else a
/// reason. Each call gets its own `DebugAllocator` so the leak / cleanup discipline is per-injection.
fn oomInjectOnce(gpa: std.mem.Allocator, input: []const u8, fail_at: usize) []const u8 {
    var debug: std.heap.DebugAllocator(.{}) = .init;
    var rec = Recording.init(debug.allocator(), gpa, fail_at);
    var reason: []const u8 = "";
    if (raw.decode(rec.allocator(), input)) |value| {
        var v = value;
        v.deinit(rec.allocator());
        reason = "accepted-under-oom";
    } else |err| {
        if (!std.mem.eql(u8, @errorName(err), "OutOfMemory")) reason = "non-oom-error-under-oom";
    }
    if (rec.leaked() and reason.len == 0) reason = "leak-under-oom";
    rec.deinit();
    if (debug.deinit() == .leak and reason.len == 0) reason = "backing-leak-under-oom";
    return reason;
}

/// Result of the OOM-robustness sweep over one case's recorded allocations.
const OomSweep = struct {
    safe: bool,
    injected: usize,
    sampled: bool,
    reason: []const u8, // "" when safe
};

/// Inject a single allocation failure at each (sampled) recorded ordinal in `[0, allocations)` and
/// require the decoder to fail cleanly with `error.OutOfMemory` and no leak — the allocator
/// precondition the occurrence contracts assume.
fn oomSweep(gpa: std.mem.Allocator, input: []const u8, allocations: usize, max_inject: usize) OomSweep {
    if (allocations == 0) return .{ .safe = true, .injected = 0, .sampled = false, .reason = "" };
    const sampled = allocations > max_inject;
    const stride = if (sampled) (allocations + max_inject - 1) / max_inject else 1;
    var injected: usize = 0;
    var k: usize = 0;
    while (k < allocations) : (k += stride) {
        const reason = oomInjectOnce(gpa, input, k);
        injected += 1;
        if (reason.len != 0) return .{ .safe = false, .injected = injected, .sampled = sampled, .reason = reason };
    }
    return .{ .safe = true, .injected = injected, .sampled = sampled, .reason = "" };
}

fn writeJsonString(w: *Writer, s: []const u8) !void {
    try w.writeByte('"');
    for (s) |c| switch (c) {
        '"' => try w.writeAll("\\\""),
        '\\' => try w.writeAll("\\\\"),
        '\n' => try w.writeAll("\\n"),
        '\r' => try w.writeAll("\\r"),
        '\t' => try w.writeAll("\\t"),
        else => if (c < 0x20) try w.print("\\u{x:0>4}", .{c}) else try w.writeByte(c),
    };
    try w.writeByte('"');
}

/// The canonical outcome line, matching the Lean runner's field set minus `value` (see module doc).
fn emitOutcome(w: *Writer, id: []const u8, outcome: Outcome, error_name: []const u8) !void {
    try w.writeAll("{\"id\":");
    try writeJsonString(w, id);
    try w.writeAll(",\"routine\":\"ssz_raw.decode\",\"outcome\":");
    try writeJsonString(w, if (outcome == .accept) "accept" else "reject");
    if (outcome == .reject) {
        try w.writeAll(",\"error\":");
        try writeJsonString(w, error_name);
    }
    try w.writeAll("}\n");
}

/// The per-allocation event array in the final ledger format. Reused by the per-routine allocating
/// vectors so every allocating routine emits the same event shape.
fn emitEvents(w: *Writer, events: []const AllocEvent) !void {
    try w.writeByte('[');
    for (events, 0..) |e, i| {
        if (i != 0) try w.writeByte(',');
        try w.print("{{\"ordinal\":{d},\"size\":{d},\"alignment\":{d},\"block\":{d}," ++
            "\"aliases\":{},\"freed\":{}}}", .{ e.ordinal, e.size, e.alignment, e.block, e.aliases, e.freed });
    }
    try w.writeByte(']');
}

fn emitLedger(w: *Writer, id: []const u8, outcome: Outcome, events: []const AllocEvent, leaked: bool, sweep: OomSweep) !void {
    try w.writeAll("{\"id\":");
    try writeJsonString(w, id);
    try w.print(",\"routine\":\"ssz_raw.decode\",\"outcome\":\"{s}\",\"allocations\":{d}," ++
        "\"leaked\":{},\"oom_safe\":{},\"oom_injected\":{d},\"oom_sampled\":{},\"events\":", .{
        if (outcome == .accept) "accept" else "reject",
        events.len, leaked, sweep.safe, sweep.injected, sweep.sampled,
    });
    try emitEvents(w, events);
    if (!sweep.safe) {
        try w.writeAll(",\"oom_reason\":");
        try writeJsonString(w, sweep.reason);
    }
    try w.writeAll("}\n");
}

fn jsonStr(obj: std.json.ObjectMap, key: []const u8) ?[]const u8 {
    const v = obj.get(key) orelse return null;
    return switch (v) {
        .string => |s| s,
        else => null,
    };
}

/// Process one corpus line; returns true if the case was a defect (leak or OOM-unsafe).
fn processLine(
    gpa: std.mem.Allocator,
    out: *Writer,
    ledger: *Writer,
    line: []const u8,
    max_inject: usize,
) !bool {
    var parsed = std.json.parseFromSlice(std.json.Value, gpa, line, .{}) catch return false;
    defer parsed.deinit();
    const obj = switch (parsed.value) {
        .object => |o| o,
        else => return false,
    };
    const routine = jsonStr(obj, "routine") orelse return false;
    if (!std.mem.eql(u8, routine, "ssz_raw.decode")) return false;
    const id = jsonStr(obj, "id") orelse return false;
    const args_val = obj.get("args") orelse return false;
    const args_obj = switch (args_val) {
        .object => |o| o,
        else => return false,
    };
    const input_hex = jsonStr(args_obj, "input") orelse return false;
    if (input_hex.len % 2 != 0) return false;

    const input = try gpa.alloc(u8, input_hex.len / 2);
    defer gpa.free(input);
    _ = std.fmt.hexToBytes(input, input_hex) catch return false;

    // Main run under the recording allocator (no injection): capture the per-event ledger and leak.
    var debug: std.heap.DebugAllocator(.{}) = .init;
    var rec = Recording.init(debug.allocator(), gpa, std.math.maxInt(usize));
    defer rec.deinit();
    var outcome: Outcome = undefined;
    var error_name: []const u8 = "";
    if (raw.decode(rec.allocator(), input)) |value| {
        var v = value;
        v.deinit(rec.allocator());
        outcome = .accept;
    } else |err| {
        outcome = .reject;
        error_name = @errorName(err);
    }
    const self_leak = rec.leaked();
    const backing_leak = debug.deinit() == .leak;
    const leaked = self_leak or backing_leak;

    const sweep = oomSweep(gpa, input, rec.events.items.len, max_inject);
    try emitOutcome(out, id, outcome, error_name);
    try emitLedger(ledger, id, outcome, rec.events.items, leaked, sweep);
    return leaked or !sweep.safe;
}

// ============================================================================================
// Item 2/3: per-routine typed vectors. Call each private catalog routine (via the overlay) with the
// vector's typed args and check the exact value / exact local error against the vector's expectation.
// ============================================================================================

/// Map a Zig error name to the handwritten-meaning error label the vectors use.
fn errLabel(zig_name: []const u8) []const u8 {
    if (std.mem.eql(u8, zig_name, "InvalidSsz")) return "invalidSsz";
    if (std.mem.eql(u8, zig_name, "UnknownFork")) return "unknownFork";
    if (std.mem.eql(u8, zig_name, "OutOfMemory")) return "outOfMemory";
    return zig_name;
}

fn jsonInt(obj: std.json.ObjectMap, key: []const u8) ?i64 {
    const v = obj.get(key) orelse return null;
    return switch (v) {
        .integer => |n| n,
        else => null,
    };
}

/// The three little-endian u64 fields of a decoded blob schedule, in the vector's value encoding.
const BlobFields = struct { target: u64, max: u64, bfuf: u64 };

/// The actual outcome of a routine call, in the vector's value encoding (no host pointers).
const Actual = union(enum) {
    nat: u256, // scalar reads (u32/u64/offset/u256)
    bytes: []const u8, // slice reads, input-relative
    boolean: bool,
    ok: void,
    err: []const u8, // local error label
    opt_u64: ?u64, // decodeOptionalU64
    opt_blob: ?BlobFields, // decodeOptionalBlobSchedule
    scalars: []const u64, // a container value flattened to a fixed-order u64 list (see flatten* below)
};

// A decoded container's value is flattened to a fixed-order list of u64 scalars, each option preceded
// by a 0/1 presence bit. The order MUST match ssz_routine_vectors.py's flat_fa/flat_fc/flat_cc and the
// Lean flatForkActivation/flatForkConfig/flatChainConfig, so all three encode the same struct value.
fn flatOptU64(v: ?u64, buf: []u64, at: usize) usize {
    if (v) |x| {
        buf[at] = 1;
        buf[at + 1] = x;
    } else {
        buf[at] = 0;
        buf[at + 1] = 0;
    }
    return at + 2;
}

fn flattenForkActivation(fa: raw.RawForkActivation, buf: []u64, at: usize) usize {
    return flatOptU64(fa.timestamp, buf, flatOptU64(fa.block_number, buf, at));
}

fn flattenBlob(bs: ?raw.RawBlobSchedule, buf: []u64, at: usize) usize {
    if (bs) |s| {
        buf[at] = 1;
        buf[at + 1] = s.target;
        buf[at + 2] = s.max;
        buf[at + 3] = s.base_fee_update_fraction;
    } else {
        buf[at] = 0;
        buf[at + 1] = 0;
        buf[at + 2] = 0;
        buf[at + 3] = 0;
    }
    return at + 4;
}

fn flattenForkConfig(fc: raw.RawForkConfig, buf: []u64, at: usize) usize {
    buf[at] = fc.fork;
    return flattenBlob(fc.blob_schedule, buf, flattenForkActivation(fc.activation, buf, at + 1));
}

fn flattenChainConfig(cc: raw.RawChainConfig, buf: []u64) usize {
    buf[0] = cc.chain_id;
    return flattenForkConfig(cc.active_fork, buf, 1);
}

/// `readArray(N)` copies its result into `buf` so the returned slice outlives the stack array.
fn runReadArray(comptime N: usize, input: []const u8, offset: usize, buf: *[256]u8) Actual {
    if (raw.probe_readArray(N, input, offset)) |arr| {
        @memcpy(buf[0..N], arr[0..N]);
        return .{ .bytes = buf[0..N] };
    } else |e| return .{ .err = errLabel(@errorName(e)) };
}

/// Dispatch one vector to its routine. `input` is the decoded `args.data`; `arrbuf` backs readArray
/// slices and `scalarbuf` backs flattened container values (both must outlive this call).
fn runRoutine(routine: []const u8, args: std.json.ObjectMap, input: []const u8, arrbuf: *[256]u8, scalarbuf: *[16]u64) ?Actual {
    const off: usize = @intCast(jsonInt(args, "offset") orelse 0);
    if (std.mem.eql(u8, routine, "ssz_raw.readU32")) {
        if (raw.probe_readU32(input, off)) |v| return .{ .nat = v } else |e| return .{ .err = errLabel(@errorName(e)) };
    } else if (std.mem.eql(u8, routine, "ssz_raw.readOffset")) {
        if (raw.probe_readOffset(input, off)) |v| return .{ .nat = v } else |e| return .{ .err = errLabel(@errorName(e)) };
    } else if (std.mem.eql(u8, routine, "ssz_raw.readU64")) {
        if (raw.probe_readU64(input, off)) |v| return .{ .nat = v } else |e| return .{ .err = errLabel(@errorName(e)) };
    } else if (std.mem.eql(u8, routine, "ssz_raw.readU256")) {
        if (raw.probe_readU256(input, off)) |v| return .{ .nat = v } else |e| return .{ .err = errLabel(@errorName(e)) };
    } else if (std.mem.eql(u8, routine, "ssz_raw.bytesAt")) {
        const len: usize = @intCast(jsonInt(args, "len") orelse 0);
        if (raw.probe_bytesAt(input, off, len)) |s| return .{ .bytes = s } else |e| return .{ .err = errLabel(@errorName(e)) };
    } else if (std.mem.eql(u8, routine, "ssz_raw.requireU32Length")) {
        if (raw.probe_requireU32Length(input)) |_| return .{ .ok = {} } else |e| return .{ .err = errLabel(@errorName(e)) };
    } else if (std.mem.eql(u8, routine, "ssz_raw.requireCanonicalOffsets")) {
        const fixed_size: usize = @intCast(jsonInt(args, "fixed_size") orelse 0);
        var offs_buf: [64]usize = undefined;
        var n: usize = 0;
        switch (args.get("offsets") orelse return null) {
            .array => |arr| for (arr.items) |it| {
                if (n >= offs_buf.len) return null;
                offs_buf[n] = switch (it) {
                    .integer => |x| @intCast(x),
                    else => return null,
                };
                n += 1;
            },
            else => return null,
        }
        if (raw.probe_requireCanonicalOffsets(input, fixed_size, offs_buf[0..n])) |_|
            return .{ .ok = {} }
        else |e| return .{ .err = errLabel(@errorName(e)) };
    } else if (std.mem.eql(u8, routine, "ssz_raw.hasExactErePrefix")) {
        return .{ .boolean = raw.probe_hasExactErePrefix(input) };
    } else if (std.mem.eql(u8, routine, "ssz_raw.decodeOptionalU64")) {
        if (raw.probe_decodeOptionalU64(input)) |v| return .{ .opt_u64 = v } else |e| return .{ .err = errLabel(@errorName(e)) };
    } else if (std.mem.eql(u8, routine, "ssz_raw.decodeOptionalBlobSchedule")) {
        if (raw.probe_decodeOptionalBlobSchedule(input)) |v| {
            if (v) |s| return .{ .opt_blob = .{ .target = s.target, .max = s.max, .bfuf = s.base_fee_update_fraction } };
            return .{ .opt_blob = null };
        } else |e| return .{ .err = errLabel(@errorName(e)) };
    } else if (std.mem.eql(u8, routine, "ssz_raw.decodeForkActivation")) {
        if (raw.probe_decodeForkActivation(input)) |fa| return .{ .scalars = scalarbuf[0..flattenForkActivation(fa, scalarbuf, 0)] } else |e| return .{ .err = errLabel(@errorName(e)) };
    } else if (std.mem.eql(u8, routine, "ssz_raw.decodeForkConfig")) {
        if (raw.probe_decodeForkConfig(input)) |fc| return .{ .scalars = scalarbuf[0..flattenForkConfig(fc, scalarbuf, 0)] } else |e| return .{ .err = errLabel(@errorName(e)) };
    } else if (std.mem.eql(u8, routine, "ssz_raw.decodeChainConfig")) {
        if (raw.probe_decodeChainConfig(input)) |cc| return .{ .scalars = scalarbuf[0..flattenChainConfig(cc, scalarbuf)] } else |e| return .{ .err = errLabel(@errorName(e)) };
    } else if (std.mem.startsWith(u8, routine, "ssz_raw.readArray[")) {
        const width: usize = @intCast(jsonInt(args, "width") orelse 0);
        inline for (.{ 20, 32, 48, 65, 96, 256 }) |N| {
            if (width == N) return runReadArray(N, input, off, arrbuf);
        }
        return null; // unknown width
    }
    return null; // routine not handled by this probe group
}

/// Whether `actual` equals the vector's `expect` object exactly.
fn actualMatches(actual: Actual, expect: std.json.ObjectMap) bool {
    const kind = jsonStr(expect, "kind") orelse return false;
    switch (actual) {
        .err => |label| {
            if (!std.mem.eql(u8, kind, "error")) return false;
            const want = jsonStr(expect, "error") orelse return false;
            return std.mem.eql(u8, label, want);
        },
        .nat => |n| {
            if (!std.mem.eql(u8, kind, "value")) return false;
            const vobj = switch (expect.get("value") orelse return false) {
                .object => |o| o,
                else => return false,
            };
            const want_s = jsonStr(vobj, "nat") orelse return false;
            const want = std.fmt.parseInt(u256, want_s, 10) catch return false;
            return n == want;
        },
        .bytes => |b| {
            if (!std.mem.eql(u8, kind, "value")) return false;
            const vobj = switch (expect.get("value") orelse return false) {
                .object => |o| o,
                else => return false,
            };
            const want_hex = jsonStr(vobj, "bytes") orelse return false;
            if (want_hex.len != b.len * 2) return false;
            var tmp: [256]u8 = undefined;
            const decoded = std.fmt.hexToBytes(tmp[0..b.len], want_hex) catch return false;
            return std.mem.eql(u8, decoded, b);
        },
        .boolean => |x| {
            if (!std.mem.eql(u8, kind, "value")) return false;
            const vobj = switch (expect.get("value") orelse return false) {
                .object => |o| o,
                else => return false,
            };
            const want = switch (vobj.get("bool") orelse return false) {
                .bool => |bb| bb,
                else => return false,
            };
            return x == want;
        },
        .ok => {
            if (!std.mem.eql(u8, kind, "value")) return false;
            const vobj = switch (expect.get("value") orelse return false) {
                .object => |o| o,
                else => return false,
            };
            return switch (vobj.get("ok") orelse return false) {
                .bool => |bb| bb,
                else => false,
            };
        },
        .opt_u64 => |ov| {
            if (!std.mem.eql(u8, kind, "value")) return false;
            const vobj = switch (expect.get("value") orelse return false) {
                .object => |o| o,
                else => return false,
            };
            switch (vobj.get("opt") orelse return false) {
                .null => return ov == null,
                .object => |oo| {
                    const want_s = jsonStr(oo, "u64") orelse return false;
                    const want = std.fmt.parseInt(u64, want_s, 10) catch return false;
                    return ov != null and ov.? == want;
                },
                else => return false,
            }
        },
        .opt_blob => |ob| {
            if (!std.mem.eql(u8, kind, "value")) return false;
            const vobj = switch (expect.get("value") orelse return false) {
                .object => |o| o,
                else => return false,
            };
            switch (vobj.get("opt") orelse return false) {
                .null => return ob == null,
                .object => |oo| {
                    if (ob == null) return false;
                    const s = ob.?;
                    const t = std.fmt.parseInt(u64, jsonStr(oo, "target") orelse return false, 10) catch return false;
                    const m = std.fmt.parseInt(u64, jsonStr(oo, "max") orelse return false, 10) catch return false;
                    const b = std.fmt.parseInt(u64, jsonStr(oo, "bfuf") orelse return false, 10) catch return false;
                    return s.target == t and s.max == m and s.bfuf == b;
                },
                else => return false,
            }
        },
        .scalars => |xs| {
            if (!std.mem.eql(u8, kind, "value")) return false;
            const vobj = switch (expect.get("value") orelse return false) {
                .object => |o| o,
                else => return false,
            };
            const arr = switch (vobj.get("scalars") orelse return false) {
                .array => |a| a,
                else => return false,
            };
            if (arr.items.len != xs.len) return false;
            for (arr.items, xs) |it, x| {
                const s = switch (it) {
                    .string => |ss| ss,
                    else => return false,
                };
                const want = std.fmt.parseInt(u64, s, 10) catch return false;
                if (want != x) return false;
            }
            return true;
        },
    }
}

fn emitRoutineOutcome(w: *Writer, id: []const u8, routine: []const u8, actual: Actual, matched: bool) !void {
    try w.writeAll("{\"id\":");
    try writeJsonString(w, id);
    try w.writeAll(",\"routine\":");
    try writeJsonString(w, routine);
    switch (actual) {
        .nat => |n| try w.print(",\"kind\":\"value\",\"nat\":\"{d}\"", .{n}),
        .bytes => |b| {
            try w.writeAll(",\"kind\":\"value\",\"bytes\":\"");
            for (b) |c| try w.print("{x:0>2}", .{c});
            try w.writeByte('"');
        },
        .boolean => |x| try w.print(",\"kind\":\"value\",\"bool\":{}", .{x}),
        .ok => try w.writeAll(",\"kind\":\"value\",\"ok\":true"),
        .opt_u64 => |ov| {
            if (ov) |v| try w.print(",\"kind\":\"value\",\"opt\":{{\"u64\":\"{d}\"}}", .{v}) else try w.writeAll(",\"kind\":\"value\",\"opt\":null");
        },
        .opt_blob => |ob| {
            if (ob) |s| try w.print(",\"kind\":\"value\",\"opt\":{{\"target\":\"{d}\",\"max\":\"{d}\",\"bfuf\":\"{d}\"}}", .{ s.target, s.max, s.bfuf }) else try w.writeAll(",\"kind\":\"value\",\"opt\":null");
        },
        .scalars => |xs| {
            try w.writeAll(",\"kind\":\"value\",\"scalars\":[");
            for (xs, 0..) |x, i| {
                if (i != 0) try w.writeByte(',');
                try w.print("\"{d}\"", .{x});
            }
            try w.writeByte(']');
        },
        .err => |label| {
            try w.writeAll(",\"kind\":\"error\",\"error\":");
            try writeJsonString(w, label);
        },
    }
    try w.print(",\"match\":{}}}\n", .{matched});
}

// ============================================================================================
// Allocating collections: decode under the shared recording allocator, render each element as a list
// of hex field tokens (u64 -> 8-byte little-endian, byte-vector -> raw bytes), free the result, and
// report the value + per-event allocation ledger + OOM sweep. Field order / stride match the source.
// ============================================================================================

/// An allocating routine's outcome in the vector's value encoding: a list of elements, each a list of
/// field tokens (raw bytes; hex-rendered at emit / compare time). No host pointers.
const AllocActual = union(enum) {
    items: []const []const []const u8,
    err: []const u8,
};

/// Builds tokens/elements into an arena that outlives the (freed) decoded result.
const TokBuilder = struct {
    arena: std.mem.Allocator,
    fn u64le(self: TokBuilder, v: u64) []const u8 {
        const b = self.arena.alloc(u8, 8) catch unreachable;
        std.mem.writeInt(u64, b[0..8], v, .little);
        return b;
    }
    fn bytes(self: TokBuilder, s: []const u8) []const u8 {
        return self.arena.dupe(u8, s) catch unreachable;
    }
    fn elem(self: TokBuilder, toks: []const []const u8) []const []const u8 {
        return self.arena.dupe([]const u8, toks) catch unreachable;
    }
};

fn isCollectionRoutine(routine: []const u8) bool {
    const names = [_][]const u8{
        "ssz_raw.decodeVersionedHashes", "ssz_raw.decodePublicKeys",       "ssz_raw.decodeWithdrawals",
        "ssz_raw.decodeDepositRequests", "ssz_raw.decodeWithdrawalRequests", "ssz_raw.decodeConsolidationRequests",
        "ssz_raw.decodeByteListList",
    };
    for (names) |n| if (std.mem.eql(u8, routine, n)) return true;
    return false;
}

/// Decode one collection under `alloc`, render its value into `arena`, then free the result. `arena`
/// outlives the free so the rendered tokens remain valid. Returns null only for a non-collection name.
fn runCollection(routine: []const u8, args: std.json.ObjectMap, input: []const u8, alloc: std.mem.Allocator, arena: std.mem.Allocator) ?AllocActual {
    const tb = TokBuilder{ .arena = arena };
    if (std.mem.eql(u8, routine, "ssz_raw.decodeVersionedHashes")) {
        if (raw.probe_decodeVersionedHashes(alloc, input)) |result| {
            const els = arena.alloc([]const []const u8, result.len) catch unreachable;
            for (result, 0..) |h, i| els[i] = tb.elem(&.{tb.bytes(h[0..])});
            alloc.free(result);
            return .{ .items = els };
        } else |e| return .{ .err = errLabel(@errorName(e)) };
    } else if (std.mem.eql(u8, routine, "ssz_raw.decodePublicKeys")) {
        if (raw.probe_decodePublicKeys(alloc, input)) |result| {
            const els = arena.alloc([]const []const u8, result.len) catch unreachable;
            for (result, 0..) |k, i| els[i] = tb.elem(&.{tb.bytes(k[0..])});
            alloc.free(result);
            return .{ .items = els };
        } else |e| return .{ .err = errLabel(@errorName(e)) };
    } else if (std.mem.eql(u8, routine, "ssz_raw.decodeWithdrawals")) {
        if (raw.probe_decodeWithdrawals(alloc, input)) |result| {
            const els = arena.alloc([]const []const u8, result.len) catch unreachable;
            for (result, 0..) |w, i| els[i] = tb.elem(&.{ tb.u64le(w.index), tb.u64le(w.validator_index), tb.bytes(w.address[0..]), tb.u64le(w.amount) });
            alloc.free(result);
            return .{ .items = els };
        } else |e| return .{ .err = errLabel(@errorName(e)) };
    } else if (std.mem.eql(u8, routine, "ssz_raw.decodeDepositRequests")) {
        if (raw.probe_decodeDepositRequests(alloc, input)) |result| {
            const els = arena.alloc([]const []const u8, result.len) catch unreachable;
            for (result, 0..) |d, i| els[i] = tb.elem(&.{ tb.bytes(d.pubkey[0..]), tb.bytes(d.withdrawal_credentials[0..]), tb.u64le(d.amount), tb.bytes(d.signature[0..]), tb.u64le(d.index) });
            alloc.free(result);
            return .{ .items = els };
        } else |e| return .{ .err = errLabel(@errorName(e)) };
    } else if (std.mem.eql(u8, routine, "ssz_raw.decodeWithdrawalRequests")) {
        if (raw.probe_decodeWithdrawalRequests(alloc, input)) |result| {
            const els = arena.alloc([]const []const u8, result.len) catch unreachable;
            for (result, 0..) |wr, i| els[i] = tb.elem(&.{ tb.bytes(wr.source_address[0..]), tb.bytes(wr.validator_pubkey[0..]), tb.u64le(wr.amount) });
            alloc.free(result);
            return .{ .items = els };
        } else |e| return .{ .err = errLabel(@errorName(e)) };
    } else if (std.mem.eql(u8, routine, "ssz_raw.decodeConsolidationRequests")) {
        if (raw.probe_decodeConsolidationRequests(alloc, input)) |result| {
            const els = arena.alloc([]const []const u8, result.len) catch unreachable;
            for (result, 0..) |c, i| els[i] = tb.elem(&.{ tb.bytes(c.source_address[0..]), tb.bytes(c.source_pubkey[0..]), tb.bytes(c.target_pubkey[0..]) });
            alloc.free(result);
            return .{ .items = els };
        } else |e| return .{ .err = errLabel(@errorName(e)) };
    } else if (std.mem.eql(u8, routine, "ssz_raw.decodeByteListList")) {
        const max_items: usize = @intCast(jsonInt(args, "max_items") orelse 0);
        const max_item_bytes: usize = @intCast(jsonInt(args, "max_item_bytes") orelse 0);
        if (raw.probe_decodeByteListList(alloc, input, max_items, max_item_bytes)) |result| {
            const els = arena.alloc([]const []const u8, result.len) catch unreachable;
            for (result, 0..) |it, i| els[i] = tb.elem(&.{tb.bytes(it)});
            alloc.free(result);
            return .{ .items = els };
        } else |e| return .{ .err = errLabel(@errorName(e)) };
    }
    return null;
}

fn hexNibble(c: u8) ?u8 {
    return switch (c) {
        '0'...'9' => c - '0',
        'a'...'f' => c - 'a' + 10,
        'A'...'F' => c - 'A' + 10,
        else => null,
    };
}

/// Whether an ascii-hex string equals a raw byte slice (no intermediate buffer, so any token length).
fn hexEqualsBytes(hex: []const u8, bytes: []const u8) bool {
    if (hex.len != bytes.len * 2) return false;
    for (bytes, 0..) |b, i| {
        const hi = hexNibble(hex[i * 2]) orelse return false;
        const lo = hexNibble(hex[i * 2 + 1]) orelse return false;
        if (b != hi * 16 + lo) return false;
    }
    return true;
}

fn allocActualMatches(actual: AllocActual, expect: std.json.ObjectMap) bool {
    const kind = jsonStr(expect, "kind") orelse return false;
    switch (actual) {
        .err => |label| {
            if (!std.mem.eql(u8, kind, "error")) return false;
            const want = jsonStr(expect, "error") orelse return false;
            return std.mem.eql(u8, label, want);
        },
        .items => |els| {
            if (!std.mem.eql(u8, kind, "value")) return false;
            const vobj = switch (expect.get("value") orelse return false) {
                .object => |o| o,
                else => return false,
            };
            const want_items = switch (vobj.get("items") orelse return false) {
                .array => |a| a,
                else => return false,
            };
            if (want_items.items.len != els.len) return false;
            for (want_items.items, els) |want_el_v, got_el| {
                const want_el = switch (want_el_v) {
                    .array => |a| a,
                    else => return false,
                };
                if (want_el.items.len != got_el.len) return false;
                for (want_el.items, got_el) |want_tok_v, got_tok| {
                    const want_hex = switch (want_tok_v) {
                        .string => |s| s,
                        else => return false,
                    };
                    if (!hexEqualsBytes(want_hex, got_tok)) return false;
                }
            }
            return true;
        },
    }
}

fn emitAllocOutcome(w: *Writer, id: []const u8, routine: []const u8, actual: AllocActual, matched: bool, events: []const AllocEvent, leaked: bool, sweep: OomSweep) !void {
    try w.writeAll("{\"id\":");
    try writeJsonString(w, id);
    try w.writeAll(",\"routine\":");
    try writeJsonString(w, routine);
    switch (actual) {
        .items => |els| {
            try w.writeAll(",\"kind\":\"value\",\"items\":[");
            for (els, 0..) |el, i| {
                if (i != 0) try w.writeByte(',');
                try w.writeByte('[');
                for (el, 0..) |tok, j| {
                    if (j != 0) try w.writeByte(',');
                    try w.writeByte('"');
                    for (tok) |c| try w.print("{x:0>2}", .{c});
                    try w.writeByte('"');
                }
                try w.writeByte(']');
            }
            try w.writeByte(']');
        },
        .err => |label| {
            try w.writeAll(",\"kind\":\"error\",\"error\":");
            try writeJsonString(w, label);
        },
    }
    try w.print(",\"match\":{},\"allocations\":{d},\"leaked\":{},\"oom_safe\":{},\"oom_injected\":{d},\"events\":", .{ matched, events.len, leaked, sweep.safe, sweep.injected });
    try emitEvents(w, events);
    if (!sweep.safe) {
        try w.writeAll(",\"oom_reason\":");
        try writeJsonString(w, sweep.reason);
    }
    try w.writeAll("}\n");
}

/// Run a collection once under a recording allocator failing at `fail_at`; classify for the OOM sweep.
fn collectionInjectOnce(gpa: std.mem.Allocator, routine: []const u8, args: std.json.ObjectMap, input: []const u8, fail_at: usize) []const u8 {
    var debug: std.heap.DebugAllocator(.{}) = .init;
    var rec = Recording.init(debug.allocator(), gpa, fail_at);
    var scratch = std.heap.ArenaAllocator.init(gpa);
    var reason: []const u8 = "";
    if (runCollection(routine, args, input, rec.allocator(), scratch.allocator())) |actual| {
        switch (actual) {
            .items => reason = "accepted-under-oom",
            .err => |label| if (!std.mem.eql(u8, label, "outOfMemory")) {
                reason = "non-oom-error-under-oom";
            },
        }
    }
    scratch.deinit();
    if (rec.leaked() and reason.len == 0) reason = "leak-under-oom";
    rec.deinit();
    if (debug.deinit() == .leak and reason.len == 0) reason = "backing-leak-under-oom";
    return reason;
}

fn collectionOomSweep(gpa: std.mem.Allocator, routine: []const u8, args: std.json.ObjectMap, input: []const u8, allocations: usize, max_inject: usize) OomSweep {
    if (allocations == 0) return .{ .safe = true, .injected = 0, .sampled = false, .reason = "" };
    const sampled = allocations > max_inject;
    const stride = if (sampled) (allocations + max_inject - 1) / max_inject else 1;
    var injected: usize = 0;
    var k: usize = 0;
    while (k < allocations) : (k += stride) {
        const reason = collectionInjectOnce(gpa, routine, args, input, k);
        injected += 1;
        if (reason.len != 0) return .{ .safe = false, .injected = injected, .sampled = sampled, .reason = reason };
    }
    return .{ .safe = true, .injected = injected, .sampled = sampled, .reason = "" };
}

/// Process one allocating-collection vector: value match + allocation ledger + OOM sweep. Returns true
/// on any defect (value mismatch, leak, or OOM-unsafe path).
fn processCollectionLine(gpa: std.mem.Allocator, out: *Writer, id: []const u8, routine: []const u8, args: std.json.ObjectMap, input: []const u8, expect: std.json.ObjectMap) !bool {
    var arena_inst = std.heap.ArenaAllocator.init(gpa);
    defer arena_inst.deinit();
    var debug: std.heap.DebugAllocator(.{}) = .init;
    var rec = Recording.init(debug.allocator(), gpa, std.math.maxInt(usize));
    defer rec.deinit();

    const actual = runCollection(routine, args, input, rec.allocator(), arena_inst.allocator()) orelse {
        _ = debug.deinit();
        try out.writeAll("{\"id\":");
        try writeJsonString(out, id);
        try out.writeAll(",\"routine\":");
        try writeJsonString(out, routine);
        try out.writeAll(",\"kind\":\"unhandled\",\"match\":false}\n");
        return true;
    };
    const self_leak = rec.leaked();
    const allocations = rec.events.items.len;
    const backing_leak = debug.deinit() == .leak;
    const leaked = self_leak or backing_leak;
    const sweep = collectionOomSweep(gpa, routine, args, input, allocations, default_max_inject);
    const matched = allocActualMatches(actual, expect);
    try emitAllocOutcome(out, id, routine, actual, matched, rec.events.items, leaked, sweep);
    return (!matched) or leaked or !sweep.safe;
}

/// Process one routine-vector line; returns true if it was a defect (mismatch or unhandled routine).
fn processRoutineLine(gpa: std.mem.Allocator, out: *Writer, line: []const u8) !bool {
    var parsed = std.json.parseFromSlice(std.json.Value, gpa, line, .{}) catch return false;
    defer parsed.deinit();
    const obj = switch (parsed.value) {
        .object => |o| o,
        else => return false,
    };
    const routine = jsonStr(obj, "routine") orelse return false;
    const id = jsonStr(obj, "id") orelse return false;
    const expect = switch (obj.get("expect") orelse return false) {
        .object => |o| o,
        else => return false,
    };
    const kind = jsonStr(expect, "kind") orelse return false;
    if (std.mem.eql(u8, kind, "gap")) {
        try out.writeAll("{\"id\":");
        try writeJsonString(out, id);
        try out.writeAll(",\"routine\":");
        try writeJsonString(out, routine);
        try out.writeAll(",\"kind\":\"gap\",\"match\":true}\n");
        return false;
    }

    const args = switch (obj.get("args") orelse return false) {
        .object => |o| o,
        else => return false,
    };
    var input: []const u8 = &[_]u8{};
    var owned = false;
    if (jsonStr(args, "data")) |hex| {
        if (hex.len % 2 != 0) return false;
        const buf = try gpa.alloc(u8, hex.len / 2);
        _ = std.fmt.hexToBytes(buf, hex) catch {
            gpa.free(buf);
            return false;
        };
        input = buf;
        owned = true;
    }
    defer if (owned) gpa.free(input);

    // Allocating collections decode under the recording allocator and report a value + ledger.
    if (isCollectionRoutine(routine)) return processCollectionLine(gpa, out, id, routine, args, input, expect);

    var arrbuf: [256]u8 = undefined;
    var scalarbuf: [16]u64 = undefined;
    const actual = runRoutine(routine, args, input, &arrbuf, &scalarbuf) orelse {
        // A vector naming a routine this probe cannot reach/dispatch is a real gap in coverage.
        try out.writeAll("{\"id\":");
        try writeJsonString(out, id);
        try out.writeAll(",\"routine\":");
        try writeJsonString(out, routine);
        try out.writeAll(",\"kind\":\"unhandled\",\"match\":false}\n");
        return true;
    };
    const matched = actualMatches(actual, expect);
    try emitRoutineOutcome(out, id, routine, actual, matched);
    return !matched;
}

fn runRoutineVectors(init: std.process.Init, gpa: std.mem.Allocator, path: []const u8) !void {
    const content = try std.Io.Dir.cwd().readFileAlloc(init.io, path, gpa, .limited(max_corpus_bytes));
    defer gpa.free(content);
    var out_buf: [64 * 1024]u8 = undefined;
    var out_file = std.Io.File.stdout().writer(init.io, &out_buf);
    const out = &out_file.interface;
    var defects: usize = 0;
    var lines = std.mem.splitScalar(u8, content, '\n');
    while (lines.next()) |line| {
        const trimmed = std.mem.trim(u8, line, " \t\r");
        if (trimmed.len == 0) continue;
        if (try processRoutineLine(gpa, out, trimmed)) defects += 1;
    }
    try out.flush();
    if (defects != 0) {
        var msg_buf: [128]u8 = undefined;
        const msg = std.fmt.bufPrint(&msg_buf, "probe: {d} routine vector(s) mismatched/unhandled\n", .{defects}) catch "probe: vector defects\n";
        stderrRaw(init.io, msg);
        std.process.exit(1);
    }
}

pub fn main(init: std.process.Init) !void {
    const gpa = init.gpa;
    const args = try init.minimal.args.toSlice(init.arena.allocator());

    var corpus_path: ?[]const u8 = null;
    var ledger_path: ?[]const u8 = null;
    var routine_vectors_path: ?[]const u8 = null;
    var max_inject: usize = default_max_inject;
    var list_routines = false;
    var i: usize = 1;
    while (i < args.len) : (i += 1) {
        const a = args[i];
        if (std.mem.eql(u8, a, "--list-routines")) {
            list_routines = true;
        } else if (std.mem.eql(u8, a, "--routine-vectors")) {
            i += 1;
            if (i >= args.len) fatal("--routine-vectors needs a path");
            routine_vectors_path = args[i];
        } else if (std.mem.eql(u8, a, "--ledger")) {
            i += 1;
            if (i >= args.len) fatal("--ledger needs a path");
            ledger_path = args[i];
        } else if (std.mem.eql(u8, a, "--max-inject")) {
            i += 1;
            if (i >= args.len) fatal("--max-inject needs a count");
            max_inject = std.fmt.parseInt(usize, args[i], 10) catch fatal("bad --max-inject");
        } else if (std.mem.startsWith(u8, a, "-")) {
            fatal("unknown flag");
        } else if (corpus_path == null) {
            corpus_path = a;
        } else {
            fatal("unexpected extra argument");
        }
    }
    if (list_routines) {
        var lr_buf: [64 * 1024]u8 = undefined;
        var lr_file = std.Io.File.stdout().writer(init.io, &lr_buf);
        const lr = &lr_file.interface;
        for (exposed_routines) |name| try lr.print("{s}\n", .{name});
        try lr.flush();
        return;
    }

    if (routine_vectors_path) |rvp| {
        try runRoutineVectors(init, gpa, rvp);
        return;
    }

    const path = corpus_path orelse fatal("usage: ssz-contract-probe <corpus.jsonl> [--ledger <path>] [--max-inject N] | --list-routines");

    const content = try std.Io.Dir.cwd().readFileAlloc(init.io, path, gpa, .limited(max_corpus_bytes));
    defer gpa.free(content);

    var out_buf: [64 * 1024]u8 = undefined;
    var out_file = std.Io.File.stdout().writer(init.io, &out_buf);
    const out = &out_file.interface;

    var ledger_buf: [64 * 1024]u8 = undefined;
    var ledger_file: std.Io.File = if (ledger_path) |lp|
        try std.Io.Dir.cwd().createFile(init.io, lp, .{})
    else
        std.Io.File.stderr();
    defer if (ledger_path != null) ledger_file.close(init.io);
    var ledger_writer = ledger_file.writer(init.io, &ledger_buf);
    const ledger = &ledger_writer.interface;

    var defects: usize = 0;
    var lines = std.mem.splitScalar(u8, content, '\n');
    while (lines.next()) |line| {
        const trimmed = std.mem.trim(u8, line, " \t\r");
        if (trimmed.len == 0) continue;
        if (try processLine(gpa, out, ledger, trimmed, max_inject)) defects += 1;
    }
    try out.flush();
    try ledger.flush();

    if (defects != 0) {
        var msg_buf: [128]u8 = undefined;
        const msg = std.fmt.bufPrint(&msg_buf, "probe: {d} case(s) leaked or were OOM-unsafe\n", .{defects}) catch "probe: defects\n";
        stderrRaw(init.io, msg);
        std.process.exit(1);
    }
}

fn stderrRaw(io: std.Io, msg: []const u8) void {
    var buf: [256]u8 = undefined;
    var w = std.Io.File.stderr().writer(io, &buf);
    w.interface.writeAll(msg) catch {};
    w.interface.flush() catch {};
}

fn fatal(comptime msg: []const u8) noreturn {
    @panic(msg);
}
