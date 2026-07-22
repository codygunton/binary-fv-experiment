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

/// The result of decoding one case (optionally with a single injected allocation failure).
const Decoded = struct {
    outcome: Outcome,
    error_name: []const u8, // "" on accept
    allocations: usize,
    allocated_bytes: usize,
    freed_bytes: usize,
    leaked: bool,
};

/// Decode `input` with a fresh leak-checked allocator, optionally failing the `fail_index`-th
/// allocation. Every case gets its own `DebugAllocator` so the leak check is per-case and the error
/// path's `errdefer` cleanup discipline is validated in isolation.
fn decodeCase(input: []const u8, fail_index: usize) Decoded {
    var debug: std.heap.DebugAllocator(.{}) = .init;
    var failing = std.testing.FailingAllocator.init(debug.allocator(), .{ .fail_index = fail_index });
    const alloc = failing.allocator();

    var out: Decoded = undefined;
    if (raw.decode(alloc, input)) |value| {
        var v = value;
        v.deinit(alloc);
        out = .{ .outcome = .accept, .error_name = "", .allocations = 0, .allocated_bytes = 0, .freed_bytes = 0, .leaked = false };
    } else |err| {
        out = .{ .outcome = .reject, .error_name = @errorName(err), .allocations = 0, .allocated_bytes = 0, .freed_bytes = 0, .leaked = false };
    }
    out.allocations = failing.alloc_index;
    out.allocated_bytes = failing.allocated_bytes;
    out.freed_bytes = failing.freed_bytes;
    out.leaked = debug.deinit() == .leak;
    return out;
}

/// Result of the OOM-robustness sweep over one case's allocations.
const OomSweep = struct {
    safe: bool,
    injected: usize,
    sampled: bool,
    reason: []const u8, // "" when safe
};

/// Inject a single allocation failure at each (sampled) index in `[0, allocations)` and require the
/// decoder to fail cleanly with `error.OutOfMemory` and no leak. This validates that the whole
/// `try`/`errdefer` chain of the composed decoder is out-of-memory-safe, which is exactly the
/// allocator precondition the occurrence contracts assume.
fn oomSweep(input: []const u8, allocations: usize, max_inject: usize) OomSweep {
    if (allocations == 0) return .{ .safe = true, .injected = 0, .sampled = false, .reason = "" };
    const sampled = allocations > max_inject;
    const stride = if (sampled) (allocations + max_inject - 1) / max_inject else 1;
    var injected: usize = 0;
    var k: usize = 0;
    while (k < allocations) : (k += stride) {
        const d = decodeCase(input, k);
        injected += 1;
        if (d.leaked) return .{ .safe = false, .injected = injected, .sampled = sampled, .reason = "leak-under-oom" };
        if (d.outcome != .reject) return .{ .safe = false, .injected = injected, .sampled = sampled, .reason = "accepted-under-oom" };
        if (!std.mem.eql(u8, d.error_name, "OutOfMemory"))
            return .{ .safe = false, .injected = injected, .sampled = sampled, .reason = "non-oom-error-under-oom" };
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
fn emitOutcome(w: *Writer, id: []const u8, d: Decoded) !void {
    try w.writeAll("{\"id\":");
    try writeJsonString(w, id);
    try w.writeAll(",\"routine\":\"ssz_raw.decode\",\"outcome\":");
    try writeJsonString(w, if (d.outcome == .accept) "accept" else "reject");
    if (d.outcome == .reject) {
        try w.writeAll(",\"error\":");
        try writeJsonString(w, d.error_name);
    }
    try w.writeAll("}\n");
}

fn emitLedger(w: *Writer, id: []const u8, d: Decoded, sweep: OomSweep) !void {
    try w.writeAll("{\"id\":");
    try writeJsonString(w, id);
    try w.print(",\"routine\":\"ssz_raw.decode\",\"outcome\":\"{s}\",\"allocations\":{d}," ++
        "\"allocated_bytes\":{d},\"freed_bytes\":{d},\"leaked\":{},\"oom_safe\":{}," ++
        "\"oom_injected\":{d},\"oom_sampled\":{}", .{
        if (d.outcome == .accept) "accept" else "reject",
        d.allocations, d.allocated_bytes, d.freed_bytes, d.leaked, sweep.safe, sweep.injected, sweep.sampled,
    });
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

    const d = decodeCase(input, std.math.maxInt(usize));
    const sweep = oomSweep(input, d.allocations, max_inject);
    try emitOutcome(out, id, d);
    try emitLedger(ledger, id, d, sweep);
    return d.leaked or !sweep.safe;
}

pub fn main(init: std.process.Init) !void {
    const gpa = init.gpa;
    const args = try init.minimal.args.toSlice(init.arena.allocator());

    var corpus_path: ?[]const u8 = null;
    var ledger_path: ?[]const u8 = null;
    var max_inject: usize = default_max_inject;
    var list_routines = false;
    var i: usize = 1;
    while (i < args.len) : (i += 1) {
        const a = args[i];
        if (std.mem.eql(u8, a, "--list-routines")) {
            list_routines = true;
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
