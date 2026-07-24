#!/usr/bin/env python3
"""Reduce production-ELF traces into deterministic evidence for all generated function instances.

Coverage is PER FUNCTION INSTANCE — a function instance is validated only on evidence in which its OWN region
executes, never inherited from another function_instance of the same source routine. Every check that cannot
be evaluated for a function instance is recorded as an EXPLICIT gap, never silently counted as a pass.

Evidence: the UNCHANGED production `zesu-ssz` ELF run under pinned `qemu-riscv64` with the diagnostic
trace plugin (`qemu_trace_plugin.so`). The plugin is self-contained — each store carries the stack
pointer — so write classification needs no separate GDB register capture, which is what makes a single
full-run trace cover ~all function instances at once. Nothing is rebuilt, relinked, patched, or instrumented.

The generic per-function-instance checks (apply to all function instances, trace-only):
  entryReached          the first in-region PC executed is the declared entryPc (the function instance is
                        entered at its binding entry); invocations are counted by entryPc executions
  controlFlowIntegrity  EXACT conformance to the generated CFG: every executed transfer whose SOURCE is
                        a PC this function instance OWNS appears verbatim in its declared `edges`. The generator
                        attributes each PC's edges to the DEEPEST function instance owning it
                        (`owned = regions - children's regions`), so an edge is declared exactly once
                        across an inline chain; the checker uses that same ownership. (An earlier version
                        of this checker compared against block-start membership instead, on the mistaken
                        inference that `edges` was non-exhaustive — it is not; that comparison had simply
                        ignored child-owned PCs. `cfg_audit.py` verifies the declared edges against the
                        control transfers decoded from the disassembly.)
  exitsRespected        every executed transfer that LEAVES the function instance's regions departs from a PC
                        listed in the declared `exits`.
  withinStepBound       max per-invocation instruction count <= the routine's contract step bound
                        (const bounds + readArray's specialization width; input-dependent bounds = gap)
  allocationConsistent  a NON-allocating routine never bumps the allocator cursor (.sbss); the
                        allocation ACT is a cursor store. Heap stores alone are allowed — a
                        non-allocating routine may fill a buffer a caller allocated (and memcpy/memmove
                        copy into the heap by design).
  inputPreserved        no store into the read-only SSZ input buffer
  codePreserved         no store into the .text code region
  writesClassified      every in-region store lands in a known region (code/cursor/heap/input/global/
                        stack, sp taken from the store record itself) — no unclassified writes
  bindingsEvaluable     every EFFECTIVE Row A binding row (the recovered table, not the raw DWARF one)
                        resolves to a concrete value from the machine state captured at the declared
                        entry PC: registers from the boundary snapshot, memory from the ELF image
                        overlaid with the preceding stores. A declared location the machine cannot
                        supply is a FAILURE, not a gap.
  bindingsRealized      the resolved values have their declared consequence in the trace, per routine
                        family: the exported entry's (input, input_len) equal the linked buffer base
                        and the exact byte length fed to the process; memcpy/memmove write exactly
                        [dst,dst+n) and read [src,src+n); an allocation's cursor bump covers its
                        request at the requested alignment; an `offset`-bound reader takes its window
                        at sliceBase+offset and touches exactly `len` bytes. Every captured invocation
                        is evaluated, not just the first.
  derivedBindingsHold   a loop-`derived` row's declared relation held at EVERY captured entry: the loop
                        register carried a multiple of the stride (it IS `index * stride`) and the
                        argument was that value plus the row's constant.
  exitBindingRealized   the result register at a declared RETURN exit matches the routine's exit
                        convention. Tail-call exits are excluded: their register file holds the
                        callee's arguments, not this function instance's result.
  allocationLedger      the function instance's cursor events ARE the allocation sequence the fixture requires
                        — same count, same order, same size, same alignment, same returned block. The
                        observed side is reconstructed from ZKVM_HEAP_POS's own write history; the
                        expected side is derived from the pinned Zig decode order and the Row B element
                        ABI applied to the exact fixture bytes, with no reference to the binary.
  meaningTie            for a fixed-width leaf reader: the little-endian integer of the EXACT window it
                        read IS the value it produced (stored, or held in a register when it left).
                        Anything weaker is an EXPLICIT gap, never a failure. The full per-value meaning
                        against the handwritten spec is the kernel-checked vertical slice (function instance 116).

This is diagnostic-only evidence and is never imported by the theorem graph. `scale_negative_tests.py`
corrupts copies of what this script captures and requires each corruption to flip the responsible
oracle predicate, so the checks here cannot quietly become unfalsifiable.
"""
from __future__ import annotations

import argparse
import json
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))   # the shared trace helpers live beside this script

# Pinned production memory layout (from the zesu-ssz ELF section headers / symbols; see STATUS).
TEXT = (65768, 81704)            # code — read-only (code preservation)
CURSOR = (86032, 86048)          # .sbss allocator words: ZKVM_HEAP_TOP@86032, ZKVM_HEAP_POS@86040
# Only ZKVM_HEAP_POS is the bump CURSOR; ZKVM_HEAP_TOP is the heap limit, written once at startup with
# the heap's end address. Treating the whole 16-byte window as the cursor made that one-off limit store
# look like an allocation event whose "size" was a huge negative jump.
CURSOR_POS = (86040, 86048)
HEAP = (86048, 67194912)         # bump heap (allocated blocks)
INPUT = (67194912, 69292064)     # SSZ input buffer — read-only (input preservation)
GLOBALS = (69292064, 69292928)   # decoder statics (stored_result / last_status / attempted / ...)
STACK_WINDOW = 1 << 16           # a store is "stack" if within this of its own recorded sp


def classify_write(addr: int, sp: int) -> str:
    if TEXT[0] <= addr < TEXT[1]:
        return "code"
    if CURSOR[0] <= addr < CURSOR[1]:
        return "allocator-cursor"
    if HEAP[0] <= addr < HEAP[1]:
        return "heap"
    if INPUT[0] <= addr < INPUT[1]:
        return "input"
    if GLOBALS[0] <= addr < GLOBALS[1]:
        return "decoder-global"
    if sp - STACK_WINDOW <= addr <= sp + STACK_WINDOW:
        return "stack"
    return "unclassified"


def parse_trace(path: Path):
    """Parse the self-contained plugin trace into (executed, loads, stores, regs).

    Every memory record carries the position in `executed` at which it happened, so the checker can ask
    what memory looked like *at* a boundary snapshot rather than only at the end of the run.
      executed: [pc]
      loads:    [(idx,pc,addr,w,v)]
      stores:   [(idx,pc,addr,w,v,sp)]
      regs:     [(idx,pc,[0,x1..x31])]   — full integer register file at a declared boundary pc"""
    executed, loads, stores, regs = [], [], [], []
    with open(path) as fh:
        for line in fh:
            p = line.split()
            if not p:
                continue
            if p[0] == "E":
                executed.append(int(p[1]))
            elif p[0] == "L":
                loads.append((len(executed), int(p[1]), int(p[2]), int(p[3]), int(p[4])))
            elif p[0] == "S":
                # S <pc> <addr> <width> <value> <sp>  (sp appended by the register-reading plugin)
                sp = int(p[5]) if len(p) > 5 else 0
                stores.append((len(executed), int(p[1]), int(p[2]), int(p[3]), int(p[4]), sp))
            elif p[0] == "R":
                # R <pc> <x1> … <x31>, taken BEFORE the instruction at <pc> executes.
                regs.append((len(executed), int(p[1]), [0] + [int(x) for x in p[2:]]))
    return executed, loads, stores, regs


# The direct-vs-dynamic transfer rule lives in ONE place (`riscv_transfers`), mirroring the extractor
# and Sail's `DecodedWord.controlTransfer`. An earlier version of this function classified a `jalr` as
# a resolved DIRECT call whenever objdump printed a `#` comment — but objdump prints one for a bare
# `jalr a5` too (rendering it as `jalr 0(a5)`), so genuine indirect calls were treated as static and
# their absence from the declared `edges` would have been reported as a CFG violation instead of being
# routed to the exit check. See riscv_transfers.resolved_target.
import riscv_transfers as rt  # noqa: E402
from riscv_transfers import dynamic_transfer_pcs  # noqa: E402
import function_instance_semantics as osem  # noqa: E402
import allocation_shapes as al  # noqa: E402


def step_bound_for(short: str, function_instance, catalog, arglb: dict):
    """Resolve a CONCRETE numeric step bound for a function instance, or None (an explicit gap) if the
    contract argument is not observable from the function instance's own trace.

    Input-dependent contract bounds have the shape `bound(arg) = C + K*(arg//D + E)`, monotonic
    non-decreasing in `arg`. Verifying `maxInsn <= bound(actualArg)` needs a value of `arg`, but a
    SOUND LOWER bound `argLB <= actualArg` suffices: since `bound` is non-decreasing,
    `bound(argLB) <= bound(actualArg)`, so `maxInsn <= bound(argLB)` implies `maxInsn <= bound(actualArg)`.
    The sound lower bounds (in `arglb`):
      inputLen   the whole-input byte length (entry routines: their slice IS the whole input — exact);
      inputBytes the count of distinct in-region input-buffer bytes the function instance read (a decoder reads
                 only within its own slice, so this is <= the slice length);
      copyLen    the in-region store count (memcpy/memmove store <= `length` bytes, one chunk per store).
    `unobservable` args (e.g. requireCanonicalOffsets' caller-passed offsets.length) stay explicit gaps.
    readArray's `32 + 4*width` is fixed per-function-instance by its comptime element width (specialization)."""
    meta = catalog.get(short)
    if not meta:
        return None, "no catalog entry", None
    sb = meta["stepBound"]
    if "const" in sb:
        return sb["const"], None, {"kind": "const"}
    if short == "readArray":
        spec = function_instance.get("specialization") or []
        if spec and str(spec[0]).isdigit():
            width = int(spec[0])
            return 32 + 4 * width, None, {"kind": "readArray", "width": width}
        return None, "readArray width not in specialization", None
    form = meta.get("stepBoundForm")
    if form:
        src = form["arg"]
        if src == "unobservable":
            return None, "input-dependent bound; argument not observable: " + form.get("interfaceNote", ""), None
        argv = arglb.get(src)
        if argv is None:
            return None, f"input-dependent bound; {src} not available", None
        C, K, D, E = form["C"], form["K"], form["D"], form["E"]
        bound = C + K * (argv // D + E)
        return bound, None, {"kind": "form", "C": C, "K": K, "D": D, "E": E,
                             "arg": src, "argLB": argv, "bound": bound}
    if "inputDependent" in sb:
        return None, f"input-dependent bound: {sb['inputDependent']}", None
    return None, sb.get("unknown", "unknown bound"), None


STORE_SUMMARY_TIES = {"raw"}  # memcpy/memmove: summarize the (large) destination-buffer write set


def carry_value(v, sp):
    """How a resolved binding value may be carried into the committed evidence.

    Guest STACK addresses shift between the host and the Nix sandbox even under `setarch -R`, so an
    absolute stack address must never enter a committed artifact. Small scalars (offsets, lengths,
    alignments) and fixed-vaddr pointers are deterministic and are carried exactly; a stack pointer is
    carried as its CLASS only. `("unresolved", 0)` marks a location the machine could not supply — a
    failure of `entryBindingsEvaluable`, never a silent pass."""
    if v is None:
        return ("unresolved", 0)
    if v < 65536:
        return ("exact", v)
    cls = classify_write(v, sp)
    return ("stack", 0) if cls == "stack" else ("exact", v)


def resolve_rows(rows, regs, mem, at_index, sp):
    """Resolve every effective Row A binding row against the captured machine state.

    Two outcomes per row:
      "exact"/"stack"  the declared location was read (a stack value is carried as its class only);
      "unresolved"     the row names a location the machine could not supply. A FAILURE.
    There is no third, "nothing to check here" outcome: the generator refuses to emit a row without a
    machine meaning, because `generatedEntryBinding` quantifies over the rows and one meaningless row
    would make the function instance's whole entry predicate unsatisfiable.

    A `derived` row additionally records the loop register it reads, so the derived relation
    `value = index * stride + constant` can be checked rather than only evaluated.
    Returns (carried_rows, evaluable, values_by_name, derived_observations)."""
    carried, ok, byname, derived = [], True, {}, []
    for r in rows:
        v = osem.resolve_binding(r, regs, mem, at_index)
        if v is None:
            ok = False
        byname[r["name"]] = v
        how, cv = carry_value(v, sp)
        carried.append({"name": r["name"], "kind": r["kind"], "reg": r["reg"], "declared": r["value"],
                        "how": how, "value": cv})
        if r["kind"] == "derived":
            scaled = regs[r["reg"]] if (regs is not None and 1 <= r["reg"] <= 31) else None
            derived.append({"name": r["name"], "register": r["reg"], "stride": r.get("stride", 0),
                            "constant": r["value"], "registerValue": scaled, "value": v})
    return carried, ok, byname, derived


def span_of(addrs):
    """(lo, count_of_distinct_bytes, hi_exclusive) of a set of byte addresses, or None if empty."""
    if not addrs:
        return None
    return (min(addrs), len(addrs), max(addrs) + 1)


def chain_is_infix(chain, path) -> bool:
    """Whether a function instance's routine chain occurs contiguously inside an expected event's call path.

    An inlined function instance's chain is its inline stack (`decodeRaw > … > decodeWithdrawals`); an emitted
    one's is just its own routine, which is why `decodeByteListList` claims the four events its four
    call sites cause. Contiguity is what stops an unrelated ancestor from claiming an event."""
    if not chain:
        return False
    n, m = len(path), len(chain)
    return any(path[i:i + m] == chain for i in range(n - m + 1))


def ledger_agrees(observed, expected) -> bool:
    """The observed cursor events ARE the independently expected allocation sequence.

    Each event must sit at the same whole-run ordinal, and the cursor must land exactly where the
    pinned bump allocator would put it for the expected size and alignment:
    `after = align_up(before, alignment) + size`. Where the allocator's returned pointer was captured it
    must be that same aligned base — the block the caller got is the block that was carved out. This
    mirrors `ScaleFunctionInstanceCheck.ledgerAgrees` exactly."""
    if len(observed) != len(expected):
        return False
    for o, e in zip(observed, expected):
        if o["ordinal"] != e["ordinal"]:
            return False
        ptr = al.align_up(o["before"], e["alignment"])
        if o["after"] != ptr + e["size"]:
            return False
        if o.get("returned") is not None and o["returned"] != ptr:
            return False
    return all(observed[i + 1]["ordinal"] > observed[i]["ordinal"] for i in range(len(observed) - 1))


def arm_ledger_holds(led) -> bool:
    """One arm's WHOLE-RUN ledger. Beyond the per-event agreement the observed events must CHAIN — each
    starts where the last ended, which is what a bump allocator does and what a dropped or inserted event
    breaks — and both sequences must be numbered 0,1,2,… with no hole. Mirrors
    `ScaleFunctionInstanceCheck.armLedgerHolds` exactly."""
    o, e = led["observed"], led["expected"]
    return (ledger_agrees(o, e)
            and all(o[i + 1]["before"] == o[i]["after"] for i in range(len(o) - 1))
            and all(x["ordinal"] == i for i, x in enumerate(o))
            and all(x["ordinal"] == i for i, x in enumerate(e)))


def derived_row_holds(d) -> bool:
    """The loop-derived relation held at every captured entry: the register carried a multiple of the
    stride (it is `index * stride`) and the parameter is that value plus the row's constant. Mirrors
    `BindingInventory.DerivedIndexRep` and `ScaleFunctionInstanceCheck.derivedRowHolds`."""
    if d["stride"] == 0 or not d["registerValues"] or len(d["registerValues"]) != len(d["values"]):
        return False
    return all(rv % d["stride"] == 0 and v == rv + d["constant"]
               for rv, v in zip(d["registerValues"], d["values"]))


def evaluate_entry_consequences(short, function_instance_index, values, ctx, inv, catalog_meta):
    """The routine-family consequence of the resolved entry bindings (layer 2 in the module docstring).

    Returns (verdict, detail) where verdict is True (realized), False (contradicted) or None (no
    consequence is observable for this family — an explicit gap)."""
    fam = (catalog_meta or {}).get("bindingFamily")
    obs = inv.setdefault("obs", {})
    obs["family"] = fam or ""
    if fam is None:
        return None, "no binding consequence defined for this routine"

    if fam == "entryAbi":
        # zesu_decode_raw(input, input_len): external ground truth — the buffer base the ELF is linked
        # at and the exact byte length of the file the process was fed.
        want_ptr, want_len = INPUT[0], ctx["inputLen"]
        got_ptr, got_len = values.get("input"), values.get("input_len")
        obs.update(entryInput=got_ptr, entryLen=got_len, wantInput=want_ptr, wantLen=want_len)
        ok = (got_ptr == want_ptr and got_len == want_len)
        return ok, (f"input={got_ptr} (expect {want_ptr}); input_len={got_len} (expect {want_len})")

    if fam == "rawCopy":
        # memcpy/memmove(dst, src, n): the copy must WRITE exactly [dst,dst+n) and READ exactly
        # [src,src+n). Off-by-one or a swapped register pair fails immediately.
        dst, src, n = values.get("dst"), values.get("src"), values.get("n")
        if None in (dst, src, n):
            return False, "dst/src/n not resolvable"
        ws, rs = inv["storeAddrs"], inv["loadAddrs"]
        want_w, want_r = set(range(dst, dst + n)), set(range(src, src + n))
        obs.update(copyN=n, copyStoredBytes=len(ws), copyWantBytes=len(want_w),
                   copySrcCovered=int(want_r <= rs))
        ok = ws == want_w and want_r <= rs
        return ok, (f"dst={dst} src={src} n={n}; wrote {len(ws)} bytes (want {len(want_w)}), "
                    f"read covers src window: {want_r <= rs}")

    if fam == "alloc":
        # zesu_raw_alloc(bytes, alignment) / allocatorAlloc(len, alignment): the cursor bump must cover
        # the request and the pointer handed back must honour the requested alignment.
        size = values.get("bytes", values.get("len"))
        align = values.get("alignment")
        ev = inv.get("ledgerEvent")
        if size is None or align is None:
            return False, "size/alignment not resolvable"
        # allocatorAlloc takes log2(alignment); zesu_raw_alloc takes the byte alignment.
        align_bytes = (1 << align) if (catalog_meta.get("alignmentIsLog2") and align < 64) else align
        if ev is None or ev.get("size") is None:
            return None, f"size={size} align={align_bytes}: no cursor bump observed in this invocation"
        # The bump allocator's behaviour is fully determined, so check the EXACT expected allocation,
        # not merely that the cursor advanced. From the pinned `zesu_raw_alloc` code:
        #     ptr    = align_up(cursor_before, alignment)
        #     cursor = ptr + bytes
        #     return   ptr
        # so both the new cursor and the returned pointer are predicted from (cursor_before, size,
        # alignment). A wrong size, a wrong alignment, a missing alignment step or a returned pointer
        # that is not the block just carved out all fail here; "the cursor moved forward inside the
        # heap" does not distinguish any of them.
        before, after = ev["before"], ev["after"]
        want_ptr = ((before + align_bytes - 1) // align_bytes) * align_bytes
        want_after = want_ptr + size
        got_ptr = inv.get("returnedPointer")
        obs.update(allocSize=size, allocAlign=align_bytes, allocBump=ev["size"],
                   allocAfter=after, allocWantAfter=want_after,
                   allocPtrMatches=(1 if (got_ptr is not None and got_ptr == want_ptr) else 0),
                   allocPtrKnown=(1 if got_ptr is not None else 0))
        ok = (after == want_after)
        if got_ptr is not None:
            ok = ok and got_ptr == want_ptr
        return ok, (f"size={size} align={align_bytes}; cursor {before}->{after} "
                    f"(expected {want_after}); returned pointer {got_ptr} "
                    f"(expected {want_ptr})")

    if fam == "offsetRead":
        # A reader bound to `offset` must take its window at sliceBase + offset, and a reader bound to
        # `len` must touch exactly `len` bytes. `bytesAt` only *forms* a sub-slice, so it may legitimately
        # perform no load at all — that is a gap, not a violation.
        off = values.get("offset")
        want_len = values.get("len")
        if "offset" not in values:
            return None, "the binding table declares no `offset` row for this function instance"
        if off is None:
            return False, "declared `offset` row did not resolve against the machine state"
        first = inv.get("firstReadAddr")
        if first is None:
            return None, (f"offset={off}: the function instance performed no data load in this invocation "
                          "(a sub-slice former reads nothing of its own)")
        base = first - off
        inv["impliedSliceBase"] = base
        if base < 0:
            return False, f"offset={off} exceeds the first load address {first}"
        cls = classify_write(base, inv.get("sp", 0))
        if cls not in ("input", "heap", "stack", "decoder-global"):
            return False, (f"offset={off} implies slice base {base}, classified {cls} — "
                           "no data region holds it")
        obs.update(offset=off, baseClassOk=1, readCount=inv["readCount"],
                   declaredLen=(-1 if want_len is None else want_len))
        if want_len is not None:
            got = inv["readCount"]
            return (got == want_len), (f"offset={off} len={want_len}; read {got} distinct bytes "
                                       f"from base {base} ({cls})")
        return True, f"offset={off}; implied slice base {base} ({cls})"

    if fam == "comptime":
        # const-folded parameters must equal the value pinned from the Zig source in the catalog, so a
        # constant-folded binding cannot drift from the source it claims to encode.
        want = (catalog_meta or {}).get("comptimeValues") or {}
        if not want:
            # Deliberately a GAP, not a pass: comparing a const binding against the value observed in
            # the very run being validated would be circular.
            return None, (catalog_meta or {}).get("comptimeNote",
                                                  "no pinned source constants for this routine")
        bad = {k: (values.get(k), v) for k, v in want.items() if values.get(k) != v}
        return (not bad), ("matches pinned source constants" if not bad else f"mismatch: {bad}")

    return None, f"unknown binding family {fam}"


def reduce_function_instance(function_instance, short, catalog, executed, loads, stores, input_len=0,
                      children_pcs=frozenset(), dynamic_pcs=frozenset(), ctx=None):
    """Extract the COMPACT, deterministic per-function-instance facts the checker consumes — observed facts
    only; the expected binding/bound/layout live in the checker. This is the reduction that BOTH the
    Python oracle (`evaluate_facts`) and the generated Lean checker evaluate identically."""
    ranges = [(r["start"], r["start"] + r["size"]) for r in function_instance["regions"]]
    entry_pc = function_instance["entryPc"]
    block_starts = sorted({b["start"] for b in function_instance["blocks"]})
    bs_set = set(block_starts)

    def in_region(pc):
        return any(a <= pc < b for a, b in ranges)

    in_region_idx = [i for i, pc in enumerate(executed) if in_region(pc)]
    meta = catalog.get(short, {})
    f: dict[str, object] = {
        "index": function_instance.get("index"),
        "qualified": function_instance["qualified"], "routine": short,
        "entryPc": entry_pc, "covered": len(in_region_idx) > 0,
        "allocates": meta.get("allocates", False),
        "meaningTieKind": meta.get("meaningTie", "structural"),
    }
    if not in_region_idx:
        return f

    f["firstInRegion"] = executed[in_region_idx[0]]
    entry_idxs = [i for i, pc in enumerate(executed) if pc == entry_pc]
    f["invocations"] = len(entry_idxs)
    if entry_idxs:
        bounds = entry_idxs + [len(executed)]
        per_inv = [sum(1 for pc in executed[a:b] if in_region(pc)) for a, b in zip(bounds, bounds[1:])]
    else:
        per_inv = [len(in_region_idx)]
    f["maxInsnPerInvocation"] = max(per_inv)

    # EXACT control-flow validation against the generated CFG.
    # The generator attributes each PC's edges to the DEEPEST function instance owning it
    # (`owned = regions - children's regions`), so every executed transfer FROM an owned PC must appear
    # verbatim in this function instance's declared `edges` — not merely land on a block start. Every executed
    # transfer that LEAVES the function instance's regions must have its source in the declared `exits`.
    owned = set()
    for a, b in ranges:
        owned |= set(range(a, b, 2))
    owned -= children_pcs
    declared_edges = sorted([e["source"], e["target"]] for e in function_instance["edges"])
    declared_set = {(e["source"], e["target"]) for e in function_instance["edges"]}
    exits = sorted(function_instance.get("exits") or [])
    exec_owned, leaving_src, dyn_src = set(), set(), set()
    for i in range(len(executed) - 1):
        s, t = executed[i], executed[i + 1]
        if s in owned:
            if s in dynamic_pcs:
                dyn_src.add(s)          # dynamic return/indirect: validated via `exits`, not `edges`
            else:
                exec_owned.add((s, t))
            if not in_region(t):
                leaving_src.add(s)
    f["blockStarts"] = block_starts
    f["declaredEdges"] = declared_edges
    f["executedOwnedEdges"] = sorted([s, t] for (s, t) in exec_owned)
    f["undeclaredExecutedEdges"] = sorted([s, t] for (s, t) in exec_owned if (s, t) not in declared_set)
    f["exits"] = exits
    f["leavingSources"] = sorted(leaving_src)
    f["leavingSourcesNotInExits"] = sorted(s for s in leaving_src if s not in set(exits))
    f["dynamicTransferSources"] = sorted(dyn_src)
    f["dynamicSourcesNotInExits"] = sorted(s for s in dyn_src if s not in set(exits))

    tie = f["meaningTieKind"]

    # Classify every in-region store with its OWN recorded sp. Stack addresses are environment-dependent
    # (the guest stack base shifts between hosts even under `setarch -R`), so they are NOT carried as
    # absolute values; only their (benign) "stack" class is summarized via `hadStackStore`. Every other
    # region (code/cursor/heap/input/global) sits at a FIXED vaddr in the static -no-pie ELF, so those
    # addresses are deterministic and are carried for the Lean checker to re-classify.
    reg_stores = [(addr, sp) for (_i, pc, addr, w, v, sp) in stores if in_region(pc)]
    f["storeCount"] = len(reg_stores)
    nonstack, had_stack, all_classes = [], False, set()
    for (addr, sp) in reg_stores:
        cls = classify_write(addr, sp)
        all_classes.add(cls)
        if cls == "stack":
            had_stack = True
        else:
            nonstack.append(addr)
    f["hadStackStore"] = had_stack
    f["storeClasses"] = sorted(all_classes)
    if tie in STORE_SUMMARY_TIES:
        # raw mem primitive: the write set is the (large) destination buffer; carry only the class set.
        f["storesSummarized"] = True
        f["inRegionStores"] = []
    else:
        # carry the deterministic non-stack store addresses; the Lean checker re-classifies each.
        f["storesSummarized"] = False
        f["inRegionStores"] = sorted(set(nonstack))

    # meaning-tie witness: a value the routine both LOADED from input and STORED (scalar carried through).
    in_input_loads = [(addr, v) for (_i, pc, addr, w, v) in loads if in_region(pc) and INPUT[0] <= addr < INPUT[1]]
    in_load_vals = sorted({v for (_, v) in in_input_loads})
    store_vals = {v for (_i, pc, addr, w, v, sp) in stores if in_region(pc)}
    f["inputLoadVals"] = in_load_vals
    f["storeHasInputPtr"] = any(INPUT[0] <= v < INPUT[1] for v in store_vals)
    f["scalarCarried"] = any(v in store_vals for v in in_load_vals)

    # RIGOROUS meaning for the fixed-width little-endian leaf readers: the value the function instance
    # produced must be the little-endian integer of the EXACT window it read. This replaces the earlier
    # "some loaded value was also stored" heuristic, which a coincidence could satisfy.
    width = meta.get("meaningWidth")
    if short == "readArray":
        spec = function_instance.get("specialization") or []
        width = int(spec[0]) if spec and str(spec[0]).isdigit() else None
    f["meaningWidth"] = width
    f["meaningLE"] = None
    if width and in_input_loads:
        bytemap = osem.observed_bytes(
            [(i, pc, addr, w, v) for (i, pc, addr, w, v) in loads
             if in_region(pc) and INPUT[0] <= addr < INPUT[1]], INPUT[0], INPUT[1])
        base = min(bytemap)
        got = len(bytemap)
        val = osem.le_value(bytemap, base, width) if got == width else None
        if val is None:
            f["meaningLEDetail"] = {"base": base, "width": width, "bytesRead": got,
                                    "reason": "read window is not exactly the declared width"}
        else:
            # "Produced" means the value left the function instance: written to memory, or held in a register
            # when the function instance returns. An INLINED leaf reader normally hands its result to the
            # enclosing frame in a register, so a store-only test would report a gap for most of them.
            in_store = val in store_vals
            in_regs = False
            if ctx is not None:
                for pc in (function_instance.get("exits") or []):
                    for (_i, _pc, regs) in ctx["regsByPc"].get(pc, []):
                        if val in regs[1:]:
                            in_regs = True
                            break
            f["meaningLE"] = True if (in_store or in_regs) else None
            f["meaningLEDetail"] = {"base": base, "width": width, "value": val,
                                    "producedAsStore": in_store, "producedInExitRegister": in_regs}

    # Step bound: resolve the (possibly input-dependent) contract bound to a concrete number using SOUND
    # lower bounds on its argument (see step_bound_for). inputBytes = distinct in-region input bytes read
    # (<= the routine's slice length); copyLen = in-region store count (<= bytes copied); inputLen = the
    # whole-input length (entry routines). requireCanonicalOffsets' offsets.length is unobservable -> gap.
    arglb = {
        "inputLen": input_len,
        "inputBytes": len({addr for (addr, _) in in_input_loads}),
        "copyLen": f["storeCount"],
    }
    bound, reason, deriv = step_bound_for(short, function_instance, catalog, arglb)
    f["stepBound"] = bound
    f["stepBoundGap"] = None if bound is not None else reason
    f["stepBoundDeriv"] = deriv

    # ---- Row A ENTRY/EXIT BINDINGS, allocation LEDGER and routine MEANING --------------------------
    # The declared bindings are the thing Row A actually says about an function instance; up to here nothing
    # evaluated them against the machine. `ctx` carries the boundary register snapshots, the shadow
    # memory (ELF image + replayed stores) and the effective binding table.
    f["armDecision"] = (ctx or {}).get("armDecision", 0)
    if ctx is not None:
        extents = dynamic_extents(entry_idxs or [in_region_idx[0]], executed, in_region,
                                  ctx["callPcs"], ctx["retPcs"], ctx["functionEntries"])
        _reduce_bindings(f, function_instance, short, meta, ctx, executed, loads, stores, ranges, in_region,
                         entry_idxs)
        _reduce_ledger(f, meta, ctx, extents, ctx["functionInstanceChain"][f["index"]])
    return f


def dynamic_extents(entry_idxs, executed, in_region, call_pcs, ret_pcs, function_entries):
    """The [start, end) trace window of each invocation — its DYNAMIC EXTENT.

    An function instance's effects include what its callees do: an allocation is performed by the allocator,
    not by the collection that requested it. So the extent covers every step from the function instance's entry
    up to and including its last own instruction, plus every step spent inside a routine it called (or
    tail-called) and has not yet returned from.

    A shadow call depth, incremented only for transfers OUT OF this function instance, is what separates
    "inside my callee" from "after me": once the depth is back to zero and the function instance's own regions
    stop executing, its extent is over. The depth also has to follow a TAIL transfer — the allocator
    vtable slot `jr`s straight into `zesu_raw_alloc`, so a plain call/return count would end the wrapper's
    extent one instruction before the allocation it exists to perform.

    Region membership alone is not enough either: an INLINED function instance's fragments are interleaved with
    its parent's code, so control leaves and re-enters its regions many times within one invocation.
    Only the LAST own instruction ends it."""
    n = len(executed)
    out = []
    for k, start in enumerate(entry_idxs):
        limit = entry_idxs[k + 1] if k + 1 < len(entry_idxs) else n
        depth, last, i = 0, start, start
        while i < limit:
            pc = executed[i]
            if depth > 0 or in_region(pc):
                last = i
                if pc in call_pcs:
                    depth += 1
                elif pc in ret_pcs:
                    depth = max(depth - 1, 0)
                elif (depth == 0 and i + 1 < n and executed[i + 1] in function_entries
                      and not in_region(executed[i + 1])):
                    depth += 1                       # a tail transfer into another routine
            i += 1
        out.append((start, last + 1))
    return out


def _reduce_ledger(f, meta, ctx, extents, chain):
    """The function instance's own slice of the allocation ledger, paired with the INDEPENDENTLY EXPECTED
    allocation sequence for the exact fixture this arm ran.

    The observed side is reconstructed from the allocator cursor's store history — the allocation ACT
    itself — not from anything the allocator reports about itself. The expected side comes from
    `allocation_shapes`: the pinned Zig decode order plus the Row B element ABI (`--dump-abi`) applied
    to the exact bytes fed to the process, with no reference to the binary. Comparing the two is what
    makes the check discriminating: "the cursor moved forward inside the heap" cannot tell an extra
    allocation, a wrong size, a wrong alignment or a reordering from the real sequence.

    A non-allocating function_instance must cause NO event; `allocationConsistent` already states that, so
    here it is an explicit gap rather than a second copy of the same claim."""
    observed = [e for e in ctx["ledger"]
                if e["size"] is not None and any(lo <= e["index"] < hi for lo, hi in extents)]
    f["ledgerEventCount"] = len(observed)
    if not meta.get("allocates"):
        f["allocationLedger"] = None
        f["ledgerGap"] = "non-allocating routine: covered by allocationConsistent"
        return
    expected = [e for e in ctx["expected"] if chain_is_infix(chain, e["routinePath"])]
    f["ledgerObserved"] = [{"ordinal": e["ordinal"], "before": e["before"], "after": e["after"],
                            "returned": e.get("returned")} for e in observed]
    f["ledgerExpected"] = [{"ordinal": e["ordinal"], "routine": e["routine"], "element": e["element"],
                            "count": e["count"], "size": e["size"], "alignment": e["alignment"]}
                           for e in expected]
    # A returned pointer the trace did not capture is a narrow per-FIELD gap: the rest of the event is
    # still compared. None occur on the current arms (`returned_blocks_all_observed`).
    f["ledgerReturnedUnknown"] = sum(1 for e in observed if e.get("returned") is None)
    # An function instance expected to allocate nothing that allocated nothing PASSES — that is a checkable
    # outcome, not an absent obligation.
    f["allocationLedger"] = ledger_agrees(f["ledgerObserved"], f["ledgerExpected"])


def _reduce_bindings(f, function_instance, short, meta, ctx, executed, loads, stores, ranges, in_region, entry_idxs):
    """Evaluate the effective Row A bindings, the allocation ledger event and the little-endian meaning
    for EACH captured invocation of this function instance, then reduce to per-function-instance evidence."""
    rows = ctx["bindings"].get(f["index"], [])
    entry_snaps = ctx["regsByPc"].get(f["entryPc"], [])
    exit_pairs = []            # (entry `dst` argument, value returned by that same invocation)
    exits = set(function_instance.get("exits") or [])
    f["bindingRowCount"] = len(rows)
    f["entrySnapshots"] = len(entry_snaps)

    if not rows:
        # A paramless function instance declares no entry placement; there is nothing to evaluate, and saying
        # "pass" would be counting an absent obligation as a discharged one.
        f["bindingsEvaluable"] = None
        f["bindingsRealized"] = None
        f["bindingGap"] = "function instance declares no parameter bindings (paramless)"
    elif not entry_snaps:
        f["bindingsEvaluable"] = None
        f["bindingsRealized"] = None
        f["bindingGap"] = "no register snapshot at the declared entry pc in this arm"
    else:
        evaluable, realized, details, carried = True, [], [], None
        derived_seen = {}
        # Evaluate every captured invocation, not just the first: a binding that holds once and breaks
        # later is a violation, and only per-invocation evaluation can see that.
        for (n, (idx, _pc, regs)) in enumerate(entry_snaps):
            sp = regs[2]
            crows, ok, byname, drows = resolve_rows(rows, regs, ctx["mem"], idx, sp)
            evaluable = evaluable and ok
            if carried is None:
                carried = crows
            for d in drows:
                # One entry per derived row, accumulating the loop register and the resolved argument
                # across the invocations — an index the relation must hold at, not just the first.
                slot = derived_seen.setdefault(d["name"], {
                    "name": d["name"], "register": d["register"], "stride": d["stride"],
                    "constant": d["constant"], "registerValues": [], "values": []})
                if d["registerValue"] is None or d["value"] is None:
                    # The declared loop register could not be read at this entry. Recording only the
                    # half that IS known leaves the two lists unequal, which both checkers reject —
                    # an unreadable location must never look like a satisfied relation.
                    slot["registerValues"].append(d["registerValue"] or 0)
                    continue
                slot["registerValues"].append(d["registerValue"])
                slot["values"].append(d["value"])
            inv = _invocation_facts(f, idx, executed, loads, stores, ranges, in_region, entry_idxs,
                                    exits, ctx)
            inv["sp"] = sp
            exit_pairs.append((byname.get("dst"), inv.get("returnedPointer")))
            verdict, detail = evaluate_entry_consequences(short, f["index"], byname, ctx, inv, meta)
            realized.append(verdict)
            if n == 0:
                f["bindingObs"] = sorted((k, int(v)) for k, v in inv.get("obs", {}).items()
                                         if not isinstance(v, str))
                f["bindingFamily"] = inv.get("obs", {}).get("family", "")
            if n < 4:            # keep the report bounded and deterministic
                details.append(detail)
        f["bindingRows"] = carried
        f["bindingHows"] = [c["how"] for c in carried]
        f["derivedRows"] = [derived_seen[k] for k in sorted(derived_seen)]
        f["realizedPass"] = sum(1 for v in realized if v is True)
        f["realizedFail"] = sum(1 for v in realized if v is False)
        f["realizedGap"] = sum(1 for v in realized if v is None)
        f["bindingsEvaluable"] = False if not evaluable else True
        if any(v is False for v in realized):
            f["bindingsRealized"] = False
        elif realized and all(v is True for v in realized):
            f["bindingsRealized"] = True
        else:
            f["bindingsRealized"] = None
            f["bindingGap"] = (meta.get("bindingFamily") and
                               f"binding consequence not observable in every invocation: {details[:2]}"
                               or "no binding consequence defined for this routine")
        f["bindingDetail"] = details

    # ---- exit binding: the result register at a declared exit pc --------------------------------
    conv = meta.get("exitConvention")
    f["exitConvention"] = conv or ""
    # A declared exit is not necessarily a RETURN: several function instances leave through a tail call, where
    # the register file holds the callee's arguments, not this routine's result. Applying a result
    # convention there compares the wrong thing, so only `ret` exits are used.
    ret_exits = sorted(exits & ctx["retPcs"])
    exit_snaps = [(i, pc, r) for pc in ret_exits for (i, p2, r) in ctx["regsByPc"].get(pc, [])]
    exit_snaps.sort()
    f["returnExits"] = ret_exits
    f["exitSnapshots"] = len(exit_snaps)
    if conv is None:
        f["exitBindingRealized"] = None
        f["exitGap"] = "no exit convention declared for this routine"
    elif not ret_exits:
        f["exitBindingRealized"] = None
        f["exitGap"] = "function instance has no `ret` exit (it leaves through a tail call)"
    elif not exit_snaps:
        f["exitBindingRealized"] = None
        f["exitGap"] = "no register snapshot at a declared return exit in this arm"
    else:
        f["exitBindingRealized"], f["exitDetail"] = _check_exit(conv, exit_snaps, f, ctx, exit_pairs)
        f["exitPairsMatched"] = sum(1 for (d, r) in exit_pairs
                                    if d is not None and r is not None and d == r)
        f["exitPairsTotal"] = sum(1 for (d, r) in exit_pairs if d is not None and r is not None)
        # Carry only DETERMINISTIC returned values. A returned pointer is usually a guest STACK
        # address, and the guest stack base differs between this host and the Nix sandbox even under
        # `setarch -R`, so putting one in a committed artifact makes the drift check fail for a reason
        # that has nothing to do with the binary. The conventions that consume this field
        # (`decodeDecision`) return small scalars; `copyDestination` uses the pair COUNTS, which are
        # environment-independent, and `exitA0Classes` already summarizes the rest.
        f["exitReturnedValues"] = sorted({r for (_d, r) in exit_pairs
                                          if r is not None and r < 65536})[:4]


def _invocation_facts(f, entry_idx, executed, loads, stores, ranges, in_region, entry_idxs, exits, ctx):
    """The observable consequences of ONE invocation: which bytes it read and wrote, and the allocator
    cursor event it caused. Bounded to [this entry, next entry) so consequences of one call are never
    attributed to another."""
    later = [i for i in entry_idxs if i > entry_idx]
    end = later[0] if later else len(executed)
    lo, hi = entry_idx, end
    read_addrs, write_addrs, first_read = set(), set(), None
    for (i, pc, addr, w, v) in loads:
        if lo <= i < hi and in_region(pc):
            for j in range(w):
                read_addrs.add(addr + j)
            if first_read is None or addr < first_read:
                first_read = addr
    for (i, pc, addr, w, v, sp) in stores:
        if lo <= i < hi and in_region(pc):
            for j in range(w):
                write_addrs.add(addr + j)
    ev = None
    for e in ctx["ledger"]:
        if lo <= e["index"] < hi:
            ev = e
            break
    # The value this invocation RETURNED: a0 at a declared `ret` exit inside the same window, so the
    # result is paired with the entry arguments of the very same call rather than any other.
    returned = None
    for pc in (exits & ctx["retPcs"]):
        for (i, _pc, regs) in ctx["regsByPc"].get(pc, []):
            if lo <= i < hi:
                returned = regs[10]
                break
        if returned is not None:
            break
    return {"loadAddrs": read_addrs, "storeAddrs": write_addrs, "readCount": len(read_addrs),
            "firstReadAddr": first_read, "ledgerEvent": ev, "window": (lo, hi),
            "returnedPointer": returned}


def _check_exit(conv, exit_snaps, f, ctx, per_inv):
    """Check the declared exit convention against the register file at a declared RETURN exit.

    Every convention here compares the returned register to something INDEPENDENTLY known — the entry
    argument of the same invocation, or the decision the process actually exited with. An earlier
    version returned `true` unconditionally for `copyDestination` and `decodeDecision`, which is not a
    check at all: it passed for any register value whatsoever."""
    f["exitA0Classes"] = sorted({classify_write(r[10], r[2]) for (_i, _pc, r) in exit_snaps})

    if conv == "allocPointer":
        # Checked exactly by the `alloc` binding family (returned pointer == align_up(cursor,
        # alignment)); repeating a weaker range test here would only add a second, laxer opinion.
        return None, "the returned pointer is checked exactly by the alloc binding family"

    if conv == "copyDestination":
        # memcpy/memmove return their `dst` argument unchanged. Pair each invocation's returned a0
        # with the `dst` captured at that same invocation's entry.
        pairs = [(d, r) for (d, r) in per_inv if d is not None and r is not None]
        if not pairs:
            return None, "no invocation paired an entry `dst` with a returned a0"
        matched = sum(1 for d, r in pairs if d == r)
        return matched == len(pairs), (f"{len(pairs)} invocation(s); returned a0 == entry dst in "
                                       f"{matched}")

    if conv == "decodeDecision":
        # The exported wrapper's return value must agree with the decision the PROCESS actually exited
        # with: the harness exits 0 when the decode succeeded and 1 when it was rejected.
        a0 = [r for (_d, r) in per_inv if r is not None]
        if not a0:
            return None, "no returned a0 captured at a return exit"
        want = 1 if ctx.get("armDecision") == 0 else 0
        return all(v == want for v in a0), (
            f"returned a0 {sorted(set(a0))}; process exit code {ctx.get('armDecision')} "
            f"implies decode decision {want}")

    return None, f"unknown exit convention {conv}"

def classes_of(f):
    """The distinct write classes for a function instance — recomputed from the carried non-stack addresses
    (classified with sp=0; they are never stack) plus the summarized `stack` flag, or the summarized set
    for raw mem primitives. Mirrors the Lean checker exactly and equals the reducer's `storeClasses`."""
    if f.get("storesSummarized"):
        return set(f["storeClasses"])
    cls = {classify_write(a, 0) for a in f["inRegionStores"]}
    if f.get("hadStackStore"):
        cls.add("stack")
    return cls


def evaluate_facts(f):
    """The reference oracle: evaluate the generic per-function-instance checks from the compact facts. Returns
    a dict mapping each check to True / False / None (None = explicit gap). The Lean checker computes the
    same booleans on the same facts."""
    checks: dict[str, object] = {}
    gaps: dict[str, str] = {}
    if not f.get("covered"):
        for name in CHECK_NAMES:
            checks[name], gaps[name] = None, "function instance region not executed by any arm"
        return checks, gaps

    checks["entryReached"] = f["firstInRegion"] == f["entryPc"]
    # EXACT generated-CFG conformance: every executed transfer from an owned PC is a declared edge.
    checks["controlFlowIntegrity"] = len(f["undeclaredExecutedEdges"]) == 0
    # every executed transfer leaving the function instance's regions departs at a declared exit PC.
    checks["exitsRespected"] = (len(f["leavingSourcesNotInExits"]) == 0
                                and len(f["dynamicSourcesNotInExits"]) == 0)

    bound = f["stepBound"]
    if bound is None:
        checks["withinStepBound"], gaps["withinStepBound"] = None, f["stepBoundGap"]
    else:
        checks["withinStepBound"] = f["maxInsnPerInvocation"] <= bound

    classes = classes_of(f)
    checks["writesClassified"] = "unclassified" not in classes
    checks["inputPreserved"] = "input" not in classes
    checks["codePreserved"] = "code" not in classes
    checks["allocationConsistent"] = True if f["allocates"] else ("allocator-cursor" not in classes)

    # Row A ENTRY BINDINGS: every declared effective location must be readable from the real machine.
    checks["bindingsEvaluable"] = f.get("bindingsEvaluable")
    if checks["bindingsEvaluable"] is None:
        gaps["bindingsEvaluable"] = f.get("bindingGap", "no binding evidence")
    # …and must have their declared consequence in the trace (routine-family specific).
    checks["bindingsRealized"] = f.get("bindingsRealized")
    if checks["bindingsRealized"] is None:
        gaps["bindingsRealized"] = f.get("bindingGap", "no binding consequence observable")
    # LOOP-DERIVED rows: the declared relation `index * stride + constant` held at every captured entry.
    drows = f.get("derivedRows") or []
    if not drows:
        checks["derivedBindingsHold"] = None
        gaps["derivedBindingsHold"] = "function instance declares no loop-derived binding row"
    else:
        checks["derivedBindingsHold"] = all(derived_row_holds(d) for d in drows)
    checks["exitBindingRealized"] = f.get("exitBindingRealized")
    if checks["exitBindingRealized"] is None:
        gaps["exitBindingRealized"] = f.get("exitGap", "no exit convention")
    # ALLOCATION LEDGER: the function instance's cursor events ARE the independently expected sequence.
    checks["allocationLedger"] = f.get("allocationLedger")
    if checks["allocationLedger"] is None:
        gaps["allocationLedger"] = f.get("ledgerGap", "function instance causes no allocation event")

    # MEANING. `meaningLE` is the rigorous statement (the little-endian integer of the exact window the
    # function instance read IS the value it produced); the older value tie remains only as a fallback for the
    # slice readers, and anything weaker is an explicit gap.
    tie = f["meaningTieKind"]
    if f.get("meaningLE") is True:
        checks["meaningTie"] = True
    elif tie == "slice" and f["storeHasInputPtr"]:
        checks["meaningTie"] = True
    elif tie in ("scalarLE", "offset") and f["scalarCarried"]:
        checks["meaningTie"] = True
    else:
        checks["meaningTie"] = None
        gaps["meaningTie"] = (f"{tie}: no clean input-to-result value tie in this region "
                              "(deep meaning is validated for function instance 116 in the Lean checker)")
    return checks, gaps


def run_full_trace(qemu, plugin, elf, input_path, out_path, bpc_path=None, bcap=256):
    """Run the UNCHANGED ELF under pinned QEMU with the trace plugin (no PC window: whole run).
    setarch -R disables host ASLR for a deterministic guest stack. `bpc_path` lists the declared Row A
    entry/exit PCs at which the plugin snapshots the whole integer register file, so the checker can
    evaluate the declared bindings against the real machine. Returns the ELF decision (0/1)."""
    args = f"{plugin},out={out_path}"
    if bpc_path:
        args += f",bpc={bpc_path},bcap={bcap}"
    cmd = ["setarch", "-R", qemu, "-plugin", args, elf]
    with open(input_path, "rb") as fh:
        r = subprocess.run(cmd, stdin=fh, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    if r.returncode >= 2:
        raise SystemExit(f"ELF faulted under QEMU on {input_path} (exit {r.returncode})")
    return r.returncode


CHECK_NAMES = ("entryReached", "controlFlowIntegrity", "exitsRespected", "withinStepBound",
               "allocationConsistent", "inputPreserved", "codePreserved", "writesClassified",
               "bindingsEvaluable", "bindingsRealized", "derivedBindingsHold", "exitBindingRealized",
               "allocationLedger", "meaningTie")


# --- Lean emission --------------------------------------------------------------------------------

def _oi(n):  # Option Nat
    return "none" if n is None else f"(some {n})"


def _ob(b):  # Option Bool  (None gap / True pass / False fail)
    return "none" if b is None else ("(some true)" if b else "(some false)")


def _ln(xs):  # List Nat
    return "[" + ", ".join(str(x) for x in xs) + "]"


def _lp(xs):  # List (Nat × Nat)
    return "[" + ", ".join(f"({a}, {b})" for a, b in xs) + "]"


def _ls(xs):  # List String
    return "[" + ", ".join('"' + str(s).replace('"', '\\"') + '"' for s in xs) + "]"


def _lsi(xs):  # List (String × Int)
    return "[" + ", ".join(f'({_str(k)}, {v})' for k, v in xs) + "]"


def _derived_to_lean(d):  # DerivedRowEvidence
    return (f"{{ name := {_str(d['name'])}, register := {d['register']}, stride := {d['stride']}, "
            f"constant := {d['constant']}, registerValues := {_ln(d['registerValues'])}, "
            f"values := {_ln(d['values'])} }}")


def _observed_to_lean(o):  # ObservedAlloc
    return (f"{{ ordinal := {o['ordinal']}, cursorBefore := {o['before']}, "
            f"cursorAfter := {o['after']}, returnedPointer := {_oi(o.get('returned'))} }}")


def _expected_to_lean(e):  # ExpectedAlloc
    return (f"{{ ordinal := {e['ordinal']}, routine := {_str(e['routine'])}, "
            f"element := {_str(e['element'])}, count := {e['count']}, size := {e['size']}, "
            f"alignment := {e['alignment']} }}")


def _b(x):
    return "true" if x else "false"


def _str(s):
    return '"' + str(s).replace("\\", "\\\\").replace('"', '\\"') + '"'


def function_instance_to_lean(rec) -> str:
    """One `(FunctionInstanceScaleEvidence × ScaleChecks)` tuple literal, deterministic."""
    f, c = rec["facts"], rec["checks"]
    ev = (
        f"{{ index := {rec['index']}, qualified := {_str(f['qualified'])}, "
        f"routine := {_str(f['routine'])}, arm := {_str(rec.get('arm') or '')}, "
        f"entryPc := {f['entryPc']}, covered := {_b(f.get('covered'))}, "
        f"firstInRegion := {f.get('firstInRegion', 0)}, "
        f"maxInsnPerInvocation := {f.get('maxInsnPerInvocation', 0)}, "
        f"declaredEdges := {_lp(f.get('declaredEdges', []))}, "
        f"executedOwnedEdges := {_lp(f.get('executedOwnedEdges', []))}, "
        f"exits := {_ln(f.get('exits', []))}, "
        f"leavingSources := {_ln(f.get('leavingSources', []))}, "
        f"dynamicTransferSources := {_ln(f.get('dynamicTransferSources', []))}, "
        f"stepBound := {_oi(f.get('stepBound'))}, allocates := {_b(f.get('allocates', False))}, "
        f"meaningTieKind := {_str(f.get('meaningTieKind', 'structural'))}, "
        f"storesSummarized := {_b(f.get('storesSummarized', False))}, "
        f"inRegionStores := {_ln(f.get('inRegionStores', []))}, "
        f"hadStackStore := {_b(f.get('hadStackStore', False))}, "
        f"storeClasses := {_ls(f.get('storeClasses', []))}, "
        f"scalarCarried := {_b(f.get('scalarCarried', False))}, "
        f"storeHasInputPtr := {_b(f.get('storeHasInputPtr', False))}, "
        f"bindingHows := {_ls(f.get('bindingHows', []))}, "
        f"derivedRows := [" + ", ".join(_derived_to_lean(d) for d in f.get('derivedRows', [])) + "], "
        f"bindingFamily := {_str(f.get('bindingFamily', ''))}, "
        f"bindingObs := {_lsi(f.get('bindingObs', []))}, "
        f"realizedPass := {f.get('realizedPass', 0)}, "
        f"realizedFail := {f.get('realizedFail', 0)}, "
        f"realizedGap := {f.get('realizedGap', 0)}, "
        f"exitConvention := {_str(f.get('exitConvention', ''))}, "
        f"exitPairsMatched := {f.get('exitPairsMatched') or 0}, "
        f"exitPairsTotal := {f.get('exitPairsTotal') or 0}, "
        f"exitReturnedValues := {_ln(f.get('exitReturnedValues') or [])}, "
        f"armDecision := {f.get('armDecision', 0)}, "
        f"returnExits := {_ln(f.get('returnExits', []))}, "
        f"exitA0Classes := {_ls(f.get('exitA0Classes', []))}, "
        f"ledgerEventCount := {f.get('ledgerEventCount', 0)}, "
        f"ledgerObserved := [" + ", ".join(_observed_to_lean(o)
                                           for o in f.get('ledgerObserved', [])) + "], "
        f"ledgerExpected := [" + ", ".join(_expected_to_lean(e)
                                           for e in f.get('ledgerExpected', [])) + "], "
        f"ledgerReturnedUnknown := {f.get('ledgerReturnedUnknown', 0)}, "
        f"meaningWidth := {_oi(f.get('meaningWidth'))}, "
        f"meaningValue := {_oi((f.get('meaningLEDetail') or {}).get('value'))}, "
        f"meaningProduced := {_b(f.get('meaningLE') is True)} }}"
    )
    ck = (
        f"{{ entryReached := {_ob(c['entryReached'])}, "
        f"controlFlowIntegrity := {_ob(c['controlFlowIntegrity'])}, "
        f"exitsRespected := {_ob(c['exitsRespected'])}, "
        f"withinStepBound := {_ob(c['withinStepBound'])}, "
        f"allocationConsistent := {_ob(c['allocationConsistent'])}, "
        f"inputPreserved := {_ob(c['inputPreserved'])}, "
        f"codePreserved := {_ob(c['codePreserved'])}, "
        f"writesClassified := {_ob(c['writesClassified'])}, "
        f"bindingsEvaluable := {_ob(c['bindingsEvaluable'])}, "
        f"bindingsRealized := {_ob(c['bindingsRealized'])}, "
        f"derivedBindingsHold := {_ob(c['derivedBindingsHold'])}, "
        f"exitBindingRealized := {_ob(c['exitBindingRealized'])}, "
        f"allocationLedger := {_ob(c['allocationLedger'])}, "
        f"meaningTie := {_ob(c['meaningTie'])} }}"
    )
    return f"  (\n    {ev},\n    {ck})"


# Function instances no input exercises. Their static unreachability is established by
# `static_reachability.py` (a backward reaching-definitions fixpoint over the reconstructed CFG plus a
# danger-set closure over the loaded image), and its residual hypotheses are stated in
# `STATIC_REACHABILITY.md`. These strings summarize that analysis; they do not stand on their own, and
# Row C's conclusions exclude these function instances either way — every check for them is an explicit gap.
DOCUMENTED_UNCOVERED = {
    "allocatorRemap": "std.mem.Allocator remap slot (vtable+16). STATIC: no instruction targets its "
                      "entry directly; for an indirect transfer to carry it, some register would have "
                      "to hold vtable+16 minus the site's load offset, and no image word holds that "
                      "value and no instruction materializes it. See STATIC_REACHABILITY.md.",
    "allocatorResize": "std.mem.Allocator resize slot (vtable+8). STATIC: same closure as remap — the "
                       "base register would have to hold a value that appears nowhere in the image and "
                       "is materialized by no instruction. See STATIC_REACHABILITY.md.",
    "zesu_raw_error": "exported raw-ABI error getter. STATIC: its entry appears at NO image address at "
                      "all and is materialized by no instruction, so no register can hold it; the "
                      "sealed _start harness discriminates success/failure via zesu_raw_result's null "
                      "return. See STATIC_REACHABILITY.md.",
}


def emit_report(records, summary) -> str:
    """A compact, deterministic per-function-instance coverage report (markdown). Gaps are shown explicitly."""
    sym = {True: "P", False: "F", None: "-"}
    short = {"entryReached": "entry", "controlFlowIntegrity": "cfg", "exitsRespected": "exit",
             "withinStepBound": "step",
             "allocationConsistent": "alloc", "inputPreserved": "inp", "codePreserved": "code",
             "writesClassified": "wr", "bindingsEvaluable": "bind", "bindingsRealized": "breal",
             "derivedBindingsHold": "deriv", "exitBindingRealized": "xbind",
             "allocationLedger": "ledg", "meaningTie": "mean"}
    L = ["# Row C — scaled per-function-instance production-ELF coverage (GENERATED)",
         "",
         "Regenerated by `targets/ssz/zesu/trace/scale_function_instances.py` from the UNCHANGED production",
         "`zesu-ssz` ELF under pinned `qemu-riscv64`. Diagnostic-only; never imported by the proof.",
         "Coverage is PER FUNCTION INSTANCE (never inherited from a sibling of the same routine). `P`=pass,",
         "`F`=fail, `-`=explicit gap (never counted as a pass).",
         "",
         "**Step bounds**: input-dependent contract bounds `C + K*(arg//D + E)` are resolved to a concrete",
         "number using a SOUND LOWER bound on `arg` (whole-input length for entry routines; distinct",
         "in-region input bytes read — <= the slice length — for containers/collections; in-region store",
         "count — <= bytes copied — for memcpy/memmove). Since the bound is monotonic, `maxInsn <=`",
         "`bound(argLB)` implies `maxInsn <= bound(actualArg)`. `requireCanonicalOffsets` is the one",
         "unresolved bound (its `offsets.length` is a caller-passed argument, not in the function instance's",
         "input reads) — an explicit gap, with the required interface change recorded in",
         "`routine_catalog.json` under that routine's `stepBoundForm.interfaceNote`.",
         "",
         "**Row A bindings** are evaluated against the real machine: every effective binding row is",
         "resolved from the register file captured at the function instance's declared entry PC (and, for",
         "`breg`/`fbreg` rows, from the ELF image overlaid with the stores preceding that point).",
         "`bind` = every declared location resolved; `breal` = the resolved values had their declared",
         "consequence in the trace (routine-family specific); `deriv` = a loop-`derived` row's relation",
         "`index * stride + constant` held at EVERY captured entry (the loop register carried a multiple",
         "of the stride and the argument was that value plus the row's constant); `xbind` = the result",
         "register at a declared RETURN exit matches the routine's convention. `ledg` compares the",
         "function instance's slice of the bump cursor's own write history against the allocation sequence",
         "derived independently of the binary (see the ledger section below).",
         "",
         "**Uncovered function instances** are STATICALLY analysed by `static_reachability.py` — a backward",
         "reaching-definitions fixpoint over the reconstructed CFG plus a danger-set closure over the",
         "loaded image — with its residual hypotheses stated in `STATIC_REACHABILITY.md`. Row C's",
         "conclusions exclude them and the one unresolved step bound either way.",
         "",
         "**Meaning checks are deliberately PARTIAL in Row C, and are reported as such.** `meaningTie`",
         "states only that the little-endian integer of the exact window a function instance read IS the value",
         "it produced — a scalar/slice tie. It does NOT run the function instance's `RoutineSpec.meaning` and",
         "compare a structured result, so every structural routine is an explicit gap (`mean: structural`)",
         "rather than a pass, as is the one function instance whose comptime limits are not readable from the",
         "pinned source. Broad source-level semantic validation is Row B's job (it runs the handwritten",
         "Lean `meaning` for all 43 routine identities against the real Zig decoder); the deep",
         "machine-level meaning check here is the kernel-checked vertical slice for function instance 116. Row C",
         "claims nothing more than the per-function-instance numbers in the table below.",
         "",
         f"**{summary['covered']}/{summary['function_instances']} function instances covered** by the present /",
         "malformed / absent arms. Per-check totals:",
         "",
         "| check | pass | fail | gap |", "|---|---:|---:|---:|"]
    for n in CHECK_NAMES:
        d = summary["byCheck"][n]
        L.append(f"| {n} | {d['pass']} | {d['fail']} | {d['gap']} |")
    census = summary.get("missingParameterRows", {}).get("rows", [])
    L += ["", "## Parameter-row census", "",
          "Every function_instance must carry a row for every parameter its ROUTINE declares — otherwise a",
          "silently dropped binding is indistinguishable from a paramless routine, and the function instance's",
          "entry predicate quietly says less than the source does. The extractor takes each signature",
          "from the function instance's DWARF abstract-origin DIE, so this census (function instances declaring fewer",
          "parameters than a sibling function instance of the same routine) is expected to be empty.", ""]
    if census:
        for c in census:
            L.append(f"- function_instance {c['index']} `{c['routine']}` — declares {c['declared']}, "
                     f"missing {c['missing']}")
        L.append("")
    else:
        L += ["No function instance is missing a parameter row.", ""]
    ledgers = summary.get("armLedgers", {})
    if ledgers:
        L += ["", "## Allocation ledger — observed cursor history vs the independently expected sequence",
              "",
              "The OBSERVED column is the `ZKVM_HEAP_POS` write history of the unchanged production ELF",
              "— the allocation ACT, not a self-report. The EXPECTED column is derived without reference",
              "to the binary: the pinned Zig decode order (`allocation_shapes.py`) applied to that arm's",
              "exact fixture bytes, sized by the Row B probe's `--dump-abi` element table. The check is",
              "`cursor' = align_up(cursor, alignment) + size` for each event, at the same ordinal, with",
              "the allocator's returned pointer equal to that aligned base.", ""]
        for name in sorted(ledgers):
            d = ledgers[name]
            L += [f"### arm `{name}` — {len(d['observed'])} allocations, process exit {d['decision']}"
                  + (f", rejected at: {d['rejectedAt']}" if d["rejectedAt"] else ""),
                  "",
                  "| # | routine | element × count | expected size | align | cursor before → after | returned |",
                  "|---:|---|---|---:|---:|---|---|"]
            for o, e in zip(d["observed"], d["expected"]):
                L.append(f"| {e['ordinal']} | `{e['routine']}` | {e['element']} × {e['count']} | "
                         f"{e['size']} | {e['alignment']} | {o['before']} → {o['after']} | "
                         f"{o['returned']} |")
            if len(d["observed"]) != len(d["expected"]):
                L.append(f"| — | **COUNT MISMATCH** | observed {len(d['observed'])} | "
                         f"expected {len(d['expected'])} | | | |")
            L.append("")
    uncovered = [r for r in records if not r["facts"].get("covered")]
    if uncovered:
        L += ["", "## Uncovered function instances (documented gaps, not passes)", ""]
        for r in uncovered:
            reason = DOCUMENTED_UNCOVERED.get(r["routine"], "not exercised by any tested arm")
            L.append(f"- function instance {r['index']} `{r['qualified']}` — {reason}")
    L += ["",
          "Header abbreviations: " + ", ".join(f"{short[n]}={n}" for n in CHECK_NAMES) + ".",
          "",
          "| idx | routine | arm | " + " | ".join(short[n] for n in CHECK_NAMES) + " | gaps |",
          "|---:|---|---|" + "|".join(["---"] * len(CHECK_NAMES)) + "|---|"]
    for r in records:
        cells = " | ".join(sym[r["checks"].get(n)] for n in CHECK_NAMES)
        gap = "; ".join(sorted(f"{short.get(k, k)}: {v}" for k, v in r.get("gaps", {}).items()))
        L.append(f"| {r['index']} | {r['routine']} | {r.get('arm') or '-'} | {cells} | {gap} |")
    return "\n".join(L) + "\n"


def arm_ledger_to_lean(name, d) -> str:
    return ("  { arm := " + _str(name) + f", decision := {d['decision']}, "
            f"inputBytes := {d['inputBytes']}, rejectedAt := {_str(d['rejectedAt'] or '')},\n"
            "    observed := [" + ", ".join(_observed_to_lean(o) for o in d["observed"]) + "],\n"
            "    expected := [" + ", ".join(_expected_to_lean(e) for e in d["expected"]) + "] }")


def emit_lean(records, arm_ledgers) -> str:
    head = [
        "-- GENERATED — do not edit. Regenerated by targets/ssz/zesu/trace/scale_function_instances.py from the",
        "-- UNCHANGED production zesu-ssz ELF under pinned qemu-riscv64. Diagnostic-only evidence;",
        "-- the validation-import guard forbids the theorem graph from importing this.",
        "import BinaryFv.SSZ.Zesu.Validation.ScaleFunctionInstanceTypes",
        "",
        "-- Large generated list literals: raise the elaborator's recursion limit.",
        "set_option maxRecDepth 100000",
        "",
        "namespace BinaryFv.SSZ.Zesu.Validation.GeneratedScaleEvidence",
        "open BinaryFv.SSZ.Zesu.Validation",
        "",
        "/-- The WHOLE-RUN allocation ledger of each arm: the cursor-write history captured from the",
        "unchanged production ELF beside the allocation sequence derived independently of the binary,",
        "from the pinned Zig decode order and the Row B element ABI applied to that arm's exact fixture. -/",
        "def armLedgers : List ArmLedger :=",
    ]
    head.append("[\n" + ",\n".join(arm_ledger_to_lean(n, arm_ledgers[n]) for n in sorted(arm_ledgers))
                + "]")
    head += [
        "",
        "/-- Compact per-function-instance production-ELF evidence paired with the Python oracle's check result,",
        "for every function instance in program.json. Coverage is per function instance; `none` checks are explicit gaps. -/",
        "def allFunctionInstances : List (FunctionInstanceScaleEvidence × ScaleChecks) :=",
    ]
    body = "[\n" + ",\n".join(function_instance_to_lean(r) for r in records) + "]"
    tail = ["", "end BinaryFv.SSZ.Zesu.Validation.GeneratedScaleEvidence", ""]
    return "\n".join(head) + "\n" + body + "\n" + "\n".join(tail)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--qemu", required=True)
    ap.add_argument("--plugin", required=True)
    ap.add_argument("--elf", required=True)
    ap.add_argument("--program", required=True)
    ap.add_argument("--bindings", required=True,
                    help="bindings.json from the extractor: the EFFECTIVE (recovered) Row A table")
    ap.add_argument("--objdump", required=True)
    ap.add_argument("--source", required=True,
                    help="the pinned zesu source tree: the decode order and size constants the "
                         "expected allocation sequence is derived from")
    ap.add_argument("--abi", required=True,
                    help="the Row B probe's --dump-abi: @sizeOf/@alignOf of each allocated element")
    ap.add_argument("--catalog", default=str(HERE / "routine_catalog.json"))
    ap.add_argument("--scratch", required=True)
    # each arm: name=path/to/input.bin ; function instances are assigned to the first arm (in order) that covers them
    ap.add_argument("--arm", action="append", required=True, metavar="NAME=INPUT")
    ap.add_argument("--out-json", required=True)
    ap.add_argument("--out-lean")
    ap.add_argument("--out-report")
    args = ap.parse_args()

    program = json.loads(Path(args.program).read_text())
    function_instances = program["function_instances"]
    catalog = json.loads(Path(args.catalog).read_text())
    scratch = Path(args.scratch)
    scratch.mkdir(parents=True, exist_ok=True)

    # The EFFECTIVE Row A bindings — the recovered table the Lean inventory validates, NOT the raw
    # DWARF rows in program.json (those still carry the 61 `callerProvided` gaps, and validating
    # against them would check a location the compiler never gave).
    btables = json.loads(Path(args.bindings).read_text())
    # A `derived` row's stride lives in the generator's audit table; attach it so the row carries its
    # whole relation (`register`, `stride`, `constant`) where it is evaluated.
    strides = {(d["function_instance"], d["name"]): d["stride"] for d in btables.get("derived", [])}
    bindings_by_function_instance = {}
    for r in btables["effective"]:
        if r["kind"] == "derived":
            r = {**r, "stride": strides[(r["function_instance"], r["name"])]}
        bindings_by_function_instance.setdefault(r["function_instance"], []).append(r)

    # The routine chain of each function instance (short names, outermost first): its inline stack plus its own
    # routine. This is how an independently expected allocation event is attributed to the function instances
    # that own it — an emitted function instance's chain is just its own routine, so `decodeByteListList`
    # claims the events of all four of its call sites.
    function_instance_chain = [
        [s["callerQualified"].split(".")[-1] for s in function_instance["inlineStack"]]
        + [function_instance["qualified"].split(".")[-1]]
        for function_instance in function_instances
    ]

    # The allocation sequence each fixture REQUIRES, derived with no reference to the binary.
    consts, abi = al.load_inputs(args.source, args.abi)

    # The boundary PCs at which the plugin snapshots registers: every declared entry and exit.
    bpcs = sorted(
        {function_instance["entryPc"] for function_instance in function_instances}
        | {
            exit_pc
            for function_instance in function_instances
            for exit_pc in (function_instance.get("exits") or [])
        }
    )
    bpc_file = scratch / "boundary_pcs.txt"
    bpc_file.write_text("\n".join(str(x) for x in bpcs) + "\n")

    # Capture one full-run trace per arm, then parse.
    arm_traces = {}
    for spec in args.arm:
        name, _, ipath = spec.partition("=")
        log = scratch / f"full_{name}.log"
        decision = run_full_trace(args.qemu, args.plugin, args.elf, ipath, log, bpc_file)
        arm_traces[name] = (parse_trace(log), decision, ipath)

    # Per-arm machine context: boundary snapshots by PC, shadow memory (ELF image + replayed stores),
    # and the allocation ledger reconstructed from the cursor's own write history.
    image = osem.load_image(args.elf)
    dyn_pcs = dynamic_transfer_pcs(args.objdump, args.elf)
    _insns, _order = rt.disassemble(args.objdump, args.elf)
    ret_pcs = {pc for pc in _order if _insns[pc][0] in rt.RET}
    call_pcs = {pc for pc in _order if rt.is_call(pc, _insns)}

    # The allocator leaf's return sites: `a0` there is the block the allocator actually handed back, so
    # each cursor event can be paired with the pointer its caller received. Without that, an allocation
    # that bumped the cursor correctly but returned a different block would be invisible.
    alloc_leaf = next(
        i
        for i, function_instance in enumerate(function_instances)
        if function_instance["qualified"] == "raw_allocator.zesu_raw_alloc"
    )
    alloc_ret_pcs = sorted(set(function_instances[alloc_leaf].get("exits") or []) & ret_pcs)

    # Every routine a transfer can land on as a call or TAIL-call target: the emitted function instances and
    # the reachable-but-excluded glue the generator catalogs beside them.
    function_entries = ({function_instance["entryPc"] for function_instance in function_instances
                         if function_instance["kind"] == "emitted"}
                        | {x["entryPc"] for x in program.get("excludedRoutines", [])})

    arm_ctx, arm_ledgers = {}, {}
    for name, ((ex, lo, st, rg), _dec, ipath) in arm_traces.items():
        by_pc = {}
        for (i, pc, r) in rg:
            by_pc.setdefault(pc, []).append((i, pc, r))
        ledger = osem.build_ledger(st, CURSOR_POS[0], CURSOR_POS[1])
        returns = sorted((i, r[10]) for pc in alloc_ret_pcs for (i, _p, r) in by_pc.get(pc, []))
        for e in ledger:
            e["returned"] = next((a0 for (i, a0) in returns if i > e["index"]), None)
        expected = al.expected_allocations(Path(ipath).read_bytes(), consts, abi)
        # The startup write of `ZKVM_HEAP_POS` has no predecessor and allocates nothing; the events
        # that carry a size are the allocations.
        sized = [e for e in ledger if e["size"] is not None]
        arm_ctx[name] = {
            "regsByPc": by_pc,
            "mem": osem.Memory(image, [(i, a, w, v) for (i, _pc, a, w, v, _sp) in st]),
            "ledger": ledger,
            "ledgerInvariants": osem.ledger_invariants(ledger),
            "bindings": bindings_by_function_instance,
            "inputLen": Path(ipath).stat().st_size,
            "armDecision": _dec,
            "expected": expected["events"],
            "functionInstanceChain": function_instance_chain,
            "callPcs": call_pcs,
            "retPcs": ret_pcs,
            "functionEntries": function_entries,
        }
        arm_ledgers[name] = {
            "decision": _dec,
            "inputBytes": Path(ipath).stat().st_size,
            "rejectedAt": expected["rejectedAt"],
            "observed": [{"ordinal": n, "before": e["before"], "after": e["after"],
                          "returned": e["returned"]} for n, e in enumerate(sized)],
            "expected": [{"ordinal": e["ordinal"], "routine": e["routine"], "element": e["element"],
                          "count": e["count"], "size": e["size"], "alignment": e["alignment"]}
                         for e in expected["events"]],
        }
        # The whole-run ordinals ARE the positions in the ALLOCATION sequence, so a per-function-instance slice
        # can be compared against the expected sequence by ordinal. The startup cursor write is not an
        # allocation and carries no ordinal.
        n = 0
        for e in ledger:
            if e["size"] is None:
                e["ordinal"] = None
            else:
                e["ordinal"], n = n, n + 1

    # PCs of each function instance's regions, for the generator's deepest-owner edge attribution.
    def _rpcs(x):
        s = set()
        for r in x["regions"]:
            s |= set(range(r["start"], r["start"] + r["size"], 2))
        return s
    all_rpcs = [_rpcs(x) for x in function_instances]

    records = []
    for idx, function_instance in enumerate(function_instances):
        kids = set()
        for c in function_instance.get("children") or []:
            kids |= all_rpcs[c]
        function_instance = {**function_instance, "index": idx}
        short = function_instance["qualified"].split(".")[-1]
        chosen = None
        for spec in args.arm:
            name = spec.split("=", 1)[0]
            (executed, loads, stores, _rg), _, _ = arm_traces[name]
            ranges = [(r["start"], r["start"] + r["size"]) for r in function_instance["regions"]]
            if any(any(a <= pc < b for a, b in ranges) for pc in executed):
                chosen = name
                break
        if chosen is None:
            facts = reduce_function_instance(
                function_instance, short, catalog, [], [], [], 0, kids, dyn_pcs
            )  # covered=False
        else:
            (executed, loads, stores, _rg), _, ipath = arm_traces[chosen]
            input_len = Path(ipath).stat().st_size
            facts = reduce_function_instance(
                function_instance, short, catalog, executed, loads, stores, input_len, kids,
                dyn_pcs, arm_ctx[chosen]
            )
        checks, gaps = evaluate_facts(facts)
        records.append({
            "index": idx, "qualified": function_instance["qualified"], "routine": short,
            "arm": chosen, "checks": checks, "gaps": gaps, "facts": facts,
        })

    # MISSING-PARAMETER CENSUS — kept as a REGRESSION guard. The extractor now takes each function instance's
    # signature from its DWARF abstract-origin DIE, so a parameter the optimizer dropped from the
    # concrete instance is still a row; this census (an function instance declaring fewer parameters than a
    # sibling function instance of the same routine) should stay empty. If it ever fills up again, the binding
    # checks would quietly report a gap instead of a missing obligation, which is what it exists to
    # surface.
    routine_params = {}
    for idx, function_instance in enumerate(function_instances):
        sh = function_instance["qualified"].split(".")[-1]
        routine_params.setdefault(sh, set()).update(
            r["name"] for r in bindings_by_function_instance.get(idx, []))
    census = []
    for idx, function_instance in enumerate(function_instances):
        sh = function_instance["qualified"].split(".")[-1]
        have = {r["name"] for r in bindings_by_function_instance.get(idx, [])}
        if not have:
            continue                       # genuinely paramless function instances are named by Row A
        missing = sorted(routine_params[sh] - have)
        if missing:
            census.append({"index": idx, "routine": sh, "declared": sorted(have),
                           "missing": missing})

    # Aggregate coverage.
    passed = {n: sum(1 for r in records if r["checks"].get(n) is True) for n in CHECK_NAMES}
    failed = {n: sum(1 for r in records if r["checks"].get(n) is False) for n in CHECK_NAMES}
    gapped = {n: sum(1 for r in records if r["checks"].get(n) is None) for n in CHECK_NAMES}
    summary = {
        "function_instances": len(function_instances),
        "covered": sum(1 for r in records if r["facts"].get("covered")),
        "byCheck": {n: {"pass": passed[n], "fail": failed[n], "gap": gapped[n]} for n in CHECK_NAMES},
        "arms": {name: {"decision": arm_traces[name][1], "input": arm_traces[name][2],
                        "ledger": arm_ctx[name]["ledgerInvariants"]} for name in arm_traces},
        "armLedgers": arm_ledgers,
        "armLedgersAgree": {name: arm_ledger_holds(d) for name, d in arm_ledgers.items()},
    }
    summary["missingParameterRows"] = {
        "function_instances": len(census),
        "note": "function instances whose effective Row A table omits a parameter that OTHER function instances of "
                "the same source routine declare. Expected to be empty: the extractor takes each "
                "signature from the function instance's DWARF abstract-origin DIE, so a parameter the "
                "optimizer dropped is still a row.",
        "rows": census,
    }
    out = {"summary": summary, "function_instances": records, "ledger": {
        name: arm_ctx[name]["ledger"] for name in arm_ctx}}
    Path(args.out_json).write_text(json.dumps(out, indent=1, sort_keys=True) + "\n")
    if args.out_lean:
        Path(args.out_lean).write_text(emit_lean(records, arm_ledgers))
    if args.out_report:
        Path(args.out_report).write_text(emit_report(records, summary))

    # Human-readable digest to stderr.
    any_fail = sum(failed.values())
    print(f"function_instances={len(function_instances)} covered={summary['covered']}", file=sys.stderr)
    for n in CHECK_NAMES:
        print(f"  {n:22s} pass={passed[n]:3d} fail={failed[n]:3d} gap={gapped[n]:3d}", file=sys.stderr)
    for name, agrees in sorted(summary["armLedgersAgree"].items()):
        d = arm_ledgers[name]
        print(f"  ledger[{name}] observed={len(d['observed'])} expected={len(d['expected'])} "
              f"agree={agrees}", file=sys.stderr)
    bad_ledger = sorted(n for n, ok in summary["armLedgersAgree"].items() if not ok)
    if any_fail:
        print("FAILURES:", file=sys.stderr)
        for r in records:
            bad = [n for n in CHECK_NAMES if r["checks"].get(n) is False]
            if bad:
                print(f"  function_instances {r['index']:3d} {r['qualified']:55s} {bad}", file=sys.stderr)
    if bad_ledger:
        print(f"WHOLE-RUN LEDGER MISMATCH on arms {bad_ledger}", file=sys.stderr)
    return 1 if (any_fail or bad_ledger) else 0


if __name__ == "__main__":
    raise SystemExit(main())
