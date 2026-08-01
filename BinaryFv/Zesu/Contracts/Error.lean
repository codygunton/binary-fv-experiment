import SszBridge.Core

namespace BinaryFv.Zesu.Contracts

open SizzLean.Spec

/-!
# The decoder's semantic error boundary

The pinned Zig decoder's error set is
`DecodeError = std.mem.Allocator.Error || error{InvalidSsz, UnknownFork}` — exactly three errors.
That is the boundary every source function contract normalizes to.

The name is `SszDecodeError`, not `DecodeError`, because `BinaryFv.RiscV.DecodeError` already exists
and means an ELF word-decode failure.

Normalizing the oracle's richer taxonomies onto these three is *lossy*, and deliberately so: the Zig
boundary genuinely cannot distinguish an offset error from a trailing-bytes error. The audit
recorded on issue #39 turned up a case that makes the direction of that lossiness matter — Zig
raises `UnknownFork` before decoding a fork's children while the oracle checks `fork > 20` only
after a complete canonical decode, so the two can disagree about *which* error a malformed
`fork = 21` payload produces. They never disagree about rejection. Contracts must therefore state
agreement of the observable outcome and must not claim the error constructors match.
-/

/-- The Zig decoder's complete error set. -/
inductive SszDecodeError where
  | invalidSsz
  | unknownFork
  | outOfMemory
deriving DecidableEq, Repr, Inhabited

/-- Every SizzLean structural decode failure is `InvalidSsz` at the Zig boundary.

This is total and constant on purpose: `SSZError`'s six constructors all describe a malformed SSZ
body, and the Zig decoder has no way to report the distinction. -/
def sszToDecodeError : SSZError → SszDecodeError := fun _ => .invalidSsz

/-- The bridge's error taxonomy at the Zig boundary.

`v3Quarantined` has no Zig counterpart at all — the Zig decoder has no V3 concept. It maps to
`invalidSsz` because the audit established that a V3-shaped buffer can never be a canonical V4 one
(`hasV3PayloadShape` demands the u32 at execution-payload offset 436 be `528`, while a valid V4
payload demands `540`), so the two implementations still agree on rejection. -/
def bridgeToDecodeError : SszBridge.BridgeError → SszDecodeError
  | .tooLarge => .invalidSsz
  | .tooShort => .invalidSsz
  | .badSchema => .invalidSsz
  | .unknownFork => .unknownFork
  | .v3Quarantined => .invalidSsz
  | .ssz error => sszToDecodeError error

/-- Lift an `Option`-valued primitive reader into the decoder's error boundary.

The Zig readers all funnel through `bytesAt`, which returns `error.InvalidSsz` exactly when
`offset > data.len or len > data.len - offset` — precisely when the SizzLean reader returns `none`.
-/
def Option.toDecodeResult {α : Type} : Option α → Except SszDecodeError α
  | some value => .ok value
  | none => .error .invalidSsz

/-- Whether a decode outcome is observable as acceptance.

The root theorem compares only acceptance versus rejection, so this is the granularity at which the
binary and the oracle are claimed to agree. -/
def isAccepted {α : Type} : Except SszDecodeError α → Bool
  | .ok _ => true
  | .error _ => false

end BinaryFv.Zesu.Contracts
