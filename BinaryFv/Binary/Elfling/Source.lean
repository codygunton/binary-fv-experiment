namespace BinaryFv.Binary.Elfling

/-!
# Address-free source identity

Every name in this module is derived from pinned source text and debug information, never from a
linked address. That is the whole point: handwritten contracts are indexed by `InstanceId`, so
relinking the binary at a different text base must not touch a single proof.

The address-bearing side of an Elfling program lives in `BinaryFv.Binary.Elfling.Instance`, which is
emitted by the generator. Nothing in this module may mention an instruction word, a program counter,
or a symbol.
-/

/-- A pinned source file: its path as recorded in debug information, plus the content hash the
generator checked it against. Two builds that disagree on `contentHash` are different programs. -/
structure SourceFile where
  path : String
  contentHash : String
deriving DecidableEq, Repr, Hashable, Inhabited

/-- A one-based line/column position within a `SourceFile`. -/
structure SourceSpan where
  line : Nat
  column : Nat
deriving DecidableEq, Repr, Hashable, Inhabited

/-- A declaration in pinned source: where it is written and what it is called.

`qualifiedName` is the fully qualified name as the compiler records it, so two same-named routines
in different modules stay distinct. -/
structure SourceDeclaration where
  file : SourceFile
  qualifiedName : String
  span : SourceSpan
deriving DecidableEq, Repr, Hashable, Inhabited

/--
A stable, source-derived function identifier.

`specialization` carries the compile-time arguments that distinguish separately-emitted
instantiations of one generic declaration. This is not decoration: a routine such as
`readArray(comptime N, data, offset)` is a *different* function in the binary for each `N`, and
collapsing those instantiations would silently merge contracts that state different things.
-/
structure FunctionId where
  declaration : SourceDeclaration
  specialization : Array String
deriving DecidableEq, Repr, Inhabited

/-- One inlining step: the declaration that was inlined into, and the call site inside it. -/
structure InlineSite where
  caller : SourceDeclaration
  callSite : SourceSpan
deriving DecidableEq, Repr, Inhabited

/--
The address-free identity of one emitted or inlined occurrence of a function.

`inlineStack` is ordered outermost-first, so the empty stack marks a separately emitted function and
a nonempty stack names the exact nesting the debug information recorded.

**This is the only thing a handwritten contract may mention.** Ranges, symbols, program counters,
and instruction words belong to `FunctionInstance`, which the generator emits. Because identity is
`(function, inlineStack)` and nothing else, relinking at a different text base leaves every
`InstanceId` — and therefore every contract — unchanged.
-/
structure InstanceId where
  function : FunctionId
  inlineStack : List InlineSite
deriving DecidableEq, Repr, Inhabited

namespace InstanceId

/-- The identity of a separately emitted (non-inlined) occurrence. -/
def emitted (function : FunctionId) : InstanceId :=
  { function := function, inlineStack := [] }

/-- How deeply this occurrence was inlined; `0` for a separately emitted function. -/
def inlineDepth (id : InstanceId) : Nat :=
  id.inlineStack.length

def isInlined (id : InstanceId) : Bool :=
  !id.inlineStack.isEmpty

/-- The declaration this occurrence was most immediately inlined into, if any. -/
def immediateCaller? (id : InstanceId) : Option SourceDeclaration :=
  id.inlineStack.getLast?.map InlineSite.caller

/-- `outer` is an inline-stack prefix of `inner`, i.e. `inner` is nested inside `outer`.

This is the *source-level* nesting test. It says nothing about addresses; range containment is
checked separately against the canonical ELF. -/
def nestedIn (inner outer : InstanceId) : Prop :=
  outer.inlineStack.isPrefixOf inner.inlineStack ∧ inner.inlineStack.length > outer.inlineStack.length

end InstanceId

end BinaryFv.Binary.Elfling
