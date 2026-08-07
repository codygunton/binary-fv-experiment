namespace BinaryFv.Binary.Elfling

/-!
# Address-free source identity

Every name in this module is derived from pinned source text and debug information, never from a
linked address. That is the whole point: handwritten contracts are indexed by `FunctionInstanceId`, so
relinking the binary at a different text base must not touch a single proof.

The handwritten types for the address-bearing side live in
`BinaryFv.Binary.Elfling.FunctionInstance`. The generator creates concrete values of those types for
one compiled binary. Nothing in this module may mention an instruction word, a program counter, or a
symbol.
-/

/-- A pinned source file, identified by its path as recorded in debug information.

This is a *stable identity* component: it carries no content hash. The content hash is validated
source *provenance* (`DeclarationProvenance`), kept separate so a generated identity can match the
catalog by name without depending on a hash the handwritten catalog cannot compute. -/
structure SourceFile where
  path : String
deriving DecidableEq, Repr, Hashable, Inhabited

/-- A one-based line/column position within a `SourceFile`. -/
structure SourceSpan where
  line : Nat
  column : Nat
deriving DecidableEq, Repr, Hashable, Inhabited

/-- A declaration in pinned source: which file it lives in and what it is called.

`qualifiedName` is the fully qualified name as the compiler records it, so two same-named source functions
in different modules stay distinct. This is *stable identity* — it deliberately omits the
declaration's line/column, which is validated provenance (`DeclarationProvenance`), not a matching
key: a source edit that shifts the declaration must not change what the source function *is*. -/
structure SourceDeclaration where
  file : SourceFile
  qualifiedName : String
deriving DecidableEq, Repr, Hashable, Inhabited

/-- Validated source provenance for a declaration: the pinned source file's content hash and the
declaration's one-based location.

This is checked against the pinned source during extraction. It is deliberately **not** part of
`FunctionId`: matching a generated function instance to a catalog entry uses stable identity (file path,
qualified name, specialization) only, so a wrong or absent hash makes provenance validation fail
rather than silently breaking identity matching. Source pinning is thereby preserved as a separate
validated obligation, not smuggled into the matching key. -/
structure DeclarationProvenance where
  sourceFileHash : String
  declSpan : SourceSpan
deriving DecidableEq, Repr, Inhabited

/--
A stable, source-derived function identifier.

`specialization` carries the compile-time arguments that distinguish separately-emitted
instantiations of one generic declaration. This is not decoration: a source function such as
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
The address-free identity of one emitted or inlined function instance of a function.

`inlineStack` is ordered outermost-first, so the empty stack marks a separately emitted function and
a nonempty stack names the exact nesting the debug information recorded.

**This is the only thing a handwritten contract may mention.** Ranges, symbols, program counters,
and instruction words belong to `FunctionInstance`, which the generator emits. Because identity is
`(function, inlineStack)` and nothing else, relinking at a different text base leaves every
`FunctionInstanceId` — and therefore every contract — unchanged.
-/
structure FunctionInstanceId where
  function : FunctionId
  inlineStack : List InlineSite
deriving DecidableEq, Repr, Inhabited

namespace FunctionInstanceId

/-- The identity of a separately emitted (non-inlined) function instance. -/
def emitted (function : FunctionId) : FunctionInstanceId :=
  { function := function, inlineStack := [] }

/-- How deeply this function instance was inlined; `0` for a separately emitted function. -/
def inlineDepth (id : FunctionInstanceId) : Nat :=
  id.inlineStack.length

def isInlined (id : FunctionInstanceId) : Bool :=
  !id.inlineStack.isEmpty

/-- The declaration this function instance was most immediately inlined into, if any. -/
def immediateCaller? (id : FunctionInstanceId) : Option SourceDeclaration :=
  id.inlineStack.getLast?.map InlineSite.caller

/-- `outer` is an inline-stack prefix of `inner`, i.e. `inner` is nested inside `outer`.

This is the *source-level* nesting test. It says nothing about addresses; range containment is
checked separately against the canonical ELF. -/
def nestedIn (inner outer : FunctionInstanceId) : Prop :=
  outer.inlineStack.isPrefixOf inner.inlineStack ∧ inner.inlineStack.length > outer.inlineStack.length

end FunctionInstanceId

end BinaryFv.Binary.Elfling
