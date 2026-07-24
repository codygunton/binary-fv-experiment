# Elfling proof layer

Elfling turns a compiled RISC-V binary back into units that can carry readable, function-shaped
proofs. The compiler may emit one source function as a callable body, copy it into several callers,
split its instructions into separate address ranges, or do all three. Elfling records those compiled
appearances without pretending that compiler output still has a one-function/one-address-range shape.

## The basic model

An **occurrence** is one compiled appearance of a source function. For example, if `readU64` remains
as a callable function and is also inlined twice into `decodeHeader`, the binary contains three
`readU64` occurrences. They share the same source-level behavior, but have different instructions,
addresses, inputs, and result locations.

A `FunctionInstance` is the static description of one occurrence: its address ranges, entry and exit
PCs, calls, inlined children, and provenance. `Instance.lean` defines that handwritten data model; it
is not generated. The extractor creates values of those types for a particular binary, and separate
checks validate those values before proofs use them.

A `FunctionTrace` is different: it is one dynamic machine execution through an occurrence. It
relates a starting Sail state to an ending Sail state and records exactly how many instructions were
retired. One static `FunctionInstance` can describe many different traces, because the same code can
run on many inputs.

```text
source functions
      │ compile
      ▼
concrete binary instructions
      │ extract and validate
      ▼
FunctionInstance values                 static: where each compiled occurrence lives
      │
      ├── shared RoutineSpec             what every occurrence of the source routine means
      └── OccurrenceBinding              where this occurrence gets arguments and leaves results
                    │ prove
                    ▼
              ScopedTrace                local execution, using child summaries at crossings
                    │ expand checked crossings
                    ▼
              FunctionTrace              ordinary instruction-by-instruction execution
```

The crossings in that diagram are the **boundaries**. A parent occurrence reaches a separately
emitted child by a call edge, or enters and leaves an inlined child through ordinary control-flow
edges. `Boundary.lean` validates those ownership-crossing edges and defines how a child summary is
spliced into the parent's trace without omitting the call, return, or outgoing instruction.

## Reading order

1. [`BinaryFv/Binary/Elfling/Instance.lean`](../../Binary/Elfling/Instance.lean) defines the static
   vocabulary: occurrence identities, address ranges, entries, exits, children, calls, and programs.
2. [`FunctionTrace.lean`](FunctionTrace.lean) defines a dynamic execution confined to a supplied
   address set until it reaches a supplied exit.
3. [`Contract.lean`](Contract.lean) gives every source routine one shared meaning and every compiled
   occurrence its own register-and-memory binding.
4. [`Boundary.lean`](Boundary.lean) validates crossings between occurrences and expands a parent
   proof that uses child summaries into one ordinary machine trace.
5. [`BoundaryTests.lean`](BoundaryTests.lean) shows which valid crossings compose and which malformed
   crossings are rejected.

The generated files and extracted addresses are evidence, not trusted axioms. Boolean checks and
Lean theorems in this layer reject stale edges, invented boundaries, missing parameter locations,
and inconsistent step counts.
