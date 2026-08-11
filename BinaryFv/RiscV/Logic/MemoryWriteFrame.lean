import BinaryFv.RiscV.Model.State

/-! Target-independent memory regions and write-frame composition. -/

namespace BinaryFv.RiscV

abbrev Region := Nat → Prop

def Region.union (r1 r2 : Region) : Region := fun address => r1 address ∨ r2 address

def Region.iUnion (regions : List Region) : Region :=
  fun address => ∃ region ∈ regions, region address

theorem Region.mem_iUnion {regions : List Region} {region : Region} {address : Nat}
    (member : region ∈ regions) (inside : region address) : Region.iUnion regions address :=
  ⟨region, member, inside⟩

def byteRange (base size : Nat) : Region :=
  fun address => base ≤ address ∧ address < base + size

def interval (before after : Nat) : Region :=
  fun address => before ≤ address ∧ address < after

def WritesOnlyWithin (owned : Region) (before after : State) : Prop :=
  ∀ address, ¬ owned address → after.mem.get? address = before.mem.get? address

theorem WritesOnlyWithin.trans_same {owned : Region} {s1 s2 s3 : State}
    (first : WritesOnlyWithin owned s1 s2) (second : WritesOnlyWithin owned s2 s3) :
    WritesOnlyWithin owned s1 s3 :=
  fun address h => (second address h).trans (first address h)

theorem WritesOnlyWithin.mono {owned wider : Region} {s1 s2 : State}
    (sub : ∀ address, owned address → wider address)
    (confined : WritesOnlyWithin owned s1 s2) : WritesOnlyWithin wider s1 s2 :=
  fun address h => confined address (fun howned => h (sub address howned))

end BinaryFv.RiscV
