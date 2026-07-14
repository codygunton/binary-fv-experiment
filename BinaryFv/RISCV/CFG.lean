import BinaryFv.RISCV.Decode

namespace BinaryFv.RISCV

open LeanRV64DExecutable.Functions

def signedTarget? {width : Nat} (address : Nat) (offset : BitVec width) : Option Nat :=
  let target := Int.ofNat address + offset.toInt
  if target < 0 then none else some target.toNat

def auipcJalrTarget? (address : Nat) (upper : BitVec 20) (lower : BitVec 12) : Option Nat :=
  let offset := (upper ++ (0 : BitVec 12)).toInt + lower.toInt
  let target := Int.ofNat address + offset
  if target < 0 then none else some (target.toNat - target.toNat % 2)

def zeroRegister : regidx := .Regidx 0#5

def returnRegister : regidx := .Regidx 1#5

/-- A decoded control transfer; unresolved `JALR` targets remain explicit obligations. -/
inductive ControlTransfer where
  | fallthrough (next : Nat)
  | conditional (taken : Option Nat) (notTaken : Nat)
  | jump (target : Option Nat)
  | call (target : Option Nat) (returnAddress : Nat)
  | indirect
  | indirectCall (returnAddress : Nat)
  | return_
  | terminal
deriving Repr

def resolvedJalrTarget? (previous : Option DecodedWord) (current : DecodedWord) : Option Nat :=
  match previous, current.instruction with
  | some { encoded := { address, .. }, instruction := .UTYPE (upper, destination, .AUIPC) },
      .JALR (lower, source, _) =>
    if address + 4 == current.encoded.address && destination == source then
      auipcJalrTarget? address upper lower
    else
      none
  | _, _ => none

def DecodedWord.controlTransfer (previous : Option DecodedWord) (decoded : DecodedWord) :
    ControlTransfer :=
  let address := decoded.encoded.address
  match decoded.instruction with
  | .JAL (immediate, destination) =>
    if destination == zeroRegister then .jump (signedTarget? address immediate)
    else .call (signedTarget? address immediate) (address + 4)
  | .JALR (immediate, source, destination) =>
    if immediate == (0 : BitVec 12) && source == returnRegister && destination == zeroRegister then
      .return_
    else
      match resolvedJalrTarget? previous decoded with
      | some target =>
        if destination == zeroRegister then .jump (some target)
        else .call (some target) (address + 4)
      | none =>
        if destination == zeroRegister then .indirect else .indirectCall (address + 4)
  | .BTYPE (immediate, _, _, _) => .conditional (signedTarget? address immediate) (address + 4)
  | .ECALL _ | .MRET _ | .SRET _ | .EBREAK _ | .WFI _ => .terminal
  | _ => .fallthrough (address + 4)

def ControlTransfer.directTargets : ControlTransfer → Array Nat
  | .fallthrough next => #[next]
  | .conditional (some taken) notTaken => #[taken, notTaken]
  | .conditional none notTaken => #[notTaken]
  | .jump (some target) => #[target]
  | .jump none | .indirect | .indirectCall _ | .return_ | .terminal => #[]
  | .call (some target) returnAddress => #[target, returnAddress]
  | .call none returnAddress => #[returnAddress]

structure ControlFlowNode where
  word : DecodedWord
  transfer : ControlTransfer
deriving Repr

def controlFlowNodes (words : Array DecodedWord) : Array ControlFlowNode :=
  words.mapIdx fun index word =>
    let previous := if index == 0 then none else words[index - 1]?
    { word, transfer := word.controlTransfer previous }

structure DirectControlEdge where
  source : Nat
  target : Nat
deriving Repr

def ControlFlowNode.directEdges (node : ControlFlowNode) : Array DirectControlEdge :=
  node.transfer.directTargets.map fun target => { source := node.word.encoded.address, target }

def directControlEdges (nodes : Array ControlFlowNode) : Array DirectControlEdge :=
  nodes.flatMap ControlFlowNode.directEdges

def hasControlFlowAddress (nodes : Array ControlFlowNode) (address : Nat) : Bool :=
  nodes.any fun node => node.word.encoded.address == address

def directTargetsPresent (nodes : Array ControlFlowNode) : Bool :=
  (directControlEdges nodes).all fun edge => hasControlFlowAddress nodes edge.target

def ControlFlowNodeAt? (nodes : Array ControlFlowNode) (address : Nat) :
    Option ControlFlowNode :=
  nodes.toList.find? fun node => node.word.encoded.address == address

def directSuccessorsAt (nodes : Array ControlFlowNode) (address : Nat) : Array Nat :=
  match ControlFlowNodeAt? nodes address with
  | some node => node.transfer.directTargets
  | none => #[]

def appendKnownAddresses (nodes : Array ControlFlowNode) (known candidates : Array Nat) : Array Nat :=
  candidates.foldl (fun accumulated candidate =>
    if hasControlFlowAddress nodes candidate &&
        !(accumulated.any fun address => address == candidate) then
      accumulated.push candidate
    else
      accumulated) known

def expandDirectReachability (nodes : Array ControlFlowNode) (known : Array Nat) : Array Nat :=
  known.foldl (fun accumulated address =>
    appendKnownAddresses nodes accumulated (directSuccessorsAt nodes address)) known

/-- Finite reachability over decoded direct/conditional/call-summary edges only. -/
def directReachable (nodes : Array ControlFlowNode) (entry : Nat) : Array Nat :=
  let rec loop : Nat → Array Nat → Array Nat
    | 0, known => known
    | fuel + 1, known =>
      let expanded := expandDirectReachability nodes known
      if expanded.size == known.size then known else loop fuel expanded
  if hasControlFlowAddress nodes entry then loop (nodes.size + 1) #[entry] else #[]

def ControlFlowNode.indirectTarget (node : ControlFlowNode) : Bool :=
  match node.transfer with
  | .indirect => true
  | _ => false

def ControlFlowNode.returnSite (node : ControlFlowNode) : Bool :=
  match node.transfer with
  | .return_ => true
  | _ => false

end BinaryFv.RISCV
