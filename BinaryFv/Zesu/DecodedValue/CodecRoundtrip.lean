import BinaryFv.Zesu.DecodedValue.Encoder
import BinaryFv.Zesu.DecodedValue.Representation

/-! Proof that the observation parser accepts the exact bytes emitted by the endpoint encoder. -/

namespace BinaryFv.Zesu

private theorem mod_mul_decomp (a b c : Nat) (hb : 0 < b) (hc : 0 < c) :
    a % (b * c) = a % b + b * ((a / b) % c) := by
  have hab : a = a % b + b * (a / b) := (Nat.mod_add_div a b).symm
  have hbc : a / b = (a / b) % c + c * (a / b / c) :=
    (Nat.mod_add_div (a / b) c).symm
  have rhs_lt : a % b + b * ((a / b) % c) < b * c := by
    calc
      a % b + b * ((a / b) % c) < b + b * ((a / b) % c) :=
        Nat.add_lt_add_right (Nat.mod_lt a hb) _
      _ = b * (((a / b) % c) + 1) := by simp [Nat.mul_add, Nat.add_comm]
      _ ≤ b * c := Nat.mul_le_mul_left b (by have := Nat.mod_lt (a / b) hc; omega)
  have ha : a = (a % b + b * ((a / b) % c)) + (b * c) * (a / b / c) := by
    calc
      a = a % b + b * (a / b) := hab
      _ = a % b + b * ((a / b) % c + c * (a / b / c)) :=
        congrArg (fun q => a % b + b * q) hbc
      _ = (a % b + b * ((a / b) % c)) + (b * c) * (a / b / c) := by
        rw [Nat.mul_add]
        ac_rfl
  calc
    a % (b * c) =
        ((a % b + b * ((a / b) % c)) + (b * c) * (a / b / c)) % (b * c) :=
      congrArg (fun value => value % (b * c)) ha
    _ = (a % b + b * ((a / b) % c)) % (b * c) := by
      rw [Nat.add_mul_mod_self_left]
    _ = a % b + b * ((a / b) % c) := Nat.mod_eq_of_lt rhs_lt

private theorem littleEndian_encodeNatLE (width value : Nat) :
    littleEndian (encodeNatLE width value).toList = value % 256 ^ width := by
  induction width generalizing value with
  | zero => exact (Nat.mod_one value).symm
  | succ width ih =>
      rw [show encodeNatLE (width + 1) value =
        #[UInt8.ofNat value] ++ encodeNatLE width (value / 256) by rfl]
      rw [Array.toList_append]
      change value % 256 + 256 * littleEndian (encodeNatLE width (value / 256)).toList =
        value % (256 ^ (width + 1))
      rw [ih, Nat.pow_succ, Nat.mul_comm]
      simpa [Nat.mul_comm] using
        (mod_mul_decomp value 256 (256 ^ width) (by decide) (Nat.pow_pos (by decide))).symm

private theorem encodeNatLE_size (width value : Nat) : (encodeNatLE width value).size = width := by
  induction width generalizing value with
  | zero => rfl
  | succ width ih => simp [encodeNatLE, ih, Nat.add_comm]

private theorem take_middle (pre bytes suffix : Array UInt8) :
    take (pre ++ (bytes ++ suffix)) bytes.size pre.size =
      some (bytes, pre.size + bytes.size) := by
  unfold take
  rw [if_pos]
  · rw [show (pre ++ (bytes ++ suffix)).extract pre.size (pre.size + bytes.size) = bytes by
      calc
        (pre ++ (bytes ++ suffix)).extract pre.size (pre.size + bytes.size) =
            (bytes ++ suffix).extract 0 bytes.size := by
          simpa only [Array.size_append, Nat.add_assoc] using
            (Array.extract_append_right (as := pre) (bs := bytes ++ suffix)
              (i := bytes.size))
        _ = bytes := by simpa using
          (Array.extract_append_left (as := bytes) (bs := suffix))]
  · simp [Array.size_append]

private theorem unsigned_of_take {input : Array UInt8} {width position next : Nat}
    {result : Array UInt8} (h : take input width position = some (result, next)) :
    unsigned input width position = some (littleEndian result.toList, next) := by
  unfold unsigned
  change (take input width position).bind
    (fun pair => some (littleEndian pair.1.toList, pair.2)) = _
  rw [h]
  rfl

private theorem unsigned_encodeNatLE (width value : Nat) (fits : value < 256 ^ width)
    (pre suffix : Array UInt8) :
    unsigned (pre ++ (encodeNatLE width value ++ suffix)) width pre.size =
      some (value, pre.size + width) := by
  have middle := take_middle pre (encodeNatLE width value) suffix
  rw [encodeNatLE_size] at middle
  rw [unsigned_of_take middle, littleEndian_encodeNatLE, Nat.mod_eq_of_lt fits]

private theorem u64_encodeNatLE (value : Nat) (fits : value < 2 ^ 64)
    (pre suffix : Array UInt8) :
    u64 (pre ++ (encodeNatLE 8 value ++ suffix)) pre.size = some (value, pre.size + 8) := by
  apply unsigned_encodeNatLE
  simpa only [show 256 ^ 8 = 2 ^ 64 by native_decide] using fits

private theorem bytes_of_u64_take {input result : Array UInt8}
    {position count middle finish : Nat}
    (countRead : u64 input position = some (count, middle))
    (dataRead : take input count middle = some (result, finish)) :
    bytes input position = some (result, finish) := by
  unfold bytes
  change (u64 input position).bind (fun pair => take input pair.1 pair.2) = _
  rw [countRead]
  exact dataRead

private theorem bytes_encode (value pre suffix : Array UInt8) (fits : value.size < 2 ^ 64) :
    bytes (pre ++ (encodeBytes value ++ suffix)) pre.size =
      some (value, pre.size + (encodeBytes value).size) := by
  let input := pre ++ (encodeBytes value ++ suffix)
  have inputEq : input = pre ++ (encodeNatLE 8 value.size ++ (value ++ suffix)) := by
    simp [input, encodeBytes, Array.append_assoc]
  have countRead : u64 input pre.size = some (value.size, pre.size + 8) := by
    rw [inputEq]
    exact u64_encodeNatLE value.size fits pre (value ++ suffix)
  have dataRead : take input value.size (pre.size + 8) =
      some (value, pre.size + 8 + value.size) := by
    rw [inputEq]
    have middle := take_middle (pre ++ encodeNatLE 8 value.size) value suffix
    simpa [Array.size_append, encodeNatLE_size, Nat.add_assoc] using middle
  simpa [input, encodeBytes, Array.size_append, encodeNatLE_size, Nat.add_assoc] using
    bytes_of_u64_take countRead dataRead

private def ParserEncodes (parse : Array UInt8 → Parser α) (encode : α → Array UInt8)
    (valid : α → Prop) : Prop :=
  ∀ value, valid value → ∀ pre suffix,
    parse (pre ++ (encode value ++ suffix)) pre.size =
      some (value, pre.size + (encode value).size)

private theorem parseManyCount_succ_of {value : Parser α} {count position middle finish : Nat}
    {head : α} {tail : Array α}
    (headRead : value position = some (head, middle))
    (tailRead : parseManyCount value count middle = some (tail, finish)) :
    parseManyCount value (count + 1) position = some (#[head] ++ tail, finish) := by
  unfold parseManyCount
  change (value position).bind (fun first =>
    (parseManyCount value count first.2).bind (fun rest =>
      some (#[first.1] ++ rest.1, rest.2))) = _
  rw [headRead]
  change (parseManyCount value count middle).bind
    (fun rest => some (#[head] ++ rest.1, rest.2)) = _
  rw [tailRead]
  rfl

private theorem parseManyCount_encode
    {parse : Array UInt8 → Parser α} {encode : α → Array UInt8} {valid : α → Prop}
    (item : ParserEncodes parse encode valid) (values : List α)
    (allValid : ∀ value ∈ values, valid value) (pre suffix : Array UInt8) :
    let encoded := encodeManyValues encode values
    let input := pre ++ (encoded ++ suffix)
    parseManyCount (parse input) values.length pre.size =
      some (values.toArray, pre.size + encoded.size) := by
  induction values generalizing pre with
  | nil => rfl
  | cons head tail ih =>
      simp only [encodeManyValues, List.length_cons]
      let tailBytes := encodeManyValues encode tail
      let input := pre ++ (encode head ++ (tailBytes ++ suffix))
      have headRead : parse input pre.size = some (head, pre.size + (encode head).size) := by
        exact item head (allValid head (by simp)) pre (tailBytes ++ suffix)
      have tailRead : parseManyCount (parse input) tail.length
          (pre.size + (encode head).size) =
          some (tail.toArray,
            pre.size + (encode head).size + tailBytes.size) := by
        have recursive := ih (fun value member => allValid value (by simp [member]))
          (pre ++ encode head)
        simpa only [input, tailBytes, Array.size_append, Array.append_assoc, Nat.add_assoc] using
          recursive
      have combined := parseManyCount_succ_of headRead tailRead
      rw [List.toArray_cons]
      simpa [input, tailBytes, Array.size_append, Array.append_assoc, Nat.add_assoc] using combined

private theorem many_encode
    {parse : Array UInt8 → Parser α} {encode : α → Array UInt8} {valid : α → Prop}
    (item : ParserEncodes parse encode valid) (values : Array α)
    (allValid : ∀ index (bound : index < values.size), valid values[index])
    (pre suffix : Array UInt8) (countFits : values.size < 2 ^ 64) :
    many (pre ++ (encodeMany encode values ++ suffix))
        (parse (pre ++ (encodeMany encode values ++ suffix))) pre.size =
      some (values, pre.size + (encodeMany encode values).size) := by
  let list := values.toList
  have listValid : ∀ value ∈ list, valid value := by
    intro value member
    have arrayMember := Array.mem_toList_iff.mp member
    obtain ⟨index, bound, valueEq⟩ := Array.mem_iff_getElem.mp arrayMember
    rw [← valueEq]
    exact allValid index bound
  let input := pre ++ (encodeMany encode values ++ suffix)
  have inputEq : input = pre ++
      (encodeNatLE 8 values.size ++ (encodeManyValues encode list ++ suffix)) := by
    simp [input, encodeMany, list, Array.append_assoc]
  have countRead : u64 input pre.size = some (values.size, pre.size + 8) := by
    rw [inputEq]
    exact u64_encodeNatLE values.size countFits pre (encodeManyValues encode list ++ suffix)
  have valuesRead : parseManyCount (parse input) list.length (pre.size + 8) =
      some (values, pre.size + 8 + (encodeManyValues encode list).size) := by
    have parsed := parseManyCount_encode item list listValid
      (pre ++ encodeNatLE 8 values.size) suffix
    simpa [inputEq, list, encodeNatLE_size, Array.size_append, Array.append_assoc,
      Nat.add_assoc] using parsed
  unfold many
  change (u64 input pre.size).bind (fun count =>
    parseManyCount (parse input) count.1 count.2) = _
  rw [countRead]
  simpa [input, encodeMany, list, encodeNatLE_size, Array.size_append, Nat.add_assoc] using
    valuesRead

private theorem optional_none_of_byte {input : Array UInt8} {position finish : Nat}
    {value : Parser α} (tag : byte input position = some (0, finish)) :
    optional input value position = some (none, finish) := by
  unfold optional
  change StateT.run (byte input >>= fun tagValue => match tagValue with
    | 0 => pure none
    | 1 => do pure (some (← value))
    | _ => failure) position = _
  rw [StateT.run_bind]
  have tag' : StateT.run (byte input) position = some (0, finish) := tag
  rw [tag']
  rfl

private theorem optional_some_of_byte {input : Array UInt8} {position middle finish : Nat}
    {value : Parser α} {result : α} (tag : byte input position = some (1, middle))
    (parsed : value middle = some (result, finish)) :
    optional input value position = some (some result, finish) := by
  unfold optional
  change StateT.run (byte input >>= fun tagValue => match tagValue with
    | 0 => pure none
    | 1 => do pure (some (← value))
    | _ => failure) position = _
  rw [StateT.run_bind]
  have tag' : StateT.run (byte input) position = some (1, middle) := tag
  rw [tag']
  change StateT.run (value >>= fun result => pure (some result)) middle = _
  rw [StateT.run_bind]
  have parsed' : StateT.run value middle = some (result, finish) := parsed
  rw [parsed']
  rfl

private theorem optional_encode
    {parse : Array UInt8 → Parser α} {encode : α → Array UInt8} {valid : α → Prop}
    (item : ParserEncodes parse encode valid) (value : Option α)
    (valueValid : ∀ itemValue ∈ value, valid itemValue) (pre suffix : Array UInt8) :
    optional (pre ++ (encodeOptional encode value ++ suffix))
        (parse (pre ++ (encodeOptional encode value ++ suffix))) pre.size =
      some (value, pre.size + (encodeOptional encode value).size) := by
  cases value with
  | none =>
      apply optional_none_of_byte
      simpa only [byte, encodeOptional, encodeNatLE, Array.append_empty] using
        unsigned_encodeNatLE 1 0 (by decide) pre suffix
  | some value =>
      let input := pre ++ (encodeOptional encode (some value) ++ suffix)
      have inputEq : input = pre ++ (encodeNatLE 1 1 ++ (encode value ++ suffix)) := by
        simp [input, encodeOptional, encodeNatLE, Array.append_assoc]
      have tag : byte input pre.size = some (1, pre.size + 1) := by
        rw [inputEq]
        exact unsigned_encodeNatLE 1 1 (by decide) pre (encode value ++ suffix)
      have parsed : parse input (pre.size + 1) =
          some (value, pre.size + 1 + (encode value).size) := by
        have valueRead := item value (valueValid value (by simp))
          (pre ++ encodeNatLE 1 1) suffix
        simpa [inputEq, encodeNatLE_size, Array.size_append, Array.append_assoc,
          Nat.add_assoc] using valueRead
      simpa [input, encodeOptional, encodeNatLE, Array.size_append, Nat.add_assoc] using
        optional_some_of_byte tag parsed

private theorem take_fixed_encode (value : Array UInt8) (width : Nat)
    (size : value.size = width) (pre suffix : Array UInt8) :
    take (pre ++ (value ++ suffix)) width pre.size = some (value, pre.size + width) := by
  simpa [size] using take_middle pre value suffix

private theorem take_fixed_parserEncodes (width : Nat) :
    ParserEncodes (fun input => take input width) id (fun bytes => bytes.size = width) := by
  intro value size pre suffix
  simpa only [id_eq, size] using take_fixed_encode value width size pre suffix

private theorem unsigned_parserEncodes (width : Nat) :
    ParserEncodes (fun input => unsigned input width) (encodeNatLE width)
      (fun value => value < 256 ^ width) := by
  intro value fits pre suffix
  simpa [encodeNatLE_size] using unsigned_encodeNatLE width value fits pre suffix

private theorem bytes_parserEncodes :
    ParserEncodes bytes encodeBytes (fun value => value.size < 2 ^ 64) := by
  intro value fits pre suffix
  exact bytes_encode value pre suffix fits

private theorem OptionalUIntRep.value_fits {width address : Nat}
    {mem : Std.ExtHashMap Nat (BitVec 8)} {value : Option Nat}
    (rep : OptionalUIntRep width mem address value) :
    ∀ item ∈ value, item < 2 ^ (8 * width) := by
  cases value with
  | none => simp
  | some item =>
      simp only [OptionalUIntRep] at rep
      intro item' member
      simp only [Option.mem_def] at member
      injection member with itemEq
      subst item'
      exact rep.1.1

private theorem OptionalByteSliceRep.value_fits {address : Nat}
    {mem : Std.ExtHashMap Nat (BitVec 8)} {value : Option (Array UInt8)}
    (rep : OptionalByteSliceRep mem address value) :
    ∀ item ∈ value, item.size < 2 ^ 64 := by
  cases value with
  | none => simp
  | some item =>
      simp only [OptionalByteSliceRep] at rep
      intro item' member
      simp only [Option.mem_def] at member
      injection member with itemEq
      subst item'
      exact rep.choose_spec.2.2.1.1

private theorem UIntRep.fits256 {width address value : Nat}
    {mem : Std.ExtHashMap Nat (BitVec 8)} (rep : UIntRep width mem address value) :
    value < 256 ^ width := by
  simpa [show 256 = 2 ^ 8 by decide, Nat.pow_mul] using rep.1

private theorem OptionalUIntRep.value_fits256 {width address : Nat}
    {mem : Std.ExtHashMap Nat (BitVec 8)} {value : Option Nat}
    (rep : OptionalUIntRep width mem address value) :
    ∀ item ∈ value, item < 256 ^ width := by
  intro item member
  simpa [show 256 = 2 ^ 8 by decide, Nat.pow_mul] using rep.value_fits item member

private theorem run_unsigned_encodeNatLE (width value : Nat) (fits : value < 256 ^ width)
    (pre suffix : Array UInt8) :
    StateT.run (unsigned (pre ++ (encodeNatLE width value ++ suffix)) width) pre.size =
      some (value, pre.size + (encodeNatLE width value).size) := by
  simpa [encodeNatLE_size] using unsigned_encodeNatLE width value fits pre suffix

private theorem run_bytes_encode (value pre suffix : Array UInt8) (fits : value.size < 2 ^ 64) :
    StateT.run (bytes (pre ++ (encodeBytes value ++ suffix))) pre.size =
      some (value, pre.size + (encodeBytes value).size) :=
  bytes_encode value pre suffix fits

private theorem unsigned_encodeUIntRep {width address value : Nat}
    {mem : Std.ExtHashMap Nat (BitVec 8)} (rep : UIntRep width mem address value)
    (pre suffix : Array UInt8) :
    unsigned (pre ++ (encodeNatLE width value ++ suffix)) width pre.size =
      some (value, pre.size + width) := by
  apply unsigned_encodeNatLE
  simpa [show 256 = 2 ^ 8 by decide, Nat.pow_mul] using rep.1

private theorem ByteSliceRep.size_fits {mem : Std.ExtHashMap Nat (BitVec 8)}
    {address : Nat} {value : Array UInt8} (rep : ByteSliceRep mem address value) :
    value.size < 2 ^ 64 := by
  rcases rep with ⟨_data, _pointer, size, _elements⟩
  exact size.1

private theorem SliceRep.size_fits {mem : Std.ExtHashMap Nat (BitVec 8)}
    {stride address : Nat} {elementRep : Std.ExtHashMap Nat (BitVec 8) → Nat → α → Prop}
    {values : Array α} (rep : SliceRep stride elementRep mem address values) :
    values.size < 2 ^ 64 := by
  rcases rep with ⟨_data, _pointer, size, _elements⟩
  exact size.1

private theorem parseWithdrawal_of_reads {input : Array UInt8} {start p1 p2 p3 finish : Nat}
    {index validator amount : Nat} {address : Array UInt8}
    (indexRead : u64 input start = some (index, p1))
    (validatorRead : u64 input p1 = some (validator, p2))
    (addressRead : take input 20 p2 = some (address, p3))
    (amountRead : u64 input p3 = some (amount, finish)) :
    parseWithdrawal input start = some ({
      index := index
      validatorIndex := validator
      address
      amount }, finish) := by
  change StateT.run ((do pure {
    index := ← u64 input
    validatorIndex := ← u64 input
    address := ← take input 20
    amount := ← u64 input }) : Parser Withdrawal) start = _
  have indexRead' : StateT.run (u64 input) start = some (index, p1) := indexRead
  have validatorRead' : StateT.run (u64 input) p1 = some (validator, p2) := validatorRead
  have addressRead' : StateT.run (take input 20) p2 = some (address, p3) := addressRead
  have amountRead' : StateT.run (u64 input) p3 = some (amount, finish) := amountRead
  simp_all [StateT.run_bind]

private theorem parseWithdrawal_encode {mem : Std.ExtHashMap Nat (BitVec 8)} {address : Nat} :
    ParserEncodes parseWithdrawal encodeWithdrawal (WithdrawalRep mem address) := by
  intro value rep pre suffix
  rcases rep with ⟨indexRep, validatorRep, amountRep, addressSize, _addressRep⟩
  let input := pre ++ (encodeWithdrawal value ++ suffix)
  have inputEq : input = pre ++ (encodeNatLE 8 value.index ++
      (encodeNatLE 8 value.validatorIndex ++
      (value.address ++ (encodeNatLE 8 value.amount ++ suffix)))) := by
    simp [input, encodeWithdrawal, Array.append_assoc]
  have indexRead : u64 input pre.size = some (value.index, pre.size + 8) := by
    rw [inputEq]
    exact u64_encodeNatLE value.index indexRep.1 pre
      (encodeNatLE 8 value.validatorIndex ++
        (value.address ++ (encodeNatLE 8 value.amount ++ suffix)))
  have validatorRead : u64 input (pre.size + 8) =
      some (value.validatorIndex, pre.size + 8 + 8) := by
    rw [inputEq]
    have read := u64_encodeNatLE value.validatorIndex validatorRep.1
      (pre ++ encodeNatLE 8 value.index) (value.address ++ (encodeNatLE 8 value.amount ++ suffix))
    simpa [Array.size_append, encodeNatLE_size, Nat.add_assoc] using read
  have addressRead : take input 20 (pre.size + 8 + 8) =
      some (value.address, pre.size + 8 + 8 + 20) := by
    rw [inputEq]
    have read := take_fixed_encode value.address 20 addressSize
      (pre ++ encodeNatLE 8 value.index ++ encodeNatLE 8 value.validatorIndex)
      (encodeNatLE 8 value.amount ++ suffix)
    simpa [Array.size_append, encodeNatLE_size, Nat.add_assoc, Array.append_assoc] using read
  have amountRead : u64 input (pre.size + 8 + 8 + 20) =
      some (value.amount, pre.size + 8 + 8 + 20 + 8) := by
    rw [inputEq]
    have read := u64_encodeNatLE value.amount amountRep.1
      (pre ++ encodeNatLE 8 value.index ++ encodeNatLE 8 value.validatorIndex ++ value.address)
      suffix
    simpa [Array.size_append, encodeNatLE_size, addressSize, Nat.add_assoc,
      Array.append_assoc] using read
  simpa [input, encodeWithdrawal, Array.size_append, encodeNatLE_size, addressSize,
    Nat.add_assoc] using parseWithdrawal_of_reads indexRead validatorRead addressRead amountRead

private theorem parseAuthorization_of_reads {input : Array UInt8}
    {start p1 p2 p3 p4 p5 finish chainId nonce v r s : Nat} {address : Array UInt8}
    (chainRead : u256 input start = some (chainId, p1))
    (addressRead : take input 20 p1 = some (address, p2))
    (nonceRead : u64 input p2 = some (nonce, p3))
    (vRead : u64 input p3 = some (v, p4))
    (rRead : u256 input p4 = some (r, p5))
    (sRead : u256 input p5 = some (s, finish)) :
    parseAuthorization input start = some ({ chainId, address, nonce, v, r, s }, finish) := by
  change StateT.run ((do pure {
    chainId := ← u256 input
    address := ← take input 20
    nonce := ← u64 input
    v := ← u64 input
    r := ← u256 input
    s := ← u256 input }) : Parser Authorization) start = _
  have chainRead' : StateT.run (u256 input) start = some (chainId, p1) := chainRead
  have addressRead' : StateT.run (take input 20) p1 = some (address, p2) := addressRead
  have nonceRead' : StateT.run (u64 input) p2 = some (nonce, p3) := nonceRead
  have vRead' : StateT.run (u64 input) p3 = some (v, p4) := vRead
  have rRead' : StateT.run (u256 input) p4 = some (r, p5) := rRead
  have sRead' : StateT.run (u256 input) p5 = some (s, finish) := sRead
  simp_all [StateT.run_bind]

private theorem parseAuthorization_encode {mem : Std.ExtHashMap Nat (BitVec 8)} {address : Nat} :
    ParserEncodes parseAuthorization encodeAuthorization (AuthorizationRep mem address) := by
  intro value rep pre suffix
  rcases rep with ⟨chainRep, rRep, sRep, nonceRep, vRep, addressSize, _addressRep⟩
  let input := pre ++ (encodeAuthorization value ++ suffix)
  have inputEq : input = pre ++ (encodeNatLE 32 value.chainId ++
      (value.address ++ (encodeNatLE 8 value.nonce ++ (encodeNatLE 8 value.v ++
      (encodeNatLE 32 value.r ++ (encodeNatLE 32 value.s ++ suffix)))))) := by
    simp [input, encodeAuthorization, Array.append_assoc]
  have chainRead : u256 input pre.size = some (value.chainId, pre.size + 32) := by
    rw [inputEq]
    exact unsigned_encodeUIntRep chainRep pre
      (value.address ++ (encodeNatLE 8 value.nonce ++ (encodeNatLE 8 value.v ++
        (encodeNatLE 32 value.r ++ (encodeNatLE 32 value.s ++ suffix)))))
  have addressRead : take input 20 (pre.size + 32) =
      some (value.address, pre.size + 32 + 20) := by
    rw [inputEq]
    have read := take_fixed_encode value.address 20 addressSize
      (pre ++ encodeNatLE 32 value.chainId)
      (encodeNatLE 8 value.nonce ++ (encodeNatLE 8 value.v ++
        (encodeNatLE 32 value.r ++ (encodeNatLE 32 value.s ++ suffix))))
    simpa [Array.size_append, encodeNatLE_size, Nat.add_assoc] using read
  have nonceRead : u64 input (pre.size + 32 + 20) =
      some (value.nonce, pre.size + 32 + 20 + 8) := by
    rw [inputEq]
    have read := unsigned_encodeUIntRep nonceRep
      (pre ++ encodeNatLE 32 value.chainId ++ value.address)
      (encodeNatLE 8 value.v ++ (encodeNatLE 32 value.r ++ (encodeNatLE 32 value.s ++ suffix)))
    simpa [u64, Array.size_append, encodeNatLE_size, addressSize, Nat.add_assoc,
      Array.append_assoc] using read
  have vRead : u64 input (pre.size + 32 + 20 + 8) =
      some (value.v, pre.size + 32 + 20 + 8 + 8) := by
    rw [inputEq]
    have read := unsigned_encodeUIntRep vRep
      (pre ++ encodeNatLE 32 value.chainId ++ value.address ++ encodeNatLE 8 value.nonce)
      (encodeNatLE 32 value.r ++ (encodeNatLE 32 value.s ++ suffix))
    simpa [u64, Array.size_append, encodeNatLE_size, addressSize, Nat.add_assoc,
      Array.append_assoc] using read
  have rRead : u256 input (pre.size + 32 + 20 + 8 + 8) =
      some (value.r, pre.size + 32 + 20 + 8 + 8 + 32) := by
    rw [inputEq]
    have read := unsigned_encodeUIntRep rRep
      (pre ++ encodeNatLE 32 value.chainId ++ value.address ++ encodeNatLE 8 value.nonce ++
        encodeNatLE 8 value.v) (encodeNatLE 32 value.s ++ suffix)
    simpa [u256, Array.size_append, encodeNatLE_size, addressSize, Nat.add_assoc,
      Array.append_assoc] using read
  have sRead : u256 input (pre.size + 32 + 20 + 8 + 8 + 32) =
      some (value.s, pre.size + 32 + 20 + 8 + 8 + 32 + 32) := by
    rw [inputEq]
    have read := unsigned_encodeUIntRep sRep
      (pre ++ encodeNatLE 32 value.chainId ++ value.address ++ encodeNatLE 8 value.nonce ++
        encodeNatLE 8 value.v ++ encodeNatLE 32 value.r) suffix
    simpa [u256, Array.size_append, encodeNatLE_size, addressSize, Nat.add_assoc,
      Array.append_assoc] using read
  simpa [input, encodeAuthorization, Array.size_append, encodeNatLE_size, addressSize,
    Nat.add_assoc] using parseAuthorization_of_reads chainRead addressRead nonceRead vRead rRead sRead

private theorem parseAccessListEntry_of_reads {input : Array UInt8}
    {start middle finish : Nat} {address : Array UInt8} {keys : Array (Array UInt8)}
    (addressRead : take input 20 start = some (address, middle))
    (keysRead : fixedMany input 32 middle = some (keys, finish)) :
    parseAccessListEntry input start = some ({ address, storageKeys := keys }, finish) := by
  change StateT.run ((do pure {
    address := ← take input 20
    storageKeys := ← fixedMany input 32 }) : Parser AccessListEntry) start = _
  have addressRead' : StateT.run (take input 20) start = some (address, middle) := addressRead
  have keysRead' : StateT.run (fixedMany input 32) middle = some (keys, finish) := keysRead
  simp_all [StateT.run_bind]

private theorem parseAccessListEntry_encode {mem : Std.ExtHashMap Nat (BitVec 8)} {address : Nat} :
    ParserEncodes parseAccessListEntry encodeAccessListEntry (AccessListEntryRep mem address) := by
  intro value rep pre suffix
  rcases rep with ⟨keysRep, addressSize, _addressRep⟩
  rcases keysRep with ⟨_data, _pointerRep, countRep, elementsRep⟩
  let input := pre ++ (encodeAccessListEntry value ++ suffix)
  have inputEq : input = pre ++ (value.address ++
      (encodeMany (fun key => key) value.storageKeys ++ suffix)) := by
    simp [input, encodeAccessListEntry, Array.append_assoc]
  have addressRead : take input 20 pre.size = some (value.address, pre.size + 20) := by
    rw [inputEq]
    exact take_fixed_encode value.address 20 addressSize pre
      (encodeMany (fun key => key) value.storageKeys ++ suffix)
  have keysRead : fixedMany input 32 (pre.size + 20) =
      some (value.storageKeys,
        pre.size + 20 + (encodeMany (fun key => key) value.storageKeys).size) := by
    unfold fixedMany
    rw [inputEq]
    have read := many_encode (take_fixed_parserEncodes 32) value.storageKeys
      (fun index bound => (elementsRep.2 index bound).1)
      (pre ++ value.address) suffix countRep.1
    simpa [Array.size_append, addressSize, Nat.add_assoc, Array.append_assoc] using read
  simpa [input, encodeAccessListEntry, Array.size_append, addressSize, Nat.add_assoc] using
    parseAccessListEntry_of_reads addressRead keysRead

private theorem parseTransaction_encode {mem : Std.ExtHashMap Nat (BitVec 8)} {address : Nat} :
    ParserEncodes parseTransaction encodeTransaction (TransactionRep mem address) := by
  sorry

private theorem parsePayload_encode {mem : Std.ExtHashMap Nat (BitVec 8)} {address : Nat} :
    ParserEncodes parsePayload encodePayload (ExecutionPayloadRep mem address) := by
  sorry

private theorem parseRequests_encode {mem : Std.ExtHashMap Nat (BitVec 8)} {address : Nat} :
    ParserEncodes parseRequests encodeRequests (ExecutionRequestsRep mem address) := by
  intro value rep pre suffix
  rcases rep with ⟨depositsRep, withdrawalsRep, consolidationsRep, builderDepositsRep,
    builderExitsRep⟩
  let input := pre ++ (encodeRequests value ++ suffix)
  have inputEq : input = pre ++ (encodeBytes value.deposits ++
      (encodeBytes value.withdrawals ++ (encodeBytes value.consolidations ++
      (encodeBytes value.builderDeposits ++ (encodeBytes value.builderExits ++ suffix))))) := by
    simp [input, encodeRequests, Array.append_assoc]
  have r1 := bytes_encode value.deposits pre
    (encodeBytes value.withdrawals ++ (encodeBytes value.consolidations ++
      (encodeBytes value.builderDeposits ++ (encodeBytes value.builderExits ++ suffix))))
    depositsRep.size_fits
  have r2 := bytes_encode value.withdrawals (pre ++ encodeBytes value.deposits)
    (encodeBytes value.consolidations ++
      (encodeBytes value.builderDeposits ++ (encodeBytes value.builderExits ++ suffix)))
    withdrawalsRep.size_fits
  have r3 := bytes_encode value.consolidations
    (pre ++ encodeBytes value.deposits ++ encodeBytes value.withdrawals)
    (encodeBytes value.builderDeposits ++ (encodeBytes value.builderExits ++ suffix))
    consolidationsRep.size_fits
  have r4 := bytes_encode value.builderDeposits
    (pre ++ encodeBytes value.deposits ++ encodeBytes value.withdrawals ++
      encodeBytes value.consolidations) (encodeBytes value.builderExits ++ suffix)
    builderDepositsRep.size_fits
  have r5 := bytes_encode value.builderExits
    (pre ++ encodeBytes value.deposits ++ encodeBytes value.withdrawals ++
      encodeBytes value.consolidations ++ encodeBytes value.builderDeposits) suffix
    builderExitsRep.size_fits
  change parseRequests input pre.size = _
  rw [inputEq]
  simp only [Array.size_append] at r2 r3 r4 r5
  simp only [Array.append_assoc] at r2 r3 r4 r5
  change StateT.run (bytes _) _ = _ at r1
  change StateT.run (bytes _) _ = _ at r2
  change StateT.run (bytes _) _ = _ at r3
  change StateT.run (bytes _) _ = _ at r4
  change StateT.run (bytes _) _ = _ at r5
  change StateT.run ((do pure {
    deposits := ← bytes _
    withdrawals := ← bytes _
    consolidations := ← bytes _
    builderDeposits := ← bytes _
    builderExits := ← bytes _ }) : Parser ExecutionRequests) pre.size = _
  simp_all [StateT.run_bind, encodeRequests, Array.size_append, Nat.add_assoc]

private theorem parseChainConfig_encode {mem : Std.ExtHashMap Nat (BitVec 8)} {address : Nat} :
    ParserEncodes parseChainConfig encodeChainConfig (ChainConfigRep mem address) := by
  intro value rep pre suffix
  rcases rep with ⟨chainRep, forkRep, activeRep, blockRep, timestampRep⟩
  let e1 := encodeNatLE 8 value.chainId
  let e2 := encodeOptional encodeBytes value.forkName
  let e3 := encodeNatLE 8 value.activeForkIndex
  let e4 := encodeOptional (encodeNatLE 8) value.activationBlock
  let e5 := encodeOptional (encodeNatLE 8) value.activationTimestamp
  let input := pre ++ (e1 ++ (e2 ++ (e3 ++ (e4 ++ (e5 ++ suffix)))))
  have inputEq : input = pre ++ (encodeChainConfig value ++ suffix) := by
    simp [input, e1, e2, e3, e4, e5, encodeChainConfig, Array.append_assoc]
  have r1 := u64_encodeNatLE value.chainId chainRep.1 pre (e2 ++ (e3 ++ (e4 ++ (e5 ++ suffix))))
  have r2 := optional_encode bytes_parserEncodes value.forkName forkRep.value_fits
    (pre ++ e1) (e3 ++ (e4 ++ (e5 ++ suffix)))
  have r3 := u64_encodeNatLE value.activeForkIndex activeRep.1
    (pre ++ e1 ++ e2) (e4 ++ (e5 ++ suffix))
  have r4 := optional_encode (unsigned_parserEncodes 8) value.activationBlock
    (fun item member => by
      simpa [show 256 ^ 8 = 2 ^ 64 by native_decide] using blockRep.value_fits item member)
    (pre ++ e1 ++ e2 ++ e3) (e5 ++ suffix)
  have r5 := optional_encode (unsigned_parserEncodes 8) value.activationTimestamp
    (fun item member => by
      simpa [show 256 ^ 8 = 2 ^ 64 by native_decide] using timestampRep.value_fits item member)
    (pre ++ e1 ++ e2 ++ e3 ++ e4) suffix
  rw [← inputEq]
  simp only [Array.size_append, Array.append_assoc] at r2 r3 r4 r5
  change StateT.run (u64 _) _ = _ at r1
  change StateT.run (optional _ _) _ = _ at r2
  change StateT.run (u64 _) _ = _ at r3
  change StateT.run (optional _ (u64 _)) _ = _ at r4
  change StateT.run (optional _ (u64 _)) _ = _ at r5
  change StateT.run ((do pure {
    chainId := ← u64 input
    forkName := ← optional input (bytes input)
    activeForkIndex := ← u64 input
    activationBlock := ← optional input (u64 input)
    activationTimestamp := ← optional input (u64 input) }) : Parser ChainConfig) pre.size = _
  simp_all [StateT.run_bind, e1, e2, e3, e4, e5, encodeChainConfig,
    encodeNatLE_size, Array.size_append, Nat.add_assoc]

private theorem parseSuccess_encode {mem : Std.ExtHashMap Nat (BitVec 8)} {address : Nat} :
    ParserEncodes parseSuccess encodeZesuDecodedResult (StatelessInputRep mem address) := by
  sorry

/-- The endpoint observation parser accepts the exact successful stream emitted from any represented
decoded value. -/
theorem decodeZesuObservation_encode_success_of_rep
    {mem : Std.ExtHashMap Nat (BitVec 8)} {address : Nat} {decoded : ZesuDecodedResult}
    (rep : StatelessInputRep mem address decoded) :
    decodeZesuObservation (encodeZesuObservation (.success decoded)) = some (.success decoded) := by
  sorry

end BinaryFv.Zesu
