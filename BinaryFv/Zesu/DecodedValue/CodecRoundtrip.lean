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

private theorem OptionalAddressRep.value_valid {address : Nat}
    {mem : Std.ExtHashMap Nat (BitVec 8)} {value : Option (Array UInt8)}
    (rep : OptionalAddressRep mem address value) :
    ∀ item ∈ value, item.size = 20 := by
  cases value with
  | none => simp
  | some item =>
      simp only [OptionalAddressRep] at rep
      intro item' member
      simp only [Option.mem_def] at member
      injection member with itemEq
      subst item'
      exact rep.1

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

private theorem u64_parserEncodes :
    ParserEncodes u64 (encodeNatLE 8) (fun value => value < 2 ^ 64) := by
  intro value fits pre suffix
  simpa only [u64, encodeNatLE_size] using u64_encodeNatLE value fits pre suffix

private theorem byte_parserEncodes :
    ParserEncodes byte (encodeNatLE 1) (fun value => value < 256) := by
  intro value fits pre suffix
  simpa only [byte, encodeNatLE_size] using unsigned_encodeNatLE 1 value (by simpa using fits) pre suffix

private theorem u128_parserEncodes :
    ParserEncodes u128 (encodeNatLE 16) (fun value => value < 256 ^ 16) := by
  intro value fits pre suffix
  simpa only [u128, encodeNatLE_size] using unsigned_encodeNatLE 16 value fits pre suffix

private theorem u256_parserEncodes :
    ParserEncodes u256 (encodeNatLE 32) (fun value => value < 256 ^ 32) := by
  intro value fits pre suffix
  simpa only [u256, encodeNatLE_size] using unsigned_encodeNatLE 32 value fits pre suffix

private theorem optional_parserEncodes
    {parse : Array UInt8 → Parser α} {encode : α → Array UInt8} {valid : α → Prop}
    (item : ParserEncodes parse encode valid) :
    ParserEncodes (fun input => optional input (parse input)) (encodeOptional encode)
      (fun value => ∀ itemValue ∈ value, valid itemValue) := by
  intro value valueValid pre suffix
  exact optional_encode item value valueValid pre suffix

private theorem many_parserEncodes
    {parse : Array UInt8 → Parser α} {encode : α → Array UInt8} {valid : α → Prop}
    (item : ParserEncodes parse encode valid) :
    ParserEncodes (fun input => many input (parse input)) (encodeMany encode)
      (fun values => values.size < 2 ^ 64 ∧
        ∀ index (bound : index < values.size), valid values[index]) := by
  intro values validity pre suffix
  exact many_encode item values validity.2 pre suffix validity.1

private theorem fixedMany_parserEncodes (width : Nat) :
    ParserEncodes (fun input => fixedMany input width) (encodeMany id)
      (fun values => values.size < 2 ^ 64 ∧
        ∀ index (bound : index < values.size), values[index].size = width) := by
  intro values validity pre suffix
  change many (pre ++ (encodeMany id values ++ suffix))
      (take (pre ++ (encodeMany id values ++ suffix)) width) pre.size = _
  exact many_encode (take_fixed_parserEncodes width) values validity.2 pre suffix validity.1

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

private theorem parseAccessListEntry_encode_any :
    ParserEncodes parseAccessListEntry encodeAccessListEntry
      (fun value => ∃ mem address, AccessListEntryRep mem address value) := by
  intro value rep pre suffix
  rcases rep with ⟨mem, address, represented⟩
  exact parseAccessListEntry_encode value represented pre suffix

private theorem parseAuthorization_encode_any :
    ParserEncodes parseAuthorization encodeAuthorization
      (fun value => ∃ mem address, AuthorizationRep mem address value) := by
  intro value rep pre suffix
  rcases rep with ⟨mem, address, represented⟩
  exact parseAuthorization_encode value represented pre suffix

set_option genInjectivity false in
private theorem parseTransaction_of_reads {input : Array UInt8}
    {p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 : Nat}
    {value : Transaction}
    (r1 : byte input p0 = some (value.txType, p1))
    (r2 : optional input (u64 input) p1 = some (value.chainId, p2))
    (r3 : u64 input p2 = some (value.nonce, p3))
    (r4 : u128 input p3 = some (value.gasPrice, p4))
    (r5 : optional input (u128 input) p4 = some (value.gasPriorityFee, p5))
    (r6 : u64 input p5 = some (value.gasLimit, p6))
    (r7 : optional input (take input 20) p6 = some (value.recipient, p7))
    (r8 : u256 input p7 = some (value.value, p8))
    (r9 : bytes input p8 = some (value.data, p9))
    (r10 : many input (parseAccessListEntry input) p9 = some (value.accessList, p10))
    (r11 : fixedMany input 32 p10 = some (value.blobHashes, p11))
    (r12 : u128 input p11 = some (value.maxFeePerBlobGas, p12))
    (r13 : many input (parseAuthorization input) p12 = some (value.authorizations, p13))
    (r14 : u64 input p13 = some (value.v, p14))
    (r15 : u256 input p14 = some (value.r, p15))
    (r16 : u256 input p15 = some (value.s, p16)) :
    parseTransaction input p0 = some (value, p16) := by
  change StateT.run ((do pure {
    txType := ← byte input
    chainId := ← optional input (u64 input)
    nonce := ← u64 input
    gasPrice := ← u128 input
    gasPriorityFee := ← optional input (u128 input)
    gasLimit := ← u64 input
    recipient := ← optional input (take input 20)
    value := ← u256 input
    data := ← bytes input
    accessList := ← many input (parseAccessListEntry input)
    blobHashes := ← fixedMany input 32
    maxFeePerBlobGas := ← u128 input
    authorizations := ← many input (parseAuthorization input)
    v := ← u64 input
    r := ← u256 input
    s := ← u256 input }) : Parser Transaction) p0 = _
  have r1' : StateT.run (byte input) p0 = _ := r1
  have r2' : StateT.run (optional input (u64 input)) p1 = _ := r2
  have r3' : StateT.run (u64 input) p2 = _ := r3
  have r4' : StateT.run (u128 input) p3 = _ := r4
  have r5' : StateT.run (optional input (u128 input)) p4 = _ := r5
  have r6' : StateT.run (u64 input) p5 = _ := r6
  have r7' : StateT.run (optional input (take input 20)) p6 = _ := r7
  have r8' : StateT.run (u256 input) p7 = _ := r8
  have r9' : StateT.run (bytes input) p8 = _ := r9
  have r10' : StateT.run (many input (parseAccessListEntry input)) p9 = _ := r10
  have r11' : StateT.run (fixedMany input 32) p10 = _ := r11
  have r12' : StateT.run (u128 input) p11 = _ := r12
  have r13' : StateT.run (many input (parseAuthorization input)) p12 = _ := r13
  have r14' : StateT.run (u64 input) p13 = _ := r14
  have r15' : StateT.run (u256 input) p14 = _ := r15
  have r16' : StateT.run (u256 input) p15 = _ := r16
  simp_all [StateT.run_bind]

set_option genInjectivity false in
private structure TransactionReadsA (input : Array UInt8) (value : Transaction)
    (start finish : Nat) where
  p1 : Nat
  p2 : Nat
  p3 : Nat
  r1 : byte input start = some (value.txType, p1)
  r2 : optional input (u64 input) p1 = some (value.chainId, p2)
  r3 : u64 input p2 = some (value.nonce, p3)
  r4 : u128 input p3 = some (value.gasPrice, finish)

set_option genInjectivity false in
private structure TransactionReadsB (input : Array UInt8) (value : Transaction)
    (start finish : Nat) where
  p5 : Nat
  p6 : Nat
  p7 : Nat
  r5 : optional input (u128 input) start = some (value.gasPriorityFee, p5)
  r6 : u64 input p5 = some (value.gasLimit, p6)
  r7 : optional input (take input 20) p6 = some (value.recipient, p7)
  r8 : u256 input p7 = some (value.value, finish)

set_option genInjectivity false in
private structure TransactionReadsC (input : Array UInt8) (value : Transaction)
    (start finish : Nat) where
  p9 : Nat
  p10 : Nat
  p11 : Nat
  r9 : bytes input start = some (value.data, p9)
  r10 : many input (parseAccessListEntry input) p9 = some (value.accessList, p10)
  r11 : fixedMany input 32 p10 = some (value.blobHashes, p11)
  r12 : u128 input p11 = some (value.maxFeePerBlobGas, finish)

set_option genInjectivity false in
private structure TransactionReadsD (input : Array UInt8) (value : Transaction)
    (start finish : Nat) where
  p13 : Nat
  p14 : Nat
  p15 : Nat
  r13 : many input (parseAuthorization input) start = some (value.authorizations, p13)
  r14 : u64 input p13 = some (value.v, p14)
  r15 : u256 input p14 = some (value.r, p15)
  r16 : u256 input p15 = some (value.s, finish)

private theorem transactionReads_parsed {input : Array UInt8} {value : Transaction}
    {p0 p4 p8 p12 p16 : Nat}
    (a : TransactionReadsA input value p0 p4) (b : TransactionReadsB input value p4 p8)
    (c : TransactionReadsC input value p8 p12) (d : TransactionReadsD input value p12 p16) :
    parseTransaction input p0 = some (value, p16) :=
  parseTransaction_of_reads a.r1 a.r2 a.r3 a.r4 b.r5 b.r6 b.r7 b.r8 c.r9 c.r10 c.r11
    c.r12 d.r13 d.r14 d.r15 d.r16

set_option genInjectivity false in
private structure ParserReadPair (first : Nat → Option (α × Nat))
    (second : Nat → Option (β × Nat)) (firstValue : α) (secondValue : β)
    (start finish : Nat) where
  middle : Nat
  firstRead : first start = some (firstValue, middle)
  secondRead : second middle = some (secondValue, finish)

private def parserReadPair_encode
    {parseA : Array UInt8 → Parser α} {encodeA : α → Array UInt8} {validA : α → Prop}
    {parseB : Array UInt8 → Parser β} {encodeB : β → Array UInt8} {validB : β → Prop}
    (codecA : ParserEncodes parseA encodeA validA)
    (codecB : ParserEncodes parseB encodeB validB)
    (a : α) (aValid : validA a) (b : β) (bValid : validB b)
    (pre suffix : Array UInt8) :
    let input := pre ++ (encodeA a ++ (encodeB b ++ suffix))
    ParserReadPair (parseA input) (parseB input) a b pre.size
      (pre.size + (encodeA a).size + (encodeB b).size) := by
  let input := pre ++ (encodeA a ++ (encodeB b ++ suffix))
  have firstRead := codecA a aValid pre (encodeB b ++ suffix)
  have secondRead := codecB b bValid (pre ++ encodeA a) suffix
  refine { middle := pre.size + (encodeA a).size, firstRead := ?_, secondRead := ?_ }
  · exact firstRead
  · simpa [input, Array.size_append, Array.append_assoc] using secondRead

private def parserReadPair_encode_in
    {parseA : Array UInt8 → Parser α} {encodeA : α → Array UInt8} {validA : α → Prop}
    {parseB : Array UInt8 → Parser β} {encodeB : β → Array UInt8} {validB : β → Prop}
    (codecA : ParserEncodes parseA encodeA validA)
    (codecB : ParserEncodes parseB encodeB validB)
    (a : α) (aValid : validA a) (b : β) (bValid : validB b)
    (pre suffix input : Array UInt8)
    (inputEq : input = pre ++ (encodeA a ++ (encodeB b ++ suffix))) :
    ParserReadPair (parseA input) (parseB input) a b pre.size
      (pre ++ encodeA a ++ encodeB b).size := by
  subst input
  simpa [Array.size_append, Nat.add_assoc] using
    parserReadPair_encode codecA codecB a aValid b bValid pre suffix

private theorem transactionReadPairs_parsed {input : Array UInt8} {value : Transaction}
    {p0 p2 p4 p6 p8 p10 p12 p14 p16 : Nat}
    (a : ParserReadPair (byte input) (optional input (u64 input)) value.txType value.chainId p0 p2)
    (b : ParserReadPair (u64 input) (u128 input) value.nonce value.gasPrice p2 p4)
    (c : ParserReadPair (optional input (u128 input)) (u64 input)
      value.gasPriorityFee value.gasLimit p4 p6)
    (d : ParserReadPair (optional input (take input 20)) (u256 input)
      value.recipient value.value p6 p8)
    (e : ParserReadPair (bytes input) (many input (parseAccessListEntry input))
      value.data value.accessList p8 p10)
    (f : ParserReadPair (fixedMany input 32) (u128 input)
      value.blobHashes value.maxFeePerBlobGas p10 p12)
    (g : ParserReadPair (many input (parseAuthorization input)) (u64 input)
      value.authorizations value.v p12 p14)
    (h : ParserReadPair (u256 input) (u256 input) value.r value.s p14 p16) :
    parseTransaction input p0 = some (value, p16) :=
  parseTransaction_of_reads a.firstRead a.secondRead b.firstRead b.secondRead c.firstRead
    c.secondRead d.firstRead d.secondRead e.firstRead e.secondRead f.firstRead f.secondRead
    g.firstRead g.secondRead h.firstRead h.secondRead


set_option genInjectivity false in
private theorem parseTransaction_encode {mem : Std.ExtHashMap Nat (BitVec 8)} {address : Nat} :
    ParserEncodes parseTransaction encodeTransaction (TransactionRep mem address) := by
  intro value rep pre suffix
  rcases rep with ⟨gasPrice, gasPriorityFee, txValue, maxFee, rRep, sRep, chainId,
    nonce, gasLimit, data, accessList, blobHashes, authorizations, vRep, txType, recipient⟩
  have accessFits := accessList.size_fits
  have blobFits := blobHashes.size_fits
  have authorizationFits := authorizations.size_fits
  rcases accessList with ⟨accessData, _accessPointer, _accessCount, accessElements⟩
  rcases blobHashes with ⟨blobData, _blobPointer, _blobCount, blobElements⟩
  rcases authorizations with ⟨authorizationData, _authorizationPointer,
    _authorizationCount, authorizationElements⟩
  let e1 := encodeNatLE 1 value.txType
  let e2 := encodeOptional (encodeNatLE 8) value.chainId
  let e3 := encodeNatLE 8 value.nonce
  let e4 := encodeNatLE 16 value.gasPrice
  let e5 := encodeOptional (encodeNatLE 16) value.gasPriorityFee
  let e6 := encodeNatLE 8 value.gasLimit
  let e7 := encodeOptional (fun address => address) value.recipient
  let e8 := encodeNatLE 32 value.value
  let e9 := encodeBytes value.data
  let e10 := encodeMany encodeAccessListEntry value.accessList
  let e11 := encodeMany (fun hash => hash) value.blobHashes
  let e12 := encodeNatLE 16 value.maxFeePerBlobGas
  let e13 := encodeMany encodeAuthorization value.authorizations
  let e14 := encodeNatLE 8 value.v
  let e15 := encodeNatLE 32 value.r
  let e16 := encodeNatLE 32 value.s
  let input := pre ++ (e1 ++ (e2 ++ (e3 ++ (e4 ++ (e5 ++ (e6 ++ (e7 ++ (e8 ++
    (e9 ++ (e10 ++ (e11 ++ (e12 ++ (e13 ++ (e14 ++ (e15 ++ (e16 ++ suffix))))))))))))))))
  have a := parserReadPair_encode_in byte_parserEncodes
    (optional_parserEncodes u64_parserEncodes) value.txType txType.fits256 value.chainId
    chainId.value_fits pre (e3 ++ e4 ++ e5 ++ e6 ++ e7 ++ e8 ++ e9 ++ e10 ++ e11 ++
      e12 ++ e13 ++ e14 ++ e15 ++ e16 ++ suffix) input (by
        simp [input, e1, e2, Array.append_assoc])
  have b := parserReadPair_encode_in u64_parserEncodes u128_parserEncodes value.nonce nonce.1
    value.gasPrice gasPrice.fits256 (pre ++ e1 ++ e2)
    (e5 ++ e6 ++ e7 ++ e8 ++ e9 ++ e10 ++ e11 ++ e12 ++ e13 ++ e14 ++ e15 ++ e16 ++ suffix)
    input (by simp [input, e3, e4, Array.append_assoc])
  have c := parserReadPair_encode_in (optional_parserEncodes u128_parserEncodes) u64_parserEncodes
    value.gasPriorityFee gasPriorityFee.value_fits256 value.gasLimit gasLimit.1
    (pre ++ e1 ++ e2 ++ e3 ++ e4)
    (e7 ++ e8 ++ e9 ++ e10 ++ e11 ++ e12 ++ e13 ++ e14 ++ e15 ++ e16 ++ suffix)
    input (by simp [input, e5, e6, Array.append_assoc])
  have d := parserReadPair_encode_in (optional_parserEncodes (take_fixed_parserEncodes 20))
    u256_parserEncodes value.recipient recipient.value_valid value.value txValue.fits256
    (pre ++ e1 ++ e2 ++ e3 ++ e4 ++ e5 ++ e6)
    (e9 ++ e10 ++ e11 ++ e12 ++ e13 ++ e14 ++ e15 ++ e16 ++ suffix)
    input (by
      change input = (pre ++ e1 ++ e2 ++ e3 ++ e4 ++ e5 ++ e6) ++
        (e7 ++ (e8 ++ (e9 ++ e10 ++ e11 ++ e12 ++ e13 ++ e14 ++ e15 ++ e16 ++ suffix)))
      simp [input, Array.append_assoc])
  have e := parserReadPair_encode_in bytes_parserEncodes
    (many_parserEncodes parseAccessListEntry_encode_any) value.data data.size_fits value.accessList
    ⟨accessFits, fun index bound => ⟨mem, accessData + index * 40, accessElements.2 index bound⟩⟩
    (pre ++ e1 ++ e2 ++ e3 ++ e4 ++ e5 ++ e6 ++ e7 ++ e8)
    (e11 ++ e12 ++ e13 ++ e14 ++ e15 ++ e16 ++ suffix)
    input (by simp [input, e9, e10, Array.append_assoc])
  have f := parserReadPair_encode_in (fixedMany_parserEncodes 32) u128_parserEncodes
    value.blobHashes ⟨blobFits, fun index bound => (blobElements.2 index bound).1⟩
    value.maxFeePerBlobGas maxFee.fits256
    (pre ++ e1 ++ e2 ++ e3 ++ e4 ++ e5 ++ e6 ++ e7 ++ e8 ++ e9 ++ e10)
    (e13 ++ e14 ++ e15 ++ e16 ++ suffix)
    input (by
      change input = (pre ++ e1 ++ e2 ++ e3 ++ e4 ++ e5 ++ e6 ++ e7 ++ e8 ++ e9 ++ e10) ++
        (e11 ++ (e12 ++ (e13 ++ e14 ++ e15 ++ e16 ++ suffix)))
      simp [input, Array.append_assoc])
  have g := parserReadPair_encode_in (many_parserEncodes parseAuthorization_encode_any)
    u64_parserEncodes value.authorizations
    ⟨authorizationFits, fun index bound =>
      ⟨mem, authorizationData + index * 144, authorizationElements.2 index bound⟩⟩
    value.v vRep.1 (pre ++ e1 ++ e2 ++ e3 ++ e4 ++ e5 ++ e6 ++ e7 ++ e8 ++ e9 ++
      e10 ++ e11 ++ e12) (e15 ++ (e16 ++ suffix)) input
    (by simp [input, e13, e14, Array.append_assoc])
  have h := parserReadPair_encode_in u256_parserEncodes u256_parserEncodes value.r rRep.fits256
    value.s sRep.fits256 (pre ++ e1 ++ e2 ++ e3 ++ e4 ++ e5 ++ e6 ++ e7 ++ e8 ++
      e9 ++ e10 ++ e11 ++ e12 ++ e13 ++ e14) suffix input
    (by simp [input, e15, e16, Array.append_assoc])
  have parsed := transactionReadPairs_parsed a b c d e f g h
  simpa [input, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14,
    e15, e16, encodeTransaction,
    encodeNatLE_size, Array.size_append, Array.append_assoc,
    Nat.add_assoc] using parsed

private theorem parseTransaction_encode_any :
    ParserEncodes parseTransaction encodeTransaction
      (fun value => ∃ mem address, TransactionRep mem address value) := by
  intro value rep pre suffix
  rcases rep with ⟨mem, address, represented⟩
  exact parseTransaction_encode value represented pre suffix

private theorem parseWithdrawal_encode_any :
    ParserEncodes parseWithdrawal encodeWithdrawal
      (fun value => ∃ mem address, WithdrawalRep mem address value) := by
  intro value rep pre suffix
  rcases rep with ⟨mem, address, represented⟩
  exact parseWithdrawal_encode value represented pre suffix

set_option genInjectivity false in
private theorem parsePayload_of_reads {input : Array UInt8} {value : ExecutionPayload}
    {p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 : Nat}
    (r1 : take input 32 p0 = some (value.parentHash, p1))
    (r2 : take input 20 p1 = some (value.feeRecipient, p2))
    (r3 : take input 32 p2 = some (value.stateRoot, p3))
    (r4 : take input 32 p3 = some (value.receiptsRoot, p4))
    (r5 : take input 256 p4 = some (value.logsBloom, p5))
    (r6 : take input 32 p5 = some (value.prevRandao, p6))
    (r7 : u64 input p6 = some (value.blockNumber, p7))
    (r8 : u64 input p7 = some (value.gasLimit, p8))
    (r9 : u64 input p8 = some (value.gasUsed, p9))
    (r10 : u64 input p9 = some (value.timestamp, p10))
    (r11 : bytes input p10 = some (value.extraData, p11))
    (r12 : u64 input p11 = some (value.baseFeePerGas, p12))
    (r13 : take input 32 p12 = some (value.blockHash, p13))
    (r14 : many input (parseTransaction input) p13 = some (value.transactions, p14))
    (r15 : many input (bytes input) p14 = some (value.rawTransactions, p15))
    (r16 : many input (parseWithdrawal input) p15 = some (value.withdrawals, p16))
    (r17 : u64 input p16 = some (value.blobGasUsed, p17))
    (r18 : u64 input p17 = some (value.excessBlobGas, p18))
    (r19 : optional input (u64 input) p18 = some (value.slotNumber, p19))
    (r20 : bytes input p19 = some (value.blockAccessList, p20)) :
    parsePayload input p0 = some (value, p20) := by
  change StateT.run ((do pure {
    parentHash := ← take input 32
    feeRecipient := ← take input 20
    stateRoot := ← take input 32
    receiptsRoot := ← take input 32
    logsBloom := ← take input 256
    prevRandao := ← take input 32
    blockNumber := ← u64 input
    gasLimit := ← u64 input
    gasUsed := ← u64 input
    timestamp := ← u64 input
    extraData := ← bytes input
    baseFeePerGas := ← u64 input
    blockHash := ← take input 32
    transactions := ← many input (parseTransaction input)
    rawTransactions := ← many input (bytes input)
    withdrawals := ← many input (parseWithdrawal input)
    blobGasUsed := ← u64 input
    excessBlobGas := ← u64 input
    slotNumber := ← optional input (u64 input)
    blockAccessList := ← bytes input }) : Parser ExecutionPayload) p0 = _
  change StateT.run (take input 32) p0 = _ at r1
  change StateT.run (take input 20) p1 = _ at r2
  change StateT.run (take input 32) p2 = _ at r3
  change StateT.run (take input 32) p3 = _ at r4
  change StateT.run (take input 256) p4 = _ at r5
  change StateT.run (take input 32) p5 = _ at r6
  change StateT.run (u64 input) p6 = _ at r7
  change StateT.run (u64 input) p7 = _ at r8
  change StateT.run (u64 input) p8 = _ at r9
  change StateT.run (u64 input) p9 = _ at r10
  change StateT.run (bytes input) p10 = _ at r11
  change StateT.run (u64 input) p11 = _ at r12
  change StateT.run (take input 32) p12 = _ at r13
  change StateT.run (many input (parseTransaction input)) p13 = _ at r14
  change StateT.run (many input (bytes input)) p14 = _ at r15
  change StateT.run (many input (parseWithdrawal input)) p15 = _ at r16
  change StateT.run (u64 input) p16 = _ at r17
  change StateT.run (u64 input) p17 = _ at r18
  change StateT.run (optional input (u64 input)) p18 = _ at r19
  change StateT.run (bytes input) p19 = _ at r20
  simp_all [StateT.run_bind]

private theorem payloadReadPairs_parsed {input : Array UInt8} {value : ExecutionPayload}
    {p0 p2 p4 p6 p8 p10 p12 p14 p16 p18 p20 : Nat}
    (a : ParserReadPair (take input 32) (take input 20) value.parentHash value.feeRecipient p0 p2)
    (b : ParserReadPair (take input 32) (take input 32) value.stateRoot value.receiptsRoot p2 p4)
    (c : ParserReadPair (take input 256) (take input 32) value.logsBloom value.prevRandao p4 p6)
    (d : ParserReadPair (u64 input) (u64 input) value.blockNumber value.gasLimit p6 p8)
    (e : ParserReadPair (u64 input) (u64 input) value.gasUsed value.timestamp p8 p10)
    (f : ParserReadPair (bytes input) (u64 input) value.extraData value.baseFeePerGas p10 p12)
    (g : ParserReadPair (take input 32) (many input (parseTransaction input))
      value.blockHash value.transactions p12 p14)
    (h : ParserReadPair (many input (bytes input)) (many input (parseWithdrawal input))
      value.rawTransactions value.withdrawals p14 p16)
    (i : ParserReadPair (u64 input) (u64 input) value.blobGasUsed value.excessBlobGas p16 p18)
    (j : ParserReadPair (optional input (u64 input)) (bytes input)
      value.slotNumber value.blockAccessList p18 p20) :
    parsePayload input p0 = some (value, p20) :=
  parsePayload_of_reads a.firstRead a.secondRead b.firstRead b.secondRead c.firstRead c.secondRead
    d.firstRead d.secondRead e.firstRead e.secondRead f.firstRead f.secondRead g.firstRead
    g.secondRead h.firstRead h.secondRead i.firstRead i.secondRead j.firstRead j.secondRead

private theorem parsePayload_encode {mem : Std.ExtHashMap Nat (BitVec 8)} {address : Nat} :
    ParserEncodes parsePayload encodePayload (ExecutionPayloadRep mem address) := by
  intro value rep pre suffix
  rcases rep with ⟨blockNumber, gasLimit, gasUsed, timestamp, extraData, baseFee,
    transactions, rawTransactions, withdrawals, blobGasUsed, excessBlobGas, slotNumber,
    blockAccessList, parentHashSize, _parentHash, feeRecipientSize, _feeRecipient,
    stateRootSize, _stateRoot, receiptsRootSize, _receiptsRoot, logsBloomSize, _logsBloom,
    prevRandaoSize, _prevRandao, blockHashSize, _blockHash⟩
  have transactionsFits := transactions.size_fits
  have rawTransactionsFits := rawTransactions.size_fits
  have withdrawalsFits := withdrawals.size_fits
  rcases transactions with ⟨transactionsData, _, _, transactionElements⟩
  rcases rawTransactions with ⟨rawTransactionsData, _, _, rawTransactionElements⟩
  rcases withdrawals with ⟨withdrawalsData, _, _, withdrawalElements⟩
  let e1 := value.parentHash
  let e2 := value.feeRecipient
  let e3 := value.stateRoot
  let e4 := value.receiptsRoot
  let e5 := value.logsBloom
  let e6 := value.prevRandao
  let e7 := encodeNatLE 8 value.blockNumber
  let e8 := encodeNatLE 8 value.gasLimit
  let e9 := encodeNatLE 8 value.gasUsed
  let e10 := encodeNatLE 8 value.timestamp
  let e11 := encodeBytes value.extraData
  let e12 := encodeNatLE 8 value.baseFeePerGas
  let e13 := value.blockHash
  let e14 := encodeMany encodeTransaction value.transactions
  let e15 := encodeMany encodeBytes value.rawTransactions
  let e16 := encodeMany encodeWithdrawal value.withdrawals
  let e17 := encodeNatLE 8 value.blobGasUsed
  let e18 := encodeNatLE 8 value.excessBlobGas
  let e19 := encodeOptional (encodeNatLE 8) value.slotNumber
  let e20 := encodeBytes value.blockAccessList
  let input := pre ++ (e1 ++ (e2 ++ (e3 ++ (e4 ++ (e5 ++ (e6 ++ (e7 ++ (e8 ++
    (e9 ++ (e10 ++ (e11 ++ (e12 ++ (e13 ++ (e14 ++ (e15 ++ (e16 ++ (e17 ++
      (e18 ++ (e19 ++ (e20 ++ suffix))))))))))))))))))))
  have a := parserReadPair_encode_in (take_fixed_parserEncodes 32) (take_fixed_parserEncodes 20)
    value.parentHash parentHashSize value.feeRecipient feeRecipientSize pre
    (e3 ++ e4 ++ e5 ++ e6 ++ e7 ++ e8 ++ e9 ++ e10 ++ e11 ++ e12 ++ e13 ++ e14 ++ e15 ++
      e16 ++ e17 ++ e18 ++ e19 ++ e20 ++ suffix) input (by
        change input = pre ++ (e1 ++ (e2 ++ (e3 ++ e4 ++ e5 ++ e6 ++ e7 ++ e8 ++ e9 ++ e10 ++
          e11 ++ e12 ++ e13 ++ e14 ++ e15 ++ e16 ++ e17 ++ e18 ++ e19 ++ e20 ++ suffix)))
        simp [input, Array.append_assoc])
  have b := parserReadPair_encode_in (take_fixed_parserEncodes 32) (take_fixed_parserEncodes 32)
    value.stateRoot stateRootSize value.receiptsRoot receiptsRootSize (pre ++ e1 ++ e2)
    (e5 ++ e6 ++ e7 ++ e8 ++ e9 ++ e10 ++ e11 ++ e12 ++ e13 ++ e14 ++ e15 ++ e16 ++ e17 ++
      e18 ++ e19 ++ e20 ++ suffix) input (by
        change input = (pre ++ e1 ++ e2) ++ (e3 ++ (e4 ++ (e5 ++ e6 ++ e7 ++ e8 ++ e9 ++ e10 ++
          e11 ++ e12 ++ e13 ++ e14 ++ e15 ++ e16 ++ e17 ++ e18 ++ e19 ++ e20 ++ suffix)))
        simp [input, Array.append_assoc])
  have c := parserReadPair_encode_in (take_fixed_parserEncodes 256) (take_fixed_parserEncodes 32)
    value.logsBloom logsBloomSize value.prevRandao prevRandaoSize (pre ++ e1 ++ e2 ++ e3 ++ e4)
    (e7 ++ e8 ++ e9 ++ e10 ++ e11 ++ e12 ++ e13 ++ e14 ++ e15 ++ e16 ++ e17 ++ e18 ++ e19 ++
      e20 ++ suffix) input (by
        change input = (pre ++ e1 ++ e2 ++ e3 ++ e4) ++
          (e5 ++ (e6 ++ (e7 ++ e8 ++ e9 ++ e10 ++ e11 ++ e12 ++ e13 ++ e14 ++ e15 ++ e16 ++
            e17 ++ e18 ++ e19 ++ e20 ++ suffix)))
        simp [input, Array.append_assoc])
  have d := parserReadPair_encode_in u64_parserEncodes u64_parserEncodes
    value.blockNumber blockNumber.1 value.gasLimit gasLimit.1
    (pre ++ e1 ++ e2 ++ e3 ++ e4 ++ e5 ++ e6)
    (e9 ++ e10 ++ e11 ++ e12 ++ e13 ++ e14 ++ e15 ++ e16 ++ e17 ++ e18 ++ e19 ++ e20 ++ suffix)
    input (by simp [input, e7, e8, Array.append_assoc])
  have e := parserReadPair_encode_in u64_parserEncodes u64_parserEncodes
    value.gasUsed gasUsed.1 value.timestamp timestamp.1
    (pre ++ e1 ++ e2 ++ e3 ++ e4 ++ e5 ++ e6 ++ e7 ++ e8)
    (e11 ++ e12 ++ e13 ++ e14 ++ e15 ++ e16 ++ e17 ++ e18 ++ e19 ++ e20 ++ suffix)
    input (by simp [input, e9, e10, Array.append_assoc])
  have f := parserReadPair_encode_in bytes_parserEncodes u64_parserEncodes
    value.extraData extraData.size_fits value.baseFeePerGas baseFee.1
    (pre ++ e1 ++ e2 ++ e3 ++ e4 ++ e5 ++ e6 ++ e7 ++ e8 ++ e9 ++ e10)
    (e13 ++ e14 ++ e15 ++ e16 ++ e17 ++ e18 ++ e19 ++ e20 ++ suffix)
    input (by simp [input, e11, e12, Array.append_assoc])
  have g := parserReadPair_encode_in (take_fixed_parserEncodes 32)
    (many_parserEncodes parseTransaction_encode_any) value.blockHash blockHashSize value.transactions
    ⟨transactionsFits, fun index bound =>
      ⟨mem, transactionsData + index * 288, transactionElements.2 index bound⟩⟩
    (pre ++ e1 ++ e2 ++ e3 ++ e4 ++ e5 ++ e6 ++ e7 ++ e8 ++ e9 ++ e10 ++ e11 ++ e12)
    (e15 ++ e16 ++ e17 ++ e18 ++ e19 ++ e20 ++ suffix) input (by
      change input = (pre ++ e1 ++ e2 ++ e3 ++ e4 ++ e5 ++ e6 ++ e7 ++ e8 ++ e9 ++ e10 ++ e11 ++ e12) ++
        (e13 ++ (e14 ++ (e15 ++ e16 ++ e17 ++ e18 ++ e19 ++ e20 ++ suffix)))
      simp [input, Array.append_assoc])
  have h := parserReadPair_encode_in (many_parserEncodes bytes_parserEncodes)
    (many_parserEncodes parseWithdrawal_encode_any) value.rawTransactions
    ⟨rawTransactionsFits, fun index bound => (rawTransactionElements.2 index bound).size_fits⟩
    value.withdrawals ⟨withdrawalsFits, fun index bound =>
      ⟨mem, withdrawalsData + index * 48, withdrawalElements.2 index bound⟩⟩
    (pre ++ e1 ++ e2 ++ e3 ++ e4 ++ e5 ++ e6 ++ e7 ++ e8 ++ e9 ++ e10 ++ e11 ++ e12 ++ e13 ++ e14)
    (e17 ++ e18 ++ e19 ++ e20 ++ suffix) input
    (by simp [input, e15, e16, Array.append_assoc])
  have i := parserReadPair_encode_in u64_parserEncodes u64_parserEncodes
    value.blobGasUsed blobGasUsed.1 value.excessBlobGas excessBlobGas.1
    (pre ++ e1 ++ e2 ++ e3 ++ e4 ++ e5 ++ e6 ++ e7 ++ e8 ++ e9 ++ e10 ++ e11 ++ e12 ++ e13 ++ e14 ++ e15 ++ e16)
    (e19 ++ e20 ++ suffix) input (by simp [input, e17, e18, Array.append_assoc])
  have j := parserReadPair_encode_in (optional_parserEncodes u64_parserEncodes) bytes_parserEncodes
    value.slotNumber slotNumber.value_fits value.blockAccessList blockAccessList.size_fits
    (pre ++ e1 ++ e2 ++ e3 ++ e4 ++ e5 ++ e6 ++ e7 ++ e8 ++ e9 ++ e10 ++ e11 ++ e12 ++ e13 ++ e14 ++ e15 ++ e16 ++ e17 ++ e18)
    suffix input (by simp [input, e19, e20, Array.append_assoc])
  have parsed := payloadReadPairs_parsed a b c d e f g h i j
  simpa [input, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14,
    e15, e16, e17, e18, e19, e20, encodePayload, encodeNatLE_size, Array.size_append,
    Array.append_assoc, Nat.add_assoc] using parsed

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
    blockRep.value_fits256
    (pre ++ e1 ++ e2 ++ e3) (e5 ++ suffix)
  have r5 := optional_encode (unsigned_parserEncodes 8) value.activationTimestamp
    timestampRep.value_fits256
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

set_option genInjectivity false in
private theorem parseSuccess_of_reads {input : Array UInt8} {value : ZesuDecodedResult}
    {p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 : Nat}
    (r1 : parsePayload input p0 = some (value.payload, p1))
    (r2 : take input 32 p1 = some (value.parentBeaconBlockRoot, p2))
    (r3 : fixedMany input 32 p2 = some (value.versionedHashes, p3))
    (r4 : parseRequests input p3 = some (value.executionRequests, p4))
    (r5 : many input (bytes input) p4 = some (value.witnessNodes, p5))
    (r6 : many input (bytes input) p5 = some (value.witnessCodes, p6))
    (r7 : many input (bytes input) p6 = some (value.witnessHeaders, p7))
    (r8 : parseChainConfig input p7 = some (value.chainConfig, p8))
    (r9 : many input (bytes input) p8 = some (value.publicKeys, p9)) :
    parseSuccess input p0 = some (value, p9) := by
  change StateT.run ((do pure {
    payload := ← parsePayload input
    parentBeaconBlockRoot := ← take input 32
    versionedHashes := ← fixedMany input 32
    executionRequests := ← parseRequests input
    witnessNodes := ← many input (bytes input)
    witnessCodes := ← many input (bytes input)
    witnessHeaders := ← many input (bytes input)
    chainConfig := ← parseChainConfig input
    publicKeys := ← many input (bytes input) }) : Parser ZesuDecodedResult) p0 = _
  change StateT.run (parsePayload input) p0 = _ at r1
  change StateT.run (take input 32) p1 = _ at r2
  change StateT.run (fixedMany input 32) p2 = _ at r3
  change StateT.run (parseRequests input) p3 = _ at r4
  change StateT.run (many input (bytes input)) p4 = _ at r5
  change StateT.run (many input (bytes input)) p5 = _ at r6
  change StateT.run (many input (bytes input)) p6 = _ at r7
  change StateT.run (parseChainConfig input) p7 = _ at r8
  change StateT.run (many input (bytes input)) p8 = _ at r9
  simp_all [StateT.run_bind]

private theorem parseSuccess_encode {mem : Std.ExtHashMap Nat (BitVec 8)} {address : Nat} :
    ParserEncodes parseSuccess encodeZesuDecodedResult (StatelessInputRep mem address) := by
  intro value rep pre suffix
  rcases rep with ⟨_fit, payload, versionedHashes, requests, parentRootSize, _parentRoot,
    witnessNodes, witnessCodes, witnessHeaders, chainConfig, publicKeys⟩
  have versionedHashesFits := versionedHashes.size_fits
  have witnessNodesFits := witnessNodes.size_fits
  have witnessCodesFits := witnessCodes.size_fits
  have witnessHeadersFits := witnessHeaders.size_fits
  have publicKeysFits := publicKeys.size_fits
  rcases versionedHashes with ⟨versionedHashesData, _, _, versionedHashElements⟩
  rcases witnessNodes with ⟨witnessNodesData, _, _, witnessNodeElements⟩
  rcases witnessCodes with ⟨witnessCodesData, _, _, witnessCodeElements⟩
  rcases witnessHeaders with ⟨witnessHeadersData, _, _, witnessHeaderElements⟩
  rcases publicKeys with ⟨publicKeysData, _, _, publicKeyElements⟩
  let e1 := encodePayload value.payload
  let e2 := value.parentBeaconBlockRoot
  let e3 := encodeMany (fun hash => hash) value.versionedHashes
  let e4 := encodeRequests value.executionRequests
  let e5 := encodeMany encodeBytes value.witnessNodes
  let e6 := encodeMany encodeBytes value.witnessCodes
  let e7 := encodeMany encodeBytes value.witnessHeaders
  let e8 := encodeChainConfig value.chainConfig
  let e9 := encodeMany encodeBytes value.publicKeys
  let input := pre ++ (e1 ++ (e2 ++ (e3 ++ (e4 ++ (e5 ++ (e6 ++ (e7 ++ (e8 ++
    (e9 ++ suffix)))))))))
  have a := parserReadPair_encode_in parsePayload_encode (take_fixed_parserEncodes 32)
    value.payload payload value.parentBeaconBlockRoot parentRootSize pre
    (e3 ++ e4 ++ e5 ++ e6 ++ e7 ++ e8 ++ e9 ++ suffix) input (by
      change input = pre ++ (e1 ++ (e2 ++ (e3 ++ e4 ++ e5 ++ e6 ++ e7 ++ e8 ++ e9 ++ suffix)))
      simp [input, Array.append_assoc])
  have b := parserReadPair_encode_in (fixedMany_parserEncodes 32) parseRequests_encode
    value.versionedHashes
    ⟨versionedHashesFits, fun index bound =>
      (versionedHashElements.2 index bound).1⟩
    value.executionRequests requests (pre ++ e1 ++ e2)
    (e5 ++ e6 ++ e7 ++ e8 ++ e9 ++ suffix) input (by
      change input = (pre ++ e1 ++ e2) ++ (e3 ++ (e4 ++ (e5 ++ e6 ++ e7 ++ e8 ++ e9 ++ suffix)))
      simp [input, Array.append_assoc])
  have c := parserReadPair_encode_in (many_parserEncodes bytes_parserEncodes)
    (many_parserEncodes bytes_parserEncodes) value.witnessNodes
    ⟨witnessNodesFits, fun index bound => (witnessNodeElements.2 index bound).size_fits⟩
    value.witnessCodes
    ⟨witnessCodesFits, fun index bound => (witnessCodeElements.2 index bound).size_fits⟩
    (pre ++ e1 ++ e2 ++ e3 ++ e4) (e7 ++ e8 ++ e9 ++ suffix) input
    (by simp [input, e5, e6, Array.append_assoc])
  have d := parserReadPair_encode_in (many_parserEncodes bytes_parserEncodes)
    parseChainConfig_encode value.witnessHeaders
    ⟨witnessHeadersFits, fun index bound => (witnessHeaderElements.2 index bound).size_fits⟩
    value.chainConfig chainConfig (pre ++ e1 ++ e2 ++ e3 ++ e4 ++ e5 ++ e6)
    (e9 ++ suffix) input (by simp [input, e7, e8, Array.append_assoc])
  have r9 := (many_parserEncodes bytes_parserEncodes) value.publicKeys
    ⟨publicKeysFits, fun index bound => (publicKeyElements.2 index bound).size_fits⟩
    (pre ++ e1 ++ e2 ++ e3 ++ e4 ++ e5 ++ e6 ++ e7 ++ e8) suffix
  have r9' : many input (bytes input) (pre ++ e1 ++ e2 ++ e3 ++ e4 ++ e5 ++ e6 ++ e7 ++ e8).size =
      some (value.publicKeys,
        (pre ++ e1 ++ e2 ++ e3 ++ e4 ++ e5 ++ e6 ++ e7 ++ e8).size + e9.size) := by
    simpa [input, e9, Array.append_assoc] using r9
  have r1 := a.firstRead
  have r2 := a.secondRead
  have r3 := b.firstRead
  have r4 := b.secondRead
  have r5 := c.firstRead
  have r6 := c.secondRead
  have r7 := d.firstRead
  have r8 := d.secondRead
  have parsed := parseSuccess_of_reads r1 r2 r3 r4 r5 r6 r7 r8 r9'
  simpa [input, e1, e2, e3, e4, e5, e6, e7, e8, e9,
    encodeZesuDecodedResult, Array.size_append, Array.append_assoc, Nat.add_assoc]
    using parsed

/-- The endpoint observation parser accepts the exact successful stream emitted from any represented
decoded value. -/
theorem decodeZesuObservation_encode_success_of_rep
    {mem : Std.ExtHashMap Nat (BitVec 8)} {address : Nat} {decoded : ZesuDecodedResult}
    (rep : StatelessInputRep mem address decoded) :
    decodeZesuObservation (encodeZesuObservation (.success decoded)) = some (.success decoded) := by
  have parsed := parseSuccess_encode decoded rep #[0x5a, 0x53, 0x53, 0x5a, 0x01, 0x01] #[]
  have parsed' : parseSuccess
      (#[0x5a, 0x53, 0x53, 0x5a, 0x01, 0x01] ++ encodeZesuDecodedResult decoded) 6 =
      some (decoded, 6 + (encodeZesuDecodedResult decoded).size) := by
    simpa using parsed
  have tag : byte
      (#[0x5a, 0x53, 0x53, 0x5a, 0x01, 0x01] ++ encodeZesuDecodedResult decoded) 5 =
      some (1, 6) := by
    simpa [byte, encodeNatLE] using unsigned_encodeNatLE 1 1 (by decide)
      #[0x5a, 0x53, 0x53, 0x5a, 0x01] (encodeZesuDecodedResult decoded)
  change StateT.run (byte
    (#[0x5a, 0x53, 0x53, 0x5a, 0x01, 0x01] ++ encodeZesuDecodedResult decoded)) 5 = _ at tag
  change StateT.run (parseSuccess
    (#[0x5a, 0x53, 0x53, 0x5a, 0x01, 0x01] ++ encodeZesuDecodedResult decoded)) 6 = _ at parsed'
  simp [decodeZesuObservation, encodeZesuObservation, StateT.run_bind, tag, parsed', guard]

end BinaryFv.Zesu
