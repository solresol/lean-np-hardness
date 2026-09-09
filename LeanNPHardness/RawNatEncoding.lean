import LeanNPHardness.BinaryNatLists

/-!
Reusable encoding and machine components extracted from `phd-thesis-lean`
commit `84be78db5a287f9a40dcb549252063d6db67de73`. Runtime bounds retain
the original explicit finite-alphabet input encodings.
-/

namespace LeanNPHardness

open Computability

namespace FramedNat

/-- Decode one framed natural and require that the complete input was used. -/
def decode (bits : List Bool) : Option ℕ := do
  let (n, rest) ← BinaryNatLists.decodeNatPrefix bits
  if rest = [] then some n else none

@[simp]
theorem decode_encode (n : ℕ) :
    decode (BinaryNatLists.encodeNat n) = some n := by
  have h := BinaryNatLists.decodeNatPrefix_encodeNat_append n []
  have h' : BinaryNatLists.decodeNatPrefix (BinaryNatLists.encodeNat n) =
      some (n, []) := by
    simpa using h
  rw [decode, h']
  rfl

/-- The self-delimiting binary natural encoding used inside the runtime CSP
wire format. -/
def finEncoding : FinEncoding ℕ where
  Γ := Bool
  encode := BinaryNatLists.encodeNat
  decode := decode
  decode_encode := decode_encode
  ΓFin := Bool.fintype

end FramedNat

namespace FramedNatList

/-- Decode one complete length-prefixed list of framed naturals. -/
def decode (bits : List Bool) : Option (List ℕ) := do
  let (xs, rest) ← BinaryNatLists.decodeNatListPrefix bits
  if rest = [] then some xs else none

@[simp]
theorem decode_encode (xs : List ℕ) :
    decode (BinaryNatLists.encodeNatList xs) = some xs := by
  have h := BinaryNatLists.decodeNatListPrefix_encode_append xs []
  have h' :
      BinaryNatLists.decodeNatListPrefix
          (BinaryNatLists.encodeNatList xs) = some (xs, []) := by
    simpa using h
  rw [decode, h']
  rfl

/-- The exact framed natural-list encoding used inside the runtime CSP wire
format. -/
def finEncoding : FinEncoding (List ℕ) where
  Γ := Bool
  encode := BinaryNatLists.encodeNatList
  decode := decode
  decode_encode := decode_encode
  ΓFin := Bool.fintype

end FramedNatList

namespace RawNatList

/-- One raw binary payload, reversed for stack consumption and terminated by
an explicit field marker. -/
def segment (bits : List Bool) : List (Option Bool) :=
  bits.reverse.map some ++ [none]

/-- The binary length field followed by the binary value fields. -/
def payloads (xs : List ℕ) : List (List Bool) :=
  Computability.encodeNat xs.length :: xs.map Computability.encodeNat

/-- A stack-oriented natural-list representation. Fields occur in reverse
order, and every field's bits occur in reverse order, so a stack traversal can
prepend the corresponding framed fields in their canonical order. -/
def encode (xs : List ℕ) : List (Option Bool) :=
  (payloads xs).reverse.flatMap segment

/-- Parse a raw field stream. `current` is accumulated by consing the reversed
input bits; completed fields are consed into `fields`, restoring both orders. -/
def parseAux :
    List (Option Bool) → List Bool → List (List Bool) →
      Option (List (List Bool))
  | [], [], fields => some fields
  | [], _ :: _, _ => none
  | none :: input, current, fields =>
      parseAux input [] (current :: fields)
  | some bit :: input, current, fields =>
      parseAux input (bit :: current) fields

/-- Parse the complete stack-oriented field stream. -/
def parse (input : List (Option Bool)) : Option (List (List Bool)) :=
  parseAux input [] []

private theorem parseAux_some_append
    (bits : List Bool) (input : List (Option Bool))
    (current : List Bool) (fields : List (List Bool)) :
    parseAux (bits.map some ++ input) current fields =
      parseAux input (bits.reverse ++ current) fields := by
  induction bits generalizing current with
  | nil => simp
  | cons bit bits ih =>
      simp [parseAux, ih, List.reverse_cons, List.append_assoc]

private theorem parseAux_segments
    (segments : List (List Bool)) (fields : List (List Bool)) :
    parseAux (segments.flatMap segment) [] fields =
      some (segments.reverse ++ fields) := by
  induction segments generalizing fields with
  | nil => simp [parseAux]
  | cons bits segments ih =>
      rw [List.flatMap_cons]
      simp only [segment, List.append_assoc]
      rw [parseAux_some_append]
      simp only [List.reverse_reverse]
      simp only [List.singleton_append, parseAux]
      rw [ih]
      simp [List.reverse_cons, List.append_assoc]

/-- Parsing any complete sequence of stack-oriented raw segments restores the
semantic field order. -/
theorem parse_segments (segments : List (List Bool)) :
    parse (segments.flatMap segment) = some segments.reverse := by
  simpa [parse] using parseAux_segments segments []

@[simp]
theorem parse_encode (xs : List ℕ) :
    parse (encode xs) = some (payloads xs) := by
  rw [parse, encode, parseAux_segments]
  simp

/-- Decode the stack-oriented representation, checking its explicit field
count before accepting it. -/
def decode (input : List (Option Bool)) : Option (List ℕ) := do
  let fields ← parse input
  match fields with
  | [] => none
  | countBits :: valueBits =>
      if Computability.decodeNat countBits = valueBits.length then
        some (valueBits.map Computability.decodeNat)
      else
        none

@[simp]
theorem decode_encode (xs : List ℕ) : decode (encode xs) = some xs := by
  simp [decode, payloads, Function.comp_def]

/-- A checked finite encoding for the stack-oriented raw natural-list stream. -/
def finEncoding : FinEncoding (List ℕ) where
  Γ := Option Bool
  encode := encode
  decode := decode
  decode_encode := decode_encode
  ΓFin := inferInstance

end RawNatList

namespace RawUnaryNatList

/-- One unary natural followed by a false field delimiter. -/
def segment (n : ℕ) : List Bool :=
  List.replicate n true ++ [false]

/-- The unary length field followed by the unary value fields. -/
def payloads (xs : List ℕ) : List ℕ :=
  xs.length :: xs

/-- A stack-oriented unary natural-list representation. Fields occur in
reverse order so a producer can prepend each successive field to its output
stack. -/
def encode (xs : List ℕ) : List Bool :=
  (payloads xs).reverse.flatMap segment

/-- Parse unary fields, accumulating the current field length and consing each
completed field so that the outer reversal is restored. -/
def parseAux : List Bool → ℕ → List ℕ → Option (List ℕ)
  | [], 0, fields => some fields
  | [], _ + 1, _ => none
  | false :: input, current, fields =>
      parseAux input 0 (current :: fields)
  | true :: input, current, fields =>
      parseAux input (current + 1) fields

def parse (input : List Bool) : Option (List ℕ) :=
  parseAux input 0 []

private theorem parseAux_replicate_true
    (n : ℕ) (input : List Bool) (current : ℕ) (fields : List ℕ) :
    parseAux (List.replicate n true ++ input) current fields =
      parseAux input (current + n) fields := by
  induction n generalizing current with
  | zero => simp
  | succ n ih =>
      rw [List.replicate_succ]
      simp only [List.cons_append, parseAux]
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (current := current + 1)

private theorem parseAux_segments
    (segments : List ℕ) (fields : List ℕ) :
    parseAux (segments.flatMap segment) 0 fields =
      some (segments.reverse ++ fields) := by
  induction segments generalizing fields with
  | nil => simp [parseAux]
  | cons n segments ih =>
      rw [List.flatMap_cons]
      simp only [segment, List.append_assoc]
      rw [parseAux_replicate_true]
      simp only [List.singleton_append, parseAux, Nat.zero_add]
      rw [ih]
      simp [List.reverse_cons, List.append_assoc]

@[simp]
theorem parse_encode (xs : List ℕ) :
    parse (encode xs) = some (payloads xs) := by
  rw [parse, encode, parseAux_segments]
  simp

/-- Decode the unary field stream, checking its explicit field count. -/
def decode (input : List Bool) : Option (List ℕ) := do
  let fields ← parse input
  match fields with
  | [] => none
  | count :: values =>
      if count = values.length then some values else none

@[simp]
theorem decode_encode (xs : List ℕ) : decode (encode xs) = some xs := by
  simp [decode, payloads]

/-- Checked finite encoding for a stack-oriented unary natural list. -/
def finEncoding : FinEncoding (List ℕ) where
  Γ := Bool
  encode := encode
  decode := decode
  decode_encode := decode_encode
  ΓFin := Bool.fintype

@[simp]
theorem segment_length (n : ℕ) : (segment n).length = n + 1 := by
  simp [segment]

private theorem segments_length (ns : List ℕ) :
    (ns.flatMap segment).length = ns.sum + ns.length := by
  induction ns with
  | nil => simp
  | cons n ns ih =>
      simp [segment, ih]
      omega

@[simp]
theorem encode_length (xs : List ℕ) :
    (encode xs).length = xs.sum + 2 * xs.length + 1 := by
  rw [encode, segments_length]
  simp [payloads]
  omega

end RawUnaryNatList

namespace RawNatLists

/-- Raw binary payloads underlying the standard nested-list encoding: the
outer length, then each inner length and its natural fields. -/
def payloads (xss : List (List ℕ)) : List (List Bool) :=
  Computability.encodeNat xss.length ::
    xss.flatMap fun xs =>
      Computability.encodeNat xs.length :: xs.map Computability.encodeNat

/-- A stack-oriented nested-list representation. Every raw field is reversed
and delimited, and the complete field sequence is reversed for stack
consumption. -/
def encode (xss : List (List ℕ)) : List (Option Bool) :=
  (payloads xss).reverse.flatMap RawNatList.segment

private theorem parseAux_some_append
    (bits : List Bool) (input : List (Option Bool))
    (current : List Bool) (fields : List (List Bool)) :
    RawNatList.parseAux (bits.map some ++ input) current fields =
      RawNatList.parseAux input (bits.reverse ++ current) fields := by
  induction bits generalizing current with
  | nil => simp
  | cons bit bits ih =>
      simp [RawNatList.parseAux, ih, List.reverse_cons, List.append_assoc]

private theorem parseAux_segments
    (segments : List (List Bool)) (fields : List (List Bool)) :
    RawNatList.parseAux
        (segments.flatMap RawNatList.segment) [] fields =
      some (segments.reverse ++ fields) := by
  induction segments generalizing fields with
  | nil => simp [RawNatList.parseAux]
  | cons bits segments ih =>
      rw [List.flatMap_cons]
      simp only [RawNatList.segment, List.append_assoc]
      rw [parseAux_some_append]
      simp only [List.reverse_reverse]
      simp only [List.singleton_append, RawNatList.parseAux]
      rw [ih]
      simp [List.reverse_cons, List.append_assoc]

@[simp]
theorem parse_encode (xss : List (List ℕ)) :
    RawNatList.parse (encode xss) = some (payloads xss) := by
  rw [RawNatList.parse, encode, parseAux_segments]
  simp

private theorem innerPayloads_frame
    (xss : List (List ℕ)) :
    List.flatMap BinaryNatLists.frame
        (xss.flatMap fun xs =>
          Computability.encodeNat xs.length :: xs.map Computability.encodeNat) =
      xss.flatMap BinaryNatLists.encodeNatList := by
  induction xss with
  | nil => rfl
  | cons xs xss ih =>
      simp only [List.flatMap_cons, List.flatMap_append,
        List.flatMap_cons, List.flatMap_map, ih]
      simp only [BinaryNatLists.encodeNatList]
      have hencode :
          (fun n => BinaryNatLists.frame (Computability.encodeNat n)) =
            BinaryNatLists.encodeNat := by
        funext n
        rfl
      rw [hencode]
      rfl

theorem payloads_frame_eq_encode (xss : List (List ℕ)) :
    (payloads xss).flatMap BinaryNatLists.frame =
      BinaryNatLists.encode xss := by
  rw [payloads, List.flatMap_cons, BinaryNatLists.encode,
    innerPayloads_frame]
  rfl

/-- Decode a raw field stream by restoring the standard nested-list frames. -/
def decode (input : List (Option Bool)) : Option (List (List ℕ)) := do
  let fields ← RawNatList.parse input
  BinaryNatLists.decode (fields.flatMap BinaryNatLists.frame)

@[simp]
theorem decode_encode (xss : List (List ℕ)) :
    decode (encode xss) = some xss := by
  simp [decode, payloads_frame_eq_encode]

/-- Checked raw-field encoding of nested natural-number lists. -/
def finEncoding : FinEncoding (List (List ℕ)) where
  Γ := Option Bool
  encode := encode
  decode := decode
  decode_encode := decode_encode
  ΓFin := inferInstance

end RawNatLists

namespace SourceOrderRawNatLists

/-!
`RawNatLists` is arranged for direct stack consumption, so its fields occur in
reverse semantic order.  The structural producer needs the compact CSP header
before its domain and scope fields.  This companion encoding reverses the
complete raw stream: fields then occur in semantic source order, each with a
leading delimiter followed by its canonical least-significant-bit-first
payload.
-/

/-- The raw nested-list fields in semantic source order. -/
def encode (xss : List (List ℕ)) : List (Option Bool) :=
  (RawNatLists.encode xss).reverse

/-- Decode by restoring the checked stack-oriented raw representation. -/
def decode (input : List (Option Bool)) : Option (List (List ℕ)) :=
  RawNatLists.decode input.reverse

@[simp]
theorem decode_encode (xss : List (List ℕ)) :
    decode (encode xss) = some xss := by
  simp [decode, encode]

/-- Source-order fields are the semantic payload sequence, with each field
represented by a leading delimiter and its canonical binary bits. -/
theorem encode_eq_payloads (xss : List (List ℕ)) :
    encode xss =
      (RawNatLists.payloads xss).flatMap
        (fun bits => none :: bits.map some) := by
  rw [encode, RawNatLists.encode, List.reverse_flatMap,
    List.reverse_reverse]
  simp [RawNatList.segment, Function.comp_def]

/-- Checked finite encoding for source-order raw nested-list fields. -/
def finEncoding : FinEncoding (List (List ℕ)) where
  Γ := Option Bool
  encode := encode
  decode := decode
  decode_encode := decode_encode
  ΓFin := inferInstance

end SourceOrderRawNatLists

namespace SourceOrderRawFields

/-!
Unlike `SourceOrderRawNatLists`, this encoding carries an uncounted sequence
of natural fields.  It is the local interface needed by structural-emitter
components: each field begins with a delimiter and is followed by its
canonical least-significant-bit-first payload.
-/

/-- Encode an uncounted natural-field sequence in semantic source order. -/
def encode (fields : List ℕ) : List (Option Bool) :=
  fields.flatMap fun field =>
    none :: (Computability.encodeNat field).map some

/-- Decode a complete source-order raw-field sequence. -/
def decode (input : List (Option Bool)) : Option (List ℕ) := do
  let payloads ← RawNatList.parse input.reverse
  pure (payloads.map Computability.decodeNat)

private theorem encode_reverse_eq_segments (fields : List ℕ) :
    (encode fields).reverse =
      ((fields.map Computability.encodeNat).reverse).flatMap
        RawNatList.segment := by
  induction fields with
  | nil => rfl
  | cons field fields ih =>
      rw [encode, List.flatMap_cons, List.reverse_append]
      change (encode fields).reverse ++
          (none :: (Computability.encodeNat field).map some).reverse = _
      rw [ih]
      simp [RawNatList.segment, List.reverse_cons]

@[simp]
theorem decode_encode (fields : List ℕ) :
    decode (encode fields) = some fields := by
  rw [decode, encode_reverse_eq_segments, RawNatList.parse_segments]
  simp [Function.comp_def]

/-- Checked encoding for uncounted semantic-order natural fields. -/
def finEncoding : FinEncoding (List ℕ) where
  Γ := Option Bool
  encode := encode
  decode := decode
  decode_encode := decode_encode
  ΓFin := inferInstance

end SourceOrderRawFields

end LeanNPHardness
