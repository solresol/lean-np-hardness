import LeanNPHardness.BinaryNatLists
import LeanNPHardness.CNF
import LeanNPHardness.ComplexityClasses

/-!
# Binary encodings of CNF languages

Encode a positive literal on variable `v` by `2 * v` and a negative literal by
`2 * v + 1`. The checked `BinaryNatLists` framing then retains every literal,
clause boundary, empty clause, and repetition. Input size is the exact number
of bits in this encoding. These constructions make no machine-runtime claim.
-/

namespace LeanNPHardness.CNF

namespace Literal

/-- Pack the variable and polarity into one natural number. -/
def toNat : Literal Nat → Nat
  | .positive v => 2 * v
  | .negative v => 2 * v + 1

/-- Recover polarity from parity and the variable from division by two. -/
def ofNat (code : Nat) : Literal Nat :=
  if code % 2 = 0 then .positive (code / 2) else .negative (code / 2)

@[simp]
theorem ofNat_toNat (literal : Literal Nat) :
    ofNat literal.toNat = literal := by
  cases literal <;> simp [toNat, ofNat, Nat.add_div, Nat.add_mod]

/-- Literal serialization distinguishes both polarity and variable. -/
theorem toNat_injective : Function.Injective toNat := by
  intro left right equal
  simpa using congrArg ofNat equal

end Literal

namespace Formula

/-- Retain the entire nested-list shape while packing literal polarity. -/
def toNatLists (formula : Formula Nat) : List (List Nat) :=
  formula.map (List.map Literal.toNat)

/-- Interpret each packed literal without removing or reordering occurrences. -/
def ofNatLists (rows : List (List Nat)) : Formula Nat :=
  rows.map (List.map Literal.ofNat)

@[simp]
theorem ofNatLists_toNatLists (formula : Formula Nat) :
    ofNatLists formula.toNatLists = formula := by
  simp [ofNatLists, toNatLists, List.map_map, Function.comp_def]

/-- The natural-list representation preserves each clause's exact width. -/
theorem toNatLists_clause_lengths (formula : Formula Nat) :
    (formula.toNatLists.map List.length) = formula.map List.length := by
  simp [toNatLists, List.map_map, Function.comp_def]

/-- Binary serialization with framed formula and clause lengths. -/
def encode (formula : Formula Nat) : List Bool :=
  BinaryNatLists.encode formula.toNatLists

/-- Decode a whole framed formula, using the underlying decoder's suffix check. -/
def decode (bits : List Bool) : Option (Formula Nat) :=
  (BinaryNatLists.decode bits).map ofNatLists

@[simp]
theorem decode_encode (formula : Formula Nat) :
    decode formula.encode = some formula := by
  simp [decode, encode]

/-- The Boolean alphabet fixes the bit-level input-size convention for CNF. -/
def finEncoding : Computability.FinEncoding (Formula Nat) where
  Γ := Bool
  encode := encode
  decode := decode
  decode_encode := decode_encode
  ΓFin := inferInstance

/-- Distinct formulas, including distinct empty/repeated clause shapes, have
distinct encodings. -/
theorem encode_injective : Function.Injective encode :=
  finEncoding.toEncoding.encode_injective

/-- Exact bit count: the formula-length frame, each clause-length frame, and
the framed packed literal codes. -/
def encodedSize (formula : Formula Nat) : Nat :=
  BinaryNatLists.natWireSize formula.length +
    (formula.map fun clause =>
      BinaryNatLists.natWireSize clause.length +
        (clause.map fun literal => BinaryNatLists.natWireSize literal.toNat).sum).sum

/-- The public size measure is exactly the length of the serialized bit list. -/
@[simp]
theorem encode_length (formula : Formula Nat) :
    formula.encode.length = formula.encodedSize := by
  simp [encode, encodedSize, BinaryNatLists.wireSize,
    BinaryNatLists.listWireSize, toNatLists, List.map_map, Function.comp_def]

@[simp]
theorem finEncoding_encode_length (formula : Formula Nat) :
    (finEncoding.encode formula).length = formula.encodedSize :=
  encode_length formula

end Formula

/-- CNF-SAT paired with the checked binary formula encoding. -/
def encodedSAT : EncodedLanguage (Formula Nat) where
  encoding := Formula.finEncoding
  accepts := SAT

/-- Exact k-SAT uses the same formula encoding and counts every occurrence. -/
def encodedExactKSAT (k : Nat) : EncodedLanguage (Formula Nat) where
  encoding := Formula.finEncoding
  accepts := ExactKSAT k

/-- The encoded exact-three-literal language for subsequent complexity proofs. -/
abbrev encodedExactThreeSAT : EncodedLanguage (Formula Nat) :=
  encodedExactKSAT 3

@[simp]
theorem encodedSAT_accepts (formula : Formula Nat) :
    encodedSAT.accepts formula ↔ formula.Satisfiable := Iff.rfl

@[simp]
theorem encodedExactKSAT_accepts (k : Nat) (formula : Formula Nat) :
    (encodedExactKSAT k).accepts formula ↔
      0 < k ∧ formula.ExactWidth k ∧ formula.Satisfiable := Iff.rfl

end LeanNPHardness.CNF
