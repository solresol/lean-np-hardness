import LeanNPHardness.CanonicalMembershipMachine

/-!
# Polynomial-time membership under a framed Boolean encoding

The input is a framed binary natural followed by a complete framed natural
list, including its length. The decoder proves this is a finite encoding of
`Nat × List Nat`. The existing canonical seven-stack TM2 machine computes
membership with polynomial `X * (4 * X + 20) + 9` in the full input bit length.

Encoding correctness, Boolean semantics, and machine runtime are separate
results. The machine contract is on canonical encodings; it does not assert
rejection of arbitrary malformed bit streams or a complete SAT verifier.
-/

namespace LeanNPHardness

open Computability Turing

namespace FramedNatListQuery

/-- A query followed by a length-prefixed list; repetitions are retained. -/
def encode (input : Nat × List Nat) : List Bool :=
  BinaryNatLists.encodeNat input.1 ++ BinaryNatLists.encodeNatList input.2

/-- Decode the query and list while retaining the unconsumed suffix. -/
def decodePrefix (bits : List Bool) : Option ((Nat × List Nat) × List Bool) := do
  let (query, rest) ← BinaryNatLists.decodeNatPrefix bits
  let (xs, suffix) ← BinaryNatLists.decodeNatListPrefix rest
  pure ((query, xs), suffix)

@[simp]
theorem decodePrefix_encode_append (input : Nat × List Nat) (suffix : List Bool) :
    decodePrefix (encode input ++ suffix) = some (input, suffix) := by
  simp [decodePrefix, encode, List.append_assoc]

/-- Require that the encoded query and list exhaust the supplied input. -/
def decode (bits : List Bool) : Option (Nat × List Nat) := do
  let (input, rest) ← decodePrefix bits
  if rest = [] then some input else none

@[simp]
theorem decode_encode (input : Nat × List Nat) :
    decode (encode input) = some input := by
  have parsed := decodePrefix_encode_append input []
  simp only [List.append_nil] at parsed
  rw [decode, parsed]
  rfl

/-- A canonical encoding cannot hide a nonempty trailing suffix. -/
theorem decode_encode_append_nonempty (input : Nat × List Nat)
    (suffix : List Bool) (nonempty : suffix ≠ []) :
    decode (encode input ++ suffix) = none := by
  simp [decode, nonempty]

/-- Finite Boolean encoding matching the serialized-membership machine input. -/
def finEncoding : FinEncoding (Nat × List Nat) where
  Γ := Bool
  encode := encode
  decode := decode
  decode_encode := decode_encode
  ΓFin := Bool.fintype

theorem encode_eq_serialized (input : Nat × List Nat) :
    encode input = MachinePrimitives.SerializedMembership.encodeInput input.1 input.2 := rfl

theorem encode_length (input : Nat × List Nat) :
    (encode input).length = (BinaryNatLists.encodeNat input.1).length +
      (BinaryNatLists.encodeNatList input.2).length := List.length_append

end FramedNatListQuery

namespace MachinePrimitives.CanonicalMembership

/-- Boolean membership, separately from its encoded-machine implementation. -/
def membership (input : Nat × List Nat) : Bool := decide (input.1 ∈ input.2)

theorem membership_eq_true_iff (input : Nat × List Nat) :
    membership input = true ↔ input.1 ∈ input.2 := by
  simp [membership]

theorem membership_eq_false_iff (input : Nat × List Nat) :
    membership input = false ↔ input.1 ∉ input.2 := by
  simp [membership]

/-- Runtime in the entire framed input's bit length, including final halting. -/
noncomputable def timePolynomial : Polynomial Nat :=
  Polynomial.X * (4 * Polynomial.X + 20) + 9

@[simp]
theorem timePolynomial_eval (n : Nat) :
    timePolynomial.eval n = n * (4 * n + 20) + 9 := by
  simp [timePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_X]

/-- A function-level polynomial-time witness using the existing canonical machine. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime FramedNatListQuery.finEncoding finEncodingBoolBool membership where
  tm := computer
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := timePolynomial
  outputsFun input := by
    simpa [FramedNatListQuery.finEncoding, FramedNatListQuery.encode_eq_serialized,
      finEncodingBoolBool, membership, Equiv.refl] using outputsInTime input.1 input.2

end MachinePrimitives.CanonicalMembership

end LeanNPHardness
