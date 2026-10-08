import LeanNPHardness.CanonicalQueryMembershipMachine
import LeanNPHardness.BooleanListMachine
import LeanNPHardness.RawNatEncoding

/-!
# Polynomial-time repeated membership under a serialized Boolean encoding

The semantic input is `(queries, certificate) : List Nat × List Nat`. Its
encoding puts a frame around the complete certificate encoding, followed by
the complete query-list encoding. The decoder checks that the certificate
occupies its entire frame and proves the finite encoding's round trip.

The existing canonical nine-stack TM2 machine computes one membership bit per
query occurrence in reverse query order, with polynomial
`X * (X * (2 * X + 18) + 8 * X + 27) + 9` in the entire input's bit length.
Encoding correctness, list semantics, and runtime are separate results. This
contract concerns canonical encodings; machine rejection of malformed streams,
literal/formula evaluation, and the complete SAT verifier remain separate.
-/

namespace LeanNPHardness

open Computability Turing

namespace FramedNatListQueries

/-- The certificate is serialized first; both lists retain every occurrence. -/
def encode (input : List Nat × List Nat) : List Bool :=
  BinaryNatLists.frame (BinaryNatLists.encodeNatList input.2) ++
    BinaryNatLists.encodeNatList input.1

/-- Parse the outer certificate frame and queries, retaining the trailing suffix. -/
def decodePrefix (bits : List Bool) : Option ((List Nat × List Nat) × List Bool) := do
  let (count, payload) ← BinaryNatLists.readUnary bits
  let (certificateBits, rest) ← BinaryNatLists.readBits count payload
  let certificate ← FramedNatList.decode certificateBits
  let (queries, suffix) ← BinaryNatLists.decodeNatListPrefix rest
  pure ((queries, certificate), suffix)

@[simp]
theorem decodePrefix_encode_append (input : List Nat × List Nat) (suffix : List Bool) :
    decodePrefix (encode input ++ suffix) = some (input, suffix) := by
  simp [-BinaryNatLists.encodeNatList_length, decodePrefix, encode,
    BinaryNatLists.frame, List.append_assoc]

/-- Require that the encoded pair exhaust the supplied input. -/
def decode (bits : List Bool) : Option (List Nat × List Nat) := do
  let (input, rest) ← decodePrefix bits
  if rest = [] then some input else none

@[simp]
theorem decode_encode (input : List Nat × List Nat) :
    decode (encode input) = some input := by
  have parsed := decodePrefix_encode_append input []
  simp only [List.append_nil] at parsed
  rw [decode, parsed]
  rfl

/-- The decoder rejects nonempty data after a complete canonical pair. -/
theorem decode_encode_append_nonempty (input : List Nat × List Nat)
    (suffix : List Bool) (nonempty : suffix ≠ []) :
    decode (encode input ++ suffix) = none := by
  simp [decode, nonempty]

/-- Finite Boolean encoding matching the serialized repeated-membership input. -/
def finEncoding : FinEncoding (List Nat × List Nat) where
  Γ := Bool
  encode := encode
  decode := decode
  decode_encode := decode_encode
  ΓFin := Bool.fintype

theorem encode_injective : Function.Injective encode := by
  intro input other equal
  have decoded := congrArg decode equal
  simpa using decoded

theorem encode_eq_serialized (input : List Nat × List Nat) :
    encode input =
      MachinePrimitives.SerializedQueryMembership.encodeInput input.1 input.2 := rfl

/-- Full bit size includes the certificate's outer frame and both list headers. -/
theorem encode_length (input : List Nat × List Nat) :
    (encode input).length =
      2 * BinaryNatLists.listWireSize input.2 + 1 +
        BinaryNatLists.listWireSize input.1 := by
  simp [encode]

end FramedNatListQueries

namespace MachinePrimitives.CanonicalQueryMembership

/-- One Boolean per query occurrence, in the machine's reverse output order. -/
def membershipResults (input : List Nat × List Nat) : List Bool :=
  (input.1.map fun query => decide (query ∈ input.2)).reverse

theorem membershipResults_eq_results (input : List Nat × List Nat) :
    membershipResults input = QueryMembershipLoop.results input.1 input.2 := rfl

/-- Reversing the output restores the original query order. -/
theorem membershipResults_reverse (input : List Nat × List Nat) :
    (membershipResults input).reverse =
      input.1.map (fun query => decide (query ∈ input.2)) := by
  simp [membershipResults]

/-- Repeated queries each contribute an output bit, including on empty certificates. -/
theorem membershipResults_length (input : List Nat × List Nat) :
    (membershipResults input).length = input.1.length := by
  simp [membershipResults]

/-- Runtime in the complete serialized bit length, including cleanup and halting. -/
noncomputable def timePolynomial : Polynomial Nat :=
  Polynomial.X * (Polynomial.X * (2 * Polynomial.X + 18) +
    8 * Polynomial.X + 27) + 9

@[simp]
theorem timePolynomial_eval (n : Nat) :
    timePolynomial.eval n = n * (n * (2 * n + 18) + 8 * n + 27) + 9 := by
  simp [timePolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X]

/-- Polynomial-time repeated membership using the existing canonical TM2 machine. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime FramedNatListQueries.finEncoding RawBoolList.finEncoding
      membershipResults where
  tm := computer
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := timePolynomial
  outputsFun input := by
    simpa [FramedNatListQueries.finEncoding, FramedNatListQueries.encode_eq_serialized,
      membershipResults_eq_results, Equiv.refl] using outputsInTime input.1 input.2

end MachinePrimitives.CanonicalQueryMembership

end LeanNPHardness
