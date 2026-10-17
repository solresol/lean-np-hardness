import LeanNPHardness.FirstMatchMachine

/-!
# Polynomial-time lookup of a natural in an ordered dictionary

The semantic input is `(query, dictionary)`. Its Boolean encoding is exactly
the existing serialized first-member input `(dictionary, [query])`; decoding
requires a singleton query list and exhaustion of the complete stream.

The existing finite TM2 machine therefore computes `List.idxOf` with its
unchanged polynomial in the complete input bit length. Output is unary,
including the dictionary-length sentinel for an absent query. Repeated
dictionary entries retain first-occurrence semantics. Dictionary construction,
preservation across lookups, and CNF traversal are separate obligations.
-/

namespace LeanNPHardness

open Computability Turing

namespace FramedNatLookup

/-- Serialize a direct lookup as the existing singleton-membership problem. -/
def encode (input : Nat × List Nat) : List Bool :=
  FramedNatListQueries.encode (input.2, [input.1])

/-- Reject non-singleton query lists and any trailing data. This is the
encoding decoder, not a claim about machine behavior on malformed streams. -/
def decode (bits : List Bool) : Option (Nat × List Nat) := do
  let (dictionary, queries) ← FramedNatListQueries.decode bits
  match queries with
  | [query] => some (query, dictionary)
  | _ => none

@[simp]
theorem decode_serialized (dictionary queries : List Nat) :
    decode (FramedNatListQueries.encode (dictionary, queries)) =
      match queries with
      | [query] => some (query, dictionary)
      | _ => none := by
  simp [decode]

@[simp]
theorem decode_encode (input : Nat × List Nat) :
    decode (encode input) = some input := by
  simp [encode]

theorem decode_reject_non_singleton (dictionary queries : List Nat)
    (h : queries.length ≠ 1) :
    decode (FramedNatListQueries.encode (dictionary, queries)) = none := by
  rw [decode_serialized]
  cases queries with
  | nil => rfl
  | cons q rest =>
      cases rest with
      | nil => simp at h
      | cons r rest => rfl

theorem decode_encode_append_nonempty (input : Nat × List Nat)
    (suffix : List Bool) (nonempty : suffix ≠ []) :
    decode (encode input ++ suffix) = none := by
  simp [decode, encode,
    FramedNatListQueries.decode_encode_append_nonempty _ suffix nonempty]

/-- Finite encoding for direct lookup; the singleton representation adds no
machine conversion step because it defines the input wire format itself. -/
def finEncoding : FinEncoding (Nat × List Nat) where
  Γ := Bool
  encode := encode
  decode := decode
  decode_encode := decode_encode
  ΓFin := Bool.fintype

theorem encode_injective : Function.Injective encode := by
  intro input other equal
  have decoded := congrArg decode equal
  simpa using decoded

/-- Full bit size includes the outer query frame, singleton-list header,
query payload and complete dictionary encoding. -/
theorem encode_length (input : Nat × List Nat) :
    (encode input).length =
      2 * (BinaryNatLists.natWireSize 1 + BinaryNatLists.natWireSize input.1) +
        1 + BinaryNatLists.listWireSize input.2 := by
  rw [encode, FramedNatListQueries.encode_length]
  simp [BinaryNatLists.listWireSize]

end FramedNatLookup

namespace MachinePrimitives.DictionaryLookup

/-- First occurrence, or the dictionary length when the query is absent. -/
def lookup (input : Nat × List Nat) : Nat := input.2.idxOf input.1

theorem lookup_eq_length_iff (input : Nat × List Nat) :
    lookup input = input.2.length ↔ input.1 ∉ input.2 := by
  exact List.idxOf_eq_length_iff

theorem lookup_getElem? (input : Nat × List Nat) (h : input.1 ∈ input.2) :
    input.2[lookup input]? = some input.1 :=
  List.getElem?_idxOf h

/-- Unary result size is bounded by the complete serialized input size. -/
theorem lookup_le_encode_length (input : Nat × List Nat) :
    lookup input ≤ (FramedNatLookup.encode input).length := by
  have indexBound := List.idxOf_le_length (l := input.2) (a := input.1)
  have dictionaryBound := BinaryNatLists.length_le_listWireSize input.2
  rw [FramedNatLookup.encode_length]
  change input.2.idxOf input.1 ≤ _
  omega

/-- Reuse the complete first-member machine and its polynomial, with no
runtime charge for a semantic reindexing of the identical encoded input. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime FramedNatLookup.finEncoding unaryFinEncodingNat lookup where
  tm := FirstMatch.firstMemberComputableInPolyTime.tm
  inputAlphabet := FirstMatch.firstMemberComputableInPolyTime.inputAlphabet
  outputAlphabet := FirstMatch.firstMemberComputableInPolyTime.outputAlphabet
  time := FirstMatch.firstMemberComputableInPolyTime.time
  outputsFun input := by
    simpa only [FramedNatLookup.finEncoding, FramedNatLookup.encode,
      FramedNatListQueries.finEncoding, FirstMatch.firstMember_singleton, lookup] using
      FirstMatch.firstMemberComputableInPolyTime.outputsFun (input.2, [input.1])

/-- Direct lookup agrees with the semantic dense-renaming index. -/
theorem lookup_denseIndex (F : CNF.Formula Nat) (query : Nat) :
    lookup (query, F.variableDictionary) = F.denseIndex query := rfl

end MachinePrimitives.DictionaryLookup

end LeanNPHardness
