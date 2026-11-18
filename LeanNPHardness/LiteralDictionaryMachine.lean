import LeanNPHardness.LiteralVariableMachine
import LeanNPHardness.DictionaryLookupEncoding

/-!
# Polynomial-time literal lookup with retained source and context

Extract the variable from a packed literal and look it up in a supplied
framed dictionary. The result is a unary index, with dictionary length as
the absence sentinel. Checked duplication retains the complete source
literal (including polarity) and the dictionary. A pair-left wrapper also
retains an independently encoded context, for example remaining formula data.

All copying, conversion, lookup, loading and return transfers are charged by
the existing finite TM2 composition and pair-adapter polynomials in the full
original tagged input length. Output size is bounded separately. This is a
canonical tagged-input interface, not an in-place framed-stream traversal or
a machine emitting renamed literals. Those assembly steps remain separate.
-/

namespace LeanNPHardness.MachineAdapters.LiteralDictionary

open Computability Turing

/-- The literal frame is exactly the one used inside the binary CNF encoding. -/
def inputEncoding : FinEncoding (CNF.Literal Nat × List Nat) :=
  PairEncoding.finEncoding FramedLiteral.finEncoding FramedNatList.finEncoding

/-- The first dictionary occurrence of the literal's variable, or its length. -/
def lookup (input : CNF.Literal Nat × List Nat) : Nat :=
  input.2.idxOf input.1.var

theorem lookup_eq_length_iff (input : CNF.Literal Nat × List Nat) :
    lookup input = input.2.length ↔ input.1.var ∉ input.2 :=
  List.idxOf_eq_length_iff

theorem lookup_getElem? (input : CNF.Literal Nat × List Nat)
    (present : input.1.var ∈ input.2) :
    input.2[lookup input]? = some input.1.var :=
  List.getElem?_idxOf present

/-- Extraction is performed on the left component while retaining the dictionary;
the tagged query/dictionary adapter then invokes the full checked lookup. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime inputEncoding unaryFinEncodingNat lookup := by
  have extract := pairReductionComputableInPolyTime
    FramedLiteral.finEncoding FramedNat.finEncoding FramedNatList.finEncoding
    (CNF.Literal.var : CNF.Literal Nat → Nat)
    MachinePrimitives.LiteralVariable.computableInPolyTime
  exact MachineComposition.compositionComputableInPolyTime inputEncoding
    (PairEncoding.finEncoding FramedNat.finEncoding FramedNatList.finEncoding)
    unaryFinEncodingNat (fun input => (input.1.var, input.2))
    MachinePrimitives.DictionaryLookup.lookup extract
    DictionaryLookupEncoding.lookupComputableInPolyTime

/-- Retain the exact literal, its polarity and every dictionary occurrence. -/
def retain (input : CNF.Literal Nat × List Nat) :
    Nat × (CNF.Literal Nat × List Nat) := (lookup input, input)

def outputEncoding : FinEncoding (Nat × (CNF.Literal Nat × List Nat)) :=
  PairEncoding.finEncoding unaryFinEncodingNat inputEncoding

@[simp]
theorem retain_source (input : CNF.Literal Nat × List Nat) :
    (retain input).2 = input := rfl

/-- This witness includes input duplication; no second source copy is assumed. -/
noncomputable def preservingComputableInPolyTime :
    TM2ComputableInPolyTime inputEncoding outputEncoding retain :=
  PairDuplication.retainInputComputableInPolyTime
    inputEncoding unaryFinEncodingNat lookup computableInPolyTime

/-- Even the absence sentinel fits within the original tagged input length. -/
theorem lookup_le_encode_length (input : CNF.Literal Nat × List Nat) :
    lookup input ≤ (inputEncoding.encode input).length := by
  have indexBound := List.idxOf_le_length (l := input.2) (a := input.1.var)
  have dictionaryBound := BinaryNatLists.length_le_listWireSize input.2
  simp only [inputEncoding, PairEncoding.finEncoding_encode_length]
  change input.2.idxOf input.1.var ≤
    (FramedLiteral.finEncoding.encode input.1).length +
      (BinaryNatLists.encodeNatList input.2).length
  rw [BinaryNatLists.encodeNatList_length]
  omega

/-- Independent size bound: unary index plus one unchanged original input. -/
theorem retain_encode_length_le (input : CNF.Literal Nat × List Nat) :
    (outputEncoding.encode (retain input)).length ≤
      2 * (inputEncoding.encode input).length := by
  have bound := lookup_le_encode_length input
  have unaryLength (n : Nat) : (unaryEncodeNat n).length = n := by
    induction n with
    | zero => rfl
    | succ n ih => simp only [unaryEncodeNat, List.length_cons, ih]
  simpa [outputEncoding, retain, PairEncoding.finEncoding_encode_length,
    unaryFinEncodingNat, unaryLength, two_mul] using
    Nat.add_le_add_right bound (inputEncoding.encode input).length

/-- The unary result agrees with the existing semantic dense-index function. -/
theorem lookup_denseIndex (formula : CNF.Formula Nat) (literal : CNF.Literal Nat) :
    lookup (literal, formula.variableDictionary) = formula.denseIndex literal.var := rfl

/-- The retained sign and computed index specify exactly the renamed literal.
This is a semantic reconstruction statement, not a re-encoding machine. -/
theorem retained_rename (literal : CNF.Literal Nat) (dictionary : List Nat) :
    (retain (literal, dictionary)).2.1.rename
        (fun _ => (retain (literal, dictionary)).1) =
      literal.rename (fun value => dictionary.idxOf value) := by
  cases literal <;> rfl

/-- Dense lookup is in range whenever the source variable occurs in the formula. -/
theorem lookup_lt_dictionary_length (formula : CNF.Formula Nat)
    (literal : CNF.Literal Nat) (present : literal.var ∈ formula.vars) :
    lookup (literal, formula.variableDictionary) < formula.variableDictionary.length :=
  formula.denseIndex_lt literal.var present

/-- Retain independently encoded caller data as well as the literal and dictionary.
For remaining formula data, use its canonical encoding as `contextEncoding`.
The bound includes the full tagged context, including loading and reassembly. -/
noncomputable def withContextComputableInPolyTime {α : Type}
    (contextEncoding : FinEncoding α) :
    TM2ComputableInPolyTime
      (PairEncoding.finEncoding inputEncoding contextEncoding)
      (PairEncoding.finEncoding outputEncoding contextEncoding)
      (fun input => (retain input.1, input.2)) :=
  pairReductionComputableInPolyTime inputEncoding outputEncoding contextEncoding
    retain preservingComputableInPolyTime

/-- Retaining context does not change the factor-two output-size bound. -/
theorem withContext_encode_length_le {α : Type} (contextEncoding : FinEncoding α)
    (input : (CNF.Literal Nat × List Nat) × α) :
    ((PairEncoding.finEncoding outputEncoding contextEncoding).encode
      (retain input.1, input.2)).length ≤
      2 * ((PairEncoding.finEncoding inputEncoding contextEncoding).encode input).length := by
  have bound := retain_encode_length_le input.1
  simp only [PairEncoding.finEncoding_encode_length]
  omega

end LeanNPHardness.MachineAdapters.LiteralDictionary
