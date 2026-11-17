import LeanNPHardness.FormulaVariablesMachine
import LeanNPHardness.DictionaryBuildMachine
import LeanNPHardness.PairDuplication

/-!
# Polynomial-time formula dictionaries with retained source

Compose the complete occurrence-list extractor with dictionary construction,
then use checked input duplication and pair-left computation to retain the
original formula. Input size is the complete binary CNF encoding; the output
uses a tagged pair of the framed dictionary and that unchanged encoding.

Only the auxiliary dictionary is deduplicated, in rightmost-occurrence order.
The polynomial witnesses charge intermediate transfers and copying through
the generic finite TM2 composition theorem. The separate output-size bound
is linear. Repeated dense-index lookup, full renaming and malformed-input
rejection remain separate obligations.
-/

namespace LeanNPHardness.MachineAdapters.FormulaDictionary

open Computability Turing

/-- Compute the exact dictionary used by semantic dense renaming, starting
from the canonical binary formula encoding. All runtime bounds use that
original encoded input length. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime CNF.Formula.finEncoding FramedNatList.finEncoding
      CNF.Formula.variableDictionary := by
  have composed := MachineComposition.compositionComputableInPolyTime
    CNF.Formula.finEncoding FramedNatList.finEncoding FramedNatList.finEncoding
    CNF.Formula.vars DictionaryConstruction.build
    MachinePrimitives.FormulaVariables.computableInPolyTime DictionaryBuild.computableInPolyTime
  simpa only [Function.comp_def, DictionaryConstruction.build_vars] using composed

/-- Preparation preserves every source literal and clause, including repetitions. -/
def prepare (formula : CNF.Formula Nat) : List Nat × CNF.Formula Nat :=
  (formula.variableDictionary, formula)

/-- The dictionary is framed; the retained formula uses its original binary encoding. -/
def outputEncoding : FinEncoding (List Nat × CNF.Formula Nat) :=
  PairEncoding.finEncoding FramedNatList.finEncoding CNF.Formula.finEncoding

@[simp]
theorem prepare_formula (formula : CNF.Formula Nat) :
    (prepare formula).2 = formula := rfl

/-- Deduplication affects the auxiliary dictionary only. -/
theorem prepare_dictionary_nodup (formula : CNF.Formula Nat) :
    (prepare formula).1.Nodup := by
  exact List.nodup_dedup formula.vars

/-- The prepared dictionary supplies exactly the existing dense-index semantics. -/
theorem lookup_prepare (formula : CNF.Formula Nat) (query : Nat) :
    MachinePrimitives.DictionaryLookup.lookup (query, (prepare formula).1) =
      formula.denseIndex query := rfl

/-- Tagged output length is the framed dictionary length plus the original
formula length; this size bound is independent of the runtime theorem. -/
theorem prepare_encode_length_le (formula : CNF.Formula Nat) :
    (outputEncoding.encode (prepare formula)).length ≤ 4 * formula.encodedSize + 1 := by
  have bound := formula.variableDictionary_encode_length_le
  simp only [outputEncoding, PairEncoding.finEncoding_encode_length, prepare,
    CNF.Formula.finEncoding_encode_length]
  change (BinaryNatLists.encodeNatList formula.variableDictionary).length +
    formula.encodedSize ≤ _
  omega

/-- Compute the dictionary and retain the exact source formula from one input.
Checked duplication, pair-left execution and composition charge all copying,
intermediate output sizes, cleanup and canonical halting in original input bits. -/
noncomputable def preservingComputableInPolyTime :
    TM2ComputableInPolyTime CNF.Formula.finEncoding outputEncoding prepare :=
  PairDuplication.retainInputComputableInPolyTime
    CNF.Formula.finEncoding FramedNatList.finEncoding
    CNF.Formula.variableDictionary computableInPolyTime

end LeanNPHardness.MachineAdapters.FormulaDictionary
