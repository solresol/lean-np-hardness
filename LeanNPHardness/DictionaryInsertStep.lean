import LeanNPHardness.DictionaryInsertCall
import LeanNPHardness.MachineRoutineRightExtension

/-!
# One dictionary insertion from a retained framed stream

Extract one canonical natural frame, serialize it with the current dictionary,
run the complete insertion machine, and return the updated dictionary. The
unread stream and original header survive unchanged. All framing, transfer and
invocation costs are charged in TM2 steps, measured in the combined framed
query/dictionary length. Repeated folding is a separate construction.
-/

namespace LeanNPHardness.MachineAdapters.DictionaryInsertStep

open Turing Routines DictionaryInsertCall

variable (c : Witness)

/-- Lift frame extraction and serialization into the caller side of the layout. -/
def loadFrame : Routine (Alphabet c) :=
  extendRight c.tm.Γ (extend ScratchAlphabet DictionaryInsertInput.routine)

/-- Loading retains arbitrary private-machine and scratch contents at no extra cost. -/
theorem loadFrame_exits (query : Nat) (dictionary : List Nat) (input header : List Bool)
    (machineStacks : Stacks c.tm.Γ) (scratch : List (Sum Bool Bool)) :
    (loadFrame c).Exits
      (contents c machineStacks (BinaryNatLists.encodeNat query ++ input) header
        (BinaryNatLists.encodeNatList dictionary) [] scratch)
      (DictionaryInsertInput.runSteps query dictionary)
      (contents c machineStacks input header []
        (DictionaryInsert.pairWord query dictionary) scratch) := by
  exact extendRight_exits c.tm.Γ _ machineStacks
    (extend_exits ScratchAlphabet _ (fun _ => scratch)
      (DictionaryInsertInput.natural_head_exits query dictionary input header))

/-- One complete frame-to-dictionary step using the supplied full insertion witness. -/
noncomputable def routine : Routine (Alphabet c) :=
  seq (loadFrame c) (DictionaryInsertCall.routine c)

/-- Exact phase costs, keeping the actual insertion run separate from its bound. -/
theorem routine_exits (query : Nat) (dictionary : List Nat) (input header : List Bool) :
    ∃ n ≤ c.time.eval (DictionaryInsert.pairWord query dictionary).length,
      (routine c).Exits
        (contents c (empty c) (BinaryNatLists.encodeNat query ++ input) header
          (BinaryNatLists.encodeNatList dictionary) [] [])
        (DictionaryInsertInput.runSteps query dictionary +
          (4 * (DictionaryInsert.pairWord query dictionary).length + 2 + n +
            (4 * (BinaryNatLists.encodeNatList
              (DictionaryConstruction.insert query dictionary)).length + 2)))
        (contents c (empty c) input header
          (BinaryNatLists.encodeNatList (DictionaryConstruction.insert query dictionary)) [] []) := by
  obtain ⟨n, hn, run⟩ := DictionaryInsertCall.routine_exits c query dictionary input header
  exact ⟨n, hn, seq_exits _ _ (loadFrame_exits c query dictionary input header (empty c) []) run⟩

/-- The full insertion polynomial plus extraction, serialization and both transfers. -/
noncomputable def timePolynomial : Polynomial Nat := c.time + 14 * Polynomial.X + 18

theorem bounded_exits (query : Nat) (dictionary : List Nat) (input header : List Bool) :
    ∃ steps ≤ (timePolynomial c).eval (DictionaryInsert.pairWord query dictionary).length,
      (routine c).Exits
        (contents c (empty c) (BinaryNatLists.encodeNat query ++ input) header
          (BinaryNatLists.encodeNatList dictionary) [] []) steps
        (contents c (empty c) input header
          (BinaryNatLists.encodeNatList (DictionaryConstruction.insert query dictionary)) [] []) := by
  obtain ⟨n, hn, run⟩ := routine_exits c query dictionary input header
  refine ⟨_, ?_, run⟩
  have loadBound := DictionaryInsertInput.runSteps_le query dictionary
  have outputBound := DictionaryInsertCall.output_length_le query dictionary
  simp only [timePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_ofNat, Polynomial.eval_X]
  omega

/-- The one-frame contract for the repository's checked insertion machine. -/
theorem checked_exits (query : Nat) (dictionary : List Nat) (input header : List Bool) :
    ∃ steps ≤ (timePolynomial DictionaryInsert.computableInPolyTime).eval
        (DictionaryInsert.pairWord query dictionary).length,
      (routine DictionaryInsert.computableInPolyTime).Exits
        (contents DictionaryInsert.computableInPolyTime (empty DictionaryInsert.computableInPolyTime)
          (BinaryNatLists.encodeNat query ++ input) header
          (BinaryNatLists.encodeNatList dictionary) [] []) steps
        (contents DictionaryInsert.computableInPolyTime (empty DictionaryInsert.computableInPolyTime)
          input header (BinaryNatLists.encodeNatList (DictionaryConstruction.insert query dictionary)) [] []) :=
  bounded_exits DictionaryInsert.computableInPolyTime query dictionary input header

/-- Prepare the source body in tail-first order within the same caller layout. -/
def prepare : Routine (Alphabet c) :=
  extendRight c.tm.Γ (extend ScratchAlphabet DictionaryInsertInput.prepare)

theorem prepare_exits (values : List Nat) (dictionary : List Bool)
    (machineStacks : Stacks c.tm.Γ) (scratch : List (Sum Bool Bool)) :
    (prepare c).Exits
      (contents c machineStacks (BinaryNatLists.encodeNatList values) [] dictionary [] scratch)
      (DictionaryInsertInput.prepareSteps values)
      (contents c machineStacks (values.reverse.flatMap BinaryNatLists.encodeNat)
        (BinaryNatLists.encodeNat values.length) dictionary [] scratch) := by
  exact extendRight_exits c.tm.Γ _ machineStacks
    (extend_exits ScratchAlphabet _ (fun _ => scratch)
      (DictionaryInsertInput.prepare_exits values dictionary []))

/-- Preparation followed by the first insertion processes the last source occurrence.
Every remaining frame and the complete original count header are retained. -/
theorem prepare_head_exits (values : List Nat) (query : Nat) (dictionary : List Nat) :
    ∃ steps ≤ DictionaryInsertInput.prepareSteps (values ++ [query]) +
        (timePolynomial c).eval (DictionaryInsert.pairWord query dictionary).length,
      (seq (prepare c) (routine c)).Exits
        (contents c (empty c) (BinaryNatLists.encodeNatList (values ++ [query])) []
          (BinaryNatLists.encodeNatList dictionary) [] []) steps
        (contents c (empty c) (values.reverse.flatMap BinaryNatLists.encodeNat)
          (BinaryNatLists.encodeNat (values ++ [query]).length)
          (BinaryNatLists.encodeNatList (DictionaryConstruction.insert query dictionary)) [] []) := by
  have prep := prepare_exits c (values ++ [query])
    (BinaryNatLists.encodeNatList dictionary) (empty c) []
  simp only [List.reverse_append, List.reverse_singleton, List.singleton_append,
    List.flatMap_cons] at prep
  obtain ⟨n, hn, run⟩ := bounded_exits c query dictionary
    (values.reverse.flatMap BinaryNatLists.encodeNat)
    (BinaryNatLists.encodeNat (values ++ [query]).length)
  exact ⟨_, Nat.add_le_add_left hn _, seq_exits _ _ prep run⟩

end LeanNPHardness.MachineAdapters.DictionaryInsertStep
