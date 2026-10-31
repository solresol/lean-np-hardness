import LeanNPHardness.DictionaryInsertStep
import LeanNPHardness.MachineRoutineBound

/-!
# Seeded dictionary folding over a framed stream

One fixed finite TM2 routine iterates complete insertion until the isolated
body is empty. The evolving accumulator determines each call's size and cost.
Full-source preparation reverses the frames, giving the tail-first dictionary
order. The original header is retained; it is not a remaining-entry counter.
-/

namespace LeanNPHardness.MachineAdapters.DictionaryFold

open Turing Routines DictionaryInsertCall

variable (c : Witness)

abbrev inputStack : Stack c := .inr (.inl DictionaryInsertInput.inputStack)

/-- Empty-stream termination on complete frames, including zero-valued entries. -/
noncomputable def routine : Routine (Alphabet c) :=
  loop (inputStack c) (DictionaryInsertStep.routine c)

/-- A bound recurrence, not an exact runtime: each insertion uses its current
dictionary, and each loop test (including the final empty test) is charged. -/
noncomputable def cost : List Nat → List Nat → Nat
  | [], _ => 1
  | query :: values, dictionary =>
      (DictionaryInsertStep.timePolynomial c).eval
          (DictionaryInsert.pairWord query dictionary).length + 1 +
        cost values (DictionaryConstruction.insert query dictionary)

/-- Stream-order folding retains the supplied header and clears all workspace. -/
theorem routine_exits (values dictionary : List Nat) (header : List Bool) :
    (routine c).ExitsLE
      (contents c (empty c) (values.flatMap BinaryNatLists.encodeNat) header
        (BinaryNatLists.encodeNatList dictionary) [] [])
      (cost c values dictionary)
      (contents c (empty c) [] header
        (BinaryNatLists.encodeNatList
          (values.foldl (fun acc query => DictionaryConstruction.insert query acc) dictionary))
        [] []) := by
  induction values generalizing dictionary with
  | nil => exact (loop_exits_nil _ _ _ rfl).le
  | cons query values ih =>
      have nonempty :
          contents c (empty c) ((query :: values).flatMap BinaryNatLists.encodeNat) header
            (BinaryNatLists.encodeNatList dictionary) [] [] (work := []) (inputStack c) ≠ [] := by
        change BinaryNatLists.encodeNat query ++ values.flatMap BinaryNatLists.encodeNat ≠ []
        intro h
        have := congrArg List.length h
        have pos := BinaryNatLists.natWireSize_pos query
        simp only [List.length_append, BinaryNatLists.encodeNat_length, List.length_nil] at this
        omega
      exact loop_exitsLE_cons _ _ nonempty
        (DictionaryInsertStep.bounded_exits c query dictionary
          (values.flatMap BinaryNatLists.encodeNat) header)
        (ih (DictionaryConstruction.insert query dictionary))

/-- Bit budget for unread frames, the current framed dictionary, and two bits
of possible count-header growth per remaining insertion. -/
def budget (values dictionary : List Nat) : Nat :=
  (values.flatMap BinaryNatLists.encodeNat).length +
    (BinaryNatLists.encodeNatList dictionary).length + 2 * values.length

theorem pair_length_le_budget (query : Nat) (values dictionary : List Nat) :
    (DictionaryInsert.pairWord query dictionary).length ≤ budget (query :: values) dictionary := by
  simp only [budget, DictionaryInsert.pairWord, List.length_append, List.length_map,
    List.flatMap_cons, List.length_cons]
  omega

/-- The budget does not grow when one frame is consumed and inserted. -/
theorem budget_insert_le (query : Nat) (values dictionary : List Nat) :
    budget values (DictionaryConstruction.insert query dictionary) ≤
      budget (query :: values) dictionary := by
  have growth := DictionaryInsertCall.output_length_le query dictionary
  simp only [DictionaryInsert.pairWord, List.length_append, List.length_map] at growth
  simp only [budget, List.flatMap_cons, List.length_append, List.length_cons]
  omega

/-- Uniformly charge all calls at the initial bit budget. -/
theorem cost_le (values dictionary : List Nat) :
    cost c values dictionary ≤ values.length *
      ((DictionaryInsertStep.timePolynomial c).eval (budget values dictionary) + 1) + 1 := by
  induction values generalizing dictionary with
  | nil => simp [cost]
  | cons query values ih =>
      have queryBound := MachineRuntime.polynomial_eval_mono
        (DictionaryInsertStep.timePolynomial c) (pair_length_le_budget query values dictionary)
      have tailBound := MachineRuntime.polynomial_eval_mono
        (DictionaryInsertStep.timePolynomial c) (budget_insert_le query values dictionary)
      have tailCost := (ih (DictionaryConstruction.insert query dictionary)).trans
        (Nat.add_le_add_right (Nat.mul_le_mul_left values.length
          (Nat.add_le_add_right tailBound 1)) 1)
      dsimp only at queryBound tailCost
      simp only [cost, List.length_cons, Nat.add_mul, Nat.one_mul]
      omega

/-- Reverse preparation followed by the complete seeded insertion loop. -/
noncomputable def preparedRoutine : Routine (Alphabet c) :=
  seq (DictionaryInsertStep.prepare c) (routine c)

/-- Full-source folding agrees with tail-first construction, retaining the
original count header and arbitrary seed contents (including repetitions). -/
theorem prepared_exits (values dictionary : List Nat) :
    (preparedRoutine c).ExitsLE
      (contents c (empty c) (BinaryNatLists.encodeNatList values) []
        (BinaryNatLists.encodeNatList dictionary) [] [])
      (DictionaryInsertInput.prepareSteps values + cost c values.reverse dictionary)
      (contents c (empty c) [] (BinaryNatLists.encodeNat values.length)
        (BinaryNatLists.encodeNatList (DictionaryConstruction.extend values dictionary)) [] []) := by
  have run := seq_exitsLE _ _
    (DictionaryInsertStep.prepare_exits c values
      (BinaryNatLists.encodeNatList dictionary) (empty c) []).le
    (routine_exits c values.reverse dictionary (BinaryNatLists.encodeNat values.length))
  simpa only [preparedRoutine, ← DictionaryConstruction.extend_eq_foldl_reverse] using run

/-- Empty-seed specialization computes exactly `List.dedup` in rightmost-occurrence order. -/
theorem dedup_exits (values : List Nat) :
    (preparedRoutine c).ExitsLE
      (contents c (empty c) (BinaryNatLists.encodeNatList values) []
        (BinaryNatLists.encodeNatList []) [] [])
      (DictionaryInsertInput.prepareSteps values + cost c values.reverse [])
      (contents c (empty c) [] (BinaryNatLists.encodeNat values.length)
        (BinaryNatLists.encodeNatList values.dedup) [] []) := by
  simpa only [DictionaryConstruction.extend_eq_dedup_append values [] (by simp),
    List.append_nil] using prepared_exits c values []

/-- Full source and seed bits, each including its own binary count header. -/
def inputSize (values dictionary : List Nat) : Nat :=
  (BinaryNatLists.encodeNatList values).length +
    (BinaryNatLists.encodeNatList dictionary).length

theorem length_le_inputSize (values dictionary : List Nat) :
    values.length ≤ inputSize values dictionary := by
  have h := BinaryNatLists.length_le_listWireSize values
  simp only [inputSize, BinaryNatLists.encodeNatList_length]
  omega

/-- Frame reversal preserves body length; the growth allowance is linear
in the original full source and seed bit lengths. -/
theorem budget_reverse_le (values dictionary : List Nat) :
    budget values.reverse dictionary ≤ 3 * inputSize values dictionary := by
  have h := length_le_inputSize values dictionary
  have reverseLength : (values.reverse.flatMap BinaryNatLists.encodeNat).length =
      (values.flatMap BinaryNatLists.encodeNat).length := by
    simp only [List.length_flatMap, List.map_reverse, List.sum_reverse]
  simp only [budget, reverseLength, List.length_reverse]
  simp only [inputSize, BinaryNatLists.encodeNatList, List.length_append] at h ⊢
  omega

/-- Polynomial bound for preparation plus folding with the seed preloaded.
Canonical input loading and final header cleanup are separate obligations. -/
noncomputable def timePolynomial : Polynomial Nat :=
  Polynomial.X * ((DictionaryInsertStep.timePolynomial c).comp (3 * Polynomial.X) + 1) +
    10 * Polynomial.X + 8

theorem prepared_cost_le (values dictionary : List Nat) :
    DictionaryInsertInput.prepareSteps values + cost c values.reverse dictionary ≤
      (timePolynomial c).eval (inputSize values dictionary) := by
  have mono := MachineRuntime.polynomial_eval_mono
    (DictionaryInsertStep.timePolynomial c) (budget_reverse_le values dictionary)
  have folded := (cost_le c values.reverse dictionary).trans
    (Nat.add_le_add_right (Nat.mul_le_mul
      (by simpa only [List.length_reverse] using length_le_inputSize values dictionary)
      (Nat.add_le_add_right mono 1)) 1)
  dsimp only at folded
  have prepared := DictionaryInsertInput.prepareSteps_le values
  have source : (BinaryNatLists.encodeNatList values).length ≤ inputSize values dictionary :=
    Nat.le_add_right _ _
  have prepBound := prepared.trans (Nat.add_le_add_right (Nat.mul_le_mul_left 10 source) 7)
  simp only [timePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_comp, Polynomial.eval_ofNat, Polynomial.eval_X, Polynomial.eval_one]
  omega

/-- Polynomial TM2 routine exit from separately supplied canonical source and seed. -/
theorem bounded_exits (values dictionary : List Nat) :
    (preparedRoutine c).ExitsLE
      (contents c (empty c) (BinaryNatLists.encodeNatList values) []
        (BinaryNatLists.encodeNatList dictionary) [] [])
      ((timePolynomial c).eval (inputSize values dictionary))
      (contents c (empty c) [] (BinaryNatLists.encodeNat values.length)
        (BinaryNatLists.encodeNatList (DictionaryConstruction.extend values dictionary)) [] []) :=
  (prepared_exits c values dictionary).mono (prepared_cost_le c values dictionary)

/-- Instantiate the loop with the full checked insertion machine. -/
theorem checked_exits (values dictionary : List Nat) :
    (preparedRoutine DictionaryInsert.computableInPolyTime).ExitsLE
      (contents DictionaryInsert.computableInPolyTime
        (empty DictionaryInsert.computableInPolyTime) (BinaryNatLists.encodeNatList values) []
        (BinaryNatLists.encodeNatList dictionary) [] [])
      ((timePolynomial DictionaryInsert.computableInPolyTime).eval (inputSize values dictionary))
      (contents DictionaryInsert.computableInPolyTime
        (empty DictionaryInsert.computableInPolyTime) [] (BinaryNatLists.encodeNat values.length)
        (BinaryNatLists.encodeNatList (DictionaryConstruction.extend values dictionary)) [] []) :=
  bounded_exits DictionaryInsert.computableInPolyTime values dictionary

end LeanNPHardness.MachineAdapters.DictionaryFold
