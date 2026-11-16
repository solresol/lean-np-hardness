import LeanNPHardness.OrderedFormulaMachine

/-!
# Source-order formula variables with an executable occurrence count

Restore the isolated variable frames while pushing one unary mark per frame
onto an independent stack. The eight-stack routine preserves caller input and
output suffixes, every occurrence and payload bit, and clears its workspace.
Restoration costs exactly `2V + 4m + 1` in body bits `V` and occurrences `m`.
The full formula bound is `N * (10N + 37) + 6` in original formula bits `N`.

The marks support binary-header generation. `FormulaVariablesMachine` separately
assembles the full framed list and packages its standalone conversion.
-/

namespace LeanNPHardness.MachinePrimitives.MarkedFormula

open Computability Turing Routines

abbrev ExtraAlphabet (_ : Unit) := Bool
abbrev Stack := OrderedFormula.Stack ⊕ Unit
abbrev Alphabet := ExtendedAlphabet (Γ := OrderedFormula.Alphabet) ExtraAlphabet

instance (k : Stack) : Fintype (Alphabet k) := by
  cases k with
  | inl k => exact inferInstanceAs (Fintype (OrderedFormula.Alphabet k))
  | inr k => exact inferInstanceAs (Fintype Bool)

def contents (input count work buffer inner outer output marks : List Bool) : Stacks Alphabet :=
  extendedStacks ExtraAlphabet
    (OrderedFormula.contents input count work buffer inner outer output) (fun _ => marks)

/-- One complete frame move, followed by one explicitly charged mark push. -/
def moveFrame : Routine Alphabet :=
  seq (extend ExtraAlphabet (OrderedFormula.reverseRoutine FrameMove.routine))
    (pushList (.inr ()) [true])

/-- Arbitrary caller data and previous marks survive the complete-frame step. -/
theorem moveFrame_exits (bits input buffer inner outer output marks : List Bool) :
    moveFrame.Exits
      (contents input [] [] (BinaryNatLists.frame bits ++ buffer) inner outer output marks)
      (2 * (BinaryNatLists.frame bits).length + 3)
      (contents input [] [] buffer inner outer (BinaryNatLists.frame bits ++ output)
        (true :: marks)) := by
  have moved := FrameMove.routine_exits bits buffer output
  rw [FrameMove.runSteps_eq_frame_length] at moved
  have hm := extend_exits ExtraAlphabet
    (OrderedFormula.reverseRoutine FrameMove.routine) (fun _ => marks)
    (OrderedFormula.reverseRoutine_exits FrameMove.routine input inner outer moved)
  have hp : (pushList (Γ := Alphabet) (.inr ()) [true]).Exits
      (contents input [] [] buffer inner outer (BinaryNatLists.frame bits ++ output) marks) 1
      (contents input [] [] buffer inner outer (BinaryNatLists.frame bits ++ output)
        (true :: marks)) := by
    convert pushList_exits (Γ := Alphabet) (.inr ()) [true]
      (contents input [] [] buffer inner outer (BinaryNatLists.frame bits ++ output) marks) using 1
    funext k
    cases k with
    | inl k => simp [contents, extendedStacks, Function.update]
    | inr k => cases k; simp [contents, extendedStacks, Function.update]
  convert seq_exits _ _ hm hp using 1 <;> rfl

/-- Test only the isolated buffer; caller input and output are never scanned. -/
def restore : Routine Alphabet :=
  loop (.inl (.inl (.inl (.inl .output)))) moveFrame

def restoreSteps (frames : List (List Bool)) : Nat :=
  loopSteps (fun i => 2 * (BinaryNatLists.frame (frames[i]?.getD [])).length + 3)
    frames.length

@[simp]
theorem restoreSteps_nil : restoreSteps [] = 1 := rfl

@[simp]
theorem restoreSteps_cons (bits : List Bool) (frames : List (List Bool)) :
    restoreSteps (bits :: frames) =
      2 * (BinaryNatLists.frame bits).length + 4 + restoreSteps frames := by
  simp [restoreSteps, loopSteps, Nat.add_assoc]

/-- Frame order reverses, payload order survives, and exactly one mark is added per frame. -/
theorem restore_exits (frames : List (List Bool))
    (input inner outer output marks : List Bool) :
    restore.Exits
      (contents input [] [] (frames.flatMap BinaryNatLists.frame) inner outer output marks)
      (restoreSteps frames)
      (contents input [] [] [] inner outer
        (frames.reverse.flatMap BinaryNatLists.frame ++ output)
        (List.replicate frames.length true ++ marks)) := by
  let S : Nat → Stacks Alphabet := fun i =>
    contents input [] [] ((frames.drop i).flatMap BinaryNatLists.frame) inner outer
      ((frames.take i).reverse.flatMap BinaryNatLists.frame ++ output)
      (List.replicate i true ++ marks)
  have hb : ∀ i < frames.length, moveFrame.Exits (S i)
      (2 * (BinaryNatLists.frame (frames[i]?.getD [])).length + 3) (S (i + 1)) := by
    intro i hi
    have run := moveFrame_exits frames[i] input
      ((frames.drop (i + 1)).flatMap BinaryNatLists.frame) inner outer
      ((frames.take i).reverse.flatMap BinaryNatLists.frame ++ output)
      (List.replicate i true ++ marks)
    simpa only [S, List.drop_eq_getElem_cons hi, List.flatMap_cons,
      List.take_add_one, List.getElem?_eq_getElem hi, Option.getD_some,
      Option.toList_some, List.reverse_append, List.reverse_singleton,
      List.flatMap_append, List.flatMap_singleton, List.flatMap_nil,
      List.nil_append, List.append_assoc, List.replicate_succ, List.cons_append] using run
  have hn : ∀ i < frames.length, S i (.inl (.inl (.inl (.inl .output)))) ≠ [] := by
    intro i hi
    change ((frames.drop i).flatMap BinaryNatLists.frame) ≠ []
    rw [List.drop_eq_getElem_cons hi, List.flatMap_cons]
    have hpos := BinaryNatLists.frame_length frames[i]
    intro h
    have := congrArg List.length h
    simp only [List.length_append, List.length_nil] at this
    omega
  have run := loop_exits (.inl (.inl (.inl (.inl .output)))) moveFrame frames.length S
    (fun i => 2 * (BinaryNatLists.frame (frames[i]?.getD [])).length + 3) hb hn
    (by simp [S, contents, OrderedFormula.contents, CountedFormula.contents,
      CountedLiteralBody.contents, FrameMove.contents])
  simpa only [restore, restoreSteps, S, List.drop_zero, List.take_zero,
    List.reverse_nil, List.flatMap_nil, List.nil_append, List.drop_length,
    List.take_length, List.replicate_zero] using run

/-- Every mark costs one step beyond ordinary complete-frame reversal. -/
theorem restoreSteps_eq (frames : List (List Bool)) :
    restoreSteps frames = 2 * (frames.flatMap BinaryNatLists.frame).length +
      4 * frames.length + 1 := by
  induction frames with
  | nil => simp
  | cons bits frames ih =>
      simp only [restoreSteps_cons, List.flatMap_cons, List.length_append,
        List.length_cons, ih]
      omega

/-- Extract the global reverse body, then restore it while collecting occurrence marks. -/
def routine : Routine Alphabet :=
  seq (extend ExtraAlphabet (extend OrderedFormula.ExtraAlphabet CountedFormula.routine)) restore

def runBound (formula : CNF.Formula Nat) : Nat :=
  CountedFormula.runBound formula + restoreSteps (formula.vars.reverse.map encodeNat)

/-- Global source order, exact occurrence marks, and both arbitrary caller suffixes. -/
theorem formula_exits (formula : CNF.Formula Nat) (input output : List Bool) :
    routine.ExitsLE
      (contents (formula.encode ++ input) [] [] [] [] [] output [])
      (runBound formula)
      (contents input [] [] [] [] []
        (formula.vars.flatMap BinaryNatLists.encodeNat ++ output)
        (List.replicate formula.vars.length true)) := by
  obtain ⟨n, hn, extract⟩ := CountedFormula.formula_exits formula input []
  have h₁ := extend_exits ExtraAlphabet
    (extend OrderedFormula.ExtraAlphabet CountedFormula.routine) (fun _ => [])
    (extend_exits OrderedFormula.ExtraAlphabet CountedFormula.routine (fun _ => output) extract)
  simp only [List.append_nil] at h₁
  have h₂ := restore_exits (formula.vars.reverse.map encodeNat) input [] [] output []
  simp only [List.flatMap_map, ← List.map_reverse, List.reverse_reverse,
    List.length_map, List.length_reverse, List.append_nil] at h₂
  exact ⟨_, Nat.add_le_add_right hn _, seq_exits _ _ h₁ h₂⟩

/-- Exact restoration overhead is separate from the traversal's upper bound. -/
theorem runBound_eq (formula : CNF.Formula Nat) :
    runBound formula = CountedFormula.runBound formula +
      2 * (formula.vars.flatMap BinaryNatLists.encodeNat).length +
      4 * formula.vars.length + 1 := by
  simp only [runBound, restoreSteps_eq, List.length_map, List.length_reverse,
    BinaryNatLists.encodeNat, List.length_flatMap, List.map_reverse, List.sum_reverse,
    List.map_map, Function.comp_def]
  omega

/-- The body itself has no growth; the independent unary count uses at most `N` bits. -/
theorem output_lengths_le (formula : CNF.Formula Nat) (output : List Bool) :
    (formula.vars.flatMap BinaryNatLists.encodeNat ++ output).length ≤
        formula.encode.length + output.length ∧
      (List.replicate formula.vars.length true).length ≤ formula.encode.length := by
  exact ⟨OrderedFormula.output_length_le formula output,
    by simpa only [List.length_replicate] using OrderedFormula.vars_length_le formula⟩

/-- Full runtime in original formula bits, independent of both caller suffix lengths. -/
theorem runBound_le (formula : CNF.Formula Nat) :
    runBound formula ≤ formula.encode.length * (10 * formula.encode.length + 37) + 6 := by
  have hc := CountedFormula.runBound_le formula
  have hv := OrderedFormula.output_length_le formula []
  simp only [List.append_nil, List.length_nil, Nat.add_zero] at hv
  have hm := OrderedFormula.vars_length_le formula
  rw [runBound_eq]
  nlinarith

theorem formula_exitsLE (formula : CNF.Formula Nat) (input output : List Bool) :
    routine.ExitsLE
      (contents (formula.encode ++ input) [] [] [] [] [] output [])
      (formula.encode.length * (10 * formula.encode.length + 37) + 6)
      (contents input [] [] [] [] []
        (formula.vars.flatMap BinaryNatLists.encodeNat ++ output)
        (List.replicate formula.vars.length true)) :=
  (formula_exits formula input output).mono (runBound_le formula)

end LeanNPHardness.MachinePrimitives.MarkedFormula
