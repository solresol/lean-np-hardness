import LeanNPHardness.CountedFormulaMachine
import LeanNPHardness.FrameReverseMachine

/-!
# Source-order formula variables with retained caller suffixes

Extract every variable occurrence into an isolated buffer in global reverse
order, then reverse complete frames once into a separate caller-output stack.
Unread input and the output suffix survive; counters, scratch and buffer clear.
The restoration overhead is exactly `2V + 3m + 1` in variable-body bits `V`
and occurrence count `m`, with total bound `N * (10N + 36) + 6` in the original
formula bits `N`. Empty clauses are handled, and every variable occurrence is
retained, including repetitions and both signs of zero.

This canonical-input routine emits a body without a total occurrence-count
header. Framed-list assembly, standalone encoding conversion, malformed-input
rejection and full dense-renaming runtime remain separate obligations.
-/

namespace LeanNPHardness.MachinePrimitives.OrderedFormula

open Computability Turing Routines

abbrev ExtraAlphabet (_ : Unit) := Bool
abbrev Stack := CountedFormula.Stack ⊕ Unit
abbrev Alphabet := ExtendedAlphabet (Γ := CountedFormula.Alphabet) ExtraAlphabet

instance (k : Stack) : Fintype (Alphabet k) := by
  cases k with
  | inl k => exact inferInstanceAs (Fintype (CountedFormula.Alphabet k))
  | inr k => exact inferInstanceAs (Fintype Bool)

/-- Separate caller output from the six-stack traversal's private buffer. -/
def contents (input count work buffer inner outer output : List Bool) : Stacks Alphabet :=
  extendedStacks ExtraAlphabet
    (CountedFormula.contents input count work buffer inner outer) (fun _ => output)

/-- The four reversal stacks occupy buffer/count/work/output respectively. -/
def reverseStack : FrameMove.Stack → Stack
  | .input => .inl (.inl (.inl .output))
  | .count => .inl (.inl (.inl .count))
  | .work => .inl (.inl (.inl .work))
  | .output => .inr ()

/-- Only stack locations change; each alphabet remains Boolean. -/
def reverseBits (k : FrameMove.Stack) (bits : List Bool) : List (Alphabet (reverseStack k)) :=
  match k with
  | .input | .count | .work | .output => bits

/-- Keep caller input and both independent count stacks untouched. -/
def reverseStacks (input inner outer : List Bool) (S : Stacks FrameMove.Alphabet) :
    Stacks Alphabet :=
  contents input (S .count) (S .work) (S .input) inner outer (S .output)

/-- Every source stack update has the corresponding isolated destination update. -/
theorem reverseStacks_update (input inner outer : List Bool) (S : Stacks FrameMove.Alphabet)
    (k : FrameMove.Stack) (bits : List Bool) :
    reverseStacks input inner outer (Function.update S k bits) =
      Function.update (reverseStacks input inner outer S) (reverseStack k) (reverseBits k bits) := by
  funext j
  cases k <;> cases j with
  | inl j =>
      cases j with
      | inl j =>
          cases j with
          | inl j => cases j <;> simp [reverseStacks, contents, CountedFormula.contents,
              CountedLiteralBody.contents, FrameMove.contents, extendedStacks,
              reverseStack, reverseBits, Function.update]
          | inr j => cases j; simp [reverseStacks, contents, CountedFormula.contents,
              CountedLiteralBody.contents, extendedStacks, reverseStack, Function.update]
      | inr j => cases j; simp [reverseStacks, contents, CountedFormula.contents,
          extendedStacks, reverseStack, Function.update]
  | inr j => cases j; simp [reverseStacks, contents,
      extendedStacks, reverseStack, reverseBits, Function.update]

variable {Λ σ : Type}

/-- Redirect the reversal instructions without changing labels or finite control. -/
def reverseStmt : TM2.Stmt FrameMove.Alphabet Λ σ → TM2.Stmt Alphabet Λ σ
  | .push k f q => match k with
    | .input => .push (.inl (.inl (.inl .output))) f (reverseStmt q)
    | .count => .push (.inl (.inl (.inl .count))) f (reverseStmt q)
    | .work => .push (.inl (.inl (.inl .work))) f (reverseStmt q)
    | .output => .push (.inr ()) f (reverseStmt q)
  | .peek k f q => match k with
    | .input => .peek (.inl (.inl (.inl .output))) f (reverseStmt q)
    | .count => .peek (.inl (.inl (.inl .count))) f (reverseStmt q)
    | .work => .peek (.inl (.inl (.inl .work))) f (reverseStmt q)
    | .output => .peek (.inr ()) f (reverseStmt q)
  | .pop k f q => match k with
    | .input => .pop (.inl (.inl (.inl .output))) f (reverseStmt q)
    | .count => .pop (.inl (.inl (.inl .count))) f (reverseStmt q)
    | .work => .pop (.inl (.inl (.inl .work))) f (reverseStmt q)
    | .output => .pop (.inr ()) f (reverseStmt q)
  | .load f q => .load f (reverseStmt q)
  | .branch t a b => .branch t (reverseStmt a) (reverseStmt b)
  | .goto f => .goto f
  | .halt => .halt

def reverseCfg (input inner outer : List Bool) (c : TM2.Cfg FrameMove.Alphabet Λ σ) :
    TM2.Cfg Alphabet Λ σ :=
  ⟨c.l, c.var, reverseStacks input inner outer c.stk⟩

/-- Every statement preserves the embedding, including all three untouched stacks. -/
theorem reverseStmt_stepAux (input inner outer : List Bool)
    (stmt : TM2.Stmt FrameMove.Alphabet Λ σ) (v : σ) (S : Stacks FrameMove.Alphabet) :
    TM2.stepAux (reverseStmt stmt) v (reverseStacks input inner outer S) =
      reverseCfg input inner outer (TM2.stepAux stmt v S) := by
  induction stmt generalizing v S with
  | push k f q ih =>
      have run := ih v (Function.update S k (f v :: S k))
      rw [reverseStacks_update] at run
      cases k <;> exact run
  | peek k f q ih =>
      cases k <;> exact ih _ _
  | pop k f q ih =>
      have run := ih (f v (S k).head?) (Function.update S k (S k).tail)
      rw [reverseStacks_update] at run
      cases k <;> exact run
  | load f q ih => exact ih _ _
  | branch t a b iha ihb =>
      cases h : t v
      · simpa only [reverseStmt, TM2.stepAux, h, Bool.cond_false] using ihb v S
      · simpa only [reverseStmt, TM2.stepAux, h, Bool.cond_true] using iha v S
  | goto f => rfl
  | halt => rfl

theorem reverse_step (input inner outer : List Bool)
    (program : Λ → TM2.Stmt FrameMove.Alphabet Λ σ) (c : TM2.Cfg FrameMove.Alphabet Λ σ) :
    TM2.step (fun l => reverseStmt (program l)) (reverseCfg input inner outer c) =
      (TM2.step program c).map (reverseCfg input inner outer) := by
  rcases c with ⟨l, v, S⟩
  cases l with
  | none => rfl
  | some l => simp only [reverseCfg, TM2.step, reverseStmt_stepAux, Option.map_some]

/-- Exact finite execution is unchanged by the checked stack relocation. -/
theorem reverse_run (input inner outer : List Bool)
    (program : Λ → TM2.Stmt FrameMove.Alphabet Λ σ) (n : Nat)
    (c : Option (TM2.Cfg FrameMove.Alphabet Λ σ)) :
    (flip Option.bind (TM2.step (fun l => reverseStmt (program l))))^[n]
        (c.map (reverseCfg input inner outer)) =
      ((flip Option.bind (TM2.step program))^[n] c).map (reverseCfg input inner outer) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
      cases c with
      | none => exact ih none
      | some c =>
          simpa only [flip, Option.map_some, Option.bind_some, reverse_step] using
            ih (TM2.step program c)

def reverseRoutine (r : Routine FrameMove.Alphabet) : Routine Alphabet where
  Λ := r.Λ
  σ := r.σ
  entry := r.entry
  init := r.init
  program l := reverseStmt (r.program l)

theorem reverseRoutine_exits (r : Routine FrameMove.Alphabet) (input inner outer : List Bool)
    {S S' : Stacks FrameMove.Alphabet} {n : Nat} (h : r.Exits S n S') :
    (reverseRoutine r).Exits (reverseStacks input inner outer S) n
      (reverseStacks input inner outer S') := by
  obtain ⟨v, h⟩ := h
  refine ⟨v, ?_⟩
  have run := reverse_run input inner outer r.program n (some ⟨some r.entry, r.init, S⟩)
  rw [h] at run
  exact run

/-- Reverse only complete frames in the isolated buffer, retaining caller data. -/
theorem restore_exits (frames : List (List Bool)) (input inner outer output : List Bool) :
    (reverseRoutine FrameReverse.routine).Exits
      (contents input [] [] (frames.flatMap BinaryNatLists.frame) inner outer output)
      (FrameReverse.runSteps frames)
      (contents input [] [] [] inner outer (frames.reverse.flatMap BinaryNatLists.frame ++ output)) :=
  reverseRoutine_exits FrameReverse.routine input inner outer (FrameReverse.routine_exits frames output)

/-- Extract all variables before restoring complete frames above caller output. -/
def routine : Routine Alphabet :=
  seq (extend ExtraAlphabet CountedFormula.routine) (reverseRoutine FrameReverse.routine)

def runBound (formula : CNF.Formula Nat) : Nat :=
  CountedFormula.runBound formula +
    FrameReverse.runSteps (formula.vars.reverse.map encodeNat)

/-- Global source order and both suffixes survive, with every work stack empty. -/
theorem formula_exits (formula : CNF.Formula Nat) (input output : List Bool) :
    routine.ExitsLE
      (contents (formula.encode ++ input) [] [] [] [] [] output)
      (runBound formula)
      (contents input [] [] [] [] []
        (formula.vars.flatMap BinaryNatLists.encodeNat ++ output)) := by
  obtain ⟨n, hn, extract⟩ := CountedFormula.formula_exits formula input []
  have h₁ := extend_exits ExtraAlphabet CountedFormula.routine (fun _ => output) extract
  simp only [List.append_nil] at h₁
  have h₂ := restore_exits (formula.vars.reverse.map encodeNat) input [] [] output
  simp only [List.flatMap_map, ← List.map_reverse, List.reverse_reverse] at h₂
  exact ⟨_, Nat.add_le_add_right hn _, seq_exits _ _ h₁ h₂⟩

/-- Exact restoration overhead, separate from the traversal's upper bound. -/
theorem runBound_eq (formula : CNF.Formula Nat) :
    runBound formula = CountedFormula.runBound formula +
      2 * (formula.vars.flatMap BinaryNatLists.encodeNat).length +
      3 * formula.vars.length + 1 := by
  simp only [runBound, FrameReverse.runSteps_eq, List.length_map, List.length_reverse,
    BinaryNatLists.encodeNat, List.length_flatMap, List.map_reverse, List.sum_reverse,
    List.map_map, Function.comp_def]
  omega

/-- Output-size bound, separately from correctness and runtime. -/
theorem output_length_le (formula : CNF.Formula Nat) (output : List Bool) :
    (formula.vars.flatMap BinaryNatLists.encodeNat ++ output).length ≤
      formula.encode.length + output.length := by
  simpa only [List.length_append, List.length_flatMap, List.map_reverse, List.sum_reverse] using
    CountedFormula.formula_output_length_le formula output

/-- The existing occurrence bound in the public size measure also holds in raw bits. -/
theorem vars_length_le (formula : CNF.Formula Nat) :
    formula.vars.length ≤ formula.encode.length := by
  simpa only [CNF.Formula.encode_length] using formula.vars_length_le_encodedSize

/-- Runtime in complete original formula bits, independently of retained suffix lengths. -/
theorem runBound_le (formula : CNF.Formula Nat) :
    runBound formula ≤ formula.encode.length * (10 * formula.encode.length + 36) + 6 := by
  have hc := CountedFormula.runBound_le formula
  have hv := output_length_le formula []
  simp only [List.append_nil, List.length_nil, Nat.add_zero] at hv
  have hm := vars_length_le formula
  rw [runBound_eq]
  nlinarith

/-- Polynomial source-order extraction from the canonical complete formula. -/
theorem formula_exitsLE (formula : CNF.Formula Nat) (input output : List Bool) :
    routine.ExitsLE
      (contents (formula.encode ++ input) [] [] [] [] [] output)
      (formula.encode.length * (10 * formula.encode.length + 36) + 6)
      (contents input [] [] [] [] []
        (formula.vars.flatMap BinaryNatLists.encodeNat ++ output)) :=
  (formula_exits formula input output).mono (runBound_le formula)

end LeanNPHardness.MachinePrimitives.OrderedFormula
