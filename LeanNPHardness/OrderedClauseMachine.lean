import LeanNPHardness.CountedClauseMachine
import LeanNPHardness.FrameReverseMachine

/-!
# Source-order clause variables with retained caller suffixes

Extract the counted clause into an initially empty private buffer. Embed the
checked complete-frame reversal with that buffer as input and the caller's
output as destination. Unread formula input and the caller's output suffix
survive, and all workspace clears. No whole-body transfer is needed.

The contract covers canonical complete clauses, with repetitions and both
signs of zero. Formula traversal, standalone encoding packaging, malformed
input rejection and full dense-renaming runtime remain separate obligations.
-/

namespace LeanNPHardness.MachinePrimitives.OrderedClause

open Computability Turing Routines

abbrev ExtraAlphabet (_ : Unit) := Bool
abbrev Stack := CountedLiteralBody.Stack ⊕ Unit
abbrev Alphabet := ExtendedAlphabet (Γ := CountedLiteralBody.Alphabet) ExtraAlphabet

instance (k : Stack) : Fintype (Alphabet k) := by
  cases k with
  | inl k => exact inferInstanceAs (Fintype (CountedLiteralBody.Alphabet k))
  | inr k => exact inferInstanceAs (Fintype Bool)

/-- The original output becomes a private buffer; the new stack is caller output. -/
def contents (input count work buffer remaining output : List Bool) : Stacks Alphabet :=
  extendedStacks ExtraAlphabet
    (CountedLiteralBody.contents input count work buffer remaining) (fun _ => output)

/-- The four reversal stacks occupy buffer/count/work/output respectively. -/
def reverseStack : FrameMove.Stack → Stack
  | .input => .inl (.inl .output)
  | .count => .inl (.inl .count)
  | .work => .inl (.inl .work)
  | .output => .inr ()

/-- Only stack locations change; each alphabet remains Boolean. -/
def reverseBits (k : FrameMove.Stack) (bits : List Bool) : List (Alphabet (reverseStack k)) :=
  match k with
  | .input | .count | .work | .output => bits

/-- Keep caller input and the independent remaining-count stack untouched. -/
def reverseStacks (input remaining : List Bool) (S : Stacks FrameMove.Alphabet) :
    Stacks Alphabet :=
  contents input (S .count) (S .work) (S .input) remaining (S .output)

/-- Every source stack update has the corresponding isolated destination update. -/
theorem reverseStacks_update (input remaining : List Bool) (S : Stacks FrameMove.Alphabet)
    (k : FrameMove.Stack) (bits : List Bool) :
    reverseStacks input remaining (Function.update S k bits) =
      Function.update (reverseStacks input remaining S) (reverseStack k) (reverseBits k bits) := by
  funext j
  cases k <;> cases j with
  | inl j =>
      cases j with
      | inl j => cases j <;> simp [reverseStacks, contents, CountedLiteralBody.contents,
          FrameMove.contents, extendedStacks, reverseStack, reverseBits, Function.update]
      | inr j => cases j; simp [reverseStacks, contents, CountedLiteralBody.contents,
          extendedStacks, reverseStack, Function.update]
  | inr j => cases j; simp [reverseStacks, contents,
      extendedStacks, reverseStack, reverseBits, Function.update]

variable {Λ σ : Type}

/-- Redirect the reversal instructions without changing labels or finite control. -/
def reverseStmt : TM2.Stmt FrameMove.Alphabet Λ σ → TM2.Stmt Alphabet Λ σ
  | .push k f q => match k with
    | .input => .push (.inl (.inl .output)) f (reverseStmt q)
    | .count => .push (.inl (.inl .count)) f (reverseStmt q)
    | .work => .push (.inl (.inl .work)) f (reverseStmt q)
    | .output => .push (.inr ()) f (reverseStmt q)
  | .peek k f q => match k with
    | .input => .peek (.inl (.inl .output)) f (reverseStmt q)
    | .count => .peek (.inl (.inl .count)) f (reverseStmt q)
    | .work => .peek (.inl (.inl .work)) f (reverseStmt q)
    | .output => .peek (.inr ()) f (reverseStmt q)
  | .pop k f q => match k with
    | .input => .pop (.inl (.inl .output)) f (reverseStmt q)
    | .count => .pop (.inl (.inl .count)) f (reverseStmt q)
    | .work => .pop (.inl (.inl .work)) f (reverseStmt q)
    | .output => .pop (.inr ()) f (reverseStmt q)
  | .load f q => .load f (reverseStmt q)
  | .branch t a b => .branch t (reverseStmt a) (reverseStmt b)
  | .goto f => .goto f
  | .halt => .halt

def reverseCfg (input remaining : List Bool) (c : TM2.Cfg FrameMove.Alphabet Λ σ) :
    TM2.Cfg Alphabet Λ σ :=
  ⟨c.l, c.var, reverseStacks input remaining c.stk⟩

/-- Every statement preserves the embedding, including both untouched stacks. -/
theorem reverseStmt_stepAux (input remaining : List Bool)
    (stmt : TM2.Stmt FrameMove.Alphabet Λ σ) (v : σ) (S : Stacks FrameMove.Alphabet) :
    TM2.stepAux (reverseStmt stmt) v (reverseStacks input remaining S) =
      reverseCfg input remaining (TM2.stepAux stmt v S) := by
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

theorem reverse_step (input remaining : List Bool)
    (program : Λ → TM2.Stmt FrameMove.Alphabet Λ σ) (c : TM2.Cfg FrameMove.Alphabet Λ σ) :
    TM2.step (fun l => reverseStmt (program l)) (reverseCfg input remaining c) =
      (TM2.step program c).map (reverseCfg input remaining) := by
  rcases c with ⟨l, v, S⟩
  cases l with
  | none => rfl
  | some l => simp only [reverseCfg, TM2.step, reverseStmt_stepAux, Option.map_some]

/-- Exact finite execution is unchanged by the checked stack relocation. -/
theorem reverse_run (input remaining : List Bool)
    (program : Λ → TM2.Stmt FrameMove.Alphabet Λ σ) (n : Nat)
    (c : Option (TM2.Cfg FrameMove.Alphabet Λ σ)) :
    (flip Option.bind (TM2.step (fun l => reverseStmt (program l))))^[n]
        (c.map (reverseCfg input remaining)) =
      ((flip Option.bind (TM2.step program))^[n] c).map (reverseCfg input remaining) := by
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

theorem reverseRoutine_exits (r : Routine FrameMove.Alphabet) (input remaining : List Bool)
    {S S' : Stacks FrameMove.Alphabet} {n : Nat} (h : r.Exits S n S') :
    (reverseRoutine r).Exits (reverseStacks input remaining S) n
      (reverseStacks input remaining S') := by
  obtain ⟨v, h⟩ := h
  refine ⟨v, ?_⟩
  have run := reverse_run input remaining r.program n (some ⟨some r.entry, r.init, S⟩)
  rw [h] at run
  exact run

/-- Reverse only complete frames in the isolated buffer, retaining caller data. -/
theorem restore_exits (frames : List (List Bool)) (input remaining output : List Bool) :
    (reverseRoutine FrameReverse.routine).Exits
      (contents input [] [] (frames.flatMap BinaryNatLists.frame) remaining output)
      (FrameReverse.runSteps frames)
      (contents input [] [] [] remaining (frames.reverse.flatMap BinaryNatLists.frame ++ output)) :=
  reverseRoutine_exits FrameReverse.routine input remaining (FrameReverse.routine_exits frames output)

/-- Extract into the empty buffer, then restore frame order above caller output. -/
def routine : Routine Alphabet :=
  seq (extend ExtraAlphabet CountedClause.routine) (reverseRoutine FrameReverse.routine)

def runBound (literals : List (CNF.Literal Nat)) : Nat :=
  CountedClause.runBound literals +
    FrameReverse.runSteps (literals.reverse.map (fun l => encodeNat l.var))

/-- A complete encoded clause yields its variable frames in original occurrence order. -/
theorem clause_exits (literals : List (CNF.Literal Nat)) (input output : List Bool) :
    routine.ExitsLE
      (contents (BinaryNatLists.encodeNatList (literals.map CNF.Literal.toNat) ++ input)
        [] [] [] [] output)
      (runBound literals)
      (contents input [] [] [] []
        (literals.flatMap (fun l => BinaryNatLists.encodeNat l.var) ++ output)) := by
  obtain ⟨n, hn, extract⟩ := CountedClause.clause_exits literals input []
  have h₁ := extend_exits ExtraAlphabet CountedClause.routine (fun _ => output) extract
  simp only [List.append_nil] at h₁
  have h₂ := restore_exits (literals.reverse.map (fun l => encodeNat l.var)) input [] output
  simp only [List.flatMap_map, ← List.map_reverse, List.reverse_reverse] at h₂
  exact ⟨_, Nat.add_le_add_right hn _, seq_exits _ _ h₁ h₂⟩

/-- Exact restoration overhead in variable-body bits and number of occurrences. -/
theorem runBound_eq (literals : List (CNF.Literal Nat)) :
    runBound literals = CountedClause.runBound literals +
      2 * (literals.flatMap (fun l => BinaryNatLists.encodeNat l.var)).length +
      3 * literals.length + 1 := by
  simp only [runBound, FrameReverse.runSteps_eq, List.length_map, List.length_reverse,
    BinaryNatLists.encodeNat, List.length_flatMap, List.map_reverse, List.sum_reverse,
    List.map_map, Function.comp_def]
  omega

/-- Runtime depends on the consumed clause, independently of either retained suffix. -/
theorem runBound_le (literals : List (CNF.Literal Nat)) :
    runBound literals ≤
      let N := (BinaryNatLists.encodeNatList (literals.map CNF.Literal.toNat)).length
      N * (5 * N + 20) + 5 := by
  have hc := CountedClause.runBound_le literals
  have hv := CountedClause.output_length_le literals []
  simp only [List.append_nil, List.length_nil, Nat.add_zero, List.length_flatMap,
    List.map_reverse, List.sum_reverse] at hv
  have hm := CountedClause.count_le_body_length literals
  have hbody : (literals.flatMap (fun l => BinaryNatLists.encodeNat l.toNat)).length ≤
      (BinaryNatLists.encodeNatList (literals.map CNF.Literal.toNat)).length := by
    simp only [BinaryNatLists.encodeNatList, List.length_append, List.flatMap_map]
    omega
  have hcount := hm.trans hbody
  rw [runBound_eq]
  simp only [List.length_flatMap] at ⊢
  dsimp only at hc ⊢
  nlinarith

/-- Polynomial complete-clause contract, retaining repetitions and both caller suffixes. -/
theorem clause_exitsLE (literals : List (CNF.Literal Nat)) (input output : List Bool) :
    routine.ExitsLE
      (contents (BinaryNatLists.encodeNatList (literals.map CNF.Literal.toNat) ++ input)
        [] [] [] [] output)
      (let N := (BinaryNatLists.encodeNatList (literals.map CNF.Literal.toNat)).length;
        N * (5 * N + 20) + 5)
      (contents input [] [] [] []
        (literals.flatMap (fun l => BinaryNatLists.encodeNat l.var) ++ output)) :=
  (clause_exits literals input output).mono (runBound_le literals)

/-- Order restoration does not enlarge the variable body or disturb the output suffix. -/
theorem output_length_le (literals : List (CNF.Literal Nat)) (output : List Bool) :
    (literals.flatMap (fun l => BinaryNatLists.encodeNat l.var) ++ output).length ≤
      (BinaryNatLists.encodeNatList (literals.map CNF.Literal.toNat)).length + output.length := by
  simpa only [List.length_append, List.length_flatMap, List.map_reverse, List.sum_reverse] using
    CountedClause.output_length_le literals output

end LeanNPHardness.MachinePrimitives.OrderedClause
