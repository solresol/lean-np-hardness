import LeanNPHardness.ClauseEvaluationStepMachine

/-!
# Packed-literal accumulation preserving an outer literal count

This finite nine-stack TM2 machine embeds `ClauseEvaluationStep` and adds
`outerRemaining`, independent of the count used by certificate lookup.
Every exact component run retains arbitrary outer contents at the same cost.
The clause-head interface consumes one packed literal frame and accumulates its
value, preserving all unread literal occurrences and the original literal count.

Certificate, accumulator, and outer count are preloaded. Outer decrement,
count-controlled repetition, header loading, and full verifier assembly remain
separate obligations. The final live continuation halt is excluded.
-/

namespace LeanNPHardness.MachinePrimitives.ClauseLiteral

open Computability Turing

inductive Stack
  | evaluation (stack : ClauseEvaluationStep.Stack)
  | outerRemaining
  deriving DecidableEq, Fintype

def Alphabet (_ : Stack) : Type := Bool

abbrev Label := ClauseEvaluationStep.Label
abbrev State := ClauseEvaluationStep.State
abbrev initialState := ClauseEvaluationStep.initialState

def evaluationContents (outer : List Bool)
    (contents : (k : ClauseEvaluationStep.Stack) → List (ClauseEvaluationStep.Alphabet k)) :
    (k : Stack) → List (Alphabet k)
  | .evaluation k => contents k
  | .outerRemaining => outer

private theorem evaluationContents_update (outer : List Bool)
    (contents : (k : ClauseEvaluationStep.Stack) → List (ClauseEvaluationStep.Alphabet k))
    (k : ClauseEvaluationStep.Stack) (value : List Bool) :
    Function.update (evaluationContents outer contents) (.evaluation k) value =
      evaluationContents outer (Function.update contents k value) := by
  funext index
  cases index with
  | evaluation index => simp [Function.update, evaluationContents]
  | outerRemaining => simp [Function.update, evaluationContents]

/-- The lifted statements touch only the eight evaluation stacks. -/
def liftStmt : TM2.Stmt ClauseEvaluationStep.Alphabet Label State → TM2.Stmt Alphabet Label State
  | .push k write next => .push (.evaluation k) write (liftStmt next)
  | .peek k read next => .peek (.evaluation k) read (liftStmt next)
  | .pop k read next => .pop (.evaluation k) read (liftStmt next)
  | .load update next => .load update (liftStmt next)
  | .branch test yes no => .branch test (liftStmt yes) (liftStmt no)
  | .goto next => .goto next
  | .halt => .halt

def program (label : Label) : TM2.Stmt Alphabet Label State :=
  liftStmt (ClauseEvaluationStep.program label)

def computer : FinTM2 where
  K := Stack
  k₀ := .evaluation .input
  k₁ := .evaluation .output
  Γ := Alphabet
  Λ := Label
  main := ClauseEvaluationStep.computer.main
  σ := State
  initialState := initialState
  Γk₀Fin := Bool.fintype
  m := program

def liftCfg (outer : List Bool) (c : ClauseEvaluationStep.computer.Cfg) : computer.Cfg where
  l := c.l
  var := c.var
  stk := evaluationContents outer c.stk

def cfg (label : Option Label) (state : State)
    (input query remaining candidate scratch count output backup outer : List Bool) : computer.Cfg :=
  liftCfg outer (ClauseEvaluationStep.cfg label state
    input query remaining candidate scratch count output backup)

/-- Statement execution retains the outer count, including on a reached halt. -/
theorem lift_stepAux (stmt : TM2.Stmt ClauseEvaluationStep.Alphabet Label State)
    (state : State)
    (contents : (k : ClauseEvaluationStep.Stack) → List (ClauseEvaluationStep.Alphabet k))
    (outer : List Bool) :
    TM2.stepAux (liftStmt stmt) state (evaluationContents outer contents) =
      liftCfg outer (TM2.stepAux stmt state contents) := by
  induction stmt generalizing state contents with
  | push k write next ih =>
      simp only [liftStmt, TM2.stepAux, evaluationContents]
      rw [evaluationContents_update]
      exact ih _ _
  | peek k read next ih => simpa only [liftStmt, TM2.stepAux, evaluationContents] using ih _ _
  | pop k read next ih =>
      simp only [liftStmt, TM2.stepAux, evaluationContents]
      rw [evaluationContents_update]
      exact ih _ _
  | load update next ih => simpa only [liftStmt, TM2.stepAux] using ih _ _
  | branch test yes no ihYes ihNo =>
      cases h : test state
      · simpa only [liftStmt, TM2.stepAux, h, Bool.false_eq_true, cond_false] using ihNo state contents
      · simpa only [liftStmt, TM2.stepAux, h, cond_true] using ihYes state contents
  | goto next => rfl
  | halt => rfl

/-- One source step costs one lifted step and leaves the outer stack unchanged. -/
theorem lift_step (outer : List Bool) (c : ClauseEvaluationStep.computer.Cfg) :
    computer.step (liftCfg outer c) =
      (ClauseEvaluationStep.computer.step c).map (liftCfg outer) := by
  rcases c with ⟨label, state, contents⟩
  cases label with
  | none => rfl
  | some label =>
      change some (TM2.stepAux (liftStmt (ClauseEvaluationStep.program label))
        state (evaluationContents outer contents)) = _
      rw [lift_stepAux]
      rfl

private theorem iterate_bind_none {α : Type} (step : α → Option α) (n : Nat) :
    (fun c => c.bind step)^[n] none = none := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply]; exact ih

/-- Arbitrary exact evaluation runs preserve any outer word with no runtime overhead. -/
theorem lift_run (n : Nat) (start finish : ClauseEvaluationStep.computer.Cfg)
    (outer : List Bool)
    (run : (fun c => c.bind ClauseEvaluationStep.computer.step)^[n]
      (some start) = some finish) :
    (fun c => c.bind computer.step)^[n] (some (liftCfg outer start)) =
      some (liftCfg outer finish) := by
  induction n generalizing start with
  | zero =>
      simp only [Function.iterate_zero, id_eq, Option.some.injEq] at run
      subst finish
      rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply] at run ⊢
      rw [Option.bind_some, lift_step]
      cases h : ClauseEvaluationStep.computer.step start with
      | none =>
          simp only [Option.bind_some, h] at run
          rw [iterate_bind_none] at run
          contradiction
      | some next =>
          simp only [Option.bind_some, h] at run
          exact ih next run

abbrev runSteps := ClauseEvaluationStep.runSteps

/-- Packed-literal accumulation preserves any outer word and both suffixes.
The full certificate survives and the inner count/query/workspace finish empty. -/
theorem whole_literal (literal : CNF.Literal Nat) (xs : List Nat)
    (input output outer : List Bool) (accumulated : Bool) :
    (fun c => c.bind computer.step)^[runSteps literal xs]
      (some (cfg (some computer.main) initialState
        (BinaryNatLists.encodeNat literal.toNat ++ input) [] [] [] [] []
        (accumulated :: output) (BinaryNatLists.encodeNatList xs) outer)) =
      some (cfg (some .done) initialState input [] [] [] [] []
        ((literal.eval (CNF.Certificate.assignment xs) || accumulated) :: output)
        (BinaryNatLists.encodeNatList xs) outer) := by
  exact lift_run _ _ _ outer
    (ClauseEvaluationStep.whole_literal literal xs input output accumulated)

/-- One literal retains the unread clause frames and original literal count.
The outer count is not decremented by this kernel; repeated literals remain. -/
theorem clause_head (literal : CNF.Literal Nat) (literals : CNF.Clause Nat)
    (xs : List Nat) (input output : List Bool) (accumulated : Bool) :
    (fun c => c.bind computer.step)^[runSteps literal xs]
      (some (cfg (some computer.main) initialState
        (((literal :: literals).map CNF.Literal.toNat).flatMap BinaryNatLists.encodeNat ++ input)
        [] [] [] [] [] (accumulated :: output) (BinaryNatLists.encodeNatList xs)
        (encodeNat (literal :: literals).length))) =
      some (cfg (some .done) initialState
        ((literals.map CNF.Literal.toNat).flatMap BinaryNatLists.encodeNat ++ input)
        [] [] [] [] [] ((literal.eval (CNF.Certificate.assignment xs) || accumulated) :: output)
        (BinaryNatLists.encodeNatList xs) (encodeNat (literal :: literals).length)) := by
  simpa only [List.map_cons, List.flatMap_cons, List.append_assoc] using
    whole_literal literal xs
      ((literals.map CNF.Literal.toNat).flatMap BinaryNatLists.encodeNat ++ input) output
      (encodeNat (literal :: literals).length) accumulated

/-- Processing the head extends the semantic value of an arbitrary processed prefix. -/
theorem clause_head_append (literal : CNF.Literal Nat) (processed literals : CNF.Clause Nat)
    (xs : List Nat) (input output : List Bool) :
    (fun c => c.bind computer.step)^[runSteps literal xs]
      (some (cfg (some computer.main) initialState
        (((literal :: literals).map CNF.Literal.toNat).flatMap BinaryNatLists.encodeNat ++ input)
        [] [] [] [] [] (processed.eval (CNF.Certificate.assignment xs) :: output)
        (BinaryNatLists.encodeNatList xs) (encodeNat (literal :: literals).length))) =
      some (cfg (some .done) initialState
        ((literals.map CNF.Literal.toNat).flatMap BinaryNatLists.encodeNat ++ input)
        [] [] [] [] [] ((processed ++ [literal]).eval (CNF.Certificate.assignment xs) :: output)
        (BinaryNatLists.encodeNatList xs) (encodeNat (literal :: literals).length)) := by
  simpa only [ClauseEvaluationStep.accumulated_eq_clause_append] using
    clause_head literal literals xs input output (processed.eval (CNF.Certificate.assignment xs))

/-- The complete-frame/certificate bound is independent of the retained outer word. -/
theorem runSteps_le_frame_bound (literal : CNF.Literal Nat) (xs : List Nat) :
    runSteps literal xs ≤ (BinaryNatLists.encodeNatList xs).length *
      (2 * BinaryNatLists.natWireSize literal.toNat +
        4 * (BinaryNatLists.encodeNatList xs).length + 18) +
      2 * BinaryNatLists.natWireSize literal.toNat + 14 :=
  ClauseEvaluationStep.runSteps_le_frame_bound literal xs

/-- Bounded literal accumulation with the independent outer count retained verbatim. -/
def literal_evalsToInTime (literal : CNF.Literal Nat) (xs : List Nat)
    (input output outer : List Bool) (accumulated : Bool) :
    EvalsToInTime computer.step
      (cfg (some computer.main) initialState
        (BinaryNatLists.encodeNat literal.toNat ++ input) [] [] [] [] []
        (accumulated :: output) (BinaryNatLists.encodeNatList xs) outer)
      (some (cfg (some .done) initialState input [] [] [] [] []
        ((literal.eval (CNF.Certificate.assignment xs) || accumulated) :: output)
        (BinaryNatLists.encodeNatList xs) outer))
      ((BinaryNatLists.encodeNatList xs).length *
        (2 * BinaryNatLists.natWireSize literal.toNat +
          4 * (BinaryNatLists.encodeNatList xs).length + 18) +
        2 * BinaryNatLists.natWireSize literal.toNat + 14) where
  steps := runSteps literal xs
  evals_in_steps := whole_literal literal xs input output outer accumulated
  steps_le_m := runSteps_le_frame_bound literal xs

end LeanNPHardness.MachinePrimitives.ClauseLiteral
