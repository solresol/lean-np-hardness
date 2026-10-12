import LeanNPHardness.PackedLiteralEvaluationMachine

/-!
# One packed-literal clause accumulation step

A finite eight-stack TM2 machine evaluates one canonical packed literal frame,
then combines its value with the supplied clause accumulator using Boolean OR.
Two pops, one push, the control reset, and the continuation jump share one step.
The complete certificate and arbitrary unread input/output suffixes survive;
query/count/workspace finish empty.

Exact cost is `PackedLiteralEvaluation.runSteps + 1`, bounded by
`N * (2L + 4N + 18) + 2L + 14` in full literal-frame/certificate bits `L`/`N`.
The certificate and accumulator are preloaded; the final live continuation halt,
count-controlled clause traversal, and full verifier assembly remain separate.
-/

namespace LeanNPHardness.MachinePrimitives.ClauseEvaluationStep

open Computability Turing

abbrev Stack := PackedLiteralEvaluation.Stack
abbrev Alphabet := PackedLiteralEvaluation.Alphabet
abbrev State := PackedLiteralEvaluation.State × Bool

def initialState : State := (PackedLiteralEvaluation.initialState, false)

inductive Label
  | step (label : PackedLiteralEvaluation.Label)
  | done
  deriving DecidableEq, Fintype

/-- Total stack operation; the machine contract supplies both leading bits. -/
def accumulateOutput (output : List Bool) : List Bool :=
  (output.head?.getD false || output.tail.head?.getD false) :: output.tail.tail

def accumulateContents (contents : (k : Stack) → List (Alphabet k)) :
    (k : Stack) → List (Alphabet k) :=
  Function.update contents .output (accumulateOutput (contents .output))

/-- Both pops, OR, push, state reset, and continuation jump share one step. -/
def accumulateStmt : TM2.Stmt Alphabet Label State :=
  .pop .output (fun state bit => (state.1, bit.getD false)) <|
    .pop .output (fun state bit => (state.1, state.2 || bit.getD false)) <|
      .push .output (fun state => state.2) <|
        .load (fun _ => initialState) (.goto fun _ => .done)

/-- Accumulation changes only output, with no assumption on the other stacks. -/
theorem accumulate_stepAux (state : State)
    (contents : (k : Stack) → List (Alphabet k)) :
    TM2.stepAux accumulateStmt state contents =
      ⟨some .done, initialState, accumulateContents contents⟩ := by
  simp [accumulateStmt, TM2.stepAux, accumulateContents, accumulateOutput]
  rfl

/-- Lift the old machine, replacing its halt by the accumulation statement. -/
def liftStmt :
    TM2.Stmt Alphabet PackedLiteralEvaluation.Label PackedLiteralEvaluation.State →
    TM2.Stmt Alphabet Label State
  | .push k write next => .push k (fun state => write state.1) (liftStmt next)
  | .peek k read next => .peek k (fun state bit => (read state.1 bit, false)) (liftStmt next)
  | .pop k read next => .pop k (fun state bit => (read state.1 bit, false)) (liftStmt next)
  | .load update next => .load (fun state => (update state.1, false)) (liftStmt next)
  | .branch test yes no => .branch (fun state => test state.1) (liftStmt yes) (liftStmt no)
  | .goto next => .goto (fun state => .step (next state.1))
  | .halt => accumulateStmt

def program : Label → TM2.Stmt Alphabet Label State
  | .step label => liftStmt (PackedLiteralEvaluation.program label)
  | .done => .halt

def computer : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .output
  Γ := Alphabet
  Λ := Label
  main := .step PackedLiteralEvaluation.computer.main
  σ := State
  initialState := initialState
  Γk₀Fin := Bool.fintype
  m := program

def cfg (label : Option Label) (state : State)
    (input query remaining candidate scratch count output backup : List Bool) : computer.Cfg where
  l := label
  var := state
  stk := (PackedLiteralEvaluation.cfg none PackedLiteralEvaluation.initialState
    input query remaining candidate scratch count output backup).stk

/-- A reached old halt includes accumulation; live configurations are unchanged. -/
def liftCfg (c : PackedLiteralEvaluation.computer.Cfg) : computer.Cfg where
  l := some (c.l.elim .done Label.step)
  var := c.l.elim initialState (fun _ => (c.var, false))
  stk := c.l.elim (accumulateContents c.stk) (fun _ => c.stk)

/-- Exact statement simulation, including the accumulation at a reached halt. -/
theorem lift_stepAux
    (stmt : TM2.Stmt Alphabet PackedLiteralEvaluation.Label PackedLiteralEvaluation.State)
    (state : PackedLiteralEvaluation.State) (contents : (k : Stack) → List (Alphabet k)) :
    TM2.stepAux (liftStmt stmt) (state, false) contents =
      liftCfg (TM2.stepAux stmt state contents) := by
  induction stmt generalizing state contents with
  | push k write next ih => simpa only [liftStmt, TM2.stepAux] using ih _ _
  | peek k read next ih => simpa only [liftStmt, TM2.stepAux] using ih _ _
  | pop k read next ih => simpa only [liftStmt, TM2.stepAux] using ih _ _
  | load update next ih => simpa only [liftStmt, TM2.stepAux] using ih _ _
  | branch test yes no ihYes ihNo =>
      cases h : test state
      · simpa only [liftStmt, TM2.stepAux, h, Bool.false_eq_true, cond_false] using ihNo state contents
      · simpa only [liftStmt, TM2.stepAux, h, cond_true] using ihYes state contents
  | goto next => rfl
  | halt => exact accumulate_stepAux _ _

private theorem lift_step (label : PackedLiteralEvaluation.Label) (state : PackedLiteralEvaluation.State)
    (contents : (k : Stack) → List (Alphabet k)) :
    computer.step (liftCfg ⟨some label, state, contents⟩) =
      some (liftCfg (TM2.stepAux (PackedLiteralEvaluation.program label) state contents)) := by
  change some (TM2.stepAux (liftStmt (PackedLiteralEvaluation.program label)) (state, false) contents) = _
  rw [lift_stepAux]

private theorem iterate_bind_none {α : Type} (step : α → Option α) (n : Nat) :
    (fun c => c.bind step)^[n] none = none := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply]; exact ih

/-- Any exact old run lifts with the same cost, accumulating if it reaches halt. -/
theorem lift_run (n : Nat) (start finish : PackedLiteralEvaluation.computer.Cfg)
    (run : (fun c => c.bind PackedLiteralEvaluation.computer.step)^[n] (some start) = some finish) :
    (fun c => c.bind computer.step)^[n] (some (liftCfg start)) = some (liftCfg finish) := by
  induction n generalizing start with
  | zero =>
      simp only [Function.iterate_zero, id_eq, Option.some.injEq] at run
      subst finish
      rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply] at run ⊢
      rcases start with ⟨label, state, contents⟩
      cases label with
      | none =>
          simp only [Option.bind_some, FinTM2.step, TM2.step] at run
          rw [iterate_bind_none] at run
          contradiction
      | some label =>
          simp only [Option.bind_some, FinTM2.step, TM2.step] at run
          rw [Option.bind_some, lift_step]
          exact ih _ run

/-- The final old continuation combines two supplied bits in exactly one step. -/
theorem accumulate_step (state : State) (value accumulated : Bool)
    (input query remaining candidate scratch count output backup : List Bool) :
    computer.step (cfg (some (.step (.evaluation .done))) state
      input query remaining candidate scratch count (value :: accumulated :: output) backup) =
      some (cfg (some .done) initialState input query remaining candidate scratch count
        ((value || accumulated) :: output) backup) := by
  change some (TM2.stepAux accumulateStmt state _) = _
  rw [accumulate_stepAux]
  congr 2
  funext index
  cases index <;> simp [accumulateContents, accumulateOutput, PackedLiteralEvaluation.cfg,
    LiteralEvaluation.cfg, PreservingMembership.membershipContents, CertificateCount.stackContents]

/-- Exact packed-literal evaluation retains the supplied clause accumulator. -/
theorem evaluation_run (literal : CNF.Literal Nat) (xs : List Nat)
    (input output : List Bool) (accumulated : Bool) :
    (fun c => c.bind computer.step)^[PackedLiteralEvaluation.runSteps literal xs]
      (some (cfg (some computer.main) initialState
        (BinaryNatLists.encodeNat literal.toNat ++ input) [] [] [] [] []
        (accumulated :: output) (BinaryNatLists.encodeNatList xs))) =
      some (cfg (some (.step (.evaluation .done))) initialState input [] [] [] [] []
        (literal.eval (CNF.Certificate.assignment xs) :: accumulated :: output)
        (BinaryNatLists.encodeNatList xs)) := by
  exact lift_run _ _ _ (PackedLiteralEvaluation.whole_literal literal xs input (accumulated :: output))

/-- Exact evaluation plus one counted accumulation step. -/
def runSteps (literal : CNF.Literal Nat) (xs : List Nat) : Nat :=
  PackedLiteralEvaluation.runSteps literal xs + 1

/-- Evaluate one packed literal and accumulate its disjunctive contribution. -/
theorem whole_literal (literal : CNF.Literal Nat) (xs : List Nat)
    (input output : List Bool) (accumulated : Bool) :
    (fun c => c.bind computer.step)^[runSteps literal xs]
      (some (cfg (some computer.main) initialState
        (BinaryNatLists.encodeNat literal.toNat ++ input) [] [] [] [] []
        (accumulated :: output) (BinaryNatLists.encodeNatList xs))) =
      some (cfg (some .done) initialState input [] [] [] [] []
        ((literal.eval (CNF.Certificate.assignment xs) || accumulated) :: output)
        (BinaryNatLists.encodeNatList xs)) := by
  rw [runSteps, Function.iterate_succ_apply', evaluation_run, Option.bind_some, accumulate_step]

/-- Semantic accumulation records exactly a satisfied literal or a prior success. -/
theorem accumulated_eq_true_iff (literal : CNF.Literal Nat) (xs : List Nat)
    (accumulated : Bool) :
    (literal.eval (CNF.Certificate.assignment xs) || accumulated) = true ↔
      literal.Satisfied (CNF.Certificate.assignment xs) ∨ accumulated = true := by
  simp

/-- Extend the value of a previously processed clause, retaining literal occurrences. -/
theorem accumulated_eq_clause_append (literal : CNF.Literal Nat) (clause : CNF.Clause Nat)
    (xs : List Nat) :
    (literal.eval (CNF.Certificate.assignment xs) || clause.eval (CNF.Certificate.assignment xs)) =
      (clause ++ [literal]).eval (CNF.Certificate.assignment xs) := by
  simp [CNF.Clause.eval_append, Bool.or_comm]

/-- The accumulated result is the value of the processed prefix with this literal appended. -/
theorem whole_literal_append (literal : CNF.Literal Nat) (clause : CNF.Clause Nat)
    (xs : List Nat) (input output : List Bool) :
    (fun c => c.bind computer.step)^[runSteps literal xs]
      (some (cfg (some computer.main) initialState
        (BinaryNatLists.encodeNat literal.toNat ++ input) [] [] [] [] []
        (clause.eval (CNF.Certificate.assignment xs) :: output) (BinaryNatLists.encodeNatList xs))) =
      some (cfg (some .done) initialState input [] [] [] [] []
        ((clause ++ [literal]).eval (CNF.Certificate.assignment xs) :: output)
        (BinaryNatLists.encodeNatList xs)) := by
  simpa only [accumulated_eq_clause_append] using
    whole_literal literal xs input output (clause.eval (CNF.Certificate.assignment xs))

/-- Polynomial bound in the complete literal frame and complete certificate bits. -/
theorem runSteps_le_frame_bound (literal : CNF.Literal Nat) (xs : List Nat) :
    runSteps literal xs ≤ (BinaryNatLists.encodeNatList xs).length *
      (2 * BinaryNatLists.natWireSize literal.toNat +
        4 * (BinaryNatLists.encodeNatList xs).length + 18) +
      2 * BinaryNatLists.natWireSize literal.toNat + 14 := by
  have bound := PackedLiteralEvaluation.runSteps_le_frame_bound literal xs
  unfold runSteps
  omega

/-- Bounded evaluation and accumulation, before the final continuation halt. -/
def literal_evalsToInTime (literal : CNF.Literal Nat) (xs : List Nat)
    (input output : List Bool) (accumulated : Bool) :
    EvalsToInTime computer.step
      (cfg (some computer.main) initialState
        (BinaryNatLists.encodeNat literal.toNat ++ input) [] [] [] [] []
        (accumulated :: output) (BinaryNatLists.encodeNatList xs))
      (some (cfg (some .done) initialState input [] [] [] [] []
        ((literal.eval (CNF.Certificate.assignment xs) || accumulated) :: output)
        (BinaryNatLists.encodeNatList xs)))
      ((BinaryNatLists.encodeNatList xs).length *
        (2 * BinaryNatLists.natWireSize literal.toNat +
          4 * (BinaryNatLists.encodeNatList xs).length + 18) +
        2 * BinaryNatLists.natWireSize literal.toNat + 14) where
  steps := runSteps literal xs
  evals_in_steps := whole_literal literal xs input output accumulated
  steps_le_m := runSteps_le_frame_bound literal xs

end LeanNPHardness.MachinePrimitives.ClauseEvaluationStep
