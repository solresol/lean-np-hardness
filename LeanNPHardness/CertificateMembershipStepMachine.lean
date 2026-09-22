import LeanNPHardness.CertificateStepMachine

/-!
# One certificate membership accumulation step

A finite seven-stack TM2 machine compares one framed entry, decrements the
retained count, and replaces the equality bit and previous accumulator on
output by their Boolean OR. The accumulation uses two pops and one push in
one TM2 statement, at the previous machine's final continuation.

The exact cost is the checked comparison/decrement cost plus one, bounded by
`2q + 2f + 4b + 9` in query, consumed-frame, and original count bit lengths.
The query, unread frames, and output suffix survive. All three work stacks
finish empty and control resets at a live `done` label before its halt.
Canonical frames and a supplied accumulator are assumed; header dispatch,
count-controlled repetition, and malformed-input rejection remain separate.
-/

namespace LeanNPHardness.MachinePrimitives.CertificateMembershipStep

open Computability Turing

abbrev Stack := CertificateCount.Stack
abbrev Alphabet := CertificateCount.Alphabet
abbrev State := CertificateStep.State × Bool

def initialState : State := (CertificateStep.initialState, false)

inductive Label
  | step (label : CertificateStep.Label)
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
    TM2.Stmt Alphabet CertificateStep.Label CertificateStep.State →
    TM2.Stmt Alphabet Label State
  | .push k write next => .push k (fun state => write state.1) (liftStmt next)
  | .peek k read next => .peek k (fun state bit => (read state.1 bit, false)) (liftStmt next)
  | .pop k read next => .pop k (fun state bit => (read state.1 bit, false)) (liftStmt next)
  | .load update next => .load (fun state => (update state.1, false)) (liftStmt next)
  | .branch test yes no => .branch (fun state => test state.1) (liftStmt yes) (liftStmt no)
  | .goto next => .goto (fun state => .step (next state.1))
  | .halt => accumulateStmt

def program : Label → TM2.Stmt Alphabet Label State
  | .step label => liftStmt (CertificateStep.program label)
  | .done => .halt

def computer : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .output
  Γ := Alphabet
  Λ := Label
  main := .step CertificateStep.computer.main
  σ := State
  initialState := initialState
  Γk₀Fin := Bool.fintype
  m := program

def cfg (label : Option Label) (state : State)
    (input query remaining candidate scratch count output : List Bool) : computer.Cfg where
  l := label
  var := state
  stk := CertificateCount.stackContents input query remaining candidate scratch count output

/-- A reached old halt includes accumulation; live configurations are unchanged. -/
def liftCfg (c : CertificateStep.computer.Cfg) : computer.Cfg where
  l := some (c.l.elim .done Label.step)
  var := c.l.elim initialState (fun _ => (c.var, false))
  stk := c.l.elim (accumulateContents c.stk) (fun _ => c.stk)

/-- Exact statement simulation, including the accumulation at a reached halt. -/
theorem lift_stepAux
    (stmt : TM2.Stmt Alphabet CertificateStep.Label CertificateStep.State)
    (state : CertificateStep.State) (contents : (k : Stack) → List (Alphabet k)) :
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

private theorem lift_step (label : CertificateStep.Label) (state : CertificateStep.State)
    (contents : (k : Stack) → List (Alphabet k)) :
    computer.step (liftCfg ⟨some label, state, contents⟩) =
      some (liftCfg (TM2.stepAux (CertificateStep.program label) state contents)) := by
  change some (TM2.stepAux (liftStmt (CertificateStep.program label)) (state, false) contents) = _
  rw [lift_stepAux]

private theorem iterate_bind_none {α : Type} (step : α → Option α) (n : Nat) :
    (fun c => c.bind step)^[n] none = none := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply]; exact ih

/-- Any exact old run lifts with the same cost, accumulating if it reaches halt. -/
theorem lift_run (n : Nat) (start finish : CertificateStep.computer.Cfg)
    (run : (fun c => c.bind CertificateStep.computer.step)^[n] (some start) = some finish) :
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
theorem accumulate_step (state : State) (equal accumulated : Bool)
    (input query remaining candidate scratch count output : List Bool) :
    computer.step (cfg (some (.step (.decrement (.transfer .done)))) state
      input query remaining candidate scratch count (equal :: accumulated :: output)) =
      some (cfg (some .done) initialState input query remaining candidate scratch count
        ((equal || accumulated) :: output)) := by
  change some (TM2.stepAux accumulateStmt state _) = _
  rw [accumulate_stepAux]
  congr 2
  funext index
  cases index <;> simp [accumulateContents, accumulateOutput, CertificateCount.stackContents]

/-- Comparison and decrement preserve the supplied accumulator until their continuation. -/
theorem comparison_decrement_run (query bits input remaining output : List Bool) (accumulated : Bool) :
    (fun c => c.bind computer.step)^[
        (3 * bits.length + max query.length bits.length + query.length + 5) +
        ((binaryPred_outputsInTime remaining).steps + (2 * (binaryPredBits remaining).length + 2))]
      (some (cfg (some computer.main) initialState
        (BinaryNatLists.frame bits ++ input) query remaining [] [] [] (accumulated :: output))) =
      some (cfg (some (.step (.decrement (.transfer .done)))) initialState
        input query (binaryPredBits remaining) [] [] []
        (decide (query = bits) :: accumulated :: output)) := by
  exact lift_run _ _ _ (CertificateStep.whole_frame query bits input remaining (accumulated :: output))

/-- One complete membership step costs the old comparison/decrement run plus one. -/
theorem whole_frame (query bits input remaining output : List Bool) (accumulated : Bool) :
    (fun c => c.bind computer.step)^[
        ((3 * bits.length + max query.length bits.length + query.length + 5) +
        ((binaryPred_outputsInTime remaining).steps + (2 * (binaryPredBits remaining).length + 2))) + 1]
      (some (cfg (some computer.main) initialState
        (BinaryNatLists.frame bits ++ input) query remaining [] [] [] (accumulated :: output))) =
      some (cfg (some .done) initialState input query (binaryPredBits remaining) [] [] []
        ((decide (query = bits) || accumulated) :: output)) := by
  rw [Function.iterate_succ_apply', comparison_decrement_run, Option.bind_some, accumulate_step]

/-- Linear bit-runtime bound for comparison, decrement, and Boolean accumulation. -/
def evalsToInTime (query bits input remaining output : List Bool) (accumulated : Bool) :
    EvalsToInTime computer.step
      (cfg (some computer.main) initialState
        (BinaryNatLists.frame bits ++ input) query remaining [] [] [] (accumulated :: output))
      (some (cfg (some .done) initialState input query (binaryPredBits remaining) [] [] []
        ((decide (query = bits) || accumulated) :: output)))
      (2 * query.length + 2 * (BinaryNatLists.frame bits).length + 4 * remaining.length + 9) where
  steps := (CertificateStep.evalsToInTime query bits input remaining (accumulated :: output)).steps + 1
  evals_in_steps := whole_frame query bits input remaining output accumulated
  steps_le_m := by
    have := (CertificateStep.evalsToInTime query bits input remaining (accumulated :: output)).steps_le_m
    omega

/-- Canonical natural equality and saturated decrement, retaining prior matches. -/
def natural_evalsToInTime (query candidate remaining : Nat) (input output : List Bool)
    (accumulated : Bool) :
    EvalsToInTime computer.step
      (cfg (some computer.main) initialState
        (BinaryNatLists.encodeNat candidate ++ input) (encodeNat query)
        (encodeNat remaining) [] [] [] (accumulated :: output))
      (some (cfg (some .done) initialState input (encodeNat query)
        (encodeNat (Nat.pred remaining)) [] [] [] ((decide (query = candidate) || accumulated) :: output)))
      (2 * (encodeNat query).length + 2 * BinaryNatLists.natWireSize candidate +
        4 * (encodeNat remaining).length + 9) := by
  simpa only [BinaryNatLists.encodeNat, BinaryNatLists.natWireSize, BinaryNatLists.frame_length,
    BinaryEquality.encodeNat_eq_iff, binaryPredBits_encodeNat] using
    evalsToInTime (encodeNat query) (encodeNat candidate) input (encodeNat remaining) output accumulated

/-- One list-head step retains every later frame and its exact count, including duplicates. -/
def list_head_evalsToInTime (query head : Nat) (tail : List Nat) (input output : List Bool)
    (accumulated : Bool) :
    EvalsToInTime computer.step
      (cfg (some computer.main) initialState
        ((head :: tail).flatMap BinaryNatLists.encodeNat ++ input)
        (encodeNat query) (encodeNat (head :: tail).length) [] [] [] (accumulated :: output))
      (some (cfg (some .done) initialState (tail.flatMap BinaryNatLists.encodeNat ++ input)
        (encodeNat query) (encodeNat tail.length) [] [] [] ((decide (query = head) || accumulated) :: output)))
      (2 * (encodeNat query).length + 2 * BinaryNatLists.natWireSize head +
        4 * (encodeNat (head :: tail).length).length + 9) := by
  simpa only [List.flatMap_cons, List.append_assoc, List.length_cons, Nat.pred_succ] using
    natural_evalsToInTime query head (head :: tail).length (tail.flatMap BinaryNatLists.encodeNat ++ input)
      output accumulated

/-- The accumulator records exactly a previous match or equality with this entry. -/
theorem accumulated_eq_true_iff (query head : Nat) (accumulated : Bool) :
    (decide (query = head) || accumulated) = true ↔ query = head ∨ accumulated = true := by
  simp

end LeanNPHardness.MachinePrimitives.CertificateMembershipStep
