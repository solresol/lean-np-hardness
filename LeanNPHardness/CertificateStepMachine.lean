import LeanNPHardness.CertificateComparisonMachine
import LeanNPHardness.CertificateDecrementMachine

/-!
# One certificate comparison and count decrement

One finite TM2 dispatcher compares a complete framed candidate with a
preloaded query and decrements the retained count in place. It reuses the
framed comparator's seven-stack embedding and the checked decrement machine.
The comparator's halt enters decrement in the same counted step.

The exact cost is the sum of comparison and decrement costs, bounded by
`2q + 2f + 4b + 8` for query, consumed-frame, and original count bit lengths.
The query and unread input/output suffixes survive, equality is pushed onto
output, and all three work stacks finish empty. Execution stops at the live
decrement continuation before its halt. A positive count is not checked here;
header dispatch, membership accumulation, and full traversal remain separate.
-/

namespace LeanNPHardness.MachinePrimitives.CertificateStep

open Computability Turing

abbrev Stack := CertificateCount.Stack
abbrev Alphabet := CertificateCount.Alphabet
abbrev State := FrameComparison.State × CertificateDecrement.State

def initialState : State := (FrameComparison.initialState, CertificateDecrement.initialState)

inductive Label
  | compare (label : FrameComparison.Label)
  | decrement (label : CertificateDecrement.Label)
  deriving DecidableEq, Fintype

abbrev compareStack := CertificateComparison.compareStack
abbrev compareContents := CertificateComparison.compareContents

@[simp] private theorem compareContents_apply (remaining : List Bool)
    (contents : (k : FrameComparison.Stack) → List (FrameComparison.Alphabet k))
    (k : FrameComparison.Stack) :
    compareContents remaining contents (compareStack k) = contents k := by
  cases k <;> rfl

private theorem compareContents_update (remaining : List Bool)
    (contents : (k : FrameComparison.Stack) → List (FrameComparison.Alphabet k))
    (k : FrameComparison.Stack) (value : List Bool) :
    Function.update (compareContents remaining contents) (compareStack k) value =
      compareContents remaining (Function.update contents k value) := by
  funext index
  cases k <;> cases index <;>
    simp [Function.update, compareContents, compareStack,
      CertificateComparison.compareContents, CertificateComparison.compareStack]

/-- Preserve the retained count during comparison and redirect its halt. -/
def compareStmt :
    TM2.Stmt FrameComparison.Alphabet FrameComparison.Label FrameComparison.State →
    TM2.Stmt Alphabet Label State
  | .push k write next => .push (compareStack k) (fun state => write state.1) (compareStmt next)
  | .peek k read next =>
      .peek (compareStack k)
        (fun state bit => (read state.1 bit, CertificateDecrement.initialState)) (compareStmt next)
  | .pop k read next =>
      .pop (compareStack k)
        (fun state bit => (read state.1 bit, CertificateDecrement.initialState)) (compareStmt next)
  | .load update next =>
      .load (fun state => (update state.1, CertificateDecrement.initialState)) (compareStmt next)
  | .branch test yes no => .branch (fun state => test state.1) (compareStmt yes) (compareStmt no)
  | .goto next => .goto (fun state => .compare (next state.1))
  | .halt => .load (fun _ => initialState) (.goto fun _ => .decrement CertificateDecrement.computer.main)

/-- Decrement retains the comparison result and uses the same seven stacks. -/
def decrementStmt :
    TM2.Stmt Alphabet CertificateDecrement.Label CertificateDecrement.State →
    TM2.Stmt Alphabet Label State
  | .push k write next => .push k (fun state => write state.2) (decrementStmt next)
  | .peek k read next =>
      .peek k (fun state bit => (FrameComparison.initialState, read state.2 bit)) (decrementStmt next)
  | .pop k read next =>
      .pop k (fun state bit => (FrameComparison.initialState, read state.2 bit)) (decrementStmt next)
  | .load update next =>
      .load (fun state => (FrameComparison.initialState, update state.2)) (decrementStmt next)
  | .branch test yes no =>
      .branch (fun state => test state.2) (decrementStmt yes) (decrementStmt no)
  | .goto next => .goto (fun state => .decrement (next state.2))
  | .halt => .halt

def program : Label → TM2.Stmt Alphabet Label State
  | .compare label => compareStmt (FrameComparison.program label)
  | .decrement label => decrementStmt (CertificateDecrement.program label)

def computer : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .output
  Γ := Alphabet
  Λ := Label
  main := .compare (.extract .prefix)
  σ := State
  initialState := initialState
  Γk₀Fin := Bool.fintype
  m := program

def cfg (label : Option Label) (state : State)
    (input query remaining candidate scratch count output : List Bool) : computer.Cfg where
  l := label
  var := state
  stk := CertificateCount.stackContents input query remaining candidate scratch count output

/-- A reached comparison halt is the live decrement entry with reset state. -/
def compareCfg (remaining : List Bool) (c : FrameComparison.computer.Cfg) : computer.Cfg where
  l := some (c.l.elim (.decrement CertificateDecrement.computer.main) Label.compare)
  var := c.l.elim initialState (fun _ => (c.var, CertificateDecrement.initialState))
  stk := compareContents remaining c.stk

/-- Statement simulation preserves the count and exact component step cost. -/
theorem compare_stepAux
    (stmt : TM2.Stmt FrameComparison.Alphabet FrameComparison.Label FrameComparison.State)
    (state : FrameComparison.State)
    (contents : (k : FrameComparison.Stack) → List (FrameComparison.Alphabet k))
    (remaining : List Bool) :
    TM2.stepAux (compareStmt stmt) (state, CertificateDecrement.initialState)
        (compareContents remaining contents) =
      compareCfg remaining (TM2.stepAux stmt state contents) := by
  induction stmt generalizing state contents with
  | push k write next ih =>
      simp only [compareStmt, TM2.stepAux, compareContents_apply]
      rw [compareContents_update]
      exact ih _ _
  | peek k read next ih =>
      simpa only [compareStmt, TM2.stepAux, compareContents_apply] using
        ih (read state (contents k).head?) contents
  | pop k read next ih =>
      simp only [compareStmt, TM2.stepAux, compareContents_apply]
      rw [compareContents_update]
      exact ih _ _
  | load update next ih =>
      simpa only [compareStmt, TM2.stepAux] using ih (update state) contents
  | branch test yes no ihYes ihNo =>
      cases h : test state
      · simpa only [compareStmt, TM2.stepAux, h, Bool.false_eq_true, cond_false] using
          ihNo state contents
      · simpa only [compareStmt, TM2.stepAux, h, cond_true] using ihYes state contents
  | goto next => rfl
  | halt => rfl

private theorem compare_step (label : FrameComparison.Label) (state : FrameComparison.State)
    (contents : (k : FrameComparison.Stack) → List (FrameComparison.Alphabet k))
    (remaining : List Bool) :
    computer.step (compareCfg remaining ⟨some label, state, contents⟩) =
      some (compareCfg remaining (TM2.stepAux (FrameComparison.program label) state contents)) := by
  change some (TM2.stepAux (compareStmt (FrameComparison.program label))
    (state, CertificateDecrement.initialState) (compareContents remaining contents)) = _
  rw [compare_stepAux]

private theorem iterate_bind_none {α : Type} (step : α → Option α) (n : Nat) :
    (fun c => c.bind step)^[n] none = none := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply]; exact ih

/-- Any exact comparison run lifts with the same step count. -/
theorem compare_run (n : Nat) (start finish : FrameComparison.computer.Cfg)
    (remaining : List Bool)
    (run : (fun c => c.bind FrameComparison.computer.step)^[n] (some start) = some finish) :
    (fun c => c.bind computer.step)^[n] (some (compareCfg remaining start)) =
      some (compareCfg remaining finish) := by
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
          rw [Option.bind_some, compare_step]
          exact ih _ run

def decrementCfg (c : CertificateDecrement.computer.Cfg) : computer.Cfg where
  l := c.l.map Label.decrement
  var := (FrameComparison.initialState, c.var)
  stk := c.stk

/-- Decrement statements have the same effect and counted cost under dispatch. -/
theorem decrement_stepAux
    (stmt : TM2.Stmt Alphabet CertificateDecrement.Label CertificateDecrement.State)
    (state : CertificateDecrement.State) (contents : (k : Stack) → List (Alphabet k)) :
    TM2.stepAux (decrementStmt stmt) (FrameComparison.initialState, state) contents =
      decrementCfg (TM2.stepAux stmt state contents) := by
  induction stmt generalizing state contents with
  | push k write next ih => simpa only [decrementStmt, TM2.stepAux] using ih _ _
  | peek k read next ih => simpa only [decrementStmt, TM2.stepAux] using ih _ _
  | pop k read next ih => simpa only [decrementStmt, TM2.stepAux] using ih _ _
  | load update next ih => simpa only [decrementStmt, TM2.stepAux] using ih _ _
  | branch test yes no ihYes ihNo =>
      cases h : test state
      · simpa only [decrementStmt, TM2.stepAux, h, Bool.false_eq_true, cond_false] using
          ihNo state contents
      · simpa only [decrementStmt, TM2.stepAux, h, cond_true] using ihYes state contents
  | goto next => rfl
  | halt => rfl

private theorem decrement_step (label : CertificateDecrement.Label)
    (state : CertificateDecrement.State) (contents : (k : Stack) → List (Alphabet k)) :
    computer.step (decrementCfg ⟨some label, state, contents⟩) =
      some (decrementCfg (TM2.stepAux (CertificateDecrement.program label) state contents)) := by
  change some (TM2.stepAux (decrementStmt (CertificateDecrement.program label))
    (FrameComparison.initialState, state) contents) = _
  rw [decrement_stepAux]

/-- Any exact decrement run lifts with the same step count. -/
theorem decrement_run (n : Nat) (start finish : CertificateDecrement.computer.Cfg)
    (run : (fun c => c.bind CertificateDecrement.computer.step)^[n]
      (some start) = some finish) :
    (fun c => c.bind computer.step)^[n] (some (decrementCfg start)) =
      some (decrementCfg finish) := by
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
          rw [Option.bind_some, decrement_step]
          exact ih _ run

/-- Comparing one frame enters decrement with equality on output. -/
theorem comparison_run (query bits input remaining output : List Bool) :
    (fun c => c.bind computer.step)^[
        3 * bits.length + max query.length bits.length + query.length + 5]
      (some (cfg (some (.compare (.extract .prefix))) initialState
        (BinaryNatLists.frame bits ++ input) query remaining [] [] [] output)) =
      some (cfg (some (.decrement CertificateDecrement.computer.main)) initialState
        input query remaining [] [] [] (decide (query = bits) :: output)) := by
  exact compare_run _ _ _ remaining (FrameComparison.whole_frame query bits input output)

/-- Exact comparison-plus-decrement execution; the final continuation halt is excluded. -/
theorem whole_frame (query bits input remaining output : List Bool) :
    (fun c => c.bind computer.step)^[
        (3 * bits.length + max query.length bits.length + query.length + 5) +
        ((binaryPred_outputsInTime remaining).steps + (2 * (binaryPredBits remaining).length + 2))]
      (some (cfg (some (.compare (.extract .prefix))) initialState
        (BinaryNatLists.frame bits ++ input) query remaining [] [] [] output)) =
      some (cfg (some (.decrement (.transfer .done))) initialState
        input query (binaryPredBits remaining) [] [] [] (decide (query = bits) :: output)) := by
  rw [Nat.add_comm (3 * bits.length + max query.length bits.length + query.length + 5),
    Function.iterate_add_apply, comparison_run]
  exact decrement_run _ _ _
    (CertificateDecrement.whole_word remaining input query [] (decide (query = bits) :: output))

/-- Linear runtime in query, consumed-frame, and retained-count bit lengths. -/
def evalsToInTime (query bits input remaining output : List Bool) :
    EvalsToInTime computer.step
      (cfg (some (.compare (.extract .prefix))) initialState
        (BinaryNatLists.frame bits ++ input) query remaining [] [] [] output)
      (some (cfg (some (.decrement (.transfer .done))) initialState
        input query (binaryPredBits remaining) [] [] [] (decide (query = bits) :: output)))
      (2 * query.length + 2 * (BinaryNatLists.frame bits).length + 4 * remaining.length + 8) where
  steps := (3 * bits.length + max query.length bits.length + query.length + 5) +
    ((binaryPred_outputsInTime remaining).steps + (2 * (binaryPredBits remaining).length + 2))
  evals_in_steps := whole_frame query bits input remaining output
  steps_le_m := by
    have := (binaryPred_outputsInTime remaining).steps_le_m
    have := binaryPredBits_length_le remaining
    rw [BinaryNatLists.frame_length]
    omega

/-- Canonical natural comparison and saturated count decrement. -/
def natural_evalsToInTime (query candidate remaining : Nat) (input output : List Bool) :
    EvalsToInTime computer.step
      (cfg (some (.compare (.extract .prefix))) initialState
        (BinaryNatLists.encodeNat candidate ++ input) (encodeNat query)
        (encodeNat remaining) [] [] [] output)
      (some (cfg (some (.decrement (.transfer .done))) initialState input (encodeNat query)
        (encodeNat (Nat.pred remaining)) [] [] [] (decide (query = candidate) :: output)))
      (2 * (encodeNat query).length + 2 * BinaryNatLists.natWireSize candidate +
        4 * (encodeNat remaining).length + 8) := by
  simpa only [BinaryNatLists.encodeNat, BinaryNatLists.natWireSize,
    BinaryNatLists.frame_length, BinaryEquality.encodeNat_eq_iff, binaryPredBits_encodeNat] using
    evalsToInTime (encodeNat query) (encodeNat candidate) input (encodeNat remaining) output

/-- One nonempty certificate-body step retains the tail and its exact count.
All later frames, including repeated entries, survive in their original order. -/
def list_head_evalsToInTime (query head : Nat) (tail : List Nat) (input output : List Bool) :
    EvalsToInTime computer.step
      (cfg (some (.compare (.extract .prefix))) initialState
        ((head :: tail).flatMap BinaryNatLists.encodeNat ++ input)
        (encodeNat query) (encodeNat (head :: tail).length) [] [] [] output)
      (some (cfg (some (.decrement (.transfer .done))) initialState
        (tail.flatMap BinaryNatLists.encodeNat ++ input)
        (encodeNat query) (encodeNat tail.length) [] [] [] (decide (query = head) :: output)))
      (2 * (encodeNat query).length + 2 * BinaryNatLists.natWireSize head +
        4 * (encodeNat (head :: tail).length).length + 8) := by
  simpa only [List.flatMap_cons, List.append_assoc, List.length_cons, Nat.pred_succ] using
    natural_evalsToInTime query head (head :: tail).length
      (tail.flatMap BinaryNatLists.encodeNat ++ input) output

end LeanNPHardness.MachinePrimitives.CertificateStep
