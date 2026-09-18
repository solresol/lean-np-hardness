import LeanNPHardness.CertificateCountMachine
import LeanNPHardness.FrameComparisonMachine

/-!
# Framed comparison while retaining the certificate count

This finite TM2 kernel uses exactly `CertificateCount.Stack`. It lifts the
checked framed comparator while preserving arbitrary bits on `remaining`.
The reached comparison halt becomes a `done` continuation in the same step.
The exact cost and the linear bound use query and consumed-frame bit lengths;
neither depends on the retained count or the unread input/output suffixes.

The contract assumes one complete candidate frame and a preloaded query.
Header initialization, decrement, Boolean membership accumulation, and the
full traversal dispatcher are separate obligations. In particular this
kernel does not consume or validate the retained count.
-/

namespace LeanNPHardness.MachinePrimitives.CertificateComparison

open Computability Turing

abbrev Stack := CertificateCount.Stack
abbrev Alphabet := CertificateCount.Alphabet
abbrev State := FrameComparison.State

inductive Label
  | compare (label : FrameComparison.Label)
  | done
  deriving DecidableEq, Fintype

def compareStack : FrameComparison.Stack → Stack
  | .input => .input
  | .query => .query
  | .candidate => .candidate
  | .scratch => .scratch
  | .count => .count
  | .output => .output

def compareContents (remaining : List Bool)
    (contents : (k : FrameComparison.Stack) → List (FrameComparison.Alphabet k)) :
    (k : Stack) → List (Alphabet k)
  | .input => contents .input
  | .query => contents .query
  | .remaining => remaining
  | .candidate => contents .candidate
  | .scratch => contents .scratch
  | .count => contents .count
  | .output => contents .output

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
    simp [Function.update, compareContents, compareStack]

/-- Embed each statement without accessing the retained-count stack. -/
def compareStmt : TM2.Stmt FrameComparison.Alphabet FrameComparison.Label State →
    TM2.Stmt Alphabet Label State
  | .push k write next => .push (compareStack k) write (compareStmt next)
  | .peek k read next => .peek (compareStack k) read (compareStmt next)
  | .pop k read next => .pop (compareStack k) read (compareStmt next)
  | .load update next => .load update (compareStmt next)
  | .branch test yes no => .branch test (compareStmt yes) (compareStmt no)
  | .goto next => .goto (fun state => .compare (next state))
  | .halt => .load (fun _ => FrameComparison.initialState) (.goto fun _ => .done)

def program : Label → TM2.Stmt Alphabet Label State
  | .compare label => compareStmt (FrameComparison.program label)
  | .done => .halt

def computer : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .output
  Γ := Alphabet
  Λ := Label
  main := .compare (.extract .prefix)
  σ := State
  initialState := FrameComparison.initialState
  Γk₀Fin := Bool.fintype
  m := program

def cfg (label : Option Label) (state : State)
    (input query remaining candidate scratch count output : List Bool) : computer.Cfg where
  l := label
  var := state
  stk := CertificateCount.stackContents input query remaining candidate scratch count output

/-- A reached component halt denotes the live continuation, with reset state. -/
def compareCfg (remaining : List Bool) (c : FrameComparison.computer.Cfg) :
    computer.Cfg where
  l := some (c.l.elim .done Label.compare)
  var := c.l.elim FrameComparison.initialState (fun _ => c.var)
  stk := compareContents remaining c.stk

/-- Every statement preserves arbitrary contents of the remaining-count stack. -/
theorem compare_stepAux
    (stmt : TM2.Stmt FrameComparison.Alphabet FrameComparison.Label State)
    (state : State)
    (contents : (k : FrameComparison.Stack) → List (FrameComparison.Alphabet k))
    (remaining : List Bool) :
    TM2.stepAux (compareStmt stmt) state (compareContents remaining contents) =
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

private theorem compare_step (label : FrameComparison.Label) (state : State)
    (contents : (k : FrameComparison.Stack) → List (FrameComparison.Alphabet k))
    (remaining : List Bool) :
    computer.step (compareCfg remaining ⟨some label, state, contents⟩) =
      some (compareCfg remaining
        (TM2.stepAux (FrameComparison.program label) state contents)) := by
  change some (TM2.stepAux (compareStmt (FrameComparison.program label))
    state (compareContents remaining contents)) = _
  rw [compare_stepAux]

private theorem iterate_bind_none {α : Type} (step : α → Option α) (n : Nat) :
    (fun c => c.bind step)^[n] none = none := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply]; exact ih

/-- Lift any exact finite comparison run with the same step count. -/
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

/-- Compare one frame, restore the query, preserve the count and suffixes,
and empty all three work stacks. The continuation's halt is not counted. -/
theorem whole_frame (query bits input remaining output : List Bool) :
    (fun c => c.bind computer.step)^[
        3 * bits.length + max query.length bits.length + query.length + 5]
      (some (cfg (some (.compare (.extract .prefix))) FrameComparison.initialState
        (BinaryNatLists.frame bits ++ input) query remaining [] [] [] output)) =
      some (cfg (some .done) FrameComparison.initialState input query remaining [] [] []
        (decide (query = bits) :: output)) := by
  exact compare_run _ _ _ remaining (FrameComparison.whole_frame query bits input output)

/-- Linear runtime in query bits and the consumed frame, independent of count. -/
def evalsToInTime (query bits input remaining output : List Bool) :
    EvalsToInTime computer.step
      (cfg (some (.compare (.extract .prefix))) FrameComparison.initialState
        (BinaryNatLists.frame bits ++ input) query remaining [] [] [] output)
      (some (cfg (some .done) FrameComparison.initialState input query remaining [] [] []
        (decide (query = bits) :: output)))
      (2 * query.length + 2 * (BinaryNatLists.frame bits).length + 3) where
  steps := 3 * bits.length + max query.length bits.length + query.length + 5
  evals_in_steps := whole_frame query bits input remaining output
  steps_le_m := by rw [BinaryNatLists.frame_length]; omega

/-- Canonical natural equality with the retained count unchanged. -/
theorem natural_run (query candidate : Nat) (input remaining output : List Bool) :
    (fun c => c.bind computer.step)^[
        3 * (encodeNat candidate).length +
          max (encodeNat query).length (encodeNat candidate).length + (encodeNat query).length + 5]
      (some (cfg (some (.compare (.extract .prefix))) FrameComparison.initialState
        (BinaryNatLists.encodeNat candidate ++ input) (encodeNat query) remaining [] [] [] output)) =
      some (cfg (some .done) FrameComparison.initialState input (encodeNat query) remaining [] [] []
        (decide (query = candidate) :: output)) := by
  simpa only [BinaryEquality.encodeNat_eq_iff] using
    whole_frame (encodeNat query) (encodeNat candidate) input remaining output

/-- The natural-number interface uses binary query and framed candidate sizes. -/
def natural_evalsToInTime (query candidate : Nat) (input remaining output : List Bool) :
    EvalsToInTime computer.step
      (cfg (some (.compare (.extract .prefix))) FrameComparison.initialState
        (BinaryNatLists.encodeNat candidate ++ input) (encodeNat query) remaining [] [] [] output)
      (some (cfg (some .done) FrameComparison.initialState input (encodeNat query) remaining [] [] []
        (decide (query = candidate) :: output)))
      (2 * (encodeNat query).length + 2 * BinaryNatLists.natWireSize candidate + 3) := by
  simpa only [BinaryNatLists.encodeNat, BinaryNatLists.natWireSize,
    BinaryNatLists.frame_length, BinaryEquality.encodeNat_eq_iff] using
    evalsToInTime (encodeNat query) (encodeNat candidate) input remaining output

/-- Compare the head of a nonempty certificate body after header extraction.
Every remaining frame, including duplicates, survives; decrement is still due. -/
theorem list_head_run (query head : Nat) (tail : List Nat) (input output : List Bool) :
    (fun c => c.bind computer.step)^[
        3 * (encodeNat head).length +
          max (encodeNat query).length (encodeNat head).length + (encodeNat query).length + 5]
      (some (cfg (some (.compare (.extract .prefix))) FrameComparison.initialState
        ((head :: tail).flatMap BinaryNatLists.encodeNat ++ input)
        (encodeNat query) (encodeNat (head :: tail).length) [] [] [] output)) =
      some (cfg (some .done) FrameComparison.initialState
        (tail.flatMap BinaryNatLists.encodeNat ++ input)
        (encodeNat query) (encodeNat (head :: tail).length) [] [] []
        (decide (query = head) :: output)) := by
  simpa only [List.flatMap_cons, List.append_assoc] using
    natural_run query head (tail.flatMap BinaryNatLists.encodeNat ++ input)
      (encodeNat (head :: tail).length) output

end LeanNPHardness.MachinePrimitives.CertificateComparison
