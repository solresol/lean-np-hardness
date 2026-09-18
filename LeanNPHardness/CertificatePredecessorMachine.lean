import LeanNPHardness.BinaryArithmetic
import LeanNPHardness.CertificateCountMachine

/-!
# Binary predecessor on the certificate stack layout

This finite TM2 kernel consumes `remaining`, uses `scratch`, and writes the
predecessor in original bit order to `candidate`. It preserves arbitrary
contents of `input`, `query`, `count`, and `output`. The existing predecessor
execution lifts with exactly the same step count, bounded by `2b + 3` for
`b` input bits. Its reached halt becomes a live `done` continuation.

For canonical binary naturals the output is saturated predecessor, including
zero and one. This is not yet an in-place count decrement: ordered transfer
from `candidate` back to `remaining` and the traversal dispatcher are separate
obligations. The final continuation's halt is excluded from the bound.
-/

namespace LeanNPHardness.MachinePrimitives.CertificatePredecessor

open Computability Turing

abbrev Stack := CertificateCount.Stack
abbrev Alphabet := CertificateCount.Alphabet
abbrev State := PredState

inductive Label
  | pred (label : PredLabel)
  | done
  deriving DecidableEq, Fintype

def predStack : PredStack → Stack
  | .input => .remaining
  | .work => .scratch
  | .output => .candidate

def predContents (input query count output : List Bool)
    (contents : (k : PredStack) → List (binaryPredComputer.Γ k)) :
    (k : Stack) → List (Alphabet k)
  | .input => input
  | .query => query
  | .remaining => contents .input
  | .candidate => contents .output
  | .scratch => contents .work
  | .count => count
  | .output => output

@[simp] private theorem predContents_apply (input query count output : List Bool)
    (contents : (k : PredStack) → List (binaryPredComputer.Γ k)) (k : PredStack) :
    predContents input query count output contents (predStack k) = contents k := by
  cases k <;> rfl

private theorem predContents_update (input query count output : List Bool)
    (contents : (k : PredStack) → List (binaryPredComputer.Γ k))
    (k : PredStack) (value : List Bool) :
    Function.update (predContents input query count output contents) (predStack k) value =
      predContents input query count output (Function.update contents k value) := by
  funext index
  cases k <;> cases index <;>
    simp [Function.update, predContents, predStack]

/-- Reuse every predecessor statement, redirecting its halt in the same step. -/
def predStmt : TM2.Stmt binaryPredComputer.Γ PredLabel State →
    TM2.Stmt Alphabet Label State
  | .push k write next => .push (predStack k) write (predStmt next)
  | .peek k read next => .peek (predStack k) read (predStmt next)
  | .pop k read next => .pop (predStack k) read (predStmt next)
  | .load update next => .load update (predStmt next)
  | .branch test yes no => .branch test (predStmt yes) (predStmt no)
  | .goto next => .goto (fun state => .pred (next state))
  | .halt => .load (fun _ => binaryPredComputer.initialState) (.goto fun _ => .done)

def program : Label → TM2.Stmt Alphabet Label State
  | .pred label => predStmt (binaryPredComputer.m label)
  | .done => .halt

def computer : FinTM2 where
  K := Stack
  k₀ := .remaining
  k₁ := .candidate
  Γ := Alphabet
  Λ := Label
  main := .pred binaryPredComputer.main
  σ := State
  initialState := binaryPredComputer.initialState
  Γk₀Fin := Bool.fintype
  m := program

def cfg (label : Option Label) (state : State)
    (input query remaining candidate scratch count output : List Bool) : computer.Cfg where
  l := label
  var := state
  stk := CertificateCount.stackContents input query remaining candidate scratch count output

def predCfg (input query count output : List Bool) (c : binaryPredComputer.Cfg) :
    computer.Cfg where
  l := some (c.l.elim .done Label.pred)
  var := c.l.elim binaryPredComputer.initialState (fun _ => c.var)
  stk := predContents input query count output c.stk

/-- Statement simulation preserves all four stacks outside the predecessor. -/
theorem pred_stepAux
    (stmt : TM2.Stmt binaryPredComputer.Γ PredLabel State) (state : State)
    (contents : (k : PredStack) → List (binaryPredComputer.Γ k))
    (input query count output : List Bool) :
    TM2.stepAux (predStmt stmt) state (predContents input query count output contents) =
      predCfg input query count output (TM2.stepAux stmt state contents) := by
  induction stmt generalizing state contents with
  | push k write next ih =>
      simp only [predStmt, TM2.stepAux, predContents_apply]
      rw [predContents_update]
      exact ih _ _
  | peek k read next ih =>
      simpa only [predStmt, TM2.stepAux, predContents_apply] using
        ih (read state (contents k).head?) contents
  | pop k read next ih =>
      simp only [predStmt, TM2.stepAux, predContents_apply]
      rw [predContents_update]
      exact ih _ _
  | load update next ih =>
      simpa only [predStmt, TM2.stepAux] using ih (update state) contents
  | branch test yes no ihYes ihNo =>
      cases h : test state
      · simpa only [predStmt, TM2.stepAux, h, Bool.false_eq_true, cond_false] using
          ihNo state contents
      · simpa only [predStmt, TM2.stepAux, h, cond_true] using ihYes state contents
  | goto next => rfl
  | halt => rfl

private theorem pred_step (label : PredLabel) (state : State)
    (contents : (k : PredStack) → List (binaryPredComputer.Γ k))
    (input query count output : List Bool) :
    computer.step (predCfg input query count output ⟨some label, state, contents⟩) =
      some (predCfg input query count output
        (TM2.stepAux (binaryPredComputer.m label) state contents)) := by
  change some (TM2.stepAux (predStmt (binaryPredComputer.m label))
    state (predContents input query count output contents)) = _
  rw [pred_stepAux]

private theorem iterate_bind_none {α : Type} (step : α → Option α) (n : Nat) :
    (fun c => c.bind step)^[n] none = none := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply]; exact ih

/-- Lift any exact predecessor run with unchanged step count. -/
theorem pred_run (n : Nat) (start finish : binaryPredComputer.Cfg)
    (input query count output : List Bool)
    (run : (fun c => c.bind binaryPredComputer.step)^[n] (some start) = some finish) :
    (fun c => c.bind computer.step)^[n] (some (predCfg input query count output start)) =
      some (predCfg input query count output finish) := by
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
          rw [Option.bind_some, pred_step]
          exact ih _ run

private theorem predCfg_initList (bits input query count output : List Bool) :
    predCfg input query count output (initList binaryPredComputer bits) =
      cfg (some (.pred binaryPredComputer.main)) binaryPredComputer.initialState
        input query bits [] [] count output := by
  unfold predCfg cfg initList
  congr

private theorem predCfg_haltList (bits input query count output : List Bool) :
    predCfg input query count output (haltList binaryPredComputer bits) =
      cfg (some .done) binaryPredComputer.initialState input query [] bits [] count output := by
  unfold predCfg cfg haltList
  congr

/-- The public output witness supplies the exact count, with four stacks preserved. -/
theorem whole_word (bits input query count output : List Bool) :
    (fun c => c.bind computer.step)^[(binaryPred_outputsInTime bits).steps]
      (some (cfg (some (.pred binaryPredComputer.main)) binaryPredComputer.initialState
        input query bits [] [] count output)) =
      some (cfg (some .done) binaryPredComputer.initialState
        input query [] (binaryPredBits bits) [] count output) := by
  have run := pred_run _ _ _ input query count output
    (binaryPred_outputsInTime bits).evals_in_steps
  simpa only [Option.map_some, predCfg_initList, predCfg_haltList] using run

/-- Linear cost in the consumed count's bit length, independent of retained data. -/
def evalsToInTime (bits input query count output : List Bool) :
    EvalsToInTime computer.step
      (cfg (some (.pred binaryPredComputer.main)) binaryPredComputer.initialState
        input query bits [] [] count output)
      (some (cfg (some .done) binaryPredComputer.initialState
        input query [] (binaryPredBits bits) [] count output))
      (2 * bits.length + 3) where
  steps := (binaryPred_outputsInTime bits).steps
  evals_in_steps := whole_word bits input query count output
  steps_le_m := (binaryPred_outputsInTime bits).steps_le_m

/-- Canonical natural counts produce saturated predecessor on `candidate`. -/
def natural_evalsToInTime (n : Nat) (input query count output : List Bool) :
    EvalsToInTime computer.step
      (cfg (some (.pred binaryPredComputer.main)) binaryPredComputer.initialState
        input query (encodeNat n) [] [] count output)
      (some (cfg (some .done) binaryPredComputer.initialState
        input query [] (encodeNat (Nat.pred n)) [] count output))
      (2 * (encodeNat n).length + 3) := by
  simpa only [binaryPredBits_encodeNat] using
    evalsToInTime (encodeNat n) input query count output

/-- After one certificate element, the output count is the tail's length.
Every remaining frame, including repetitions, and the comparison output survive. -/
def list_tail_evalsToInTime (head : Nat) (tail : List Nat)
    (input query output : List Bool) :
    EvalsToInTime computer.step
      (cfg (some (.pred binaryPredComputer.main)) binaryPredComputer.initialState
        (tail.flatMap BinaryNatLists.encodeNat ++ input)
        query (encodeNat (head :: tail).length) [] [] [] output)
      (some (cfg (some .done) binaryPredComputer.initialState
        (tail.flatMap BinaryNatLists.encodeNat ++ input)
        query [] (encodeNat tail.length) [] [] output))
      (2 * (encodeNat (head :: tail).length).length + 3) := by
  simpa only [List.length_cons, Nat.pred_succ] using
    natural_evalsToInTime (head :: tail).length
      (tail.flatMap BinaryNatLists.encodeNat ++ input) query [] output

end LeanNPHardness.MachinePrimitives.CertificatePredecessor
