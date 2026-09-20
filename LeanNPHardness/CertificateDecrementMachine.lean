import LeanNPHardness.CertificatePredecessorMachine
import LeanNPHardness.CertificateCountTransferMachine

/-!
# In-place decrement of the retained certificate count

One finite TM2 dispatcher computes saturated binary predecessor and transfers
its result through scratch back to `remaining` in original bit order. The
predecessor halt enters transfer in the same counted step. Input, query,
count, and output survive unchanged; candidate and scratch finish empty.

The exact cost is the predecessor witness's steps plus `2p + 2`, where `p`
is its output bit length. This is at most `4b + 5` for `b` initial count bits.
Execution ends at the live transfer `done` continuation, before its halt.
Header dispatch, membership accumulation, and full traversal remain separate.
-/

namespace LeanNPHardness.MachinePrimitives.CertificateDecrement

open Computability Turing

abbrev Stack := CertificateCount.Stack
abbrev Alphabet := CertificateCount.Alphabet
abbrev State := PredState × CertificateCountTransfer.State

def initialState : State := (binaryPredComputer.initialState, none)

inductive Label
  | pred (label : PredLabel)
  | transfer (label : CertificateCountTransfer.Label)
  deriving DecidableEq, Fintype

abbrev predStack := CertificatePredecessor.predStack
abbrev predContents := CertificatePredecessor.predContents

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
    simp [Function.update, predContents, predStack,
      CertificatePredecessor.predContents, CertificatePredecessor.predStack]

/-- Reuse every predecessor statement, redirecting its halt in the same step. -/
def predStmt : TM2.Stmt binaryPredComputer.Γ PredLabel PredState →
    TM2.Stmt Alphabet Label State
  | .push k write next => .push (predStack k) (fun state => write state.1) (predStmt next)
  | .peek k read next =>
      .peek (predStack k) (fun state bit => (read state.1 bit, none)) (predStmt next)
  | .pop k read next =>
      .pop (predStack k) (fun state bit => (read state.1 bit, none)) (predStmt next)
  | .load update next => .load (fun state => (update state.1, none)) (predStmt next)
  | .branch test yes no => .branch (fun state => test state.1) (predStmt yes) (predStmt no)
  | .goto next => .goto (fun state => .pred (next state.1))
  | .halt => .load (fun _ => initialState) (.goto fun _ => .transfer .reverse)

/-- Transfer uses the same seven stacks, with only its control lifted. -/
def transferStmt :
    TM2.Stmt Alphabet CertificateCountTransfer.Label CertificateCountTransfer.State →
    TM2.Stmt Alphabet Label State
  | .push k write next => .push k (fun state => write state.2) (transferStmt next)
  | .peek k read next =>
      .peek k (fun state bit => (binaryPredComputer.initialState, read state.2 bit))
        (transferStmt next)
  | .pop k read next =>
      .pop k (fun state bit => (binaryPredComputer.initialState, read state.2 bit))
        (transferStmt next)
  | .load update next =>
      .load (fun state => (binaryPredComputer.initialState, update state.2)) (transferStmt next)
  | .branch test yes no =>
      .branch (fun state => test state.2) (transferStmt yes) (transferStmt no)
  | .goto next => .goto (fun state => .transfer (next state.2))
  | .halt => .halt

def program : Label → TM2.Stmt Alphabet Label State
  | .pred label => predStmt (binaryPredComputer.m label)
  | .transfer label => transferStmt (CertificateCountTransfer.program label)

def computer : FinTM2 where
  K := Stack
  k₀ := .remaining
  k₁ := .remaining
  Γ := Alphabet
  Λ := Label
  main := .pred binaryPredComputer.main
  σ := State
  initialState := initialState
  Γk₀Fin := Bool.fintype
  m := program

def cfg (label : Option Label) (state : State)
    (input query remaining candidate scratch count output : List Bool) : computer.Cfg where
  l := label
  var := state
  stk := CertificateCount.stackContents input query remaining candidate scratch count output

def predCfg (input query count output : List Bool) (c : binaryPredComputer.Cfg) :
    computer.Cfg where
  l := some (c.l.elim (.transfer .reverse) Label.pred)
  var := c.l.elim initialState (fun _ => (c.var, none))
  stk := predContents input query count output c.stk

/-- Statement simulation preserves all four stacks outside the predecessor. -/
theorem pred_stepAux
    (stmt : TM2.Stmt binaryPredComputer.Γ PredLabel PredState) (state : PredState)
    (contents : (k : PredStack) → List (binaryPredComputer.Γ k))
    (input query count output : List Bool) :
    TM2.stepAux (predStmt stmt) (state, none) (predContents input query count output contents) =
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

private theorem pred_step (label : PredLabel) (state : PredState)
    (contents : (k : PredStack) → List (binaryPredComputer.Γ k))
    (input query count output : List Bool) :
    computer.step (predCfg input query count output ⟨some label, state, contents⟩) =
      some (predCfg input query count output
        (TM2.stepAux (binaryPredComputer.m label) state contents)) := by
  change some (TM2.stepAux (predStmt (binaryPredComputer.m label))
    (state, none) (predContents input query count output contents)) = _
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

/-- Transfer configuration retains the complete shared stack contents. -/
def transferCfg (c : CertificateCountTransfer.computer.Cfg) : computer.Cfg where
  l := c.l.map Label.transfer
  var := (binaryPredComputer.initialState, c.var)
  stk := c.stk

/-- Transfer statement simulation has no extra control-transition cost. -/
theorem transfer_stepAux
    (stmt : TM2.Stmt Alphabet CertificateCountTransfer.Label CertificateCountTransfer.State)
    (state : CertificateCountTransfer.State) (contents : (k : Stack) → List (Alphabet k)) :
    TM2.stepAux (transferStmt stmt) (binaryPredComputer.initialState, state) contents =
      transferCfg (TM2.stepAux stmt state contents) := by
  induction stmt generalizing state contents with
  | push k write next ih => simpa only [transferStmt, TM2.stepAux] using ih _ _
  | peek k read next ih => simpa only [transferStmt, TM2.stepAux] using ih _ _
  | pop k read next ih => simpa only [transferStmt, TM2.stepAux] using ih _ _
  | load update next ih => simpa only [transferStmt, TM2.stepAux] using ih _ _
  | branch test yes no ihYes ihNo =>
      cases h : test state
      · simpa only [transferStmt, TM2.stepAux, h, Bool.false_eq_true, cond_false] using
          ihNo state contents
      · simpa only [transferStmt, TM2.stepAux, h, cond_true] using ihYes state contents
  | goto next => rfl
  | halt => rfl

private theorem transfer_step (label : CertificateCountTransfer.Label)
    (state : CertificateCountTransfer.State) (contents : (k : Stack) → List (Alphabet k)) :
    computer.step (transferCfg ⟨some label, state, contents⟩) =
      some (transferCfg (TM2.stepAux (CertificateCountTransfer.program label) state contents)) := by
  change some (TM2.stepAux (transferStmt (CertificateCountTransfer.program label))
    (binaryPredComputer.initialState, state) contents) = _
  rw [transfer_stepAux]

/-- Lift any exact finite transfer run with unchanged step count. -/
theorem transfer_run (n : Nat) (start finish : CertificateCountTransfer.computer.Cfg)
    (run : (fun c => c.bind CertificateCountTransfer.computer.step)^[n]
      (some start) = some finish) :
    (fun c => c.bind computer.step)^[n] (some (transferCfg start)) =
      some (transferCfg finish) := by
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
          rw [Option.bind_some, transfer_step]
          exact ih _ run

private theorem predCfg_initList (bits input query count output : List Bool) :
    predCfg input query count output (initList binaryPredComputer bits) =
      cfg (some (.pred binaryPredComputer.main)) initialState
        input query bits [] [] count output := by
  unfold predCfg cfg initList
  congr

private theorem predCfg_haltList (bits input query count output : List Bool) :
    predCfg input query count output (haltList binaryPredComputer bits) =
      cfg (some (.transfer .reverse)) initialState input query [] bits [] count output := by
  unfold predCfg cfg haltList
  congr

/-- Predecessor execution enters ordered transfer in its final counted step. -/
theorem predecessor_run (bits input query count output : List Bool) :
    (fun c => c.bind computer.step)^[(binaryPred_outputsInTime bits).steps]
      (some (cfg (some (.pred binaryPredComputer.main)) initialState
        input query bits [] [] count output)) =
      some (cfg (some (.transfer .reverse)) initialState
        input query [] (binaryPredBits bits) [] count output) := by
  have run := pred_run _ _ _ input query count output
    (binaryPred_outputsInTime bits).evals_in_steps
  simpa only [Option.map_some, predCfg_initList, predCfg_haltList] using run

/-- In-place decrement: exact predecessor cost plus exact ordered-transfer cost. -/
theorem whole_word (bits input query count output : List Bool) :
    (fun c => c.bind computer.step)^[(binaryPred_outputsInTime bits).steps +
        (2 * (binaryPredBits bits).length + 2)]
      (some (cfg (some (.pred binaryPredComputer.main)) initialState
        input query bits [] [] count output)) =
      some (cfg (some (.transfer .done)) initialState
        input query (binaryPredBits bits) [] [] count output) := by
  rw [Nat.add_comm (binaryPred_outputsInTime bits).steps,
    Function.iterate_add_apply, predecessor_run]
  simpa only [transferCfg, CertificateCountTransfer.cfg, cfg, initialState, List.append_nil] using
    transfer_run _ _ _
      (CertificateCountTransfer.whole_word (binaryPredBits bits) input query [] count output)

/-- Linear runtime in the original count's bit length, independent of retained data. -/
def evalsToInTime (bits input query count output : List Bool) :
    EvalsToInTime computer.step
      (cfg (some (.pred binaryPredComputer.main)) initialState
        input query bits [] [] count output)
      (some (cfg (some (.transfer .done)) initialState
        input query (binaryPredBits bits) [] [] count output))
      (4 * bits.length + 5) where
  steps := (binaryPred_outputsInTime bits).steps + (2 * (binaryPredBits bits).length + 2)
  evals_in_steps := whole_word bits input query count output
  steps_le_m := by
    have := (binaryPred_outputsInTime bits).steps_le_m
    have := binaryPredBits_length_le bits
    omega

/-- Canonical counts are decremented in place, saturating at zero. -/
def natural_evalsToInTime (n : Nat) (input query count output : List Bool) :
    EvalsToInTime computer.step
      (cfg (some (.pred binaryPredComputer.main)) initialState
        input query (encodeNat n) [] [] count output)
      (some (cfg (some (.transfer .done)) initialState
        input query (encodeNat (Nat.pred n)) [] [] count output))
      (4 * (encodeNat n).length + 5) := by
  simpa only [binaryPredBits_encodeNat] using
    evalsToInTime (encodeNat n) input query count output

/-- After one element, the retained count becomes the tail length.
Unread frames, including repetitions, and all prior comparison output survive. -/
def list_tail_evalsToInTime (head : Nat) (tail : List Nat)
    (input query output : List Bool) :
    EvalsToInTime computer.step
      (cfg (some (.pred binaryPredComputer.main)) initialState
        (tail.flatMap BinaryNatLists.encodeNat ++ input)
        query (encodeNat (head :: tail).length) [] [] [] output)
      (some (cfg (some (.transfer .done)) initialState
        (tail.flatMap BinaryNatLists.encodeNat ++ input)
        query (encodeNat tail.length) [] [] [] output))
      (4 * (encodeNat (head :: tail).length).length + 5) := by
  simpa only [List.length_cons, Nat.pred_succ] using
    natural_evalsToInTime (head :: tail).length
      (tail.flatMap BinaryNatLists.encodeNat ++ input) query [] output

end LeanNPHardness.MachinePrimitives.CertificateDecrement
