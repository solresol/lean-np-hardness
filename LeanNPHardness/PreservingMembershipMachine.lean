import LeanNPHardness.BooleanCopyMachine
import LeanNPHardness.CertificateMembershipMachine

/-!
# Membership while retaining a complete certificate

An eight-stack finite TM2 dispatcher copies a separately supplied certificate
from `backup` through `scratch` onto `input`, then runs certificate membership.
The query and input/output suffixes survive, as does the complete backup,
including its header and repetitions. Count and work stacks finish empty.

The exact cost is `2N + 3` plus the existing membership cost: two copying
exhaustion steps and one entry step are included. The final live membership
continuation's halt is excluded. The polynomial bound uses raw binary query
length `q` and complete framed certificate length `N`. Loading the backup and
query, repeated-query dispatch, malformed-input rejection, and the full SAT
verifier remain separate obligations; this is not canonical list output.
-/

namespace LeanNPHardness.MachinePrimitives.PreservingMembership

open Computability Turing

inductive Stack
  | input | query | remaining | candidate | scratch | count | output | backup
  deriving DecidableEq, Fintype

def Alphabet (_ : Stack) : Type := Bool

inductive Label
  | copy (label : BooleanCopy.Label)
  | membership (label : CertificateMembership.Label)
  deriving DecidableEq, Fintype

abbrev State := BooleanCopy.State × CertificateMembership.State

def initialState : State := (none, CertificateMembership.initialState)

def copyStack : BooleanCopy.Stack → Stack
  | .source => .backup
  | .scratch => .scratch
  | .target => .input

def copyContents (query remaining candidate count output : List Bool)
    (contents : (k : BooleanCopy.Stack) → List (BooleanCopy.Alphabet k)) :
    (k : Stack) → List (Alphabet k)
  | .input => contents .target
  | .query => query
  | .remaining => remaining
  | .candidate => candidate
  | .scratch => contents .scratch
  | .count => count
  | .output => output
  | .backup => contents .source

def membershipStack : CertificateMembership.Stack → Stack
  | .input => .input
  | .query => .query
  | .remaining => .remaining
  | .candidate => .candidate
  | .scratch => .scratch
  | .count => .count
  | .output => .output

def membershipContents (backup : List Bool)
    (contents : (k : CertificateMembership.Stack) → List (CertificateMembership.Alphabet k)) :
    (k : Stack) → List (Alphabet k)
  | .input => contents .input
  | .query => contents .query
  | .remaining => contents .remaining
  | .candidate => contents .candidate
  | .scratch => contents .scratch
  | .count => contents .count
  | .output => contents .output
  | .backup => backup

@[simp] private theorem copyContents_apply (query remaining candidate count output : List Bool)
    (contents : (k : BooleanCopy.Stack) → List (BooleanCopy.Alphabet k)) (k : BooleanCopy.Stack) :
    copyContents query remaining candidate count output contents (copyStack k) = contents k := by
  cases k <;> rfl

private theorem copyContents_update (query remaining candidate count output : List Bool)
    (contents : (k : BooleanCopy.Stack) → List (BooleanCopy.Alphabet k))
    (k : BooleanCopy.Stack) (value : List Bool) :
    Function.update (copyContents query remaining candidate count output contents) (copyStack k) value =
      copyContents query remaining candidate count output (Function.update contents k value) := by
  funext index
  cases k <;> cases index <;>
    simp [Function.update, copyContents, copyStack]

@[simp] private theorem membershipContents_apply (backup : List Bool)
    (contents : (k : CertificateMembership.Stack) → List (CertificateMembership.Alphabet k)) (k : CertificateMembership.Stack) :
    membershipContents backup contents (membershipStack k) = contents k := by
  cases k <;> rfl

private theorem membershipContents_update (backup : List Bool)
    (contents : (k : CertificateMembership.Stack) → List (CertificateMembership.Alphabet k))
    (k : CertificateMembership.Stack) (value : List Bool) :
    Function.update (membershipContents backup contents) (membershipStack k) value =
      membershipContents backup (Function.update contents k value) := by
  funext index
  cases k <;> cases index <;>
    simp [Function.update, membershipContents, membershipStack]

/-- Embed copy control and stack operations in the shared finite machine. -/
def copyStmt : TM2.Stmt BooleanCopy.Alphabet BooleanCopy.Label BooleanCopy.State →
    TM2.Stmt Alphabet Label State
  | .push k write next => .push (copyStack k) (fun state => write state.1) (copyStmt next)
  | .peek k read next => .peek (copyStack k)
      (fun state bit => (read state.1 bit, CertificateMembership.initialState)) (copyStmt next)
  | .pop k read next => .pop (copyStack k)
      (fun state bit => (read state.1 bit, CertificateMembership.initialState)) (copyStmt next)
  | .load update next => .load (fun state => (update state.1, CertificateMembership.initialState)) (copyStmt next)
  | .branch test yes no => .branch (fun state => test state.1) (copyStmt yes) (copyStmt no)
  | .goto next => .goto (fun state => .copy (next state.1))
  | .halt => .load (fun _ => initialState) (.goto fun _ => .membership (.header .prefix))

/-- Embed membership control and stack operations in the shared finite machine. -/
def membershipStmt : TM2.Stmt CertificateMembership.Alphabet CertificateMembership.Label CertificateMembership.State →
    TM2.Stmt Alphabet Label State
  | .push k write next => .push (membershipStack k) (fun state => write state.2) (membershipStmt next)
  | .peek k read next => .peek (membershipStack k)
      (fun state bit => (none, read state.2 bit)) (membershipStmt next)
  | .pop k read next => .pop (membershipStack k)
      (fun state bit => (none, read state.2 bit)) (membershipStmt next)
  | .load update next => .load (fun state => (none, update state.2)) (membershipStmt next)
  | .branch test yes no => .branch (fun state => test state.2) (membershipStmt yes) (membershipStmt no)
  | .goto next => .goto (fun state => .membership (next state.2))
  | .halt => .halt

def program : Label → TM2.Stmt Alphabet Label State
  | .copy label => copyStmt (BooleanCopy.program label)
  | .membership label => membershipStmt (CertificateMembership.program label)

def computer : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .output
  Γ := Alphabet
  Λ := Label
  main := .copy .reverse
  σ := State
  initialState := initialState
  Γk₀Fin := Bool.fintype
  m := program

def cfg (label : Option Label) (state : State)
    (input query remaining candidate scratch count output backup : List Bool) : computer.Cfg where
  l := label
  var := state
  stk := membershipContents backup
    (CertificateCount.stackContents input query remaining candidate scratch count output)

def copyCfg (query remaining candidate count output : List Bool)
    (c : BooleanCopy.computer.Cfg) : computer.Cfg where
  l := some (c.l.elim (.membership (.header .prefix)) Label.copy)
  var := c.l.elim initialState (fun _ => (c.var, CertificateMembership.initialState))
  stk := copyContents query remaining candidate count output c.stk

def membershipCfg (backup : List Bool) (c : CertificateMembership.computer.Cfg) : computer.Cfg where
  l := c.l.map Label.membership
  var := (none, c.var)
  stk := membershipContents backup c.stk

/-- Statement simulation preserves all stacks outside the copy kernel. -/
theorem copy_stepAux
    (stmt : TM2.Stmt BooleanCopy.Alphabet BooleanCopy.Label BooleanCopy.State)
    (state : BooleanCopy.State)
    (contents : (k : BooleanCopy.Stack) → List (BooleanCopy.Alphabet k)) (query remaining candidate count output : List Bool) :
    TM2.stepAux (copyStmt stmt) (state, CertificateMembership.initialState) (copyContents query remaining candidate count output contents) =
      copyCfg query remaining candidate count output (TM2.stepAux stmt state contents) := by
  induction stmt generalizing state contents with
  | push k write next ih =>
      simp only [copyStmt, TM2.stepAux, copyContents_apply]
      rw [copyContents_update]
      exact ih _ _
  | peek k read next ih =>
      simpa only [copyStmt, TM2.stepAux, copyContents_apply] using ih _ _
  | pop k read next ih =>
      simp only [copyStmt, TM2.stepAux, copyContents_apply]
      rw [copyContents_update]
      exact ih _ _
  | load update next ih => simpa only [copyStmt, TM2.stepAux] using ih _ _
  | branch test yes no ihYes ihNo =>
      cases h : test state
      · simpa only [copyStmt, TM2.stepAux, h, Bool.false_eq_true, cond_false] using ihNo state contents
      · simpa only [copyStmt, TM2.stepAux, h, cond_true] using ihYes state contents
  | goto next => rfl
  | halt => rfl

private theorem copy_step (label : BooleanCopy.Label) (state : BooleanCopy.State)
    (contents : (k : BooleanCopy.Stack) → List (BooleanCopy.Alphabet k)) (query remaining candidate count output : List Bool) :
    computer.step (copyCfg query remaining candidate count output ⟨some label, state, contents⟩) =
      some (copyCfg query remaining candidate count output (TM2.stepAux (BooleanCopy.program label) state contents)) := by
  change some (TM2.stepAux (copyStmt (BooleanCopy.program label))
    (state, CertificateMembership.initialState) (copyContents query remaining candidate count output contents)) = _
  rw [copy_stepAux]

/-- Statement simulation preserves all stacks outside the membership kernel. -/
theorem membership_stepAux
    (stmt : TM2.Stmt CertificateMembership.Alphabet CertificateMembership.Label CertificateMembership.State)
    (state : CertificateMembership.State)
    (contents : (k : CertificateMembership.Stack) → List (CertificateMembership.Alphabet k)) (backup : List Bool) :
    TM2.stepAux (membershipStmt stmt) (none, state) (membershipContents backup contents) =
      membershipCfg backup (TM2.stepAux stmt state contents) := by
  induction stmt generalizing state contents with
  | push k write next ih =>
      simp only [membershipStmt, TM2.stepAux, membershipContents_apply]
      rw [membershipContents_update]
      exact ih _ _
  | peek k read next ih =>
      simpa only [membershipStmt, TM2.stepAux, membershipContents_apply] using ih _ _
  | pop k read next ih =>
      simp only [membershipStmt, TM2.stepAux, membershipContents_apply]
      rw [membershipContents_update]
      exact ih _ _
  | load update next ih => simpa only [membershipStmt, TM2.stepAux] using ih _ _
  | branch test yes no ihYes ihNo =>
      cases h : test state
      · simpa only [membershipStmt, TM2.stepAux, h, Bool.false_eq_true, cond_false] using ihNo state contents
      · simpa only [membershipStmt, TM2.stepAux, h, cond_true] using ihYes state contents
  | goto next => rfl
  | halt => rfl

private theorem membership_step (label : CertificateMembership.Label) (state : CertificateMembership.State)
    (contents : (k : CertificateMembership.Stack) → List (CertificateMembership.Alphabet k)) (backup : List Bool) :
    computer.step (membershipCfg backup ⟨some label, state, contents⟩) =
      some (membershipCfg backup (TM2.stepAux (CertificateMembership.program label) state contents)) := by
  change some (TM2.stepAux (membershipStmt (CertificateMembership.program label))
    (none, state) (membershipContents backup contents)) = _
  rw [membership_stepAux]

private theorem iterate_bind_none {α : Type} (step : α → Option α) (n : Nat) :
    (fun c => c.bind step)^[n] none = none := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply]; exact ih

/-- Lift an exact copy run without changing its step count. -/
theorem copy_run (n : Nat) (start finish : BooleanCopy.computer.Cfg) (query remaining candidate count output : List Bool)
    (run : (fun c => c.bind BooleanCopy.computer.step)^[n] (some start) = some finish) :
    (fun c => c.bind computer.step)^[n] (some (copyCfg query remaining candidate count output start)) =
      some (copyCfg query remaining candidate count output finish) := by
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
          rw [Option.bind_some, copy_step]
          exact ih _ run

/-- Lift an exact membership run without changing its step count. -/
theorem membership_run (n : Nat) (start finish : CertificateMembership.computer.Cfg) (backup : List Bool)
    (run : (fun c => c.bind CertificateMembership.computer.step)^[n] (some start) = some finish) :
    (fun c => c.bind computer.step)^[n] (some (membershipCfg backup start)) =
      some (membershipCfg backup finish) := by
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
          rw [Option.bind_some, membership_step]
          exact ih _ run

/-- The copier preserves arbitrary query/count/output data and restores backup. -/
theorem copy_whole_word (bits input query remaining candidate count output : List Bool) :
    (fun c => c.bind computer.step)^[2 * bits.length + 2]
      (some (cfg (some (.copy .reverse)) initialState
        input query remaining candidate [] count output bits)) =
      some (cfg (some (.copy .done)) initialState
        (bits ++ input) query remaining candidate [] count output bits) := by
  exact copy_run _ _ _ query remaining candidate count output (BooleanCopy.whole_word bits input)

/-- One counted transition enters membership after the copier's live endpoint. -/
theorem membership_entry_step
    (input query remaining candidate scratch count output backup : List Bool) :
    computer.step (cfg (some (.copy .done)) initialState
      input query remaining candidate scratch count output backup) =
      some (cfg (some (.membership (.header .prefix))) initialState
        input query remaining candidate scratch count output backup) := by
  rfl

/-- Exact copy, entry, and membership costs. -/
def runSteps (query : Nat) (xs : List Nat) : Nat :=
  (2 * (BinaryNatLists.encodeNatList xs).length + 3) + CertificateMembership.runSteps query xs

/-- Query membership using only a working copy; retain the entire certificate. -/
theorem whole_list (query : Nat) (xs : List Nat) (input output : List Bool) :
    (fun c => c.bind computer.step)^[runSteps query xs]
      (some (cfg (some (.copy .reverse)) initialState
        input (encodeNat query) [] [] [] [] output (BinaryNatLists.encodeNatList xs))) =
      some (cfg (some (.membership (.loop .done))) initialState
        input (encodeNat query) [] [] [] [] (decide (query ∈ xs) :: output)
        (BinaryNatLists.encodeNatList xs)) := by
  rw [runSteps, Nat.add_comm, Function.iterate_add_apply,
    show 2 * (BinaryNatLists.encodeNatList xs).length + 3 =
      1 + (2 * (BinaryNatLists.encodeNatList xs).length + 2) by omega,
    Function.iterate_add_apply, copy_whole_word]
  simp only [Function.iterate_one, Option.bind_some, membership_entry_step]
  exact membership_run _ _ _ (BinaryNatLists.encodeNatList xs)
    (CertificateMembership.whole_list query xs input output)

/-- Polynomial time in query bits and complete framed certificate bits. -/
theorem runSteps_le_bit_bound (query : Nat) (xs : List Nat) :
    runSteps query xs ≤ (BinaryNatLists.encodeNatList xs).length *
      (2 * (encodeNat query).length + 4 * (BinaryNatLists.encodeNatList xs).length + 18) + 7 := by
  have bound := CertificateMembership.runSteps_le_bit_bound query xs
  unfold runSteps
  rw [show 2 * (encodeNat query).length + 4 * (BinaryNatLists.encodeNatList xs).length + 18 =
    (2 * (encodeNat query).length + 4 * (BinaryNatLists.encodeNatList xs).length + 16) + 2
      by omega, Nat.mul_add]
  omega

/-- Bounded machine execution with retained certificate, query, and suffixes. -/
def evalsToInTime (query : Nat) (xs : List Nat) (input output : List Bool) :
    EvalsToInTime computer.step
      (cfg (some (.copy .reverse)) initialState
        input (encodeNat query) [] [] [] [] output (BinaryNatLists.encodeNatList xs))
      (some (cfg (some (.membership (.loop .done))) initialState
        input (encodeNat query) [] [] [] [] (decide (query ∈ xs) :: output)
        (BinaryNatLists.encodeNatList xs)))
      ((BinaryNatLists.encodeNatList xs).length *
        (2 * (encodeNat query).length + 4 * (BinaryNatLists.encodeNatList xs).length + 18) + 7) where
  steps := runSteps query xs
  evals_in_steps := whole_list query xs input output
  steps_le_m := runSteps_le_bit_bound query xs

end LeanNPHardness.MachinePrimitives.PreservingMembership
