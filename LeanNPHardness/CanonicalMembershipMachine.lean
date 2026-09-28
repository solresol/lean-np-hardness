import LeanNPHardness.SerializedMembershipMachine

/-!
# Canonical halting output for serialized membership

This finite seven-stack TM2 machine runs serialized membership, discards the
retained query one bit per step, and halts with the initial control state.
On a canonical query/certificate input every non-output stack finishes empty,
so the result satisfies mathlib's `TM2OutputsInTime` contract. The bound is
quadratic in the complete serialized input's bit length, including cleanup
and the final halt. Repeated certificate entries are preserved by traversal.

`MembershipComputable` packages the encoding and polynomial-time function witness.
Malformed-input rejection and the full SAT verifier remain separate obligations.
-/

namespace LeanNPHardness.MachinePrimitives.CanonicalMembership

open Computability Turing

abbrev Stack := SerializedMembership.Stack
abbrev Alphabet := SerializedMembership.Alphabet
abbrev State := SerializedMembership.State
abbrev initialState := SerializedMembership.initialState

inductive Label
  | membership (label : SerializedMembership.Label)
  | cleanup
  deriving DecidableEq, Fintype

/-- Redirect the component halt into query cleanup, retaining all other steps. -/
def liftStmt : TM2.Stmt Alphabet SerializedMembership.Label State →
    TM2.Stmt Alphabet Label State
  | .push k write next => .push k write (liftStmt next)
  | .peek k read next => .peek k read (liftStmt next)
  | .pop k read next => .pop k read (liftStmt next)
  | .load update next => .load update (liftStmt next)
  | .branch test yes no => .branch test (liftStmt yes) (liftStmt no)
  | .goto next => .goto (fun state => .membership (next state))
  | .halt => .goto (fun _ => .cleanup)

def program : Label → TM2.Stmt Alphabet Label State
  | .membership label => liftStmt (SerializedMembership.program label)
  | .cleanup => .pop .query (fun _ bit => (bit, CertificateMembership.initialState))
      (.branch (fun state => state.1.isSome)
        (.goto fun _ => .cleanup)
        (.load (fun _ => initialState) .halt))

def computer : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .output
  Γ := Alphabet
  Λ := Label
  main := .membership (.query .prefix)
  σ := State
  initialState := initialState
  Γk₀Fin := Bool.fintype
  m := program

def cfg (label : Option Label) (state : State)
    (input query remaining candidate scratch count output : List Bool) : computer.Cfg where
  l := label
  var := state
  stk := CertificateCount.stackContents input query remaining candidate scratch count output

def liftCfg (c : SerializedMembership.computer.Cfg) : computer.Cfg where
  l := some (c.l.elim .cleanup Label.membership)
  var := c.var
  stk := c.stk

/-- Statement simulation includes the component halt-to-cleanup transition. -/
theorem lift_stepAux (stmt : TM2.Stmt Alphabet SerializedMembership.Label State)
    (state : State) (contents : (k : Stack) → List (Alphabet k)) :
    TM2.stepAux (liftStmt stmt) state contents =
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
  | halt => rfl

private theorem lift_step (label : SerializedMembership.Label) (state : State)
    (contents : (k : Stack) → List (Alphabet k)) :
    computer.step (liftCfg ⟨some label, state, contents⟩) =
      some (liftCfg (TM2.stepAux (SerializedMembership.program label) state contents)) := by
  change some (TM2.stepAux (liftStmt (SerializedMembership.program label)) state contents) = _
  rw [lift_stepAux]

private theorem iterate_bind_none {α : Type} (step : α → Option α) (n : Nat) :
    (fun c => c.bind step)^[n] none = none := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply]; exact ih

/-- Every exact component run lifts with the same number of steps. -/
theorem lift_run (n : Nat) (start finish : SerializedMembership.computer.Cfg)
    (run : (fun c => c.bind SerializedMembership.computer.step)^[n]
      (some start) = some finish) :
    (fun c => c.bind computer.step)^[n] (some (liftCfg start)) =
      some (liftCfg finish) := by
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

/-- The live membership continuation enters cleanup in one counted step. -/
theorem cleanup_entry_step (state : State)
    (input query remaining candidate scratch count output : List Bool) :
    computer.step
      (cfg (some (.membership (.membership (.loop .done)))) state
        input query remaining candidate scratch count output) =
      some (cfg (some .cleanup) state
        input query remaining candidate scratch count output) := by
  rfl

private theorem cleanup_step_cons (state : State) (bit : Bool)
    (input query remaining candidate scratch count output : List Bool) :
    computer.step (cfg (some .cleanup) state
      input (bit :: query) remaining candidate scratch count output) =
      some (cfg (some .cleanup) (some bit, CertificateMembership.initialState)
        input query remaining candidate scratch count output) := by
  simp [computer, FinTM2.step, cfg, program, CertificateCount.stackContents]
  funext index
  cases index <;> simp [Function.update, CertificateCount.stackContents]

private theorem cleanup_step_nil (state : State)
    (input remaining candidate scratch count output : List Bool) :
    computer.step (cfg (some .cleanup) state
      input [] remaining candidate scratch count output) =
      some (cfg none initialState input [] remaining candidate scratch count output) := by
  simp [computer, FinTM2.step, cfg, program, CertificateCount.stackContents]

/-- Query cleanup takes exactly one step per bit plus the final empty-stack halt.
All six other stacks are preserved, even when they are nonempty. -/
theorem cleanup_run (state : State)
    (input query remaining candidate scratch count output : List Bool) :
    (fun c => c.bind computer.step)^[query.length + 1]
      (some (cfg (some .cleanup) state
        input query remaining candidate scratch count output)) =
      some (cfg none initialState input [] remaining candidate scratch count output) := by
  induction query generalizing state with
  | nil =>
      simpa only [List.length_nil, Nat.zero_add, Function.iterate_one, Option.bind_some] using
        cleanup_step_nil state input remaining candidate scratch count output
  | cons bit query ih =>
      rw [List.length_cons, Nat.add_right_comm, Function.iterate_succ_apply,
        Option.bind_some, cleanup_step_cons]
      exact ih _

/-- Complete serialized membership, the cleanup entry, and the final query scan. -/
def runSteps (query : Nat) (xs : List Nat) : Nat :=
  SerializedMembership.runSteps query xs + ((encodeNat query).length + 2)

/-- Exact halting execution preserves input/output suffixes and clears the query. -/
theorem whole_input (query : Nat) (xs : List Nat) (input output : List Bool) :
    (fun c => c.bind computer.step)^[runSteps query xs]
      (some (cfg (some (.membership (.query .prefix))) initialState
        (SerializedMembership.encodeInput query xs ++ input) [] [] [] [] [] output)) =
      some (cfg none initialState input [] [] [] [] [] (decide (query ∈ xs) :: output)) := by
  rw [runSteps, Nat.add_comm, Function.iterate_add_apply]
  have run := lift_run _ _ _ (SerializedMembership.whole_input query xs input output)
  rw [show cfg (some (.membership (.query .prefix))) initialState
      (SerializedMembership.encodeInput query xs ++ input) [] [] [] [] [] output =
      liftCfg (SerializedMembership.cfg (some (.query .prefix)) initialState
        (SerializedMembership.encodeInput query xs ++ input) [] [] [] [] [] output) from rfl,
    run]
  rw [show (encodeNat query).length + 2 = ((encodeNat query).length + 1) + 1 by omega,
    Function.iterate_succ_apply, Option.bind_some]
  change (fun c => c.bind computer.step)^[List.length (encodeNat query) + 1]
    (computer.step (cfg (some (.membership (.membership (.loop .done)))) initialState
      input (encodeNat query) [] [] [] [] (decide (query ∈ xs) :: output))) = _
  rw [cleanup_entry_step]
  exact cleanup_run _ _ _ _ _ _ _ _

/-- The quadratic bit bound includes cleanup, control reset, and halting. -/
theorem runSteps_le_bit_bound (query : Nat) (xs : List Nat) :
    runSteps query xs ≤ (SerializedMembership.encodeInput query xs).length *
      (4 * (SerializedMembership.encodeInput query xs).length + 20) + 9 := by
  have query_le : (encodeNat query).length ≤
      (SerializedMembership.encodeInput query xs).length := by
    simp only [SerializedMembership.encodeInput, List.length_append,
      BinaryNatLists.encodeNat, BinaryNatLists.frame_length]
    omega
  have bound := SerializedMembership.runSteps_le_bit_bound query xs
  unfold runSteps
  rw [show 4 * (SerializedMembership.encodeInput query xs).length + 20 =
    (4 * (SerializedMembership.encodeInput query xs).length + 19) + 1 by omega,
    Nat.mul_add, Nat.mul_one]
  omega

theorem initList_eq_cfg (input : List Bool) :
    initList computer input =
      cfg (some (.membership (.query .prefix))) initialState input [] [] [] [] [] [] := by
  unfold initList cfg
  congr
  funext index
  cases index <;> rfl

theorem haltList_eq_cfg (output : List Bool) :
    haltList computer output = cfg none initialState [] [] [] [] [] [] output := by
  unfold haltList cfg
  congr
  funext index
  cases index <;> rfl

/-- Canonical list-output membership with a checked quadratic bit-runtime bound. -/
def outputsInTime (query : Nat) (xs : List Nat) :
    TM2OutputsInTime computer (SerializedMembership.encodeInput query xs)
      (some (encodeBool (decide (query ∈ xs))))
      ((SerializedMembership.encodeInput query xs).length *
        (4 * (SerializedMembership.encodeInput query xs).length + 20) + 9) := by
  rw [TM2OutputsInTime, initList_eq_cfg]
  simp only [Option.map_some, encodeBool, List.pure_def, haltList_eq_cfg]
  exact {
    steps := runSteps query xs
    evals_in_steps := by simpa only [List.append_nil] using whole_input query xs [] []
    steps_le_m := runSteps_le_bit_bound query xs
  }

end LeanNPHardness.MachinePrimitives.CanonicalMembership
