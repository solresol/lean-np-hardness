import LeanNPHardness.SerializedQueryMembershipMachine

/-!
# Canonical halting output for repeated membership queries

This finite nine-stack TM2 machine runs serialized repeated membership, drains
its retained certificate backup one bit per step, and halts with initial control.
On a canonical serialized certificate/query-list input all non-output stacks
finish empty. Output contains one membership bit per query occurrence, in
reverse query order. Empty lists, zero, and repetitions remain covered.

The separate cubic bound in complete serialized input bits includes the cleanup
entry, backup drain, control reset, and final halt. `QueryMembershipComputable`
supplies the function-level encoding and polynomial-time witness packaging.
Malformed-input rejection, literal/formula evaluation, and the full SAT verifier
remain separate obligations.
-/

namespace LeanNPHardness.MachinePrimitives.CanonicalQueryMembership

open Computability Turing

abbrev Stack := SerializedQueryMembership.Stack
abbrev Alphabet := SerializedQueryMembership.Alphabet
abbrev State := SerializedQueryMembership.State
abbrev initialState := SerializedQueryMembership.initialState

inductive Label
  | membership (label : SerializedQueryMembership.Label)
  | cleanup
  deriving DecidableEq, Fintype

/-- Redirect the component halt into backup cleanup, retaining all other steps. -/
def liftStmt : TM2.Stmt Alphabet SerializedQueryMembership.Label State →
    TM2.Stmt Alphabet Label State
  | .push k write next => .push k write (liftStmt next)
  | .peek k read next => .peek k read (liftStmt next)
  | .pop k read next => .pop k read (liftStmt next)
  | .load update next => .load update (liftStmt next)
  | .branch test yes no => .branch test (liftStmt yes) (liftStmt no)
  | .goto next => .goto (fun state => .membership (next state))
  | .halt => .goto (fun _ => .cleanup)

def program : Label → TM2.Stmt Alphabet Label State
  | .membership label => liftStmt (SerializedQueryMembership.program label)
  | .cleanup => .pop (.lookup .backup) (fun _ bit => (bit, EncodedQueryMembership.initialState))
      (.branch (fun state => state.1.isSome)
        (.goto fun _ => .cleanup)
        (.load (fun _ => initialState) .halt))

def computer : FinTM2 where
  K := Stack
  k₀ := .lookup .input
  k₁ := .lookup .output
  Γ := Alphabet
  Λ := Label
  main := .membership (.certificate .prefix)
  σ := State
  initialState := initialState
  Γk₀Fin := Bool.fintype
  m := program

def cfg (label : Option Label) (state : State)
    (input query remaining candidate scratch count output backup outer : List Bool) : computer.Cfg where
  l := label
  var := state
  stk := (SerializedQueryMembership.cfg none initialState
    input query remaining candidate scratch count output backup outer).stk

def liftCfg (c : SerializedQueryMembership.computer.Cfg) : computer.Cfg where
  l := some (c.l.elim .cleanup Label.membership)
  var := c.var
  stk := c.stk

/-- Statement simulation includes the component halt-to-cleanup transition. -/
theorem lift_stepAux (stmt : TM2.Stmt Alphabet SerializedQueryMembership.Label State)
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

private theorem lift_step (label : SerializedQueryMembership.Label) (state : State)
    (contents : (k : Stack) → List (Alphabet k)) :
    computer.step (liftCfg ⟨some label, state, contents⟩) =
      some (liftCfg (TM2.stepAux (SerializedQueryMembership.program label) state contents)) := by
  change some (TM2.stepAux (liftStmt (SerializedQueryMembership.program label)) state contents) = _
  rw [lift_stepAux]

private theorem iterate_bind_none {α : Type} (step : α → Option α) (n : Nat) :
    (fun c => c.bind step)^[n] none = none := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply]; exact ih

/-- Every exact component run lifts with the same number of steps. -/
theorem lift_run (n : Nat) (start finish : SerializedQueryMembership.computer.Cfg)
    (run : (fun c => c.bind SerializedQueryMembership.computer.step)^[n]
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

/-- The live membership continuation enters backup cleanup in one counted step. -/
theorem cleanup_entry_step (state : State)
    (input query remaining candidate scratch count output backup outer : List Bool) :
    computer.step
      (cfg (some (.membership (.membership (.loop .done)))) state
        input query remaining candidate scratch count output backup outer) =
      some (cfg (some .cleanup) state
        input query remaining candidate scratch count output backup outer) := by
  rfl

private theorem cleanup_step_cons (state : State) (bit : Bool)
    (input query remaining candidate scratch count output backup outer : List Bool) :
    computer.step (cfg (some .cleanup) state
      input query remaining candidate scratch count output (bit :: backup) outer) =
      some (cfg (some .cleanup) (some bit, EncodedQueryMembership.initialState)
        input query remaining candidate scratch count output backup outer) := by
  simp [computer, FinTM2.step, cfg, program, SerializedQueryMembership.cfg,
    EncodedQueryMembership.cfg, QueryMembershipLoop.cfg, QueryMembershipStep.cfg,
    QueryMembership.cfg, QueryMembership.liftCfg, QueryMembership.lookupContents,
    ReusableMembership.cfg, PreservingMembership.membershipContents]
  funext index
  cases index with
  | lookup index => cases index <;> simp [Function.update, QueryMembership.lookupContents,
      PreservingMembership.membershipContents, CertificateCount.stackContents]
  | outerRemaining => simp [Function.update, QueryMembership.lookupContents]

private theorem cleanup_step_nil (state : State)
    (input query remaining candidate scratch count output outer : List Bool) :
    computer.step (cfg (some .cleanup) state
      input query remaining candidate scratch count output [] outer) =
      some (cfg none initialState input query remaining candidate scratch count output [] outer) := by
  simp [computer, FinTM2.step, cfg, program, SerializedQueryMembership.cfg,
    EncodedQueryMembership.cfg, QueryMembershipLoop.cfg, QueryMembershipStep.cfg,
    QueryMembership.cfg, QueryMembership.liftCfg, QueryMembership.lookupContents,
    ReusableMembership.cfg, PreservingMembership.membershipContents]

/-- Backup cleanup takes one step per bit plus the final empty-stack halt.
All eight other stacks survive, including arbitrary input/output suffixes. -/
theorem cleanup_run (state : State)
    (input query remaining candidate scratch count output backup outer : List Bool) :
    (fun c => c.bind computer.step)^[backup.length + 1]
      (some (cfg (some .cleanup) state
        input query remaining candidate scratch count output backup outer)) =
      some (cfg none initialState input query remaining candidate scratch count output [] outer) := by
  induction backup generalizing state with
  | nil =>
      simpa only [List.length_nil, Nat.zero_add, Function.iterate_one, Option.bind_some] using
        cleanup_step_nil state input query remaining candidate scratch count output outer
  | cons bit backup ih =>
      rw [List.length_cons, Nat.add_right_comm, Function.iterate_succ_apply,
        Option.bind_some, cleanup_step_cons]
      exact ih _

/-- Exact serialized traversal, cleanup entry, backup drain, and halt. -/
def runSteps (queries xs : List Nat) : Nat :=
  SerializedQueryMembership.runSteps queries xs + ((BinaryNatLists.encodeNatList xs).length + 2)

/-- Exact halting execution clears backup and retains input/output suffixes. -/
theorem whole_input (queries xs : List Nat) (input output : List Bool) :
    (fun c => c.bind computer.step)^[runSteps queries xs]
      (some (cfg (some (.membership (.certificate .prefix))) initialState
        (SerializedQueryMembership.encodeInput queries xs ++ input) [] [] [] [] [] output [] [])) =
      some (cfg none initialState input [] [] [] [] []
        (QueryMembershipLoop.results queries xs ++ output) [] []) := by
  rw [runSteps, Nat.add_comm, Function.iterate_add_apply]
  have run := lift_run _ _ _ (SerializedQueryMembership.whole_input queries xs input output)
  rw [show cfg (some (.membership (.certificate .prefix))) initialState
      (SerializedQueryMembership.encodeInput queries xs ++ input) [] [] [] [] [] output [] [] =
      liftCfg (SerializedQueryMembership.cfg (some (.certificate .prefix)) initialState
        (SerializedQueryMembership.encodeInput queries xs ++ input) [] [] [] [] [] output [] []) from rfl,
    run]
  rw [show (BinaryNatLists.encodeNatList xs).length + 2 =
      ((BinaryNatLists.encodeNatList xs).length + 1) + 1 by omega,
    Function.iterate_succ_apply, Option.bind_some]
  change (fun c => c.bind computer.step)^[(BinaryNatLists.encodeNatList xs).length + 1]
    (computer.step (cfg (some (.membership (.membership (.loop .done)))) initialState
      input [] [] [] [] [] (QueryMembershipLoop.results queries xs ++ output)
        (BinaryNatLists.encodeNatList xs) [])) = _
  rw [cleanup_entry_step]
  exact cleanup_run _ _ _ _ _ _ _ _ _ _

/-- The cubic bit bound includes cleanup, control reset, and the final halt. -/
theorem runSteps_le_bit_bound (queries xs : List Nat) :
    runSteps queries xs ≤ (SerializedQueryMembership.encodeInput queries xs).length *
      ((SerializedQueryMembership.encodeInput queries xs).length *
        (2 * (SerializedQueryMembership.encodeInput queries xs).length + 18) +
        8 * (SerializedQueryMembership.encodeInput queries xs).length + 27) + 9 := by
  have length_eq := SerializedQueryMembership.encodeInput_length queries xs
  have certificate_le : (BinaryNatLists.encodeNatList xs).length ≤
      (SerializedQueryMembership.encodeInput queries xs).length := by omega
  have bound := SerializedQueryMembership.runSteps_le_bit_bound queries xs
  unfold runSteps
  rw [show (SerializedQueryMembership.encodeInput queries xs).length *
        (2 * (SerializedQueryMembership.encodeInput queries xs).length + 18) +
        8 * (SerializedQueryMembership.encodeInput queries xs).length + 27 =
      ((SerializedQueryMembership.encodeInput queries xs).length *
        (2 * (SerializedQueryMembership.encodeInput queries xs).length + 18) +
        8 * (SerializedQueryMembership.encodeInput queries xs).length + 26) + 1 by omega,
    Nat.mul_add, Nat.mul_one]
  omega

theorem initList_eq_cfg (input : List Bool) :
    initList computer input = cfg (some (.membership (.certificate .prefix)))
      initialState input [] [] [] [] [] [] [] [] := by
  unfold initList cfg
  congr
  funext index
  cases index with
  | lookup index => cases index <;> rfl
  | outerRemaining => rfl

theorem haltList_eq_cfg (output : List Bool) :
    haltList computer output = cfg none initialState [] [] [] [] [] [] output [] [] := by
  unfold haltList cfg
  congr
  funext index
  cases index with
  | lookup index => cases index <;> rfl
  | outerRemaining => rfl

/-- Canonical reverse membership output with a cubic serialized-bit runtime bound. -/
def outputsInTime (queries xs : List Nat) :
    TM2OutputsInTime computer (SerializedQueryMembership.encodeInput queries xs)
      (some (QueryMembershipLoop.results queries xs))
      ((SerializedQueryMembership.encodeInput queries xs).length *
        ((SerializedQueryMembership.encodeInput queries xs).length *
          (2 * (SerializedQueryMembership.encodeInput queries xs).length + 18) +
          8 * (SerializedQueryMembership.encodeInput queries xs).length + 27) + 9) := by
  rw [TM2OutputsInTime, initList_eq_cfg]
  simp only [Option.map_some, haltList_eq_cfg]
  exact {
    steps := runSteps queries xs
    evals_in_steps := by simpa only [List.append_nil] using whole_input queries xs [] []
    steps_le_m := runSteps_le_bit_bound queries xs
  }

end LeanNPHardness.MachinePrimitives.CanonicalQueryMembership
