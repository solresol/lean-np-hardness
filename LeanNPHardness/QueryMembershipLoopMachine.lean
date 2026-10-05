import LeanNPHardness.QueryMembershipStepMachine
import LeanNPHardness.CertificateMembershipLoopMachine

/-!
# Count-controlled queries against a retained certificate

A finite nine-stack TM2 dispatcher repeats framed membership lookup and outer
count decrement. The canonical count and complete framed certificate are
preloaded. Every query is consumed, including repetitions. Membership bits are
pushed in reverse query order above the original output suffix; the certificate
and input suffix survive, and all count and workspace stacks finish empty.

Exact execution counts each peek and return jump. A separate bound is
`Q * (N * (2Q + 4N + 18) + 8Q + 20) + 1`, where `Q` is the framed query-body
length and `N` is the full framed certificate length, both in bits.
`EncodedQueryMembershipMachine` supplies outer-header loading. Backup loading,
literal/formula evaluation, and the full verifier remain separate. Execution ends at a live continuation before its halt.
-/

namespace LeanNPHardness.MachinePrimitives.QueryMembershipLoop

open Computability Turing

abbrev Stack := QueryMembershipStep.Stack
abbrev Alphabet := QueryMembershipStep.Alphabet
abbrev State := QueryMembershipStep.State × Bool
def initialState : State := (QueryMembershipStep.initialState, false)

inductive Label
  | check
  | entry (label : QueryMembershipStep.Label)
  | done
  deriving DecidableEq, Fintype

/-- Reached component halts return to the count test in one counted step. -/
def liftStmt : TM2.Stmt Alphabet QueryMembershipStep.Label QueryMembershipStep.State →
    TM2.Stmt Alphabet Label State
  | .push k write next => .push k (fun state => write state.1) (liftStmt next)
  | .peek k read next => .peek k (fun state bit => (read state.1 bit, false)) (liftStmt next)
  | .pop k read next => .pop k (fun state bit => (read state.1 bit, false)) (liftStmt next)
  | .load update next => .load (fun state => (update state.1, false)) (liftStmt next)
  | .branch test yes no => .branch (fun state => test state.1) (liftStmt yes) (liftStmt no)
  | .goto next => .goto (fun state => .entry (next state.1))
  | .halt => .load (fun _ => initialState) (.goto fun _ => .check)

def program : Label → TM2.Stmt Alphabet Label State
  | .check =>
      .peek .outerRemaining (fun state bit => (state.1, bit.isSome)) <|
        .branch (fun state => state.2)
          (.load (fun _ => initialState)
            (.goto fun _ => .entry QueryMembershipStep.computer.main))
          (.load (fun _ => initialState) (.goto fun _ => .done))
  | .entry label => liftStmt (QueryMembershipStep.program label)
  | .done => .halt

def computer : FinTM2 where
  K := Stack
  k₀ := .lookup .input
  k₁ := .lookup .output
  Γ := Alphabet
  Λ := Label
  main := .check
  σ := State
  initialState := initialState
  Γk₀Fin := Bool.fintype
  m := program

def cfg (label : Option Label) (state : State)
    (input query remaining candidate scratch count output backup outer : List Bool) : computer.Cfg where
  l := label
  var := state
  stk := (QueryMembershipStep.cfg none QueryMembershipStep.initialState
    input query remaining candidate scratch count output backup outer).stk

def liftCfg (c : QueryMembershipStep.computer.Cfg) : computer.Cfg where
  l := some (c.l.elim .check Label.entry)
  var := c.l.elim initialState (fun _ => (c.var, false))
  stk := c.stk

/-- Component statements retain their exact cost and every stack. -/
theorem lift_stepAux (stmt : TM2.Stmt Alphabet QueryMembershipStep.Label QueryMembershipStep.State)
    (state : QueryMembershipStep.State) (contents : (k : Stack) → List (Alphabet k)) :
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
  | halt => rfl

private theorem lift_step (label : QueryMembershipStep.Label) (state : QueryMembershipStep.State)
    (contents : (k : Stack) → List (Alphabet k)) :
    computer.step (liftCfg ⟨some label, state, contents⟩) =
      some (liftCfg (TM2.stepAux (QueryMembershipStep.program label) state contents)) := by
  change some (TM2.stepAux (liftStmt (QueryMembershipStep.program label)) (state, false) contents) = _
  rw [lift_stepAux]

private theorem iterate_bind_none {α : Type} (step : α → Option α) (n : Nat) :
    (fun c => c.bind step)^[n] none = none := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply]; exact ih

/-- Exact component execution lifts without additional dispatch overhead. -/
theorem lift_run (n : Nat) (start finish : QueryMembershipStep.computer.Cfg)
    (run : (fun c => c.bind QueryMembershipStep.computer.step)^[n]
      (some start) = some finish) :
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

/-- Peek tests presence, not the low bit, and preserves every stack. -/
theorem check_step (state : State)
    (input query remaining candidate scratch count output backup outer : List Bool) :
    computer.step (cfg (some .check) state
      input query remaining candidate scratch count output backup outer) =
      some (cfg (some (if outer = [] then .done
        else .entry QueryMembershipStep.computer.main)) initialState
        input query remaining candidate scratch count output backup outer) := by
  cases outer <;>
    simp [computer, FinTM2.step, cfg, program, QueryMembershipStep.cfg,
      QueryMembership.cfg, QueryMembership.liftCfg, QueryMembership.lookupContents, TM2.stepAux]

/-- The live decrement endpoint returns to the count test in one step. -/
theorem return_step (state : State)
    (input query remaining candidate scratch count output backup outer : List Bool) :
    computer.step (cfg (some (.entry (.decrement (.transfer .done)))) state
      input query remaining candidate scratch count output backup outer) =
      some (cfg (some .check) initialState
        input query remaining candidate scratch count output backup outer) := rfl

/-- One complete query plus the return jump restores the exact tail count. -/
theorem entry_run (query : Nat) (queries xs : List Nat) (input output : List Bool) :
    (fun c => c.bind computer.step)^[QueryMembershipStep.runSteps query xs
        (encodeNat (query :: queries).length) + 1]
      (some (cfg (some (.entry QueryMembershipStep.computer.main)) initialState
        ((query :: queries).flatMap BinaryNatLists.encodeNat ++ input)
        [] [] [] [] [] output (BinaryNatLists.encodeNatList xs)
        (encodeNat (query :: queries).length))) =
      some (cfg (some .check) initialState
        (queries.flatMap BinaryNatLists.encodeNat ++ input)
        [] [] [] [] [] (decide (query ∈ xs) :: output)
        (BinaryNatLists.encodeNatList xs) (encodeNat queries.length)) := by
  have run := lift_run _ _ _ (QueryMembershipStep.list_head query queries xs input output)
  rw [Function.iterate_succ_apply', show
    (fun c => c.bind computer.step)^[QueryMembershipStep.runSteps query xs
        (encodeNat (query :: queries).length)]
      (some (cfg (some (.entry QueryMembershipStep.computer.main)) initialState
        ((query :: queries).flatMap BinaryNatLists.encodeNat ++ input)
        [] [] [] [] [] output (BinaryNatLists.encodeNatList xs)
        (encodeNat (query :: queries).length))) =
      some (cfg (some (.entry (.decrement (.transfer .done)))) initialState
        (queries.flatMap BinaryNatLists.encodeNat ++ input)
        [] [] [] [] [] (decide (query ∈ xs) :: output)
        (BinaryNatLists.encodeNatList xs) (encodeNat queries.length)) from run,
    Option.bind_some, return_step]

/-- Exact cost: one test and return per entry, and one final zero test. -/
def runSteps (xs : List Nat) : List Nat → Nat
  | [] => 1
  | query :: queries => (runSteps xs queries +
      (QueryMembershipStep.runSteps query xs (encodeNat (query :: queries).length) + 1)) + 1

/-- Semantic output in stack order; repeated queries each contribute one bit. -/
def results (queries xs : List Nat) : List Bool :=
  (queries.map fun query => decide (query ∈ xs)).reverse

/-- Pushing the head result before the tail yields reverse query order. -/
theorem results_cons (query : Nat) (queries xs : List Nat) (output : List Bool) :
    results queries xs ++ (decide (query ∈ xs) :: output) =
      results (query :: queries) xs ++ output := by
  simp [results, List.append_assoc]

/-- Traverse all canonical query frames, retaining the certificate and both suffixes. -/
theorem whole_list (queries xs : List Nat) (input output : List Bool) :
    (fun c => c.bind computer.step)^[runSteps xs queries]
      (some (cfg (some .check) initialState
        (queries.flatMap BinaryNatLists.encodeNat ++ input)
        [] [] [] [] [] output (BinaryNatLists.encodeNatList xs) (encodeNat queries.length))) =
      some (cfg (some .done) initialState input [] [] [] [] []
        (results queries xs ++ output) (BinaryNatLists.encodeNatList xs) []) := by
  induction queries generalizing output with
  | nil =>
      rw [runSteps, Function.iterate_one, Option.bind_some, check_step]
      simp [encodeNat, encodeNum, results]
  | cons query queries ih =>
      rw [runSteps, Function.iterate_succ_apply, Option.bind_some, check_step]
      have nonempty : encodeNat (query :: queries).length ≠ [] := by
        intro empty
        have zero := (CertificateCount.encodeNat_eq_nil_iff (query :: queries).length).mp empty
        simp only [List.length_cons, Nat.succ_ne_zero] at zero
      rw [if_neg nonempty, Function.iterate_add_apply, entry_run, ih, results_cons]

/-- A uniform bound for traversal inside any larger framed query-body budget. -/
theorem runSteps_le (queries xs : List Nat) (budget : Nat)
    (fits : (queries.flatMap BinaryNatLists.encodeNat).length ≤ budget) :
    runSteps xs queries ≤ queries.length *
      ((BinaryNatLists.encodeNatList xs).length *
        (2 * budget + 4 * (BinaryNatLists.encodeNatList xs).length + 18) +
        8 * budget + 20) + 1 := by
  induction queries with
  | nil => simp [runSteps]
  | cons query queries ih =>
      have tailFits : (queries.flatMap BinaryNatLists.encodeNat).length ≤ budget := by
        simp only [List.flatMap_cons, List.length_append] at fits
        omega
      have queryFits : (encodeNat query).length ≤ budget := by
        have size := BinaryNatLists.encodeNat_length query
        simp only [BinaryNatLists.natWireSize] at size
        simp only [List.flatMap_cons, List.length_append] at fits
        omega
      have countFits : (encodeNat (query :: queries).length).length ≤ budget :=
        (BinaryNatLists.encodeNat_length_le _).trans
          ((CertificateMembershipLoop.length_le_body_length _).trans fits)
      have entry := QueryMembershipStep.runSteps_le_bit_bound query xs
        (encodeNat (query :: queries).length)
      have product := Nat.mul_le_mul_left (BinaryNatLists.encodeNatList xs).length
        (show 2 * (encodeNat query).length + 4 * (BinaryNatLists.encodeNatList xs).length + 18 ≤
          2 * budget + 4 * (BinaryNatLists.encodeNatList xs).length + 18 by omega)
      have tailBound := ih tailFits
      simp only [List.length_cons] at entry countFits
      simp only [runSteps, List.length_cons, Nat.add_mul, Nat.one_mul]
      omega

/-- Polynomial TM2 runtime in framed query-body and full certificate bit lengths. -/
theorem runSteps_le_bit_bound (queries xs : List Nat) :
    runSteps xs queries ≤ (queries.flatMap BinaryNatLists.encodeNat).length *
      ((BinaryNatLists.encodeNatList xs).length *
        (2 * (queries.flatMap BinaryNatLists.encodeNat).length +
          4 * (BinaryNatLists.encodeNatList xs).length + 18) +
        8 * (queries.flatMap BinaryNatLists.encodeNat).length + 20) + 1 := by
  have bound := runSteps_le queries xs _ (Nat.le_refl _)
  have product := Nat.mul_le_mul_right
    ((BinaryNatLists.encodeNatList xs).length *
      (2 * (queries.flatMap BinaryNatLists.encodeNat).length +
        4 * (BinaryNatLists.encodeNatList xs).length + 18) +
      8 * (queries.flatMap BinaryNatLists.encodeNat).length + 20)
    (CertificateMembershipLoop.length_le_body_length queries)
  omega

/-- Bounded execution of the preloaded-count query-body traversal. -/
def evalsToInTime (queries xs : List Nat) (input output : List Bool) :
    EvalsToInTime computer.step
      (cfg (some .check) initialState (queries.flatMap BinaryNatLists.encodeNat ++ input)
        [] [] [] [] [] output (BinaryNatLists.encodeNatList xs) (encodeNat queries.length))
      (some (cfg (some .done) initialState input [] [] [] [] []
        (results queries xs ++ output) (BinaryNatLists.encodeNatList xs) []))
      ((queries.flatMap BinaryNatLists.encodeNat).length *
        ((BinaryNatLists.encodeNatList xs).length *
          (2 * (queries.flatMap BinaryNatLists.encodeNat).length +
            4 * (BinaryNatLists.encodeNatList xs).length + 18) +
          8 * (queries.flatMap BinaryNatLists.encodeNat).length + 20) + 1) where
  steps := runSteps xs queries
  evals_in_steps := whole_list queries xs input output
  steps_le_m := runSteps_le_bit_bound queries xs

/-- The machine emits exactly one bit for every query occurrence. -/
theorem results_length (queries xs : List Nat) :
    (results queries xs).length = queries.length := by
  simp [results]

end LeanNPHardness.MachinePrimitives.QueryMembershipLoop
