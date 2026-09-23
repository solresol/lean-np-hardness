import LeanNPHardness.CertificateMembershipStepMachine

/-!
# Count-controlled certificate membership traversal

A finite seven-stack TM2 dispatcher repeats the checked comparison, decrement,
and accumulation step until the retained canonical count is zero. Every entry
is consumed, even after a match, so repetitions and the unread suffix retain
their wire meaning. The query and output suffix survive; all work stacks empty.

The exact recursive cost counts one peek per iteration, one return jump per
entry, and a final peek. A separate bound uses query bits, framed body bits,
entry count, and the initial count's binary length. The count, query, and Boolean
accumulator are preloaded; header loading and a serialized verifier are separate.
Execution ends at a live `done` continuation before its halt.
-/

namespace LeanNPHardness.MachinePrimitives.CertificateMembershipLoop

open Computability Turing

abbrev Stack := CertificateCount.Stack
abbrev Alphabet := CertificateCount.Alphabet
abbrev State := CertificateMembershipStep.State
abbrev initialState := CertificateMembershipStep.initialState

inductive Label
  | check
  | entry (label : CertificateMembershipStep.Label)
  | done
  deriving DecidableEq, Fintype

/-- Reached component halts return to the count test in one counted step. -/
def liftStmt : TM2.Stmt Alphabet CertificateMembershipStep.Label State →
    TM2.Stmt Alphabet Label State
  | .push k write next => .push k write (liftStmt next)
  | .peek k read next => .peek k read (liftStmt next)
  | .pop k read next => .pop k read (liftStmt next)
  | .load update next => .load update (liftStmt next)
  | .branch test yes no => .branch test (liftStmt yes) (liftStmt no)
  | .goto next => .goto (fun state => .entry (next state))
  | .halt => .load (fun _ => initialState) (.goto fun _ => .check)

def program : Label → TM2.Stmt Alphabet Label State
  | .check =>
      .peek .remaining (fun state bit => (state.1, bit.isSome)) <|
        .branch (fun state => state.2)
          (.load (fun _ => initialState)
            (.goto fun _ => .entry CertificateMembershipStep.computer.main))
          (.load (fun _ => initialState) (.goto fun _ => .done))
  | .entry label => liftStmt (CertificateMembershipStep.program label)
  | .done => .halt

def computer : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .output
  Γ := Alphabet
  Λ := Label
  main := .check
  σ := State
  initialState := initialState
  Γk₀Fin := Bool.fintype
  m := program

def cfg (label : Option Label) (state : State)
    (input query remaining candidate scratch count output : List Bool) : computer.Cfg where
  l := label
  var := state
  stk := CertificateCount.stackContents input query remaining candidate scratch count output

def liftCfg (c : CertificateMembershipStep.computer.Cfg) : computer.Cfg where
  l := some (c.l.elim .check Label.entry)
  var := c.l.elim initialState (fun _ => c.var)
  stk := c.stk

/-- Component statements retain their exact cost and every stack. -/
theorem lift_stepAux (stmt : TM2.Stmt Alphabet CertificateMembershipStep.Label State)
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

private theorem lift_step (label : CertificateMembershipStep.Label) (state : State)
    (contents : (k : Stack) → List (Alphabet k)) :
    computer.step (liftCfg ⟨some label, state, contents⟩) =
      some (liftCfg (TM2.stepAux (CertificateMembershipStep.program label) state contents)) := by
  change some (TM2.stepAux (liftStmt (CertificateMembershipStep.program label)) state contents) = _
  rw [lift_stepAux]

private theorem iterate_bind_none {α : Type} (step : α → Option α) (n : Nat) :
    (fun c => c.bind step)^[n] none = none := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply]; exact ih

/-- Exact component execution lifts without additional dispatch overhead. -/
theorem lift_run (n : Nat) (start finish : CertificateMembershipStep.computer.Cfg)
    (run : (fun c => c.bind CertificateMembershipStep.computer.step)^[n]
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

/-- Peek tests presence, not the low bit, and preserves all stack contents. -/
theorem check_step (state : State)
    (input query remaining candidate scratch count output : List Bool) :
    computer.step (cfg (some .check) state input query remaining candidate scratch count output) =
      some (cfg (some (if remaining = [] then .done
        else .entry CertificateMembershipStep.computer.main)) initialState
        input query remaining candidate scratch count output) := by
  cases remaining <;>
    simp [computer, FinTM2.step, cfg, program, CertificateCount.stackContents, TM2.stepAux]

/-- The reached component continuation returns to the peek in one step. -/
theorem return_step (state : State)
    (input query remaining candidate scratch count output : List Bool) :
    computer.step (cfg (some (.entry .done)) state
      input query remaining candidate scratch count output) =
      some (cfg (some .check) initialState input query remaining candidate scratch count output) := rfl

/-- The component's exact cost is independent of the accumulator and suffixes. -/
def entrySteps (query head : Nat) (tail : List Nat) : Nat :=
  ((3 * (encodeNat head).length + max (encodeNat query).length (encodeNat head).length +
    (encodeNat query).length + 5) +
    ((binaryPred_outputsInTime (encodeNat (head :: tail).length)).steps +
      (2 * (binaryPredBits (encodeNat (head :: tail).length)).length + 2))) + 1

theorem entrySteps_le (query head : Nat) (tail : List Nat) :
    entrySteps query head tail ≤
      2 * (encodeNat query).length + 2 * BinaryNatLists.natWireSize head +
        4 * (encodeNat (head :: tail).length).length + 9 := by
  simpa only [BinaryNatLists.natWireSize, BinaryNatLists.frame_length] using
    (CertificateMembershipStep.evalsToInTime (encodeNat query) (encodeNat head) []
      (encodeNat (head :: tail).length) [] false).steps_le_m

/-- One complete entry, including its return jump, restores the tail count. -/
theorem entry_run (query head : Nat) (tail : List Nat) (input output : List Bool)
    (accumulated : Bool) :
    (fun c => c.bind computer.step)^[entrySteps query head tail + 1]
      (some (cfg (some (.entry CertificateMembershipStep.computer.main)) initialState
        ((head :: tail).flatMap BinaryNatLists.encodeNat ++ input)
        (encodeNat query) (encodeNat (head :: tail).length) [] [] [] (accumulated :: output))) =
      some (cfg (some .check) initialState (tail.flatMap BinaryNatLists.encodeNat ++ input)
        (encodeNat query) (encodeNat tail.length) [] [] []
        ((decide (query = head) || accumulated) :: output)) := by
  have run := lift_run _ _ _
    (CertificateMembershipStep.whole_frame (encodeNat query) (encodeNat head)
      (tail.flatMap BinaryNatLists.encodeNat ++ input) (encodeNat (head :: tail).length)
      output accumulated)
  rw [Function.iterate_succ_apply', show
    (fun c => c.bind computer.step)^[entrySteps query head tail]
      (some (cfg (some (.entry CertificateMembershipStep.computer.main)) initialState
        ((head :: tail).flatMap BinaryNatLists.encodeNat ++ input)
        (encodeNat query) (encodeNat (head :: tail).length) [] [] [] (accumulated :: output))) =
      some (cfg (some (.entry .done)) initialState (tail.flatMap BinaryNatLists.encodeNat ++ input)
        (encodeNat query) (encodeNat tail.length) [] [] []
        ((decide (query = head) || accumulated) :: output)) from by
          simpa only [entrySteps, BinaryNatLists.encodeNat, List.flatMap_cons, List.append_assoc,
            List.length_cons, Nat.pred_succ, BinaryEquality.encodeNat_eq_iff,
            binaryPredBits_encodeNat] using run,
    Option.bind_some, return_step]

/-- Exact runtime: one test per entry, one return per entry, and a final test. -/
def runSteps (query : Nat) : List Nat → Nat
  | [] => 1
  | head :: tail => (runSteps query tail + (entrySteps query head tail + 1)) + 1

/-- Accumulation agrees with list membership, retaining an earlier match. -/
theorem membership_cons (query head : Nat) (tail : List Nat) (accumulated : Bool) :
    (decide (query ∈ tail) || (decide (query = head) || accumulated)) =
      (decide (query ∈ head :: tail) || accumulated) := by
  by_cases h : query = head <;> by_cases ht : query ∈ tail <;>
    simp [List.mem_cons, h, ht]

/-- Traverse the complete canonical body, preserving query and arbitrary suffixes. -/
theorem whole_list (query : Nat) (xs : List Nat) (input output : List Bool) (accumulated : Bool) :
    (fun c => c.bind computer.step)^[runSteps query xs]
      (some (cfg (some .check) initialState (xs.flatMap BinaryNatLists.encodeNat ++ input)
        (encodeNat query) (encodeNat xs.length) [] [] [] (accumulated :: output))) =
      some (cfg (some .done) initialState input (encodeNat query) [] [] [] []
        ((decide (query ∈ xs) || accumulated) :: output)) := by
  induction xs generalizing accumulated with
  | nil =>
      rw [runSteps, Function.iterate_one, Option.bind_some, check_step]
      simp [encodeNat, encodeNum]
  | cons head tail ih =>
      rw [runSteps, Function.iterate_succ_apply, Option.bind_some, check_step]
      have nonempty : encodeNat (head :: tail).length ≠ [] := by
        intro empty
        have zero := (CertificateCount.encodeNat_eq_nil_iff (head :: tail).length).mp empty
        simp only [List.length_cons, Nat.succ_ne_zero] at zero
      rw [if_neg nonempty, Function.iterate_add_apply, entry_run query head tail input output accumulated,
        ih, membership_cons]

/-- Every remaining count uses no more bits than the initial count. -/
theorem count_bits_mono {m n : Nat} (h : m ≤ n) :
    (encodeNat m).length ≤ (encodeNat n).length := by
  simpa only [BinaryNatLists.encodeNat_length_eq_size] using Nat.size_le_size h

/-- Separate runtime bound in entry count, query bits, body bits, and count bits. -/
theorem runSteps_le (query : Nat) (xs : List Nat) :
    runSteps query xs ≤
      xs.length * (2 * (encodeNat query).length + 4 * (encodeNat xs.length).length + 11) +
        2 * (xs.flatMap BinaryNatLists.encodeNat).length + 1 := by
  induction xs with
  | nil => simp [runSteps]
  | cons head tail ih =>
      have entry := entrySteps_le query head tail
      have mono := count_bits_mono (Nat.le_succ tail.length)
      have mul := Nat.mul_le_mul_left tail.length
        (show 2 * (encodeNat query).length + 4 * (encodeNat tail.length).length + 11 ≤
          2 * (encodeNat query).length + 4 * (encodeNat (head :: tail).length).length + 11 by
            simpa only [List.length_cons] using Nat.add_le_add_right
              (Nat.add_le_add_left (Nat.mul_le_mul_left 4 mono) _) 11)
      simp only [runSteps, List.length_cons, List.flatMap_cons, List.length_append,
        BinaryNatLists.encodeNat_length, Nat.add_mul, Nat.one_mul] at *
      omega

/-- Checked TM2 runtime for the preloaded-count certificate-body loop. -/
def evalsToInTime (query : Nat) (xs : List Nat) (input output : List Bool) (accumulated : Bool) :
    EvalsToInTime computer.step
      (cfg (some .check) initialState (xs.flatMap BinaryNatLists.encodeNat ++ input)
        (encodeNat query) (encodeNat xs.length) [] [] [] (accumulated :: output))
      (some (cfg (some .done) initialState input (encodeNat query) [] [] [] []
        ((decide (query ∈ xs) || accumulated) :: output)))
      (xs.length * (2 * (encodeNat query).length + 4 * (encodeNat xs.length).length + 11) +
        2 * (xs.flatMap BinaryNatLists.encodeNat).length + 1) where
  steps := runSteps query xs
  evals_in_steps := whole_list query xs input output accumulated
  steps_le_m := runSteps_le query xs

/-- Every framed entry contributes at least one bit, including the natural zero. -/
theorem length_le_body_length (xs : List Nat) :
    xs.length ≤ (xs.flatMap BinaryNatLists.encodeNat).length := by
  induction xs with
  | nil => simp
  | cons head tail ih =>
      have positive := BinaryNatLists.natWireSize_pos head
      simp only [List.length_cons, List.flatMap_cons, List.length_append,
        BinaryNatLists.encodeNat_length]
      omega

/-- A polynomial bound solely in query bit length and framed body bit length. -/
theorem runSteps_le_bit_bound (query : Nat) (xs : List Nat) :
    runSteps query xs ≤
      (xs.flatMap BinaryNatLists.encodeNat).length *
        (2 * (encodeNat query).length + 4 * (xs.flatMap BinaryNatLists.encodeNat).length + 11) +
        2 * (xs.flatMap BinaryNatLists.encodeNat).length + 1 := by
  have entries := length_le_body_length xs
  have bits := (BinaryNatLists.encodeNat_length_le xs.length).trans entries
  have product := Nat.mul_le_mul entries
    (show 2 * (encodeNat query).length + 4 * (encodeNat xs.length).length + 11 ≤
      2 * (encodeNat query).length + 4 * (xs.flatMap BinaryNatLists.encodeNat).length + 11 by omega)
  have bound := runSteps_le query xs
  omega

/-- The returned Boolean is precisely membership or an already recorded match. -/
theorem result_eq_true_iff (query : Nat) (xs : List Nat) (accumulated : Bool) :
    (decide (query ∈ xs) || accumulated) = true ↔ query ∈ xs ∨ accumulated = true := by
  simp

end LeanNPHardness.MachinePrimitives.CertificateMembershipLoop
