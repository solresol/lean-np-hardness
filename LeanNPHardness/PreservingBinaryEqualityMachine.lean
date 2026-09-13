import LeanNPHardness.BinaryEqualityMachine

/-!
# Binary equality with query restoration

This finite TM2 kernel compares two separately supplied Boolean words. During
comparison it saves each query bit on a scratch stack, then restores the query
in its original order. It consumes the candidate, empties scratch, and pushes
one Boolean result while preserving the output suffix. The exact runtime is
`max query.length candidate.length + query.length + 2` TM2 steps, including
both exhaustion transitions. Serialized input loading and certificate-list
traversal are separate obligations.
-/

namespace LeanNPHardness.MachinePrimitives.PreservingBinaryEquality

open Computability Turing

inductive Stack
  | query
  | candidate
  | scratch
  | output
  deriving DecidableEq, Fintype

inductive Label
  | scan
  | restore
  deriving DecidableEq, Fintype

abbrev State := BinaryEquality.State

def initialState : State := BinaryEquality.initialState

def Alphabet (_ : Stack) : Type := Bool

private def observeQuery (state : State) (symbol : Option Bool) : State :=
  { state with left := symbol }

private def observeCandidate (state : State) (symbol : Option Bool) : State :=
  { state with right := symbol, equal := state.equal && decide (state.left = symbol) }

/-- Copying a present query bit is part of the finite scan statement; the
restore loop contributes one additional TM2 step per query bit. -/
def program : Label → TM2.Stmt Alphabet Label State
  | .scan =>
      .pop .query observeQuery <|
        .pop .candidate observeCandidate <|
          .branch (fun state => state.left.isSome)
            (.push .scratch (fun state => state.left.getD false) <|
              .goto fun _ => .scan)
            (.branch (fun state => state.right.isSome)
              (.goto fun _ => .scan)
              (.goto fun _ => .restore))
  | .restore =>
      .pop .scratch observeQuery <|
        .branch (fun state => state.left.isSome)
          (.push .query (fun state => state.left.getD false) <|
            .goto fun _ => .restore)
          (.push .output (fun state => state.equal) <|
            .load (fun _ => initialState) .halt)

def computer : FinTM2 where
  K := Stack
  k₀ := .query
  k₁ := .output
  Γ := Alphabet
  Λ := Label
  main := .scan
  σ := State
  initialState := initialState
  Γk₀Fin := Bool.fintype
  m := program

def stackContents (query candidate scratch output : List Bool) :
    (index : Stack) → List (Alphabet index)
  | .query => query
  | .candidate => candidate
  | .scratch => scratch
  | .output => output

def cfg (label : Option Label) (state : State)
    (query candidate scratch output : List Bool) : computer.Cfg where
  l := label
  var := state
  stk := stackContents query candidate scratch output

private theorem scan_step_nil_nil (state : State) (scratch output : List Bool) :
    computer.step (cfg (some .scan) state [] [] scratch output) =
      some (cfg (some .restore) ⟨none, none, state.equal⟩ [] [] scratch output) := by
  rcases state with ⟨left, right, equal⟩
  simp [computer, FinTM2.step, cfg, program, stackContents, Alphabet,
    observeQuery, observeCandidate, Function.update]
  funext index
  cases index <;> rfl

private theorem scan_step_cons_nil (state : State) (bit : Bool)
    (query scratch output : List Bool) :
    computer.step (cfg (some .scan) state (bit :: query) [] scratch output) =
      some (cfg (some .scan) ⟨some bit, none, false⟩ query [] (bit :: scratch) output) := by
  rcases state with ⟨left, right, equal⟩
  simp [computer, FinTM2.step, cfg, program, stackContents, Alphabet,
    observeQuery, observeCandidate, Function.update]
  funext index
  cases index <;> rfl

private theorem scan_step_nil_cons (state : State) (bit : Bool)
    (candidate scratch output : List Bool) :
    computer.step (cfg (some .scan) state [] (bit :: candidate) scratch output) =
      some (cfg (some .scan) ⟨none, some bit, false⟩ [] candidate scratch output) := by
  rcases state with ⟨left, right, equal⟩
  simp [computer, FinTM2.step, cfg, program, stackContents, Alphabet,
    observeQuery, observeCandidate, Function.update]
  funext index
  cases index <;> rfl

private theorem scan_step_cons_cons (state : State) (a b : Bool)
    (query candidate scratch output : List Bool) :
    computer.step (cfg (some .scan) state (a :: query) (b :: candidate) scratch output) =
      some (cfg (some .scan) ⟨some a, some b, state.equal && decide (a = b)⟩
        query candidate (a :: scratch) output) := by
  rcases state with ⟨left, right, equal⟩
  simp [computer, FinTM2.step, cfg, program, stackContents, Alphabet,
    observeQuery, observeCandidate, Function.update]
  funext index
  cases index <;> rfl

/-- Exact scan invariant: the reversed query is saved above the supplied
scratch suffix, and the accumulated equality flag records the comparison. -/
theorem scan_run (query candidate scratch output : List Bool) (state : State) :
    (fun c => c.bind computer.step)^[max query.length candidate.length + 1]
        (some (cfg (some .scan) state query candidate scratch output)) =
      some (cfg (some .restore) ⟨none, none, state.equal && decide (query = candidate)⟩
        [] [] (query.reverse ++ scratch) output) := by
  induction query generalizing candidate scratch state with
  | nil =>
      induction candidate generalizing state with
      | nil =>
          simpa only [List.length_nil, Nat.zero_max, Nat.zero_add,
            Function.iterate_one, Option.bind_some, decide_true, Bool.and_true,
            List.reverse_nil, List.nil_append] using scan_step_nil_nil state scratch output
      | cons bit candidate ih =>
          simp only [List.length_nil, List.length_cons, Nat.zero_max]
          rw [Function.iterate_succ_apply, Option.bind_some, scan_step_nil_cons]
          simpa using ih ⟨none, some bit, false⟩
  | cons a query ih =>
      cases candidate with
      | nil =>
          simp only [List.length_nil, List.length_cons, Nat.max_zero]
          rw [Function.iterate_succ_apply, Option.bind_some, scan_step_cons_nil]
          simpa [List.reverse_cons, List.append_assoc] using
            ih [] (a :: scratch) ⟨some a, none, false⟩
      | cons b candidate =>
          simp only [List.length_cons, Nat.succ_max_succ]
          rw [Function.iterate_succ_apply, Option.bind_some, scan_step_cons_cons]
          simpa [Bool.and_assoc, List.reverse_cons, List.append_assoc] using
            ih candidate (a :: scratch) ⟨some a, some b, state.equal && decide (a = b)⟩

private theorem restore_step_nil (state : State) (query candidate output : List Bool) :
    computer.step (cfg (some .restore) state query candidate [] output) =
      some (cfg none initialState query candidate [] (state.equal :: output)) := by
  rcases state with ⟨left, right, equal⟩
  simp [computer, FinTM2.step, cfg, program, stackContents, Alphabet,
    observeQuery, Function.update]
  funext index
  cases index <;> rfl

private theorem restore_step_cons (state : State) (bit : Bool)
    (query candidate scratch output : List Bool) :
    computer.step (cfg (some .restore) state query candidate (bit :: scratch) output) =
      some (cfg (some .restore) ⟨some bit, state.right, state.equal⟩
        (bit :: query) candidate scratch output) := by
  rcases state with ⟨left, right, equal⟩
  simp [computer, FinTM2.step, cfg, program, stackContents, Alphabet,
    observeQuery, Function.update]
  funext index
  cases index <;> rfl

/-- Restore scratch in reverse order onto the query, retaining the candidate
and output suffix. The accumulated comparison is emitted exactly once. -/
theorem restore_run (query candidate scratch output : List Bool) (state : State) :
    (fun c => c.bind computer.step)^[scratch.length + 1]
        (some (cfg (some .restore) state query candidate scratch output)) =
      some (cfg none initialState (scratch.reverse ++ query) candidate []
        (state.equal :: output)) := by
  induction scratch generalizing query state with
  | nil =>
      simpa only [List.length_nil, Nat.zero_add, Function.iterate_one,
        Option.bind_some, List.reverse_nil, List.nil_append] using
        restore_step_nil state query candidate output
  | cons bit scratch ih =>
      simp only [List.length_cons]
      rw [Function.iterate_succ_apply, Option.bind_some, restore_step_cons]
      simpa [List.reverse_cons, List.append_assoc] using
        ih (bit :: query) ⟨some bit, state.right, state.equal⟩

/-- The complete kernel preserves the query's exact word and order, consumes
the candidate, empties scratch, and restores initial finite control. -/
theorem whole_list (query candidate output : List Bool) :
    (fun c => c.bind computer.step)^[max query.length candidate.length + query.length + 2]
        (some (cfg (some .scan) initialState query candidate [] output)) =
      some (cfg none initialState query [] [] (decide (query = candidate) :: output)) := by
  rw [show max query.length candidate.length + query.length + 2 =
      (query.length + 1) + (max query.length candidate.length + 1) by omega,
    Function.iterate_add_apply, scan_run]
  simpa [initialState, BinaryEquality.initialState] using
    restore_run [] [] query.reverse output ⟨none, none, decide (query = candidate)⟩

/-- Linear time in the actual supplied word lengths, with restoration counted. -/
def evalsToInTime (query candidate output : List Bool) :
    EvalsToInTime computer.step
      (cfg (some .scan) initialState query candidate [] output)
      (some (cfg none initialState query [] [] (decide (query = candidate) :: output)))
      (2 * query.length + candidate.length + 2) where
  steps := max query.length candidate.length + query.length + 2
  evals_in_steps := whole_list query candidate output
  steps_le_m := by omega

/-- Canonically encoded natural equality with the query encoding restored. -/
theorem natural_run (query candidate : Nat) (output : List Bool) :
    (fun c => c.bind computer.step)^[
        max (encodeNat query).length (encodeNat candidate).length +
          (encodeNat query).length + 2]
        (some (cfg (some .scan) initialState (encodeNat query) (encodeNat candidate) [] output)) =
      some (cfg none initialState (encodeNat query) [] [] (decide (query = candidate) :: output)) := by
  simpa only [BinaryEquality.encodeNat_eq_iff] using
    whole_list (encodeNat query) (encodeNat candidate) output

/-- The natural-number interface measures encoded bits, not numeric values. -/
def natural_evalsToInTime (query candidate : Nat) (output : List Bool) :
    EvalsToInTime computer.step
      (cfg (some .scan) initialState (encodeNat query) (encodeNat candidate) [] output)
      (some (cfg none initialState (encodeNat query) [] [] (decide (query = candidate) :: output)))
      (2 * (encodeNat query).length + (encodeNat candidate).length + 2) where
  steps := max (encodeNat query).length (encodeNat candidate).length +
    (encodeNat query).length + 2
  evals_in_steps := natural_run query candidate output
  steps_le_m := by omega

end LeanNPHardness.MachinePrimitives.PreservingBinaryEquality
