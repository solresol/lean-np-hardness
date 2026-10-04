import LeanNPHardness.QueryMembershipMachine
import LeanNPHardness.CertificateDecrementMachine

/-!
# One reusable membership query and outer count decrement

A finite nine-stack TM2 dispatcher runs a framed membership lookup, then
saturated decrement of the independent outer query count. The decrement uses
the emptied candidate/scratch workspace and preserves the inner certificate
count, full backup, unread queries, and emitted membership result.

Exact execution includes one lookup-to-decrement transition. The bit bound is
`N * (2q + 4N + 18) + 4q + 4b + 18`, for raw query bits `q`, full framed
certificate bits `N`, and outer count bits `b`. The list-head interface restores
the exact tail count, retaining repeated queries and certificate entries.
The certificate and count are preloaded. `QueryMembershipLoopMachine` adds
count-controlled repeated execution. Header loading and the full SAT verifier
remain separate.
The final live decrement continuation's halt is excluded.
-/

namespace LeanNPHardness.MachinePrimitives.QueryMembershipStep

open Computability Turing

abbrev Stack := QueryMembership.Stack
abbrev Alphabet := QueryMembership.Alphabet
abbrev State := QueryMembership.State × CertificateDecrement.State

def initialState : State := (QueryMembership.initialState, CertificateDecrement.initialState)

inductive Label
  | lookup (label : QueryMembership.Label)
  | decrement (label : CertificateDecrement.Label)
  deriving DecidableEq, Fintype

/-- The decrement's source count is the outer count, independent of lookup's count. -/
def decrementStack : CertificateDecrement.Stack → Stack
  | .input => .lookup .input
  | .query => .lookup .query
  | .remaining => .outerRemaining
  | .candidate => .lookup .candidate
  | .scratch => .lookup .scratch
  | .count => .lookup .count
  | .output => .lookup .output

def decrementContents (remaining backup : List Bool)
    (contents : (k : CertificateDecrement.Stack) → List (CertificateDecrement.Alphabet k)) :
    (k : Stack) → List (Alphabet k)
  | .lookup .input => contents .input
  | .lookup .query => contents .query
  | .lookup .remaining => remaining
  | .lookup .candidate => contents .candidate
  | .lookup .scratch => contents .scratch
  | .lookup .count => contents .count
  | .lookup .output => contents .output
  | .lookup .backup => backup
  | .outerRemaining => contents .remaining

@[simp] private theorem decrementContents_apply (remaining backup : List Bool)
    (contents : (k : CertificateDecrement.Stack) → List (CertificateDecrement.Alphabet k))
    (k : CertificateDecrement.Stack) :
    decrementContents remaining backup contents (decrementStack k) = contents k := by
  cases k <;> rfl

private theorem decrementContents_update (remaining backup : List Bool)
    (contents : (k : CertificateDecrement.Stack) → List (CertificateDecrement.Alphabet k))
    (k : CertificateDecrement.Stack) (value : List Bool) :
    Function.update (decrementContents remaining backup contents) (decrementStack k) value =
      decrementContents remaining backup (Function.update contents k value) := by
  funext index
  cases index with
  | lookup index =>
      cases k <;> cases index <;> simp [Function.update, decrementContents, decrementStack]
  | outerRemaining =>
      cases k <;> simp [Function.update, decrementContents, decrementStack]

/-- Lookup statements retain their cost; a reached halt enters decrement. -/
def lookupStmt :
    TM2.Stmt QueryMembership.Alphabet QueryMembership.Label QueryMembership.State →
    TM2.Stmt Alphabet Label State
  | .push k write next => .push k (fun state => write state.1) (lookupStmt next)
  | .peek k read next =>
      .peek k
        (fun state bit => (read state.1 bit, CertificateDecrement.initialState)) (lookupStmt next)
  | .pop k read next =>
      .pop k
        (fun state bit => (read state.1 bit, CertificateDecrement.initialState)) (lookupStmt next)
  | .load update next =>
      .load (fun state => (update state.1, CertificateDecrement.initialState)) (lookupStmt next)
  | .branch test yes no => .branch (fun state => test state.1) (lookupStmt yes) (lookupStmt no)
  | .goto next => .goto (fun state => .lookup (next state.1))
  | .halt => .load (fun _ => initialState) (.goto fun _ => .decrement CertificateDecrement.computer.main)

/-- Decrement reuses lookup workspace and retains the backup and inner count. -/
def decrementStmt :
    TM2.Stmt CertificateDecrement.Alphabet CertificateDecrement.Label CertificateDecrement.State →
    TM2.Stmt Alphabet Label State
  | .push k write next => .push (decrementStack k) (fun state => write state.2) (decrementStmt next)
  | .peek k read next =>
      .peek (decrementStack k) (fun state bit => (QueryMembership.initialState, read state.2 bit))
        (decrementStmt next)
  | .pop k read next =>
      .pop (decrementStack k) (fun state bit => (QueryMembership.initialState, read state.2 bit))
        (decrementStmt next)
  | .load update next =>
      .load (fun state => (QueryMembership.initialState, update state.2)) (decrementStmt next)
  | .branch test yes no =>
      .branch (fun state => test state.2) (decrementStmt yes) (decrementStmt no)
  | .goto next => .goto (fun state => .decrement (next state.2))
  | .halt => .halt

def program : Label → TM2.Stmt Alphabet Label State
  | .lookup label => lookupStmt (QueryMembership.program label)
  | .decrement label => decrementStmt (CertificateDecrement.program label)

def computer : FinTM2 where
  K := Stack
  k₀ := .lookup .input
  k₁ := .lookup .output
  Γ := Alphabet
  Λ := Label
  main := .lookup (.query .prefix)
  σ := State
  initialState := initialState
  Γk₀Fin := Bool.fintype
  m := program

def cfg (label : Option Label) (state : State)
    (input query remaining candidate scratch count output backup outer : List Bool) : computer.Cfg where
  l := label
  var := state
  stk := (QueryMembership.cfg none QueryMembership.initialState
    input query remaining candidate scratch count output backup outer).stk

/-- A reached lookup halt becomes the live decrement entry with reset control. -/
def lookupCfg (c : QueryMembership.computer.Cfg) : computer.Cfg where
  l := some (c.l.elim (.decrement CertificateDecrement.computer.main) Label.lookup)
  var := c.l.elim initialState (fun _ => (c.var, CertificateDecrement.initialState))
  stk := c.stk

/-- Lookup statements have the same counted cost under dispatch. -/
theorem lookup_stepAux
    (stmt : TM2.Stmt QueryMembership.Alphabet QueryMembership.Label QueryMembership.State)
    (state : QueryMembership.State)
    (contents : (k : QueryMembership.Stack) → List (QueryMembership.Alphabet k)) :
    TM2.stepAux (lookupStmt stmt) (state, CertificateDecrement.initialState) contents =
      lookupCfg (TM2.stepAux stmt state contents) := by
  induction stmt generalizing state contents with
  | push k write next ih =>
      simp only [lookupStmt, TM2.stepAux]
      exact ih _ _
  | peek k read next ih =>
      simpa only [lookupStmt, TM2.stepAux] using
        ih (read state (contents k).head?) contents
  | pop k read next ih =>
      simp only [lookupStmt, TM2.stepAux]
      exact ih _ _
  | load update next ih =>
      simpa only [lookupStmt, TM2.stepAux] using ih (update state) contents
  | branch test yes no ihYes ihNo =>
      cases h : test state
      · simpa only [lookupStmt, TM2.stepAux, h, Bool.false_eq_true, cond_false] using
          ihNo state contents
      · simpa only [lookupStmt, TM2.stepAux, h, cond_true] using ihYes state contents
  | goto next => rfl
  | halt => rfl

private theorem lookup_step (label : QueryMembership.Label) (state : QueryMembership.State)
    (contents : (k : QueryMembership.Stack) → List (QueryMembership.Alphabet k)) :
    computer.step (lookupCfg ⟨some label, state, contents⟩) =
      some (lookupCfg (TM2.stepAux (QueryMembership.program label) state contents)) := by
  change some (TM2.stepAux (lookupStmt (QueryMembership.program label))
    (state, CertificateDecrement.initialState) contents) = _
  rw [lookup_stepAux]

private theorem iterate_bind_none {α : Type} (step : α → Option α) (n : Nat) :
    (fun c => c.bind step)^[n] none = none := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply]; exact ih

/-- Any exact lookup run lifts with the same step count. -/
theorem lookup_run (n : Nat) (start finish : QueryMembership.computer.Cfg)
    (run : (fun c => c.bind QueryMembership.computer.step)^[n] (some start) = some finish) :
    (fun c => c.bind computer.step)^[n] (some (lookupCfg start)) =
      some (lookupCfg finish) := by
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
          rw [Option.bind_some, lookup_step]
          exact ih _ run

def decrementCfg (remaining backup : List Bool) (c : CertificateDecrement.computer.Cfg) :
    computer.Cfg where
  l := c.l.map Label.decrement
  var := (QueryMembership.initialState, c.var)
  stk := decrementContents remaining backup c.stk

/-- Decrement statements have the same effect and counted cost under dispatch. -/
theorem decrement_stepAux
    (stmt : TM2.Stmt CertificateDecrement.Alphabet CertificateDecrement.Label CertificateDecrement.State)
    (state : CertificateDecrement.State)
    (contents : (k : CertificateDecrement.Stack) → List (CertificateDecrement.Alphabet k))
    (remaining backup : List Bool) :
    TM2.stepAux (decrementStmt stmt) (QueryMembership.initialState, state)
        (decrementContents remaining backup contents) =
      decrementCfg remaining backup (TM2.stepAux stmt state contents) := by
  induction stmt generalizing state contents with
  | push k write next ih =>
      simp only [decrementStmt, TM2.stepAux, decrementContents_apply]
      rw [decrementContents_update]
      exact ih _ _
  | peek k read next ih => simpa only [decrementStmt, TM2.stepAux, decrementContents_apply] using ih _ _
  | pop k read next ih =>
      simp only [decrementStmt, TM2.stepAux, decrementContents_apply]
      rw [decrementContents_update]
      exact ih _ _
  | load update next ih => simpa only [decrementStmt, TM2.stepAux] using ih _ _
  | branch test yes no ihYes ihNo =>
      cases h : test state
      · simpa only [decrementStmt, TM2.stepAux, h, Bool.false_eq_true, cond_false] using
          ihNo state contents
      · simpa only [decrementStmt, TM2.stepAux, h, cond_true] using ihYes state contents
  | goto next => rfl
  | halt => rfl

private theorem decrement_step (label : CertificateDecrement.Label)
    (state : CertificateDecrement.State)
    (contents : (k : CertificateDecrement.Stack) → List (CertificateDecrement.Alphabet k))
    (remaining backup : List Bool) :
    computer.step (decrementCfg remaining backup ⟨some label, state, contents⟩) =
      some (decrementCfg remaining backup (TM2.stepAux (CertificateDecrement.program label) state contents)) := by
  change some (TM2.stepAux (decrementStmt (CertificateDecrement.program label))
    (QueryMembership.initialState, state) (decrementContents remaining backup contents)) = _
  rw [decrement_stepAux]

/-- Any exact decrement run lifts with the same step count. -/
theorem decrement_run (n : Nat) (start finish : CertificateDecrement.computer.Cfg)
    (remaining backup : List Bool)
    (run : (fun c => c.bind CertificateDecrement.computer.step)^[n]
      (some start) = some finish) :
    (fun c => c.bind computer.step)^[n] (some (decrementCfg remaining backup start)) =
      some (decrementCfg remaining backup finish) := by
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

/-- One lookup leaves its result and all retained data at the live lookup endpoint. -/
theorem lookup_whole_query (query : Nat) (xs : List Nat) (input output outer : List Bool) :
    (fun c => c.bind computer.step)^[QueryMembership.runSteps query xs]
      (some (cfg (some (.lookup (.query .prefix))) initialState
        (BinaryNatLists.encodeNat query ++ input) [] [] [] [] [] output
        (BinaryNatLists.encodeNatList xs) outer)) =
      some (cfg (some (.lookup .done)) initialState
        input [] [] [] [] [] (decide (query ∈ xs) :: output)
        (BinaryNatLists.encodeNatList xs) outer) := by
  exact lookup_run _ _ _ (QueryMembership.whole_query query xs input output outer)

/-- The lookup endpoint enters decrement in one further counted step. -/
theorem decrement_entry_step (state : State)
    (input query remaining candidate scratch count output backup outer : List Bool) :
    computer.step (cfg (some (.lookup .done)) state
      input query remaining candidate scratch count output backup outer) =
      some (cfg (some (.decrement CertificateDecrement.computer.main)) initialState
        input query remaining candidate scratch count output backup outer) := by
  rfl

/-- Identify the embedded decrement layout with the shared named configuration. -/
private theorem decrementCfg_cfg (label : Option CertificateDecrement.Label)
    (state : CertificateDecrement.State)
    (input query outer candidate scratch count output remaining backup : List Bool) :
    decrementCfg remaining backup
      (CertificateDecrement.cfg label state input query outer candidate scratch count output) =
      cfg (label.map Label.decrement) (QueryMembership.initialState, state)
        input query remaining candidate scratch count output backup outer := by
  unfold decrementCfg cfg CertificateDecrement.cfg
  congr 1
  funext index
  cases index with
  | lookup index => cases index <;> rfl
  | outerRemaining => rfl

/-- Outer decrement preserves arbitrary inner count, backup, and traversal data. -/
theorem decrement_whole_word (outer input query remaining count output backup : List Bool) :
    (fun c => c.bind computer.step)^[(binaryPred_outputsInTime outer).steps +
        (2 * (binaryPredBits outer).length + 2)]
      (some (cfg (some (.decrement CertificateDecrement.computer.main)) initialState
        input query remaining [] [] count output backup outer)) =
      some (cfg (some (.decrement (.transfer .done))) initialState
        input query remaining [] [] count output backup (binaryPredBits outer)) := by
  simpa only [decrementCfg_cfg, Option.map_some, initialState] using
    decrement_run _ _ _ remaining backup
      (CertificateDecrement.whole_word outer input query count output)

/-- Exact lookup cost plus one entry step and the exact in-place decrement cost. -/
def runSteps (query : Nat) (xs : List Nat) (outer : List Bool) : Nat :=
  QueryMembership.runSteps query xs +
    (((binaryPred_outputsInTime outer).steps + (2 * (binaryPredBits outer).length + 2)) + 1)

/-- Framed lookup followed by saturated outer decrement, retaining backup and suffixes. -/
theorem whole_query (query : Nat) (xs : List Nat) (input output outer : List Bool) :
    (fun c => c.bind computer.step)^[runSteps query xs outer]
      (some (cfg (some (.lookup (.query .prefix))) initialState
        (BinaryNatLists.encodeNat query ++ input) [] [] [] [] [] output
        (BinaryNatLists.encodeNatList xs) outer)) =
      some (cfg (some (.decrement (.transfer .done))) initialState
        input [] [] [] [] [] (decide (query ∈ xs) :: output)
        (BinaryNatLists.encodeNatList xs) (binaryPredBits outer)) := by
  rw [runSteps, Nat.add_comm, Function.iterate_add_apply, lookup_whole_query,
    Function.iterate_succ_apply, Option.bind_some, decrement_entry_step]
  exact decrement_whole_word _ _ _ _ _ _ _

/-- One query-list head is consumed and the exact tail count is restored.
All unread query frames and repeated occurrences remain in their original order. -/
theorem list_head (query : Nat) (queries xs : List Nat) (input output : List Bool) :
    (fun c => c.bind computer.step)^[runSteps query xs (encodeNat (query :: queries).length)]
      (some (cfg (some (.lookup (.query .prefix))) initialState
        ((query :: queries).flatMap BinaryNatLists.encodeNat ++ input) [] [] [] [] [] output
        (BinaryNatLists.encodeNatList xs) (encodeNat (query :: queries).length))) =
      some (cfg (some (.decrement (.transfer .done))) initialState
        (queries.flatMap BinaryNatLists.encodeNat ++ input) [] [] [] [] []
        (decide (query ∈ xs) :: output)
        (BinaryNatLists.encodeNatList xs) (encodeNat queries.length)) := by
  simpa only [List.flatMap_cons, List.append_assoc, binaryPredBits_encodeNat,
    List.length_cons, Nat.pred_succ] using
    whole_query query xs (queries.flatMap BinaryNatLists.encodeNat ++ input) output
      (encodeNat (query :: queries).length)

/-- Polynomial bound in raw query, full framed certificate, and outer count bits. -/
theorem runSteps_le_bit_bound (query : Nat) (xs : List Nat) (outer : List Bool) :
    runSteps query xs outer ≤ (BinaryNatLists.encodeNatList xs).length *
      (2 * (encodeNat query).length + 4 * (BinaryNatLists.encodeNatList xs).length + 18) +
      4 * (encodeNat query).length + 4 * outer.length + 18 := by
  have := QueryMembership.runSteps_le_bit_bound query xs
  have := (binaryPred_outputsInTime outer).steps_le_m
  have := binaryPredBits_length_le outer
  unfold runSteps
  omega

/-- Bounded execution of one framed membership query and outer decrement. -/
def evalsToInTime (query : Nat) (xs : List Nat) (input output outer : List Bool) :
    EvalsToInTime computer.step
      (cfg (some (.lookup (.query .prefix))) initialState
        (BinaryNatLists.encodeNat query ++ input) [] [] [] [] [] output
        (BinaryNatLists.encodeNatList xs) outer)
      (some (cfg (some (.decrement (.transfer .done))) initialState
        input [] [] [] [] [] (decide (query ∈ xs) :: output)
        (BinaryNatLists.encodeNatList xs) (binaryPredBits outer)))
      ((BinaryNatLists.encodeNatList xs).length *
        (2 * (encodeNat query).length + 4 * (BinaryNatLists.encodeNatList xs).length + 18) +
        4 * (encodeNat query).length + 4 * outer.length + 18) where
  steps := runSteps query xs outer
  evals_in_steps := whole_query query xs input output outer
  steps_le_m := runSteps_le_bit_bound query xs outer

/-- Bounded nonempty query-body execution restores the count of the unread tail. -/
def list_head_evalsToInTime (query : Nat) (queries xs : List Nat) (input output : List Bool) :
    EvalsToInTime computer.step
      (cfg (some (.lookup (.query .prefix))) initialState
        ((query :: queries).flatMap BinaryNatLists.encodeNat ++ input) [] [] [] [] [] output
        (BinaryNatLists.encodeNatList xs) (encodeNat (query :: queries).length))
      (some (cfg (some (.decrement (.transfer .done))) initialState
        (queries.flatMap BinaryNatLists.encodeNat ++ input) [] [] [] [] []
        (decide (query ∈ xs) :: output)
        (BinaryNatLists.encodeNatList xs) (encodeNat queries.length)))
      ((BinaryNatLists.encodeNatList xs).length *
        (2 * (encodeNat query).length + 4 * (BinaryNatLists.encodeNatList xs).length + 18) +
        4 * (encodeNat query).length + 4 * (encodeNat (query :: queries).length).length + 18) where
  steps := runSteps query xs (encodeNat (query :: queries).length)
  evals_in_steps := list_head query queries xs input output
  steps_le_m := runSteps_le_bit_bound query xs (encodeNat (query :: queries).length)

end LeanNPHardness.MachinePrimitives.QueryMembershipStep
