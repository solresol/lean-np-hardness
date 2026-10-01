import LeanNPHardness.PreservingMembershipMachine

/-!
# Framed membership with a reusable certificate

This finite eight-stack TM2 dispatcher extracts one framed query, runs
certificate-preserving membership, and drains the query. It leaves the complete
certificate on `backup`, preserves arbitrary unread input and output suffixes,
and empties query/count/work stacks at a live `done` continuation. Thus a caller
can start another lookup without restoring the certificate or clearing scratch.

Exact execution and the polynomial bit bound are separate from Boolean
membership semantics. The certificate must already occupy `backup`; inputs
must be canonical complete encodings. Backup loading, repeated-query dispatch,
malformed-input rejection, and the full SAT verifier remain separate obligations.
-/

namespace LeanNPHardness.MachinePrimitives.ReusableMembership

open Computability Turing

abbrev Stack := PreservingMembership.Stack
abbrev Alphabet := PreservingMembership.Alphabet
abbrev State := FrameExtraction.State × PreservingMembership.State

def initialState : State := (none, PreservingMembership.initialState)

inductive Label
  | query (label : FrameExtraction.Label)
  | membership (label : PreservingMembership.Label)
  | cleanup
  | done
  deriving DecidableEq, Fintype

/-- The extracted payload becomes the query; the old query slot protects the count. -/
def queryStack : FrameExtraction.Stack → Stack
  | .input => .input
  | .query => .remaining
  | .candidate => .query
  | .scratch => .scratch
  | .count => .count

def queryContents (candidate output backup : List Bool)
    (contents : (k : FrameExtraction.Stack) → List (FrameExtraction.Alphabet k)) :
    (k : Stack) → List (Alphabet k)
  | .input => contents .input
  | .query => contents .candidate
  | .remaining => contents .query
  | .candidate => candidate
  | .scratch => contents .scratch
  | .count => contents .count
  | .output => output
  | .backup => backup

@[simp] private theorem queryContents_apply (candidate output backup : List Bool)
    (contents : (k : FrameExtraction.Stack) → List (FrameExtraction.Alphabet k))
    (k : FrameExtraction.Stack) :
    queryContents candidate output backup contents (queryStack k) = contents k := by
  cases k <;> rfl

private theorem queryContents_update (candidate output backup : List Bool)
    (contents : (k : FrameExtraction.Stack) → List (FrameExtraction.Alphabet k))
    (k : FrameExtraction.Stack) (value : List Bool) :
    Function.update (queryContents candidate output backup contents) (queryStack k) value =
      queryContents candidate output backup (Function.update contents k value) := by
  funext index
  cases k <;> cases index <;>
    simp [Function.update, queryContents, queryStack]

/-- Query extraction enters certificate copying in its final counted step. -/
def queryStmt : TM2.Stmt FrameExtraction.Alphabet FrameExtraction.Label FrameExtraction.State →
    TM2.Stmt Alphabet Label State
  | .push k write next => .push (queryStack k) (fun state => write state.1) (queryStmt next)
  | .peek k read next => .peek (queryStack k)
      (fun state bit => (read state.1 bit, PreservingMembership.initialState)) (queryStmt next)
  | .pop k read next => .pop (queryStack k)
      (fun state bit => (read state.1 bit, PreservingMembership.initialState)) (queryStmt next)
  | .load update next =>
      .load (fun state => (update state.1, PreservingMembership.initialState)) (queryStmt next)
  | .branch test yes no => .branch (fun state => test state.1) (queryStmt yes) (queryStmt no)
  | .goto next => .goto (fun state => .query (next state.1))
  | .halt => .load (fun _ => initialState) (.goto fun _ => .membership (.copy .reverse))

/-- Membership control retains its exact costs and redirects halt to cleanup. -/
def membershipStmt : TM2.Stmt Alphabet PreservingMembership.Label PreservingMembership.State →
    TM2.Stmt Alphabet Label State
  | .push k write next => .push k (fun state => write state.2) (membershipStmt next)
  | .peek k read next => .peek k (fun state bit => (none, read state.2 bit)) (membershipStmt next)
  | .pop k read next => .pop k (fun state bit => (none, read state.2 bit)) (membershipStmt next)
  | .load update next => .load (fun state => (none, update state.2)) (membershipStmt next)
  | .branch test yes no => .branch (fun state => test state.2) (membershipStmt yes) (membershipStmt no)
  | .goto next => .goto (fun state => .membership (next state.2))
  | .halt => .goto (fun _ => .cleanup)

def program : Label → TM2.Stmt Alphabet Label State
  | .query label => queryStmt (FrameExtraction.program label)
  | .membership label => membershipStmt (PreservingMembership.program label)
  | .cleanup => .pop .query (fun _ bit => (bit, PreservingMembership.initialState))
      (.branch (fun state => state.1.isSome)
        (.goto fun _ => .cleanup)
        (.load (fun _ => initialState) (.goto fun _ => .done)))
  | .done => .halt

def computer : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .output
  Γ := Alphabet
  Λ := Label
  main := .query .prefix
  σ := State
  initialState := initialState
  Γk₀Fin := Bool.fintype
  m := program

def cfg (label : Option Label) (state : State)
    (input query remaining candidate scratch count output backup : List Bool) : computer.Cfg where
  l := label
  var := state
  stk := PreservingMembership.membershipContents backup
    (CertificateCount.stackContents input query remaining candidate scratch count output)

def queryCfg (candidate output backup : List Bool) (c : FrameExtraction.computer.Cfg) : computer.Cfg where
  l := some (c.l.elim (.membership (.copy .reverse)) Label.query)
  var := c.l.elim initialState (fun _ => (c.var, PreservingMembership.initialState))
  stk := queryContents candidate output backup c.stk

def membershipCfg (c : PreservingMembership.computer.Cfg) : computer.Cfg where
  l := some (c.l.elim .cleanup Label.membership)
  var := (none, c.var)
  stk := c.stk

/-- Extractor statements preserve private stacks and enter membership at halt. -/
theorem query_stepAux
    (stmt : TM2.Stmt FrameExtraction.Alphabet FrameExtraction.Label FrameExtraction.State)
    (state : FrameExtraction.State)
    (contents : (k : FrameExtraction.Stack) → List (FrameExtraction.Alphabet k))
    (candidate output backup : List Bool) :
    TM2.stepAux (queryStmt stmt) (state, PreservingMembership.initialState)
      (queryContents candidate output backup contents) =
      queryCfg candidate output backup (TM2.stepAux stmt state contents) := by
  induction stmt generalizing state contents with
  | push k write next ih =>
      simp only [queryStmt, TM2.stepAux, queryContents_apply]
      rw [queryContents_update]
      exact ih _ _
  | peek k read next ih =>
      simpa only [queryStmt, TM2.stepAux, queryContents_apply] using ih _ _
  | pop k read next ih =>
      simp only [queryStmt, TM2.stepAux, queryContents_apply]
      rw [queryContents_update]
      exact ih _ _
  | load update next ih => simpa only [queryStmt, TM2.stepAux] using ih _ _
  | branch test yes no ihYes ihNo =>
      cases h : test state
      · simpa only [queryStmt, TM2.stepAux, h, Bool.false_eq_true, cond_false] using ihNo state contents
      · simpa only [queryStmt, TM2.stepAux, h, cond_true] using ihYes state contents
  | goto next => rfl
  | halt => rfl

/-- The membership one-step simulation preserves its exact cost. -/
theorem membership_stepAux
    (stmt : TM2.Stmt Alphabet PreservingMembership.Label PreservingMembership.State)
    (state : PreservingMembership.State) (contents : (k : Stack) → List (Alphabet k)) :
    TM2.stepAux (membershipStmt stmt) (none, state) contents =
      membershipCfg (TM2.stepAux stmt state contents) := by
  induction stmt generalizing state contents with
  | push k write next ih => simpa only [membershipStmt, TM2.stepAux] using ih _ _
  | peek k read next ih => simpa only [membershipStmt, TM2.stepAux] using ih _ _
  | pop k read next ih => simpa only [membershipStmt, TM2.stepAux] using ih _ _
  | load update next ih => simpa only [membershipStmt, TM2.stepAux] using ih _ _
  | branch test yes no ihYes ihNo =>
      cases h : test state
      · simpa only [membershipStmt, TM2.stepAux, h, Bool.false_eq_true, cond_false] using ihNo state contents
      · simpa only [membershipStmt, TM2.stepAux, h, cond_true] using ihYes state contents
  | goto next => rfl
  | halt => rfl

private theorem query_step (label : FrameExtraction.Label) (state : FrameExtraction.State)
    (contents : (k : FrameExtraction.Stack) → List (FrameExtraction.Alphabet k))
    (candidate output backup : List Bool) :
    computer.step (queryCfg candidate output backup ⟨some label, state, contents⟩) =
      some (queryCfg candidate output backup (TM2.stepAux (FrameExtraction.program label) state contents)) := by
  change some (TM2.stepAux (queryStmt (FrameExtraction.program label))
    (state, PreservingMembership.initialState) (queryContents candidate output backup contents)) = _
  rw [query_stepAux]

private theorem membership_step (label : PreservingMembership.Label)
    (state : PreservingMembership.State) (contents : (k : Stack) → List (Alphabet k)) :
    computer.step (membershipCfg ⟨some label, state, contents⟩) =
      some (membershipCfg (TM2.stepAux (PreservingMembership.program label) state contents)) := by
  change some (TM2.stepAux (membershipStmt (PreservingMembership.program label)) (none, state) contents) = _
  rw [membership_stepAux]

private theorem iterate_bind_none {α : Type} (step : α → Option α) (n : Nat) :
    (fun c => c.bind step)^[n] none = none := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply]; exact ih

/-- Exact extraction execution enters copying in its final step. -/
theorem query_run (n : Nat) (start finish : FrameExtraction.computer.Cfg)
    (candidate output backup : List Bool)
    (run : (fun c => c.bind FrameExtraction.computer.step)^[n] (some start) = some finish) :
    (fun c => c.bind computer.step)^[n] (some (queryCfg candidate output backup start)) =
      some (queryCfg candidate output backup finish) := by
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
          rw [Option.bind_some, query_step]
          exact ih _ run

/-- Exact membership execution lifts without additional dispatch steps. -/
theorem membership_run (n : Nat) (start finish : PreservingMembership.computer.Cfg)
    (run : (fun c => c.bind PreservingMembership.computer.step)^[n]
      (some start) = some finish) :
    (fun c => c.bind computer.step)^[n] (some (membershipCfg start)) = some (membershipCfg finish) := by
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

/-- Extract a complete query frame in order, retaining every other data stack. -/
theorem query_whole_frame (bits input remaining candidate output backup : List Bool) :
    (fun c => c.bind computer.step)^[3 * bits.length + 3]
      (some (cfg (some (.query .prefix)) initialState
        (BinaryNatLists.frame bits ++ input) [] remaining candidate [] [] output backup)) =
      some (cfg (some (.membership (.copy .reverse))) initialState
        input bits remaining candidate [] [] output backup) := by
  have run := query_run _ _ _ candidate output backup
    (FrameExtraction.whole_frame bits input remaining [])
  simpa only [List.append_nil] using run

/-- The live membership continuation enters cleanup in one counted step. -/
theorem cleanup_entry_step (state : State)
    (input query remaining candidate scratch count output backup : List Bool) :
    computer.step
      (cfg (some (.membership (.membership (.loop .done)))) state
        input query remaining candidate scratch count output backup) =
      some (cfg (some .cleanup) state
        input query remaining candidate scratch count output backup) := by
  rfl

private theorem cleanup_step_cons (state : State) (bit : Bool)
    (input query remaining candidate scratch count output backup : List Bool) :
    computer.step (cfg (some .cleanup) state
      input (bit :: query) remaining candidate scratch count output backup) =
      some (cfg (some .cleanup) (some bit, PreservingMembership.initialState)
        input query remaining candidate scratch count output backup) := by
  simp [computer, FinTM2.step, cfg, program, PreservingMembership.membershipContents, CertificateCount.stackContents]
  funext index
  cases index <;> simp [Function.update, PreservingMembership.membershipContents, CertificateCount.stackContents]

private theorem cleanup_step_nil (state : State)
    (input remaining candidate scratch count output backup : List Bool) :
    computer.step (cfg (some .cleanup) state
      input [] remaining candidate scratch count output backup) =
      some (cfg (some .done) initialState input [] remaining candidate scratch count output backup) := by
  simp [computer, FinTM2.step, cfg, program, PreservingMembership.membershipContents, CertificateCount.stackContents]

/-- Query cleanup takes exactly one step per bit plus the final empty-stack transition.
All seven other stacks are preserved, even when they are nonempty. -/
theorem cleanup_run (state : State)
    (input query remaining candidate scratch count output backup : List Bool) :
    (fun c => c.bind computer.step)^[query.length + 1]
      (some (cfg (some .cleanup) state
        input query remaining candidate scratch count output backup)) =
      some (cfg (some .done) initialState input [] remaining candidate scratch count output backup) := by
  induction query generalizing state with
  | nil =>
      simpa only [List.length_nil, Nat.zero_add, Function.iterate_one, Option.bind_some] using
        cleanup_step_nil state input remaining candidate scratch count output backup
  | cons bit query ih =>
      rw [List.length_cons, Nat.add_right_comm, Function.iterate_succ_apply,
        Option.bind_some, cleanup_step_cons]
      exact ih _

/-- Exact query extraction, preserved-certificate lookup, entry, and cleanup costs. -/
def runSteps (query : Nat) (xs : List Nat) : Nat :=
  (3 * (encodeNat query).length + 3) +
    (PreservingMembership.runSteps query xs + ((encodeNat query).length + 2))

/-- One framed lookup clears query/work stacks and retains the certificate and suffixes. -/
theorem whole_query (query : Nat) (xs : List Nat) (input output : List Bool) :
    (fun c => c.bind computer.step)^[runSteps query xs]
      (some (cfg (some (.query .prefix)) initialState
        (BinaryNatLists.encodeNat query ++ input) [] [] [] [] [] output
        (BinaryNatLists.encodeNatList xs))) =
      some (cfg (some .done) initialState
        input [] [] [] [] [] (decide (query ∈ xs) :: output)
        (BinaryNatLists.encodeNatList xs)) := by
  rw [runSteps, Nat.add_comm, Function.iterate_add_apply]
  simp only [BinaryNatLists.encodeNat]
  rw [query_whole_frame, Nat.add_comm, Function.iterate_add_apply]
  have run := membership_run _ _ _ (PreservingMembership.whole_list query xs input output)
  rw [show cfg (some (.membership (.copy .reverse))) initialState
      input (encodeNat query) [] [] [] [] output (BinaryNatLists.encodeNatList xs) =
      membershipCfg (PreservingMembership.cfg (some (.copy .reverse))
        PreservingMembership.initialState input (encodeNat query) [] [] [] [] output
        (BinaryNatLists.encodeNatList xs)) from rfl, run]
  rw [show (encodeNat query).length + 2 = ((encodeNat query).length + 1) + 1 by omega,
    Function.iterate_succ_apply, Option.bind_some]
  change (fun c => c.bind computer.step)^[List.length (encodeNat query) + 1]
    (computer.step (cfg (some (.membership (.membership (.loop .done)))) initialState
      input (encodeNat query) [] [] [] [] (decide (query ∈ xs) :: output)
      (BinaryNatLists.encodeNatList xs))) = _
  rw [cleanup_entry_step]
  exact cleanup_run _ _ _ _ _ _ _ _ _

/-- Polynomial bound in raw query bits and complete framed certificate bits.
The final live continuation's halt is excluded. -/
theorem runSteps_le_bit_bound (query : Nat) (xs : List Nat) :
    runSteps query xs ≤ (BinaryNatLists.encodeNatList xs).length *
      (2 * (encodeNat query).length + 4 * (BinaryNatLists.encodeNatList xs).length + 18) +
      4 * (encodeNat query).length + 12 := by
  have bound := PreservingMembership.runSteps_le_bit_bound query xs
  unfold runSteps
  omega

/-- Bounded execution from a framed query, leaving the lookup workspace reusable. -/
def evalsToInTime (query : Nat) (xs : List Nat) (input output : List Bool) :
    EvalsToInTime computer.step
      (cfg (some (.query .prefix)) initialState
        (BinaryNatLists.encodeNat query ++ input) [] [] [] [] [] output
        (BinaryNatLists.encodeNatList xs))
      (some (cfg (some .done) initialState
        input [] [] [] [] [] (decide (query ∈ xs) :: output)
        (BinaryNatLists.encodeNatList xs)))
      ((BinaryNatLists.encodeNatList xs).length *
        (2 * (encodeNat query).length + 4 * (BinaryNatLists.encodeNatList xs).length + 18) +
        4 * (encodeNat query).length + 12) where
  steps := runSteps query xs
  evals_in_steps := whole_query query xs input output
  steps_le_m := runSteps_le_bit_bound query xs

/-- Boolean meaning of the output, independently of loading and cleanup. -/
theorem result_eq_true_iff (query : Nat) (xs : List Nat) :
    decide (query ∈ xs) = true ↔ query ∈ xs := by simp

end LeanNPHardness.MachinePrimitives.ReusableMembership
