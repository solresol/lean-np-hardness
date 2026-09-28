import LeanNPHardness.CertificateMembershipMachine

/-!
# Membership from a serialized query and certificate

A finite seven-stack TM2 dispatcher extracts a leading framed natural onto
`query` and enters the checked certificate-membership machine. Both phases
retain their exact costs. Starting with empty query/work stacks, it consumes
`BinaryNatLists.encodeNat query ++ BinaryNatLists.encodeNatList xs`, preserves
arbitrary input/output suffixes, and emits the membership bit. Repeated entries
are consumed unchanged. The loaded query remains available after traversal.

The runtime bound uses the complete serialized input's bit length. Execution
ends at a live continuation before its halt. Canonical complete encodings are
assumed. `CanonicalMembershipMachine` supplies query cleanup and canonical
halting output; `MembershipComputable` supplies function-level packaging.
Malformed-input rejection and the full SAT verifier remain separate obligations.
-/

namespace LeanNPHardness.MachinePrimitives.SerializedMembership

open Computability Turing

abbrev Stack := CertificateCount.Stack
abbrev Alphabet := CertificateCount.Alphabet
abbrev State := FrameExtraction.State × CertificateMembership.State

def initialState : State := (none, CertificateMembership.initialState)

inductive Label
  | query (label : FrameExtraction.Label)
  | membership (label : CertificateMembership.Label)
  deriving DecidableEq, Fintype

/-- The extracted payload becomes the query; the old query slot protects the count. -/
def queryStack : FrameExtraction.Stack → Stack
  | .input => .input
  | .query => .remaining
  | .candidate => .query
  | .scratch => .scratch
  | .count => .count

def queryContents (candidate output : List Bool)
    (contents : (k : FrameExtraction.Stack) → List (FrameExtraction.Alphabet k)) :
    (k : Stack) → List (Alphabet k)
  | .input => contents .input
  | .query => contents .candidate
  | .remaining => contents .query
  | .candidate => candidate
  | .scratch => contents .scratch
  | .count => contents .count
  | .output => output

@[simp] private theorem queryContents_apply (candidate output : List Bool)
    (contents : (k : FrameExtraction.Stack) → List (FrameExtraction.Alphabet k))
    (k : FrameExtraction.Stack) :
    queryContents candidate output contents (queryStack k) = contents k := by
  cases k <;> rfl

private theorem queryContents_update (candidate output : List Bool)
    (contents : (k : FrameExtraction.Stack) → List (FrameExtraction.Alphabet k))
    (k : FrameExtraction.Stack) (value : List Bool) :
    Function.update (queryContents candidate output contents) (queryStack k) value =
      queryContents candidate output (Function.update contents k value) := by
  funext index
  cases k <;> cases index <;>
    simp [Function.update, queryContents, queryStack]

/-- Query extraction enters certificate membership in its final counted step. -/
def queryStmt : TM2.Stmt FrameExtraction.Alphabet FrameExtraction.Label FrameExtraction.State →
    TM2.Stmt Alphabet Label State
  | .push k write next => .push (queryStack k) (fun state => write state.1) (queryStmt next)
  | .peek k read next => .peek (queryStack k)
      (fun state bit => (read state.1 bit, CertificateMembership.initialState)) (queryStmt next)
  | .pop k read next => .pop (queryStack k)
      (fun state bit => (read state.1 bit, CertificateMembership.initialState)) (queryStmt next)
  | .load update next =>
      .load (fun state => (update state.1, CertificateMembership.initialState)) (queryStmt next)
  | .branch test yes no => .branch (fun state => test state.1) (queryStmt yes) (queryStmt no)
  | .goto next => .goto (fun state => .query (next state.1))
  | .halt => .load (fun _ => initialState) (.goto fun _ => .membership (.header .prefix))

/-- Membership control retains its stack operations and exact costs. -/
def membershipStmt : TM2.Stmt Alphabet CertificateMembership.Label CertificateMembership.State →
    TM2.Stmt Alphabet Label State
  | .push k write next => .push k (fun state => write state.2) (membershipStmt next)
  | .peek k read next => .peek k (fun state bit => (none, read state.2 bit)) (membershipStmt next)
  | .pop k read next => .pop k (fun state bit => (none, read state.2 bit)) (membershipStmt next)
  | .load update next => .load (fun state => (none, update state.2)) (membershipStmt next)
  | .branch test yes no => .branch (fun state => test state.2) (membershipStmt yes) (membershipStmt no)
  | .goto next => .goto (fun state => .membership (next state.2))
  | .halt => .halt

def program : Label → TM2.Stmt Alphabet Label State
  | .query label => queryStmt (FrameExtraction.program label)
  | .membership label => membershipStmt (CertificateMembership.program label)

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
    (input query remaining candidate scratch count output : List Bool) : computer.Cfg where
  l := label
  var := state
  stk := CertificateCount.stackContents input query remaining candidate scratch count output

def queryCfg (candidate output : List Bool) (c : FrameExtraction.computer.Cfg) : computer.Cfg where
  l := some (c.l.elim (.membership (.header .prefix)) Label.query)
  var := c.l.elim initialState (fun _ => (c.var, CertificateMembership.initialState))
  stk := queryContents candidate output c.stk

def membershipCfg (c : CertificateMembership.computer.Cfg) : computer.Cfg where
  l := c.l.map Label.membership
  var := (none, c.var)
  stk := c.stk

/-- Extractor statements preserve private stacks and enter membership at halt. -/
theorem query_stepAux
    (stmt : TM2.Stmt FrameExtraction.Alphabet FrameExtraction.Label FrameExtraction.State)
    (state : FrameExtraction.State)
    (contents : (k : FrameExtraction.Stack) → List (FrameExtraction.Alphabet k))
    (candidate output : List Bool) :
    TM2.stepAux (queryStmt stmt) (state, CertificateMembership.initialState)
      (queryContents candidate output contents) =
      queryCfg candidate output (TM2.stepAux stmt state contents) := by
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
    (stmt : TM2.Stmt Alphabet CertificateMembership.Label CertificateMembership.State)
    (state : CertificateMembership.State) (contents : (k : Stack) → List (Alphabet k)) :
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
    (candidate output : List Bool) :
    computer.step (queryCfg candidate output ⟨some label, state, contents⟩) =
      some (queryCfg candidate output (TM2.stepAux (FrameExtraction.program label) state contents)) := by
  change some (TM2.stepAux (queryStmt (FrameExtraction.program label))
    (state, CertificateMembership.initialState) (queryContents candidate output contents)) = _
  rw [query_stepAux]

private theorem membership_step (label : CertificateMembership.Label)
    (state : CertificateMembership.State) (contents : (k : Stack) → List (Alphabet k)) :
    computer.step (membershipCfg ⟨some label, state, contents⟩) =
      some (membershipCfg (TM2.stepAux (CertificateMembership.program label) state contents)) := by
  change some (TM2.stepAux (membershipStmt (CertificateMembership.program label)) (none, state) contents) = _
  rw [membership_stepAux]

private theorem iterate_bind_none {α : Type} (step : α → Option α) (n : Nat) :
    (fun c => c.bind step)^[n] none = none := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply]; exact ih

/-- Exact extraction execution enters membership in its final step. -/
theorem query_run (n : Nat) (start finish : FrameExtraction.computer.Cfg)
    (candidate output : List Bool)
    (run : (fun c => c.bind FrameExtraction.computer.step)^[n] (some start) = some finish) :
    (fun c => c.bind computer.step)^[n] (some (queryCfg candidate output start)) =
      some (queryCfg candidate output finish) := by
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
theorem membership_run (n : Nat) (start finish : CertificateMembership.computer.Cfg)
    (run : (fun c => c.bind CertificateMembership.computer.step)^[n]
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
theorem query_whole_frame (bits input remaining candidate output : List Bool) :
    (fun c => c.bind computer.step)^[3 * bits.length + 3]
      (some (cfg (some (.query .prefix)) initialState
        (BinaryNatLists.frame bits ++ input) [] remaining candidate [] [] output)) =
      some (cfg (some (.membership (.header .prefix))) initialState
        input bits remaining candidate [] [] output) := by
  have run := query_run _ _ _ candidate output
    (FrameExtraction.whole_frame bits input remaining [])
  simpa only [List.append_nil] using run

/-- A framed query followed by the complete framed certificate. -/
def encodeInput (query : Nat) (xs : List Nat) : List Bool :=
  BinaryNatLists.encodeNat query ++ BinaryNatLists.encodeNatList xs

/-- Exact query extraction plus complete certificate-membership execution. -/
def runSteps (query : Nat) (xs : List Nat) : Nat :=
  (3 * (encodeNat query).length + 3) + CertificateMembership.runSteps query xs

/-- Membership from one serialized input, with exact cost and preserved suffixes. -/
theorem whole_input (query : Nat) (xs : List Nat) (input output : List Bool) :
    (fun c => c.bind computer.step)^[runSteps query xs]
      (some (cfg (some (.query .prefix)) initialState
        (encodeInput query xs ++ input) [] [] [] [] [] output)) =
      some (cfg (some (.membership (.loop .done))) initialState
        input (encodeNat query) [] [] [] [] (decide (query ∈ xs) :: output)) := by
  rw [runSteps, Nat.add_comm, Function.iterate_add_apply]
  simp only [encodeInput, BinaryNatLists.encodeNat, List.append_assoc]
  rw [query_whole_frame]
  exact membership_run _ _ _ (CertificateMembership.whole_list query xs input output)

/-- A quadratic bound in the complete serialized query/certificate bit length. -/
theorem runSteps_le_bit_bound (query : Nat) (xs : List Nat) :
    runSteps query xs ≤ (encodeInput query xs).length *
      (4 * (encodeInput query xs).length + 19) + 7 := by
  have query_le : (encodeNat query).length ≤ (encodeInput query xs).length := by
    simp only [encodeInput, List.length_append, BinaryNatLists.encodeNat,
      BinaryNatLists.frame_length]
    omega
  have certificate_le : (BinaryNatLists.encodeNatList xs).length ≤
      (encodeInput query xs).length := by
    simp only [encodeInput, List.length_append]
    omega
  have inner_le : 2 * (encodeNat query).length +
      4 * (BinaryNatLists.encodeNatList xs).length + 16 ≤
      4 * (encodeInput query xs).length + 16 := by
    simp only [encodeInput, List.length_append, BinaryNatLists.encodeNat,
      BinaryNatLists.frame_length]
    omega
  have product := Nat.mul_le_mul certificate_le inner_le
  have bound := CertificateMembership.runSteps_le_bit_bound query xs
  unfold runSteps
  rw [show 4 * (encodeInput query xs).length + 19 =
      (4 * (encodeInput query xs).length + 16) + 3 by omega, Nat.mul_add]
  omega

/-- Serialized membership has a checked polynomial step bound on canonical inputs. -/
def evalsToInTime (query : Nat) (xs : List Nat) (input output : List Bool) :
    EvalsToInTime computer.step
      (cfg (some (.query .prefix)) initialState (encodeInput query xs ++ input)
        [] [] [] [] [] output)
      (some (cfg (some (.membership (.loop .done))) initialState
        input (encodeNat query) [] [] [] [] (decide (query ∈ xs) :: output)))
      ((encodeInput query xs).length * (4 * (encodeInput query xs).length + 19) + 7) where
  steps := runSteps query xs
  evals_in_steps := whole_input query xs input output
  steps_le_m := runSteps_le_bit_bound query xs

/-- Boolean semantics of the emitted bit, separate from machine execution. -/
theorem result_eq_true_iff (query : Nat) (xs : List Nat) :
    decide (query ∈ xs) = true ↔ query ∈ xs := by simp

end LeanNPHardness.MachinePrimitives.SerializedMembership
