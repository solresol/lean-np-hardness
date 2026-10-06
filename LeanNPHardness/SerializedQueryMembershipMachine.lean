import LeanNPHardness.EncodedQueryMembershipMachine

/-!
# Repeated membership from a serialized certificate and query list

This finite nine-stack TM2 dispatcher extracts one outer frame containing the
complete certificate encoding onto `backup`, then enters the checked encoded
query-list dispatcher. No certificate or query count is preloaded. The complete
canonical input is consumed, including repeated occurrences, while the loaded
certificate and arbitrary input/output suffixes survive. Count/workspace stacks
finish empty, and output has one membership bit per query in reverse order.

Exact execution includes membership entry in the extractor's final counted
step. The separate bound is `S * (S * (2S + 18) + 8S + 26) + 7` in complete
serialized input bits `S`. Execution ends at a live continuation before its
halt. Backup cleanup, canonical halting output, malformed-input rejection,
literal/formula evaluation, and the full SAT verifier remain separate.
-/

namespace LeanNPHardness.MachinePrimitives.SerializedQueryMembership

open Computability Turing

abbrev Stack := EncodedQueryMembership.Stack
abbrev Alphabet := EncodedQueryMembership.Alphabet
abbrev State := FrameExtraction.State × EncodedQueryMembership.State

def initialState : State := (none, EncodedQueryMembership.initialState)

inductive Label
  | certificate (label : FrameExtraction.Label)
  | membership (label : EncodedQueryMembership.Label)
  deriving DecidableEq, Fintype

/-- Direct the complete framed certificate payload into its reusable backup stack. -/
def certificateStack : FrameExtraction.Stack → Stack
  | .input => .lookup .input
  | .query => .lookup .query
  | .candidate => .lookup .backup
  | .scratch => .lookup .scratch
  | .count => .lookup .count

def certificateContents (remaining candidate output outer : List Bool)
    (contents : (k : FrameExtraction.Stack) → List (FrameExtraction.Alphabet k)) :
    (k : Stack) → List (Alphabet k)
  | .lookup .input => contents .input
  | .lookup .query => contents .query
  | .lookup .remaining => remaining
  | .lookup .candidate => candidate
  | .lookup .scratch => contents .scratch
  | .lookup .count => contents .count
  | .lookup .output => output
  | .lookup .backup => contents .candidate
  | .outerRemaining => outer

@[simp] private theorem certificateContents_apply (remaining candidate output outer : List Bool)
    (contents : (k : FrameExtraction.Stack) → List (FrameExtraction.Alphabet k))
    (k : FrameExtraction.Stack) :
    certificateContents remaining candidate output outer contents (certificateStack k) = contents k := by
  cases k <;> rfl

private theorem certificateContents_update (remaining candidate output outer : List Bool)
    (contents : (k : FrameExtraction.Stack) → List (FrameExtraction.Alphabet k))
    (k : FrameExtraction.Stack) (value : List Bool) :
    Function.update (certificateContents remaining candidate output outer contents) (certificateStack k) value =
      certificateContents remaining candidate output outer (Function.update contents k value) := by
  funext index
  cases index with
  | lookup index =>
      cases k <;> cases index <;> simp [Function.update, certificateContents, certificateStack]
  | outerRemaining =>
      cases k <;> simp [Function.update, certificateContents, certificateStack]

/-- Certificate extraction enters query processing in its final counted step. -/
def certificateStmt : TM2.Stmt FrameExtraction.Alphabet FrameExtraction.Label FrameExtraction.State →
    TM2.Stmt Alphabet Label State
  | .push k write next => .push (certificateStack k) (fun state => write state.1) (certificateStmt next)
  | .peek k read next => .peek (certificateStack k)
      (fun state bit => (read state.1 bit, EncodedQueryMembership.initialState)) (certificateStmt next)
  | .pop k read next => .pop (certificateStack k)
      (fun state bit => (read state.1 bit, EncodedQueryMembership.initialState)) (certificateStmt next)
  | .load update next =>
      .load (fun state => (update state.1, EncodedQueryMembership.initialState)) (certificateStmt next)
  | .branch test yes no => .branch (fun state => test state.1) (certificateStmt yes) (certificateStmt no)
  | .goto next => .goto (fun state => .certificate (next state.1))
  | .halt => .load (fun _ => initialState) (.goto fun _ => .membership (.header .prefix))

/-- Membership control is embedded without changing its stack operations or costs. -/
def membershipStmt : TM2.Stmt Alphabet EncodedQueryMembership.Label EncodedQueryMembership.State →
    TM2.Stmt Alphabet Label State
  | .push k write next => .push k (fun state => write state.2) (membershipStmt next)
  | .peek k read next => .peek k (fun state bit => (none, read state.2 bit)) (membershipStmt next)
  | .pop k read next => .pop k (fun state bit => (none, read state.2 bit)) (membershipStmt next)
  | .load update next => .load (fun state => (none, update state.2)) (membershipStmt next)
  | .branch test yes no => .branch (fun state => test state.2) (membershipStmt yes) (membershipStmt no)
  | .goto next => .goto (fun state => .membership (next state.2))
  | .halt => .halt

def program : Label → TM2.Stmt Alphabet Label State
  | .certificate label => certificateStmt (FrameExtraction.program label)
  | .membership label => membershipStmt (EncodedQueryMembership.program label)

def computer : FinTM2 where
  K := Stack
  k₀ := .lookup .input
  k₁ := .lookup .output
  Γ := Alphabet
  Λ := Label
  main := .certificate .prefix
  σ := State
  initialState := initialState
  Γk₀Fin := Bool.fintype
  m := program

def cfg (label : Option Label) (state : State)
    (input query remaining candidate scratch count output backup outer : List Bool) : computer.Cfg where
  l := label
  var := state
  stk := (EncodedQueryMembership.cfg none EncodedQueryMembership.initialState
    input query remaining candidate scratch count output backup outer).stk

def certificateCfg (remaining candidate output outer : List Bool) (c : FrameExtraction.computer.Cfg) : computer.Cfg where
  l := some (c.l.elim (.membership (.header .prefix)) Label.certificate)
  var := c.l.elim initialState (fun _ => (c.var, EncodedQueryMembership.initialState))
  stk := certificateContents remaining candidate output outer c.stk

def membershipCfg (c : EncodedQueryMembership.computer.Cfg) : computer.Cfg where
  l := c.l.map Label.membership
  var := (none, c.var)
  stk := c.stk

/-- Extractor statements preserve output, query workspace, and both list counts. -/
theorem certificate_stepAux
    (stmt : TM2.Stmt FrameExtraction.Alphabet FrameExtraction.Label FrameExtraction.State)
    (state : FrameExtraction.State)
    (contents : (k : FrameExtraction.Stack) → List (FrameExtraction.Alphabet k))
    (remaining candidate output outer : List Bool) :
    TM2.stepAux (certificateStmt stmt) (state, EncodedQueryMembership.initialState)
      (certificateContents remaining candidate output outer contents) =
      certificateCfg remaining candidate output outer (TM2.stepAux stmt state contents) := by
  induction stmt generalizing state contents with
  | push k write next ih =>
      simp only [certificateStmt, TM2.stepAux, certificateContents_apply]
      rw [certificateContents_update]
      exact ih _ _
  | peek k read next ih =>
      simpa only [certificateStmt, TM2.stepAux, certificateContents_apply] using ih _ _
  | pop k read next ih =>
      simp only [certificateStmt, TM2.stepAux, certificateContents_apply]
      rw [certificateContents_update]
      exact ih _ _
  | load update next ih => simpa only [certificateStmt, TM2.stepAux] using ih _ _
  | branch test yes no ihYes ihNo =>
      cases h : test state
      · simpa only [certificateStmt, TM2.stepAux, h, Bool.false_eq_true, cond_false] using ihNo state contents
      · simpa only [certificateStmt, TM2.stepAux, h, cond_true] using ihYes state contents
  | goto next => rfl
  | halt => rfl

/-- The membership's one-step simulation preserves its exact cost. -/
theorem membership_stepAux
    (stmt : TM2.Stmt Alphabet EncodedQueryMembership.Label EncodedQueryMembership.State)
    (state : EncodedQueryMembership.State) (contents : (k : Stack) → List (Alphabet k)) :
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

private theorem certificate_step (label : FrameExtraction.Label) (state : FrameExtraction.State)
    (contents : (k : FrameExtraction.Stack) → List (FrameExtraction.Alphabet k))
    (remaining candidate output outer : List Bool) :
    computer.step (certificateCfg remaining candidate output outer ⟨some label, state, contents⟩) =
      some (certificateCfg remaining candidate output outer (TM2.stepAux (FrameExtraction.program label) state contents)) := by
  change some (TM2.stepAux (certificateStmt (FrameExtraction.program label))
    (state, EncodedQueryMembership.initialState) (certificateContents remaining candidate output outer contents)) = _
  rw [certificate_stepAux]

private theorem membership_step (label : EncodedQueryMembership.Label)
    (state : EncodedQueryMembership.State) (contents : (k : Stack) → List (Alphabet k)) :
    computer.step (membershipCfg ⟨some label, state, contents⟩) =
      some (membershipCfg (TM2.stepAux (EncodedQueryMembership.program label) state contents)) := by
  change some (TM2.stepAux (membershipStmt (EncodedQueryMembership.program label)) (none, state) contents) = _
  rw [membership_stepAux]

private theorem iterate_bind_none {α : Type} (step : α → Option α) (n : Nat) :
    (fun c => c.bind step)^[n] none = none := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply]; exact ih

/-- Exact extraction execution includes query-processing entry at its final step. -/
theorem certificate_run (n : Nat) (start finish : FrameExtraction.computer.Cfg)
    (remaining candidate output outer : List Bool)
    (run : (fun c => c.bind FrameExtraction.computer.step)^[n] (some start) = some finish) :
    (fun c => c.bind computer.step)^[n] (some (certificateCfg remaining candidate output outer start)) =
      some (certificateCfg remaining candidate output outer finish) := by
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
          rw [Option.bind_some, certificate_step]
          exact ih _ run

/-- Exact membership execution lifts without additional dispatch steps. -/
theorem membership_run (n : Nat) (start finish : EncodedQueryMembership.computer.Cfg)
    (run : (fun c => c.bind EncodedQueryMembership.computer.step)^[n]
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

/-- Identify the extractor embedding with the shared nine-stack configuration. -/
private theorem certificateCfg_cfg (label : Option FrameExtraction.Label)
    (state : FrameExtraction.State)
    (input query backup scratch count remaining candidate output outer : List Bool) :
    certificateCfg remaining candidate output outer
      (FrameExtraction.cfg label state input query backup scratch count) =
      cfg (some (label.elim (.membership (.header .prefix)) Label.certificate))
        (label.elim initialState (fun _ => (state, EncodedQueryMembership.initialState)))
        input query remaining candidate scratch count output backup outer := by
  unfold certificateCfg cfg FrameExtraction.cfg
  congr 1
  funext index
  cases index with
  | lookup index => cases index <;> rfl
  | outerRemaining => rfl

/-- Load one certificate frame in order, retaining arbitrary private stack contents. -/
theorem certificate_whole_frame
    (bits input query remaining candidate output outer : List Bool) :
    (fun c => c.bind computer.step)^[3 * bits.length + 3]
      (some (cfg (some (.certificate .prefix)) initialState
        (BinaryNatLists.frame bits ++ input) query remaining candidate [] [] output [] outer)) =
      some (cfg (some (.membership (.header .prefix))) initialState
        input query remaining candidate [] [] output bits outer) := by
  have run := certificate_run _ _ _ remaining candidate output outer
    (FrameExtraction.whole_frame bits input query [])
  simpa only [List.append_nil, certificateCfg_cfg, Option.elim_some, Option.elim_none] using run

/-- One outer certificate frame followed by the complete query-list encoding. -/
def encodeInput (queries xs : List Nat) : List Bool :=
  BinaryNatLists.frame (BinaryNatLists.encodeNatList xs) ++
    BinaryNatLists.encodeNatList queries

/-- Exact serialized bit length, counting both headers and every occurrence. -/
theorem encodeInput_length (queries xs : List Nat) :
    (encodeInput queries xs).length =
      2 * (BinaryNatLists.encodeNatList xs).length + 1 +
        (BinaryNatLists.encodeNatList queries).length := by
  simp only [encodeInput, List.length_append, BinaryNatLists.frame_length]

/-- Exact certificate extraction plus complete repeated-membership execution. -/
def runSteps (queries xs : List Nat) : Nat :=
  (3 * (BinaryNatLists.encodeNatList xs).length + 3) +
    EncodedQueryMembership.runSteps queries xs

/-- Repeated membership from one serialized input, with retained backup and suffixes. -/
theorem whole_input (queries xs : List Nat) (input output : List Bool) :
    (fun c => c.bind computer.step)^[runSteps queries xs]
      (some (cfg (some (.certificate .prefix)) initialState
        (encodeInput queries xs ++ input) [] [] [] [] [] output [] [])) =
      some (cfg (some (.membership (.loop .done))) initialState input [] [] [] [] []
        (QueryMembershipLoop.results queries xs ++ output) (BinaryNatLists.encodeNatList xs) []) := by
  rw [runSteps, Nat.add_comm, Function.iterate_add_apply]
  simp only [encodeInput, List.append_assoc]
  rw [certificate_whole_frame]
  exact membership_run _ _ _ (EncodedQueryMembership.whole_list queries xs input output)

/-- A cubic bound in the complete serialized certificate/query input's bit length. -/
theorem runSteps_le_bit_bound (queries xs : List Nat) :
    runSteps queries xs ≤ (encodeInput queries xs).length *
      ((encodeInput queries xs).length * (2 * (encodeInput queries xs).length + 18) +
        8 * (encodeInput queries xs).length + 26) + 7 := by
  have length_eq := encodeInput_length queries xs
  have query_le : (BinaryNatLists.encodeNatList queries).length ≤
      (encodeInput queries xs).length := by omega
  have certificate_le : (BinaryNatLists.encodeNatList xs).length ≤
      (encodeInput queries xs).length := by omega
  have inner_le : 2 * (BinaryNatLists.encodeNatList queries).length +
      4 * (BinaryNatLists.encodeNatList xs).length + 18 ≤
      2 * (encodeInput queries xs).length + 18 := by omega
  have inner_product := Nat.mul_le_mul certificate_le inner_le
  have outer_le : (BinaryNatLists.encodeNatList xs).length *
      (2 * (BinaryNatLists.encodeNatList queries).length +
        4 * (BinaryNatLists.encodeNatList xs).length + 18) +
      8 * (BinaryNatLists.encodeNatList queries).length + 23 ≤
      (encodeInput queries xs).length * (2 * (encodeInput queries xs).length + 18) +
        8 * (encodeInput queries xs).length + 23 := by omega
  have product := Nat.mul_le_mul query_le outer_le
  have bound := EncodedQueryMembership.runSteps_le_bit_bound queries xs
  unfold runSteps
  rw [show (encodeInput queries xs).length * (2 * (encodeInput queries xs).length + 18) +
      8 * (encodeInput queries xs).length + 26 =
    ((encodeInput queries xs).length * (2 * (encodeInput queries xs).length + 18) +
      8 * (encodeInput queries xs).length + 23) + 3 by omega, Nat.mul_add]
  omega

/-- Bounded execution needs no preloaded certificate or list count. -/
def evalsToInTime (queries xs : List Nat) (input output : List Bool) :
    EvalsToInTime computer.step
      (cfg (some (.certificate .prefix)) initialState (encodeInput queries xs ++ input)
        [] [] [] [] [] output [] [])
      (some (cfg (some (.membership (.loop .done))) initialState input [] [] [] [] []
        (QueryMembershipLoop.results queries xs ++ output) (BinaryNatLists.encodeNatList xs) []))
      ((encodeInput queries xs).length *
        ((encodeInput queries xs).length * (2 * (encodeInput queries xs).length + 18) +
          8 * (encodeInput queries xs).length + 26) + 7) where
  steps := runSteps queries xs
  evals_in_steps := whole_input queries xs input output
  steps_le_m := runSteps_le_bit_bound queries xs

end LeanNPHardness.MachinePrimitives.SerializedQueryMembership
