import LeanNPHardness.QueryMembershipLoopMachine

/-!
# Reusable membership from a complete encoded query list

This finite nine-stack TM2 dispatcher loads the framed outer query count and
enters the checked count-controlled membership loop. The full certificate is
preloaded on `backup`. Canonical complete query encodings, including the header
and every repeated occurrence, are consumed; both suffixes and the certificate
survive. All count and workspace stacks finish empty, with one membership bit
per query occurrence in reverse query order.

Exact execution includes header extraction and loop entry in its final step.
The separate runtime bound is `M * (N * (2M + 4N + 18) + 8M + 23) + 4`,
where `M` and `N` are full framed query-list and certificate lengths in bits.
Execution ends at a live continuation before its halt. Certificate loading,
malformed-input rejection, literal/formula evaluation, and the full SAT verifier
remain separate obligations.
-/

namespace LeanNPHardness.MachinePrimitives.EncodedQueryMembership

open Computability Turing

abbrev Stack := QueryMembershipLoop.Stack
abbrev Alphabet := QueryMembershipLoop.Alphabet
abbrev State := FrameExtraction.State × QueryMembershipLoop.State

def initialState : State := (none, QueryMembershipLoop.initialState)

inductive Label
  | header (label : FrameExtraction.Label)
  | loop (label : QueryMembershipLoop.Label)
  deriving DecidableEq, Fintype

/-- Direct the extractor payload into the independent outer query count. -/
def headerStack : FrameExtraction.Stack → Stack
  | .input => .lookup .input
  | .query => .lookup .query
  | .candidate => .outerRemaining
  | .scratch => .lookup .scratch
  | .count => .lookup .count

def headerContents (remaining candidate output backup : List Bool)
    (contents : (k : FrameExtraction.Stack) → List (FrameExtraction.Alphabet k)) :
    (k : Stack) → List (Alphabet k)
  | .lookup .input => contents .input
  | .lookup .query => contents .query
  | .lookup .remaining => remaining
  | .lookup .candidate => candidate
  | .lookup .scratch => contents .scratch
  | .lookup .count => contents .count
  | .lookup .output => output
  | .lookup .backup => backup
  | .outerRemaining => contents .candidate

@[simp] private theorem headerContents_apply (remaining candidate output backup : List Bool)
    (contents : (k : FrameExtraction.Stack) → List (FrameExtraction.Alphabet k))
    (k : FrameExtraction.Stack) :
    headerContents remaining candidate output backup contents (headerStack k) = contents k := by
  cases k <;> rfl

private theorem headerContents_update (remaining candidate output backup : List Bool)
    (contents : (k : FrameExtraction.Stack) → List (FrameExtraction.Alphabet k))
    (k : FrameExtraction.Stack) (value : List Bool) :
    Function.update (headerContents remaining candidate output backup contents) (headerStack k) value =
      headerContents remaining candidate output backup (Function.update contents k value) := by
  funext index
  cases index with
  | lookup index =>
      cases k <;> cases index <;> simp [Function.update, headerContents, headerStack]
  | outerRemaining =>
      cases k <;> simp [Function.update, headerContents, headerStack]

/-- Header extraction enters the query loop in its final counted step. -/
def headerStmt : TM2.Stmt FrameExtraction.Alphabet FrameExtraction.Label FrameExtraction.State →
    TM2.Stmt Alphabet Label State
  | .push k write next => .push (headerStack k) (fun state => write state.1) (headerStmt next)
  | .peek k read next => .peek (headerStack k)
      (fun state bit => (read state.1 bit, QueryMembershipLoop.initialState)) (headerStmt next)
  | .pop k read next => .pop (headerStack k)
      (fun state bit => (read state.1 bit, QueryMembershipLoop.initialState)) (headerStmt next)
  | .load update next =>
      .load (fun state => (update state.1, QueryMembershipLoop.initialState)) (headerStmt next)
  | .branch test yes no => .branch (fun state => test state.1) (headerStmt yes) (headerStmt no)
  | .goto next => .goto (fun state => .header (next state.1))
  | .halt => .load (fun _ => initialState) (.goto fun _ => .loop .check)

/-- Loop control is embedded without changing its stack operations or costs. -/
def loopStmt : TM2.Stmt Alphabet QueryMembershipLoop.Label QueryMembershipLoop.State →
    TM2.Stmt Alphabet Label State
  | .push k write next => .push k (fun state => write state.2) (loopStmt next)
  | .peek k read next => .peek k (fun state bit => (none, read state.2 bit)) (loopStmt next)
  | .pop k read next => .pop k (fun state bit => (none, read state.2 bit)) (loopStmt next)
  | .load update next => .load (fun state => (none, update state.2)) (loopStmt next)
  | .branch test yes no => .branch (fun state => test state.2) (loopStmt yes) (loopStmt no)
  | .goto next => .goto (fun state => .loop (next state.2))
  | .halt => .halt

def program : Label → TM2.Stmt Alphabet Label State
  | .header label => headerStmt (FrameExtraction.program label)
  | .loop label => loopStmt (QueryMembershipLoop.program label)

def computer : FinTM2 where
  K := Stack
  k₀ := .lookup .input
  k₁ := .lookup .output
  Γ := Alphabet
  Λ := Label
  main := .header .prefix
  σ := State
  initialState := initialState
  Γk₀Fin := Bool.fintype
  m := program

def cfg (label : Option Label) (state : State)
    (input query remaining candidate scratch count output backup outer : List Bool) : computer.Cfg where
  l := label
  var := state
  stk := (QueryMembershipLoop.cfg none QueryMembershipLoop.initialState
    input query remaining candidate scratch count output backup outer).stk

def headerCfg (remaining candidate output backup : List Bool) (c : FrameExtraction.computer.Cfg) : computer.Cfg where
  l := some (c.l.elim (.loop .check) Label.header)
  var := c.l.elim initialState (fun _ => (c.var, QueryMembershipLoop.initialState))
  stk := headerContents remaining candidate output backup c.stk

def loopCfg (c : QueryMembershipLoop.computer.Cfg) : computer.Cfg where
  l := c.l.map Label.loop
  var := (none, c.var)
  stk := c.stk

/-- Extractor statements preserve backup, output, and the independent inner count. -/
theorem header_stepAux
    (stmt : TM2.Stmt FrameExtraction.Alphabet FrameExtraction.Label FrameExtraction.State)
    (state : FrameExtraction.State)
    (contents : (k : FrameExtraction.Stack) → List (FrameExtraction.Alphabet k))
    (remaining candidate output backup : List Bool) :
    TM2.stepAux (headerStmt stmt) (state, QueryMembershipLoop.initialState)
      (headerContents remaining candidate output backup contents) =
      headerCfg remaining candidate output backup (TM2.stepAux stmt state contents) := by
  induction stmt generalizing state contents with
  | push k write next ih =>
      simp only [headerStmt, TM2.stepAux, headerContents_apply]
      rw [headerContents_update]
      exact ih _ _
  | peek k read next ih =>
      simpa only [headerStmt, TM2.stepAux, headerContents_apply] using ih _ _
  | pop k read next ih =>
      simp only [headerStmt, TM2.stepAux, headerContents_apply]
      rw [headerContents_update]
      exact ih _ _
  | load update next ih => simpa only [headerStmt, TM2.stepAux] using ih _ _
  | branch test yes no ihYes ihNo =>
      cases h : test state
      · simpa only [headerStmt, TM2.stepAux, h, Bool.false_eq_true, cond_false] using ihNo state contents
      · simpa only [headerStmt, TM2.stepAux, h, cond_true] using ihYes state contents
  | goto next => rfl
  | halt => rfl

/-- The loop's one-step simulation preserves its exact cost. -/
theorem loop_stepAux
    (stmt : TM2.Stmt Alphabet QueryMembershipLoop.Label QueryMembershipLoop.State)
    (state : QueryMembershipLoop.State) (contents : (k : Stack) → List (Alphabet k)) :
    TM2.stepAux (loopStmt stmt) (none, state) contents =
      loopCfg (TM2.stepAux stmt state contents) := by
  induction stmt generalizing state contents with
  | push k write next ih => simpa only [loopStmt, TM2.stepAux] using ih _ _
  | peek k read next ih => simpa only [loopStmt, TM2.stepAux] using ih _ _
  | pop k read next ih => simpa only [loopStmt, TM2.stepAux] using ih _ _
  | load update next ih => simpa only [loopStmt, TM2.stepAux] using ih _ _
  | branch test yes no ihYes ihNo =>
      cases h : test state
      · simpa only [loopStmt, TM2.stepAux, h, Bool.false_eq_true, cond_false] using ihNo state contents
      · simpa only [loopStmt, TM2.stepAux, h, cond_true] using ihYes state contents
  | goto next => rfl
  | halt => rfl

private theorem header_step (label : FrameExtraction.Label) (state : FrameExtraction.State)
    (contents : (k : FrameExtraction.Stack) → List (FrameExtraction.Alphabet k))
    (remaining candidate output backup : List Bool) :
    computer.step (headerCfg remaining candidate output backup ⟨some label, state, contents⟩) =
      some (headerCfg remaining candidate output backup (TM2.stepAux (FrameExtraction.program label) state contents)) := by
  change some (TM2.stepAux (headerStmt (FrameExtraction.program label))
    (state, QueryMembershipLoop.initialState) (headerContents remaining candidate output backup contents)) = _
  rw [header_stepAux]

private theorem loop_step (label : QueryMembershipLoop.Label)
    (state : QueryMembershipLoop.State) (contents : (k : Stack) → List (Alphabet k)) :
    computer.step (loopCfg ⟨some label, state, contents⟩) =
      some (loopCfg (TM2.stepAux (QueryMembershipLoop.program label) state contents)) := by
  change some (TM2.stepAux (loopStmt (QueryMembershipLoop.program label)) (none, state) contents) = _
  rw [loop_stepAux]

private theorem iterate_bind_none {α : Type} (step : α → Option α) (n : Nat) :
    (fun c => c.bind step)^[n] none = none := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply]; exact ih

/-- Exact extraction execution includes query-loop entry at its final step. -/
theorem header_run (n : Nat) (start finish : FrameExtraction.computer.Cfg)
    (remaining candidate output backup : List Bool)
    (run : (fun c => c.bind FrameExtraction.computer.step)^[n] (some start) = some finish) :
    (fun c => c.bind computer.step)^[n] (some (headerCfg remaining candidate output backup start)) =
      some (headerCfg remaining candidate output backup finish) := by
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
          rw [Option.bind_some, header_step]
          exact ih _ run

/-- Exact loop execution lifts without additional dispatch steps. -/
theorem loop_run (n : Nat) (start finish : QueryMembershipLoop.computer.Cfg)
    (run : (fun c => c.bind QueryMembershipLoop.computer.step)^[n]
      (some start) = some finish) :
    (fun c => c.bind computer.step)^[n] (some (loopCfg start)) = some (loopCfg finish) := by
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
          rw [Option.bind_some, loop_step]
          exact ih _ run

/-- Identify the extractor embedding with the shared nine-stack configuration. -/
private theorem headerCfg_cfg (label : Option FrameExtraction.Label)
    (state : FrameExtraction.State)
    (input query outer scratch count remaining candidate output backup : List Bool) :
    headerCfg remaining candidate output backup
      (FrameExtraction.cfg label state input query outer scratch count) =
      cfg (some (label.elim (.loop .check) Label.header))
        (label.elim initialState (fun _ => (state, QueryMembershipLoop.initialState)))
        input query remaining candidate scratch count output backup outer := by
  unfold headerCfg cfg FrameExtraction.cfg
  congr 1
  funext index
  cases index with
  | lookup index => cases index <;> rfl
  | outerRemaining => rfl

/-- Load a full outer header while preserving arbitrary private stack contents. -/
theorem header_whole_frame (bits input query remaining candidate output backup : List Bool) :
    (fun c => c.bind computer.step)^[3 * bits.length + 3]
      (some (cfg (some (.header .prefix)) initialState
        (BinaryNatLists.frame bits ++ input) query remaining candidate [] [] output backup [])) =
      some (cfg (some (.loop .check)) initialState
        input query remaining candidate [] [] output backup bits) := by
  have run := header_run _ _ _ remaining candidate output backup
    (FrameExtraction.whole_frame bits input query [])
  simpa only [List.append_nil, headerCfg_cfg, Option.elim_some, Option.elim_none] using run

/-- Exact cost of header loading, loop entry, and all repeated membership queries. -/
def runSteps (queries xs : List Nat) : Nat :=
  (3 * (encodeNat queries.length).length + 3) + QueryMembershipLoop.runSteps xs queries

/-- Traverse a complete encoded query list, retaining the certificate and both suffixes. -/
theorem whole_list (queries xs : List Nat) (input output : List Bool) :
    (fun c => c.bind computer.step)^[runSteps queries xs]
      (some (cfg (some (.header .prefix)) initialState
        (BinaryNatLists.encodeNatList queries ++ input)
        [] [] [] [] [] output (BinaryNatLists.encodeNatList xs) [])) =
      some (cfg (some (.loop .done)) initialState input [] [] [] [] []
        (QueryMembershipLoop.results queries xs ++ output) (BinaryNatLists.encodeNatList xs) []) := by
  rw [runSteps, Nat.add_comm, Function.iterate_add_apply]
  simp only [BinaryNatLists.encodeNatList, BinaryNatLists.encodeNat, List.append_assoc]
  rw [header_whole_frame]
  exact loop_run _ _ _ (QueryMembershipLoop.whole_list queries xs input output)

/-- Polynomial runtime in full framed query-list and certificate bit lengths. -/
theorem runSteps_le_bit_bound (queries xs : List Nat) :
    runSteps queries xs ≤ (BinaryNatLists.encodeNatList queries).length *
      ((BinaryNatLists.encodeNatList xs).length *
        (2 * (BinaryNatLists.encodeNatList queries).length +
          4 * (BinaryNatLists.encodeNatList xs).length + 18) +
        8 * (BinaryNatLists.encodeNatList queries).length + 23) + 4 := by
  have body_le : (queries.flatMap BinaryNatLists.encodeNat).length ≤
      (BinaryNatLists.encodeNatList queries).length := by
    simp only [BinaryNatLists.encodeNatList, List.length_append]
    omega
  have count_le : (encodeNat queries.length).length ≤
      (BinaryNatLists.encodeNatList queries).length := by
    simp only [BinaryNatLists.encodeNatList, List.length_append,
      BinaryNatLists.encodeNat, BinaryNatLists.frame_length]
    omega
  have bound := QueryMembershipLoop.runSteps_le queries xs
    (BinaryNatLists.encodeNatList queries).length body_le
  have entries_le := (CertificateMembershipLoop.length_le_body_length queries).trans body_le
  have product := Nat.mul_le_mul_right
    ((BinaryNatLists.encodeNatList xs).length *
      (2 * (BinaryNatLists.encodeNatList queries).length +
        4 * (BinaryNatLists.encodeNatList xs).length + 18) +
      8 * (BinaryNatLists.encodeNatList queries).length + 20) entries_le
  unfold runSteps
  rw [show (BinaryNatLists.encodeNatList xs).length *
      (2 * (BinaryNatLists.encodeNatList queries).length +
        4 * (BinaryNatLists.encodeNatList xs).length + 18) +
      8 * (BinaryNatLists.encodeNatList queries).length + 23 =
    ((BinaryNatLists.encodeNatList xs).length *
      (2 * (BinaryNatLists.encodeNatList queries).length +
        4 * (BinaryNatLists.encodeNatList xs).length + 18) +
      8 * (BinaryNatLists.encodeNatList queries).length + 20) + 3 by omega,
    Nat.mul_add]
  omega

/-- Bounded execution from the complete query encoding and a retained certificate. -/
def evalsToInTime (queries xs : List Nat) (input output : List Bool) :
    EvalsToInTime computer.step
      (cfg (some (.header .prefix)) initialState
        (BinaryNatLists.encodeNatList queries ++ input)
        [] [] [] [] [] output (BinaryNatLists.encodeNatList xs) [])
      (some (cfg (some (.loop .done)) initialState input [] [] [] [] []
        (QueryMembershipLoop.results queries xs ++ output) (BinaryNatLists.encodeNatList xs) []))
      ((BinaryNatLists.encodeNatList queries).length *
        ((BinaryNatLists.encodeNatList xs).length *
          (2 * (BinaryNatLists.encodeNatList queries).length +
            4 * (BinaryNatLists.encodeNatList xs).length + 18) +
          8 * (BinaryNatLists.encodeNatList queries).length + 23) + 4) where
  steps := runSteps queries xs
  evals_in_steps := whole_list queries xs input output
  steps_le_m := runSteps_le_bit_bound queries xs

end LeanNPHardness.MachinePrimitives.EncodedQueryMembership
