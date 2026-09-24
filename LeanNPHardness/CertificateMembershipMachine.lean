import LeanNPHardness.CertificateMembershipLoopMachine

/-!
# Membership from a complete encoded certificate

A finite seven-stack TM2 dispatcher extracts the framed list count and then
traverses every certificate entry. The extractor's final step initializes the
output accumulator to false and enters the loop's count test. The query is
preloaded in canonical binary form; the certificate includes its own header.

Exact execution consumes the complete certificate, including duplicates,
preserves the query and arbitrary input/output suffixes, empties all work
stacks, and ends at the live loop continuation before its halt. Runtime is
bounded separately in query bits and full certificate bits. Canonical complete
encodings are assumed; malformed-input rejection and a full verifier are separate.
-/

namespace LeanNPHardness.MachinePrimitives.CertificateMembership

open Computability Turing

abbrev Stack := CertificateCount.Stack
abbrev Alphabet := CertificateCount.Alphabet
abbrev State := FrameExtraction.State × CertificateMembershipLoop.State

def initialState : State := (none, CertificateMembershipLoop.initialState)

inductive Label
  | header (label : FrameExtraction.Label)
  | loop (label : CertificateMembershipLoop.Label)
  deriving DecidableEq, Fintype

abbrev headerStack := CertificateCount.extractStack
abbrev headerContents := CertificateCount.extractContents

@[simp] private theorem headerContents_apply (candidate output : List Bool)
    (contents : (k : FrameExtraction.Stack) → List (FrameExtraction.Alphabet k))
    (k : FrameExtraction.Stack) :
    headerContents candidate output contents (headerStack k) = contents k := by
  cases k <;> rfl

private theorem headerContents_update (candidate output : List Bool)
    (contents : (k : FrameExtraction.Stack) → List (FrameExtraction.Alphabet k))
    (k : FrameExtraction.Stack) (value : List Bool) :
    Function.update (headerContents candidate output contents) (headerStack k) value =
      headerContents candidate output (Function.update contents k value) := by
  funext index
  cases k <;> cases index <;>
    simp [Function.update, headerContents, headerStack,
      CertificateCount.extractContents, CertificateCount.extractStack]

/-- Header extraction targets `remaining`; its halt initializes membership. -/
def headerStmt : TM2.Stmt FrameExtraction.Alphabet FrameExtraction.Label FrameExtraction.State →
    TM2.Stmt Alphabet Label State
  | .push k write next => .push (headerStack k) (fun state => write state.1) (headerStmt next)
  | .peek k read next => .peek (headerStack k)
      (fun state bit => (read state.1 bit, CertificateMembershipLoop.initialState)) (headerStmt next)
  | .pop k read next => .pop (headerStack k)
      (fun state bit => (read state.1 bit, CertificateMembershipLoop.initialState)) (headerStmt next)
  | .load update next =>
      .load (fun state => (update state.1, CertificateMembershipLoop.initialState)) (headerStmt next)
  | .branch test yes no => .branch (fun state => test state.1) (headerStmt yes) (headerStmt no)
  | .goto next => .goto (fun state => .header (next state.1))
  | .halt => .push .output (fun _ => false)
      (.load (fun _ => initialState) (.goto fun _ => .loop .check))

/-- Loop control is embedded without changing its stack operations or costs. -/
def loopStmt : TM2.Stmt Alphabet CertificateMembershipLoop.Label CertificateMembershipLoop.State →
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
  | .loop label => loopStmt (CertificateMembershipLoop.program label)

def computer : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .output
  Γ := Alphabet
  Λ := Label
  main := .header .prefix
  σ := State
  initialState := initialState
  Γk₀Fin := Bool.fintype
  m := program

def cfg (label : Option Label) (state : State)
    (input query remaining candidate scratch count output : List Bool) : computer.Cfg where
  l := label
  var := state
  stk := CertificateCount.stackContents input query remaining candidate scratch count output

def headerCfg (candidate output : List Bool) (c : FrameExtraction.computer.Cfg) : computer.Cfg where
  l := some (c.l.elim (.loop .check) Label.header)
  var := c.l.elim initialState (fun _ => (c.var, CertificateMembershipLoop.initialState))
  stk := headerContents candidate (c.l.elim (false :: output) (fun _ => output)) c.stk

def loopCfg (c : CertificateMembershipLoop.computer.Cfg) : computer.Cfg where
  l := c.l.map Label.loop
  var := (none, c.var)
  stk := c.stk

/-- Extractor statements preserve private data and initialize output only at halt. -/
theorem header_stepAux
    (stmt : TM2.Stmt FrameExtraction.Alphabet FrameExtraction.Label FrameExtraction.State)
    (state : FrameExtraction.State)
    (contents : (k : FrameExtraction.Stack) → List (FrameExtraction.Alphabet k))
    (candidate output : List Bool) :
    TM2.stepAux (headerStmt stmt) (state, CertificateMembershipLoop.initialState)
      (headerContents candidate output contents) =
      headerCfg candidate output (TM2.stepAux stmt state contents) := by
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
  | halt =>
      simp only [headerStmt, TM2.stepAux, headerCfg, Option.elim_none]
      congr 1
      funext index
      cases index <;> rfl

/-- The loop's one-step simulation preserves its exact cost. -/
theorem loop_stepAux
    (stmt : TM2.Stmt Alphabet CertificateMembershipLoop.Label CertificateMembershipLoop.State)
    (state : CertificateMembershipLoop.State) (contents : (k : Stack) → List (Alphabet k)) :
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
    (candidate output : List Bool) :
    computer.step (headerCfg candidate output ⟨some label, state, contents⟩) =
      some (headerCfg candidate output (TM2.stepAux (FrameExtraction.program label) state contents)) := by
  change some (TM2.stepAux (headerStmt (FrameExtraction.program label))
    (state, CertificateMembershipLoop.initialState) (headerContents candidate output contents)) = _
  rw [header_stepAux]

private theorem loop_step (label : CertificateMembershipLoop.Label)
    (state : CertificateMembershipLoop.State) (contents : (k : Stack) → List (Alphabet k)) :
    computer.step (loopCfg ⟨some label, state, contents⟩) =
      some (loopCfg (TM2.stepAux (CertificateMembershipLoop.program label) state contents)) := by
  change some (TM2.stepAux (loopStmt (CertificateMembershipLoop.program label)) (none, state) contents) = _
  rw [loop_stepAux]

private theorem iterate_bind_none {α : Type} (step : α → Option α) (n : Nat) :
    (fun c => c.bind step)^[n] none = none := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply]; exact ih

/-- Exact extraction execution includes the new initialization at its final step. -/
theorem header_run (n : Nat) (start finish : FrameExtraction.computer.Cfg)
    (candidate output : List Bool)
    (run : (fun c => c.bind FrameExtraction.computer.step)^[n] (some start) = some finish) :
    (fun c => c.bind computer.step)^[n] (some (headerCfg candidate output start)) =
      some (headerCfg candidate output finish) := by
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
theorem loop_run (n : Nat) (start finish : CertificateMembershipLoop.computer.Cfg)
    (run : (fun c => c.bind CertificateMembershipLoop.computer.step)^[n]
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

/-- Load a complete header and initialize the false accumulator in the same run. -/
theorem header_whole_frame (bits input query output : List Bool) :
    (fun c => c.bind computer.step)^[3 * bits.length + 3]
      (some (cfg (some (.header .prefix)) initialState
        (BinaryNatLists.frame bits ++ input) query [] [] [] [] output)) =
      some (cfg (some (.loop .check)) initialState input query bits [] [] [] (false :: output)) := by
  have run := header_run _ _ _ [] output (FrameExtraction.whole_frame bits input query [])
  simpa only [List.append_nil] using run

/-- Exact runtime includes header extraction, initialization, and every loop step. -/
def runSteps (query : Nat) (xs : List Nat) : Nat :=
  (3 * (encodeNat xs.length).length + 3) + CertificateMembershipLoop.runSteps query xs

/-- Membership from a full certificate encoding, preserving the query and suffixes. -/
theorem whole_list (query : Nat) (xs : List Nat) (input output : List Bool) :
    (fun c => c.bind computer.step)^[runSteps query xs]
      (some (cfg (some (.header .prefix)) initialState
        (BinaryNatLists.encodeNatList xs ++ input) (encodeNat query) [] [] [] [] output)) =
      some (cfg (some (.loop .done)) initialState input (encodeNat query) [] [] [] []
        (decide (query ∈ xs) :: output)) := by
  rw [runSteps, Nat.add_comm, Function.iterate_add_apply]
  simp only [BinaryNatLists.encodeNatList, BinaryNatLists.encodeNat, List.append_assoc]
  rw [header_whole_frame]
  simpa only [Bool.or_false] using
    loop_run _ _ _ (CertificateMembershipLoop.whole_list query xs input output false)

/-- Polynomial runtime in raw query bits and the complete framed certificate bits. -/
theorem runSteps_le_bit_bound (query : Nat) (xs : List Nat) :
    runSteps query xs ≤
      (BinaryNatLists.encodeNatList xs).length *
        (2 * (encodeNat query).length + 4 * (BinaryNatLists.encodeNatList xs).length + 16) + 4 := by
  have body_le : (xs.flatMap BinaryNatLists.encodeNat).length ≤
      (BinaryNatLists.encodeNatList xs).length := by
    simp only [BinaryNatLists.encodeNatList, List.length_append]
    omega
  have count_le : (encodeNat xs.length).length ≤
      (BinaryNatLists.encodeNatList xs).length := by
    simp only [BinaryNatLists.encodeNatList, List.length_append,
      BinaryNatLists.encodeNat, BinaryNatLists.frame_length]
    omega
  have product := Nat.mul_le_mul body_le
    (show 2 * (encodeNat query).length + 4 * (xs.flatMap BinaryNatLists.encodeNat).length + 11 ≤
      2 * (encodeNat query).length + 4 * (BinaryNatLists.encodeNatList xs).length + 11 by omega)
  have bound := CertificateMembershipLoop.runSteps_le_bit_bound query xs
  unfold runSteps
  rw [show 2 * (encodeNat query).length +
      4 * (BinaryNatLists.encodeNatList xs).length + 16 =
      (2 * (encodeNat query).length + 4 * (BinaryNatLists.encodeNatList xs).length + 11) + 5
      by omega, Nat.mul_add]
  omega

/-- The complete encoded-certificate kernel has a checked polynomial step bound. -/
def evalsToInTime (query : Nat) (xs : List Nat) (input output : List Bool) :
    EvalsToInTime computer.step
      (cfg (some (.header .prefix)) initialState
        (BinaryNatLists.encodeNatList xs ++ input) (encodeNat query) [] [] [] [] output)
      (some (cfg (some (.loop .done)) initialState input (encodeNat query) [] [] [] []
        (decide (query ∈ xs) :: output)))
      ((BinaryNatLists.encodeNatList xs).length *
        (2 * (encodeNat query).length + 4 * (BinaryNatLists.encodeNatList xs).length + 16) + 4) where
  steps := runSteps query xs
  evals_in_steps := whole_list query xs input output
  steps_le_m := runSteps_le_bit_bound query xs

/-- Separate Boolean semantics of the emitted bit. -/
theorem result_eq_true_iff (query : Nat) (xs : List Nat) :
    decide (query ∈ xs) = true ↔ query ∈ xs := by simp

end LeanNPHardness.MachinePrimitives.CertificateMembership
