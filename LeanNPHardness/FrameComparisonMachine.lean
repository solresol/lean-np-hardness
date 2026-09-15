import LeanNPHardness.FrameExtractionMachine
import LeanNPHardness.PreservingBinaryEqualityMachine

/-!
# Query-preserving comparison with one framed candidate

One finite TM2 dispatcher extracts an ordered frame, compares it with a
preloaded query, restores that query, and emits one Boolean. Extraction and
comparison share scratch storage. The unread input and output suffix survive;
all work stacks are empty at completion. The exact cost is the sum of the two
checked kernel costs; redirecting extraction's halt adds no TM2 step.

The input contract assumes one complete frame. Parsing the outer binary list
count, certificate traversal, and a full SAT verifier remain separate tasks.
-/

namespace LeanNPHardness.MachinePrimitives.FrameComparison

open Computability Turing

inductive Stack
  | input | query | candidate | scratch | count | output
  deriving DecidableEq, Fintype

inductive Label
  | extract (label : FrameExtraction.Label)
  | compare (label : PreservingBinaryEquality.Label)
  deriving DecidableEq, Fintype

abbrev State := FrameExtraction.State × PreservingBinaryEquality.State

def initialState : State := (none, PreservingBinaryEquality.initialState)

def Alphabet (_ : Stack) : Type := Bool

def extractStack : FrameExtraction.Stack → Stack
  | .input => .input
  | .query => .query
  | .candidate => .candidate
  | .scratch => .scratch
  | .count => .count

def extractContents (output : List Bool)
    (contents : (k : FrameExtraction.Stack) → List (FrameExtraction.Alphabet k)) :
    (k : Stack) → List (Alphabet k)
  | .input => contents .input
  | .query => contents .query
  | .candidate => contents .candidate
  | .scratch => contents .scratch
  | .count => contents .count
  | .output => output

@[simp] private theorem extractContents_apply (output : List Bool)
    (contents : (k : FrameExtraction.Stack) → List (FrameExtraction.Alphabet k))
    (k : FrameExtraction.Stack) :
    extractContents output contents (extractStack k) = contents k := by
  cases k <;> rfl

private theorem extractContents_update (output : List Bool)
    (contents : (k : FrameExtraction.Stack) → List (FrameExtraction.Alphabet k))
    (k : FrameExtraction.Stack) (value : List Bool) :
    Function.update (extractContents output contents) (extractStack k) value =
      extractContents output (Function.update contents k value) := by
  funext index
  cases k <;> cases index <;>
    simp [Function.update, extractContents, extractStack]

/-- Lift the checked extract statements to shared stacks and finite control. -/
def extractStmt : TM2.Stmt FrameExtraction.Alphabet FrameExtraction.Label FrameExtraction.State →
    TM2.Stmt Alphabet Label State
  | .push k write next =>
      .push (extractStack k) (fun state => write state.1) (extractStmt next)
  | .peek k read next =>
      .peek (extractStack k)
        (fun state symbol => (read state.1 symbol, PreservingBinaryEquality.initialState)) (extractStmt next)
  | .pop k read next =>
      .pop (extractStack k)
        (fun state symbol => (read state.1 symbol, PreservingBinaryEquality.initialState)) (extractStmt next)
  | .load update next =>
      .load (fun state => (update state.1, PreservingBinaryEquality.initialState)) (extractStmt next)
  | .branch test yes no =>
      .branch (fun state => test state.1) (extractStmt yes) (extractStmt no)
  | .goto next => .goto (fun state => .extract (next state.1))
  | .halt => .load (fun _ => initialState) (.goto fun _ => .compare .scan)

def compareStack : PreservingBinaryEquality.Stack → Stack
  | .query => .query
  | .candidate => .candidate
  | .scratch => .scratch
  | .output => .output

def compareContents (input count : List Bool)
    (contents : (k : PreservingBinaryEquality.Stack) → List (PreservingBinaryEquality.Alphabet k)) :
    (k : Stack) → List (Alphabet k)
  | .input => input
  | .query => contents .query
  | .candidate => contents .candidate
  | .scratch => contents .scratch
  | .count => count
  | .output => contents .output

@[simp] private theorem compareContents_apply (input count : List Bool)
    (contents : (k : PreservingBinaryEquality.Stack) → List (PreservingBinaryEquality.Alphabet k))
    (k : PreservingBinaryEquality.Stack) :
    compareContents input count contents (compareStack k) = contents k := by
  cases k <;> rfl

private theorem compareContents_update (input count : List Bool)
    (contents : (k : PreservingBinaryEquality.Stack) → List (PreservingBinaryEquality.Alphabet k))
    (k : PreservingBinaryEquality.Stack) (value : List Bool) :
    Function.update (compareContents input count contents) (compareStack k) value =
      compareContents input count (Function.update contents k value) := by
  funext index
  cases k <;> cases index <;>
    simp [Function.update, compareContents, compareStack]

/-- Lift the checked compare statements to shared stacks and finite control. -/
def compareStmt : TM2.Stmt PreservingBinaryEquality.Alphabet PreservingBinaryEquality.Label PreservingBinaryEquality.State →
    TM2.Stmt Alphabet Label State
  | .push k write next =>
      .push (compareStack k) (fun state => write state.2) (compareStmt next)
  | .peek k read next =>
      .peek (compareStack k)
        (fun state symbol => (none, read state.2 symbol)) (compareStmt next)
  | .pop k read next =>
      .pop (compareStack k)
        (fun state symbol => (none, read state.2 symbol)) (compareStmt next)
  | .load update next =>
      .load (fun state => (none, update state.2)) (compareStmt next)
  | .branch test yes no =>
      .branch (fun state => test state.2) (compareStmt yes) (compareStmt no)
  | .goto next => .goto (fun state => .compare (next state.2))
  | .halt => .halt

/-- Total dispatcher; extraction's final step enters comparison directly. -/
def program : Label → TM2.Stmt Alphabet Label State
  | .extract label => extractStmt (FrameExtraction.program label)
  | .compare label => compareStmt (PreservingBinaryEquality.program label)

def computer : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .output
  Γ := Alphabet
  Λ := Label
  main := .extract .prefix
  σ := State
  initialState := initialState
  Γk₀Fin := Bool.fintype
  m := program

def stackContents (input query candidate scratch count output : List Bool) :
    (k : Stack) → List (Alphabet k)
  | .input => input
  | .query => query
  | .candidate => candidate
  | .scratch => scratch
  | .count => count
  | .output => output

def cfg (label : Option Label) (state : State)
    (input query candidate scratch count output : List Bool) : computer.Cfg where
  l := label
  var := state
  stk := stackContents input query candidate scratch count output

/-- A reached extraction halt denotes the live comparison entry. -/
def extractCfg (output : List Bool) (c : FrameExtraction.computer.Cfg) : computer.Cfg where
  l := some (c.l.elim (.compare .scan) Label.extract)
  var := c.l.elim initialState (fun _ => (c.var, PreservingBinaryEquality.initialState))
  stk := extractContents output c.stk

/-- Comparison preserves the unread input and counter stack. -/
def compareCfg (input count : List Bool)
    (c : PreservingBinaryEquality.computer.Cfg) : computer.Cfg where
  l := c.l.map Label.compare
  var := (none, c.var)
  stk := compareContents input count c.stk

/-- Statement execution preserves the embedding, including its halt behavior. -/
theorem extract_stepAux
    (stmt : TM2.Stmt FrameExtraction.Alphabet FrameExtraction.Label FrameExtraction.State)
    (state : FrameExtraction.State)
    (contents : (k : FrameExtraction.Stack) → List (FrameExtraction.Alphabet k)) (output : List Bool) :
    TM2.stepAux (extractStmt stmt) (state, PreservingBinaryEquality.initialState) (extractContents output contents) =
      extractCfg output (TM2.stepAux stmt state contents) := by
  induction stmt generalizing state contents with
  | push k write next ih =>
      simp only [extractStmt, TM2.stepAux, extractContents_apply]
      rw [extractContents_update]
      exact ih _ _
  | peek k read next ih =>
      simpa only [extractStmt, TM2.stepAux, extractContents_apply] using
        ih (read state (contents k).head?) contents
  | pop k read next ih =>
      simp only [extractStmt, TM2.stepAux, extractContents_apply]
      rw [extractContents_update]
      exact ih _ _
  | load update next ih =>
      simpa only [extractStmt, TM2.stepAux] using ih (update state) contents
  | branch test yes no ihYes ihNo =>
      cases h : test state
      · simpa only [extractStmt, TM2.stepAux, h, Bool.false_eq_true, cond_false] using
          ihNo state contents
      · simpa only [extractStmt, TM2.stepAux, h, cond_true] using ihYes state contents
  | goto next => rfl
  | halt => rfl

private theorem extract_step (label : FrameExtraction.Label) (state : FrameExtraction.State)
    (contents : (k : FrameExtraction.Stack) → List (FrameExtraction.Alphabet k)) (output : List Bool) :
    computer.step (extractCfg output ⟨some label, state, contents⟩) =
      some (extractCfg output (TM2.stepAux (FrameExtraction.program label) state contents)) := by
  change some (TM2.stepAux (extractStmt (FrameExtraction.program label))
    (state, PreservingBinaryEquality.initialState) (extractContents output contents)) = _
  rw [extract_stepAux]

/-- Statement execution preserves the embedding, including its halt behavior. -/
theorem compare_stepAux
    (stmt : TM2.Stmt PreservingBinaryEquality.Alphabet PreservingBinaryEquality.Label PreservingBinaryEquality.State)
    (state : PreservingBinaryEquality.State)
    (contents : (k : PreservingBinaryEquality.Stack) → List (PreservingBinaryEquality.Alphabet k)) (input count : List Bool) :
    TM2.stepAux (compareStmt stmt) (none, state) (compareContents input count contents) =
      compareCfg input count (TM2.stepAux stmt state contents) := by
  induction stmt generalizing state contents with
  | push k write next ih =>
      simp only [compareStmt, TM2.stepAux, compareContents_apply]
      rw [compareContents_update]
      exact ih _ _
  | peek k read next ih =>
      simpa only [compareStmt, TM2.stepAux, compareContents_apply] using
        ih (read state (contents k).head?) contents
  | pop k read next ih =>
      simp only [compareStmt, TM2.stepAux, compareContents_apply]
      rw [compareContents_update]
      exact ih _ _
  | load update next ih =>
      simpa only [compareStmt, TM2.stepAux] using ih (update state) contents
  | branch test yes no ihYes ihNo =>
      cases h : test state
      · simpa only [compareStmt, TM2.stepAux, h, Bool.false_eq_true, cond_false] using
          ihNo state contents
      · simpa only [compareStmt, TM2.stepAux, h, cond_true] using ihYes state contents
  | goto next => rfl
  | halt => rfl

private theorem compare_step (label : PreservingBinaryEquality.Label) (state : PreservingBinaryEquality.State)
    (contents : (k : PreservingBinaryEquality.Stack) → List (PreservingBinaryEquality.Alphabet k)) (input count : List Bool) :
    computer.step (compareCfg input count ⟨some label, state, contents⟩) =
      some (compareCfg input count (TM2.stepAux (PreservingBinaryEquality.program label) state contents)) := by
  change some (TM2.stepAux (compareStmt (PreservingBinaryEquality.program label))
    (none, state) (compareContents input count contents)) = _
  rw [compare_stepAux]

private theorem iterate_bind_none {α : Type} (step : α → Option α) (n : Nat) :
    (fun c => c.bind step)^[n] none = none := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply]; exact ih

/-- Lift any exact finite extract run with unchanged step count. -/
theorem extract_run (n : Nat) (start finish : FrameExtraction.computer.Cfg) (output : List Bool)
    (run : (fun c => c.bind FrameExtraction.computer.step)^[n] (some start) = some finish) :
    (fun c => c.bind computer.step)^[n] (some (extractCfg output start)) =
      some (extractCfg output finish) := by
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
          rw [Option.bind_some, extract_step]
          exact ih _ run

/-- Lift any exact finite compare run with unchanged step count. -/
theorem compare_run (n : Nat) (start finish : PreservingBinaryEquality.computer.Cfg) (input count : List Bool)
    (run : (fun c => c.bind PreservingBinaryEquality.computer.step)^[n] (some start) = some finish) :
    (fun c => c.bind computer.step)^[n] (some (compareCfg input count start)) =
      some (compareCfg input count finish) := by
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
          rw [Option.bind_some, compare_step]
          exact ih _ run

/-- Ordered extraction followed by query-preserving equality. Arbitrary input
and output suffixes survive, and both work stacks and the candidate end empty. -/
theorem whole_frame (query bits input output : List Bool) :
    (fun c => c.bind computer.step)^[
        3 * bits.length + max query.length bits.length + query.length + 5]
      (some (cfg (some (.extract .prefix)) initialState
        (BinaryNatLists.frame bits ++ input) query [] [] [] output)) =
      some (cfg none initialState input query [] [] [] (decide (query = bits) :: output)) := by
  have extraction := extract_run _ _ _ output
    (FrameExtraction.whole_frame bits input query [])
  have comparison := compare_run _ _ _ input []
    (PreservingBinaryEquality.whole_list query bits output)
  simp only [List.append_nil] at extraction
  change (fun c => c.bind computer.step)^[3 * bits.length + 3]
    (some (cfg (some (.extract .prefix)) initialState
      (BinaryNatLists.frame bits ++ input) query [] [] [] output)) =
    some (cfg (some (.compare .scan)) initialState input query bits [] [] output) at extraction
  change (fun c => c.bind computer.step)^[max query.length bits.length + query.length + 2]
    (some (cfg (some (.compare .scan)) initialState input query bits [] [] output)) =
    some (cfg none initialState input query [] [] [] (decide (query = bits) :: output)) at comparison
  rw [show 3 * bits.length + max query.length bits.length + query.length + 5 =
    (max query.length bits.length + query.length + 2) + (3 * bits.length + 3) by omega,
    Function.iterate_add_apply, extraction, comparison]

/-- A linear bound in query bits and the consumed frame length. -/
def evalsToInTime (query bits input output : List Bool) :
    EvalsToInTime computer.step
      (cfg (some (.extract .prefix)) initialState
        (BinaryNatLists.frame bits ++ input) query [] [] [] output)
      (some (cfg none initialState input query [] [] [] (decide (query = bits) :: output)))
      (2 * query.length + 2 * (BinaryNatLists.frame bits).length + 3) where
  steps := 3 * bits.length + max query.length bits.length + query.length + 5
  evals_in_steps := whole_frame query bits input output
  steps_le_m := by rw [BinaryNatLists.frame_length]; omega

/-- A framed canonical natural is compared with a preloaded canonical query. -/
theorem natural_run (query candidate : Nat) (input output : List Bool) :
    (fun c => c.bind computer.step)^[
        3 * (encodeNat candidate).length +
          max (encodeNat query).length (encodeNat candidate).length + (encodeNat query).length + 5]
      (some (cfg (some (.extract .prefix)) initialState
        (BinaryNatLists.encodeNat candidate ++ input) (encodeNat query) [] [] [] output)) =
      some (cfg none initialState input (encodeNat query) [] [] []
        (decide (query = candidate) :: output)) := by
  simpa only [BinaryEquality.encodeNat_eq_iff] using
    whole_frame (encodeNat query) (encodeNat candidate) input output

/-- Runtime uses encoded bit lengths, independent of the unread suffix. -/
def natural_evalsToInTime (query candidate : Nat) (input output : List Bool) :
    EvalsToInTime computer.step
      (cfg (some (.extract .prefix)) initialState
        (BinaryNatLists.encodeNat candidate ++ input) (encodeNat query) [] [] [] output)
      (some (cfg none initialState input (encodeNat query) [] [] []
        (decide (query = candidate) :: output)))
      (2 * (encodeNat query).length + 2 * BinaryNatLists.natWireSize candidate + 3) := by
  simpa only [BinaryNatLists.encodeNat, BinaryNatLists.natWireSize,
    BinaryNatLists.frame_length, BinaryEquality.encodeNat_eq_iff] using
    evalsToInTime (encodeNat query) (encodeNat candidate) input output

end LeanNPHardness.MachinePrimitives.FrameComparison
