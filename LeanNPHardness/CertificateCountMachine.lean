import LeanNPHardness.FrameExtractionMachine

/-!
# Retaining and testing a certificate's binary list count

This finite TM2 kernel extracts the outer framed binary count into a dedicated
`remaining` stack, preserving the query, candidate, output, and unread input.
A single peek then selects `empty` or `nonempty` without consuming the count.
The complete header-to-branch run takes exactly `3 * countBits.length + 4`
steps. These labels are continuation boundaries; their halt is not counted.

The contract assumes a complete frame and, for the zero test's natural-number
meaning, a canonical binary natural. No malformed-input rejection, count/body
consistency check, decrement, or certificate-membership loop is asserted.
-/

namespace LeanNPHardness.MachinePrimitives.CertificateCount

open Computability Turing

inductive Stack
  | input | query | remaining | candidate | scratch | count | output
  deriving DecidableEq, Fintype

inductive Label
  | extract (label : FrameExtraction.Label)
  | check | empty | nonempty
  deriving DecidableEq, Fintype

abbrev State := FrameExtraction.State

def Alphabet (_ : Stack) : Type := Bool

def extractStack : FrameExtraction.Stack → Stack
  | .input => .input
  | .query => .query
  | .candidate => .remaining
  | .scratch => .scratch
  | .count => .count

def extractContents (candidate output : List Bool)
    (contents : (k : FrameExtraction.Stack) → List (FrameExtraction.Alphabet k)) :
    (k : Stack) → List (Alphabet k)
  | .input => contents .input
  | .query => contents .query
  | .remaining => contents .candidate
  | .candidate => candidate
  | .scratch => contents .scratch
  | .count => contents .count
  | .output => output

@[simp] private theorem extractContents_apply (candidate output : List Bool)
    (contents : (k : FrameExtraction.Stack) → List (FrameExtraction.Alphabet k))
    (k : FrameExtraction.Stack) :
    extractContents candidate output contents (extractStack k) = contents k := by
  cases k <;> rfl

private theorem extractContents_update (candidate output : List Bool)
    (contents : (k : FrameExtraction.Stack) → List (FrameExtraction.Alphabet k))
    (k : FrameExtraction.Stack) (value : List Bool) :
    Function.update (extractContents candidate output contents) (extractStack k) value =
      extractContents candidate output (Function.update contents k value) := by
  funext index
  cases k <;> cases index <;>
    simp [Function.update, extractContents, extractStack]

/-- Reuse the checked extractor, directing its payload into `remaining` and
its reached halt into the count test in the same TM2 step. -/
def extractStmt : TM2.Stmt FrameExtraction.Alphabet FrameExtraction.Label State →
    TM2.Stmt Alphabet Label State
  | .push k write next => .push (extractStack k) write (extractStmt next)
  | .peek k read next => .peek (extractStack k) read (extractStmt next)
  | .pop k read next => .pop (extractStack k) read (extractStmt next)
  | .load update next => .load update (extractStmt next)
  | .branch test yes no => .branch test (extractStmt yes) (extractStmt no)
  | .goto next => .goto (fun state => .extract (next state))
  | .halt => .load (fun _ => none) (.goto fun _ => .check)

def program : Label → TM2.Stmt Alphabet Label State
  | .extract label => extractStmt (FrameExtraction.program label)
  | .check =>
      .peek .remaining (fun _ symbol => symbol) <|
        .branch Option.isSome
          (.load (fun _ => none) (.goto fun _ => .nonempty))
          (.load (fun _ => none) (.goto fun _ => .empty))
  | .empty => .halt
  | .nonempty => .halt

def computer : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .remaining
  Γ := Alphabet
  Λ := Label
  main := .extract .prefix
  σ := State
  initialState := none
  Γk₀Fin := Bool.fintype
  m := program

def stackContents (input query remaining candidate scratch count output : List Bool) :
    (k : Stack) → List (Alphabet k)
  | .input => input
  | .query => query
  | .remaining => remaining
  | .candidate => candidate
  | .scratch => scratch
  | .count => count
  | .output => output

def cfg (label : Option Label) (state : State)
    (input query remaining candidate scratch count output : List Bool) : computer.Cfg where
  l := label
  var := state
  stk := stackContents input query remaining candidate scratch count output

def extractCfg (candidate output : List Bool) (c : FrameExtraction.computer.Cfg) :
    computer.Cfg where
  l := some (c.l.elim .check Label.extract)
  var := c.l.elim none (fun _ => c.var)
  stk := extractContents candidate output c.stk

/-- All extractor statements preserve both private stacks. -/
theorem extract_stepAux
    (stmt : TM2.Stmt FrameExtraction.Alphabet FrameExtraction.Label State)
    (state : State)
    (contents : (k : FrameExtraction.Stack) → List (FrameExtraction.Alphabet k))
    (candidate output : List Bool) :
    TM2.stepAux (extractStmt stmt) state (extractContents candidate output contents) =
      extractCfg candidate output (TM2.stepAux stmt state contents) := by
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

private theorem extract_step (label : FrameExtraction.Label) (state : State)
    (contents : (k : FrameExtraction.Stack) → List (FrameExtraction.Alphabet k))
    (candidate output : List Bool) :
    computer.step (extractCfg candidate output ⟨some label, state, contents⟩) =
      some (extractCfg candidate output
        (TM2.stepAux (FrameExtraction.program label) state contents)) := by
  change some (TM2.stepAux (extractStmt (FrameExtraction.program label))
    state (extractContents candidate output contents)) = _
  rw [extract_stepAux]

private theorem iterate_bind_none {α : Type} (step : α → Option α) (n : Nat) :
    (fun c => c.bind step)^[n] none = none := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply]; exact ih

/-- Exact extraction runs lift without adding dispatcher steps. -/
theorem extract_run (n : Nat) (start finish : FrameExtraction.computer.Cfg)
    (candidate output : List Bool)
    (run : (fun c => c.bind FrameExtraction.computer.step)^[n] (some start) = some finish) :
    (fun c => c.bind computer.step)^[n] (some (extractCfg candidate output start)) =
      some (extractCfg candidate output finish) := by
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

/-- Load one complete frame into the initially empty remaining-count stack. -/
theorem whole_frame (bits input query candidate output : List Bool) :
    (fun c => c.bind computer.step)^[3 * bits.length + 3]
      (some (cfg (some (.extract .prefix)) none
        (BinaryNatLists.frame bits ++ input) query [] candidate [] [] output)) =
      some (cfg (some .check) none input query bits candidate [] [] output) := by
  have run := extract_run _ _ _ candidate output
    (FrameExtraction.whole_frame bits input query [])
  simpa only [List.append_nil] using run

/-- A non-destructive count test, independent of the bit at the stack head. -/
theorem check_step (state : State)
    (input query remaining candidate scratch count output : List Bool) :
    computer.step (cfg (some .check) state
      input query remaining candidate scratch count output) =
      some (cfg (some (if remaining = [] then .empty else .nonempty)) none
        input query remaining candidate scratch count output) := by
  cases remaining <;>
    simp [computer, FinTM2.step, cfg, program, stackContents, TM2.stepAux]

/-- The exact run includes extraction and the final non-destructive peek. -/
theorem checked_frame (bits input query candidate output : List Bool) :
    (fun c => c.bind computer.step)^[3 * bits.length + 4]
      (some (cfg (some (.extract .prefix)) none
        (BinaryNatLists.frame bits ++ input) query [] candidate [] [] output)) =
      some (cfg (some (if bits = [] then .empty else .nonempty)) none
        input query bits candidate [] [] output) := by
  rw [show 3 * bits.length + 4 = 1 + (3 * bits.length + 3) by omega,
    Function.iterate_add_apply, whole_frame, Function.iterate_one, Option.bind_some,
    check_step]

/-- Canonical binary zero is precisely the empty word. In particular a low
zero bit on a positive even number must still select the nonempty branch. -/
theorem encodeNat_eq_nil_iff (n : Nat) : encodeNat n = [] ↔ n = 0 := by
  constructor
  · intro h
    have decoded := congrArg decodeNat h
    rw [decode_encodeNat] at decoded
    exact decoded
  · rintro rfl
    simp [encodeNat, encodeNum]

/-- Load a canonical count and select the correct natural-number branch. -/
theorem natural_run (n : Nat) (input query candidate output : List Bool) :
    (fun c => c.bind computer.step)^[3 * (encodeNat n).length + 4]
      (some (cfg (some (.extract .prefix)) none
        (BinaryNatLists.encodeNat n ++ input) query [] candidate [] [] output)) =
      some (cfg (some (if n = 0 then .empty else .nonempty)) none
        input query (encodeNat n) candidate [] [] output) := by
  simpa only [encodeNat_eq_nil_iff] using
    checked_frame (encodeNat n) input query candidate output

/-- Runtime is linear in the consumed header bits, regardless of the body. -/
def natural_evalsToInTime (n : Nat) (input query candidate output : List Bool) :
    EvalsToInTime computer.step
      (cfg (some (.extract .prefix)) none
        (BinaryNatLists.encodeNat n ++ input) query [] candidate [] [] output)
      (some (cfg (some (if n = 0 then .empty else .nonempty)) none
        input query (encodeNat n) candidate [] [] output))
      (2 * BinaryNatLists.natWireSize n + 2) where
  steps := 3 * (encodeNat n).length + 4
  evals_in_steps := natural_run n input query candidate output
  steps_le_m := by simp only [BinaryNatLists.natWireSize]; omega

/-- Initialize traversal from the actual length-prefixed natural-list wire
format, retaining every framed element, including repetitions, and the suffix. -/
theorem list_run (xs : List Nat) (input query candidate output : List Bool) :
    (fun c => c.bind computer.step)^[3 * (encodeNat xs.length).length + 4]
      (some (cfg (some (.extract .prefix)) none
        (BinaryNatLists.encodeNatList xs ++ input) query [] candidate [] [] output)) =
      some (cfg (some (if xs = [] then .empty else .nonempty)) none
        (xs.flatMap BinaryNatLists.encodeNat ++ input) query (encodeNat xs.length)
        candidate [] [] output) := by
  simpa only [BinaryNatLists.encodeNatList, List.append_assoc, List.length_eq_zero_iff] using
    natural_run xs.length (xs.flatMap BinaryNatLists.encodeNat ++ input) query candidate output

/-- The list interface has a linear bound in the full encoded certificate
length. The exact count is still only the header-extraction and test cost. -/
def list_evalsToInTime (xs : List Nat) (input query candidate output : List Bool) :
    EvalsToInTime computer.step
      (cfg (some (.extract .prefix)) none
        (BinaryNatLists.encodeNatList xs ++ input) query [] candidate [] [] output)
      (some (cfg (some (if xs = [] then .empty else .nonempty)) none
        (xs.flatMap BinaryNatLists.encodeNat ++ input) query (encodeNat xs.length)
        candidate [] [] output))
      (2 * (BinaryNatLists.encodeNatList xs).length + 2) where
  steps := 3 * (encodeNat xs.length).length + 4
  evals_in_steps := list_run xs input query candidate output
  steps_le_m := by
    rw [BinaryNatLists.encodeNatList_length]
    simp only [BinaryNatLists.listWireSize, BinaryNatLists.natWireSize]
    omega

end LeanNPHardness.MachinePrimitives.CertificateCount
