import LeanNPHardness.MachineRun

/-!
# Equality of independently supplied binary words

A finite TM2 kernel consumes words from two Boolean stacks, compares their
symbols (including exhaustion), and pushes one result onto a third stack.
It takes exactly `max left.length right.length + 1` TM2 steps. Inputs are
already on separate stacks; serialized-pair loading and certificate traversal
are separate obligations. Natural equality uses mathlib's canonical binary
encoding, without an aligned-pair encoding or a maximum-variable bound.
-/

namespace LeanNPHardness.MachinePrimitives.BinaryEquality

open Computability Turing

inductive Stack
  | left
  | right
  | output
  deriving DecidableEq, Fintype

inductive Label
  | scan
  deriving DecidableEq, Fintype

/-- All remembered symbols and the accumulated equality flag are finite. -/
structure State where
  left : Option Bool
  right : Option Bool
  equal : Bool
  deriving DecidableEq, Fintype

def initialState : State := ⟨none, none, true⟩

def Alphabet (_ : Stack) : Type := Bool

private def observeLeft (state : State) (symbol : Option Bool) : State :=
  { state with left := symbol }

private def observeRight (state : State) (symbol : Option Bool) : State :=
  { state with right := symbol, equal := state.equal && decide (state.left = symbol) }

/-- Exhaust both stacks even after a mismatch, so the output configuration has
empty work stacks and a runtime independent of the mismatch position. -/
def program : Label → TM2.Stmt Alphabet Label State
  | .scan =>
      .pop .left observeLeft <|
        .pop .right observeRight <|
          .branch (fun state => state.left.isSome || state.right.isSome)
            (.goto fun _ => .scan)
            (.push .output (fun state => state.equal) <|
              .load (fun _ => initialState) .halt)

def computer : FinTM2 where
  K := Stack
  k₀ := .left
  k₁ := .output
  Γ := Alphabet
  Λ := Label
  main := .scan
  σ := State
  initialState := initialState
  Γk₀Fin := Bool.fintype
  m := program

def stackContents (left right output : List Bool) : (index : Stack) → List (Alphabet index)
  | .left => left
  | .right => right
  | .output => output

def cfg (label : Option Label) (state : State) (left right output : List Bool) :
    computer.Cfg where
  l := label
  var := state
  stk := stackContents left right output

private theorem step_nil_nil (state : State) (output : List Bool) :
    computer.step (cfg (some .scan) state [] [] output) =
      some (cfg none initialState [] [] (state.equal :: output)) := by
  rcases state with ⟨left, right, equal⟩
  simp [computer, FinTM2.step, cfg, program, stackContents, Alphabet,
    observeLeft, observeRight, Function.update]
  funext index
  cases index <;> rfl

private theorem step_cons_nil (state : State) (bit : Bool) (left output : List Bool) :
    computer.step (cfg (some .scan) state (bit :: left) [] output) =
      some (cfg (some .scan) ⟨some bit, none, false⟩ left [] output) := by
  rcases state with ⟨previousLeft, previousRight, equal⟩
  simp [computer, FinTM2.step, cfg, program, stackContents, Alphabet,
    observeLeft, observeRight, Function.update]
  funext index
  cases index <;> rfl

private theorem step_nil_cons (state : State) (bit : Bool) (right output : List Bool) :
    computer.step (cfg (some .scan) state [] (bit :: right) output) =
      some (cfg (some .scan) ⟨none, some bit, false⟩ [] right output) := by
  rcases state with ⟨previousLeft, previousRight, equal⟩
  simp [computer, FinTM2.step, cfg, program, stackContents, Alphabet,
    observeLeft, observeRight, Function.update]
  funext index
  cases index <;> rfl

private theorem step_cons_cons (state : State) (a b : Bool)
    (left right output : List Bool) :
    computer.step (cfg (some .scan) state (a :: left) (b :: right) output) =
      some (cfg (some .scan)
        ⟨some a, some b, state.equal && decide (a = b)⟩ left right output) := by
  rcases state with ⟨previousLeft, previousRight, equal⟩
  simp [computer, FinTM2.step, cfg, program, stackContents, Alphabet,
    observeLeft, observeRight, Function.update]
  funext index
  cases index <;> rfl

/-- Exact execution from arbitrary finite control and output suffix. The
previously accumulated flag is conjoined with equality of the remaining words. -/
theorem scan_run (left right output : List Bool) (state : State) :
    (fun c => c.bind computer.step)^[max left.length right.length + 1]
        (some (cfg (some .scan) state left right output)) =
      some (cfg none initialState [] []
        ((state.equal && decide (left = right)) :: output)) := by
  induction left generalizing right state with
  | nil =>
      induction right generalizing state with
      | nil =>
          simpa only [List.length_nil, Nat.zero_max, Nat.zero_add,
            Function.iterate_one, Option.bind_some, decide_true, Bool.and_true] using
            step_nil_nil state output
      | cons bit right ih =>
          simp only [List.length_nil, List.length_cons, Nat.zero_max]
          rw [Function.iterate_succ_apply, Option.bind_some, step_nil_cons]
          simpa using ih ⟨none, some bit, false⟩
  | cons a left ih =>
      cases right with
      | nil =>
          simp only [List.length_nil, List.length_cons, Nat.max_zero]
          rw [Function.iterate_succ_apply, Option.bind_some, step_cons_nil]
          simpa using ih [] ⟨some a, none, false⟩
      | cons b right =>
          simp only [List.length_cons, Nat.succ_max_succ]
          rw [Function.iterate_succ_apply, Option.bind_some, step_cons_cons]
          simpa [Bool.and_assoc] using
            ih right ⟨some a, some b, state.equal && decide (a = b)⟩

/-- Equality of two independently supplied words, with empty input stacks and
the initial finite state restored at the end. -/
theorem whole_list (left right output : List Bool) :
    (fun c => c.bind computer.step)^[max left.length right.length + 1]
        (some (cfg (some .scan) initialState left right output)) =
      some (cfg none initialState [] [] (decide (left = right) :: output)) := by
  simpa [initialState] using scan_run left right output initialState

/-- The runtime bound uses the sum of actual supplied bit lengths. -/
def evalsToInTime (left right output : List Bool) :
    EvalsToInTime computer.step
      (cfg (some .scan) initialState left right output)
      (some (cfg none initialState [] [] (decide (left = right) :: output)))
      (left.length + right.length + 1) where
  steps := max left.length right.length + 1
  evals_in_steps := whole_list left right output
  steps_le_m := by omega

/-- Canonical binary words are equal exactly when their natural numbers are. -/
theorem encodeNat_eq_iff (left right : Nat) :
    encodeNat left = encodeNat right ↔ left = right := by
  constructor
  · intro h
    simpa using congrArg decodeNat h
  · exact congrArg encodeNat

/-- The same finite kernel computes natural equality from separately supplied
canonical binary encodings, with an exact bit-length runtime. -/
theorem natural_run (left right : Nat) (output : List Bool) :
    (fun c => c.bind computer.step)^[max (encodeNat left).length (encodeNat right).length + 1]
        (some (cfg (some .scan) initialState (encodeNat left) (encodeNat right) output)) =
      some (cfg none initialState [] [] (decide (left = right) :: output)) := by
  simpa only [encodeNat_eq_iff] using whole_list (encodeNat left) (encodeNat right) output

/-- Natural equality is bounded by the total length of the two binary inputs
plus one; this starts from the explicit two-input configuration. -/
def natural_evalsToInTime (left right : Nat) (output : List Bool) :
    EvalsToInTime computer.step
      (cfg (some .scan) initialState (encodeNat left) (encodeNat right) output)
      (some (cfg none initialState [] [] (decide (left = right) :: output)))
      ((encodeNat left).length + (encodeNat right).length + 1) where
  steps := max (encodeNat left).length (encodeNat right).length + 1
  evals_in_steps := natural_run left right output
  steps_le_m := by omega

end LeanNPHardness.MachinePrimitives.BinaryEquality
