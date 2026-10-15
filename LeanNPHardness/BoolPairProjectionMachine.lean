import LeanNPHardness.BooleanListMachine
import LeanNPHardness.PairEncoding

/-!
# Projecting a Boolean paired with a Boolean list

A two-stack finite machine reads a tagged pair encoding `inl b :: bits.map inr`,
stores `b` in finite control, drains the remaining certificate symbols, and
emits `b`. This is the machine behind regarding a polynomial-time decider as a
verifier that ignores its string certificate. The exact run takes
`bits.length + 2` steps, bounded by the input length plus one.
-/

namespace LeanNPHardness.MachinePrimitives.BoolPairFirst

open Computability Turing StateTransition

inductive Stack
  | input
  | output
  deriving DecidableEq, Fintype

inductive Label
  | start
  | drain
  deriving DecidableEq, Fintype

/-- Finite control stores the projected Boolean and whether the last pop
observed a symbol. -/
structure State where
  stored : Option Bool
  observed : Bool
  deriving DecidableEq, Fintype

def Alphabet : Stack → Type
  | .input => Sum Bool Bool
  | .output => Bool

def initialState : State := ⟨none, false⟩

def storeFirst (state : State) : Option (Sum Bool Bool) → State
  | some (Sum.inl b) => ⟨some b, true⟩
  | some (Sum.inr _) => ⟨state.stored, true⟩
  | none => ⟨state.stored, false⟩

def observe (state : State) (symbol : Option (Sum Bool Bool)) : State :=
  ⟨state.stored, symbol.isSome⟩

def program : Label → TM2.Stmt Alphabet Label State
  | .start => .pop .input storeFirst (.goto fun _ => .drain)
  | .drain =>
      .pop .input observe <|
        .branch (fun state => state.observed)
          (.goto fun _ => .drain)
          (.push .output (fun state => state.stored.getD false) <|
            .load (fun _ => initialState) .halt)

def computer : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .output
  Γ := Alphabet
  Λ := Label
  main := .start
  σ := State
  initialState := initialState
  Γk₀Fin := inferInstanceAs (Fintype (Sum Bool Bool))
  m := program

private def stackContents (input : List (Sum Bool Bool)) (output : List Bool) :
    (index : Stack) → List (Alphabet index)
  | .input => input
  | .output => output

private def cfg (label : Option Label) (state : State)
    (input : List (Sum Bool Bool)) (output : List Bool) : computer.Cfg where
  l := label
  var := state
  stk := stackContents input output

private theorem start_step (b : Bool) (rest : List (Sum Bool Bool)) (output : List Bool)
    (state : State) :
    computer.step (cfg (some .start) state (Sum.inl b :: rest) output) =
      some (cfg (some .drain) ⟨some b, true⟩ rest output) := by
  simp [computer, FinTM2.step, cfg, program, stackContents, storeFirst]
  funext index
  cases index <;> rfl

private theorem drain_step_cons (b : Bool) (x : Bool) (rest : List (Sum Bool Bool))
    (output : List Bool) (observed : Bool) :
    computer.step (cfg (some .drain) ⟨some b, observed⟩ (Sum.inr x :: rest) output) =
      some (cfg (some .drain) ⟨some b, true⟩ rest output) := by
  simp [computer, FinTM2.step, cfg, program, stackContents, observe, Function.update]
  funext index
  cases index <;> rfl

private theorem drain_step_nil (b : Bool) (output : List Bool) (observed : Bool) :
    computer.step (cfg (some .drain) ⟨some b, observed⟩ [] output) =
      some (cfg none initialState [] (b :: output)) := by
  simp [computer, FinTM2.step, cfg, program, stackContents, observe, initialState,
    Function.update]
  funext index
  cases index <;> rfl

private theorem drain_run (b : Bool) (bits : List Bool) (output : List Bool) (observed : Bool) :
    (flip Option.bind computer.step)^[bits.length + 1]
        (some (cfg (some .drain) ⟨some b, observed⟩ (bits.map Sum.inr) output)) =
      some (cfg none initialState [] (b :: output)) := by
  induction bits generalizing observed with
  | nil =>
      simp only [List.map_nil, List.length_nil, Nat.zero_add, Function.iterate_one]
      change computer.step (cfg (some .drain) ⟨some b, observed⟩ [] output) = _
      exact drain_step_nil b output observed
  | cons x rest ih =>
      rw [List.map_cons, List.length_cons, Nat.add_right_comm, Function.iterate_succ_apply]
      change (flip Option.bind computer.step)^[rest.length + 1]
        (computer.step (cfg (some .drain) ⟨some b, observed⟩ (Sum.inr x :: rest.map Sum.inr) output)) = _
      rw [drain_step_cons]
      exact ih true

private theorem initList_eq (b : Bool) (bits : List Bool) :
    initList computer (Sum.inl b :: bits.map Sum.inr) =
      cfg (some .start) initialState (Sum.inl b :: bits.map Sum.inr) [] := by
  unfold initList cfg
  congr
  funext index
  cases index <;> rfl

private theorem haltList_eq (b : Bool) :
    haltList computer [b] = cfg none initialState [] [b] := by
  unfold haltList cfg
  congr
  funext index
  cases index <;> rfl

/-- Exact projection run in `bits.length + 2` steps. -/
def outputsInTime (b : Bool) (bits : List Bool) :
    TM2OutputsInTime computer (Sum.inl b :: bits.map Sum.inr) (some [b]) (bits.length + 2) where
  steps := bits.length + 2
  evals_in_steps := by
    rw [initList_eq]
    simp only [Option.map_some]
    rw [haltList_eq]
    rw [show bits.length + 2 = (bits.length + 1) + 1 by omega, Function.iterate_succ_apply]
    change (flip Option.bind computer.step)^[bits.length + 1]
      (computer.step (cfg (some .start) initialState (Sum.inl b :: bits.map Sum.inr) [])) = _
    rw [start_step]
    exact drain_run b bits [] true
  steps_le_m := le_rfl

/-- The first component of a Boolean paired with a Boolean list is computable
in linear time. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime
      (PairEncoding.finEncoding finEncodingBoolBool RawBoolList.finEncoding)
      finEncodingBoolBool (fun pair => pair.1) where
  tm := computer
  inputAlphabet := Equiv.refl (Sum Bool Bool)
  outputAlphabet := Equiv.refl Bool
  time := Polynomial.X + 1
  outputsFun pair := by
    rcases pair with ⟨b, bits⟩
    have run := outputsInTime b bits
    simp only [PairEncoding.finEncoding_encode, finEncodingBoolBool, encodeBool,
      RawBoolList.finEncoding, Equiv.refl, Equiv.invFun_as_coe, Equiv.coe_fn_symm_mk,
      Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
    simpa [Nat.add_assoc] using run

end LeanNPHardness.MachinePrimitives.BoolPairFirst
