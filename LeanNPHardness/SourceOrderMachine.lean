import LeanNPHardness.FramingMachine

/-!
Reusable encoding and machine components extracted from `phd-thesis-lean`
commit `84be78db5a287f9a40dcb549252063d6db67de73`. Runtime bounds retain
the original explicit finite-alphabet input encodings.
-/

namespace LeanNPHardness.MachinePrimitives

open Computability Turing
open LeanNPHardness.MachineComposition

inductive SourceOrderRawFieldStack
  | input
  | output
  deriving DecidableEq, Fintype

inductive SourceOrderRawFieldLabel
  | copy
  deriving DecidableEq, Fintype

/-- `none` means that the input stack was empty; `some none` is a field
delimiter and `some (some bit)` is a binary payload symbol. -/
abbrev SourceOrderRawFieldState := Option (Option Bool)

private def sourceOrderRawFieldPopped
    (_state : SourceOrderRawFieldState) (symbol : Option (Option Bool)) :
    SourceOrderRawFieldState :=
  symbol

private def sourceOrderRawFieldPresent : SourceOrderRawFieldState → Bool
  | some _ => true
  | none => false

private def sourceOrderRawFieldHeld : SourceOrderRawFieldState → Option Bool
  | some symbol => symbol
  | none => none

private def SourceOrderRawFieldAlphabet
    (_ : SourceOrderRawFieldStack) : Type :=
  Option Bool

/-- Reverse every raw input cell onto the output stack.  Because the source
encoding already reverses field order and field payloads for stack
consumption, this exposes the exact semantic source order. -/
def sourceOrderRawFieldProgram :
    SourceOrderRawFieldLabel →
      TM2.Stmt SourceOrderRawFieldAlphabet SourceOrderRawFieldLabel
        SourceOrderRawFieldState
  | .copy =>
      .pop .input sourceOrderRawFieldPopped <|
        .branch sourceOrderRawFieldPresent
          (.push .output sourceOrderRawFieldHeld <|
            .goto (fun _ => .copy))
          .halt

def sourceOrderRawFieldComputer : FinTM2 where
  K := SourceOrderRawFieldStack
  k₀ := .input
  k₁ := .output
  Γ := SourceOrderRawFieldAlphabet
  Λ := SourceOrderRawFieldLabel
  main := .copy
  σ := SourceOrderRawFieldState
  initialState := none
  Γk₀Fin := show Fintype (Option Bool) from inferInstance
  m := sourceOrderRawFieldProgram

private def sourceOrderRawFieldStackContents
    (input output : List (Option Bool)) :
    (index : SourceOrderRawFieldStack) →
      List (SourceOrderRawFieldAlphabet index)
  | .input => input
  | .output => output

private def sourceOrderRawFieldCfg
    (label : Option SourceOrderRawFieldLabel)
    (state : SourceOrderRawFieldState)
    (input output : List (Option Bool)) :
    sourceOrderRawFieldComputer.Cfg where
  l := label
  var := state
  stk := sourceOrderRawFieldStackContents input output

private theorem sourceOrderRawField_step_cons (symbol : Option Bool)
    (input output : List (Option Bool))
    (state : SourceOrderRawFieldState) :
    sourceOrderRawFieldComputer.step
        (sourceOrderRawFieldCfg (some .copy) state
          (symbol :: input) output) =
      some (sourceOrderRawFieldCfg (some .copy) (some symbol)
        input (symbol :: output)) := by
  simp [sourceOrderRawFieldComputer, FinTM2.step,
    sourceOrderRawFieldCfg, sourceOrderRawFieldProgram,
    sourceOrderRawFieldStackContents, SourceOrderRawFieldAlphabet,
    sourceOrderRawFieldPopped, sourceOrderRawFieldPresent,
    sourceOrderRawFieldHeld, Function.update]
  funext index
  cases index <;> rfl

private theorem sourceOrderRawField_step_nil
    (output : List (Option Bool)) (state : SourceOrderRawFieldState) :
    sourceOrderRawFieldComputer.step
        (sourceOrderRawFieldCfg (some .copy) state [] output) =
      some (sourceOrderRawFieldCfg none none [] output) := by
  simp [sourceOrderRawFieldComputer, FinTM2.step,
    sourceOrderRawFieldCfg, sourceOrderRawFieldProgram,
    sourceOrderRawFieldStackContents, SourceOrderRawFieldAlphabet,
    sourceOrderRawFieldPopped, sourceOrderRawFieldPresent]

private def sourceOrderRawFieldEvalsToInTimeOne
    {start finish : sourceOrderRawFieldComputer.Cfg}
    (hstep : sourceOrderRawFieldComputer.step start = some finish) :
    EvalsToInTime sourceOrderRawFieldComputer.step
      start (some finish) 1 where
  steps := 1
  evals_in_steps := by
    simpa [Function.iterate_one] using hstep
  steps_le_m := Nat.le_refl 1

private def sourceOrderRawField_copy_evals
    (input output : List (Option Bool))
    (state : SourceOrderRawFieldState) :
    EvalsToInTime sourceOrderRawFieldComputer.step
      (sourceOrderRawFieldCfg (some .copy) state input output)
      (some (sourceOrderRawFieldCfg none none []
        (input.reverse ++ output)))
      (input.length + 1) := by
  induction input generalizing output state with
  | nil =>
      simpa using sourceOrderRawFieldEvalsToInTimeOne
        (sourceOrderRawField_step_nil output state)
  | cons symbol input ih =>
      let middle := sourceOrderRawFieldCfg (some .copy) (some symbol)
        input (symbol :: output)
      have hone : EvalsToInTime sourceOrderRawFieldComputer.step
          (sourceOrderRawFieldCfg (some .copy) state
            (symbol :: input) output)
          (some middle) 1 :=
        sourceOrderRawFieldEvalsToInTimeOne (by
          simpa [middle] using sourceOrderRawField_step_cons
            symbol input output state)
      have hrest := ih (symbol :: output) (some symbol)
      have hall := EvalsToInTime.trans sourceOrderRawFieldComputer.step
        1 (input.length + 1)
        (sourceOrderRawFieldCfg (some .copy) state
          (symbol :: input) output)
        middle
        (some (sourceOrderRawFieldCfg none none []
          ((symbol :: input).reverse ++ output)))
        hone
        (by
          simpa [middle, List.reverse_cons, List.append_assoc] using hrest)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hall

private theorem sourceOrderRawField_initList_eq_cfg
    (input : List (Option Bool)) :
    initList sourceOrderRawFieldComputer input =
      sourceOrderRawFieldCfg (some .copy) none input [] := by
  unfold initList sourceOrderRawFieldCfg
  congr
  funext index
  cases index <;> rfl

private theorem sourceOrderRawField_haltList_eq_cfg
    (output : List (Option Bool)) :
    haltList sourceOrderRawFieldComputer output =
      sourceOrderRawFieldCfg none none [] output := by
  unfold haltList sourceOrderRawFieldCfg
  congr
  funext index
  cases index <;> rfl

/-- Whole-stream reversal emits the checked source-order encoding in exactly
one more step than the raw input length. -/
def sourceOrderRawFields_outputsInTime (xss : List (List ℕ)) :
    TM2OutputsInTime sourceOrderRawFieldComputer
      (RawNatLists.encode xss)
      (some (SourceOrderRawNatLists.encode xss))
      ((RawNatLists.encode xss).length + 1) := by
  have hrun := sourceOrderRawField_copy_evals
    (RawNatLists.encode xss) [] none
  rw [TM2OutputsInTime, sourceOrderRawField_initList_eq_cfg]
  simp only [Option.map_some]
  rw [sourceOrderRawField_haltList_eq_cfg]
  simpa [SourceOrderRawNatLists.encode] using hrun

/-- A genuine linear-time encoding change from stack-oriented reverse fields
to semantic source-order fields. -/
noncomputable def sourceOrderRawFieldsComputableInPolyTime :
    @TM2ComputableInPolyTime (List (List ℕ)) (List (List ℕ))
      RawNatLists.finEncoding SourceOrderRawNatLists.finEncoding id where
  tm := sourceOrderRawFieldComputer
  inputAlphabet := Equiv.refl (Option Bool)
  outputAlphabet := Equiv.refl (Option Bool)
  time := Polynomial.X + 1
  outputsFun xss := by
    simpa [RawNatLists.finEncoding, SourceOrderRawNatLists.finEncoding,
      Equiv.refl, Polynomial.eval_add, Polynomial.eval_one,
      Polynomial.eval_X] using sourceOrderRawFields_outputsInTime xss


end LeanNPHardness.MachinePrimitives
