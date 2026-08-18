import LeanNPHardness.MachineCompositionExecution
import LeanNPHardness.MachineRuntimeBounds

namespace LeanNPHardness

open Computability Turing

namespace MachineRuntime

/-- A polynomial over natural-number coefficients is monotone on natural
inputs. This is the order fact needed to run a component polynomial at an
upper bound for its encoded input length. -/
theorem polynomial_eval_mono (p : Polynomial ℕ) : Monotone p.eval := by
  intro a b hab
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simpa only [Polynomial.eval_add] using Nat.add_le_add hp hq
  | monomial n coefficient =>
      simp only [Polynomial.eval_monomial]
      exact Nat.mul_le_mul_left coefficient (Nat.pow_le_pow_left hab n)

end MachineRuntime

namespace MachineComposition

/-- A polynomial upper bound for the encoded output length of a polynomial-
time machine. Its constant multiplier is the largest number of pushes that
one counted machine step can perform. -/
noncomputable def outputSizePolynomial {alpha beta : Type}
    (sourceEncoding : FinEncoding alpha)
    (targetEncoding : FinEncoding beta)
    (f : alpha → beta)
    (computer : TM2ComputableInPolyTime sourceEncoding targetEncoding f) :
    Polynomial ℕ :=
  Polynomial.X +
    computer.time * Polynomial.C (MachineRuntime.machinePushBound computer.tm)

@[simp]
theorem outputSizePolynomial_eval {alpha beta : Type}
    (sourceEncoding : FinEncoding alpha)
    (targetEncoding : FinEncoding beta)
    (f : alpha → beta)
    (computer : TM2ComputableInPolyTime sourceEncoding targetEncoding f)
    (n : ℕ) :
    (outputSizePolynomial sourceEncoding targetEncoding f computer).eval n =
      n + computer.time.eval n *
        MachineRuntime.machinePushBound computer.tm := by
  simp [outputSizePolynomial, Polynomial.eval_add, Polynomial.eval_mul]

/-- The polynomial runtime used by the sequential composition machine. It
adds the second machine's time at the first machine's output-size bound, the
linear transfer cost, and the first machine's time. -/
noncomputable def compositionTimePolynomial {alpha beta gamma : Type}
    (sourceEncoding : FinEncoding alpha)
    (middleEncoding : FinEncoding beta)
    (targetEncoding : FinEncoding gamma)
    (f : alpha → beta) (g : beta → gamma)
    (first : TM2ComputableInPolyTime sourceEncoding middleEncoding f)
    (second : TM2ComputableInPolyTime middleEncoding targetEncoding g) :
    Polynomial ℕ :=
  let size := outputSizePolynomial sourceEncoding middleEncoding f first
  second.time.comp size + Polynomial.C 4 * size + Polynomial.C 4 + first.time

@[simp]
theorem compositionTimePolynomial_eval {alpha beta gamma : Type}
    (sourceEncoding : FinEncoding alpha)
    (middleEncoding : FinEncoding beta)
    (targetEncoding : FinEncoding gamma)
    (f : alpha → beta) (g : beta → gamma)
    (first : TM2ComputableInPolyTime sourceEncoding middleEncoding f)
    (second : TM2ComputableInPolyTime middleEncoding targetEncoding g)
    (n : ℕ) :
    (compositionTimePolynomial sourceEncoding middleEncoding targetEncoding
        f g first second).eval n =
      second.time.eval
          (n + first.time.eval n *
            MachineRuntime.machinePushBound first.tm) +
        4 *
          (n + first.time.eval n *
            MachineRuntime.machinePushBound first.tm) +
        4 + first.time.eval n := by
  simp [compositionTimePolynomial, outputSizePolynomial,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_comp]

/-- Time-bounded canonical list-output witnesses compose through the concrete
sequential machine. The bound keeps the two supplied component bounds and the
exact linear cost of transferring the intermediate list separate. -/
def compositionMachine_outputsInTime {Γ₀ Γ₁ Γ₂ : Type}
    [Fintype Γ₁]
    (first : TM2ComputableAux Γ₀ Γ₁)
    (second : TM2ComputableAux Γ₁ Γ₂)
    (input : List (first.tm.Γ first.tm.k₀))
    (intermediate : List (first.tm.Γ first.tm.k₁))
    (output : List (second.tm.Γ second.tm.k₁))
    (firstTime secondTime : ℕ)
    (firstRun : TM2OutputsInTime first.tm input (some intermediate) firstTime)
    (secondRun : TM2OutputsInTime second.tm
      (intermediate.map (middleAlphabetEquiv first second))
      (some output) secondTime) :
    TM2OutputsInTime (compositionMachine first second) input (some output)
      (secondTime + (4 * intermediate.length + 4 + firstTime)) := by
  let liftedSecondRun : EvalsTo (TM2.step second.tm.m)
      (rightEntryMachineCfg first second
        (transferredContents first second (haltList first.tm intermediate).stk))
      (some (haltList second.tm output)) :=
    { steps := secondRun.steps
      evals_in_steps := by
        rw [rightEntryMachineCfg_transferred_haltList]
        exact secondRun.evals_in_steps }
  have complete := compositionProgram_complete_run first second
    (initList first.tm input) (haltList first.tm intermediate) first.tm.main
    firstRun.toEvalsTo rfl rfl (haltList second.tm output) liftedSecondRun
  have firstOutputLength :
      ((haltList first.tm intermediate).stk first.tm.k₁).length =
        intermediate.length := by
    simp [haltList]
  simp only [liftedSecondRun, firstOutputLength] at complete
  refine
    { steps := secondRun.steps +
        (4 * intermediate.length + 4 + firstRun.steps)
      evals_in_steps := ?_
      steps_le_m := ?_ }
  · rw [compositionMachine_initList]
    simpa [FinTM2.step, compositionMachine,
      rightPhaseCfg_haltList first second intermediate output] using
        complete
  · exact Nat.add_le_add secondRun.steps_le_m
      (Nat.add_le_add_left firstRun.steps_le_m
        (4 * intermediate.length + 4))

/-- Generic polynomial-time composition for mathlib's finite TM2 model,
proved using the concrete sequential machine, the checked output-size bound,
and the exact three-phase execution theorem. -/
noncomputable def compositionComputableInPolyTime {alpha beta gamma : Type}
    (sourceEncoding : FinEncoding alpha)
    (middleEncoding : FinEncoding beta)
    (targetEncoding : FinEncoding gamma)
    (f : alpha → beta) (g : beta → gamma)
    (first : TM2ComputableInPolyTime sourceEncoding middleEncoding f)
    (second : TM2ComputableInPolyTime middleEncoding targetEncoding g) :
    TM2ComputableInPolyTime sourceEncoding targetEncoding (g ∘ f) where
  toTM2ComputableAux :=
    compositionAux first.toTM2ComputableAux second.toTM2ComputableAux
  time := compositionTimePolynomial sourceEncoding middleEncoding
    targetEncoding f g first second
  outputsFun a := by
    let input := List.map first.inputAlphabet.invFun
      (sourceEncoding.encode a)
    let intermediate := List.map first.outputAlphabet.invFun
      (middleEncoding.encode (f a))
    let output := List.map second.outputAlphabet.invFun
      (targetEncoding.encode (g (f a)))
    let secondRun : TM2OutputsInTime second.tm
        (intermediate.map
          (middleAlphabetEquiv first.toTM2ComputableAux
            second.toTM2ComputableAux))
        (some output)
        (second.time.eval (middleEncoding.encode (f a)).length) := by
      dsimp only [intermediate, output]
      rw [map_outputAlphabet_invFun_middleAlphabetEquiv]
      exact second.outputsFun (f a)
    let composed := compositionMachine_outputsInTime
      first.toTM2ComputableAux second.toTM2ComputableAux
      input intermediate output
      (first.time.eval (sourceEncoding.encode a).length)
      (second.time.eval (middleEncoding.encode (f a)).length)
      (first.outputsFun a) secondRun
    refine
      { toEvalsTo := composed.toEvalsTo
        steps_le_m := composed.steps_le_m.trans ?_ }
    have intermediateLengthEq :
        intermediate.length = (middleEncoding.encode (f a)).length := by
      simp [intermediate]
    have intermediateLength :
        intermediate.length ≤
          (sourceEncoding.encode a).length +
            first.time.eval (sourceEncoding.encode a).length *
              MachineRuntime.machinePushBound first.tm := by
      simpa [intermediate] using
        MachineRuntime.computableInPolyTime_output_length_le
          sourceEncoding middleEncoding f first a
    have secondTimeMono :
        second.time.eval intermediate.length ≤
          second.time.eval
            ((sourceEncoding.encode a).length +
              first.time.eval (sourceEncoding.encode a).length *
                MachineRuntime.machinePushBound first.tm) :=
      MachineRuntime.polynomial_eval_mono second.time intermediateLength
    rw [compositionTimePolynomial_eval]
    rw [← intermediateLengthEq]
    omega

end MachineComposition

end LeanNPHardness
