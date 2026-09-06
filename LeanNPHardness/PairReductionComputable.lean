import LeanNPHardness.PairReductionMachine
import LeanNPHardness.MachineCompositionRuntime

namespace LeanNPHardness.MachineAdapters

open Computability Turing

/-- The checked pair-left machine computes `(a, c) ↦ (f a, c)` under the
canonical tagged pair encodings. Runtime bounds are supplied separately. -/
def pairReductionComputable {α β certificate : Type}
    (sourceEncoding : FinEncoding α) (targetEncoding : FinEncoding β)
    (certificateEncoding : FinEncoding certificate) (f : α → β)
    (computer : TM2Computable sourceEncoding targetEncoding f) :
    TM2Computable (PairEncoding.finEncoding sourceEncoding certificateEncoding)
      (PairEncoding.finEncoding targetEncoding certificateEncoding)
      (fun pair => (f pair.1, pair.2)) where
  toTM2ComputableAux := pairReductionAux computer.toTM2ComputableAux
  outputsFun pair := by
    let source := (PairEncoding.finEncoding sourceEncoding certificateEncoding).encode pair
    let privateOutput := (targetEncoding.encode (f pair.1)).map computer.outputAlphabet.invFun
    let reductionRun : TM2Outputs computer.tm
        ((PairEncoding.leftSymbols source).map computer.inputAlphabet.symm)
        (some privateOutput) := by
      refine ⟨(computer.outputsFun pair.1).steps, ?_⟩
      simpa [source, PairEncoding.finEncoding] using
        (computer.outputsFun pair.1).evals_in_steps
    let run := pairReductionMachine_outputs computer.toTM2ComputableAux
      source privateOutput reductionRun
    refine ⟨run.steps, ?_⟩
    simpa [run, source, privateOutput, pairReductionAux,
      PairEncoding.finEncoding, List.map_map] using run.evals_in_steps

/-- Function-level specialization preserves the exact step count, measured in
the full tagged input and the encoded reduced output. -/
theorem pairReductionComputable_outputs_steps {α β certificate : Type}
    (sourceEncoding : FinEncoding α) (targetEncoding : FinEncoding β)
    (certificateEncoding : FinEncoding certificate) (f : α → β)
    (computer : TM2Computable sourceEncoding targetEncoding f)
    (pair : α × certificate) :
    ((pairReductionComputable sourceEncoding targetEncoding certificateEncoding
      f computer).outputsFun pair).steps =
      (computer.outputsFun pair.1).steps +
        8 * ((PairEncoding.finEncoding sourceEncoding certificateEncoding).encode pair).length +
        4 * (targetEncoding.encode (f pair.1)).length + 22 := by
  unfold pairReductionComputable
  rw [pairReductionMachine_outputs_steps]
  simp

/-- The pair-left runtime in the full tagged input length `N`: the reduction
time, linear preprocessing, linear output reassembly at the checked reduced
output-size bound, and the fixed control overhead. -/
noncomputable def pairReductionTimePolynomial {α β : Type}
    (sourceEncoding : FinEncoding α) (targetEncoding : FinEncoding β)
    (f : α → β)
    (computer : TM2ComputableInPolyTime sourceEncoding targetEncoding f) :
    Polynomial ℕ :=
  computer.time + Polynomial.C 8 * Polynomial.X +
    Polynomial.C 4 *
      MachineComposition.outputSizePolynomial sourceEncoding targetEncoding f computer +
    Polynomial.C 22

@[simp]
theorem pairReductionTimePolynomial_eval {α β : Type}
    (sourceEncoding : FinEncoding α) (targetEncoding : FinEncoding β)
    (f : α → β)
    (computer : TM2ComputableInPolyTime sourceEncoding targetEncoding f)
    (n : ℕ) :
    (pairReductionTimePolynomial sourceEncoding targetEncoding f computer).eval n =
      computer.time.eval n + 8 * n +
        4 * (MachineComposition.outputSizePolynomial sourceEncoding targetEncoding
          f computer).eval n + 22 := by
  simp [pairReductionTimePolynomial, Polynomial.eval_add, Polynomial.eval_mul]

/-- Polynomial-time computation is closed under mapping the left component of
a canonically encoded pair. The bound uses the entire input/certificate length,
so no restriction on certificate length is needed for this machine result. -/
noncomputable def pairReductionComputableInPolyTime {α β certificate : Type}
    (sourceEncoding : FinEncoding α) (targetEncoding : FinEncoding β)
    (certificateEncoding : FinEncoding certificate) (f : α → β)
    (computer : TM2ComputableInPolyTime sourceEncoding targetEncoding f) :
    TM2ComputableInPolyTime
      (PairEncoding.finEncoding sourceEncoding certificateEncoding)
      (PairEncoding.finEncoding targetEncoding certificateEncoding)
      (fun pair => (f pair.1, pair.2)) where
  toTM2ComputableAux := pairReductionAux computer.toTM2ComputableAux
  time := pairReductionTimePolynomial sourceEncoding targetEncoding f computer
  outputsFun pair := by
    let paired := pairReductionComputable sourceEncoding targetEncoding
      certificateEncoding f computer.toTM2ComputableInTime.toTM2Computable
    refine
      { toEvalsTo := paired.outputsFun pair
        steps_le_m := ?_ }
    rw [pairReductionComputable_outputs_steps, pairReductionTimePolynomial_eval]
    have inputLength : (sourceEncoding.encode pair.1).length ≤
        ((PairEncoding.finEncoding sourceEncoding certificateEncoding).encode pair).length := by
      simp only [PairEncoding.finEncoding_encode_length]
      omega
    have reductionTime := (computer.outputsFun pair.1).steps_le_m
    have timeMono : computer.time.eval (sourceEncoding.encode pair.1).length ≤
        computer.time.eval
          ((PairEncoding.finEncoding sourceEncoding certificateEncoding).encode pair).length :=
      MachineRuntime.polynomial_eval_mono computer.time inputLength
    have outputLength : (targetEncoding.encode (f pair.1)).length ≤
        (MachineComposition.outputSizePolynomial sourceEncoding targetEncoding
          f computer).eval (sourceEncoding.encode pair.1).length := by
      simpa only [MachineComposition.outputSizePolynomial_eval] using
        MachineRuntime.computableInPolyTime_output_length_le
          sourceEncoding targetEncoding f computer pair.1
    have outputMono :
        (MachineComposition.outputSizePolynomial sourceEncoding targetEncoding f computer).eval
            (sourceEncoding.encode pair.1).length ≤
          (MachineComposition.outputSizePolynomial sourceEncoding targetEncoding f computer).eval
            ((PairEncoding.finEncoding sourceEncoding certificateEncoding).encode pair).length :=
      MachineRuntime.polynomial_eval_mono
        (MachineComposition.outputSizePolynomial sourceEncoding targetEncoding f computer)
        inputLength
    change (computer.outputsFun pair.1).steps +
      8 * ((PairEncoding.finEncoding sourceEncoding certificateEncoding).encode pair).length +
      4 * (targetEncoding.encode (f pair.1)).length + 22 ≤ _
    omega

end LeanNPHardness.MachineAdapters
