import LeanNPHardness.CookLevinMachine
import LeanNPHardness.TableauGeneratorBound

/-!
# Cook--Levin: NP-hardness of unary CNF-SAT

The Cook--Levin machine of a verifier runs within the polynomial
`timePoly`, so the tableau map is a checked polynomial-time many-one
reduction from any NP language to CNF-SAT under the unary-index encoding:
`encodedUnarySAT_NPHard`.

Computational model: mathlib's `FinTM2` two-stack machines with
`TM2ComputableInPolyTime`; the input size is the length of the source
language's encoding of the input.
-/

namespace LeanNPHardness.CookLevin

open Turing Computability CNF CNF.Unary MachineTableau TableauStacks Routines EncodedLanguage
  Polynomial MachinePrimitives

variable {α : Type} {problem : EncodedLanguage α}

/-- The time polynomial of the Cook--Levin machine. -/
noncomputable def timePoly {verify : α × List Bool → Bool} (bound : Polynomial ℕ)
    (computer : VerifierMachine (problem := problem) verify) : Polynomial ℕ :=
  C (Instance.K (templateInstance computer) bound computer.time) *
    sizePoly bound computer.time ^ 4

theorem cost_le (verify : α × List Bool → Bool) (bound : Polynomial ℕ)
    (computer : VerifierMachine (problem := problem) verify) (x : α) :
    cost verify bound computer x ≤ (timePoly bound computer).eval (problem.encoding.encode x).length := by
  unfold cost timePoly
  rw [eval_mul, eval_C, eval_pow, sizePoly_eval]
  exact Instance.generatorCost_le (tableauInstance verify bound computer x) bound computer.time _
    rfl rfl rfl

/-- The Cook--Levin machine computes the tableau map in polynomial time. -/
noncomputable def computableInPolyTime (verify : α × List Bool → Bool) (bound : Polynomial ℕ)
    (computer : VerifierMachine (problem := problem) verify) :
    TM2ComputableInPolyTime problem.encoding CNF.Unary.finEncoding
      (formula verify bound computer) where
  tm := machine bound computer
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := timePoly bound computer
  outputsFun x := by
    have run := evalsToInTimeMono (machine_outputsInTime verify bound computer x)
      (cost_le verify bound computer x)
    simpa [Equiv.refl] using run

/-- The checked polynomial-time reduction from an NP language to unary SAT. -/
noncomputable def polytimeReduction (V : PolytimeVerifier problem)
    (computer : VerifierMachine (problem := problem) V.verify) :
    problem.PolytimeReducesTo encodedUnarySAT where
  map := formula V.verify V.certificateBound computer
  correct x := accepts_iff_sat V computer x
  polytime := ⟨computableInPolyTime V.verify V.certificateBound computer⟩

/-- Cook--Levin: CNF-SAT under the unary-index encoding is NP-hard. -/
theorem encodedUnarySAT_NPHard : encodedUnarySAT.NPHard := by
  intro β source hsource
  obtain ⟨V⟩ := hsource
  obtain ⟨computer⟩ := V.polytime
  exact ⟨polytimeReduction V computer⟩

end LeanNPHardness.CookLevin
