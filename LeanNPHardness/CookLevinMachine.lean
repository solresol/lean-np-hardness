import LeanNPHardness.CookLevin
import LeanNPHardness.TableauGenerator

/-!
# The Cook--Levin reduction as a machine

For a polynomial-time verifier machine, the generator over the verifier's
template instance is a single two-stack machine (`machine`) that maps the
encoding of an input to the unary encoding of its Cook--Levin tableau in
exactly `cost` steps (`machine_outputsInTime`). Its polynomial time bound is
established separately.
-/

namespace LeanNPHardness.CookLevin

open Turing Computability CNF CNF.Unary MachineTableau TableauStacks Routines EncodedLanguage

variable {α : Type} {problem : EncodedLanguage α}

/-- A verifier machine of a Boolean-string-certificate verifier. -/
abbrev VerifierMachine (verify : α × List Bool → Bool) :=
  TM2ComputableInPolyTime (PairEncoding.finEncoding problem.encoding certificateEncoding)
    finEncodingBoolBool verify

/-- The input-independent template instance of the verifier machine. -/
noncomputable def templateInstance {verify : α × List Bool → Bool}
    (computer : VerifierMachine (problem := problem) verify) : Instance where
  tm := computer.tm
  extra := [computer.outputAlphabet.invFun true]
  inputLength := 0
  certBound := 0
  horizon := 0
  input := []
  input_length := rfl
  certSym b := computer.inputAlphabet.invFun (Sum.inr b)
  certSym_injective := fun b b' h => Sum.inr.inj (computer.inputAlphabet.symm.injective h)
  output := [computer.outputAlphabet.invFun true]
  output_mem := fun s hs => hs
  output_short := by simp

theorem tableauInstance_template (verify : α × List Bool → Bool) (bound : Polynomial ℕ)
    (computer : VerifierMachine (problem := problem) verify) (x : α) :
    (tableauInstance verify bound computer x).template = templateInstance computer :=
  rfl

/-- Input symbols of the problem as input symbols of the verifier machine. -/
noncomputable def conv {verify : α × List Bool → Bool}
    (computer : VerifierMachine (problem := problem) verify) (s : problem.encoding.Γ) :
    computer.tm.Γ computer.tm.k₀ :=
  computer.inputAlphabet.invFun (Sum.inl s)

/-- Problem alphabets are decidable classically; the generator is
noncomputable anyway. -/
noncomputable local instance : DecidableEq problem.encoding.Γ := Classical.decEq _

/-- The generator routine of the verifier. -/
noncomputable def generatorRoutine {verify : α × List Bool → Bool} (bound : Polynomial ℕ)
    (computer : VerifierMachine (problem := problem) verify) : GRoutine problem.encoding.Γ :=
  generator bound computer.time (templateInstance computer).pb (templateInstance computer).D
    (templateInstance computer).width (templateInstance computer) (conv computer)

/-- Exact steps of the generator on an input. -/
noncomputable def cost (verify : α × List Bool → Bool) (bound : Polynomial ℕ)
    (computer : VerifierMachine (problem := problem) verify) (x : α) : ℕ :=
  generatorCost (tableauInstance verify bound computer x) bound computer.time
    (problem.encoding.encode x).length

theorem generatorRoutine_exits (verify : α × List Bool → Bool) (bound : Polynomial ℕ)
    (computer : VerifierMachine (problem := problem) verify) (x : α) :
    (generatorRoutine bound computer).Exits
      (paramStacks (problem.encoding.encode x) [] 0 0 0 0 0 0 0 0)
      (cost verify bound computer x)
      (outputStacks (encode (formula verify bound computer x))) :=
  generator_exits (tableauInstance verify bound computer x) (conv computer) bound computer.time
    (problem.encoding.encode x) rfl rfl rfl

/-- The Cook--Levin machine of the verifier. -/
noncomputable def machine {verify : α × List Bool → Bool} (bound : Polynomial ℕ)
    (computer : VerifierMachine (problem := problem) verify) : FinTM2 :=
  toGenMachine (generatorRoutine bound computer)

/-- The machine maps an encoded input to the unary encoding of its tableau
in exactly `cost` steps. -/
noncomputable def machine_outputsInTime (verify : α × List Bool → Bool) (bound : Polynomial ℕ)
    (computer : VerifierMachine (problem := problem) verify) (x : α) :
    TM2OutputsInTime (machine bound computer) (problem.encoding.encode x)
      (some (encode (formula verify bound computer x))) (cost verify bound computer x) :=
  toGenMachine_outputsInTime _ _ _ _ (generatorRoutine_exits verify bound computer x)

end LeanNPHardness.CookLevin
