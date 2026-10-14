import LeanNPHardness.ComplexityClasses
import LeanNPHardness.PairReductionComputable

namespace LeanNPHardness.EncodedLanguage

open Computability

namespace PolytimeVerifier

/-- Pull a verifier back along a checked polynomial-time many-one reduction.
The Boolean-string certificate is retained. The machine first maps the
input component through the reduction, then runs the target verifier; its
runtime is polynomial in the full tagged input/certificate encoding length.
The separately checked certificate bound is polynomial in source input length.
-/
noncomputable def pullback {α β : Type}
    {source : EncodedLanguage α} {target : EncodedLanguage β}
    (targetVerifier : PolytimeVerifier target)
    (reduction : source.PolytimeReducesTo target) :
    PolytimeVerifier source :=
  let reductionComputer := Classical.choice reduction.polytime
  { verify := fun pair => targetVerifier.verify (reduction.map pair.1, pair.2)
    certificateBound :=
      targetVerifier.pullbackCertificateBound reduction reductionComputer
    sound := fun input witness haccepts =>
      (reduction.correct input).2
        (targetVerifier.sound (reduction.map input) witness haccepts)
    complete := targetVerifier.pullback_complete reduction reductionComputer
    polytime := by
      rcases targetVerifier.polytime with ⟨verifierComputer⟩
      exact ⟨MachineComposition.compositionComputableInPolyTime
        (PairEncoding.finEncoding source.encoding certificateEncoding)
        (PairEncoding.finEncoding target.encoding certificateEncoding)
        finEncodingBoolBool (fun pair => (reduction.map pair.1, pair.2))
        targetVerifier.verify
        (MachineAdapters.pairReductionComputableInPolyTime source.encoding
          target.encoding certificateEncoding reduction.map
          reductionComputer)
        verifierComputer⟩ }

@[simp]
theorem pullback_verify {α β : Type}
    {source : EncodedLanguage α} {target : EncodedLanguage β}
    (targetVerifier : PolytimeVerifier target)
    (reduction : source.PolytimeReducesTo target) (pair : α × List Bool) :
    (targetVerifier.pullback reduction).verify pair =
      targetVerifier.verify (reduction.map pair.1, pair.2) :=
  rfl

end PolytimeVerifier

namespace InNP

/-- Verifier-based NP membership transports backward along a checked
polynomial-time many-one reduction. -/
theorem of_reduction {α β : Type}
    {source : EncodedLanguage α} {target : EncodedLanguage β}
    (reduction : source.PolytimeReducesTo target)
    (targetInNP : target.InNP) : source.InNP := by
  rcases targetInNP with ⟨targetVerifier⟩
  exact (targetVerifier.pullback reduction).toInNP

end InNP

end LeanNPHardness.EncodedLanguage
