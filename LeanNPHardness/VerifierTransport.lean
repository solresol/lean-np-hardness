import LeanNPHardness.ComplexityClasses
import LeanNPHardness.PairReductionComputable

namespace LeanNPHardness.EncodedLanguage

open Computability

namespace PolytimeVerifier

/-- Pull a verifier back along a checked polynomial-time many-one reduction.
The certificate and its encoding are retained. The machine first maps the
input component through the reduction, then runs the target verifier; its
runtime is polynomial in the full tagged input/certificate encoding length.
The separately checked certificate bound is polynomial in source input length.
-/
noncomputable def pullback {α β certificate : Type}
    {source : EncodedLanguage α} {target : EncodedLanguage β}
    (targetVerifier : PolytimeVerifier (certificate := certificate) target)
    (reduction : source.PolytimeReducesTo target) :
    PolytimeVerifier (certificate := certificate) source :=
  let reductionComputer := Classical.choice reduction.polytime
  { certificateEncoding := targetVerifier.certificateEncoding
    verify := fun pair => targetVerifier.verify (reduction.map pair.1, pair.2)
    certificateBound :=
      targetVerifier.pullbackCertificateBound reduction reductionComputer
    sound := fun input witness haccepts =>
      (reduction.correct input).2
        (targetVerifier.sound (reduction.map input) witness haccepts)
    complete := targetVerifier.pullback_complete reduction reductionComputer
    polytime := by
      rcases targetVerifier.polytime with ⟨verifierComputer⟩
      exact ⟨MachineComposition.compositionComputableInPolyTime
        (PairEncoding.finEncoding source.encoding targetVerifier.certificateEncoding)
        (PairEncoding.finEncoding target.encoding targetVerifier.certificateEncoding)
        finEncodingBoolBool (fun pair => (reduction.map pair.1, pair.2))
        targetVerifier.verify
        (MachineAdapters.pairReductionComputableInPolyTime source.encoding
          target.encoding targetVerifier.certificateEncoding reduction.map
          reductionComputer)
        verifierComputer⟩ }

@[simp]
theorem pullback_verify {α β certificate : Type}
    {source : EncodedLanguage α} {target : EncodedLanguage β}
    (targetVerifier : PolytimeVerifier (certificate := certificate) target)
    (reduction : source.PolytimeReducesTo target) (pair : α × certificate) :
    (targetVerifier.pullback reduction).verify pair =
      targetVerifier.verify (reduction.map pair.1, pair.2) :=
  rfl

@[simp]
theorem pullback_certificateEncoding {α β certificate : Type}
    {source : EncodedLanguage α} {target : EncodedLanguage β}
    (targetVerifier : PolytimeVerifier (certificate := certificate) target)
    (reduction : source.PolytimeReducesTo target) :
    (targetVerifier.pullback reduction).certificateEncoding =
      targetVerifier.certificateEncoding :=
  rfl

end PolytimeVerifier

namespace InNP

/-- Verifier-based NP membership transports backward along a checked
polynomial-time many-one reduction. -/
theorem of_reduction {α β : Type}
    {source : EncodedLanguage α} {target : EncodedLanguage β}
    (reduction : source.PolytimeReducesTo target)
    (targetInNP : target.InNP) : source.InNP := by
  rcases targetInNP with ⟨certificate, ⟨targetVerifier⟩⟩
  exact (targetVerifier.pullback reduction).toInNP

end InNP

end LeanNPHardness.EncodedLanguage
