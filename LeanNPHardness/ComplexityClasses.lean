import LeanNPHardness.PairEncoding
import LeanNPHardness.PolytimeComposition

namespace LeanNPHardness

open Computability

/-- A decision language together with the finite encoding that fixes its input
size measure. -/
structure EncodedLanguage (α : Type) where
  encoding : FinEncoding α
  accepts : Language α

namespace EncodedLanguage

/-- Polynomial-time many-one reduction between encoded decision languages. -/
abbrev PolytimeReducesTo {α β : Type}
    (source : EncodedLanguage α) (target : EncodedLanguage β) :=
  PolytimeManyOneReduction source.encoding target.encoding
    source.accepts target.accepts

/-- A total Boolean decider with separate semantic and polynomial-time machine
evidence. Both Boolean outcomes are specified explicitly. -/
structure PolytimeDecider {α : Type} (problem : EncodedLanguage α) where
  decide : α → Bool
  accepts_iff : ∀ input, decide input = true ↔ problem.accepts input
  rejects_iff : ∀ input, decide input = false ↔ ¬ problem.accepts input
  polytime :
    Nonempty
      (Turing.TM2ComputableInPolyTime problem.encoding finEncodingBoolBool
        decide)

namespace PolytimeDecider

/-- Build the explicit two-outcome decider contract from correctness of the
positive outcome. Totality of `Bool` supplies the negative outcome. -/
def ofAcceptsIff {α : Type} {problem : EncodedLanguage α}
    (decide : α → Bool)
    (accepts_iff : ∀ input, decide input = true ↔ problem.accepts input)
    (polytime :
      Nonempty
        (Turing.TM2ComputableInPolyTime problem.encoding finEncodingBoolBool
          decide)) :
    PolytimeDecider problem where
  decide := decide
  accepts_iff := accepts_iff
  rejects_iff input := by
    constructor
    · intro hfalse haccepts
      have htrue : decide input = true := (accepts_iff input).2 haccepts
      simp [hfalse] at htrue
    · intro hrejects
      cases hdecision : decide input with
      | false => rfl
      | true =>
          exact (hrejects ((accepts_iff input).1 hdecision)).elim
  polytime := polytime

end PolytimeDecider

/-- Deterministic polynomial-time decidability for an encoded language. The
runtime is measured in the length of `problem.encoding.encode input`. -/
def InP {α : Type} (problem : EncodedLanguage α) : Prop :=
  Nonempty (PolytimeDecider problem)

/-- A checked polynomial-time Boolean decider places its encoded language in
`P`. -/
theorem PolytimeDecider.toInP {α : Type} {problem : EncodedLanguage α}
    (decider : PolytimeDecider problem) : problem.InP :=
  ⟨decider⟩

/-- A polynomial-time verifier with an explicit polynomial bound on encoded
certificate length. Soundness applies to every accepting certificate, while
completeness supplies a certificate satisfying the size bound. -/
structure PolytimeVerifier {α certificate : Type}
    (problem : EncodedLanguage α) where
  certificateEncoding : FinEncoding certificate
  verify : α × certificate → Bool
  certificateBound : Polynomial ℕ
  sound : ∀ input witness, verify (input, witness) = true → problem.accepts input
  complete : ∀ input, problem.accepts input → ∃ witness,
    (certificateEncoding.encode witness).length ≤
        certificateBound.eval (problem.encoding.encode input).length ∧
      verify (input, witness) = true
  polytime :
    Nonempty
      (Turing.TM2ComputableInPolyTime
        (PairEncoding.finEncoding problem.encoding certificateEncoding)
        finEncodingBoolBool verify)

/-- Verifier-based nondeterministic polynomial time for an encoded language.
The existential certificate type carries its own finite encoding. -/
def InNP {α : Type} (problem : EncodedLanguage α) : Prop :=
  ∃ certificate : Type,
    Nonempty (PolytimeVerifier (certificate := certificate) problem)

namespace PolytimeVerifier

/-- Membership is equivalent to the existence of an accepting certificate
whose encoded length satisfies the verifier's explicit polynomial bound. -/
theorem accepts_iff_exists_certificate {α certificate : Type}
    {problem : EncodedLanguage α}
    (verifier : PolytimeVerifier (certificate := certificate) problem)
    (input : α) :
    problem.accepts input ↔ ∃ witness,
      (verifier.certificateEncoding.encode witness).length ≤
          verifier.certificateBound.eval (problem.encoding.encode input).length ∧
        verifier.verify (input, witness) = true := by
  constructor
  · exact verifier.complete input
  · rintro ⟨witness, _, haccepts⟩
    exact verifier.sound input witness haccepts

/-- A checked verifier places its encoded language in `NP`. -/
theorem toInNP {α certificate : Type} {problem : EncodedLanguage α}
    (verifier : PolytimeVerifier (certificate := certificate) problem) :
    problem.InNP :=
  ⟨certificate, ⟨verifier⟩⟩

end PolytimeVerifier

end EncodedLanguage

end LeanNPHardness
