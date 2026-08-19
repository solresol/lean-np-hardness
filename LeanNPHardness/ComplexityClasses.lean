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

end EncodedLanguage

end LeanNPHardness
