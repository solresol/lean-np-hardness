import LeanNPHardness.PairEncoding
import LeanNPHardness.PolytimeComposition

namespace LeanNPHardness

open Computability

namespace MachineAdapters

/-- Reuse a polynomial-time machine on the left component of a pair whose
right component has the empty `Unit` encoding. The machine and time polynomial
are unchanged; only the external input-alphabet equivalence is adjusted. -/
noncomputable def ignoreUnitCertificate {α β : Type}
    (sourceEncoding : FinEncoding α) (targetEncoding : FinEncoding β)
    {f : α → β}
    (computer :
      Turing.TM2ComputableInPolyTime sourceEncoding targetEncoding f) :
    Turing.TM2ComputableInPolyTime
      (PairEncoding.finEncoding sourceEncoding UnitEncoding.finEncoding)
      targetEncoding (fun pair => f pair.1) where
  tm := computer.tm
  inputAlphabet :=
    computer.inputAlphabet.trans
      (Equiv.sumEmpty sourceEncoding.Γ Empty).symm
  outputAlphabet := computer.outputAlphabet
  time := computer.time
  outputsFun pair := by
    rcases pair with ⟨input, witness⟩
    rcases witness with ⟨⟩
    simpa [PairEncoding.finEncoding, UnitEncoding.finEncoding] using
      computer.outputsFun input

end MachineAdapters

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

/-- An encoded language is NP-hard when every encoded language in NP has a
checked polynomial-time many-one reduction to it. `Nonempty` keeps hardness a
proposition while retaining the reduction witness supplied by each use. -/
def NPHard {α : Type} (problem : EncodedLanguage α) : Prop :=
  ∀ {β : Type} (source : EncodedLanguage β),
    source.InNP → Nonempty (source.PolytimeReducesTo problem)

/-- An encoded language is NP-complete when it is both NP-hard and in NP. -/
def NPComplete {α : Type} (problem : EncodedLanguage α) : Prop :=
  problem.NPHard ∧ problem.InNP

namespace NPHard

/-- NP-hardness transports forward along a checked polynomial-time many-one
reduction. -/
theorem of_reduction {α β : Type}
    {source : EncodedLanguage α} {target : EncodedLanguage β}
    (reduction : source.PolytimeReducesTo target)
    (sourceHard : source.NPHard) : target.NPHard := by
  intro γ problem problemInNP
  rcases sourceHard problem problemInNP with ⟨toSource⟩
  exact ⟨toSource.comp reduction⟩

end NPHard

namespace NPComplete

/-- The hardness component of NP-completeness. -/
theorem nphard {α : Type} {problem : EncodedLanguage α}
    (complete : problem.NPComplete) : problem.NPHard :=
  complete.1

/-- The membership component of NP-completeness. -/
theorem inNP {α : Type} {problem : EncodedLanguage α}
    (complete : problem.NPComplete) : problem.InNP :=
  complete.2

/-- Build NP-completeness by transporting hardness along a checked reduction
and proving target membership in NP separately. -/
theorem of_reduction {α β : Type}
    {source : EncodedLanguage α} {target : EncodedLanguage β}
    (sourceHard : source.NPHard)
    (reduction : source.PolytimeReducesTo target)
    (targetInNP : target.InNP) : target.NPComplete :=
  ⟨sourceHard.of_reduction reduction, targetInNP⟩

end NPComplete

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

namespace PolytimeDecider

/-- Regard a deterministic polynomial-time decider as a verifier using the
unique empty certificate. -/
noncomputable def toUnitVerifier {α : Type}
    {problem : EncodedLanguage α} (decider : PolytimeDecider problem) :
    PolytimeVerifier (certificate := Unit) problem where
  certificateEncoding := UnitEncoding.finEncoding
  verify pair := decider.decide pair.1
  certificateBound := 0
  sound input _ haccepts := (decider.accepts_iff input).1 haccepts
  complete input haccepts := by
    refine ⟨(), ?_, (decider.accepts_iff input).2 haccepts⟩
    simp [UnitEncoding.finEncoding]
  polytime := decider.polytime.map fun computer =>
    MachineAdapters.ignoreUnitCertificate problem.encoding
      finEncodingBoolBool computer

end PolytimeDecider

/-- Every encoded language in deterministic polynomial time is in verifier-
based nondeterministic polynomial time. -/
theorem inP_toInNP {α : Type} {problem : EncodedLanguage α} :
    problem.InP → problem.InNP := by
  rintro ⟨decider⟩
  exact decider.toUnitVerifier.toInNP

end EncodedLanguage

end LeanNPHardness
