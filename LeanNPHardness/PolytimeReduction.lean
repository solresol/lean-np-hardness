import LeanNPHardness.SemanticReduction
import Mathlib.Computability.TMComputable

namespace LeanNPHardness

open Computability

/-- A semantic many-one reduction whose map is computed in polynomial time by
mathlib's finite two-stack Turing-machine model. -/
structure PolytimeManyOneReduction {α β : Type}
    (sourceEncoding : FinEncoding α) (targetEncoding : FinEncoding β)
    (source : Language α) (target : Language β) where
  map : α → β
  correct : ∀ x, source x ↔ target (map x)
  polytime :
    Nonempty
      (Turing.TM2ComputableInPolyTime sourceEncoding targetEncoding map)

namespace PolytimeManyOneReduction

/-- Forget the machine and runtime evidence. -/
def toManyOneReduction {α β : Type}
    {sourceEncoding : FinEncoding α} {targetEncoding : FinEncoding β}
    {source : Language α} {target : Language β}
    (reduction :
      PolytimeManyOneReduction sourceEncoding targetEncoding source target) :
    ManyOneReduction source target where
  map := reduction.map
  correct := reduction.correct

/-- Polynomial-time identity reduction. -/
noncomputable def refl {α : Type} (encoding : FinEncoding α)
    (language : Language α) :
    PolytimeManyOneReduction encoding encoding language language where
  map := id
  correct _ := Iff.rfl
  polytime := ⟨Turing.idComputableInPolyTime encoding⟩

/-- Compose polynomial reductions when a checked machine witness for the
composed map is supplied explicitly.

Closing this witness generically, without relying on mathlib's current
`proof_wanted` declaration, is the first major project milestone. -/
def compOfWitness {α β γ : Type}
    {sourceEncoding : FinEncoding α} {middleEncoding : FinEncoding β}
    {targetEncoding : FinEncoding γ}
    {source : Language α} {middle : Language β} {target : Language γ}
    (first :
      PolytimeManyOneReduction sourceEncoding middleEncoding source middle)
    (second :
      PolytimeManyOneReduction middleEncoding targetEncoding middle target)
    (polytime :
      Nonempty
        (Turing.TM2ComputableInPolyTime sourceEncoding targetEncoding
          (second.map ∘ first.map))) :
    PolytimeManyOneReduction sourceEncoding targetEncoding source target where
  map := second.map ∘ first.map
  correct x := (first.correct x).trans (second.correct (first.map x))
  polytime := polytime

@[simp]
theorem refl_map {α : Type} (encoding : FinEncoding α)
    (language : Language α) (x : α) :
    (refl encoding language).map x = x :=
  rfl

@[simp]
theorem compOfWitness_map {α β γ : Type}
    {sourceEncoding : FinEncoding α} {middleEncoding : FinEncoding β}
    {targetEncoding : FinEncoding γ}
    {source : Language α} {middle : Language β} {target : Language γ}
    (first :
      PolytimeManyOneReduction sourceEncoding middleEncoding source middle)
    (second :
      PolytimeManyOneReduction middleEncoding targetEncoding middle target)
    (polytime :
      Nonempty
        (Turing.TM2ComputableInPolyTime sourceEncoding targetEncoding
          (second.map ∘ first.map)))
    (x : α) :
    (compOfWitness first second polytime).map x =
      second.map (first.map x) :=
  rfl

end PolytimeManyOneReduction

end LeanNPHardness
