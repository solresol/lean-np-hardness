namespace LeanNPHardness

universe u v w

/-- A decision language over inputs of type `α`. -/
abbrev Language (α : Type u) :=
  α → Prop

/-- A semantic many-one reduction. Polynomial-time evidence is added in
`PolytimeReduction.lean`. -/
structure ManyOneReduction {α : Type u} {β : Type v}
    (source : Language α) (target : Language β) where
  map : α → β
  correct : ∀ x, source x ↔ target (map x)

namespace ManyOneReduction

/-- Every language many-one reduces to itself. -/
def refl {α : Type u} (language : Language α) :
    ManyOneReduction language language where
  map := id
  correct _ := Iff.rfl

/-- Semantic many-one reductions compose. -/
def comp {α : Type u} {β : Type v} {γ : Type w}
    {source : Language α} {middle : Language β} {target : Language γ}
    (first : ManyOneReduction source middle)
    (second : ManyOneReduction middle target) :
    ManyOneReduction source target where
  map := second.map ∘ first.map
  correct x := (first.correct x).trans (second.correct (first.map x))

@[simp]
theorem refl_map {α : Type u} (language : Language α) (x : α) :
    (refl language).map x = x :=
  rfl

@[simp]
theorem comp_map {α : Type u} {β : Type v} {γ : Type w}
    {source : Language α} {middle : Language β} {target : Language γ}
    (first : ManyOneReduction source middle)
    (second : ManyOneReduction middle target) (x : α) :
    (comp first second).map x = second.map (first.map x) :=
  rfl

end ManyOneReduction

end LeanNPHardness
