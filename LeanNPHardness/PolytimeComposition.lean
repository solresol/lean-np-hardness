import LeanNPHardness.PolytimeReduction

namespace LeanNPHardness

open Computability

namespace PolytimeManyOneReduction

/-- Compose a polynomial-time reduction after the identity reduction without
requiring the unfinished generic machine-composition theorem. The original
machine witness is reused because `reduction.map ∘ id = reduction.map`. -/
noncomputable def reflComp {α β : Type}
    {sourceEncoding : FinEncoding α} {targetEncoding : FinEncoding β}
    {source : Language α} {target : Language β}
    (reduction :
      PolytimeManyOneReduction sourceEncoding targetEncoding source target) :
    PolytimeManyOneReduction sourceEncoding targetEncoding source target :=
  compOfWitness (refl sourceEncoding source) reduction (by
    simpa only [Function.comp_id] using reduction.polytime)

/-- Compose a polynomial-time reduction before the identity reduction without
requiring the unfinished generic machine-composition theorem. The original
machine witness is reused because `id ∘ reduction.map = reduction.map`. -/
noncomputable def compRefl {α β : Type}
    {sourceEncoding : FinEncoding α} {targetEncoding : FinEncoding β}
    {source : Language α} {target : Language β}
    (reduction :
      PolytimeManyOneReduction sourceEncoding targetEncoding source target) :
    PolytimeManyOneReduction sourceEncoding targetEncoding source target :=
  compOfWitness reduction (refl targetEncoding target) (by
    simpa only [Function.id_comp] using reduction.polytime)

@[simp]
theorem reflComp_map {α β : Type}
    {sourceEncoding : FinEncoding α} {targetEncoding : FinEncoding β}
    {source : Language α} {target : Language β}
    (reduction :
      PolytimeManyOneReduction sourceEncoding targetEncoding source target)
    (x : α) :
    (reflComp reduction).map x = reduction.map x :=
  rfl

@[simp]
theorem compRefl_map {α β : Type}
    {sourceEncoding : FinEncoding α} {targetEncoding : FinEncoding β}
    {source : Language α} {target : Language β}
    (reduction :
      PolytimeManyOneReduction sourceEncoding targetEncoding source target)
    (x : α) :
    (compRefl reduction).map x = reduction.map x :=
  rfl

end PolytimeManyOneReduction

end LeanNPHardness
