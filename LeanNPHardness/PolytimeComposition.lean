import LeanNPHardness.PolytimeReduction
import LeanNPHardness.MachineCompositionRuntime

namespace LeanNPHardness

open Computability

namespace PolytimeManyOneReduction

/-- Closed composition of polynomial-time many-one reductions. The runtime
witness is supplied by the checked concrete sequential TM2 construction. -/
noncomputable def comp {α β γ : Type}
    {sourceEncoding : FinEncoding α} {middleEncoding : FinEncoding β}
    {targetEncoding : FinEncoding γ}
    {source : Language α} {middle : Language β} {target : Language γ}
    (first :
      PolytimeManyOneReduction sourceEncoding middleEncoding source middle)
    (second :
      PolytimeManyOneReduction middleEncoding targetEncoding middle target) :
    PolytimeManyOneReduction sourceEncoding targetEncoding source target :=
  compOfWitness first second (by
    rcases first.polytime with ⟨firstComputer⟩
    rcases second.polytime with ⟨secondComputer⟩
    exact ⟨MachineComposition.compositionComputableInPolyTime
      sourceEncoding middleEncoding targetEncoding first.map second.map
      firstComputer secondComputer⟩)

@[simp]
theorem comp_map {α β γ : Type}
    {sourceEncoding : FinEncoding α} {middleEncoding : FinEncoding β}
    {targetEncoding : FinEncoding γ}
    {source : Language α} {middle : Language β} {target : Language γ}
    (first :
      PolytimeManyOneReduction sourceEncoding middleEncoding source middle)
    (second :
      PolytimeManyOneReduction middleEncoding targetEncoding middle target)
    (x : α) :
    (comp first second).map x = second.map (first.map x) :=
  rfl

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
