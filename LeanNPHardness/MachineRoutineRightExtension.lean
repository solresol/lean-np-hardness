import LeanNPHardness.MachineRoutineExtension

/-!
# Extending routines on the right of retained stacks

The right-summand counterpart of `extend` uses the same finite control and
exact runtime while preserving arbitrary left-hand stack contents. This lets
caller routines share a layout with a private machine on the left.
-/

namespace LeanNPHardness.Routines

open Turing

variable {K J : Type} [DecidableEq K] [DecidableEq J]
variable {Γ : K → Type} (Δ : J → Type)

theorem extendedStacks_update_right (S : Stacks Γ) (extra : Stacks Δ)
    (k : K) (value : List (Γ k)) :
    extendedStacks Γ extra (Function.update S k value) =
      Function.update (extendedStacks Γ extra S) (.inr k) value := by
  funext index
  cases index with
  | inl j => simp
  | inr j =>
      by_cases h : j = k
      · subst j; simp
      · have hsum : (Sum.inr j : J ⊕ K) ≠ .inr k := fun h' => h (Sum.inr.inj h')
        simp [h, hsum]

variable {Λ σ : Type}

/-- Redirect each stack instruction to the right summand. -/
def extendRightStmt : TM2.Stmt Γ Λ σ → TM2.Stmt (ExtendedAlphabet (Γ := Δ) Γ) Λ σ
  | .push k f q => .push (.inr k) f (extendRightStmt q)
  | .peek k f q => .peek (.inr k) f (extendRightStmt q)
  | .pop k f q => .pop (.inr k) f (extendRightStmt q)
  | .load f q => .load f (extendRightStmt q)
  | .branch t a b => .branch t (extendRightStmt a) (extendRightStmt b)
  | .goto f => .goto f
  | .halt => .halt

def extendRightCfg (extra : Stacks Δ) (c : TM2.Cfg Γ Λ σ) :
    TM2.Cfg (ExtendedAlphabet (Γ := Δ) Γ) Λ σ :=
  ⟨c.l, c.var, extendedStacks Γ extra c.stk⟩

/-- Stack extension commutes with every statement, preserving all extra data. -/
theorem extendRightStmt_stepAux (extra : Stacks Δ) (stmt : TM2.Stmt Γ Λ σ)
    (v : σ) (S : Stacks Γ) :
    TM2.stepAux (extendRightStmt Δ stmt) v (extendedStacks Γ extra S) =
      extendRightCfg Δ extra (TM2.stepAux stmt v S) := by
  induction stmt generalizing v S with
  | push k f q ih =>
      simp only [extendRightStmt, TM2.stepAux, extendedStacks_inr]
      rw [← extendedStacks_update_right]
      exact ih _ _
  | peek k f q ih =>
      simpa only [extendRightStmt, TM2.stepAux, extendedStacks_inr] using
        ih (f v (S k).head?) S
  | pop k f q ih =>
      simp only [extendRightStmt, TM2.stepAux, extendedStacks_inr]
      rw [← extendedStacks_update_right]
      exact ih _ _
  | load f q ih =>
      simpa only [extendRightStmt, TM2.stepAux] using ih (f v) S
  | branch t a b iha ihb =>
      cases h : t v
      · simpa only [extendRightStmt, TM2.stepAux, h, Bool.cond_false] using ihb v S
      · simpa only [extendRightStmt, TM2.stepAux, h, Bool.cond_true] using iha v S
  | goto f => rfl
  | halt => rfl

theorem extendRight_step (extra : Stacks Δ) (program : Λ → TM2.Stmt Γ Λ σ)
    (c : TM2.Cfg Γ Λ σ) :
    TM2.step (fun l => extendRightStmt Δ (program l)) (extendRightCfg Δ extra c) =
      (TM2.step program c).map (extendRightCfg Δ extra) := by
  rcases c with ⟨l, v, S⟩
  cases l with
  | none => rfl
  | some l => simp only [extendRightCfg, TM2.step, extendRightStmt_stepAux, Option.map_some]

/-- Arbitrary finite execution, including halted/absent configurations, has
exactly the same step count in the extended layout. -/
theorem extendRight_run (extra : Stacks Δ) (program : Λ → TM2.Stmt Γ Λ σ) (n : Nat)
    (c : Option (TM2.Cfg Γ Λ σ)) :
    (flip Option.bind (TM2.step (fun l => extendRightStmt Δ (program l))))^[n]
        (c.map (extendRightCfg Δ extra)) =
      ((flip Option.bind (TM2.step program))^[n] c).map (extendRightCfg Δ extra) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
      cases c with
      | none => exact ih none
      | some c =>
          simpa only [flip, Option.map_some, Option.bind_some, extendRight_step] using
            ih (TM2.step program c)

/-- Add arbitrary untouched stacks without changing a routine's finite control. -/
def extendRight (r : Routine Γ) : Routine (ExtendedAlphabet (Γ := Δ) Γ) where
  Λ := r.Λ
  σ := r.σ
  entry := r.entry
  init := r.init
  program l := extendRightStmt Δ (r.program l)

/-- An exact routine contract remains valid with arbitrary extra stack contents. -/
theorem extendRight_exits (r : Routine Γ) (extra : Stacks Δ)
    {S S' : Stacks Γ} {n : Nat} (h : r.Exits S n S') :
    (extendRight Δ r).Exits (extendedStacks Γ extra S) n (extendedStacks Γ extra S') := by
  obtain ⟨v, h⟩ := h
  refine ⟨v, ?_⟩
  have run := extendRight_run Δ extra r.program n (some ⟨some r.entry, r.init, S⟩)
  rw [h] at run
  exact run

end LeanNPHardness.Routines
