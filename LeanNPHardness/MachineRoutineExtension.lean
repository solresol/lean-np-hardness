import LeanNPHardness.MachineRoutine

/-!
# Extending a routine with untouched stacks

Embed a routine's stack family in the left summand of a larger layout.
Every extra stack retains its arbitrary initial contents, with no change to
labels, finite control, or exact runtime. No finiteness or inhabitedness of
the extra alphabets is needed for this simulation; a bundled finite machine
must still supply its own finiteness instances.
-/

namespace LeanNPHardness.Routines

open Turing

variable {K J : Type} [DecidableEq K] [DecidableEq J]
variable {Γ : K → Type} (Δ : J → Type)

/-- The original stack alphabets and a disjoint family of extra alphabets. -/
def ExtendedAlphabet : K ⊕ J → Type
  | .inl k => Γ k
  | .inr j => Δ j

/-- Keep the original and extra contents separate, including nonempty extras. -/
def extendedStacks (S : Stacks Γ) (extra : Stacks Δ) :
    Stacks (ExtendedAlphabet (Γ := Γ) Δ)
  | .inl k => S k
  | .inr j => extra j

omit [DecidableEq K] [DecidableEq J] in
@[simp] theorem extendedStacks_inl (S : Stacks Γ) (extra : Stacks Δ) (k : K) :
    extendedStacks Δ S extra (.inl k) = S k := rfl

omit [DecidableEq K] [DecidableEq J] in
@[simp] theorem extendedStacks_inr (S : Stacks Γ) (extra : Stacks Δ) (j : J) :
    extendedStacks Δ S extra (.inr j) = extra j := rfl

theorem extendedStacks_update (S : Stacks Γ) (extra : Stacks Δ)
    (k : K) (value : List (Γ k)) :
    extendedStacks Δ (Function.update S k value) extra =
      Function.update (extendedStacks Δ S extra) (.inl k) value := by
  funext index
  cases index with
  | inl j =>
      by_cases h : j = k
      · subst j; simp
      · have hsum : (Sum.inl j : K ⊕ J) ≠ .inl k := fun h' => h (Sum.inl.inj h')
        simp [h, hsum]
  | inr j => simp

variable {Λ σ : Type}

/-- Redirect each stack instruction to the left summand. -/
def extendStmt : TM2.Stmt Γ Λ σ → TM2.Stmt (ExtendedAlphabet (Γ := Γ) Δ) Λ σ
  | .push k f q => .push (.inl k) f (extendStmt q)
  | .peek k f q => .peek (.inl k) f (extendStmt q)
  | .pop k f q => .pop (.inl k) f (extendStmt q)
  | .load f q => .load f (extendStmt q)
  | .branch t a b => .branch t (extendStmt a) (extendStmt b)
  | .goto f => .goto f
  | .halt => .halt

def extendCfg (extra : Stacks Δ) (c : TM2.Cfg Γ Λ σ) :
    TM2.Cfg (ExtendedAlphabet (Γ := Γ) Δ) Λ σ :=
  ⟨c.l, c.var, extendedStacks Δ c.stk extra⟩

/-- Stack extension commutes with every statement, preserving all extra data. -/
theorem extendStmt_stepAux (extra : Stacks Δ) (stmt : TM2.Stmt Γ Λ σ)
    (v : σ) (S : Stacks Γ) :
    TM2.stepAux (extendStmt Δ stmt) v (extendedStacks Δ S extra) =
      extendCfg Δ extra (TM2.stepAux stmt v S) := by
  induction stmt generalizing v S with
  | push k f q ih =>
      simp only [extendStmt, TM2.stepAux, extendedStacks_inl]
      rw [← extendedStacks_update]
      exact ih _ _
  | peek k f q ih =>
      simpa only [extendStmt, TM2.stepAux, extendedStacks_inl] using
        ih (f v (S k).head?) S
  | pop k f q ih =>
      simp only [extendStmt, TM2.stepAux, extendedStacks_inl]
      rw [← extendedStacks_update]
      exact ih _ _
  | load f q ih =>
      simpa only [extendStmt, TM2.stepAux] using ih (f v) S
  | branch t a b iha ihb =>
      cases h : t v
      · simpa only [extendStmt, TM2.stepAux, h, Bool.cond_false] using ihb v S
      · simpa only [extendStmt, TM2.stepAux, h, Bool.cond_true] using iha v S
  | goto f => rfl
  | halt => rfl

theorem extend_step (extra : Stacks Δ) (program : Λ → TM2.Stmt Γ Λ σ)
    (c : TM2.Cfg Γ Λ σ) :
    TM2.step (fun l => extendStmt Δ (program l)) (extendCfg Δ extra c) =
      (TM2.step program c).map (extendCfg Δ extra) := by
  rcases c with ⟨l, v, S⟩
  cases l with
  | none => rfl
  | some l => simp only [extendCfg, TM2.step, extendStmt_stepAux, Option.map_some]

/-- Arbitrary finite execution, including halted/absent configurations, has
exactly the same step count in the extended layout. -/
theorem extend_run (extra : Stacks Δ) (program : Λ → TM2.Stmt Γ Λ σ) (n : Nat)
    (c : Option (TM2.Cfg Γ Λ σ)) :
    (flip Option.bind (TM2.step (fun l => extendStmt Δ (program l))))^[n]
        (c.map (extendCfg Δ extra)) =
      ((flip Option.bind (TM2.step program))^[n] c).map (extendCfg Δ extra) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
      cases c with
      | none => exact ih none
      | some c =>
          simpa only [flip, Option.map_some, Option.bind_some, extend_step] using
            ih (TM2.step program c)

/-- Add arbitrary untouched stacks without changing a routine's finite control. -/
def extend (r : Routine Γ) : Routine (ExtendedAlphabet (Γ := Γ) Δ) where
  Λ := r.Λ
  σ := r.σ
  entry := r.entry
  init := r.init
  program l := extendStmt Δ (r.program l)

/-- An exact routine contract remains valid with arbitrary extra stack contents. -/
theorem extend_exits (r : Routine Γ) (extra : Stacks Δ)
    {S S' : Stacks Γ} {n : Nat} (h : r.Exits S n S') :
    (extend Δ r).Exits (extendedStacks Δ S extra) n (extendedStacks Δ S' extra) := by
  obtain ⟨v, h⟩ := h
  refine ⟨v, ?_⟩
  have run := extend_run Δ extra r.program n (some ⟨some r.entry, r.init, S⟩)
  rw [h] at run
  exact run

end LeanNPHardness.Routines
