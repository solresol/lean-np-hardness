import LeanNPHardness.MachineRoutine

/-!
# Running a routine on selected stacks

A stack map replaces the index and alphabet of each stack instruction. If the
caller's representation of the stacks respects reads and writes, the translated
routine executes in exactly the same number of steps.
-/

namespace LeanNPHardness.Routines

open Turing

variable {K J : Type} [DecidableEq K] [DecidableEq J] {Γ : K → Type} {Δ : J → Type}

/-- Stack addresses in the caller and the alphabet equivalence at each address. -/
structure StackMap (Γ : K → Type) (Δ : J → Type) where
  index : K → J
  symbol : ∀ k, Γ k ≃ Δ (index k)

namespace StackMap

variable (m : StackMap Γ Δ) {Λ σ : Type}

private def stmt : TM2.Stmt Γ Λ σ → TM2.Stmt Δ Λ σ
  | .push k f q => .push (m.index k) (fun v => m.symbol k (f v)) (stmt q)
  | .peek k f q => .peek (m.index k) (fun v a => f v (a.map (m.symbol k).symm)) (stmt q)
  | .pop k f q => .pop (m.index k) (fun v a => f v (a.map (m.symbol k).symm)) (stmt q)
  | .load f q => .load f (stmt q)
  | .branch t a b => .branch t (stmt a) (stmt b)
  | .goto f => .goto f
  | .halt => .halt

/-- Wire the selected stacks directly into the control of the original routine. -/
def routine (r : Routine Γ) : Routine Δ where
  Λ := r.Λ
  σ := r.σ
  entry := r.entry
  init := r.init
  program l := m.stmt (r.program l)

variable (place : Stacks Γ → Stacks Δ)
  (read : ∀ S k, place S (m.index k) = (S k).map (m.symbol k))
  (write : ∀ S k w, place (Function.update S k w) =
    Function.update (place S) (m.index k) (w.map (m.symbol k)))

private def cfg (c : TM2.Cfg Γ Λ σ) : TM2.Cfg Δ Λ σ :=
  ⟨c.l, c.var, place c.stk⟩

include read write

private theorem stepAux (q : TM2.Stmt Γ Λ σ) (v : σ) (S : Stacks Γ) :
    TM2.stepAux (m.stmt q) v (place S) = cfg place (TM2.stepAux q v S) := by
  have top (S : Stacks Γ) (k : K) :
      (place S (m.index k)).head?.map (m.symbol k).symm = (S k).head? := by
    rw [read S k]
    cases S k <;> simp
  induction q generalizing v S with
  | push k f q ih =>
      simpa only [stmt, TM2.stepAux, write, List.map_cons, read] using
        ih v (Function.update S k (f v :: S k))
  | peek k f q ih =>
      simpa only [stmt, TM2.stepAux, top] using ih (f v (S k).head?) S
  | pop k f q ih =>
      simp only [stmt, TM2.stepAux, top]
      simpa only [write, read, List.map_tail] using
        ih (f v (S k).head?) (Function.update S k (S k).tail)
  | load f q ih => exact ih (f v) S
  | branch t a b ha hb =>
      cases h : t v
      · simpa only [stmt, TM2.stepAux, h, Bool.cond_false] using hb v S
      · simpa only [stmt, TM2.stepAux, h, Bool.cond_true] using ha v S
  | goto f => rfl
  | halt => rfl

private theorem step (r : Routine Γ) (c : TM2.Cfg Γ r.Λ r.σ) :
    TM2.step (m.routine r).program (cfg place c) =
      (TM2.step r.program c).map (cfg place) := by
  rcases c with ⟨_ | l, v, S⟩
  · rfl
  · exact congrArg some (m.stepAux place read write (r.program l) v S)

/-- Lifting a routine through a read- and write-preserving stack representation
preserves the exact step count, including its exit. -/
theorem exits (r : Routine Γ) {S S' : Stacks Γ} {n : Nat} (h : r.Exits S n S') :
    (m.routine r).Exits (place S) n (place S') := by
  have run (n : Nat) (c : Option (TM2.Cfg Γ r.Λ r.σ)) :
      (flip Option.bind (TM2.step (m.routine r).program))^[n] (c.map (cfg place)) =
        ((flip Option.bind (TM2.step r.program))^[n] c).map (cfg place) := by
    induction n generalizing c with
    | zero => rfl
    | succ n ih =>
        rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
        cases c with
        | none => exact ih none
        | some c =>
            simpa only [flip, Option.map_some, Option.bind_some, m.step place read write] using
              ih (TM2.step r.program c)
  obtain ⟨v, hv⟩ := h
  have lifted := run n (some ⟨some r.entry, r.init, S⟩)
  rw [hv] at lifted
  exact ⟨v, lifted⟩

end StackMap

end LeanNPHardness.Routines
