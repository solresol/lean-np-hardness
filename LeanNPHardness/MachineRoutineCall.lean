import LeanNPHardness.MachineRoutineExtension

/-!
# Calling a bundled machine as a routine

A canonical bounded machine computation supplies an exact routine exit at
some step count within the same bound. Extending that routine preserves
arbitrary caller stacks. Loading and returning encoded words are separate
operations and are not included in this contract.
-/

namespace LeanNPHardness.Routines

open Turing

/-- Reuse the complete bundled program, with its halt interpreted as routine exit. -/
def ofMachine (tm : FinTM2) : Routine tm.Γ where
  Λ := tm.Λ
  σ := tm.σ
  ΛFin := tm.ΛFin
  σFin := tm.σFin
  entry := tm.main
  init := tm.initialState
  program := tm.m

/-- A canonical machine computation yields an exact exit within its stated bound. -/
theorem ofMachine_exits (tm : FinTM2) (input : List (tm.Γ tm.k₀))
    (output : List (tm.Γ tm.k₁)) (bound : Nat)
    (h : TM2OutputsInTime tm input (some output) bound) :
    ∃ n ≤ bound, (ofMachine tm).Exits (initList tm input).stk n
      (haltList tm output).stk := by
  exact ⟨h.steps, h.steps_le_m, tm.initialState, h.evals_in_steps⟩

/-- Calling the entire machine preserves all caller stacks at unchanged cost. -/
theorem ofMachine_extended_exits {J : Type} [DecidableEq J] (Δ : J → Type)
    (tm : FinTM2) (extra : Stacks Δ) (input : List (tm.Γ tm.k₀))
    (output : List (tm.Γ tm.k₁)) (bound : Nat)
    (h : TM2OutputsInTime tm input (some output) bound) :
    ∃ n ≤ bound, (extend Δ (ofMachine tm)).Exits
      (extendedStacks Δ (initList tm input).stk extra) n
      (extendedStacks Δ (haltList tm output).stk extra) := by
  obtain ⟨n, hn, run⟩ := ofMachine_exits tm input output bound h
  exact ⟨n, hn, extend_exits Δ (ofMachine tm) extra run⟩

end LeanNPHardness.Routines
