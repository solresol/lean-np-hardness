import LeanNPHardness.MachineRuntimeBounds

/-!
# Padded runs of a bundled TM2 machine

`padStep` is the total step function that leaves a halted configuration
unchanged. A live run of exactly `s` steps is a padded run of `s` steps, and
a padded run reaching a halted configuration within `T` steps is a live run
to that configuration at its first halting time, which is unique. This is
the bridge between mathlib's option-valued exact runs and the fixed-horizon
Cook--Levin tableau. No runtime claim is made.
-/

namespace LeanNPHardness.MachinePaddedRun

open Turing

variable (tm : FinTM2)

/-- The step function that stays put once the machine has halted. -/
def padStep (c : tm.Cfg) : tm.Cfg := (tm.step c).getD c

theorem step_eq_none_iff (c : tm.Cfg) : tm.step c = none ↔ c.l = none := by
  rcases c with ⟨label, state, contents⟩
  cases label <;> simp [FinTM2.step, TM2.step]

theorem padStep_of_step (c c' : tm.Cfg) (h : tm.step c = some c') : padStep tm c = c' := by
  unfold padStep
  rw [h]
  rfl

theorem padStep_of_halt (c : tm.Cfg) (h : c.l = none) : padStep tm c = c := by
  unfold padStep
  rw [(step_eq_none_iff tm c).2 h]
  rfl

theorem iterate_padStep_of_halt (c : tm.Cfg) (h : c.l = none) (m : ℕ) :
    (padStep tm)^[m] c = c := by
  induction m with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply', ih, padStep_of_halt tm c h]

private theorem iterate_bind_none (steps : ℕ) :
    (flip Option.bind tm.step)^[steps] none = none := by
  induction steps with
  | zero => rfl
  | succ steps ih => rw [Function.iterate_succ_apply]; exact ih

/-- A live option-valued run is a padded run of the same length. -/
theorem iterate_padStep_of_run (s : ℕ) :
    ∀ (c c' : tm.Cfg), (flip Option.bind tm.step)^[s] (some c) = some c' →
      (padStep tm)^[s] c = c' := by
  induction s with
  | zero => intro c c' h; simpa using h
  | succ s ih =>
      intro c c' h
      rw [Function.iterate_succ_apply] at h
      change (flip Option.bind tm.step)^[s] (tm.step c) = some c' at h
      cases hstep : tm.step c with
      | none => rw [hstep, iterate_bind_none] at h; cases h
      | some c₁ =>
          rw [hstep] at h
          rw [Function.iterate_succ_apply, padStep_of_step tm c c₁ hstep]
          exact ih c₁ c' h

/-- A padded run reaching a halted configuration is a live run that halts
there at its first halting time, within the same number of steps. -/
theorem run_of_iterate_padStep (T : ℕ) :
    ∀ (c h : tm.Cfg), (padStep tm)^[T] c = h → h.l = none →
      ∃ s ≤ T, (flip Option.bind tm.step)^[s] (some c) = some h := by
  induction T with
  | zero =>
      intro c h hrun _
      exact ⟨0, le_rfl, by simpa using hrun⟩
  | succ T ih =>
      intro c h hrun hh
      rw [Function.iterate_succ_apply] at hrun
      cases hstep : tm.step c with
      | none =>
          have hc : c.l = none := (step_eq_none_iff tm c).1 hstep
          rw [padStep_of_halt tm c hc] at hrun
          obtain ⟨s, hs, hrun'⟩ := ih c h hrun hh
          exact ⟨s, by omega, hrun'⟩
      | some c₁ =>
          rw [padStep_of_step tm c c₁ hstep] at hrun
          obtain ⟨s, hs, hrun'⟩ := ih c₁ h hrun hh
          refine ⟨s + 1, by omega, ?_⟩
          rw [Function.iterate_succ_apply]
          change (flip Option.bind tm.step)^[s] (tm.step c) = some h
          rw [hstep]
          exact hrun'

theorem iterate_of_halt_eq_none (h : tm.Cfg) (hh : h.l = none) (m : ℕ) (hm : 0 < m) :
    (flip Option.bind tm.step)^[m] (some h) = none := by
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rw [Function.iterate_succ_apply]
  change (flip Option.bind tm.step)^[m] (tm.step h) = none
  rw [(step_eq_none_iff tm h).2 hh, iterate_bind_none]

/-- Live runs reach a halted configuration at a unique time. -/
theorem run_halt_unique (c h h' : tm.Cfg) (s s' : ℕ)
    (hs : (flip Option.bind tm.step)^[s] (some c) = some h)
    (hs' : (flip Option.bind tm.step)^[s'] (some c) = some h')
    (hh : h.l = none) (hh' : h'.l = none) : s = s' ∧ h = h' := by
  have key : ∀ (a b : ℕ) (x y : tm.Cfg), a < b →
      (flip Option.bind tm.step)^[a] (some c) = some x →
      (flip Option.bind tm.step)^[b] (some c) = some y → x.l = none → False := by
    intro a b x y hab hx hy hx'
    have : (flip Option.bind tm.step)^[b] (some c) = none := by
      rw [show b = (b - a) + a by omega, Function.iterate_add_apply, hx,
        iterate_of_halt_eq_none tm x hx' (b - a) (by omega)]
    rw [hy] at this
    cases this
  rcases Nat.lt_trichotomy s s' with hlt | heq | hgt
  · exact (key s s' h h' hlt hs hs' hh).elim
  · subst heq
    rw [hs] at hs'
    exact ⟨rfl, Option.some.inj hs'⟩
  · exact (key s' s h' h hgt hs' hs hh').elim

@[simp]
theorem haltList_l (output : List (tm.Γ tm.k₁)) : (haltList tm output).l = none := rfl

/-- Reaching a canonical halting configuration within `T` padded steps is
the same as mathlib's exact run reaching it in at most `T` steps. -/
theorem iterate_padStep_eq_haltList_iff (input : List (tm.Γ tm.k₀))
    (output : List (tm.Γ tm.k₁)) (T : ℕ) :
    (padStep tm)^[T] (initList tm input) = haltList tm output ↔
      ∃ s ≤ T, (flip Option.bind tm.step)^[s] (some (initList tm input)) =
        some (haltList tm output) := by
  constructor
  · intro h
    exact run_of_iterate_padStep tm T _ _ h rfl
  · rintro ⟨s, hs, hrun⟩
    have := iterate_padStep_of_run tm s _ _ hrun
    rw [show T = (T - s) + s by omega, Function.iterate_add_apply, this,
      iterate_padStep_of_halt tm _ rfl]

end LeanNPHardness.MachinePaddedRun
