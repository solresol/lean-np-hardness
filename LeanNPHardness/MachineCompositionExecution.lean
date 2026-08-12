import LeanNPHardness.MachineCompositionProgram

namespace LeanNPHardness.MachineComposition

open Turing

/-- Iterating an option-valued transition from `none` remains at `none`. -/
private theorem iterate_bind_none {α : Type} (step : α → Option α) (steps : ℕ) :
    (flip Option.bind step)^[steps] none = none := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
      rw [Function.iterate_succ_apply]
      exact ih

/-- A halted TM2 configuration has no successor. -/
private theorem step_of_halted {K : Type} {Γ : K → Type} {Λ σ : Type}
    [DecidableEq K] (program : Λ → TM2.Stmt Γ Λ σ)
    (cfg : TM2.Cfg Γ Λ σ) (hhalt : cfg.l = none) :
    TM2.step program cfg = none := by
  cases cfg with
  | mk label state contents =>
      change label = none at hhalt
      subst label
      rfl

/-- On a running endpoint, the halt-redirecting lift is the ordinary
left-control lift. -/
private theorem liftLeftThenTransferCfg_of_running {Γ₀ Γ₁ Γ₂ : Type}
    (first : TM2ComputableAux Γ₀ Γ₁)
    (second : TM2ComputableAux Γ₁ Γ₂)
    (cfg : TM2.Cfg first.tm.Γ first.tm.Λ first.tm.σ)
    (label : first.tm.Λ) (hlabel : cfg.l = some label) :
    liftLeftThenTransferCfg first second cfg =
      liftLeftControlCfg first second cfg := by
  cases cfg with
  | mk cfgLabel state contents =>
      change cfgLabel = some label at hlabel
      subst cfgLabel
      rfl

/-- An exact finite run of the first machine is reproduced by the total
composition program in the same number of steps. The starting configuration
must be at a live first-machine label. A running endpoint remains in the left
phase, while a halted endpoint is redirected to the transfer entry. -/
theorem compositionProgram_left_run {Γ₀ Γ₁ Γ₂ : Type}
    (first : TM2ComputableAux Γ₀ Γ₁)
    (second : TM2ComputableAux Γ₁ Γ₂)
    (steps : ℕ)
    (cfg nextCfg : TM2.Cfg first.tm.Γ first.tm.Λ first.tm.σ)
    (label : first.tm.Λ) (scratch : List Γ₁)
    (hlabel : cfg.l = some label)
    (hrun :
      (flip Option.bind (TM2.step first.tm.m))^[steps] (some cfg) =
        some nextCfg) :
    (flip Option.bind (TM2.step (compositionProgram first second)))^[steps]
        (some (liftScratchCfg first second scratch
          (liftLeftControlCfg first second cfg))) =
      some (liftScratchCfg first second scratch
        (liftLeftThenTransferCfg first second nextCfg)) := by
  induction steps generalizing cfg label with
  | zero =>
      simp only [Function.iterate_zero_apply] at hrun ⊢
      injection hrun with hcfg
      subst nextCfg
      cases cfg with
      | mk currentLabel state contents =>
          change currentLabel = some label at hlabel
          cases currentLabel with
          | none => simp at hlabel
          | some currentLabel =>
              simp only [Option.some.injEq] at hlabel
              subst currentLabel
              rfl
  | succ steps ih =>
      cases cfg with
      | mk currentLabel state contents =>
          change currentLabel = some label at hlabel
          cases currentLabel with
          | none => simp at hlabel
          | some currentLabel =>
              simp only [Option.some.injEq] at hlabel
              subst currentLabel
              rw [Function.iterate_succ_apply] at hrun ⊢
              change
                (flip Option.bind (TM2.step first.tm.m))^[steps]
                    (TM2.step first.tm.m
                      (TM2.Cfg.mk (some label) state contents)) =
                  some nextCfg at hrun
              change
                (flip Option.bind
                    (TM2.step (compositionProgram first second)))^[steps]
                    (TM2.step (compositionProgram first second)
                      (liftScratchCfg first second scratch
                        (liftLeftControlCfg first second
                          (TM2.Cfg.mk (some label) state contents)))) =
                  some (liftScratchCfg first second scratch
                    (liftLeftThenTransferCfg first second nextCfg))
              rw [compositionProgram_left_step]
              let stepped := TM2.stepAux (first.tm.m label) state contents
              change
                (flip Option.bind (TM2.step first.tm.m))^[steps]
                    (some stepped) = some nextCfg at hrun
              change
                (flip Option.bind (TM2.step (compositionProgram first second)))^[steps]
                    (some (liftScratchCfg first second scratch
                      (liftLeftThenTransferCfg first second stepped))) =
                  some (liftScratchCfg first second scratch
                    (liftLeftThenTransferCfg first second nextCfg))
              cases hstepped : stepped.l with
              | none =>
                  cases steps with
                  | zero =>
                      simp only [Function.iterate_zero_apply] at hrun ⊢
                      injection hrun with hcfg
                      subst nextCfg
                      rfl
                  | succ steps =>
                      rw [Function.iterate_succ_apply] at hrun
                      change
                        (flip Option.bind (TM2.step first.tm.m))^[steps]
                            (TM2.step first.tm.m stepped) =
                          some nextCfg at hrun
                      have hstep : TM2.step first.tm.m stepped = none :=
                        step_of_halted first.tm.m stepped hstepped
                      rw [hstep] at hrun
                      rw [iterate_bind_none] at hrun
                      contradiction
              | some nextLabel =>
                  have hlift :
                      liftLeftThenTransferCfg first second stepped =
                        liftLeftControlCfg first second stepped :=
                    liftLeftThenTransferCfg_of_running first second stepped
                      nextLabel hstepped
                  rw [hlift]
                  exact ih stepped nextLabel hstepped hrun

/-- A first-machine run ending in a halted configuration reaches the canonical
transfer entry under the total composition program, with no component-step
overhead and with scratch storage unchanged. -/
theorem compositionProgram_left_run_to_transfer {Γ₀ Γ₁ Γ₂ : Type}
    (first : TM2ComputableAux Γ₀ Γ₁)
    (second : TM2ComputableAux Γ₁ Γ₂)
    (steps : ℕ)
    (cfg finalCfg : TM2.Cfg first.tm.Γ first.tm.Λ first.tm.σ)
    (label : first.tm.Λ) (scratch : List Γ₁)
    (hlabel : cfg.l = some label)
    (hrun :
      (flip Option.bind (TM2.step first.tm.m))^[steps] (some cfg) =
        some finalCfg)
    (hhalt : finalCfg.l = none) :
    (flip Option.bind (TM2.step (compositionProgram first second)))^[steps]
        (some (liftScratchCfg first second scratch
          (liftLeftControlCfg first second cfg))) =
      some (liftScratchCfg first second scratch
        (leftTransferEntryCfg first second finalCfg.var finalCfg.stk)) := by
  rw [compositionProgram_left_run first second steps cfg finalCfg label scratch
    hlabel hrun]
  cases finalCfg with
  | mk finalLabel finalState finalContents =>
      cases finalLabel with
      | none => rfl
      | some finalLabel => simp at hhalt

/-- Lift mathlib's exact execution witness for a first-machine computation to
an execution witness reaching transfer. The lifted witness records the same
step count as the original run. -/
def compositionProgram_left_evalsTo_transfer {Γ₀ Γ₁ Γ₂ : Type}
    (first : TM2ComputableAux Γ₀ Γ₁)
    (second : TM2ComputableAux Γ₁ Γ₂)
    (cfg finalCfg : TM2.Cfg first.tm.Γ first.tm.Λ first.tm.σ)
    (label : first.tm.Λ) (scratch : List Γ₁)
    (run : EvalsTo (TM2.step first.tm.m) cfg (some finalCfg))
    (hlabel : cfg.l = some label) (hhalt : finalCfg.l = none) :
    EvalsTo (TM2.step (compositionProgram first second))
      (liftScratchCfg first second scratch
        (liftLeftControlCfg first second cfg))
      (some (liftScratchCfg first second scratch
        (leftTransferEntryCfg first second finalCfg.var finalCfg.stk))) where
  steps := run.steps
  evals_in_steps :=
    compositionProgram_left_run_to_transfer first second run.steps cfg finalCfg
      label scratch hlabel run.evals_in_steps hhalt

end LeanNPHardness.MachineComposition
