import LeanNPHardness.MachineCompositionProgram

namespace LeanNPHardness.MachineComposition

open Computability Turing

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

/-- Combine arbitrary preserved first-machine stacks with the live stack
contents of a second-machine configuration. This is the stack layout needed
after transfer: running the second component must not discard the first
component's work stacks. -/
def rightPhaseStacks {Γ₀ Γ₁ Γ₂ : Type}
    (first : TM2ComputableAux Γ₀ Γ₁)
    (second : TM2ComputableAux Γ₁ Γ₂)
    (leftContents : ∀ k, List (first.tm.Γ k))
    (rightContents : ∀ k, List (second.tm.Γ k)) :
    ∀ k, List (StackAlphabet first.tm second.tm k)
  | Sum.inl k => leftContents k
  | Sum.inr k => rightContents k

@[simp]
theorem rightPhaseStacks_left {Γ₀ Γ₁ Γ₂ : Type}
    (first : TM2ComputableAux Γ₀ Γ₁)
    (second : TM2ComputableAux Γ₁ Γ₂)
    (leftContents : ∀ k, List (first.tm.Γ k))
    (rightContents : ∀ k, List (second.tm.Γ k)) (k : first.tm.K) :
    rightPhaseStacks first second leftContents rightContents (Sum.inl k) =
      leftContents k :=
  rfl

@[simp]
theorem rightPhaseStacks_right {Γ₀ Γ₁ Γ₂ : Type}
    (first : TM2ComputableAux Γ₀ Γ₁)
    (second : TM2ComputableAux Γ₁ Γ₂)
    (leftContents : ∀ k, List (first.tm.Γ k))
    (rightContents : ∀ k, List (second.tm.Γ k)) (k : second.tm.K) :
    rightPhaseStacks first second leftContents rightContents (Sum.inr k) =
      rightContents k :=
  rfl

/-- Updating a second-machine stack preserves every first-machine stack in
the right-phase combined layout. -/
theorem rightPhaseStacks_update {Γ₀ Γ₁ Γ₂ : Type}
    (first : TM2ComputableAux Γ₀ Γ₁)
    (second : TM2ComputableAux Γ₁ Γ₂)
    (leftContents : ∀ k, List (first.tm.Γ k))
    (rightContents : ∀ k, List (second.tm.Γ k))
    (k : second.tm.K) (value : List (second.tm.Γ k)) :
    rightPhaseStacks first second leftContents
        (Function.update rightContents k value) =
      Function.update
        (rightPhaseStacks first second leftContents rightContents)
        (Sum.inr k) value := by
  funext index
  cases index with
  | inl j =>
      simp
  | inr j =>
      by_cases h : j = k
      · subst j
        simp
      · have hsum :
            (Sum.inr j : StackIndex first.tm second.tm) ≠ Sum.inr k := by
          intro equality
          exact h (Sum.inr.inj equality)
        simp [h, hsum]

/-- Embed a second-machine configuration into the final composition layout
while preserving arbitrary first-machine stacks and scratch contents. -/
def rightPhaseCfg {Γ₀ Γ₁ Γ₂ : Type}
    (first : TM2ComputableAux Γ₀ Γ₁)
    (second : TM2ComputableAux Γ₁ Γ₂)
    (leftContents : ∀ k, List (first.tm.Γ k)) (scratch : List Γ₁)
    (cfg : TM2.Cfg second.tm.Γ second.tm.Λ second.tm.σ) :
    TM2.Cfg (TransferStackAlphabet first second)
      (ControlLabel first second) (ControlState first second) where
  l := cfg.l.map (rightLabel first second)
  var := cfg.l.elim
    (leftState first second first.tm.initialState)
    (fun _ => rightState first second cfg.var)
  stk := extendStacks first second
    (rightPhaseStacks first second leftContents cfg.stk) scratch

/-- Lifting a second-machine statement into combined control preserves
arbitrary first-machine stack contents. -/
private theorem liftRightThenHalt_stepAux_preserving_left {Γ₀ Γ₁ Γ₂ : Type}
    (first : TM2ComputableAux Γ₀ Γ₁)
    (second : TM2ComputableAux Γ₁ Γ₂)
    (stmt : TM2.Stmt second.tm.Γ second.tm.Λ second.tm.σ)
    (state : second.tm.σ)
    (leftContents : ∀ k, List (first.tm.Γ k))
    (rightContents : ∀ k, List (second.tm.Γ k)) :
    TM2.stepAux (liftRightThenHaltStmt first second stmt)
        (rightState first second state)
        (rightPhaseStacks first second leftContents rightContents) =
      { l := (TM2.stepAux stmt state rightContents).l.map
          (rightLabel first second)
        var := (TM2.stepAux stmt state rightContents).l.elim
          (leftState first second first.tm.initialState)
          (fun _ => rightState first second
            (TM2.stepAux stmt state rightContents).var)
        stk := rightPhaseStacks first second leftContents
          (TM2.stepAux stmt state rightContents).stk } := by
  induction stmt generalizing state rightContents with
  | push k write next ih =>
      simp only [liftRightThenHaltStmt, TM2.stepAux,
        rightStateValue_rightState]
      rw [← rightPhaseStacks_update]
      exact ih _ _
  | peek k read next ih =>
      simpa only [liftRightThenHaltStmt, TM2.stepAux,
        rightStateValue_rightState, rightPhaseStacks_right] using
        ih (read state (rightContents k).head?) rightContents
  | pop k read next ih =>
      simp only [liftRightThenHaltStmt, TM2.stepAux,
        rightStateValue_rightState, rightPhaseStacks_right]
      rw [← rightPhaseStacks_update]
      exact ih _ _
  | load update next ih =>
      simpa only [liftRightThenHaltStmt, TM2.stepAux,
        rightStateValue_rightState] using ih (update state) rightContents
  | branch test yes no ihYes ihNo =>
      by_cases h : test state
      · simpa only [liftRightThenHaltStmt, TM2.stepAux,
          rightStateValue_rightState, h, cond_true] using
          ihYes state rightContents
      · simpa only [liftRightThenHaltStmt, TM2.stepAux,
          rightStateValue_rightState, h, cond_false] using
          ihNo state rightContents
  | goto next =>
      rfl
  | halt =>
      rfl

/-- One second-machine step is simulated by the total composition program
while arbitrary first-machine stacks and scratch contents remain unchanged.
A reached halt uses the composed machine's canonical initial state. -/
theorem compositionProgram_right_step_preserving_left {Γ₀ Γ₁ Γ₂ : Type}
    (first : TM2ComputableAux Γ₀ Γ₁)
    (second : TM2ComputableAux Γ₁ Γ₂)
    (leftContents : ∀ k, List (first.tm.Γ k)) (scratch : List Γ₁)
    (cfg : TM2.Cfg second.tm.Γ second.tm.Λ second.tm.σ) :
    TM2.step (compositionProgram first second)
        (rightPhaseCfg first second leftContents scratch cfg) =
      Option.map (rightPhaseCfg first second leftContents scratch)
        (TM2.step second.tm.m cfg) := by
  cases cfg with
  | mk label state rightContents =>
      cases label with
      | none =>
          rfl
      | some label =>
          simp only [rightPhaseCfg, TM2.step, Option.map_some, Option.elim_some,
            compositionProgram, rightLabel]
          rw [liftScratch_stepAux,
            liftRightThenHalt_stepAux_preserving_left]
          rfl

/-- Any exact finite second-machine run is reproduced by the total
composition program with the same step count, preserving the first-machine
stacks and scratch contents. -/
theorem compositionProgram_right_run {Γ₀ Γ₁ Γ₂ : Type}
    (first : TM2ComputableAux Γ₀ Γ₁)
    (second : TM2ComputableAux Γ₁ Γ₂)
    (steps : ℕ)
    (cfg nextCfg : TM2.Cfg second.tm.Γ second.tm.Λ second.tm.σ)
    (leftContents : ∀ k, List (first.tm.Γ k)) (scratch : List Γ₁)
    (hrun :
      (flip Option.bind (TM2.step second.tm.m))^[steps] (some cfg) =
        some nextCfg) :
    (flip Option.bind (TM2.step (compositionProgram first second)))^[steps]
        (some (rightPhaseCfg first second leftContents scratch cfg)) =
      some (rightPhaseCfg first second leftContents scratch nextCfg) := by
  induction steps generalizing cfg with
  | zero =>
      simp only [Function.iterate_zero_apply] at hrun ⊢
      injection hrun with hcfg
      subst nextCfg
      rfl
  | succ steps ih =>
      rw [Function.iterate_succ_apply] at hrun ⊢
      change
        (flip Option.bind (TM2.step second.tm.m))^[steps]
            (TM2.step second.tm.m cfg) = some nextCfg at hrun
      change
        (flip Option.bind (TM2.step (compositionProgram first second)))^[steps]
            (TM2.step (compositionProgram first second)
              (rightPhaseCfg first second leftContents scratch cfg)) =
          some (rightPhaseCfg first second leftContents scratch nextCfg)
      rw [compositionProgram_right_step_preserving_left]
      cases hstep : TM2.step second.tm.m cfg with
      | none =>
          rw [hstep] at hrun
          rw [iterate_bind_none] at hrun
          contradiction
      | some stepped =>
          simp only [Option.map_some]
          rw [hstep] at hrun
          exact ih stepped hrun

/-- Lift mathlib's exact execution witness for the second component through
the total composition program without losing the original step count or the
preserved first-machine and scratch stacks. -/
def compositionProgram_right_evalsTo {Γ₀ Γ₁ Γ₂ : Type}
    (first : TM2ComputableAux Γ₀ Γ₁)
    (second : TM2ComputableAux Γ₁ Γ₂)
    (cfg finalCfg : TM2.Cfg second.tm.Γ second.tm.Λ second.tm.σ)
    (leftContents : ∀ k, List (first.tm.Γ k)) (scratch : List Γ₁)
    (run : EvalsTo (TM2.step second.tm.m) cfg (some finalCfg)) :
    EvalsTo (TM2.step (compositionProgram first second))
      (rightPhaseCfg first second leftContents scratch cfg)
      (some (rightPhaseCfg first second leftContents scratch finalCfg)) where
  steps := run.steps
  evals_in_steps :=
    compositionProgram_right_run first second run.steps cfg finalCfg
      leftContents scratch run.evals_in_steps

/-- The second-machine configuration represented by a combined stack family
at the canonical right-phase entry point. -/
def rightEntryMachineCfg {Γ₀ Γ₁ Γ₂ : Type}
    (first : TM2ComputableAux Γ₀ Γ₁)
    (second : TM2ComputableAux Γ₁ Γ₂)
    (contents : ∀ k, List (StackAlphabet first.tm second.tm k)) :
    TM2.Cfg second.tm.Γ second.tm.Λ second.tm.σ where
  l := some second.tm.main
  var := second.tm.initialState
  stk k := contents (Sum.inr k)

/-- The transfer loop's `rightEntryCfg` is exactly the right-phase embedding
of the represented second-machine entry configuration, with the first-machine
half of the combined stack family preserved. -/
theorem rightEntryCfg_eq_rightPhaseCfg {Γ₀ Γ₁ Γ₂ : Type}
    (first : TM2ComputableAux Γ₀ Γ₁)
    (second : TM2ComputableAux Γ₁ Γ₂)
    (contents : ∀ k, List (StackAlphabet first.tm second.tm k))
    (scratch : List Γ₁) :
    rightEntryCfg first second contents scratch =
      rightPhaseCfg first second (fun k => contents (Sum.inl k)) scratch
        (rightEntryMachineCfg first second contents) := by
  congr 1
  funext index
  cases index <;> rfl

/-- Lift a second-machine execution witness directly from the canonical
configuration produced by the transfer loop. Arbitrary preserved first-machine
stacks remain present throughout the right phase. -/
def compositionProgram_rightEntry_evalsTo {Γ₀ Γ₁ Γ₂ : Type}
    (first : TM2ComputableAux Γ₀ Γ₁)
    (second : TM2ComputableAux Γ₁ Γ₂)
    (contents : ∀ k, List (StackAlphabet first.tm second.tm k))
    (scratch : List Γ₁)
    (finalCfg : TM2.Cfg second.tm.Γ second.tm.Λ second.tm.σ)
    (run : EvalsTo (TM2.step second.tm.m)
      (rightEntryMachineCfg first second contents) (some finalCfg)) :
    EvalsTo (TM2.step (compositionProgram first second))
      (rightEntryCfg first second contents scratch)
      (some (rightPhaseCfg first second
        (fun k => contents (Sum.inl k)) scratch finalCfg)) where
  steps := run.steps
  evals_in_steps := by
    rw [rightEntryCfg_eq_rightPhaseCfg]
    exact compositionProgram_right_run first second run.steps
      (rightEntryMachineCfg first second contents) finalCfg
      (fun k => contents (Sum.inl k)) scratch run.evals_in_steps

/-- The combined component stacks after the transfer phase has emptied the
first output stack and copied its order-preserving alphabet conversion into
the second input stack. -/
def transferredContents {Γ₀ Γ₁ Γ₂ : Type}
    (first : TM2ComputableAux Γ₀ Γ₁)
    (second : TM2ComputableAux Γ₁ Γ₂)
    (contents : ∀ k, List (first.tm.Γ k)) :
    ∀ k, List (StackAlphabet first.tm second.tm k) :=
  Function.update
    (Function.update (leftStacks first.tm second.tm contents)
      (Sum.inl first.tm.k₁) [])
    (Sum.inr second.tm.k₀)
    ((contents first.tm.k₁).map (middleAlphabetEquiv first second))

/-- The lifted transfer entry produced by a halted first-machine run is the
exact starting configuration expected by the whole-list transfer theorem.
The explicit no-op updates record the empty second input and unchanged first
output needed by that theorem's accumulator interface. -/
theorem liftScratch_leftTransferEntryCfg_eq_transferStart
    {Γ₀ Γ₁ Γ₂ : Type}
    (first : TM2ComputableAux Γ₀ Γ₁)
    (second : TM2ComputableAux Γ₁ Γ₂)
    (state : first.tm.σ)
    (contents : ∀ k, List (first.tm.Γ k)) :
    liftScratchCfg first second []
        (leftTransferEntryCfg first second state contents) =
      transferActionCfg first second (.phase .reverseOutput)
        (leftState first second state)
        (Function.update
          (Function.update (leftStacks first.tm second.tm contents)
            (Sum.inr second.tm.k₀) [])
          (Sum.inl first.tm.k₁) (contents first.tm.k₁)) [] := by
  unfold liftScratchCfg leftTransferEntryCfg transferActionCfg
  congr 1
  funext index
  cases index with
  | inl combinedIndex =>
      cases combinedIndex with
      | inl index =>
          by_cases h : index = first.tm.k₁
          · subst index
            simp [extendStacks, leftStacks]
          · have hsum :
                (Sum.inl index : StackIndex first.tm second.tm) ≠
                  Sum.inl first.tm.k₁ := by
                intro equality
                exact h (Sum.inl.inj equality)
            simp [extendStacks, leftStacks, hsum]
      | inr index =>
          by_cases h : index = second.tm.k₀
          · subst index
            simp [extendStacks, leftStacks]
          · have hsum :
                (Sum.inr index : StackIndex first.tm second.tm) ≠
                  Sum.inr second.tm.k₀ := by
                intro equality
                exact h (Sum.inr.inj equality)
            simp [extendStacks, leftStacks, hsum]
  | inr unitIndex =>
      cases unitIndex
      simp [extendStacks]

/-- The total composition program reproduces a complete first-machine run,
the order-preserving intermediate transfer, and a complete second-machine run.
Its exact step count is the sum of the two component witnesses and
`4 * intermediate.length + 4` transfer steps. -/
theorem compositionProgram_complete_run {Γ₀ Γ₁ Γ₂ : Type}
    (first : TM2ComputableAux Γ₀ Γ₁)
    (second : TM2ComputableAux Γ₁ Γ₂)
    (firstCfg firstFinal : TM2.Cfg first.tm.Γ first.tm.Λ first.tm.σ)
    (firstLabel : first.tm.Λ)
    (firstRun : EvalsTo (TM2.step first.tm.m) firstCfg (some firstFinal))
    (hlabel : firstCfg.l = some firstLabel)
    (hhalt : firstFinal.l = none)
    (secondFinal : TM2.Cfg second.tm.Γ second.tm.Λ second.tm.σ)
    (secondRun : EvalsTo (TM2.step second.tm.m)
      (rightEntryMachineCfg first second
        (transferredContents first second firstFinal.stk))
      (some secondFinal)) :
    (flip Option.bind (TM2.step (compositionProgram first second)))^[
        secondRun.steps +
          (4 * (firstFinal.stk first.tm.k₁).length + 4 + firstRun.steps)]
      (some (liftScratchCfg first second []
        (liftLeftControlCfg first second firstCfg))) =
      some (rightPhaseCfg first second
        (fun k =>
          transferredContents first second firstFinal.stk (Sum.inl k))
        [] secondFinal) := by
  have leftRun :=
    compositionProgram_left_run_to_transfer first second firstRun.steps
      firstCfg firstFinal firstLabel [] hlabel firstRun.evals_in_steps hhalt
  have transferRun :=
    compositionProgram_transfer_whole_list first second
      (leftState first second firstFinal.var)
      (leftStacks first.tm second.tm firstFinal.stk)
      (firstFinal.stk first.tm.k₁) []
  have leftAndTransfer :
      (flip Option.bind (TM2.step (compositionProgram first second)))^[
          4 * (firstFinal.stk first.tm.k₁).length + 4 + firstRun.steps]
        (some (liftScratchCfg first second []
          (liftLeftControlCfg first second firstCfg))) =
        some (rightEntryCfg first second
          (transferredContents first second firstFinal.stk) []) := by
    rw [Function.iterate_add_apply, leftRun]
    rw [liftScratch_leftTransferEntryCfg_eq_transferStart]
    simpa [transferredContents] using transferRun
  rw [Function.iterate_add_apply, leftAndTransfer]
  exact (compositionProgram_rightEntry_evalsTo first second
    (transferredContents first second firstFinal.stk) [] secondFinal
    secondRun).evals_in_steps

/-- Package `compositionProgram_complete_run` as mathlib's exact execution
witness, retaining the explicit summed step count. -/
def compositionProgram_complete_evalsTo {Γ₀ Γ₁ Γ₂ : Type}
    (first : TM2ComputableAux Γ₀ Γ₁)
    (second : TM2ComputableAux Γ₁ Γ₂)
    (firstCfg firstFinal : TM2.Cfg first.tm.Γ first.tm.Λ first.tm.σ)
    (firstLabel : first.tm.Λ)
    (firstRun : EvalsTo (TM2.step first.tm.m) firstCfg (some firstFinal))
    (hlabel : firstCfg.l = some firstLabel)
    (hhalt : firstFinal.l = none)
    (secondFinal : TM2.Cfg second.tm.Γ second.tm.Λ second.tm.σ)
    (secondRun : EvalsTo (TM2.step second.tm.m)
      (rightEntryMachineCfg first second
        (transferredContents first second firstFinal.stk))
      (some secondFinal)) :
    EvalsTo (TM2.step (compositionProgram first second))
      (liftScratchCfg first second []
        (liftLeftControlCfg first second firstCfg))
      (some (rightPhaseCfg first second
        (fun k =>
          transferredContents first second firstFinal.stk (Sum.inl k))
        [] secondFinal)) where
  steps := secondRun.steps +
    (4 * (firstFinal.stk first.tm.k₁).length + 4 + firstRun.steps)
  evals_in_steps := compositionProgram_complete_run first second firstCfg
    firstFinal firstLabel firstRun hlabel hhalt secondFinal secondRun

/-- The composed machine's canonical input configuration is exactly the
scratch-layout embedding of the first machine's canonical input
configuration. -/
theorem compositionMachine_initList {Γ₀ Γ₁ Γ₂ : Type} [Fintype Γ₁]
    (first : TM2ComputableAux Γ₀ Γ₁)
    (second : TM2ComputableAux Γ₁ Γ₂)
    (input : List (first.tm.Γ first.tm.k₀)) :
    initList (compositionMachine first second) input =
      liftScratchCfg first second []
        (liftLeftControlCfg first second (initList first.tm input)) := by
  unfold initList compositionMachine liftScratchCfg liftLeftControlCfg
  congr 1
  funext index
  cases index with
  | inl combinedIndex =>
      cases combinedIndex with
      | inl k =>
          by_cases h : k = first.tm.k₀
          · subst k
            simp [extendStacks, leftStacks, transferLeftIndex]
          · have hbase :
                (Sum.inl k : StackIndex first.tm second.tm) ≠
                  Sum.inl first.tm.k₀ := by
              intro equality
              exact h (Sum.inl.inj equality)
            have hinput :
                (Sum.inl (Sum.inl k) : TransferStackIndex first second) ≠
                  Sum.inl (Sum.inl first.tm.k₀) := by
              intro equality
              exact hbase (Sum.inl.inj equality)
            simp [extendStacks, leftStacks, transferLeftIndex, h, hinput]
      | inr k =>
          have hinput :
              (Sum.inl (Sum.inr k) : TransferStackIndex first second) ≠
                Sum.inl (Sum.inl first.tm.k₀) := by
            simp
          simp [extendStacks, leftStacks, transferLeftIndex, hinput]
  | inr unitIndex =>
      cases unitIndex
      simp [extendStacks, transferLeftIndex]

/-- After a canonical first-machine halt and the transfer update, the
represented second-machine entry is its canonical input configuration with
the intermediate alphabet conversion applied. -/
theorem rightEntryMachineCfg_transferred_haltList {Γ₀ Γ₁ Γ₂ : Type}
    (first : TM2ComputableAux Γ₀ Γ₁)
    (second : TM2ComputableAux Γ₁ Γ₂)
    (intermediate : List (first.tm.Γ first.tm.k₁)) :
    rightEntryMachineCfg first second
        (transferredContents first second
          (haltList first.tm intermediate).stk) =
      initList second.tm
        (intermediate.map (middleAlphabetEquiv first second)) := by
  unfold rightEntryMachineCfg initList
  congr 1
  funext k
  by_cases h : k = second.tm.k₀
  · subst k
    simp [transferredContents, haltList]
  · have hsum :
        (Sum.inr k : StackIndex first.tm second.tm) ≠ Sum.inr second.tm.k₀ := by
      intro equality
      exact h (Sum.inr.inj equality)
    simp [transferredContents, haltList, h, hsum]

/-- A canonical second-machine halt, combined with the emptied canonical
first-machine stacks and scratch stack, is exactly the composed machine's
canonical halt configuration. -/
theorem rightPhaseCfg_haltList {Γ₀ Γ₁ Γ₂ : Type} [Fintype Γ₁]
    (first : TM2ComputableAux Γ₀ Γ₁)
    (second : TM2ComputableAux Γ₁ Γ₂)
    (intermediate : List (first.tm.Γ first.tm.k₁))
    (output : List (second.tm.Γ second.tm.k₁)) :
    rightPhaseCfg first second
        (fun k => transferredContents first second
          (haltList first.tm intermediate).stk (Sum.inl k)) []
        (haltList second.tm output) =
      haltList (compositionMachine first second) output := by
  unfold rightPhaseCfg haltList compositionMachine
  congr 1
  funext index
  cases index with
  | inl combinedIndex =>
      cases combinedIndex with
      | inl k =>
          have hout :
              (Sum.inl (Sum.inl k) : TransferStackIndex first second) ≠
                Sum.inl (Sum.inr second.tm.k₁) := by
            simp
          by_cases h : k = first.tm.k₁
          · subst k
            simp [rightPhaseStacks, transferredContents, extendStacks,
              transferRightIndex, hout]
          · have hsum :
                (Sum.inl k : StackIndex first.tm second.tm) ≠
                  Sum.inl first.tm.k₁ := by
                intro equality
                exact h (Sum.inl.inj equality)
            simp [rightPhaseStacks, transferredContents, extendStacks,
              leftStacks, h, transferRightIndex, hsum, hout]
      | inr k =>
          by_cases h : k = second.tm.k₁
          · subst k
            simp [rightPhaseStacks, extendStacks, transferRightIndex]
          · have hbase :
                (Sum.inr k : StackIndex first.tm second.tm) ≠
                  Sum.inr second.tm.k₁ := by
              intro equality
              exact h (Sum.inr.inj equality)
            have houtput :
                (Sum.inl (Sum.inr k) : TransferStackIndex first second) ≠
                  Sum.inl (Sum.inr second.tm.k₁) := by
              intro equality
              exact hbase (Sum.inl.inj equality)
            simp [rightPhaseStacks, extendStacks, h, transferRightIndex,
              houtput]
  | inr unitIndex =>
      cases unitIndex
      simp [extendStacks, transferRightIndex]

/-- Canonical list-level output witnesses for two component machines compose
through `compositionMachine`. The first output is converted through the shared
middle alphabet before becoming the second input. -/
def compositionMachine_outputs {Γ₀ Γ₁ Γ₂ : Type} [Fintype Γ₁]
    (first : TM2ComputableAux Γ₀ Γ₁)
    (second : TM2ComputableAux Γ₁ Γ₂)
    (input : List (first.tm.Γ first.tm.k₀))
    (intermediate : List (first.tm.Γ first.tm.k₁))
    (output : List (second.tm.Γ second.tm.k₁))
    (firstRun : TM2Outputs first.tm input (some intermediate))
    (secondRun : TM2Outputs second.tm
      (intermediate.map (middleAlphabetEquiv first second)) (some output)) :
    TM2Outputs (compositionMachine first second) input (some output) := by
  let liftedSecondRun : EvalsTo (TM2.step second.tm.m)
      (rightEntryMachineCfg first second
        (transferredContents first second (haltList first.tm intermediate).stk))
      (some (haltList second.tm output)) := by
    rw [rightEntryMachineCfg_transferred_haltList]
    exact secondRun
  have complete := compositionProgram_complete_evalsTo first second
    (initList first.tm input) (haltList first.tm intermediate) first.tm.main
    firstRun rfl rfl (haltList second.tm output) liftedSecondRun
  unfold TM2Outputs
  rw [compositionMachine_initList]
  simpa [FinTM2.step, compositionMachine,
    rightPhaseCfg_haltList first second intermediate output] using complete

/-- Mapping a canonical middle-alphabet list into the first machine's output
alphabet and then across the composition bridge is the same as mapping it
directly into the second machine's input alphabet. -/
theorem map_outputAlphabet_invFun_middleAlphabetEquiv
    {Γ₀ Γ₁ Γ₂ : Type}
    (first : TM2ComputableAux Γ₀ Γ₁)
    (second : TM2ComputableAux Γ₁ Γ₂)
    (symbols : List Γ₁) :
    (symbols.map first.outputAlphabet.invFun).map
        (middleAlphabetEquiv first second) =
      symbols.map second.inputAlphabet.invFun := by
  simp [middleAlphabetEquiv, List.map_map]

/-- Checked function-level correctness of sequential machine composition.
This bundles the structural composition machine with the two component
`outputsFun` witnesses. Its polynomial runtime bound remains separate. -/
def compositionComputable {α β γ : Type}
    (sourceEncoding : FinEncoding α)
    (middleEncoding : FinEncoding β)
    (targetEncoding : FinEncoding γ)
    (f : α → β) (g : β → γ)
    (first : TM2Computable sourceEncoding middleEncoding f)
    (second : TM2Computable middleEncoding targetEncoding g) :
    TM2Computable sourceEncoding targetEncoding (g ∘ f) where
  toTM2ComputableAux :=
    compositionAux first.toTM2ComputableAux second.toTM2ComputableAux
  outputsFun a := by
    apply compositionMachine_outputs first.toTM2ComputableAux
      second.toTM2ComputableAux
      (List.map first.inputAlphabet.invFun (sourceEncoding.encode a))
      (List.map first.outputAlphabet.invFun (middleEncoding.encode (f a)))
      (List.map second.outputAlphabet.invFun
        (targetEncoding.encode (g (f a))))
      (first.outputsFun a)
    rw [map_outputAlphabet_invFun_middleAlphabetEquiv]
    exact second.outputsFun (f a)

end LeanNPHardness.MachineComposition
