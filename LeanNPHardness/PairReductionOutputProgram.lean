import LeanNPHardness.PairOutputTransfer
import LeanNPHardness.PairReductionProgram

namespace LeanNPHardness.MachineAdapters

open Turing

/-- Finite control labels for the existing pair/reduction dispatcher followed
by output/certificate reassembly. -/
def PairReductionOutputControlLabel {Γ₀ Γ₁ Δ : Type}
    (computer : TM2ComputableAux Γ₀ Γ₁) :=
  PairReductionControlLabel (Δ := Δ) computer ⊕
    PairOutputTransferLabel Γ₁ Δ

instance {Γ₀ Γ₁ Δ : Type} [Fintype Γ₀] [Fintype Γ₁] [Fintype Δ]
    (computer : TM2ComputableAux Γ₀ Γ₁) :
    Fintype (PairReductionOutputControlLabel (Δ := Δ) computer) := by
  letI : Fintype (PairReductionControlLabel (Δ := Δ) computer) :=
    inferInstance
  exact inferInstanceAs
    (Fintype
      (PairReductionControlLabel (Δ := Δ) computer ⊕
        PairOutputTransferLabel Γ₁ Δ))

/-- The old dispatcher state and the output-transfer optional-symbol state
occupy disjoint branches. -/
def PairReductionOutputControlState {Γ₀ Γ₁ Δ : Type}
    (computer : TM2ComputableAux Γ₀ Γ₁) :=
  PairReductionControlState (Δ := Δ) computer ⊕ Option (Sum Γ₁ Δ)

instance {Γ₀ Γ₁ Δ : Type} [Fintype Γ₀] [Fintype Γ₁] [Fintype Δ]
    (computer : TM2ComputableAux Γ₀ Γ₁) :
    Fintype (PairReductionOutputControlState (Δ := Δ) computer) := by
  letI : Fintype (PairReductionControlState (Δ := Δ) computer) :=
    inferInstance
  exact inferInstanceAs
    (Fintype
      (PairReductionControlState (Δ := Δ) computer ⊕ Option (Sum Γ₁ Δ)))

def pairReductionOutputReductionLabel {Γ₀ Γ₁ Δ : Type}
    (computer : TM2ComputableAux Γ₀ Γ₁)
    (label : PairReductionControlLabel (Δ := Δ) computer) :
    PairReductionOutputControlLabel (Δ := Δ) computer :=
  Sum.inl label

def pairReductionOutputTransferLabel {Γ₀ Γ₁ Δ : Type}
    (computer : TM2ComputableAux Γ₀ Γ₁)
    (label : PairOutputTransferLabel Γ₁ Δ) :
    PairReductionOutputControlLabel (Δ := Δ) computer :=
  Sum.inr label

def pairReductionOutputReductionState {Γ₀ Γ₁ Δ : Type}
    (computer : TM2ComputableAux Γ₀ Γ₁)
    (state : PairReductionControlState (Δ := Δ) computer) :
    PairReductionOutputControlState (Δ := Δ) computer :=
  Sum.inl state

def pairReductionOutputTransferState {Γ₀ Γ₁ Δ : Type}
    (computer : TM2ComputableAux Γ₀ Γ₁) (state : Option (Sum Γ₁ Δ)) :
    PairReductionOutputControlState (Δ := Δ) computer :=
  Sum.inr state

/-- Recover the old dispatcher state while its control branch is active. The
fallback is never reached by the checked phase simulation. -/
def pairReductionOutputReductionStateValue {Γ₀ Γ₁ Δ : Type}
    (computer : TM2ComputableAux Γ₀ Γ₁) :
    PairReductionOutputControlState (Δ := Δ) computer →
      PairReductionControlState (Δ := Δ) computer
  | Sum.inl state => state
  | Sum.inr _ => pairAdapterControlState computer none

/-- Recover the output-transfer state while its control branch is active. -/
def pairReductionOutputTransferStateValue {Γ₀ Γ₁ Δ : Type}
    (computer : TM2ComputableAux Γ₀ Γ₁) :
    PairReductionOutputControlState (Δ := Δ) computer → Option (Sum Γ₁ Δ)
  | Sum.inl _ => none
  | Sum.inr state => state

@[simp]
theorem pairReductionOutputReductionStateValue_reduction
    {Γ₀ Γ₁ Δ : Type} (computer : TM2ComputableAux Γ₀ Γ₁)
    (state : PairReductionControlState (Δ := Δ) computer) :
    pairReductionOutputReductionStateValue computer
        (pairReductionOutputReductionState computer state) = state :=
  rfl

@[simp]
theorem pairReductionOutputTransferStateValue_transfer
    {Γ₀ Γ₁ Δ : Type} (computer : TM2ComputableAux Γ₀ Γ₁)
    (state : Option (Sum Γ₁ Δ)) :
    pairReductionOutputTransferStateValue computer
        (pairReductionOutputTransferState (Δ := Δ) computer state) = state :=
  rfl

/-- Lift an old dispatcher statement to the output-extended stack family. A
reached halt enters output/certificate reassembly in the same machine step. -/
def liftPairReductionThenOutputStmt {Γ₀ Γ₁ Δ : Type}
    (computer : TM2ComputableAux Γ₀ Γ₁) :
    TM2.Stmt (PairReductionStackAlphabet computer Δ)
        (PairReductionControlLabel (Δ := Δ) computer)
        (PairReductionControlState (Δ := Δ) computer) →
      TM2.Stmt (PairOutputStackAlphabet computer Δ)
        (PairReductionOutputControlLabel (Δ := Δ) computer)
        (PairReductionOutputControlState (Δ := Δ) computer)
  | .push index write next =>
      .push (Sum.inl index)
        (fun state => write
          (pairReductionOutputReductionStateValue computer state))
        (liftPairReductionThenOutputStmt computer next)
  | .peek index read next =>
      .peek (Sum.inl index)
        (fun state symbol => pairReductionOutputReductionState computer
          (read (pairReductionOutputReductionStateValue computer state)
            symbol))
        (liftPairReductionThenOutputStmt computer next)
  | .pop index read next =>
      .pop (Sum.inl index)
        (fun state symbol => pairReductionOutputReductionState computer
          (read (pairReductionOutputReductionStateValue computer state)
            symbol))
        (liftPairReductionThenOutputStmt computer next)
  | .load update next =>
      .load
        (fun state => pairReductionOutputReductionState computer
          (update (pairReductionOutputReductionStateValue computer state)))
        (liftPairReductionThenOutputStmt computer next)
  | .branch test yes no =>
      .branch
        (fun state => test
          (pairReductionOutputReductionStateValue computer state))
        (liftPairReductionThenOutputStmt computer yes)
        (liftPairReductionThenOutputStmt computer no)
  | .goto next =>
      .goto (fun state => pairReductionOutputReductionLabel computer
        (next (pairReductionOutputReductionStateValue computer state)))
  | .halt =>
      .load (fun _ => pairReductionOutputTransferState computer none)
        (.goto (fun _ => pairReductionOutputTransferLabel computer
          .certificateReverseScan))

/-- Lift output-transfer control into the combined dispatcher while retaining
its ordinary final halt. -/
def liftPairOutputTransferControlStmt {Γ₀ Γ₁ Δ : Type}
    (computer : TM2ComputableAux Γ₀ Γ₁) :
    TM2.Stmt (PairOutputStackAlphabet computer Δ)
        (PairOutputTransferLabel Γ₁ Δ) (Option (Sum Γ₁ Δ)) →
      TM2.Stmt (PairOutputStackAlphabet computer Δ)
        (PairReductionOutputControlLabel (Δ := Δ) computer)
        (PairReductionOutputControlState (Δ := Δ) computer)
  | .push index write next =>
      .push index
        (fun state => write
          (pairReductionOutputTransferStateValue computer state))
        (liftPairOutputTransferControlStmt computer next)
  | .peek index read next =>
      .peek index
        (fun state symbol => pairReductionOutputTransferState computer
          (read (pairReductionOutputTransferStateValue computer state) symbol))
        (liftPairOutputTransferControlStmt computer next)
  | .pop index read next =>
      .pop index
        (fun state symbol => pairReductionOutputTransferState computer
          (read (pairReductionOutputTransferStateValue computer state) symbol))
        (liftPairOutputTransferControlStmt computer next)
  | .load update next =>
      .load
        (fun state => pairReductionOutputTransferState computer
          (update (pairReductionOutputTransferStateValue computer state)))
        (liftPairOutputTransferControlStmt computer next)
  | .branch test yes no =>
      .branch
        (fun state => test
          (pairReductionOutputTransferStateValue computer state))
        (liftPairOutputTransferControlStmt computer yes)
        (liftPairOutputTransferControlStmt computer no)
  | .goto next =>
      .goto (fun state => pairReductionOutputTransferLabel computer
        (next (pairReductionOutputTransferStateValue computer state)))
  | .halt => .halt

/-- Total dispatcher from tagged-pair preprocessing through reduction and
output/certificate reassembly. -/
def pairReductionOutputProgram {Γ₀ Γ₁ Δ : Type}
    (computer : TM2ComputableAux Γ₀ Γ₁) :
    PairReductionOutputControlLabel (Δ := Δ) computer →
      TM2.Stmt (PairOutputStackAlphabet computer Δ)
        (PairReductionOutputControlLabel (Δ := Δ) computer)
        (PairReductionOutputControlState (Δ := Δ) computer)
  | Sum.inl label =>
      liftPairReductionThenOutputStmt computer
        (pairReductionProgram computer label)
  | Sum.inr label =>
      liftPairOutputTransferControlStmt computer
        (pairOutputTransferProgram computer label)

/-- Embed an old-dispatcher configuration and preserve arbitrary contents on
the two output-only stacks. A reached old halt denotes the output-transfer
entry point. -/
def liftPairReductionThenOutputCfg {Γ₀ Γ₁ Δ : Type}
    (computer : TM2ComputableAux Γ₀ Γ₁)
    (reducedReverse : List Γ₁) (output : List (Sum Γ₁ Δ))
    (cfg : TM2.Cfg (PairReductionStackAlphabet computer Δ)
      (PairReductionControlLabel (Δ := Δ) computer)
      (PairReductionControlState (Δ := Δ) computer)) :
    TM2.Cfg (PairOutputStackAlphabet computer Δ)
      (PairReductionOutputControlLabel (Δ := Δ) computer)
      (PairReductionOutputControlState (Δ := Δ) computer) where
  l := some (cfg.l.elim
    (pairReductionOutputTransferLabel computer .certificateReverseScan)
    (pairReductionOutputReductionLabel computer))
  var := cfg.l.elim
    (pairReductionOutputTransferState computer none)
    (fun _ => pairReductionOutputReductionState computer cfg.var)
  stk := pairOutputStacks computer cfg.stk reducedReverse output

/-- Embed an output-transfer configuration into combined control. -/
def liftPairOutputTransferControlCfg {Γ₀ Γ₁ Δ : Type}
    (computer : TM2ComputableAux Γ₀ Γ₁)
    (cfg : TM2.Cfg (PairOutputStackAlphabet computer Δ)
      (PairOutputTransferLabel Γ₁ Δ) (Option (Sum Γ₁ Δ))) :
    TM2.Cfg (PairOutputStackAlphabet computer Δ)
      (PairReductionOutputControlLabel (Δ := Δ) computer)
      (PairReductionOutputControlState (Δ := Δ) computer) where
  l := cfg.l.map (pairReductionOutputTransferLabel computer)
  var := pairReductionOutputTransferState computer cfg.var
  stk := cfg.stk

/-- Lifting an old-dispatcher statement commutes with one complete `stepAux`,
including stack updates and the reached-halt transition into reassembly. -/
theorem liftPairReductionThenOutput_stepAux {Γ₀ Γ₁ Δ : Type}
    (computer : TM2ComputableAux Γ₀ Γ₁)
    (stmt : TM2.Stmt (PairReductionStackAlphabet computer Δ)
      (PairReductionControlLabel (Δ := Δ) computer)
      (PairReductionControlState (Δ := Δ) computer))
    (state : PairReductionControlState (Δ := Δ) computer)
    (workingContents :
      ∀ index, List (PairReductionStackAlphabet computer Δ index))
    (reducedReverse : List Γ₁) (output : List (Sum Γ₁ Δ)) :
    TM2.stepAux (liftPairReductionThenOutputStmt computer stmt)
        (pairReductionOutputReductionState computer state)
        (pairOutputStacks computer workingContents reducedReverse output) =
      liftPairReductionThenOutputCfg computer reducedReverse output
        (TM2.stepAux stmt state workingContents) := by
  induction stmt generalizing state workingContents with
  | push index write next ih =>
      simp only [liftPairReductionThenOutputStmt, TM2.stepAux,
        pairReductionOutputReductionStateValue_reduction]
      rw [pairOutputStacks_working_update]
      exact ih _ _
  | peek index read next ih =>
      simpa only [liftPairReductionThenOutputStmt, TM2.stepAux,
        pairReductionOutputReductionStateValue_reduction,
        pairOutputStacks_working] using
        ih (read state (workingContents index).head?) workingContents
  | pop index read next ih =>
      simp only [liftPairReductionThenOutputStmt, TM2.stepAux,
        pairReductionOutputReductionStateValue_reduction,
        pairOutputStacks_working]
      rw [pairOutputStacks_working_update]
      exact ih _ _
  | load update next ih =>
      simpa only [liftPairReductionThenOutputStmt, TM2.stepAux,
        pairReductionOutputReductionStateValue_reduction] using
        ih (update state) workingContents
  | branch test yes no ihYes ihNo =>
      by_cases h : test state
      · simpa only [liftPairReductionThenOutputStmt, TM2.stepAux,
          pairReductionOutputReductionStateValue_reduction, h,
          cond_true] using ihYes state workingContents
      · simpa only [liftPairReductionThenOutputStmt, TM2.stepAux,
          pairReductionOutputReductionStateValue_reduction, h,
          cond_false] using ihNo state workingContents
  | goto next =>
      rfl
  | halt =>
      rfl

/-- One live step of the existing dispatcher is reproduced under combined
control while the output-only stacks remain unchanged. -/
theorem pairReductionOutputProgram_reduction_step {Γ₀ Γ₁ Δ : Type}
    (computer : TM2ComputableAux Γ₀ Γ₁)
    (label : PairReductionControlLabel (Δ := Δ) computer)
    (state : PairReductionControlState (Δ := Δ) computer)
    (workingContents :
      ∀ index, List (PairReductionStackAlphabet computer Δ index))
    (reducedReverse : List Γ₁) (output : List (Sum Γ₁ Δ)) :
    TM2.step (pairReductionOutputProgram computer)
        (liftPairReductionThenOutputCfg computer reducedReverse output
          (TM2.Cfg.mk (some label) state workingContents)) =
      some (liftPairReductionThenOutputCfg computer reducedReverse output
        (TM2.stepAux (pairReductionProgram computer label) state
          workingContents)) := by
  change some (TM2.stepAux
    (liftPairReductionThenOutputStmt computer
      (pairReductionProgram computer label))
    (pairReductionOutputReductionState computer state)
    (pairOutputStacks computer workingContents reducedReverse output)) = _
  rw [liftPairReductionThenOutput_stepAux]

private theorem pairReductionOutput_iterate_bind_none {α : Type}
    (step : α → Option α) (steps : ℕ) :
    (flip Option.bind step)^[steps] none = none := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
      rw [Function.iterate_succ_apply]
      exact ih

/-- Any exact finite old-dispatcher run is reproduced with the same step count
and unchanged output-only stacks. A halted final configuration is represented
by the live output-transfer entry configuration. -/
theorem pairReductionOutputProgram_reduction_run {Γ₀ Γ₁ Δ : Type}
    (computer : TM2ComputableAux Γ₀ Γ₁) (steps : ℕ)
    (cfg finalCfg : TM2.Cfg (PairReductionStackAlphabet computer Δ)
      (PairReductionControlLabel (Δ := Δ) computer)
      (PairReductionControlState (Δ := Δ) computer))
    (reducedReverse : List Γ₁) (output : List (Sum Γ₁ Δ))
    (run :
      (flip Option.bind (TM2.step (pairReductionProgram computer)))^[steps]
        (some cfg) = some finalCfg) :
    (flip Option.bind
        (TM2.step (pairReductionOutputProgram computer)))^[steps]
      (some (liftPairReductionThenOutputCfg computer reducedReverse output
        cfg)) =
      some (liftPairReductionThenOutputCfg computer reducedReverse output
        finalCfg) := by
  induction steps generalizing cfg with
  | zero =>
      simp only [Function.iterate_zero_apply, Option.some.injEq] at run ⊢
      subst finalCfg
      rfl
  | succ steps ih =>
      rw [Function.iterate_succ_apply] at run ⊢
      cases cfg with
      | mk label state workingContents =>
          cases label with
          | none =>
              simp only [flip, Option.bind_some, TM2.step] at run
              rw [pairReductionOutput_iterate_bind_none] at run
              contradiction
          | some label =>
              simp only [flip, Option.bind_some, TM2.step] at run
              change
                (flip Option.bind
                    (TM2.step (pairReductionOutputProgram computer)))^[steps]
                    (TM2.step (pairReductionOutputProgram computer)
                      (liftPairReductionThenOutputCfg computer reducedReverse
                        output
                        (TM2.Cfg.mk (some label) state workingContents))) =
                  some (liftPairReductionThenOutputCfg computer reducedReverse
                    output finalCfg)
              rw [pairReductionOutputProgram_reduction_step]
              exact ih _ run

/-- If one old-dispatcher step reaches its halt, the combined dispatcher enters
certificate reassembly in that same counted step and preserves both new stacks.
-/
theorem pairReductionOutputProgram_halt_to_output {Γ₀ Γ₁ Δ : Type}
    (computer : TM2ComputableAux Γ₀ Γ₁)
    (label : PairReductionControlLabel (Δ := Δ) computer)
    (state finalState : PairReductionControlState (Δ := Δ) computer)
    (workingContents finalContents :
      ∀ index, List (PairReductionStackAlphabet computer Δ index))
    (reducedReverse : List Γ₁) (output : List (Sum Γ₁ Δ))
    (halted : TM2.stepAux (pairReductionProgram computer label) state
      workingContents = TM2.Cfg.mk none finalState finalContents) :
    TM2.step (pairReductionOutputProgram computer)
        (liftPairReductionThenOutputCfg computer reducedReverse output
          (TM2.Cfg.mk (some label) state workingContents)) =
      some (liftPairOutputTransferControlCfg computer
        (TM2.Cfg.mk (some .certificateReverseScan) none
          (pairOutputStacks computer finalContents reducedReverse output))) := by
  rw [pairReductionOutputProgram_reduction_step, halted]
  rfl

/-- Output-transfer statement execution commutes exactly with the combined
control lift. -/
theorem liftPairOutputTransferControl_stepAux {Γ₀ Γ₁ Δ : Type}
    (computer : TM2ComputableAux Γ₀ Γ₁)
    (stmt : TM2.Stmt (PairOutputStackAlphabet computer Δ)
      (PairOutputTransferLabel Γ₁ Δ) (Option (Sum Γ₁ Δ)))
    (state : Option (Sum Γ₁ Δ))
    (contents : ∀ index, List (PairOutputStackAlphabet computer Δ index)) :
    TM2.stepAux (liftPairOutputTransferControlStmt computer stmt)
        (pairReductionOutputTransferState computer state) contents =
      liftPairOutputTransferControlCfg computer
        (TM2.stepAux stmt state contents) := by
  induction stmt generalizing state contents with
  | push index write next ih =>
      simpa only [liftPairOutputTransferControlStmt, TM2.stepAux,
        pairReductionOutputTransferStateValue_transfer] using ih state _
  | peek index read next ih =>
      simpa only [liftPairOutputTransferControlStmt, TM2.stepAux,
        pairReductionOutputTransferStateValue_transfer] using
        ih (read state (contents index).head?) contents
  | pop index read next ih =>
      simpa only [liftPairOutputTransferControlStmt, TM2.stepAux,
        pairReductionOutputTransferStateValue_transfer] using ih _ _
  | load update next ih =>
      simpa only [liftPairOutputTransferControlStmt, TM2.stepAux,
        pairReductionOutputTransferStateValue_transfer] using
        ih (update state) contents
  | branch test yes no ihYes ihNo =>
      by_cases h : test state
      · simpa only [liftPairOutputTransferControlStmt, TM2.stepAux,
          pairReductionOutputTransferStateValue_transfer, h,
          cond_true] using ihYes state contents
      · simpa only [liftPairOutputTransferControlStmt, TM2.stepAux,
          pairReductionOutputTransferStateValue_transfer, h,
          cond_false] using ihNo state contents
  | goto next =>
      rfl
  | halt =>
      rfl

/-- One live output-reassembly step is reproduced by the combined dispatcher.
-/
theorem pairReductionOutputProgram_output_step {Γ₀ Γ₁ Δ : Type}
    (computer : TM2ComputableAux Γ₀ Γ₁)
    (label : PairOutputTransferLabel Γ₁ Δ)
    (state : Option (Sum Γ₁ Δ))
    (contents : ∀ index, List (PairOutputStackAlphabet computer Δ index)) :
    TM2.step (pairReductionOutputProgram computer)
        (liftPairOutputTransferControlCfg computer
          (TM2.Cfg.mk (some label) state contents)) =
      some (liftPairOutputTransferControlCfg computer
        (TM2.stepAux (pairOutputTransferProgram computer label) state
          contents)) := by
  change some (TM2.stepAux
    (liftPairOutputTransferControlStmt computer
      (pairOutputTransferProgram computer label))
    (pairReductionOutputTransferState computer state) contents) = _
  rw [liftPairOutputTransferControl_stepAux]

/-- Any exact finite output-transfer run is reproduced by the combined
dispatcher with the same step count. -/
theorem pairReductionOutputProgram_output_run {Γ₀ Γ₁ Δ : Type}
    (computer : TM2ComputableAux Γ₀ Γ₁) (steps : ℕ)
    (cfg finalCfg : TM2.Cfg (PairOutputStackAlphabet computer Δ)
      (PairOutputTransferLabel Γ₁ Δ) (Option (Sum Γ₁ Δ)))
    (run :
      (flip Option.bind (TM2.step (pairOutputTransferProgram computer)))^[
        steps] (some cfg) = some finalCfg) :
    (flip Option.bind
        (TM2.step (pairReductionOutputProgram computer)))^[steps]
      (some (liftPairOutputTransferControlCfg computer cfg)) =
      some (liftPairOutputTransferControlCfg computer finalCfg) := by
  induction steps generalizing cfg with
  | zero =>
      simp only [Function.iterate_zero_apply, Option.some.injEq] at run ⊢
      subst finalCfg
      rfl
  | succ steps ih =>
      rw [Function.iterate_succ_apply] at run ⊢
      cases cfg with
      | mk label state contents =>
          cases label with
          | none =>
              simp only [flip, Option.bind_some, TM2.step] at run
              rw [pairReductionOutput_iterate_bind_none] at run
              contradiction
          | some label =>
              simp only [flip, Option.bind_some, TM2.step] at run
              change
                (flip Option.bind
                    (TM2.step (pairReductionOutputProgram computer)))^[steps]
                    (TM2.step (pairReductionOutputProgram computer)
                      (liftPairOutputTransferControlCfg computer
                        (TM2.Cfg.mk (some label) state contents))) =
                  some (liftPairOutputTransferControlCfg computer finalCfg)
              rw [pairReductionOutputProgram_output_step]
              exact ih _ run

/-- The total dispatcher reproduces the complete pair-left computation: it
preprocesses an arbitrary tagged source, transfers its left projection into
the reduction machine, executes a supplied exact reduction run, and reassembles
the private reduction output with the preserved right projection. The exact
cost keeps preprocessing, reduction, and output reassembly separate. -/
theorem pairReductionOutputProgram_complete_run {Γ₀ Γ₁ Δ : Type}
    (computer : TM2ComputableAux Γ₀ Γ₁)
    (source : List (Sum Γ₀ Δ))
    (machineContents finalMachineContents :
      ∀ index, List (computer.tm.Γ index))
    (finalState : computer.tm.σ)
    (privateOutput : List (computer.tm.Γ computer.tm.k₁))
    (reductionRun : EvalsTo (TM2.step computer.tm.m)
      (TM2.Cfg.mk (some computer.tm.main) computer.tm.initialState
        (Function.update machineContents computer.tm.k₀
          ((PairEncoding.leftSymbols source).map
              computer.inputAlphabet.symm ++
            machineContents computer.tm.k₀)))
      (some (TM2.Cfg.mk none finalState
        (Function.update finalMachineContents computer.tm.k₁
          privateOutput)))) :
    (flip Option.bind
        (TM2.step (pairReductionOutputProgram computer)))^[
      (4 * privateOutput.length +
          4 * (PairEncoding.rightSymbols source).length + 8) +
        (reductionRun.steps +
          (4 * source.length +
            4 * (PairEncoding.leftSymbols source).length + 13))]
      (some (liftPairReductionThenOutputCfg computer [] []
        (liftPairAdapterThenTransferCfg computer
          (liftPairAdapterCfg computer machineContents
            (pairAdapterCfg (.split .scan) none source [] [] [] []))))) =
      some (liftPairOutputTransferControlCfg computer
        (pairOutputTransferCfg computer .done none [] [] [] [] []
          (Function.update finalMachineContents computer.tm.k₁ []) []
          ((privateOutput.map computer.outputAlphabet).map
              (Sum.inl : Γ₁ → Sum Γ₁ Δ) ++
            (PairEncoding.rightSymbols source).map
              (Sum.inr : Δ → Sum Γ₁ Δ)))) := by
  let adapterContents :
      ∀ index, List (PairAdapterStackAlphabet Γ₀ Δ index) :=
    pairAdapterStacks [] [] [] [] (PairEncoding.rightSymbols source)
  let initialCfg : TM2.Cfg computer.tm.Γ computer.tm.Λ computer.tm.σ :=
    TM2.Cfg.mk (some computer.tm.main) computer.tm.initialState
      (Function.update machineContents computer.tm.k₀
        ((PairEncoding.leftSymbols source).map computer.inputAlphabet.symm ++
          machineContents computer.tm.k₀))
  let finalCfg : TM2.Cfg computer.tm.Γ computer.tm.Λ computer.tm.σ :=
    TM2.Cfg.mk none finalState
      (Function.update finalMachineContents computer.tm.k₁ privateOutput)
  have preprocessRun :=
    pairReductionProgram_preprocess_transfer_whole_list computer source
      machineContents
  have machineRun :
      (flip Option.bind (TM2.step (pairReductionProgram computer)))^[
          reductionRun.steps]
        (some (liftReductionMachineControlCfg computer
          (liftReductionCfg computer adapterContents initialCfg))) =
        some (liftReductionMachineControlCfg computer
          (liftReductionCfg computer adapterContents finalCfg)) :=
    pairReductionProgram_machine_run computer reductionRun.steps initialCfg
      finalCfg adapterContents reductionRun.evals_in_steps
  have reductionPhases :
      (flip Option.bind (TM2.step (pairReductionProgram computer)))^[
          reductionRun.steps +
            (4 * source.length +
              4 * (PairEncoding.leftSymbols source).length + 13)]
        (some (liftPairAdapterThenTransferCfg computer
          (liftPairAdapterCfg computer machineContents
            (pairAdapterCfg (.split .scan) none source [] [] [] [])))) =
        some (liftReductionMachineControlCfg computer
          (liftReductionCfg computer adapterContents finalCfg)) := by
    rw [Function.iterate_add_apply, preprocessRun]
    exact machineRun
  have liftedReductionPhases :=
    pairReductionOutputProgram_reduction_run computer
      (reductionRun.steps +
        (4 * source.length +
          4 * (PairEncoding.leftSymbols source).length + 13))
      (liftPairAdapterThenTransferCfg computer
        (liftPairAdapterCfg computer machineContents
          (pairAdapterCfg (.split .scan) none source [] [] [] [])))
      (liftReductionMachineControlCfg computer
        (liftReductionCfg computer adapterContents finalCfg)) [] []
      reductionPhases
  have outputRun := pairOutputTransfer_whole_list computer [] [] []
    (PairEncoding.rightSymbols source) privateOutput finalMachineContents
  have liftedOutputRun :=
    pairReductionOutputProgram_output_run computer
      (4 * privateOutput.length +
        4 * (PairEncoding.rightSymbols source).length + 8)
      (pairOutputTransferCfg computer .certificateReverseScan none [] [] [] []
        (PairEncoding.rightSymbols source)
        (Function.update finalMachineContents computer.tm.k₁ privateOutput) [] [])
      (pairOutputTransferCfg computer .done none [] [] [] [] []
        (Function.update finalMachineContents computer.tm.k₁ []) []
        ((privateOutput.map computer.outputAlphabet).map
            (Sum.inl : Γ₁ → Sum Γ₁ Δ) ++
          (PairEncoding.rightSymbols source).map
            (Sum.inr : Δ → Sum Γ₁ Δ)))
      outputRun
  rw [Function.iterate_add_apply, liftedReductionPhases]
  simpa [adapterContents, finalCfg, liftReductionCfg,
    liftReductionMachineControlCfg, liftPairOutputTransferControlCfg,
    liftPairReductionThenOutputCfg, pairOutputTransferCfg] using
    liftedOutputRun

/-- Package the complete exact pair-left execution as mathlib's `EvalsTo`
witness without hiding its three-part step count. -/
def pairReductionOutputProgram_complete_evalsTo {Γ₀ Γ₁ Δ : Type}
    (computer : TM2ComputableAux Γ₀ Γ₁)
    (source : List (Sum Γ₀ Δ))
    (machineContents finalMachineContents :
      ∀ index, List (computer.tm.Γ index))
    (finalState : computer.tm.σ)
    (privateOutput : List (computer.tm.Γ computer.tm.k₁))
    (reductionRun : EvalsTo (TM2.step computer.tm.m)
      (TM2.Cfg.mk (some computer.tm.main) computer.tm.initialState
        (Function.update machineContents computer.tm.k₀
          ((PairEncoding.leftSymbols source).map
              computer.inputAlphabet.symm ++
            machineContents computer.tm.k₀)))
      (some (TM2.Cfg.mk none finalState
        (Function.update finalMachineContents computer.tm.k₁
          privateOutput)))) :
    EvalsTo (TM2.step (pairReductionOutputProgram computer))
      (liftPairReductionThenOutputCfg computer [] []
        (liftPairAdapterThenTransferCfg computer
          (liftPairAdapterCfg computer machineContents
            (pairAdapterCfg (.split .scan) none source [] [] [] []))))
      (some (liftPairOutputTransferControlCfg computer
        (pairOutputTransferCfg computer .done none [] [] [] [] []
          (Function.update finalMachineContents computer.tm.k₁ []) []
          ((privateOutput.map computer.outputAlphabet).map
              (Sum.inl : Γ₁ → Sum Γ₁ Δ) ++
            (PairEncoding.rightSymbols source).map
              (Sum.inr : Δ → Sum Γ₁ Δ))))) where
  steps :=
    (4 * privateOutput.length +
        4 * (PairEncoding.rightSymbols source).length + 8) +
      (reductionRun.steps +
        (4 * source.length +
          4 * (PairEncoding.leftSymbols source).length + 13))
  evals_in_steps := pairReductionOutputProgram_complete_run computer source
    machineContents finalMachineContents finalState privateOutput reductionRun

end LeanNPHardness.MachineAdapters
