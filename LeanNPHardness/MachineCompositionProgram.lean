import LeanNPHardness.MachineControlSimulation
import LeanNPHardness.MachineTransfer

namespace LeanNPHardness.MachineComposition

open Turing

/-- The total program for sequential machine composition on the final
scratch-extended stack layout. First-machine labels run with reached halts
redirected to transfer, transfer actions run the order-preserving copy loop,
and second-machine labels run with ordinary halting behavior. -/
def compositionProgram {Γ₀ Γ₁ Γ₂ : Type}
    (first : TM2ComputableAux Γ₀ Γ₁)
    (second : TM2ComputableAux Γ₁ Γ₂) :
    ControlLabel first second →
      TM2.Stmt (TransferStackAlphabet first second)
        (ControlLabel first second) (ControlState first second)
  | Sum.inl label =>
      liftScratchStmt first second
        (liftLeftThenTransferStmt first second (first.tm.m label))
  | Sum.inr (Sum.inl action) =>
      transferProgram first second
        (transferActionLabel first second action)
  | Sum.inr (Sum.inr label) =>
      liftScratchStmt first second
        (liftRightControlStmt first second (second.tm.m label))

/-- The finite two-stack-style machine carrying out the sequential program.
Its external input stack is the first machine's input stack, and its external
output stack is the second machine's output stack. No computation or runtime
claim is bundled into this structural construction. -/
def compositionMachine {Γ₀ Γ₁ Γ₂ : Type} [Fintype Γ₁]
    (first : TM2ComputableAux Γ₀ Γ₁)
    (second : TM2ComputableAux Γ₁ Γ₂) : FinTM2 where
  K := TransferStackIndex first second
  k₀ := transferLeftIndex first second first.tm.k₀
  k₁ := transferRightIndex first second second.tm.k₁
  Γ := TransferStackAlphabet first second
  Λ := ControlLabel first second
  main := leftLabel first second first.tm.main
  σ := ControlState first second
  initialState := leftState first second first.tm.initialState
  Γk₀Fin := by
    change Fintype (first.tm.Γ first.tm.k₀)
    exact first.tm.Γk₀Fin
  m := compositionProgram first second

/-- The structural composition machine together with its external alphabet
equivalences. Proving that it computes function composition in polynomial time
is a separate result. -/
def compositionAux {Γ₀ Γ₁ Γ₂ : Type} [Fintype Γ₁]
    (first : TM2ComputableAux Γ₀ Γ₁)
    (second : TM2ComputableAux Γ₁ Γ₂) : TM2ComputableAux Γ₀ Γ₂ where
  tm := compositionMachine first second
  inputAlphabet := first.inputAlphabet
  outputAlphabet := second.outputAlphabet

@[simp]
theorem compositionProgram_left {Γ₀ Γ₁ Γ₂ : Type}
    (first : TM2ComputableAux Γ₀ Γ₁)
    (second : TM2ComputableAux Γ₁ Γ₂) (label : first.tm.Λ) :
    compositionProgram first second (leftLabel first second label) =
      liftScratchStmt first second
        (liftLeftThenTransferStmt first second (first.tm.m label)) :=
  rfl

@[simp]
theorem compositionProgram_transfer {Γ₀ Γ₁ Γ₂ : Type}
    (first : TM2ComputableAux Γ₀ Γ₁)
    (second : TM2ComputableAux Γ₁ Γ₂) (action : TransferAction Γ₁) :
    compositionProgram first second
        (transferActionLabel first second action) =
      transferProgram first second
        (transferActionLabel first second action) :=
  rfl

@[simp]
theorem compositionProgram_right {Γ₀ Γ₁ Γ₂ : Type}
    (first : TM2ComputableAux Γ₀ Γ₁)
    (second : TM2ComputableAux Γ₁ Γ₂) (label : second.tm.Λ) :
    compositionProgram first second (rightLabel first second label) =
      liftScratchStmt first second
        (liftRightControlStmt first second (second.tm.m label)) :=
  rfl

/-- One first-machine step is simulated exactly by the total composition
program after adding scratch storage. A reached halt is redirected to transfer,
and the scratch contents are preserved by the component step. -/
theorem compositionProgram_left_step {Γ₀ Γ₁ Γ₂ : Type}
    (first : TM2ComputableAux Γ₀ Γ₁)
    (second : TM2ComputableAux Γ₁ Γ₂)
    (cfg : TM2.Cfg first.tm.Γ first.tm.Λ first.tm.σ)
    (scratch : List Γ₁) :
    TM2.step (compositionProgram first second)
        (liftScratchCfg first second scratch
          (liftLeftControlCfg first second cfg)) =
      Option.map (liftScratchCfg first second scratch)
        (Option.map (liftLeftThenTransferCfg first second)
          (TM2.step first.tm.m cfg)) := by
  cases cfg with
  | mk label state contents =>
      cases label with
      | none =>
          rfl
      | some label =>
          simp only [liftScratchCfg, liftLeftControlCfg, TM2.step,
            Option.map_some, compositionProgram, leftLabel]
          rw [liftScratch_stepAux, liftLeftThenTransfer_stepAux]
          rfl

/-- One second-machine step is simulated exactly by the total composition
program after adding scratch storage. Ordinary second-machine halting behavior
is preserved, and the scratch contents are unchanged. -/
theorem compositionProgram_right_step {Γ₀ Γ₁ Γ₂ : Type}
    (first : TM2ComputableAux Γ₀ Γ₁)
    (second : TM2ComputableAux Γ₁ Γ₂)
    (cfg : TM2.Cfg second.tm.Γ second.tm.Λ second.tm.σ)
    (scratch : List Γ₁) :
    TM2.step (compositionProgram first second)
        (liftScratchCfg first second scratch
          (liftRightControlCfg first second cfg)) =
      Option.map (liftScratchCfg first second scratch)
        (Option.map (liftRightControlCfg first second)
          (TM2.step second.tm.m cfg)) := by
  cases cfg with
  | mk label state contents =>
      cases label with
      | none =>
          rfl
      | some label =>
          simp only [liftScratchCfg, liftRightControlCfg, TM2.step,
            Option.map_some, compositionProgram, rightLabel]
          rw [liftScratch_stepAux, liftRightControl_stepAux]
          rfl

end LeanNPHardness.MachineComposition
