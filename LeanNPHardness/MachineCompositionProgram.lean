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

/-- On a transfer-action configuration, one step of the total composition
program is exactly one step of the isolated transfer program. -/
theorem compositionProgram_transfer_step {Γ₀ Γ₁ Γ₂ : Type}
    (first : TM2ComputableAux Γ₀ Γ₁)
    (second : TM2ComputableAux Γ₁ Γ₂) (action : TransferAction Γ₁)
    (state : ControlState first second)
    (contents : ∀ k, List (StackAlphabet first.tm second.tm k))
    (scratch : List Γ₁) :
    TM2.step (compositionProgram first second)
        (transferActionCfg first second action state contents scratch) =
      TM2.step (transferProgram first second)
        (transferActionCfg first second action state contents scratch) := by
  rfl

/-- Two total-program steps implement one nonempty reverse-output iteration. -/
theorem compositionProgram_reverseOutput_iteration_nonempty
    {Γ₀ Γ₁ Γ₂ : Type}
    (first : TM2ComputableAux Γ₀ Γ₁)
    (second : TM2ComputableAux Γ₁ Γ₂)
    (state : ControlState first second)
    (contents : ∀ k, List (StackAlphabet first.tm second.tm k))
    (scratch : List Γ₁) (head : first.tm.Γ first.tm.k₁)
    (tail : List (first.tm.Γ first.tm.k₁)) :
    (TM2.step (compositionProgram first second)
        (transferActionCfg first second (.phase .reverseOutput) state
          (Function.update contents (Sum.inl first.tm.k₁) (head :: tail))
          scratch)).bind (TM2.step (compositionProgram first second)) =
      some (transferActionCfg first second (.phase .reverseOutput)
        (transferState first second (some (first.outputAlphabet head)))
        (Function.update contents (Sum.inl first.tm.k₁) tail)
        (first.outputAlphabet head :: scratch)) := by
  rw [compositionProgram_transfer_step, reverseOutput_step_nonempty,
    Option.bind_some, compositionProgram_transfer_step, reversePush_step_some]

/-- Two total-program steps detect an empty first output stack and enter the
fill-input phase. -/
theorem compositionProgram_reverseOutput_iteration_empty
    {Γ₀ Γ₁ Γ₂ : Type}
    (first : TM2ComputableAux Γ₀ Γ₁)
    (second : TM2ComputableAux Γ₁ Γ₂)
    (state : ControlState first second)
    (contents : ∀ k, List (StackAlphabet first.tm second.tm k))
    (scratch : List Γ₁) :
    (TM2.step (compositionProgram first second)
        (transferActionCfg first second (.phase .reverseOutput) state
          (Function.update contents (Sum.inl first.tm.k₁) []) scratch)).bind
        (TM2.step (compositionProgram first second)) =
      some (transferActionCfg first second (.phase .fillInput)
        (transferState first second none)
        (Function.update contents (Sum.inl first.tm.k₁) []) scratch) := by
  rw [compositionProgram_transfer_step, reverseOutput_step_empty,
    Option.bind_some, compositionProgram_transfer_step, reversePush_step_none]

/-- Under the total composition program, repeated reverse-output iterations
consume the whole first output stack in exactly two steps per symbol plus two
exhaustion steps. -/
theorem compositionProgram_reverseOutput_whole_list {Γ₀ Γ₁ Γ₂ : Type}
    (first : TM2ComputableAux Γ₀ Γ₁)
    (second : TM2ComputableAux Γ₁ Γ₂)
    (state : ControlState first second)
    (contents : ∀ k, List (StackAlphabet first.tm second.tm k))
    (output : List (first.tm.Γ first.tm.k₁)) (scratch : List Γ₁) :
    (flip Option.bind (TM2.step (compositionProgram first second)))^[
        2 * output.length + 2]
      (some (transferActionCfg first second (.phase .reverseOutput) state
        (Function.update contents (Sum.inl first.tm.k₁) output) scratch)) =
      some (transferActionCfg first second (.phase .fillInput)
        (transferState first second none)
        (Function.update contents (Sum.inl first.tm.k₁) [])
        ((output.map first.outputAlphabet).reverse ++ scratch)) := by
  induction output generalizing state scratch with
  | nil =>
      simpa [Function.iterate_succ_apply'] using
        compositionProgram_reverseOutput_iteration_empty first second state
          contents scratch
  | cons head tail ih =>
      have firstIteration :=
        compositionProgram_reverseOutput_iteration_nonempty first second state
          contents scratch head tail
      rw [List.length_cons]
      have stepCount : 2 * (tail.length + 1) + 2 =
          (2 * tail.length + 2) + 2 := by omega
      rw [stepCount, Function.iterate_add_apply]
      rw [show
        (flip Option.bind (TM2.step (compositionProgram first second)))^[2]
          (some (transferActionCfg first second (.phase .reverseOutput) state
            (Function.update contents (Sum.inl first.tm.k₁) (head :: tail))
            scratch)) =
          some (transferActionCfg first second (.phase .reverseOutput)
            (transferState first second (some (first.outputAlphabet head)))
            (Function.update contents (Sum.inl first.tm.k₁) tail)
            (first.outputAlphabet head :: scratch)) by
        simpa [Function.iterate_succ_apply'] using firstIteration]
      simpa [List.map, List.reverse_cons, List.append_assoc] using
        ih (transferState first second (some (first.outputAlphabet head)))
          (first.outputAlphabet head :: scratch)

/-- Two total-program steps implement one nonempty fill-input iteration. -/
theorem compositionProgram_fillInput_iteration_nonempty
    {Γ₀ Γ₁ Γ₂ : Type}
    (first : TM2ComputableAux Γ₀ Γ₁)
    (second : TM2ComputableAux Γ₁ Γ₂)
    (state : ControlState first second)
    (contents : ∀ k, List (StackAlphabet first.tm second.tm k))
    (input : List (second.tm.Γ second.tm.k₀))
    (head : Γ₁) (tail : List Γ₁) :
    (TM2.step (compositionProgram first second)
        (transferActionCfg first second (.phase .fillInput) state
          (Function.update contents (Sum.inr second.tm.k₀) input)
          (head :: tail))).bind (TM2.step (compositionProgram first second)) =
      some (transferActionCfg first second (.phase .fillInput)
        (transferState first second (some head))
        (Function.update contents (Sum.inr second.tm.k₀)
          (second.inputAlphabet.symm head :: input)) tail) := by
  rw [compositionProgram_transfer_step, fillInput_step_nonempty,
    Option.bind_some, compositionProgram_transfer_step, fillPush_step_some]

/-- Two total-program steps detect empty scratch storage and enter the second
machine's main label. -/
theorem compositionProgram_fillInput_iteration_empty {Γ₀ Γ₁ Γ₂ : Type}
    (first : TM2ComputableAux Γ₀ Γ₁)
    (second : TM2ComputableAux Γ₁ Γ₂)
    (state : ControlState first second)
    (contents : ∀ k, List (StackAlphabet first.tm second.tm k)) :
    Option.bind
        (TM2.step (compositionProgram first second)
          (transferActionCfg first second (.phase .fillInput) state contents []))
        (TM2.step (compositionProgram first second)) =
      some (rightEntryCfg first second contents []) := by
  rw [compositionProgram_transfer_step, fillInput_step_empty,
    Option.bind_some, compositionProgram_transfer_step, fillPush_step_none]

/-- Under the total composition program, repeated fill-input iterations
consume the whole scratch stack in exactly two steps per symbol plus two
exhaustion steps. -/
theorem compositionProgram_fillInput_whole_list {Γ₀ Γ₁ Γ₂ : Type}
    (first : TM2ComputableAux Γ₀ Γ₁)
    (second : TM2ComputableAux Γ₁ Γ₂)
    (state : ControlState first second)
    (contents : ∀ k, List (StackAlphabet first.tm second.tm k))
    (input : List (second.tm.Γ second.tm.k₀)) (scratch : List Γ₁) :
    (flip Option.bind (TM2.step (compositionProgram first second)))^[
        2 * scratch.length + 2]
      (some (transferActionCfg first second (.phase .fillInput) state
        (Function.update contents (Sum.inr second.tm.k₀) input) scratch)) =
      some (rightEntryCfg first second
        (Function.update contents (Sum.inr second.tm.k₀)
          ((scratch.map second.inputAlphabet.symm).reverse ++ input)) []) := by
  induction scratch generalizing state input with
  | nil =>
      simpa [Function.iterate_succ_apply'] using
        compositionProgram_fillInput_iteration_empty first second state
          (Function.update contents (Sum.inr second.tm.k₀) input)
  | cons head tail ih =>
      have firstIteration :=
        compositionProgram_fillInput_iteration_nonempty first second state
          contents input head tail
      rw [List.length_cons]
      have stepCount : 2 * (tail.length + 1) + 2 =
          (2 * tail.length + 2) + 2 := by omega
      rw [stepCount, Function.iterate_add_apply]
      rw [show
        (flip Option.bind (TM2.step (compositionProgram first second)))^[2]
          (some (transferActionCfg first second (.phase .fillInput) state
            (Function.update contents (Sum.inr second.tm.k₀) input)
            (head :: tail))) =
          some (transferActionCfg first second (.phase .fillInput)
            (transferState first second (some head))
            (Function.update contents (Sum.inr second.tm.k₀)
              (second.inputAlphabet.symm head :: input)) tail) by
        simpa [Function.iterate_succ_apply'] using firstIteration]
      simpa [List.map, List.reverse_cons, List.append_assoc] using
        ih (transferState first second (some head))
          (second.inputAlphabet.symm head :: input)

/-- The total composition program executes the complete order-preserving
transfer in exactly four steps per first-output symbol plus four exhaustion
steps, then enters the second machine's initial control configuration. -/
theorem compositionProgram_transfer_whole_list {Γ₀ Γ₁ Γ₂ : Type}
    (first : TM2ComputableAux Γ₀ Γ₁)
    (second : TM2ComputableAux Γ₁ Γ₂)
    (state : ControlState first second)
    (contents : ∀ k, List (StackAlphabet first.tm second.tm k))
    (output : List (first.tm.Γ first.tm.k₁))
    (input : List (second.tm.Γ second.tm.k₀)) :
    (flip Option.bind (TM2.step (compositionProgram first second)))^[
        4 * output.length + 4]
      (some (transferActionCfg first second (.phase .reverseOutput) state
        (Function.update
          (Function.update contents (Sum.inr second.tm.k₀) input)
          (Sum.inl first.tm.k₁) output) [])) =
      some (rightEntryCfg first second
        (Function.update
          (Function.update contents (Sum.inl first.tm.k₁) [])
          (Sum.inr second.tm.k₀)
          (output.map (middleAlphabetEquiv first second) ++ input)) []) := by
  have reverseRun :
      (flip Option.bind (TM2.step (compositionProgram first second)))^[
          2 * output.length + 2]
        (some (transferActionCfg first second (.phase .reverseOutput) state
          (Function.update
            (Function.update contents (Sum.inr second.tm.k₀) input)
            (Sum.inl first.tm.k₁) output) [])) =
        some (transferActionCfg first second (.phase .fillInput)
          (transferState first second none)
          (Function.update
            (Function.update contents (Sum.inr second.tm.k₀) input)
            (Sum.inl first.tm.k₁) [])
          (output.map first.outputAlphabet).reverse) := by
    simpa using
      compositionProgram_reverseOutput_whole_list first second state
        (Function.update contents (Sum.inr second.tm.k₀) input) output []
  have updatesCommute :
      Function.update
          (Function.update contents (Sum.inr second.tm.k₀) input)
          (Sum.inl first.tm.k₁) [] =
        Function.update
          (Function.update contents (Sum.inl first.tm.k₁) [])
          (Sum.inr second.tm.k₀) input := by
    exact Function.update_comm
      (a := (Sum.inr second.tm.k₀ : StackIndex first.tm second.tm))
      (b := Sum.inl first.tm.k₁) (by simp) input [] contents
  have fillRun :=
    compositionProgram_fillInput_whole_list first second
      (transferState first second none)
      (Function.update contents (Sum.inl first.tm.k₁) []) input
      ((output.map first.outputAlphabet).reverse)
  have stepCount :
      4 * output.length + 4 =
        (2 * (output.map first.outputAlphabet).reverse.length + 2) +
          (2 * output.length + 2) := by
    simp
    omega
  rw [stepCount, Function.iterate_add_apply, reverseRun, updatesCommute, fillRun]
  simp [List.map_reverse, List.map_map, Function.comp_def,
    middleAlphabetEquiv]

end LeanNPHardness.MachineComposition
