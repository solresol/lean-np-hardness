import LeanNPHardness.MachineControl

namespace LeanNPHardness.MachineComposition

open Turing

/-- Extend the two component stack families with one scratch stack. The
scratch stack uses the shared middle encoding alphabet. -/
def TransferStackIndex {Γ₀ Γ₁ Γ₂ : Type}
    (first : TM2ComputableAux Γ₀ Γ₁)
    (second : TM2ComputableAux Γ₁ Γ₂) :=
  StackIndex first.tm second.tm ⊕ Unit

instance {Γ₀ Γ₁ Γ₂ : Type}
    (first : TM2ComputableAux Γ₀ Γ₁)
    (second : TM2ComputableAux Γ₁ Γ₂) :
    DecidableEq (TransferStackIndex first second) :=
  inferInstanceAs
    (DecidableEq (StackIndex first.tm second.tm ⊕ Unit))

instance {Γ₀ Γ₁ Γ₂ : Type}
    (first : TM2ComputableAux Γ₀ Γ₁)
    (second : TM2ComputableAux Γ₁ Γ₂) :
    Fintype (TransferStackIndex first second) :=
  inferInstanceAs (Fintype (StackIndex first.tm second.tm ⊕ Unit))

/-- Alphabet family for the component stacks plus canonical middle-alphabet
scratch storage. -/
def TransferStackAlphabet {Γ₀ Γ₁ Γ₂ : Type}
    (first : TM2ComputableAux Γ₀ Γ₁)
    (second : TM2ComputableAux Γ₁ Γ₂) :
    TransferStackIndex first second → Type
  | Sum.inl index => StackAlphabet first.tm second.tm index
  | Sum.inr _ => Γ₁

/-- The first machine's stack index in the scratch-extended layout. -/
def transferLeftIndex {Γ₀ Γ₁ Γ₂ : Type}
    (first : TM2ComputableAux Γ₀ Γ₁)
    (second : TM2ComputableAux Γ₁ Γ₂) (index : first.tm.K) :
    TransferStackIndex first second :=
  Sum.inl (Sum.inl index)

/-- The second machine's stack index in the scratch-extended layout. -/
def transferRightIndex {Γ₀ Γ₁ Γ₂ : Type}
    (first : TM2ComputableAux Γ₀ Γ₁)
    (second : TM2ComputableAux Γ₁ Γ₂) (index : second.tm.K) :
    TransferStackIndex first second :=
  Sum.inl (Sum.inr index)

/-- The canonical middle-alphabet scratch stack. -/
def scratchIndex {Γ₀ Γ₁ Γ₂ : Type}
    (first : TM2ComputableAux Γ₀ Γ₁)
    (second : TM2ComputableAux Γ₁ Γ₂) :
    TransferStackIndex first second :=
  Sum.inr ()

/-- Embed a combined stack family into the scratch-extended family. -/
def extendStacks {Γ₀ Γ₁ Γ₂ : Type}
    (first : TM2ComputableAux Γ₀ Γ₁)
    (second : TM2ComputableAux Γ₁ Γ₂)
    (contents : ∀ k, List (StackAlphabet first.tm second.tm k))
    (scratch : List Γ₁) :
    ∀ k, List (TransferStackAlphabet first second k)
  | Sum.inl index => contents index
  | Sum.inr _ => scratch

/-- Embed the first machine's stacks into the scratch-extended layout. All
second-machine stacks and scratch storage start empty. -/
def transferLeftStacks {Γ₀ Γ₁ Γ₂ : Type}
    (first : TM2ComputableAux Γ₀ Γ₁)
    (second : TM2ComputableAux Γ₁ Γ₂)
    (contents : ∀ k, List (first.tm.Γ k)) :
    ∀ k, List (TransferStackAlphabet first second k) :=
  extendStacks first second (leftStacks first.tm second.tm contents) []

/-- Embed the second machine's stacks into the scratch-extended layout. All
first-machine stacks and scratch storage start empty. -/
def transferRightStacks {Γ₀ Γ₁ Γ₂ : Type}
    (first : TM2ComputableAux Γ₀ Γ₁)
    (second : TM2ComputableAux Γ₁ Γ₂)
    (contents : ∀ k, List (second.tm.Γ k)) :
    ∀ k, List (TransferStackAlphabet first second k) :=
  extendStacks first second (rightStacks first.tm second.tm contents) []

@[simp]
theorem transferLeftStacks_left {Γ₀ Γ₁ Γ₂ : Type}
    (first : TM2ComputableAux Γ₀ Γ₁)
    (second : TM2ComputableAux Γ₁ Γ₂)
    (contents : ∀ k, List (first.tm.Γ k)) (index : first.tm.K) :
    transferLeftStacks first second contents
        (transferLeftIndex first second index) = contents index :=
  rfl

@[simp]
theorem transferLeftStacks_right {Γ₀ Γ₁ Γ₂ : Type}
    (first : TM2ComputableAux Γ₀ Γ₁)
    (second : TM2ComputableAux Γ₁ Γ₂)
    (contents : ∀ k, List (first.tm.Γ k)) (index : second.tm.K) :
    transferLeftStacks first second contents
        (transferRightIndex first second index) = [] :=
  rfl

@[simp]
theorem transferLeftStacks_scratch {Γ₀ Γ₁ Γ₂ : Type}
    (first : TM2ComputableAux Γ₀ Γ₁)
    (second : TM2ComputableAux Γ₁ Γ₂)
    (contents : ∀ k, List (first.tm.Γ k)) :
    transferLeftStacks first second contents (scratchIndex first second) = [] :=
  rfl

@[simp]
theorem transferRightStacks_left {Γ₀ Γ₁ Γ₂ : Type}
    (first : TM2ComputableAux Γ₀ Γ₁)
    (second : TM2ComputableAux Γ₁ Γ₂)
    (contents : ∀ k, List (second.tm.Γ k)) (index : first.tm.K) :
    transferRightStacks first second contents
        (transferLeftIndex first second index) = [] :=
  rfl

@[simp]
theorem transferRightStacks_right {Γ₀ Γ₁ Γ₂ : Type}
    (first : TM2ComputableAux Γ₀ Γ₁)
    (second : TM2ComputableAux Γ₁ Γ₂)
    (contents : ∀ k, List (second.tm.Γ k)) (index : second.tm.K) :
    transferRightStacks first second contents
        (transferRightIndex first second index) = contents index :=
  rfl

@[simp]
theorem transferRightStacks_scratch {Γ₀ Γ₁ Γ₂ : Type}
    (first : TM2ComputableAux Γ₀ Γ₁)
    (second : TM2ComputableAux Γ₁ Γ₂)
    (contents : ∀ k, List (second.tm.Γ k)) :
    transferRightStacks first second contents (scratchIndex first second) = [] :=
  rfl

@[simp]
theorem extendStacks_scratch {Γ₀ Γ₁ Γ₂ : Type}
    (first : TM2ComputableAux Γ₀ Γ₁)
    (second : TM2ComputableAux Γ₁ Γ₂)
    (contents : ∀ k, List (StackAlphabet first.tm second.tm k))
    (scratch : List Γ₁) :
    (extendStacks first second contents scratch) (scratchIndex first second) =
      scratch :=
  rfl

/-- Updating a component stack commutes with extending the combined stack
family by scratch storage. -/
theorem extendStacks_update {Γ₀ Γ₁ Γ₂ : Type}
    (first : TM2ComputableAux Γ₀ Γ₁)
    (second : TM2ComputableAux Γ₁ Γ₂)
    (contents : ∀ k, List (StackAlphabet first.tm second.tm k))
    (scratch : List Γ₁) (index : StackIndex first.tm second.tm)
    (value : List (StackAlphabet first.tm second.tm index)) :
    extendStacks first second (Function.update contents index value) scratch =
      Function.update (extendStacks first second contents scratch)
        (Sum.inl index) value := by
  funext extendedIndex
  cases extendedIndex with
  | inl combinedIndex =>
      by_cases h : combinedIndex = index
      · subst combinedIndex
        simp [extendStacks]
      · have hsum :
            (Sum.inl combinedIndex : TransferStackIndex first second) ≠
              Sum.inl index := by
          intro equality
          exact h (Sum.inl.inj equality)
        simp [extendStacks, h, hsum]
  | inr scratchIndex =>
      simp [extendStacks]

/-- Updating a first-machine stack commutes with embedding it into the
scratch-extended layout. -/
theorem transferLeftStacks_update {Γ₀ Γ₁ Γ₂ : Type}
    (first : TM2ComputableAux Γ₀ Γ₁)
    (second : TM2ComputableAux Γ₁ Γ₂)
    (contents : ∀ k, List (first.tm.Γ k)) (index : first.tm.K)
    (value : List (first.tm.Γ index)) :
    transferLeftStacks first second (Function.update contents index value) =
      Function.update (transferLeftStacks first second contents)
        (transferLeftIndex first second index) value := by
  rw [transferLeftStacks, transferLeftStacks, leftStacks_update]
  rw [extendStacks_update]
  rfl

/-- Updating a second-machine stack commutes with embedding it into the
scratch-extended layout. -/
theorem transferRightStacks_update {Γ₀ Γ₁ Γ₂ : Type}
    (first : TM2ComputableAux Γ₀ Γ₁)
    (second : TM2ComputableAux Γ₁ Γ₂)
    (contents : ∀ k, List (second.tm.Γ k)) (index : second.tm.K)
    (value : List (second.tm.Γ index)) :
    transferRightStacks first second (Function.update contents index value) =
      Function.update (transferRightStacks first second contents)
        (transferRightIndex first second index) value := by
  rw [transferRightStacks, transferRightStacks, rightStacks_update]
  rw [extendStacks_update]
  rfl

/-- Replacing the scratch stack commutes with the explicit scratch extension. -/
theorem extendStacks_scratch_update {Γ₀ Γ₁ Γ₂ : Type}
    (first : TM2ComputableAux Γ₀ Γ₁)
    (second : TM2ComputableAux Γ₁ Γ₂)
    (contents : ∀ k, List (StackAlphabet first.tm second.tm k))
    (scratch value : List Γ₁) :
    Function.update (extendStacks first second contents scratch)
        (scratchIndex first second) value =
      extendStacks first second contents value := by
  funext index
  cases index with
  | inl combinedIndex =>
      simp [extendStacks, scratchIndex]
  | inr unitIndex =>
      cases unitIndex
      simp [extendStacks, scratchIndex]

/-- A transfer-action configuration with explicit component-stack and scratch
contents. -/
def transferActionCfg {Γ₀ Γ₁ Γ₂ : Type}
    (first : TM2ComputableAux Γ₀ Γ₁)
    (second : TM2ComputableAux Γ₁ Γ₂) (action : TransferAction Γ₁)
    (state : ControlState first second)
    (contents : ∀ k, List (StackAlphabet first.tm second.tm k))
    (scratch : List Γ₁) :
    TM2.Cfg (TransferStackAlphabet first second)
      (ControlLabel first second) (ControlState first second) where
  l := some (transferActionLabel first second action)
  var := state
  stk := extendStacks first second contents scratch

/-- Pop one symbol from the first machine's output stack, translate it to the
canonical middle alphabet, and select the corresponding scratch-push action.
An empty output stack selects the `none` action. -/
def reverseOutputStmt {Γ₀ Γ₁ Γ₂ : Type}
    (first : TM2ComputableAux Γ₀ Γ₁)
    (second : TM2ComputableAux Γ₁ Γ₂) :
    TM2.Stmt (TransferStackAlphabet first second)
      (ControlLabel first second) (ControlState first second) :=
  .pop (transferLeftIndex first second first.tm.k₁)
    (fun _ symbol =>
      transferState first second (symbol.map first.outputAlphabet))
    (.goto (fun state =>
      reversePushLabel first second (transferStateValue first second state)))

/-- Complete a reverse-output iteration after its pop. A present canonical
symbol is pushed to scratch and control returns to `reverseOutput`; absence
advances to the `fillInput` phase. -/
def reversePushStmt {Γ₀ Γ₁ Γ₂ : Type}
    (first : TM2ComputableAux Γ₀ Γ₁)
    (second : TM2ComputableAux Γ₁ Γ₂) (symbol : Option Γ₁) :
    TM2.Stmt (TransferStackAlphabet first second)
      (ControlLabel first second) (ControlState first second) :=
  match symbol with
  | none => .goto (fun _ => fillInputLabel first second)
  | some symbol =>
      .push (scratchIndex first second) (fun _ => symbol)
        (.goto (fun _ => transferLabel first second))

/-- The executable reverse-output fragment of the eventual composed program.
Component labels and the not-yet-implemented fill-input phase halt. -/
def reverseOutputProgram {Γ₀ Γ₁ Γ₂ : Type}
    (first : TM2ComputableAux Γ₀ Γ₁)
    (second : TM2ComputableAux Γ₁ Γ₂) :
    ControlLabel first second →
      TM2.Stmt (TransferStackAlphabet first second)
        (ControlLabel first second) (ControlState first second)
  | Sum.inr (Sum.inl (.phase .reverseOutput)) =>
      reverseOutputStmt first second
  | Sum.inr (Sum.inl (.reversePush symbol)) =>
      reversePushStmt first second symbol
  | _ => .halt

/-- A reverse-output pop on a nonempty source records the translated head
symbol and removes it from the first output stack. -/
theorem reverseOutput_step_nonempty {Γ₀ Γ₁ Γ₂ : Type}
    (first : TM2ComputableAux Γ₀ Γ₁)
    (second : TM2ComputableAux Γ₁ Γ₂)
    (state : ControlState first second)
    (contents : ∀ k, List (StackAlphabet first.tm second.tm k))
    (scratch : List Γ₁) (head : first.tm.Γ first.tm.k₁)
    (tail : List (first.tm.Γ first.tm.k₁)) :
    TM2.step (reverseOutputProgram first second)
        (transferActionCfg first second (.phase .reverseOutput) state
          (Function.update contents (Sum.inl first.tm.k₁) (head :: tail))
          scratch) =
      some (transferActionCfg first second
        (.reversePush (some (first.outputAlphabet head)))
        (transferState first second (some (first.outputAlphabet head)))
        (Function.update contents (Sum.inl first.tm.k₁) tail) scratch) := by
  simp only [TM2.step, reverseOutputProgram, reverseOutputStmt, TM2.stepAux,
    transferActionCfg, transferActionLabel, reversePushLabel,
    transferStateValue_transferState]
  rw [extendStacks_update, extendStacks_update]
  simp [transferLeftIndex]

/-- A reverse-output pop on an empty source records absence and leaves all
stacks unchanged. -/
theorem reverseOutput_step_empty {Γ₀ Γ₁ Γ₂ : Type}
    (first : TM2ComputableAux Γ₀ Γ₁)
    (second : TM2ComputableAux Γ₁ Γ₂)
    (state : ControlState first second)
    (contents : ∀ k, List (StackAlphabet first.tm second.tm k))
    (scratch : List Γ₁) :
    TM2.step (reverseOutputProgram first second)
        (transferActionCfg first second (.phase .reverseOutput) state
          (Function.update contents (Sum.inl first.tm.k₁) []) scratch) =
      some (transferActionCfg first second (.reversePush none)
        (transferState first second none)
        (Function.update contents (Sum.inl first.tm.k₁) []) scratch) := by
  simp only [TM2.step, reverseOutputProgram, reverseOutputStmt, TM2.stepAux,
    transferActionCfg, transferActionLabel, reversePushLabel,
    transferStateValue_transferState]
  rw [extendStacks_update]
  simp [transferLeftIndex]

/-- The symbol-carrying action pushes its canonical symbol onto scratch and
returns to the reverse-output stage. -/
theorem reversePush_step_some {Γ₀ Γ₁ Γ₂ : Type}
    (first : TM2ComputableAux Γ₀ Γ₁)
    (second : TM2ComputableAux Γ₁ Γ₂) (symbol : Γ₁)
    (state : ControlState first second)
    (contents : ∀ k, List (StackAlphabet first.tm second.tm k))
    (scratch : List Γ₁) :
    TM2.step (reverseOutputProgram first second)
        (transferActionCfg first second (.reversePush (some symbol)) state
          contents scratch) =
      some (transferActionCfg first second (.phase .reverseOutput) state
        contents (symbol :: scratch)) := by
  simp only [TM2.step, reverseOutputProgram, reversePushStmt, TM2.stepAux,
    transferActionCfg, transferActionLabel, transferLabel,
    transferPhaseLabel]
  simp only [extendStacks_scratch]
  rw [extendStacks_scratch_update]

/-- The empty-source action advances to the fill-input phase without changing
state or stacks. -/
theorem reversePush_step_none {Γ₀ Γ₁ Γ₂ : Type}
    (first : TM2ComputableAux Γ₀ Γ₁)
    (second : TM2ComputableAux Γ₁ Γ₂)
    (state : ControlState first second)
    (contents : ∀ k, List (StackAlphabet first.tm second.tm k))
    (scratch : List Γ₁) :
    TM2.step (reverseOutputProgram first second)
        (transferActionCfg first second (.reversePush none) state
          contents scratch) =
      some (transferActionCfg first second (.phase .fillInput) state
        contents scratch) := by
  rfl

/-- Two program steps implement one nonempty reverse-output iteration: the
source head is removed, translated, and pushed onto scratch. -/
theorem reverseOutput_iteration_nonempty {Γ₀ Γ₁ Γ₂ : Type}
    (first : TM2ComputableAux Γ₀ Γ₁)
    (second : TM2ComputableAux Γ₁ Γ₂)
    (state : ControlState first second)
    (contents : ∀ k, List (StackAlphabet first.tm second.tm k))
    (scratch : List Γ₁) (head : first.tm.Γ first.tm.k₁)
    (tail : List (first.tm.Γ first.tm.k₁)) :
    (TM2.step (reverseOutputProgram first second)
        (transferActionCfg first second (.phase .reverseOutput) state
          (Function.update contents (Sum.inl first.tm.k₁) (head :: tail))
          scratch)).bind (TM2.step (reverseOutputProgram first second)) =
      some (transferActionCfg first second (.phase .reverseOutput)
        (transferState first second (some (first.outputAlphabet head)))
        (Function.update contents (Sum.inl first.tm.k₁) tail)
        (first.outputAlphabet head :: scratch)) := by
  rw [reverseOutput_step_nonempty, Option.bind_some, reversePush_step_some]

/-- Two program steps detect an empty first output stack and enter the
fill-input phase without changing scratch storage. -/
theorem reverseOutput_iteration_empty {Γ₀ Γ₁ Γ₂ : Type}
    (first : TM2ComputableAux Γ₀ Γ₁)
    (second : TM2ComputableAux Γ₁ Γ₂)
    (state : ControlState first second)
    (contents : ∀ k, List (StackAlphabet first.tm second.tm k))
    (scratch : List Γ₁) :
    (TM2.step (reverseOutputProgram first second)
        (transferActionCfg first second (.phase .reverseOutput) state
          (Function.update contents (Sum.inl first.tm.k₁) []) scratch)).bind
        (TM2.step (reverseOutputProgram first second)) =
      some (transferActionCfg first second (.phase .fillInput)
        (transferState first second none)
        (Function.update contents (Sum.inl first.tm.k₁) []) scratch) := by
  rw [reverseOutput_step_empty, Option.bind_some, reversePush_step_none]

/-- Lift a statement over the combined component stacks into the
scratch-extended stack family. Labels, state, and statement behavior are
unchanged; every component-stack index is injected on the left. -/
def liftScratchStmt {Γ₀ Γ₁ Γ₂ Λ σ : Type}
    (first : TM2ComputableAux Γ₀ Γ₁)
    (second : TM2ComputableAux Γ₁ Γ₂) :
    TM2.Stmt (StackAlphabet first.tm second.tm) Λ σ →
      TM2.Stmt (TransferStackAlphabet first second) Λ σ
  | .push index write next =>
      .push (Sum.inl index) write (liftScratchStmt first second next)
  | .peek index read next =>
      .peek (Sum.inl index) read (liftScratchStmt first second next)
  | .pop index read next =>
      .pop (Sum.inl index) read (liftScratchStmt first second next)
  | .load update next =>
      .load update (liftScratchStmt first second next)
  | .branch test yes no =>
      .branch test (liftScratchStmt first second yes)
        (liftScratchStmt first second no)
  | .goto next => .goto next
  | .halt => .halt

/-- Embed a combined-stack configuration into the scratch-extended layout,
preserving an arbitrary scratch-stack value. -/
def liftScratchCfg {Γ₀ Γ₁ Γ₂ Λ σ : Type}
    (first : TM2ComputableAux Γ₀ Γ₁)
    (second : TM2ComputableAux Γ₁ Γ₂) (scratch : List Γ₁)
    (cfg : TM2.Cfg (StackAlphabet first.tm second.tm) Λ σ) :
    TM2.Cfg (TransferStackAlphabet first second) Λ σ where
  l := cfg.l
  var := cfg.var
  stk := extendStacks first second cfg.stk scratch

/-- Lift a combined-stack program into the scratch-extended layout. -/
def liftScratchProgram {Γ₀ Γ₁ Γ₂ Λ σ : Type}
    (first : TM2ComputableAux Γ₀ Γ₁)
    (second : TM2ComputableAux Γ₁ Γ₂)
    (program : Λ → TM2.Stmt (StackAlphabet first.tm second.tm) Λ σ) :
    Λ → TM2.Stmt (TransferStackAlphabet first second) Λ σ :=
  fun label => liftScratchStmt first second (program label)

/-- Lifting into the scratch-extended stack family commutes with execution of
one complete statement and leaves the scratch stack unchanged. -/
theorem liftScratch_stepAux {Γ₀ Γ₁ Γ₂ Λ σ : Type}
    (first : TM2ComputableAux Γ₀ Γ₁)
    (second : TM2ComputableAux Γ₁ Γ₂)
    (stmt : TM2.Stmt (StackAlphabet first.tm second.tm) Λ σ)
    (state : σ)
    (contents : ∀ k, List (StackAlphabet first.tm second.tm k))
    (scratch : List Γ₁) :
    TM2.stepAux (liftScratchStmt first second stmt) state
        (extendStacks first second contents scratch) =
      liftScratchCfg first second scratch
        (TM2.stepAux stmt state contents) := by
  induction stmt generalizing state contents with
  | push index write next ih =>
      simp only [liftScratchStmt, TM2.stepAux]
      rw [← extendStacks_update]
      exact ih _ _
  | peek index read next ih =>
      simpa only [liftScratchStmt, TM2.stepAux, extendStacks] using
        ih (read state (contents index).head?) contents
  | pop index read next ih =>
      simp only [liftScratchStmt, TM2.stepAux, extendStacks]
      rw [← extendStacks_update]
      exact ih _ _
  | load update next ih =>
      simpa only [liftScratchStmt, TM2.stepAux] using
        ih (update state) contents
  | branch test yes no ihYes ihNo =>
      by_cases h : test state
      · simpa only [liftScratchStmt, TM2.stepAux, h, cond_true] using
          ihYes state contents
      · simpa only [liftScratchStmt, TM2.stepAux, h, cond_false] using
          ihNo state contents
  | goto next =>
      rfl
  | halt =>
      rfl

/-- One program step is simulated exactly after adding scratch storage. -/
theorem liftScratch_step {Γ₀ Γ₁ Γ₂ Λ σ : Type}
    (first : TM2ComputableAux Γ₀ Γ₁)
    (second : TM2ComputableAux Γ₁ Γ₂)
    (program : Λ → TM2.Stmt (StackAlphabet first.tm second.tm) Λ σ)
    (cfg : TM2.Cfg (StackAlphabet first.tm second.tm) Λ σ)
    (scratch : List Γ₁) :
    TM2.step (liftScratchProgram first second program)
        (liftScratchCfg first second scratch cfg) =
      Option.map (liftScratchCfg first second scratch)
        (TM2.step program cfg) := by
  cases cfg with
  | mk label state contents =>
      cases label with
      | none =>
          rfl
      | some label =>
          simp only [liftScratchCfg, TM2.step, liftScratchProgram]
          rw [liftScratch_stepAux]
          rfl

end LeanNPHardness.MachineComposition
