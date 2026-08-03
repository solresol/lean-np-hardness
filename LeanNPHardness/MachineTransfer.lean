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

end LeanNPHardness.MachineComposition
