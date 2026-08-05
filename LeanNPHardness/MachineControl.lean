import LeanNPHardness.MachineEmbedding

namespace LeanNPHardness.MachineComposition

open Turing

/-- The two stages of an order-preserving intermediate-output transfer. The
first stage reverses the first machine's output onto scratch storage; the
second stage reverses scratch storage onto the second machine's input. -/
inductive TransferPhase
  | reverseOutput
  | fillInput
  deriving DecidableEq, Fintype

/-- Executable transfer actions. The intermediate `reversePush` action carries
the optional canonical symbol read from the first output stack, so an empty
stack can advance to `fillInput` without assuming an arbitrary inhabitant of
the middle alphabet. -/
inductive TransferAction (Γ : Type)
  | phase (phase : TransferPhase)
  | reversePush (symbol : Option Γ)
  deriving DecidableEq, Fintype

/-- Labels for the two component programs and the executable transfer
actions. -/
def ControlLabel {Γ₀ Γ₁ Γ₂ : Type}
    (first : TM2ComputableAux Γ₀ Γ₁)
    (second : TM2ComputableAux Γ₁ Γ₂) :=
  first.tm.Λ ⊕ (TransferAction Γ₁ ⊕ second.tm.Λ)

instance {Γ₀ Γ₁ Γ₂ : Type} [Fintype Γ₁]
    (first : TM2ComputableAux Γ₀ Γ₁)
    (second : TM2ComputableAux Γ₁ Γ₂) :
    Fintype (ControlLabel first second) := by
  letI : Fintype first.tm.Λ := first.tm.ΛFin
  letI : Fintype second.tm.Λ := second.tm.ΛFin
  exact inferInstanceAs
    (Fintype (first.tm.Λ ⊕ (TransferAction Γ₁ ⊕ second.tm.Λ)))

/-- Inject a first-machine label into combined control. -/
def leftLabel {Γ₀ Γ₁ Γ₂ : Type}
    (first : TM2ComputableAux Γ₀ Γ₁)
    (second : TM2ComputableAux Γ₁ Γ₂) (label : first.tm.Λ) :
    ControlLabel first second :=
  Sum.inl label

/-- Inject an executable transfer action into combined control. -/
def transferActionLabel {Γ₀ Γ₁ Γ₂ : Type}
    (first : TM2ComputableAux Γ₀ Γ₁)
    (second : TM2ComputableAux Γ₁ Γ₂) (action : TransferAction Γ₁) :
    ControlLabel first second :=
  Sum.inr (Sum.inl action)

/-- Inject a transfer stage into combined control. -/
def transferPhaseLabel {Γ₀ Γ₁ Γ₂ : Type}
    (first : TM2ComputableAux Γ₀ Γ₁)
    (second : TM2ComputableAux Γ₁ Γ₂) (phase : TransferPhase) :
    ControlLabel first second :=
  transferActionLabel first second (.phase phase)

/-- The entry label for transferring the intermediate encoding. -/
def transferLabel {Γ₀ Γ₁ Γ₂ : Type}
    (first : TM2ComputableAux Γ₀ Γ₁)
    (second : TM2ComputableAux Γ₁ Γ₂) :
    ControlLabel first second :=
  transferPhaseLabel first second .reverseOutput

/-- The second transfer-stage label, which fills the second input stack from
the reversed scratch stack. -/
def fillInputLabel {Γ₀ Γ₁ Γ₂ : Type}
    (first : TM2ComputableAux Γ₀ Γ₁)
    (second : TM2ComputableAux Γ₁ Γ₂) :
    ControlLabel first second :=
  transferPhaseLabel first second .fillInput

/-- The action label following a reverse-output pop. A present symbol is
pushed to scratch; absence records that the source stack is exhausted. -/
def reversePushLabel {Γ₀ Γ₁ Γ₂ : Type}
    (first : TM2ComputableAux Γ₀ Γ₁)
    (second : TM2ComputableAux Γ₁ Γ₂) (symbol : Option Γ₁) :
    ControlLabel first second :=
  transferActionLabel first second (.reversePush symbol)

/-- Inject a second-machine label into combined control. -/
def rightLabel {Γ₀ Γ₁ Γ₂ : Type}
    (first : TM2ComputableAux Γ₀ Γ₁)
    (second : TM2ComputableAux Γ₁ Γ₂) (label : second.tm.Λ) :
    ControlLabel first second :=
  Sum.inr (Sum.inr label)

@[simp]
theorem leftLabel_ne_transferLabel {Γ₀ Γ₁ Γ₂ : Type}
    (first : TM2ComputableAux Γ₀ Γ₁)
    (second : TM2ComputableAux Γ₁ Γ₂) (label : first.tm.Λ) :
    leftLabel first second label ≠ transferLabel first second := by
  simp [leftLabel, transferLabel, transferPhaseLabel, transferActionLabel]

@[simp]
theorem rightLabel_ne_transferLabel {Γ₀ Γ₁ Γ₂ : Type}
    (first : TM2ComputableAux Γ₀ Γ₁)
    (second : TM2ComputableAux Γ₁ Γ₂) (label : second.tm.Λ) :
    rightLabel first second label ≠ transferLabel first second := by
  intro equality
  have inner :
      (Sum.inr label : TransferAction Γ₁ ⊕ second.tm.Λ) =
        Sum.inl (.phase .reverseOutput) :=
    Sum.inr.inj equality
  cases inner

@[simp]
theorem transferLabel_ne_fillInputLabel {Γ₀ Γ₁ Γ₂ : Type}
    (first : TM2ComputableAux Γ₀ Γ₁)
    (second : TM2ComputableAux Γ₁ Γ₂) :
    transferLabel first second ≠ fillInputLabel first second := by
  intro equality
  have actionEquality :
      TransferAction.phase TransferPhase.reverseOutput =
        TransferAction.phase TransferPhase.fillInput :=
    Sum.inl.inj (Sum.inr.inj equality)
  have phaseEquality :
      TransferPhase.reverseOutput = TransferPhase.fillInput :=
    TransferAction.phase.inj actionEquality
  cases phaseEquality

/-- Phase-tagged internal state. The transfer phase stores at most one symbol
in the shared, finite middle encoding alphabet rather than either machine's
private stack alphabet. -/
def ControlState {Γ₀ Γ₁ Γ₂ : Type}
    (first : TM2ComputableAux Γ₀ Γ₁)
    (second : TM2ComputableAux Γ₁ Γ₂) :=
  first.tm.σ ⊕ (Option Γ₁ ⊕ second.tm.σ)

instance {Γ₀ Γ₁ Γ₂ : Type} [Fintype Γ₁]
    (first : TM2ComputableAux Γ₀ Γ₁)
    (second : TM2ComputableAux Γ₁ Γ₂) :
    Fintype (ControlState first second) := by
  letI : Fintype first.tm.σ := first.tm.σFin
  letI : Fintype second.tm.σ := second.tm.σFin
  exact inferInstanceAs
    (Fintype (first.tm.σ ⊕ (Option Γ₁ ⊕ second.tm.σ)))

/-- Inject a first-machine state into combined control. -/
def leftState {Γ₀ Γ₁ Γ₂ : Type}
    (first : TM2ComputableAux Γ₀ Γ₁)
    (second : TM2ComputableAux Γ₁ Γ₂) (state : first.tm.σ) :
    ControlState first second :=
  Sum.inl state

/-- A transfer-phase state, optionally holding one canonical middle symbol. -/
def transferState {Γ₀ Γ₁ Γ₂ : Type}
    (first : TM2ComputableAux Γ₀ Γ₁)
    (second : TM2ComputableAux Γ₁ Γ₂) (symbol : Option Γ₁) :
    ControlState first second :=
  Sum.inr (Sum.inl symbol)

/-- Read the optional canonical symbol held by a transfer state. States from
either component phase map to `none`, keeping transfer label selection total. -/
def transferStateValue {Γ₀ Γ₁ Γ₂ : Type}
    (first : TM2ComputableAux Γ₀ Γ₁)
    (second : TM2ComputableAux Γ₁ Γ₂) :
    ControlState first second → Option Γ₁
  | Sum.inr (Sum.inl symbol) => symbol
  | _ => none

/-- Inject a second-machine state into combined control. -/
def rightState {Γ₀ Γ₁ Γ₂ : Type}
    (first : TM2ComputableAux Γ₀ Γ₁)
    (second : TM2ComputableAux Γ₁ Γ₂) (state : second.tm.σ) :
    ControlState first second :=
  Sum.inr (Sum.inr state)

/-- Read a first-machine state, using its declared initial state outside the
first phase so lifted statement functions remain total. -/
def leftStateValue {Γ₀ Γ₁ Γ₂ : Type}
    (first : TM2ComputableAux Γ₀ Γ₁)
    (second : TM2ComputableAux Γ₁ Γ₂) :
    ControlState first second → first.tm.σ
  | Sum.inl state => state
  | Sum.inr _ => first.tm.initialState

/-- Read a second-machine state, using its declared initial state outside the
second phase so lifted statement functions remain total. -/
def rightStateValue {Γ₀ Γ₁ Γ₂ : Type}
    (first : TM2ComputableAux Γ₀ Γ₁)
    (second : TM2ComputableAux Γ₁ Γ₂) :
    ControlState first second → second.tm.σ
  | Sum.inl _ => second.tm.initialState
  | Sum.inr (Sum.inl _) => second.tm.initialState
  | Sum.inr (Sum.inr state) => state

@[simp]
theorem leftStateValue_leftState {Γ₀ Γ₁ Γ₂ : Type}
    (first : TM2ComputableAux Γ₀ Γ₁)
    (second : TM2ComputableAux Γ₁ Γ₂) (state : first.tm.σ) :
    leftStateValue first second (leftState first second state) = state :=
  rfl

@[simp]
theorem rightStateValue_rightState {Γ₀ Γ₁ Γ₂ : Type}
    (first : TM2ComputableAux Γ₀ Γ₁)
    (second : TM2ComputableAux Γ₁ Γ₂) (state : second.tm.σ) :
    rightStateValue first second (rightState first second state) = state :=
  rfl

@[simp]
theorem transferStateValue_transferState {Γ₀ Γ₁ Γ₂ : Type}
    (first : TM2ComputableAux Γ₀ Γ₁)
    (second : TM2ComputableAux Γ₁ Γ₂) (symbol : Option Γ₁) :
    transferStateValue first second (transferState first second symbol) = symbol :=
  rfl

/-- Convert a symbol from the first machine's output stack alphabet to the
second machine's input stack alphabet through their shared encoded alphabet. -/
def middleAlphabetEquiv {Γ₀ Γ₁ Γ₂ : Type}
    (first : TM2ComputableAux Γ₀ Γ₁)
    (second : TM2ComputableAux Γ₁ Γ₂) :
    first.tm.Γ first.tm.k₁ ≃ second.tm.Γ second.tm.k₀ :=
  first.outputAlphabet.trans second.inputAlphabet.symm

@[simp]
theorem middleAlphabetEquiv_apply {Γ₀ Γ₁ Γ₂ : Type}
    (first : TM2ComputableAux Γ₀ Γ₁)
    (second : TM2ComputableAux Γ₁ Γ₂)
    (symbol : first.tm.Γ first.tm.k₁) :
    middleAlphabetEquiv first second symbol =
      second.inputAlphabet.symm (first.outputAlphabet symbol) :=
  rfl

@[simp]
theorem middleAlphabetEquiv_symm_apply_apply {Γ₀ Γ₁ Γ₂ : Type}
    (first : TM2ComputableAux Γ₀ Γ₁)
    (second : TM2ComputableAux Γ₁ Γ₂)
    (symbol : first.tm.Γ first.tm.k₁) :
    (middleAlphabetEquiv first second).symm
        (middleAlphabetEquiv first second symbol) = symbol :=
  Equiv.symm_apply_apply (middleAlphabetEquiv first second) symbol

@[simp]
theorem middleAlphabetEquiv_apply_symm_apply {Γ₀ Γ₁ Γ₂ : Type}
    (first : TM2ComputableAux Γ₀ Γ₁)
    (second : TM2ComputableAux Γ₁ Γ₂)
    (symbol : second.tm.Γ second.tm.k₀) :
    middleAlphabetEquiv first second
        ((middleAlphabetEquiv first second).symm symbol) = symbol :=
  Equiv.apply_symm_apply (middleAlphabetEquiv first second) symbol

end LeanNPHardness.MachineComposition
