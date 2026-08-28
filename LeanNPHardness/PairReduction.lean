import LeanNPHardness.PairAdapter

namespace LeanNPHardness.MachineAdapters

open Turing

/-- Extend the five preprocessing stacks with every private stack of a
reduction machine. Keeping the families disjoint lets the reduction run
without changing the restored certificate or the preprocessing scratch
stacks. -/
def PairReductionStackIndex {Γ₀ Γ₁ : Type}
    (computer : TM2ComputableAux Γ₀ Γ₁) :=
  PairAdapterStackIndex ⊕ computer.tm.K

instance {Γ₀ Γ₁ : Type} (computer : TM2ComputableAux Γ₀ Γ₁) :
    DecidableEq (PairReductionStackIndex computer) := by
  letI : DecidableEq computer.tm.K := computer.tm.kDecidableEq
  exact inferInstanceAs
    (DecidableEq (PairAdapterStackIndex ⊕ computer.tm.K))

instance {Γ₀ Γ₁ : Type} (computer : TM2ComputableAux Γ₀ Γ₁) :
    Fintype (PairReductionStackIndex computer) := by
  letI : Fintype computer.tm.K := computer.tm.kFin
  exact inferInstanceAs (Fintype (PairAdapterStackIndex ⊕ computer.tm.K))

/-- Alphabet family for the preprocessing stacks and the reduction machine's
private stacks. The restored left component uses the reduction's canonical
input alphabet `Γ₀`; the right component is the certificate alphabet. -/
def PairReductionStackAlphabet {Γ₀ Γ₁ : Type}
    (computer : TM2ComputableAux Γ₀ Γ₁) (Δ : Type) :
    PairReductionStackIndex computer → Type
  | Sum.inl index => PairAdapterStackAlphabet Γ₀ Δ index
  | Sum.inr index => computer.tm.Γ index

/-- Combine arbitrary preprocessing-stack contents with arbitrary reduction
machine contents. This form is useful both before the reduction starts and
while simulating an intermediate reduction configuration. -/
def pairReductionStacks {Γ₀ Γ₁ Δ : Type}
    (computer : TM2ComputableAux Γ₀ Γ₁)
    (adapterContents :
      ∀ index, List (PairAdapterStackAlphabet Γ₀ Δ index))
    (machineContents : ∀ index, List (computer.tm.Γ index)) :
    ∀ index, List (PairReductionStackAlphabet computer Δ index)
  | Sum.inl index => adapterContents index
  | Sum.inr index => machineContents index

@[simp]
theorem pairReductionStacks_adapter {Γ₀ Γ₁ Δ : Type}
    (computer : TM2ComputableAux Γ₀ Γ₁)
    (adapterContents :
      ∀ index, List (PairAdapterStackAlphabet Γ₀ Δ index))
    (machineContents : ∀ index, List (computer.tm.Γ index))
    (index : PairAdapterStackIndex) :
    pairReductionStacks computer adapterContents machineContents
        (Sum.inl index) = adapterContents index :=
  rfl

@[simp]
theorem pairReductionStacks_machine {Γ₀ Γ₁ Δ : Type}
    (computer : TM2ComputableAux Γ₀ Γ₁)
    (adapterContents :
      ∀ index, List (PairAdapterStackAlphabet Γ₀ Δ index))
    (machineContents : ∀ index, List (computer.tm.Γ index))
    (index : computer.tm.K) :
    pairReductionStacks computer adapterContents machineContents
        (Sum.inr index) = machineContents index :=
  rfl

/-- Updating a private reduction-machine stack commutes with embedding it in
the combined pair-reduction layout. -/
theorem pairReductionStacks_machine_update {Γ₀ Γ₁ Δ : Type}
    (computer : TM2ComputableAux Γ₀ Γ₁)
    (adapterContents :
      ∀ index, List (PairAdapterStackAlphabet Γ₀ Δ index))
    (machineContents : ∀ index, List (computer.tm.Γ index))
    (index : computer.tm.K) (value : List (computer.tm.Γ index)) :
    pairReductionStacks computer adapterContents
        (Function.update machineContents index value) =
      Function.update
        (pairReductionStacks computer adapterContents machineContents)
        (Sum.inr index) value := by
  funext combinedIndex
  cases combinedIndex with
  | inl adapterIndex =>
      simp [pairReductionStacks]
  | inr machineIndex =>
      by_cases h : machineIndex = index
      · subst machineIndex
        simp [pairReductionStacks]
      · have hsum :
            (Sum.inr machineIndex : PairReductionStackIndex computer) ≠
              Sum.inr index := by
          intro equality
          exact h (Sum.inr.inj equality)
        simp [pairReductionStacks, h, hsum]

/-- Lift a reduction-machine statement to the combined pair-reduction stack
family. Only private machine stacks are addressed; labels, state, and halt
behavior are unchanged. -/
def liftReductionStmt {Γ₀ Γ₁ Δ : Type}
    (computer : TM2ComputableAux Γ₀ Γ₁) :
    TM2.Stmt computer.tm.Γ computer.tm.Λ computer.tm.σ →
      TM2.Stmt (PairReductionStackAlphabet computer Δ)
        computer.tm.Λ computer.tm.σ
  | .push index write next =>
      .push (Sum.inr index) write (liftReductionStmt computer next)
  | .peek index read next =>
      .peek (Sum.inr index) read (liftReductionStmt computer next)
  | .pop index read next =>
      .pop (Sum.inr index) read (liftReductionStmt computer next)
  | .load update next =>
      .load update (liftReductionStmt computer next)
  | .branch test yes no =>
      .branch test (liftReductionStmt computer yes)
        (liftReductionStmt computer no)
  | .goto next => .goto next
  | .halt => .halt

/-- Embed a reduction-machine configuration while preserving arbitrary
contents on all five preprocessing stacks. -/
def liftReductionCfg {Γ₀ Γ₁ Δ : Type}
    (computer : TM2ComputableAux Γ₀ Γ₁)
    (adapterContents :
      ∀ index, List (PairAdapterStackAlphabet Γ₀ Δ index))
    (cfg : TM2.Cfg computer.tm.Γ computer.tm.Λ computer.tm.σ) :
    TM2.Cfg (PairReductionStackAlphabet computer Δ)
      computer.tm.Λ computer.tm.σ where
  l := cfg.l
  var := cfg.var
  stk := pairReductionStacks computer adapterContents cfg.stk

@[simp]
theorem liftReductionCfg_adapter {Γ₀ Γ₁ Δ : Type}
    (computer : TM2ComputableAux Γ₀ Γ₁)
    (adapterContents :
      ∀ index, List (PairAdapterStackAlphabet Γ₀ Δ index))
    (cfg : TM2.Cfg computer.tm.Γ computer.tm.Λ computer.tm.σ)
    (index : PairAdapterStackIndex) :
    (liftReductionCfg computer adapterContents cfg).stk (Sum.inl index) =
      adapterContents index :=
  rfl

/-- Lift the whole reduction program to the combined stack family. -/
def liftReductionProgram {Γ₀ Γ₁ Δ : Type}
    (computer : TM2ComputableAux Γ₀ Γ₁)
    (program : computer.tm.Λ →
      TM2.Stmt computer.tm.Γ computer.tm.Λ computer.tm.σ) :
    computer.tm.Λ →
      TM2.Stmt (PairReductionStackAlphabet computer Δ)
        computer.tm.Λ computer.tm.σ :=
  fun label => liftReductionStmt computer (program label)

/-- Lifting a reduction statement commutes with its complete execution and
leaves every preprocessing stack unchanged. -/
theorem liftReduction_stepAux {Γ₀ Γ₁ Δ : Type}
    (computer : TM2ComputableAux Γ₀ Γ₁)
    (stmt : TM2.Stmt computer.tm.Γ computer.tm.Λ computer.tm.σ)
    (state : computer.tm.σ)
    (machineContents : ∀ index, List (computer.tm.Γ index))
    (adapterContents :
      ∀ index, List (PairAdapterStackAlphabet Γ₀ Δ index)) :
    TM2.stepAux (liftReductionStmt computer stmt) state
        (pairReductionStacks computer adapterContents machineContents) =
      liftReductionCfg computer adapterContents
        (TM2.stepAux stmt state machineContents) := by
  induction stmt generalizing state machineContents with
  | push index write next ih =>
      simp only [liftReductionStmt, TM2.stepAux]
      rw [← pairReductionStacks_machine_update]
      exact ih _ _
  | peek index read next ih =>
      simpa only [liftReductionStmt, TM2.stepAux,
        pairReductionStacks_machine] using
        ih (read state (machineContents index).head?) machineContents
  | pop index read next ih =>
      simp only [liftReductionStmt, TM2.stepAux,
        pairReductionStacks_machine]
      rw [← pairReductionStacks_machine_update]
      exact ih _ _
  | load update next ih =>
      simpa only [liftReductionStmt, TM2.stepAux] using
        ih (update state) machineContents
  | branch test yes no ihYes ihNo =>
      by_cases h : test state
      · simpa only [liftReductionStmt, TM2.stepAux, h, cond_true] using
          ihYes state machineContents
      · simpa only [liftReductionStmt, TM2.stepAux, h, cond_false] using
          ihNo state machineContents
  | goto next =>
      rfl
  | halt =>
      rfl

/-- One reduction-program step is simulated exactly in the extended layout.
The unchanged `adapterContents` parameter includes the ordered certificate
stack, making certificate preservation explicit in the theorem statement. -/
theorem liftReduction_step {Γ₀ Γ₁ Δ : Type}
    (computer : TM2ComputableAux Γ₀ Γ₁)
    (program : computer.tm.Λ →
      TM2.Stmt computer.tm.Γ computer.tm.Λ computer.tm.σ)
    (cfg : TM2.Cfg computer.tm.Γ computer.tm.Λ computer.tm.σ)
    (adapterContents :
      ∀ index, List (PairAdapterStackAlphabet Γ₀ Δ index)) :
    TM2.step (liftReductionProgram computer program)
        (liftReductionCfg computer adapterContents cfg) =
      Option.map (liftReductionCfg computer adapterContents)
        (TM2.step program cfg) := by
  cases cfg with
  | mk label state machineContents =>
      cases label with
      | none =>
          rfl
      | some label =>
          simp only [liftReductionCfg, TM2.step, liftReductionProgram]
          rw [liftReduction_stepAux]
          rfl

end LeanNPHardness.MachineAdapters
