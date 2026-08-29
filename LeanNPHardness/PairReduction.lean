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

/-- Updating a preprocessing stack commutes with embedding it in the combined
pair-reduction layout. This is the adapter-side counterpart of
`pairReductionStacks_machine_update`. -/
theorem pairReductionStacks_adapter_update {Γ₀ Γ₁ Δ : Type}
    (computer : TM2ComputableAux Γ₀ Γ₁)
    (adapterContents :
      ∀ index, List (PairAdapterStackAlphabet Γ₀ Δ index))
    (machineContents : ∀ index, List (computer.tm.Γ index))
    (index : PairAdapterStackIndex)
    (value : List (PairAdapterStackAlphabet Γ₀ Δ index)) :
    pairReductionStacks computer
        (Function.update adapterContents index value) machineContents =
      Function.update
        (pairReductionStacks computer adapterContents machineContents)
        (Sum.inl index) value := by
  funext combinedIndex
  cases combinedIndex with
  | inl adapterIndex =>
      by_cases h : adapterIndex = index
      · subst adapterIndex
        simp [pairReductionStacks]
      · have hsum :
            (Sum.inl adapterIndex : PairReductionStackIndex computer) ≠
              Sum.inl index := by
          intro equality
          exact h (Sum.inl.inj equality)
        simp [pairReductionStacks, h, hsum]
  | inr machineIndex =>
      simp [pairReductionStacks]

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

/-- Finite control for moving the restored left input into the reduction
machine's private input stack. The first phase reverses the ordered input onto
the now-empty left scratch stack; the second phase restores the order while
converting each symbol through the reduction machine's input equivalence. -/
inductive PairInputTransferLabel (Γ₀ : Type)
  | reverseScan
  | reversePush (symbol : Option Γ₀)
  | fillScan
  | fillPush (symbol : Option Γ₀)
  | done
  deriving DecidableEq, Fintype

/-- Explicit configuration for the ordered-input transfer program. The source
and certificate stacks are parameters so the execution theorems state their
preservation directly. -/
def pairInputTransferCfg {Γ₀ Γ₁ Δ : Type}
    (computer : TM2ComputableAux Γ₀ Γ₁)
    (label : PairInputTransferLabel Γ₀) (state : Option Γ₀)
    (source : List (Sum Γ₀ Δ)) (leftReverse leftOrdered : List Γ₀)
    (rightReverse rightOrdered : List Δ)
    (machineContents : ∀ index, List (computer.tm.Γ index)) :
    TM2.Cfg (PairReductionStackAlphabet computer Δ)
      (PairInputTransferLabel Γ₀) (Option Γ₀) where
  l := some label
  var := state
  stk := pairReductionStacks computer
    (pairAdapterStacks source leftReverse leftOrdered rightReverse
      rightOrdered) machineContents

/-- Total two-phase input-transfer dispatcher. The `done` label halts in this
standalone program; a later combined dispatcher can redirect it to the lifted
reduction machine's initial control. -/
def pairInputTransferProgram {Γ₀ Γ₁ Δ : Type}
    (computer : TM2ComputableAux Γ₀ Γ₁) :
    PairInputTransferLabel Γ₀ →
      TM2.Stmt (PairReductionStackAlphabet computer Δ)
        (PairInputTransferLabel Γ₀) (Option Γ₀)
  | .reverseScan =>
      .pop (Sum.inl .leftOrdered) (fun _ symbol => symbol)
        (.goto (fun symbol => .reversePush symbol))
  | .reversePush none => .goto (fun _ => .fillScan)
  | .reversePush (some symbol) =>
      .push (Sum.inl .leftReverse) (fun _ => symbol)
        (.goto (fun _ => .reverseScan))
  | .fillScan =>
      .pop (Sum.inl .leftReverse) (fun _ symbol => symbol)
        (.goto (fun symbol => .fillPush symbol))
  | .fillPush none => .goto (fun _ => .done)
  | .fillPush (some symbol) =>
      .push (Sum.inr computer.tm.k₀)
        (fun _ => computer.inputAlphabet.symm symbol)
        (.goto (fun _ => .fillScan))
  | .done => .halt

theorem pairInputTransfer_reverseScan_step_nonempty {Γ₀ Γ₁ Δ : Type}
    (computer : TM2ComputableAux Γ₀ Γ₁) (state : Option Γ₀)
    (source : List (Sum Γ₀ Δ)) (leftReverse : List Γ₀)
    (head : Γ₀) (tail : List Γ₀) (rightReverse rightOrdered : List Δ)
    (machineContents : ∀ index, List (computer.tm.Γ index)) :
    TM2.step (pairInputTransferProgram computer)
        (pairInputTransferCfg computer .reverseScan state source leftReverse
          (head :: tail) rightReverse rightOrdered machineContents) =
      some (pairInputTransferCfg computer (.reversePush (some head))
        (some head) source leftReverse tail rightReverse rightOrdered
        machineContents) := by
  simp only [TM2.step, pairInputTransferProgram, TM2.stepAux,
    pairInputTransferCfg, pairReductionStacks_adapter,
    pairAdapterStacks_leftOrdered]
  rw [← pairReductionStacks_adapter_update,
    pairAdapterStacks_leftOrdered_update]
  simp

theorem pairInputTransfer_reverseScan_step_empty {Γ₀ Γ₁ Δ : Type}
    (computer : TM2ComputableAux Γ₀ Γ₁) (state : Option Γ₀)
    (source : List (Sum Γ₀ Δ)) (leftReverse : List Γ₀)
    (rightReverse rightOrdered : List Δ)
    (machineContents : ∀ index, List (computer.tm.Γ index)) :
    TM2.step (pairInputTransferProgram computer)
        (pairInputTransferCfg computer .reverseScan state source leftReverse
          [] rightReverse rightOrdered machineContents) =
      some (pairInputTransferCfg computer (.reversePush none) none source
        leftReverse [] rightReverse rightOrdered machineContents) := by
  simp only [TM2.step, pairInputTransferProgram, TM2.stepAux,
    pairInputTransferCfg, pairReductionStacks_adapter,
    pairAdapterStacks_leftOrdered]
  rw [← pairReductionStacks_adapter_update,
    pairAdapterStacks_leftOrdered_update]
  simp

theorem pairInputTransfer_reversePush_step_some {Γ₀ Γ₁ Δ : Type}
    (computer : TM2ComputableAux Γ₀ Γ₁) (symbol : Γ₀)
    (state : Option Γ₀) (source : List (Sum Γ₀ Δ))
    (leftReverse leftOrdered : List Γ₀)
    (rightReverse rightOrdered : List Δ)
    (machineContents : ∀ index, List (computer.tm.Γ index)) :
    TM2.step (pairInputTransferProgram computer)
        (pairInputTransferCfg computer (.reversePush (some symbol)) state
          source leftReverse leftOrdered rightReverse rightOrdered
          machineContents) =
      some (pairInputTransferCfg computer .reverseScan state source
        (symbol :: leftReverse) leftOrdered rightReverse rightOrdered
        machineContents) := by
  simp only [TM2.step, pairInputTransferProgram, TM2.stepAux,
    pairInputTransferCfg, pairReductionStacks_adapter,
    pairAdapterStacks_leftReverse]
  rw [← pairReductionStacks_adapter_update,
    pairAdapterStacks_leftReverse_update]

theorem pairInputTransfer_reversePush_step_none {Γ₀ Γ₁ Δ : Type}
    (computer : TM2ComputableAux Γ₀ Γ₁) (state : Option Γ₀)
    (source : List (Sum Γ₀ Δ)) (leftReverse leftOrdered : List Γ₀)
    (rightReverse rightOrdered : List Δ)
    (machineContents : ∀ index, List (computer.tm.Γ index)) :
    TM2.step (pairInputTransferProgram computer)
        (pairInputTransferCfg computer (.reversePush none) state source
          leftReverse leftOrdered rightReverse rightOrdered machineContents) =
      some (pairInputTransferCfg computer .fillScan state source leftReverse
        leftOrdered rightReverse rightOrdered machineContents) :=
  rfl

theorem pairInputTransfer_reverse_iteration_nonempty {Γ₀ Γ₁ Δ : Type}
    (computer : TM2ComputableAux Γ₀ Γ₁) (state : Option Γ₀)
    (source : List (Sum Γ₀ Δ)) (leftReverse : List Γ₀)
    (head : Γ₀) (tail : List Γ₀) (rightReverse rightOrdered : List Δ)
    (machineContents : ∀ index, List (computer.tm.Γ index)) :
    (TM2.step (pairInputTransferProgram computer)
        (pairInputTransferCfg computer .reverseScan state source leftReverse
          (head :: tail) rightReverse rightOrdered machineContents)).bind
        (TM2.step (pairInputTransferProgram computer)) =
      some (pairInputTransferCfg computer .reverseScan (some head) source
        (head :: leftReverse) tail rightReverse rightOrdered
        machineContents) := by
  rw [pairInputTransfer_reverseScan_step_nonempty, Option.bind_some,
    pairInputTransfer_reversePush_step_some]

theorem pairInputTransfer_reverse_iteration_empty {Γ₀ Γ₁ Δ : Type}
    (computer : TM2ComputableAux Γ₀ Γ₁) (state : Option Γ₀)
    (source : List (Sum Γ₀ Δ)) (leftReverse : List Γ₀)
    (rightReverse rightOrdered : List Δ)
    (machineContents : ∀ index, List (computer.tm.Γ index)) :
    (TM2.step (pairInputTransferProgram computer)
        (pairInputTransferCfg computer .reverseScan state source leftReverse
          [] rightReverse rightOrdered machineContents)).bind
        (TM2.step (pairInputTransferProgram computer)) =
      some (pairInputTransferCfg computer .fillScan none source leftReverse []
        rightReverse rightOrdered machineContents) := by
  rw [pairInputTransfer_reverseScan_step_empty, Option.bind_some,
    pairInputTransfer_reversePush_step_none]

/-- The first transfer phase empties the ordered left stack and reverses it
onto the reusable left scratch stack in exactly two steps per symbol plus two
exhaustion steps. -/
theorem pairInputTransfer_reverse_whole_list {Γ₀ Γ₁ Δ : Type}
    (computer : TM2ComputableAux Γ₀ Γ₁) (state : Option Γ₀)
    (source : List (Sum Γ₀ Δ)) (leftReverse input : List Γ₀)
    (rightReverse rightOrdered : List Δ)
    (machineContents : ∀ index, List (computer.tm.Γ index)) :
    (flip Option.bind (TM2.step (pairInputTransferProgram computer)))^[
        2 * input.length + 2]
      (some (pairInputTransferCfg computer .reverseScan state source
        leftReverse input rightReverse rightOrdered machineContents)) =
      some (pairInputTransferCfg computer .fillScan none source
        (input.reverse ++ leftReverse) [] rightReverse rightOrdered
        machineContents) := by
  induction input generalizing state leftReverse with
  | nil =>
      simpa [Function.iterate_succ_apply'] using
        pairInputTransfer_reverse_iteration_empty computer state source
          leftReverse rightReverse rightOrdered machineContents
  | cons head tail ih =>
      have firstIteration :=
        pairInputTransfer_reverse_iteration_nonempty computer state source
          leftReverse head tail rightReverse rightOrdered machineContents
      rw [List.length_cons]
      have stepCount : 2 * (tail.length + 1) + 2 =
          (2 * tail.length + 2) + 2 := by omega
      rw [stepCount, Function.iterate_add_apply]
      rw [show
        (flip Option.bind (TM2.step (pairInputTransferProgram computer)))^[2]
            (some (pairInputTransferCfg computer .reverseScan state source
              leftReverse (head :: tail) rightReverse rightOrdered
              machineContents)) =
          some (pairInputTransferCfg computer .reverseScan (some head) source
            (head :: leftReverse) tail rightReverse rightOrdered
            machineContents) by
        simpa [Function.iterate_succ_apply'] using firstIteration]
      simpa [List.reverse_cons, List.append_assoc] using
        ih (some head) (head :: leftReverse)

theorem pairInputTransfer_fillScan_step_nonempty {Γ₀ Γ₁ Δ : Type}
    (computer : TM2ComputableAux Γ₀ Γ₁) (state : Option Γ₀)
    (source : List (Sum Γ₀ Δ)) (head : Γ₀) (tail leftOrdered : List Γ₀)
    (rightReverse rightOrdered : List Δ)
    (machineContents : ∀ index, List (computer.tm.Γ index)) :
    TM2.step (pairInputTransferProgram computer)
        (pairInputTransferCfg computer .fillScan state source (head :: tail)
          leftOrdered rightReverse rightOrdered machineContents) =
      some (pairInputTransferCfg computer (.fillPush (some head)) (some head)
        source tail leftOrdered rightReverse rightOrdered machineContents) := by
  simp only [TM2.step, pairInputTransferProgram, TM2.stepAux,
    pairInputTransferCfg, pairReductionStacks_adapter,
    pairAdapterStacks_leftReverse]
  rw [← pairReductionStacks_adapter_update,
    pairAdapterStacks_leftReverse_update]
  simp

theorem pairInputTransfer_fillScan_step_empty {Γ₀ Γ₁ Δ : Type}
    (computer : TM2ComputableAux Γ₀ Γ₁) (state : Option Γ₀)
    (source : List (Sum Γ₀ Δ)) (leftOrdered : List Γ₀)
    (rightReverse rightOrdered : List Δ)
    (machineContents : ∀ index, List (computer.tm.Γ index)) :
    TM2.step (pairInputTransferProgram computer)
        (pairInputTransferCfg computer .fillScan state source [] leftOrdered
          rightReverse rightOrdered machineContents) =
      some (pairInputTransferCfg computer (.fillPush none) none source []
        leftOrdered rightReverse rightOrdered machineContents) := by
  simp only [TM2.step, pairInputTransferProgram, TM2.stepAux,
    pairInputTransferCfg, pairReductionStacks_adapter,
    pairAdapterStacks_leftReverse]
  rw [← pairReductionStacks_adapter_update,
    pairAdapterStacks_leftReverse_update]
  simp

theorem pairInputTransfer_fillPush_step_some {Γ₀ Γ₁ Δ : Type}
    (computer : TM2ComputableAux Γ₀ Γ₁) (symbol : Γ₀)
    (state : Option Γ₀) (source : List (Sum Γ₀ Δ))
    (leftReverse leftOrdered : List Γ₀)
    (rightReverse rightOrdered : List Δ)
    (machineContents : ∀ index, List (computer.tm.Γ index)) :
    TM2.step (pairInputTransferProgram computer)
        (pairInputTransferCfg computer (.fillPush (some symbol)) state source
          leftReverse leftOrdered rightReverse rightOrdered machineContents) =
      some (pairInputTransferCfg computer .fillScan state source leftReverse
        leftOrdered rightReverse rightOrdered
        (Function.update machineContents computer.tm.k₀
          (computer.inputAlphabet.symm symbol ::
            machineContents computer.tm.k₀))) := by
  simp only [TM2.step, pairInputTransferProgram, TM2.stepAux,
    pairInputTransferCfg, pairReductionStacks_machine]
  rw [← pairReductionStacks_machine_update]

theorem pairInputTransfer_fillPush_step_none {Γ₀ Γ₁ Δ : Type}
    (computer : TM2ComputableAux Γ₀ Γ₁) (state : Option Γ₀)
    (source : List (Sum Γ₀ Δ)) (leftReverse leftOrdered : List Γ₀)
    (rightReverse rightOrdered : List Δ)
    (machineContents : ∀ index, List (computer.tm.Γ index)) :
    TM2.step (pairInputTransferProgram computer)
        (pairInputTransferCfg computer (.fillPush none) state source
          leftReverse leftOrdered rightReverse rightOrdered machineContents) =
      some (pairInputTransferCfg computer .done state source leftReverse
        leftOrdered rightReverse rightOrdered machineContents) :=
  rfl

theorem pairInputTransfer_fill_iteration_nonempty {Γ₀ Γ₁ Δ : Type}
    (computer : TM2ComputableAux Γ₀ Γ₁) (state : Option Γ₀)
    (source : List (Sum Γ₀ Δ)) (head : Γ₀) (tail leftOrdered : List Γ₀)
    (rightReverse rightOrdered : List Δ)
    (machineContents : ∀ index, List (computer.tm.Γ index)) :
    (TM2.step (pairInputTransferProgram computer)
        (pairInputTransferCfg computer .fillScan state source (head :: tail)
          leftOrdered rightReverse rightOrdered machineContents)).bind
        (TM2.step (pairInputTransferProgram computer)) =
      some (pairInputTransferCfg computer .fillScan (some head) source tail
        leftOrdered rightReverse rightOrdered
        (Function.update machineContents computer.tm.k₀
          (computer.inputAlphabet.symm head ::
            machineContents computer.tm.k₀))) := by
  rw [pairInputTransfer_fillScan_step_nonempty, Option.bind_some,
    pairInputTransfer_fillPush_step_some]

theorem pairInputTransfer_fill_iteration_empty {Γ₀ Γ₁ Δ : Type}
    (computer : TM2ComputableAux Γ₀ Γ₁) (state : Option Γ₀)
    (source : List (Sum Γ₀ Δ)) (leftOrdered : List Γ₀)
    (rightReverse rightOrdered : List Δ)
    (machineContents : ∀ index, List (computer.tm.Γ index)) :
    (TM2.step (pairInputTransferProgram computer)
        (pairInputTransferCfg computer .fillScan state source [] leftOrdered
          rightReverse rightOrdered machineContents)).bind
        (TM2.step (pairInputTransferProgram computer)) =
      some (pairInputTransferCfg computer .done none source [] leftOrdered
        rightReverse rightOrdered machineContents) := by
  rw [pairInputTransfer_fillScan_step_empty, Option.bind_some,
    pairInputTransfer_fillPush_step_none]

/-- The second transfer phase empties scratch and prepends its symbols, in
reverse order, to the reduction machine's private input stack. -/
theorem pairInputTransfer_fill_whole_list {Γ₀ Γ₁ Δ : Type}
    (computer : TM2ComputableAux Γ₀ Γ₁) (state : Option Γ₀)
    (source : List (Sum Γ₀ Δ)) (scratch leftOrdered : List Γ₀)
    (rightReverse rightOrdered : List Δ)
    (machineContents : ∀ index, List (computer.tm.Γ index)) :
    (flip Option.bind (TM2.step (pairInputTransferProgram computer)))^[
        2 * scratch.length + 2]
      (some (pairInputTransferCfg computer .fillScan state source scratch
        leftOrdered rightReverse rightOrdered machineContents)) =
      some (pairInputTransferCfg computer .done none source [] leftOrdered
        rightReverse rightOrdered
        (Function.update machineContents computer.tm.k₀
          ((scratch.map computer.inputAlphabet.symm).reverse ++
            machineContents computer.tm.k₀))) := by
  induction scratch generalizing state machineContents with
  | nil =>
      simpa [Function.iterate_succ_apply'] using
        pairInputTransfer_fill_iteration_empty computer state source
          leftOrdered rightReverse rightOrdered machineContents
  | cons head tail ih =>
      have firstIteration :=
        pairInputTransfer_fill_iteration_nonempty computer state source head
          tail leftOrdered rightReverse rightOrdered machineContents
      rw [List.length_cons]
      have stepCount : 2 * (tail.length + 1) + 2 =
          (2 * tail.length + 2) + 2 := by omega
      rw [stepCount, Function.iterate_add_apply]
      rw [show
        (flip Option.bind (TM2.step (pairInputTransferProgram computer)))^[2]
            (some (pairInputTransferCfg computer .fillScan state source
              (head :: tail) leftOrdered rightReverse rightOrdered
              machineContents)) =
          some (pairInputTransferCfg computer .fillScan (some head) source tail
            leftOrdered rightReverse rightOrdered
            (Function.update machineContents computer.tm.k₀
              (computer.inputAlphabet.symm head ::
                machineContents computer.tm.k₀))) by
        simpa [Function.iterate_succ_apply'] using firstIteration]
      simpa [List.map, List.reverse_cons, List.append_assoc] using
        ih (some head)
          (Function.update machineContents computer.tm.k₀
            (computer.inputAlphabet.symm head ::
              machineContents computer.tm.k₀))

/-- The complete transfer preserves the restored input order. Starting with
empty scratch, it empties the ordered left stack and prepends the equivalent
private symbols to the reduction machine's input stack in exactly four steps
per input symbol plus four exhaustion steps. Every certificate stack and every
other reduction-machine stack is retained. -/
theorem pairInputTransfer_whole_list {Γ₀ Γ₁ Δ : Type}
    (computer : TM2ComputableAux Γ₀ Γ₁) (state : Option Γ₀)
    (source : List (Sum Γ₀ Δ)) (input : List Γ₀)
    (rightReverse rightOrdered : List Δ)
    (machineContents : ∀ index, List (computer.tm.Γ index)) :
    (flip Option.bind (TM2.step (pairInputTransferProgram computer)))^[
        4 * input.length + 4]
      (some (pairInputTransferCfg computer .reverseScan state source [] input
        rightReverse rightOrdered machineContents)) =
      some (pairInputTransferCfg computer .done none source [] [] rightReverse
        rightOrdered
        (Function.update machineContents computer.tm.k₀
          (input.map computer.inputAlphabet.symm ++
            machineContents computer.tm.k₀))) := by
  have reverseRun :=
    pairInputTransfer_reverse_whole_list computer state source [] input
      rightReverse rightOrdered machineContents
  have fillRun :=
    pairInputTransfer_fill_whole_list computer none source input.reverse []
      rightReverse rightOrdered machineContents
  have stepCount :
      4 * input.length + 4 =
        (2 * input.reverse.length + 2) + (2 * input.length + 2) := by
    simp
    omega
  rw [stepCount, Function.iterate_add_apply, reverseRun]
  simpa using fillRun

end LeanNPHardness.MachineAdapters
