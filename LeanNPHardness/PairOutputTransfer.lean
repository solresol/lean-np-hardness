import LeanNPHardness.PairReduction

namespace LeanNPHardness.MachineAdapters

open Turing

/-- Two stacks used only after the reduction machine halts: one reverses the
reduced output, and the other stores the final tagged output/certificate pair.
-/
inductive PairOutputExtraStackIndex
  | reducedReverse
  | output
  deriving DecidableEq, Fintype

/-- Extend the pair/reduction layout with output-reassembly scratch and result
stacks. The old layout is embedded unchanged on the left. -/
def PairOutputStackIndex {Γ₀ Γ₁ : Type}
    (computer : TM2ComputableAux Γ₀ Γ₁) :=
  PairReductionStackIndex computer ⊕ PairOutputExtraStackIndex

instance {Γ₀ Γ₁ : Type} (computer : TM2ComputableAux Γ₀ Γ₁) :
    DecidableEq (PairOutputStackIndex computer) := by
  letI : DecidableEq (PairReductionStackIndex computer) := inferInstance
  exact inferInstanceAs
    (DecidableEq
      (PairReductionStackIndex computer ⊕ PairOutputExtraStackIndex))

instance {Γ₀ Γ₁ : Type} (computer : TM2ComputableAux Γ₀ Γ₁) :
    Fintype (PairOutputStackIndex computer) := by
  letI : Fintype (PairReductionStackIndex computer) := inferInstance
  exact inferInstanceAs
    (Fintype (PairReductionStackIndex computer ⊕ PairOutputExtraStackIndex))

/-- The existing pair/reduction stacks retain their alphabets. The new scratch
uses the canonical reduction-output alphabet, while the final result stack uses
the tagged pair-output alphabet. -/
def PairOutputStackAlphabet {Γ₀ Γ₁ : Type}
    (computer : TM2ComputableAux Γ₀ Γ₁) (Δ : Type) :
    PairOutputStackIndex computer → Type
  | Sum.inl index => PairReductionStackAlphabet computer Δ index
  | Sum.inr .reducedReverse => Γ₁
  | Sum.inr .output => Sum Γ₁ Δ

/-- Combine the complete pre-reassembly layout with the two new output stacks.
-/
def pairOutputStacks {Γ₀ Γ₁ Δ : Type}
    (computer : TM2ComputableAux Γ₀ Γ₁)
    (workingContents :
      ∀ index, List (PairReductionStackAlphabet computer Δ index))
    (reducedReverse : List Γ₁) (output : List (Sum Γ₁ Δ)) :
    ∀ index, List (PairOutputStackAlphabet computer Δ index)
  | Sum.inl index => workingContents index
  | Sum.inr .reducedReverse => reducedReverse
  | Sum.inr .output => output

@[simp]
theorem pairOutputStacks_working {Γ₀ Γ₁ Δ : Type}
    (computer : TM2ComputableAux Γ₀ Γ₁)
    (workingContents :
      ∀ index, List (PairReductionStackAlphabet computer Δ index))
    (reducedReverse : List Γ₁) (output : List (Sum Γ₁ Δ))
    (index : PairReductionStackIndex computer) :
    pairOutputStacks computer workingContents reducedReverse output
        (Sum.inl index) = workingContents index :=
  rfl

@[simp]
theorem pairOutputStacks_reducedReverse {Γ₀ Γ₁ Δ : Type}
    (computer : TM2ComputableAux Γ₀ Γ₁)
    (workingContents :
      ∀ index, List (PairReductionStackAlphabet computer Δ index))
    (reducedReverse : List Γ₁) (output : List (Sum Γ₁ Δ)) :
    pairOutputStacks computer workingContents reducedReverse output
        (Sum.inr .reducedReverse) = reducedReverse :=
  rfl

@[simp]
theorem pairOutputStacks_output {Γ₀ Γ₁ Δ : Type}
    (computer : TM2ComputableAux Γ₀ Γ₁)
    (workingContents :
      ∀ index, List (PairReductionStackAlphabet computer Δ index))
    (reducedReverse : List Γ₁) (output : List (Sum Γ₁ Δ)) :
    pairOutputStacks computer workingContents reducedReverse output
        (Sum.inr .output) = output :=
  rfl

theorem pairOutputStacks_working_update {Γ₀ Γ₁ Δ : Type}
    (computer : TM2ComputableAux Γ₀ Γ₁)
    (workingContents :
      ∀ index, List (PairReductionStackAlphabet computer Δ index))
    (reducedReverse : List Γ₁) (output : List (Sum Γ₁ Δ))
    (index : PairReductionStackIndex computer)
    (value : List (PairReductionStackAlphabet computer Δ index)) :
    Function.update
        (pairOutputStacks computer workingContents reducedReverse output)
        (Sum.inl index) value =
      pairOutputStacks computer (Function.update workingContents index value)
        reducedReverse output := by
  funext combinedIndex
  cases combinedIndex with
  | inl workingIndex =>
      by_cases h : workingIndex = index
      · subst workingIndex
        simp [pairOutputStacks]
      · have hsum :
            (Sum.inl workingIndex : PairOutputStackIndex computer) ≠
              Sum.inl index := by
          intro equality
          exact h (Sum.inl.inj equality)
        simp [pairOutputStacks, h, hsum]
  | inr extraIndex =>
      cases extraIndex <;> simp [pairOutputStacks]

theorem pairOutputStacks_reducedReverse_update {Γ₀ Γ₁ Δ : Type}
    (computer : TM2ComputableAux Γ₀ Γ₁)
    (workingContents :
      ∀ index, List (PairReductionStackAlphabet computer Δ index))
    (reducedReverse value : List Γ₁) (output : List (Sum Γ₁ Δ)) :
    Function.update
        (pairOutputStacks computer workingContents reducedReverse output)
        (Sum.inr .reducedReverse) value =
      pairOutputStacks computer workingContents value output := by
  funext index
  cases index with
  | inl workingIndex => simp [pairOutputStacks]
  | inr extraIndex =>
      cases extraIndex with
      | reducedReverse => simp [pairOutputStacks]
      | output =>
          have h :
              (Sum.inr PairOutputExtraStackIndex.output :
                PairOutputStackIndex computer) ≠
                Sum.inr PairOutputExtraStackIndex.reducedReverse := by
            intro equality
            cases Sum.inr.inj equality
          simp [pairOutputStacks, h]

theorem pairOutputStacks_output_update {Γ₀ Γ₁ Δ : Type}
    (computer : TM2ComputableAux Γ₀ Γ₁)
    (workingContents :
      ∀ index, List (PairReductionStackAlphabet computer Δ index))
    (reducedReverse : List Γ₁)
    (output value : List (Sum Γ₁ Δ)) :
    Function.update
        (pairOutputStacks computer workingContents reducedReverse output)
        (Sum.inr .output) value =
      pairOutputStacks computer workingContents reducedReverse value := by
  funext index
  cases index with
  | inl workingIndex => simp [pairOutputStacks]
  | inr extraIndex =>
      cases extraIndex with
      | reducedReverse =>
          have h :
              (Sum.inr PairOutputExtraStackIndex.reducedReverse :
                PairOutputStackIndex computer) ≠
                Sum.inr PairOutputExtraStackIndex.output := by
            intro equality
            cases Sum.inr.inj equality
          simp [pairOutputStacks, h]
      | output => simp [pairOutputStacks]

/-- Four two-step loops first copy the certificate, then prepend the reduced
output. The symbol-carrying labels keep the program total without requiring an
arbitrary inhabitant of either output alphabet. -/
inductive PairOutputTransferLabel (Γ₁ Δ : Type)
  | certificateReverseScan
  | certificateReversePush (symbol : Option (Sum Γ₁ Δ))
  | certificateFillScan
  | certificateFillPush (symbol : Option (Sum Γ₁ Δ))
  | reducedReverseScan
  | reducedReversePush (symbol : Option (Sum Γ₁ Δ))
  | reducedFillScan
  | reducedFillPush (symbol : Option (Sum Γ₁ Δ))
  | done
  deriving DecidableEq, Fintype

/-- Explicit configuration for standalone output/certificate reassembly. -/
def pairOutputTransferCfg {Γ₀ Γ₁ Δ : Type}
    (computer : TM2ComputableAux Γ₀ Γ₁)
    (label : PairOutputTransferLabel Γ₁ Δ)
    (state : Option (Sum Γ₁ Δ))
    (source : List (Sum Γ₀ Δ)) (leftReverse leftOrdered : List Γ₀)
    (rightReverse rightOrdered : List Δ)
    (machineContents : ∀ index, List (computer.tm.Γ index))
    (reducedReverse : List Γ₁) (output : List (Sum Γ₁ Δ)) :
    TM2.Cfg (PairOutputStackAlphabet computer Δ)
      (PairOutputTransferLabel Γ₁ Δ) (Option (Sum Γ₁ Δ)) where
  l := some label
  var := state
  stk := pairOutputStacks computer
    (pairReductionStacks computer
      (pairAdapterStacks source leftReverse leftOrdered rightReverse
        rightOrdered) machineContents)
    reducedReverse output

/-- Standalone output-reassembly program. It copies the preserved certificate
in canonical order, reverses the private reduction output through a fresh
scratch stack, and prepends the canonical tagged reduction output. -/
def pairOutputTransferProgram {Γ₀ Γ₁ Δ : Type}
    (computer : TM2ComputableAux Γ₀ Γ₁) :
    PairOutputTransferLabel Γ₁ Δ →
      TM2.Stmt (PairOutputStackAlphabet computer Δ)
        (PairOutputTransferLabel Γ₁ Δ) (Option (Sum Γ₁ Δ))
  | .certificateReverseScan =>
      .pop (Sum.inl (Sum.inl .rightOrdered))
        (fun _ symbol => symbol.map Sum.inr)
        (.goto (fun symbol => .certificateReversePush symbol))
  | .certificateReversePush none =>
      .goto (fun _ => .certificateFillScan)
  | .certificateReversePush (some (Sum.inr symbol)) =>
      .push (Sum.inl (Sum.inl .rightReverse)) (fun _ => symbol)
        (.goto (fun _ => .certificateReverseScan))
  | .certificateReversePush (some (Sum.inl _)) =>
      .goto (fun _ => .certificateFillScan)
  | .certificateFillScan =>
      .pop (Sum.inl (Sum.inl .rightReverse))
        (fun _ symbol => symbol.map Sum.inr)
        (.goto (fun symbol => .certificateFillPush symbol))
  | .certificateFillPush none =>
      .goto (fun _ => .reducedReverseScan)
  | .certificateFillPush (some (Sum.inr symbol)) =>
      .push (Sum.inr .output) (fun _ => Sum.inr symbol)
        (.goto (fun _ => .certificateFillScan))
  | .certificateFillPush (some (Sum.inl _)) =>
      .goto (fun _ => .reducedReverseScan)
  | .reducedReverseScan =>
      .pop (Sum.inl (Sum.inr computer.tm.k₁))
        (fun _ symbol => symbol.map (fun privateSymbol =>
          Sum.inl (computer.outputAlphabet privateSymbol)))
        (.goto (fun symbol => .reducedReversePush symbol))
  | .reducedReversePush none =>
      .goto (fun _ => .reducedFillScan)
  | .reducedReversePush (some (Sum.inl symbol)) =>
      .push (Sum.inr .reducedReverse) (fun _ => symbol)
        (.goto (fun _ => .reducedReverseScan))
  | .reducedReversePush (some (Sum.inr _)) =>
      .goto (fun _ => .reducedFillScan)
  | .reducedFillScan =>
      .pop (Sum.inr .reducedReverse)
        (fun _ symbol => symbol.map Sum.inl)
        (.goto (fun symbol => .reducedFillPush symbol))
  | .reducedFillPush none => .goto (fun _ => .done)
  | .reducedFillPush (some (Sum.inl symbol)) =>
      .push (Sum.inr .output) (fun _ => Sum.inl symbol)
        (.goto (fun _ => .reducedFillScan))
  | .reducedFillPush (some (Sum.inr _)) => .goto (fun _ => .done)
  | .done => .halt

theorem pairOutputTransfer_certificateReverse_iteration_nonempty
    {Γ₀ Γ₁ Δ : Type} (computer : TM2ComputableAux Γ₀ Γ₁)
    (state : Option (Sum Γ₁ Δ))
    (source : List (Sum Γ₀ Δ)) (leftReverse leftOrdered : List Γ₀)
    (rightReverse : List Δ) (head : Δ) (tail : List Δ)
    (machineContents : ∀ index, List (computer.tm.Γ index))
    (reducedReverse : List Γ₁) (output : List (Sum Γ₁ Δ)) :
    (TM2.step (pairOutputTransferProgram computer)
        (pairOutputTransferCfg computer .certificateReverseScan state source
          leftReverse leftOrdered rightReverse (head :: tail) machineContents
          reducedReverse output)).bind
        (TM2.step (pairOutputTransferProgram computer)) =
      some (pairOutputTransferCfg computer .certificateReverseScan
        (some (Sum.inr head)) source leftReverse leftOrdered
        (head :: rightReverse) tail machineContents reducedReverse output) := by
  simp only [TM2.step, pairOutputTransferProgram, TM2.stepAux,
    pairOutputTransferCfg, pairOutputStacks_working,
    pairReductionStacks_adapter, pairAdapterStacks_rightOrdered]
  rw [pairOutputStacks_working_update,
    ← pairReductionStacks_adapter_update,
    pairAdapterStacks_rightOrdered_update]
  simp only [List.head?_cons, List.tail_cons, Option.map_some,
    Option.bind_some]
  simp only [TM2.stepAux, pairOutputStacks_working,
    pairReductionStacks_adapter, pairAdapterStacks_rightReverse]
  rw [pairOutputStacks_working_update,
    ← pairReductionStacks_adapter_update,
    pairAdapterStacks_rightReverse_update]

theorem pairOutputTransfer_certificateReverse_iteration_empty
    {Γ₀ Γ₁ Δ : Type} (computer : TM2ComputableAux Γ₀ Γ₁)
    (state : Option (Sum Γ₁ Δ))
    (source : List (Sum Γ₀ Δ)) (leftReverse leftOrdered : List Γ₀)
    (rightReverse : List Δ)
    (machineContents : ∀ index, List (computer.tm.Γ index))
    (reducedReverse : List Γ₁) (output : List (Sum Γ₁ Δ)) :
    (TM2.step (pairOutputTransferProgram computer)
        (pairOutputTransferCfg computer .certificateReverseScan state source
          leftReverse leftOrdered rightReverse [] machineContents
          reducedReverse output)).bind
        (TM2.step (pairOutputTransferProgram computer)) =
      some (pairOutputTransferCfg computer .certificateFillScan none source
        leftReverse leftOrdered rightReverse [] machineContents
        reducedReverse output) := by
  simp only [TM2.step, pairOutputTransferProgram, TM2.stepAux,
    pairOutputTransferCfg, pairOutputStacks_working,
    pairReductionStacks_adapter, pairAdapterStacks_rightOrdered]
  rw [pairOutputStacks_working_update,
    ← pairReductionStacks_adapter_update,
    pairAdapterStacks_rightOrdered_update]
  rfl

/-- Reverse the preserved ordered certificate onto its reusable scratch stack
in exactly two steps per symbol plus two exhaustion steps. -/
theorem pairOutputTransfer_certificateReverse_whole_list
    {Γ₀ Γ₁ Δ : Type} (computer : TM2ComputableAux Γ₀ Γ₁)
    (state : Option (Sum Γ₁ Δ))
    (source : List (Sum Γ₀ Δ)) (leftReverse leftOrdered : List Γ₀)
    (rightReverse certificate : List Δ)
    (machineContents : ∀ index, List (computer.tm.Γ index))
    (reducedReverse : List Γ₁) (output : List (Sum Γ₁ Δ)) :
    (flip Option.bind (TM2.step (pairOutputTransferProgram computer)))^[
        2 * certificate.length + 2]
      (some (pairOutputTransferCfg computer .certificateReverseScan state
        source leftReverse leftOrdered rightReverse certificate machineContents
        reducedReverse output)) =
      some (pairOutputTransferCfg computer .certificateFillScan none source
        leftReverse leftOrdered (certificate.reverse ++ rightReverse) []
        machineContents reducedReverse output) := by
  induction certificate generalizing state rightReverse with
  | nil =>
      simpa [Function.iterate_succ_apply'] using
        pairOutputTransfer_certificateReverse_iteration_empty computer state
          source leftReverse leftOrdered rightReverse machineContents
          reducedReverse output
  | cons head tail ih =>
      have firstIteration :=
        pairOutputTransfer_certificateReverse_iteration_nonempty computer state
          source leftReverse leftOrdered rightReverse head tail machineContents
          reducedReverse output
      rw [List.length_cons]
      have stepCount : 2 * (tail.length + 1) + 2 =
          (2 * tail.length + 2) + 2 := by omega
      rw [stepCount, Function.iterate_add_apply]
      rw [show
        (flip Option.bind (TM2.step (pairOutputTransferProgram computer)))^[2]
            (some (pairOutputTransferCfg computer .certificateReverseScan state
              source leftReverse leftOrdered rightReverse (head :: tail)
              machineContents reducedReverse output)) =
          some (pairOutputTransferCfg computer .certificateReverseScan
            (some (Sum.inr head)) source leftReverse leftOrdered
            (head :: rightReverse) tail machineContents reducedReverse output) by
        simpa [Function.iterate_succ_apply'] using firstIteration]
      simpa [List.reverse_cons, List.append_assoc] using
        ih (some (Sum.inr head)) (head :: rightReverse)

theorem pairOutputTransfer_certificateFill_iteration_nonempty
    {Γ₀ Γ₁ Δ : Type} (computer : TM2ComputableAux Γ₀ Γ₁)
    (state : Option (Sum Γ₁ Δ))
    (source : List (Sum Γ₀ Δ)) (leftReverse leftOrdered : List Γ₀)
    (head : Δ) (tail rightOrdered : List Δ)
    (machineContents : ∀ index, List (computer.tm.Γ index))
    (reducedReverse : List Γ₁) (output : List (Sum Γ₁ Δ)) :
    (TM2.step (pairOutputTransferProgram computer)
        (pairOutputTransferCfg computer .certificateFillScan state source
          leftReverse leftOrdered (head :: tail) rightOrdered machineContents
          reducedReverse output)).bind
        (TM2.step (pairOutputTransferProgram computer)) =
      some (pairOutputTransferCfg computer .certificateFillScan
        (some (Sum.inr head)) source leftReverse leftOrdered tail rightOrdered
        machineContents reducedReverse (Sum.inr head :: output)) := by
  simp only [TM2.step, pairOutputTransferProgram, TM2.stepAux,
    pairOutputTransferCfg, pairOutputStacks_working,
    pairReductionStacks_adapter, pairAdapterStacks_rightReverse]
  rw [pairOutputStacks_working_update,
    ← pairReductionStacks_adapter_update,
    pairAdapterStacks_rightReverse_update]
  simp only [List.head?_cons, List.tail_cons, Option.map_some,
    Option.bind_some]
  simp only [TM2.stepAux, pairOutputStacks_output]
  rw [pairOutputStacks_output_update]

theorem pairOutputTransfer_certificateFill_iteration_empty
    {Γ₀ Γ₁ Δ : Type} (computer : TM2ComputableAux Γ₀ Γ₁)
    (state : Option (Sum Γ₁ Δ))
    (source : List (Sum Γ₀ Δ)) (leftReverse leftOrdered : List Γ₀)
    (rightOrdered : List Δ)
    (machineContents : ∀ index, List (computer.tm.Γ index))
    (reducedReverse : List Γ₁) (output : List (Sum Γ₁ Δ)) :
    (TM2.step (pairOutputTransferProgram computer)
        (pairOutputTransferCfg computer .certificateFillScan state source
          leftReverse leftOrdered [] rightOrdered machineContents
          reducedReverse output)).bind
        (TM2.step (pairOutputTransferProgram computer)) =
      some (pairOutputTransferCfg computer .reducedReverseScan none source
        leftReverse leftOrdered [] rightOrdered machineContents
        reducedReverse output) := by
  simp only [TM2.step, pairOutputTransferProgram, TM2.stepAux,
    pairOutputTransferCfg, pairOutputStacks_working,
    pairReductionStacks_adapter, pairAdapterStacks_rightReverse]
  rw [pairOutputStacks_working_update,
    ← pairReductionStacks_adapter_update,
    pairAdapterStacks_rightReverse_update]
  rfl

/-- Copy the reversed certificate into the tagged output stack, restoring its
canonical order, in exactly two steps per symbol plus two exhaustion steps. -/
theorem pairOutputTransfer_certificateFill_whole_list
    {Γ₀ Γ₁ Δ : Type} (computer : TM2ComputableAux Γ₀ Γ₁)
    (state : Option (Sum Γ₁ Δ))
    (source : List (Sum Γ₀ Δ)) (leftReverse leftOrdered : List Γ₀)
    (certificateScratch rightOrdered : List Δ)
    (machineContents : ∀ index, List (computer.tm.Γ index))
    (reducedReverse : List Γ₁) (output : List (Sum Γ₁ Δ)) :
    (flip Option.bind (TM2.step (pairOutputTransferProgram computer)))^[
        2 * certificateScratch.length + 2]
      (some (pairOutputTransferCfg computer .certificateFillScan state source
        leftReverse leftOrdered certificateScratch rightOrdered machineContents
        reducedReverse output)) =
      some (pairOutputTransferCfg computer .reducedReverseScan none source
        leftReverse leftOrdered [] rightOrdered machineContents reducedReverse
        ((certificateScratch.map (Sum.inr : Δ → Sum Γ₁ Δ)).reverse ++
          output)) := by
  induction certificateScratch generalizing state output with
  | nil =>
      simpa [Function.iterate_succ_apply'] using
        pairOutputTransfer_certificateFill_iteration_empty computer state
          source leftReverse leftOrdered rightOrdered machineContents
          reducedReverse output
  | cons head tail ih =>
      have firstIteration :=
        pairOutputTransfer_certificateFill_iteration_nonempty computer state
          source leftReverse leftOrdered head tail rightOrdered machineContents
          reducedReverse output
      rw [List.length_cons]
      have stepCount : 2 * (tail.length + 1) + 2 =
          (2 * tail.length + 2) + 2 := by omega
      rw [stepCount, Function.iterate_add_apply]
      rw [show
        (flip Option.bind (TM2.step (pairOutputTransferProgram computer)))^[2]
            (some (pairOutputTransferCfg computer .certificateFillScan state
              source leftReverse leftOrdered (head :: tail) rightOrdered
              machineContents reducedReverse output)) =
          some (pairOutputTransferCfg computer .certificateFillScan
            (some (Sum.inr head)) source leftReverse leftOrdered tail
            rightOrdered machineContents reducedReverse
            (Sum.inr head :: output)) by
        simpa [Function.iterate_succ_apply'] using firstIteration]
      simpa [List.map, List.reverse_cons, List.append_assoc] using
        ih (some (Sum.inr head)) (Sum.inr head :: output)

theorem pairOutputTransfer_reducedReverse_iteration_nonempty
    {Γ₀ Γ₁ Δ : Type} (computer : TM2ComputableAux Γ₀ Γ₁)
    (state : Option (Sum Γ₁ Δ))
    (source : List (Sum Γ₀ Δ)) (leftReverse leftOrdered : List Γ₀)
    (rightReverse rightOrdered : List Δ)
    (head : computer.tm.Γ computer.tm.k₁)
    (tail : List (computer.tm.Γ computer.tm.k₁))
    (machineContents : ∀ index, List (computer.tm.Γ index))
    (reducedReverse : List Γ₁) (output : List (Sum Γ₁ Δ)) :
    (TM2.step (pairOutputTransferProgram computer)
        (pairOutputTransferCfg computer .reducedReverseScan state source
          leftReverse leftOrdered rightReverse rightOrdered
          (Function.update machineContents computer.tm.k₁ (head :: tail))
          reducedReverse output)).bind
        (TM2.step (pairOutputTransferProgram computer)) =
      some (pairOutputTransferCfg computer .reducedReverseScan
        (some (Sum.inl (computer.outputAlphabet head))) source leftReverse
        leftOrdered rightReverse rightOrdered
        (Function.update machineContents computer.tm.k₁ tail)
        (computer.outputAlphabet head :: reducedReverse) output) := by
  simp only [TM2.step, pairOutputTransferProgram, TM2.stepAux,
    pairOutputTransferCfg, pairOutputStacks_working,
    pairReductionStacks_machine, Function.update_self]
  rw [pairOutputStacks_working_update,
    ← pairReductionStacks_machine_update]
  simp only [Function.update_idem, List.head?_cons, List.tail_cons,
    Option.map_some, Option.bind_some]
  simp only [TM2.stepAux, pairOutputStacks_reducedReverse]
  rw [pairOutputStacks_reducedReverse_update]

theorem pairOutputTransfer_reducedReverse_iteration_empty
    {Γ₀ Γ₁ Δ : Type} (computer : TM2ComputableAux Γ₀ Γ₁)
    (state : Option (Sum Γ₁ Δ))
    (source : List (Sum Γ₀ Δ)) (leftReverse leftOrdered : List Γ₀)
    (rightReverse rightOrdered : List Δ)
    (machineContents : ∀ index, List (computer.tm.Γ index))
    (reducedReverse : List Γ₁) (output : List (Sum Γ₁ Δ)) :
    (TM2.step (pairOutputTransferProgram computer)
        (pairOutputTransferCfg computer .reducedReverseScan state source
          leftReverse leftOrdered rightReverse rightOrdered
          (Function.update machineContents computer.tm.k₁ [])
          reducedReverse output)).bind
        (TM2.step (pairOutputTransferProgram computer)) =
      some (pairOutputTransferCfg computer .reducedFillScan none source
        leftReverse leftOrdered rightReverse rightOrdered
        (Function.update machineContents computer.tm.k₁ [])
        reducedReverse output) := by
  simp only [TM2.step, pairOutputTransferProgram, TM2.stepAux,
    pairOutputTransferCfg, pairOutputStacks_working,
    pairReductionStacks_machine, Function.update_self]
  rw [pairOutputStacks_working_update,
    ← pairReductionStacks_machine_update]
  simp only [Function.update_idem, List.head?_nil, List.tail_nil,
    Option.map_none, Option.bind_some]
  rfl

/-- Empty the private reduction output and reverse its canonical image onto
the new scratch stack in exactly two steps per symbol plus two exhaustion
steps. -/
theorem pairOutputTransfer_reducedReverse_whole_list
    {Γ₀ Γ₁ Δ : Type} (computer : TM2ComputableAux Γ₀ Γ₁)
    (state : Option (Sum Γ₁ Δ))
    (source : List (Sum Γ₀ Δ)) (leftReverse leftOrdered : List Γ₀)
    (rightReverse rightOrdered : List Δ)
    (privateOutput : List (computer.tm.Γ computer.tm.k₁))
    (machineContents : ∀ index, List (computer.tm.Γ index))
    (reducedReverse : List Γ₁) (output : List (Sum Γ₁ Δ)) :
    (flip Option.bind (TM2.step (pairOutputTransferProgram computer)))^[
        2 * privateOutput.length + 2]
      (some (pairOutputTransferCfg computer .reducedReverseScan state source
        leftReverse leftOrdered rightReverse rightOrdered
        (Function.update machineContents computer.tm.k₁ privateOutput)
        reducedReverse output)) =
      some (pairOutputTransferCfg computer .reducedFillScan none source
        leftReverse leftOrdered rightReverse rightOrdered
        (Function.update machineContents computer.tm.k₁ [])
        ((privateOutput.map computer.outputAlphabet).reverse ++
          reducedReverse) output) := by
  induction privateOutput generalizing state reducedReverse with
  | nil =>
      simpa [Function.iterate_succ_apply'] using
        pairOutputTransfer_reducedReverse_iteration_empty computer state source
          leftReverse leftOrdered rightReverse rightOrdered machineContents
          reducedReverse output
  | cons head tail ih =>
      have firstIteration :=
        pairOutputTransfer_reducedReverse_iteration_nonempty computer state
          source leftReverse leftOrdered rightReverse rightOrdered head tail
          machineContents reducedReverse output
      rw [List.length_cons]
      have stepCount : 2 * (tail.length + 1) + 2 =
          (2 * tail.length + 2) + 2 := by omega
      rw [stepCount, Function.iterate_add_apply]
      rw [show
        (flip Option.bind (TM2.step (pairOutputTransferProgram computer)))^[2]
            (some (pairOutputTransferCfg computer .reducedReverseScan state
              source leftReverse leftOrdered rightReverse rightOrdered
              (Function.update machineContents computer.tm.k₁ (head :: tail))
              reducedReverse output)) =
          some (pairOutputTransferCfg computer .reducedReverseScan
            (some (Sum.inl (computer.outputAlphabet head))) source leftReverse
            leftOrdered rightReverse rightOrdered
            (Function.update machineContents computer.tm.k₁ tail)
            (computer.outputAlphabet head :: reducedReverse) output) by
        simpa [Function.iterate_succ_apply'] using firstIteration]
      simpa [List.map, List.reverse_cons, List.append_assoc] using
        ih (some (Sum.inl (computer.outputAlphabet head)))
          (computer.outputAlphabet head :: reducedReverse)

theorem pairOutputTransfer_reducedFill_iteration_nonempty
    {Γ₀ Γ₁ Δ : Type} (computer : TM2ComputableAux Γ₀ Γ₁)
    (state : Option (Sum Γ₁ Δ))
    (source : List (Sum Γ₀ Δ)) (leftReverse leftOrdered : List Γ₀)
    (rightReverse rightOrdered : List Δ)
    (head : Γ₁) (tail : List Γ₁)
    (machineContents : ∀ index, List (computer.tm.Γ index))
    (output : List (Sum Γ₁ Δ)) :
    (TM2.step (pairOutputTransferProgram computer)
        (pairOutputTransferCfg computer .reducedFillScan state source
          leftReverse leftOrdered rightReverse rightOrdered machineContents
          (head :: tail) output)).bind
        (TM2.step (pairOutputTransferProgram computer)) =
      some (pairOutputTransferCfg computer .reducedFillScan
        (some (Sum.inl head)) source leftReverse leftOrdered rightReverse
        rightOrdered machineContents tail (Sum.inl head :: output)) := by
  simp only [TM2.step, pairOutputTransferProgram, TM2.stepAux,
    pairOutputTransferCfg, pairOutputStacks_reducedReverse]
  rw [pairOutputStacks_reducedReverse_update]
  simp only [List.head?_cons, List.tail_cons, Option.map_some,
    Option.bind_some]
  simp only [TM2.stepAux, pairOutputStacks_output]
  rw [pairOutputStacks_output_update]

theorem pairOutputTransfer_reducedFill_iteration_empty
    {Γ₀ Γ₁ Δ : Type} (computer : TM2ComputableAux Γ₀ Γ₁)
    (state : Option (Sum Γ₁ Δ))
    (source : List (Sum Γ₀ Δ)) (leftReverse leftOrdered : List Γ₀)
    (rightReverse rightOrdered : List Δ)
    (machineContents : ∀ index, List (computer.tm.Γ index))
    (output : List (Sum Γ₁ Δ)) :
    (TM2.step (pairOutputTransferProgram computer)
        (pairOutputTransferCfg computer .reducedFillScan state source
          leftReverse leftOrdered rightReverse rightOrdered machineContents []
          output)).bind
        (TM2.step (pairOutputTransferProgram computer)) =
      some (pairOutputTransferCfg computer .done none source leftReverse
        leftOrdered rightReverse rightOrdered machineContents [] output) := by
  simp only [TM2.step, pairOutputTransferProgram, TM2.stepAux,
    pairOutputTransferCfg, pairOutputStacks_reducedReverse]
  rw [pairOutputStacks_reducedReverse_update]
  rfl

/-- Copy the reversed reduced output into the tagged result stack, restoring
canonical order, in exactly two steps per symbol plus two exhaustion steps. -/
theorem pairOutputTransfer_reducedFill_whole_list
    {Γ₀ Γ₁ Δ : Type} (computer : TM2ComputableAux Γ₀ Γ₁)
    (state : Option (Sum Γ₁ Δ))
    (source : List (Sum Γ₀ Δ)) (leftReverse leftOrdered : List Γ₀)
    (rightReverse rightOrdered : List Δ)
    (reducedScratch : List Γ₁)
    (machineContents : ∀ index, List (computer.tm.Γ index))
    (output : List (Sum Γ₁ Δ)) :
    (flip Option.bind (TM2.step (pairOutputTransferProgram computer)))^[
        2 * reducedScratch.length + 2]
      (some (pairOutputTransferCfg computer .reducedFillScan state source
        leftReverse leftOrdered rightReverse rightOrdered machineContents
        reducedScratch output)) =
      some (pairOutputTransferCfg computer .done none source leftReverse
        leftOrdered rightReverse rightOrdered machineContents []
        ((reducedScratch.map (Sum.inl : Γ₁ → Sum Γ₁ Δ)).reverse ++
          output)) := by
  induction reducedScratch generalizing state output with
  | nil =>
      simpa [Function.iterate_succ_apply'] using
        pairOutputTransfer_reducedFill_iteration_empty computer state source
          leftReverse leftOrdered rightReverse rightOrdered machineContents
          output
  | cons head tail ih =>
      have firstIteration :=
        pairOutputTransfer_reducedFill_iteration_nonempty computer state source
          leftReverse leftOrdered rightReverse rightOrdered head tail
          machineContents output
      rw [List.length_cons]
      have stepCount : 2 * (tail.length + 1) + 2 =
          (2 * tail.length + 2) + 2 := by omega
      rw [stepCount, Function.iterate_add_apply]
      rw [show
        (flip Option.bind (TM2.step (pairOutputTransferProgram computer)))^[2]
            (some (pairOutputTransferCfg computer .reducedFillScan state
              source leftReverse leftOrdered rightReverse rightOrdered
              machineContents (head :: tail) output)) =
          some (pairOutputTransferCfg computer .reducedFillScan
            (some (Sum.inl head)) source leftReverse leftOrdered rightReverse
            rightOrdered machineContents tail (Sum.inl head :: output)) by
        simpa [Function.iterate_succ_apply'] using firstIteration]
      simpa [List.map, List.reverse_cons, List.append_assoc] using
        ih (some (Sum.inl head)) (Sum.inl head :: output)

/-- Complete standalone output reassembly. Starting from a halted reduction
output and the preserved ordered certificate, the program empties both source
stacks and constructs the canonical tagged pair encoding in exactly four
steps per reduced-output symbol, four per certificate symbol, and eight fixed
exhaustion steps. -/
theorem pairOutputTransfer_whole_list
    {Γ₀ Γ₁ Δ : Type} (computer : TM2ComputableAux Γ₀ Γ₁)
    (source : List (Sum Γ₀ Δ)) (leftReverse leftOrdered : List Γ₀)
    (certificate : List Δ)
    (privateOutput : List (computer.tm.Γ computer.tm.k₁))
    (machineContents : ∀ index, List (computer.tm.Γ index)) :
    (flip Option.bind (TM2.step (pairOutputTransferProgram computer)))^[
        4 * privateOutput.length + 4 * certificate.length + 8]
      (some (pairOutputTransferCfg computer .certificateReverseScan none source
        leftReverse leftOrdered [] certificate
        (Function.update machineContents computer.tm.k₁ privateOutput) [] [])) =
      some (pairOutputTransferCfg computer .done none source leftReverse
        leftOrdered [] [] (Function.update machineContents computer.tm.k₁ [])
        []
        ((privateOutput.map computer.outputAlphabet).map
            (Sum.inl : Γ₁ → Sum Γ₁ Δ) ++
          certificate.map (Sum.inr : Δ → Sum Γ₁ Δ))) := by
  have certificateReverseRun :=
    pairOutputTransfer_certificateReverse_whole_list computer none source
      leftReverse leftOrdered [] certificate
      (Function.update machineContents computer.tm.k₁ privateOutput) [] []
  have certificateFillRun :=
    pairOutputTransfer_certificateFill_whole_list computer none source
      leftReverse leftOrdered certificate.reverse []
      (Function.update machineContents computer.tm.k₁ privateOutput) [] []
  have reducedReverseRun :=
    pairOutputTransfer_reducedReverse_whole_list computer none source
      leftReverse leftOrdered [] [] privateOutput machineContents []
      (certificate.map (Sum.inr : Δ → Sum Γ₁ Δ))
  have reducedFillRun :=
    pairOutputTransfer_reducedFill_whole_list computer none source leftReverse
      leftOrdered [] [] (privateOutput.map computer.outputAlphabet).reverse
      (Function.update machineContents computer.tm.k₁ [])
      (certificate.map (Sum.inr : Δ → Sum Γ₁ Δ))
  have stepCount :
      4 * privateOutput.length + 4 * certificate.length + 8 =
        (2 * (privateOutput.map computer.outputAlphabet).reverse.length + 2) +
          ((2 * privateOutput.length + 2) +
            ((2 * certificate.reverse.length + 2) +
              (2 * certificate.length + 2))) := by
    simp
    omega
  rw [stepCount]
  rw [Function.iterate_add_apply
    (flip Option.bind (TM2.step (pairOutputTransferProgram computer)))
    (2 * (privateOutput.map computer.outputAlphabet).reverse.length + 2)
    ((2 * privateOutput.length + 2) +
      ((2 * certificate.reverse.length + 2) +
        (2 * certificate.length + 2)))]
  rw [Function.iterate_add_apply
    (flip Option.bind (TM2.step (pairOutputTransferProgram computer)))
    (2 * privateOutput.length + 2)
    ((2 * certificate.reverse.length + 2) +
      (2 * certificate.length + 2))]
  rw [Function.iterate_add_apply
    (flip Option.bind (TM2.step (pairOutputTransferProgram computer)))
    (2 * certificate.reverse.length + 2)
    (2 * certificate.length + 2)]
  rw [certificateReverseRun]
  have certificateFillRun' :
      (flip Option.bind (TM2.step (pairOutputTransferProgram computer)))^[
          2 * certificate.reverse.length + 2]
        (some (pairOutputTransferCfg computer .certificateFillScan none source
          leftReverse leftOrdered (certificate.reverse ++ []) []
          (Function.update machineContents computer.tm.k₁ privateOutput)
          [] [])) =
        some (pairOutputTransferCfg computer .reducedReverseScan none source
          leftReverse leftOrdered [] []
          (Function.update machineContents computer.tm.k₁ privateOutput) []
          (certificate.map (Sum.inr : Δ → Sum Γ₁ Δ))) := by
    simpa [List.map_reverse] using certificateFillRun
  rw [certificateFillRun']
  rw [reducedReverseRun]
  have reducedFillRun' :
      (flip Option.bind (TM2.step (pairOutputTransferProgram computer)))^[
          2 * (privateOutput.map computer.outputAlphabet).reverse.length + 2]
        (some (pairOutputTransferCfg computer .reducedFillScan none source
          leftReverse leftOrdered [] []
          (Function.update machineContents computer.tm.k₁ [])
          ((privateOutput.map computer.outputAlphabet).reverse ++ [])
          (certificate.map (Sum.inr : Δ → Sum Γ₁ Δ)))) =
        some (pairOutputTransferCfg computer .done none source leftReverse
          leftOrdered [] []
          (Function.update machineContents computer.tm.k₁ []) []
          ((privateOutput.map computer.outputAlphabet).map
              (Sum.inl : Γ₁ → Sum Γ₁ Δ) ++
            certificate.map (Sum.inr : Δ → Sum Γ₁ Δ))) := by
    simpa [List.map_reverse, List.map_map] using reducedFillRun
  exact reducedFillRun'

end LeanNPHardness.MachineAdapters
