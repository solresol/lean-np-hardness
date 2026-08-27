import LeanNPHardness.PairMachine

namespace LeanNPHardness.MachineAdapters

open Turing

/-- The shared five-stack layout for the preprocessing part of a pair-left
machine adapter. The tagged source is classified onto two reverse stacks,
then restored onto two ordered component stacks. -/
inductive PairAdapterStackIndex
  | source
  | leftReverse
  | leftOrdered
  | rightReverse
  | rightOrdered
  deriving DecidableEq, Fintype

/-- The dependent alphabets of the shared pair-adapter stack layout. -/
def PairAdapterStackAlphabet (Γ Δ : Type) : PairAdapterStackIndex → Type
  | .source => Sum Γ Δ
  | .leftReverse => Γ
  | .leftOrdered => Γ
  | .rightReverse => Δ
  | .rightOrdered => Δ

/-- Finite phase-tagged control for classification followed by restoration. -/
inductive PairAdapterLabel (Γ Δ : Type)
  | split (action : PairSplitAction Γ Δ)
  | restore (action : PairRestoreAction Γ Δ)
  deriving DecidableEq, Fintype

/-- Explicit contents of all five preprocessing stacks. -/
def pairAdapterStacks {Γ Δ : Type}
    (source : List (Sum Γ Δ)) (leftReverse leftOrdered : List Γ)
    (rightReverse rightOrdered : List Δ) :
    ∀ index, List (PairAdapterStackAlphabet Γ Δ index)
  | .source => source
  | .leftReverse => leftReverse
  | .leftOrdered => leftOrdered
  | .rightReverse => rightReverse
  | .rightOrdered => rightOrdered

@[simp]
theorem pairAdapterStacks_source {Γ Δ : Type}
    (source : List (Sum Γ Δ)) (leftReverse leftOrdered : List Γ)
    (rightReverse rightOrdered : List Δ) :
    pairAdapterStacks source leftReverse leftOrdered rightReverse rightOrdered
        .source = source :=
  rfl

@[simp]
theorem pairAdapterStacks_leftReverse {Γ Δ : Type}
    (source : List (Sum Γ Δ)) (leftReverse leftOrdered : List Γ)
    (rightReverse rightOrdered : List Δ) :
    pairAdapterStacks source leftReverse leftOrdered rightReverse rightOrdered
        .leftReverse = leftReverse :=
  rfl

@[simp]
theorem pairAdapterStacks_leftOrdered {Γ Δ : Type}
    (source : List (Sum Γ Δ)) (leftReverse leftOrdered : List Γ)
    (rightReverse rightOrdered : List Δ) :
    pairAdapterStacks source leftReverse leftOrdered rightReverse rightOrdered
        .leftOrdered = leftOrdered :=
  rfl

@[simp]
theorem pairAdapterStacks_rightReverse {Γ Δ : Type}
    (source : List (Sum Γ Δ)) (leftReverse leftOrdered : List Γ)
    (rightReverse rightOrdered : List Δ) :
    pairAdapterStacks source leftReverse leftOrdered rightReverse rightOrdered
        .rightReverse = rightReverse :=
  rfl

@[simp]
theorem pairAdapterStacks_rightOrdered {Γ Δ : Type}
    (source : List (Sum Γ Δ)) (leftReverse leftOrdered : List Γ)
    (rightReverse rightOrdered : List Δ) :
    pairAdapterStacks source leftReverse leftOrdered rightReverse rightOrdered
        .rightOrdered = rightOrdered :=
  rfl

theorem pairAdapterStacks_source_update {Γ Δ : Type}
    (source value : List (Sum Γ Δ)) (leftReverse leftOrdered : List Γ)
    (rightReverse rightOrdered : List Δ) :
    Function.update
        (pairAdapterStacks source leftReverse leftOrdered rightReverse
          rightOrdered)
        PairAdapterStackIndex.source value =
      pairAdapterStacks value leftReverse leftOrdered rightReverse
        rightOrdered := by
  funext index
  cases index <;> simp [pairAdapterStacks]

theorem pairAdapterStacks_leftReverse_update {Γ Δ : Type}
    (source : List (Sum Γ Δ)) (leftReverse value leftOrdered : List Γ)
    (rightReverse rightOrdered : List Δ) :
    Function.update
        (pairAdapterStacks source leftReverse leftOrdered rightReverse
          rightOrdered)
        PairAdapterStackIndex.leftReverse value =
      pairAdapterStacks source value leftOrdered rightReverse rightOrdered := by
  funext index
  cases index <;> simp [pairAdapterStacks]

theorem pairAdapterStacks_leftOrdered_update {Γ Δ : Type}
    (source : List (Sum Γ Δ)) (leftReverse leftOrdered value : List Γ)
    (rightReverse rightOrdered : List Δ) :
    Function.update
        (pairAdapterStacks source leftReverse leftOrdered rightReverse
          rightOrdered)
        PairAdapterStackIndex.leftOrdered value =
      pairAdapterStacks source leftReverse value rightReverse rightOrdered := by
  funext index
  cases index <;> simp [pairAdapterStacks]

theorem pairAdapterStacks_rightReverse_update {Γ Δ : Type}
    (source : List (Sum Γ Δ)) (leftReverse leftOrdered : List Γ)
    (rightReverse value rightOrdered : List Δ) :
    Function.update
        (pairAdapterStacks source leftReverse leftOrdered rightReverse
          rightOrdered)
        PairAdapterStackIndex.rightReverse value =
      pairAdapterStacks source leftReverse leftOrdered value rightOrdered := by
  funext index
  cases index <;> simp [pairAdapterStacks]

theorem pairAdapterStacks_rightOrdered_update {Γ Δ : Type}
    (source : List (Sum Γ Δ)) (leftReverse leftOrdered : List Γ)
    (rightReverse rightOrdered value : List Δ) :
    Function.update
        (pairAdapterStacks source leftReverse leftOrdered rightReverse
          rightOrdered)
        PairAdapterStackIndex.rightOrdered value =
      pairAdapterStacks source leftReverse leftOrdered rightReverse value := by
  funext index
  cases index <;> simp [pairAdapterStacks]

/-- A configuration of the integrated classification/restoration program. -/
def pairAdapterCfg {Γ Δ : Type} (label : PairAdapterLabel Γ Δ)
    (state : Option (Sum Γ Δ)) (source : List (Sum Γ Δ))
    (leftReverse leftOrdered : List Γ)
    (rightReverse rightOrdered : List Δ) :
    TM2.Cfg (PairAdapterStackAlphabet Γ Δ) (PairAdapterLabel Γ Δ)
      (Option (Sum Γ Δ)) where
  l := some label
  var := state
  stk := pairAdapterStacks source leftReverse leftOrdered rightReverse
    rightOrdered

/-- Total preprocessing dispatcher. Split labels classify the tagged source,
the split endpoint enters restoration in one step, and restore labels recover
the two canonical component orders. -/
def pairAdapterProgram {Γ Δ : Type} :
    PairAdapterLabel Γ Δ →
      TM2.Stmt (PairAdapterStackAlphabet Γ Δ) (PairAdapterLabel Γ Δ)
        (Option (Sum Γ Δ))
  | .split .scan =>
      .pop .source (fun _ symbol => symbol)
        (.goto (fun symbol => .split (.push symbol)))
  | .split (.push none) => .goto (fun _ => .split .done)
  | .split (.push (some (.inl symbol))) =>
      .push .leftReverse (fun _ => symbol)
        (.goto (fun _ => .split .scan))
  | .split (.push (some (.inr symbol))) =>
      .push .rightReverse (fun _ => symbol)
        (.goto (fun _ => .split .scan))
  | .split .done => .goto (fun _ => .restore .leftScan)
  | .restore .leftScan =>
      .pop .leftReverse (fun _ symbol => symbol.map Sum.inl)
        (.goto (fun symbol => .restore (.leftPush symbol)))
  | .restore (.leftPush none) => .goto (fun _ => .restore .rightScan)
  | .restore (.leftPush (some (.inl symbol))) =>
      .push .leftOrdered (fun _ => symbol)
        (.goto (fun _ => .restore .leftScan))
  | .restore (.leftPush (some (.inr _))) =>
      .goto (fun _ => .restore .rightScan)
  | .restore .rightScan =>
      .pop .rightReverse (fun _ symbol => symbol.map Sum.inr)
        (.goto (fun symbol => .restore (.rightPush symbol)))
  | .restore (.rightPush none) => .goto (fun _ => .restore .done)
  | .restore (.rightPush (some (.inl _))) =>
      .goto (fun _ => .restore .done)
  | .restore (.rightPush (some (.inr symbol))) =>
      .push .rightOrdered (fun _ => symbol)
        (.goto (fun _ => .restore .rightScan))
  | .restore .done => .halt

theorem pairAdapter_split_scan_step_nonempty {Γ Δ : Type}
    (state : Option (Sum Γ Δ)) (head : Sum Γ Δ)
    (tail : List (Sum Γ Δ)) (leftReverse leftOrdered : List Γ)
    (rightReverse rightOrdered : List Δ) :
    TM2.step pairAdapterProgram
        (pairAdapterCfg (.split .scan) state (head :: tail) leftReverse
          leftOrdered rightReverse rightOrdered) =
      some (pairAdapterCfg (.split (.push (some head))) (some head) tail
        leftReverse leftOrdered rightReverse rightOrdered) := by
  simp only [TM2.step, pairAdapterProgram, TM2.stepAux, pairAdapterCfg,
    pairAdapterStacks_source]
  rw [pairAdapterStacks_source_update]
  simp

theorem pairAdapter_split_scan_step_empty {Γ Δ : Type}
    (state : Option (Sum Γ Δ)) (leftReverse leftOrdered : List Γ)
    (rightReverse rightOrdered : List Δ) :
    TM2.step pairAdapterProgram
        (pairAdapterCfg (.split .scan) state [] leftReverse leftOrdered
          rightReverse rightOrdered) =
      some (pairAdapterCfg (.split (.push none)) none [] leftReverse
        leftOrdered rightReverse rightOrdered) := by
  simp only [TM2.step, pairAdapterProgram, TM2.stepAux, pairAdapterCfg,
    pairAdapterStacks_source]
  rw [pairAdapterStacks_source_update]
  simp

theorem pairAdapter_split_push_left_step {Γ Δ : Type} (symbol : Γ)
    (state : Option (Sum Γ Δ)) (source : List (Sum Γ Δ))
    (leftReverse leftOrdered : List Γ)
    (rightReverse rightOrdered : List Δ) :
    TM2.step pairAdapterProgram
        (pairAdapterCfg (.split (.push (some (.inl symbol)))) state source
          leftReverse leftOrdered rightReverse rightOrdered) =
      some (pairAdapterCfg (.split .scan) state source
        (symbol :: leftReverse) leftOrdered rightReverse rightOrdered) := by
  simp only [TM2.step, pairAdapterProgram, TM2.stepAux, pairAdapterCfg,
    pairAdapterStacks_leftReverse]
  rw [pairAdapterStacks_leftReverse_update]

theorem pairAdapter_split_push_right_step {Γ Δ : Type} (symbol : Δ)
    (state : Option (Sum Γ Δ)) (source : List (Sum Γ Δ))
    (leftReverse leftOrdered : List Γ)
    (rightReverse rightOrdered : List Δ) :
    TM2.step pairAdapterProgram
        (pairAdapterCfg (.split (.push (some (.inr symbol)))) state source
          leftReverse leftOrdered rightReverse rightOrdered) =
      some (pairAdapterCfg (.split .scan) state source leftReverse leftOrdered
        (symbol :: rightReverse) rightOrdered) := by
  simp only [TM2.step, pairAdapterProgram, TM2.stepAux, pairAdapterCfg,
    pairAdapterStacks_rightReverse]
  rw [pairAdapterStacks_rightReverse_update]

theorem pairAdapter_split_push_none_step {Γ Δ : Type}
    (state : Option (Sum Γ Δ)) (leftReverse leftOrdered : List Γ)
    (rightReverse rightOrdered : List Δ) :
    TM2.step pairAdapterProgram
        (pairAdapterCfg (.split (.push none)) state [] leftReverse
          leftOrdered rightReverse rightOrdered) =
      some (pairAdapterCfg (.split .done) state [] leftReverse leftOrdered
        rightReverse rightOrdered) :=
  rfl

theorem pairAdapter_split_done_step {Γ Δ : Type}
    (state : Option (Sum Γ Δ)) (leftReverse leftOrdered : List Γ)
    (rightReverse rightOrdered : List Δ) :
    TM2.step pairAdapterProgram
        (pairAdapterCfg (.split .done) state [] leftReverse leftOrdered
          rightReverse rightOrdered) =
      some (pairAdapterCfg (.restore .leftScan) state [] leftReverse
        leftOrdered rightReverse rightOrdered) :=
  rfl

theorem pairAdapter_split_iteration_left {Γ Δ : Type}
    (state : Option (Sum Γ Δ)) (symbol : Γ)
    (tail : List (Sum Γ Δ)) (leftReverse leftOrdered : List Γ)
    (rightReverse rightOrdered : List Δ) :
    (TM2.step pairAdapterProgram
        (pairAdapterCfg (.split .scan) state (Sum.inl symbol :: tail)
          leftReverse leftOrdered rightReverse rightOrdered)).bind
        (TM2.step pairAdapterProgram) =
      some (pairAdapterCfg (.split .scan) (some (.inl symbol)) tail
        (symbol :: leftReverse) leftOrdered rightReverse rightOrdered) := by
  rw [pairAdapter_split_scan_step_nonempty, Option.bind_some,
    pairAdapter_split_push_left_step]

theorem pairAdapter_split_iteration_right {Γ Δ : Type}
    (state : Option (Sum Γ Δ)) (symbol : Δ)
    (tail : List (Sum Γ Δ)) (leftReverse leftOrdered : List Γ)
    (rightReverse rightOrdered : List Δ) :
    (TM2.step pairAdapterProgram
        (pairAdapterCfg (.split .scan) state (Sum.inr symbol :: tail)
          leftReverse leftOrdered rightReverse rightOrdered)).bind
        (TM2.step pairAdapterProgram) =
      some (pairAdapterCfg (.split .scan) (some (.inr symbol)) tail
        leftReverse leftOrdered (symbol :: rightReverse) rightOrdered) := by
  rw [pairAdapter_split_scan_step_nonempty, Option.bind_some,
    pairAdapter_split_push_right_step]

theorem pairAdapter_split_iteration_empty {Γ Δ : Type}
    (state : Option (Sum Γ Δ)) (leftReverse leftOrdered : List Γ)
    (rightReverse rightOrdered : List Δ) :
    (TM2.step pairAdapterProgram
        (pairAdapterCfg (.split .scan) state [] leftReverse leftOrdered
          rightReverse rightOrdered)).bind (TM2.step pairAdapterProgram) =
      some (pairAdapterCfg (.split .done) none [] leftReverse leftOrdered
        rightReverse rightOrdered) := by
  rw [pairAdapter_split_scan_step_empty, Option.bind_some,
    pairAdapter_split_push_none_step]

/-- Classification executes unchanged in the shared layout while preserving
the two ordered stacks for the following phase. -/
theorem pairAdapter_split_whole_list {Γ Δ : Type}
    (state : Option (Sum Γ Δ)) (source : List (Sum Γ Δ))
    (leftReverse leftOrdered : List Γ)
    (rightReverse rightOrdered : List Δ) :
    (flip Option.bind (TM2.step pairAdapterProgram))^[
        2 * source.length + 2]
      (some (pairAdapterCfg (.split .scan) state source leftReverse
        leftOrdered rightReverse rightOrdered)) =
      some (pairAdapterCfg (.split .done) none []
        ((PairEncoding.leftSymbols source).reverse ++ leftReverse)
        leftOrdered
        ((PairEncoding.rightSymbols source).reverse ++ rightReverse)
        rightOrdered) := by
  induction source generalizing state leftReverse rightReverse with
  | nil =>
      simpa [Function.iterate_succ_apply'] using
        pairAdapter_split_iteration_empty state leftReverse leftOrdered
          rightReverse rightOrdered
  | cons head tail ih =>
      cases head with
      | inl symbol =>
          have firstIteration :=
            pairAdapter_split_iteration_left state symbol tail leftReverse
              leftOrdered rightReverse rightOrdered
          rw [List.length_cons]
          have stepCount : 2 * (tail.length + 1) + 2 =
              (2 * tail.length + 2) + 2 := by omega
          rw [stepCount, Function.iterate_add_apply]
          rw [show
            (flip Option.bind (TM2.step pairAdapterProgram))^[2]
                (some (pairAdapterCfg (.split .scan) state
                  (Sum.inl symbol :: tail) leftReverse leftOrdered
                  rightReverse rightOrdered)) =
              some (pairAdapterCfg (.split .scan) (some (.inl symbol)) tail
                (symbol :: leftReverse) leftOrdered rightReverse
                rightOrdered) by
            simpa [Function.iterate_succ_apply'] using firstIteration]
          simpa [PairEncoding.leftSymbols, PairEncoding.rightSymbols,
            List.reverse_cons, List.append_assoc] using
            ih (some (Sum.inl symbol)) (symbol :: leftReverse) rightReverse
      | inr symbol =>
          have firstIteration :=
            pairAdapter_split_iteration_right state symbol tail leftReverse
              leftOrdered rightReverse rightOrdered
          rw [List.length_cons]
          have stepCount : 2 * (tail.length + 1) + 2 =
              (2 * tail.length + 2) + 2 := by omega
          rw [stepCount, Function.iterate_add_apply]
          rw [show
            (flip Option.bind (TM2.step pairAdapterProgram))^[2]
                (some (pairAdapterCfg (.split .scan) state
                  (Sum.inr symbol :: tail) leftReverse leftOrdered
                  rightReverse rightOrdered)) =
              some (pairAdapterCfg (.split .scan) (some (.inr symbol)) tail
                leftReverse leftOrdered (symbol :: rightReverse)
                rightOrdered) by
            simpa [Function.iterate_succ_apply'] using firstIteration]
          simpa [PairEncoding.leftSymbols, PairEncoding.rightSymbols,
            List.reverse_cons, List.append_assoc] using
            ih (some (Sum.inr symbol)) leftReverse (symbol :: rightReverse)

theorem pairAdapter_restore_left_scan_step_nonempty {Γ Δ : Type}
    (state : Option (Sum Γ Δ)) (source : List (Sum Γ Δ))
    (head : Γ) (tail leftOrdered : List Γ)
    (rightReverse rightOrdered : List Δ) :
    TM2.step pairAdapterProgram
        (pairAdapterCfg (.restore .leftScan) state source (head :: tail)
          leftOrdered rightReverse rightOrdered) =
      some (pairAdapterCfg (.restore (.leftPush (some (.inl head))))
        (some (.inl head)) source tail leftOrdered rightReverse
        rightOrdered) := by
  simp only [TM2.step, pairAdapterProgram, TM2.stepAux, pairAdapterCfg,
    pairAdapterStacks_leftReverse]
  rw [pairAdapterStacks_leftReverse_update]
  simp

theorem pairAdapter_restore_left_scan_step_empty {Γ Δ : Type}
    (state : Option (Sum Γ Δ)) (source : List (Sum Γ Δ))
    (leftOrdered : List Γ) (rightReverse rightOrdered : List Δ) :
    TM2.step pairAdapterProgram
        (pairAdapterCfg (.restore .leftScan) state source [] leftOrdered
          rightReverse rightOrdered) =
      some (pairAdapterCfg (.restore (.leftPush none)) none source []
        leftOrdered rightReverse rightOrdered) := by
  simp only [TM2.step, pairAdapterProgram, TM2.stepAux, pairAdapterCfg,
    pairAdapterStacks_leftReverse]
  rw [pairAdapterStacks_leftReverse_update]
  simp

theorem pairAdapter_restore_left_push_step {Γ Δ : Type}
    (symbol : Γ) (state : Option (Sum Γ Δ))
    (source : List (Sum Γ Δ)) (leftReverse leftOrdered : List Γ)
    (rightReverse rightOrdered : List Δ) :
    TM2.step pairAdapterProgram
        (pairAdapterCfg (.restore (.leftPush (some (.inl symbol)))) state
          source leftReverse leftOrdered rightReverse rightOrdered) =
      some (pairAdapterCfg (.restore .leftScan) state source leftReverse
        (symbol :: leftOrdered) rightReverse rightOrdered) := by
  simp only [TM2.step, pairAdapterProgram, TM2.stepAux, pairAdapterCfg,
    pairAdapterStacks_leftOrdered]
  rw [pairAdapterStacks_leftOrdered_update]

theorem pairAdapter_restore_left_push_none_step {Γ Δ : Type}
    (state : Option (Sum Γ Δ)) (source : List (Sum Γ Δ))
    (leftOrdered : List Γ) (rightReverse rightOrdered : List Δ) :
    TM2.step pairAdapterProgram
        (pairAdapterCfg (.restore (.leftPush none)) state source []
          leftOrdered rightReverse rightOrdered) =
      some (pairAdapterCfg (.restore .rightScan) state source [] leftOrdered
        rightReverse rightOrdered) :=
  rfl

theorem pairAdapter_restore_right_scan_step_nonempty {Γ Δ : Type}
    (state : Option (Sum Γ Δ)) (source : List (Sum Γ Δ))
    (leftOrdered : List Γ) (head : Δ) (tail rightOrdered : List Δ) :
    TM2.step pairAdapterProgram
        (pairAdapterCfg (.restore .rightScan) state source [] leftOrdered
          (head :: tail) rightOrdered) =
      some (pairAdapterCfg (.restore (.rightPush (some (.inr head))))
        (some (.inr head)) source [] leftOrdered tail rightOrdered) := by
  simp only [TM2.step, pairAdapterProgram, TM2.stepAux, pairAdapterCfg,
    pairAdapterStacks_rightReverse]
  rw [pairAdapterStacks_rightReverse_update]
  simp

theorem pairAdapter_restore_right_scan_step_empty {Γ Δ : Type}
    (state : Option (Sum Γ Δ)) (source : List (Sum Γ Δ))
    (leftOrdered : List Γ) (rightOrdered : List Δ) :
    TM2.step pairAdapterProgram
        (pairAdapterCfg (.restore .rightScan) state source [] leftOrdered []
          rightOrdered) =
      some (pairAdapterCfg (.restore (.rightPush none)) none source []
        leftOrdered [] rightOrdered) := by
  simp only [TM2.step, pairAdapterProgram, TM2.stepAux, pairAdapterCfg,
    pairAdapterStacks_rightReverse]
  rw [pairAdapterStacks_rightReverse_update]
  simp

theorem pairAdapter_restore_right_push_step {Γ Δ : Type}
    (symbol : Δ) (state : Option (Sum Γ Δ))
    (source : List (Sum Γ Δ)) (leftOrdered : List Γ)
    (rightReverse rightOrdered : List Δ) :
    TM2.step pairAdapterProgram
        (pairAdapterCfg (.restore (.rightPush (some (.inr symbol)))) state
          source [] leftOrdered rightReverse rightOrdered) =
      some (pairAdapterCfg (.restore .rightScan) state source [] leftOrdered
        rightReverse (symbol :: rightOrdered)) := by
  simp only [TM2.step, pairAdapterProgram, TM2.stepAux, pairAdapterCfg,
    pairAdapterStacks_rightOrdered]
  rw [pairAdapterStacks_rightOrdered_update]

theorem pairAdapter_restore_right_push_none_step {Γ Δ : Type}
    (state : Option (Sum Γ Δ)) (source : List (Sum Γ Δ))
    (leftOrdered : List Γ) (rightOrdered : List Δ) :
    TM2.step pairAdapterProgram
        (pairAdapterCfg (.restore (.rightPush none)) state source []
          leftOrdered [] rightOrdered) =
      some (pairAdapterCfg (.restore .done) state source [] leftOrdered []
        rightOrdered) :=
  rfl

theorem pairAdapter_restore_left_iteration_nonempty {Γ Δ : Type}
    (state : Option (Sum Γ Δ)) (source : List (Sum Γ Δ))
    (head : Γ) (tail leftOrdered : List Γ)
    (rightReverse rightOrdered : List Δ) :
    (TM2.step pairAdapterProgram
        (pairAdapterCfg (.restore .leftScan) state source (head :: tail)
          leftOrdered rightReverse rightOrdered)).bind
        (TM2.step pairAdapterProgram) =
      some (pairAdapterCfg (.restore .leftScan) (some (.inl head)) source
        tail (head :: leftOrdered) rightReverse rightOrdered) := by
  rw [pairAdapter_restore_left_scan_step_nonempty, Option.bind_some,
    pairAdapter_restore_left_push_step]

theorem pairAdapter_restore_left_iteration_empty {Γ Δ : Type}
    (state : Option (Sum Γ Δ)) (source : List (Sum Γ Δ))
    (leftOrdered : List Γ) (rightReverse rightOrdered : List Δ) :
    (TM2.step pairAdapterProgram
        (pairAdapterCfg (.restore .leftScan) state source [] leftOrdered
          rightReverse rightOrdered)).bind (TM2.step pairAdapterProgram) =
      some (pairAdapterCfg (.restore .rightScan) none source [] leftOrdered
        rightReverse rightOrdered) := by
  rw [pairAdapter_restore_left_scan_step_empty, Option.bind_some,
    pairAdapter_restore_left_push_none_step]

theorem pairAdapter_restore_right_iteration_nonempty {Γ Δ : Type}
    (state : Option (Sum Γ Δ)) (source : List (Sum Γ Δ))
    (leftOrdered : List Γ) (head : Δ) (tail rightOrdered : List Δ) :
    (TM2.step pairAdapterProgram
        (pairAdapterCfg (.restore .rightScan) state source [] leftOrdered
          (head :: tail) rightOrdered)).bind (TM2.step pairAdapterProgram) =
      some (pairAdapterCfg (.restore .rightScan) (some (.inr head)) source []
        leftOrdered tail (head :: rightOrdered)) := by
  rw [pairAdapter_restore_right_scan_step_nonempty, Option.bind_some,
    pairAdapter_restore_right_push_step]

theorem pairAdapter_restore_right_iteration_empty {Γ Δ : Type}
    (state : Option (Sum Γ Δ)) (source : List (Sum Γ Δ))
    (leftOrdered : List Γ) (rightOrdered : List Δ) :
    (TM2.step pairAdapterProgram
        (pairAdapterCfg (.restore .rightScan) state source [] leftOrdered []
          rightOrdered)).bind (TM2.step pairAdapterProgram) =
      some (pairAdapterCfg (.restore .done) none source [] leftOrdered []
        rightOrdered) := by
  rw [pairAdapter_restore_right_scan_step_empty, Option.bind_some,
    pairAdapter_restore_right_push_none_step]

theorem pairAdapter_restore_left_whole_list {Γ Δ : Type}
    (state : Option (Sum Γ Δ)) (source : List (Sum Γ Δ))
    (leftReverse leftOrdered : List Γ)
    (rightReverse rightOrdered : List Δ) :
    (flip Option.bind (TM2.step pairAdapterProgram))^[
        2 * leftReverse.length + 2]
      (some (pairAdapterCfg (.restore .leftScan) state source leftReverse
        leftOrdered rightReverse rightOrdered)) =
      some (pairAdapterCfg (.restore .rightScan) none source []
        (leftReverse.reverse ++ leftOrdered) rightReverse rightOrdered) := by
  induction leftReverse generalizing state leftOrdered with
  | nil =>
      simpa [Function.iterate_succ_apply'] using
        pairAdapter_restore_left_iteration_empty state source leftOrdered
          rightReverse rightOrdered
  | cons head tail ih =>
      have firstIteration :=
        pairAdapter_restore_left_iteration_nonempty state source head tail
          leftOrdered rightReverse rightOrdered
      rw [List.length_cons]
      have stepCount : 2 * (tail.length + 1) + 2 =
          (2 * tail.length + 2) + 2 := by omega
      rw [stepCount, Function.iterate_add_apply]
      rw [show
        (flip Option.bind (TM2.step pairAdapterProgram))^[2]
            (some (pairAdapterCfg (.restore .leftScan) state source
              (head :: tail) leftOrdered rightReverse rightOrdered)) =
          some (pairAdapterCfg (.restore .leftScan) (some (.inl head))
            source tail (head :: leftOrdered) rightReverse rightOrdered) by
        simpa [Function.iterate_succ_apply'] using firstIteration]
      simpa [List.reverse_cons, List.append_assoc] using
        ih (some (.inl head)) (head :: leftOrdered)

theorem pairAdapter_restore_right_whole_list {Γ Δ : Type}
    (state : Option (Sum Γ Δ)) (source : List (Sum Γ Δ))
    (leftOrdered : List Γ) (rightReverse rightOrdered : List Δ) :
    (flip Option.bind (TM2.step pairAdapterProgram))^[
        2 * rightReverse.length + 2]
      (some (pairAdapterCfg (.restore .rightScan) state source [] leftOrdered
        rightReverse rightOrdered)) =
      some (pairAdapterCfg (.restore .done) none source [] leftOrdered []
        (rightReverse.reverse ++ rightOrdered)) := by
  induction rightReverse generalizing state rightOrdered with
  | nil =>
      simpa [Function.iterate_succ_apply'] using
        pairAdapter_restore_right_iteration_empty state source leftOrdered
          rightOrdered
  | cons head tail ih =>
      have firstIteration :=
        pairAdapter_restore_right_iteration_nonempty state source leftOrdered
          head tail rightOrdered
      rw [List.length_cons]
      have stepCount : 2 * (tail.length + 1) + 2 =
          (2 * tail.length + 2) + 2 := by omega
      rw [stepCount, Function.iterate_add_apply]
      rw [show
        (flip Option.bind (TM2.step pairAdapterProgram))^[2]
            (some (pairAdapterCfg (.restore .rightScan) state source []
              leftOrdered (head :: tail) rightOrdered)) =
          some (pairAdapterCfg (.restore .rightScan) (some (.inr head))
            source [] leftOrdered tail (head :: rightOrdered)) by
        simpa [Function.iterate_succ_apply'] using firstIteration]
      simpa [List.reverse_cons, List.append_assoc] using
        ih (some (.inr head)) (head :: rightOrdered)

/-- Restoration executes in the same shared layout and preserves the emptied
tagged source stack. -/
theorem pairAdapter_restore_whole_list {Γ Δ : Type}
    (state : Option (Sum Γ Δ)) (source : List (Sum Γ Δ))
    (leftReverse : List Γ) (rightReverse : List Δ) :
    (flip Option.bind (TM2.step pairAdapterProgram))^[
        2 * leftReverse.length + 2 * rightReverse.length + 4]
      (some (pairAdapterCfg (.restore .leftScan) state source leftReverse []
        rightReverse [])) =
      some (pairAdapterCfg (.restore .done) none source []
        leftReverse.reverse [] rightReverse.reverse) := by
  have leftRun :=
    pairAdapter_restore_left_whole_list state source leftReverse []
      rightReverse []
  have rightRun :=
    pairAdapter_restore_right_whole_list (Γ := Γ) none source
      leftReverse.reverse rightReverse []
  have leftRun' :
      (flip Option.bind (TM2.step pairAdapterProgram))^[
          2 * leftReverse.length + 2]
        (some (pairAdapterCfg (.restore .leftScan) state source leftReverse []
          rightReverse [])) =
        some (pairAdapterCfg (.restore .rightScan) none source []
          leftReverse.reverse rightReverse []) := by
    simpa using leftRun
  have rightRun' :
      (flip Option.bind (TM2.step pairAdapterProgram))^[
          2 * rightReverse.length + 2]
        (some (pairAdapterCfg (.restore .rightScan) none source []
          leftReverse.reverse rightReverse [])) =
        some (pairAdapterCfg (.restore .done) none source []
          leftReverse.reverse [] rightReverse.reverse) := by
    simpa using rightRun
  have stepCount :
      2 * leftReverse.length + 2 * rightReverse.length + 4 =
        (2 * rightReverse.length + 2) + (2 * leftReverse.length + 2) := by
    omega
  rw [stepCount, Function.iterate_add_apply, leftRun', rightRun']

/-- The integrated preprocessing program classifies an arbitrary tagged list,
crosses the phase boundary, and restores both projections to their original
order. Its exact cost is four steps per source symbol plus seven fixed steps. -/
theorem pairAdapter_whole_list {Γ Δ : Type}
    (state : Option (Sum Γ Δ)) (source : List (Sum Γ Δ)) :
    (flip Option.bind (TM2.step pairAdapterProgram))^[4 * source.length + 7]
      (some (pairAdapterCfg (.split .scan) state source [] [] [] [])) =
      some (pairAdapterCfg (.restore .done) none [] []
        (PairEncoding.leftSymbols source) []
        (PairEncoding.rightSymbols source)) := by
  have splitRun :
      (flip Option.bind (TM2.step pairAdapterProgram))^[
          2 * source.length + 2]
        (some (pairAdapterCfg (.split .scan) state source [] [] [] [])) =
        some (pairAdapterCfg (.split .done) none []
          (PairEncoding.leftSymbols source).reverse []
          (PairEncoding.rightSymbols source).reverse []) := by
    simpa using pairAdapter_split_whole_list state source [] [] [] []
  have bridgeRun :
      (flip Option.bind (TM2.step pairAdapterProgram))^[1]
        (some (pairAdapterCfg (.split .done) none []
          (PairEncoding.leftSymbols source).reverse []
          (PairEncoding.rightSymbols source).reverse [])) =
        some (pairAdapterCfg (.restore .leftScan) none []
          (PairEncoding.leftSymbols source).reverse []
          (PairEncoding.rightSymbols source).reverse []) := by
    simpa [Function.iterate_succ_apply'] using
      pairAdapter_split_done_step (Γ := Γ) (Δ := Δ) none
        (PairEncoding.leftSymbols source).reverse []
        (PairEncoding.rightSymbols source).reverse []
  have restoreRun :
      (flip Option.bind (TM2.step pairAdapterProgram))^[
          2 * (PairEncoding.leftSymbols source).length +
            2 * (PairEncoding.rightSymbols source).length + 4]
        (some (pairAdapterCfg (.restore .leftScan) none []
          (PairEncoding.leftSymbols source).reverse []
          (PairEncoding.rightSymbols source).reverse [])) =
        some (pairAdapterCfg (.restore .done) none [] []
          (PairEncoding.leftSymbols source) []
          (PairEncoding.rightSymbols source)) := by
    simpa using pairAdapter_restore_whole_list (Γ := Γ) (Δ := Δ) none []
      (PairEncoding.leftSymbols source).reverse
      (PairEncoding.rightSymbols source).reverse
  have projectionLength :=
    PairEncoding.leftSymbols_length_add_rightSymbols_length source
  have stepCount :
      4 * source.length + 7 =
        (2 * (PairEncoding.leftSymbols source).length +
            2 * (PairEncoding.rightSymbols source).length + 4) +
          (1 + (2 * source.length + 2)) := by
    omega
  rw [stepCount]
  rw [Function.iterate_add_apply]
  rw [show
    (flip Option.bind (TM2.step pairAdapterProgram))^[
        1 + (2 * source.length + 2)]
      (some (pairAdapterCfg (.split .scan) state source [] [] [] [])) =
      (flip Option.bind (TM2.step pairAdapterProgram))^[1]
        ((flip Option.bind (TM2.step pairAdapterProgram))^[
            2 * source.length + 2]
          (some (pairAdapterCfg (.split .scan) state source [] [] [] []))) by
    rw [Function.iterate_add_apply]]
  rw [splitRun, bridgeRun, restoreRun]

/-- The exact integrated preprocessing run as a finite-execution witness. -/
def pairAdapter_evalsTo {Γ Δ : Type}
    (state : Option (Sum Γ Δ)) (source : List (Sum Γ Δ)) :
    EvalsTo (TM2.step pairAdapterProgram)
      (pairAdapterCfg (.split .scan) state source [] [] [] [])
      (some (pairAdapterCfg (.restore .done) none [] []
        (PairEncoding.leftSymbols source) []
        (PairEncoding.rightSymbols source))) where
  steps := 4 * source.length + 7
  evals_in_steps := pairAdapter_whole_list state source

/-- On a canonical tagged pair encoding, the integrated preprocessing machine
recovers exactly the input and certificate encodings on their ordered stacks. -/
theorem pairAdapter_finEncoding_whole_list {α β : Type}
    (left : Computability.FinEncoding α)
    (right : Computability.FinEncoding β) (pair : α × β) :
    (flip Option.bind (TM2.step pairAdapterProgram))^[
        4 * ((PairEncoding.finEncoding left right).encode pair).length + 7]
      (some (pairAdapterCfg (.split .scan) none
        ((PairEncoding.finEncoding left right).encode pair) [] [] [] [])) =
      some (pairAdapterCfg (.restore .done) none [] []
        (left.encode pair.1) [] (right.encode pair.2)) := by
  simpa [PairEncoding.finEncoding] using
    pairAdapter_whole_list (Γ := left.Γ) (Δ := right.Γ) none
      ((PairEncoding.finEncoding left right).encode pair)

end LeanNPHardness.MachineAdapters
