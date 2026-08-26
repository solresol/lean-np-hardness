import LeanNPHardness.PairEncoding
import Mathlib.Computability.TMComputable

namespace LeanNPHardness.MachineAdapters

open Turing

/-- The stacks used by the first phase of a machine adapter on tagged pairs.
The source stack contains the combined tagged encoding; each component has a
separate reverse stack. -/
inductive PairSplitStackIndex
  | source
  | leftReverse
  | rightReverse
  deriving DecidableEq, Fintype

/-- The dependent alphabet family for the tagged source and the two private
component stacks. -/
def PairSplitStackAlphabet (Γ Δ : Type) : PairSplitStackIndex → Type
  | .source => Sum Γ Δ
  | .leftReverse => Γ
  | .rightReverse => Δ

/-- Finite control for scanning a tagged pair encoding. The intermediate
`push` action carries the symbol read from the source, avoiding any
`Inhabited` assumption on either component alphabet. -/
inductive PairSplitAction (Γ Δ : Type)
  | scan
  | push (symbol : Option (Sum Γ Δ))
  | done
  deriving DecidableEq, Fintype

/-- Explicit contents for the source and component reverse stacks. -/
def pairSplitStacks {Γ Δ : Type}
    (source : List (Sum Γ Δ)) (leftReverse : List Γ)
    (rightReverse : List Δ) :
    ∀ index, List (PairSplitStackAlphabet Γ Δ index)
  | .source => source
  | .leftReverse => leftReverse
  | .rightReverse => rightReverse

@[simp]
theorem pairSplitStacks_source {Γ Δ : Type}
    (source : List (Sum Γ Δ)) (leftReverse : List Γ)
    (rightReverse : List Δ) :
    pairSplitStacks source leftReverse rightReverse .source = source :=
  rfl

@[simp]
theorem pairSplitStacks_leftReverse {Γ Δ : Type}
    (source : List (Sum Γ Δ)) (leftReverse : List Γ)
    (rightReverse : List Δ) :
    pairSplitStacks source leftReverse rightReverse .leftReverse =
      leftReverse :=
  rfl

@[simp]
theorem pairSplitStacks_rightReverse {Γ Δ : Type}
    (source : List (Sum Γ Δ)) (leftReverse : List Γ)
    (rightReverse : List Δ) :
    pairSplitStacks source leftReverse rightReverse .rightReverse =
      rightReverse :=
  rfl

/-- Replacing the tagged source commutes with its dependent stack update. -/
theorem pairSplitStacks_source_update {Γ Δ : Type}
    (source value : List (Sum Γ Δ)) (leftReverse : List Γ)
    (rightReverse : List Δ) :
    Function.update (pairSplitStacks source leftReverse rightReverse)
        PairSplitStackIndex.source value =
      pairSplitStacks value leftReverse rightReverse := by
  funext index
  cases index <;> simp [pairSplitStacks]

/-- Replacing the left reverse stack commutes with its dependent update. -/
theorem pairSplitStacks_leftReverse_update {Γ Δ : Type}
    (source : List (Sum Γ Δ)) (leftReverse value : List Γ)
    (rightReverse : List Δ) :
    Function.update (pairSplitStacks source leftReverse rightReverse)
        PairSplitStackIndex.leftReverse value =
      pairSplitStacks source value rightReverse := by
  funext index
  cases index <;> simp [pairSplitStacks]

/-- Replacing the right reverse stack commutes with its dependent update. -/
theorem pairSplitStacks_rightReverse_update {Γ Δ : Type}
    (source : List (Sum Γ Δ)) (leftReverse : List Γ)
    (rightReverse value : List Δ) :
    Function.update (pairSplitStacks source leftReverse rightReverse)
        PairSplitStackIndex.rightReverse value =
      pairSplitStacks source leftReverse value := by
  funext index
  cases index <;> simp [pairSplitStacks]

/-- A configuration of the tagged-pair classification pass with every stack
made explicit. -/
def pairSplitCfg {Γ Δ : Type} (action : PairSplitAction Γ Δ)
    (state : Option (Sum Γ Δ)) (source : List (Sum Γ Δ))
    (leftReverse : List Γ) (rightReverse : List Δ) :
    TM2.Cfg (PairSplitStackAlphabet Γ Δ) (PairSplitAction Γ Δ)
      (Option (Sum Γ Δ)) where
  l := some action
  var := state
  stk := pairSplitStacks source leftReverse rightReverse

/-- The executable classification pass. A scan pops one tagged symbol and
selects a symbol-carrying action; that action pushes to the corresponding
private stack. Exhaustion enters the explicit `done` label. -/
def pairSplitProgram {Γ Δ : Type} :
    PairSplitAction Γ Δ →
      TM2.Stmt (PairSplitStackAlphabet Γ Δ) (PairSplitAction Γ Δ)
        (Option (Sum Γ Δ))
  | .scan =>
      .pop .source (fun _ symbol => symbol)
        (.goto (fun symbol => .push symbol))
  | .push none => .goto (fun _ => .done)
  | .push (some (.inl symbol)) =>
      .push .leftReverse (fun _ => symbol) (.goto (fun _ => .scan))
  | .push (some (.inr symbol)) =>
      .push .rightReverse (fun _ => symbol) (.goto (fun _ => .scan))
  | .done => .halt

/-- A nonempty scan removes the source head and records it in finite control. -/
theorem pairSplit_scan_step_nonempty {Γ Δ : Type}
    (state : Option (Sum Γ Δ)) (head : Sum Γ Δ)
    (tail : List (Sum Γ Δ)) (leftReverse : List Γ)
    (rightReverse : List Δ) :
    TM2.step pairSplitProgram
        (pairSplitCfg .scan state (head :: tail) leftReverse rightReverse) =
      some (pairSplitCfg (.push (some head)) (some head) tail leftReverse
        rightReverse) := by
  simp only [TM2.step, pairSplitProgram, TM2.stepAux, pairSplitCfg,
    pairSplitStacks_source]
  rw [pairSplitStacks_source_update]
  simp

/-- An empty scan records exhaustion without changing component stacks. -/
theorem pairSplit_scan_step_empty {Γ Δ : Type}
    (state : Option (Sum Γ Δ)) (leftReverse : List Γ)
    (rightReverse : List Δ) :
    TM2.step pairSplitProgram
        (pairSplitCfg .scan state [] leftReverse rightReverse) =
      some (pairSplitCfg (.push none) none [] leftReverse rightReverse) := by
  simp only [TM2.step, pairSplitProgram, TM2.stepAux, pairSplitCfg,
    pairSplitStacks_source]
  rw [pairSplitStacks_source_update]
  simp

/-- A carried left symbol is pushed onto the left reverse stack. -/
theorem pairSplit_push_left_step {Γ Δ : Type} (symbol : Γ)
    (state : Option (Sum Γ Δ)) (source : List (Sum Γ Δ))
    (leftReverse : List Γ) (rightReverse : List Δ) :
    TM2.step pairSplitProgram
        (pairSplitCfg (.push (some (.inl symbol))) state source leftReverse
          rightReverse) =
      some (pairSplitCfg .scan state source (symbol :: leftReverse)
        rightReverse) := by
  simp only [TM2.step, pairSplitProgram, TM2.stepAux, pairSplitCfg,
    pairSplitStacks_leftReverse]
  rw [pairSplitStacks_leftReverse_update]

/-- A carried right symbol is pushed onto the right reverse stack. -/
theorem pairSplit_push_right_step {Γ Δ : Type} (symbol : Δ)
    (state : Option (Sum Γ Δ)) (source : List (Sum Γ Δ))
    (leftReverse : List Γ) (rightReverse : List Δ) :
    TM2.step pairSplitProgram
        (pairSplitCfg (.push (some (.inr symbol))) state source leftReverse
          rightReverse) =
      some (pairSplitCfg .scan state source leftReverse
        (symbol :: rightReverse)) := by
  simp only [TM2.step, pairSplitProgram, TM2.stepAux, pairSplitCfg,
    pairSplitStacks_rightReverse]
  rw [pairSplitStacks_rightReverse_update]

/-- The exhaustion action enters the explicit completed configuration. -/
theorem pairSplit_push_none_step {Γ Δ : Type}
    (state : Option (Sum Γ Δ)) (leftReverse : List Γ)
    (rightReverse : List Δ) :
    TM2.step pairSplitProgram
        (pairSplitCfg (.push none) state [] leftReverse rightReverse) =
      some (pairSplitCfg .done state [] leftReverse rightReverse) :=
  rfl

/-- Two program steps classify one left source symbol. -/
theorem pairSplit_iteration_left {Γ Δ : Type}
    (state : Option (Sum Γ Δ)) (symbol : Γ)
    (tail : List (Sum Γ Δ)) (leftReverse : List Γ)
    (rightReverse : List Δ) :
    (TM2.step pairSplitProgram
        (pairSplitCfg .scan state (Sum.inl symbol :: tail) leftReverse
          rightReverse)).bind (TM2.step pairSplitProgram) =
      some (pairSplitCfg .scan (some (Sum.inl symbol)) tail
        (symbol :: leftReverse) rightReverse) := by
  rw [pairSplit_scan_step_nonempty, Option.bind_some,
    pairSplit_push_left_step]

/-- Two program steps classify one right source symbol. -/
theorem pairSplit_iteration_right {Γ Δ : Type}
    (state : Option (Sum Γ Δ)) (symbol : Δ)
    (tail : List (Sum Γ Δ)) (leftReverse : List Γ)
    (rightReverse : List Δ) :
    (TM2.step pairSplitProgram
        (pairSplitCfg .scan state (Sum.inr symbol :: tail) leftReverse
          rightReverse)).bind (TM2.step pairSplitProgram) =
      some (pairSplitCfg .scan (some (Sum.inr symbol)) tail leftReverse
        (symbol :: rightReverse)) := by
  rw [pairSplit_scan_step_nonempty, Option.bind_some,
    pairSplit_push_right_step]

/-- Two program steps detect source exhaustion and complete classification. -/
theorem pairSplit_iteration_empty {Γ Δ : Type}
    (state : Option (Sum Γ Δ)) (leftReverse : List Γ)
    (rightReverse : List Δ) :
    (TM2.step pairSplitProgram
        (pairSplitCfg .scan state [] leftReverse rightReverse)).bind
        (TM2.step pairSplitProgram) =
      some (pairSplitCfg .done none [] leftReverse rightReverse) := by
  rw [pairSplit_scan_step_empty, Option.bind_some,
    pairSplit_push_none_step]

/-- The executable classification pass consumes an arbitrary tagged list in
exactly two steps per source symbol plus two exhaustion steps. It preserves
the relative order of each tag class on its private reverse stack: projecting
the original source and reversing gives the newly prepended stack contents. -/
theorem pairSplit_whole_list {Γ Δ : Type}
    (state : Option (Sum Γ Δ)) (source : List (Sum Γ Δ))
    (leftReverse : List Γ) (rightReverse : List Δ) :
    (flip Option.bind (TM2.step pairSplitProgram))^[2 * source.length + 2]
      (some (pairSplitCfg .scan state source leftReverse rightReverse)) =
      some (pairSplitCfg .done none []
        ((PairEncoding.leftSymbols source).reverse ++ leftReverse)
        ((PairEncoding.rightSymbols source).reverse ++ rightReverse)) := by
  induction source generalizing state leftReverse rightReverse with
  | nil =>
      simpa [Function.iterate_succ_apply'] using
        pairSplit_iteration_empty state leftReverse rightReverse
  | cons head tail ih =>
      cases head with
      | inl symbol =>
          have firstIteration :=
            pairSplit_iteration_left state symbol tail leftReverse rightReverse
          rw [List.length_cons]
          have stepCount : 2 * (tail.length + 1) + 2 =
              (2 * tail.length + 2) + 2 := by omega
          rw [stepCount, Function.iterate_add_apply]
          rw [show
            (flip Option.bind (TM2.step pairSplitProgram))^[2]
                (some (pairSplitCfg .scan state
                  (Sum.inl symbol :: tail) leftReverse rightReverse)) =
              some (pairSplitCfg .scan (some (Sum.inl symbol)) tail
                (symbol :: leftReverse) rightReverse) by
            simpa [Function.iterate_succ_apply'] using firstIteration]
          simpa [PairEncoding.leftSymbols, PairEncoding.rightSymbols,
            List.reverse_cons, List.append_assoc] using
            ih (some (Sum.inl symbol)) (symbol :: leftReverse) rightReverse
      | inr symbol =>
          have firstIteration :=
            pairSplit_iteration_right state symbol tail leftReverse rightReverse
          rw [List.length_cons]
          have stepCount : 2 * (tail.length + 1) + 2 =
              (2 * tail.length + 2) + 2 := by omega
          rw [stepCount, Function.iterate_add_apply]
          rw [show
            (flip Option.bind (TM2.step pairSplitProgram))^[2]
                (some (pairSplitCfg .scan state
                  (Sum.inr symbol :: tail) leftReverse rightReverse)) =
              some (pairSplitCfg .scan (some (Sum.inr symbol)) tail leftReverse
                (symbol :: rightReverse)) by
            simpa [Function.iterate_succ_apply'] using firstIteration]
          simpa [PairEncoding.leftSymbols, PairEncoding.rightSymbols,
            List.reverse_cons, List.append_assoc] using
            ih (some (Sum.inr symbol)) leftReverse (symbol :: rightReverse)

/-- The exact iterate theorem packaged in mathlib's finite-execution witness. -/
def pairSplit_evalsTo {Γ Δ : Type}
    (state : Option (Sum Γ Δ)) (source : List (Sum Γ Δ))
    (leftReverse : List Γ) (rightReverse : List Δ) :
    EvalsTo (TM2.step pairSplitProgram)
      (pairSplitCfg .scan state source leftReverse rightReverse)
      (some (pairSplitCfg .done none []
        ((PairEncoding.leftSymbols source).reverse ++ leftReverse)
        ((PairEncoding.rightSymbols source).reverse ++ rightReverse))) where
  steps := 2 * source.length + 2
  evals_in_steps := pairSplit_whole_list state source leftReverse rightReverse

/-- On the repository's canonical tagged encoding, classification produces
exactly the reversed input and certificate encodings on their private stacks. -/
theorem pairSplit_finEncoding_whole_list {α β : Type}
    (left : Computability.FinEncoding α)
    (right : Computability.FinEncoding β) (pair : α × β) :
    (flip Option.bind (TM2.step pairSplitProgram))^[
        2 * ((PairEncoding.finEncoding left right).encode pair).length + 2]
      (some (pairSplitCfg .scan none
        ((PairEncoding.finEncoding left right).encode pair) [] [])) =
      some (pairSplitCfg .done none []
        (left.encode pair.1).reverse (right.encode pair.2).reverse) := by
  simpa [PairEncoding.finEncoding] using
    pairSplit_whole_list (Γ := left.Γ) (Δ := right.Γ) none
      ((PairEncoding.finEncoding left right).encode pair) [] []

/-- The four private stacks used to restore the two classified components to
their canonical order. Each component has a reverse stack produced by the
classification pass and a separate ordered destination stack. -/
inductive PairRestoreStackIndex
  | leftReverse
  | leftOrdered
  | rightReverse
  | rightOrdered
  deriving DecidableEq, Fintype

/-- The dependent alphabet family for the component restoration phase. -/
def PairRestoreStackAlphabet (Γ Δ : Type) : PairRestoreStackIndex → Type
  | .leftReverse => Γ
  | .leftOrdered => Γ
  | .rightReverse => Δ
  | .rightOrdered => Δ

/-- Finite control for restoring the left component and then the right
component. Symbol-carrying push actions avoid any `Inhabited` assumption. -/
inductive PairRestoreAction (Γ Δ : Type)
  | leftScan
  | leftPush (symbol : Option (Sum Γ Δ))
  | rightScan
  | rightPush (symbol : Option (Sum Γ Δ))
  | done
  deriving DecidableEq, Fintype

/-- Explicit contents for both reverse stacks and both ordered stacks. -/
def pairRestoreStacks {Γ Δ : Type}
    (leftReverse leftOrdered : List Γ)
    (rightReverse rightOrdered : List Δ) :
    ∀ index, List (PairRestoreStackAlphabet Γ Δ index)
  | .leftReverse => leftReverse
  | .leftOrdered => leftOrdered
  | .rightReverse => rightReverse
  | .rightOrdered => rightOrdered

@[simp]
theorem pairRestoreStacks_leftReverse {Γ Δ : Type}
    (leftReverse leftOrdered : List Γ)
    (rightReverse rightOrdered : List Δ) :
    pairRestoreStacks leftReverse leftOrdered rightReverse rightOrdered
        .leftReverse = leftReverse :=
  rfl

@[simp]
theorem pairRestoreStacks_leftOrdered {Γ Δ : Type}
    (leftReverse leftOrdered : List Γ)
    (rightReverse rightOrdered : List Δ) :
    pairRestoreStacks leftReverse leftOrdered rightReverse rightOrdered
        .leftOrdered = leftOrdered :=
  rfl

@[simp]
theorem pairRestoreStacks_rightReverse {Γ Δ : Type}
    (leftReverse leftOrdered : List Γ)
    (rightReverse rightOrdered : List Δ) :
    pairRestoreStacks leftReverse leftOrdered rightReverse rightOrdered
        .rightReverse = rightReverse :=
  rfl

@[simp]
theorem pairRestoreStacks_rightOrdered {Γ Δ : Type}
    (leftReverse leftOrdered : List Γ)
    (rightReverse rightOrdered : List Δ) :
    pairRestoreStacks leftReverse leftOrdered rightReverse rightOrdered
        .rightOrdered = rightOrdered :=
  rfl

/-- Replacing the left reverse stack commutes with its dependent update. -/
theorem pairRestoreStacks_leftReverse_update {Γ Δ : Type}
    (leftReverse value leftOrdered : List Γ)
    (rightReverse rightOrdered : List Δ) :
    Function.update
        (pairRestoreStacks leftReverse leftOrdered rightReverse rightOrdered)
        PairRestoreStackIndex.leftReverse value =
      pairRestoreStacks value leftOrdered rightReverse rightOrdered := by
  funext index
  cases index <;> simp [pairRestoreStacks]

/-- Replacing the left ordered stack commutes with its dependent update. -/
theorem pairRestoreStacks_leftOrdered_update {Γ Δ : Type}
    (leftReverse leftOrdered value : List Γ)
    (rightReverse rightOrdered : List Δ) :
    Function.update
        (pairRestoreStacks leftReverse leftOrdered rightReverse rightOrdered)
        PairRestoreStackIndex.leftOrdered value =
      pairRestoreStacks leftReverse value rightReverse rightOrdered := by
  funext index
  cases index <;> simp [pairRestoreStacks]

/-- Replacing the right reverse stack commutes with its dependent update. -/
theorem pairRestoreStacks_rightReverse_update {Γ Δ : Type}
    (leftReverse leftOrdered : List Γ)
    (rightReverse value rightOrdered : List Δ) :
    Function.update
        (pairRestoreStacks leftReverse leftOrdered rightReverse rightOrdered)
        PairRestoreStackIndex.rightReverse value =
      pairRestoreStacks leftReverse leftOrdered value rightOrdered := by
  funext index
  cases index <;> simp [pairRestoreStacks]

/-- Replacing the right ordered stack commutes with its dependent update. -/
theorem pairRestoreStacks_rightOrdered_update {Γ Δ : Type}
    (leftReverse leftOrdered : List Γ)
    (rightReverse rightOrdered value : List Δ) :
    Function.update
        (pairRestoreStacks leftReverse leftOrdered rightReverse rightOrdered)
        PairRestoreStackIndex.rightOrdered value =
      pairRestoreStacks leftReverse leftOrdered rightReverse value := by
  funext index
  cases index <;> simp [pairRestoreStacks]

/-- A configuration of the order-restoration phase with all component stacks
made explicit. -/
def pairRestoreCfg {Γ Δ : Type} (action : PairRestoreAction Γ Δ)
    (state : Option (Sum Γ Δ)) (leftReverse leftOrdered : List Γ)
    (rightReverse rightOrdered : List Δ) :
    TM2.Cfg (PairRestoreStackAlphabet Γ Δ) (PairRestoreAction Γ Δ)
      (Option (Sum Γ Δ)) where
  l := some action
  var := state
  stk := pairRestoreStacks leftReverse leftOrdered rightReverse rightOrdered

/-- Restore the left reverse stack onto its ordered destination, then do the
same for the right component. Exhausted scans advance to the next phase. -/
def pairRestoreProgram {Γ Δ : Type} :
    PairRestoreAction Γ Δ →
      TM2.Stmt (PairRestoreStackAlphabet Γ Δ) (PairRestoreAction Γ Δ)
        (Option (Sum Γ Δ))
  | .leftScan =>
      .pop .leftReverse (fun _ symbol => symbol.map Sum.inl)
        (.goto (fun symbol => .leftPush symbol))
  | .leftPush none => .goto (fun _ => .rightScan)
  | .leftPush (some (.inl symbol)) =>
      .push .leftOrdered (fun _ => symbol) (.goto (fun _ => .leftScan))
  | .leftPush (some (.inr _)) => .goto (fun _ => .rightScan)
  | .rightScan =>
      .pop .rightReverse (fun _ symbol => symbol.map Sum.inr)
        (.goto (fun symbol => .rightPush symbol))
  | .rightPush none => .goto (fun _ => .done)
  | .rightPush (some (.inl _)) => .goto (fun _ => .done)
  | .rightPush (some (.inr symbol)) =>
      .push .rightOrdered (fun _ => symbol) (.goto (fun _ => .rightScan))
  | .done => .halt

/-- A nonempty left scan removes the reverse-stack head and records it in
finite control. -/
theorem pairRestore_left_scan_step_nonempty {Γ Δ : Type}
    (state : Option (Sum Γ Δ)) (head : Γ) (tail leftOrdered : List Γ)
    (rightReverse rightOrdered : List Δ) :
    TM2.step pairRestoreProgram
        (pairRestoreCfg .leftScan state (head :: tail) leftOrdered
          rightReverse rightOrdered) =
      some (pairRestoreCfg (.leftPush (some (.inl head)))
        (some (.inl head)) tail leftOrdered rightReverse rightOrdered) := by
  simp only [TM2.step, pairRestoreProgram, TM2.stepAux, pairRestoreCfg,
    pairRestoreStacks_leftReverse]
  rw [pairRestoreStacks_leftReverse_update]
  simp

/-- An empty left scan records exhaustion without changing any stack. -/
theorem pairRestore_left_scan_step_empty {Γ Δ : Type}
    (state : Option (Sum Γ Δ)) (leftOrdered : List Γ)
    (rightReverse rightOrdered : List Δ) :
    TM2.step pairRestoreProgram
        (pairRestoreCfg .leftScan state [] leftOrdered rightReverse
          rightOrdered) =
      some (pairRestoreCfg (.leftPush none) none [] leftOrdered rightReverse
        rightOrdered) := by
  simp only [TM2.step, pairRestoreProgram, TM2.stepAux, pairRestoreCfg,
    pairRestoreStacks_leftReverse]
  rw [pairRestoreStacks_leftReverse_update]
  simp

/-- A carried left symbol is pushed onto the ordered left stack. -/
theorem pairRestore_left_push_step {Γ Δ : Type}
    (state : Option (Sum Γ Δ)) (symbol : Γ)
    (leftReverse leftOrdered : List Γ)
    (rightReverse rightOrdered : List Δ) :
    TM2.step pairRestoreProgram
        (pairRestoreCfg (.leftPush (some (.inl symbol))) state leftReverse
          leftOrdered rightReverse rightOrdered) =
      some (pairRestoreCfg .leftScan state leftReverse
        (symbol :: leftOrdered) rightReverse rightOrdered) := by
  simp only [TM2.step, pairRestoreProgram, TM2.stepAux, pairRestoreCfg,
    pairRestoreStacks_leftOrdered]
  rw [pairRestoreStacks_leftOrdered_update]

/-- Exhausting the left reverse stack advances to right restoration. -/
theorem pairRestore_left_push_none_step {Γ Δ : Type}
    (state : Option (Sum Γ Δ)) (leftOrdered : List Γ)
    (rightReverse rightOrdered : List Δ) :
    TM2.step pairRestoreProgram
        (pairRestoreCfg (.leftPush none) state [] leftOrdered rightReverse
          rightOrdered) =
      some (pairRestoreCfg .rightScan state [] leftOrdered rightReverse
        rightOrdered) :=
  rfl

/-- A nonempty right scan removes the reverse-stack head and records it in
finite control. -/
theorem pairRestore_right_scan_step_nonempty {Γ Δ : Type}
    (state : Option (Sum Γ Δ)) (leftOrdered : List Γ)
    (head : Δ) (tail rightOrdered : List Δ) :
    TM2.step pairRestoreProgram
        (pairRestoreCfg .rightScan state [] leftOrdered (head :: tail)
          rightOrdered) =
      some (pairRestoreCfg (.rightPush (some (.inr head)))
        (some (.inr head)) [] leftOrdered tail rightOrdered) := by
  simp only [TM2.step, pairRestoreProgram, TM2.stepAux, pairRestoreCfg,
    pairRestoreStacks_rightReverse]
  rw [pairRestoreStacks_rightReverse_update]
  simp

/-- An empty right scan records exhaustion without changing any stack. -/
theorem pairRestore_right_scan_step_empty {Γ Δ : Type}
    (state : Option (Sum Γ Δ)) (leftOrdered : List Γ)
    (rightOrdered : List Δ) :
    TM2.step pairRestoreProgram
        (pairRestoreCfg .rightScan state [] leftOrdered [] rightOrdered) =
      some (pairRestoreCfg (.rightPush none) none [] leftOrdered []
        rightOrdered) := by
  simp only [TM2.step, pairRestoreProgram, TM2.stepAux, pairRestoreCfg,
    pairRestoreStacks_rightReverse]
  rw [pairRestoreStacks_rightReverse_update]
  simp

/-- A carried right symbol is pushed onto the ordered right stack. -/
theorem pairRestore_right_push_step {Γ Δ : Type}
    (state : Option (Sum Γ Δ)) (leftOrdered : List Γ) (symbol : Δ)
    (rightReverse rightOrdered : List Δ) :
    TM2.step pairRestoreProgram
        (pairRestoreCfg (.rightPush (some (.inr symbol))) state [] leftOrdered
          rightReverse rightOrdered) =
      some (pairRestoreCfg .rightScan state [] leftOrdered rightReverse
        (symbol :: rightOrdered)) := by
  simp only [TM2.step, pairRestoreProgram, TM2.stepAux, pairRestoreCfg,
    pairRestoreStacks_rightOrdered]
  rw [pairRestoreStacks_rightOrdered_update]

/-- Exhausting the right reverse stack enters the completed configuration. -/
theorem pairRestore_right_push_none_step {Γ Δ : Type}
    (state : Option (Sum Γ Δ)) (leftOrdered : List Γ)
    (rightOrdered : List Δ) :
    TM2.step pairRestoreProgram
        (pairRestoreCfg (.rightPush none) state [] leftOrdered []
          rightOrdered) =
      some (pairRestoreCfg .done state [] leftOrdered [] rightOrdered) :=
  rfl

/-- Two program steps restore one left symbol. -/
theorem pairRestore_left_iteration_nonempty {Γ Δ : Type}
    (state : Option (Sum Γ Δ)) (head : Γ) (tail leftOrdered : List Γ)
    (rightReverse rightOrdered : List Δ) :
    (TM2.step pairRestoreProgram
        (pairRestoreCfg .leftScan state (head :: tail) leftOrdered
          rightReverse rightOrdered)).bind (TM2.step pairRestoreProgram) =
      some (pairRestoreCfg .leftScan (some (.inl head)) tail
        (head :: leftOrdered) rightReverse rightOrdered) := by
  rw [pairRestore_left_scan_step_nonempty, Option.bind_some,
    pairRestore_left_push_step]

/-- Two program steps detect exhaustion of the left reverse stack. -/
theorem pairRestore_left_iteration_empty {Γ Δ : Type}
    (state : Option (Sum Γ Δ)) (leftOrdered : List Γ)
    (rightReverse rightOrdered : List Δ) :
    (TM2.step pairRestoreProgram
        (pairRestoreCfg .leftScan state [] leftOrdered rightReverse
          rightOrdered)).bind (TM2.step pairRestoreProgram) =
      some (pairRestoreCfg .rightScan none [] leftOrdered rightReverse
        rightOrdered) := by
  rw [pairRestore_left_scan_step_empty, Option.bind_some,
    pairRestore_left_push_none_step]

/-- Two program steps restore one right symbol. -/
theorem pairRestore_right_iteration_nonempty {Γ Δ : Type}
    (state : Option (Sum Γ Δ)) (leftOrdered : List Γ)
    (head : Δ) (tail rightOrdered : List Δ) :
    (TM2.step pairRestoreProgram
        (pairRestoreCfg .rightScan state [] leftOrdered (head :: tail)
          rightOrdered)).bind (TM2.step pairRestoreProgram) =
      some (pairRestoreCfg .rightScan (some (.inr head)) [] leftOrdered tail
        (head :: rightOrdered)) := by
  rw [pairRestore_right_scan_step_nonempty, Option.bind_some,
    pairRestore_right_push_step]

/-- Two program steps detect exhaustion of the right reverse stack. -/
theorem pairRestore_right_iteration_empty {Γ Δ : Type}
    (state : Option (Sum Γ Δ)) (leftOrdered : List Γ)
    (rightOrdered : List Δ) :
    (TM2.step pairRestoreProgram
        (pairRestoreCfg .rightScan state [] leftOrdered [] rightOrdered)).bind
        (TM2.step pairRestoreProgram) =
      some (pairRestoreCfg .done none [] leftOrdered [] rightOrdered) := by
  rw [pairRestore_right_scan_step_empty, Option.bind_some,
    pairRestore_right_push_none_step]

/-- Repeated left restoration consumes the entire left reverse stack in two
steps per symbol plus two exhaustion steps and prepends its reversal to the
ordered left stack. -/
theorem pairRestore_left_whole_list {Γ Δ : Type}
    (state : Option (Sum Γ Δ)) (leftReverse leftOrdered : List Γ)
    (rightReverse rightOrdered : List Δ) :
    (flip Option.bind (TM2.step pairRestoreProgram))^[
        2 * leftReverse.length + 2]
      (some (pairRestoreCfg .leftScan state leftReverse leftOrdered
        rightReverse rightOrdered)) =
      some (pairRestoreCfg .rightScan none []
        (leftReverse.reverse ++ leftOrdered) rightReverse rightOrdered) := by
  induction leftReverse generalizing state leftOrdered with
  | nil =>
      simpa [Function.iterate_succ_apply'] using
        pairRestore_left_iteration_empty state leftOrdered rightReverse
          rightOrdered
  | cons head tail ih =>
      have firstIteration :=
        pairRestore_left_iteration_nonempty state head tail leftOrdered
          rightReverse rightOrdered
      rw [List.length_cons]
      have stepCount : 2 * (tail.length + 1) + 2 =
          (2 * tail.length + 2) + 2 := by omega
      rw [stepCount, Function.iterate_add_apply]
      rw [show
        (flip Option.bind (TM2.step pairRestoreProgram))^[2]
            (some (pairRestoreCfg .leftScan state (head :: tail) leftOrdered
              rightReverse rightOrdered)) =
          some (pairRestoreCfg .leftScan (some (.inl head)) tail
            (head :: leftOrdered) rightReverse rightOrdered) by
        simpa [Function.iterate_succ_apply'] using firstIteration]
      simpa [List.reverse_cons, List.append_assoc] using
        ih (some (.inl head)) (head :: leftOrdered)

/-- Repeated right restoration consumes the entire right reverse stack in two
steps per symbol plus two exhaustion steps and prepends its reversal to the
ordered right stack. -/
theorem pairRestore_right_whole_list {Γ Δ : Type}
    (state : Option (Sum Γ Δ)) (leftOrdered : List Γ)
    (rightReverse rightOrdered : List Δ) :
    (flip Option.bind (TM2.step pairRestoreProgram))^[
        2 * rightReverse.length + 2]
      (some (pairRestoreCfg .rightScan state [] leftOrdered rightReverse
        rightOrdered)) =
      some (pairRestoreCfg .done none [] leftOrdered []
        (rightReverse.reverse ++ rightOrdered)) := by
  induction rightReverse generalizing state rightOrdered with
  | nil =>
      simpa [Function.iterate_succ_apply'] using
        pairRestore_right_iteration_empty state leftOrdered rightOrdered
  | cons head tail ih =>
      have firstIteration :=
        pairRestore_right_iteration_nonempty state leftOrdered head tail
          rightOrdered
      rw [List.length_cons]
      have stepCount : 2 * (tail.length + 1) + 2 =
          (2 * tail.length + 2) + 2 := by omega
      rw [stepCount, Function.iterate_add_apply]
      rw [show
        (flip Option.bind (TM2.step pairRestoreProgram))^[2]
            (some (pairRestoreCfg .rightScan state [] leftOrdered
              (head :: tail) rightOrdered)) =
          some (pairRestoreCfg .rightScan (some (.inr head)) [] leftOrdered
            tail (head :: rightOrdered)) by
        simpa [Function.iterate_succ_apply'] using firstIteration]
      simpa [List.reverse_cons, List.append_assoc] using
        ih (some (.inr head)) (head :: rightOrdered)

/-- The complete restoration phase consumes both reverse stacks, restores both
components to canonical order, and has an exact linear step count. -/
theorem pairRestore_whole_list {Γ Δ : Type}
    (state : Option (Sum Γ Δ)) (leftReverse : List Γ)
    (rightReverse : List Δ) :
    (flip Option.bind (TM2.step pairRestoreProgram))^[
        2 * leftReverse.length + 2 * rightReverse.length + 4]
      (some (pairRestoreCfg .leftScan state leftReverse [] rightReverse [])) =
      some (pairRestoreCfg .done none [] leftReverse.reverse []
        rightReverse.reverse) := by
  have leftRun :=
    pairRestore_left_whole_list state leftReverse [] rightReverse []
  have rightRun :=
    pairRestore_right_whole_list (Γ := Γ) none leftReverse.reverse
      rightReverse []
  have leftRun' :
      (flip Option.bind (TM2.step pairRestoreProgram))^[
          2 * leftReverse.length + 2]
        (some (pairRestoreCfg .leftScan state leftReverse [] rightReverse [])) =
        some (pairRestoreCfg .rightScan none [] leftReverse.reverse
          rightReverse []) := by
    simpa using leftRun
  have rightRun' :
      (flip Option.bind (TM2.step pairRestoreProgram))^[
          2 * rightReverse.length + 2]
        (some (pairRestoreCfg .rightScan none [] leftReverse.reverse
          rightReverse [])) =
        some (pairRestoreCfg .done none [] leftReverse.reverse []
          rightReverse.reverse) := by
    simpa using rightRun
  have stepCount :
      2 * leftReverse.length + 2 * rightReverse.length + 4 =
        (2 * rightReverse.length + 2) + (2 * leftReverse.length + 2) := by
    omega
  rw [stepCount, Function.iterate_add_apply, leftRun', rightRun']

/-- The complete restoration theorem packaged as an exact finite-execution
witness. -/
def pairRestore_evalsTo {Γ Δ : Type}
    (state : Option (Sum Γ Δ)) (leftReverse : List Γ)
    (rightReverse : List Δ) :
    EvalsTo (TM2.step pairRestoreProgram)
      (pairRestoreCfg .leftScan state leftReverse [] rightReverse [])
      (some (pairRestoreCfg .done none [] leftReverse.reverse []
        rightReverse.reverse)) where
  steps := 2 * leftReverse.length + 2 * rightReverse.length + 4
  evals_in_steps := pairRestore_whole_list state leftReverse rightReverse

/-- Reversing the two stacks produced by canonical tagged-pair
classification restores exactly the original component encodings. -/
theorem pairRestore_finEncoding_whole_list {α β : Type}
    (left : Computability.FinEncoding α)
    (right : Computability.FinEncoding β) (pair : α × β) :
    (flip Option.bind (TM2.step pairRestoreProgram))^[
        2 * (left.encode pair.1).length +
          2 * (right.encode pair.2).length + 4]
      (some (pairRestoreCfg .leftScan none
        (left.encode pair.1).reverse [] (right.encode pair.2).reverse [])) =
      some (pairRestoreCfg .done none [] (left.encode pair.1) []
        (right.encode pair.2)) := by
  simpa using pairRestore_whole_list (Γ := left.Γ) (Δ := right.Γ) none
    (left.encode pair.1).reverse (right.encode pair.2).reverse

end LeanNPHardness.MachineAdapters
