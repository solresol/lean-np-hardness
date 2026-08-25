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

end LeanNPHardness.MachineAdapters
