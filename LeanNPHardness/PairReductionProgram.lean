import LeanNPHardness.PairReduction

namespace LeanNPHardness.MachineAdapters

open Turing

/-- Lift a preprocessing statement to the extended pair/reduction stack
family. The statement can address only the five preprocessing stacks, so all
private reduction-machine stacks remain untouched. -/
def liftPairAdapterStmt {Γ₀ Γ₁ Δ : Type}
    (computer : TM2ComputableAux Γ₀ Γ₁) :
    TM2.Stmt (PairAdapterStackAlphabet Γ₀ Δ) (PairAdapterLabel Γ₀ Δ)
        (Option (Sum Γ₀ Δ)) →
      TM2.Stmt (PairReductionStackAlphabet computer Δ)
        (PairAdapterLabel Γ₀ Δ) (Option (Sum Γ₀ Δ))
  | .push index write next =>
      .push (Sum.inl index) write (liftPairAdapterStmt computer next)
  | .peek index read next =>
      .peek (Sum.inl index) read (liftPairAdapterStmt computer next)
  | .pop index read next =>
      .pop (Sum.inl index) read (liftPairAdapterStmt computer next)
  | .load update next =>
      .load update (liftPairAdapterStmt computer next)
  | .branch test yes no =>
      .branch test (liftPairAdapterStmt computer yes)
        (liftPairAdapterStmt computer no)
  | .goto next => .goto next
  | .halt => .halt

/-- Embed a preprocessing configuration while preserving arbitrary contents
on every private reduction-machine stack. -/
def liftPairAdapterCfg {Γ₀ Γ₁ Δ : Type}
    (computer : TM2ComputableAux Γ₀ Γ₁)
    (machineContents : ∀ index, List (computer.tm.Γ index))
    (cfg : TM2.Cfg (PairAdapterStackAlphabet Γ₀ Δ)
      (PairAdapterLabel Γ₀ Δ) (Option (Sum Γ₀ Δ))) :
    TM2.Cfg (PairReductionStackAlphabet computer Δ)
      (PairAdapterLabel Γ₀ Δ) (Option (Sum Γ₀ Δ)) where
  l := cfg.l
  var := cfg.var
  stk := pairReductionStacks computer cfg.stk machineContents

@[simp]
theorem liftPairAdapterCfg_adapter {Γ₀ Γ₁ Δ : Type}
    (computer : TM2ComputableAux Γ₀ Γ₁)
    (machineContents : ∀ index, List (computer.tm.Γ index))
    (cfg : TM2.Cfg (PairAdapterStackAlphabet Γ₀ Δ)
      (PairAdapterLabel Γ₀ Δ) (Option (Sum Γ₀ Δ)))
    (index : PairAdapterStackIndex) :
    (liftPairAdapterCfg computer machineContents cfg).stk (Sum.inl index) =
      cfg.stk index :=
  rfl

@[simp]
theorem liftPairAdapterCfg_machine {Γ₀ Γ₁ Δ : Type}
    (computer : TM2ComputableAux Γ₀ Γ₁)
    (machineContents : ∀ index, List (computer.tm.Γ index))
    (cfg : TM2.Cfg (PairAdapterStackAlphabet Γ₀ Δ)
      (PairAdapterLabel Γ₀ Δ) (Option (Sum Γ₀ Δ)))
    (index : computer.tm.K) :
    (liftPairAdapterCfg computer machineContents cfg).stk (Sum.inr index) =
      machineContents index :=
  rfl

/-- Lift the complete preprocessing program to the extended stack family. -/
def liftPairAdapterProgram {Γ₀ Γ₁ Δ : Type}
    (computer : TM2ComputableAux Γ₀ Γ₁)
    (program : PairAdapterLabel Γ₀ Δ →
      TM2.Stmt (PairAdapterStackAlphabet Γ₀ Δ) (PairAdapterLabel Γ₀ Δ)
        (Option (Sum Γ₀ Δ))) :
    PairAdapterLabel Γ₀ Δ →
      TM2.Stmt (PairReductionStackAlphabet computer Δ)
        (PairAdapterLabel Γ₀ Δ) (Option (Sum Γ₀ Δ)) :=
  fun label => liftPairAdapterStmt computer (program label)

/-- Lifting a preprocessing statement commutes with its complete execution
and preserves every private reduction-machine stack. -/
theorem liftPairAdapter_stepAux {Γ₀ Γ₁ Δ : Type}
    (computer : TM2ComputableAux Γ₀ Γ₁)
    (stmt : TM2.Stmt (PairAdapterStackAlphabet Γ₀ Δ)
      (PairAdapterLabel Γ₀ Δ) (Option (Sum Γ₀ Δ)))
    (state : Option (Sum Γ₀ Δ))
    (adapterContents :
      ∀ index, List (PairAdapterStackAlphabet Γ₀ Δ index))
    (machineContents : ∀ index, List (computer.tm.Γ index)) :
    TM2.stepAux (liftPairAdapterStmt computer stmt) state
        (pairReductionStacks computer adapterContents machineContents) =
      liftPairAdapterCfg computer machineContents
        (TM2.stepAux stmt state adapterContents) := by
  induction stmt generalizing state adapterContents with
  | push index write next ih =>
      simp only [liftPairAdapterStmt, TM2.stepAux]
      rw [← pairReductionStacks_adapter_update]
      exact ih _ _
  | peek index read next ih =>
      simpa only [liftPairAdapterStmt, TM2.stepAux,
        pairReductionStacks_adapter] using
        ih (read state (adapterContents index).head?) adapterContents
  | pop index read next ih =>
      simp only [liftPairAdapterStmt, TM2.stepAux,
        pairReductionStacks_adapter]
      rw [← pairReductionStacks_adapter_update]
      exact ih _ _
  | load update next ih =>
      simpa only [liftPairAdapterStmt, TM2.stepAux] using
        ih (update state) adapterContents
  | branch test yes no ihYes ihNo =>
      by_cases h : test state
      · simpa only [liftPairAdapterStmt, TM2.stepAux, h, cond_true] using
          ihYes state adapterContents
      · simpa only [liftPairAdapterStmt, TM2.stepAux, h, cond_false] using
          ihNo state adapterContents
  | goto next =>
      rfl
  | halt =>
      rfl

/-- One preprocessing-program step is simulated exactly in the extended
pair/reduction layout. -/
theorem liftPairAdapter_step {Γ₀ Γ₁ Δ : Type}
    (computer : TM2ComputableAux Γ₀ Γ₁)
    (program : PairAdapterLabel Γ₀ Δ →
      TM2.Stmt (PairAdapterStackAlphabet Γ₀ Δ) (PairAdapterLabel Γ₀ Δ)
        (Option (Sum Γ₀ Δ)))
    (cfg : TM2.Cfg (PairAdapterStackAlphabet Γ₀ Δ)
      (PairAdapterLabel Γ₀ Δ) (Option (Sum Γ₀ Δ)))
    (machineContents : ∀ index, List (computer.tm.Γ index)) :
    TM2.step (liftPairAdapterProgram computer program)
        (liftPairAdapterCfg computer machineContents cfg) =
      Option.map (liftPairAdapterCfg computer machineContents)
        (TM2.step program cfg) := by
  cases cfg with
  | mk label state adapterContents =>
      cases label with
      | none =>
          rfl
      | some label =>
          simp only [liftPairAdapterCfg, TM2.step,
            liftPairAdapterProgram]
          rw [liftPairAdapter_stepAux]
          rfl

/-- Every exact finite preprocessing run lifts to the extended stack family
with the same step count and unchanged private reduction-machine contents. -/
theorem liftPairAdapter_run {Γ₀ Γ₁ Δ : Type}
    (computer : TM2ComputableAux Γ₀ Γ₁)
    (program : PairAdapterLabel Γ₀ Δ →
      TM2.Stmt (PairAdapterStackAlphabet Γ₀ Δ) (PairAdapterLabel Γ₀ Δ)
        (Option (Sum Γ₀ Δ)))
    (steps : ℕ)
    (cfg : TM2.Cfg (PairAdapterStackAlphabet Γ₀ Δ)
      (PairAdapterLabel Γ₀ Δ) (Option (Sum Γ₀ Δ)))
    (machineContents : ∀ index, List (computer.tm.Γ index)) :
    (flip Option.bind (TM2.step (liftPairAdapterProgram computer program)))^[
        steps]
      (some (liftPairAdapterCfg computer machineContents cfg)) =
      Option.map (liftPairAdapterCfg computer machineContents)
        ((flip Option.bind (TM2.step program))^[steps] (some cfg)) := by
  let embed :
      Option (TM2.Cfg (PairAdapterStackAlphabet Γ₀ Δ)
        (PairAdapterLabel Γ₀ Δ) (Option (Sum Γ₀ Δ))) →
        Option (TM2.Cfg (PairReductionStackAlphabet computer Δ)
          (PairAdapterLabel Γ₀ Δ) (Option (Sum Γ₀ Δ))) :=
    Option.map (liftPairAdapterCfg (Δ := Δ) computer machineContents)
  have commute : Function.Semiconj embed
      (flip Option.bind (TM2.step program))
      (flip Option.bind
        (TM2.step (liftPairAdapterProgram computer program))) := by
    intro current
    cases current with
    | none => rfl
    | some current =>
        exact (liftPairAdapter_step computer program current
          machineContents).symm
  exact (commute.iterate_right steps (some cfg)).symm

/-- The complete tagged-pair preprocessing run executes unchanged on the
extended pair/reduction stack family. It recovers both ordered component
encodings in exactly `4 * source.length + 7` steps while preserving every
private reduction-machine stack. -/
theorem liftPairAdapter_whole_list {Γ₀ Γ₁ Δ : Type}
    (computer : TM2ComputableAux Γ₀ Γ₁)
    (state : Option (Sum Γ₀ Δ)) (source : List (Sum Γ₀ Δ))
    (machineContents : ∀ index, List (computer.tm.Γ index)) :
    (flip Option.bind
        (TM2.step (liftPairAdapterProgram computer pairAdapterProgram)))^[
        4 * source.length + 7]
      (some (liftPairAdapterCfg computer machineContents
        (pairAdapterCfg (.split .scan) state source [] [] [] []))) =
      some (liftPairAdapterCfg computer machineContents
        (pairAdapterCfg (.restore .done) none [] []
          (PairEncoding.leftSymbols source) []
          (PairEncoding.rightSymbols source))) := by
  rw [liftPairAdapter_run]
  rw [pairAdapter_whole_list]
  rfl

end LeanNPHardness.MachineAdapters
