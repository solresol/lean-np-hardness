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

/-- Finite phase-tagged labels for preprocessing a tagged pair, transferring
its left component into the reduction machine, and then running that machine.
-/
def PairReductionControlLabel {Γ₀ Γ₁ Δ : Type}
    (computer : TM2ComputableAux Γ₀ Γ₁) :=
  PairAdapterLabel Γ₀ Δ ⊕ (PairInputTransferLabel Γ₀ ⊕ computer.tm.Λ)

instance {Γ₀ Γ₁ Δ : Type} [Fintype Γ₀] [Fintype Δ]
    (computer : TM2ComputableAux Γ₀ Γ₁) :
    Fintype (PairReductionControlLabel (Δ := Δ) computer) := by
  letI : Fintype computer.tm.Λ := computer.tm.ΛFin
  exact inferInstanceAs
    (Fintype
      (PairAdapterLabel Γ₀ Δ ⊕
        (PairInputTransferLabel Γ₀ ⊕ computer.tm.Λ)))

/-- Preprocessing and input transfer share a tagged optional-symbol state.
The reduction machine occupies the other state branch once transfer ends. -/
def PairReductionControlState {Γ₀ Γ₁ Δ : Type}
    (computer : TM2ComputableAux Γ₀ Γ₁) :=
  Option (Sum Γ₀ Δ) ⊕ computer.tm.σ

instance {Γ₀ Γ₁ Δ : Type} [Fintype Γ₀] [Fintype Δ]
    (computer : TM2ComputableAux Γ₀ Γ₁) :
    Fintype (PairReductionControlState (Δ := Δ) computer) := by
  letI : Fintype computer.tm.σ := computer.tm.σFin
  exact inferInstanceAs
    (Fintype (Option (Sum Γ₀ Δ) ⊕ computer.tm.σ))

def pairAdapterControlLabel {Γ₀ Γ₁ Δ : Type}
    (computer : TM2ComputableAux Γ₀ Γ₁)
    (label : PairAdapterLabel Γ₀ Δ) :
    PairReductionControlLabel (Δ := Δ) computer :=
  Sum.inl label

def pairInputTransferControlLabel {Γ₀ Γ₁ Δ : Type}
    (computer : TM2ComputableAux Γ₀ Γ₁)
    (label : PairInputTransferLabel Γ₀) :
    PairReductionControlLabel (Δ := Δ) computer :=
  Sum.inr (Sum.inl label)

def reductionMachineControlLabel {Γ₀ Γ₁ Δ : Type}
    (computer : TM2ComputableAux Γ₀ Γ₁) (label : computer.tm.Λ) :
    PairReductionControlLabel (Δ := Δ) computer :=
  Sum.inr (Sum.inr label)

def pairAdapterControlState {Γ₀ Γ₁ Δ : Type}
    (computer : TM2ComputableAux Γ₀ Γ₁) (state : Option (Sum Γ₀ Δ)) :
    PairReductionControlState (Δ := Δ) computer :=
  Sum.inl state

def pairInputTransferControlState {Γ₀ Γ₁ Δ : Type}
    (computer : TM2ComputableAux Γ₀ Γ₁) (state : Option Γ₀) :
    PairReductionControlState (Δ := Δ) computer :=
  Sum.inl (state.map Sum.inl)

def reductionMachineControlState {Γ₀ Γ₁ Δ : Type}
    (computer : TM2ComputableAux Γ₀ Γ₁) (state : computer.tm.σ) :
    PairReductionControlState (Δ := Δ) computer :=
  Sum.inr state

def pairAdapterControlStateValue {Γ₀ Γ₁ Δ : Type}
    (computer : TM2ComputableAux Γ₀ Γ₁) :
    PairReductionControlState (Δ := Δ) computer → Option (Sum Γ₀ Δ)
  | Sum.inl state => state
  | Sum.inr _ => none

def pairInputTransferControlStateValue {Γ₀ Γ₁ Δ : Type}
    (computer : TM2ComputableAux Γ₀ Γ₁) :
    PairReductionControlState (Δ := Δ) computer → Option Γ₀
  | Sum.inl (some (Sum.inl symbol)) => some symbol
  | _ => none

def reductionMachineControlStateValue {Γ₀ Γ₁ Δ : Type}
    (computer : TM2ComputableAux Γ₀ Γ₁) :
    PairReductionControlState (Δ := Δ) computer → computer.tm.σ
  | Sum.inr state => state
  | Sum.inl _ => computer.tm.initialState

@[simp]
theorem pairAdapterControlStateValue_adapter {Γ₀ Γ₁ Δ : Type}
    (computer : TM2ComputableAux Γ₀ Γ₁) (state : Option (Sum Γ₀ Δ)) :
    pairAdapterControlStateValue computer
        (pairAdapterControlState computer state) = state :=
  rfl

@[simp]
theorem pairInputTransferControlStateValue_transfer {Γ₀ Γ₁ Δ : Type}
    (computer : TM2ComputableAux Γ₀ Γ₁) (state : Option Γ₀) :
    pairInputTransferControlStateValue computer
        (pairInputTransferControlState (Δ := Δ) computer state) = state := by
  cases state <;> rfl

@[simp]
theorem reductionMachineControlStateValue_machine {Γ₀ Γ₁ Δ : Type}
    (computer : TM2ComputableAux Γ₀ Γ₁) (state : computer.tm.σ) :
    reductionMachineControlStateValue (Δ := Δ) computer
        (reductionMachineControlState computer state) = state :=
  rfl

/-- Lift preprocessing control to the total dispatcher. A reached halt is
redirected to the ordered-input transfer entry label. -/
def liftPairAdapterThenTransferStmt {Γ₀ Γ₁ Δ : Type}
    (computer : TM2ComputableAux Γ₀ Γ₁) :
    TM2.Stmt (PairReductionStackAlphabet computer Δ)
        (PairAdapterLabel Γ₀ Δ) (Option (Sum Γ₀ Δ)) →
      TM2.Stmt (PairReductionStackAlphabet computer Δ)
        (PairReductionControlLabel (Δ := Δ) computer)
        (PairReductionControlState (Δ := Δ) computer)
  | .push index write next =>
      .push index
        (fun state => write (pairAdapterControlStateValue computer state))
        (liftPairAdapterThenTransferStmt computer next)
  | .peek index read next =>
      .peek index
        (fun state symbol => pairAdapterControlState computer
          (read (pairAdapterControlStateValue computer state) symbol))
        (liftPairAdapterThenTransferStmt computer next)
  | .pop index read next =>
      .pop index
        (fun state symbol => pairAdapterControlState computer
          (read (pairAdapterControlStateValue computer state) symbol))
        (liftPairAdapterThenTransferStmt computer next)
  | .load update next =>
      .load
        (fun state => pairAdapterControlState computer
          (update (pairAdapterControlStateValue computer state)))
        (liftPairAdapterThenTransferStmt computer next)
  | .branch test yes no =>
      .branch
        (fun state => test (pairAdapterControlStateValue computer state))
        (liftPairAdapterThenTransferStmt computer yes)
        (liftPairAdapterThenTransferStmt computer no)
  | .goto next =>
      .goto (fun state => pairAdapterControlLabel computer
        (next (pairAdapterControlStateValue computer state)))
  | .halt =>
      .goto (fun _ => pairInputTransferControlLabel computer .reverseScan)

/-- Lift input-transfer control to the total dispatcher. A reached halt loads
the reduction machine's declared initial state and enters its main label. -/
def liftPairInputTransferThenReductionStmt {Γ₀ Γ₁ Δ : Type}
    (computer : TM2ComputableAux Γ₀ Γ₁) :
    TM2.Stmt (PairReductionStackAlphabet computer Δ)
        (PairInputTransferLabel Γ₀) (Option Γ₀) →
      TM2.Stmt (PairReductionStackAlphabet computer Δ)
        (PairReductionControlLabel (Δ := Δ) computer)
        (PairReductionControlState (Δ := Δ) computer)
  | .push index write next =>
      .push index
        (fun state => write (pairInputTransferControlStateValue computer state))
        (liftPairInputTransferThenReductionStmt computer next)
  | .peek index read next =>
      .peek index
        (fun state symbol => pairInputTransferControlState computer
          (read (pairInputTransferControlStateValue computer state) symbol))
        (liftPairInputTransferThenReductionStmt computer next)
  | .pop index read next =>
      .pop index
        (fun state symbol => pairInputTransferControlState computer
          (read (pairInputTransferControlStateValue computer state) symbol))
        (liftPairInputTransferThenReductionStmt computer next)
  | .load update next =>
      .load
        (fun state => pairInputTransferControlState computer
          (update (pairInputTransferControlStateValue computer state)))
        (liftPairInputTransferThenReductionStmt computer next)
  | .branch test yes no =>
      .branch
        (fun state => test
          (pairInputTransferControlStateValue computer state))
        (liftPairInputTransferThenReductionStmt computer yes)
        (liftPairInputTransferThenReductionStmt computer no)
  | .goto next =>
      .goto (fun state => pairInputTransferControlLabel computer
        (next (pairInputTransferControlStateValue computer state)))
  | .halt =>
      .load (fun _ => reductionMachineControlState computer
          computer.tm.initialState)
        (.goto (fun _ => reductionMachineControlLabel computer
          computer.tm.main))

/-- Lift reduction-machine control to the total dispatcher while preserving
the reduction machine's eventual halt. -/
def liftReductionMachineControlStmt {Γ₀ Γ₁ Δ : Type}
    (computer : TM2ComputableAux Γ₀ Γ₁) :
    TM2.Stmt (PairReductionStackAlphabet computer Δ)
        computer.tm.Λ computer.tm.σ →
      TM2.Stmt (PairReductionStackAlphabet computer Δ)
        (PairReductionControlLabel (Δ := Δ) computer)
        (PairReductionControlState (Δ := Δ) computer)
  | .push index write next =>
      .push index
        (fun state => write (reductionMachineControlStateValue computer state))
        (liftReductionMachineControlStmt computer next)
  | .peek index read next =>
      .peek index
        (fun state symbol => reductionMachineControlState computer
          (read (reductionMachineControlStateValue computer state) symbol))
        (liftReductionMachineControlStmt computer next)
  | .pop index read next =>
      .pop index
        (fun state symbol => reductionMachineControlState computer
          (read (reductionMachineControlStateValue computer state) symbol))
        (liftReductionMachineControlStmt computer next)
  | .load update next =>
      .load
        (fun state => reductionMachineControlState computer
          (update (reductionMachineControlStateValue computer state)))
        (liftReductionMachineControlStmt computer next)
  | .branch test yes no =>
      .branch
        (fun state => test (reductionMachineControlStateValue computer state))
        (liftReductionMachineControlStmt computer yes)
        (liftReductionMachineControlStmt computer no)
  | .goto next =>
      .goto (fun state => reductionMachineControlLabel computer
        (next (reductionMachineControlStateValue computer state)))
  | .halt => .halt

/-- One total dispatcher over the extended pair/reduction stack layout. -/
def pairReductionProgram {Γ₀ Γ₁ Δ : Type}
    (computer : TM2ComputableAux Γ₀ Γ₁) :
    PairReductionControlLabel (Δ := Δ) computer →
      TM2.Stmt (PairReductionStackAlphabet computer Δ)
        (PairReductionControlLabel (Δ := Δ) computer)
        (PairReductionControlState (Δ := Δ) computer)
  | Sum.inl label =>
      liftPairAdapterThenTransferStmt computer
        (liftPairAdapterProgram computer pairAdapterProgram label)
  | Sum.inr (Sum.inl label) =>
      liftPairInputTransferThenReductionStmt computer
        (pairInputTransferProgram computer label)
  | Sum.inr (Sum.inr label) =>
      liftReductionMachineControlStmt computer
        (liftReductionProgram computer computer.tm.m label)

/-- Embed a preprocessing configuration into the total control. A halted
preprocessing configuration denotes the input-transfer entry point. -/
def liftPairAdapterThenTransferCfg {Γ₀ Γ₁ Δ : Type}
    (computer : TM2ComputableAux Γ₀ Γ₁)
    (cfg : TM2.Cfg (PairReductionStackAlphabet computer Δ)
      (PairAdapterLabel Γ₀ Δ) (Option (Sum Γ₀ Δ))) :
    TM2.Cfg (PairReductionStackAlphabet computer Δ)
      (PairReductionControlLabel (Δ := Δ) computer)
      (PairReductionControlState (Δ := Δ) computer) where
  l := some (cfg.l.elim
    (pairInputTransferControlLabel computer .reverseScan)
    (pairAdapterControlLabel computer))
  var := pairAdapterControlState computer cfg.var
  stk := cfg.stk

/-- Embed an input-transfer configuration into total control. A halted
transfer configuration denotes the reduction machine's initial control. -/
def liftPairInputTransferThenReductionCfg {Γ₀ Γ₁ Δ : Type}
    (computer : TM2ComputableAux Γ₀ Γ₁)
    (cfg : TM2.Cfg (PairReductionStackAlphabet computer Δ)
      (PairInputTransferLabel Γ₀) (Option Γ₀)) :
    TM2.Cfg (PairReductionStackAlphabet computer Δ)
      (PairReductionControlLabel (Δ := Δ) computer)
      (PairReductionControlState (Δ := Δ) computer) where
  l := some (cfg.l.elim
    (reductionMachineControlLabel computer computer.tm.main)
    (pairInputTransferControlLabel computer))
  var := cfg.l.elim
    (reductionMachineControlState computer computer.tm.initialState)
    (fun _ => pairInputTransferControlState computer cfg.var)
  stk := cfg.stk

/-- Embed a running or halted reduction-machine configuration into total
control. -/
def liftReductionMachineControlCfg {Γ₀ Γ₁ Δ : Type}
    (computer : TM2ComputableAux Γ₀ Γ₁)
    (cfg : TM2.Cfg (PairReductionStackAlphabet computer Δ)
      computer.tm.Λ computer.tm.σ) :
    TM2.Cfg (PairReductionStackAlphabet computer Δ)
      (PairReductionControlLabel (Δ := Δ) computer)
      (PairReductionControlState (Δ := Δ) computer) where
  l := cfg.l.map (reductionMachineControlLabel computer)
  var := reductionMachineControlState computer cfg.var
  stk := cfg.stk

/-- Preprocessing statement execution commutes with the total-control lift,
including the reached-halt transition into input transfer. -/
theorem liftPairAdapterThenTransfer_stepAux {Γ₀ Γ₁ Δ : Type}
    (computer : TM2ComputableAux Γ₀ Γ₁)
    (stmt : TM2.Stmt (PairReductionStackAlphabet computer Δ)
      (PairAdapterLabel Γ₀ Δ) (Option (Sum Γ₀ Δ)))
    (state : Option (Sum Γ₀ Δ))
    (contents : ∀ index,
      List (PairReductionStackAlphabet computer Δ index)) :
    TM2.stepAux (liftPairAdapterThenTransferStmt computer stmt)
        (pairAdapterControlState computer state) contents =
      liftPairAdapterThenTransferCfg computer
        (TM2.stepAux stmt state contents) := by
  induction stmt generalizing state contents with
  | push index write next ih =>
      simpa only [liftPairAdapterThenTransferStmt, TM2.stepAux,
        pairAdapterControlStateValue_adapter] using ih state _
  | peek index read next ih =>
      simpa only [liftPairAdapterThenTransferStmt, TM2.stepAux,
        pairAdapterControlStateValue_adapter] using
        ih (read state (contents index).head?) contents
  | pop index read next ih =>
      simpa only [liftPairAdapterThenTransferStmt, TM2.stepAux,
        pairAdapterControlStateValue_adapter] using
        ih (read state (contents index).head?) _
  | load update next ih =>
      simpa only [liftPairAdapterThenTransferStmt, TM2.stepAux,
        pairAdapterControlStateValue_adapter] using ih (update state) contents
  | branch test yes no ihYes ihNo =>
      by_cases h : test state
      · simpa only [liftPairAdapterThenTransferStmt, TM2.stepAux,
          pairAdapterControlStateValue_adapter, h, cond_true] using
          ihYes state contents
      · simpa only [liftPairAdapterThenTransferStmt, TM2.stepAux,
          pairAdapterControlStateValue_adapter, h, cond_false] using
          ihNo state contents
  | goto next =>
      rfl
  | halt =>
      rfl

/-- One live preprocessing-label step is reproduced by the total dispatcher.
-/
theorem pairReductionProgram_adapter_step {Γ₀ Γ₁ Δ : Type}
    (computer : TM2ComputableAux Γ₀ Γ₁)
    (label : PairAdapterLabel Γ₀ Δ) (state : Option (Sum Γ₀ Δ))
    (contents : ∀ index,
      List (PairReductionStackAlphabet computer Δ index)) :
    TM2.step (pairReductionProgram computer)
        (liftPairAdapterThenTransferCfg computer
          (TM2.Cfg.mk (some label) state contents)) =
      some (liftPairAdapterThenTransferCfg computer
        (TM2.stepAux
          (liftPairAdapterProgram computer pairAdapterProgram label)
          state contents)) := by
  change some (TM2.stepAux
    (liftPairAdapterThenTransferStmt computer
      (liftPairAdapterProgram computer pairAdapterProgram label))
    (pairAdapterControlState computer state) contents) = _
  rw [liftPairAdapterThenTransfer_stepAux]

/-- Input-transfer execution commutes with the total-control lift, including
the reached-halt transition into the reduction machine's initial control. -/
theorem liftPairInputTransferThenReduction_stepAux {Γ₀ Γ₁ Δ : Type}
    (computer : TM2ComputableAux Γ₀ Γ₁)
    (stmt : TM2.Stmt (PairReductionStackAlphabet computer Δ)
      (PairInputTransferLabel Γ₀) (Option Γ₀))
    (state : Option Γ₀)
    (contents : ∀ index,
      List (PairReductionStackAlphabet computer Δ index)) :
    TM2.stepAux (liftPairInputTransferThenReductionStmt computer stmt)
        (pairInputTransferControlState computer state) contents =
      liftPairInputTransferThenReductionCfg computer
        (TM2.stepAux stmt state contents) := by
  induction stmt generalizing state contents with
  | push index write next ih =>
      simpa only [liftPairInputTransferThenReductionStmt, TM2.stepAux,
        pairInputTransferControlStateValue_transfer] using ih state _
  | peek index read next ih =>
      simpa only [liftPairInputTransferThenReductionStmt, TM2.stepAux,
        pairInputTransferControlStateValue_transfer] using
        ih (read state (contents index).head?) contents
  | pop index read next ih =>
      simpa only [liftPairInputTransferThenReductionStmt, TM2.stepAux,
        pairInputTransferControlStateValue_transfer] using
        ih (read state (contents index).head?) _
  | load update next ih =>
      simpa only [liftPairInputTransferThenReductionStmt, TM2.stepAux,
        pairInputTransferControlStateValue_transfer] using
        ih (update state) contents
  | branch test yes no ihYes ihNo =>
      by_cases h : test state
      · simpa only [liftPairInputTransferThenReductionStmt, TM2.stepAux,
          pairInputTransferControlStateValue_transfer, h, cond_true] using
          ihYes state contents
      · simpa only [liftPairInputTransferThenReductionStmt, TM2.stepAux,
          pairInputTransferControlStateValue_transfer, h, cond_false] using
          ihNo state contents
  | goto next =>
      simp only [liftPairInputTransferThenReductionStmt, TM2.stepAux,
        pairInputTransferControlStateValue_transfer,
        liftPairInputTransferThenReductionCfg, Option.elim_some]
  | halt =>
      rfl

/-- One live input-transfer-label step is reproduced by the total dispatcher.
-/
theorem pairReductionProgram_transfer_step {Γ₀ Γ₁ Δ : Type}
    (computer : TM2ComputableAux Γ₀ Γ₁)
    (label : PairInputTransferLabel Γ₀) (state : Option Γ₀)
    (contents : ∀ index,
      List (PairReductionStackAlphabet computer Δ index)) :
    TM2.step (pairReductionProgram computer)
        (liftPairInputTransferThenReductionCfg computer
          (TM2.Cfg.mk (some label) state contents)) =
      some (liftPairInputTransferThenReductionCfg computer
        (TM2.stepAux (pairInputTransferProgram computer label)
          state contents)) := by
  change some (TM2.stepAux
    (liftPairInputTransferThenReductionStmt computer
      (pairInputTransferProgram computer label))
    (pairInputTransferControlState computer state) contents) = _
  rw [liftPairInputTransferThenReduction_stepAux]

/-- Reduction-machine execution commutes exactly with the total-control lift.
-/
theorem liftReductionMachineControl_stepAux {Γ₀ Γ₁ Δ : Type}
    (computer : TM2ComputableAux Γ₀ Γ₁)
    (stmt : TM2.Stmt (PairReductionStackAlphabet computer Δ)
      computer.tm.Λ computer.tm.σ)
    (state : computer.tm.σ)
    (contents : ∀ index,
      List (PairReductionStackAlphabet computer Δ index)) :
    TM2.stepAux (liftReductionMachineControlStmt computer stmt)
        (reductionMachineControlState computer state) contents =
      liftReductionMachineControlCfg computer
        (TM2.stepAux stmt state contents) := by
  induction stmt generalizing state contents with
  | push index write next ih =>
      simpa only [liftReductionMachineControlStmt, TM2.stepAux,
        reductionMachineControlStateValue_machine] using ih state _
  | peek index read next ih =>
      simpa only [liftReductionMachineControlStmt, TM2.stepAux,
        reductionMachineControlStateValue_machine] using
        ih (read state (contents index).head?) contents
  | pop index read next ih =>
      simpa only [liftReductionMachineControlStmt, TM2.stepAux,
        reductionMachineControlStateValue_machine] using
        ih (read state (contents index).head?) _
  | load update next ih =>
      simpa only [liftReductionMachineControlStmt, TM2.stepAux,
        reductionMachineControlStateValue_machine] using
        ih (update state) contents
  | branch test yes no ihYes ihNo =>
      by_cases h : test state
      · simpa only [liftReductionMachineControlStmt, TM2.stepAux,
          reductionMachineControlStateValue_machine, h, cond_true] using
          ihYes state contents
      · simpa only [liftReductionMachineControlStmt, TM2.stepAux,
          reductionMachineControlStateValue_machine, h, cond_false] using
          ihNo state contents
  | goto next =>
      rfl
  | halt =>
      rfl

/-- One live reduction-machine-label step is reproduced by the total
dispatcher. -/
theorem pairReductionProgram_machine_step {Γ₀ Γ₁ Δ : Type}
    (computer : TM2ComputableAux Γ₀ Γ₁) (label : computer.tm.Λ)
    (state : computer.tm.σ)
    (contents : ∀ index,
      List (PairReductionStackAlphabet computer Δ index)) :
    TM2.step (pairReductionProgram computer)
        (liftReductionMachineControlCfg computer
          (TM2.Cfg.mk (some label) state contents)) =
      some (liftReductionMachineControlCfg computer
        (TM2.stepAux (liftReductionProgram computer computer.tm.m label)
          state contents)) := by
  change some (TM2.stepAux
    (liftReductionMachineControlStmt computer
      (liftReductionProgram computer computer.tm.m label))
    (reductionMachineControlState computer state) contents) = _
  rw [liftReductionMachineControl_stepAux]

private theorem pairReduction_iterate_bind_none {α : Type}
    (step : α → Option α) (steps : ℕ) :
    (flip Option.bind step)^[steps] none = none := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
      rw [Function.iterate_succ_apply]
      exact ih

/-- One reduction-machine step is reproduced by the total dispatcher while
all five preprocessing stacks remain unchanged. In particular, the ordered
certificate is preserved explicitly by the fixed `adapterContents` argument.
-/
theorem pairReductionProgram_machine_step_preserving_adapter
    {Γ₀ Γ₁ Δ : Type} (computer : TM2ComputableAux Γ₀ Γ₁)
    (adapterContents :
      ∀ index, List (PairAdapterStackAlphabet Γ₀ Δ index))
    (cfg : TM2.Cfg computer.tm.Γ computer.tm.Λ computer.tm.σ) :
    TM2.step (pairReductionProgram computer)
        (liftReductionMachineControlCfg computer
          (liftReductionCfg computer adapterContents cfg)) =
      Option.map
        (fun nextCfg => liftReductionMachineControlCfg computer
          (liftReductionCfg computer adapterContents nextCfg))
        (TM2.step computer.tm.m cfg) := by
  cases cfg with
  | mk label state machineContents =>
      cases label with
      | none =>
          rfl
      | some label =>
          change TM2.step (pairReductionProgram computer)
              (liftReductionMachineControlCfg computer
                (TM2.Cfg.mk (some label) state
                  (pairReductionStacks computer adapterContents
                    machineContents))) = _
          rw [pairReductionProgram_machine_step]
          simp only [liftReductionProgram]
          rw [liftReduction_stepAux]
          rfl

/-- Any exact finite reduction-machine run is reproduced by the total
dispatcher with the same step count, preserving all five adapter stacks.
-/
theorem pairReductionProgram_machine_run {Γ₀ Γ₁ Δ : Type}
    (computer : TM2ComputableAux Γ₀ Γ₁) (steps : ℕ)
    (cfg finalCfg : TM2.Cfg computer.tm.Γ computer.tm.Λ computer.tm.σ)
    (adapterContents :
      ∀ index, List (PairAdapterStackAlphabet Γ₀ Δ index))
    (run :
      (flip Option.bind (TM2.step computer.tm.m))^[steps] (some cfg) =
        some finalCfg) :
    (flip Option.bind (TM2.step (pairReductionProgram computer)))^[steps]
        (some (liftReductionMachineControlCfg computer
          (liftReductionCfg computer adapterContents cfg))) =
      some (liftReductionMachineControlCfg computer
        (liftReductionCfg computer adapterContents finalCfg)) := by
  induction steps generalizing cfg with
  | zero =>
      simp only [Function.iterate_zero_apply, Option.some.injEq] at run ⊢
      subst finalCfg
      rfl
  | succ steps ih =>
      rw [Function.iterate_succ_apply] at run ⊢
      change
        (flip Option.bind (TM2.step computer.tm.m))^[steps]
            (TM2.step computer.tm.m cfg) = some finalCfg at run
      change
        (flip Option.bind (TM2.step (pairReductionProgram computer)))^[steps]
            (TM2.step (pairReductionProgram computer)
              (liftReductionMachineControlCfg computer
                (liftReductionCfg computer adapterContents cfg))) =
          some (liftReductionMachineControlCfg computer
            (liftReductionCfg computer adapterContents finalCfg))
      rw [pairReductionProgram_machine_step_preserving_adapter]
      cases hstep : TM2.step computer.tm.m cfg with
      | none =>
          rw [hstep] at run
          rw [pairReduction_iterate_bind_none] at run
          contradiction
      | some stepped =>
          simp only [Option.map_some]
          rw [hstep] at run
          exact ih stepped run

/-- Package an exact reduction-machine execution witness under the total
dispatcher without changing its step count or any adapter stack.
-/
def pairReductionProgram_machine_evalsTo {Γ₀ Γ₁ Δ : Type}
    (computer : TM2ComputableAux Γ₀ Γ₁)
    (cfg finalCfg : TM2.Cfg computer.tm.Γ computer.tm.Λ computer.tm.σ)
    (adapterContents :
      ∀ index, List (PairAdapterStackAlphabet Γ₀ Δ index))
    (run : EvalsTo (TM2.step computer.tm.m) cfg (some finalCfg)) :
    EvalsTo (TM2.step (pairReductionProgram computer))
      (liftReductionMachineControlCfg computer
        (liftReductionCfg computer adapterContents cfg))
      (some (liftReductionMachineControlCfg computer
        (liftReductionCfg computer adapterContents finalCfg))) where
  steps := run.steps
  evals_in_steps :=
    pairReductionProgram_machine_run computer run.steps cfg finalCfg
      adapterContents run.evals_in_steps

/-- Any exact finite preprocessing run is reproduced by the total dispatcher.
The final configuration is not stepped, so it may still carry the standalone
preprocessing program's `done` label. -/
theorem pairReductionProgram_adapter_run {Γ₀ Γ₁ Δ : Type}
    (computer : TM2ComputableAux Γ₀ Γ₁) (steps : ℕ)
    (cfg finalCfg : TM2.Cfg (PairReductionStackAlphabet computer Δ)
      (PairAdapterLabel Γ₀ Δ) (Option (Sum Γ₀ Δ)))
    (run :
      (flip Option.bind
        (TM2.step (liftPairAdapterProgram computer pairAdapterProgram)))^[
          steps] (some cfg) = some finalCfg) :
    (flip Option.bind (TM2.step (pairReductionProgram computer)))^[steps]
        (some (liftPairAdapterThenTransferCfg computer cfg)) =
      some (liftPairAdapterThenTransferCfg computer finalCfg) := by
  induction steps generalizing cfg with
  | zero =>
      simp only [Function.iterate_zero_apply, Option.some.injEq] at run ⊢
      subst finalCfg
      rfl
  | succ steps ih =>
      rw [Function.iterate_succ_apply] at run ⊢
      cases cfg with
      | mk label state contents =>
          cases label with
          | none =>
              simp only [flip, Option.bind_some, TM2.step] at run
              rw [pairReduction_iterate_bind_none] at run
              contradiction
          | some label =>
              simp only [flip, Option.bind_some, TM2.step] at run
              change
                (flip Option.bind
                    (TM2.step (pairReductionProgram computer)))^[steps]
                    (TM2.step (pairReductionProgram computer)
                      (liftPairAdapterThenTransferCfg computer
                        (TM2.Cfg.mk (some label) state contents))) =
                  some (liftPairAdapterThenTransferCfg computer finalCfg)
              rw [pairReductionProgram_adapter_step]
              exact ih _ run

/-- Any exact finite input-transfer run is reproduced by the total dispatcher.
The final standalone `done` label remains available for the checked boundary
step into reduction-machine control. -/
theorem pairReductionProgram_transfer_run {Γ₀ Γ₁ Δ : Type}
    (computer : TM2ComputableAux Γ₀ Γ₁) (steps : ℕ)
    (cfg finalCfg : TM2.Cfg (PairReductionStackAlphabet computer Δ)
      (PairInputTransferLabel Γ₀) (Option Γ₀))
    (run :
      (flip Option.bind (TM2.step (pairInputTransferProgram computer)))^[
        steps] (some cfg) = some finalCfg) :
    (flip Option.bind (TM2.step (pairReductionProgram computer)))^[steps]
        (some (liftPairInputTransferThenReductionCfg computer cfg)) =
      some (liftPairInputTransferThenReductionCfg computer finalCfg) := by
  induction steps generalizing cfg with
  | zero =>
      simp only [Function.iterate_zero_apply, Option.some.injEq] at run ⊢
      subst finalCfg
      rfl
  | succ steps ih =>
      rw [Function.iterate_succ_apply] at run ⊢
      cases cfg with
      | mk label state contents =>
          cases label with
          | none =>
              simp only [flip, Option.bind_some, TM2.step] at run
              rw [pairReduction_iterate_bind_none] at run
              contradiction
          | some label =>
              simp only [flip, Option.bind_some, TM2.step] at run
              change
                (flip Option.bind
                    (TM2.step (pairReductionProgram computer)))^[steps]
                    (TM2.step (pairReductionProgram computer)
                      (liftPairInputTransferThenReductionCfg computer
                        (TM2.Cfg.mk (some label) state contents))) =
                  some
                    (liftPairInputTransferThenReductionCfg computer finalCfg)
              rw [pairReductionProgram_transfer_step]
              exact ih _ run

/-- The preprocessing `done` label crosses into ordered-input transfer in one
total-dispatcher step without changing any stack. -/
theorem pairReductionProgram_adapter_done_step {Γ₀ Γ₁ Δ : Type}
    (computer : TM2ComputableAux Γ₀ Γ₁)
    (contents : ∀ index,
      List (PairReductionStackAlphabet computer Δ index)) :
    TM2.step (pairReductionProgram computer)
        (liftPairAdapterThenTransferCfg computer
          (TM2.Cfg.mk (some (.restore .done)) none contents)) =
      some (liftPairInputTransferThenReductionCfg computer
        (TM2.Cfg.mk (some .reverseScan) none contents)) := by
  rw [pairReductionProgram_adapter_step]
  rfl

/-- The input-transfer `done` label crosses into the reduction machine's main
label and declared initial state in one total-dispatcher step. -/
theorem pairReductionProgram_transfer_done_step {Γ₀ Γ₁ Δ : Type}
    (computer : TM2ComputableAux Γ₀ Γ₁)
    (contents : ∀ index,
      List (PairReductionStackAlphabet computer Δ index)) :
    TM2.step (pairReductionProgram computer)
        (liftPairInputTransferThenReductionCfg computer
          (TM2.Cfg.mk (some .done) none contents)) =
      some (liftReductionMachineControlCfg computer
        (TM2.Cfg.mk (some computer.tm.main) computer.tm.initialState
          contents)) := by
  rw [pairReductionProgram_transfer_step]
  rfl

/-- The total dispatcher preprocesses an arbitrary tagged pair, transfers its
left projection in order into the reduction machine's private input stack,
preserves the right projection as the ordered certificate, and enters the
reduction machine's declared initial control. The exact cost is linear in the
tagged source and its left projection. -/
theorem pairReductionProgram_preprocess_transfer_whole_list
    {Γ₀ Γ₁ Δ : Type} (computer : TM2ComputableAux Γ₀ Γ₁)
    (source : List (Sum Γ₀ Δ))
    (machineContents : ∀ index, List (computer.tm.Γ index)) :
    (flip Option.bind (TM2.step (pairReductionProgram computer)))^[
        4 * source.length +
          4 * (PairEncoding.leftSymbols source).length + 13]
      (some (liftPairAdapterThenTransferCfg computer
        (liftPairAdapterCfg computer machineContents
          (pairAdapterCfg (.split .scan) none source [] [] [] [])))) =
      some (liftReductionMachineControlCfg computer
        (TM2.Cfg.mk (some computer.tm.main) computer.tm.initialState
          (pairReductionStacks computer
            (pairAdapterStacks [] [] [] []
              (PairEncoding.rightSymbols source))
            (Function.update machineContents computer.tm.k₀
              ((PairEncoding.leftSymbols source).map
                  computer.inputAlphabet.symm ++
                machineContents computer.tm.k₀))))) := by
  have preprocessRun :
      (flip Option.bind (TM2.step (pairReductionProgram computer)))^[
          4 * source.length + 7]
        (some (liftPairAdapterThenTransferCfg computer
          (liftPairAdapterCfg computer machineContents
            (pairAdapterCfg (.split .scan) none source [] [] [] [])))) =
        some (liftPairAdapterThenTransferCfg computer
          (liftPairAdapterCfg computer machineContents
            (pairAdapterCfg (.restore .done) none [] []
              (PairEncoding.leftSymbols source) []
              (PairEncoding.rightSymbols source)))) :=
    pairReductionProgram_adapter_run computer (4 * source.length + 7)
      _ _ (liftPairAdapter_whole_list computer none source machineContents)
  have preprocessBridge :
      (flip Option.bind (TM2.step (pairReductionProgram computer)))^[1]
        (some (liftPairAdapterThenTransferCfg computer
          (liftPairAdapterCfg computer machineContents
            (pairAdapterCfg (.restore .done) none [] []
              (PairEncoding.leftSymbols source) []
              (PairEncoding.rightSymbols source))))) =
        some (liftPairInputTransferThenReductionCfg computer
          (pairInputTransferCfg computer .reverseScan none [] []
            (PairEncoding.leftSymbols source) []
            (PairEncoding.rightSymbols source) machineContents)) := by
    simpa [Function.iterate_succ_apply', liftPairAdapterCfg,
      pairAdapterCfg, pairInputTransferCfg] using
      pairReductionProgram_adapter_done_step computer
        (pairReductionStacks computer
          (pairAdapterStacks [] [] (PairEncoding.leftSymbols source) []
            (PairEncoding.rightSymbols source)) machineContents)
  have transferRun :
      (flip Option.bind (TM2.step (pairReductionProgram computer)))^[
          4 * (PairEncoding.leftSymbols source).length + 4]
        (some (liftPairInputTransferThenReductionCfg computer
          (pairInputTransferCfg computer .reverseScan none [] []
            (PairEncoding.leftSymbols source) []
            (PairEncoding.rightSymbols source) machineContents))) =
        some (liftPairInputTransferThenReductionCfg computer
          (pairInputTransferCfg computer .done none [] [] [] []
            (PairEncoding.rightSymbols source)
            (Function.update machineContents computer.tm.k₀
              ((PairEncoding.leftSymbols source).map
                  computer.inputAlphabet.symm ++
                machineContents computer.tm.k₀)))) :=
    pairReductionProgram_transfer_run computer
      (4 * (PairEncoding.leftSymbols source).length + 4) _ _
      (pairInputTransfer_whole_list computer none []
        (PairEncoding.leftSymbols source) []
        (PairEncoding.rightSymbols source) machineContents)
  have machineBridge :
      (flip Option.bind (TM2.step (pairReductionProgram computer)))^[1]
        (some (liftPairInputTransferThenReductionCfg computer
          (pairInputTransferCfg computer .done none [] [] [] []
            (PairEncoding.rightSymbols source)
            (Function.update machineContents computer.tm.k₀
              ((PairEncoding.leftSymbols source).map
                  computer.inputAlphabet.symm ++
                machineContents computer.tm.k₀))))) =
        some (liftReductionMachineControlCfg computer
          (TM2.Cfg.mk (some computer.tm.main) computer.tm.initialState
            (pairReductionStacks computer
              (pairAdapterStacks [] [] [] []
                (PairEncoding.rightSymbols source))
              (Function.update machineContents computer.tm.k₀
                ((PairEncoding.leftSymbols source).map
                    computer.inputAlphabet.symm ++
                  machineContents computer.tm.k₀))))) := by
    simpa [Function.iterate_succ_apply', pairInputTransferCfg] using
      pairReductionProgram_transfer_done_step computer
        (pairReductionStacks computer
          (pairAdapterStacks [] [] [] []
            (PairEncoding.rightSymbols source))
          (Function.update machineContents computer.tm.k₀
            ((PairEncoding.leftSymbols source).map
                computer.inputAlphabet.symm ++
              machineContents computer.tm.k₀)))
  have stepCount :
      4 * source.length +
          4 * (PairEncoding.leftSymbols source).length + 13 =
        1 + ((4 * (PairEncoding.leftSymbols source).length + 4) +
          (1 + (4 * source.length + 7))) := by
    omega
  rw [stepCount]
  rw [Function.iterate_add_apply
    (flip Option.bind (TM2.step (pairReductionProgram computer))) 1
    ((4 * (PairEncoding.leftSymbols source).length + 4) +
      (1 + (4 * source.length + 7)))]
  rw [Function.iterate_add_apply
    (flip Option.bind (TM2.step (pairReductionProgram computer)))
    (4 * (PairEncoding.leftSymbols source).length + 4)
    (1 + (4 * source.length + 7))]
  rw [Function.iterate_add_apply
    (flip Option.bind (TM2.step (pairReductionProgram computer))) 1
    (4 * source.length + 7)]
  rw [preprocessRun, preprocessBridge, transferRun, machineBridge]

end LeanNPHardness.MachineAdapters
