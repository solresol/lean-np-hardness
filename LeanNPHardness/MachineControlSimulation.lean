import LeanNPHardness.MachineControl

namespace LeanNPHardness.MachineComposition

open Turing

/-- Lift a first-machine statement into the combined stack, label, and state
types while preserving `halt`. State-dependent operations are totalized with
`leftStateValue`; on a genuine left-phase state they reduce to the original
operations. -/
def liftLeftControlStmt {Γ₀ Γ₁ Γ₂ : Type}
    (first : TM2ComputableAux Γ₀ Γ₁)
    (second : TM2ComputableAux Γ₁ Γ₂) :
    TM2.Stmt first.tm.Γ first.tm.Λ first.tm.σ →
      TM2.Stmt (StackAlphabet first.tm second.tm)
        (ControlLabel first second) (ControlState first second)
  | .push k write next =>
      .push (Sum.inl k)
        (fun state => write (leftStateValue first second state))
        (liftLeftControlStmt first second next)
  | .peek k read next =>
      .peek (Sum.inl k)
        (fun state symbol =>
          leftState first second
            (read (leftStateValue first second state) symbol))
        (liftLeftControlStmt first second next)
  | .pop k read next =>
      .pop (Sum.inl k)
        (fun state symbol =>
          leftState first second
            (read (leftStateValue first second state) symbol))
        (liftLeftControlStmt first second next)
  | .load update next =>
      .load
        (fun state =>
          leftState first second
            (update (leftStateValue first second state)))
        (liftLeftControlStmt first second next)
  | .branch test yes no =>
      .branch
        (fun state => test (leftStateValue first second state))
        (liftLeftControlStmt first second yes)
        (liftLeftControlStmt first second no)
  | .goto next =>
      .goto
        (fun state =>
          leftLabel first second (next (leftStateValue first second state)))
  | .halt => .halt

/-- Embed a first-machine configuration into the combined control types. -/
def liftLeftControlCfg {Γ₀ Γ₁ Γ₂ : Type}
    (first : TM2ComputableAux Γ₀ Γ₁)
    (second : TM2ComputableAux Γ₁ Γ₂)
    (cfg : TM2.Cfg first.tm.Γ first.tm.Λ first.tm.σ) :
    TM2.Cfg (StackAlphabet first.tm second.tm)
      (ControlLabel first second) (ControlState first second) where
  l := cfg.l.map (leftLabel first second)
  var := leftState first second cfg.var
  stk := leftStacks first.tm second.tm cfg.stk

/-- Lift the first program into combined control. Non-left labels halt; they
are unreachable in the phase-preserving simulation proved below. -/
def liftLeftControlProgram {Γ₀ Γ₁ Γ₂ : Type}
    (first : TM2ComputableAux Γ₀ Γ₁)
    (second : TM2ComputableAux Γ₁ Γ₂)
    (program : first.tm.Λ → TM2.Stmt first.tm.Γ first.tm.Λ first.tm.σ) :
    ControlLabel first second →
      TM2.Stmt (StackAlphabet first.tm second.tm)
        (ControlLabel first second) (ControlState first second)
  | Sum.inl label => liftLeftControlStmt first second (program label)
  | Sum.inr _ => .halt

/-- Lifting into combined control commutes with execution of one first-machine
statement from a genuine left-phase state and stack family. -/
theorem liftLeftControl_stepAux {Γ₀ Γ₁ Γ₂ : Type}
    (first : TM2ComputableAux Γ₀ Γ₁)
    (second : TM2ComputableAux Γ₁ Γ₂)
    (stmt : TM2.Stmt first.tm.Γ first.tm.Λ first.tm.σ)
    (state : first.tm.σ)
    (contents : ∀ k, List (first.tm.Γ k)) :
    TM2.stepAux (liftLeftControlStmt first second stmt)
        (leftState first second state)
        (leftStacks first.tm second.tm contents) =
      liftLeftControlCfg first second
        (TM2.stepAux stmt state contents) := by
  induction stmt generalizing state contents with
  | push k write next ih =>
      simp only [liftLeftControlStmt, TM2.stepAux,
        leftStateValue_leftState]
      rw [← leftStacks_update]
      exact ih _ _
  | peek k read next ih =>
      simpa only [liftLeftControlStmt, TM2.stepAux,
        leftStateValue_leftState, leftStacks_inl] using
        ih (read state (contents k).head?) contents
  | pop k read next ih =>
      simp only [liftLeftControlStmt, TM2.stepAux,
        leftStateValue_leftState, leftStacks_inl]
      rw [← leftStacks_update]
      exact ih _ _
  | load update next ih =>
      simpa only [liftLeftControlStmt, TM2.stepAux,
        leftStateValue_leftState] using
        ih (update state) contents
  | branch test yes no ihYes ihNo =>
      by_cases h : test state
      · simpa only [liftLeftControlStmt, TM2.stepAux,
          leftStateValue_leftState, h, cond_true] using
          ihYes state contents
      · simpa only [liftLeftControlStmt, TM2.stepAux,
          leftStateValue_leftState, h, cond_false] using
          ihNo state contents
  | goto next =>
      rfl
  | halt =>
      rfl

/-- One step of the first program is simulated exactly after injecting its
stacks, labels, and state into the combined control types. -/
theorem liftLeftControl_step {Γ₀ Γ₁ Γ₂ : Type}
    (first : TM2ComputableAux Γ₀ Γ₁)
    (second : TM2ComputableAux Γ₁ Γ₂)
    (program : first.tm.Λ → TM2.Stmt first.tm.Γ first.tm.Λ first.tm.σ)
    (cfg : TM2.Cfg first.tm.Γ first.tm.Λ first.tm.σ) :
    TM2.step (liftLeftControlProgram first second program)
        (liftLeftControlCfg first second cfg) =
      Option.map (liftLeftControlCfg first second)
        (TM2.step program cfg) := by
  cases cfg with
  | mk label state contents =>
      cases label with
      | none =>
          rfl
      | some label =>
          simp only [liftLeftControlCfg, TM2.step,
            Option.map_some, liftLeftControlProgram, leftLabel]
          rw [liftLeftControl_stepAux]
          rfl

end LeanNPHardness.MachineComposition
