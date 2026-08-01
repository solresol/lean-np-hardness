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

/-- Lift a second-machine statement into the combined stack, label, and state
types while preserving `halt`. State-dependent operations are totalized with
`rightStateValue`; on a genuine right-phase state they reduce to the original
operations. -/
def liftRightControlStmt {Γ₀ Γ₁ Γ₂ : Type}
    (first : TM2ComputableAux Γ₀ Γ₁)
    (second : TM2ComputableAux Γ₁ Γ₂) :
    TM2.Stmt second.tm.Γ second.tm.Λ second.tm.σ →
      TM2.Stmt (StackAlphabet first.tm second.tm)
        (ControlLabel first second) (ControlState first second)
  | .push k write next =>
      .push (Sum.inr k)
        (fun state => write (rightStateValue first second state))
        (liftRightControlStmt first second next)
  | .peek k read next =>
      .peek (Sum.inr k)
        (fun state symbol =>
          rightState first second
            (read (rightStateValue first second state) symbol))
        (liftRightControlStmt first second next)
  | .pop k read next =>
      .pop (Sum.inr k)
        (fun state symbol =>
          rightState first second
            (read (rightStateValue first second state) symbol))
        (liftRightControlStmt first second next)
  | .load update next =>
      .load
        (fun state =>
          rightState first second
            (update (rightStateValue first second state)))
        (liftRightControlStmt first second next)
  | .branch test yes no =>
      .branch
        (fun state => test (rightStateValue first second state))
        (liftRightControlStmt first second yes)
        (liftRightControlStmt first second no)
  | .goto next =>
      .goto
        (fun state =>
          rightLabel first second (next (rightStateValue first second state)))
  | .halt => .halt

/-- Embed a second-machine configuration into the combined control types. -/
def liftRightControlCfg {Γ₀ Γ₁ Γ₂ : Type}
    (first : TM2ComputableAux Γ₀ Γ₁)
    (second : TM2ComputableAux Γ₁ Γ₂)
    (cfg : TM2.Cfg second.tm.Γ second.tm.Λ second.tm.σ) :
    TM2.Cfg (StackAlphabet first.tm second.tm)
      (ControlLabel first second) (ControlState first second) where
  l := cfg.l.map (rightLabel first second)
  var := rightState first second cfg.var
  stk := rightStacks first.tm second.tm cfg.stk

/-- Lift the second program into combined control. Non-right labels halt; they
are unreachable in the phase-preserving simulation proved below. -/
def liftRightControlProgram {Γ₀ Γ₁ Γ₂ : Type}
    (first : TM2ComputableAux Γ₀ Γ₁)
    (second : TM2ComputableAux Γ₁ Γ₂)
    (program : second.tm.Λ → TM2.Stmt second.tm.Γ second.tm.Λ second.tm.σ) :
    ControlLabel first second →
      TM2.Stmt (StackAlphabet first.tm second.tm)
        (ControlLabel first second) (ControlState first second)
  | Sum.inr (Sum.inr label) =>
      liftRightControlStmt first second (program label)
  | _ => .halt

/-- Lifting into combined control commutes with execution of one second-machine
statement from a genuine right-phase state and stack family. -/
theorem liftRightControl_stepAux {Γ₀ Γ₁ Γ₂ : Type}
    (first : TM2ComputableAux Γ₀ Γ₁)
    (second : TM2ComputableAux Γ₁ Γ₂)
    (stmt : TM2.Stmt second.tm.Γ second.tm.Λ second.tm.σ)
    (state : second.tm.σ)
    (contents : ∀ k, List (second.tm.Γ k)) :
    TM2.stepAux (liftRightControlStmt first second stmt)
        (rightState first second state)
        (rightStacks first.tm second.tm contents) =
      liftRightControlCfg first second
        (TM2.stepAux stmt state contents) := by
  induction stmt generalizing state contents with
  | push k write next ih =>
      simp only [liftRightControlStmt, TM2.stepAux,
        rightStateValue_rightState]
      rw [← rightStacks_update]
      exact ih _ _
  | peek k read next ih =>
      simpa only [liftRightControlStmt, TM2.stepAux,
        rightStateValue_rightState, rightStacks_inr] using
        ih (read state (contents k).head?) contents
  | pop k read next ih =>
      simp only [liftRightControlStmt, TM2.stepAux,
        rightStateValue_rightState, rightStacks_inr]
      rw [← rightStacks_update]
      exact ih _ _
  | load update next ih =>
      simpa only [liftRightControlStmt, TM2.stepAux,
        rightStateValue_rightState] using
        ih (update state) contents
  | branch test yes no ihYes ihNo =>
      by_cases h : test state
      · simpa only [liftRightControlStmt, TM2.stepAux,
          rightStateValue_rightState, h, cond_true] using
          ihYes state contents
      · simpa only [liftRightControlStmt, TM2.stepAux,
          rightStateValue_rightState, h, cond_false] using
          ihNo state contents
  | goto next =>
      rfl
  | halt =>
      rfl

/-- One step of the second program is simulated exactly after injecting its
stacks, labels, and state into the combined control types. -/
theorem liftRightControl_step {Γ₀ Γ₁ Γ₂ : Type}
    (first : TM2ComputableAux Γ₀ Γ₁)
    (second : TM2ComputableAux Γ₁ Γ₂)
    (program : second.tm.Λ → TM2.Stmt second.tm.Γ second.tm.Λ second.tm.σ)
    (cfg : TM2.Cfg second.tm.Γ second.tm.Λ second.tm.σ) :
    TM2.step (liftRightControlProgram first second program)
        (liftRightControlCfg first second cfg) =
      Option.map (liftRightControlCfg first second)
        (TM2.step program cfg) := by
  cases cfg with
  | mk label state contents =>
      cases label with
      | none =>
          rfl
      | some label =>
          simp only [liftRightControlCfg, TM2.step,
            Option.map_some, liftRightControlProgram, rightLabel]
          rw [liftRightControl_stepAux]
          rfl

end LeanNPHardness.MachineComposition
