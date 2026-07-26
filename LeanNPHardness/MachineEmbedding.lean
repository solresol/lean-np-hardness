import Mathlib.Computability.TMComputable

namespace LeanNPHardness.MachineComposition

open Turing

/-- The stack indices used while composing two finite two-stack machines. -/
def StackIndex (first second : FinTM2) :=
  first.K ⊕ second.K

instance (first second : FinTM2) :
    DecidableEq (StackIndex first second) := by
  letI : DecidableEq first.K := first.kDecidableEq
  letI : DecidableEq second.K := second.kDecidableEq
  exact inferInstanceAs (DecidableEq (first.K ⊕ second.K))

instance (first second : FinTM2) :
    Fintype (StackIndex first second) := by
  letI : Fintype first.K := first.kFin
  letI : Fintype second.K := second.kFin
  exact inferInstanceAs (Fintype (first.K ⊕ second.K))

/-- The alphabet family for the disjoint union of two machines' stacks. -/
def StackAlphabet (first second : FinTM2) :
    StackIndex first second → Type
  | Sum.inl k => first.Γ k
  | Sum.inr k => second.Γ k

/-- Embed the first machine's stacks into a combined stack family, leaving all
stacks belonging to the second machine empty. -/
def leftStacks (first second : FinTM2)
    (contents : ∀ k, List (first.Γ k)) :
    ∀ k, List (StackAlphabet first second k)
  | Sum.inl k => contents k
  | Sum.inr _ => []

@[simp]
theorem leftStacks_inl (first second : FinTM2)
    (contents : ∀ k, List (first.Γ k)) (k : first.K) :
    leftStacks first second contents (Sum.inl k) = contents k :=
  rfl

@[simp]
theorem leftStacks_inr (first second : FinTM2)
    (contents : ∀ k, List (first.Γ k)) (k : second.K) :
    leftStacks first second contents (Sum.inr k) = [] :=
  rfl

/-- Updating a first-machine stack before embedding is the same as updating
its left injection after embedding. -/
theorem leftStacks_update (first second : FinTM2)
    (contents : ∀ k, List (first.Γ k)) (k : first.K)
    (value : List (first.Γ k)) :
    leftStacks first second (Function.update contents k value) =
      Function.update (leftStacks first second contents) (Sum.inl k) value := by
  funext index
  cases index with
  | inl j =>
      by_cases h : j = k
      · subst j
        simp
      · have hsum :
            (Sum.inl j : StackIndex first second) ≠ Sum.inl k := by
          intro equality
          exact h (Sum.inl.inj equality)
        simp [h, hsum]
  | inr j =>
      simp

/-- Lift a statement of the first machine to the combined stack family.
Control labels and internal state are unchanged. -/
def liftLeftStmt (first second : FinTM2) :
    TM2.Stmt first.Γ first.Λ first.σ →
      TM2.Stmt (StackAlphabet first second) first.Λ first.σ
  | .push k write next =>
      .push (Sum.inl k) write (liftLeftStmt first second next)
  | .peek k read next =>
      .peek (Sum.inl k) read (liftLeftStmt first second next)
  | .pop k read next =>
      .pop (Sum.inl k) read (liftLeftStmt first second next)
  | .load update next =>
      .load update (liftLeftStmt first second next)
  | .branch test yes no =>
      .branch test (liftLeftStmt first second yes)
        (liftLeftStmt first second no)
  | .goto next => .goto next
  | .halt => .halt

/-- Lift a configuration of the first machine into the combined stack family.
All second-machine stacks start empty. -/
def liftLeftCfg (first second : FinTM2)
    (cfg : TM2.Cfg first.Γ first.Λ first.σ) :
    TM2.Cfg (StackAlphabet first second) first.Λ first.σ where
  l := cfg.l
  var := cfg.var
  stk := leftStacks first second cfg.stk

/-- Lifting the first machine commutes with execution of a single statement. -/
theorem liftLeft_stepAux (first second : FinTM2)
    (stmt : TM2.Stmt first.Γ first.Λ first.σ)
    (state : first.σ) (contents : ∀ k, List (first.Γ k)) :
    TM2.stepAux (liftLeftStmt first second stmt) state
        (leftStacks first second contents) =
      liftLeftCfg first second (TM2.stepAux stmt state contents) := by
  induction stmt generalizing state contents with
  | push k write next ih =>
      simp only [liftLeftStmt, TM2.stepAux]
      rw [← leftStacks_update]
      exact ih _ _
  | peek k read next ih =>
      simpa only [liftLeftStmt, TM2.stepAux, leftStacks_inl] using
        ih (read state (contents k).head?) contents
  | pop k read next ih =>
      simp only [liftLeftStmt, TM2.stepAux, leftStacks_inl]
      rw [← leftStacks_update]
      exact ih _ _
  | load update next ih =>
      simpa only [liftLeftStmt, TM2.stepAux] using ih (update state) contents
  | branch test yes no ihYes ihNo =>
      by_cases h : test state
      · simpa only [liftLeftStmt, TM2.stepAux, h, cond_true] using
          ihYes state contents
      · simpa only [liftLeftStmt, TM2.stepAux, h, cond_false] using
          ihNo state contents
  | goto next =>
      rfl
  | halt =>
      rfl

/-- One step of the first machine is simulated exactly by its lift into the
combined stack family. -/
theorem liftLeft_step (first second : FinTM2)
    (program : first.Λ → TM2.Stmt first.Γ first.Λ first.σ)
    (cfg : TM2.Cfg first.Γ first.Λ first.σ) :
    TM2.step (fun label => liftLeftStmt first second (program label))
        (liftLeftCfg first second cfg) =
      Option.map (liftLeftCfg first second) (TM2.step program cfg) := by
  cases cfg with
  | mk label state contents =>
      cases label with
      | none =>
          rfl
      | some label =>
          simp only [liftLeftCfg, TM2.step]
          rw [liftLeft_stepAux]
          rfl

end LeanNPHardness.MachineComposition
