import LeanNPHardness.ReusableMembershipMachine

/-!
# Membership lookup preserving an outer query count

This finite nine-stack TM2 machine embeds `ReusableMembership` and adds
`outerRemaining`, independent of the count consumed during certificate traversal.
Every source statement and exact run lifts at the same cost, retaining arbitrary
contents on the outer stack. The canonical query-list head interface keeps the
unread frames, their repetitions, and the original outer count intact.

The certificate and outer count are preloaded. Header loading, outer decrement,
repeated-query dispatch, and the full SAT verifier remain separate obligations.
The lookup ends at a live `done` label; its final halt is excluded from the bound.
-/

namespace LeanNPHardness.MachinePrimitives.QueryMembership

open Computability Turing

inductive Stack
  | lookup (stack : ReusableMembership.Stack)
  | outerRemaining
  deriving DecidableEq, Fintype

def Alphabet (_ : Stack) : Type := Bool

abbrev Label := ReusableMembership.Label
abbrev State := ReusableMembership.State
abbrev initialState := ReusableMembership.initialState

def lookupContents (outer : List Bool)
    (contents : (k : ReusableMembership.Stack) → List (ReusableMembership.Alphabet k)) :
    (k : Stack) → List (Alphabet k)
  | .lookup k => contents k
  | .outerRemaining => outer

private theorem lookupContents_update (outer : List Bool)
    (contents : (k : ReusableMembership.Stack) → List (ReusableMembership.Alphabet k))
    (k : ReusableMembership.Stack) (value : List Bool) :
    Function.update (lookupContents outer contents) (.lookup k) value =
      lookupContents outer (Function.update contents k value) := by
  funext index
  cases index with
  | lookup index => simp [Function.update, lookupContents]
  | outerRemaining => simp [Function.update, lookupContents]

/-- The lifted statements touch only the eight lookup stacks. -/
def liftStmt : TM2.Stmt ReusableMembership.Alphabet Label State → TM2.Stmt Alphabet Label State
  | .push k write next => .push (.lookup k) write (liftStmt next)
  | .peek k read next => .peek (.lookup k) read (liftStmt next)
  | .pop k read next => .pop (.lookup k) read (liftStmt next)
  | .load update next => .load update (liftStmt next)
  | .branch test yes no => .branch test (liftStmt yes) (liftStmt no)
  | .goto next => .goto next
  | .halt => .halt

def program (label : Label) : TM2.Stmt Alphabet Label State :=
  liftStmt (ReusableMembership.program label)

def computer : FinTM2 where
  K := Stack
  k₀ := .lookup .input
  k₁ := .lookup .output
  Γ := Alphabet
  Λ := Label
  main := .query .prefix
  σ := State
  initialState := initialState
  Γk₀Fin := Bool.fintype
  m := program

def liftCfg (outer : List Bool) (c : ReusableMembership.computer.Cfg) : computer.Cfg where
  l := c.l
  var := c.var
  stk := lookupContents outer c.stk

def cfg (label : Option Label) (state : State)
    (input query remaining candidate scratch count output backup outer : List Bool) : computer.Cfg :=
  liftCfg outer (ReusableMembership.cfg label state
    input query remaining candidate scratch count output backup)

/-- Statement execution retains the outer count, including on a reached halt. -/
theorem lift_stepAux (stmt : TM2.Stmt ReusableMembership.Alphabet Label State)
    (state : State)
    (contents : (k : ReusableMembership.Stack) → List (ReusableMembership.Alphabet k))
    (outer : List Bool) :
    TM2.stepAux (liftStmt stmt) state (lookupContents outer contents) =
      liftCfg outer (TM2.stepAux stmt state contents) := by
  induction stmt generalizing state contents with
  | push k write next ih =>
      simp only [liftStmt, TM2.stepAux, lookupContents]
      rw [lookupContents_update]
      exact ih _ _
  | peek k read next ih => simpa only [liftStmt, TM2.stepAux, lookupContents] using ih _ _
  | pop k read next ih =>
      simp only [liftStmt, TM2.stepAux, lookupContents]
      rw [lookupContents_update]
      exact ih _ _
  | load update next ih => simpa only [liftStmt, TM2.stepAux] using ih _ _
  | branch test yes no ihYes ihNo =>
      cases h : test state
      · simpa only [liftStmt, TM2.stepAux, h, Bool.false_eq_true, cond_false] using ihNo state contents
      · simpa only [liftStmt, TM2.stepAux, h, cond_true] using ihYes state contents
  | goto next => rfl
  | halt => rfl

/-- One source step costs one lifted step and leaves the outer stack unchanged. -/
theorem lift_step (outer : List Bool) (c : ReusableMembership.computer.Cfg) :
    computer.step (liftCfg outer c) =
      (ReusableMembership.computer.step c).map (liftCfg outer) := by
  rcases c with ⟨label, state, contents⟩
  cases label with
  | none => rfl
  | some label =>
      change some (TM2.stepAux (liftStmt (ReusableMembership.program label))
        state (lookupContents outer contents)) = _
      rw [lift_stepAux]
      rfl

private theorem iterate_bind_none {α : Type} (step : α → Option α) (n : Nat) :
    (fun c => c.bind step)^[n] none = none := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply]; exact ih

/-- Arbitrary exact lookup runs preserve any outer word with no runtime overhead. -/
theorem lift_run (n : Nat) (start finish : ReusableMembership.computer.Cfg)
    (outer : List Bool)
    (run : (fun c => c.bind ReusableMembership.computer.step)^[n]
      (some start) = some finish) :
    (fun c => c.bind computer.step)^[n] (some (liftCfg outer start)) =
      some (liftCfg outer finish) := by
  induction n generalizing start with
  | zero =>
      simp only [Function.iterate_zero, id_eq, Option.some.injEq] at run
      subst finish
      rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply] at run ⊢
      rw [Option.bind_some, lift_step]
      cases h : ReusableMembership.computer.step start with
      | none =>
          simp only [Option.bind_some, h] at run
          rw [iterate_bind_none] at run
          contradiction
      | some next =>
          simp only [Option.bind_some, h] at run
          exact ih next run

abbrev runSteps := ReusableMembership.runSteps

/-- Framed membership retains the outer word, full certificate, and both suffixes.
All lookup query/count/work stacks are empty at the live continuation. -/
theorem whole_query (query : Nat) (xs : List Nat) (input output outer : List Bool) :
    (fun c => c.bind computer.step)^[runSteps query xs]
      (some (cfg (some (.query .prefix)) initialState
        (BinaryNatLists.encodeNat query ++ input) [] [] [] [] [] output
        (BinaryNatLists.encodeNatList xs) outer)) =
      some (cfg (some .done) initialState
        input [] [] [] [] [] (decide (query ∈ xs) :: output)
        (BinaryNatLists.encodeNatList xs) outer) := by
  exact lift_run _ _ _ outer (ReusableMembership.whole_query query xs input output)

/-- One head lookup preserves all remaining query frames and the original list count.
The outer count is deliberately not decremented by this kernel. -/
theorem list_head (query : Nat) (queries xs : List Nat) (input output : List Bool) :
    (fun c => c.bind computer.step)^[runSteps query xs]
      (some (cfg (some (.query .prefix)) initialState
        ((query :: queries).flatMap BinaryNatLists.encodeNat ++ input) [] [] [] [] [] output
        (BinaryNatLists.encodeNatList xs) (encodeNat (query :: queries).length))) =
      some (cfg (some .done) initialState
        (queries.flatMap BinaryNatLists.encodeNat ++ input) [] [] [] [] []
        (decide (query ∈ xs) :: output)
        (BinaryNatLists.encodeNatList xs) (encodeNat (query :: queries).length)) := by
  simpa only [List.flatMap_cons, List.append_assoc] using
    whole_query query xs (queries.flatMap BinaryNatLists.encodeNat ++ input) output
      (encodeNat (query :: queries).length)

/-- The raw-query/full-certificate polynomial bound is independent of the outer word. -/
theorem runSteps_le_bit_bound (query : Nat) (xs : List Nat) :
    runSteps query xs ≤ (BinaryNatLists.encodeNatList xs).length *
      (2 * (encodeNat query).length + 4 * (BinaryNatLists.encodeNatList xs).length + 18) +
      4 * (encodeNat query).length + 12 :=
  ReusableMembership.runSteps_le_bit_bound query xs

/-- Bounded lookup execution with the outer query count retained verbatim. -/
def evalsToInTime (query : Nat) (xs : List Nat) (input output outer : List Bool) :
    EvalsToInTime computer.step
      (cfg (some (.query .prefix)) initialState
        (BinaryNatLists.encodeNat query ++ input) [] [] [] [] [] output
        (BinaryNatLists.encodeNatList xs) outer)
      (some (cfg (some .done) initialState
        input [] [] [] [] [] (decide (query ∈ xs) :: output)
        (BinaryNatLists.encodeNatList xs) outer))
      ((BinaryNatLists.encodeNatList xs).length *
        (2 * (encodeNat query).length + 4 * (BinaryNatLists.encodeNatList xs).length + 18) +
        4 * (encodeNat query).length + 12) where
  steps := runSteps query xs
  evals_in_steps := whole_query query xs input output outer
  steps_le_m := runSteps_le_bit_bound query xs

end LeanNPHardness.MachinePrimitives.QueryMembership
