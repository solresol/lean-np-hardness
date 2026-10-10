import LeanNPHardness.ReusableMembershipMachine
import LeanNPHardness.CNFCertificate

/-!
# Literal evaluation with a reusable certificate

This finite eight-stack TM2 wrapper retains a supplied negative-polarity bit
through framed membership lookup. One further step replaces the membership bit
by its conditional negation and resets control at a live `done` continuation.
The complete certificate and unread input/output suffixes survive; query/count/
work stacks finish empty. Exact execution, the polynomial bit bound, and
agreement with `CNF.Literal.eval` are stated separately.

The input is a framed variable, with polarity in finite control and the complete
certificate already on `backup`. This does not yet parse the even/odd literal
code used by `CNF.Formula.finEncoding`. Serialized literal extraction, clause
aggregation, exact-width checking, and the full verifier remain separate.
-/

namespace LeanNPHardness.MachinePrimitives.LiteralEvaluation

open Computability Turing

abbrev Stack := ReusableMembership.Stack
abbrev Alphabet := ReusableMembership.Alphabet
abbrev State := ReusableMembership.State × Bool

/-- True marks a negative literal. -/
def polarity : CNF.Literal Nat → Bool
  | .positive _ => false
  | .negative _ => true

def applyPolarity (negative value : Bool) : Bool :=
  if negative then !value else value

/-- Boolean literal semantics, independently of any machine execution. -/
theorem result_eq_eval (literal : CNF.Literal Nat) (xs : List Nat) :
    applyPolarity (polarity literal) (decide (literal.var ∈ xs)) =
      literal.eval (CNF.Certificate.assignment xs) := by
  cases literal <;> rfl

theorem result_eq_true_iff (literal : CNF.Literal Nat) (xs : List Nat) :
    applyPolarity (polarity literal) (decide (literal.var ∈ xs)) = true ↔
      literal.Satisfied (CNF.Certificate.assignment xs) := by
  rw [result_eq_eval, CNF.Literal.eval_eq_true]

def lookupState (negative : Bool) : State := (ReusableMembership.initialState, negative)

def initialState : State := lookupState false

inductive Label
  | lookup (label : ReusableMembership.Label)
  | done
  deriving DecidableEq, Fintype

/-- Total output operation; the execution contract supplies a leading bit. -/
def signedContents (negative : Bool) (contents : (k : Stack) → List (Alphabet k)) :
    (k : Stack) → List (Alphabet k) :=
  Function.update contents .output
    (applyPolarity negative ((contents .output).head?.getD false) ::
      (contents .output).tail)

/-- After the pop, the polarity register holds the result until it is pushed. -/
def signStmt : TM2.Stmt Alphabet Label State :=
  .pop .output (fun state bit => (state.1, applyPolarity state.2 (bit.getD false))) <|
    .push .output (fun state => state.2) <|
      .load (fun _ => initialState) (.goto fun _ => .done)

/-- Conditional negation changes only output and resets finite control. -/
theorem sign_stepAux (state : State) (contents : (k : Stack) → List (Alphabet k)) :
    TM2.stepAux signStmt state contents =
      ⟨some .done, initialState, signedContents state.2 contents⟩ := by
  simp [signStmt, TM2.stepAux, signedContents]

/-- Every lookup instruction retains polarity; its halt applies the sign. -/
def liftStmt : TM2.Stmt Alphabet ReusableMembership.Label ReusableMembership.State →
    TM2.Stmt Alphabet Label State
  | .push k write next => .push k (fun state => write state.1) (liftStmt next)
  | .peek k read next => .peek k (fun state bit => (read state.1 bit, state.2)) (liftStmt next)
  | .pop k read next => .pop k (fun state bit => (read state.1 bit, state.2)) (liftStmt next)
  | .load update next => .load (fun state => (update state.1, state.2)) (liftStmt next)
  | .branch test yes no => .branch (fun state => test state.1) (liftStmt yes) (liftStmt no)
  | .goto next => .goto (fun state => .lookup (next state.1))
  | .halt => signStmt

def program : Label → TM2.Stmt Alphabet Label State
  | .lookup label => liftStmt (ReusableMembership.program label)
  | .done => .halt

def computer : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .output
  Γ := Alphabet
  Λ := Label
  main := .lookup ReusableMembership.computer.main
  σ := State
  initialState := initialState
  Γk₀Fin := Bool.fintype
  m := program

def cfg (label : Option Label) (state : State)
    (input query remaining candidate scratch count output backup : List Bool) : computer.Cfg where
  l := label
  var := state
  stk := PreservingMembership.membershipContents backup
    (CertificateCount.stackContents input query remaining candidate scratch count output)

/-- A reached lookup halt includes the sign operation; live stacks are unchanged. -/
def liftCfg (negative : Bool) (c : ReusableMembership.computer.Cfg) : computer.Cfg where
  l := some (c.l.elim .done Label.lookup)
  var := c.l.elim initialState (fun _ => (c.var, negative))
  stk := c.l.elim (signedContents negative c.stk) (fun _ => c.stk)

/-- Exact statement simulation with retained polarity through every live step. -/
theorem lift_stepAux
    (stmt : TM2.Stmt Alphabet ReusableMembership.Label ReusableMembership.State)
    (state : ReusableMembership.State) (negative : Bool)
    (contents : (k : Stack) → List (Alphabet k)) :
    TM2.stepAux (liftStmt stmt) (state, negative) contents =
      liftCfg negative (TM2.stepAux stmt state contents) := by
  induction stmt generalizing state contents with
  | push k write next ih => simpa only [liftStmt, TM2.stepAux] using ih _ _
  | peek k read next ih => simpa only [liftStmt, TM2.stepAux] using ih _ _
  | pop k read next ih => simpa only [liftStmt, TM2.stepAux] using ih _ _
  | load update next ih => simpa only [liftStmt, TM2.stepAux] using ih _ _
  | branch test yes no ihYes ihNo =>
      cases h : test state
      · simpa only [liftStmt, TM2.stepAux, h, Bool.false_eq_true, cond_false] using ihNo state contents
      · simpa only [liftStmt, TM2.stepAux, h, cond_true] using ihYes state contents
  | goto next => rfl
  | halt => exact sign_stepAux _ _

private theorem lift_step (label : ReusableMembership.Label) (state : ReusableMembership.State)
    (negative : Bool) (contents : (k : Stack) → List (Alphabet k)) :
    computer.step (liftCfg negative ⟨some label, state, contents⟩) =
      some (liftCfg negative (TM2.stepAux (ReusableMembership.program label) state contents)) := by
  change some (TM2.stepAux (liftStmt (ReusableMembership.program label)) (state, negative) contents) = _
  rw [lift_stepAux]

private theorem iterate_bind_none {α : Type} (step : α → Option α) (n : Nat) :
    (fun c => c.bind step)^[n] none = none := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply]; exact ih

/-- Exact lookup runs lift without any extra dispatch steps. -/
theorem lift_run (n : Nat) (start finish : ReusableMembership.computer.Cfg) (negative : Bool)
    (run : (fun c => c.bind ReusableMembership.computer.step)^[n] (some start) = some finish) :
    (fun c => c.bind computer.step)^[n] (some (liftCfg negative start)) =
      some (liftCfg negative finish) := by
  induction n generalizing start with
  | zero =>
      simp only [Function.iterate_zero, id_eq, Option.some.injEq] at run
      subst finish
      rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply] at run ⊢
      rcases start with ⟨label, state, contents⟩
      cases label with
      | none =>
          simp only [Option.bind_some, FinTM2.step, TM2.step] at run
          rw [iterate_bind_none] at run
          contradiction
      | some label =>
          simp only [Option.bind_some, FinTM2.step, TM2.step] at run
          rw [Option.bind_some, lift_step]
          exact ih _ run

/-- The lookup continuation applies the sign in exactly one counted step. -/
theorem sign_step (state : ReusableMembership.State) (negative value : Bool)
    (input query remaining candidate scratch count output backup : List Bool) :
    computer.step (cfg (some (.lookup .done)) (state, negative)
      input query remaining candidate scratch count (value :: output) backup) =
      some (cfg (some .done) initialState input query remaining candidate scratch count
        (applyPolarity negative value :: output) backup) := by
  change some (TM2.stepAux signStmt (state, negative) _) = _
  rw [sign_stepAux]
  congr 2
  funext index
  cases index <;> simp [signedContents, PreservingMembership.membershipContents,
    CertificateCount.stackContents]

def runSteps (query : Nat) (xs : List Nat) : Nat := ReusableMembership.runSteps query xs + 1

/-- Lookup plus conditional negation retains backup and suffixes and clears workspace. -/
theorem whole_query (query : Nat) (negative : Bool) (xs : List Nat) (input output : List Bool) :
    (fun c => c.bind computer.step)^[runSteps query xs]
      (some (cfg (some computer.main) (lookupState negative)
        (BinaryNatLists.encodeNat query ++ input) [] [] [] [] [] output
        (BinaryNatLists.encodeNatList xs))) =
      some (cfg (some .done) initialState input [] [] [] [] []
        (applyPolarity negative (decide (query ∈ xs)) :: output)
        (BinaryNatLists.encodeNatList xs)) := by
  have run := lift_run _ _ _ negative (ReusableMembership.whole_query query xs input output)
  rw [runSteps, Function.iterate_succ_apply']
  change (fun c => c.bind computer.step)
    ((fun c => c.bind computer.step)^[ReusableMembership.runSteps query xs]
      (some (liftCfg negative (ReusableMembership.cfg (some (.query .prefix))
        ReusableMembership.initialState (BinaryNatLists.encodeNat query ++ input)
        [] [] [] [] [] output (BinaryNatLists.encodeNatList xs))))) = _
  rw [run]
  exact sign_step _ _ _ _ _ _ _ _ _ _ _

/-- The bit bound counts the sign step and excludes the final live continuation halt. -/
theorem runSteps_le_bit_bound (query : Nat) (xs : List Nat) :
    runSteps query xs ≤ (BinaryNatLists.encodeNatList xs).length *
      (2 * (encodeNat query).length + 4 * (BinaryNatLists.encodeNatList xs).length + 18) +
      4 * (encodeNat query).length + 13 := by
  have bound := ReusableMembership.runSteps_le_bit_bound query xs
  unfold runSteps
  omega

/-- Machine output agrees with literal evaluation for either polarity. -/
theorem whole_literal (literal : CNF.Literal Nat) (xs : List Nat) (input output : List Bool) :
    (fun c => c.bind computer.step)^[runSteps literal.var xs]
      (some (cfg (some computer.main) (lookupState (polarity literal))
        (BinaryNatLists.encodeNat literal.var ++ input) [] [] [] [] [] output
        (BinaryNatLists.encodeNatList xs))) =
      some (cfg (some .done) initialState input [] [] [] [] []
        (literal.eval (CNF.Certificate.assignment xs) :: output)
        (BinaryNatLists.encodeNatList xs)) := by
  simpa only [result_eq_eval] using whole_query literal.var (polarity literal) xs input output

/-- Bounded literal evaluation from a supplied polarity and framed variable. -/
def literal_evalsToInTime (literal : CNF.Literal Nat) (xs : List Nat) (input output : List Bool) :
    EvalsToInTime computer.step
      (cfg (some computer.main) (lookupState (polarity literal))
        (BinaryNatLists.encodeNat literal.var ++ input) [] [] [] [] [] output
        (BinaryNatLists.encodeNatList xs))
      (some (cfg (some .done) initialState input [] [] [] [] []
        (literal.eval (CNF.Certificate.assignment xs) :: output)
        (BinaryNatLists.encodeNatList xs)))
      ((BinaryNatLists.encodeNatList xs).length *
        (2 * (encodeNat literal.var).length + 4 * (BinaryNatLists.encodeNatList xs).length + 18) +
        4 * (encodeNat literal.var).length + 13) where
  steps := runSteps literal.var xs
  evals_in_steps := whole_literal literal xs input output
  steps_le_m := runSteps_le_bit_bound literal.var xs

end LeanNPHardness.MachinePrimitives.LiteralEvaluation
