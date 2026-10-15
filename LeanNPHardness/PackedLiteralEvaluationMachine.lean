import LeanNPHardness.PackedLiteralMachine

/-!
# Evaluation of packed literal frames

This finite eight-stack TM2 dispatcher loads the even/odd literal encoding
straight into the raw-query slot, then reuses certificate-preserving lookup,
query cleanup, and conditional negation. The complete certificate and arbitrary
unread input/output suffixes survive; query/count/workspace finish empty.

Exact execution counts the transition from the loader's live continuation.
The certificate is preloaded and the final live continuation halt is excluded.
`ClauseEvaluationStepMachine` adds one disjunctive accumulation step. Repeated
clause traversal, exact-width checking, and the full verifier remain separate.
-/

namespace LeanNPHardness.MachinePrimitives.PackedLiteralEvaluation

open Computability Turing StateTransition

abbrev Stack := LiteralEvaluation.Stack
abbrev Alphabet := LiteralEvaluation.Alphabet
abbrev State := PackedLiteral.State × LiteralEvaluation.State

def initialState : State := (none, LiteralEvaluation.initialState)

inductive Label
  | loader (label : PackedLiteral.Label)
  | evaluation (label : LiteralEvaluation.Label)
  deriving DecidableEq, Fintype

/-- Reuse the query-extraction injection: candidate becomes the raw query. -/
abbrev loaderStack := ReusableMembership.queryStack
abbrev loaderContents := ReusableMembership.queryContents

@[simp] private theorem loaderContents_apply (candidate output backup : List Bool)
    (contents : (k : PackedLiteral.Stack) → List (PackedLiteral.Alphabet k))
    (k : PackedLiteral.Stack) :
    loaderContents candidate output backup contents (loaderStack k) = contents k := by
  cases k <;> rfl

private theorem loaderContents_update (candidate output backup : List Bool)
    (contents : (k : PackedLiteral.Stack) → List (PackedLiteral.Alphabet k))
    (k : PackedLiteral.Stack) (value : List Bool) :
    Function.update (loaderContents candidate output backup contents) (loaderStack k) value =
      loaderContents candidate output backup (Function.update contents k value) := by
  funext index
  cases k <;> cases index <;>
    simp [Function.update, loaderContents, loaderStack,
      ReusableMembership.queryContents, ReusableMembership.queryStack]

/-- Loader halt transfers the extracted polarity and enters raw-variable evaluation. -/
def loaderStmt : TM2.Stmt PackedLiteral.Alphabet PackedLiteral.Label PackedLiteral.State →
    TM2.Stmt Alphabet Label State
  | .push k write next => .push (loaderStack k) (fun state => write state.1) (loaderStmt next)
  | .peek k read next => .peek (loaderStack k)
      (fun state bit => (read state.1 bit, LiteralEvaluation.initialState)) (loaderStmt next)
  | .pop k read next => .pop (loaderStack k)
      (fun state bit => (read state.1 bit, LiteralEvaluation.initialState)) (loaderStmt next)
  | .load update next =>
      .load (fun state => (update state.1, LiteralEvaluation.initialState)) (loaderStmt next)
  | .branch test yes no => .branch (fun state => test state.1) (loaderStmt yes) (loaderStmt no)
  | .goto next => .goto (fun state => .loader (next state.1))
  | .halt => .load (fun state => (none, LiteralEvaluation.lookupState (state.1.getD false)))
      (.goto fun _ => .evaluation (.lookup (.membership (.copy .reverse))))

/-- Evaluation keeps the original stack operations and exact costs. -/
def evaluationStmt : TM2.Stmt Alphabet LiteralEvaluation.Label LiteralEvaluation.State →
    TM2.Stmt Alphabet Label State
  | .push k write next => .push k (fun state => write state.2) (evaluationStmt next)
  | .peek k read next => .peek k (fun state bit => (none, read state.2 bit)) (evaluationStmt next)
  | .pop k read next => .pop k (fun state bit => (none, read state.2 bit)) (evaluationStmt next)
  | .load update next => .load (fun state => (none, update state.2)) (evaluationStmt next)
  | .branch test yes no => .branch (fun state => test state.2) (evaluationStmt yes) (evaluationStmt no)
  | .goto next => .goto (fun state => .evaluation (next state.2))
  | .halt => .halt

def program : Label → TM2.Stmt Alphabet Label State
  | .loader label => loaderStmt (PackedLiteral.program label)
  | .evaluation label => evaluationStmt (LiteralEvaluation.program label)

def computer : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .output
  Γ := Alphabet
  Λ := Label
  main := .loader PackedLiteral.computer.main
  σ := State
  initialState := initialState
  Γk₀Fin := Bool.fintype
  m := program

def cfg (label : Option Label) (state : State)
    (input query remaining candidate scratch count output backup : List Bool) : computer.Cfg where
  l := label
  var := state
  stk := (LiteralEvaluation.cfg none LiteralEvaluation.initialState
    input query remaining candidate scratch count output backup).stk

def loaderCfg (candidate output backup : List Bool) (c : PackedLiteral.computer.Cfg) : computer.Cfg where
  l := some (c.l.elim (.evaluation (.lookup (.membership (.copy .reverse)))) Label.loader)
  var := c.l.elim (none, LiteralEvaluation.lookupState (c.var.getD false))
    (fun _ => (c.var, LiteralEvaluation.initialState))
  stk := loaderContents candidate output backup c.stk

def evaluationCfg (c : LiteralEvaluation.computer.Cfg) : computer.Cfg where
  l := c.l.map Label.evaluation
  var := (none, c.var)
  stk := c.stk

/-- Loading preserves private stacks and initializes polarity at the entry transition. -/
theorem loader_stepAux
    (stmt : TM2.Stmt PackedLiteral.Alphabet PackedLiteral.Label PackedLiteral.State)
    (state : PackedLiteral.State)
    (contents : (k : PackedLiteral.Stack) → List (PackedLiteral.Alphabet k))
    (candidate output backup : List Bool) :
    TM2.stepAux (loaderStmt stmt) (state, LiteralEvaluation.initialState)
      (loaderContents candidate output backup contents) =
      loaderCfg candidate output backup (TM2.stepAux stmt state contents) := by
  induction stmt generalizing state contents with
  | push k write next ih =>
      simp only [loaderStmt, TM2.stepAux, loaderContents_apply]
      rw [loaderContents_update]
      exact ih _ _
  | peek k read next ih =>
      simpa only [loaderStmt, TM2.stepAux, loaderContents_apply] using ih _ _
  | pop k read next ih =>
      simp only [loaderStmt, TM2.stepAux, loaderContents_apply]
      rw [loaderContents_update]
      exact ih _ _
  | load update next ih => simpa only [loaderStmt, TM2.stepAux] using ih _ _
  | branch test yes no ihYes ihNo =>
      cases h : test state
      · simpa only [loaderStmt, TM2.stepAux, h, Bool.false_eq_true, cond_false] using ihNo state contents
      · simpa only [loaderStmt, TM2.stepAux, h, cond_true] using ihYes state contents
  | goto next => rfl
  | halt => rfl

/-- The evaluation simulation preserves its exact cost. -/
theorem evaluation_stepAux
    (stmt : TM2.Stmt Alphabet LiteralEvaluation.Label LiteralEvaluation.State)
    (state : LiteralEvaluation.State) (contents : (k : Stack) → List (Alphabet k)) :
    TM2.stepAux (evaluationStmt stmt) (none, state) contents =
      evaluationCfg (TM2.stepAux stmt state contents) := by
  induction stmt generalizing state contents with
  | push k write next ih => simpa only [evaluationStmt, TM2.stepAux] using ih _ _
  | peek k read next ih => simpa only [evaluationStmt, TM2.stepAux] using ih _ _
  | pop k read next ih => simpa only [evaluationStmt, TM2.stepAux] using ih _ _
  | load update next ih => simpa only [evaluationStmt, TM2.stepAux] using ih _ _
  | branch test yes no ihYes ihNo =>
      cases h : test state
      · simpa only [evaluationStmt, TM2.stepAux, h, Bool.false_eq_true, cond_false] using ihNo state contents
      · simpa only [evaluationStmt, TM2.stepAux, h, cond_true] using ihYes state contents
  | goto next => rfl
  | halt => rfl

private theorem loader_step (label : PackedLiteral.Label) (state : PackedLiteral.State)
    (contents : (k : PackedLiteral.Stack) → List (PackedLiteral.Alphabet k))
    (candidate output backup : List Bool) :
    computer.step (loaderCfg candidate output backup ⟨some label, state, contents⟩) =
      some (loaderCfg candidate output backup (TM2.stepAux (PackedLiteral.program label) state contents)) := by
  change some (TM2.stepAux (loaderStmt (PackedLiteral.program label))
    (state, LiteralEvaluation.initialState) (loaderContents candidate output backup contents)) = _
  rw [loader_stepAux]

private theorem evaluation_step (label : LiteralEvaluation.Label)
    (state : LiteralEvaluation.State) (contents : (k : Stack) → List (Alphabet k)) :
    computer.step (evaluationCfg ⟨some label, state, contents⟩) =
      some (evaluationCfg (TM2.stepAux (LiteralEvaluation.program label) state contents)) := by
  change some (TM2.stepAux (evaluationStmt (LiteralEvaluation.program label)) (none, state) contents) = _
  rw [evaluation_stepAux]

private theorem iterate_bind_none {α : Type} (step : α → Option α) (n : Nat) :
    (fun c => c.bind step)^[n] none = none := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply]; exact ih

/-- Exact loader runs preserve private stacks and component costs. -/
theorem loader_run (n : Nat) (start finish : PackedLiteral.computer.Cfg)
    (candidate output backup : List Bool)
    (run : (fun c => c.bind PackedLiteral.computer.step)^[n] (some start) = some finish) :
    (fun c => c.bind computer.step)^[n] (some (loaderCfg candidate output backup start)) =
      some (loaderCfg candidate output backup finish) := by
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
          rw [Option.bind_some, loader_step]
          exact ih _ run

/-- Exact evaluation execution lifts without additional dispatch steps. -/
theorem evaluation_run (n : Nat) (start finish : LiteralEvaluation.computer.Cfg)
    (run : (fun c => c.bind LiteralEvaluation.computer.step)^[n]
      (some start) = some finish) :
    (fun c => c.bind computer.step)^[n] (some (evaluationCfg start)) = some (evaluationCfg finish) := by
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
          rw [Option.bind_some, evaluation_step]
          exact ih _ run

/-- Identify the loader injection with the shared eight-stack configuration. -/
private theorem loaderCfg_cfg (label : Option PackedLiteral.Label)
    (state : PackedLiteral.State)
    (input remaining query scratch count candidate output backup : List Bool) :
    loaderCfg candidate output backup
      (PackedLiteral.cfg label state input remaining query scratch count) =
      cfg (some (label.elim (.evaluation (.lookup (.membership (.copy .reverse)))) Label.loader))
        (label.elim (none, LiteralEvaluation.lookupState (state.getD false))
          (fun _ => (state, LiteralEvaluation.initialState)))
        input query remaining candidate scratch count output backup := by
  unfold loaderCfg cfg PackedLiteral.cfg
  congr 1

/-- Loading preserves arbitrary count/candidate/output/backup contents. -/
theorem loader_whole_literal (literal : CNF.Literal Nat)
    (input remaining candidate output backup : List Bool) :
    (fun c => c.bind computer.step)^[3 * (encodeNat literal.toNat).length + 4]
      (some (cfg (some computer.main) initialState
        (BinaryNatLists.encodeNat literal.toNat ++ input) [] remaining candidate [] [] output backup)) =
      some (cfg (some (.loader .done))
        (some (LiteralEvaluation.polarity literal), LiteralEvaluation.initialState)
        input (encodeNat literal.var) remaining candidate [] [] output backup) := by
  have run := loader_run _ _ _ candidate output backup
    (PackedLiteral.whole_literal literal input remaining)
  simpa only [loaderCfg_cfg, Option.elim_some] using! run

/-- One counted step moves polarity from the loader register to evaluation control. -/
theorem evaluation_entry_step (negative : Bool)
    (input query remaining candidate scratch count output backup : List Bool) :
    computer.step (cfg (some (.loader .done)) (some negative, LiteralEvaluation.initialState)
      input query remaining candidate scratch count output backup) =
      some (cfg (some (.evaluation (.lookup (.membership (.copy .reverse)))))
        (none, LiteralEvaluation.lookupState negative)
        input query remaining candidate scratch count output backup) := by
  rfl

/-- Exact loading, entry, raw lookup, cleanup, and conditional-negation costs. -/
def runSteps (literal : CNF.Literal Nat) (xs : List Nat) : Nat :=
  (3 * (encodeNat literal.toNat).length + 4) +
    (1 + LiteralEvaluation.rawRunSteps literal.var xs)

/-- Evaluate the actual framed literal code and leave the certificate reusable. -/
theorem whole_literal (literal : CNF.Literal Nat) (xs : List Nat) (input output : List Bool) :
    (fun c => c.bind computer.step)^[runSteps literal xs]
      (some (cfg (some computer.main) initialState
        (BinaryNatLists.encodeNat literal.toNat ++ input) [] [] [] [] [] output
        (BinaryNatLists.encodeNatList xs))) =
      some (cfg (some (.evaluation .done)) initialState input [] [] [] [] []
        (literal.eval (CNF.Certificate.assignment xs) :: output)
        (BinaryNatLists.encodeNatList xs)) := by
  rw [runSteps, Nat.add_comm, Function.iterate_add_apply, loader_whole_literal,
    Nat.add_comm 1, Function.iterate_succ_apply, Option.bind_some, evaluation_entry_step]
  have run := evaluation_run _ _ _
    (LiteralEvaluation.whole_raw_query literal.var (LiteralEvaluation.polarity literal) xs input output)
  simpa only [LiteralEvaluation.result_eq_eval] using! run

/-- Bound in raw variable bits, packed payload bits, and full certificate bits. -/
theorem runSteps_le_bit_bound (literal : CNF.Literal Nat) (xs : List Nat) :
    runSteps literal xs ≤ (BinaryNatLists.encodeNatList xs).length *
      (2 * (encodeNat literal.var).length + 4 * (BinaryNatLists.encodeNatList xs).length + 18) +
      3 * (encodeNat literal.toNat).length + (encodeNat literal.var).length + 15 := by
  have bound := PreservingMembership.runSteps_le_bit_bound literal.var xs
  unfold runSteps LiteralEvaluation.rawRunSteps ReusableMembership.rawRunSteps
  omega

/-- Polynomial bound measured only in the complete literal frame and certificate. -/
theorem runSteps_le_frame_bound (literal : CNF.Literal Nat) (xs : List Nat) :
    runSteps literal xs ≤ (BinaryNatLists.encodeNatList xs).length *
      (2 * BinaryNatLists.natWireSize literal.toNat +
        4 * (BinaryNatLists.encodeNatList xs).length + 18) +
      2 * BinaryNatLists.natWireSize literal.toNat + 13 := by
  have tail := congrArg List.length (PackedLiteral.tail_encode_toNat literal)
  simp only [List.length_tail] at tail
  have bound := runSteps_le_bit_bound literal xs
  unfold BinaryNatLists.natWireSize
  have mulBound := Nat.mul_le_mul_left (BinaryNatLists.encodeNatList xs).length
    (show 2 * (encodeNat literal.var).length + 4 * (BinaryNatLists.encodeNatList xs).length + 18 ≤
      2 * (2 * (encodeNat literal.toNat).length + 1) +
        4 * (BinaryNatLists.encodeNatList xs).length + 18 by omega)
  omega

/-- Bounded packed-literal evaluation, before the final continuation halt. -/
def literal_evalsToInTime (literal : CNF.Literal Nat) (xs : List Nat) (input output : List Bool) :
    EvalsToInTime computer.step
      (cfg (some computer.main) initialState
        (BinaryNatLists.encodeNat literal.toNat ++ input) [] [] [] [] [] output
        (BinaryNatLists.encodeNatList xs))
      (some (cfg (some (.evaluation .done)) initialState input [] [] [] [] []
        (literal.eval (CNF.Certificate.assignment xs) :: output)
        (BinaryNatLists.encodeNatList xs)))
      ((BinaryNatLists.encodeNatList xs).length *
        (2 * BinaryNatLists.natWireSize literal.toNat +
          4 * (BinaryNatLists.encodeNatList xs).length + 18) +
        2 * BinaryNatLists.natWireSize literal.toNat + 13) where
  steps := runSteps literal xs
  evals_in_steps := whole_literal literal xs input output
  steps_le_m := runSteps_le_frame_bound literal xs

end LeanNPHardness.MachinePrimitives.PackedLiteralEvaluation
