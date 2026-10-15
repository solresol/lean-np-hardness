import LeanNPHardness.LiteralEvaluationMachine

/-!
# Loading the packed binary code of a literal

The formula encoding packs positive `v` as `2 * v` and negative `v` as
`2 * v + 1`. The low bit is the negative-polarity bit, with default false for
positive zero's empty encoding; the remaining bits encode the variable.

This five-stack TM2 kernel extracts one complete frame, then pops that low bit
into finite control. It retains arbitrary input and query contents and leaves
the raw variable on candidate with both work stacks empty. Execution ends at
a live continuation. `PackedLiteralEvaluationMachine` injects this loader into
reusable lookup, applies literal semantics, and drains the raw query.
-/

namespace LeanNPHardness.MachinePrimitives.PackedLiteral

open Computability Turing StateTransition

private theorem encodeNat_double (n : Nat) :
    encodeNat (2 * n) = if n = 0 then [] else false :: encodeNat n := by
  have cast : ((2 * n : Nat) : Num) = (n : Num).bit0 := by
    apply Num.to_nat_inj.mp
    rw [Num.to_of_nat, Num.cast_bit0, Num.to_of_nat]
  unfold encodeNat
  rw [cast]
  cases h : (n : Num) with
  | zero =>
      have hn : n = 0 := by simpa using congrArg (fun m : Num => (m : Nat)) h
      simp [hn, Num.bit0, encodeNum]
  | pos p =>
      have hn : n ≠ 0 := by
        intro hn
        simp [hn] at h
      simp [hn, Num.bit0, encodeNum, encodePosNum]

private theorem encodeNat_double_add_one (n : Nat) :
    encodeNat (2 * n + 1) = true :: encodeNat n := by
  have cast : ((2 * n + 1 : Nat) : Num) = (n : Num).bit1 := by
    apply Num.to_nat_inj.mp
    rw [Num.to_of_nat, Num.cast_bit1, Num.to_of_nat]
  unfold encodeNat
  rw [cast]
  cases (n : Num) <;> rfl

/-- The low bit supplies polarity, including the empty encoding of positive zero. -/
theorem head_encode_toNat (literal : CNF.Literal Nat) :
    ((encodeNat literal.toNat).head?).getD false = LiteralEvaluation.polarity literal := by
  cases literal with
  | positive n =>
      simp only [CNF.Literal.toNat, encodeNat_double, LiteralEvaluation.polarity]
      split <;> rfl
  | negative n =>
      rw [CNF.Literal.toNat, encodeNat_double_add_one]
      rfl

/-- Popping the low bit exposes the exact canonical variable encoding. -/
theorem tail_encode_toNat (literal : CNF.Literal Nat) :
    (encodeNat literal.toNat).tail = encodeNat literal.var := by
  cases literal with
  | positive n =>
      simp only [CNF.Literal.toNat, encodeNat_double, CNF.Literal.var]
      split
      · next h => subst n; simp [encodeNat, encodeNum]
      · rfl
  | negative n =>
      rw [CNF.Literal.toNat, encodeNat_double_add_one]
      rfl

abbrev Stack := FrameExtraction.Stack
abbrev Alphabet := FrameExtraction.Alphabet
abbrev State := FrameExtraction.State

inductive Label
  | extract (label : FrameExtraction.Label)
  | split
  | done
  deriving DecidableEq, Fintype

/-- Extraction's halt becomes a live polarity-splitting continuation. -/
def liftStmt : TM2.Stmt Alphabet FrameExtraction.Label State → TM2.Stmt Alphabet Label State
  | .push k write next => .push k write (liftStmt next)
  | .peek k read next => .peek k read (liftStmt next)
  | .pop k read next => .pop k read (liftStmt next)
  | .load update next => .load update (liftStmt next)
  | .branch test yes no => .branch test (liftStmt yes) (liftStmt no)
  | .goto next => .goto (fun state => .extract (next state))
  | .halt => .goto (fun _ => .split)

def program : Label → TM2.Stmt Alphabet Label State
  | .extract label => liftStmt (FrameExtraction.program label)
  | .split => .pop .candidate (fun _ bit => some (bit.getD false)) (.goto fun _ => .done)
  | .done => .halt

def computer : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .candidate
  Γ := Alphabet
  Λ := Label
  main := .extract .prefix
  σ := State
  initialState := none
  Γk₀Fin := Bool.fintype
  m := program

def cfg (label : Option Label) (state : State)
    (input query candidate scratch count : List Bool) : computer.Cfg where
  l := label
  var := state
  stk := FrameExtraction.stackContents input query candidate scratch count

def liftCfg (c : FrameExtraction.computer.Cfg) : computer.Cfg where
  l := some (c.l.elim .split Label.extract)
  var := c.var
  stk := c.stk

/-- The extractor's statements have unchanged cost and unchanged stack effects. -/
theorem lift_stepAux (stmt : TM2.Stmt Alphabet FrameExtraction.Label State)
    (state : State) (contents : (k : Stack) → List (Alphabet k)) :
    TM2.stepAux (liftStmt stmt) state contents =
      liftCfg (TM2.stepAux stmt state contents) := by
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
  | halt => rfl

private theorem lift_step (label : FrameExtraction.Label) (state : State)
    (contents : (k : Stack) → List (Alphabet k)) :
    computer.step (liftCfg ⟨some label, state, contents⟩) =
      some (liftCfg (TM2.stepAux (FrameExtraction.program label) state contents)) := by
  change some (TM2.stepAux (liftStmt (FrameExtraction.program label)) state contents) = _
  rw [lift_stepAux]

private theorem iterate_bind_none {α : Type} (step : α → Option α) (n : Nat) :
    (fun c => c.bind step)^[n] none = none := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply]; exact ih

/-- Exact extractor runs reach the split continuation without an extra step. -/
theorem lift_run (n : Nat) (start finish : FrameExtraction.computer.Cfg)
    (run : (fun c => c.bind FrameExtraction.computer.step)^[n] (some start) = some finish) :
    (fun c => c.bind computer.step)^[n] (some (liftCfg start)) = some (liftCfg finish) := by
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

/-- One pop retains the low bit (default false) and exposes the tail. -/
theorem split_step (state : State) (input query bits scratch count : List Bool) :
    computer.step (cfg (some .split) state input query bits scratch count) =
      some (cfg (some .done) (some (bits.head?.getD false))
        input query bits.tail scratch count) := by
  simp [computer, FinTM2.step, cfg, program, FrameExtraction.stackContents, Alphabet,
    FrameExtraction.Alphabet]
  funext index
  cases index <;> rfl

/-- Extract and split a framed payload, preserving the unread input and query. -/
theorem whole_frame (bits input query : List Bool) :
    (fun c => c.bind computer.step)^[3 * bits.length + 4]
      (some (cfg (some computer.main) none (BinaryNatLists.frame bits ++ input) query [] [] [])) =
      some (cfg (some .done) (some (bits.head?.getD false)) input query bits.tail [] []) := by
  have run := lift_run _ _ _ (FrameExtraction.whole_frame bits input query [])
  rw [show 3 * bits.length + 4 = (3 * bits.length + 3) + 1 by omega,
    Function.iterate_succ_apply']
  change (fun c => c.bind computer.step)
    ((fun c => c.bind computer.step)^[3 * bits.length + 3]
      (some (liftCfg (FrameExtraction.cfg (some .prefix) none
        (BinaryNatLists.frame bits ++ input) query [] [] [])))) = _
  rw [run]
  simpa only [List.append_nil] using! split_step none input query bits [] []

/-- The exact framed literal code yields its polarity and raw variable bits. -/
theorem whole_literal (literal : CNF.Literal Nat) (input query : List Bool) :
    (fun c => c.bind computer.step)^[3 * (encodeNat literal.toNat).length + 4]
      (some (cfg (some computer.main) none
        (BinaryNatLists.encodeNat literal.toNat ++ input) query [] [] [])) =
      some (cfg (some .done) (some (LiteralEvaluation.polarity literal))
        input query (encodeNat literal.var) [] []) := by
  simpa only [head_encode_toNat, tail_encode_toNat] using!
    whole_frame (encodeNat literal.toNat) input query

/-- Linear bound in the consumed literal frame's full bit length; final halt excluded. -/
def literal_evalsToInTime (literal : CNF.Literal Nat) (input query : List Bool) :
    EvalsToInTime computer.step
      (cfg (some computer.main) none
        (BinaryNatLists.encodeNat literal.toNat ++ input) query [] [] [])
      (some (cfg (some .done) (some (LiteralEvaluation.polarity literal))
        input query (encodeNat literal.var) [] []))
      (2 * BinaryNatLists.natWireSize literal.toNat + 2) where
  steps := 3 * (encodeNat literal.toNat).length + 4
  evals_in_steps := whole_literal literal input query
  steps_le_m := by unfold BinaryNatLists.natWireSize; omega

end LeanNPHardness.MachinePrimitives.PackedLiteral
