import LeanNPHardness.MarkedFormulaMachine
import LeanNPHardness.UnaryCountMachine

/-!
# Complete framed variable lists from binary formulas

Compose source-order marked extraction with binary header generation on the
same eight Boolean stacks. Header generation reuses emptied workspace, keeps
caller input untouched, and prepends the count above the body and output suffix.
The complete canonical-input conversion takes at most `N * (22N + 67) + 14`
steps in original formula bits. Occurrences, including repetitions and both
signs of zero, are retained. Malformed-input rejection and dense renaming are
separate obligations.
-/

namespace LeanNPHardness.MachinePrimitives.FormulaVariables

open Computability Turing Routines

abbrev Stack := MarkedFormula.Stack
abbrev Alphabet := MarkedFormula.Alphabet
abbrev contents := MarkedFormula.contents

/-- Header/count/work/buffer reuse the extraction buffer/count/work/inner stacks. -/
def headerStack : UnaryCount.Stack → Stack
  | .inl .input => .inl (.inl (.inl (.inl .output)))
  | .inl .count => .inl (.inl (.inl (.inl .count)))
  | .inl .work => .inl (.inl (.inl (.inl .work)))
  | .inl .output => .inl (.inl (.inl (.inr ())))
  | .inr .marks => .inr ()
  | .inr .output => .inl (.inr ())

def headerBits (k : UnaryCount.Stack) (bits : List (UnaryCount.Alphabet k)) :
    List (Alphabet (headerStack k)) :=
  match k with
  | .inl .input | .inl .count | .inl .work | .inl .output
  | .inr .marks | .inr .output => bits

/-- The input suffix and unused outer counter retain arbitrary contents. -/
def headerStacks (input outer : List Bool) (S : Stacks UnaryCount.Alphabet) :
    Stacks Alphabet :=
  contents input (S (.inl .count)) (S (.inl .work)) (S (.inl .input))
    (S (.inl .output)) outer (S (.inr .output)) (S (.inr .marks))

theorem headerStacks_update (input outer : List Bool) (S : Stacks UnaryCount.Alphabet)
    (k : UnaryCount.Stack) (bits : List (UnaryCount.Alphabet k)) :
    headerStacks input outer (Function.update S k bits) =
      Function.update (headerStacks input outer S) (headerStack k) (headerBits k bits) := by
  funext j
  rcases k with (k | k) <;> cases k <;>
    rcases j with ((((j | ⟨⟩) | ⟨⟩) | ⟨⟩) | ⟨⟩) <;> try cases j
  all_goals simp [headerStacks, contents, MarkedFormula.contents, OrderedFormula.contents,
    CountedFormula.contents, CountedLiteralBody.contents, FrameMove.contents,
    extendedStacks, headerStack, headerBits, Function.update]

variable {Λ σ : Type}

/-- Change only the six stack locations, retaining the finite control. -/
def headerStmt : TM2.Stmt UnaryCount.Alphabet Λ σ → TM2.Stmt Alphabet Λ σ
  | .push k f q => match k with
    | .inl .input => .push (.inl (.inl (.inl (.inl .output)))) f (headerStmt q)
    | .inl .count => .push (.inl (.inl (.inl (.inl .count)))) f (headerStmt q)
    | .inl .work => .push (.inl (.inl (.inl (.inl .work)))) f (headerStmt q)
    | .inl .output => .push (.inl (.inl (.inl (.inr ())))) f (headerStmt q)
    | .inr .marks => .push (.inr ()) f (headerStmt q)
    | .inr .output => .push (.inl (.inr ())) f (headerStmt q)
  | .peek k f q => match k with
    | .inl .input => .peek (.inl (.inl (.inl (.inl .output)))) f (headerStmt q)
    | .inl .count => .peek (.inl (.inl (.inl (.inl .count)))) f (headerStmt q)
    | .inl .work => .peek (.inl (.inl (.inl (.inl .work)))) f (headerStmt q)
    | .inl .output => .peek (.inl (.inl (.inl (.inr ())))) f (headerStmt q)
    | .inr .marks => .peek (.inr ()) f (headerStmt q)
    | .inr .output => .peek (.inl (.inr ())) f (headerStmt q)
  | .pop k f q => match k with
    | .inl .input => .pop (.inl (.inl (.inl (.inl .output)))) f (headerStmt q)
    | .inl .count => .pop (.inl (.inl (.inl (.inl .count)))) f (headerStmt q)
    | .inl .work => .pop (.inl (.inl (.inl (.inl .work)))) f (headerStmt q)
    | .inl .output => .pop (.inl (.inl (.inl (.inr ())))) f (headerStmt q)
    | .inr .marks => .pop (.inr ()) f (headerStmt q)
    | .inr .output => .pop (.inl (.inr ())) f (headerStmt q)
  | .load f q => .load f (headerStmt q)
  | .branch t a b => .branch t (headerStmt a) (headerStmt b)
  | .goto f => .goto f
  | .halt => .halt

def headerCfg (input outer : List Bool) (c : TM2.Cfg UnaryCount.Alphabet Λ σ) :
    TM2.Cfg Alphabet Λ σ :=
  ⟨c.l, c.var, headerStacks input outer c.stk⟩

/-- Relocated instructions preserve both untouched stacks at the same cost. -/
theorem headerStmt_stepAux (input outer : List Bool)
    (stmt : TM2.Stmt UnaryCount.Alphabet Λ σ) (v : σ) (S : Stacks UnaryCount.Alphabet) :
    TM2.stepAux (headerStmt stmt) v (headerStacks input outer S) =
      headerCfg input outer (TM2.stepAux stmt v S) := by
  induction stmt generalizing v S with
  | push k f q ih =>
      have run := ih v (Function.update S k (f v :: S k))
      rw [headerStacks_update] at run
      rcases k with (k | k) <;> cases k <;> exact run
  | peek k f q ih =>
      rcases k with (k | k) <;> cases k <;> exact ih _ _
  | pop k f q ih =>
      have run := ih (f v (S k).head?) (Function.update S k (S k).tail)
      rw [headerStacks_update] at run
      rcases k with (k | k) <;> cases k <;> exact run
  | load f q ih => exact ih _ _
  | branch t a b iha ihb =>
      cases h : t v
      · simpa only [headerStmt, TM2.stepAux, h, Bool.cond_false] using ihb v S
      · simpa only [headerStmt, TM2.stepAux, h, Bool.cond_true] using iha v S
  | goto f => rfl
  | halt => rfl

theorem header_step (input outer : List Bool)
    (program : Λ → TM2.Stmt UnaryCount.Alphabet Λ σ) (c : TM2.Cfg UnaryCount.Alphabet Λ σ) :
    TM2.step (fun l => headerStmt (program l)) (headerCfg input outer c) =
      (TM2.step program c).map (headerCfg input outer) := by
  rcases c with ⟨l, v, S⟩
  cases l with
  | none => rfl
  | some l => simp only [headerCfg, TM2.step, headerStmt_stepAux, Option.map_some]

theorem header_run (input outer : List Bool)
    (program : Λ → TM2.Stmt UnaryCount.Alphabet Λ σ) (n : Nat)
    (c : Option (TM2.Cfg UnaryCount.Alphabet Λ σ)) :
    (flip Option.bind (TM2.step (fun l => headerStmt (program l))))^[n]
        (c.map (headerCfg input outer)) =
      ((flip Option.bind (TM2.step program))^[n] c).map (headerCfg input outer) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
      cases c with
      | none => exact ih none
      | some c =>
          simpa only [flip, Option.map_some, Option.bind_some, header_step] using
            ih (TM2.step program c)

def headerRoutine (r : Routine UnaryCount.Alphabet) : Routine Alphabet where
  Λ := r.Λ
  σ := r.σ
  entry := r.entry
  init := r.init
  program l := headerStmt (r.program l)

theorem headerRoutine_exits (r : Routine UnaryCount.Alphabet) (input outer : List Bool)
    {S S' : Stacks UnaryCount.Alphabet} {n : Nat} (h : r.Exits S n S') :
    (headerRoutine r).Exits (headerStacks input outer S) n
      (headerStacks input outer S') := by
  obtain ⟨v, h⟩ := h
  refine ⟨v, ?_⟩
  have run := header_run input outer r.program n (some ⟨some r.entry, r.init, S⟩)
  rw [h] at run
  exact run

/-- Count occurrence marks without scanning caller input or the restored output. -/
theorem header_exits (n : Nat) (input outer output : List Bool) :
    (headerRoutine UnaryCount.routine).Exits
      (contents input [] [] [] [] outer output (List.replicate n true))
      (UnaryCount.runSteps n)
      (contents input [] [] [] [] outer (BinaryNatLists.encodeNat n ++ output) []) :=
  headerRoutine_exits UnaryCount.routine input outer (UnaryCount.natural_exits n output)

def routine : Routine Alphabet := seq MarkedFormula.routine (headerRoutine UnaryCount.routine)

def runBound (formula : CNF.Formula Nat) : Nat :=
  MarkedFormula.runBound formula + UnaryCount.runSteps formula.vars.length

/-- The complete framed variable list, in source order, with both arbitrary suffixes. -/
theorem formula_exits (formula : CNF.Formula Nat) (input output : List Bool) :
    routine.ExitsLE
      (contents (formula.encode ++ input) [] [] [] [] [] output [])
      (runBound formula)
      (contents input [] [] [] [] [] (BinaryNatLists.encodeNatList formula.vars ++ output) []) := by
  have run := seq_exitsLE _ _ (MarkedFormula.formula_exits formula input output)
    (header_exits formula.vars.length input []
      (formula.vars.flatMap BinaryNatLists.encodeNat ++ output)).le
  simpa only [routine, runBound, BinaryNatLists.encodeNatList, List.append_assoc] using run

/-- Charge both phases in original formula bits, independently of caller suffix lengths. -/
theorem runBound_le (formula : CNF.Formula Nat) :
    runBound formula ≤ formula.encode.length * (22 * formula.encode.length + 67) + 14 := by
  have he := MarkedFormula.runBound_le formula
  have hh := UnaryCount.runSteps_le formula.vars.length
  have hm := OrderedFormula.vars_length_le formula
  have hp := Nat.mul_le_mul hm (Nat.add_le_add_right (Nat.mul_le_mul_left 12 hm) 30)
  unfold runBound
  nlinarith

theorem formula_exitsLE (formula : CNF.Formula Nat) (input output : List Bool) :
    routine.ExitsLE
      (contents (formula.encode ++ input) [] [] [] [] [] output [])
      (formula.encode.length * (22 * formula.encode.length + 67) + 14)
      (contents input [] [] [] [] [] (BinaryNatLists.encodeNatList formula.vars ++ output) []) :=
  (formula_exits formula input output).mono (runBound_le formula)

/-- The new count header and occurrence body together use at most `3N + 1` bits. -/
theorem output_length_le (formula : CNF.Formula Nat) (output : List Bool) :
    (BinaryNatLists.encodeNatList formula.vars ++ output).length ≤
      3 * formula.encode.length + 1 + output.length := by
  have hb := OrderedFormula.output_length_le formula output
  have hh := UnaryCount.header_length_le formula.vars.length
  have hm := OrderedFormula.vars_length_le formula
  simp only [BinaryNatLists.encodeNatList, List.length_append] at hb ⊢
  omega

def computer : FinTM2 := toMachine routine (.inl (.inl (.inl (.inl .input)))) (.inl (.inr ()))

/-- Canonical full output includes empty workspace, control reset and halt. -/
noncomputable def outputsInTime (formula : CNF.Formula Nat) :
    TM2OutputsInTime computer formula.encode (some (BinaryNatLists.encodeNatList formula.vars))
      (formula.encode.length * (22 * formula.encode.length + 67) + 14) := by
  apply toMachine_outputsInTime_le routine (.inl (.inl (.inl (.inl .input)))) (.inl (.inr ()))
  have hi : (initList computer formula.encode).stk =
      contents formula.encode [] [] [] [] [] [] [] := by
    funext k
    rcases k with ((((k | ⟨⟩) | ⟨⟩) | ⟨⟩) | ⟨⟩) <;> try cases k
    all_goals rfl
  have ho : (haltList computer (BinaryNatLists.encodeNatList formula.vars)).stk =
      contents [] [] [] [] [] [] (BinaryNatLists.encodeNatList formula.vars) [] := by
    funext k
    rcases k with ((((k | ⟨⟩) | ⟨⟩) | ⟨⟩) | ⟨⟩) <;> try cases k
    all_goals rfl
  change routine.ExitsLE (initList computer _).stk _ (haltList computer _).stk
  rw [hi, ho]
  simpa only [List.append_nil] using formula_exitsLE formula [] []

/-- Standalone occurrence-preserving conversion from binary CNF to a framed natural list. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime CNF.Formula.finEncoding FramedNatList.finEncoding CNF.Formula.vars where
  tm := computer
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := Polynomial.X * (22 * Polynomial.X + 67) + 14
  outputsFun formula := by
    simpa [CNF.Formula.finEncoding, FramedNatList.finEncoding, Equiv.refl,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X] using outputsInTime formula

end LeanNPHardness.MachinePrimitives.FormulaVariables
