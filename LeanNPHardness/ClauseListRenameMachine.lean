import LeanNPHardness.FramedClauseRenameMachine
import LeanNPHardness.CountedFormulaMachine

/-!
# Dense renaming of a counted list of framed clauses

The caller supplies the decoded clause count. The outer loop pops one mark
before each complete-clause call. Its output stack holds the logical prefix
in reverse, including a terminator for every clause. The dictionary and the
bits following the formula body are available to the caller on exit.
-/

namespace LeanNPHardness.MachineAdapters.ClauseListRename

open Computability Routines MachinePrimitives CNF.Unary

variable (c : LiteralRenameStep.Witness)

abbrev Stack := ClauseRename.Stack c ⊕ Unit
abbrev Alphabet := ExtendedAlphabet (Γ := ClauseRename.Alphabet c) ClauseRename.CountAlphabet

private abbrev remaining : Stack c := .inr ()

def contents (input dictionary : List Bool) (out : List Sym) (marks : List Bool) :
    Stacks (Alphabet c) :=
  extendedStacks ClauseRename.CountAlphabet (ClauseRename.contents c input dictionary out [])
    (fun _ => marks)

private noncomputable def iteration : Routine (Alphabet c) :=
  seq (popOne (remaining c)) (extend ClauseRename.CountAlphabet (FramedClauseRename.routine c))

/-- Stop at the decoded clause count, even when the unread suffix starts with another clause. -/
noncomputable def routine : Routine (Alphabet c) := loop (remaining c) (iteration c)

private theorem pop_exits (input dictionary : List Bool) (out : List Sym) (marks : List Bool) :
    (popOne (remaining c)).Exits (contents c input dictionary out (true :: marks)) 1
      (contents c input dictionary out marks) := by
  convert popOne_exits (Γ := Alphabet c) (remaining c) _ using 1
  funext j
  rcases j with j | ⟨⟩ <;> rfl

private theorem iteration_exits (clause : CNF.Clause Nat) (dict : List Nat)
    (input : List Bool) (prior : List Sym) (marks : List Bool) :
    let source := CountedFormula.clauseBits clause
    let dictionary := BinaryNatLists.encodeNatList dict
    (iteration c).ExitsLE (contents c (source ++ input) dictionary prior.reverse (true :: marks))
      (1 + (FramedClauseRename.timePolynomial c).eval (source.length + dictionary.length))
      (contents c input dictionary
        (prior ++ encodeClause (clause.map (CNF.Literal.rename dict.idxOf))).reverse marks) := by
  intro source dictionary
  obtain ⟨n, hn, run⟩ := FramedClauseRename.clause_exits c clause dict input prior
  exact seq_exitsLE _ _ (pop_exits c _ _ _ marks).le
    ⟨n, hn, extend_exits ClauseRename.CountAlphabet _ (fun _ => marks) run⟩

/-- A formula with no clauses exits in one test, with the entire caller state intact. -/
theorem empty_exits (input dictionary : List Bool) (out : List Sym) :
    (routine c).Exits (contents c input dictionary out []) 1 (contents c input dictionary out []) :=
  loop_exits_nil (remaining c) (iteration c) _ rfl

/-- Each empty clause consumes its one-bit zero header and emits one boundary.
The seven steps per clause include the outer test and pop. The final test costs one. -/
theorem empty_clauses_exits (n : Nat) (input dictionary : List Bool) (out : List Sym) :
    (routine c).Exits
      (contents c (List.replicate n false ++ input) dictionary out (List.replicate n true))
      (7 * n + 1) (contents c input dictionary (List.replicate n .endClause ++ out) []) := by
  induction n generalizing out with
  | zero => simpa using empty_exits c input dictionary out
  | succ n ih =>
      let tailInput := List.replicate n false ++ input
      let marks := List.replicate n true
      have step : (iteration c).Exits
          (contents c (false :: tailInput) dictionary out (true :: marks)) 6
          (contents c tailInput dictionary (.endClause :: out) marks) :=
        seq_exits _ _ (pop_exits c _ _ _ marks) (extend_exits ClauseRename.CountAlphabet _
          (fun _ => marks) (FramedClauseRename.empty_exits c tailInput dictionary out))
      have run := loop_exits_cons (remaining c) (iteration c) (List.cons_ne_nil true _)
        step (ih (.endClause :: out))
      rw [List.replicate_succ' (a := Sym.endClause), List.append_assoc]
      simpa only [routine, tailInput, marks, List.replicate_succ, List.cons_append,
        List.nil_append, Nat.mul_succ, Nat.add_assoc, Nat.add_comm 7] using run

private theorem loop_exits (formula : CNF.Formula Nat) (dict : List Nat)
    (input : List Bool) (prior : List Sym) (N : Nat)
    (hN : (CountedFormula.sourceBody formula).length + (BinaryNatLists.encodeNatList dict).length
      ≤ N) :
    let dictionary := BinaryNatLists.encodeNatList dict
    (routine c).ExitsLE
      (contents c (CountedFormula.sourceBody formula ++ input) dictionary prior.reverse
        (List.replicate formula.length true))
      (formula.length * ((FramedClauseRename.timePolynomial c).eval N + 2) + 1)
      (contents c input dictionary (prior ++ encode (formula.rename dict.idxOf)).reverse []) := by
  induction formula generalizing prior with
  | nil =>
      simpa [CountedFormula.sourceBody, CNF.Formula.rename] using
        (empty_exits c input (BinaryNatLists.encodeNatList dict) prior.reverse).le
  | cons clause rest ih =>
      let source := CountedFormula.clauseBits clause
      let word := encodeClause (clause.map (CNF.Literal.rename dict.idxOf))
      change (source ++ CountedFormula.sourceBody rest).length + _ ≤ N at hN
      rw [List.length_append] at hN
      have headBound : (FramedClauseRename.timePolynomial c).eval
          (source.length + (BinaryNatLists.encodeNatList dict).length) ≤
          (FramedClauseRename.timePolynomial c).eval N :=
        MachineRuntime.polynomial_eval_mono _ (by omega)
      have headRun := iteration_exits c clause dict (CountedFormula.sourceBody rest ++ input) prior
        (List.replicate rest.length true)
      have tailRun := ih (prior ++ word) (by omega)
      have run := loop_exitsLE_cons (remaining c) (iteration c)
        (List.cons_ne_nil true _) headRun tailRun
      have bound : 1 + (FramedClauseRename.timePolynomial c).eval
          (source.length + (BinaryNatLists.encodeNatList dict).length) + 1 +
          (rest.length * ((FramedClauseRename.timePolynomial c).eval N + 2) + 1) ≤
          (rest.length + 1) * ((FramedClauseRename.timePolynomial c).eval N + 2) + 1 := by
        rw [Nat.add_mul, Nat.one_mul]
        omega
      simpa only [routine, CountedFormula.sourceBody, List.flatMap_cons, CNF.Formula.rename,
        List.map_cons, encode_cons, List.length_cons, List.replicate_succ, word,
        List.append_assoc] using run.mono bound

/-- In body and dictionary bits, each clause costs a framed-clause call, a pop and a test. -/
noncomputable def timePolynomial : Polynomial Nat :=
  Polynomial.X * (FramedClauseRename.timePolynomial c + 2) + 1

/-- Consume exactly the counted clauses and append their unary renaming to the logical prefix. -/
theorem clauses_exits (formula : CNF.Formula Nat) (dict : List Nat)
    (input : List Bool) (prior : List Sym) :
    let source := CountedFormula.sourceBody formula
    let dictionary := BinaryNatLists.encodeNatList dict
    (routine c).ExitsLE
      (contents c (source ++ input) dictionary prior.reverse (List.replicate formula.length true))
      ((timePolynomial c).eval (source.length + dictionary.length))
      (contents c input dictionary (prior ++ encode (formula.rename dict.idxOf)).reverse []) := by
  intro source dictionary
  let N := source.length + dictionary.length
  have count : formula.length ≤ N :=
    (CountedFormula.count_le_body_length formula).trans (Nat.le_add_right _ _)
  apply (loop_exits c formula dict input prior N le_rfl).mono
  simp only [timePolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
    Polynomial.eval_ofNat, Polynomial.eval_one]
  exact Nat.add_le_add_right (Nat.mul_le_mul_right _ count) 1

/-- The formula's own dictionary gives precisely the unary word for its dense renaming. -/
theorem dense_clauses_exits (formula : CNF.Formula Nat) (input : List Bool) (prior : List Sym) :
    let c := LiteralRename.computableInPolyTime
    let dictionary := BinaryNatLists.encodeNatList formula.variableDictionary
    let source := CountedFormula.sourceBody formula
    (routine c).ExitsLE
      (contents c (source ++ input) dictionary prior.reverse (List.replicate formula.length true))
      ((timePolynomial c).eval (source.length + dictionary.length))
      (contents c input dictionary (prior ++ encode formula.denseRename).reverse []) :=
  clauses_exits LiteralRename.computableInPolyTime formula formula.variableDictionary input prior

end LeanNPHardness.MachineAdapters.ClauseListRename
