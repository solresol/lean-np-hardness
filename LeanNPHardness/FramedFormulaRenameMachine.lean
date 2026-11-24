import LeanNPHardness.ClauseListRenameMachine
import LeanNPHardness.DictionaryConstruction

/-!
# Dense renaming from the binary formula header

The outer count decoder uses the same input and scratch as a clause decoder,
but writes its marks directly onto the formula counter. The literal counter
stays empty until the traversal starts reading the first clause.
-/

namespace LeanNPHardness.MachineAdapters.FramedFormulaRename

open Computability Routines MachinePrimitives CNF.Unary

variable (c : LiteralRenameStep.Witness)

/-- Reuse the clause header's instructions with its counter wired to the outer stack. -/
private def address : ClauseRename.Stack c → ClauseListRename.Stack c
  | .inl k => .inl (.inl k)
  | .inr u => .inr u

private def wiring : StackMap (ClauseRename.Alphabet c) (ClauseListRename.Alphabet c) where
  index := address c
  symbol k := by cases k <;> exact Equiv.refl _

def header : Routine (ClauseListRename.Alphabet c) := (wiring c).routine (FramedClauseRename.header c)

/-- Embed the decoder state, leaving the traversal's literal counter empty. -/
private def place (S : Stacks (ClauseRename.Alphabet c)) : Stacks (ClauseListRename.Alphabet c)
  | .inl (.inl k) => S (.inl k)
  | .inl (.inr _) => []
  | .inr u => S (.inr u)

private theorem place_contents (input dict : List Bool) (out : List Sym) (marks : List Bool) :
    place c (ClauseRename.contents c input dict out marks) =
      ClauseListRename.contents c input dict out marks := by
  funext j
  rcases j with (k | u) | u <;> rfl

private theorem place_exits {S S' : Stacks (ClauseRename.Alphabet c)} {steps : Nat}
    (run : (FramedClauseRename.header c).Exits S steps S') :
    (header c).Exits (place c S) steps (place c S') := by
  apply (wiring c).exits (place c) _ _ _ run
  · intro S k
    cases k <;> change _ = List.map id _ <;> rw [List.map_id] <;> rfl
  · intro S k w
    cases k with
    | inl k =>
        change _ = Function.update (place c S) (address c (.inl k)) (w.map id)
        rw [List.map_id]
        funext j
        rcases j with (j | _) | _
        · by_cases h : j = k
          · subst j; simp [place, address]
          · simp [place, address, Function.update, h]
        · rfl
        · rfl
    | inr u =>
        cases u
        change _ = Function.update (place c S) (address c (.inr ())) (w.map id)
        rw [List.map_id]
        funext j
        rcases j with (j | _) | ⟨⟩
        · rfl
        · rfl
        · simp [place, address]

/-- Decode the canonical outer frame without consuming any clause or suffix bits. -/
theorem header_exits (n : Nat) (input dict : List Bool) (out : List Sym) :
    (header c).ExitsLE
      (ClauseListRename.contents c (BinaryNatLists.encodeNat n ++ input) dict out [])
      ((encodeNat n).length * (5 * n + 8) + 3)
      (ClauseListRename.contents c input dict out (List.replicate n true)) := by
  obtain ⟨steps, bound, run⟩ := FramedClauseRename.header_exits c n input dict out
  exact ⟨steps, bound, by simpa only [place_contents] using place_exits c run⟩

noncomputable def routine : Routine (ClauseListRename.Alphabet c) :=
  seq (header c) (ClauseListRename.routine c)

/-- With no clauses, read the zero header and perform the final outer test. -/
theorem empty_exits (input dict : List Bool) (out : List Sym) :
    (routine c).Exits (ClauseListRename.contents c (false :: input) dict out []) 4
      (ClauseListRename.contents c input dict out []) := by
  have load := place_exits c (FramedClauseRename.zero_header_exits c input dict out)
  simp only [place_contents] at load
  exact seq_exits _ _ load (ClauseListRename.empty_exits c input dict out)

/-- Header and traversal time in the combined length of the full formula and dictionary. -/
noncomputable def timePolynomial : Polynomial Nat :=
  Polynomial.X * (5 * Polynomial.X + 8) + 3 + ClauseListRename.timePolynomial c

/-- Read the canonical formula, leave the dictionary and suffix intact, and append
the entire unary renaming to the logical prefix on the reverse output stack. -/
theorem formula_exits (formula : CNF.Formula Nat) (dict : List Nat)
    (input : List Bool) (prior : List Sym) :
    let dictionary := BinaryNatLists.encodeNatList dict
    (routine c).ExitsLE
      (ClauseListRename.contents c (formula.encode ++ input) dictionary prior.reverse [])
      ((timePolynomial c).eval (formula.encode.length + dictionary.length))
      (ClauseListRename.contents c input dictionary
        (prior ++ encode (formula.rename dict.idxOf)).reverse []) := by
  intro dictionary
  let body := CountedFormula.sourceBody formula
  let N := formula.encode.length + dictionary.length
  have size : N = 2 * (encodeNat formula.length).length + 1 + body.length + dictionary.length := by
    simp only [N, CountedFormula.encode_eq, List.length_append, BinaryNatLists.encodeNat,
      BinaryNatLists.frame_length, body]
  have count : formula.length ≤ body.length := CountedFormula.count_le_body_length formula
  have headerBound := Nat.mul_le_mul (show (encodeNat formula.length).length ≤ N by omega)
    (show 5 * formula.length + 8 ≤ 5 * N + 8 by omega)
  have bodyBound := MachineRuntime.polynomial_eval_mono (ClauseListRename.timePolynomial c)
    (show body.length + dictionary.length ≤ N by omega)
  have run := seq_exitsLE _ _ (header_exits c formula.length (body ++ input) dictionary prior.reverse)
    (ClauseListRename.clauses_exits c formula dict input prior)
  change (routine c).ExitsLE _ ((timePolynomial c).eval N) _
  rw [CountedFormula.encode_eq, List.append_assoc]
  apply run.mono
  simp only [timePolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
    Polynomial.eval_ofNat]
  exact Nat.add_le_add (Nat.add_le_add_right headerBound 3) bodyBound

/-- With the formula's dictionary in place, the output is its dense renaming.
The time bound depends only on the bit length of the original formula. -/
theorem dense_formula_exits (formula : CNF.Formula Nat) (input : List Bool) (prior : List Sym) :
    let c := LiteralRename.computableInPolyTime
    let dictionary := BinaryNatLists.encodeNatList formula.variableDictionary
    (routine c).ExitsLE
      (ClauseListRename.contents c (formula.encode ++ input) dictionary prior.reverse [])
      ((timePolynomial c).eval (4 * formula.encodedSize + 1))
      (ClauseListRename.contents c input dictionary (prior ++ encode formula.denseRename).reverse []) := by
  intro c dictionary
  apply (formula_exits c formula formula.variableDictionary input prior).mono
  apply MachineRuntime.polynomial_eval_mono
  rw [CNF.Formula.encode_length]
  have size := formula.variableDictionary_encode_length_le
  omega

end LeanNPHardness.MachineAdapters.FramedFormulaRename
