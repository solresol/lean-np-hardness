import LeanNPHardness.FramedFormulaRenameMachine

/-!
# Source-order unary output from a binary formula

The renaming traversal writes into an empty buffer. A final transfer places the
unary word ahead of the caller's output suffix and empties the buffer. The
framed dictionary and the unconsumed input are retained throughout.
-/

namespace LeanNPHardness.MachineAdapters.OrderedFormulaRename

open Computability Routines MachinePrimitives CNF.Unary

variable (c : LiteralRenameStep.Witness)

abbrev OutputAlphabet (_ : Unit) := CNF.Unary.Sym
abbrev Stack := ClauseListRename.Stack c ⊕ Unit
abbrev Alphabet := ExtendedAlphabet (Γ := ClauseListRename.Alphabet c) OutputAlphabet

private abbrev buffer : Stack c := .inl (.inl (.inl (.inr (.inr .output))))
private abbrev output : Stack c := .inr ()
private instance : Fintype (Alphabet c (buffer c)) := inferInstanceAs (Fintype Sym)

def contents (input dictionary : List Bool) (reversed out : List Sym) : Stacks (Alphabet c) :=
  extendedStacks OutputAlphabet (ClauseListRename.contents c input dictionary reversed [])
    (fun _ => out)

def restore : Routine (Alphabet c) := moveAll (buffer c) (output c) id .mark

/-- Restore the logical word in exactly two steps per symbol and one final test. -/
theorem restore_exits (input dictionary : List Bool) (word out : List Sym) :
    (restore c).Exits (contents c input dictionary word.reverse out) (2 * word.length + 1)
      (contents c input dictionary [] (word ++ out)) := by
  have run := moveAll_exits (Γ := Alphabet c) (buffer c) (output c) (by simp [buffer, output])
    id .mark (contents c input dictionary word.reverse out)
  change (restore c).Exits _ (2 * word.reverse.length + 1)
    (Function.update (Function.update _ (buffer c) []) (output c)
      ((word.reverse.map id).reverse ++ out)) at run
  simp only [List.length_reverse, List.map_id, List.reverse_reverse] at run
  convert run using 1
  funext k
  rcases k with (((k | (k | e)) | u) | v) | w
  · rfl
  · rfl
  · cases e <;> rfl
  · rfl
  · rfl
  · cases w; rfl

noncomputable def routine : Routine (Alphabet c) :=
  seq (extend OutputAlphabet (FramedFormulaRename.routine c)) (restore c)

/-- The empty formula takes four traversal steps and one empty-buffer test. -/
theorem empty_exits (input dictionary : List Bool) (out : List Sym) :
    (routine c).Exits (contents c (false :: input) dictionary [] out) 5
      (contents c input dictionary [] out) :=
  seq_exits _ _ (extend_exits OutputAlphabet _ (fun _ => out)
    (FramedFormulaRename.empty_exits c input dictionary [])) (restore_exits c input dictionary [] out)

/-- Rename with a supplied dictionary, charging restoration by the actual number
of emitted symbols. Neither suffix contributes to the bound. -/
theorem formula_exits (formula : CNF.Formula Nat) (dict : List Nat)
    (input : List Bool) (out : List Sym) :
    let dictionary := BinaryNatLists.encodeNatList dict
    let word := encode (formula.rename dict.idxOf)
    (routine c).ExitsLE (contents c (formula.encode ++ input) dictionary [] out)
      ((FramedFormulaRename.timePolynomial c).eval (formula.encode.length + dictionary.length) +
        (2 * word.length + 1))
      (contents c input dictionary [] (word ++ out)) := by
  intro dictionary word
  obtain ⟨steps, bound, run⟩ := FramedFormulaRename.formula_exits c formula dict input []
  exact seq_exitsLE _ _ ⟨steps, bound, extend_exits OutputAlphabet _ (fun _ => out) run⟩
    (restore_exits c input dictionary word out).le

/-- Time in original formula bits with the formula's dictionary already present. -/
noncomputable def timePolynomial : Polynomial Nat :=
  (FramedFormulaRename.timePolynomial c).comp (4 * Polynomial.X + 1) +
    (2 * Polynomial.X * (Polynomial.X + 1) + 1)

/-- The complete dense unary encoding precedes the caller's suffix in source order. -/
theorem dense_formula_exits (formula : CNF.Formula Nat) (input : List Bool) (out : List Sym) :
    let c := LiteralRename.computableInPolyTime
    let dictionary := BinaryNatLists.encodeNatList formula.variableDictionary
    (routine c).ExitsLE (contents c (formula.encode ++ input) dictionary [] out)
      ((timePolynomial c).eval formula.encodedSize)
      (contents c input dictionary [] (encode formula.denseRename ++ out)) := by
  intro c dictionary
  obtain ⟨steps, bound, run⟩ := FramedFormulaRename.dense_formula_exits formula input []
  have traversal : (extend OutputAlphabet (FramedFormulaRename.routine c)).ExitsLE
      (contents c (formula.encode ++ input) dictionary [] out)
      ((FramedFormulaRename.timePolynomial c).eval (4 * formula.encodedSize + 1))
      (contents c input dictionary (encode formula.denseRename).reverse out) :=
    ⟨steps, bound, extend_exits OutputAlphabet _ (fun _ => out) run⟩
  apply (seq_exitsLE _ _ traversal (restore_exits c input dictionary (encode formula.denseRename) out).le).mono
  simp only [timePolynomial, Polynomial.eval_add, Polynomial.eval_comp, Polynomial.eval_mul,
    Polynomial.eval_X, Polynomial.eval_ofNat, Polynomial.eval_one, Nat.mul_assoc]
  have size := formula.denseRename_unary_length_le
  omega

end LeanNPHardness.MachineAdapters.OrderedFormulaRename
