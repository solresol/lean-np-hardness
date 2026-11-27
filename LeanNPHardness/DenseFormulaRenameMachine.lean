import LeanNPHardness.TaggedFormulaRenameMachine

/-!
# Polynomial-time dense renaming from binary to unary CNF

Drain the dictionary after the tagged traversal, leaving only the unary output.
For an arbitrary supplied dictionary, a missing variable uses its length as
an index. The bound on the emitted word includes that extra case. Composing
the tagged machine with dictionary preparation gives a single-input machine.
-/

namespace LeanNPHardness.MachineAdapters.DenseFormulaRename

open Computability Turing Routines MachinePrimitives CNF.Unary
open TaggedFormulaRename (Stack Alphabet contents)

variable (c : LiteralRenameStep.Witness)

private abbrev inputStack : Stack c := .inr ()
private abbrev outputStack : Stack c := .inl (.inr ())
private abbrev dictionaryStack : Stack c :=
  .inl (.inl (.inl (.inl (.inr (.inr .dictionary)))))

/-- Clearing the retained dictionary costs two steps per bit and a final test.
The tagged input, unread formula and ordered output survive the drain. -/
theorem cleanup_exits (pair : List (Bool ⊕ Bool)) (input dictionary : List Bool)
    (out : List Sym) :
    (drain (Γ := Alphabet c) (dictionaryStack c)).Exits (contents c pair input dictionary out)
      (2 * dictionary.length + 1) (contents c pair input [] out) := by
  convert drain_exits (Γ := Alphabet c) (dictionaryStack c) (contents c pair input dictionary out)
    using 1 <;> try rfl
  funext j
  rcases j with ((((p | (f | e)) | u) | v) | w) | z <;>
    first | rfl | (cases e <;> rfl)

noncomputable def routine : Routine (Alphabet c) :=
  seq (TaggedFormulaRename.routine c) (drain (dictionaryStack c))

/-- The complete tagged wire contains both the dictionary and the original formula. -/
private theorem pair_length (dict : List Nat) (formula : CNF.Formula Nat) :
    (FormulaDictionary.outputEncoding.encode (dict, formula)).length =
      (BinaryNatLists.encodeNatList dict).length + formula.encode.length :=
  PairEncoding.finEncoding_encode_length _ _ _

/-- Each occurrence takes one sign plus its first dictionary index, including
the length sentinel. Every clause contributes one terminator. -/
theorem output_length_le (dict : List Nat) (formula : CNF.Formula Nat) :
    let n := (FormulaDictionary.outputEncoding.encode (dict, formula)).length
    (encode (formula.rename dict.idxOf)).length ≤ n * (n + 1) := by
  intro n
  have h := encode_length_le_of_vars_lt (formula.rename dict.idxOf) (dict.length + 1) (by
    intro x hx
    rw [CNF.Formula.vars_rename, List.mem_map] at hx
    obtain ⟨y, _, rfl⟩ := hx
    exact Nat.lt_succ_of_le List.idxOf_le_length)
  simp only [CNF.Formula.vars_rename, List.length_map, CNF.Formula.rename_length] at h
  have size : n = (BinaryNatLists.encodeNatList dict).length + formula.encode.length :=
    pair_length dict formula
  have vars := OrderedFormula.vars_length_le formula
  have clauses := CountedFormula.count_le_body_length formula
  have header : 0 < (BinaryNatLists.encodeNat formula.length).length := by
    rw [BinaryNatLists.encodeNat_length]
    exact BinaryNatLists.natWireSize_pos _
  have bits : formula.encode.length =
      (BinaryNatLists.encodeNat formula.length).length + (CountedFormula.sourceBody formula).length := by
    rw [CountedFormula.encode_eq, List.length_append]
  have dictCount : dict.length ≤ (BinaryNatLists.encodeNatList dict).length := by
    rw [BinaryNatLists.encodeNatList_length]
    exact BinaryNatLists.length_le_listWireSize _
  calc
    _ ≤ formula.vars.length * (dict.length + 1) + formula.length := h
    _ ≤ n * n + n := Nat.add_le_add (Nat.mul_le_mul (by omega) (by omega)) (by omega)
    _ = _ := by rw [Nat.mul_add, Nat.mul_one]

/-- Charge loading, the framed traversal, unary output restoration and dictionary
cleanup in the combined bit length of the supplied pair. -/
noncomputable def timePolynomial : Polynomial Nat :=
  FramedFormulaRename.timePolynomial c + 2 * Polynomial.X * (Polynomial.X + 1) +
    5 * Polynomial.X + 5

theorem routine_exits (dict : List Nat) (formula : CNF.Formula Nat) :
    let pair := FormulaDictionary.outputEncoding.encode (dict, formula)
    (routine c).ExitsLE (contents c pair [] [] []) ((timePolynomial c).eval pair.length)
      (contents c [] [] [] (encode (formula.rename dict.idxOf))) := by
  intro pair
  have traversal := TaggedFormulaRename.formula_exits c dict formula []
  simp only [List.append_nil] at traversal
  apply (seq_exitsLE _ _ traversal
    (cleanup_exits c [] [] (BinaryNatLists.encodeNatList dict) (encode (formula.rename dict.idxOf))).le).mono
  have size := pair_length dict formula
  have emitted := output_length_le dict formula
  simp only [timePolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
    Polynomial.eval_ofNat, Polynomial.eval_one, Nat.mul_assoc]
  dsimp only [pair]
  omega

private instance : Fintype (Alphabet c (inputStack c)) := inferInstanceAs (Fintype (Bool ⊕ Bool))

noncomputable def computer : FinTM2 := by
  letI : Fintype c.tm.K := c.tm.kFin
  exact toMachine (routine c) (inputStack c) (outputStack c)

/-- On every encoded pair the machine halts with reset control, empty workspace
and precisely the unary encoding on its output stack. -/
noncomputable def outputsInTime (dict : List Nat) (formula : CNF.Formula Nat) :
    let pair := FormulaDictionary.outputEncoding.encode (dict, formula)
    TM2OutputsInTime (computer c) pair (some (encode (formula.rename dict.idxOf)))
      ((timePolynomial c).eval pair.length) := by
  intro pair
  letI : Fintype c.tm.K := c.tm.kFin
  apply toMachine_outputsInTime_le (routine c) (inputStack c) (outputStack c)
  have initial : (initList (computer c) pair).stk = contents c pair [] [] [] := by
    funext j
    rcases j with ((((p | (f | e)) | ⟨⟩) | ⟨⟩) | ⟨⟩) | ⟨⟩ <;>
      first | rfl | (cases f <;> rfl) | (cases e <;> rfl)
  have final (out : List Sym) : (haltList (computer c) out).stk = contents c [] [] [] out := by
    funext j
    rcases j with ((((p | (f | e)) | ⟨⟩) | ⟨⟩) | ⟨⟩) | ⟨⟩ <;>
      first | rfl | (cases f <;> rfl) | (cases e <;> rfl)
  change (routine c).ExitsLE (initList (computer c) pair).stk _ (haltList (computer c) _).stk
  rw [initial, final]
  exact routine_exits c dict formula

/-- Rename from any encoded dictionary/formula pair, including dictionaries
with duplicate entries and dictionaries missing some formula variables. -/
noncomputable def pairComputableInPolyTime :
    TM2ComputableInPolyTime FormulaDictionary.outputEncoding finEncoding
      (fun p => p.2.rename p.1.idxOf) where
  tm := computer LiteralRename.computableInPolyTime
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := timePolynomial LiteralRename.computableInPolyTime
  outputsFun p := by
    simpa [Equiv.refl, finEncoding_encode] using
      outputsInTime LiteralRename.computableInPolyTime p.1 p.2

/-- Starting with one binary formula, build its dictionary and emit the complete
dense unary formula. Composition charges intermediate transfers in the original
formula's encoded bit length. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime CNF.Formula.finEncoding finEncoding CNF.Formula.denseRename :=
  MachineComposition.compositionComputableInPolyTime CNF.Formula.finEncoding
    FormulaDictionary.outputEncoding finEncoding FormulaDictionary.prepare
    (fun p => p.2.rename p.1.idxOf)
    FormulaDictionary.preservingComputableInPolyTime pairComputableInPolyTime

end LeanNPHardness.MachineAdapters.DenseFormulaRename
