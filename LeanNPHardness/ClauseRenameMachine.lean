import LeanNPHardness.LiteralRenameStep
import LeanNPHardness.CertificateMembershipLoopMachine

/-!
# Counted renaming of a clause body

The remaining-literal stack holds one mark per packed frame. Each iteration pops one
mark and appends one renamed literal to the reverse-stored output. On exhaustion
the routine pushes a single clause terminator, even when the starting count is zero.
The caller supplies the decoded count and retains the dictionary and unread input.
-/

namespace LeanNPHardness.MachineAdapters.ClauseRename

open Computability Routines MachinePrimitives CNF.Unary

abbrev CountAlphabet (_ : Unit) := Bool

variable (c : LiteralRenameStep.Witness)

abbrev Stack := LiteralRenameStep.Stack c ⊕ Unit
abbrev Alphabet := ExtendedAlphabet (Γ := LiteralRenameStep.Alphabet c) CountAlphabet

private abbrev remaining : Stack c := .inr ()
private abbrev output : Stack c := .inl (.inr (.inr .output))

def contents (input dict : List Bool) (out : List Sym) (marks : List Bool) :
    Stacks (Alphabet c) :=
  extendedStacks CountAlphabet (LiteralRenameStep.contents c input dict out) (fun _ => marks)

private noncomputable def iteration : Routine (Alphabet c) :=
  seq (popOne (remaining c)) (extend CountAlphabet (LiteralRenameStep.routine c))

private def finish : Routine (Alphabet c) := pushList (output c) [.endClause]

/-- Rename the counted body, then write its boundary. -/
noncomputable def routine : Routine (Alphabet c) :=
  seq (loop (remaining c) (iteration c)) (finish c)

private theorem iteration_exits (lit : CNF.Literal Nat) (dict : List Nat)
    (input : List Bool) (out : List Sym) (marks : List Bool) :
    let frame := BinaryNatLists.encodeNat lit.toNat
    let dictionary := BinaryNatLists.encodeNatList dict
    (iteration c).ExitsLE (contents c (frame ++ input) dictionary out (true :: marks))
      (1 + (LiteralRenameStep.timePolynomial c).eval (frame.length + dictionary.length))
      (contents c input dictionary ((encodeLiteral (LiteralRename.rename (lit, dict))).reverse ++ out)
        marks) := by
  dsimp only
  obtain ⟨n, hn, renameRun⟩ := LiteralRenameStep.bounded_exits c lit dict input out
  have pop : (popOne (Γ := Alphabet c) (remaining c)).Exits
      (contents c (BinaryNatLists.encodeNat lit.toNat ++ input)
        (BinaryNatLists.encodeNatList dict) out (true :: marks)) 1
      (contents c (BinaryNatLists.encodeNat lit.toNat ++ input)
        (BinaryNatLists.encodeNatList dict) out marks) := by
    convert popOne_exits (Γ := Alphabet c) (remaining c) _ using 1
    funext k
    rcases k with k | ⟨⟩ <;> simp [contents, remaining, Function.update]
  exact seq_exitsLE _ _ pop.le ⟨n, hn, extend_exits CountAlphabet _ (fun _ => marks) renameRun⟩

/-- Concatenation of the packed literal frames, excluding the clause count header. -/
def bodyBits (clause : CNF.Clause Nat) : List Bool :=
  clause.flatMap (fun l => BinaryNatLists.encodeNat l.toNat)

private def literalSymbols (clause : CNF.Clause Nat) (dict : List Nat) : List Sym :=
  clause.flatMap (fun l => encodeLiteral (LiteralRename.rename (l, dict)))

private theorem loop_exits (clause : CNF.Clause Nat) (dict : List Nat)
    (input : List Bool) (out : List Sym) (N : Nat)
    (hN : (bodyBits clause).length + (BinaryNatLists.encodeNatList dict).length ≤ N) :
    (loop (remaining c) (iteration c)).ExitsLE
      (contents c (bodyBits clause ++ input) (BinaryNatLists.encodeNatList dict) out
        (List.replicate clause.length true))
      (clause.length * ((LiteralRenameStep.timePolynomial c).eval N + 2) + 1)
      (contents c input (BinaryNatLists.encodeNatList dict)
        ((literalSymbols clause dict).reverse ++ out) []) := by
  induction clause generalizing out with
  | nil =>
      simpa [bodyBits, literalSymbols] using
        (loop_exits_nil (Γ := Alphabet c) (remaining c) (iteration c)
          (contents c input (BinaryNatLists.encodeNatList dict) out []) rfl).le
  | cons lit rest ih =>
      let frame := BinaryNatLists.encodeNat lit.toNat
      let word := encodeLiteral (LiteralRename.rename (lit, dict))
      change (frame ++ bodyBits rest).length + _ ≤ N at hN
      rw [List.length_append] at hN
      have headBound := MachineRuntime.polynomial_eval_mono (LiteralRenameStep.timePolynomial c)
        (show frame.length + (BinaryNatLists.encodeNatList dict).length ≤ N by omega)
      have headRun := iteration_exits c lit dict (bodyBits rest ++ input) out
        (List.replicate rest.length true)
      have tailRun := ih (word.reverse ++ out) (by omega)
      have joined := loop_exitsLE_cons (remaining c) (iteration c)
        (List.cons_ne_nil true _) headRun tailRun
      simp only [bodyBits, List.flatMap_cons, List.append_assoc, List.length_cons,
        List.replicate_succ, literalSymbols, List.reverse_append, Nat.add_mul, Nat.one_mul]
      apply joined.mono
      dsimp only [frame] at headBound
      omega

private theorem finish_exits (input dictionary : List Bool) (out : List Sym) :
    (finish c).Exits (contents c input dictionary out []) 1
      (contents c input dictionary (.endClause :: out) []) := by
  unfold finish
  convert pushList_exits (Γ := Alphabet c) (output c) [.endClause]
    (contents c input dictionary out []) using 1
  funext k
  rcases k with (k | (k | k)) | k
  · simp [contents, output, Function.update, LiteralRenameStep.contents, LiteralRenameStep.layout]
  · simp [contents, output, Function.update, LiteralRenameStep.contents, LiteralRenameStep.layout]
  · cases k <;> rfl
  · rfl

/-- With zero marks the empty-count test and terminator push take exactly two steps.
The unread input may already start with another clause. -/
theorem empty_exits (input dictionary : List Bool) (out : List Sym) :
    (routine c).Exits (contents c input dictionary out []) 2
      (contents c input dictionary (.endClause :: out) []) :=
  seq_exits _ _ (loop_exits_nil (remaining c) (iteration c) _ rfl)
    (finish_exits c input dictionary out)

/-- The input measure accounts for the complete dictionary and the literal frames.
A single call costs at most the literal-step polynomial. The loop adds a count
pop and test per occurrence, then a final test and one terminator push. -/
noncomputable def timePolynomial : Polynomial Nat :=
  Polynomial.X * (LiteralRenameStep.timePolynomial c + 2) + 2

/-- Consume the counted frames and append the exact unary clause to the logical prefix. -/
theorem clause_exits (clause : CNF.Clause Nat) (dict : List Nat)
    (input : List Bool) (prior : List Sym) :
    let dictionary := BinaryNatLists.encodeNatList dict
    (routine c).ExitsLE
      (contents c (bodyBits clause ++ input) dictionary prior.reverse
        (List.replicate clause.length true))
      ((timePolynomial c).eval ((bodyBits clause).length + dictionary.length))
      (contents c input dictionary
        (prior ++ encodeClause (clause.map (fun l => LiteralRename.rename (l, dict)))).reverse []) := by
  dsimp only
  let N := (bodyBits clause).length + (BinaryNatLists.encodeNatList dict).length
  have hbody : clause.length ≤ (bodyBits clause).length := by
    simpa only [bodyBits, List.length_map, List.flatMap_map, Function.comp_def] using
      CertificateMembershipLoop.length_le_body_length (clause.map CNF.Literal.toNat)
  have hcount : clause.length ≤ N := hbody.trans (Nat.le_add_right _ _)
  have run := seq_exitsLE _ _ (loop_exits c clause dict input prior.reverse N le_rfl)
    (finish_exits c _ _ _).le
  have bound := Nat.mul_le_mul_right ((LiteralRenameStep.timePolynomial c).eval N + 2) hcount
  simpa only [routine, encodeClause, List.flatMap_map, Function.comp_def, literalSymbols,
    List.reverse_append, List.reverse_singleton, List.singleton_append, List.cons_append,
    List.nil_append, List.append_assoc] using run.mono (m := (timePolynomial c).eval N) (by
      simp only [timePolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
        Polynomial.eval_ofNat]
      omega)

/-- For a formula's own dictionary the emitted clause is its dense renaming. -/
theorem dense_clause_exits (formula : CNF.Formula Nat) (clause : CNF.Clause Nat)
    (input : List Bool) (prior : List Sym) :
    let c := LiteralRename.computableInPolyTime
    let dictionary := BinaryNatLists.encodeNatList formula.variableDictionary
    (routine c).ExitsLE
      (contents c (bodyBits clause ++ input) dictionary prior.reverse
        (List.replicate clause.length true))
      ((timePolynomial c).eval ((bodyBits clause).length + dictionary.length))
      (contents c input dictionary
        (prior ++ encodeClause (clause.map (CNF.Literal.rename formula.denseIndex))).reverse []) := by
  simpa only [LiteralRename.rename_dense] using
    clause_exits LiteralRename.computableInPolyTime clause formula.variableDictionary input prior

end LeanNPHardness.MachineAdapters.ClauseRename
