import LeanNPHardness.ClauseRenameMachine
import LeanNPHardness.CountedClauseMachine
import LeanNPHardness.MachineRoutineStackMap

/-!
# Dense renaming of a complete binary clause

The count decoder and clause loop share the raw input and remaining-literal
stacks. Reading the count frame therefore leaves the loop ready to run on the
first literal. Both stages retain the dictionary, output prefix and unread
input, including the next clause's header.
-/

namespace LeanNPHardness.MachineAdapters.FramedClauseRename

open Computability Routines MachinePrimitives CNF.Unary

variable (c : LiteralRenameStep.Witness)

private def index : CountHeader.Stack → ClauseRename.Stack c
  | .inl k => .inl (.inr (.inl k))
  | .inr u => .inr u

private def wiring : StackMap CountHeader.Alphabet (ClauseRename.Alphabet c) where
  index := index c
  symbol k := by cases k <;> exact Equiv.refl _

/-- Decode a framed binary count directly into the clause loop's counter. -/
def header : Routine (ClauseRename.Alphabet c) := (wiring c).routine CountHeader.routine

private def place (dict : List Bool) (out : List Sym) (S : Stacks CountHeader.Alphabet) :
    Stacks (ClauseRename.Alphabet c)
  | .inl (.inr (.inl k)) => S (.inl k)
  | .inr u => S (.inr u)
  | .inl (.inl _) => []
  | .inl (.inr (.inr .dictionary)) => dict
  | .inl (.inr (.inr .output)) => out

private theorem place_contents (input dict marks : List Bool) (out : List Sym) :
    place c dict out (CountHeader.contents input [] [] [] marks) =
      ClauseRename.contents c input dict out marks := by
  funext j
  rcases j with (p | (f | e)) | u
  · rfl
  · cases f <;> rfl
  · cases e <;> rfl
  · rfl

private theorem place_exits (dict : List Bool) (out : List Sym) {S S' : Stacks CountHeader.Alphabet}
    {n : Nat} (run : CountHeader.routine.Exits S n S') :
    (header c).Exits (place c dict out S) n (place c dict out S') := by
  apply (wiring c).exits (place c dict out) _ _ CountHeader.routine run
  · intro S k
    cases k <;> change _ = List.map id _ <;> rw [List.map_id] <;> rfl
  · intro S k w
    cases k with
    | inl k =>
        change _ = Function.update (place c dict out S) (index c (.inl k)) (w.map id)
        rw [List.map_id]
        funext j
        rcases j with (p | (f | e)) | u
        · rfl
        · by_cases h : f = k
          · subst f; simp [place, index]
          · simp [place, index, Function.update, h]
        · cases e <;> rfl
        · rfl
    | inr u =>
        cases u
        change _ = Function.update (place c dict out S) (index c (.inr ())) (w.map id)
        rw [List.map_id]
        funext j
        rcases j with (p | (f | e)) | ⟨⟩
        · rfl
        · rfl
        · cases e <;> rfl
        · simp [place, index]

/-- All count-decoding steps are charged, with no transfer between the two
counters because the decoder writes on the loop's own stack. -/
theorem header_exits (n : Nat) (input dict : List Bool) (out : List Sym) :
    (header c).ExitsLE
      (ClauseRename.contents c (BinaryNatLists.encodeNat n ++ input) dict out [])
      ((encodeNat n).length * (5 * n + 8) + 3)
      (ClauseRename.contents c input dict out (List.replicate n true)) := by
  obtain ⟨steps, bound, run⟩ := CountHeader.natural_exits n input []
  exact ⟨steps, bound, by simpa only [place_contents] using place_exits c dict out run⟩

/-- Read the count, consume the packed frames and emit one clause terminator. -/
noncomputable def routine : Routine (ClauseRename.Alphabet c) :=
  seq (header c) (ClauseRename.routine c)

/-- For the canonical zero header, two read steps, one decoder exit test,
one clause-loop exit test and one terminator push take exactly five steps. -/
theorem empty_exits (input dict : List Bool) (out : List Sym) :
    (routine c).Exits (ClauseRename.contents c (false :: input) dict out []) 5
      (ClauseRename.contents c input dict (.endClause :: out) []) := by
  have read := extend_exits CountedLiteralBody.ExtraAlphabet CountHeader.readBits (fun _ => [])
    (CountHeader.readBits_exits [] input [] [])
  have test := loop_exits_nil CountHeader.bitsStack (dispatch CountHeader.bitsStack CountHeader.horn)
    (CountHeader.contents input [] [] [] []) rfl
  have decoded : CountHeader.routine.Exits
      (CountHeader.contents (false :: input) [] [] [] []) 3 (CountHeader.contents input [] [] [] []) :=
    seq_exits _ _ read test
  have load := place_exits c dict out decoded
  simp only [place_contents] at load
  exact seq_exits _ _ load (ClauseRename.empty_exits c input dict out)

/-- The input length includes the count frame, all literal frames, and the
framed dictionary. Each occurrence contributes at least one body bit. -/
noncomputable def timePolynomial : Polynomial Nat :=
  Polynomial.X * (5 * Polynomial.X + 8) + 3 + ClauseRename.timePolynomial c

/-- One complete canonical clause extends the logical prefix with every renamed
literal in source order and its terminator. The next input bits remain in place. -/
theorem clause_exits (clause : CNF.Clause Nat) (dict : List Nat)
    (input : List Bool) (prior : List Sym) :
    let source := BinaryNatLists.encodeNatList (clause.map CNF.Literal.toNat)
    let dictionary := BinaryNatLists.encodeNatList dict
    (routine c).ExitsLE (ClauseRename.contents c (source ++ input) dictionary prior.reverse [])
      ((timePolynomial c).eval (source.length + dictionary.length))
      (ClauseRename.contents c input dictionary
        (prior ++ encodeClause (clause.map (fun l => LiteralRename.rename (l, dict)))).reverse []) := by
  intro source dictionary
  let N := source.length + dictionary.length
  have source_eq : source = BinaryNatLists.encodeNat clause.length ++ ClauseRename.bodyBits clause := by
    simp only [source, BinaryNatLists.encodeNatList, List.length_map, List.flatMap_map,
      ClauseRename.bodyBits]
  have size : N = 2 * (encodeNat clause.length).length + 1 +
      (ClauseRename.bodyBits clause).length + dictionary.length := by
    simp only [N, source_eq, List.length_append, BinaryNatLists.encodeNat, BinaryNatLists.frame_length]
  have count := CountedClause.count_le_body_length clause
  change clause.length ≤ (ClauseRename.bodyBits clause).length at count
  have headerBound := Nat.mul_le_mul
    (show (encodeNat clause.length).length ≤ N by omega)
    (show 5 * clause.length + 8 ≤ 5 * N + 8 by omega)
  have bodyBound := MachineRuntime.polynomial_eval_mono (ClauseRename.timePolynomial c)
    (show (ClauseRename.bodyBits clause).length + dictionary.length ≤ N by omega)
  have load := header_exits c clause.length (ClauseRename.bodyBits clause ++ input) dictionary
    prior.reverse
  have run := seq_exitsLE _ _ load (ClauseRename.clause_exits c clause dict input prior)
  have bounded := run.mono (m := (timePolynomial c).eval N) (by
    simp only [timePolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
      Polynomial.eval_ofNat]
    change _ + (ClauseRename.timePolynomial c).eval
      ((ClauseRename.bodyBits clause).length + dictionary.length) ≤ _
    exact Nat.add_le_add (Nat.add_le_add_right headerBound 3) bodyBound)
  change (routine c).ExitsLE _ ((timePolynomial c).eval N) _
  simpa only [routine, source_eq, List.append_assoc] using bounded

/-- With the formula dictionary, the complete binary clause emits its dense unary encoding. -/
theorem dense_clause_exits (formula : CNF.Formula Nat) (clause : CNF.Clause Nat)
    (input : List Bool) (prior : List Sym) :
    let c := LiteralRename.computableInPolyTime
    let source := BinaryNatLists.encodeNatList (clause.map CNF.Literal.toNat)
    let dictionary := BinaryNatLists.encodeNatList formula.variableDictionary
    (routine c).ExitsLE (ClauseRename.contents c (source ++ input) dictionary prior.reverse [])
      ((timePolynomial c).eval (source.length + dictionary.length))
      (ClauseRename.contents c input dictionary
        (prior ++ encodeClause (clause.map (CNF.Literal.rename formula.denseIndex))).reverse []) := by
  simpa only [LiteralRename.rename_dense] using
    clause_exits LiteralRename.computableInPolyTime clause formula.variableDictionary input prior

end LeanNPHardness.MachineAdapters.FramedClauseRename
