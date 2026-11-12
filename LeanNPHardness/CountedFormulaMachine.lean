import LeanNPHardness.CountedClauseMachine
import LeanNPHardness.CNFCertificate

/-!
# Counted formula traversal with a global variable-order invariant

A sixth Boolean stack counts clauses independently of their literal counts.
The accumulator contains the reverse of all variable occurrences processed so
far, including repetitions across clause boundaries. Each canonical clause is
consumed exactly once; empty clauses still consume one outer mark. Arbitrary
input and output suffixes survive, and all counters and scratch finish empty.

The full routine reads the formula's binary clause count before the loop.
Bounds use the original formula bits, not the numeric count's binary header
alone. Output is a reverse-ordered variable body: restoring global source order,
adding the variable count header, standalone packaging, and dense renaming
remain separate obligations.
-/

namespace LeanNPHardness.MachinePrimitives.CountedFormula

open Computability Routines

abbrev ExtraAlphabet (_ : Unit) := Bool
abbrev Stack := CountedLiteralBody.Stack ⊕ Unit
abbrev Alphabet := ExtendedAlphabet (Γ := CountedLiteralBody.Alphabet) ExtraAlphabet

instance (k : Stack) : Fintype (Alphabet k) := by
  cases k with
  | inl k => exact inferInstanceAs (Fintype (CountedLiteralBody.Alphabet k))
  | inr k => exact inferInstanceAs (Fintype Bool)

abbrev outerStack : Stack := .inr ()
abbrev innerStack : Stack := .inl CountedLiteralBody.remainingStack

def contents (input count work output inner outer : List Bool) : Stacks Alphabet :=
  extendedStacks ExtraAlphabet
    (CountedLiteralBody.contents input count work output inner) (fun _ => outer)

/-- A complete encoded clause, including its framed literal count. -/
def clauseBits (clause : CNF.Clause Nat) : List Bool :=
  BinaryNatLists.encodeNatList (clause.map CNF.Literal.toNat)

/-- Formula body after its outer count header, retaining all clause boundaries. -/
def sourceBody (formula : CNF.Formula Nat) : List Bool :=
  formula.flatMap clauseBits

/-- Pop exactly one outer mark before consuming a complete clause. -/
def body : Routine Alphabet :=
  seq (popOne outerStack) (extend ExtraAlphabet CountedClause.routine)

theorem body_exits (clause : CNF.Clause Nat) (input output outer : List Bool) :
    body.ExitsLE
      (contents (clauseBits clause ++ input) [] [] output [] (true :: outer))
      (1 + CountedClause.runBound clause)
      (contents input [] []
        (clause.vars.reverse.flatMap BinaryNatLists.encodeNat ++ output) [] outer) := by
  have hp : (popOne (Γ := Alphabet) outerStack).Exits
      (contents (clauseBits clause ++ input) [] [] output [] (true :: outer)) 1
      (contents (clauseBits clause ++ input) [] [] output [] outer) := by
    convert popOne_exits (Γ := Alphabet) outerStack
      (contents (clauseBits clause ++ input) [] [] output [] (true :: outer)) using 1
    funext k
    cases k with
    | inl k => rfl
    | inr u => cases u; rfl
  obtain ⟨n, hn, hc⟩ := CountedClause.clause_exits clause input output
  have hc' := extend_exits ExtraAlphabet CountedClause.routine (fun _ => outer) hc
  refine ⟨1 + n, Nat.add_le_add_left hn 1, ?_⟩
  simpa only [body, contents, CNF.Clause.vars, ← List.map_reverse, List.flatMap_map,
    Function.comp_def] using seq_exits _ _ hp hc'

/-- Only the independent outer count determines the formula boundary. -/
def traversal : Routine Alphabet := loop outerStack body

/-- Per-clause bounds plus the outer pop/test overhead and final empty test. -/
def traversalBound : CNF.Formula Nat → Nat
  | [] => 1
  | clause :: formula => CountedClause.runBound clause + 2 + traversalBound formula

/-- The accumulator reverses all occurrences globally, not just within each clause. -/
theorem traversal_exits (formula : CNF.Formula Nat) (input output : List Bool) :
    traversal.ExitsLE
      (contents (sourceBody formula ++ input) [] [] output []
        (List.replicate formula.length true))
      (traversalBound formula)
      (contents input [] []
        (formula.vars.reverse.flatMap BinaryNatLists.encodeNat ++ output) [] []) := by
  induction formula generalizing output with
  | nil =>
      simpa only [traversal, traversalBound, sourceBody, CNF.Formula.vars,
        List.flatMap_nil, List.reverse_nil, List.nil_append, List.length_nil,
        List.replicate_zero] using
        (loop_exits_nil outerStack body (contents input [] [] output [] []) rfl).le
  | cons clause formula ih =>
      have hb := body_exits clause (sourceBody formula ++ input) output
        (List.replicate formula.length true)
      have ht := ih (clause.vars.reverse.flatMap BinaryNatLists.encodeNat ++ output)
      have hn : contents (clauseBits clause ++ (sourceBody formula ++ input))
          [] [] output [] (true :: List.replicate formula.length true) outerStack ≠ [] := by
        simp [contents, outerStack, extendedStacks]
      have run := loop_exitsLE_cons outerStack body hn hb ht
      have cost : 1 + CountedClause.runBound clause + 1 + traversalBound formula =
          CountedClause.runBound clause + 2 + traversalBound formula := by omega
      rw [cost] at run
      simpa only [traversal, traversalBound, sourceBody, List.flatMap_cons,
        CNF.Formula.vars, List.reverse_append, List.flatMap_append, List.append_assoc,
        List.length_cons, List.replicate_succ, Nat.add_assoc] using run

/-- An empty clause still has a one-bit count frame. -/
theorem clauseBits_length_pos (clause : CNF.Clause Nat) : 1 ≤ (clauseBits clause).length := by
  simp only [clauseBits, BinaryNatLists.encodeNatList, List.length_append,
    BinaryNatLists.encodeNat, BinaryNatLists.frame_length]
  omega

/-- The numeric outer count is bounded by the consumed clause-body bits. -/
theorem count_le_body_length (formula : CNF.Formula Nat) :
    formula.length ≤ (sourceBody formula).length := by
  induction formula with
  | nil => simp [sourceBody]
  | cons clause formula ih =>
      have hp := clauseBits_length_pos clause
      simp only [sourceBody, List.flatMap_cons, List.length_append, List.length_cons] at ih ⊢
      omega

/-- Charge every clause and count operation to the original body bits. -/
theorem traversalBound_le (formula : CNF.Formula Nat) :
    traversalBound formula ≤
      (sourceBody formula).length * (5 * (sourceBody formula).length + 21) + 1 := by
  induction formula with
  | nil => simp [traversalBound, sourceBody]
  | cons clause formula ih =>
      have hc := CountedClause.runBound_le clause
      have hp := clauseBits_length_pos clause
      change CountedClause.runBound clause ≤
        (clauseBits clause).length * (5 * (clauseBits clause).length + 15) + 4 at hc
      change CountedClause.runBound clause + 2 + traversalBound formula ≤ _
      simp only [sourceBody, List.flatMap_cons, List.length_append] at ih ⊢
      nlinarith

/-- Output size is a separate statement from the machine runtime. -/
theorem output_length_le (formula : CNF.Formula Nat) (output : List Bool) :
    (formula.vars.reverse.flatMap BinaryNatLists.encodeNat ++ output).length ≤
      (sourceBody formula).length + output.length := by
  have h : (formula.vars.reverse.flatMap BinaryNatLists.encodeNat).length ≤
      (sourceBody formula).length := by
    induction formula with
    | nil => simp [CNF.Formula.vars, sourceBody]
    | cons clause formula ih =>
        have hc := CountedClause.output_length_le clause []
        simp only [List.append_nil, List.length_nil, Nat.add_zero] at hc
        simp only [CNF.Formula.vars, CNF.Clause.vars, List.flatMap_cons,
          List.reverse_append, List.flatMap_append, ← List.map_reverse,
          List.flatMap_map, List.length_append, sourceBody,
          clauseBits] at ih ⊢
        omega
  simpa only [List.length_append] using Nat.add_le_add_right h output.length

/-- Move the loaded outer marks away from the clause routine's inner counter. -/
def moveCount : Routine Alphabet := moveAll innerStack outerStack (fun b => b) false

/-- Unary marks may be reversed; they represent exactly the same count. -/
theorem moveCount_exits (n : Nat) (input output : List Bool) :
    moveCount.Exits (contents input [] [] output (List.replicate n true) [])
      (2 * n + 1) (contents input [] [] output [] (List.replicate n true)) := by
  convert moveAll_exits (Γ := Alphabet) innerStack outerStack (by decide)
    (fun b => b) false (contents input [] [] output (List.replicate n true) []) using 1
  · rfl
  · simp [contents, innerStack, CountedLiteralBody.contents,
      CountedLiteralBody.remainingStack, extendedStacks]
  · funext k
    cases k with
    | inl k =>
        cases k with
        | inl k => cases k <;> simp [contents, innerStack, outerStack,
            CountedLiteralBody.contents, CountedLiteralBody.remainingStack,
            FrameMove.contents, extendedStacks, Function.update]
        | inr u => cases u; simp [contents, innerStack, outerStack,
            CountedLiteralBody.contents, CountedLiteralBody.remainingStack,
            extendedStacks, Function.update]
    | inr u => cases u; simp [contents, innerStack, outerStack,
        CountedLiteralBody.contents, CountedLiteralBody.remainingStack,
        extendedStacks, Function.update]

/-- Load the outer count, isolate it, and traverse exactly its complete clauses. -/
def routine : Routine Alphabet :=
  seq (seq (extend ExtraAlphabet CountHeader.routine) moveCount) traversal

def runBound (formula : CNF.Formula Nat) : Nat :=
  (encodeNat formula.length).length * (5 * formula.length + 8) + 3 +
    (2 * formula.length + 1) + traversalBound formula

/-- Identify the consumed body with the existing canonical formula encoding. -/
theorem encode_eq (formula : CNF.Formula Nat) :
    formula.encode = BinaryNatLists.encodeNat formula.length ++ sourceBody formula := by
  simp only [CNF.Formula.encode, BinaryNatLists.encode, CNF.Formula.toNatLists,
    List.length_map, List.flatMap_map, sourceBody]
  rfl

/-- Consume a complete formula, preserving both suffixes and all variable occurrences. -/
theorem formula_exits (formula : CNF.Formula Nat) (input output : List Bool) :
    routine.ExitsLE (contents (formula.encode ++ input) [] [] output [] [])
      (runBound formula)
      (contents input [] []
        (formula.vars.reverse.flatMap BinaryNatLists.encodeNat ++ output) [] []) := by
  obtain ⟨n, hn, header⟩ := CountHeader.natural_exits formula.length
    (sourceBody formula ++ input) output
  have load : (extend ExtraAlphabet CountHeader.routine).ExitsLE
      (contents (BinaryNatLists.encodeNat formula.length ++ (sourceBody formula ++ input))
        [] [] output [] [])
      ((encodeNat formula.length).length * (5 * formula.length + 8) + 3)
      (contents (sourceBody formula ++ input) [] [] output
        (List.replicate formula.length true) []) :=
    ⟨n, hn, extend_exits ExtraAlphabet CountHeader.routine (fun _ => []) header⟩
  have move := moveCount_exits formula.length (sourceBody formula ++ input) output
  have walk := traversal_exits formula input output
  simpa only [routine, runBound, encode_eq, List.append_assoc] using
    seq_exitsLE _ _ (seq_exitsLE _ _ load move.le) walk

/-- Quadratic bound in all original formula bits, independent of the retained suffixes. -/
theorem runBound_le (formula : CNF.Formula Nat) :
    runBound formula ≤ formula.encode.length * (10 * formula.encode.length + 31) + 5 := by
  let N := formula.encode.length
  let B := (sourceBody formula).length
  have hN : N = 2 * (encodeNat formula.length).length + 1 + B := by
    simp only [N, B, encode_eq, List.length_append, BinaryNatLists.encodeNat,
      BinaryNatLists.frame_length]
  have hb : (encodeNat formula.length).length ≤ N := by omega
  have hB : B ≤ N := by omega
  have hm : formula.length ≤ N := (count_le_body_length formula).trans hB
  have hh := Nat.mul_le_mul hb (show 5 * formula.length + 8 ≤ 5 * N + 8 by omega)
  have ht := (traversalBound_le formula).trans
    (Nat.add_le_add_right (Nat.mul_le_mul hB (by omega : 5 * B + 21 ≤ 5 * N + 21)) 1)
  change runBound formula ≤ N * (10 * N + 31) + 5
  unfold runBound
  nlinarith

/-- Complete canonical formula traversal with an explicit original-bit runtime bound. -/
theorem formula_exitsLE (formula : CNF.Formula Nat) (input output : List Bool) :
    routine.ExitsLE (contents (formula.encode ++ input) [] [] output [] [])
      (formula.encode.length * (10 * formula.encode.length + 31) + 5)
      (contents input [] []
        (formula.vars.reverse.flatMap BinaryNatLists.encodeNat ++ output) [] []) :=
  (formula_exits formula input output).mono (runBound_le formula)

/-- The emitted variable body is no longer than the consumed formula. -/
theorem formula_output_length_le (formula : CNF.Formula Nat) (output : List Bool) :
    (formula.vars.reverse.flatMap BinaryNatLists.encodeNat ++ output).length ≤
      formula.encode.length + output.length := by
  have h := output_length_le formula output
  simp only [encode_eq, List.length_append] at h ⊢
  omega

end LeanNPHardness.MachinePrimitives.CountedFormula
