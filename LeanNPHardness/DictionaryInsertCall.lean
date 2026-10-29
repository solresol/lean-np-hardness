import LeanNPHardness.DictionaryInsertInput
import LeanNPHardness.MachineRoutineCall

/-!
# Calling insertion while retaining a framed stream

The complete polynomial-time insertion machine runs on private stacks. The
caller keeps the unread stream and original header, and supplies a tagged
query/dictionary word. Two ordered transfers load the private machine and
return its framed result to the dictionary stack. Their costs are separate
from the insertion machine's polynomial. The repeated fold remains separate.
-/

namespace LeanNPHardness.MachineAdapters.DictionaryInsertCall

open Turing Routines MachinePrimitives

abbrev Witness := TM2ComputableInPolyTime
  (PairEncoding.finEncoding FramedNat.finEncoding FramedNatList.finEncoding)
  FramedNatList.finEncoding
  (fun input : Nat × List Nat => DictionaryConstruction.insert input.1 input.2)

abbrev ScratchAlphabet (_ : Unit) := Sum Bool Bool
abbrev CallerStack := DictionaryInsertInput.Stack ⊕ Unit
abbrev CallerAlphabet := ExtendedAlphabet (Γ := DictionaryInsertInput.Alphabet) ScratchAlphabet

variable (c : Witness)

abbrev Stack := c.tm.K ⊕ CallerStack
abbrev Alphabet := ExtendedAlphabet (Γ := c.tm.Γ) CallerAlphabet

abbrev pairStack : Stack c := .inr (.inl DictionaryInsertInput.pairStack)
abbrev scratchStack : Stack c := .inr (.inr ())
abbrev workStack : Stack c := .inr (.inl DictionaryInsertInput.countStack)
abbrev dictionaryStack : Stack c := .inr (.inl DictionaryInsertInput.dictionaryStack)

instance : Fintype (Alphabet c (pairStack c)) := inferInstanceAs (Fintype (Sum Bool Bool))
instance : Fintype (Alphabet c (scratchStack c)) := inferInstanceAs (Fintype (Sum Bool Bool))
instance : Fintype (Alphabet c (workStack c)) := inferInstanceAs (Fintype Bool)
noncomputable instance : Fintype (Alphabet c (.inl c.tm.k₁)) :=
  Fintype.ofEquiv Bool c.outputAlphabet.symm

def caller (input header dictionary : List Bool) (pair scratch : List (Sum Bool Bool))
    (work : List Bool := []) : Stacks CallerAlphabet :=
  extendedStacks ScratchAlphabet
    (DictionaryInsertInput.contents input work [] [] header dictionary pair) (fun _ => scratch)

def contents (machineStacks : Stacks c.tm.Γ) (input header dictionary : List Bool)
    (pair scratch : List (Sum Bool Bool)) (work : List Bool := []) : Stacks (Alphabet c) :=
  extendedStacks CallerAlphabet machineStacks (caller input header dictionary pair scratch work)

def empty : Stacks c.tm.Γ := fun _ => []

noncomputable def load : Routine (Alphabet c) :=
  seq (moveAll (Γ := Alphabet c) (pairStack c) (scratchStack c) id (.inl false))
    (moveAll (Γ := Alphabet c) (scratchStack c) (.inl c.tm.k₀)
      c.inputAlphabet.symm (c.inputAlphabet.symm (.inl false)))

local macro "caller_cases" : tactic => `(tactic|
  (rename_i k; rcases k with ((k | e) | u) | s <;>
    (try cases k) <;> (try cases e) <;> (try cases u) <;> (try cases s) <;>
    simp [contents, caller, DictionaryInsertInput.contents, FramedListReverse.contents,
      extendedStacks, FrameMove.contents, Function.update, pairStack, scratchStack,
      workStack, dictionaryStack, haltList, List.map_map, Function.comp_def]))

/-- Ordered loading through the actual input-alphabet equivalence. -/
theorem load_exits (word : List (Sum Bool Bool)) (input header : List Bool) :
    (load c).Exits (contents c (empty c) input header [] word [])
      (4 * word.length + 2)
      (contents c (initList c.tm (word.map c.inputAlphabet.symm)).stk input header [] [] []) := by
  have h₁ : (moveAll (Γ := Alphabet c) (pairStack c) (scratchStack c) id (.inl false)).Exits
      (contents c (empty c) input header [] word []) (2 * word.length + 1)
      (contents c (empty c) input header [] [] word.reverse) := by
    convert moveAll_exits (Γ := Alphabet c) (pairStack c) (scratchStack c) (by simp)
      id (.inl false) (contents c (empty c) input header [] word []) using 1
    · rfl
    · funext k; cases k
      · rfl
      · caller_cases
  have h₂ : (moveAll (Γ := Alphabet c) (scratchStack c) (.inl c.tm.k₀)
        c.inputAlphabet.symm (c.inputAlphabet.symm (.inl false))).Exits
      (contents c (empty c) input header [] [] word.reverse) (2 * word.length + 1)
      (contents c (initList c.tm (word.map c.inputAlphabet.symm)).stk input header [] [] []) := by
    convert moveAll_exits (Γ := Alphabet c) (scratchStack c) (.inl c.tm.k₀) (by simp)
      c.inputAlphabet.symm (c.inputAlphabet.symm (.inl false))
      (contents c (empty c) input header [] [] word.reverse) using 1
    · simp [contents, scratchStack, caller]
    · funext k; cases k with
      | inl k =>
          by_cases h : k = c.tm.k₀
          · subst k; simp [contents, empty, initList, caller, List.map_reverse]
          · simp [contents, empty, initList, Function.update, h]
      | inr k => caller_cases
  convert seq_exits _ _ h₁ h₂ using 1 <;> first | rfl | omega

/-- The complete insertion program, with all caller stacks retained. -/
def invoke : Routine (Alphabet c) := extend CallerAlphabet (ofMachine c.tm)

theorem invoke_exits (query : Nat) (dictionary : List Nat) (input header : List Bool) :
    ∃ n ≤ c.time.eval (DictionaryInsert.pairWord query dictionary).length,
      (invoke c).Exits
        (contents c (initList c.tm
          ((DictionaryInsert.pairWord query dictionary).map c.inputAlphabet.symm)).stk
          input header [] [] []) n
        (contents c (haltList c.tm
          ((BinaryNatLists.encodeNatList (DictionaryConstruction.insert query dictionary)).map
            c.outputAlphabet.symm)).stk input header [] [] []) := by
  exact ofMachine_extended_exits CallerAlphabet c.tm (caller input header [] [] []) _ _ _
    (c.outputsFun (query, dictionary))

/-- Return the canonical output through the actual output-alphabet equivalence. -/
noncomputable def returnResult : Routine (Alphabet c) :=
  seq (moveAll (Γ := Alphabet c) (.inl c.tm.k₁) (workStack c) c.outputAlphabet false)
    (moveAll (Γ := Alphabet c) (workStack c) (dictionaryStack c) id false)

theorem returnResult_exits (word input header : List Bool) :
    (returnResult c).Exits
      (contents c (haltList c.tm (word.map c.outputAlphabet.symm)).stk input header [] [] [])
      (4 * word.length + 2) (contents c (empty c) input header word [] []) := by
  have h₁ : (moveAll (Γ := Alphabet c) (.inl c.tm.k₁) (workStack c)
        c.outputAlphabet false).Exits
      (contents c (haltList c.tm (word.map c.outputAlphabet.symm)).stk input header [] [] [])
      (2 * word.length + 1) (contents c (empty c) input header [] [] [] word.reverse) := by
    convert moveAll_exits (Γ := Alphabet c) (.inl c.tm.k₁) (workStack c) (by simp)
      c.outputAlphabet false
      (contents c (haltList c.tm (word.map c.outputAlphabet.symm)).stk input header [] [] []) using 1
    · simp [contents, haltList]
    · funext k; cases k with
      | inl k =>
          by_cases h : k = c.tm.k₁
          · subst k; simp [contents, empty, haltList, workStack]
          · simp [contents, empty, haltList, Function.update, workStack, h]
      | inr k => caller_cases
  have h₂ : (moveAll (Γ := Alphabet c) (workStack c) (dictionaryStack c) id false).Exits
      (contents c (empty c) input header [] [] [] word.reverse) (2 * word.length + 1)
      (contents c (empty c) input header word [] []) := by
    convert moveAll_exits (Γ := Alphabet c) (workStack c) (dictionaryStack c) (by simp)
      id false (contents c (empty c) input header [] [] [] word.reverse) using 1
    · simp [contents, caller, workStack, DictionaryInsertInput.contents,
        FramedListReverse.contents, FrameMove.contents]
    · funext k; cases k
      · rfl
      · caller_cases
  convert seq_exits _ _ h₁ h₂ using 1 <;> first | rfl | omega

/-- Load, execute the full insertion machine, and return the updated dictionary. -/
noncomputable def routine : Routine (Alphabet c) := seq (load c) (seq (invoke c) (returnResult c))

/-- One insertion call preserves the unread stream and original header, clears
all private stacks and scratch, and returns the dictionary in original bit order. -/
theorem routine_exits (query : Nat) (dictionary : List Nat) (input header : List Bool) :
    ∃ n ≤ c.time.eval (DictionaryInsert.pairWord query dictionary).length,
      (routine c).Exits
        (contents c (empty c) input header [] (DictionaryInsert.pairWord query dictionary) [])
        (4 * (DictionaryInsert.pairWord query dictionary).length + 2 + n +
          (4 * (BinaryNatLists.encodeNatList (DictionaryConstruction.insert query dictionary)).length + 2))
        (contents c (empty c) input header
          (BinaryNatLists.encodeNatList (DictionaryConstruction.insert query dictionary)) [] []) := by
  obtain ⟨n, hn, run⟩ := invoke_exits c query dictionary input header
  refine ⟨n, hn, ?_⟩
  convert seq_exits _ _ (load_exits c (DictionaryInsert.pairWord query dictionary) input header)
    (seq_exits _ _ run (returnResult_exits c _ input header)) using 1 <;> first | rfl | omega

/-- Insertion adds at most the query frame and two count-header bits. -/
theorem output_length_le (query : Nat) (dictionary : List Nat) :
    (BinaryNatLists.encodeNatList (DictionaryConstruction.insert query dictionary)).length ≤
      (DictionaryInsert.pairWord query dictionary).length + 2 := by
  have sub := BinaryNatLists.encodeNatList_length_le_of_sublist
    (DictionaryConstruction.insert_sublist query dictionary)
  have growth := FramedSucc.frame_length_le (Computability.encodeNat dictionary.length)
  simp only [binarySuccBits_encodeNat] at growth
  simp only [DictionaryInsert.pairWord, List.length_append, List.length_map,
    BinaryNatLists.encodeNatList, List.length_cons, List.flatMap_cons,
    BinaryNatLists.encodeNat] at sub ⊢
  omega

/-- The insertion polynomial plus all loading and return costs, in original pair symbols. -/
noncomputable def timePolynomial : Polynomial Nat := c.time + 8 * Polynomial.X + 12

theorem bounded_exits (query : Nat) (dictionary : List Nat) (input header : List Bool) :
    ∃ steps ≤ (timePolynomial c).eval (DictionaryInsert.pairWord query dictionary).length,
      (routine c).Exits
        (contents c (empty c) input header [] (DictionaryInsert.pairWord query dictionary) []) steps
        (contents c (empty c) input header
          (BinaryNatLists.encodeNatList (DictionaryConstruction.insert query dictionary)) [] []) := by
  obtain ⟨n, hn, run⟩ := routine_exits c query dictionary input header
  refine ⟨_, ?_, run⟩
  have size := output_length_le query dictionary
  simp only [timePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_ofNat, Polynomial.eval_X]
  omega

/-- The retained-stream call instantiated with the repository's checked full
insertion machine, including membership and input retention. -/
theorem checked_exits (query : Nat) (dictionary : List Nat) (input header : List Bool) :
    ∃ steps ≤ (timePolynomial DictionaryInsert.computableInPolyTime).eval
        (DictionaryInsert.pairWord query dictionary).length,
      (routine DictionaryInsert.computableInPolyTime).Exits
        (contents DictionaryInsert.computableInPolyTime (empty DictionaryInsert.computableInPolyTime)
          input header [] (DictionaryInsert.pairWord query dictionary) []) steps
        (contents DictionaryInsert.computableInPolyTime (empty DictionaryInsert.computableInPolyTime)
          input header (BinaryNatLists.encodeNatList (DictionaryConstruction.insert query dictionary)) [] []) :=
  bounded_exits DictionaryInsert.computableInPolyTime query dictionary input header

end LeanNPHardness.MachineAdapters.DictionaryInsertCall
