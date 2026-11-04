import LeanNPHardness.DictionaryFold

/-!
# Standalone polynomial-time dictionary construction

Initialize an encoded empty seed, run the checked tail-first fold, and drain
its retained source header. The resulting finite TM2 computes the dictionary
from one complete framed list, with all workspace empty at the final halt.
-/

namespace LeanNPHardness.MachineAdapters.DictionaryBuild

open Turing Routines MachinePrimitives DictionaryInsertCall

variable (c : Witness)

abbrev inputStack : Stack c := DictionaryFold.inputStack c
abbrev headerStack : Stack c := .inr (.inl (.inl (.inr .header)))

instance : Fintype (Alphabet c (inputStack c)) := inferInstanceAs (Fintype Bool)

/-- The empty list still has a count header; it must be initialized explicitly. -/
def seedRoutine : Routine (Alphabet c) :=
  pushList (dictionaryStack c) (BinaryNatLists.encodeNatList [])

local macro "stack_cases" : tactic => `(tactic|
  (funext k; rcases k with k | (((k | e) | u) | s)
   · simp [contents, empty, caller, extendedStacks, Function.update, inputStack,
       DictionaryFold.inputStack, headerStack, dictionaryStack, initList, haltList]
   all_goals (try cases k) <;> (try cases e) <;> (try cases u) <;> (try cases s) <;>
     simp [contents, empty, caller, DictionaryInsertInput.contents, FramedListReverse.contents,
       extendedStacks, FrameMove.contents, Function.update, inputStack,
       DictionaryFold.inputStack, DictionaryInsertInput.inputStack,
       headerStack, dictionaryStack, DictionaryInsertInput.dictionaryStack,
       initList, haltList]))

/-- Initialization costs one TM2 step and preserves arbitrary input bits. -/
theorem seedRoutine_exits (input : List Bool) :
    (seedRoutine c).Exits (contents c (empty c) input [] [] [] []) 1
      (contents c (empty c) input [] (BinaryNatLists.encodeNatList []) [] []) := by
  convert pushList_exits (Γ := Alphabet c) (dictionaryStack c)
    (BinaryNatLists.encodeNatList []) (contents c (empty c) input [] [] [] []) using 1
    <;> first | rfl | stack_cases

/-- Header cleanup leaves the already computed dictionary untouched. -/
theorem cleanup_exits (header dictionary : List Bool) :
    (drain (Γ := Alphabet c) (headerStack c)).Exits
      (contents c (empty c) [] header dictionary [] []) (2 * header.length + 1)
      (contents c (empty c) [] [] dictionary [] []) := by
  convert drain_exits (Γ := Alphabet c) (headerStack c)
    (contents c (empty c) [] header dictionary [] []) using 1
    <;> first | rfl | stack_cases

noncomputable def routine : Routine (Alphabet c) :=
  seq (seedRoutine c) (seq (DictionaryFold.preparedRoutine c) (drain (headerStack c)))

/-- Canonical single-input construction, including initialization and cleanup. -/
theorem routine_exits (values : List Nat) :
    (routine c).ExitsLE
      (contents c (empty c) (BinaryNatLists.encodeNatList values) [] [] [] [])
      (1 + (DictionaryFold.timePolynomial c).eval (DictionaryFold.inputSize values []) +
        (2 * (BinaryNatLists.encodeNat values.length).length + 1))
      (contents c (empty c) [] []
        (BinaryNatLists.encodeNatList (DictionaryConstruction.build values)) [] []) := by
  have run := seq_exitsLE _ _ (seedRoutine_exits c (BinaryNatLists.encodeNatList values)).le
    (seq_exitsLE _ _ (DictionaryFold.bounded_exits c values [])
      (cleanup_exits c (BinaryNatLists.encodeNat values.length)
        (BinaryNatLists.encodeNatList (DictionaryConstruction.extend values []))).le)
  convert run using 1 <;> first | rfl | omega

/-- Substitute the one-bit empty seed, then charge source-header cleanup. -/
noncomputable def timePolynomial : Polynomial Nat :=
  (DictionaryFold.timePolynomial c).comp (Polynomial.X + 1) + 2 * Polynomial.X + 2

theorem inputSize_empty (values : List Nat) :
    DictionaryFold.inputSize values [] = (BinaryNatLists.encodeNatList values).length + 1 := by
  rfl

theorem runSteps_le (values : List Nat) :
    1 + (DictionaryFold.timePolynomial c).eval (DictionaryFold.inputSize values []) +
      (2 * (BinaryNatLists.encodeNat values.length).length + 1) ≤
    (timePolynomial c).eval (BinaryNatLists.encodeNatList values).length := by
  have header : (BinaryNatLists.encodeNat values.length).length ≤
      (BinaryNatLists.encodeNatList values).length := by
    simp only [BinaryNatLists.encodeNatList, List.length_append]
    omega
  simp only [timePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_comp, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_ofNat,
    inputSize_empty]
  omega

/-- The input is the full framed source; the output is its framed dictionary. -/
noncomputable def computer : FinTM2 := by
  letI : Fintype c.tm.K := c.tm.kFin
  exact toMachine (routine c) (inputStack c) (dictionaryStack c)

/-- Canonical halting output, with initialization, workspace cleanup and reset charged. -/
noncomputable def outputsInTime (values : List Nat) :
    TM2OutputsInTime (computer c) (BinaryNatLists.encodeNatList values)
      (some (BinaryNatLists.encodeNatList (DictionaryConstruction.build values)))
      ((timePolynomial c).eval (BinaryNatLists.encodeNatList values).length) := by
  letI : Fintype c.tm.K := c.tm.kFin
  apply toMachine_outputsInTime_le (routine c) (inputStack c) (dictionaryStack c)
  have hi : (initList (computer c) (BinaryNatLists.encodeNatList values)).stk =
      contents c (empty c) (BinaryNatLists.encodeNatList values) [] [] [] [] := by
    simp only [computer, toMachine, initList]
    stack_cases
  have ho : (haltList (computer c)
        (BinaryNatLists.encodeNatList (DictionaryConstruction.build values))).stk =
      contents c (empty c) [] []
        (BinaryNatLists.encodeNatList (DictionaryConstruction.build values)) [] [] := by
    simp only [computer, toMachine, haltList]
    stack_cases
  change (routine c).ExitsLE (initList (computer c) _).stk _ (haltList (computer c) _).stk
  rw [hi, ho]
  exact (routine_exits c values).mono (runSteps_le c values)

/-- The checked insertion witness yields polynomial-time dictionary construction
under the full framed-list encoding, with no separately supplied seed. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime FramedNatList.finEncoding FramedNatList.finEncoding
      DictionaryConstruction.build where
  tm := computer DictionaryInsert.computableInPolyTime
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := timePolynomial DictionaryInsert.computableInPolyTime
  outputsFun values := by
    simpa [FramedNatList.finEncoding, Equiv.refl] using
      outputsInTime DictionaryInsert.computableInPolyTime values

end LeanNPHardness.MachineAdapters.DictionaryBuild
