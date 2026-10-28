import LeanNPHardness.FramedListReverseMachine
import LeanNPHardness.DictionaryInsertMachine

/-!
# Loading one dictionary-insertion input from a framed stream

The seven-stack routine extracts one intact frame and serializes it with the
current dictionary as a tagged pair. It preserves the unread stream, retained
list header and arbitrary tagged-output suffix. All transfer and framing costs
are charged in TM2 steps; invoking insertion and iterating the fold are separate.
-/

namespace LeanNPHardness.MachineAdapters.DictionaryInsertInput

open Computability Turing Routines MachinePrimitives

abbrev ExtraAlphabet (_ : Unit) := Sum Bool Bool
abbrev Stack := FramedListReverse.Stack ⊕ Unit
abbrev Alphabet := ExtendedAlphabet (Γ := FramedListReverse.Alphabet) ExtraAlphabet

instance (k : Stack) : Fintype (Alphabet k) := by
  cases k with
  | inl k => exact inferInstanceAs (Fintype (FramedListReverse.Alphabet k))
  | inr k => exact inferInstanceAs (Fintype (Sum Bool Bool))

abbrev inputStack : Stack := .inl (.inl .input)
abbrev countStack : Stack := .inl (.inl .count)
abbrev queryStack : Stack := .inl (.inl .output)
abbrev dictionaryStack : Stack := .inl (.inr .seed)
abbrev pairStack : Stack := .inr ()

def contents (input count work query header dictionary : List Bool)
    (pair : List (Sum Bool Bool)) : Stacks Alphabet :=
  extendedStacks ExtraAlphabet
    (FramedListReverse.contents input count work query header dictionary) (fun _ => pair)

/-- Extract the query while retaining both the outer header and the dictionary. -/
def extract : Routine Alphabet :=
  extend ExtraAlphabet (extend FramedListReverse.ExtraAlphabet FrameMove.routine)

theorem extract_exits (bits input header dictionary : List Bool)
    (pair : List (Sum Bool Bool)) :
    extract.Exits (contents (BinaryNatLists.frame bits ++ input) [] [] [] header dictionary pair)
      (2 * (BinaryNatLists.frame bits).length + 2)
      (contents input [] [] (BinaryNatLists.frame bits) header dictionary pair) := by
  have run := FrameMove.routine_exits bits input []
  rw [FrameMove.runSteps_eq_frame_length] at run
  convert
    extend_exits (Γ := FramedListReverse.Alphabet) ExtraAlphabet _ (fun _ => pair)
      (extend_exits FramedListReverse.ExtraAlphabet FrameMove.routine
        (fun | .header => header | .seed => dictionary) run) using 1 <;>
    simp [extract, contents, FramedListReverse.contents] <;> rfl

/-- Push the right component first so the left query can be placed above it. -/
def serialize : Routine Alphabet :=
  seq (moveAll (Γ := Alphabet) dictionaryStack countStack id false)
    (seq (moveAll (Γ := Alphabet) countStack pairStack Sum.inr (.inl false))
      (seq (moveAll (Γ := Alphabet) queryStack countStack id false)
        (moveAll (Γ := Alphabet) countStack pairStack Sum.inl (.inl false))))

local macro "transfer_proof" : tactic => `(tactic|
  (try simp only [inputStack, countStack, queryStack, dictionaryStack, pairStack,
    contents, FramedListReverse.contents, extendedStacks, FrameMove.contents,
    List.map_id_fun, List.map_id, List.length_reverse, List.reverse_reverse,
    List.map_reverse, List.append_nil]
   <;> first | rfl | (funext k; rcases k with (k | k) | u <;>
     (try cases k) <;> (try cases u) <;>
     simp [FrameMove.contents, Function.update, Alphabet, ExtendedAlphabet, List.append_assoc])))

/-- Serialize arbitrary component words in order, clearing all consumed workspace. -/
theorem serialize_exits (query dictionary input header : List Bool)
    (pair : List (Sum Bool Bool)) :
    serialize.Exits (contents input [] [] query header dictionary pair)
      (4 * query.length + 4 * dictionary.length + 4)
      (contents input [] [] [] header []
        (query.map Sum.inl ++ dictionary.map Sum.inr ++ pair)) := by
  have h₁ : (moveAll (Γ := Alphabet) dictionaryStack countStack id false).Exits
      (contents input [] [] query header dictionary pair) (2 * dictionary.length + 1)
      (contents input dictionary.reverse [] query header [] pair) := by
    convert moveAll_exits (Γ := Alphabet) dictionaryStack countStack (by decide) id false
      (contents input [] [] query header dictionary pair) using 1 <;> transfer_proof
  have h₂ : (moveAll (Γ := Alphabet) countStack pairStack Sum.inr (.inl false)).Exits
      (contents input dictionary.reverse [] query header [] pair) (2 * dictionary.length + 1)
      (contents input [] [] query header [] (dictionary.map Sum.inr ++ pair)) := by
    convert moveAll_exits (Γ := Alphabet) countStack pairStack (by decide) Sum.inr (.inl false)
      (contents input dictionary.reverse [] query header [] pair) using 1 <;> transfer_proof
  have h₃ : (moveAll (Γ := Alphabet) queryStack countStack id false).Exits
      (contents input [] [] query header [] (dictionary.map Sum.inr ++ pair))
      (2 * query.length + 1)
      (contents input query.reverse [] [] header [] (dictionary.map Sum.inr ++ pair)) := by
    convert moveAll_exits (Γ := Alphabet) queryStack countStack (by decide) id false
      (contents input [] [] query header [] (dictionary.map Sum.inr ++ pair)) using 1
      <;> transfer_proof
  have h₄ : (moveAll (Γ := Alphabet) countStack pairStack Sum.inl (.inl false)).Exits
      (contents input query.reverse [] [] header [] (dictionary.map Sum.inr ++ pair))
      (2 * query.length + 1)
      (contents input [] [] [] header [] (query.map Sum.inl ++ dictionary.map Sum.inr ++ pair)) := by
    convert moveAll_exits (Γ := Alphabet) countStack pairStack (by decide) Sum.inl (.inl false)
      (contents input query.reverse [] [] header [] (dictionary.map Sum.inr ++ pair)) using 1
      <;> transfer_proof
  have run := seq_exits _ _ h₁ (seq_exits _ _ h₂ (seq_exits _ _ h₃ h₄))
  convert run using 1 <;> first | rfl | omega

def routine : Routine Alphabet := seq extract serialize

/-- One intact frame and the full dictionary become a tagged insertion input.
The unread stream and retained header are neither scanned nor modified. -/
theorem routine_exits (bits dictionary input header : List Bool)
    (pair : List (Sum Bool Bool)) :
    routine.Exits (contents (BinaryNatLists.frame bits ++ input) [] [] [] header dictionary pair)
      (6 * (BinaryNatLists.frame bits).length + 4 * dictionary.length + 6)
      (contents input [] [] [] header []
        ((BinaryNatLists.frame bits).map Sum.inl ++ dictionary.map Sum.inr ++ pair)) := by
  have run := seq_exits _ _ (extract_exits bits input header dictionary pair)
    (serialize_exits (BinaryNatLists.frame bits) dictionary input header pair)
  convert run using 1 <;> first | rfl | omega

def runSteps (query : Nat) (dictionary : List Nat) : Nat :=
  6 * (BinaryNatLists.encodeNat query).length +
    4 * (BinaryNatLists.encodeNatList dictionary).length + 6

/-- The result is exactly the existing insertion machine's canonical tagged input. -/
theorem natural_head_exits (query : Nat) (dictionary : List Nat) (input header : List Bool) :
    routine.Exits
      (contents (BinaryNatLists.encodeNat query ++ input) [] [] [] header
        (BinaryNatLists.encodeNatList dictionary) [])
      (runSteps query dictionary)
      (contents input [] [] [] header [] (DictionaryInsert.pairWord query dictionary)) := by
  simpa only [runSteps, DictionaryInsert.pairWord, BinaryNatLists.encodeNat,
    List.append_nil] using
    routine_exits (encodeNat query) (BinaryNatLists.encodeNatList dictionary) input header []

/-- Adapter cost alone is linear in the complete tagged query/dictionary input. -/
theorem runSteps_le (query : Nat) (dictionary : List Nat) :
    runSteps query dictionary ≤ 6 * (DictionaryInsert.pairWord query dictionary).length + 6 := by
  simp only [runSteps, DictionaryInsert.pairWord, List.length_append, List.length_map]
  omega

/-- Move the prepared reversed body onto the stream stack without changing its order. -/
def returnBody : Routine Alphabet :=
  seq (moveAll (Γ := Alphabet) queryStack countStack id false)
    (moveAll (Γ := Alphabet) countStack inputStack id false)

theorem returnBody_exits (body header dictionary : List Bool)
    (pair : List (Sum Bool Bool)) :
    returnBody.Exits (contents [] [] [] body header dictionary pair)
      (4 * body.length + 2) (contents body [] [] [] header dictionary pair) := by
  have h₁ : (moveAll (Γ := Alphabet) queryStack countStack id false).Exits
      (contents [] [] [] body header dictionary pair) (2 * body.length + 1)
      (contents [] body.reverse [] [] header dictionary pair) := by
    convert moveAll_exits (Γ := Alphabet) queryStack countStack (by decide) id false
      (contents [] [] [] body header dictionary pair) using 1 <;> transfer_proof
  have h₂ : (moveAll (Γ := Alphabet) countStack inputStack id false).Exits
      (contents [] body.reverse [] [] header dictionary pair) (2 * body.length + 1)
      (contents body [] [] [] header dictionary pair) := by
    convert moveAll_exits (Γ := Alphabet) countStack inputStack (by decide) id false
      (contents [] body.reverse [] [] header dictionary pair) using 1 <;> transfer_proof
  have run := seq_exits _ _ h₁ h₂
  convert run using 1 <;> first | rfl | omega

/-- Prepare the complete source for successive calls to the one-entry adapter. -/
def prepare : Routine Alphabet :=
  seq (extend ExtraAlphabet FramedListReverse.prepare) returnBody

def prepareSteps (values : List Nat) : Nat :=
  FramedListReverse.prepareSteps values +
    4 * (values.flatMap BinaryNatLists.encodeNat).length + 2

/-- The body now lies on the adapter's input stack in tail-first order.
The complete original header and arbitrary seed remain on their own stacks. -/
theorem prepare_exits (values : List Nat) (dictionary : List Bool)
    (pair : List (Sum Bool Bool)) :
    prepare.Exits (contents (BinaryNatLists.encodeNatList values) [] [] [] [] dictionary pair)
      (prepareSteps values)
      (contents (values.reverse.flatMap BinaryNatLists.encodeNat) [] [] []
        (BinaryNatLists.encodeNat values.length) dictionary pair) := by
  have h₁ := extend_exits (Γ := FramedListReverse.Alphabet) ExtraAlphabet
    FramedListReverse.prepare (fun _ => pair) (FramedListReverse.prepare_exits values dictionary)
  have run := seq_exits _ _ h₁
    (returnBody_exits (values.reverse.flatMap BinaryNatLists.encodeNat)
      (BinaryNatLists.encodeNat values.length) dictionary pair)
  convert run using 1 <;>
    (try simp only [prepareSteps, List.length_flatMap, List.map_reverse, List.sum_reverse]) <;>
    rfl

/-- Preparation scans only the source; the seed and tagged suffix are untouched. -/
theorem prepareSteps_le (values : List Nat) :
    prepareSteps values ≤ 10 * (BinaryNatLists.encodeNatList values).length + 7 := by
  have bound := FramedListReverse.prepareSteps_le values
  simp only [prepareSteps, BinaryNatLists.encodeNatList, List.length_append] at *
  omega

/-- For a nonempty source, the first tagged query is its last occurrence.
The remaining reversed frames and original count header survive verbatim. -/
theorem prepare_head_exits (values : List Nat) (query : Nat) (dictionary : List Nat) :
    (seq prepare routine).Exits
      (contents (BinaryNatLists.encodeNatList (values ++ [query])) [] [] [] []
        (BinaryNatLists.encodeNatList dictionary) [])
      (prepareSteps (values ++ [query]) + runSteps query dictionary)
      (contents (values.reverse.flatMap BinaryNatLists.encodeNat) [] [] []
        (BinaryNatLists.encodeNat (values ++ [query]).length) []
        (DictionaryInsert.pairWord query dictionary)) := by
  have h := prepare_exits (values ++ [query]) (BinaryNatLists.encodeNatList dictionary) []
  simp only [List.reverse_append, List.reverse_singleton, List.singleton_append,
    List.flatMap_cons] at h
  exact seq_exits _ _ h
    (natural_head_exits query dictionary (values.reverse.flatMap BinaryNatLists.encodeNat)
      (BinaryNatLists.encodeNat (values ++ [query]).length))

end LeanNPHardness.MachineAdapters.DictionaryInsertInput
