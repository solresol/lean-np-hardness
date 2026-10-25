import LeanNPHardness.TaggedFramedListCons
import LeanNPHardness.TaggedMembership
import LeanNPHardness.DictionaryConstruction

/-!
# Polynomial-time conditional dictionary insertion

A finite TM2 consumes the tagged encoding of `(present, (query, dictionary))`.
It returns the dictionary unchanged on true and uses the checked framed-list
cons on false. The selector costs at most `13n + 24` steps in the complete
tagged input length, including loading, workspace cleanup, reset and halt.

Composing it with membership and input retention computes conditional insertion
from the original query/dictionary pair. That composition has its own polynomial;
the linear selector bound does not include membership. Existing dictionary
occurrences are retained. The seeded fold and dense CNF renaming remain separate.
-/

namespace LeanNPHardness.MachineAdapters.DictionaryInsert

open Computability Turing Routines MachinePrimitives

namespace KeepDictionary

open TaggedFramedListCons

def cleanup : Routine Alphabet :=
  seq (drain queryStack)
    (seq (moveAll (Γ := Alphabet) dictionaryStack workStack id false)
      (moveAll (Γ := Alphabet) workStack outputStack id false))

local macro "stacks_ext" : tactic => `(tactic|
  (funext k; rcases k with (k | ⟨⟩) | ⟨⟩ <;>
    simp [contents, FramedListCons.contents, extendedStacks, FramedSucc.contents,
      Function.update, Alphabet, ExtendedAlphabet] <;> cases k <;> rfl))

theorem cleanup_exits (query dictionary : List Bool) :
    cleanup.Exits (contents [] query dictionary [] [] [])
      (2 * query.length + 4 * dictionary.length + 3)
      (contents [] [] [] [] [] dictionary) := by
  have hq : (drain (Γ := Alphabet) queryStack).Exits
      (contents [] query dictionary [] [] []) (2 * query.length + 1)
      (contents [] [] dictionary [] [] []) := by
    convert drain_exits (Γ := Alphabet) queryStack
      (contents [] query dictionary [] [] []) using 1
    · rfl
    · stacks_ext
  have hr : (moveAll (Γ := Alphabet) dictionaryStack workStack id false).Exits
      (contents [] [] dictionary [] [] []) (2 * dictionary.length + 1)
      (contents [] [] [] [] dictionary.reverse []) := by
    convert moveAll_exits (Γ := Alphabet) dictionaryStack workStack (by decide) id false
      (contents [] [] dictionary [] [] []) using 1
    · rfl
    · simp only [contents, FramedListCons.contents, extendedStacks, FramedSucc.contents,
        List.map_id, List.append_nil]
      stacks_ext
  have ho : (moveAll (Γ := Alphabet) workStack outputStack id false).Exits
      (contents [] [] [] [] dictionary.reverse []) (2 * dictionary.length + 1)
      (contents [] [] [] [] [] dictionary) := by
    convert moveAll_exits (Γ := Alphabet) workStack outputStack (by decide) id false
      (contents [] [] [] [] dictionary.reverse []) using 1
    · simp [contents, FramedListCons.contents, extendedStacks, FramedSucc.contents]
    · simp only [contents, FramedListCons.contents, extendedStacks, FramedSucc.contents,
        List.map_id, List.reverse_reverse, List.append_nil]
      stacks_ext
  simpa only [cleanup, show 2 * query.length + 4 * dictionary.length + 3 =
    (2 * query.length + 1) + ((2 * dictionary.length + 1) +
      (2 * dictionary.length + 1)) by omega] using seq_exits _ _ hq (seq_exits _ _ hr ho)

def routine : Routine Alphabet := seq load cleanup

/-- Discard only the query; retain the complete dictionary word in order. -/
theorem routine_exits (query dictionary : List Bool) :
    routine.Exits (contents (query.map Sum.inl ++ dictionary.map Sum.inr) [] [] [] [] [])
      (5 * query.length + 7 * dictionary.length + 6)
      (contents [] [] [] [] [] dictionary) := by
  simpa only [routine, show 5 * query.length + 7 * dictionary.length + 6 =
    (3 * (query.length + dictionary.length) + 3) +
      (2 * query.length + 4 * dictionary.length + 3) by omega] using
    seq_exits _ _ (load_exits query dictionary) (cleanup_exits query dictionary)

end KeepDictionary

inductive Extra
  | input | work
  deriving DecidableEq, Fintype

def ExtraAlphabet : Extra → Type
  | .input => Sum Bool (Sum Bool Bool)
  | .work => Sum Bool Bool

abbrev Stack := TaggedFramedListCons.Stack ⊕ Extra
abbrev Alphabet := ExtendedAlphabet (Γ := TaggedFramedListCons.Alphabet) ExtraAlphabet

instance (k : Stack) : Fintype (Alphabet k) := by
  cases k with
  | inl k => exact inferInstanceAs (Fintype (TaggedFramedListCons.Alphabet k))
  | inr k =>
      cases k <;> dsimp [Alphabet, ExtendedAlphabet, ExtraAlphabet] <;> infer_instance

abbrev inputStack : Stack := .inr .input
instance : DecidableEq (Alphabet inputStack) :=
  inferInstanceAs (DecidableEq (Sum Bool (Sum Bool Bool)))

abbrev workStack : Stack := .inr .work
abbrev pairStack : Stack := .inl TaggedFramedListCons.inputStack
abbrev outputStack : Stack := .inl TaggedFramedListCons.outputStack

def extras (input : List (Sum Bool (Sum Bool Bool))) (work : List (Sum Bool Bool)) :
    Stacks ExtraAlphabet
  | .input => input
  | .work => work

def contents (input : List (Sum Bool (Sum Bool Bool)))
    (work pair : List (Sum Bool Bool)) (output : List Bool) : Stacks Alphabet :=
  extendedStacks _ (TaggedFramedListCons.contents pair [] [] [] [] output) (extras input work)

def unwrap : Sum Bool (Sum Bool Bool) → Sum Bool Bool := Sum.elim Sum.inl id

def load : Routine Alphabet :=
  seq (moveAll (Γ := Alphabet) inputStack workStack unwrap (.inl false))
    (moveAll (Γ := Alphabet) workStack pairStack id (.inl false))

local macro "stacks_ext" : tactic => `(tactic|
  (funext k; rcases k with k | k
   · rcases k with (k | ⟨⟩) | ⟨⟩ <;>
       simp [contents, TaggedFramedListCons.contents, FramedListCons.contents,
         extendedStacks, FramedSucc.contents, Function.update, Alphabet,
         TaggedFramedListCons.Alphabet, ExtendedAlphabet] <;> cases k <;> rfl
   · cases k <;> simp [contents, extras, extendedStacks, Function.update]))

/-- Strip the outer right tag, preserving every inner tag and bit. -/
theorem load_exits (pair : List (Sum Bool Bool)) :
    load.Exits (contents (pair.map Sum.inr) [] [] []) (4 * pair.length + 2)
      (contents [] [] pair []) := by
  have hr : (moveAll (Γ := Alphabet) inputStack workStack unwrap (.inl false)).Exits
      (contents (pair.map Sum.inr) [] [] []) (2 * pair.length + 1)
      (contents [] pair.reverse [] []) := by
    convert moveAll_exits (Γ := Alphabet) inputStack workStack (by decide) unwrap (.inl false)
      (contents (pair.map Sum.inr) [] [] []) using 1
    · simp [contents, extras, extendedStacks]
    · simp only [contents, extras, extendedStacks, List.map_map, Function.comp_def,
        unwrap, Sum.elim_inr, id_eq, List.append_nil]
      stacks_ext
  have ho : (moveAll (Γ := Alphabet) workStack pairStack id (.inl false)).Exits
      (contents [] pair.reverse [] []) (2 * pair.length + 1) (contents [] [] pair []) := by
    convert moveAll_exits (Γ := Alphabet) workStack pairStack (by decide) id (.inl false)
      (contents [] pair.reverse [] []) using 1
    · simp [contents, extras, extendedStacks]
    · simp only [contents, extras, extendedStacks, TaggedFramedListCons.contents,
        List.map_id, List.reverse_reverse, List.append_nil]
      stacks_ext
  simpa only [load, show 4 * pair.length + 2 =
    (2 * pair.length + 1) + (2 * pair.length + 1) by omega] using seq_exits _ _ hr ho

/-- The supplied flag selects the branch; membership is computed separately. -/
def select (input : Bool × (Nat × List Nat)) : List Nat :=
  if input.1 then input.2.2 else input.2.1 :: input.2.2

def branch (present : Bool) : Routine TaggedFramedListCons.Alphabet :=
  if present then KeepDictionary.routine else TaggedFramedListCons.routine

def branchSteps (present : Bool) (x : Nat) (xs : List Nat) : Nat :=
  if present then 5 * (BinaryNatLists.encodeNat x).length +
    7 * (BinaryNatLists.encodeNatList xs).length + 6
  else TaggedFramedListCons.runSteps x xs

theorem branch_exits (present : Bool) (x : Nat) (xs : List Nat) :
    (branch present).Exits
      (TaggedFramedListCons.contents ((BinaryNatLists.encodeNat x).map Sum.inl ++
        (BinaryNatLists.encodeNatList xs).map Sum.inr) [] [] [] [] [])
      (branchSteps present x xs)
      (TaggedFramedListCons.contents [] [] [] [] []
        (BinaryNatLists.encodeNatList (select (present, (x, xs))))) := by
  cases present
  · exact TaggedFramedListCons.routine_exits x xs
  · exact KeepDictionary.routine_exits _ _

def handlers : Sum Bool (Sum Bool Bool) → Routine Alphabet
  | .inl present => seq load (extend ExtraAlphabet (branch present))
  | .inr _ => skip

def routine : Routine Alphabet := dispatch inputStack handlers

def pairWord (x : Nat) (xs : List Nat) : List (Sum Bool Bool) :=
  (BinaryNatLists.encodeNat x).map Sum.inl ++ (BinaryNatLists.encodeNatList xs).map Sum.inr

def runSteps (present : Bool) (x : Nat) (xs : List Nat) : Nat :=
  4 * (pairWord x xs).length + 2 + branchSteps present x xs + 1

/-- Exact selection, from one serialized input to canonical framed output. -/
theorem routine_exits (present : Bool) (x : Nat) (xs : List Nat) :
    routine.Exits (contents (.inl present :: (pairWord x xs).map Sum.inr) [] [] [])
      (runSteps present x xs)
      (contents [] [] [] (BinaryNatLists.encodeNatList (select (present, (x, xs))))) := by
  have hb := extend_exits ExtraAlphabet (branch present) (extras [] [])
    (branch_exits present x xs)
  have hs := seq_exits _ _ (load_exits (pairWord x xs)) hb
  have hu : Function.update (contents (.inl present :: (pairWord x xs).map Sum.inr) [] [] [])
      inputStack ((pairWord x xs).map Sum.inr) =
      contents ((pairWord x xs).map Sum.inr) [] [] [] := by stacks_ext
  unfold routine runSteps
  apply dispatch_exits (Γ := Alphabet) inputStack handlers _ (.inl present) _ rfl
  rw [hu]
  exact hs

/-- A common bound for both branches, in complete input symbols including the flag. -/
theorem runSteps_le (present : Bool) (x : Nat) (xs : List Nat) :
    runSteps present x xs ≤ 13 * ((pairWord x xs).length + 1) + 24 := by
  have bound := TaggedFramedListCons.runSteps_le x xs
  cases present <;>
    simp only [runSteps, branchSteps, Bool.false_eq_true, ite_false, ite_true,
      pairWord, List.length_append, List.length_map] <;> omega

def computer : FinTM2 := toMachine routine inputStack outputStack

/-- Canonical output includes empty workspace, initial control and final halt. -/
def outputsInTime (present : Bool) (x : Nat) (xs : List Nat) :
    TM2OutputsInTime computer (.inl present :: (pairWord x xs).map Sum.inr)
      (some (BinaryNatLists.encodeNatList (select (present, (x, xs)))))
      (13 * ((pairWord x xs).length + 1) + 24) := by
  have run : TM2OutputsInTime computer (.inl present :: (pairWord x xs).map Sum.inr)
      (some (BinaryNatLists.encodeNatList (select (present, (x, xs)))))
      (runSteps present x xs) := by
    apply toMachine_outputsInTime routine inputStack outputStack
    have hi : (initList computer (.inl present :: (pairWord x xs).map Sum.inr)).stk =
        contents (.inl present :: (pairWord x xs).map Sum.inr) [] [] [] := by
      funext k; rcases k with k | k
      · rcases k with (k | ⟨⟩) | ⟨⟩ <;> first | rfl | (cases k <;> rfl)
      · cases k <;> rfl
    have ho : (haltList computer
        (BinaryNatLists.encodeNatList (select (present, (x, xs))))).stk =
        contents [] [] [] (BinaryNatLists.encodeNatList (select (present, (x, xs)))) := by
      funext k; rcases k with k | k
      · rcases k with (k | ⟨⟩) | ⟨⟩ <;> first | rfl | (cases k <;> rfl)
      · cases k <;> rfl
    change routine.Exits (initList computer _).stk _ (haltList computer _).stk
    rw [hi, ho]
    exact routine_exits present x xs
  exact evalsToInTimeMono run (runSteps_le present x xs)

/-- Linear selection after membership, measured in the entire nested tagged input. -/
noncomputable def selectComputableInPolyTime :
    TM2ComputableInPolyTime
      (PairEncoding.finEncoding finEncodingBoolBool
        (PairEncoding.finEncoding FramedNat.finEncoding FramedNatList.finEncoding))
      FramedNatList.finEncoding select where
  tm := computer
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 13 * Polynomial.X + 24
  outputsFun input := by
    rcases input with ⟨present, x, xs⟩
    simpa [PairEncoding.finEncoding, finEncodingBoolBool, encodeBool,
      FramedNat.finEncoding, FramedNatList.finEncoding, pairWord, Equiv.refl,
      TM2OutputsInTime, FinTM2.step, Polynomial.eval_add,
      Polynomial.eval_mul, Polynomial.eval_X, Nat.add_assoc] using outputsInTime present x xs

/-- Conditional insertion from one original tagged pair, charging membership,
input retention, selection, cleanup and halt through checked TM2 composition. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime
      (PairEncoding.finEncoding FramedNat.finEncoding FramedNatList.finEncoding)
      FramedNatList.finEncoding
      (fun input : Nat × List Nat => DictionaryConstruction.insert input.1 input.2) := by
  have composed := MachineComposition.compositionComputableInPolyTime _ _ _ _ _
    TaggedMembership.preservingMembershipComputableInPolyTime selectComputableInPolyTime
  simpa only [Function.comp_def, select, DictionaryConstruction.insert_eq_membership]
    using composed

end LeanNPHardness.MachineAdapters.DictionaryInsert
