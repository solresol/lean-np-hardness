import LeanNPHardness.FramedSuccMachine
import LeanNPHardness.MachineRoutineExtension
import LeanNPHardness.MachineRoutinePrimitives

/-!
# Framed-list cons from two supplied stacks

Increment the dictionary header while retaining a supplied framed query,
then assemble the new header, query, and every old entry in original order.
The five-stack finite routine clears all workspace. The input-size measure
is the sum of the complete query and dictionary bit lengths. Loading these
two stacks from a tagged input is a separate obligation.
-/

namespace LeanNPHardness.MachinePrimitives.FramedListCons

open Computability Turing Routines

abbrev Stack := FramedSucc.Stack ⊕ Unit
abbrev Alphabet := ExtendedAlphabet (Γ := FramedSucc.Alphabet) (fun _ : Unit => Bool)

instance (k : Stack) : Fintype (Alphabet k) := by
  rcases k with k | ⟨⟩ <;> exact inferInstanceAs (Fintype Bool)

def contents (input count work output query : List Bool) : Stacks Alphabet :=
  extendedStacks _ (FramedSucc.contents input count work output) (fun _ => query)

/-- The header updater runs without inspecting or consuming the query. -/
def countRoutine : Routine Alphabet := extend _ FramedSucc.routine

theorem count_exits (xs : List Nat) (query : List Bool) :
    countRoutine.Exits (contents (BinaryNatLists.encodeNatList xs) [] [] [] query)
      (2 * (encodeNat xs.length).length + 2 * (encodeNat (xs.length + 1)).length + 4)
      (contents (xs.flatMap BinaryNatLists.encodeNat) [] []
        (BinaryNatLists.encodeNat (xs.length + 1)) query) := by
  simpa only [List.append_nil, countRoutine, contents] using
    extend_exits (fun _ : Unit => Bool) FramedSucc.routine (fun _ => query)
      (FramedSucc.listCount_exits xs [] [])

private def saveHeader : Routine Alphabet := moveAll (Γ := Alphabet) (.inl .output) (.inl .count) id false
private def reverseBody : Routine Alphabet := moveAll (Γ := Alphabet) (.inl .input) (.inl .work) id false
private def emitWork : Routine Alphabet := moveAll (Γ := Alphabet) (.inl .work) (.inl .output) id false
private def reverseQuery : Routine Alphabet := moveAll (Γ := Alphabet) (.inr ()) (.inl .work) id false
private def emitHeader : Routine Alphabet := moveAll (Γ := Alphabet) (.inl .count) (.inl .output) id false

/-- Each transfer reverses its source; paired passes recover the original order. -/
def assemble : Routine Alphabet :=
  seq saveHeader (seq reverseBody (seq emitWork (seq reverseQuery (seq emitWork emitHeader))))

local macro "transfer_proof" : tactic => `(tactic|
  (try simp only [saveHeader, reverseBody, emitWork, reverseQuery, emitHeader, contents, extendedStacks, FramedSucc.contents, List.map_id_fun,
     List.map_id, List.append_assoc, List.length_reverse, List.reverse_reverse, List.append_nil]
   <;> first | rfl | (funext k; rcases k with k | ⟨⟩ <;>
     simp [extendedStacks, FramedSucc.contents, Function.update, Alphabet,
       ExtendedAlphabet] <;> cases k <;> rfl)))

/-- Exact reassembly cost, with no dropped or reordered body/query bits. -/
theorem assemble_exits (header body query : List Bool) :
    assemble.Exits (contents body [] [] header query)
      (4 * header.length + 4 * body.length + 4 * query.length + 6)
      (contents [] [] [] (header ++ query ++ body) []) := by
  have h₁ : saveHeader.Exits (contents body [] [] header query) (2 * header.length + 1)
      (contents body header.reverse [] [] query) := by
    convert moveAll_exits (Γ := Alphabet) (.inl .output) (.inl .count) (by decide) id false
      (contents body [] [] header query) using 1 <;> transfer_proof
  have h₂ : reverseBody.Exits (contents body header.reverse [] [] query) (2 * body.length + 1)
      (contents [] header.reverse body.reverse [] query) := by
    convert moveAll_exits (Γ := Alphabet) (.inl .input) (.inl .work) (by decide) id false
      (contents body header.reverse [] [] query) using 1 <;> transfer_proof
  have h₃ : emitWork.Exits (contents [] header.reverse body.reverse [] query)
      (2 * body.length + 1) (contents [] header.reverse [] body query) := by
    convert moveAll_exits (Γ := Alphabet) (.inl .work) (.inl .output) (by decide) id false
      (contents [] header.reverse body.reverse [] query) using 1 <;> transfer_proof
  have h₄ : reverseQuery.Exits (contents [] header.reverse [] body query)
      (2 * query.length + 1) (contents [] header.reverse query.reverse body []) := by
    convert moveAll_exits (Γ := Alphabet) (.inr ()) (.inl .work) (by decide) id false
      (contents [] header.reverse [] body query) using 1 <;> transfer_proof
  have h₅ : emitWork.Exits (contents [] header.reverse query.reverse body [])
      (2 * query.length + 1) (contents [] header.reverse [] (query ++ body) []) := by
    convert moveAll_exits (Γ := Alphabet) (.inl .work) (.inl .output) (by decide) id false
      (contents [] header.reverse query.reverse body []) using 1 <;> transfer_proof
  have h₆ : emitHeader.Exits (contents [] header.reverse [] (query ++ body) [])
      (2 * header.length + 1) (contents [] [] [] (header ++ query ++ body) []) := by
    convert moveAll_exits (Γ := Alphabet) (.inl .count) (.inl .output) (by decide) id false
      (contents [] header.reverse [] (query ++ body) []) using 1 <;> transfer_proof
  have run := seq_exits _ _ h₁ (seq_exits _ _ h₂ (seq_exits _ _ h₃
    (seq_exits _ _ h₄ (seq_exits _ _ h₅ h₆))))
  simpa only [assemble, show 4 * header.length + 4 * body.length + 4 * query.length + 6 =
    (2 * header.length + 1) + ((2 * body.length + 1) + ((2 * body.length + 1) +
    ((2 * query.length + 1) + ((2 * query.length + 1) + (2 * header.length + 1))))) by omega] using run

def routine : Routine Alphabet := seq countRoutine assemble

/-- Exact cost includes header update, header storage, and all restoration passes. -/
def runSteps (x : Nat) (xs : List Nat) : Nat :=
  2 * (encodeNat xs.length).length + 2 * (encodeNat (xs.length + 1)).length + 4 +
    (4 * (BinaryNatLists.encodeNat (xs.length + 1)).length +
      4 * (xs.flatMap BinaryNatLists.encodeNat).length +
      4 * (BinaryNatLists.encodeNat x).length + 6)

/-- The output is the full encoding of `x :: xs`, including all repetitions. -/
theorem routine_exits (x : Nat) (xs : List Nat) :
    routine.Exits
      (contents (BinaryNatLists.encodeNatList xs) [] [] [] (BinaryNatLists.encodeNat x))
      (runSteps x xs) (contents [] [] [] (BinaryNatLists.encodeNatList (x :: xs)) []) := by
  have run := seq_exits _ _ (count_exits xs (BinaryNatLists.encodeNat x))
    (assemble_exits (BinaryNatLists.encodeNat (xs.length + 1))
      (xs.flatMap BinaryNatLists.encodeNat) (BinaryNatLists.encodeNat x))
  simpa only [routine, runSteps, BinaryNatLists.encodeNatList,
    List.length_cons, List.flatMap_cons, List.append_assoc] using run

/-- Linear in the complete supplied component encodings, never the count's value. -/
theorem runSteps_le (x : Nat) (xs : List Nat) :
    runSteps x xs ≤ 6 * ((BinaryNatLists.encodeNat x).length +
      (BinaryNatLists.encodeNatList xs).length) + 18 := by
  have cost := FramedSucc.runSteps_le_frame_bound (encodeNat xs.length)
  have growth := FramedSucc.frame_length_le (encodeNat xs.length)
  simp only [binarySuccBits_encodeNat] at cost growth
  simp only [runSteps, BinaryNatLists.encodeNatList, List.length_append, BinaryNatLists.encodeNat]
  omega

end LeanNPHardness.MachinePrimitives.FramedListCons
