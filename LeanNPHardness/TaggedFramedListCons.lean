import LeanNPHardness.FramedListCons
import LeanNPHardness.PairEncoding

/-!
# Framed-list cons from a single tagged input

A finite six-stack TM2 loads the tagged pair of a framed natural and a framed
natural list, then invokes the checked cons kernel. The loader temporarily
uses the kernel's empty count/work stacks for reversed components, restoring
each with one transfer. Loading costs exactly `3n + 3`; the complete machine
is bounded by `9n + 21` in the original tagged input length. All occurrences
survive, and canonical cleanup, state reset, and halting are included.
-/

namespace LeanNPHardness.MachineAdapters.TaggedFramedListCons

open Computability Turing Routines MachinePrimitives

abbrev Stack := FramedListCons.Stack ⊕ Unit
abbrev Alphabet := ExtendedAlphabet (Γ := FramedListCons.Alphabet)
  (fun _ : Unit => Sum Bool Bool)

instance (k : Stack) : Fintype (Alphabet k) := by
  rcases k with (k | ⟨⟩) | ⟨⟩
  · exact inferInstanceAs (Fintype Bool)
  · exact inferInstanceAs (Fintype Bool)
  · exact inferInstanceAs (Fintype (Sum Bool Bool))

abbrev inputStack : Stack := .inr ()
abbrev queryStack : Stack := .inl (.inr ())
abbrev dictionaryStack : Stack := .inl (.inl .input)
abbrev countStack : Stack := .inl (.inl .count)
abbrev workStack : Stack := .inl (.inl .work)
abbrev outputStack : Stack := .inl (.inl .output)

def contents (input : List (Sum Bool Bool)) (query dictionary count work output : List Bool) :
    Stacks Alphabet :=
  extendedStacks _ (FramedListCons.contents dictionary count work output query) (fun _ => input)

abbrev State := Option (Sum Bool Bool)

private def held : State → Bool
  | some (.inl b) | some (.inr b) => b
  | none => false

private def isLeft : State → Bool
  | some (.inl _) => true
  | _ => false

/-- Scan into the two work stacks, leaving the eventual component stacks empty. -/
def scan : Routine Alphabet where
  Λ := Unit
  σ := State
  entry := ()
  init := none
  program _ := .pop inputStack (fun _ s => s) <|
    .branch Option.isSome
      (.branch isLeft
        (.push countStack held (.goto fun _ => ()))
        (.push workStack held (.goto fun _ => ()))) .halt

def cfg (label : Option Unit) (state : State) (input : List (Sum Bool Bool))
    (query dictionary count work output : List Bool) : TM2.Cfg Alphabet Unit State :=
  ⟨label, state, contents input query dictionary count work output⟩

private abbrev step := flip Option.bind (TM2.step scan.program)

local macro "stacks_ext" : tactic => `(tactic|
  (funext k; rcases k with (k | ⟨⟩) | ⟨⟩ <;>
    simp [contents, FramedListCons.contents, extendedStacks, FramedSucc.contents,
      Function.update, Alphabet, ExtendedAlphabet] <;> cases k <;> rfl))

private theorem scan_nil (state : State) (query dictionary count work output : List Bool) :
    step (some (cfg (some ()) state [] query dictionary count work output)) =
      some (cfg none none [] query dictionary count work output) := by
  simp [step, flip, scan, cfg, TM2.step, TM2.stepAux, contents, extendedStacks]

private theorem scan_cons (a : Sum Bool Bool) (state : State)
    (input : List (Sum Bool Bool)) (query dictionary count work output : List Bool) :
    step (some (cfg (some ()) state (a :: input) query dictionary count work output)) =
      some (cfg (some ()) (some a) input query dictionary
        (PairEncoding.leftSymbols [a] ++ count)
        (PairEncoding.rightSymbols [a] ++ work) output) := by
  cases a <;>
    simp [step, flip, scan, cfg, TM2.step, TM2.stepAux, contents,
      FramedListCons.contents, extendedStacks, FramedSucc.contents, Alphabet,
      held, isLeft, PairEncoding.leftSymbols, PairEncoding.rightSymbols, Function.update]
    <;> stacks_ext

/-- Exact scan for arbitrary tag order and arbitrary preserved stacks. -/
theorem scan_run (input : List (Sum Bool Bool))
    (query dictionary count work output : List Bool) (state : State) :
    step^[input.length + 1]
        (some (cfg (some ()) state input query dictionary count work output)) =
      some (cfg none none [] query dictionary
        ((PairEncoding.leftSymbols input).reverse ++ count)
        ((PairEncoding.rightSymbols input).reverse ++ work) output) := by
  induction input generalizing count work state with
  | nil => simpa [PairEncoding.leftSymbols, PairEncoding.rightSymbols] using
      scan_nil state query dictionary count work output
  | cons a input ih =>
      rw [List.length_cons, Function.iterate_succ_apply, scan_cons, ih]
      cases a <;> simp [PairEncoding.leftSymbols, PairEncoding.rightSymbols,
        List.reverse_cons, List.append_assoc]

private def restoreQuery : Routine Alphabet :=
  moveAll (Γ := Alphabet) countStack queryStack id false

private def restoreDictionary : Routine Alphabet :=
  moveAll (Γ := Alphabet) workStack dictionaryStack id false

def restore : Routine Alphabet := seq restoreQuery restoreDictionary

local macro "transfer_proof" : tactic => `(tactic|
  (try simp only [restoreQuery, restoreDictionary, contents, FramedListCons.contents,
     extendedStacks, FramedSucc.contents, List.map_id_fun, List.map_id,
     List.length_reverse, List.reverse_reverse, List.append_nil]
   <;> first | rfl | stacks_ext))

/-- Two transfers restore both components and empty the reused work stacks. -/
theorem restore_exits (query dictionary : List Bool) :
    restore.Exits (contents [] [] [] query.reverse dictionary.reverse [])
      (2 * query.length + 2 * dictionary.length + 2)
      (contents [] query dictionary [] [] []) := by
  have hq : restoreQuery.Exits (contents [] [] [] query.reverse dictionary.reverse [])
      (2 * query.length + 1) (contents [] query [] [] dictionary.reverse []) := by
    convert moveAll_exits (Γ := Alphabet) countStack queryStack (by decide) id false
      (contents [] [] [] query.reverse dictionary.reverse []) using 1 <;> transfer_proof
  have hd : restoreDictionary.Exits (contents [] query [] [] dictionary.reverse [])
      (2 * dictionary.length + 1) (contents [] query dictionary [] [] []) := by
    convert moveAll_exits (Γ := Alphabet) workStack dictionaryStack (by decide) id false
      (contents [] query [] [] dictionary.reverse []) using 1 <;> transfer_proof
  simpa only [restore, show 2 * query.length + 2 * dictionary.length + 2 =
    (2 * query.length + 1) + (2 * dictionary.length + 1) by omega] using seq_exits _ _ hq hd

def load : Routine Alphabet := seq scan restore

/-- Loading supports arbitrary component words, including empty words. -/
theorem load_exits (query dictionary : List Bool) :
    load.Exits (contents (query.map Sum.inl ++ dictionary.map Sum.inr) [] [] [] [] [])
      (3 * (query.length + dictionary.length) + 3)
      (contents [] query dictionary [] [] []) := by
  have hs : scan.Exits
      (contents (query.map Sum.inl ++ dictionary.map Sum.inr) [] [] [] [] [])
      (query.length + dictionary.length + 1)
      (contents [] [] [] query.reverse dictionary.reverse []) := by
    refine ⟨none, ?_⟩
    change step^[_] (some (cfg (some ()) none _ [] [] [] [] [])) = _
    have run := scan_run (query.map Sum.inl ++ dictionary.map Sum.inr) [] [] [] [] [] none
    simp only [PairEncoding.leftSymbols_append, PairEncoding.rightSymbols_append,
      PairEncoding.leftSymbols_map_inl, PairEncoding.leftSymbols_map_inr,
      PairEncoding.rightSymbols_map_inl, PairEncoding.rightSymbols_map_inr,
      List.nil_append, List.append_nil, List.length_append, List.length_map] at run
    exact run
  simpa only [load, show 3 * (query.length + dictionary.length) + 3 =
    (query.length + dictionary.length + 1) +
      (2 * query.length + 2 * dictionary.length + 2) by omega] using
    seq_exits _ _ hs (restore_exits query dictionary)

def consRoutine : Routine Alphabet :=
  extend (fun _ : Unit => Sum Bool Bool) FramedListCons.routine

def routine : Routine Alphabet := seq load consRoutine

def runSteps (x : Nat) (xs : List Nat) : Nat :=
  3 * ((BinaryNatLists.encodeNat x).length + (BinaryNatLists.encodeNatList xs).length) + 3 +
    FramedListCons.runSteps x xs

/-- Cons from the original tagged input, preserving all list occurrences. -/
theorem routine_exits (x : Nat) (xs : List Nat) :
    routine.Exits
      (contents ((BinaryNatLists.encodeNat x).map Sum.inl ++
        (BinaryNatLists.encodeNatList xs).map Sum.inr) [] [] [] [] [])
      (runSteps x xs) (contents [] [] [] [] [] (BinaryNatLists.encodeNatList (x :: xs))) := by
  have hc : consRoutine.Exits
      (contents [] (BinaryNatLists.encodeNat x) (BinaryNatLists.encodeNatList xs) [] [] [])
      (FramedListCons.runSteps x xs)
      (contents [] [] [] [] [] (BinaryNatLists.encodeNatList (x :: xs))) :=
    extend_exits (fun _ : Unit => Sum Bool Bool) FramedListCons.routine (fun _ => [])
      (FramedListCons.routine_exits x xs)
  exact seq_exits _ _ (load_exits _ _) hc

/-- The runtime is linear in encoded bits, independent of numerical index values. -/
theorem runSteps_le (x : Nat) (xs : List Nat) :
    runSteps x xs ≤ 9 * ((BinaryNatLists.encodeNat x).length +
      (BinaryNatLists.encodeNatList xs).length) + 21 := by
  have bound := FramedListCons.runSteps_le x xs
  unfold runSteps
  omega

def computer : FinTM2 := toMachine routine inputStack outputStack

/-- Canonical output includes empty workspace, state reset and halting. -/
def outputsInTime (x : Nat) (xs : List Nat) :
    TM2OutputsInTime computer
      ((BinaryNatLists.encodeNat x).map Sum.inl ++ (BinaryNatLists.encodeNatList xs).map Sum.inr)
      (some (BinaryNatLists.encodeNatList (x :: xs)))
      (9 * ((BinaryNatLists.encodeNat x).length + (BinaryNatLists.encodeNatList xs).length) + 21) := by
  have run : TM2OutputsInTime computer
      ((BinaryNatLists.encodeNat x).map Sum.inl ++ (BinaryNatLists.encodeNatList xs).map Sum.inr)
      (some (BinaryNatLists.encodeNatList (x :: xs))) (runSteps x xs) := by
    apply toMachine_outputsInTime routine inputStack outputStack
    have hi : (initList computer
        ((BinaryNatLists.encodeNat x).map Sum.inl ++ (BinaryNatLists.encodeNatList xs).map Sum.inr)).stk =
        contents ((BinaryNatLists.encodeNat x).map Sum.inl ++
          (BinaryNatLists.encodeNatList xs).map Sum.inr) [] [] [] [] [] := by
      funext k; rcases k with (k | ⟨⟩) | ⟨⟩ <;> first | rfl | (cases k <;> rfl)
    have ho : (haltList computer (BinaryNatLists.encodeNatList (x :: xs))).stk =
        contents [] [] [] [] [] (BinaryNatLists.encodeNatList (x :: xs)) := by
      funext k; rcases k with (k | ⟨⟩) | ⟨⟩ <;> first | rfl | (cases k <;> rfl)
    change routine.Exits (initList computer _).stk _ (haltList computer _).stk
    rw [hi, ho]
    exact routine_exits x xs
  exact evalsToInTimeMono run (runSteps_le x xs)

/-- A standalone cons witness under the independently framed tagged-pair encoding. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime
      (PairEncoding.finEncoding FramedNat.finEncoding FramedNatList.finEncoding)
      FramedNatList.finEncoding (fun input : Nat × List Nat => input.1 :: input.2) where
  tm := computer
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 9 * Polynomial.X + 21
  outputsFun input := by
    simpa [PairEncoding.finEncoding, FramedNat.finEncoding, FramedNatList.finEncoding,
      Equiv.refl, TM2OutputsInTime, FinTM2.step,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X] using
        outputsInTime input.1 input.2

end LeanNPHardness.MachineAdapters.TaggedFramedListCons
