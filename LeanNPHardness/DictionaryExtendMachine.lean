import LeanNPHardness.DictionaryBuildMachine

/-!
# Standalone polynomial-time seeded dictionary construction

Load a tagged pair of full framed lists into the checked fold's source/seed
stacks. The empty count and header stacks hold reversed components during
loading. After folding, drain the retained source header and halt with the
extended dictionary alone. Arbitrary seed repetitions are preserved.
-/

namespace LeanNPHardness.MachineAdapters.DictionaryExtend

open Turing Routines MachinePrimitives DictionaryInsertCall

variable (c : Witness)

abbrev inputStack : Stack c := pairStack c
abbrev sourceStack : Stack c := DictionaryFold.inputStack c
abbrev headerStack : Stack c := DictionaryBuild.headerStack c

instance : Fintype (Alphabet c (headerStack c)) := inferInstanceAs (Fintype Bool)

abbrev State := Option (Sum Bool Bool)

private def held : State → Bool
  | some (.inl b) | some (.inr b) => b
  | none => false

private def isLeft : State → Bool
  | some (.inl _) => true
  | _ => false

/-- Reuse count/header as reverse buffers, without inspecting component bits. -/
def scan : Routine (Alphabet c) where
  Λ := Unit
  σ := State
  entry := ()
  init := none
  program _ := .pop (inputStack c) (fun _ s => s) <|
    .branch Option.isSome
      (.branch isLeft
        (.push (workStack c) held (.goto fun _ => ()))
        (.push (headerStack c) held (.goto fun _ => ()))) .halt

def cfg (label : Option Unit) (state : State) (pair : List (Sum Bool Bool))
    (source header dictionary work : List Bool) : TM2.Cfg (Alphabet c) Unit State :=
  ⟨label, state, contents c (empty c) source header dictionary pair [] work⟩

private abbrev step := flip Option.bind (TM2.step (scan c).program)

local macro "stack_cases" : tactic => `(tactic|
  (funext k; rcases k with k | (((k | e) | u) | s)
   · simp [contents, empty, caller, extendedStacks, Function.update, inputStack,
       pairStack, sourceStack, DictionaryFold.inputStack, workStack, headerStack,
       DictionaryBuild.headerStack, dictionaryStack, initList, haltList]
   all_goals (try cases k) <;> (try cases e) <;> (try cases u) <;> (try cases s) <;>
     simp [contents, empty, caller, DictionaryInsertInput.contents, FramedListReverse.contents,
       extendedStacks, FrameMove.contents, Function.update, inputStack, pairStack,
       sourceStack, DictionaryFold.inputStack, DictionaryInsertInput.inputStack,
       workStack, DictionaryInsertInput.countStack, headerStack, DictionaryBuild.headerStack,
       dictionaryStack, DictionaryInsertInput.dictionaryStack, initList, haltList]))

private theorem scan_nil (state : State) (source header dictionary work : List Bool) :
    step c (some (cfg c (some ()) state [] source header dictionary work)) =
      some (cfg c none none [] source header dictionary work) := by
  simp [step, flip, scan, cfg, TM2.step, TM2.stepAux, contents, extendedStacks,
    caller, inputStack, pairStack, DictionaryInsertInput.contents]

private theorem scan_cons (a : Sum Bool Bool) (state : State)
    (pair : List (Sum Bool Bool)) (source header dictionary work : List Bool) :
    step c (some (cfg c (some ()) state (a :: pair) source header dictionary work)) =
      some (cfg c (some ()) (some a) pair source
        (PairEncoding.rightSymbols [a] ++ header) dictionary
        (PairEncoding.leftSymbols [a] ++ work)) := by
  cases a <;>
    simp [step, flip, scan, cfg, TM2.step, TM2.stepAux, contents, caller,
      DictionaryInsertInput.contents, FramedListReverse.contents, extendedStacks,
      FrameMove.contents, inputStack, pairStack, workStack, headerStack,
      DictionaryBuild.headerStack, held, isLeft, PairEncoding.leftSymbols,
      PairEncoding.rightSymbols, Function.update] <;> stack_cases

/-- Exact loading scan for arbitrary tag order, preserving all occurrences. -/
theorem scan_run (pair : List (Sum Bool Bool))
    (source header dictionary work : List Bool) (state : State) :
    (step c)^[pair.length + 1]
        (some (cfg c (some ()) state pair source header dictionary work)) =
      some (cfg c none none [] source
        ((PairEncoding.rightSymbols pair).reverse ++ header) dictionary
        ((PairEncoding.leftSymbols pair).reverse ++ work)) := by
  induction pair generalizing header work state with
  | nil => simpa [PairEncoding.leftSymbols, PairEncoding.rightSymbols] using
      scan_nil c state source header dictionary work
  | cons a pair ih =>
      rw [List.length_cons, Function.iterate_succ_apply, scan_cons, ih]
      cases a <;> simp [PairEncoding.leftSymbols, PairEncoding.rightSymbols,
        List.reverse_cons, List.append_assoc]

/-- Restore each component once, leaving the fold's workspace empty. -/
def restore : Routine (Alphabet c) :=
  seq (moveAll (Γ := Alphabet c) (workStack c) (sourceStack c) id false)
    (moveAll (Γ := Alphabet c) (headerStack c) (dictionaryStack c) id false)

local macro "transfer_proof" : tactic => `(tactic|
  (try simp only [contents, caller, DictionaryInsertInput.contents,
     FramedListReverse.contents, extendedStacks, FrameMove.contents,
     workStack, sourceStack, DictionaryFold.inputStack, DictionaryInsertInput.inputStack,
     DictionaryInsertInput.countStack, headerStack, DictionaryBuild.headerStack,
     dictionaryStack, DictionaryInsertInput.dictionaryStack,
     List.map_id_fun, List.map_id, List.length_reverse, List.reverse_reverse, List.append_nil]
   <;> first | rfl | stack_cases))

theorem restore_exits (source dictionary : List Bool) :
    (restore c).Exits
      (contents c (empty c) [] dictionary.reverse [] [] [] source.reverse)
      (2 * source.length + 2 * dictionary.length + 2)
      (contents c (empty c) source [] dictionary [] []) := by
  have hs : (moveAll (Γ := Alphabet c) (workStack c) (sourceStack c) id false).Exits
      (contents c (empty c) [] dictionary.reverse [] [] [] source.reverse)
      (2 * source.length + 1)
      (contents c (empty c) source dictionary.reverse [] [] []) := by
    convert moveAll_exits (Γ := Alphabet c) (workStack c) (sourceStack c) (by simp)
      id false (contents c (empty c) [] dictionary.reverse [] [] [] source.reverse) using 1
      <;> transfer_proof
  have hd : (moveAll (Γ := Alphabet c) (headerStack c) (dictionaryStack c) id false).Exits
      (contents c (empty c) source dictionary.reverse [] [] [])
      (2 * dictionary.length + 1)
      (contents c (empty c) source [] dictionary [] []) := by
    convert moveAll_exits (Γ := Alphabet c) (headerStack c) (dictionaryStack c) (by simp)
      id false (contents c (empty c) source dictionary.reverse [] [] []) using 1
      <;> transfer_proof
  convert seq_exits _ _ hs hd using 1 <;> first | rfl | omega

def load : Routine (Alphabet c) := seq (scan c) (restore c)

/-- Arbitrary source/seed words load in exactly `3n + 3` steps. -/
theorem load_exits (source dictionary : List Bool) :
    (load c).Exits
      (contents c (empty c) [] [] [] (source.map Sum.inl ++ dictionary.map Sum.inr) [])
      (3 * (source.length + dictionary.length) + 3)
      (contents c (empty c) source [] dictionary [] []) := by
  have hs : (scan c).Exits
      (contents c (empty c) [] [] [] (source.map Sum.inl ++ dictionary.map Sum.inr) [])
      (source.length + dictionary.length + 1)
      (contents c (empty c) [] dictionary.reverse [] [] [] source.reverse) := by
    refine ⟨none, ?_⟩
    change (step c)^[_] (some (cfg c (some ()) none _ [] [] [] [])) = _
    have run := scan_run c (source.map Sum.inl ++ dictionary.map Sum.inr) [] [] [] [] none
    simp only [PairEncoding.leftSymbols_append, PairEncoding.rightSymbols_append,
      PairEncoding.leftSymbols_map_inl, PairEncoding.leftSymbols_map_inr,
      PairEncoding.rightSymbols_map_inl, PairEncoding.rightSymbols_map_inr,
      List.nil_append, List.append_nil, List.length_append, List.length_map] at run
    exact run
  convert seq_exits _ _ hs (restore_exits c source dictionary) using 1
    <;> first | rfl | omega

/-- Canonical tagged encoding of the two complete framed lists. -/
def pairWord (values dictionary : List Nat) : List (Sum Bool Bool) :=
  (BinaryNatLists.encodeNatList values).map Sum.inl ++
    (BinaryNatLists.encodeNatList dictionary).map Sum.inr

theorem pairWord_length (values dictionary : List Nat) :
    (pairWord values dictionary).length = DictionaryFold.inputSize values dictionary := by
  simp [pairWord, DictionaryFold.inputSize]

noncomputable def routine : Routine (Alphabet c) :=
  seq (load c) (seq (DictionaryFold.preparedRoutine c) (drain (headerStack c)))

/-- Loading, tail-first seeded folding and final header cleanup. -/
theorem routine_exits (values dictionary : List Nat) :
    (routine c).ExitsLE
      (contents c (empty c) [] [] [] (pairWord values dictionary) [])
      (3 * DictionaryFold.inputSize values dictionary + 3 +
        (DictionaryFold.timePolynomial c).eval (DictionaryFold.inputSize values dictionary) +
        (2 * (BinaryNatLists.encodeNat values.length).length + 1))
      (contents c (empty c) [] []
        (BinaryNatLists.encodeNatList (DictionaryConstruction.extend values dictionary)) [] []) := by
  have run := seq_exitsLE _ _
    (load_exits c (BinaryNatLists.encodeNatList values)
      (BinaryNatLists.encodeNatList dictionary)).le
    (seq_exitsLE _ _ (DictionaryFold.bounded_exits c values dictionary)
      (DictionaryBuild.cleanup_exits c (BinaryNatLists.encodeNat values.length)
        (BinaryNatLists.encodeNatList (DictionaryConstruction.extend values dictionary))).le)
  convert run using 1 <;> first | rfl | (simp only [DictionaryFold.inputSize]; omega)

/-- All wrapper costs are charged in the original tagged-pair length. -/
noncomputable def timePolynomial : Polynomial Nat :=
  DictionaryFold.timePolynomial c + 5 * Polynomial.X + 4

theorem runSteps_le (values dictionary : List Nat) :
    3 * DictionaryFold.inputSize values dictionary + 3 +
      (DictionaryFold.timePolynomial c).eval (DictionaryFold.inputSize values dictionary) +
      (2 * (BinaryNatLists.encodeNat values.length).length + 1) ≤
    (timePolynomial c).eval (pairWord values dictionary).length := by
  have header : (BinaryNatLists.encodeNat values.length).length ≤
      DictionaryFold.inputSize values dictionary := by
    simp only [DictionaryFold.inputSize, BinaryNatLists.encodeNatList, List.length_append]
    omega
  simp only [timePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_X, Polynomial.eval_ofNat, pairWord_length]
  omega

noncomputable def computer : FinTM2 := by
  letI : Fintype c.tm.K := c.tm.kFin
  exact toMachine (routine c) (inputStack c) (dictionaryStack c)

/-- Canonical halting output, empty workspace and reset state are included. -/
noncomputable def outputsInTime (values dictionary : List Nat) :
    TM2OutputsInTime (computer c) (pairWord values dictionary)
      (some (BinaryNatLists.encodeNatList (DictionaryConstruction.extend values dictionary)))
      ((timePolynomial c).eval (pairWord values dictionary).length) := by
  letI : Fintype c.tm.K := c.tm.kFin
  apply toMachine_outputsInTime_le (routine c) (inputStack c) (dictionaryStack c)
  have hi : (initList (computer c) (pairWord values dictionary)).stk =
      contents c (empty c) [] [] [] (pairWord values dictionary) [] := by
    simp only [computer, toMachine, initList]
    stack_cases
  have ho : (haltList (computer c)
        (BinaryNatLists.encodeNatList (DictionaryConstruction.extend values dictionary))).stk =
      contents c (empty c) [] []
        (BinaryNatLists.encodeNatList (DictionaryConstruction.extend values dictionary)) [] [] := by
    simp only [computer, toMachine, haltList]
    stack_cases
  change (routine c).ExitsLE (initList (computer c) _).stk _ (haltList (computer c) _).stk
  rw [hi, ho]
  exact (routine_exits c values dictionary).mono (runSteps_le c values dictionary)

/-- Standalone seeded construction; no duplicate-free hypothesis on the seed. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime
      (PairEncoding.finEncoding FramedNatList.finEncoding FramedNatList.finEncoding)
      FramedNatList.finEncoding
      (fun input : List Nat × List Nat => DictionaryConstruction.extend input.1 input.2) where
  tm := computer DictionaryInsert.computableInPolyTime
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := timePolynomial DictionaryInsert.computableInPolyTime
  outputsFun input := by
    simpa [PairEncoding.finEncoding, FramedNatList.finEncoding, Equiv.refl, pairWord] using
      outputsInTime DictionaryInsert.computableInPolyTime input.1 input.2

end LeanNPHardness.MachineAdapters.DictionaryExtend
