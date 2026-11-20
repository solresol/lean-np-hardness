import LeanNPHardness.LiteralRenameMachine
import LeanNPHardness.MachineRoutineCall
import LeanNPHardness.MachineRoutineRightExtension
import LeanNPHardness.MachineRoutineBound

/-!
# Renaming one literal from a binary CNF stream

Move the leading packed frame, copy the reusable dictionary into the private
renamer's input, then prepend the tagged literal bits there. A single transfer
of the result extends a reversed unary output prefix. Thus successive calls
can read left to right without rescanning the prefix or the unread stream.
-/

namespace LeanNPHardness.MachineAdapters.LiteralRenameStep

open Computability Turing Routines MachinePrimitives CNF.Unary

abbrev Witness := TM2ComputableInPolyTime LiteralDictionary.inputEncoding
  literalEncoding LiteralRename.rename

inductive Extra
  | dictionary | output
  deriving DecidableEq, Fintype

def ExtraAlphabet : Extra → Type
  | .dictionary => Bool
  | .output => Sym

abbrev CallerAlphabet := ExtendedAlphabet (Γ := FrameMove.Alphabet) ExtraAlphabet

variable (c : Witness)

abbrev Stack := c.tm.K ⊕ (FrameMove.Stack ⊕ Extra)
abbrev Alphabet := ExtendedAlphabet (Γ := c.tm.Γ) CallerAlphabet

private abbrev frameStack : Stack c := .inr (.inl .output)
private abbrev scratchStack : Stack c := .inr (.inl .count)
private abbrev dictStack : Stack c := .inr (.inr .dictionary)
private abbrev outStack : Stack c := .inr (.inr .output)

private instance : Fintype (Alphabet c (frameStack c)) := inferInstanceAs (Fintype Bool)
private instance : Fintype (Alphabet c (scratchStack c)) := inferInstanceAs (Fintype Bool)
private instance : Fintype (Alphabet c (dictStack c)) := inferInstanceAs (Fintype Bool)
private noncomputable instance : Fintype (Alphabet c (.inl c.tm.k₁)) :=
  Fintype.ofEquiv Sym c.outputAlphabet.symm

private def extra (dictionary : List Bool) (output : List Sym) : Stacks ExtraAlphabet
  | .dictionary => dictionary
  | .output => output

/-- The private machine stacks and the caller's frame mover, dictionary and output. -/
def layout (privateStacks : Stacks c.tm.Γ) (input scratch frame dictionary : List Bool)
    (output : List Sym) : Stacks (Alphabet c) :=
  extendedStacks CallerAlphabet privateStacks (extendedStacks ExtraAlphabet
    (FrameMove.contents input scratch [] frame) (extra dictionary output))

/-- Between calls only the raw input, framed dictionary and unary accumulator are occupied. -/
def contents (input dictionary : List Bool) (output : List Sym) : Stacks (Alphabet c) :=
  layout c (fun _ => []) input [] [] dictionary output

private def extract : Routine (Alphabet c) :=
  extendRight c.tm.Γ (extend ExtraAlphabet FrameMove.routine)

private theorem extract_exits (bits input dict : List Bool) (out : List Sym) :
    (extract c).Exits (contents c (BinaryNatLists.frame bits ++ input) dict out)
      (2 * (BinaryNatLists.frame bits).length + 2)
      (layout c (fun _ => []) input [] (BinaryNatLists.frame bits) dict out) := by
  have h := FrameMove.routine_exits bits input []
  rw [FrameMove.runSteps_eq_frame_length, List.append_nil] at h
  exact extendRight_exits c.tm.Γ _ (fun _ => [])
    (extend_exits ExtraAlphabet _ (extra dict out) h)

private def leftBit (b : Bool) := c.inputAlphabet.symm (Sum.inl b)
private def rightBit (b : Bool) := c.inputAlphabet.symm (Sum.inr b)

private noncomputable def copyDictionary : Routine (Alphabet c) :=
  copyAll (dictStack c) (.inl c.tm.k₀) (scratchStack c) id id (rightBit c)
    false false (rightBit c false)

private noncomputable def loadFrame : Routine (Alphabet c) :=
  seq (moveAll (Γ := Alphabet c) (frameStack c) (scratchStack c) id false)
    (moveAll (Γ := Alphabet c) (scratchStack c) (.inl c.tm.k₀) (leftBit c) (leftBit c false))

private abbrev loaded (word : List (c.tm.Γ c.tm.k₀)) := (initList c.tm word).stk

local macro "caller_stacks" : tactic => `(tactic|
  (rename_i k; rcases k with k | k <;> cases k <;>
    simp [layout, extendedStacks, FrameMove.contents, extra, Function.update,
      dictStack, frameStack, scratchStack, outStack]))

/-- The right-tagged copy is made on the private input itself. -/
private theorem copy_exits (input frame dict : List Bool) (out : List Sym) :
    (copyDictionary c).Exits (layout c (fun _ => []) input [] frame dict out)
      (4 * dict.length + 2)
      (layout c (loaded c (dict.map (rightBit c))) input [] frame dict out) := by
  convert copyAll_exits (Γ := Alphabet c) (dictStack c) (.inl c.tm.k₀) (scratchStack c)
    id id (rightBit c) false false (rightBit c false) (by simp)
    (by simp [dictStack, scratchStack]) (by simp) (fun _ => rfl) (layout c (fun _ => []) input [] frame dict out) rfl using 1 <;> try rfl
  funext k
  cases k with
  | inl k =>
    by_cases h : k = c.tm.k₀
    · subst k; simp [layout, loaded, initList, dictStack, extra]
    · simp [layout, loaded, initList, Function.update, h]
  | inr k => caller_stacks

private theorem loadFrame_exits (input frame dict : List Bool) (out : List Sym)
    (word : List (c.tm.Γ c.tm.k₀)) :
    (loadFrame c).Exits (layout c (loaded c word) input [] frame dict out)
      (4 * frame.length + 2)
      (layout c (loaded c (frame.map (leftBit c) ++ word)) input [] [] dict out) := by
  have first : (moveAll (Γ := Alphabet c) (frameStack c) (scratchStack c) id false).Exits
      (layout c (loaded c word) input [] frame dict out) (2 * frame.length + 1)
      (layout c (loaded c word) input frame.reverse [] dict out) := by
    convert moveAll_exits (Γ := Alphabet c) (frameStack c) (scratchStack c)
      (by simp [frameStack, scratchStack]) id false (layout c (loaded c word) input [] frame dict out) using 1 <;> try rfl
    funext k; cases k
    · rfl
    · caller_stacks
  have second : (moveAll (Γ := Alphabet c) (scratchStack c) (.inl c.tm.k₀)
        (leftBit c) (leftBit c false)).Exits
      (layout c (loaded c word) input frame.reverse [] dict out) (2 * frame.length + 1)
      (layout c (loaded c (frame.map (leftBit c) ++ word)) input [] [] dict out) := by
    convert moveAll_exits (Γ := Alphabet c) (scratchStack c) (.inl c.tm.k₀) (by simp)
      (leftBit c) (leftBit c false) (layout c (loaded c word) input frame.reverse [] dict out)
      using 1
    · simp [layout, scratchStack, FrameMove.contents]
    · funext k
      cases k with
      | inl k =>
        by_cases h : k = c.tm.k₀
        · subst k; simp [layout, loaded, initList, scratchStack, FrameMove.contents, List.map_reverse]
        · simp [layout, loaded, initList, Function.update, h, scratchStack]
      | inr k => caller_stacks
  convert seq_exits _ _ first second using 1 <;> first | rfl | omega

/-- Extraction, dictionary copy and ordered loading into the machine input. -/
noncomputable def load : Routine (Alphabet c) :=
  seq (extract c) (seq (copyDictionary c) (loadFrame c))

theorem load_exits (lit : CNF.Literal Nat) (dict : List Nat) (input : List Bool)
    (out : List Sym) :
    let frame := BinaryNatLists.encodeNat lit.toNat
    let dictionary := BinaryNatLists.encodeNatList dict
    let wire := LiteralDictionary.inputEncoding.encode (lit, dict)
    (load c).Exits (contents c (frame ++ input) dictionary out)
      (6 * frame.length + 4 * dictionary.length + 6)
      (layout c (initList c.tm (wire.map c.inputAlphabet.symm)).stk input [] [] dictionary out) := by
  dsimp only
  let frame := BinaryNatLists.encodeNat lit.toNat
  let dictionary := BinaryNatLists.encodeNatList dict
  have run := seq_exits _ _ (extract_exits c (encodeNat lit.toNat) input dictionary out)
    (seq_exits _ _ (copy_exits c input frame dictionary out)
      (loadFrame_exits c input frame dictionary out (dictionary.map (rightBit c))))
  have wire : (LiteralDictionary.inputEncoding.encode (lit, dict)).map c.inputAlphabet.symm =
      frame.map (leftBit c) ++ dictionary.map (rightBit c) := by
    simp [LiteralDictionary.inputEncoding, PairEncoding.finEncoding_encode, frame, dictionary,
      List.map_map, Function.comp_def]
    rfl
  rw [wire]
  convert run using 1 <;> try rfl
  change 6 * frame.length + 4 * dictionary.length + 6 =
    2 * frame.length + 2 + (4 * dictionary.length + 2 + (4 * frame.length + 2))
  omega

private noncomputable def collect : Routine (Alphabet c) :=
  moveAll (.inl c.tm.k₁) (outStack c) c.outputAlphabet .mark

private theorem collect_exits (word : List Sym) (input dictionary : List Bool) (out : List Sym) :
    (collect c).Exits
      (layout c (haltList c.tm (word.map c.outputAlphabet.symm)).stk input [] [] dictionary out)
      (2 * word.length + 1) (contents c input dictionary (word.reverse ++ out)) := by
  convert moveAll_exits (Γ := Alphabet c) (.inl c.tm.k₁) (outStack c) (by simp)
    c.outputAlphabet .mark
    (layout c (haltList c.tm (word.map c.outputAlphabet.symm)).stk input [] [] dictionary out)
    using 1 <;> try rfl
  · simp [layout, haltList]
  · unfold contents
    funext k; cases k with
    | inl k =>
      by_cases h : k = c.tm.k₁
      · subst k; simp [layout, outStack]
      · simp [layout, haltList, Function.update, h, outStack]
    | inr k =>
      caller_stacks
      simp [haltList, List.map_map, Function.comp_def]

/-- The output stack holds the reverse of the unary prefix produced so far. -/
noncomputable def routine : Routine (Alphabet c) :=
  seq (load c) (seq (extend CallerAlphabet (ofMachine c.tm)) (collect c))

/-- Charge loading and result transfer separately from the actual rename call. -/
theorem routine_exits (lit : CNF.Literal Nat) (dict : List Nat) (input : List Bool)
    (out : List Sym) :
    let frame := BinaryNatLists.encodeNat lit.toNat
    let dictionary := BinaryNatLists.encodeNatList dict
    let result := encodeLiteral (LiteralRename.rename (lit, dict))
    ∃ n ≤ c.time.eval (LiteralDictionary.inputEncoding.encode (lit, dict)).length,
      (routine c).Exits (contents c (frame ++ input) dictionary out)
        (6 * frame.length + 4 * dictionary.length + 6 + (n + (2 * result.length + 1)))
        (contents c input dictionary (result.reverse ++ out)) := by
  obtain ⟨n, hn, call⟩ := ofMachine_extended_exits CallerAlphabet c.tm
    (extendedStacks ExtraAlphabet (FrameMove.contents input [] [] [])
      (extra (BinaryNatLists.encodeNatList dict) out)) _ _ _ (c.outputsFun (lit, dict))
  exact ⟨n, hn, seq_exits _ _ (load_exits c lit dict input out)
    (seq_exits _ _ call (collect_exits c _ _ _ _))⟩

/-- The input measure is the full packed frame plus the complete framed dictionary. -/
noncomputable def timePolynomial : Polynomial Nat := c.time + 8 * Polynomial.X + 7

theorem bounded_exits (lit : CNF.Literal Nat) (dict : List Nat) (input : List Bool)
    (out : List Sym) :
    let frame := BinaryNatLists.encodeNat lit.toNat
    let dictionary := BinaryNatLists.encodeNatList dict
    (routine c).ExitsLE (contents c (frame ++ input) dictionary out)
      ((timePolynomial c).eval (frame.length + dictionary.length))
      (contents c input dictionary ((encodeLiteral (LiteralRename.rename (lit, dict))).reverse ++ out)) := by
  obtain ⟨n, hn, run⟩ := routine_exits c lit dict input out
  refine ⟨_, ?_, run⟩
  have size := LiteralRename.encode_length_le (lit, dict)
  simp only [LiteralDictionary.inputEncoding, PairEncoding.finEncoding_encode_length,
    FramedLiteral.finEncoding, FramedNatList.finEncoding] at hn size
  change (encodeLiteral (LiteralRename.rename (lit, dict))).length ≤ _ at size
  simp only [timePolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
    Polynomial.eval_X]
  omega

/-- With the checked renamer, one call appends the renamed occurrence to the logical prefix
and preserves even a noncanonical unread suffix, with no private or scratch data left. -/
theorem literal_exits (lit : CNF.Literal Nat) (dict : List Nat) (input : List Bool)
    (prior : List Sym) :
    let c := LiteralRename.computableInPolyTime
    let frame := BinaryNatLists.encodeNat lit.toNat
    let dictionary := BinaryNatLists.encodeNatList dict
    (routine c).ExitsLE (contents c (frame ++ input) dictionary prior.reverse)
      ((timePolynomial c).eval (frame.length + dictionary.length))
      (contents c input dictionary (prior ++ encodeLiteral (LiteralRename.rename (lit, dict))).reverse) := by
  simpa only [List.reverse_append] using
    bounded_exits LiteralRename.computableInPolyTime lit dict input prior.reverse

/-- Processing the head of a clause body extends its dense-renamed occurrence prefix.
Every remaining literal frame and any following formula data stay on the input stack. -/
theorem clause_head_exits (formula : CNF.Formula Nat) (done rest : CNF.Clause Nat)
    (lit : CNF.Literal Nat) (input : List Bool) :
    let c := LiteralRename.computableInPolyTime
    let pack := fun l : CNF.Literal Nat => BinaryNatLists.encodeNat l.toNat
    let emit := fun l : CNF.Literal Nat => encodeLiteral (l.rename formula.denseIndex)
    let dictionary := BinaryNatLists.encodeNatList formula.variableDictionary
    (routine c).ExitsLE
      (contents c ((lit :: rest).flatMap pack ++ input) dictionary (done.flatMap emit).reverse)
      ((timePolynomial c).eval ((pack lit).length + dictionary.length))
      (contents c (rest.flatMap pack ++ input) dictionary ((done ++ [lit]).flatMap emit).reverse) := by
  simpa only [List.flatMap_cons, List.flatMap_append, List.flatMap_nil, List.append_nil,
    List.append_assoc, LiteralRename.rename_dense] using
    literal_exits lit formula.variableDictionary
      (rest.flatMap (fun l => BinaryNatLists.encodeNat l.toNat) ++ input)
      (done.flatMap (fun l => encodeLiteral (l.rename formula.denseIndex)))

end LeanNPHardness.MachineAdapters.LiteralRenameStep
