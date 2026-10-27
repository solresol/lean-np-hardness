import LeanNPHardness.FrameReverseMachine
import LeanNPHardness.MachineRoutineExtension
import LeanNPHardness.MachineRoutinePrimitives
import LeanNPHardness.RawNatEncoding

/-!
# Reversing a complete framed natural list

Separate the count header, reverse the isolated body, and retain an arbitrary
seed on an untouched stack. The preparation contract supports tail-first
dictionary traversal. Reattaching the unchanged header also gives a standalone
linear-time reversal under `FramedNatList.finEncoding`. All costs count TM2
steps in complete encoded input bits, including header storage and cleanup.
-/

namespace LeanNPHardness.MachinePrimitives.FramedListReverse

open Computability Turing Routines

inductive Extra
  | header | seed
  deriving DecidableEq, Fintype

abbrev Stack := FrameMove.Stack ⊕ Extra
abbrev ExtraAlphabet (_ : Extra) := Bool
abbrev Alphabet := ExtendedAlphabet (Γ := FrameMove.Alphabet) ExtraAlphabet

instance (k : Stack) : Fintype (Alphabet k) := by
  cases k <;> exact inferInstanceAs (Fintype Bool)

def contents (input count work output header seed : List Bool) : Stacks Alphabet :=
  extendedStacks ExtraAlphabet (FrameMove.contents input count work output)
    (fun | .header => header | .seed => seed)

private def extractHeader : Routine Alphabet := extend ExtraAlphabet FrameMove.routine
private def reverseHeader : Routine Alphabet :=
  moveAll (Γ := Alphabet) (.inl .output) (.inl .count) id false
private def storeHeader : Routine Alphabet :=
  moveAll (Γ := Alphabet) (.inl .count) (.inr .header) id false

/-- Separate one intact leading frame while preserving its arbitrary suffix and seed. -/
def splitHeader : Routine Alphabet := seq extractHeader (seq reverseHeader storeHeader)

local macro "transfer_proof" : tactic => `(tactic|
  (try simp only [reverseHeader, storeHeader, contents, extendedStacks, FrameMove.contents,
    List.map_id_fun, List.map_id, List.length_reverse, List.reverse_reverse,
    List.append_nil]
   <;> first | rfl | (funext k; rcases k with k | k <;> cases k <;>
     simp [contents, extendedStacks, FrameMove.contents, Function.update,
       Alphabet, ExtendedAlphabet])))

/-- The header is stored in its original bit order; all workspace is cleared. -/
theorem splitHeader_exits (bits input seed : List Bool) :
    splitHeader.Exits
      (contents (BinaryNatLists.frame bits ++ input) [] [] [] [] seed)
      (6 * (BinaryNatLists.frame bits).length + 4)
      (contents input [] [] [] (BinaryNatLists.frame bits) seed) := by
  let header := BinaryNatLists.frame bits
  have h₁ : extractHeader.Exits (contents (header ++ input) [] [] [] [] seed)
      (2 * header.length + 2) (contents input [] [] header [] seed) := by
    have run := FrameMove.routine_exits bits input []
    rw [FrameMove.runSteps_eq_frame_length] at run
    simpa only [extractHeader, contents, header, List.append_nil] using
      extend_exits ExtraAlphabet FrameMove.routine
        (fun | .header => [] | .seed => seed) run
  have h₂ : reverseHeader.Exits (contents input [] [] header [] seed)
      (2 * header.length + 1) (contents input header.reverse [] [] [] seed) := by
    convert moveAll_exits (Γ := Alphabet) (.inl .output) (.inl .count) (by decide)
      id false (contents input [] [] header [] seed) using 1 <;> transfer_proof
  have h₃ : storeHeader.Exits (contents input header.reverse [] [] [] seed)
      (2 * header.length + 1) (contents input [] [] [] header seed) := by
    convert moveAll_exits (Γ := Alphabet) (.inl .count) (.inr .header) (by decide)
      id false (contents input header.reverse [] [] [] seed) using 1 <;> transfer_proof
  have run := seq_exits _ _ h₁ (seq_exits _ _ h₂ h₃)
  convert run using 1 <;> (try dsimp only [header]) <;> first | rfl | omega

/-- Body reversal leaves the stored header and seed untouched. -/
def reverseBody : Routine Alphabet := extend ExtraAlphabet FrameReverse.routine

theorem reverseBody_exits (values : List Nat) (output header seed : List Bool) :
    reverseBody.Exits
      (contents (values.flatMap BinaryNatLists.encodeNat) [] [] output header seed)
      (2 * (values.flatMap BinaryNatLists.encodeNat).length + 3 * values.length + 1)
      (contents [] [] [] (values.reverse.flatMap BinaryNatLists.encodeNat ++ output)
        header seed) := by
  exact extend_exits ExtraAlphabet FrameReverse.routine
    (fun | .header => header | .seed => seed) (FrameReverse.natural_body_exits values output)

/-- Prepare a complete list for tail-first traversal without consuming its seed. -/
def prepare : Routine Alphabet := seq splitHeader reverseBody

def prepareSteps (values : List Nat) : Nat :=
  6 * (BinaryNatLists.encodeNat values.length).length +
    2 * (values.flatMap BinaryNatLists.encodeNat).length + 3 * values.length + 5

theorem prepare_exits (values : List Nat) (seed : List Bool) :
    prepare.Exits (contents (BinaryNatLists.encodeNatList values) [] [] [] [] seed)
      (prepareSteps values)
      (contents [] [] [] (values.reverse.flatMap BinaryNatLists.encodeNat)
        (BinaryNatLists.encodeNat values.length) seed) := by
  have run := seq_exits _ _
    (splitHeader_exits (encodeNat values.length) (values.flatMap BinaryNatLists.encodeNat) seed)
    (reverseBody_exits values [] (BinaryNatLists.encodeNat values.length) seed)
  convert run using 1 <;>
    (try simp only [prepareSteps, BinaryNatLists.encodeNat, List.append_nil]) <;>
    first | rfl | omega

private theorem length_le_body (values : List Nat) :
    values.length ≤ (values.flatMap BinaryNatLists.encodeNat).length := by
  induction values with
  | nil => simp
  | cons x xs ih =>
      simp only [List.length_cons, List.flatMap_cons, List.length_append,
        BinaryNatLists.encodeNat, BinaryNatLists.frame_length]
      omega

/-- The seed is never scanned; preparation is linear in the complete source encoding. -/
theorem prepareSteps_le (values : List Nat) :
    prepareSteps values ≤ 6 * (BinaryNatLists.encodeNatList values).length + 5 := by
  have h := length_le_body values
  simp only [prepareSteps, BinaryNatLists.encodeNatList, List.length_append]
  omega

private def reverseStoredHeader : Routine Alphabet :=
  moveAll (Γ := Alphabet) (.inr .header) (.inl .count) id false
private def emitHeader : Routine Alphabet :=
  moveAll (Γ := Alphabet) (.inl .count) (.inl .output) id false

/-- Reattach the saved header in original order above the reversed body. -/
def assemble : Routine Alphabet := seq reverseStoredHeader emitHeader

theorem assemble_exits (body header seed : List Bool) :
    assemble.Exits (contents [] [] [] body header seed)
      (4 * header.length + 2) (contents [] [] [] (header ++ body) [] seed) := by
  have h₁ : reverseStoredHeader.Exits (contents [] [] [] body header seed)
      (2 * header.length + 1) (contents [] header.reverse [] body [] seed) := by
    unfold reverseStoredHeader
    convert moveAll_exits (Γ := Alphabet) (.inr .header) (.inl .count) (by decide)
      id false (contents [] [] [] body header seed) using 1 <;> transfer_proof
  have h₂ : emitHeader.Exits (contents [] header.reverse [] body [] seed)
      (2 * header.length + 1) (contents [] [] [] (header ++ body) [] seed) := by
    unfold emitHeader
    convert moveAll_exits (Γ := Alphabet) (.inl .count) (.inl .output) (by decide)
      id false (contents [] header.reverse [] body [] seed) using 1 <;> transfer_proof
  have run := seq_exits _ _ h₁ h₂
  simpa only [assemble, show 4 * header.length + 2 =
    (2 * header.length + 1) + (2 * header.length + 1) by omega] using run

def routine : Routine Alphabet := seq prepare assemble

def runSteps (values : List Nat) : Nat :=
  10 * (BinaryNatLists.encodeNat values.length).length +
    2 * (values.flatMap BinaryNatLists.encodeNat).length + 3 * values.length + 7

/-- Complete list reversal preserves every value occurrence and the arbitrary seed. -/
theorem routine_exits (values : List Nat) (seed : List Bool) :
    routine.Exits (contents (BinaryNatLists.encodeNatList values) [] [] [] [] seed)
      (runSteps values) (contents [] [] [] (BinaryNatLists.encodeNatList values.reverse) [] seed) := by
  have run := seq_exits _ _ (prepare_exits values seed)
    (assemble_exits (values.reverse.flatMap BinaryNatLists.encodeNat)
      (BinaryNatLists.encodeNat values.length) seed)
  convert run using 1 <;>
    (try simp only [runSteps, prepareSteps, BinaryNatLists.encodeNatList, List.length_reverse]) <;>
    first | rfl | omega

theorem runSteps_le (values : List Nat) :
    runSteps values ≤ 10 * (BinaryNatLists.encodeNatList values).length + 7 := by
  have h := length_le_body values
  simp only [runSteps, BinaryNatLists.encodeNatList, List.length_append]
  omega

/-- The count header and total body size are unchanged by reversal. -/
theorem output_length (values : List Nat) :
    (BinaryNatLists.encodeNatList values.reverse).length =
      (BinaryNatLists.encodeNatList values).length := by
  simp only [BinaryNatLists.encodeNatList, List.length_append, List.length_reverse,
    List.length_flatMap, List.map_reverse, List.sum_reverse]

def computer : FinTM2 := toMachine routine (.inl .input) (.inl .output)

/-- Canonical output with empty workspace, reset control and final halt included. -/
def outputsInTime (values : List Nat) :
    TM2OutputsInTime computer (BinaryNatLists.encodeNatList values)
      (some (BinaryNatLists.encodeNatList values.reverse))
      (10 * (BinaryNatLists.encodeNatList values).length + 7) := by
  have run : TM2OutputsInTime computer (BinaryNatLists.encodeNatList values)
      (some (BinaryNatLists.encodeNatList values.reverse)) (runSteps values) := by
    apply toMachine_outputsInTime routine (.inl .input) (.inl .output)
    have hi : (initList computer (BinaryNatLists.encodeNatList values)).stk =
        contents (BinaryNatLists.encodeNatList values) [] [] [] [] [] := by
      funext k; rcases k with k | k <;> cases k <;> rfl
    have ho : (haltList computer (BinaryNatLists.encodeNatList values.reverse)).stk =
        contents [] [] [] (BinaryNatLists.encodeNatList values.reverse) [] [] := by
      funext k; rcases k with k | k <;> cases k <;> rfl
    change routine.Exits (initList computer _).stk _ (haltList computer _).stk
    rw [hi, ho]
    exact routine_exits values []
  exact evalsToInTimeMono run (runSteps_le values)

/-- Reversal of full framed natural lists with polynomial `10X + 7`. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime FramedNatList.finEncoding FramedNatList.finEncoding List.reverse where
  tm := computer
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 10 * Polynomial.X + 7
  outputsFun values := by
    simpa [FramedNatList.finEncoding, Equiv.refl, Polynomial.eval_add,
      Polynomial.eval_mul, Polynomial.eval_X] using outputsInTime values

end LeanNPHardness.MachinePrimitives.FramedListReverse
