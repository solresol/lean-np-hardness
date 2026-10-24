import LeanNPHardness.MachineRoutinePrimitives
import LeanNPHardness.MembershipComputable
import LeanNPHardness.PairDuplication
import LeanNPHardness.RawNatEncoding

/-!
# Boolean membership from a tagged query and dictionary

Erase the tags from the canonical pair of a framed natural and a framed
natural list. Two transfers preserve the complete bit order in exactly
`4n + 2` TM2 steps, with `n` the original tagged input length. The resulting
word is the existing serialized-membership encoding, with no size growth.

Checked machine composition supplies Boolean membership and a version that
retains the original tagged pair. Conversion, copying, cleanup and halting
are charged; the membership polynomial is separate from the linear converter.
Canonical inputs include zero, empty dictionaries and repeated entries.
This does not supply conditional insertion or malformed-input rejection.
-/

namespace LeanNPHardness.MachineAdapters.TaggedMembership

open Computability Turing Routines

inductive Stack
  | input | work | output
  deriving DecidableEq, Fintype

def Alphabet : Stack → Type
  | .input => Sum Bool Bool
  | _ => Bool

instance (k : Stack) : Fintype (Alphabet k) := by
  cases k <;> unfold Alphabet <;> infer_instance

/-- Discard only the tag, retaining its payload bit. -/
def eraseTag : Sum Bool Bool → Bool := Sum.elim id id

def contents (input : List (Sum Bool Bool)) (work output : List Bool) : Stacks Alphabet
  | .input => input
  | .work => work
  | .output => output

def reverseInput : Routine Alphabet :=
  moveAll (Γ := Alphabet) .input .work eraseTag false

def restoreOutput : Routine Alphabet :=
  moveAll (Γ := Alphabet) .work .output id false

def routine : Routine Alphabet := seq reverseInput restoreOutput

/-- Tag erasure preserves order, occurrences and an arbitrary output suffix. -/
theorem routine_exits (input : List (Sum Bool Bool)) (output : List Bool) :
    routine.Exits (contents input [] output) (4 * input.length + 2)
      (contents [] [] (input.map eraseTag ++ output)) := by
  have hr : reverseInput.Exits (contents input [] output) (2 * input.length + 1)
      (contents [] (input.map eraseTag).reverse output) := by
    unfold reverseInput
    convert moveAll_exits (Γ := Alphabet) .input .work (by decide) eraseTag false
      (contents input [] output) using 1
    · rfl
    · funext k; cases k <;> simp [contents, Function.update]
  have ho : restoreOutput.Exits (contents [] (input.map eraseTag).reverse output)
      (2 * input.length + 1) (contents [] [] (input.map eraseTag ++ output)) := by
    unfold restoreOutput
    convert moveAll_exits (Γ := Alphabet) .work .output (by decide) id false
      (contents [] (input.map eraseTag).reverse output) using 1
    · simp [contents]
    · funext k; cases k <;> simp [contents, Function.update]
  simpa only [routine, show 4 * input.length + 2 =
    (2 * input.length + 1) + (2 * input.length + 1) by omega] using
      seq_exits _ _ hr ho

def computer : FinTM2 := toMachine routine .input .output

/-- Canonical conversion includes empty workspace, reset control and halt. -/
def outputsInTime (input : List (Sum Bool Bool)) :
    TM2OutputsInTime computer input (some (input.map eraseTag)) (4 * input.length + 2) := by
  apply toMachine_outputsInTime routine Stack.input Stack.output
  have hi : (initList computer input).stk = contents input [] [] := by
    funext k; cases k <;> rfl
  have ho : (haltList computer (input.map eraseTag)).stk =
      contents [] [] (input.map eraseTag) := by
    funext k; cases k <;> rfl
  change routine.Exits (initList computer _).stk _ (haltList computer _).stk
  rw [hi, ho]
  simpa only [List.append_nil] using routine_exits input []

/-- On canonical pairs, tag erasure is exactly the membership wire format. -/
theorem encode_eq (input : Nat × List Nat) :
    ((PairEncoding.finEncoding FramedNat.finEncoding FramedNatList.finEncoding).encode
      input).map eraseTag = FramedNatListQuery.encode input := by
  simp [PairEncoding.finEncoding, FramedNat.finEncoding, FramedNatList.finEncoding,
    FramedNatListQuery.encode, List.map_map, Function.comp_def, eraseTag]

/-- The converter neither adds nor removes any encoded payload bits. -/
theorem encode_length (input : Nat × List Nat) :
    (FramedNatListQuery.encode input).length =
      ((PairEncoding.finEncoding FramedNat.finEncoding FramedNatList.finEncoding).encode
        input).length := by
  rw [← encode_eq, List.length_map]

/-- Linear identity re-encoding, measured in the original tagged symbols. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime
      (PairEncoding.finEncoding FramedNat.finEncoding FramedNatList.finEncoding)
      FramedNatListQuery.finEncoding id where
  tm := computer
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 4 * Polynomial.X + 2
  outputsFun input := by
    have run := outputsInTime
      ((PairEncoding.finEncoding FramedNat.finEncoding FramedNatList.finEncoding).encode input)
    rw [encode_eq] at run
    simpa [FramedNatListQuery.finEncoding, Equiv.refl,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X] using run

/-- Boolean membership from one tagged input, charging conversion and lookup. -/
noncomputable def membershipComputableInPolyTime :
    TM2ComputableInPolyTime
      (PairEncoding.finEncoding FramedNat.finEncoding FramedNatList.finEncoding)
      finEncodingBoolBool MachinePrimitives.CanonicalMembership.membership :=
  MachineComposition.compositionComputableInPolyTime _ _ _ id
    MachinePrimitives.CanonicalMembership.membership computableInPolyTime
    MachinePrimitives.CanonicalMembership.computableInPolyTime

/-- Retain the original query/dictionary pair, with all copying charged. -/
noncomputable def preservingMembershipComputableInPolyTime :
    TM2ComputableInPolyTime
      (PairEncoding.finEncoding FramedNat.finEncoding FramedNatList.finEncoding)
      (PairEncoding.finEncoding finEncodingBoolBool
        (PairEncoding.finEncoding FramedNat.finEncoding FramedNatList.finEncoding))
      (fun input => (MachinePrimitives.CanonicalMembership.membership input, input)) :=
  PairDuplication.retainInputComputableInPolyTime _ _ _ membershipComputableInPolyTime

end LeanNPHardness.MachineAdapters.TaggedMembership
