import LeanNPHardness.FramedSuccMachine
import LeanNPHardness.MachineRoutineExtension
import LeanNPHardness.MachineRoutineBound
import LeanNPHardness.BooleanListMachine

/-!
# Framed binary counts from an isolated mark stack

Consume one mark per occurrence, incrementing an isolated framed binary
counter. Two charged transfers restore the counter after each successor;
two final transfers prepend its frame to arbitrary caller output. The six
Boolean stacks finish empty except for that output. Marker values are ignored.

The input-size measure is the number of supplied marks, not the bit length
of an already encoded count. `MarkedFormulaMachine` supplies formula occurrence
marks; `FormulaVariablesMachine` separately composes full framed-list assembly.
-/

namespace LeanNPHardness.MachinePrimitives.UnaryCount

open Computability Turing Routines

inductive ExtraStack
  | marks | output
  deriving DecidableEq, Fintype

abbrev ExtraAlphabet (_ : ExtraStack) := Bool
abbrev Stack := FramedSucc.Stack ⊕ ExtraStack
abbrev Alphabet := ExtendedAlphabet (Γ := FramedSucc.Alphabet) ExtraAlphabet

instance (k : Stack) : Fintype (Alphabet k) := by
  cases k <;> exact inferInstanceAs (Fintype Bool)

def contents (header count work buffer marks output : List Bool) : Stacks Alphabet :=
  extendedStacks ExtraAlphabet (FramedSucc.contents header count work buffer)
    (fun k => match k with | .marks => marks | .output => output)

def successor : Routine Alphabet := extend ExtraAlphabet FramedSucc.routine
def reverseCounter : Routine Alphabet :=
  moveAll (Γ := Alphabet) (.inl .output) (.inl .work) id false
def restoreCounter : Routine Alphabet :=
  moveAll (Γ := Alphabet) (.inl .work) (.inl .input) id false

/-- Remove exactly one mark before updating the isolated counter. -/
def increment : Routine Alphabet :=
  seq (popOne (.inr .marks)) (seq successor (seq reverseCounter restoreCounter))

def incrementSteps (n : Nat) : Nat :=
  1 + (2 * (encodeNat n).length + 2 * (encodeNat (n + 1)).length + 4) +
    (4 * (BinaryNatLists.encodeNat (n + 1)).length + 2)

local macro "stack_eq" : tactic => `(tactic|
  (funext k; cases k with
   | inl k => cases k <;> simp [contents, extendedStacks, FramedSucc.contents,
       Function.update]
   | inr k => cases k <;> simp [contents, extendedStacks, Function.update]))

local macro "transfer_proof" : tactic => `(tactic|
  (try simp only [reverseCounter, restoreCounter, contents, extendedStacks,
    FramedSucc.contents, List.map_id_fun, List.map_id, List.append_nil,
    List.length_reverse, List.reverse_reverse]
   <;> first | rfl | stack_eq))

/-- Exact count update, including mark consumption and both restoration passes. -/
theorem increment_exits (n : Nat) (mark : Bool) (marks output : List Bool) :
    increment.Exits
      (contents (BinaryNatLists.encodeNat n) [] [] [] (mark :: marks) output)
      (incrementSteps n)
      (contents (BinaryNatLists.encodeNat (n + 1)) [] [] [] marks output) := by
  have hp : (popOne (Γ := Alphabet) (.inr .marks)).Exits
      (contents (BinaryNatLists.encodeNat n) [] [] [] (mark :: marks) output) 1
      (contents (BinaryNatLists.encodeNat n) [] [] [] marks output) := by
    convert popOne_exits (Γ := Alphabet) (.inr .marks)
      (contents (BinaryNatLists.encodeNat n) [] [] [] (mark :: marks) output) using 1
    stack_eq
  have hs : successor.Exits (contents (BinaryNatLists.encodeNat n) [] [] [] marks output)
      (2 * (encodeNat n).length + 2 * (encodeNat (n + 1)).length + 4)
      (contents [] [] [] (BinaryNatLists.encodeNat (n + 1)) marks output) := by
    simpa only [successor, contents, List.append_nil] using
      extend_exits ExtraAlphabet FramedSucc.routine
        (fun k => match k with | .marks => marks | .output => output)
        (FramedSucc.natural_exits n [] [])
  have hr : reverseCounter.Exits
      (contents [] [] [] (BinaryNatLists.encodeNat (n + 1)) marks output)
      (2 * (BinaryNatLists.encodeNat (n + 1)).length + 1)
      (contents [] [] (BinaryNatLists.encodeNat (n + 1)).reverse [] marks output) := by
    convert moveAll_exits (Γ := Alphabet) (.inl .output) (.inl .work) (by decide) id false
      (contents [] [] [] (BinaryNatLists.encodeNat (n + 1)) marks output) using 1
      <;> transfer_proof
  have ht : restoreCounter.Exits
      (contents [] [] (BinaryNatLists.encodeNat (n + 1)).reverse [] marks output)
      (2 * (BinaryNatLists.encodeNat (n + 1)).length + 1)
      (contents (BinaryNatLists.encodeNat (n + 1)) [] [] [] marks output) := by
    convert moveAll_exits (Γ := Alphabet) (.inl .work) (.inl .input) (by decide) id false
      (contents [] [] (BinaryNatLists.encodeNat (n + 1)).reverse [] marks output) using 1
      <;> transfer_proof
  have run := seq_exits _ _ hp (seq_exits _ _ hs (seq_exits _ _ hr ht))
  convert run using 1 <;> first | rfl | (simp only [incrementSteps]; omega)

/-- Counter size is bounded in consumed marks, including the zero frame. -/
theorem header_length_le (n : Nat) :
    (BinaryNatLists.encodeNat n).length ≤ 2 * n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have growth := FramedSucc.frame_length_le (encodeNat n)
      rw [binarySuccBits_encodeNat] at growth
      change (BinaryNatLists.encodeNat (n + 1)).length ≤
        (BinaryNatLists.encodeNat n).length + 2 at growth
      omega

theorem incrementSteps_le (n : Nat) : incrementSteps n ≤ 12 * n + 21 := by
  have h₀ := header_length_le n
  have h₁ := header_length_le (n + 1)
  simp only [BinaryNatLists.encodeNat, BinaryNatLists.frame_length] at h₀ h₁
  simp only [incrementSteps, BinaryNatLists.encodeNat, BinaryNatLists.frame_length]
  omega

def countLoop : Routine Alphabet := loop (.inr .marks) increment

/-- The loop counts every supplied mark once, with all tests included. -/
theorem countLoop_exits (marks output : List Bool) :
    countLoop.Exits (contents (BinaryNatLists.encodeNat 0) [] [] [] marks output)
      (loopSteps incrementSteps marks.length)
      (contents (BinaryNatLists.encodeNat marks.length) [] [] [] [] output) := by
  let S : Nat → Stacks Alphabet := fun i =>
    contents (BinaryNatLists.encodeNat i) [] [] [] (marks.drop i) output
  have hb : ∀ i < marks.length, increment.Exits (S i) (incrementSteps i) (S (i + 1)) := by
    intro i hi
    simpa only [S, List.drop_eq_getElem_cons hi] using
      increment_exits i marks[i] (marks.drop (i + 1)) output
  have hn : ∀ i < marks.length, S i (.inr .marks) ≠ [] := by
    intro i hi
    change marks.drop i ≠ []
    simpa only [Ne, List.drop_eq_nil_iff, not_le] using hi
  have run := loop_exits (.inr .marks) increment marks.length S incrementSteps hb hn
    (by simp [S, contents])
  simpa only [countLoop, S, List.drop_zero, List.drop_length] using run

def reverseHeader : Routine Alphabet :=
  moveAll (Γ := Alphabet) (.inl .input) (.inl .work) id false
def emitHeader : Routine Alphabet :=
  moveAll (Γ := Alphabet) (.inl .work) (.inr .output) id false
def emit : Routine Alphabet := seq reverseHeader emitHeader

/-- Append the complete count frame above caller output without scanning that suffix. -/
theorem emit_exits (header output : List Bool) :
    emit.Exits (contents header [] [] [] [] output) (4 * header.length + 2)
      (contents [] [] [] [] [] (header ++ output)) := by
  have h₁ : reverseHeader.Exits (contents header [] [] [] [] output)
      (2 * header.length + 1) (contents [] [] header.reverse [] [] output) := by
    convert moveAll_exits (Γ := Alphabet) (.inl .input) (.inl .work) (by decide) id false
      (contents header [] [] [] [] output) using 1
      <;> (try simp only [reverseHeader]) <;> transfer_proof
  have h₂ : emitHeader.Exits (contents [] [] header.reverse [] [] output)
      (2 * header.length + 1) (contents [] [] [] [] [] (header ++ output)) := by
    convert moveAll_exits (Γ := Alphabet) (.inl .work) (.inr .output) (by decide) id false
      (contents [] [] header.reverse [] [] output) using 1
      <;> (try simp only [emitHeader]) <;> transfer_proof
  convert seq_exits _ _ h₁ h₂ using 1 <;> first | rfl | omega

/-- Initialize the empty counter explicitly, then count and emit it. -/
def routine : Routine Alphabet :=
  seq (pushList (.inl .input) (BinaryNatLists.encodeNat 0)) (seq countLoop emit)

def runSteps (m : Nat) : Nat :=
  1 + loopSteps incrementSteps m + (4 * (BinaryNatLists.encodeNat m).length + 2)

/-- Produce the framed length of an isolated mark stack and clear every work stack. -/
theorem routine_exits (marks output : List Bool) :
    routine.Exits (contents [] [] [] [] marks output) (runSteps marks.length)
      (contents [] [] [] [] [] (BinaryNatLists.encodeNat marks.length ++ output)) := by
  have hi : (pushList (Γ := Alphabet) (.inl .input) (BinaryNatLists.encodeNat 0)).Exits
      (contents [] [] [] [] marks output) 1
      (contents (BinaryNatLists.encodeNat 0) [] [] [] marks output) := by
    convert pushList_exits (Γ := Alphabet) (.inl .input) (BinaryNatLists.encodeNat 0)
      (contents [] [] [] [] marks output) using 1
    stack_eq
  have run := seq_exits _ _ hi
    (seq_exits _ _ (countLoop_exits marks output) (emit_exits _ output))
  convert run using 1 <;> first | rfl | (simp only [runSteps]; omega)

/-- Quadratic in unary input length; initialization, transfers and tests are charged. -/
theorem runSteps_le (m : Nat) : runSteps m ≤ m * (12 * m + 30) + 8 := by
  have hl := loopSteps_le incrementSteps (12 * m + 21) m (by
    intro i hi
    exact (incrementSteps_le i).trans (by omega))
  have hh := header_length_le m
  simp only [runSteps]
  simp only [Nat.mul_add] at hl ⊢
  omega

theorem routine_exitsLE (marks output : List Bool) :
    routine.ExitsLE (contents [] [] [] [] marks output)
      (marks.length * (12 * marks.length + 30) + 8)
      (contents [] [] [] [] [] (BinaryNatLists.encodeNat marks.length ++ output)) :=
  (routine_exits marks output).le.mono (runSteps_le marks.length)

/-- A preloaded unary occurrence count produces its canonical binary frame. -/
theorem natural_exits (n : Nat) (output : List Bool) :
    routine.Exits (contents [] [] [] [] (List.replicate n true) output) (runSteps n)
      (contents [] [] [] [] [] (BinaryNatLists.encodeNat n ++ output)) := by
  simpa only [List.length_replicate] using routine_exits (List.replicate n true) output

def computer : FinTM2 := toMachine routine (.inr .marks) (.inr .output)

/-- Canonical halting output includes cleanup, control reset and the final halt. -/
def outputsInTime (marks : List Bool) :
    TM2OutputsInTime computer marks (some (BinaryNatLists.encodeNat marks.length))
      (marks.length * (12 * marks.length + 30) + 8) := by
  have run : TM2OutputsInTime computer marks (some (BinaryNatLists.encodeNat marks.length))
      (runSteps marks.length) := by
    apply toMachine_outputsInTime routine (.inr .marks) (.inr .output)
    have hi : (initList computer marks).stk = contents [] [] [] [] marks [] := by
      funext k; cases k with
      | inl k => cases k <;> rfl
      | inr k => cases k <;> rfl
    have ho : (haltList computer (BinaryNatLists.encodeNat marks.length)).stk =
        contents [] [] [] [] [] (BinaryNatLists.encodeNat marks.length) := by
      funext k; cases k with
      | inl k => cases k <;> rfl
      | inr k => cases k <;> rfl
    change routine.Exits (initList computer _).stk _ (haltList computer _).stk
    rw [hi, ho]
    simpa only [List.append_nil] using routine_exits marks []
  exact evalsToInTimeMono run (runSteps_le marks.length)

/-- Standalone length computation under raw Boolean-list and framed natural encodings. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime RawBoolList.finEncoding FramedNat.finEncoding List.length where
  tm := computer
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := Polynomial.X * (12 * Polynomial.X + 30) + 8
  outputsFun marks := by
    simpa [RawBoolList.finEncoding, FramedNat.finEncoding, Equiv.refl,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X] using outputsInTime marks

end LeanNPHardness.MachinePrimitives.UnaryCount
