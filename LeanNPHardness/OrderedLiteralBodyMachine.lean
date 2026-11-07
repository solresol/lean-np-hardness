import LeanNPHardness.LiteralBodyMachine
import LeanNPHardness.FrameReverseMachine
import LeanNPHardness.MachineRoutinePrimitives

/-!
# Extracting a literal body's variables in source order

The checked literal-body loop emits variables in reverse occurrence order.
Return that complete output to the input stack without changing its bits, then
run the checked complete-frame reversal. The same four stacks suffice, and every
transfer and loop test is charged. The final output retains the source order and
all repetitions, with no growth and runtime at most `15B + 4` in source body bits.

The input is an isolated literal body: no count headers or trailing input. The
other stacks start empty. Counted clause/formula traversal, a standalone body
encoding and malformed-input rejection are separate obligations.
-/

namespace LeanNPHardness.MachinePrimitives.OrderedLiteralBody

open Computability Turing Routines
open FrameMove (Stack Alphabet contents)

/-- Return an arbitrary body to input in its original bit order via empty count. -/
def returnBody : Routine Alphabet :=
  seq (moveAll (Γ := Alphabet) Stack.output Stack.count id false)
    (moveAll (Γ := Alphabet) Stack.count Stack.input id false)

local macro "transfer_proof" : tactic => `(tactic|
  (try simp only [contents, List.map_id_fun, List.map_id,
    List.length_reverse, List.reverse_reverse, List.append_nil]
   <;> first | rfl | (funext k; cases k <;> simp [contents, Function.update])))

/-- Both bit reversals are counted; the original body order is restored. -/
theorem returnBody_exits (body : List Bool) :
    returnBody.Exits (contents [] [] [] body) (4 * body.length + 2)
      (contents body [] [] []) := by
  have h₁ : (moveAll (Γ := Alphabet) Stack.output Stack.count id false).Exits
      (contents [] [] [] body) (2 * body.length + 1)
      (contents [] body.reverse [] []) := by
    convert moveAll_exits (Γ := Alphabet) Stack.output Stack.count (by decide)
      id false (contents [] [] [] body) using 1 <;> transfer_proof
  have h₂ : (moveAll (Γ := Alphabet) Stack.count Stack.input id false).Exits
      (contents [] body.reverse [] []) (2 * body.length + 1)
      (contents body [] [] []) := by
    convert moveAll_exits (Γ := Alphabet) Stack.count Stack.input (by decide)
      id false (contents [] body.reverse [] []) using 1 <;> transfer_proof
  have run := seq_exits _ _ h₁ h₂
  convert run using 1 <;> first | rfl | omega

/-- Extract, return the reversed variable body, then reverse complete frames. -/
def routine : Routine Alphabet :=
  seq LiteralBody.routine (seq returnBody FrameReverse.routine)

/-- Exact phase sum in the original payloads, before their low bits are removed. -/
def runSteps (frames : List (List Bool)) : Nat :=
  LiteralBody.runSteps frames +
    (4 * (frames.reverse.flatMap (fun bits => BinaryNatLists.frame bits.tail)).length + 2) +
    FrameReverse.runSteps (frames.reverse.map List.tail)

/-- Ordered extraction consumes exactly the body and clears every work stack. -/
theorem routine_exits (frames : List (List Bool)) :
    routine.Exits (contents (frames.flatMap BinaryNatLists.frame) [] [] [])
      (runSteps frames)
      (contents [] [] [] (frames.flatMap (fun bits => BinaryNatLists.frame bits.tail))) := by
  have h₁ := LiteralBody.routine_exits frames []
  simp only [List.append_nil] at h₁
  have h₂ := returnBody_exits
    (frames.reverse.flatMap (fun bits => BinaryNatLists.frame bits.tail))
  have h₃ := FrameReverse.routine_exits (frames.reverse.map List.tail) []
  simp only [List.flatMap_map, ← List.map_reverse, List.reverse_reverse,
    List.append_nil] at h₃
  have run := seq_exits _ _ h₁ (seq_exits _ _ h₂ h₃)
  simpa only [routine, runSteps, Nat.add_assoc] using run

/-- Extraction cost plus six steps per output bit, three per frame and three tests. -/
theorem runSteps_eq (frames : List (List Bool)) :
    runSteps frames = LiteralBody.runSteps frames +
      6 * (frames.flatMap (fun bits => BinaryNatLists.frame bits.tail)).length +
      3 * frames.length + 3 := by
  simp only [runSteps, FrameReverse.runSteps_eq, List.length_map, List.length_reverse,
    List.length_flatMap, List.map_reverse, List.sum_reverse, List.map_map, Function.comp_def]
  omega

/-- Removing low bits retains source order and cannot enlarge the body. -/
theorem output_length_le (frames : List (List Bool)) :
    (frames.flatMap (fun bits => BinaryNatLists.frame bits.tail)).length ≤
      (frames.flatMap BinaryNatLists.frame).length := by
  simpa only [List.length_flatMap, List.map_reverse, List.sum_reverse] using
    LiteralBody.output_length_le frames

/-- All phases are linear in the original body bits, including empty input. -/
theorem runSteps_le (frames : List (List Bool)) :
    runSteps frames ≤ 15 * (frames.flatMap BinaryNatLists.frame).length + 4 := by
  have hcount : frames.length ≤ (frames.flatMap BinaryNatLists.frame).length := by
    induction frames with
    | nil => simp
    | cons bits frames ih =>
        simp only [List.length_cons, List.flatMap_cons, List.length_append,
          BinaryNatLists.frame_length]
        omega
  have hextract := LiteralBody.runSteps_le frames
  have hsize := output_length_le frames
  rw [runSteps_eq]
  omega

/-- One variable per original literal, in source order, with all repetitions. -/
theorem literal_body_exits (literals : List (CNF.Literal Nat)) :
    routine.Exits
      (contents (literals.flatMap (fun l => BinaryNatLists.encodeNat l.toNat)) [] [] [])
      (runSteps (literals.map (fun l => encodeNat l.toNat)))
      (contents [] [] [] (literals.flatMap (fun l => BinaryNatLists.encodeNat l.var))) := by
  simpa only [List.flatMap_map, Function.comp_def,
    PackedLiteral.tail_encode_toNat, BinaryNatLists.encodeNat] using
    routine_exits (literals.map (fun l => encodeNat l.toNat))

/-- The ordered variable body's encoded size is bounded by its literal source. -/
theorem literal_output_length_le (literals : List (CNF.Literal Nat)) :
    (literals.flatMap (fun l => BinaryNatLists.encodeNat l.var)).length ≤
      (literals.flatMap (fun l => BinaryNatLists.encodeNat l.toNat)).length := by
  simpa only [List.flatMap_map, Function.comp_def,
    PackedLiteral.tail_encode_toNat, BinaryNatLists.encodeNat] using
    output_length_le (literals.map (fun l => encodeNat l.toNat))

def computer : FinTM2 := toMachine routine Stack.input Stack.output

/-- Canonical source-order output, with empty workspace, reset control and halt. -/
def outputsInTime (literals : List (CNF.Literal Nat)) :
    TM2OutputsInTime computer
      (literals.flatMap (fun l => BinaryNatLists.encodeNat l.toNat))
      (some (literals.flatMap (fun l => BinaryNatLists.encodeNat l.var)))
      (15 * (literals.flatMap (fun l => BinaryNatLists.encodeNat l.toNat)).length + 4) := by
  have run : TM2OutputsInTime computer
      (literals.flatMap (fun l => BinaryNatLists.encodeNat l.toNat))
      (some (literals.flatMap (fun l => BinaryNatLists.encodeNat l.var)))
      (runSteps (literals.map (fun l => encodeNat l.toNat))) := by
    apply toMachine_outputsInTime routine Stack.input Stack.output
    have hi : (initList computer
        (literals.flatMap (fun l => BinaryNatLists.encodeNat l.toNat))).stk =
        contents (literals.flatMap (fun l => BinaryNatLists.encodeNat l.toNat)) [] [] [] := by
      funext k; cases k <;> rfl
    have ho : (haltList computer
        (literals.flatMap (fun l => BinaryNatLists.encodeNat l.var))).stk =
        contents [] [] [] (literals.flatMap (fun l => BinaryNatLists.encodeNat l.var)) := by
      funext k; cases k <;> rfl
    change routine.Exits (initList computer _).stk _ (haltList computer _).stk
    rw [hi, ho]
    exact literal_body_exits literals
  apply evalsToInTimeMono run
  simpa only [List.flatMap_map, Function.comp_def, BinaryNatLists.encodeNat] using
    runSteps_le (literals.map (fun l => encodeNat l.toNat))

end LeanNPHardness.MachinePrimitives.OrderedLiteralBody
