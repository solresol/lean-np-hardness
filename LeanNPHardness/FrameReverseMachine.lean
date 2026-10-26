import LeanNPHardness.FrameMoveMachine
import LeanNPHardness.MachineRun

/-!
# Reversing a stream of complete frames

The same finite routine handles every stream length. It transfers each frame
above the accumulated output, reversing frame order while retaining each
payload's bit order and all repeated occurrences. The input is an isolated
frame body, without a list-count header or an arbitrary trailing input suffix.
-/

namespace LeanNPHardness.MachinePrimitives.FrameReverse

open Computability Turing Routines
open FrameMove (Stack Alphabet contents)

/-- Move complete frames until the isolated input body is empty. -/
def routine : Routine Alphabet := loop Stack.input FrameMove.routine

/-- Exact cost, including each nonempty test and the final empty test. -/
def runSteps (frames : List (List Bool)) : Nat :=
  loopSteps (fun i => 2 * (BinaryNatLists.frame (frames[i]?.getD [])).length + 2)
    frames.length

@[simp]
theorem runSteps_nil : runSteps [] = 1 := rfl

@[simp]
theorem runSteps_cons (bits : List Bool) (frames : List (List Bool)) :
    runSteps (bits :: frames) =
      2 * (BinaryNatLists.frame bits).length + 3 + runSteps frames := by
  simp [runSteps, loopSteps, Nat.add_assoc]

/-- Every visited frame is prepended intact; the original output suffix survives. -/
theorem routine_exits (frames : List (List Bool)) (output : List Bool) :
    routine.Exits (contents (frames.flatMap BinaryNatLists.frame) [] [] output)
      (runSteps frames)
      (contents [] [] [] (frames.reverse.flatMap BinaryNatLists.frame ++ output)) := by
  let S : Nat → Stacks Alphabet := fun i =>
    contents ((frames.drop i).flatMap BinaryNatLists.frame) [] []
      ((frames.take i).reverse.flatMap BinaryNatLists.frame ++ output)
  have hbody : ∀ i < frames.length, FrameMove.routine.Exits (S i)
      (2 * (BinaryNatLists.frame (frames[i]?.getD [])).length + 2) (S (i + 1)) := by
    intro i hi
    have run := FrameMove.routine_exits frames[i]
      ((frames.drop (i + 1)).flatMap BinaryNatLists.frame)
      ((frames.take i).reverse.flatMap BinaryNatLists.frame ++ output)
    rw [FrameMove.runSteps_eq_frame_length] at run
    simpa only [S, List.drop_eq_getElem_cons hi, List.flatMap_cons,
      List.take_add_one, List.getElem?_eq_getElem hi, Option.getD_some,
      Option.toList_some, List.reverse_append, List.reverse_singleton,
      List.flatMap_append, List.flatMap_singleton, List.flatMap_nil, List.nil_append, List.append_assoc] using run
  have hne : ∀ i < frames.length, S i Stack.input ≠ [] := by
    intro i hi
    change ((frames.drop i).flatMap BinaryNatLists.frame) ≠ []
    rw [List.drop_eq_getElem_cons hi, List.flatMap_cons]
    have hpos := BinaryNatLists.frame_length frames[i]
    intro h
    have := congrArg List.length h
    simp only [List.length_append, List.length_nil] at this
    omega
  have run := loop_exits Stack.input FrameMove.routine frames.length S
    (fun i => 2 * (BinaryNatLists.frame (frames[i]?.getD [])).length + 2)
    hbody hne (by simp [S, contents])
  simpa only [routine, runSteps, S, List.drop_zero, List.take_zero,
    List.reverse_nil, List.flatMap_nil, List.nil_append, List.drop_length,
    List.take_length] using run

/-- Linear exact cost in body bits `B` and number of frames `m`: `2B + 3m + 1`. -/
theorem runSteps_eq (frames : List (List Bool)) :
    runSteps frames = 2 * (frames.flatMap BinaryNatLists.frame).length +
      3 * frames.length + 1 := by
  induction frames with
  | nil => simp
  | cons bits frames ih =>
      simp only [runSteps_cons, List.flatMap_cons, List.length_append, List.length_cons, ih]
      omega

/-- Each frame contains a separator, so `5B + 1` bounds the complete run. -/
theorem runSteps_le (frames : List (List Bool)) :
    runSteps frames ≤ 5 * (frames.flatMap BinaryNatLists.frame).length + 1 := by
  have h : frames.length ≤ (frames.flatMap BinaryNatLists.frame).length := by
    induction frames with
    | nil => simp
    | cons bits frames ih =>
        simp only [List.length_cons, List.flatMap_cons, List.length_append,
          BinaryNatLists.frame_length]
        omega
  rw [runSteps_eq]
  omega

/-- Reversal retains exactly the same number of body bits. -/
theorem output_length (frames : List (List Bool)) :
    (frames.reverse.flatMap BinaryNatLists.frame).length =
      (frames.flatMap BinaryNatLists.frame).length := by
  simp only [List.length_flatMap, List.map_reverse, List.sum_reverse]

/-- Natural-list bodies keep every occurrence, including zeros and repetitions. -/
theorem natural_body_exits (values : List Nat) (output : List Bool) :
    routine.Exits (contents (values.flatMap BinaryNatLists.encodeNat) [] [] output)
      (2 * (values.flatMap BinaryNatLists.encodeNat).length + 3 * values.length + 1)
      (contents [] [] [] (values.reverse.flatMap BinaryNatLists.encodeNat ++ output)) := by
  simpa only [runSteps_eq, List.flatMap_map, List.length_map, ← List.map_reverse,
    Function.comp_def,
    show (fun n => BinaryNatLists.frame (encodeNat n)) = BinaryNatLists.encodeNat from rfl] using
    routine_exits (values.map encodeNat) output

def computer : FinTM2 := toMachine routine Stack.input Stack.output

/-- Canonical halting output for a frame body, with empty workspace and reset control. -/
def outputsInTime (frames : List (List Bool)) :
    TM2OutputsInTime computer (frames.flatMap BinaryNatLists.frame)
      (some (frames.reverse.flatMap BinaryNatLists.frame))
      (5 * (frames.flatMap BinaryNatLists.frame).length + 1) := by
  have run : TM2OutputsInTime computer (frames.flatMap BinaryNatLists.frame)
      (some (frames.reverse.flatMap BinaryNatLists.frame)) (runSteps frames) := by
    apply toMachine_outputsInTime routine Stack.input Stack.output
    have hi : (initList computer (frames.flatMap BinaryNatLists.frame)).stk =
        contents (frames.flatMap BinaryNatLists.frame) [] [] [] := by
      funext k; cases k <;> rfl
    have ho : (haltList computer (frames.reverse.flatMap BinaryNatLists.frame)).stk =
        contents [] [] [] (frames.reverse.flatMap BinaryNatLists.frame) := by
      funext k; cases k <;> rfl
    change routine.Exits (initList computer _).stk _ (haltList computer _).stk
    rw [hi, ho]
    simpa only [List.append_nil] using routine_exits frames []
  exact evalsToInTimeMono run (runSteps_le frames)

end LeanNPHardness.MachinePrimitives.FrameReverse
