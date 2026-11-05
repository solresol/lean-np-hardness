import LeanNPHardness.LiteralVariableMachine
import LeanNPHardness.MachineRun

/-!
# Extracting variables from an isolated literal body

Iterate the checked single-literal routine over a stream of complete frames.
Each occurrence emits one variable frame, in reverse occurrence order, retaining
an arbitrary output suffix. The input must be an isolated body: list-count
headers and trailing input are not part of this exhaustion-loop contract.

The exact cost sums every literal extraction and every loop test. It is bounded
by `6B + 1` in the original body bit length `B`, including canonical reset and
halt. Clause/formula boundary handling and restoring source order remain separate.
-/

namespace LeanNPHardness.MachinePrimitives.LiteralBody

open Computability Turing Routines
open FrameMove (Stack Alphabet contents)

/-- Extract one framed variable per occurrence until the isolated body is empty. -/
def routine : Routine Alphabet := loop Stack.input LiteralVariable.routine

/-- Charge every extraction, every nonempty test, and the final empty test. -/
def runSteps (frames : List (List Bool)) : Nat :=
  loopSteps (fun i => LiteralVariable.runSteps (frames[i]?.getD [])) frames.length

@[simp]
theorem runSteps_nil : runSteps [] = 1 := rfl

@[simp]
theorem runSteps_cons (bits : List Bool) (frames : List (List Bool)) :
    runSteps (bits :: frames) = LiteralVariable.runSteps bits + 1 + runSteps frames := by
  simp [runSteps, loopSteps, Nat.add_assoc]

/-- The finite loop consumes exactly the supplied frames and retains the output suffix. -/
theorem routine_exits (frames : List (List Bool)) (output : List Bool) :
    routine.Exits (contents (frames.flatMap BinaryNatLists.frame) [] [] output)
      (runSteps frames)
      (contents [] [] []
        (frames.reverse.flatMap (fun bits => BinaryNatLists.frame bits.tail) ++ output)) := by
  let S : Nat → Stacks Alphabet := fun i =>
    contents ((frames.drop i).flatMap BinaryNatLists.frame) [] []
      ((frames.take i).reverse.flatMap (fun bits => BinaryNatLists.frame bits.tail) ++ output)
  have hbody : ∀ i < frames.length, LiteralVariable.routine.Exits (S i)
      (LiteralVariable.runSteps (frames[i]?.getD [])) (S (i + 1)) := by
    intro i hi
    have run := LiteralVariable.routine_exits frames[i]
      ((frames.drop (i + 1)).flatMap BinaryNatLists.frame)
      ((frames.take i).reverse.flatMap (fun bits => BinaryNatLists.frame bits.tail) ++ output)
    simpa only [S, List.drop_eq_getElem_cons hi, List.flatMap_cons,
      List.take_add_one, List.getElem?_eq_getElem hi, Option.getD_some,
      Option.toList_some, List.reverse_append, List.reverse_singleton,
      List.flatMap_append, List.flatMap_singleton, List.flatMap_nil,
      List.nil_append, List.append_assoc] using run
  have hne : ∀ i < frames.length, S i Stack.input ≠ [] := by
    intro i hi
    change ((frames.drop i).flatMap BinaryNatLists.frame) ≠ []
    rw [List.drop_eq_getElem_cons hi, List.flatMap_cons]
    have hpos := BinaryNatLists.frame_length frames[i]
    intro h
    have := congrArg List.length h
    simp only [List.length_append, List.length_nil] at this
    omega
  have run := loop_exits Stack.input LiteralVariable.routine frames.length S
    (fun i => LiteralVariable.runSteps (frames[i]?.getD [])) hbody hne
    (by simp [S, contents])
  simpa only [routine, runSteps, S, List.drop_zero, List.take_zero,
    List.reverse_nil, List.flatMap_nil, List.nil_append, List.drop_length,
    List.take_length] using run

/-- Exact phase sum: one extra test per frame and one final empty test. -/
theorem runSteps_eq_sum (frames : List (List Bool)) :
    runSteps frames = (frames.map LiteralVariable.runSteps).sum + frames.length + 1 := by
  induction frames with
  | nil => simp
  | cons bits frames ih =>
      simp only [runSteps_cons, List.map_cons, List.sum_cons, List.length_cons, ih]
      omega

/-- The sum is bounded using complete source frames, before polarity removal. -/
theorem runSteps_le_size_count (frames : List (List Bool)) :
    runSteps frames ≤ 2 * (frames.flatMap BinaryNatLists.frame).length +
      4 * frames.length + 1 := by
  induction frames with
  | nil => simp
  | cons bits frames ih =>
      have hb := LiteralVariable.runSteps_le bits
      simp only [runSteps_cons, List.flatMap_cons, List.length_append, List.length_cons]
      omega

/-- Every frame has a separator; thus all loop costs are linear in source bits. -/
theorem runSteps_le (frames : List (List Bool)) :
    runSteps frames ≤ 6 * (frames.flatMap BinaryNatLists.frame).length + 1 := by
  have h : frames.length ≤ (frames.flatMap BinaryNatLists.frame).length := by
    induction frames with
    | nil => simp
    | cons bits frames ih =>
        simp only [List.length_cons, List.flatMap_cons, List.length_append,
          BinaryNatLists.frame_length]
        omega
  have bound := runSteps_le_size_count frames
  omega

/-- Removing each low bit and reversing frame order cannot enlarge the body. -/
theorem output_length_le (frames : List (List Bool)) :
    (frames.reverse.flatMap (fun bits => BinaryNatLists.frame bits.tail)).length ≤
      (frames.flatMap BinaryNatLists.frame).length := by
  simp only [List.length_flatMap, List.map_reverse, List.sum_reverse]
  induction frames with
  | nil => simp
  | cons bits frames ih =>
      simp only [List.map_cons, List.sum_cons, BinaryNatLists.frame_length,
        List.length_tail] at *
      omega

/-- Exact variable occurrences, including repeated literals and both signs of zero. -/
theorem literal_body_exits (literals : List (CNF.Literal Nat)) (output : List Bool) :
    routine.Exits
      (contents (literals.flatMap (fun l => BinaryNatLists.encodeNat l.toNat)) [] [] output)
      (runSteps (literals.map (fun l => encodeNat l.toNat)))
      (contents [] [] []
        (literals.reverse.flatMap (fun l => BinaryNatLists.encodeNat l.var) ++ output)) := by
  simpa only [List.flatMap_map, ← List.map_reverse, Function.comp_def,
    PackedLiteral.tail_encode_toNat, BinaryNatLists.encodeNat] using
    routine_exits (literals.map (fun l => encodeNat l.toNat)) output

/-- The complete variable-body output is bounded by the original literal-body bits. -/
theorem literal_output_length_le (literals : List (CNF.Literal Nat)) :
    (literals.reverse.flatMap (fun l => BinaryNatLists.encodeNat l.var)).length ≤
      (literals.flatMap (fun l => BinaryNatLists.encodeNat l.toNat)).length := by
  simpa only [List.flatMap_map, ← List.map_reverse, Function.comp_def,
    PackedLiteral.tail_encode_toNat, BinaryNatLists.encodeNat] using
    output_length_le (literals.map (fun l => encodeNat l.toNat))

def computer : FinTM2 := toMachine routine Stack.input Stack.output

/-- Canonical machine output with empty workspace, reset control and halt. -/
def outputsInTime (literals : List (CNF.Literal Nat)) :
    TM2OutputsInTime computer
      (literals.flatMap (fun l => BinaryNatLists.encodeNat l.toNat))
      (some (literals.reverse.flatMap (fun l => BinaryNatLists.encodeNat l.var)))
      (6 * (literals.flatMap (fun l => BinaryNatLists.encodeNat l.toNat)).length + 1) := by
  have run : TM2OutputsInTime computer
      (literals.flatMap (fun l => BinaryNatLists.encodeNat l.toNat))
      (some (literals.reverse.flatMap (fun l => BinaryNatLists.encodeNat l.var)))
      (runSteps (literals.map (fun l => encodeNat l.toNat))) := by
    apply toMachine_outputsInTime routine Stack.input Stack.output
    have hi : (initList computer
        (literals.flatMap (fun l => BinaryNatLists.encodeNat l.toNat))).stk =
        contents (literals.flatMap (fun l => BinaryNatLists.encodeNat l.toNat)) [] [] [] := by
      funext k; cases k <;> rfl
    have ho : (haltList computer
        (literals.reverse.flatMap (fun l => BinaryNatLists.encodeNat l.var))).stk =
        contents [] [] []
          (literals.reverse.flatMap (fun l => BinaryNatLists.encodeNat l.var)) := by
      funext k; cases k <;> rfl
    change routine.Exits (initList computer _).stk _ (haltList computer _).stk
    rw [hi, ho]
    simpa only [List.append_nil] using literal_body_exits literals []
  apply evalsToInTimeMono run
  simpa only [List.flatMap_map, Function.comp_def, BinaryNatLists.encodeNat] using
    runSteps_le (literals.map (fun l => encodeNat l.toNat))

end LeanNPHardness.MachinePrimitives.LiteralBody
