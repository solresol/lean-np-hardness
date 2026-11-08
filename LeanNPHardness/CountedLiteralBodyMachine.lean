import LeanNPHardness.LiteralBodyMachine
import LeanNPHardness.MachineRoutineExtension
import LeanNPHardness.MachineRoutineBound

/-!
# Count-controlled literal-body extraction with unread input

A fifth Boolean stack holds one mark per remaining literal. Each iteration
consumes one mark and one complete packed-literal frame. Unlike an exhaustion
loop on the input stack, this loop stops at the clause boundary even when more
formula input follows. It retains arbitrary input/output suffixes and emits
one variable frame per occurrence, in reverse occurrence order.

The exact cost includes every count pop and loop test, and is at most `7B + 1`
in the consumed body bit length `B`. The unary count is preloaded: reading its
binary header, restoring source order with retained input, and assembling a
full formula adapter are separate obligations. No standalone polynomial-time
encoding conversion is claimed here.
-/

namespace LeanNPHardness.MachinePrimitives.CountedLiteralBody

open Computability Turing Routines

abbrev ExtraAlphabet (_ : Unit) := Bool
abbrev Stack := FrameMove.Stack ⊕ Unit
abbrev Alphabet := ExtendedAlphabet (Γ := FrameMove.Alphabet) ExtraAlphabet

instance (k : Stack) : Fintype (Alphabet k) := by
  cases k with
  | inl k => exact inferInstanceAs (Fintype Bool)
  | inr k => exact inferInstanceAs (Fintype Bool)

abbrev remainingStack : Stack := .inr ()

def contents (input count work output remaining : List Bool) : Stacks Alphabet :=
  extendedStacks ExtraAlphabet (FrameMove.contents input count work output) (fun _ => remaining)

/-- Remove one outer mark, then extract one framed variable. -/
def body : Routine Alphabet :=
  seq (popOne remainingStack) (extend ExtraAlphabet LiteralVariable.routine)

/-- The outer count is independent of the literal's own payload-length stack. -/
theorem body_exits (bits input output remaining : List Bool) :
    body.Exits (contents (BinaryNatLists.frame bits ++ input) [] [] output (true :: remaining))
      (1 + LiteralVariable.runSteps bits)
      (contents input [] [] (BinaryNatLists.frame bits.tail ++ output) remaining) := by
  have hp : (popOne (Γ := Alphabet) remainingStack).Exits
      (contents (BinaryNatLists.frame bits ++ input) [] [] output (true :: remaining)) 1
      (contents (BinaryNatLists.frame bits ++ input) [] [] output remaining) := by
    convert popOne_exits (Γ := Alphabet) remainingStack
      (contents (BinaryNatLists.frame bits ++ input) [] [] output (true :: remaining)) using 1
    funext k
    cases k with
    | inl k => rfl
    | inr u => cases u; rfl
  exact seq_exits _ _ hp (extend_exits ExtraAlphabet LiteralVariable.routine (fun _ => remaining)
    (LiteralVariable.routine_exits bits input output))

/-- Test only the remaining count, never the unread input. -/
def routine : Routine Alphabet := loop remainingStack body

/-- Exact cost, charging the count pop as well as each loop test. -/
def runSteps (frames : List (List Bool)) : Nat :=
  loopSteps (fun i => 1 + LiteralVariable.runSteps (frames[i]?.getD [])) frames.length

@[simp] theorem runSteps_nil : runSteps [] = 1 := rfl

@[simp] theorem runSteps_cons (bits : List Bool) (frames : List (List Bool)) :
    runSteps (bits :: frames) = LiteralVariable.runSteps bits + 2 + runSteps frames := by
  simp only [runSteps, List.length_cons, loopSteps, List.getElem?_cons_zero,
    Option.getD_some, List.getElem?_cons_succ]
  omega

/-- Consume exactly the counted body, leaving arbitrary following bits untouched. -/
theorem routine_exits (frames : List (List Bool)) (input output : List Bool) :
    routine.Exits
      (contents (frames.flatMap BinaryNatLists.frame ++ input) [] [] output
        (List.replicate frames.length true))
      (runSteps frames)
      (contents input [] []
        (frames.reverse.flatMap (fun bits => BinaryNatLists.frame bits.tail) ++ output) []) := by
  let S : Nat → Stacks Alphabet := fun i =>
    contents ((frames.drop i).flatMap BinaryNatLists.frame ++ input) [] []
      ((frames.take i).reverse.flatMap (fun bits => BinaryNatLists.frame bits.tail) ++ output)
      (List.replicate (frames.length - i) true)
  have hbody : ∀ i < frames.length, body.Exits (S i)
      (1 + LiteralVariable.runSteps (frames[i]?.getD [])) (S (i + 1)) := by
    intro i hi
    have run := body_exits frames[i]
      ((frames.drop (i + 1)).flatMap BinaryNatLists.frame ++ input)
      ((frames.take i).reverse.flatMap (fun bits => BinaryNatLists.frame bits.tail) ++ output)
      (List.replicate (frames.length - (i + 1)) true)
    have hc : frames.length - i = (frames.length - (i + 1)) + 1 := by omega
    simpa only [S, List.drop_eq_getElem_cons hi, List.flatMap_cons,
      List.take_add_one, List.getElem?_eq_getElem hi, Option.getD_some,
      Option.toList_some, List.reverse_append, List.reverse_singleton,
      List.flatMap_append, List.flatMap_singleton, List.flatMap_nil,
      List.nil_append, List.append_assoc, hc, List.replicate_succ] using run
  have hne : ∀ i < frames.length, S i remainingStack ≠ [] := by
    intro i hi
    change List.replicate (frames.length - i) true ≠ []
    simp only [ne_eq, List.replicate_eq_nil_iff]
    omega
  have run := loop_exits remainingStack body frames.length S
    (fun i => 1 + LiteralVariable.runSteps (frames[i]?.getD [])) hbody hne
    (by simp [S, contents, remainingStack])
  simpa only [routine, runSteps, S, List.drop_zero, List.take_zero,
    List.reverse_nil, List.flatMap_nil, List.nil_append, List.drop_length,
    List.take_length, Nat.sub_zero, Nat.sub_self, List.replicate_zero] using run

/-- Compared with the isolated-body loop, exactly one count pop is added per frame. -/
theorem runSteps_eq (frames : List (List Bool)) :
    runSteps frames = LiteralBody.runSteps frames + frames.length := by
  induction frames with
  | nil => rfl
  | cons bits frames ih =>
      simp only [runSteps_cons, LiteralBody.runSteps_cons, List.length_cons, ih]
      omega

/-- All phases, including count pops and the final empty test, appear in this sum. -/
theorem runSteps_eq_sum (frames : List (List Bool)) :
    runSteps frames = (frames.map LiteralVariable.runSteps).sum + 2 * frames.length + 1 := by
  rw [runSteps_eq, LiteralBody.runSteps_eq_sum]
  omega

/-- Linear cost in consumed source bits and the number of occurrences. -/
theorem runSteps_le_size_count (frames : List (List Bool)) :
    runSteps frames ≤ 2 * (frames.flatMap BinaryNatLists.frame).length +
      5 * frames.length + 1 := by
  rw [runSteps_eq]
  have h := LiteralBody.runSteps_le_size_count frames
  omega

/-- Runtime is independent of the lengths of the retained input/output suffixes. -/
theorem runSteps_le (frames : List (List Bool)) :
    runSteps frames ≤ 7 * (frames.flatMap BinaryNatLists.frame).length + 1 := by
  have h : frames.length ≤ (frames.flatMap BinaryNatLists.frame).length := by
    induction frames with
    | nil => simp
    | cons bits frames ih =>
        simp only [List.length_cons, List.flatMap_cons, List.length_append,
          BinaryNatLists.frame_length]
        omega
  have bound := runSteps_le_size_count frames
  omega

/-- Exact variables of the counted clause, including repetitions and both signs of zero. -/
theorem literal_body_exits (literals : List (CNF.Literal Nat)) (input output : List Bool) :
    routine.Exits
      (contents (literals.flatMap (fun l => BinaryNatLists.encodeNat l.toNat) ++ input)
        [] [] output (List.replicate literals.length true))
      (runSteps (literals.map (fun l => encodeNat l.toNat)))
      (contents input [] []
        (literals.reverse.flatMap (fun l => BinaryNatLists.encodeNat l.var) ++ output) []) := by
  simpa only [List.flatMap_map, ← List.map_reverse, Function.comp_def,
    PackedLiteral.tail_encode_toNat, BinaryNatLists.encodeNat, List.length_map] using
    routine_exits (literals.map (fun l => encodeNat l.toNat)) input output

/-- The emitted frames cannot grow; the retained suffix is counted on both sides. -/
theorem literal_output_length_le (literals : List (CNF.Literal Nat)) (output : List Bool) :
    (literals.reverse.flatMap (fun l => BinaryNatLists.encodeNat l.var) ++ output).length ≤
      (literals.flatMap (fun l => BinaryNatLists.encodeNat l.toNat)).length + output.length := by
  rw [List.length_append]
  exact Nat.add_le_add_right (LiteralBody.literal_output_length_le literals) _

/-- A retained-suffix routine contract with the bound in consumed literal-body bits. -/
theorem literal_body_exitsLE (literals : List (CNF.Literal Nat)) (input output : List Bool) :
    routine.ExitsLE
      (contents (literals.flatMap (fun l => BinaryNatLists.encodeNat l.toNat) ++ input)
        [] [] output (List.replicate literals.length true))
      (7 * (literals.flatMap (fun l => BinaryNatLists.encodeNat l.toNat)).length + 1)
      (contents input [] []
        (literals.reverse.flatMap (fun l => BinaryNatLists.encodeNat l.var) ++ output) []) := by
  apply (literal_body_exits literals input output).le.mono
  simpa only [List.flatMap_map, Function.comp_def, BinaryNatLists.encodeNat] using
    runSteps_le (literals.map (fun l => encodeNat l.toNat))

end LeanNPHardness.MachinePrimitives.CountedLiteralBody
