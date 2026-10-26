import LeanNPHardness.BinaryNatLists
import LeanNPHardness.MachineRoutine

/-!
# Moving frames without changing their payloads

A four-stack finite TM2 moves one complete frame above an arbitrary output
suffix, retaining the unread input. Both workspace stacks finish empty. This
is the body of a frame-order reversal pass for tail-first dictionary traversal.
-/

namespace LeanNPHardness.MachinePrimitives.FrameMove

open Computability Turing StateTransition Routines

inductive Stack
  | input | count | work | output
  deriving DecidableEq, Fintype

inductive Label
  | prefix | copy | restore | length
  deriving Fintype

abbrev Alphabet (_ : Stack) := Bool
abbrev State := Option Bool

private def held (s : State) : Bool := s.getD false

def contents (input count work output : List Bool) : Stacks Alphabet
  | .input => input
  | .count => count
  | .work => work
  | .output => output

/-- Read the length, move exactly that payload, restore its order, and reframe. -/
def routine : Routine Alphabet where
  Λ := Label
  σ := State
  entry := .prefix
  init := none
  program
    | .prefix => .pop .input (fun _ s => s) <|
        .branch held
          (.push .count (fun _ => true) (.goto fun _ => .prefix))
          (.goto fun _ => .copy)
    | .copy => .pop .count (fun _ s => s) <|
        .branch Option.isSome
          (.pop .input (fun _ s => s) <|
            .push .work held (.goto fun _ => .copy))
          (.goto fun _ => .restore)
    | .restore => .pop .work (fun _ s => s) <|
        .branch Option.isSome
          (.push .output held (.push .count (fun _ => true) (.goto fun _ => .restore)))
          (.push .output (fun _ => false) (.goto fun _ => .length))
    | .length => .pop .count (fun _ s => s) <|
        .branch Option.isSome
          (.push .output (fun _ => true) (.goto fun _ => .length)) .halt

def cfg (label : Option Label) (state : State) (input count work output : List Bool) :
    TM2.Cfg Alphabet Label State :=
  ⟨label, state, contents input count work output⟩

private abbrev step := flip Option.bind (TM2.step routine.program)

private theorem prefix_false (state : State) (input count work output : List Bool) :
    step (some (cfg (some .prefix) state (false :: input) count work output)) =
      some (cfg (some .copy) (some false) input count work output) := by
  simp [step, flip, routine, cfg, TM2.step, TM2.stepAux, contents, held, Function.update]
  funext k; cases k <;> rfl

private theorem prefix_true (state : State) (input count work output : List Bool) :
    step (some (cfg (some .prefix) state (true :: input) count work output)) =
      some (cfg (some .prefix) (some true) input (true :: count) work output) := by
  simp [step, flip, routine, cfg, TM2.step, TM2.stepAux, contents, held, Function.update]
  funext k; cases k <;> rfl

private theorem copy_nil (state : State) (input work output : List Bool) :
    step (some (cfg (some .copy) state input [] work output)) =
      some (cfg (some .restore) none input [] work output) := by
  simp [step, flip, routine, cfg, TM2.step, TM2.stepAux, contents, held, Function.update]

private theorem copy_cons (a : Bool) (state : State) (input count work output : List Bool) :
    step (some (cfg (some .copy) state (a :: input) (true :: count) work output)) =
      some (cfg (some .copy) (some a) input count (a :: work) output) := by
  simp [step, flip, routine, cfg, TM2.step, TM2.stepAux, contents, held, Function.update]
  funext k; cases k <;> rfl

private theorem restore_nil (state : State) (input count output : List Bool) :
    step (some (cfg (some .restore) state input count [] output)) =
      some (cfg (some .length) none input count [] (false :: output)) := by
  simp [step, flip, routine, cfg, TM2.step, TM2.stepAux, contents, held, Function.update]
  funext k; cases k <;> rfl

private theorem restore_cons (a : Bool) (state : State) (input count work output : List Bool) :
    step (some (cfg (some .restore) state input count (a :: work) output)) =
      some (cfg (some .restore) (some a) input (true :: count) work (a :: output)) := by
  simp [step, flip, routine, cfg, TM2.step, TM2.stepAux, contents, held, Function.update]
  funext k; cases k <;> rfl

private theorem length_nil (state : State) (input work output : List Bool) :
    step (some (cfg (some .length) state input [] work output)) =
      some (cfg none none input [] work output) := by
  simp [step, flip, routine, cfg, TM2.step, TM2.stepAux, contents, Function.update]

private theorem length_cons (a : Bool) (state : State) (input count work output : List Bool) :
    step (some (cfg (some .length) state input (a :: count) work output)) =
      some (cfg (some .length) (some a) input count work (true :: output)) := by
  simp [step, flip, routine, cfg, TM2.step, TM2.stepAux, contents, Function.update]
  funext k; cases k <;> rfl

/-- Read the unary payload length without touching the payload or its suffix. -/
theorem prefix_run (n : Nat) (input count work output : List Bool) (state : State) :
    step^[n + 1]
      (some (cfg (some .prefix) state
        (List.replicate n true ++ false :: input) count work output)) =
      some (cfg (some .copy) (some false) input
        (List.replicate n true ++ count) work output) := by
  induction n generalizing count state with
  | zero => simpa using prefix_false state input count work output
  | succ n ih =>
      rw [List.replicate_succ, List.cons_append, Function.iterate_succ_apply,
        prefix_true, ih]
      rw [← List.replicate_succ, List.replicate_succ',
        List.append_assoc, List.singleton_append]

/-- Copy exactly the remaining payload, keeping the unread suffix intact. -/
theorem copy_run (bits input work output : List Bool) (state : State) :
    step^[bits.length + 1]
      (some (cfg (some .copy) state (bits ++ input)
        (List.replicate bits.length true) work output)) =
      some (cfg (some .restore) none input [] (bits.reverse ++ work) output) := by
  induction bits generalizing work state with
  | nil => simpa using copy_nil state input work output
  | cons a bits ih =>
      rw [List.length_cons, List.replicate_succ, List.cons_append,
        Function.iterate_succ_apply, copy_cons, ih]
      simp [List.reverse_cons, List.append_assoc]

/-- Restore payload order, count the length, and push the frame separator. -/
theorem restore_run (input count work output : List Bool) (state : State) :
    step^[work.length + 1]
      (some (cfg (some .restore) state input count work output)) =
      some (cfg (some .length) none input
        (List.replicate work.length true ++ count) [] (false :: (work.reverse ++ output))) := by
  induction work generalizing count output state with
  | nil => simpa using restore_nil state input count output
  | cons a work ih =>
      rw [List.length_cons, Function.iterate_succ_apply, restore_cons, ih]
      simp [List.reverse_cons, List.replicate_succ', List.append_assoc]

/-- Emit the unary prefix and halt with reset state. -/
theorem length_run (input count work output : List Bool) (state : State) :
    step^[count.length + 1]
      (some (cfg (some .length) state input count work output)) =
      some (cfg none none input [] work (List.replicate count.length true ++ output)) := by
  induction count generalizing output state with
  | nil => simpa using length_nil state input work output
  | cons a count ih =>
      rw [List.length_cons, Function.iterate_succ_apply, length_cons, ih]
      simp [List.replicate_succ', List.append_assoc]

/-- Exact frame transfer, preserving both suffixes and every payload bit. -/
theorem routine_exits (bits input output : List Bool) :
    routine.Exits (contents (BinaryNatLists.frame bits ++ input) [] [] output)
      (4 * bits.length + 4)
      (contents input [] [] (BinaryNatLists.frame bits ++ output)) := by
  refine ⟨none, ?_⟩
  change step^[_] (some (cfg (some .prefix) none _ [] [] output)) = _
  rw [show 4 * bits.length + 4 =
      (bits.length + 1 + (bits.length + 1) +
        (bits.length + 1)) + (bits.length + 1) by omega,
    Function.iterate_add_apply]
  have hp := prefix_run bits.length (bits ++ input) [] [] output none
  simp only [List.append_nil] at hp
  rw [show BinaryNatLists.frame bits ++ input =
      List.replicate bits.length true ++ false :: (bits ++ input) by
        simp [BinaryNatLists.frame, List.append_assoc], hp,
    Function.iterate_add_apply, copy_run, List.append_nil,
    Function.iterate_add_apply]
  have hr := restore_run input [] bits.reverse output none
  simp only [List.length_reverse, List.reverse_reverse, List.append_nil] at hr
  rw [hr]
  have hl := length_run input (List.replicate bits.length true) []
    (false :: (bits ++ output)) none
  simpa [BinaryNatLists.frame, List.append_assoc, cfg] using hl

/-- The exact cost is linear in the complete frame, including its prefix. -/
theorem runSteps_eq_frame_length (bits : List Bool) :
    4 * bits.length + 4 =
      2 * (BinaryNatLists.frame bits).length + 2 := by
  rw [BinaryNatLists.frame_length]
  omega

/-- Transfer one natural without changing its encoding or the unread body. -/
theorem natural_exits (n : Nat) (input output : List Bool) :
    routine.Exits (contents (BinaryNatLists.encodeNat n ++ input) [] [] output)
      (2 * (BinaryNatLists.encodeNat n).length + 2)
      (contents input [] [] (BinaryNatLists.encodeNat n ++ output)) := by
  simpa only [runSteps_eq_frame_length, BinaryNatLists.encodeNat] using
    routine_exits (encodeNat n) input output

end LeanNPHardness.MachinePrimitives.FrameMove
