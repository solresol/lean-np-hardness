import LeanNPHardness.BinaryArithmetic
import LeanNPHardness.RawNatEncoding
import LeanNPHardness.MachineRoutine

/-!
# Successor of one framed binary natural

A four-stack finite TM2 reads exactly one length-delimited payload, increments
it, and emits its new frame. The unread input and existing output suffixes
are preserved. Exact cost is `2b + 2b' + 4` for old/new payload lengths,
bounded by `2L + 4` in consumed frame length `L`. This supplies the count
update needed by framed-list construction, without assuming a raw count is
already loaded or charging time in the numerical value of that count.
-/

namespace LeanNPHardness.MachinePrimitives.FramedSucc

open Computability Turing StateTransition Routines

inductive Stack
  | input | count | work | output
  deriving DecidableEq, Fintype

inductive Label
  | prefix | carry | copy | restore | length
  deriving Fintype

abbrev Alphabet (_ : Stack) := Bool
abbrev State := Option Bool

private def held (s : State) : Bool := s.getD false

def contents (input count work output : List Bool) : Stacks Alphabet
  | .input => input
  | .count => count
  | .work => work
  | .output => output

/-- Count the frame prefix, increment exactly that many payload bits, then reframe. -/
def routine : Routine Alphabet where
  Λ := Label
  σ := State
  entry := .prefix
  init := none
  program
    | .prefix => .pop .input (fun _ s => s) <|
        .branch held
          (.push .count (fun _ => true) (.goto fun _ => .prefix))
          (.goto fun _ => .carry)
    | .carry => .pop .count (fun _ s => s) <|
        .branch Option.isSome
          (.pop .input (fun _ s => s) <|
            .branch held
              (.push .work (fun _ => false) (.goto fun _ => .carry))
              (.push .work (fun _ => true) (.goto fun _ => .copy)))
          (.push .work (fun _ => true) (.goto fun _ => .restore))
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
      some (cfg (some .carry) (some false) input count work output) := by
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

private theorem carry_nil (state : State) (input work output : List Bool) :
    step (some (cfg (some .carry) state input [] work output)) =
      some (cfg (some .restore) none input [] (true :: work) output) := by
  simp [step, flip, routine, cfg, TM2.step, TM2.stepAux, contents, held, Function.update]
  funext k; cases k <;> rfl

private theorem carry_false (state : State) (input count work output : List Bool) :
    step (some (cfg (some .carry) state (false :: input) (true :: count) work output)) =
      some (cfg (some .copy) (some false) input count (true :: work) output) := by
  simp [step, flip, routine, cfg, TM2.step, TM2.stepAux, contents, held, Function.update]
  funext k; cases k <;> rfl

private theorem carry_true (state : State) (input count work output : List Bool) :
    step (some (cfg (some .carry) state (true :: input) (true :: count) work output)) =
      some (cfg (some .carry) (some true) input count (false :: work) output) := by
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
      some (cfg (some .carry) (some false) input
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

/-- Propagate carry within the counted payload, adding a high bit on overflow. -/
theorem carry_run (bits input work output : List Bool) (state : State) :
    step^[bits.length + 1]
      (some (cfg (some .carry) state (bits ++ input)
        (List.replicate bits.length true) work output)) =
      some (cfg (some .restore) none input []
        ((binarySuccBits bits).reverse ++ work) output) := by
  induction bits generalizing work state with
  | nil => simpa [binarySuccBits] using carry_nil state input work output
  | cons a bits ih =>
      rw [List.length_cons, List.replicate_succ, List.cons_append,
        Function.iterate_succ_apply]
      cases a with
      | false =>
          rw [carry_false, copy_run]
          simp [binarySuccBits, List.reverse_cons, List.append_assoc]
      | true =>
          rw [carry_true, ih]
          simp [binarySuccBits, List.reverse_cons, List.append_assoc]

/-- Restore payload order, count the new length, and push the frame separator. -/
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

/-- Emit the new unary prefix and halt with reset state. -/
theorem length_run (input count work output : List Bool) (state : State) :
    step^[count.length + 1]
      (some (cfg (some .length) state input count work output)) =
      some (cfg none none input [] work (List.replicate count.length true ++ output)) := by
  induction count generalizing output state with
  | nil => simpa using length_nil state input work output
  | cons a count ih =>
      rw [List.length_cons, Function.iterate_succ_apply, length_cons, ih]
      simp [List.replicate_succ', List.append_assoc]

/-- Exact framed successor with arbitrary unread input and output suffixes. -/
theorem routine_exits (bits input output : List Bool) :
    routine.Exits (contents (BinaryNatLists.frame bits ++ input) [] [] output)
      (2 * bits.length + 2 * (binarySuccBits bits).length + 4)
      (contents input [] [] (BinaryNatLists.frame (binarySuccBits bits) ++ output)) := by
  refine ⟨none, ?_⟩
  change step^[_] (some (cfg (some .prefix) none _ [] [] output)) = _
  rw [show 2 * bits.length + 2 * (binarySuccBits bits).length + 4 =
      ((binarySuccBits bits).length + 1 + ((binarySuccBits bits).length + 1) +
        (bits.length + 1)) + (bits.length + 1) by omega,
    Function.iterate_add_apply]
  have hp := prefix_run bits.length (bits ++ input) [] [] output none
  simp only [List.append_nil] at hp
  rw [show BinaryNatLists.frame bits ++ input =
      List.replicate bits.length true ++ false :: (bits ++ input) by
        simp [BinaryNatLists.frame, List.append_assoc], hp,
    Function.iterate_add_apply, carry_run, List.append_nil,
    Function.iterate_add_apply]
  have hr := restore_run input [] (binarySuccBits bits).reverse output none
  simp only [List.length_reverse, List.reverse_reverse, List.append_nil] at hr
  rw [hr]
  have hl := length_run input (List.replicate (binarySuccBits bits).length true) []
    (false :: (binarySuccBits bits ++ output)) none
  simpa [BinaryNatLists.frame, List.append_assoc, cfg] using hl

/-- Runtime is linear in the consumed frame, independent of both suffixes. -/
theorem runSteps_le_frame_bound (bits : List Bool) :
    2 * bits.length + 2 * (binarySuccBits bits).length + 4 ≤
      2 * (BinaryNatLists.frame bits).length + 4 := by
  have h := binarySuccBits_length_le bits
  rw [BinaryNatLists.frame_length]
  omega

/-- Canonical natural-number semantics, including zero and carry overflow. -/
theorem natural_exits (n : Nat) (input output : List Bool) :
    routine.Exits (contents (BinaryNatLists.encodeNat n ++ input) [] [] output)
      (2 * (encodeNat n).length + 2 * (encodeNat (n + 1)).length + 4)
      (contents input [] [] (BinaryNatLists.encodeNat (n + 1) ++ output)) := by
  simpa only [BinaryNatLists.encodeNat, binarySuccBits_encodeNat] using
    routine_exits (encodeNat n) input output

/-- Increment a list header while retaining every entry frame and trailing bit.
The new header is emitted separately; inserting a new entry is a later routine. -/
theorem listCount_exits (xs : List Nat) (input output : List Bool) :
    routine.Exits (contents (BinaryNatLists.encodeNatList xs ++ input) [] [] output)
      (2 * (encodeNat xs.length).length + 2 * (encodeNat (xs.length + 1)).length + 4)
      (contents (xs.flatMap BinaryNatLists.encodeNat ++ input) [] []
        (BinaryNatLists.encodeNat (xs.length + 1) ++ output)) := by
  simpa only [BinaryNatLists.encodeNatList, List.append_assoc] using
    natural_exits xs.length (xs.flatMap BinaryNatLists.encodeNat ++ input) output

/-- Framing the increment adds at most two bits, even on carry overflow. -/
theorem frame_length_le (bits : List Bool) :
    (BinaryNatLists.frame (binarySuccBits bits)).length ≤
      (BinaryNatLists.frame bits).length + 2 := by
  have h := binarySuccBits_length_le bits
  simp only [BinaryNatLists.frame_length]
  omega

def computer : FinTM2 := toMachine routine .input .output

/-- Standalone framed output with empty workspace, reset state and halt. -/
def outputsInTime (bits : List Bool) :
    TM2OutputsInTime computer (BinaryNatLists.frame bits)
      (some (BinaryNatLists.frame (binarySuccBits bits)))
      (2 * (BinaryNatLists.frame bits).length + 4) := by
  have run : TM2OutputsInTime computer (BinaryNatLists.frame bits)
      (some (BinaryNatLists.frame (binarySuccBits bits)))
      (2 * bits.length + 2 * (binarySuccBits bits).length + 4) := by
    apply toMachine_outputsInTime routine Stack.input Stack.output
    have hi : (initList computer (BinaryNatLists.frame bits)).stk =
        contents (BinaryNatLists.frame bits) [] [] [] := by
      funext k; cases k <;> rfl
    have ho : (haltList computer (BinaryNatLists.frame (binarySuccBits bits))).stk =
        contents [] [] [] (BinaryNatLists.frame (binarySuccBits bits)) := by
      funext k; cases k <;> rfl
    change routine.Exits (initList computer _).stk _ (haltList computer _).stk
    rw [hi, ho]
    simpa only [List.append_nil] using routine_exits bits [] []
  exact evalsToInTimeMono run (runSteps_le_frame_bound bits)

/-- Successor under the self-delimiting natural encoding, with polynomial `2X + 4`. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime FramedNat.finEncoding FramedNat.finEncoding (fun n => n + 1) where
  tm := computer
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 2 * Polynomial.X + 4
  outputsFun n := by
    simpa [FramedNat.finEncoding, BinaryNatLists.encodeNat, Equiv.refl,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X] using
      outputsInTime (encodeNat n)

end LeanNPHardness.MachinePrimitives.FramedSucc
