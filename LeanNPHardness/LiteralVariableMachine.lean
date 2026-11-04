import LeanNPHardness.FrameMoveMachine
import LeanNPHardness.PackedLiteralMachine
import LeanNPHardness.RawNatEncoding

/-!
# Extracting a framed variable from one packed literal

Read the unary payload length and discard its first bit only if the payload
is nonempty. Reframe the remaining bits with the checked frame-move routine.
The empty payload of positive zero must not consume any unread input.

The four-stack routine preserves arbitrary unread input and output suffixes,
and emits one variable frame per literal occurrence. Its exact cost is
`b + 3 * (b - 1) + 5` for packed payload length `b`, bounded by `2L + 3`
in the complete literal frame length `L`. Standalone packaging includes reset,
empty workspace and halt. Formula traversal and dictionary composition remain
separate obligations; the machine contract covers canonical encodings.
-/

namespace LeanNPHardness

open Computability Turing StateTransition Routines

namespace FramedLiteral

/-- A standalone literal uses exactly the frame occurring in the CNF encoding. -/
def finEncoding : FinEncoding (CNF.Literal Nat) where
  Γ := Bool
  encode literal := BinaryNatLists.encodeNat literal.toNat
  decode bits := (FramedNat.decode bits).map CNF.Literal.ofNat
  decode_encode literal := by simp
  ΓFin := Bool.fintype

end FramedLiteral

namespace MachinePrimitives.LiteralVariable

abbrev Stack := FrameMove.Stack
abbrev Alphabet := FrameMove.Alphabet
abbrev State := FrameMove.State
abbrev contents := FrameMove.contents

/-- `false` reads the prefix; `true` removes one payload bit if present. -/
def headerRoutine : Routine Alphabet where
  Λ := Bool
  σ := State
  entry := false
  init := none
  program
    | false => .pop .input (fun _ bit => bit) <|
        .branch (fun bit => bit.getD false)
          (.push .count (fun _ => true) (.goto fun _ => false))
          (.goto fun _ => true)
    | true => .pop .count (fun _ bit => bit) <|
        .branch Option.isSome (.pop .input (fun _ bit => bit) .halt) .halt

def cfg (label : Option Bool) (state : State) (input count work output : List Bool) :
    TM2.Cfg Alphabet Bool State :=
  ⟨label, state, contents input count work output⟩

private abbrev step := flip Option.bind (TM2.step headerRoutine.program)

private theorem prefix_false (state : State) (input count work output : List Bool) :
    step (some (cfg (some false) state (false :: input) count work output)) =
      some (cfg (some true) (some false) input count work output) := by
  simp [step, flip, headerRoutine, cfg, TM2.step, TM2.stepAux, contents,
    FrameMove.contents, Function.update]
  funext k; cases k <;> rfl

private theorem prefix_true (state : State) (input count work output : List Bool) :
    step (some (cfg (some false) state (true :: input) count work output)) =
      some (cfg (some false) (some true) input (true :: count) work output) := by
  simp [step, flip, headerRoutine, cfg, TM2.step, TM2.stepAux, contents,
    FrameMove.contents, Function.update]
  funext k; cases k <;> rfl

/-- Read the prefix without touching the payload or either suffix. -/
theorem prefix_run (n : Nat) (input count work output : List Bool) (state : State) :
    step^[n + 1]
      (some (cfg (some false) state
        (List.replicate n true ++ false :: input) count work output)) =
      some (cfg (some true) (some false) input
        (List.replicate n true ++ count) work output) := by
  induction n generalizing count state with
  | zero => simpa using prefix_false state input count work output
  | succ n ih =>
      rw [List.replicate_succ, List.cons_append, Function.iterate_succ_apply,
        prefix_true, ih]
      rw [← List.replicate_succ, List.replicate_succ',
        List.append_assoc, List.singleton_append]

/-- Discard the low bit only within the counted payload, including empty zero. -/
theorem header_exits (bits input work output : List Bool) :
    headerRoutine.Exits
      (contents (BinaryNatLists.frame bits ++ input) [] work output)
      (bits.length + 2)
      (contents (bits.tail ++ input) (List.replicate bits.tail.length true) work output) := by
  refine ⟨bits.head?, ?_⟩
  change step^[_] (some (cfg (some false) none _ [] work output)) = _
  rw [show bits.length + 2 = (bits.length + 1) + 1 by omega,
    Function.iterate_succ_apply']
  have hp := prefix_run bits.length (bits ++ input) [] work output none
  simp only [List.append_nil] at hp
  rw [show BinaryNatLists.frame bits ++ input =
      List.replicate bits.length true ++ false :: (bits ++ input) by
        simp [BinaryNatLists.frame, List.append_assoc], hp]
  cases bits with
  | nil =>
      simp [step, flip, headerRoutine, cfg, TM2.step, TM2.stepAux, contents,
        FrameMove.contents, Function.update]
  | cons bit bits =>
      simp [step, flip, headerRoutine, cfg, TM2.step, TM2.stepAux, contents,
        FrameMove.contents, Function.update]
      funext k; cases k <;> rfl

/-- The header adapter followed by the counted-payload re-framing routine. -/
def routine : Routine Alphabet := seq headerRoutine FrameMove.payloadRoutine

def runSteps (bits : List Bool) : Nat := bits.length + 3 * bits.tail.length + 5

/-- Consume one frame and emit its tail as one frame, retaining both suffixes. -/
theorem routine_exits (bits input output : List Bool) :
    routine.Exits (contents (BinaryNatLists.frame bits ++ input) [] [] output)
      (runSteps bits)
      (contents input [] [] (BinaryNatLists.frame bits.tail ++ output)) := by
  have h := seq_exits headerRoutine FrameMove.payloadRoutine
    (header_exits bits input [] output) (FrameMove.payload_exits bits.tail input output)
  rw [show runSteps bits = bits.length + 2 + (3 * bits.tail.length + 3) by
    unfold runSteps; omega]
  exact h

/-- All phases are linear in complete consumed frame bits, independent of suffixes. -/
theorem runSteps_le (bits : List Bool) :
    runSteps bits ≤ 2 * (BinaryNatLists.frame bits).length + 3 := by
  simp only [runSteps, BinaryNatLists.frame_length, List.length_tail]
  omega

/-- Exact packed-literal semantics, including both signs of zero. -/
theorem literal_exits (literal : CNF.Literal Nat) (input output : List Bool) :
    routine.Exits (contents (BinaryNatLists.encodeNat literal.toNat ++ input) [] [] output)
      (runSteps (encodeNat literal.toNat))
      (contents input [] [] (BinaryNatLists.encodeNat literal.var ++ output)) := by
  simpa only [BinaryNatLists.encodeNat, PackedLiteral.tail_encode_toNat] using
    routine_exits (encodeNat literal.toNat) input output

/-- Extracting the variable cannot enlarge the complete frame. -/
theorem output_length_le (literal : CNF.Literal Nat) :
    (BinaryNatLists.encodeNat literal.var).length ≤
      (BinaryNatLists.encodeNat literal.toNat).length := by
  change (BinaryNatLists.frame (encodeNat literal.var)).length ≤ _
  rw [← PackedLiteral.tail_encode_toNat literal]
  simp only [BinaryNatLists.encodeNat, BinaryNatLists.frame_length, List.length_tail]
  omega

def computer : FinTM2 := toMachine routine .input .output

/-- Canonical output, empty workspace, reset state and halt, all within the bound. -/
def outputsInTime (literal : CNF.Literal Nat) :
    TM2OutputsInTime computer (BinaryNatLists.encodeNat literal.toNat)
      (some (BinaryNatLists.encodeNat literal.var))
      (2 * (BinaryNatLists.encodeNat literal.toNat).length + 3) := by
  have run : TM2OutputsInTime computer (BinaryNatLists.encodeNat literal.toNat)
      (some (BinaryNatLists.encodeNat literal.var)) (runSteps (encodeNat literal.toNat)) := by
    apply toMachine_outputsInTime routine FrameMove.Stack.input FrameMove.Stack.output
    have hi : (initList computer (BinaryNatLists.encodeNat literal.toNat)).stk =
        contents (BinaryNatLists.encodeNat literal.toNat) [] [] [] := by
      funext k; cases k <;> rfl
    have ho : (haltList computer (BinaryNatLists.encodeNat literal.var)).stk =
        contents [] [] [] (BinaryNatLists.encodeNat literal.var) := by
      funext k; cases k <;> rfl
    change routine.Exits (initList computer _).stk _ (haltList computer _).stk
    rw [hi, ho]
    simpa only [List.append_nil] using literal_exits literal [] []
  exact evalsToInTimeMono run (runSteps_le (encodeNat literal.toNat))

/-- Literal variable extraction under the exact CNF literal frame, with `2X + 3`. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime FramedLiteral.finEncoding FramedNat.finEncoding
      (CNF.Literal.var : CNF.Literal Nat → Nat) where
  tm := computer
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 2 * Polynomial.X + 3
  outputsFun literal := by
    simpa [FramedLiteral.finEncoding, FramedNat.finEncoding, Equiv.refl,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X] using
      outputsInTime literal

end MachinePrimitives.LiteralVariable

end LeanNPHardness
