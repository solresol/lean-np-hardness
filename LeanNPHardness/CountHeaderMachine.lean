import LeanNPHardness.CountedLiteralBodyMachine
import LeanNPHardness.SatVerifyMachine

/-!
# Loading a framed binary count on Boolean stacks

Read exactly one frame, reverse its payload, and use Horner's scheme to
produce a unary count for `CountedLiteralBody`. Both suffixes survive and
the two scratch stacks finish empty. The bound depends on the decoded
numeric count as well as the header length; no polynomial bound in the
header length alone is claimed.
-/

namespace LeanNPHardness.MachinePrimitives.CountHeader

open Computability Turing Routines

/-! The first phase uses the existing four-stack frame layout. -/

def readBits : Routine FrameMove.Alphabet where
  Λ := Bool
  σ := Option Bool
  entry := false
  init := none
  program
    | false => .pop .input (fun _ bit => bit) <|
        .branch (fun bit => bit.getD false)
          (.push .count (fun _ => true) (.goto fun _ => false))
          (.goto fun _ => true)
    | true => .pop .count (fun _ bit => bit) <|
        .branch Option.isSome
          (.pop .input (fun _ bit => bit) <|
            .push .work (fun bit => bit.getD false) (.goto fun _ => true)) .halt

private def cfg (label : Option Bool) (state : Option Bool)
    (input count work output : List Bool) :
    TM2.Cfg FrameMove.Alphabet Bool (Option Bool) :=
  ⟨label, state, FrameMove.contents input count work output⟩

private abbrev step := flip Option.bind (TM2.step readBits.program)

private theorem prefix_false (state : Option Bool) (input count work output : List Bool) :
    step (some (cfg (some false) state (false :: input) count work output)) =
      some (cfg (some true) (some false) input count work output) := by
  simp [step, flip, readBits, cfg, TM2.step, TM2.stepAux, FrameMove.contents, Function.update]
  funext k; cases k <;> rfl

private theorem prefix_true (state : Option Bool) (input count work output : List Bool) :
    step (some (cfg (some false) state (true :: input) count work output)) =
      some (cfg (some false) (some true) input (true :: count) work output) := by
  simp [step, flip, readBits, cfg, TM2.step, TM2.stepAux, FrameMove.contents, Function.update]
  funext k; cases k <;> rfl

private theorem prefix_run (n : Nat) (input count work output : List Bool)
    (state : Option Bool) :
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

private theorem copy_nil (state : Option Bool) (input work output : List Bool) :
    step (some (cfg (some true) state input [] work output)) =
      some (cfg none none input [] work output) := by
  simp [step, flip, readBits, cfg, TM2.step, TM2.stepAux, FrameMove.contents, Function.update]

private theorem copy_cons (a : Bool) (state : Option Bool)
    (input count work output : List Bool) :
    step (some (cfg (some true) state (a :: input) (true :: count) work output)) =
      some (cfg (some true) (some a) input count (a :: work) output) := by
  simp [step, flip, readBits, cfg, TM2.step, TM2.stepAux, FrameMove.contents, Function.update]
  funext k; cases k <;> rfl

private theorem copy_run (bits input work output : List Bool) (state : Option Bool) :
    step^[bits.length + 1]
      (some (cfg (some true) state (bits ++ input)
        (List.replicate bits.length true) work output)) =
      some (cfg none none input [] (bits.reverse ++ work) output) := by
  induction bits generalizing work state with
  | nil => simpa using copy_nil state input work output
  | cons a bits ih =>
      rw [List.length_cons, List.replicate_succ, List.cons_append,
        Function.iterate_succ_apply, copy_cons, ih]
      simp [List.reverse_cons, List.append_assoc]

/-- Load the payload most-significant bit first, retaining all following input. -/
theorem readBits_exits (bits input work output : List Bool) :
    readBits.Exits
      (FrameMove.contents (BinaryNatLists.frame bits ++ input) [] work output)
      (2 * bits.length + 2)
      (FrameMove.contents input [] (bits.reverse ++ work) output) := by
  refine ⟨none, ?_⟩
  change step^[_] (some (cfg (some false) none _ [] work output)) = _
  rw [show 2 * bits.length + 2 = (bits.length + 1) + (bits.length + 1) by omega,
    Function.iterate_add_apply]
  have hp := prefix_run bits.length (bits ++ input) [] work output none
  simp only [List.append_nil] at hp
  rw [show BinaryNatLists.frame bits ++ input =
      List.replicate bits.length true ++ false :: (bits ++ input) by
        simp [BinaryNatLists.frame, List.append_assoc], hp, copy_run]
  rfl

abbrev Stack := CountedLiteralBody.Stack
abbrev Alphabet := CountedLiteralBody.Alphabet
abbrev contents := CountedLiteralBody.contents
abbrev remaining : Stack := CountedLiteralBody.remainingStack
abbrev scratch : Stack := .inl .count
abbrev bitsStack : Stack := .inl .work
abbrev marks (n : Nat) : List Bool := List.replicate n true

instance (k : Stack) : DecidableEq (Alphabet k) := by
  cases k with
  | inl k => exact inferInstanceAs (DecidableEq Bool)
  | inr k => exact inferInstanceAs (DecidableEq Bool)

/-- Double the accumulator using the empty payload-length stack as scratch. -/
def double : Routine Alphabet :=
  seq (moveAll remaining scratch id true)
    (loop scratch (seq (popOne scratch) (pushList remaining [true, true])))

theorem doubleLoop_exits (a : Nat) : ∀ (S : Stacks Alphabet) (c : Nat),
    S scratch = marks a → S remaining = marks c →
    (loop scratch (seq (popOne scratch) (pushList remaining [true, true]))).ExitsLE
      S (3 * a + 1)
      (Function.update (Function.update S scratch []) remaining (marks (c + 2 * a))) := by
  induction a with
  | zero =>
      intro S c hu hl
      refine (loop_exitsLE_nil _ _ S (by simp [hu]) 0).congr ?_
      funext k; cases k <;> rename_i k <;> cases k <;> simp [scratch, remaining, hu, hl]
  | succ a ih =>
      intro S c hu hl
      have hb := seq_exitsLE _ _ (popOne_exitsLE (Γ := Alphabet) scratch S 0)
        (pushList_exitsLE (Γ := Alphabet) remaining [true, true] _ 0)
      have h2 := ih (Function.update (Function.update S scratch (S scratch).tail) remaining
          (([true, true] : List (Alphabet remaining)) ++
            (Function.update S scratch (S scratch).tail) remaining)) (c + 2)
        (by simp [scratch, remaining, hu, marks, List.replicate_succ])
        (by simp [scratch, remaining, hl, marks, List.replicate_succ])
      refine ((loop_exitsLE_cons _ _ (by simp [hu, marks, List.replicate_succ]) hb h2).mono
        (by omega)).congr ?_
      funext k; cases k <;> rename_i k <;> cases k <;>
        simp [scratch, remaining]
      omega

theorem double_exits (a : Nat) (S : Stacks Alphabet)
    (hl : S remaining = marks a) (hu : S scratch = []) :
    double.ExitsLE S (5 * a + 2) (Function.update S remaining (marks (2 * a))) := by
  have run := seq_exitsLE _ _
    (moveAll_exits (Γ := Alphabet) remaining scratch (by decide) id true S).le
    (doubleLoop_exits a _ 0 (by simp [scratch, remaining, hl, hu, marks]) (by simp))
  refine (run.mono (by simp [hl, marks]; omega)).congr ?_
  funext k; cases k <;> rename_i k <;> cases k <;> simp [scratch, remaining, hu]

def horn (bit : Bool) : Routine Alphabet :=
  if bit then seq double (pushList remaining [true]) else double

/-- Decode an arbitrary most-significant-first word, charging every unary transfer. -/
theorem hornLoop_exits (ms : List Bool) : ∀ (S : Stacks Alphabet) (acc : Nat),
    S bitsStack = ms → S remaining = marks acc → S scratch = [] →
    (loop bitsStack (dispatch bitsStack horn)).ExitsLE S
      (ms.length * (5 * SatVerify.hornerB acc ms + 6) + 1)
      (Function.update (Function.update S bitsStack []) remaining
        (marks (SatVerify.hornerB acc ms))) := by
  induction ms with
  | nil =>
      intro S acc ht hl hu
      refine ((loop_exitsLE_nil (Γ := Alphabet) bitsStack (dispatch bitsStack horn) S
        (by simp [ht]) 0).mono (by simp)).congr ?_
      funext k; cases k <;> rename_i k <;> cases k <;>
        simp [bitsStack, remaining, ht, hl, SatVerify.hornerB]
  | cons b ms ih =>
      intro S acc ht hl hu
      have hacc := SatVerify.le_hornerB ms (2 * acc + (if b then 1 else 0))
      have hstep : (horn b).ExitsLE (Function.update S bitsStack ms) (5 * acc + 3)
          (Function.update (Function.update S bitsStack ms) remaining
            (marks (2 * acc + (if b then 1 else 0)))) := by
        cases b
        · exact ((double_exits acc _ (by simp [bitsStack, remaining, hl])
            (by simp [bitsStack, scratch, hu])).mono (by omega)).congr
            (by funext k; cases k <;> rename_i k <;> cases k <;> simp)
        · refine ((seq_exitsLE _ _
            (double_exits acc _ (by simp [bitsStack, remaining, hl])
              (by simp [bitsStack, scratch, hu]))
            (pushList_exitsLE (Γ := Alphabet) remaining [true] _ 0)).mono (by omega)).congr ?_
          funext k; cases k <;> rename_i k <;> cases k <;>
            simp [remaining, marks, List.replicate_succ]
      have h2 := ih (Function.update (Function.update S bitsStack ms) remaining
          (marks (2 * acc + (if b then 1 else 0)))) (2 * acc + (if b then 1 else 0))
        (by simp [bitsStack, remaining]) (by simp) (by simp [bitsStack, remaining, scratch, hu])
      refine ((loop_exitsLE_cons _ _ (by simp [ht])
        (dispatch_exitsLE (Γ := Alphabet) bitsStack horn S b ms ht hstep) h2).mono ?_).congr ?_
      · simp only [SatVerify.hornerB, List.length_cons, Nat.add_mul, Nat.one_mul]
        have : acc ≤ SatVerify.hornerB (2 * acc + (if b then 1 else 0)) ms :=
          le_trans (by split <;> omega) hacc
        omega
      · funext k; cases k <;> rename_i k <;> cases k <;> simp [SatVerify.hornerB]

/-- Read the complete binary frame and leave its value on the outer-count stack. -/
def routine : Routine Alphabet :=
  seq (extend CountedLiteralBody.ExtraAlphabet readBits)
    (loop bitsStack (dispatch bitsStack horn))

/-- Load a canonical count without consuming any body or output suffix bits. -/
theorem natural_exits (n : Nat) (input output : List Bool) :
    routine.ExitsLE (contents (BinaryNatLists.encodeNat n ++ input) [] [] output [])
      ((encodeNat n).length * (5 * n + 8) + 3)
      (contents input [] [] output (marks n)) := by
  have load := extend_exits CountedLiteralBody.ExtraAlphabet readBits (fun _ => [])
    (readBits_exits (encodeNat n) input [] output)
  simp only [List.append_nil] at load
  have decode := hornLoop_exits (encodeNat n).reverse
    (contents input [] (encodeNat n).reverse output []) 0 rfl rfl rfl
  rw [SatVerify.hornerB_reverse, SatVerify.hval_encodeNat, List.length_reverse] at decode
  have run := seq_exitsLE _ _ load.le decode
  refine (run.mono (by nlinarith)).congr ?_
  funext k; cases k <;> rename_i k <;> cases k <;>
    simp [bitsStack, remaining, contents, CountedLiteralBody.contents,
      extendedStacks, FrameMove.contents]

end LeanNPHardness.MachinePrimitives.CountHeader
