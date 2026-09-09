import LeanNPHardness.RawNatEncoding
import LeanNPHardness.MachineRun

/-!
Reusable encoding and machine components extracted from `phd-thesis-lean`
commit `84be78db5a287f9a40dcb549252063d6db67de73`. Runtime bounds retain
the original explicit finite-alphabet input encodings.
-/

namespace LeanNPHardness.MachinePrimitives

open Computability Turing
open LeanNPHardness.MachineComposition

/-- Four Boolean stacks suffice to preserve the payload while prefixing its
length: input, reversed payload, unary counter, and output. -/
inductive FrameStack
  | input
  | scratch
  | count
  | output
  deriving DecidableEq, Fintype

/-- The three traversal phases of the framing program. -/
inductive FrameLabel
  | stash
  | restore
  | prefix
  deriving DecidableEq, Fintype

/-- The local state holds the bit most recently popped from a stack. -/
abbrev FrameState := Option Bool

private def poppedBit (_ : FrameState) (bit : Option Bool) : FrameState :=
  bit

def heldBit : FrameState → Bool
  | some bit => bit
  | none => false

/-- The finite framing program.  `stash` reverses the payload and records its
unary length, `restore` restores the payload on the output stack and adds the
separator, and `prefix` moves the unary length in front of it. -/
def frameProgram :
    FrameLabel → TM2.Stmt (fun _ : FrameStack => Bool) FrameLabel FrameState
  | .stash =>
      .pop .input poppedBit <|
        .branch Option.isSome
          (.push .scratch heldBit <|
            .push .count (fun _ => true) <|
              .goto (fun _ => .stash))
          (.goto (fun _ => .restore))
  | .restore =>
      .pop .scratch poppedBit <|
        .branch Option.isSome
          (.push .output heldBit <|
            .goto (fun _ => .restore))
          (.push .output (fun _ => false) <|
            .goto (fun _ => .prefix))
  | .prefix =>
      .pop .count poppedBit <|
        .branch Option.isSome
          (.push .output (fun _ => true) <|
            .goto (fun _ => .prefix))
          .halt

/-- The concrete finite machine implementing `BinaryNatLists.frame`. -/
def frameComputer : FinTM2 where
  K := FrameStack
  k₀ := .input
  k₁ := .output
  Γ _ := Bool
  Λ := FrameLabel
  main := .stash
  σ := FrameState
  initialState := none
  Γk₀Fin := Bool.fintype
  m := frameProgram

private def stackContents
    (input scratch count output : List Bool) :
    FrameStack → List Bool
  | .input => input
  | .scratch => scratch
  | .count => count
  | .output => output

def cfg (label : Option FrameLabel) (state : FrameState)
    (input scratch count output : List Bool) : frameComputer.Cfg where
  l := label
  var := state
  stk := stackContents input scratch count output

private theorem step_stash_cons (bit : Bool) (input scratch count output : List Bool)
    (state : FrameState) :
    frameComputer.step
        (cfg (some .stash) state (bit :: input) scratch count output) =
      some (cfg (some .stash) (some bit) input (bit :: scratch)
        (true :: count) output) := by
  simp [frameComputer, FinTM2.step, cfg, frameProgram, stackContents,
    poppedBit, heldBit, Function.update]
  funext index
  cases index <;> rfl

private theorem step_stash_nil (scratch count output : List Bool)
    (state : FrameState) :
    frameComputer.step (cfg (some .stash) state [] scratch count output) =
      some (cfg (some .restore) none [] scratch count output) := by
  simp [frameComputer, FinTM2.step, cfg, frameProgram, stackContents,
    poppedBit, Function.update]

private theorem step_restore_cons (bit : Bool) (scratch count output : List Bool)
    (state : FrameState) :
    frameComputer.step
        (cfg (some .restore) state [] (bit :: scratch) count output) =
      some (cfg (some .restore) (some bit) [] scratch count (bit :: output)) := by
  simp [frameComputer, FinTM2.step, cfg, frameProgram, stackContents,
    poppedBit, heldBit, Function.update]
  funext index
  cases index <;> rfl

private theorem step_restore_nil (count output : List Bool)
    (state : FrameState) :
    frameComputer.step (cfg (some .restore) state [] [] count output) =
      some (cfg (some .prefix) none [] [] count (false :: output)) := by
  simp [frameComputer, FinTM2.step, cfg, frameProgram, stackContents,
    poppedBit, Function.update]
  funext index
  cases index <;> rfl

private theorem step_prefix_cons (tick : Bool) (count output : List Bool)
    (state : FrameState) :
    frameComputer.step
        (cfg (some .prefix) state [] [] (tick :: count) output) =
      some (cfg (some .prefix) (some tick) [] [] count (true :: output)) := by
  simp [frameComputer, FinTM2.step, cfg, frameProgram, stackContents,
    poppedBit, Function.update]
  funext index
  cases index <;> rfl

private theorem step_prefix_nil (output : List Bool) (state : FrameState) :
    frameComputer.step (cfg (some .prefix) state [] [] [] output) =
      some (cfg none none [] [] [] output) := by
  simp [frameComputer, FinTM2.step, cfg, frameProgram, stackContents,
    poppedBit, Function.update]

private def evalsToInTimeOne
    {start finish : frameComputer.Cfg}
    (hstep : frameComputer.step start = some finish) :
    EvalsToInTime frameComputer.step start (some finish) 1 where
  steps := 1
  evals_in_steps := by
    simpa [Function.iterate_one] using hstep
  steps_le_m := Nat.le_refl 1


private def stash_evals
    (input scratch count output : List Bool) (state : FrameState) :
    EvalsToInTime frameComputer.step
      (cfg (some .stash) state input scratch count output)
      (some (cfg (some .restore) none [] (input.reverse ++ scratch)
        (List.replicate input.length true ++ count) output))
      (input.length + 1) := by
  induction input generalizing scratch count state with
  | nil =>
      simpa using evalsToInTimeOne (step_stash_nil scratch count output state)
  | cons bit input ih =>
      let middle := cfg (some .stash) (some bit) input (bit :: scratch)
        (true :: count) output
      have hone : EvalsToInTime frameComputer.step
          (cfg (some .stash) state (bit :: input) scratch count output)
          (some middle) 1 :=
        evalsToInTimeOne (step_stash_cons bit input scratch count output state)
      have hrest := ih (bit :: scratch) (true :: count) (some bit)
      have htrans := EvalsToInTime.trans frameComputer.step 1
        (input.length + 1)
        (cfg (some .stash) state (bit :: input) scratch count output)
        middle
        (some (cfg (some .restore) none []
          ((bit :: input).reverse ++ scratch)
          (List.replicate (bit :: input).length true ++ count) output))
        hone
        (by
          simpa [middle, List.reverse_cons, List.replicate_succ,
            List.append_assoc, replicate_true_append_cons] using hrest)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htrans

private def restore_evals
    (scratch count output : List Bool) (state : FrameState) :
    EvalsToInTime frameComputer.step
      (cfg (some .restore) state [] scratch count output)
      (some (cfg (some .prefix) none [] [] count
        (false :: (scratch.reverse ++ output))))
      (scratch.length + 1) := by
  induction scratch generalizing output state with
  | nil =>
      simpa using evalsToInTimeOne (step_restore_nil count output state)
  | cons bit scratch ih =>
      let middle := cfg (some .restore) (some bit) [] scratch count
        (bit :: output)
      have hone : EvalsToInTime frameComputer.step
          (cfg (some .restore) state [] (bit :: scratch) count output)
          (some middle) 1 :=
        evalsToInTimeOne
          (step_restore_cons bit scratch count output state)
      have hrest := ih (bit :: output) (some bit)
      have htrans := EvalsToInTime.trans frameComputer.step 1
        (scratch.length + 1)
        (cfg (some .restore) state [] (bit :: scratch) count output)
        middle
        (some (cfg (some .prefix) none [] [] count
          (false :: ((bit :: scratch).reverse ++ output))))
        hone
        (by
          simpa [middle, List.reverse_cons, List.append_assoc] using hrest)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htrans

private def prefix_evals
    (count output : List Bool) (state : FrameState) :
    EvalsToInTime frameComputer.step
      (cfg (some .prefix) state [] [] count output)
      (some (cfg none none [] [] []
        (List.replicate count.length true ++ output)))
      (count.length + 1) := by
  induction count generalizing output state with
  | nil =>
      simpa using evalsToInTimeOne (step_prefix_nil output state)
  | cons tick count ih =>
      let middle := cfg (some .prefix) (some tick) [] [] count
        (true :: output)
      have hone : EvalsToInTime frameComputer.step
          (cfg (some .prefix) state [] [] (tick :: count) output)
          (some middle) 1 :=
        evalsToInTimeOne (step_prefix_cons tick count output state)
      have hrest := ih (true :: output) (some tick)
      have htrans := EvalsToInTime.trans frameComputer.step 1
        (count.length + 1)
        (cfg (some .prefix) state [] [] (tick :: count) output)
        middle
        (some (cfg none none [] [] []
          (List.replicate (tick :: count).length true ++ output)))
        hone
        (by
          simpa [middle, List.replicate_succ, List.append_assoc,
            replicate_true_append_cons] using hrest)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htrans

private theorem initList_eq_cfg (bits : List Bool) :
    initList frameComputer bits = cfg (some .stash) none bits [] [] [] := by
  unfold initList cfg
  congr
  funext index
  cases index <;> rfl

private theorem haltList_eq_cfg (bits : List Bool) :
    haltList frameComputer bits = cfg none none [] [] [] bits := by
  unfold haltList cfg
  congr
  funext index
  cases index <;> rfl

/-- The framing machine emits the self-delimiting payload in exactly
`3 * bits.length + 3` machine steps. -/
def frame_outputsInTime (bits : List Bool) :
    TM2OutputsInTime frameComputer bits
      (some (BinaryNatLists.frame bits)) (3 * bits.length + 3) := by
  have hstash := stash_evals bits [] [] [] none
  have hrestore := restore_evals bits.reverse
    (List.replicate bits.length true) [] none
  have hprefix := prefix_evals (List.replicate bits.length true)
    (false :: bits) none
  have hfirst := EvalsToInTime.trans frameComputer.step
    (bits.length + 1) (bits.length + 1)
    (cfg (some .stash) none bits [] [] [])
    (cfg (some .restore) none [] bits.reverse
      (List.replicate bits.length true) [])
    (some (cfg (some .prefix) none [] []
      (List.replicate bits.length true) (false :: bits)))
    (by simpa using hstash)
    (by simpa using hrestore)
  have hall := EvalsToInTime.trans frameComputer.step
    ((bits.length + 1) + (bits.length + 1))
    (bits.length + 1)
    (cfg (some .stash) none bits [] [] [])
    (cfg (some .prefix) none [] []
      (List.replicate bits.length true) (false :: bits))
    (some (cfg none none [] [] [] (BinaryNatLists.frame bits)))
    hfirst
    (by simpa [BinaryNatLists.frame] using hprefix)
  rw [TM2OutputsInTime, initList_eq_cfg]
  simp only [Option.map_some]
  rw [haltList_eq_cfg]
  have htime :
      bits.length + 1 + (bits.length + 1 + (bits.length + 1)) =
        3 * bits.length + 3 := by
    omega
  simpa only [htime] using hall

/-- A genuine polynomial-time machine witness for changing the encoding of a
natural from mathlib's raw binary representation to the self-delimiting
framed representation used by the CSP wire format.  The computed mathematical
function is the identity; the machine performs the nontrivial encoding pass. -/
noncomputable def framedNatComputableInPolyTime :
    @TM2ComputableInPolyTime ℕ ℕ Computability.finEncodingNatBool
      FramedNat.finEncoding id where
  tm := frameComputer
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := 3 * Polynomial.X + 3
  outputsFun n := by
    simpa [Computability.finEncodingNatBool,
      Computability.encodingNatBool, FramedNat.finEncoding,
      BinaryNatLists.encodeNat, Equiv.refl,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_natCast,
      Polynomial.eval_X] using
        frame_outputsInTime (Computability.encodeNat n)

/-- Three stacks suffice for the list serializer: the raw field stream, a
unary counter for the current field, and the framed output. -/
inductive ListFrameStack
  | input
  | count
  | output
  deriving DecidableEq, Fintype

/-- The serializer alternates between scanning a field, prefixing its length,
and checking whether another field remains. -/
inductive ListFrameLabel
  | scan
  | prefix
  | next
  deriving DecidableEq, Fintype

/-- The finite control remembers the last raw symbol and the last unary-count
symbol popped from their heterogeneous stacks. -/
structure ListFrameState where
  raw : Option (Option Bool)
  tick : Option Bool
  deriving DecidableEq, Fintype

private def listFrameInitialState : ListFrameState :=
  ⟨none, none⟩

private def listPoppedRaw
    (state : ListFrameState) (symbol : Option (Option Bool)) :
    ListFrameState :=
  { state with raw := symbol }

private def listPoppedTick
    (state : ListFrameState) (tick : Option Bool) : ListFrameState :=
  { state with tick := tick }

private def listRawIsBit : ListFrameState → Bool
  | ⟨some (some _), _⟩ => true
  | _ => false

private def listRawPresent : ListFrameState → Bool
  | ⟨some _, _⟩ => true
  | _ => false

private def listHeldBit : ListFrameState → Bool
  | ⟨some (some bit), _⟩ => bit
  | _ => false

private def listTickPresent : ListFrameState → Bool
  | ⟨_, some _⟩ => true
  | _ => false

private def ListFrameAlphabet : ListFrameStack → Type
  | .input => Option Bool
  | .count => Bool
  | .output => Bool

/-- The finite list-framing program. Scanning reversed payload bits prepends
each payload in forward order. The delimiter adds `false`; the counter then
adds the unary length prefix. Since fields arrive in reverse order, the final
output has the canonical list order. -/
def listFrameProgram :
    ListFrameLabel →
      TM2.Stmt ListFrameAlphabet ListFrameLabel ListFrameState
  | .scan =>
      .pop .input listPoppedRaw <|
        .branch listRawIsBit
          (.push .output listHeldBit <|
            .push .count (fun _ => true) <|
              .goto (fun _ => .scan))
          (.push .output (fun _ => false) <|
            .goto (fun _ => .prefix))
  | .prefix =>
      .pop .count listPoppedTick <|
        .branch listTickPresent
          (.push .output (fun _ => true) <|
            .goto (fun _ => .prefix))
          (.goto (fun _ => .next))
  | .next =>
      .peek .input listPoppedRaw <|
        .branch listRawPresent
          (.goto (fun _ => .scan))
          .halt

/-- The concrete finite machine serializing stack-oriented natural lists. -/
def listFrameComputer : FinTM2 where
  K := ListFrameStack
  k₀ := .input
  k₁ := .output
  Γ := ListFrameAlphabet
  Λ := ListFrameLabel
  main := .scan
  σ := ListFrameState
  initialState := listFrameInitialState
  Γk₀Fin := by
    change Fintype (Option Bool)
    infer_instance
  m := listFrameProgram

private def listStackContents
    (input : List (Option Bool)) (count output : List Bool) :
    (index : ListFrameStack) → List (ListFrameAlphabet index)
  | .input => input
  | .count => count
  | .output => output

private def listCfg (label : Option ListFrameLabel)
    (state : ListFrameState) (input : List (Option Bool))
    (count output : List Bool) : listFrameComputer.Cfg where
  l := label
  var := state
  stk := listStackContents input count output

private theorem list_step_scan_bit (bit : Bool)
    (input : List (Option Bool)) (count output : List Bool)
    (state : ListFrameState) :
    listFrameComputer.step
        (listCfg (some .scan) state (some bit :: input) count output) =
      some (listCfg (some .scan)
        (listPoppedRaw state (some (some bit))) input
        (true :: count) (bit :: output)) := by
  simp [listFrameComputer, FinTM2.step, listCfg, listFrameProgram,
    listStackContents, ListFrameAlphabet, listPoppedRaw, listRawIsBit,
    listHeldBit, Function.update]
  funext index
  cases index <;> rfl

private theorem list_step_scan_delimiter
    (input : List (Option Bool)) (count output : List Bool)
    (state : ListFrameState) :
    listFrameComputer.step
        (listCfg (some .scan) state (none :: input) count output) =
      some (listCfg (some .prefix)
        (listPoppedRaw state (some none)) input count (false :: output)) := by
  simp [listFrameComputer, FinTM2.step, listCfg, listFrameProgram,
    listStackContents, ListFrameAlphabet, listPoppedRaw, listRawIsBit,
    Function.update]
  funext index
  cases index <;> rfl

private theorem list_step_prefix_cons (tick : Bool)
    (input : List (Option Bool)) (count output : List Bool)
    (state : ListFrameState) :
    listFrameComputer.step
        (listCfg (some .prefix) state input (tick :: count) output) =
      some (listCfg (some .prefix)
        (listPoppedTick state (some tick)) input count (true :: output)) := by
  simp [listFrameComputer, FinTM2.step, listCfg, listFrameProgram,
    listStackContents, ListFrameAlphabet, listPoppedTick,
    listTickPresent, Function.update]
  funext index
  cases index <;> rfl

private theorem list_step_prefix_nil (input : List (Option Bool))
    (output : List Bool) (state : ListFrameState) :
    listFrameComputer.step
        (listCfg (some .prefix) state input [] output) =
      some (listCfg (some .next) (listPoppedTick state none)
        input [] output) := by
  simp [listFrameComputer, FinTM2.step, listCfg, listFrameProgram,
    listStackContents, ListFrameAlphabet, listPoppedTick,
    listTickPresent, Function.update]

private theorem list_step_next_cons (symbol : Option Bool)
    (input : List (Option Bool)) (output : List Bool)
    (state : ListFrameState) :
    listFrameComputer.step
        (listCfg (some .next) state (symbol :: input) [] output) =
      some (listCfg (some .scan)
        (listPoppedRaw state (some symbol)) (symbol :: input) [] output) := by
  simp [listFrameComputer, FinTM2.step, listCfg, listFrameProgram,
    listStackContents, ListFrameAlphabet, listPoppedRaw, listRawPresent]

private theorem list_step_next_nil (output : List Bool)
    (raw : Option (Option Bool)) :
    listFrameComputer.step
        (listCfg (some .next) ⟨raw, none⟩ [] [] output) =
      some (listCfg none listFrameInitialState [] [] output) := by
  simp [listFrameComputer, FinTM2.step, listCfg, listFrameProgram,
    listStackContents, ListFrameAlphabet, listPoppedRaw, listRawPresent,
    listFrameInitialState]

private def listEvalsToInTimeOne
    {start finish : listFrameComputer.Cfg}
    (hstep : listFrameComputer.step start = some finish) :
    EvalsToInTime listFrameComputer.step start (some finish) 1 where
  steps := 1
  evals_in_steps := by
    simpa [Function.iterate_one] using hstep
  steps_le_m := Nat.le_refl 1

private def list_scanSegment_evals
    (reversedBits : List Bool) (input : List (Option Bool))
    (count output : List Bool) (state : ListFrameState) :
    EvalsToInTime listFrameComputer.step
      (listCfg (some .scan) state
        (reversedBits.map some ++ none :: input) count output)
      (some (listCfg (some .prefix)
        (listPoppedRaw state (some none)) input
        (List.replicate reversedBits.length true ++ count)
        (false :: (reversedBits.reverse ++ output))))
      (reversedBits.length + 1) := by
  induction reversedBits generalizing count output state with
  | nil =>
      simpa using listEvalsToInTimeOne
        (list_step_scan_delimiter input count output state)
  | cons bit reversedBits ih =>
      let middle := listCfg (some .scan)
        (listPoppedRaw state (some (some bit)))
        (reversedBits.map some ++ none :: input)
        (true :: count) (bit :: output)
      have hone : EvalsToInTime listFrameComputer.step
          (listCfg (some .scan) state
            ((bit :: reversedBits).map some ++ none :: input) count output)
          (some middle) 1 :=
        listEvalsToInTimeOne (by
          simpa [middle] using
            list_step_scan_bit bit
              (reversedBits.map some ++ none :: input) count output state)
      have hrest := ih (true :: count) (bit :: output)
        (listPoppedRaw state (some (some bit)))
      have htrans := EvalsToInTime.trans listFrameComputer.step
        1 (reversedBits.length + 1)
        (listCfg (some .scan) state
          ((bit :: reversedBits).map some ++ none :: input) count output)
        middle
        (some (listCfg (some .prefix)
          (listPoppedRaw state (some none)) input
          (List.replicate (bit :: reversedBits).length true ++ count)
          (false :: ((bit :: reversedBits).reverse ++ output))))
        hone
        (by
          simpa [middle, listPoppedRaw, List.reverse_cons,
            List.append_assoc, replicate_true_append_cons] using hrest)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htrans

private def list_prefix_evals
    (count : List Bool) (input : List (Option Bool))
    (output : List Bool) (state : ListFrameState) :
    EvalsToInTime listFrameComputer.step
      (listCfg (some .prefix) state input count output)
      (some (listCfg (some .next) (listPoppedTick state none)
        input [] (List.replicate count.length true ++ output)))
      (count.length + 1) := by
  induction count generalizing output state with
  | nil =>
      simpa using listEvalsToInTimeOne
        (list_step_prefix_nil input output state)
  | cons tick count ih =>
      let middle := listCfg (some .prefix)
        (listPoppedTick state (some tick)) input count (true :: output)
      have hone : EvalsToInTime listFrameComputer.step
          (listCfg (some .prefix) state input (tick :: count) output)
          (some middle) 1 :=
        listEvalsToInTimeOne
          (list_step_prefix_cons tick input count output state)
      have hrest := ih (true :: output) (listPoppedTick state (some tick))
      have htrans := EvalsToInTime.trans listFrameComputer.step
        1 (count.length + 1)
        (listCfg (some .prefix) state input (tick :: count) output)
        middle
        (some (listCfg (some .next) (listPoppedTick state none)
          input [] (List.replicate (tick :: count).length true ++ output)))
        hone
        (by
          simpa [middle, listPoppedTick, List.append_assoc,
            replicate_true_append_cons] using hrest)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htrans

private def list_next_present_evals
    (input : List (Option Bool)) (hinput : input ≠ [])
    (output : List Bool) (state : ListFrameState) :
    EvalsToInTime listFrameComputer.step
      (listCfg (some .next) state input [] output)
      (some (listCfg (some .scan)
        (listPoppedRaw state input.head?) input [] output)) 1 := by
  cases input with
  | nil => exact (hinput rfl).elim
  | cons symbol input =>
      simpa using listEvalsToInTimeOne
        (list_step_next_cons symbol input output state)

private theorem segment_nonempty (bits : List Bool) :
    RawNatList.segment bits ≠ [] := by
  simp [RawNatList.segment]

private theorem segments_flatMap_nonempty
    (bits : List Bool) (segments : List (List Bool)) :
    (bits :: segments).flatMap RawNatList.segment ≠ [] := by
  simp [RawNatList.segment]

private def list_segments_evals
    (segments : List (List Bool)) (hsegments : segments ≠ [])
    (output : List Bool) (state : ListFrameState) :
    EvalsToInTime listFrameComputer.step
      (listCfg (some .scan) state
        (segments.flatMap RawNatList.segment) [] output)
      (some (listCfg none listFrameInitialState [] []
        (segments.reverse.flatMap BinaryNatLists.frame ++ output)))
      (2 * (segments.flatMap RawNatList.segment).length + segments.length) := by
  induction segments generalizing output state with
  | nil => exact (hsegments rfl).elim
  | cons bits segments ih =>
      let tailInput := segments.flatMap RawNatList.segment
      have hscan := list_scanSegment_evals bits.reverse tailInput [] output state
      have hprefix := list_prefix_evals
        (List.replicate bits.length true) tailInput
        (false :: (bits ++ output))
        (listPoppedRaw state (some none))
      have hfirst := EvalsToInTime.trans listFrameComputer.step
        (bits.length + 1) (bits.length + 1)
        (listCfg (some .scan) state
          ((bits :: segments).flatMap RawNatList.segment) [] output)
        (listCfg (some .prefix) (listPoppedRaw state (some none))
          tailInput (List.replicate bits.length true)
          (false :: (bits ++ output)))
        (some (listCfg (some .next)
          (listPoppedTick (listPoppedRaw state (some none)) none)
          tailInput [] (BinaryNatLists.frame bits ++ output)))
        (by simpa [tailInput, RawNatList.segment] using hscan)
        (by
          simpa [BinaryNatLists.frame, listPoppedTick,
            List.append_assoc] using hprefix)
      cases segments with
      | nil =>
          have hnext := listEvalsToInTimeOne
            (list_step_next_nil (BinaryNatLists.frame bits ++ output)
              (listPoppedRaw state (some none)).raw)
          have hall := EvalsToInTime.trans listFrameComputer.step
            ((bits.length + 1) + (bits.length + 1)) 1
            (listCfg (some .scan) state
              ([bits].flatMap RawNatList.segment) [] output)
            (listCfg (some .next)
              (listPoppedTick (listPoppedRaw state (some none)) none)
              [] [] (BinaryNatLists.frame bits ++ output))
            (some (listCfg none listFrameInitialState [] []
              (BinaryNatLists.frame bits ++ output)))
            (by simpa [tailInput] using hfirst)
            (by simpa [listPoppedTick, listPoppedRaw] using hnext)
          refine evalsToInTimeMono (by
            simpa [RawNatList.segment] using hall) ?_
          change
            1 + ((bits.length + 1) + (bits.length + 1)) ≤
              2 * ([bits].flatMap RawNatList.segment).length + [bits].length
          simp [RawNatList.segment]
          omega
      | cons next segments =>
          let rest := next :: segments
          have htail :
              (rest.flatMap RawNatList.segment) ≠ [] :=
            segments_flatMap_nonempty next segments
          have hnext := list_next_present_evals
            (rest.flatMap RawNatList.segment) htail
            (BinaryNatLists.frame bits ++ output)
            (listPoppedTick (listPoppedRaw state (some none)) none)
          have hthroughNext := EvalsToInTime.trans listFrameComputer.step
            ((bits.length + 1) + (bits.length + 1)) 1
            (listCfg (some .scan) state
              ((bits :: rest).flatMap RawNatList.segment) [] output)
            (listCfg (some .next)
              (listPoppedTick (listPoppedRaw state (some none)) none)
              (rest.flatMap RawNatList.segment) []
              (BinaryNatLists.frame bits ++ output))
            (some (listCfg (some .scan)
              (listPoppedRaw
                (listPoppedTick (listPoppedRaw state (some none)) none)
                (rest.flatMap RawNatList.segment).head?)
              (rest.flatMap RawNatList.segment) []
              (BinaryNatLists.frame bits ++ output)))
            (by simpa [tailInput, rest] using hfirst)
            hnext
          have hrest := ih (by simp)
            (BinaryNatLists.frame bits ++ output)
            (listPoppedRaw
              (listPoppedTick (listPoppedRaw state (some none)) none)
              (rest.flatMap RawNatList.segment).head?)
          have hall := EvalsToInTime.trans listFrameComputer.step
            (1 + ((bits.length + 1) + (bits.length + 1)))
            (2 * (rest.flatMap RawNatList.segment).length + rest.length)
            (listCfg (some .scan) state
              ((bits :: rest).flatMap RawNatList.segment) [] output)
            (listCfg (some .scan)
              (listPoppedRaw
                (listPoppedTick (listPoppedRaw state (some none)) none)
                (rest.flatMap RawNatList.segment).head?)
              (rest.flatMap RawNatList.segment) []
              (BinaryNatLists.frame bits ++ output))
            (some (listCfg none listFrameInitialState [] []
              ((bits :: rest).reverse.flatMap BinaryNatLists.frame ++ output)))
            hthroughNext
            (by
              simpa [rest, List.reverse_cons, List.append_assoc] using hrest)
          refine evalsToInTimeMono (by
            simpa [rest, RawNatList.segment, List.reverse_cons,
              List.append_assoc] using hall) ?_
          simp [RawNatList.segment]
          omega

private theorem segments_length_le_raw_length
    (segments : List (List Bool)) :
    segments.length ≤ (segments.flatMap RawNatList.segment).length := by
  induction segments with
  | nil => simp
  | cons bits segments ih =>
      simp only [List.length_cons, List.flatMap_cons, List.length_append]
      have hpositive : 0 < (RawNatList.segment bits).length := by
        simp [RawNatList.segment]
      omega

private theorem payloads_frame_eq_encodeNatList (xs : List ℕ) :
    (RawNatList.payloads xs).flatMap BinaryNatLists.frame =
      BinaryNatLists.encodeNatList xs := by
  rw [RawNatList.payloads, List.flatMap_cons,
    BinaryNatLists.encodeNatList]
  change
    BinaryNatLists.frame (Computability.encodeNat xs.length) ++
        (xs.map Computability.encodeNat).flatMap BinaryNatLists.frame =
      BinaryNatLists.frame (Computability.encodeNat xs.length) ++
        xs.flatMap
          (fun n => BinaryNatLists.frame (Computability.encodeNat n))
  rw [List.flatMap_map]

private theorem list_initList_eq_cfg (input : List (Option Bool)) :
    initList listFrameComputer input =
      listCfg (some .scan) listFrameInitialState input [] [] := by
  unfold initList listCfg
  congr
  funext index
  cases index <;> rfl

private theorem list_haltList_eq_cfg (output : List Bool) :
    haltList listFrameComputer output =
      listCfg none listFrameInitialState [] [] output := by
  unfold haltList listCfg
  congr
  funext index
  cases index <;> rfl

/-- The list serializer traverses every raw field and emits the exact canonical
length-prefixed framed list in at most three times the raw input length. -/
def listFrame_outputsInTime (xs : List ℕ) :
    TM2OutputsInTime listFrameComputer (RawNatList.encode xs)
      (some (BinaryNatLists.encodeNatList xs))
      (3 * (RawNatList.encode xs).length) := by
  have hpayloads : RawNatList.payloads xs ≠ [] := by
    simp [RawNatList.payloads]
  have hpayloadsReverse : (RawNatList.payloads xs).reverse ≠ [] := by
    intro hreverse
    apply hpayloads
    have := congrArg List.reverse hreverse
    simpa using this
  have hsegments := list_segments_evals
    (RawNatList.payloads xs).reverse
    hpayloadsReverse [] listFrameInitialState
  have hlength :=
    segments_length_le_raw_length (RawNatList.payloads xs).reverse
  have hbound :
      2 * (RawNatList.encode xs).length +
          (RawNatList.payloads xs).reverse.length ≤
        3 * (RawNatList.encode xs).length := by
    change (RawNatList.payloads xs).reverse.length ≤
      (RawNatList.encode xs).length at hlength
    omega
  have hmono := evalsToInTimeMono hsegments (by
    simpa [RawNatList.encode] using hbound)
  rw [TM2OutputsInTime, list_initList_eq_cfg]
  simp only [Option.map_some]
  rw [list_haltList_eq_cfg]
  simpa [RawNatList.encode, payloads_frame_eq_encodeNatList] using hmono

/-- The same finite serializer frames every field of a raw nested-list
stream.  Its proof is representation-generic: the outer length, every inner
length, and every value are simply raw natural fields to `listFrameComputer`.
-/
def nestedListFrame_outputsInTime (xss : List (List ℕ)) :
    TM2OutputsInTime listFrameComputer (RawNatLists.encode xss)
      (some (BinaryNatLists.encode xss))
      (3 * (RawNatLists.encode xss).length) := by
  have hpayloads : RawNatLists.payloads xss ≠ [] := by
    simp [RawNatLists.payloads]
  have hpayloadsReverse : (RawNatLists.payloads xss).reverse ≠ [] := by
    intro hreverse
    apply hpayloads
    have := congrArg List.reverse hreverse
    simpa using this
  have hsegments := list_segments_evals
    (RawNatLists.payloads xss).reverse
    hpayloadsReverse [] listFrameInitialState
  have hlength :=
    segments_length_le_raw_length (RawNatLists.payloads xss).reverse
  have hbound :
      2 * (RawNatLists.encode xss).length +
          (RawNatLists.payloads xss).reverse.length ≤
        3 * (RawNatLists.encode xss).length := by
    change (RawNatLists.payloads xss).reverse.length ≤
      (RawNatLists.encode xss).length at hlength
    omega
  have hmono := evalsToInTimeMono hsegments (by
    simpa [RawNatLists.encode] using hbound)
  rw [TM2OutputsInTime, list_initList_eq_cfg]
  simp only [Option.map_some]
  rw [list_haltList_eq_cfg]
  simpa [RawNatLists.encode, RawNatLists.payloads_frame_eq_encode] using hmono
/-- A genuine linear-time finite-machine witness converting the natural
stack-stream representation into the exact framed list encoding used by the
runtime CSP compiler. -/
noncomputable def framedNatListComputableInPolyTime :
    @TM2ComputableInPolyTime (List ℕ) (List ℕ) RawNatList.finEncoding
      FramedNatList.finEncoding id where
  tm := listFrameComputer
  inputAlphabet := Equiv.refl (Option Bool)
  outputAlphabet := Equiv.refl Bool
  time := 3 * Polynomial.X
  outputsFun xs := by
    simpa [RawNatList.finEncoding, FramedNatList.finEncoding, Equiv.refl,
      Polynomial.eval_mul, Polynomial.eval_natCast, Polynomial.eval_X] using
        listFrame_outputsInTime xs

/-- Three heterogeneous stacks suffice to expose a framed input stream as
raw delimited fields: the canonical Boolean input, a unary field counter, and
the stack-oriented raw output. -/
inductive UnframeStack
  | input
  | count
  | output
  deriving DecidableEq, Fintype

/-- The input traversal scans a unary prefix, copies the counted payload, and
then checks whether another framed field remains. -/
inductive UnframeLabel
  | scan
  | payload
  | next
  deriving DecidableEq, Fintype

/-- Finite control remembers the latest input bit and unary counter symbol. -/
structure UnframeState where
  inputBit : Option Bool
  tick : Option Bool
  deriving DecidableEq, Fintype

private def unframeInitialState : UnframeState :=
  ⟨none, none⟩

private def unframePoppedInput
    (state : UnframeState) (bit : Option Bool) : UnframeState :=
  { state with inputBit := bit }

private def unframePoppedTick
    (state : UnframeState) (tick : Option Bool) : UnframeState :=
  { state with tick := tick }

private def unframeInputTrue : UnframeState → Bool
  | ⟨some true, _⟩ => true
  | _ => false

private def unframeInputPresent : UnframeState → Bool
  | ⟨some _, _⟩ => true
  | _ => false

private def unframeTickPresent : UnframeState → Bool
  | ⟨_, some _⟩ => true
  | _ => false

private def unframeHeldInput : UnframeState → Option Bool
  | ⟨some bit, _⟩ => some bit
  | _ => none

private def UnframeAlphabet : UnframeStack → Type
  | .input => Bool
  | .count => Bool
  | .output => Option Bool

/-- The finite unframing program. It consumes the unary length prefix, puts a
field delimiter on the output, and copies the counted payload. Stack pushes
reverse both the payload bits and the sequence of fields, producing exactly
the raw representation used by later compiler passes. -/
def unframeProgram :
    UnframeLabel → TM2.Stmt UnframeAlphabet UnframeLabel UnframeState
  | .scan =>
      .pop .input unframePoppedInput <|
        .branch unframeInputTrue
          (.push .count (fun _ => true) <|
            .goto (fun _ => .scan))
          (.push .output (fun _ => none) <|
            .goto (fun _ => .payload))
  | .payload =>
      .pop .count unframePoppedTick <|
        .branch unframeTickPresent
          (.pop .input unframePoppedInput <|
            .push .output unframeHeldInput <|
              .goto (fun _ => .payload))
          (.goto (fun _ => .next))
  | .next =>
      .peek .input unframePoppedInput <|
        .branch unframeInputPresent
          (.goto (fun _ => .scan))
          .halt

/-- Concrete finite machine converting canonical framed fields into the raw
stack stream used by subsequent passes. -/
def unframeComputer : FinTM2 where
  K := UnframeStack
  k₀ := .input
  k₁ := .output
  Γ := UnframeAlphabet
  Λ := UnframeLabel
  main := .scan
  σ := UnframeState
  initialState := unframeInitialState
  Γk₀Fin := Bool.fintype
  m := unframeProgram

private def unframeStackContents
    (input count : List Bool) (output : List (Option Bool)) :
    (index : UnframeStack) → List (UnframeAlphabet index)
  | .input => input
  | .count => count
  | .output => output

private def unframeCfg (label : Option UnframeLabel)
    (state : UnframeState) (input count : List Bool)
    (output : List (Option Bool)) : unframeComputer.Cfg where
  l := label
  var := state
  stk := unframeStackContents input count output

private theorem unframe_step_scan_true (input count : List Bool)
    (output : List (Option Bool)) (state : UnframeState) :
    unframeComputer.step
        (unframeCfg (some .scan) state (true :: input) count output) =
      some (unframeCfg (some .scan)
        (unframePoppedInput state (some true)) input
        (true :: count) output) := by
  simp [unframeComputer, FinTM2.step, unframeCfg, unframeProgram,
    unframeStackContents, UnframeAlphabet, unframePoppedInput,
    unframeInputTrue, Function.update]
  funext index
  cases index <;> rfl

private theorem unframe_step_scan_false (input count : List Bool)
    (output : List (Option Bool)) (state : UnframeState) :
    unframeComputer.step
        (unframeCfg (some .scan) state (false :: input) count output) =
      some (unframeCfg (some .payload)
        (unframePoppedInput state (some false)) input count
        (none :: output)) := by
  simp [unframeComputer, FinTM2.step, unframeCfg, unframeProgram,
    unframeStackContents, UnframeAlphabet, unframePoppedInput,
    unframeInputTrue, Function.update]
  funext index
  cases index <;> rfl

private theorem unframe_step_payload_cons (bit tick : Bool)
    (input count : List Bool) (output : List (Option Bool))
    (state : UnframeState) :
    unframeComputer.step
        (unframeCfg (some .payload) state (bit :: input)
          (tick :: count) output) =
      some (unframeCfg (some .payload)
        (unframePoppedInput (unframePoppedTick state (some tick))
          (some bit))
        input count (some bit :: output)) := by
  simp [unframeComputer, FinTM2.step, unframeCfg, unframeProgram,
    unframeStackContents, UnframeAlphabet, unframePoppedInput,
    unframePoppedTick, unframeTickPresent, unframeHeldInput,
    Function.update]
  funext index
  cases index <;> rfl

private theorem unframe_step_payload_nil (input : List Bool)
    (output : List (Option Bool)) (state : UnframeState) :
    unframeComputer.step
        (unframeCfg (some .payload) state input [] output) =
      some (unframeCfg (some .next)
        (unframePoppedTick state none) input [] output) := by
  simp [unframeComputer, FinTM2.step, unframeCfg, unframeProgram,
    unframeStackContents, UnframeAlphabet, unframePoppedTick,
    unframeTickPresent, Function.update]

private theorem unframe_step_next_cons (bit : Bool)
    (input : List Bool) (output : List (Option Bool))
    (state : UnframeState) :
    unframeComputer.step
        (unframeCfg (some .next) state (bit :: input) [] output) =
      some (unframeCfg (some .scan)
        (unframePoppedInput state (some bit))
        (bit :: input) [] output) := by
  simp [unframeComputer, FinTM2.step, unframeCfg, unframeProgram,
    unframeStackContents, UnframeAlphabet, unframePoppedInput,
    unframeInputPresent]

private theorem unframe_step_next_nil (output : List (Option Bool))
    (inputBit : Option Bool) :
    unframeComputer.step
        (unframeCfg (some .next) ⟨inputBit, none⟩ [] [] output) =
      some (unframeCfg none unframeInitialState [] [] output) := by
  simp [unframeComputer, FinTM2.step, unframeCfg, unframeProgram,
    unframeStackContents, UnframeAlphabet, unframePoppedInput,
    unframeInputPresent, unframeInitialState]

private def unframeEvalsToInTimeOne
    {start finish : unframeComputer.Cfg}
    (hstep : unframeComputer.step start = some finish) :
    EvalsToInTime unframeComputer.step start (some finish) 1 where
  steps := 1
  evals_in_steps := by
    simpa [Function.iterate_one] using hstep
  steps_le_m := Nat.le_refl 1

private def unframe_scan_evals (prefixLength : ℕ) (input count : List Bool)
    (output : List (Option Bool)) (state : UnframeState) :
    EvalsToInTime unframeComputer.step
      (unframeCfg (some .scan) state
        (List.replicate prefixLength true ++ false :: input)
        count output)
      (some (unframeCfg (some .payload)
        (unframePoppedInput state (some false)) input
        (List.replicate prefixLength true ++ count) (none :: output)))
      (prefixLength + 1) := by
  induction prefixLength generalizing count state with
  | zero =>
      simpa using unframeEvalsToInTimeOne
        (unframe_step_scan_false input count output state)
  | succ prefixLength ih =>
      let middle := unframeCfg (some .scan)
        (unframePoppedInput state (some true))
        (List.replicate prefixLength true ++ false :: input)
        (true :: count) output
      have hone : EvalsToInTime unframeComputer.step
          (unframeCfg (some .scan) state
            (List.replicate (prefixLength + 1) true ++ false :: input)
            count output)
          (some middle) 1 :=
        unframeEvalsToInTimeOne (by
          simpa [middle, List.replicate_succ] using
            unframe_step_scan_true
              (List.replicate prefixLength true ++ false :: input)
              count output state)
      have hrest := ih (true :: count)
        (unframePoppedInput state (some true))
      have htrans := EvalsToInTime.trans unframeComputer.step
        1 (prefixLength + 1)
        (unframeCfg (some .scan) state
          (List.replicate (prefixLength + 1) true ++ false :: input)
          count output)
        middle
        (some (unframeCfg (some .payload)
          (unframePoppedInput state (some false)) input
          (List.replicate (prefixLength + 1) true ++ count)
          (none :: output)))
        hone
        (by
          simpa [middle, unframePoppedInput, List.replicate_succ,
            replicate_true_append_cons] using hrest)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htrans

/-- State after copying a payload. Only the last copied bit is retained, and
the exhausted unary counter is recorded as absent. -/
private def unframePayloadState (inputBit : Option Bool) :
    List Bool → UnframeState
  | [] => ⟨inputBit, none⟩
  | bit :: bits => unframePayloadState (some bit) bits

@[simp]
private theorem unframePayloadState_tick
    (inputBit : Option Bool) (bits : List Bool) :
    (unframePayloadState inputBit bits).tick = none := by
  induction bits generalizing inputBit with
  | nil => rfl
  | cons bit bits ih => exact ih (some bit)

private def unframe_payload_evals (bits input : List Bool)
    (output : List (Option Bool)) (state : UnframeState) :
    EvalsToInTime unframeComputer.step
      (unframeCfg (some .payload) state (bits ++ input)
        (List.replicate bits.length true) output)
      (some (unframeCfg (some .next)
        (unframePayloadState state.inputBit bits) input []
        (bits.reverse.map some ++ output)))
      (bits.length + 1) := by
  induction bits generalizing output state with
  | nil =>
      cases state with
      | mk inputBit tick =>
          simpa [unframePayloadState, unframePoppedTick] using
            unframeEvalsToInTimeOne
              (unframe_step_payload_nil input output ⟨inputBit, tick⟩)
  | cons bit bits ih =>
      let middle := unframeCfg (some .payload)
        (unframePoppedInput (unframePoppedTick state (some true))
          (some bit))
        (bits ++ input) (List.replicate bits.length true)
        (some bit :: output)
      have hone : EvalsToInTime unframeComputer.step
          (unframeCfg (some .payload) state
            ((bit :: bits) ++ input)
            (List.replicate (bit :: bits).length true) output)
          (some middle) 1 :=
        unframeEvalsToInTimeOne (by
          simpa [middle, List.replicate_succ] using
            unframe_step_payload_cons bit true
              (bits ++ input) (List.replicate bits.length true)
              output state)
      have hrest := ih (some bit :: output)
        (unframePoppedInput (unframePoppedTick state (some true))
          (some bit))
      have htrans := EvalsToInTime.trans unframeComputer.step
        1 (bits.length + 1)
        (unframeCfg (some .payload) state
          ((bit :: bits) ++ input)
          (List.replicate (bit :: bits).length true) output)
        middle
        (some (unframeCfg (some .next)
          (unframePayloadState state.inputBit (bit :: bits))
          input [] ((bit :: bits).reverse.map some ++ output)))
        hone
        (by
          simpa [middle, unframePayloadState, unframePoppedInput,
            unframePoppedTick, List.reverse_cons, List.map_append,
            List.append_assoc] using hrest)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htrans

private def unframe_next_present_evals (input : List Bool)
    (hinput : input ≠ []) (output : List (Option Bool))
    (state : UnframeState) :
    EvalsToInTime unframeComputer.step
      (unframeCfg (some .next) state input [] output)
      (some (unframeCfg (some .scan)
        (unframePoppedInput state input.head?) input [] output)) 1 := by
  cases input with
  | nil => exact (hinput rfl).elim
  | cons bit input =>
      simpa using unframeEvalsToInTimeOne
        (unframe_step_next_cons bit input output state)

private def unframe_next_nil_evals (output : List (Option Bool))
    (state : UnframeState) (htick : state.tick = none) :
    EvalsToInTime unframeComputer.step
      (unframeCfg (some .next) state [] [] output)
      (some (unframeCfg none unframeInitialState [] [] output)) 1 := by
  cases state with
  | mk inputBit tick =>
      change tick = none at htick
      subst tick
      exact unframeEvalsToInTimeOne
        (unframe_step_next_nil output inputBit)

private theorem frames_flatMap_nonempty (bits : List Bool)
    (fields : List (List Bool)) :
    ((bits :: fields).flatMap BinaryNatLists.frame) ≠ [] := by
  simp [BinaryNatLists.frame]

private def unframe_fields_evals
    (fields : List (List Bool)) (hfields : fields ≠ [])
    (output : List (Option Bool)) (state : UnframeState) :
    EvalsToInTime unframeComputer.step
      (unframeCfg (some .scan) state
        (fields.flatMap BinaryNatLists.frame) [] output)
      (some (unframeCfg none unframeInitialState [] []
        (fields.reverse.flatMap RawNatList.segment ++ output)))
      ((fields.flatMap BinaryNatLists.frame).length + 2 * fields.length) := by
  induction fields generalizing output state with
  | nil => exact (hfields rfl).elim
  | cons bits fields ih =>
      let tailInput := fields.flatMap BinaryNatLists.frame
      have hscan := unframe_scan_evals bits.length
        (bits ++ tailInput) [] output state
      have hpayload := unframe_payload_evals bits tailInput
        (none :: output) (unframePoppedInput state (some false))
      have hfirst := EvalsToInTime.trans unframeComputer.step
        (bits.length + 1) (bits.length + 1)
        (unframeCfg (some .scan) state
          ((bits :: fields).flatMap BinaryNatLists.frame) [] output)
        (unframeCfg (some .payload)
          (unframePoppedInput state (some false))
          (bits ++ tailInput) (List.replicate bits.length true)
          (none :: output))
        (some (unframeCfg (some .next)
          (unframePayloadState
            (unframePoppedInput state (some false)).inputBit bits)
          tailInput [] (RawNatList.segment bits ++ output)))
        (by
          simpa [tailInput, BinaryNatLists.frame, List.append_assoc] using hscan)
        (by
          simpa [RawNatList.segment, List.append_assoc] using hpayload)
      cases fields with
      | nil =>
          have hnext := unframe_next_nil_evals
            (RawNatList.segment bits ++ output)
            (unframePayloadState
              (unframePoppedInput state (some false)).inputBit bits)
            (unframePayloadState_tick _ _)
          have hall := EvalsToInTime.trans unframeComputer.step
            ((bits.length + 1) + (bits.length + 1)) 1
            (unframeCfg (some .scan) state
              ([bits].flatMap BinaryNatLists.frame) [] output)
            (unframeCfg (some .next)
              (unframePayloadState
                (unframePoppedInput state (some false)).inputBit bits)
              [] [] (RawNatList.segment bits ++ output))
            (some (unframeCfg none unframeInitialState [] []
              (RawNatList.segment bits ++ output)))
            (by simpa [tailInput] using hfirst)
            hnext
          have htime :
              1 + ((bits.length + 1) + (bits.length + 1)) =
                ([bits].flatMap BinaryNatLists.frame).length +
                  2 * [bits].length := by
            simp [BinaryNatLists.frame]
            omega
          rw [htime] at hall
          simpa [RawNatList.segment] using hall
      | cons next fields =>
          let rest := next :: fields
          have htail :
              (rest.flatMap BinaryNatLists.frame) ≠ [] :=
            frames_flatMap_nonempty next fields
          have hnext := unframe_next_present_evals
            (rest.flatMap BinaryNatLists.frame) htail
            (RawNatList.segment bits ++ output)
            (unframePayloadState
              (unframePoppedInput state (some false)).inputBit bits)
          have hthroughNext := EvalsToInTime.trans unframeComputer.step
            ((bits.length + 1) + (bits.length + 1)) 1
            (unframeCfg (some .scan) state
              ((bits :: rest).flatMap BinaryNatLists.frame) [] output)
            (unframeCfg (some .next)
              (unframePayloadState
                (unframePoppedInput state (some false)).inputBit bits)
              (rest.flatMap BinaryNatLists.frame) []
              (RawNatList.segment bits ++ output))
            (some (unframeCfg (some .scan)
              (unframePoppedInput
                (unframePayloadState
                  (unframePoppedInput state (some false)).inputBit bits)
                (rest.flatMap BinaryNatLists.frame).head?)
              (rest.flatMap BinaryNatLists.frame) []
              (RawNatList.segment bits ++ output)))
            (by simpa [tailInput, rest] using hfirst)
            hnext
          have hrest := ih (by simp)
            (RawNatList.segment bits ++ output)
            (unframePoppedInput
              (unframePayloadState
                (unframePoppedInput state (some false)).inputBit bits)
              (rest.flatMap BinaryNatLists.frame).head?)
          have hall := EvalsToInTime.trans unframeComputer.step
            (1 + ((bits.length + 1) + (bits.length + 1)))
            ((rest.flatMap BinaryNatLists.frame).length +
              2 * rest.length)
            (unframeCfg (some .scan) state
              ((bits :: rest).flatMap BinaryNatLists.frame) [] output)
            (unframeCfg (some .scan)
              (unframePoppedInput
                (unframePayloadState
                  (unframePoppedInput state (some false)).inputBit bits)
                (rest.flatMap BinaryNatLists.frame).head?)
              (rest.flatMap BinaryNatLists.frame) []
              (RawNatList.segment bits ++ output))
            (some (unframeCfg none unframeInitialState [] []
              ((bits :: rest).reverse.flatMap RawNatList.segment ++ output)))
            hthroughNext
            (by
              simpa [rest, List.reverse_cons, List.append_assoc] using hrest)
          have htime :
              ((rest.flatMap BinaryNatLists.frame).length +
                  2 * rest.length) +
                  (1 + ((bits.length + 1) + (bits.length + 1))) =
                ((bits :: rest).flatMap BinaryNatLists.frame).length +
                  2 * (bits :: rest).length := by
            simp [BinaryNatLists.frame]
            omega
          rw [htime] at hall
          simpa [rest, List.append_assoc] using hall

private theorem fields_length_le_frames_length
    (fields : List (List Bool)) :
    fields.length ≤ (fields.flatMap BinaryNatLists.frame).length := by
  induction fields with
  | nil => simp
  | cons bits fields ih =>
      simp only [List.length_cons, List.flatMap_cons, List.length_append]
      have hpositive : 0 < (BinaryNatLists.frame bits).length := by
        simp [BinaryNatLists.frame]
      omega

private theorem unframe_initList_eq_cfg (input : List Bool) :
    initList unframeComputer input =
      unframeCfg (some .scan) unframeInitialState input [] [] := by
  unfold initList unframeCfg
  congr
  funext index
  cases index <;> rfl

private theorem unframe_haltList_eq_cfg (output : List (Option Bool)) :
    haltList unframeComputer output =
      unframeCfg none unframeInitialState [] [] output := by
  unfold haltList unframeCfg
  congr
  funext index
  cases index <;> rfl

/-- The unframing traversal consumes the standard nested-list encoding and
emits its explicit stack-oriented raw fields in at most three times the input
length. -/
def unframe_outputsInTime (xss : List (List ℕ)) :
    TM2OutputsInTime unframeComputer (BinaryNatLists.encode xss)
      (some (RawNatLists.encode xss))
      (3 * (BinaryNatLists.encode xss).length) := by
  have hpayloads : RawNatLists.payloads xss ≠ [] := by
    simp [RawNatLists.payloads]
  have hfields := unframe_fields_evals
    (RawNatLists.payloads xss) hpayloads [] unframeInitialState
  have hlength :=
    fields_length_le_frames_length (RawNatLists.payloads xss)
  have hbound :
      ((RawNatLists.payloads xss).flatMap BinaryNatLists.frame).length +
          2 * (RawNatLists.payloads xss).length ≤
        3 * ((RawNatLists.payloads xss).flatMap
          BinaryNatLists.frame).length := by
    omega
  have hmono := evalsToInTimeMono hfields hbound
  have hinput :
      BinaryNatLists.encode xss =
        (RawNatLists.payloads xss).flatMap BinaryNatLists.frame :=
    (RawNatLists.payloads_frame_eq_encode xss).symm
  rw [TM2OutputsInTime, hinput, unframe_initList_eq_cfg]
  simp only [Option.map_some]
  rw [unframe_haltList_eq_cfg]
  simpa [RawNatLists.encode] using hmono

/-- A genuine linear-time finite-machine witness exposing every field of the
standard nested-list input as an explicitly delimited raw binary stack stream.
The mathematical function is the identity; the change of encoding supplies
the traversal interface used by later arithmetic and compiler passes. -/
noncomputable def unframedNatListsComputableInPolyTime :
    @TM2ComputableInPolyTime (List (List ℕ)) (List (List ℕ))
      BinaryNatLists.finEncoding RawNatLists.finEncoding id where
  tm := unframeComputer
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl (Option Bool)
  time := 3 * Polynomial.X
  outputsFun xss := by
    simpa [BinaryNatLists.finEncoding, RawNatLists.finEncoding, Equiv.refl,
      Polynomial.eval_mul, Polynomial.eval_natCast, Polynomial.eval_X] using
        unframe_outputsInTime xss


end LeanNPHardness.MachinePrimitives
