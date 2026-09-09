import LeanNPHardness.CountedNatRows
import LeanNPHardness.FramingMachine

/-!
Reusable encoding and machine components extracted from `phd-thesis-lean`
commit `84be78db5a287f9a40dcb549252063d6db67de73`. Runtime bounds retain
the original explicit finite-alphabet input encodings.
-/

namespace LeanNPHardness.MachinePrimitives

open Computability Turing
open LeanNPHardness.MachineComposition

inductive CountedRowPayloadStack
  | input
  | scratch
  | output
  deriving DecidableEq, Fintype

/-- Initial delimiter removal, binary count skipping, payload staging, and
order restoration. -/
inductive CountedRowPayloadLabel
  | start
  | skipCount
  | stash
  | restore
  deriving DecidableEq, Fintype

/-- The outer option records stack exhaustion; the inner option distinguishes
a field delimiter from a binary payload bit. -/
abbrev CountedRowPayloadState := Option (Option Bool)

private def countedRowPayloadPopped
    (_state : CountedRowPayloadState)
    (symbol : Option (Option Bool)) : CountedRowPayloadState :=
  symbol

private def countedRowPayloadPresent : CountedRowPayloadState → Bool
  | some _ => true
  | none => false

private def countedRowPayloadIsBit : CountedRowPayloadState → Bool
  | some (some _) => true
  | _ => false

private def countedRowPayloadHeld : CountedRowPayloadState → Option Bool
  | some symbol => symbol
  | none => none

private def CountedRowPayloadAlphabet
    (_index : CountedRowPayloadStack) : Type :=
  Option Bool

/-- Remove the first delimiter and its binary field, then reverse the
remaining source cells twice so their semantic order is unchanged. -/
def countedRowPayloadProgram :
    CountedRowPayloadLabel →
      TM2.Stmt CountedRowPayloadAlphabet CountedRowPayloadLabel
        CountedRowPayloadState
  | .start =>
      .pop .input countedRowPayloadPopped <|
        .goto (fun _ => .skipCount)
  | .skipCount =>
      .pop .input countedRowPayloadPopped <|
        .branch countedRowPayloadPresent
          (.branch countedRowPayloadIsBit
            (.goto (fun _ => .skipCount))
            (.push .scratch countedRowPayloadHeld <|
              .goto (fun _ => .stash)))
          (.goto (fun _ => .restore))
  | .stash =>
      .pop .input countedRowPayloadPopped <|
        .branch countedRowPayloadPresent
          (.push .scratch countedRowPayloadHeld <|
            .goto (fun _ => .stash))
          (.goto (fun _ => .restore))
  | .restore =>
      .pop .scratch countedRowPayloadPopped <|
        .branch countedRowPayloadPresent
          (.push .output countedRowPayloadHeld <|
            .goto (fun _ => .restore))
          .halt

/-- Concrete three-stack machine extracting the complete domain-row payload.
-/
def countedRowPayloadComputer : FinTM2 where
  K := CountedRowPayloadStack
  k₀ := .input
  k₁ := .output
  Γ := CountedRowPayloadAlphabet
  Λ := CountedRowPayloadLabel
  main := .start
  σ := CountedRowPayloadState
  initialState := none
  Γk₀Fin := show Fintype (Option Bool) from inferInstance
  m := countedRowPayloadProgram

private def countedRowPayloadStackContents
    (input scratch output : List (Option Bool)) :
    (index : CountedRowPayloadStack) →
      List (CountedRowPayloadAlphabet index)
  | .input => input
  | .scratch => scratch
  | .output => output

private def countedRowPayloadCfg
    (label : Option CountedRowPayloadLabel)
    (state : CountedRowPayloadState)
    (input scratch output : List (Option Bool)) :
    countedRowPayloadComputer.Cfg where
  l := label
  var := state
  stk := countedRowPayloadStackContents input scratch output

private theorem countedRowPayload_step_start
    (input scratch output : List (Option Bool))
    (state : CountedRowPayloadState) :
    countedRowPayloadComputer.step
        (countedRowPayloadCfg (some .start) state input scratch output) =
      some (countedRowPayloadCfg (some .skipCount) input.head?
        input.tail scratch output) := by
  simp [countedRowPayloadComputer, FinTM2.step, countedRowPayloadCfg,
    countedRowPayloadProgram, countedRowPayloadStackContents,
    CountedRowPayloadAlphabet, countedRowPayloadPopped]
  funext index
  cases index <;> rfl

private theorem countedRowPayload_step_skipCount_bit
    (bit : Bool) (input scratch output : List (Option Bool))
    (state : CountedRowPayloadState) :
    countedRowPayloadComputer.step
        (countedRowPayloadCfg (some .skipCount) state
          (some bit :: input) scratch output) =
      some (countedRowPayloadCfg (some .skipCount) (some (some bit))
        input scratch output) := by
  cases bit <;>
    simp [countedRowPayloadComputer, FinTM2.step, countedRowPayloadCfg,
      countedRowPayloadProgram, countedRowPayloadStackContents,
      CountedRowPayloadAlphabet, countedRowPayloadPopped,
      countedRowPayloadPresent, countedRowPayloadIsBit] <;>
    (funext index; cases index <;> rfl)

private theorem countedRowPayload_step_skipCount_delimiter
    (input scratch output : List (Option Bool))
    (state : CountedRowPayloadState) :
    countedRowPayloadComputer.step
        (countedRowPayloadCfg (some .skipCount) state
          (none :: input) scratch output) =
      some (countedRowPayloadCfg (some .stash) (some none)
        input (none :: scratch) output) := by
  simp [countedRowPayloadComputer, FinTM2.step, countedRowPayloadCfg,
    countedRowPayloadProgram, countedRowPayloadStackContents,
    CountedRowPayloadAlphabet, countedRowPayloadPopped,
    countedRowPayloadPresent, countedRowPayloadIsBit,
    countedRowPayloadHeld, Function.update]
  funext index
  cases index <;> rfl

private theorem countedRowPayload_step_skipCount_nil
    (scratch output : List (Option Bool))
    (state : CountedRowPayloadState) :
    countedRowPayloadComputer.step
        (countedRowPayloadCfg (some .skipCount) state [] scratch output) =
      some (countedRowPayloadCfg (some .restore) none [] scratch output) := by
  simp [countedRowPayloadComputer, FinTM2.step, countedRowPayloadCfg,
    countedRowPayloadProgram, countedRowPayloadStackContents,
    CountedRowPayloadAlphabet, countedRowPayloadPopped,
    countedRowPayloadPresent]

private theorem countedRowPayload_step_stash_cons
    (symbol : Option Bool) (input scratch output : List (Option Bool))
    (state : CountedRowPayloadState) :
    countedRowPayloadComputer.step
        (countedRowPayloadCfg (some .stash) state
          (symbol :: input) scratch output) =
      some (countedRowPayloadCfg (some .stash) (some symbol)
        input (symbol :: scratch) output) := by
  rcases symbol with _ | bit <;>
    simp [countedRowPayloadComputer, FinTM2.step, countedRowPayloadCfg,
      countedRowPayloadProgram, countedRowPayloadStackContents,
      CountedRowPayloadAlphabet, countedRowPayloadPopped,
      countedRowPayloadPresent, countedRowPayloadHeld, Function.update] <;>
    (funext index; cases index <;> rfl)

private theorem countedRowPayload_step_stash_nil
    (scratch output : List (Option Bool))
    (state : CountedRowPayloadState) :
    countedRowPayloadComputer.step
        (countedRowPayloadCfg (some .stash) state [] scratch output) =
      some (countedRowPayloadCfg (some .restore) none [] scratch output) := by
  simp [countedRowPayloadComputer, FinTM2.step, countedRowPayloadCfg,
    countedRowPayloadProgram, countedRowPayloadStackContents,
    CountedRowPayloadAlphabet, countedRowPayloadPopped,
    countedRowPayloadPresent]

private theorem countedRowPayload_step_restore_cons
    (symbol : Option Bool) (scratch output : List (Option Bool))
    (state : CountedRowPayloadState) :
    countedRowPayloadComputer.step
        (countedRowPayloadCfg (some .restore) state []
          (symbol :: scratch) output) =
      some (countedRowPayloadCfg (some .restore) (some symbol) []
        scratch (symbol :: output)) := by
  rcases symbol with _ | bit <;>
    simp [countedRowPayloadComputer, FinTM2.step, countedRowPayloadCfg,
      countedRowPayloadProgram, countedRowPayloadStackContents,
      CountedRowPayloadAlphabet, countedRowPayloadPopped,
      countedRowPayloadPresent, countedRowPayloadHeld, Function.update] <;>
    (funext index; cases index <;> rfl)

private theorem countedRowPayload_step_restore_nil
    (output : List (Option Bool)) (state : CountedRowPayloadState) :
    countedRowPayloadComputer.step
        (countedRowPayloadCfg (some .restore) state [] [] output) =
      some (countedRowPayloadCfg none none [] [] output) := by
  simp [countedRowPayloadComputer, FinTM2.step, countedRowPayloadCfg,
    countedRowPayloadProgram, countedRowPayloadStackContents,
    CountedRowPayloadAlphabet, countedRowPayloadPopped,
    countedRowPayloadPresent]

private def countedRowPayloadEvalsToInTimeOne
    {start finish : countedRowPayloadComputer.Cfg}
    (hstep : countedRowPayloadComputer.step start = some finish) :
    EvalsToInTime countedRowPayloadComputer.step start (some finish) 1 where
  steps := 1
  evals_in_steps := by
    simpa [Function.iterate_one] using hstep
  steps_le_m := Nat.le_refl 1

private def countedRowPayload_skipCount_nil_evals
    (bits : List Bool) (scratch output : List (Option Bool))
    (state : CountedRowPayloadState) :
    EvalsToInTime countedRowPayloadComputer.step
      (countedRowPayloadCfg (some .skipCount) state
        (bits.map some) scratch output)
      (some (countedRowPayloadCfg (some .restore) none [] scratch output))
      (bits.length + 1) := by
  induction bits generalizing state with
  | nil =>
      simpa using countedRowPayloadEvalsToInTimeOne
        (countedRowPayload_step_skipCount_nil scratch output state)
  | cons bit bits ih =>
      have hone := countedRowPayloadEvalsToInTimeOne
        (countedRowPayload_step_skipCount_bit bit
          (bits.map some) scratch output state)
      have hrest := ih (some (some bit))
      exact EvalsToInTime.trans countedRowPayloadComputer.step
        1 (bits.length + 1)
        (countedRowPayloadCfg (some .skipCount) state
          ((bit :: bits).map some) scratch output)
        (countedRowPayloadCfg (some .skipCount) (some (some bit))
          (bits.map some) scratch output)
        (some (countedRowPayloadCfg (some .restore) none [] scratch output))
        (by simpa using hone) hrest

private def countedRowPayload_stash_evals
    (input scratch output : List (Option Bool))
    (state : CountedRowPayloadState) :
    EvalsToInTime countedRowPayloadComputer.step
      (countedRowPayloadCfg (some .stash) state input scratch output)
      (some (countedRowPayloadCfg (some .restore) none []
        (input.reverse ++ scratch) output))
      (input.length + 1) := by
  induction input generalizing scratch state with
  | nil =>
      simpa using countedRowPayloadEvalsToInTimeOne
        (countedRowPayload_step_stash_nil scratch output state)
  | cons symbol input ih =>
      have hone := countedRowPayloadEvalsToInTimeOne
        (countedRowPayload_step_stash_cons symbol input scratch output state)
      have hrest := ih (symbol :: scratch) (some symbol)
      have hall := EvalsToInTime.trans countedRowPayloadComputer.step
        1 (input.length + 1)
        (countedRowPayloadCfg (some .stash) state
          (symbol :: input) scratch output)
        (countedRowPayloadCfg (some .stash) (some symbol)
          input (symbol :: scratch) output)
        (some (countedRowPayloadCfg (some .restore) none []
          ((symbol :: input).reverse ++ scratch) output))
        (by simpa using hone)
        (by simpa [List.reverse_cons, List.append_assoc] using hrest)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hall

private def countedRowPayload_skipCount_payload_evals
    (bits : List Bool) (tail scratch output : List (Option Bool))
    (state : CountedRowPayloadState) :
    EvalsToInTime countedRowPayloadComputer.step
      (countedRowPayloadCfg (some .skipCount) state
        (bits.map some ++ none :: tail) scratch output)
      (some (countedRowPayloadCfg (some .restore) none []
        ((none :: tail).reverse ++ scratch) output))
      (bits.length + tail.length + 2) := by
  induction bits generalizing state with
  | nil =>
      have hdelimiter := countedRowPayloadEvalsToInTimeOne
        (countedRowPayload_step_skipCount_delimiter tail scratch output state)
      have hstash := countedRowPayload_stash_evals
        tail (none :: scratch) output (some none)
      have hall := EvalsToInTime.trans countedRowPayloadComputer.step
        1 (tail.length + 1)
        (countedRowPayloadCfg (some .skipCount) state
          (none :: tail) scratch output)
        (countedRowPayloadCfg (some .stash) (some none)
          tail (none :: scratch) output)
        (some (countedRowPayloadCfg (some .restore) none []
          ((none :: tail).reverse ++ scratch) output))
        (by simpa using hdelimiter)
        (by
          simpa [List.reverse_cons, List.append_assoc] using hstash)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hall
  | cons bit bits ih =>
      have hone := countedRowPayloadEvalsToInTimeOne
        (countedRowPayload_step_skipCount_bit bit
          (bits.map some ++ none :: tail) scratch output state)
      have hrest := ih (some (some bit))
      have hall := EvalsToInTime.trans countedRowPayloadComputer.step
        1 (bits.length + tail.length + 2)
        (countedRowPayloadCfg (some .skipCount) state
          ((bit :: bits).map some ++ none :: tail) scratch output)
        (countedRowPayloadCfg (some .skipCount) (some (some bit))
          (bits.map some ++ none :: tail) scratch output)
        (some (countedRowPayloadCfg (some .restore) none []
          ((none :: tail).reverse ++ scratch) output))
        (by simpa using hone) hrest
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hall

private def countedRowPayload_restore_evals
    (scratch output : List (Option Bool))
    (state : CountedRowPayloadState) :
    EvalsToInTime countedRowPayloadComputer.step
      (countedRowPayloadCfg (some .restore) state [] scratch output)
      (some (countedRowPayloadCfg none none [] []
        (scratch.reverse ++ output)))
      (scratch.length + 1) := by
  induction scratch generalizing output state with
  | nil =>
      simpa using countedRowPayloadEvalsToInTimeOne
        (countedRowPayload_step_restore_nil output state)
  | cons symbol scratch ih =>
      have hone := countedRowPayloadEvalsToInTimeOne
        (countedRowPayload_step_restore_cons symbol scratch output state)
      have hrest := ih (symbol :: output) (some symbol)
      have hall := EvalsToInTime.trans countedRowPayloadComputer.step
        1 (scratch.length + 1)
        (countedRowPayloadCfg (some .restore) state []
          (symbol :: scratch) output)
        (countedRowPayloadCfg (some .restore) (some symbol) []
          scratch (symbol :: output))
        (some (countedRowPayloadCfg none none [] []
          ((symbol :: scratch).reverse ++ output)))
        (by simpa using hone)
        (by simpa [List.reverse_cons, List.append_assoc] using hrest)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hall

private theorem countedRowPayload_initList_eq_cfg
    (input : List (Option Bool)) :
    initList countedRowPayloadComputer input =
      countedRowPayloadCfg (some .start) none input [] [] := by
  unfold initList countedRowPayloadCfg
  congr
  funext index
  cases index <;> rfl

private theorem countedRowPayload_haltList_eq_cfg
    (output : List (Option Bool)) :
    haltList countedRowPayloadComputer output =
      countedRowPayloadCfg none none [] [] output := by
  unfold haltList countedRowPayloadCfg
  congr
  funext index
  cases index <;> rfl

private theorem CountedNatRows.inputEncode_eq_count_payload
    (domains : List (List ℕ)) :
    CountedNatRows.inputEncode domains =
      none :: (encodeNat domains.length).map some ++
        SourceOrderRawFields.encode (CountedNatRows.rowFields domains) := by
  simp [CountedNatRows.inputEncode, CountedNatRows.inputFields,
    SourceOrderRawFields.encode]

/-- The checked outer domain count is removed in linear time, while every
count-prefixed domain row is preserved exactly in source order. -/
def countedRowPayload_outputsInTime (domains : List (List ℕ)) :
    TM2OutputsInTime countedRowPayloadComputer
      (CountedNatRows.inputEncode domains)
      (some (SourceOrderRawFields.encode
        (CountedNatRows.rowFields domains)))
      (2 * (CountedNatRows.inputEncode domains).length + 1) := by
  cases domains with
  | nil =>
      have hstart := countedRowPayloadEvalsToInTimeOne
        (countedRowPayload_step_start [none] [] [] none)
      have hskip := countedRowPayload_skipCount_nil_evals [] [] [] (some none)
      have hfirst := EvalsToInTime.trans countedRowPayloadComputer.step
        1 1
        (countedRowPayloadCfg (some .start) none [none] [] [])
        (countedRowPayloadCfg (some .skipCount) (some none) [] [] [])
        (some (countedRowPayloadCfg (some .restore) none [] [] []))
        (by simpa using hstart)
        (by simpa using hskip)
      have hrestore := countedRowPayload_restore_evals [] [] none
      have hall := EvalsToInTime.trans countedRowPayloadComputer.step
        2 1
        (countedRowPayloadCfg (some .start) none [none] [] [])
        (countedRowPayloadCfg (some .restore) none [] [] [])
        (some (countedRowPayloadCfg none none [] [] []))
        (by simpa using hfirst)
        (by simpa using hrestore)
      have hmono : EvalsToInTime countedRowPayloadComputer.step
          (countedRowPayloadCfg (some .start) none
            (CountedNatRows.inputEncode []) [] [])
          (some (countedRowPayloadCfg none none [] [] []))
          (2 * (CountedNatRows.inputEncode []).length + 1) := by
        have hzero : encodeNat 0 = [] := by
          unfold encodeNat
          change encodeNum (Num.ofNat' 0) = []
          rw [Num.ofNat'_zero]
          rfl
        simpa [CountedNatRows.inputEncode,
          CountedNatRows.inputFields, CountedNatRows.rowFields,
          SourceOrderRawFields.encode, hzero] using hall
      rw [TM2OutputsInTime, countedRowPayload_initList_eq_cfg]
      simp only [Option.map_some]
      rw [countedRowPayload_haltList_eq_cfg]
      simpa [CountedNatRows.rowFields,
        SourceOrderRawFields.encode] using hmono
  | cons domain domains =>
      let countBits := encodeNat (domain :: domains).length
      let tail := (encodeNat domain.length).map some ++
        SourceOrderRawFields.encode
          (domain ++ CountedNatRows.rowFields domains)
      have hinput : CountedNatRows.inputEncode (domain :: domains) =
          none :: countBits.map some ++ none :: tail := by
        simp [CountedNatRows.inputEncode, CountedNatRows.inputFields,
          CountedNatRows.rowFields, SourceOrderRawFields.encode,
          countBits, tail]
      have hpayload : SourceOrderRawFields.encode
          (CountedNatRows.rowFields (domain :: domains)) = none :: tail := by
        simp [CountedNatRows.rowFields, SourceOrderRawFields.encode, tail]
      have hstart := countedRowPayloadEvalsToInTimeOne
        (countedRowPayload_step_start
          (none :: countBits.map some ++ none :: tail) [] [] none)
      have hskip := countedRowPayload_skipCount_payload_evals
        countBits tail [] [] (some none)
      have hfirst := EvalsToInTime.trans countedRowPayloadComputer.step
        1 (countBits.length + tail.length + 2)
        (countedRowPayloadCfg (some .start) none
          (none :: countBits.map some ++ none :: tail) [] [])
        (countedRowPayloadCfg (some .skipCount) (some none)
          (countBits.map some ++ none :: tail) [] [])
        (some (countedRowPayloadCfg (some .restore) none []
          (none :: tail).reverse []))
        (by simpa using hstart)
        (by simpa using hskip)
      have hrestore := countedRowPayload_restore_evals
        (none :: tail).reverse [] none
      have hfirst' : EvalsToInTime countedRowPayloadComputer.step
          (countedRowPayloadCfg (some .start) none
            (none :: countBits.map some ++ none :: tail) [] [])
          (some (countedRowPayloadCfg (some .restore) none []
            (none :: tail).reverse []))
          (countBits.length + tail.length + 3) := by
        rw [show countBits.length + tail.length + 3 =
          (countBits.length + tail.length + 2) + 1 by omega]
        exact hfirst
      have hall := EvalsToInTime.trans countedRowPayloadComputer.step
        (countBits.length + tail.length + 3)
        ((none :: tail).reverse.length + 1)
        (countedRowPayloadCfg (some .start) none
          (none :: countBits.map some ++ none :: tail) [] [])
        (countedRowPayloadCfg (some .restore) none []
          (none :: tail).reverse [])
        (some (countedRowPayloadCfg none none [] [] (none :: tail)))
        hfirst'
        (by simpa using hrestore)
      have hmono : EvalsToInTime countedRowPayloadComputer.step
          (countedRowPayloadCfg (some .start) none
            (CountedNatRows.inputEncode (domain :: domains)) [] [])
          (some (countedRowPayloadCfg none none [] [] (none :: tail)))
          (2 * (CountedNatRows.inputEncode
            (domain :: domains)).length + 1) := by
        rw [hinput]
        apply evalsToInTimeMono hall
        simp only [List.length_cons, List.length_append, List.length_map,
          List.length_reverse]
        omega
      rw [TM2OutputsInTime, countedRowPayload_initList_eq_cfg]
      simp only [Option.map_some]
      rw [countedRowPayload_haltList_eq_cfg]
      simpa [hpayload] using hmono

/-- A genuine linear-time finite-machine witness for extracting the complete
count-prefixed row payload from the checked domain-section encoding. -/
noncomputable def countedRowPayloadComputableInPolyTime :
    @TM2ComputableInPolyTime (List (List ℕ)) (List ℕ)
      CountedNatRows.inputFinEncoding SourceOrderRawFields.finEncoding
      CountedNatRows.rowFields where
  tm := countedRowPayloadComputer
  inputAlphabet := Equiv.refl (Option Bool)
  outputAlphabet := Equiv.refl (Option Bool)
  time := 2 * Polynomial.X + 1
  outputsFun domains := by
    simpa [CountedNatRows.inputFinEncoding,
      SourceOrderRawFields.finEncoding, Equiv.refl, Polynomial.eval_add,
      Polynomial.eval_mul, Polynomial.eval_natCast, Polynomial.eval_one,
      Polynomial.eval_X] using countedRowPayload_outputsInTime domains

/-- The same concrete pass preserves the structured list-of-domains meaning:
its checked output decoder reconstructs every row, including empty rows, and
rejects malformed or partial count-prefixed payloads. -/
noncomputable def countedRowPayloadStructuredComputableInPolyTime :
    @TM2ComputableInPolyTime (List (List ℕ)) (List (List ℕ))
      CountedNatRows.inputFinEncoding
      CountedNatRows.rowPayloadFinEncoding id where
  tm := countedRowPayloadComputer
  inputAlphabet := Equiv.refl (Option Bool)
  outputAlphabet := Equiv.refl (Option Bool)
  time := 2 * Polynomial.X + 1
  outputsFun domains := by
    simpa [CountedNatRows.inputFinEncoding,
      CountedNatRows.rowPayloadFinEncoding,
      CountedNatRows.rowPayloadEncode, Equiv.refl, Polynomial.eval_add,
      Polynomial.eval_mul, Polynomial.eval_natCast, Polynomial.eval_one,
      Polynomial.eval_X] using countedRowPayload_outputsInTime domains


end LeanNPHardness.MachinePrimitives
