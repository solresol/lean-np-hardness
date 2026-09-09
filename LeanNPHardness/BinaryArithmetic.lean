import LeanNPHardness.MachineRun

/-!
Reusable encoding and machine components extracted from `phd-thesis-lean`
commit `84be78db5a287f9a40dcb549252063d6db67de73`. Runtime bounds retain
the original explicit finite-alphabet input encodings.
-/

namespace LeanNPHardness.MachinePrimitives

open Computability Turing
open LeanNPHardness.MachineComposition


/-- Increment a least-significant-bit-first binary word. On canonical
`encodeNat` words this is exactly natural-number successor. -/
def binarySuccBits : List Bool → List Bool
  | [] => [true]
  | false :: bits => true :: bits
  | true :: bits => false :: binarySuccBits bits

private theorem binarySuccBits_encodePosNum (n : PosNum) :
    binarySuccBits (encodePosNum n) = encodePosNum n.succ := by
  induction n with
  | one => rfl
  | bit0 n ih => rfl
  | bit1 n ih =>
      simp only [encodePosNum, binarySuccBits, PosNum.succ]
      rw [ih]

private theorem binarySuccBits_encodeNum (n : Num) :
    binarySuccBits (encodeNum n) = encodeNum n.succ := by
  cases n with
  | zero => rfl
  | pos n =>
      simp only [encodeNum, Num.succ, Num.succ']
      exact binarySuccBits_encodePosNum n

/-- The bit-level transformation agrees with successor on mathlib's canonical
binary natural encoding, including the empty encoding of zero. -/
@[simp]
theorem binarySuccBits_encodeNat (n : ℕ) :
    binarySuccBits (encodeNat n) = encodeNat (n + 1) := by
  unfold encodeNat
  rw [binarySuccBits_encodeNum]
  change encodeNum (Num.ofNat' n).succ = encodeNum (Num.ofNat' (n + 1))
  rw [Num.ofNat'_succ, Num.add_one]

theorem binarySuccBits_length_le (bits : List Bool) :
    (binarySuccBits bits).length ≤ bits.length + 1 := by
  induction bits with
  | nil => simp [binarySuccBits]
  | cons bit bits ih =>
      cases bit <;> simp [binarySuccBits, ih]

/-- Input, reversal work, and canonical output stacks for binary successor. -/
inductive SuccStack
  | input
  | work
  | output
  deriving DecidableEq, Fintype

/-- Carry propagation, untouched-suffix copy, and output reversal phases. -/
inductive SuccLabel
  | carry
  | copy
  | reverse
  deriving DecidableEq, Fintype

/-- Finite control remembers the most recently popped bit. -/
structure SuccState where
  bit : Option Bool
  deriving DecidableEq, Fintype

private def succInitialState : SuccState :=
  ⟨none⟩

private def succPoppedBit (_state : SuccState) (bit : Option Bool) : SuccState :=
  ⟨bit⟩

private def succBitPresent : SuccState → Bool
  | ⟨some _⟩ => true
  | _ => false

private def succBitTrue : SuccState → Bool
  | ⟨some true⟩ => true
  | _ => false

private def succHeldBit : SuccState → Bool
  | ⟨some bit⟩ => bit
  | _ => false

private def SuccAlphabet (_index : SuccStack) : Type := Bool

/-- A finite three-stack successor program for least-significant-bit-first
binary words. -/
def binarySuccProgram :
    SuccLabel → TM2.Stmt SuccAlphabet SuccLabel SuccState
  | .carry =>
      .pop .input succPoppedBit <|
        .branch succBitPresent
          (.branch succBitTrue
            (.push .work (fun _ => false) <|
              .goto (fun _ => .carry))
            (.push .work (fun _ => true) <|
              .goto (fun _ => .copy)))
          (.push .work (fun _ => true) <|
            .goto (fun _ => .reverse))
  | .copy =>
      .pop .input succPoppedBit <|
        .branch succBitPresent
          (.push .work succHeldBit <|
            .goto (fun _ => .copy))
          (.goto (fun _ => .reverse))
  | .reverse =>
      .pop .work succPoppedBit <|
        .branch succBitPresent
          (.push .output succHeldBit <|
            .goto (fun _ => .reverse))
          .halt

/-- Concrete finite machine computing binary successor. -/
def binarySuccComputer : FinTM2 where
  K := SuccStack
  k₀ := .input
  k₁ := .output
  Γ := SuccAlphabet
  Λ := SuccLabel
  main := .carry
  σ := SuccState
  initialState := succInitialState
  Γk₀Fin := Bool.fintype
  m := binarySuccProgram

private def succStackContents
    (input work output : List Bool) :
    (index : SuccStack) → List (SuccAlphabet index)
  | .input => input
  | .work => work
  | .output => output

private def succCfg (label : Option SuccLabel) (state : SuccState)
    (input work output : List Bool) : binarySuccComputer.Cfg where
  l := label
  var := state
  stk := succStackContents input work output

private theorem succ_step_carry_nil (work output : List Bool)
    (state : SuccState) :
    binarySuccComputer.step
        (succCfg (some .carry) state [] work output) =
      some (succCfg (some .reverse) succInitialState []
        (true :: work) output) := by
  simp [binarySuccComputer, FinTM2.step, succCfg, binarySuccProgram,
    succStackContents, SuccAlphabet, succPoppedBit, succBitPresent,
    succInitialState, Function.update]
  funext index
  cases index <;> rfl

private theorem succ_step_carry_false (bits work output : List Bool)
    (state : SuccState) :
    binarySuccComputer.step
        (succCfg (some .carry) state (false :: bits) work output) =
      some (succCfg (some .copy) ⟨some false⟩ bits
        (true :: work) output) := by
  simp [binarySuccComputer, FinTM2.step, succCfg, binarySuccProgram,
    succStackContents, SuccAlphabet, succPoppedBit, succBitPresent,
    succBitTrue, Function.update]
  funext index
  cases index <;> rfl

private theorem succ_step_carry_true (bits work output : List Bool)
    (state : SuccState) :
    binarySuccComputer.step
        (succCfg (some .carry) state (true :: bits) work output) =
      some (succCfg (some .carry) ⟨some true⟩ bits
        (false :: work) output) := by
  simp [binarySuccComputer, FinTM2.step, succCfg, binarySuccProgram,
    succStackContents, SuccAlphabet, succPoppedBit, succBitPresent,
    succBitTrue, Function.update]
  funext index
  cases index <;> rfl

private theorem succ_step_copy_nil (work output : List Bool)
    (state : SuccState) :
    binarySuccComputer.step
        (succCfg (some .copy) state [] work output) =
      some (succCfg (some .reverse) succInitialState [] work output) := by
  simp [binarySuccComputer, FinTM2.step, succCfg, binarySuccProgram,
    succStackContents, SuccAlphabet, succPoppedBit, succBitPresent,
    succInitialState, Function.update]

private theorem succ_step_copy_cons (bit : Bool) (bits work output : List Bool)
    (state : SuccState) :
    binarySuccComputer.step
        (succCfg (some .copy) state (bit :: bits) work output) =
      some (succCfg (some .copy) ⟨some bit⟩ bits
        (bit :: work) output) := by
  cases bit <;>
    simp [binarySuccComputer, FinTM2.step, succCfg, binarySuccProgram,
      succStackContents, SuccAlphabet, succPoppedBit, succBitPresent,
      succHeldBit, Function.update] <;>
    (funext index; cases index <;> rfl)

private theorem succ_step_reverse_nil (output : List Bool)
    (state : SuccState) :
    binarySuccComputer.step
        (succCfg (some .reverse) state [] [] output) =
      some (succCfg none succInitialState [] [] output) := by
  simp [binarySuccComputer, FinTM2.step, succCfg, binarySuccProgram,
    succStackContents, SuccAlphabet, succPoppedBit, succBitPresent,
    succInitialState, Function.update]

private theorem succ_step_reverse_cons (bit : Bool)
    (work output : List Bool) (state : SuccState) :
    binarySuccComputer.step
        (succCfg (some .reverse) state [] (bit :: work) output) =
      some (succCfg (some .reverse) ⟨some bit⟩ [] work
        (bit :: output)) := by
  cases bit <;>
    simp [binarySuccComputer, FinTM2.step, succCfg, binarySuccProgram,
      succStackContents, SuccAlphabet, succPoppedBit, succBitPresent,
      succHeldBit, Function.update] <;>
    (funext index; cases index <;> rfl)

private def succEvalsToInTimeOne
    {start finish : binarySuccComputer.Cfg}
    (hstep : binarySuccComputer.step start = some finish) :
    EvalsToInTime binarySuccComputer.step start (some finish) 1 where
  steps := 1
  evals_in_steps := by
    simpa [Function.iterate_one] using hstep
  steps_le_m := Nat.le_refl 1

private def succ_copy_evals (bits work output : List Bool)
    (state : SuccState) :
    EvalsToInTime binarySuccComputer.step
      (succCfg (some .copy) state bits work output)
      (some (succCfg (some .reverse) succInitialState []
        (bits.reverse ++ work) output))
      (bits.length + 1) := by
  induction bits generalizing work state with
  | nil =>
      simpa using succEvalsToInTimeOne
        (succ_step_copy_nil work output state)
  | cons bit bits ih =>
      let middle := succCfg (some .copy) ⟨some bit⟩ bits
        (bit :: work) output
      have hone : EvalsToInTime binarySuccComputer.step
          (succCfg (some .copy) state (bit :: bits) work output)
          (some middle) 1 :=
        succEvalsToInTimeOne (by
          simpa [middle] using succ_step_copy_cons bit bits work output state)
      have hrest := ih (bit :: work) ⟨some bit⟩
      have htrans := EvalsToInTime.trans binarySuccComputer.step
        1 (bits.length + 1)
        (succCfg (some .copy) state (bit :: bits) work output)
        middle
        (some (succCfg (some .reverse) succInitialState []
          ((bit :: bits).reverse ++ work) output))
        hone
        (by simpa [middle, List.reverse_cons, List.append_assoc] using hrest)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htrans

private def succ_carry_evals (bits work output : List Bool)
    (state : SuccState) :
    EvalsToInTime binarySuccComputer.step
      (succCfg (some .carry) state bits work output)
      (some (succCfg (some .reverse) succInitialState []
        ((binarySuccBits bits).reverse ++ work) output))
      (bits.length + 1) := by
  induction bits generalizing work state with
  | nil =>
      simpa [binarySuccBits] using succEvalsToInTimeOne
        (succ_step_carry_nil work output state)
  | cons bit bits ih =>
      cases bit with
      | false =>
          let middle := succCfg (some .copy) ⟨some false⟩ bits
            (true :: work) output
          have hone : EvalsToInTime binarySuccComputer.step
              (succCfg (some .carry) state (false :: bits) work output)
              (some middle) 1 :=
            succEvalsToInTimeOne (by
              simpa [middle] using succ_step_carry_false bits work output state)
          have hcopy := succ_copy_evals bits (true :: work) output ⟨some false⟩
          have htrans := EvalsToInTime.trans binarySuccComputer.step
            1 (bits.length + 1)
            (succCfg (some .carry) state (false :: bits) work output)
            middle
            (some (succCfg (some .reverse) succInitialState []
              ((binarySuccBits (false :: bits)).reverse ++ work) output))
            hone
            (by
              simpa [middle, binarySuccBits, List.reverse_cons,
                List.append_assoc] using hcopy)
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htrans
      | true =>
          let middle := succCfg (some .carry) ⟨some true⟩ bits
            (false :: work) output
          have hone : EvalsToInTime binarySuccComputer.step
              (succCfg (some .carry) state (true :: bits) work output)
              (some middle) 1 :=
            succEvalsToInTimeOne (by
              simpa [middle] using succ_step_carry_true bits work output state)
          have hrest := ih (false :: work) ⟨some true⟩
          have htrans := EvalsToInTime.trans binarySuccComputer.step
            1 (bits.length + 1)
            (succCfg (some .carry) state (true :: bits) work output)
            middle
            (some (succCfg (some .reverse) succInitialState []
              ((binarySuccBits (true :: bits)).reverse ++ work) output))
            hone
            (by
              simpa [middle, binarySuccBits, List.reverse_cons,
                List.append_assoc] using hrest)
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htrans

private def succ_reverse_evals (work output : List Bool)
    (state : SuccState) :
    EvalsToInTime binarySuccComputer.step
      (succCfg (some .reverse) state [] work output)
      (some (succCfg none succInitialState [] []
        (work.reverse ++ output)))
      (work.length + 1) := by
  induction work generalizing output state with
  | nil =>
      simpa using succEvalsToInTimeOne
        (succ_step_reverse_nil output state)
  | cons bit work ih =>
      let middle := succCfg (some .reverse) ⟨some bit⟩ [] work
        (bit :: output)
      have hone : EvalsToInTime binarySuccComputer.step
          (succCfg (some .reverse) state [] (bit :: work) output)
          (some middle) 1 :=
        succEvalsToInTimeOne (by
          simpa [middle] using succ_step_reverse_cons bit work output state)
      have hrest := ih (bit :: output) ⟨some bit⟩
      have htrans := EvalsToInTime.trans binarySuccComputer.step
        1 (work.length + 1)
        (succCfg (some .reverse) state [] (bit :: work) output)
        middle
        (some (succCfg none succInitialState [] []
          ((bit :: work).reverse ++ output)))
        hone
        (by simpa [middle, List.reverse_cons, List.append_assoc] using hrest)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htrans

private theorem succ_initList_eq_cfg (input : List Bool) :
    initList binarySuccComputer input =
      succCfg (some .carry) succInitialState input [] [] := by
  unfold initList succCfg
  congr
  funext index
  cases index <;> rfl

private theorem succ_haltList_eq_cfg (output : List Bool) :
    haltList binarySuccComputer output =
      succCfg none succInitialState [] [] output := by
  unfold haltList succCfg
  congr
  funext index
  cases index <;> rfl

/-- Binary successor runs in at most `2s + 3` steps on an arbitrary bit word
of length `s` and emits `binarySuccBits` of that word. -/
def binarySucc_outputsInTime (bits : List Bool) :
    TM2OutputsInTime binarySuccComputer bits
      (some (binarySuccBits bits)) (2 * bits.length + 3) := by
  have hcarry := succ_carry_evals bits [] [] succInitialState
  have hreverse := succ_reverse_evals
    (binarySuccBits bits).reverse [] succInitialState
  have hall := EvalsToInTime.trans binarySuccComputer.step
    (bits.length + 1) ((binarySuccBits bits).reverse.length + 1)
    (succCfg (some .carry) succInitialState bits [] [])
    (succCfg (some .reverse) succInitialState []
      (binarySuccBits bits).reverse [])
    (some (succCfg none succInitialState [] [] (binarySuccBits bits)))
    (by simpa using hcarry)
    (by simpa using hreverse)
  have hbound := binarySuccBits_length_le bits
  have hmono : EvalsToInTime binarySuccComputer.step
      (succCfg (some .carry) succInitialState bits [] [])
      (some (succCfg none succInitialState [] [] (binarySuccBits bits)))
      (2 * bits.length + 3) :=
    evalsToInTimeMono hall (by
      simp only [List.length_reverse]
      omega)
  rw [TM2OutputsInTime, succ_initList_eq_cfg]
  simp only [Option.map_some]
  rw [succ_haltList_eq_cfg]
  exact hmono

/-- A genuine linear-time finite-machine witness for successor on mathlib's
standard binary natural-number encoding. -/
noncomputable def binarySuccComputableInPolyTime :
    @TM2ComputableInPolyTime ℕ ℕ finEncodingNatBool finEncodingNatBool
      (fun n => n + 1) where
  tm := binarySuccComputer
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := 2 * Polynomial.X + 3
  outputsFun n := by
    simpa [finEncodingNatBool, Equiv.refl, binarySuccBits_encodeNat,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_natCast,
      Polynomial.eval_X] using binarySucc_outputsInTime (encodeNat n)


/-!
The source-order structural scan must count down both the remaining domain
lists and the remaining values in the current list.  The following finite
machine supplies the missing canonical binary predecessor primitive.  It
propagates a borrow across low zero bits, removes the now-leading zero when a
power of two is decremented, copies the untouched suffix, and reverses one
work stack into canonical least-significant-bit-first order.
-/

/-- Decrement a least-significant-bit-first binary word, saturating at zero.
On canonical `encodeNat` words the result is again canonical. -/
def binaryPredBits : List Bool → List Bool
  | [] => []
  | false :: bits => true :: binaryPredBits bits
  | true :: [] => []
  | true :: bit :: bits => false :: bit :: bits

private theorem binaryPredBits_encodePosNum (n : PosNum) :
    binaryPredBits (encodePosNum n) = encodeNum n.pred' := by
  induction n with
  | one => rfl
  | bit0 n ih =>
      simp only [encodePosNum, binaryPredBits, PosNum.pred']
      rw [ih]
      cases n.pred' <;> rfl
  | bit1 n _ih =>
      cases n <;> rfl

private theorem binaryPredBits_encodeNum (n : Num) :
    binaryPredBits (encodeNum n) = encodeNum n.pred := by
  cases n with
  | zero => rfl
  | pos n => exact binaryPredBits_encodePosNum n

/-- The bit-level transformation agrees with saturated predecessor on
mathlib's canonical natural-number encoding, including `0` and `1`. -/
@[simp]
theorem binaryPredBits_encodeNat (n : ℕ) :
    binaryPredBits (encodeNat n) = encodeNat (Nat.pred n) := by
  unfold encodeNat
  rw [binaryPredBits_encodeNum]
  apply congrArg encodeNum
  exact Num.to_nat_inj.mp (by simp [Num.pred_to_nat])

private theorem binaryPredBits_length_le (bits : List Bool) :
    (binaryPredBits bits).length ≤ bits.length := by
  induction bits with
  | nil => simp [binaryPredBits]
  | cons bit bits ih =>
      cases bit with
      | false => simp [binaryPredBits, ih]
      | true =>
          cases bits <;> simp [binaryPredBits]

/-- Input, reversal work, and canonical output stacks for binary
predecessor. -/
inductive PredStack
  | input
  | work
  | output
  deriving DecidableEq, Fintype

/-- Borrow propagation, leading-zero inspection, suffix copy, and output
reversal phases. -/
inductive PredLabel
  | borrow
  | check
  | copy
  | reverse
  deriving DecidableEq, Fintype

/-- Finite control remembers the most recently popped bit. -/
structure PredState where
  bit : Option Bool
  deriving DecidableEq, Fintype

private def predInitialState : PredState :=
  ⟨none⟩

private def predPoppedBit (_state : PredState) (bit : Option Bool) : PredState :=
  ⟨bit⟩

private def predBitPresent : PredState → Bool
  | ⟨some _⟩ => true
  | _ => false

private def predBitTrue : PredState → Bool
  | ⟨some true⟩ => true
  | _ => false

private def predHeldBit : PredState → Bool
  | ⟨some bit⟩ => bit
  | _ => false

private def PredAlphabet (_index : PredStack) : Type := Bool

/-- A finite three-stack predecessor program for least-significant-bit-first
binary words.  The `check` phase suppresses the high zero that would otherwise
be emitted when decrementing a power of two. -/
def binaryPredProgram :
    PredLabel → TM2.Stmt PredAlphabet PredLabel PredState
  | .borrow =>
      .pop .input predPoppedBit <|
        .branch predBitPresent
          (.branch predBitTrue
            (.goto (fun _ => .check))
            (.push .work (fun _ => true) <|
              .goto (fun _ => .borrow)))
          (.goto (fun _ => .reverse))
  | .check =>
      .pop .input predPoppedBit <|
        .branch predBitPresent
          (.push .work (fun _ => false) <|
            .push .work predHeldBit <|
              .goto (fun _ => .copy))
          (.goto (fun _ => .reverse))
  | .copy =>
      .pop .input predPoppedBit <|
        .branch predBitPresent
          (.push .work predHeldBit <|
            .goto (fun _ => .copy))
          (.goto (fun _ => .reverse))
  | .reverse =>
      .pop .work predPoppedBit <|
        .branch predBitPresent
          (.push .output predHeldBit <|
            .goto (fun _ => .reverse))
          .halt

/-- Concrete finite machine computing saturated binary predecessor. -/
def binaryPredComputer : FinTM2 where
  K := PredStack
  k₀ := .input
  k₁ := .output
  Γ := PredAlphabet
  Λ := PredLabel
  main := .borrow
  σ := PredState
  initialState := predInitialState
  Γk₀Fin := Bool.fintype
  m := binaryPredProgram

private def predStackContents
    (input work output : List Bool) :
    (index : PredStack) → List (PredAlphabet index)
  | .input => input
  | .work => work
  | .output => output

private def predCfg (label : Option PredLabel) (state : PredState)
    (input work output : List Bool) : binaryPredComputer.Cfg where
  l := label
  var := state
  stk := predStackContents input work output

private theorem pred_step_borrow_nil (work output : List Bool)
    (state : PredState) :
    binaryPredComputer.step
        (predCfg (some .borrow) state [] work output) =
      some (predCfg (some .reverse) predInitialState [] work output) := by
  simp [binaryPredComputer, FinTM2.step, predCfg, binaryPredProgram,
    predStackContents, PredAlphabet, predPoppedBit, predBitPresent,
    predInitialState, Function.update]

private theorem pred_step_borrow_false (bits work output : List Bool)
    (state : PredState) :
    binaryPredComputer.step
        (predCfg (some .borrow) state (false :: bits) work output) =
      some (predCfg (some .borrow) ⟨some false⟩ bits
        (true :: work) output) := by
  simp [binaryPredComputer, FinTM2.step, predCfg, binaryPredProgram,
    predStackContents, PredAlphabet, predPoppedBit, predBitPresent,
    predBitTrue, Function.update]
  funext index
  cases index <;> rfl

private theorem pred_step_borrow_true (bits work output : List Bool)
    (state : PredState) :
    binaryPredComputer.step
        (predCfg (some .borrow) state (true :: bits) work output) =
      some (predCfg (some .check) ⟨some true⟩ bits work output) := by
  simp [binaryPredComputer, FinTM2.step, predCfg, binaryPredProgram,
    predStackContents, PredAlphabet, predPoppedBit, predBitPresent,
    predBitTrue, Function.update]
  funext index
  cases index <;> rfl

private theorem pred_step_check_nil (work output : List Bool)
    (state : PredState) :
    binaryPredComputer.step
        (predCfg (some .check) state [] work output) =
      some (predCfg (some .reverse) predInitialState [] work output) := by
  simp [binaryPredComputer, FinTM2.step, predCfg, binaryPredProgram,
    predStackContents, PredAlphabet, predPoppedBit, predBitPresent,
    predInitialState, Function.update]

private theorem pred_step_check_cons (bit : Bool)
    (bits work output : List Bool) (state : PredState) :
    binaryPredComputer.step
        (predCfg (some .check) state (bit :: bits) work output) =
      some (predCfg (some .copy) ⟨some bit⟩ bits
        (bit :: false :: work) output) := by
  cases bit <;>
    simp [binaryPredComputer, FinTM2.step, predCfg, binaryPredProgram,
      predStackContents, PredAlphabet, predPoppedBit, predBitPresent,
      predHeldBit, Function.update] <;>
    (funext index; cases index <;> rfl)

private theorem pred_step_copy_nil (work output : List Bool)
    (state : PredState) :
    binaryPredComputer.step
        (predCfg (some .copy) state [] work output) =
      some (predCfg (some .reverse) predInitialState [] work output) := by
  simp [binaryPredComputer, FinTM2.step, predCfg, binaryPredProgram,
    predStackContents, PredAlphabet, predPoppedBit, predBitPresent,
    predInitialState, Function.update]

private theorem pred_step_copy_cons (bit : Bool)
    (bits work output : List Bool) (state : PredState) :
    binaryPredComputer.step
        (predCfg (some .copy) state (bit :: bits) work output) =
      some (predCfg (some .copy) ⟨some bit⟩ bits
        (bit :: work) output) := by
  cases bit <;>
    simp [binaryPredComputer, FinTM2.step, predCfg, binaryPredProgram,
      predStackContents, PredAlphabet, predPoppedBit, predBitPresent,
      predHeldBit, Function.update] <;>
    (funext index; cases index <;> rfl)

private theorem pred_step_reverse_nil (output : List Bool)
    (state : PredState) :
    binaryPredComputer.step
        (predCfg (some .reverse) state [] [] output) =
      some (predCfg none predInitialState [] [] output) := by
  simp [binaryPredComputer, FinTM2.step, predCfg, binaryPredProgram,
    predStackContents, PredAlphabet, predPoppedBit, predBitPresent,
    predInitialState, Function.update]

private theorem pred_step_reverse_cons (bit : Bool)
    (work output : List Bool) (state : PredState) :
    binaryPredComputer.step
        (predCfg (some .reverse) state [] (bit :: work) output) =
      some (predCfg (some .reverse) ⟨some bit⟩ [] work
        (bit :: output)) := by
  cases bit <;>
    simp [binaryPredComputer, FinTM2.step, predCfg, binaryPredProgram,
      predStackContents, PredAlphabet, predPoppedBit, predBitPresent,
      predHeldBit, Function.update] <;>
    (funext index; cases index <;> rfl)

private def predEvalsToInTimeOne
    {start finish : binaryPredComputer.Cfg}
    (hstep : binaryPredComputer.step start = some finish) :
    EvalsToInTime binaryPredComputer.step start (some finish) 1 where
  steps := 1
  evals_in_steps := by
    simpa [Function.iterate_one] using hstep
  steps_le_m := Nat.le_refl 1

private def pred_copy_evals (bits work output : List Bool)
    (state : PredState) :
    EvalsToInTime binaryPredComputer.step
      (predCfg (some .copy) state bits work output)
      (some (predCfg (some .reverse) predInitialState []
        (bits.reverse ++ work) output))
      (bits.length + 1) := by
  induction bits generalizing work state with
  | nil =>
      simpa using predEvalsToInTimeOne
        (pred_step_copy_nil work output state)
  | cons bit bits ih =>
      let middle := predCfg (some .copy) ⟨some bit⟩ bits
        (bit :: work) output
      have hone : EvalsToInTime binaryPredComputer.step
          (predCfg (some .copy) state (bit :: bits) work output)
          (some middle) 1 :=
        predEvalsToInTimeOne (by
          simpa [middle] using pred_step_copy_cons bit bits work output state)
      have hrest := ih (bit :: work) ⟨some bit⟩
      have hall := EvalsToInTime.trans binaryPredComputer.step
        1 (bits.length + 1)
        (predCfg (some .copy) state (bit :: bits) work output)
        middle
        (some (predCfg (some .reverse) predInitialState []
          ((bit :: bits).reverse ++ work) output))
        hone
        (by simpa [middle, List.reverse_cons, List.append_assoc] using hrest)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hall

private def predPrepareTime : List Bool → ℕ
  | [] => 1
  | false :: bits => 1 + predPrepareTime bits
  | true :: [] => 2
  | true :: _bit :: bits => 2 + (bits.length + 1)

private def pred_borrow_evals (bits work output : List Bool)
    (state : PredState) :
    EvalsToInTime binaryPredComputer.step
      (predCfg (some .borrow) state bits work output)
      (some (predCfg (some .reverse) predInitialState []
        ((binaryPredBits bits).reverse ++ work) output))
      (predPrepareTime bits) := by
  induction bits generalizing work state with
  | nil =>
      simpa [predPrepareTime, binaryPredBits] using predEvalsToInTimeOne
        (pred_step_borrow_nil work output state)
  | cons bit bits ih =>
      cases bit with
      | false =>
          let middle := predCfg (some .borrow) ⟨some false⟩ bits
            (true :: work) output
          have hone : EvalsToInTime binaryPredComputer.step
              (predCfg (some .borrow) state (false :: bits) work output)
              (some middle) 1 :=
            predEvalsToInTimeOne (by
              simpa [middle] using
                pred_step_borrow_false bits work output state)
          have hrest := ih (true :: work) ⟨some false⟩
          have hall := EvalsToInTime.trans binaryPredComputer.step
            1 (predPrepareTime bits)
            (predCfg (some .borrow) state (false :: bits) work output)
            middle
            (some (predCfg (some .reverse) predInitialState []
              ((binaryPredBits (false :: bits)).reverse ++ work) output))
            hone
            (by
              simpa [middle, binaryPredBits, List.reverse_cons,
                List.append_assoc] using hrest)
          simpa [predPrepareTime, Nat.add_comm] using hall
      | true =>
          cases bits with
          | nil =>
              let middle := predCfg (some .check) ⟨some true⟩ [] work output
              have hone : EvalsToInTime binaryPredComputer.step
                  (predCfg (some .borrow) state [true] work output)
                  (some middle) 1 :=
                predEvalsToInTimeOne (by
                  simpa [middle] using
                    pred_step_borrow_true [] work output state)
              have htwo := predEvalsToInTimeOne
                (pred_step_check_nil work output ⟨some true⟩)
              have hall := EvalsToInTime.trans binaryPredComputer.step
                1 1
                (predCfg (some .borrow) state [true] work output)
                middle
                (some (predCfg (some .reverse) predInitialState []
                  work output))
                hone
                (by simpa [middle] using htwo)
              simpa [predPrepareTime, binaryPredBits] using hall
          | cons next bits =>
              let afterBorrow := predCfg (some .check) ⟨some true⟩
                (next :: bits) work output
              have hborrow : EvalsToInTime binaryPredComputer.step
                  (predCfg (some .borrow) state
                    (true :: next :: bits) work output)
                  (some afterBorrow) 1 :=
                predEvalsToInTimeOne (by
                  simpa [afterBorrow] using
                    pred_step_borrow_true (next :: bits) work output state)
              let afterCheck := predCfg (some .copy) ⟨some next⟩ bits
                (next :: false :: work) output
              have hcheck : EvalsToInTime binaryPredComputer.step
                  afterBorrow (some afterCheck) 1 :=
                predEvalsToInTimeOne (by
                  simpa [afterBorrow, afterCheck] using
                    pred_step_check_cons next bits work output ⟨some true⟩)
              have hfirst := EvalsToInTime.trans binaryPredComputer.step
                1 1
                (predCfg (some .borrow) state
                  (true :: next :: bits) work output)
                afterBorrow
                (some afterCheck)
                hborrow hcheck
              have hcopy := pred_copy_evals bits
                (next :: false :: work) output ⟨some next⟩
              have hall := EvalsToInTime.trans binaryPredComputer.step
                2 (bits.length + 1)
                (predCfg (some .borrow) state
                  (true :: next :: bits) work output)
                afterCheck
                (some (predCfg (some .reverse) predInitialState []
                  ((binaryPredBits (true :: next :: bits)).reverse ++ work)
                  output))
                (by simpa using hfirst)
                (by
                  simpa [afterCheck, binaryPredBits, List.reverse_cons,
                    List.append_assoc] using hcopy)
              simpa [predPrepareTime, Nat.add_assoc, Nat.add_comm,
                Nat.add_left_comm] using hall

private theorem predPrepareTime_le (bits : List Bool) :
    predPrepareTime bits ≤ bits.length + 2 := by
  induction bits with
  | nil => simp [predPrepareTime]
  | cons bit bits ih =>
      cases bit with
      | false =>
          simp only [predPrepareTime, List.length_cons]
          omega
      | true =>
          cases bits with
          | nil => simp [predPrepareTime]
          | cons head tail =>
              simp only [predPrepareTime, List.length_cons]
              omega

private def pred_reverse_evals (work output : List Bool)
    (state : PredState) :
    EvalsToInTime binaryPredComputer.step
      (predCfg (some .reverse) state [] work output)
      (some (predCfg none predInitialState [] []
        (work.reverse ++ output)))
      (work.length + 1) := by
  induction work generalizing output state with
  | nil =>
      simpa using predEvalsToInTimeOne
        (pred_step_reverse_nil output state)
  | cons bit work ih =>
      let middle := predCfg (some .reverse) ⟨some bit⟩ [] work
        (bit :: output)
      have hone : EvalsToInTime binaryPredComputer.step
          (predCfg (some .reverse) state [] (bit :: work) output)
          (some middle) 1 :=
        predEvalsToInTimeOne (by
          simpa [middle] using
            pred_step_reverse_cons bit work output state)
      have hrest := ih (bit :: output) ⟨some bit⟩
      have hall := EvalsToInTime.trans binaryPredComputer.step
        1 (work.length + 1)
        (predCfg (some .reverse) state [] (bit :: work) output)
        middle
        (some (predCfg none predInitialState [] []
          ((bit :: work).reverse ++ output)))
        hone
        (by simpa [middle, List.reverse_cons, List.append_assoc] using hrest)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hall

private theorem pred_initList_eq_cfg (input : List Bool) :
    initList binaryPredComputer input =
      predCfg (some .borrow) predInitialState input [] [] := by
  unfold initList predCfg
  congr
  funext index
  cases index <;> rfl

private theorem pred_haltList_eq_cfg (output : List Bool) :
    haltList binaryPredComputer output =
      predCfg none predInitialState [] [] output := by
  unfold haltList predCfg
  congr
  funext index
  cases index <;> rfl

/-- Binary predecessor runs in at most `2s + 3` steps on an arbitrary bit
word of length `s` and emits `binaryPredBits` of that word. -/
def binaryPred_outputsInTime (bits : List Bool) :
    TM2OutputsInTime binaryPredComputer bits
      (some (binaryPredBits bits)) (2 * bits.length + 3) := by
  have hborrow := pred_borrow_evals bits [] [] predInitialState
  have hreverse := pred_reverse_evals
    (binaryPredBits bits).reverse [] predInitialState
  have hall := EvalsToInTime.trans binaryPredComputer.step
    (predPrepareTime bits) ((binaryPredBits bits).reverse.length + 1)
    (predCfg (some .borrow) predInitialState bits [] [])
    (predCfg (some .reverse) predInitialState []
      (binaryPredBits bits).reverse [])
    (some (predCfg none predInitialState [] [] (binaryPredBits bits)))
    (by simpa using hborrow)
    (by simpa using hreverse)
  have hprepare := predPrepareTime_le bits
  have hlength := binaryPredBits_length_le bits
  have hmono : EvalsToInTime binaryPredComputer.step
      (predCfg (some .borrow) predInitialState bits [] [])
      (some (predCfg none predInitialState [] [] (binaryPredBits bits)))
      (2 * bits.length + 3) :=
    evalsToInTimeMono hall (by
      simp only [List.length_reverse]
      omega)
  rw [TM2OutputsInTime, pred_initList_eq_cfg]
  simp only [Option.map_some]
  rw [pred_haltList_eq_cfg]
  exact hmono

/-- A genuine linear-time finite-machine witness for saturated predecessor on
mathlib's standard binary natural-number encoding. -/
noncomputable def binaryPredComputableInPolyTime :
    @TM2ComputableInPolyTime ℕ ℕ finEncodingNatBool finEncodingNatBool
      Nat.pred where
  tm := binaryPredComputer
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := 2 * Polynomial.X + 3
  outputsFun n := by
    simpa [finEncodingNatBool, Equiv.refl, binaryPredBits_encodeNat,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_natCast,
      Polynomial.eval_X] using binaryPred_outputsInTime (encodeNat n)

/-! ## Binary comparison

Bounded enumeration and the eventual prime scan need a checked comparison
primitive. Two canonical least-significant-bit-first words are aligned into a
finite paired alphabet. Missing bits are represented by `none`; this preserves
both words exactly while letting one finite-control pass visit corresponding
bit positions from least to most significant.
-/

namespace BinaryNatPair

/-- Align two bit strings, padding only the exhausted side with `none`. -/
def zipBits : List Bool → List Bool → List (Option Bool × Option Bool)
  | [], [] => []
  | left :: lefts, [] => (some left, none) :: zipBits lefts []
  | [], right :: rights => (none, some right) :: zipBits [] rights
  | left :: lefts, right :: rights =>
      (some left, some right) :: zipBits lefts rights

/-- Recover the left bit string from an aligned pair stream. -/
def leftBits : List (Option Bool × Option Bool) → List Bool
  | [] => []
  | (none, _) :: pairs => leftBits pairs
  | (some bit, _) :: pairs => bit :: leftBits pairs

/-- Recover the right bit string from an aligned pair stream. -/
def rightBits : List (Option Bool × Option Bool) → List Bool
  | [] => []
  | (_, none) :: pairs => rightBits pairs
  | (_, some bit) :: pairs => bit :: rightBits pairs

@[simp]
theorem leftBits_zipBits (left right : List Bool) :
    leftBits (zipBits left right) = left := by
  induction left generalizing right with
  | nil =>
      induction right with
      | nil => simp [zipBits, leftBits]
      | cons right rights ih =>
          simp [zipBits, leftBits, ih]
  | cons left lefts ih =>
      cases right with
      | nil => simp [zipBits, leftBits, ih]
      | cons right rights => simp [zipBits, leftBits, ih]

@[simp]
theorem rightBits_zipBits (left right : List Bool) :
    rightBits (zipBits left right) = right := by
  induction left generalizing right with
  | nil =>
      induction right with
      | nil => simp [zipBits, rightBits]
      | cons right rights ih =>
          simp [zipBits, rightBits, ih]
  | cons left lefts ih =>
      cases right with
      | nil => simp [zipBits, rightBits, ih]
      | cons right rights => simp [zipBits, rightBits, ih]

/-- Canonical paired binary encoding of two naturals. -/
def encode (pair : ℕ × ℕ) : List (Option Bool × Option Bool) :=
  zipBits (encodeNat pair.1) (encodeNat pair.2)

/-- Decode both projections of an aligned bit stream. -/
def decode (pairs : List (Option Bool × Option Bool)) : Option (ℕ × ℕ) :=
  some (decodeNat (leftBits pairs), decodeNat (rightBits pairs))

@[simp]
theorem decode_encode (pair : ℕ × ℕ) : decode (encode pair) = some pair := by
  rcases pair with ⟨left, right⟩
  simp [decode, encode]

/-- Checked finite encoding of a pair of canonical binary naturals. -/
def finEncoding : FinEncoding (ℕ × ℕ) where
  Γ := Option Bool × Option Bool
  encode := encode
  decode := decode
  decode_encode := decode_encode
  ΓFin := inferInstance

end BinaryNatPair

/-- Update a less-than-or-equal decision with one more significant aligned
bit pair. A missing high bit makes that side shorter; unequal present bits
replace the decision made by all less significant positions. -/
def binaryLEUpdate (current : Bool) : Option Bool → Option Bool → Bool
  | none, none => current
  | none, some _ => true
  | some _, none => false
  | some false, some true => true
  | some true, some false => false
  | some false, some false => current
  | some true, some true => current

/-- Comparison directly on two least-significant-bit-first words. -/
def binaryLEBitsAux : Bool → List Bool → List Bool → Bool
  | current, [], [] => current
  | current, left :: lefts, [] =>
      binaryLEBitsAux (binaryLEUpdate current (some left) none) lefts []
  | current, [], right :: rights =>
      binaryLEBitsAux (binaryLEUpdate current none (some right)) [] rights
  | current, left :: lefts, right :: rights =>
      binaryLEBitsAux
        (binaryLEUpdate current (some left) (some right)) lefts rights

/-- Fold the same comparison update over the paired wire representation. -/
def binaryLEPairsAux : Bool → List (Option Bool × Option Bool) → Bool
  | current, [] => current
  | current, pair :: pairs =>
      binaryLEPairsAux (binaryLEUpdate current pair.1 pair.2) pairs

@[simp]
theorem binaryLEPairsAux_zipBits
    (current : Bool) (left right : List Bool) :
    binaryLEPairsAux current (BinaryNatPair.zipBits left right) =
      binaryLEBitsAux current left right := by
  induction left generalizing current right with
  | nil =>
      induction right generalizing current with
      | nil => simp [BinaryNatPair.zipBits, binaryLEPairsAux,
          binaryLEBitsAux]
      | cons right rights ih =>
          simp [BinaryNatPair.zipBits, binaryLEPairsAux,
            binaryLEBitsAux, ih]
  | cons left lefts ih =>
      cases right with
      | nil =>
          simp [BinaryNatPair.zipBits, binaryLEPairsAux,
            binaryLEBitsAux, ih]
      | cons right rights =>
          simp [BinaryNatPair.zipBits, binaryLEPairsAux,
            binaryLEBitsAux, ih]

/-- Translate a three-way comparison into a decision, retaining `current`
only when all inspected higher bits are equal. -/
def orderingLEResult (current : Bool) : Ordering → Bool
  | .lt => true
  | .eq => current
  | .gt => false

private theorem binaryLEBitsAux_true_left_nil (bits : List Bool) :
    binaryLEBitsAux true [] bits = true := by
  induction bits with
  | nil => simp [binaryLEBitsAux]
  | cons bit bits ih =>
      cases bit <;> simpa [binaryLEBitsAux, binaryLEUpdate] using ih

private theorem binaryLEBitsAux_false_right_nil (bits : List Bool) :
    binaryLEBitsAux false bits [] = false := by
  induction bits with
  | nil => simp [binaryLEBitsAux]
  | cons bit bits ih =>
      cases bit <;> simpa [binaryLEBitsAux, binaryLEUpdate] using ih

private theorem binaryLEBitsAux_left_nonempty
    (current bit : Bool) (bits : List Bool) :
    binaryLEBitsAux current [] (bit :: bits) = true := by
  cases bit <;>
    simpa [binaryLEBitsAux, binaryLEUpdate] using
      binaryLEBitsAux_true_left_nil bits

private theorem binaryLEBitsAux_right_nonempty
    (current bit : Bool) (bits : List Bool) :
    binaryLEBitsAux current (bit :: bits) [] = false := by
  cases bit <;>
    simpa [binaryLEBitsAux, binaryLEUpdate] using
      binaryLEBitsAux_false_right_nil bits

private theorem binaryLEBitsAux_left_of_nonempty
    (current : Bool) {bits : List Bool} (hbits : bits ≠ []) :
    binaryLEBitsAux current [] bits = true := by
  cases bits with
  | nil => exact (hbits rfl).elim
  | cons bit bits => exact binaryLEBitsAux_left_nonempty current bit bits

private theorem binaryLEBitsAux_right_of_nonempty
    (current : Bool) {bits : List Bool} (hbits : bits ≠ []) :
    binaryLEBitsAux current bits [] = false := by
  cases bits with
  | nil => exact (hbits rfl).elim
  | cons bit bits => exact binaryLEBitsAux_right_nonempty current bit bits

private theorem binaryLEBitsAux_encodePosNum
    (current : Bool) (left right : PosNum) :
    binaryLEBitsAux current (encodePosNum left) (encodePosNum right) =
      orderingLEResult current (PosNum.cmp left right) := by
  induction left generalizing current right with
  | one =>
      cases right with
      | one => simp [encodePosNum, binaryLEBitsAux, binaryLEUpdate,
          orderingLEResult, PosNum.cmp]
      | bit1 right =>
          simp only [encodePosNum, binaryLEBitsAux, binaryLEUpdate,
            orderingLEResult, PosNum.cmp]
          exact binaryLEBitsAux_left_of_nonempty current
            (encodePosNum_nonempty right)
      | bit0 right =>
          simp only [encodePosNum, binaryLEBitsAux, binaryLEUpdate,
            orderingLEResult, PosNum.cmp]
          exact binaryLEBitsAux_left_of_nonempty false
            (encodePosNum_nonempty right)
  | bit1 left ih =>
      cases right with
      | one =>
          simp only [encodePosNum, binaryLEBitsAux, binaryLEUpdate,
            orderingLEResult, PosNum.cmp]
          exact binaryLEBitsAux_right_of_nonempty current
            (encodePosNum_nonempty left)
      | bit1 right =>
          simpa [encodePosNum, binaryLEBitsAux, binaryLEUpdate,
            PosNum.cmp] using ih current right
      | bit0 right =>
          have h := ih (binaryLEUpdate current (some true) (some false)) right
          cases hcmp : PosNum.cmp left right <;>
            simp [encodePosNum, binaryLEBitsAux, binaryLEUpdate,
              PosNum.cmp, hcmp, orderingLEResult] at h ⊢ <;>
            exact h
  | bit0 left ih =>
      cases right with
      | one =>
          simp only [encodePosNum, binaryLEBitsAux, binaryLEUpdate,
            orderingLEResult, PosNum.cmp]
          exact binaryLEBitsAux_right_of_nonempty true
            (encodePosNum_nonempty left)
      | bit1 right =>
          have h := ih (binaryLEUpdate current (some false) (some true)) right
          cases hcmp : PosNum.cmp left right <;>
            simp [encodePosNum, binaryLEBitsAux, binaryLEUpdate,
              PosNum.cmp, hcmp, orderingLEResult] at h ⊢ <;>
            exact h
      | bit0 right =>
          simpa [encodePosNum, binaryLEBitsAux, binaryLEUpdate,
            PosNum.cmp] using ih current right

private theorem orderingLEResult_cmp_true (left right : PosNum) :
    orderingLEResult true (PosNum.cmp left right) =
      decide ((left : ℕ) ≤ (right : ℕ)) := by
  have hcmpNat := PosNum.cmp_to_nat left right
  cases hcmp : PosNum.cmp left right with
  | lt =>
      simp [hcmp] at hcmpNat
      have hlePos : left ≤ right := hcmpNat.le
      have hle : (left : ℕ) ≤ (right : ℕ) :=
        PosNum.le_to_nat.mpr hlePos
      simp [orderingLEResult, hle]
  | eq =>
      simp [hcmp] at hcmpNat
      subst right
      simp [orderingLEResult]
  | gt =>
      simp [hcmp] at hcmpNat
      have hlt : (right : ℕ) < (left : ℕ) :=
        PosNum.lt_to_nat.mpr hcmpNat
      have hnle : ¬(left : ℕ) ≤ (right : ℕ) := Nat.not_le_of_gt hlt
      simp [orderingLEResult, hnle]

/-- Bit comparison agrees with natural-number comparison on canonical binary
encodings, including zero on either side. -/
@[simp]
theorem binaryLEBitsAux_encodeNat (left right : ℕ) :
    binaryLEBitsAux true (encodeNat left) (encodeNat right) =
      decide (left ≤ right) := by
  unfold encodeNat
  cases hleft : (left : Num) with
  | zero =>
      cases hright : (right : Num) with
      | zero =>
          have hleftNat := congrArg (fun n : Num => (n : ℕ)) hleft
          have hrightNat := congrArg (fun n : Num => (n : ℕ)) hright
          simp at hleftNat hrightNat
          simp [hleftNat, hrightNat, encodeNum, binaryLEBitsAux]
      | pos rightPos =>
          have hleftNat := congrArg (fun n : Num => (n : ℕ)) hleft
          have hrightNat := congrArg (fun n : Num => (n : ℕ)) hright
          simp at hleftNat hrightNat
          have hcompare :
              binaryLEBitsAux true [] (encodePosNum rightPos) = true :=
            binaryLEBitsAux_left_of_nonempty true
              (encodePosNum_nonempty rightPos)
          simp [hleftNat, hrightNat, encodeNum, hcompare]
  | pos leftPos =>
      cases hright : (right : Num) with
      | zero =>
          have hleftNat := congrArg (fun n : Num => (n : ℕ)) hleft
          have hrightNat := congrArg (fun n : Num => (n : ℕ)) hright
          simp at hleftNat hrightNat
          have hleftPos : 0 < (leftPos : ℕ) := PosNum.to_nat_pos leftPos
          have hcompare :
              binaryLEBitsAux true (encodePosNum leftPos) [] = false :=
            binaryLEBitsAux_right_of_nonempty true
              (encodePosNum_nonempty leftPos)
          simp [hleftNat, hrightNat, encodeNum, hcompare,
            Nat.ne_of_gt hleftPos]
      | pos rightPos =>
          have hleftNat := congrArg (fun n : Num => (n : ℕ)) hleft
          have hrightNat := congrArg (fun n : Num => (n : ℕ)) hright
          simp at hleftNat hrightNat
          rw [show encodeNum (Num.pos leftPos) = encodePosNum leftPos by rfl,
            show encodeNum (Num.pos rightPos) = encodePosNum rightPos by rfl,
            binaryLEBitsAux_encodePosNum,
            orderingLEResult_cmp_true]
          simp [hleftNat, hrightNat]

/-- Input and single-bit output stacks for binary comparison. -/
inductive CompareStack
  | input
  | output
  deriving DecidableEq, Fintype

/-- The comparison program needs one scanning label. -/
inductive CompareLabel
  | scan
  deriving DecidableEq, Fintype

/-- Finite control stores the last aligned pair and the decision from all bit
positions inspected so far. -/
structure CompareState where
  pair : Option (Option Bool × Option Bool)
  result : Bool
  deriving DecidableEq, Fintype

private def compareInitialState : CompareState :=
  ⟨none, true⟩

private def comparePoppedPair
    (state : CompareState)
    (pair : Option (Option Bool × Option Bool)) : CompareState :=
  match pair with
  | none => { state with pair := none }
  | some bits =>
      ⟨some bits, binaryLEUpdate state.result bits.1 bits.2⟩

private def comparePairPresent : CompareState → Bool
  | ⟨some _, _⟩ => true
  | _ => false

private def compareResult (state : CompareState) : Bool :=
  state.result

private def CompareAlphabet : CompareStack → Type
  | .input => Option Bool × Option Bool
  | .output => Bool

/-- One-pass finite program for aligned binary comparison. -/
def binaryLEProgram :
    CompareLabel → TM2.Stmt CompareAlphabet CompareLabel CompareState
  | .scan =>
      .pop .input comparePoppedPair <|
        .branch comparePairPresent
          (.goto (fun _ => .scan))
          (.push .output compareResult <|
            .load (fun _ => compareInitialState) .halt)

/-- Concrete finite machine deciding less-than-or-equal on paired binary
naturals. -/
def binaryLEComputer : FinTM2 where
  K := CompareStack
  k₀ := .input
  k₁ := .output
  Γ := CompareAlphabet
  Λ := CompareLabel
  main := .scan
  σ := CompareState
  initialState := compareInitialState
  Γk₀Fin := by
    change Fintype (Option Bool × Option Bool)
    infer_instance
  m := binaryLEProgram

private def compareStackContents
    (input : List (Option Bool × Option Bool)) (output : List Bool) :
    (index : CompareStack) → List (CompareAlphabet index)
  | .input => input
  | .output => output

private def compareCfg (label : Option CompareLabel) (state : CompareState)
    (input : List (Option Bool × Option Bool)) (output : List Bool) :
    binaryLEComputer.Cfg where
  l := label
  var := state
  stk := compareStackContents input output

private theorem compare_step_cons
    (pair : Option Bool × Option Bool)
    (pairs : List (Option Bool × Option Bool)) (output : List Bool)
    (state : CompareState) :
    binaryLEComputer.step
        (compareCfg (some .scan) state (pair :: pairs) output) =
      some (compareCfg (some .scan)
        (comparePoppedPair state (some pair)) pairs output) := by
  rcases pair with ⟨left, right⟩
  rcases left with _ | left <;> rcases right with _ | right <;>
    simp [binaryLEComputer, FinTM2.step, compareCfg, binaryLEProgram,
      compareStackContents, CompareAlphabet, comparePoppedPair,
      comparePairPresent, binaryLEUpdate, Function.update] <;>
    (funext index; cases index <;> rfl)

private theorem compare_step_nil (output : List Bool)
    (state : CompareState) :
    binaryLEComputer.step
        (compareCfg (some .scan) state [] output) =
      some (compareCfg none compareInitialState []
        (state.result :: output)) := by
  rcases state with ⟨pair, result⟩
  simp [binaryLEComputer, FinTM2.step, compareCfg, binaryLEProgram,
    compareStackContents, CompareAlphabet, comparePoppedPair,
    comparePairPresent, compareResult, compareInitialState,
    Function.update]
  funext index
  cases index <;> rfl

private def compareEvalsToInTimeOne
    {start finish : binaryLEComputer.Cfg}
    (hstep : binaryLEComputer.step start = some finish) :
    EvalsToInTime binaryLEComputer.step start (some finish) 1 where
  steps := 1
  evals_in_steps := by
    simpa [Function.iterate_one] using hstep
  steps_le_m := Nat.le_refl 1

private def compare_scan_evals
    (pairs : List (Option Bool × Option Bool)) (output : List Bool)
    (state : CompareState) :
    EvalsToInTime binaryLEComputer.step
      (compareCfg (some .scan) state pairs output)
      (some (compareCfg none compareInitialState []
        (binaryLEPairsAux state.result pairs :: output)))
      (pairs.length + 1) := by
  induction pairs generalizing state with
  | nil =>
      simpa [binaryLEPairsAux] using compareEvalsToInTimeOne
        (compare_step_nil output state)
  | cons pair pairs ih =>
      let middle := compareCfg (some .scan)
        (comparePoppedPair state (some pair)) pairs output
      have hone : EvalsToInTime binaryLEComputer.step
          (compareCfg (some .scan) state (pair :: pairs) output)
          (some middle) 1 :=
        compareEvalsToInTimeOne (by
          simpa [middle] using compare_step_cons pair pairs output state)
      have hrest := ih (comparePoppedPair state (some pair))
      have htrans := EvalsToInTime.trans binaryLEComputer.step
        1 (pairs.length + 1)
        (compareCfg (some .scan) state (pair :: pairs) output)
        middle
        (some (compareCfg none compareInitialState []
          (binaryLEPairsAux state.result (pair :: pairs) :: output)))
        hone
        (by
          simpa [middle, comparePoppedPair, binaryLEPairsAux] using hrest)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htrans

private theorem compare_initList_eq_cfg
    (input : List (Option Bool × Option Bool)) :
    initList binaryLEComputer input =
      compareCfg (some .scan) compareInitialState input [] := by
  unfold initList compareCfg
  congr
  funext index
  cases index <;> rfl

private theorem compare_haltList_eq_cfg (output : List Bool) :
    haltList binaryLEComputer output =
      compareCfg none compareInitialState [] output := by
  unfold haltList compareCfg
  congr
  funext index
  cases index <;> rfl

/-- Binary comparison runs in exactly one scan plus the final output step. -/
def binaryLE_outputsInTime (pair : ℕ × ℕ) :
    TM2OutputsInTime binaryLEComputer (BinaryNatPair.encode pair)
      (some [decide (pair.1 ≤ pair.2)])
      ((BinaryNatPair.encode pair).length + 1) := by
  have hrun := compare_scan_evals (BinaryNatPair.encode pair) []
    compareInitialState
  rw [TM2OutputsInTime, compare_initList_eq_cfg]
  simp only [Option.map_some]
  rw [compare_haltList_eq_cfg]
  rcases pair with ⟨left, right⟩
  simpa [BinaryNatPair.encode, compareInitialState] using hrun

/-- A genuine linear-time finite-machine witness deciding comparison on two
canonical binary naturals. -/
noncomputable def binaryLEComputableInPolyTime :
    @TM2ComputableInPolyTime (ℕ × ℕ) Bool BinaryNatPair.finEncoding
      finEncodingBoolBool (fun pair => decide (pair.1 ≤ pair.2)) where
  tm := binaryLEComputer
  inputAlphabet := Equiv.refl (Option Bool × Option Bool)
  outputAlphabet := Equiv.refl Bool
  time := Polynomial.X + 1
  outputsFun pair := by
    simpa [BinaryNatPair.finEncoding, finEncodingBoolBool, encodeBool,
      Equiv.refl, Polynomial.eval_add, Polynomial.eval_one,
      Polynomial.eval_X] using binaryLE_outputsInTime pair

/-! ## Binary addition

The Bertrand interval has upper endpoint `2 * q`, and bounded candidate
enumeration repeatedly advances binary values.  The following ripple-carry
pass complements successor and comparison with checked addition on the same
aligned-pair encoding.  Bits are visited least-significant first, so finite
control only needs the current carry.
-/

/-- One ripple-carry addition step.  The first component is the emitted bit;
the second is the carry into the next bit position. -/
def binaryAddStep (carry : Bool) (left right : Option Bool) : Bool × Bool :=
  match carry, left, right with
  | false, none, none => (false, false)
  | false, none, some false => (false, false)
  | false, some false, none => (false, false)
  | false, some false, some false => (false, false)
  | false, none, some true => (true, false)
  | false, some true, none => (true, false)
  | false, some false, some true => (true, false)
  | false, some true, some false => (true, false)
  | false, some true, some true => (false, true)
  | true, none, none => (true, false)
  | true, none, some false => (true, false)
  | true, some false, none => (true, false)
  | true, some false, some false => (true, false)
  | true, none, some true => (false, true)
  | true, some true, none => (false, true)
  | true, some false, some true => (false, true)
  | true, some true, some false => (false, true)
  | true, some true, some true => (true, true)

/-- Ripple-carry addition directly on two least-significant-bit-first words. -/
def binaryAddBitsAux : Bool → List Bool → List Bool → List Bool
  | carry, [], [] => if carry then [true] else []
  | carry, left :: lefts, [] =>
      let step := binaryAddStep carry (some left) none
      step.1 :: binaryAddBitsAux step.2 lefts []
  | carry, [], right :: rights =>
      let step := binaryAddStep carry none (some right)
      step.1 :: binaryAddBitsAux step.2 [] rights
  | carry, left :: lefts, right :: rights =>
      let step := binaryAddStep carry (some left) (some right)
      step.1 :: binaryAddBitsAux step.2 lefts rights

/-- The same addition fold over the aligned pair wire representation. -/
def binaryAddPairsAux : Bool →
    List (Option Bool × Option Bool) → List Bool
  | carry, [] => if carry then [true] else []
  | carry, pair :: pairs =>
      let step := binaryAddStep carry pair.1 pair.2
      step.1 :: binaryAddPairsAux step.2 pairs

@[simp]
theorem binaryAddPairsAux_zipBits
    (carry : Bool) (left right : List Bool) :
    binaryAddPairsAux carry (BinaryNatPair.zipBits left right) =
      binaryAddBitsAux carry left right := by
  induction left generalizing carry right with
  | nil =>
      induction right generalizing carry with
      | nil => simp [BinaryNatPair.zipBits, binaryAddPairsAux,
          binaryAddBitsAux]
      | cons right rights ih =>
          simp [BinaryNatPair.zipBits, binaryAddPairsAux,
            binaryAddBitsAux, ih]
  | cons left lefts ih =>
      cases right with
      | nil =>
          simp [BinaryNatPair.zipBits, binaryAddPairsAux,
            binaryAddBitsAux, ih]
      | cons right rights =>
          simp [BinaryNatPair.zipBits, binaryAddPairsAux,
            binaryAddBitsAux, ih]

private theorem binaryAddBitsAux_false_left_nil (bits : List Bool) :
    binaryAddBitsAux false [] bits = bits := by
  induction bits with
  | nil => simp [binaryAddBitsAux]
  | cons bit bits ih =>
      cases bit <;> simp [binaryAddBitsAux, binaryAddStep, ih]

private theorem binaryAddBitsAux_false_right_nil (bits : List Bool) :
    binaryAddBitsAux false bits [] = bits := by
  induction bits with
  | nil => simp [binaryAddBitsAux]
  | cons bit bits ih =>
      cases bit <;> simp [binaryAddBitsAux, binaryAddStep, ih]

private theorem binaryAddBitsAux_true_left_nil (bits : List Bool) :
    binaryAddBitsAux true [] bits = binarySuccBits bits := by
  induction bits with
  | nil => simp [binaryAddBitsAux, binarySuccBits]
  | cons bit bits ih =>
      cases bit <;> simp [binaryAddBitsAux, binaryAddStep,
        binarySuccBits, binaryAddBitsAux_false_left_nil, ih]

private theorem binaryAddBitsAux_true_right_nil (bits : List Bool) :
    binaryAddBitsAux true bits [] = binarySuccBits bits := by
  induction bits with
  | nil => simp [binaryAddBitsAux, binarySuccBits]
  | cons bit bits ih =>
      cases bit <;> simp [binaryAddBitsAux, binaryAddStep,
        binarySuccBits, binaryAddBitsAux_false_right_nil, ih]

private theorem binaryAddBitsAux_true_eq_succ
    (left right : List Bool) :
    binaryAddBitsAux true left right =
      binarySuccBits (binaryAddBitsAux false left right) := by
  induction left generalizing right with
  | nil =>
      rw [binaryAddBitsAux_true_left_nil,
        binaryAddBitsAux_false_left_nil]
  | cons left lefts ih =>
      cases right with
      | nil =>
          rw [binaryAddBitsAux_true_right_nil,
            binaryAddBitsAux_false_right_nil]
      | cons right rights =>
          cases left <;> cases right <;>
            simp [binaryAddBitsAux, binaryAddStep, binarySuccBits, ih]

private theorem binaryAddBitsAux_encodePosNum
    (left right : PosNum) :
    binaryAddBitsAux false (encodePosNum left) (encodePosNum right) =
      encodePosNum (left + right) := by
  induction left generalizing right with
  | one =>
      cases right with
      | one =>
          change binaryAddBitsAux false [true] [true] = [false, true]
          simp [binaryAddBitsAux, binaryAddStep]
      | bit1 right =>
          change binaryAddBitsAux false [true]
              (true :: encodePosNum right) =
            encodePosNum (PosNum.bit1 right).succ
          simp only [binaryAddBitsAux, binaryAddStep]
          rw [binaryAddBitsAux_true_left_nil,
            binarySuccBits_encodePosNum]
          change false :: encodePosNum right.succ =
            false :: encodePosNum right.succ
          rfl
      | bit0 right =>
          change binaryAddBitsAux false [true]
              (false :: encodePosNum right) =
            encodePosNum (PosNum.bit0 right).succ
          simp only [binaryAddBitsAux, binaryAddStep]
          rw [binaryAddBitsAux_false_left_nil]
          rfl
  | bit1 left ih =>
      cases right with
      | one =>
          change binaryAddBitsAux false (true :: encodePosNum left)
              [true] = encodePosNum (PosNum.bit1 left).succ
          simp only [binaryAddBitsAux, binaryAddStep]
          rw [binaryAddBitsAux_true_right_nil,
            binarySuccBits_encodePosNum]
          change false :: encodePosNum left.succ =
            false :: encodePosNum left.succ
          rfl
      | bit1 right =>
          change binaryAddBitsAux false (true :: encodePosNum left)
              (true :: encodePosNum right) =
            encodePosNum (PosNum.bit0 ((left + right).succ))
          simp only [binaryAddBitsAux, binaryAddStep, encodePosNum]
          rw [binaryAddBitsAux_true_eq_succ,
            ih, binarySuccBits_encodePosNum]
      | bit0 right =>
          change binaryAddBitsAux false (true :: encodePosNum left)
              (false :: encodePosNum right) =
            encodePosNum (PosNum.bit1 (left + right))
          simp only [binaryAddBitsAux, binaryAddStep, encodePosNum]
          rw [ih]
  | bit0 left ih =>
      cases right with
      | one =>
          change binaryAddBitsAux false (false :: encodePosNum left)
              [true] = encodePosNum (PosNum.bit0 left).succ
          simp only [binaryAddBitsAux, binaryAddStep]
          rw [binaryAddBitsAux_false_right_nil]
          rfl
      | bit1 right =>
          change binaryAddBitsAux false (false :: encodePosNum left)
              (true :: encodePosNum right) =
            encodePosNum (PosNum.bit1 (left + right))
          simp only [binaryAddBitsAux, binaryAddStep, encodePosNum]
          rw [ih]
      | bit0 right =>
          change binaryAddBitsAux false (false :: encodePosNum left)
              (false :: encodePosNum right) =
            encodePosNum (PosNum.bit0 (left + right))
          simp only [binaryAddBitsAux, binaryAddStep, encodePosNum]
          rw [ih]

private theorem binaryAddBitsAux_encodeNum (left right : Num) :
    binaryAddBitsAux false (encodeNum left) (encodeNum right) =
      encodeNum (left + right) := by
  cases left with
  | zero =>
      change binaryAddBitsAux false [] (encodeNum right) = encodeNum right
      exact binaryAddBitsAux_false_left_nil (encodeNum right)
  | pos left =>
      cases right with
      | zero =>
          change binaryAddBitsAux false (encodePosNum left) [] =
            encodePosNum left
          exact binaryAddBitsAux_false_right_nil (encodePosNum left)
      | pos right =>
          change binaryAddBitsAux false (encodePosNum left)
              (encodePosNum right) = encodePosNum (left + right)
          exact
            binaryAddBitsAux_encodePosNum left right

/-- Ripple-carry addition agrees with natural-number addition on mathlib's
canonical binary encodings, including zero on either side. -/
@[simp]
theorem binaryAddBitsAux_encodeNat (left right : ℕ) :
    binaryAddBitsAux false (encodeNat left) (encodeNat right) =
      encodeNat (left + right) := by
  unfold encodeNat
  rw [binaryAddBitsAux_encodeNum, ← Num.add_of_nat]

private theorem binaryAddPairsAux_length_le
    (carry : Bool) (pairs : List (Option Bool × Option Bool)) :
    (binaryAddPairsAux carry pairs).length ≤ pairs.length + 1 := by
  induction pairs generalizing carry with
  | nil => cases carry <;> simp [binaryAddPairsAux]
  | cons pair pairs ih =>
      simp only [binaryAddPairsAux, List.length_cons]
      exact Nat.succ_le_succ (ih (binaryAddStep carry pair.1 pair.2).2)

/-- Input, reverse-work, and canonical output stacks for binary addition. -/
inductive AddStack
  | input
  | work
  | output
  deriving DecidableEq, Fintype

/-- Ripple-carry scanning and output reversal phases. -/
inductive AddLabel
  | scan
  | reverse
  deriving DecidableEq, Fintype

/-- Finite control stores the latest aligned pair, its emitted bit, and the
carry into the next position. -/
structure AddState where
  pair : Option (Option Bool × Option Bool)
  bit : Option Bool
  carry : Bool
  deriving DecidableEq, Fintype

private def addInitialState : AddState :=
  ⟨none, none, false⟩

private def addPoppedPair
    (state : AddState)
    (pair : Option (Option Bool × Option Bool)) : AddState :=
  match pair with
  | none => { state with pair := none }
  | some bits =>
      let step := binaryAddStep state.carry bits.1 bits.2
      ⟨some bits, some step.1, step.2⟩

private def addPoppedWork
    (state : AddState) (bit : Option Bool) : AddState :=
  { state with bit := bit }

private def addPairPresent : AddState → Bool
  | ⟨some _, _, _⟩ => true
  | _ => false

private def addBitPresent : AddState → Bool
  | ⟨_, some _, _⟩ => true
  | _ => false

private def addCarry (state : AddState) : Bool :=
  state.carry

private def addEmittedBit : AddState → Bool
  | ⟨_, some bit, _⟩ => bit
  | _ => false

private def AddAlphabet : AddStack → Type
  | .input => Option Bool × Option Bool
  | .work => Bool
  | .output => Bool

/-- A finite ripple-carry adder.  Scanning pushes emitted bits onto a work
stack; the reverse phase restores least-significant-bit-first output order. -/
def binaryAddProgram :
    AddLabel → TM2.Stmt AddAlphabet AddLabel AddState
  | .scan =>
      .pop .input addPoppedPair <|
        .branch addPairPresent
          (.push .work addEmittedBit <|
            .goto (fun _ => .scan))
          (.branch addCarry
            (.push .work (fun _ => true) <|
              .goto (fun _ => .reverse))
            (.goto (fun _ => .reverse)))
  | .reverse =>
      .pop .work addPoppedWork <|
        .branch addBitPresent
          (.push .output addEmittedBit <|
            .goto (fun _ => .reverse))
          (.load (fun _ => addInitialState) .halt)

/-- Concrete finite machine adding two aligned canonical binary naturals. -/
def binaryAddComputer : FinTM2 where
  K := AddStack
  k₀ := .input
  k₁ := .output
  Γ := AddAlphabet
  Λ := AddLabel
  main := .scan
  σ := AddState
  initialState := addInitialState
  Γk₀Fin := by
    change Fintype (Option Bool × Option Bool)
    infer_instance
  m := binaryAddProgram

private def addStackContents
    (input : List (Option Bool × Option Bool))
    (work output : List Bool) :
    (index : AddStack) → List (AddAlphabet index)
  | .input => input
  | .work => work
  | .output => output

private def addCfg (label : Option AddLabel) (state : AddState)
    (input : List (Option Bool × Option Bool))
    (work output : List Bool) : binaryAddComputer.Cfg where
  l := label
  var := state
  stk := addStackContents input work output

private theorem add_step_scan_cons
    (pair : Option Bool × Option Bool)
    (pairs : List (Option Bool × Option Bool))
    (work output : List Bool) (state : AddState) :
    binaryAddComputer.step
        (addCfg (some .scan) state (pair :: pairs) work output) =
      some (addCfg (some .scan)
        (addPoppedPair state (some pair)) pairs
        ((binaryAddStep state.carry pair.1 pair.2).1 :: work) output) := by
  rcases state with ⟨heldPair, heldBit, carry⟩
  rcases pair with ⟨left, right⟩
  rcases left with _ | left <;> rcases right with _ | right <;>
    cases carry <;>
    simp [binaryAddComputer, FinTM2.step, addCfg, binaryAddProgram,
      addStackContents, AddAlphabet, addPoppedPair, addPairPresent,
      addEmittedBit, binaryAddStep, Function.update] <;>
    (funext index; cases index <;> rfl)

private theorem add_step_scan_nil_false
    (work output : List Bool) (pair : Option (Option Bool × Option Bool))
    (bit : Option Bool) :
    binaryAddComputer.step
        (addCfg (some .scan) ⟨pair, bit, false⟩ [] work output) =
      some (addCfg (some .reverse) ⟨none, bit, false⟩ [] work output) := by
  simp [binaryAddComputer, FinTM2.step, addCfg, binaryAddProgram,
    addStackContents, AddAlphabet, addPoppedPair, addPairPresent, addCarry,
    Function.update]

private theorem add_step_scan_nil_true
    (work output : List Bool) (pair : Option (Option Bool × Option Bool))
    (bit : Option Bool) :
    binaryAddComputer.step
        (addCfg (some .scan) ⟨pair, bit, true⟩ [] work output) =
      some (addCfg (some .reverse) ⟨none, bit, true⟩ []
        (true :: work) output) := by
  simp [binaryAddComputer, FinTM2.step, addCfg, binaryAddProgram,
    addStackContents, AddAlphabet, addPoppedPair, addPairPresent, addCarry,
    Function.update]
  funext index
  cases index <;> rfl

private theorem add_step_reverse_cons
    (bit : Bool) (work output : List Bool) (state : AddState) :
    binaryAddComputer.step
        (addCfg (some .reverse) state [] (bit :: work) output) =
      some (addCfg (some .reverse) (addPoppedWork state (some bit))
        [] work (bit :: output)) := by
  rcases state with ⟨pair, heldBit, carry⟩
  cases bit <;>
    simp [binaryAddComputer, FinTM2.step, addCfg, binaryAddProgram,
      addStackContents, AddAlphabet, addPoppedWork, addBitPresent,
      addEmittedBit, Function.update] <;>
    (funext index; cases index <;> rfl)

private theorem add_step_reverse_nil
    (output : List Bool) (state : AddState) :
    binaryAddComputer.step
        (addCfg (some .reverse) state [] [] output) =
      some (addCfg none addInitialState [] [] output) := by
  rcases state with ⟨pair, bit, carry⟩
  simp [binaryAddComputer, FinTM2.step, addCfg, binaryAddProgram,
    addStackContents, AddAlphabet, addPoppedWork, addBitPresent,
    addInitialState, Function.update]

private def addEvalsToInTimeOne
    {start finish : binaryAddComputer.Cfg}
    (hstep : binaryAddComputer.step start = some finish) :
    EvalsToInTime binaryAddComputer.step start (some finish) 1 where
  steps := 1
  evals_in_steps := by
    simpa [Function.iterate_one] using hstep
  steps_le_m := Nat.le_refl 1

private def addFoldState :
    AddState → List (Option Bool × Option Bool) → AddState
  | state, [] => addPoppedPair state none
  | state, pair :: pairs =>
      addFoldState (addPoppedPair state (some pair)) pairs

private def add_scan_evals
    (pairs : List (Option Bool × Option Bool))
    (work output : List Bool) (state : AddState) :
    EvalsToInTime binaryAddComputer.step
      (addCfg (some .scan) state pairs work output)
      (some (addCfg (some .reverse) (addFoldState state pairs) []
        ((binaryAddPairsAux state.carry pairs).reverse ++ work) output))
      (pairs.length + 1) := by
  induction pairs generalizing work state with
  | nil =>
      rcases state with ⟨pair, bit, carry⟩
      cases carry with
      | false =>
          simpa [addFoldState, binaryAddPairsAux] using
            addEvalsToInTimeOne
              (add_step_scan_nil_false work output pair bit)
      | true =>
          simpa [addFoldState, binaryAddPairsAux] using
            addEvalsToInTimeOne
              (add_step_scan_nil_true work output pair bit)
  | cons pair pairs ih =>
      let nextState := addPoppedPair state (some pair)
      let step := binaryAddStep state.carry pair.1 pair.2
      let middle := addCfg (some .scan) nextState pairs
        (step.1 :: work) output
      have hone : EvalsToInTime binaryAddComputer.step
          (addCfg (some .scan) state (pair :: pairs) work output)
          (some middle) 1 :=
        addEvalsToInTimeOne (by
          simpa [middle, nextState, step] using
            add_step_scan_cons pair pairs work output state)
      have hrest := ih (step.1 :: work) nextState
      have htrans := EvalsToInTime.trans binaryAddComputer.step
        1 (pairs.length + 1)
        (addCfg (some .scan) state (pair :: pairs) work output)
        middle
        (some (addCfg (some .reverse)
          (addFoldState state (pair :: pairs)) []
          ((binaryAddPairsAux state.carry (pair :: pairs)).reverse ++ work)
          output))
        hone
        (by
          simpa [middle, nextState, step, addFoldState,
            binaryAddPairsAux, addPoppedPair, List.reverse_cons,
            List.append_assoc] using hrest)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htrans

private def add_reverse_evals
    (work output : List Bool) (state : AddState) :
    EvalsToInTime binaryAddComputer.step
      (addCfg (some .reverse) state [] work output)
      (some (addCfg none addInitialState [] []
        (work.reverse ++ output)))
      (work.length + 1) := by
  induction work generalizing output state with
  | nil =>
      simpa using addEvalsToInTimeOne (add_step_reverse_nil output state)
  | cons bit work ih =>
      let nextState := addPoppedWork state (some bit)
      let middle := addCfg (some .reverse) nextState [] work
        (bit :: output)
      have hone : EvalsToInTime binaryAddComputer.step
          (addCfg (some .reverse) state [] (bit :: work) output)
          (some middle) 1 :=
        addEvalsToInTimeOne (by
          simpa [middle, nextState] using
            add_step_reverse_cons bit work output state)
      have hrest := ih (bit :: output) nextState
      have htrans := EvalsToInTime.trans binaryAddComputer.step
        1 (work.length + 1)
        (addCfg (some .reverse) state [] (bit :: work) output)
        middle
        (some (addCfg none addInitialState [] []
          ((bit :: work).reverse ++ output)))
        hone
        (by simpa [middle, nextState, List.reverse_cons,
          List.append_assoc] using hrest)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htrans

private theorem add_initList_eq_cfg
    (input : List (Option Bool × Option Bool)) :
    initList binaryAddComputer input =
      addCfg (some .scan) addInitialState input [] [] := by
  unfold initList addCfg
  congr
  funext index
  cases index <;> rfl

private theorem add_haltList_eq_cfg (output : List Bool) :
    haltList binaryAddComputer output =
      addCfg none addInitialState [] [] output := by
  unfold haltList addCfg
  congr
  funext index
  cases index <;> rfl

/-- Binary addition uses one aligned scan and one output reversal, taking at
most `2s + 3` steps for paired input length `s`. -/
def binaryAdd_outputsInTime (pair : ℕ × ℕ) :
    TM2OutputsInTime binaryAddComputer (BinaryNatPair.encode pair)
      (some (encodeNat (pair.1 + pair.2)))
      (2 * (BinaryNatPair.encode pair).length + 3) := by
  let input := BinaryNatPair.encode pair
  let result := binaryAddPairsAux false input
  have hscan := add_scan_evals input [] [] addInitialState
  have hreverse := add_reverse_evals result.reverse []
    (addFoldState addInitialState input)
  have hall := EvalsToInTime.trans binaryAddComputer.step
    (input.length + 1) (result.reverse.length + 1)
    (addCfg (some .scan) addInitialState input [] [])
    (addCfg (some .reverse) (addFoldState addInitialState input) []
      result.reverse [])
    (some (addCfg none addInitialState [] [] result))
    (by simpa [result] using hscan)
    (by simpa [result] using hreverse)
  have hlength := binaryAddPairsAux_length_le false input
  change result.length ≤ input.length + 1 at hlength
  have hmono : EvalsToInTime binaryAddComputer.step
      (addCfg (some .scan) addInitialState input [] [])
      (some (addCfg none addInitialState [] [] result))
      (2 * input.length + 3) :=
    evalsToInTimeMono hall (by
      simp only [List.length_reverse]
      omega)
  rw [TM2OutputsInTime, add_initList_eq_cfg]
  simp only [Option.map_some]
  rw [add_haltList_eq_cfg]
  rcases pair with ⟨left, right⟩
  simpa [input, result, BinaryNatPair.encode, addInitialState] using hmono

/-- A genuine linear-time finite-machine witness for addition on mathlib's
standard binary natural-number encoding. -/
noncomputable def binaryAddComputableInPolyTime :
    @TM2ComputableInPolyTime (ℕ × ℕ) ℕ BinaryNatPair.finEncoding
      finEncodingNatBool (fun pair => pair.1 + pair.2) where
  tm := binaryAddComputer
  inputAlphabet := Equiv.refl (Option Bool × Option Bool)
  outputAlphabet := Equiv.refl Bool
  time := 2 * Polynomial.X + 3
  outputsFun pair := by
    simpa [BinaryNatPair.finEncoding, finEncodingNatBool, Equiv.refl,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_natCast,
      Polynomial.eval_X] using binaryAdd_outputsInTime pair

end LeanNPHardness.MachinePrimitives
