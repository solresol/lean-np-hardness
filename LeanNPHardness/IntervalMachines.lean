import LeanNPHardness.BinaryArithmetic
import LeanNPHardness.RawNatEncoding
import LeanNPHardness.BoundedPrime

/-!
Bounded number-theory components extracted from phd-thesis-lean at 84be78d.
All enumeration, trial-division and prime-selection runtime bounds use the
explicit unary/padded input encodings; no binary-input polynomial bound is
asserted for these algorithms.
-/

namespace LeanNPHardness.MachinePrimitives

open Computability Turing
open LeanNPHardness.MachineComposition LeanNPHardness.BoundedPrime

/-! ## Bertrand-interval candidate enumeration

The interval contains `q` candidates, so enumerating it cannot be polynomial
in the bit length of a standalone binary encoding of `q`.  The full CSP input
provides the needed padding: its explicit domain entries witness that
`q ≤ input length`.  The component below makes that invariant explicit by
using mathlib's unary encoding of the scan bound.  It emits the candidates in
the checked stack-oriented raw-natural-list encoding used by the serialization
pass above.  A later structural compiler pass will produce this unary bound
while deduplicating the domain symbols.
-/

/-- The next `count` naturals strictly above `current`. -/
def intervalFrom : ℕ → ℕ → List ℕ
  | 0, _ => []
  | count + 1, current => (current + 1) :: intervalFrom count (current + 1)

/-- The complete inclusive Bertrand scan interval `[q + 1, 2q]`. -/
def bertrandCandidates (q : ℕ) : List ℕ :=
  intervalFrom q q

@[simp]
theorem intervalFrom_length (count current : ℕ) :
    (intervalFrom count current).length = count := by
  induction count generalizing current with
  | zero => rfl
  | succ count ih => simp [intervalFrom, ih]

@[simp]
theorem bertrandCandidates_length (q : ℕ) :
    (bertrandCandidates q).length = q := by
  simp [bertrandCandidates]

theorem mem_intervalFrom_iff (value count current : ℕ) :
    value ∈ intervalFrom count current ↔
      current < value ∧ value ≤ current + count := by
  induction count generalizing current with
  | zero => simp [intervalFrom]
  | succ count ih =>
      simp only [intervalFrom, List.mem_cons, ih]
      omega

@[simp]
theorem mem_bertrandCandidates_iff (q value : ℕ) :
    value ∈ bertrandCandidates q ↔ q < value ∧ value ≤ 2 * q := by
  rw [bertrandCandidates, mem_intervalFrom_iff]
  omega

@[simp]
theorem unaryEncodeNat_length (n : ℕ) :
    (unaryEncodeNat n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [unaryEncodeNat, ih]

/-- Input unary markers, a preserved unary copy, the current binary value,
binary work storage, and the stack-oriented raw-field output. -/
inductive EnumerateStack
  | input
  | unary
  | counter
  | work
  | output
  deriving DecidableEq, Fintype

/-- Counting, in-place increment, field emission, candidate iteration, and
final cleanup phases. -/
inductive EnumerateLabel
  | count
  | incCarry
  | incCopy
  | incRestore
  | emitStart
  | emitCopy
  | emitRestore
  | candidates
  | cleanup
  deriving DecidableEq, Fintype

/-- Finite control stores one popped bit and whether increment returns to
field emission rather than the initial unary-counting loop. -/
structure EnumerateState where
  bit : Option Bool
  returnToEmit : Bool
  deriving DecidableEq, Fintype

private def enumerateInitialState : EnumerateState :=
  ⟨none, false⟩

private def enumeratePoppedBit
    (state : EnumerateState) (bit : Option Bool) : EnumerateState :=
  { state with bit := bit }

private def enumerateSetReturn
    (returnToEmit : Bool) (_state : EnumerateState) : EnumerateState :=
  ⟨none, returnToEmit⟩

private def enumerateBitPresent : EnumerateState → Bool
  | ⟨some _, _⟩ => true
  | _ => false

private def enumerateBitTrue : EnumerateState → Bool
  | ⟨some true, _⟩ => true
  | _ => false

private def enumerateHeldBit : EnumerateState → Bool
  | ⟨some bit, _⟩ => bit
  | _ => false

private def enumerateHeldRawBit : EnumerateState → Option Bool
  | ⟨some bit, _⟩ => some bit
  | _ => none

private def enumerateReturnToEmit (state : EnumerateState) : Bool :=
  state.returnToEmit

private def EnumerateAlphabet : EnumerateStack → Type
  | .input => Bool
  | .unary => Bool
  | .counter => Bool
  | .work => Bool
  | .output => Option Bool

/-- A finite machine that counts a unary bound into binary, emits the count
field, then emits each candidate through `2q` while preserving the counter. -/
def bertrandCandidateProgram :
    EnumerateLabel → TM2.Stmt EnumerateAlphabet EnumerateLabel EnumerateState
  | .count =>
      .pop .input enumeratePoppedBit <|
        .branch enumerateBitPresent
          (.push .unary (fun _ => true) <|
            .load (enumerateSetReturn false) <|
              .goto (fun _ => .incCarry))
          (.goto (fun _ => .emitStart))
  | .incCarry =>
      .pop .counter enumeratePoppedBit <|
        .branch enumerateBitPresent
          (.branch enumerateBitTrue
            (.push .work (fun _ => false) <|
              .goto (fun _ => .incCarry))
            (.push .work (fun _ => true) <|
              .goto (fun _ => .incCopy)))
          (.push .work (fun _ => true) <|
            .goto (fun _ => .incRestore))
  | .incCopy =>
      .pop .counter enumeratePoppedBit <|
        .branch enumerateBitPresent
          (.push .work enumerateHeldBit <|
            .goto (fun _ => .incCopy))
          (.goto (fun _ => .incRestore))
  | .incRestore =>
      .pop .work enumeratePoppedBit <|
        .branch enumerateBitPresent
          (.push .counter enumerateHeldBit <|
            .goto (fun _ => .incRestore))
          (.branch enumerateReturnToEmit
            (.goto (fun _ => .emitStart))
            (.goto (fun _ => .count)))
  | .emitStart =>
      .push .output (fun _ => none) <|
        .goto (fun _ => .emitCopy)
  | .emitCopy =>
      .pop .counter enumeratePoppedBit <|
        .branch enumerateBitPresent
          (.push .work enumerateHeldBit <|
            .push .output enumerateHeldRawBit <|
              .goto (fun _ => .emitCopy))
          (.goto (fun _ => .emitRestore))
  | .emitRestore =>
      .pop .work enumeratePoppedBit <|
        .branch enumerateBitPresent
          (.push .counter enumerateHeldBit <|
            .goto (fun _ => .emitRestore))
          (.goto (fun _ => .candidates))
  | .candidates =>
      .pop .unary enumeratePoppedBit <|
        .branch enumerateBitPresent
          (.load (enumerateSetReturn true) <|
            .goto (fun _ => .incCarry))
          (.goto (fun _ => .cleanup))
  | .cleanup =>
      .pop .counter enumeratePoppedBit <|
        .branch enumerateBitPresent
          (.goto (fun _ => .cleanup))
          (.load (fun _ => enumerateInitialState) .halt)

/-- Concrete finite machine enumerating the Bertrand interval from a unary
bound into `RawNatList.finEncoding`. -/
def bertrandCandidateComputer : FinTM2 where
  K := EnumerateStack
  k₀ := .input
  k₁ := .output
  Γ := EnumerateAlphabet
  Λ := EnumerateLabel
  main := .count
  σ := EnumerateState
  initialState := enumerateInitialState
  Γk₀Fin := Bool.fintype
  m := bertrandCandidateProgram

private def enumerateStackContents
    (input unary counter work : List Bool)
    (output : List (Option Bool)) :
    (index : EnumerateStack) → List (EnumerateAlphabet index)
  | .input => input
  | .unary => unary
  | .counter => counter
  | .work => work
  | .output => output

private def enumerateCfg (label : Option EnumerateLabel)
    (state : EnumerateState) (input unary counter work : List Bool)
    (output : List (Option Bool)) : bertrandCandidateComputer.Cfg where
  l := label
  var := state
  stk := enumerateStackContents input unary counter work output

private def enumerateEvalsToInTimeOne
    {start finish : bertrandCandidateComputer.Cfg}
    (hstep : bertrandCandidateComputer.step start = some finish) :
    EvalsToInTime bertrandCandidateComputer.step start (some finish) 1 where
  steps := 1
  evals_in_steps := by
    simpa [Function.iterate_one] using hstep
  steps_le_m := Nat.le_refl 1

private theorem enumerate_step_count_cons
    (input unary counter : List Bool) (output : List (Option Bool)) :
    bertrandCandidateComputer.step
        (enumerateCfg (some .count) enumerateInitialState
          (true :: input) unary counter [] output) =
      some (enumerateCfg (some .incCarry) enumerateInitialState
        input (true :: unary) counter [] output) := by
  simp [bertrandCandidateComputer, FinTM2.step, enumerateCfg,
    bertrandCandidateProgram, enumerateStackContents, EnumerateAlphabet,
    enumeratePoppedBit, enumerateBitPresent, enumerateSetReturn,
    enumerateInitialState, Function.update]
  funext index
  cases index <;> rfl

private theorem enumerate_step_count_nil
    (unary counter : List Bool) (output : List (Option Bool)) :
    bertrandCandidateComputer.step
        (enumerateCfg (some .count) enumerateInitialState
          [] unary counter [] output) =
      some (enumerateCfg (some .emitStart) enumerateInitialState
        [] unary counter [] output) := by
  simp [bertrandCandidateComputer, FinTM2.step, enumerateCfg,
    bertrandCandidateProgram, enumerateStackContents, EnumerateAlphabet,
    enumeratePoppedBit, enumerateBitPresent, enumerateInitialState,
    Function.update]

private theorem enumerate_step_inc_carry_nil
    (input unary work : List Bool) (output : List (Option Bool))
    (state : EnumerateState) :
    bertrandCandidateComputer.step
        (enumerateCfg (some .incCarry) state input unary [] work output) =
      some (enumerateCfg (some .incRestore)
        (enumeratePoppedBit state none) input unary []
        (true :: work) output) := by
  rcases state with ⟨bit, returnToEmit⟩
  simp [bertrandCandidateComputer, FinTM2.step, enumerateCfg,
    bertrandCandidateProgram, enumerateStackContents, EnumerateAlphabet,
    enumeratePoppedBit, enumerateBitPresent, Function.update]
  funext index
  cases index <;> rfl

private theorem enumerate_step_inc_carry_false
    (bits input unary work : List Bool) (output : List (Option Bool))
    (state : EnumerateState) :
    bertrandCandidateComputer.step
        (enumerateCfg (some .incCarry) state input unary
          (false :: bits) work output) =
      some (enumerateCfg (some .incCopy)
        (enumeratePoppedBit state (some false)) input unary bits
        (true :: work) output) := by
  rcases state with ⟨bit, returnToEmit⟩
  simp [bertrandCandidateComputer, FinTM2.step, enumerateCfg,
    bertrandCandidateProgram, enumerateStackContents, EnumerateAlphabet,
    enumeratePoppedBit, enumerateBitPresent, enumerateBitTrue,
    Function.update]
  funext index
  cases index <;> rfl

private theorem enumerate_step_inc_carry_true
    (bits input unary work : List Bool) (output : List (Option Bool))
    (state : EnumerateState) :
    bertrandCandidateComputer.step
        (enumerateCfg (some .incCarry) state input unary
          (true :: bits) work output) =
      some (enumerateCfg (some .incCarry)
        (enumeratePoppedBit state (some true)) input unary bits
        (false :: work) output) := by
  rcases state with ⟨bit, returnToEmit⟩
  simp [bertrandCandidateComputer, FinTM2.step, enumerateCfg,
    bertrandCandidateProgram, enumerateStackContents, EnumerateAlphabet,
    enumeratePoppedBit, enumerateBitPresent, enumerateBitTrue,
    Function.update]
  funext index
  cases index <;> rfl

private theorem enumerate_step_inc_copy_nil
    (input unary work : List Bool) (output : List (Option Bool))
    (state : EnumerateState) :
    bertrandCandidateComputer.step
        (enumerateCfg (some .incCopy) state input unary [] work output) =
      some (enumerateCfg (some .incRestore)
        (enumeratePoppedBit state none) input unary [] work output) := by
  rcases state with ⟨bit, returnToEmit⟩
  simp [bertrandCandidateComputer, FinTM2.step, enumerateCfg,
    bertrandCandidateProgram, enumerateStackContents, EnumerateAlphabet,
    enumeratePoppedBit, enumerateBitPresent, Function.update]

private theorem enumerate_step_inc_copy_cons
    (bit : Bool) (bits input unary work : List Bool)
    (output : List (Option Bool)) (state : EnumerateState) :
    bertrandCandidateComputer.step
        (enumerateCfg (some .incCopy) state input unary
          (bit :: bits) work output) =
      some (enumerateCfg (some .incCopy)
        (enumeratePoppedBit state (some bit)) input unary bits
        (bit :: work) output) := by
  rcases state with ⟨held, returnToEmit⟩
  cases bit <;>
    simp [bertrandCandidateComputer, FinTM2.step, enumerateCfg,
      bertrandCandidateProgram, enumerateStackContents, EnumerateAlphabet,
      enumeratePoppedBit, enumerateBitPresent, enumerateHeldBit,
      Function.update] <;>
    (funext index; cases index <;> rfl)

private theorem enumerate_step_inc_restore_cons
    (bit : Bool) (work input unary counter : List Bool)
    (output : List (Option Bool)) (state : EnumerateState) :
    bertrandCandidateComputer.step
        (enumerateCfg (some .incRestore) state input unary counter
          (bit :: work) output) =
      some (enumerateCfg (some .incRestore)
        (enumeratePoppedBit state (some bit)) input unary
        (bit :: counter) work output) := by
  rcases state with ⟨held, returnToEmit⟩
  cases bit <;>
    simp [bertrandCandidateComputer, FinTM2.step, enumerateCfg,
      bertrandCandidateProgram, enumerateStackContents, EnumerateAlphabet,
      enumeratePoppedBit, enumerateBitPresent, enumerateHeldBit,
      Function.update] <;>
    (funext index; cases index <;> rfl)

private theorem enumerate_step_inc_restore_nil_false
    (input unary counter : List Bool) (output : List (Option Bool))
    (bit : Option Bool) :
    bertrandCandidateComputer.step
        (enumerateCfg (some .incRestore) ⟨bit, false⟩ input unary counter
          [] output) =
      some (enumerateCfg (some .count) enumerateInitialState
        input unary counter [] output) := by
  simp [bertrandCandidateComputer, FinTM2.step, enumerateCfg,
    bertrandCandidateProgram, enumerateStackContents, EnumerateAlphabet,
    enumeratePoppedBit, enumerateBitPresent, enumerateReturnToEmit,
    enumerateInitialState, Function.update]

private theorem enumerate_step_inc_restore_nil_true
    (input unary counter : List Bool) (output : List (Option Bool))
    (bit : Option Bool) :
    bertrandCandidateComputer.step
        (enumerateCfg (some .incRestore) ⟨bit, true⟩ input unary counter
          [] output) =
      some (enumerateCfg (some .emitStart) ⟨none, true⟩
        input unary counter [] output) := by
  simp [bertrandCandidateComputer, FinTM2.step, enumerateCfg,
    bertrandCandidateProgram, enumerateStackContents, EnumerateAlphabet,
    enumeratePoppedBit, enumerateBitPresent, enumerateReturnToEmit,
    Function.update]

private theorem enumerate_step_emit_start
    (input unary counter work : List Bool) (output : List (Option Bool))
    (state : EnumerateState) :
    bertrandCandidateComputer.step
        (enumerateCfg (some .emitStart) state input unary counter work output) =
      some (enumerateCfg (some .emitCopy) state input unary counter work
        (none :: output)) := by
  rcases state with ⟨bit, returnToEmit⟩
  simp [bertrandCandidateComputer, FinTM2.step, enumerateCfg,
    bertrandCandidateProgram, enumerateStackContents, EnumerateAlphabet]
  funext index
  cases index <;> rfl

private theorem enumerate_step_emit_copy_nil
    (input unary work : List Bool) (output : List (Option Bool))
    (state : EnumerateState) :
    bertrandCandidateComputer.step
        (enumerateCfg (some .emitCopy) state input unary [] work output) =
      some (enumerateCfg (some .emitRestore)
        (enumeratePoppedBit state none) input unary [] work output) := by
  rcases state with ⟨bit, returnToEmit⟩
  simp [bertrandCandidateComputer, FinTM2.step, enumerateCfg,
    bertrandCandidateProgram, enumerateStackContents, EnumerateAlphabet,
    enumeratePoppedBit, enumerateBitPresent, Function.update]

private theorem enumerate_step_emit_copy_cons
    (bit : Bool) (bits input unary work : List Bool)
    (output : List (Option Bool)) (state : EnumerateState) :
    bertrandCandidateComputer.step
        (enumerateCfg (some .emitCopy) state input unary
          (bit :: bits) work output) =
      some (enumerateCfg (some .emitCopy)
        (enumeratePoppedBit state (some bit)) input unary bits
        (bit :: work) (some bit :: output)) := by
  rcases state with ⟨held, returnToEmit⟩
  cases bit <;>
    simp [bertrandCandidateComputer, FinTM2.step, enumerateCfg,
      bertrandCandidateProgram, enumerateStackContents, EnumerateAlphabet,
      enumeratePoppedBit, enumerateBitPresent, enumerateHeldBit,
      enumerateHeldRawBit, Function.update] <;>
    (funext index; cases index <;> rfl)

private theorem enumerate_step_emit_restore_cons
    (bit : Bool) (work input unary counter : List Bool)
    (output : List (Option Bool)) (state : EnumerateState) :
    bertrandCandidateComputer.step
        (enumerateCfg (some .emitRestore) state input unary counter
          (bit :: work) output) =
      some (enumerateCfg (some .emitRestore)
        (enumeratePoppedBit state (some bit)) input unary
        (bit :: counter) work output) := by
  rcases state with ⟨held, returnToEmit⟩
  cases bit <;>
    simp [bertrandCandidateComputer, FinTM2.step, enumerateCfg,
      bertrandCandidateProgram, enumerateStackContents, EnumerateAlphabet,
      enumeratePoppedBit, enumerateBitPresent, enumerateHeldBit,
      Function.update] <;>
    (funext index; cases index <;> rfl)

private theorem enumerate_step_emit_restore_nil
    (input unary counter : List Bool) (output : List (Option Bool))
    (state : EnumerateState) :
    bertrandCandidateComputer.step
        (enumerateCfg (some .emitRestore) state input unary counter [] output) =
      some (enumerateCfg (some .candidates)
        (enumeratePoppedBit state none) input unary counter [] output) := by
  rcases state with ⟨bit, returnToEmit⟩
  simp [bertrandCandidateComputer, FinTM2.step, enumerateCfg,
    bertrandCandidateProgram, enumerateStackContents, EnumerateAlphabet,
    enumeratePoppedBit, enumerateBitPresent, Function.update]

private theorem enumerate_step_candidates_cons
    (unary input counter : List Bool) (output : List (Option Bool))
    (state : EnumerateState) :
    bertrandCandidateComputer.step
        (enumerateCfg (some .candidates) state input
          (true :: unary) counter [] output) =
      some (enumerateCfg (some .incCarry) ⟨none, true⟩
        input unary counter [] output) := by
  rcases state with ⟨bit, returnToEmit⟩
  simp [bertrandCandidateComputer, FinTM2.step, enumerateCfg,
    bertrandCandidateProgram, enumerateStackContents, EnumerateAlphabet,
    enumeratePoppedBit, enumerateBitPresent, enumerateSetReturn]
  funext index
  cases index <;> rfl

private theorem enumerate_step_candidates_nil
    (input counter : List Bool) (output : List (Option Bool))
    (state : EnumerateState) :
    bertrandCandidateComputer.step
        (enumerateCfg (some .candidates) state input [] counter [] output) =
      some (enumerateCfg (some .cleanup)
        (enumeratePoppedBit state none) input [] counter [] output) := by
  rcases state with ⟨bit, returnToEmit⟩
  simp [bertrandCandidateComputer, FinTM2.step, enumerateCfg,
    bertrandCandidateProgram, enumerateStackContents, EnumerateAlphabet,
    enumeratePoppedBit, enumerateBitPresent]

private theorem enumerate_step_cleanup_cons
    (bit : Bool) (bits : List Bool) (output : List (Option Bool))
    (state : EnumerateState) :
    bertrandCandidateComputer.step
        (enumerateCfg (some .cleanup) state [] [] (bit :: bits) [] output) =
      some (enumerateCfg (some .cleanup)
        (enumeratePoppedBit state (some bit)) [] [] bits [] output) := by
  rcases state with ⟨held, returnToEmit⟩
  cases bit <;>
    simp [bertrandCandidateComputer, FinTM2.step, enumerateCfg,
      bertrandCandidateProgram, enumerateStackContents, EnumerateAlphabet,
      enumeratePoppedBit, enumerateBitPresent] <;>
    (funext index; cases index <;> rfl)

private theorem enumerate_step_cleanup_nil
    (output : List (Option Bool)) (state : EnumerateState) :
    bertrandCandidateComputer.step
        (enumerateCfg (some .cleanup) state [] [] [] [] output) =
      some (enumerateCfg none enumerateInitialState [] [] [] [] output) := by
  rcases state with ⟨bit, returnToEmit⟩
  simp [bertrandCandidateComputer, FinTM2.step, enumerateCfg,
    bertrandCandidateProgram, enumerateStackContents, EnumerateAlphabet,
    enumeratePoppedBit, enumerateBitPresent, enumerateInitialState]

private def enumerate_inc_copy_evals
    (bits input unary work : List Bool) (output : List (Option Bool))
    (state : EnumerateState) :
    EvalsToInTime bertrandCandidateComputer.step
      (enumerateCfg (some .incCopy) state input unary bits work output)
      (some (enumerateCfg (some .incRestore)
        ⟨none, state.returnToEmit⟩ input unary []
        (bits.reverse ++ work) output))
      (bits.length + 1) := by
  induction bits generalizing work state with
  | nil =>
      simpa using enumerateEvalsToInTimeOne
        (enumerate_step_inc_copy_nil input unary work output state)
  | cons bit bits ih =>
      let nextState := enumeratePoppedBit state (some bit)
      let middle := enumerateCfg (some .incCopy) nextState input unary bits
        (bit :: work) output
      have hone : EvalsToInTime bertrandCandidateComputer.step
          (enumerateCfg (some .incCopy) state input unary
            (bit :: bits) work output)
          (some middle) 1 :=
        enumerateEvalsToInTimeOne (by
          simpa [middle, nextState] using
            enumerate_step_inc_copy_cons bit bits input unary work output state)
      have hrest := ih (bit :: work) nextState
      have htrans := EvalsToInTime.trans bertrandCandidateComputer.step
        1 (bits.length + 1)
        (enumerateCfg (some .incCopy) state input unary
          (bit :: bits) work output)
        middle
        (some (enumerateCfg (some .incRestore)
          ⟨none, state.returnToEmit⟩ input unary []
          ((bit :: bits).reverse ++ work) output))
        hone
        (by
          simpa [middle, nextState, enumeratePoppedBit,
            List.reverse_cons, List.append_assoc] using hrest)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htrans

private def enumerate_inc_carry_evals
    (bits input unary work : List Bool) (output : List (Option Bool))
    (state : EnumerateState) :
    EvalsToInTime bertrandCandidateComputer.step
      (enumerateCfg (some .incCarry) state input unary bits work output)
      (some (enumerateCfg (some .incRestore)
        ⟨none, state.returnToEmit⟩ input unary []
        ((binarySuccBits bits).reverse ++ work) output))
      (bits.length + 1) := by
  induction bits generalizing work state with
  | nil =>
      simpa [binarySuccBits, enumeratePoppedBit] using
        enumerateEvalsToInTimeOne
          (enumerate_step_inc_carry_nil input unary work output state)
  | cons bit bits ih =>
      cases bit with
      | false =>
          let nextState := enumeratePoppedBit state (some false)
          let middle := enumerateCfg (some .incCopy) nextState input unary bits
            (true :: work) output
          have hone : EvalsToInTime bertrandCandidateComputer.step
              (enumerateCfg (some .incCarry) state input unary
                (false :: bits) work output)
              (some middle) 1 :=
            enumerateEvalsToInTimeOne (by
              simpa [middle, nextState] using
                enumerate_step_inc_carry_false bits input unary work output state)
          have hcopy :=
            enumerate_inc_copy_evals bits input unary (true :: work) output
              nextState
          have htrans := EvalsToInTime.trans bertrandCandidateComputer.step
            1 (bits.length + 1)
            (enumerateCfg (some .incCarry) state input unary
              (false :: bits) work output)
            middle
            (some (enumerateCfg (some .incRestore)
              ⟨none, state.returnToEmit⟩ input unary []
              ((binarySuccBits (false :: bits)).reverse ++ work) output))
            hone
            (by
              simpa [middle, nextState, enumeratePoppedBit, binarySuccBits,
                List.reverse_cons, List.append_assoc] using hcopy)
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htrans
      | true =>
          let nextState := enumeratePoppedBit state (some true)
          let middle := enumerateCfg (some .incCarry) nextState input unary bits
            (false :: work) output
          have hone : EvalsToInTime bertrandCandidateComputer.step
              (enumerateCfg (some .incCarry) state input unary
                (true :: bits) work output)
              (some middle) 1 :=
            enumerateEvalsToInTimeOne (by
              simpa [middle, nextState] using
                enumerate_step_inc_carry_true bits input unary work output state)
          have hrest := ih (false :: work) nextState
          have htrans := EvalsToInTime.trans bertrandCandidateComputer.step
            1 (bits.length + 1)
            (enumerateCfg (some .incCarry) state input unary
              (true :: bits) work output)
            middle
            (some (enumerateCfg (some .incRestore)
              ⟨none, state.returnToEmit⟩ input unary []
              ((binarySuccBits (true :: bits)).reverse ++ work) output))
            hone
            (by
              simpa [middle, nextState, enumeratePoppedBit, binarySuccBits,
                List.reverse_cons, List.append_assoc] using hrest)
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htrans

private def enumerate_inc_restore_false_evals
    (work input unary counter : List Bool) (output : List (Option Bool))
    (bit : Option Bool) :
    EvalsToInTime bertrandCandidateComputer.step
      (enumerateCfg (some .incRestore) ⟨bit, false⟩
        input unary counter work output)
      (some (enumerateCfg (some .count) enumerateInitialState
        input unary (work.reverse ++ counter) [] output))
      (work.length + 1) := by
  induction work generalizing counter bit with
  | nil =>
      simpa using enumerateEvalsToInTimeOne
        (enumerate_step_inc_restore_nil_false input unary counter output bit)
  | cons head tail ih =>
      let middle := enumerateCfg (some .incRestore) ⟨some head, false⟩
        input unary (head :: counter) tail output
      have hone : EvalsToInTime bertrandCandidateComputer.step
          (enumerateCfg (some .incRestore) ⟨bit, false⟩
            input unary counter (head :: tail) output)
          (some middle) 1 :=
        enumerateEvalsToInTimeOne (by
          simpa [middle, enumeratePoppedBit] using
            enumerate_step_inc_restore_cons head tail input unary counter
              output ⟨bit, false⟩)
      have hrest := ih (head :: counter) (some head)
      have htrans := EvalsToInTime.trans bertrandCandidateComputer.step
        1 (tail.length + 1)
        (enumerateCfg (some .incRestore) ⟨bit, false⟩
          input unary counter (head :: tail) output)
        middle
        (some (enumerateCfg (some .count) enumerateInitialState
          input unary ((head :: tail).reverse ++ counter) [] output))
        hone
        (by simpa [middle, List.reverse_cons, List.append_assoc] using hrest)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htrans

private def enumerate_inc_restore_true_evals
    (work input unary counter : List Bool) (output : List (Option Bool))
    (bit : Option Bool) :
    EvalsToInTime bertrandCandidateComputer.step
      (enumerateCfg (some .incRestore) ⟨bit, true⟩
        input unary counter work output)
      (some (enumerateCfg (some .emitStart) ⟨none, true⟩
        input unary (work.reverse ++ counter) [] output))
      (work.length + 1) := by
  induction work generalizing counter bit with
  | nil =>
      simpa using enumerateEvalsToInTimeOne
        (enumerate_step_inc_restore_nil_true input unary counter output bit)
  | cons head tail ih =>
      let middle := enumerateCfg (some .incRestore) ⟨some head, true⟩
        input unary (head :: counter) tail output
      have hone : EvalsToInTime bertrandCandidateComputer.step
          (enumerateCfg (some .incRestore) ⟨bit, true⟩
            input unary counter (head :: tail) output)
          (some middle) 1 :=
        enumerateEvalsToInTimeOne (by
          simpa [middle, enumeratePoppedBit] using
            enumerate_step_inc_restore_cons head tail input unary counter
              output ⟨bit, true⟩)
      have hrest := ih (head :: counter) (some head)
      have htrans := EvalsToInTime.trans bertrandCandidateComputer.step
        1 (tail.length + 1)
        (enumerateCfg (some .incRestore) ⟨bit, true⟩
          input unary counter (head :: tail) output)
        middle
        (some (enumerateCfg (some .emitStart) ⟨none, true⟩
          input unary ((head :: tail).reverse ++ counter) [] output))
        hone
        (by simpa [middle, List.reverse_cons, List.append_assoc] using hrest)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htrans

private def enumerateIncrementTime (bits : List Bool) : ℕ :=
  (bits.length + 1) + ((binarySuccBits bits).length + 1)

private def enumerate_increment_false_evals
    (bits input unary : List Bool) (output : List (Option Bool)) :
    EvalsToInTime bertrandCandidateComputer.step
      (enumerateCfg (some .incCarry) enumerateInitialState
        input unary bits [] output)
      (some (enumerateCfg (some .count) enumerateInitialState
        input unary (binarySuccBits bits) [] output))
      (enumerateIncrementTime bits) := by
  have hcarry := enumerate_inc_carry_evals bits input unary [] output
    enumerateInitialState
  have hrestore := enumerate_inc_restore_false_evals
    (binarySuccBits bits).reverse input unary [] output none
  have htrans := EvalsToInTime.trans bertrandCandidateComputer.step
    (bits.length + 1) ((binarySuccBits bits).reverse.length + 1)
    (enumerateCfg (some .incCarry) enumerateInitialState
      input unary bits [] output)
    (enumerateCfg (some .incRestore) ⟨none, false⟩
      input unary [] (binarySuccBits bits).reverse output)
    (some (enumerateCfg (some .count) enumerateInitialState
      input unary (binarySuccBits bits) [] output))
    (by simpa [enumerateInitialState] using hcarry)
    (by simpa using hrestore)
  simpa [enumerateIncrementTime, Nat.add_comm] using htrans

private def enumerate_increment_true_evals
    (bits input unary : List Bool) (output : List (Option Bool)) :
    EvalsToInTime bertrandCandidateComputer.step
      (enumerateCfg (some .incCarry) ⟨none, true⟩
        input unary bits [] output)
      (some (enumerateCfg (some .emitStart) ⟨none, true⟩
        input unary (binarySuccBits bits) [] output))
      (enumerateIncrementTime bits) := by
  have hcarry := enumerate_inc_carry_evals bits input unary [] output
    ⟨none, true⟩
  have hrestore := enumerate_inc_restore_true_evals
    (binarySuccBits bits).reverse input unary [] output none
  have htrans := EvalsToInTime.trans bertrandCandidateComputer.step
    (bits.length + 1) ((binarySuccBits bits).reverse.length + 1)
    (enumerateCfg (some .incCarry) ⟨none, true⟩
      input unary bits [] output)
    (enumerateCfg (some .incRestore) ⟨none, true⟩
      input unary [] (binarySuccBits bits).reverse output)
    (some (enumerateCfg (some .emitStart) ⟨none, true⟩
      input unary (binarySuccBits bits) [] output))
    (by simpa using hcarry)
    (by simpa using hrestore)
  simpa [enumerateIncrementTime, Nat.add_comm] using htrans

private def enumerate_emit_copy_evals
    (bits input unary work : List Bool) (output : List (Option Bool))
    (state : EnumerateState) :
    EvalsToInTime bertrandCandidateComputer.step
      (enumerateCfg (some .emitCopy) state input unary bits work output)
      (some (enumerateCfg (some .emitRestore)
        ⟨none, state.returnToEmit⟩ input unary []
        (bits.reverse ++ work)
        (bits.reverse.map some ++ output)))
      (bits.length + 1) := by
  induction bits generalizing work output state with
  | nil =>
      simpa using enumerateEvalsToInTimeOne
        (enumerate_step_emit_copy_nil input unary work output state)
  | cons bit bits ih =>
      let nextState := enumeratePoppedBit state (some bit)
      let middle := enumerateCfg (some .emitCopy) nextState input unary bits
        (bit :: work) (some bit :: output)
      have hone : EvalsToInTime bertrandCandidateComputer.step
          (enumerateCfg (some .emitCopy) state input unary
            (bit :: bits) work output)
          (some middle) 1 :=
        enumerateEvalsToInTimeOne (by
          simpa [middle, nextState] using
            enumerate_step_emit_copy_cons bit bits input unary work output state)
      have hrest := ih (bit :: work) (some bit :: output) nextState
      have htrans := EvalsToInTime.trans bertrandCandidateComputer.step
        1 (bits.length + 1)
        (enumerateCfg (some .emitCopy) state input unary
          (bit :: bits) work output)
        middle
        (some (enumerateCfg (some .emitRestore)
          ⟨none, state.returnToEmit⟩ input unary []
          ((bit :: bits).reverse ++ work)
          ((bit :: bits).reverse.map some ++ output)))
        hone
        (by
          simpa [middle, nextState, enumeratePoppedBit,
            List.reverse_cons, List.map_append,
            List.append_assoc] using hrest)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htrans

private def enumerate_emit_restore_evals
    (work input unary counter : List Bool) (output : List (Option Bool))
    (state : EnumerateState) :
    EvalsToInTime bertrandCandidateComputer.step
      (enumerateCfg (some .emitRestore) state input unary counter work output)
      (some (enumerateCfg (some .candidates)
        ⟨none, state.returnToEmit⟩ input unary
        (work.reverse ++ counter) [] output))
      (work.length + 1) := by
  induction work generalizing counter state with
  | nil =>
      simpa using enumerateEvalsToInTimeOne
        (enumerate_step_emit_restore_nil input unary counter output state)
  | cons head tail ih =>
      let nextState := enumeratePoppedBit state (some head)
      let middle := enumerateCfg (some .emitRestore) nextState input unary
        (head :: counter) tail output
      have hone : EvalsToInTime bertrandCandidateComputer.step
          (enumerateCfg (some .emitRestore) state input unary counter
            (head :: tail) output)
          (some middle) 1 :=
        enumerateEvalsToInTimeOne (by
          simpa [middle, nextState] using
            enumerate_step_emit_restore_cons head tail input unary counter
              output state)
      have hrest := ih (head :: counter) nextState
      have htrans := EvalsToInTime.trans bertrandCandidateComputer.step
        1 (tail.length + 1)
        (enumerateCfg (some .emitRestore) state input unary counter
          (head :: tail) output)
        middle
        (some (enumerateCfg (some .candidates)
          ⟨none, state.returnToEmit⟩ input unary
          ((head :: tail).reverse ++ counter) [] output))
        hone
        (by
          simpa [middle, nextState, enumeratePoppedBit,
            List.reverse_cons, List.append_assoc] using hrest)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htrans

private def enumerateEmitTime (bits : List Bool) : ℕ :=
  2 * bits.length + 3

private def enumerate_emit_evals
    (bits input unary : List Bool) (output : List (Option Bool))
    (state : EnumerateState) :
    EvalsToInTime bertrandCandidateComputer.step
      (enumerateCfg (some .emitStart) state input unary bits [] output)
      (some (enumerateCfg (some .candidates)
        ⟨none, state.returnToEmit⟩ input unary bits []
        (RawNatList.segment bits ++ output)))
      (enumerateEmitTime bits) := by
  let afterStart := enumerateCfg (some .emitCopy) state input unary bits []
    (none :: output)
  have hstart : EvalsToInTime bertrandCandidateComputer.step
      (enumerateCfg (some .emitStart) state input unary bits [] output)
      (some afterStart) 1 :=
    enumerateEvalsToInTimeOne (by
      simpa [afterStart] using
        enumerate_step_emit_start input unary bits [] output state)
  have hcopy := enumerate_emit_copy_evals bits input unary []
    (none :: output) state
  let afterCopy := enumerateCfg (some .emitRestore)
    ⟨none, state.returnToEmit⟩ input unary [] bits.reverse
    (bits.reverse.map some ++ none :: output)
  have hfirst := EvalsToInTime.trans bertrandCandidateComputer.step
    1 (bits.length + 1)
    (enumerateCfg (some .emitStart) state input unary bits [] output)
    afterStart
    (some afterCopy)
    hstart
    (by simpa [afterStart, afterCopy] using hcopy)
  have hrestore := enumerate_emit_restore_evals bits.reverse input unary []
    (bits.reverse.map some ++ none :: output)
    ⟨none, state.returnToEmit⟩
  have hall := EvalsToInTime.trans bertrandCandidateComputer.step
    (1 + (bits.length + 1)) (bits.reverse.length + 1)
    (enumerateCfg (some .emitStart) state input unary bits [] output)
    afterCopy
    (some (enumerateCfg (some .candidates)
      ⟨none, state.returnToEmit⟩ input unary bits []
      (RawNatList.segment bits ++ output)))
    (by simpa [Nat.add_comm] using hfirst)
    (by
      simpa [afterCopy, RawNatList.segment, List.append_assoc] using hrestore)
  simpa [enumerateEmitTime, two_mul, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm] using hall

private def enumerate_cleanup_evals
    (bits : List Bool) (output : List (Option Bool))
    (state : EnumerateState) :
    EvalsToInTime bertrandCandidateComputer.step
      (enumerateCfg (some .cleanup) state [] [] bits [] output)
      (some (enumerateCfg none enumerateInitialState [] [] [] [] output))
      (bits.length + 1) := by
  induction bits generalizing state with
  | nil =>
      simpa using enumerateEvalsToInTimeOne
        (enumerate_step_cleanup_nil output state)
  | cons bit bits ih =>
      let nextState := enumeratePoppedBit state (some bit)
      let middle := enumerateCfg (some .cleanup) nextState
        [] [] bits [] output
      have hone : EvalsToInTime bertrandCandidateComputer.step
          (enumerateCfg (some .cleanup) state
            [] [] (bit :: bits) [] output)
          (some middle) 1 :=
        enumerateEvalsToInTimeOne (by
          simpa [middle, nextState] using
            enumerate_step_cleanup_cons bit bits output state)
      have hrest := ih nextState
      have htrans := EvalsToInTime.trans bertrandCandidateComputer.step
        1 (bits.length + 1)
        (enumerateCfg (some .cleanup) state
          [] [] (bit :: bits) [] output)
        middle
        (some (enumerateCfg none enumerateInitialState [] [] [] [] output))
        hone
        (by simpa [middle] using hrest)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htrans

private def enumerateCountTime : ℕ → ℕ → ℕ
  | 0, _ => 1
  | remaining + 1, processed =>
      1 + enumerateIncrementTime (encodeNat processed) +
        enumerateCountTime remaining (processed + 1)

private def enumerate_count_evals
    (remaining processed : ℕ) (output : List (Option Bool)) :
    EvalsToInTime bertrandCandidateComputer.step
      (enumerateCfg (some .count) enumerateInitialState
        (unaryEncodeNat remaining) (unaryEncodeNat processed)
        (encodeNat processed) [] output)
      (some (enumerateCfg (some .emitStart) enumerateInitialState
        [] (unaryEncodeNat (processed + remaining))
        (encodeNat (processed + remaining)) [] output))
      (enumerateCountTime remaining processed) := by
  induction remaining generalizing processed with
  | zero =>
      simpa [enumerateCountTime] using
        enumerateEvalsToInTimeOne
          (enumerate_step_count_nil (unaryEncodeNat processed)
            (encodeNat processed) output)
  | succ remaining ih =>
      let afterPop := enumerateCfg (some .incCarry) enumerateInitialState
        (unaryEncodeNat remaining) (unaryEncodeNat (processed + 1))
        (encodeNat processed) [] output
      have hpop : EvalsToInTime bertrandCandidateComputer.step
          (enumerateCfg (some .count) enumerateInitialState
            (unaryEncodeNat (remaining + 1)) (unaryEncodeNat processed)
            (encodeNat processed) [] output)
          (some afterPop) 1 :=
        enumerateEvalsToInTimeOne (by
          simpa [afterPop, unaryEncodeNat] using
            enumerate_step_count_cons (unaryEncodeNat remaining)
              (unaryEncodeNat processed) (encodeNat processed) output)
      have hinc := enumerate_increment_false_evals
        (encodeNat processed) (unaryEncodeNat remaining)
        (unaryEncodeNat (processed + 1)) output
      let afterInc := enumerateCfg (some .count) enumerateInitialState
        (unaryEncodeNat remaining) (unaryEncodeNat (processed + 1))
        (encodeNat (processed + 1)) [] output
      have hfirst := EvalsToInTime.trans bertrandCandidateComputer.step
        1 (enumerateIncrementTime (encodeNat processed))
        (enumerateCfg (some .count) enumerateInitialState
          (unaryEncodeNat (remaining + 1)) (unaryEncodeNat processed)
          (encodeNat processed) [] output)
        afterPop
        (some afterInc)
        hpop
        (by
          simpa [afterPop, afterInc, binarySuccBits_encodeNat] using hinc)
      have hrest := ih (processed + 1)
      have hall := EvalsToInTime.trans bertrandCandidateComputer.step
        (1 + enumerateIncrementTime (encodeNat processed))
        (enumerateCountTime remaining (processed + 1))
        (enumerateCfg (some .count) enumerateInitialState
          (unaryEncodeNat (remaining + 1)) (unaryEncodeNat processed)
          (encodeNat processed) [] output)
        afterInc
        (some (enumerateCfg (some .emitStart) enumerateInitialState
          [] (unaryEncodeNat (processed + (remaining + 1)))
          (encodeNat (processed + (remaining + 1))) [] output))
        (by simpa [Nat.add_comm] using hfirst)
        (by
          simpa [afterInc, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using hrest)
      simpa [enumerateCountTime, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using hall

private def encodedIntervalSuffix (count current : ℕ) :
    List (Option Bool) :=
  (intervalFrom count current).reverse.flatMap
    (fun value => RawNatList.segment (encodeNat value))

private def enumerateCandidateTime : ℕ → ℕ → ℕ
  | 0, current => (encodeNat current).length + 2
  | count + 1, current =>
      1 + enumerateIncrementTime (encodeNat current) +
        enumerateEmitTime (encodeNat (current + 1)) +
        enumerateCandidateTime count (current + 1)

private def enumerate_candidates_evals
    (count current : ℕ) (output : List (Option Bool))
    (state : EnumerateState) :
    EvalsToInTime bertrandCandidateComputer.step
      (enumerateCfg (some .candidates) state []
        (unaryEncodeNat count) (encodeNat current) [] output)
      (some (enumerateCfg none enumerateInitialState [] [] [] []
        (encodedIntervalSuffix count current ++ output)))
      (enumerateCandidateTime count current) := by
  induction count generalizing current output state with
  | zero =>
      let afterPop := enumerateCfg (some .cleanup)
        (enumeratePoppedBit state none) [] [] (encodeNat current) [] output
      have hpop : EvalsToInTime bertrandCandidateComputer.step
          (enumerateCfg (some .candidates) state [] []
            (encodeNat current) [] output)
          (some afterPop) 1 :=
        enumerateEvalsToInTimeOne (by
          simpa [afterPop] using
            enumerate_step_candidates_nil [] (encodeNat current) output state)
      have hcleanup := enumerate_cleanup_evals
        (encodeNat current) output (enumeratePoppedBit state none)
      have hall := EvalsToInTime.trans bertrandCandidateComputer.step
        1 ((encodeNat current).length + 1)
        (enumerateCfg (some .candidates) state [] []
          (encodeNat current) [] output)
        afterPop
        (some (enumerateCfg none enumerateInitialState [] [] [] [] output))
        hpop
        (by simpa [afterPop] using hcleanup)
      simpa [enumerateCandidateTime, encodedIntervalSuffix, intervalFrom,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hall
  | succ count ih =>
      let afterPop := enumerateCfg (some .incCarry) ⟨none, true⟩
        [] (unaryEncodeNat count) (encodeNat current) [] output
      have hpop : EvalsToInTime bertrandCandidateComputer.step
          (enumerateCfg (some .candidates) state []
            (unaryEncodeNat (count + 1)) (encodeNat current) [] output)
          (some afterPop) 1 :=
        enumerateEvalsToInTimeOne (by
          simpa [afterPop, unaryEncodeNat] using
            enumerate_step_candidates_cons (unaryEncodeNat count) []
              (encodeNat current) output state)
      have hinc := enumerate_increment_true_evals
        (encodeNat current) [] (unaryEncodeNat count) output
      let afterInc := enumerateCfg (some .emitStart) ⟨none, true⟩
        [] (unaryEncodeNat count) (encodeNat (current + 1)) [] output
      have hfirst := EvalsToInTime.trans bertrandCandidateComputer.step
        1 (enumerateIncrementTime (encodeNat current))
        (enumerateCfg (some .candidates) state []
          (unaryEncodeNat (count + 1)) (encodeNat current) [] output)
        afterPop
        (some afterInc)
        hpop
        (by
          simpa [afterPop, afterInc, binarySuccBits_encodeNat] using hinc)
      have hemit := enumerate_emit_evals (encodeNat (current + 1)) []
        (unaryEncodeNat count) output ⟨none, true⟩
      let afterEmit := enumerateCfg (some .candidates) ⟨none, true⟩
        [] (unaryEncodeNat count) (encodeNat (current + 1)) []
        (RawNatList.segment (encodeNat (current + 1)) ++ output)
      have hsecond := EvalsToInTime.trans bertrandCandidateComputer.step
        (1 + enumerateIncrementTime (encodeNat current))
        (enumerateEmitTime (encodeNat (current + 1)))
        (enumerateCfg (some .candidates) state []
          (unaryEncodeNat (count + 1)) (encodeNat current) [] output)
        afterInc
        (some afterEmit)
        (by simpa [Nat.add_comm] using hfirst)
        (by simpa [afterInc, afterEmit] using hemit)
      have hrest := ih (current + 1)
        (RawNatList.segment (encodeNat (current + 1)) ++ output)
        ⟨none, true⟩
      have hall := EvalsToInTime.trans bertrandCandidateComputer.step
        ((1 + enumerateIncrementTime (encodeNat current)) +
          enumerateEmitTime (encodeNat (current + 1)))
        (enumerateCandidateTime count (current + 1))
        (enumerateCfg (some .candidates) state []
          (unaryEncodeNat (count + 1)) (encodeNat current) [] output)
        afterEmit
        (some (enumerateCfg none enumerateInitialState [] [] [] []
          (encodedIntervalSuffix (count + 1) current ++ output)))
        (by simpa [Nat.add_comm] using hsecond)
        (by
          simpa [afterEmit, encodedIntervalSuffix, intervalFrom,
            List.reverse_cons, List.flatMap_append,
            List.append_assoc] using hrest)
      simpa [enumerateCandidateTime, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using hall

private theorem enumerateIncrementTime_encodeNat_le (n : ℕ) :
    enumerateIncrementTime (encodeNat n) ≤ 2 * n + 3 := by
  have hbits := BinaryNatLists.encodeNat_length_le n
  have hsucc := binarySuccBits_length_le (encodeNat n)
  simp only [enumerateIncrementTime]
  omega

private theorem enumerateEmitTime_encodeNat_le (n : ℕ) :
    enumerateEmitTime (encodeNat n) ≤ 2 * n + 3 := by
  have hbits := BinaryNatLists.encodeNat_length_le n
  simp only [enumerateEmitTime]
  omega

private theorem enumerateCountTime_le (remaining processed : ℕ) :
    enumerateCountTime remaining processed ≤
      2 * remaining * (processed + remaining + 2) + 1 := by
  induction remaining generalizing processed with
  | zero => simp [enumerateCountTime]
  | succ remaining ih =>
      have hinc := enumerateIncrementTime_encodeNat_le processed
      have hrest := ih (processed + 1)
      rw [enumerateCountTime]
      calc
        1 + enumerateIncrementTime (encodeNat processed) +
            enumerateCountTime remaining (processed + 1) ≤
            1 + (2 * processed + 3) +
              (2 * remaining * (processed + 1 + remaining + 2) + 1) := by
                omega
        _ ≤ 2 * (remaining + 1) *
              (processed + (remaining + 1) + 2) + 1 := by
                nlinarith

private theorem enumerateCandidateTime_le (count current : ℕ) :
    enumerateCandidateTime count current ≤
      5 * (count + 1) * (current + count + 2) := by
  induction count generalizing current with
  | zero =>
      have hbits := BinaryNatLists.encodeNat_length_le current
      simp only [enumerateCandidateTime]
      nlinarith
  | succ count ih =>
      have hinc := enumerateIncrementTime_encodeNat_le current
      have hemit := enumerateEmitTime_encodeNat_le (current + 1)
      have hrest := ih (current + 1)
      rw [enumerateCandidateTime]
      calc
        1 + enumerateIncrementTime (encodeNat current) +
            enumerateEmitTime (encodeNat (current + 1)) +
            enumerateCandidateTime count (current + 1) ≤
            1 + (2 * current + 3) + (2 * (current + 1) + 3) +
              5 * (count + 1) * (current + 1 + count + 2) := by
                omega
        _ ≤ 5 * (count + 1 + 1) *
              (current + (count + 1) + 2) := by
                nlinarith

private theorem flatMap_segment_reverse_map_encode (xs : List ℕ) :
    (xs.map encodeNat).reverse.flatMap RawNatList.segment =
      xs.reverse.flatMap
        (fun value => RawNatList.segment (encodeNat value)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp [List.reverse_cons, List.flatMap_append, ih]

private theorem rawNatList_encode_bertrandCandidates (q : ℕ) :
    RawNatList.encode (bertrandCandidates q) =
      encodedIntervalSuffix q q ++
        RawNatList.segment (encodeNat q) := by
  simp [RawNatList.encode, RawNatList.payloads, bertrandCandidates,
    encodedIntervalSuffix, List.reverse_cons,
    flatMap_segment_reverse_map_encode, List.flatMap_append]

private theorem enumerate_initList_eq_cfg (input : List Bool) :
    initList bertrandCandidateComputer input =
      enumerateCfg (some .count) enumerateInitialState input [] [] [] [] := by
  unfold initList enumerateCfg
  congr
  funext index
  cases index <;> rfl

private theorem enumerate_haltList_eq_cfg (output : List (Option Bool)) :
    haltList bertrandCandidateComputer output =
      enumerateCfg none enumerateInitialState [] [] [] [] output := by
  unfold haltList enumerateCfg
  congr
  funext index
  cases index <;> rfl

private def enumerateTotalTime (q : ℕ) : ℕ :=
  enumerateCountTime q 0 + enumerateEmitTime (encodeNat q) +
    enumerateCandidateTime q q

private theorem enumerateTotalTime_le (q : ℕ) :
    enumerateTotalTime q ≤ 16 * (q + 1) ^ 2 := by
  have hcount := enumerateCountTime_le q 0
  have hemit := enumerateEmitTime_encodeNat_le q
  have hcandidates := enumerateCandidateTime_le q q
  simp only [enumerateTotalTime]
  nlinarith [sq_nonneg (q : ℤ)]

/-- The concrete enumerator emits exactly `[q + 1, ..., 2q]` in at most
`16(q+1)^2` steps from the unary scan-bound encoding. -/
def bertrandCandidate_outputsInTime (q : ℕ) :
    TM2OutputsInTime bertrandCandidateComputer (unaryEncodeNat q)
      (some (RawNatList.encode (bertrandCandidates q)))
      (16 * (q + 1) ^ 2) := by
  have hcount := enumerate_count_evals q 0 []
  have hemit := enumerate_emit_evals (encodeNat q) []
    (unaryEncodeNat q) [] enumerateInitialState
  let afterCount := enumerateCfg (some .emitStart) enumerateInitialState
    [] (unaryEncodeNat q) (encodeNat q) [] []
  let afterEmit := enumerateCfg (some .candidates) enumerateInitialState
    [] (unaryEncodeNat q) (encodeNat q) []
    (RawNatList.segment (encodeNat q))
  have hfirst := EvalsToInTime.trans bertrandCandidateComputer.step
    (enumerateCountTime q 0) (enumerateEmitTime (encodeNat q))
    (enumerateCfg (some .count) enumerateInitialState
      (unaryEncodeNat q) [] [] [] [])
    afterCount
    (some afterEmit)
    (by
      simpa [afterCount, unaryEncodeNat, encodeNat, encodeNum] using hcount)
    (by simpa [afterCount, afterEmit, enumerateInitialState] using hemit)
  have hcandidates := enumerate_candidates_evals q q
    (RawNatList.segment (encodeNat q)) enumerateInitialState
  have hall := EvalsToInTime.trans bertrandCandidateComputer.step
    (enumerateCountTime q 0 + enumerateEmitTime (encodeNat q))
    (enumerateCandidateTime q q)
    (enumerateCfg (some .count) enumerateInitialState
      (unaryEncodeNat q) [] [] [] [])
    afterEmit
    (some (enumerateCfg none enumerateInitialState [] [] [] []
      (RawNatList.encode (bertrandCandidates q))))
    (by simpa [Nat.add_comm] using hfirst)
    (by
      rw [rawNatList_encode_bertrandCandidates]
      simpa [afterEmit, encodedIntervalSuffix] using hcandidates)
  have hmono : EvalsToInTime bertrandCandidateComputer.step
      (enumerateCfg (some .count) enumerateInitialState
        (unaryEncodeNat q) [] [] [] [])
      (some (enumerateCfg none enumerateInitialState [] [] [] []
        (RawNatList.encode (bertrandCandidates q))))
      (16 * (q + 1) ^ 2) :=
    evalsToInTimeMono
      (by simpa [enumerateTotalTime, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using hall)
      (enumerateTotalTime_le q)
  rw [TM2OutputsInTime, enumerate_initList_eq_cfg]
  simp only [Option.map_some]
  rw [enumerate_haltList_eq_cfg]
  exact hmono

/-- Genuine polynomial-time enumeration of the Bertrand interval.  Unary
input is intentional: the eventual full compiler establishes `q` by scanning
an explicit CSP input of length at least `q`. -/
noncomputable def bertrandCandidatesComputableInPolyTime :
    @TM2ComputableInPolyTime ℕ (List ℕ) unaryFinEncodingNat
      RawNatList.finEncoding bertrandCandidates where
  tm := bertrandCandidateComputer
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl (Option Bool)
  time := 16 * (Polynomial.X + 1) ^ 2
  outputsFun q := by
    simpa [unaryFinEncodingNat, RawNatList.finEncoding, Equiv.refl,
      Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add,
      Polynomial.eval_natCast, Polynomial.eval_one, Polynomial.eval_X] using
        bertrandCandidate_outputsInTime q

/-! ## Unary Bertrand-candidate stream

The candidate-primality machine below consumes unary naturals.  Converting the
binary fields emitted by `bertrandCandidateComputer` back to unary would add an
unnecessary adapter.  This companion producer keeps the original binary
enumerator intact for serialization while emitting the same semantic list in
`RawUnaryNatList.finEncoding` for the internal prime scan.
-/

/-- Unary input, a decreasing iteration counter, the current unary value,
scratch storage used to preserve that value while emitting it, and output. -/
inductive UnaryBertrandStack
  | input
  | remaining
  | current
  | work
  | output
  deriving DecidableEq, Fintype

/-- Copy the input twice, emit the count field, emit each larger candidate,
and erase all non-output stacks. -/
inductive UnaryBertrandLabel
  | count
  | emitStart
  | emitCopy
  | emitRestore
  | candidates
  | cleanup
  deriving DecidableEq, Fintype

abbrev UnaryBertrandState := Option Bool

private def unaryBertrandObserved
    (_state : UnaryBertrandState) (bit : Option Bool) :
    UnaryBertrandState :=
  bit

private def unaryBertrandMarkerPresent : UnaryBertrandState → Bool
  | some _ => true
  | none => false

private def unaryBertrandHeldBit : UnaryBertrandState → Bool
  | some bit => bit
  | none => false

private def UnaryBertrandAlphabet (_ : UnaryBertrandStack) : Type := Bool

/-- Generate the unary length field `q`, followed by the candidates
`q+1, ..., 2q`, in stack-oriented reverse-field order. -/
def unaryBertrandCandidateProgram :
    UnaryBertrandLabel →
      TM2.Stmt UnaryBertrandAlphabet UnaryBertrandLabel UnaryBertrandState
  | .count =>
      .pop .input unaryBertrandObserved <|
        .branch unaryBertrandMarkerPresent
          (.push .remaining unaryBertrandHeldBit <|
            .push .current unaryBertrandHeldBit <|
              .goto (fun _ => .count))
          (.goto (fun _ => .emitStart))
  | .emitStart =>
      .push .output (fun _ => false) <|
        .goto (fun _ => .emitCopy)
  | .emitCopy =>
      .pop .current unaryBertrandObserved <|
        .branch unaryBertrandMarkerPresent
          (.push .work unaryBertrandHeldBit <|
            .push .output unaryBertrandHeldBit <|
              .goto (fun _ => .emitCopy))
          (.goto (fun _ => .emitRestore))
  | .emitRestore =>
      .pop .work unaryBertrandObserved <|
        .branch unaryBertrandMarkerPresent
          (.push .current unaryBertrandHeldBit <|
            .goto (fun _ => .emitRestore))
          (.goto (fun _ => .candidates))
  | .candidates =>
      .pop .remaining unaryBertrandObserved <|
        .branch unaryBertrandMarkerPresent
          (.push .current unaryBertrandHeldBit <|
            .goto (fun _ => .emitStart))
          (.goto (fun _ => .cleanup))
  | .cleanup =>
      .pop .current unaryBertrandObserved <|
        .branch unaryBertrandMarkerPresent
          (.goto (fun _ => .cleanup))
          (.load (fun _ => none) .halt)

/-- Concrete producer for the unary-delimited Bertrand candidate stream. -/
def unaryBertrandCandidateComputer : FinTM2 where
  K := UnaryBertrandStack
  k₀ := .input
  k₁ := .output
  Γ := UnaryBertrandAlphabet
  Λ := UnaryBertrandLabel
  main := .count
  σ := UnaryBertrandState
  initialState := none
  Γk₀Fin := Bool.fintype
  m := unaryBertrandCandidateProgram

def unaryBertrandStackContents
    (input remaining current work output : List Bool) :
    (index : UnaryBertrandStack) → List (UnaryBertrandAlphabet index)
  | .input => input
  | .remaining => remaining
  | .current => current
  | .work => work
  | .output => output

def unaryBertrandCfg
    (label : Option UnaryBertrandLabel) (state : UnaryBertrandState)
    (input remaining current work output : List Bool) :
    unaryBertrandCandidateComputer.Cfg where
  l := label
  var := state
  stk := unaryBertrandStackContents input remaining current work output

private theorem unaryBertrand_step_count_cons
    (bit : Bool) (input remaining current work output : List Bool)
    (state : UnaryBertrandState) :
    unaryBertrandCandidateComputer.step
        (unaryBertrandCfg (some .count) state (bit :: input) remaining
          current work output) =
      some (unaryBertrandCfg (some .count) (some bit) input
        (bit :: remaining) (bit :: current) work output) := by
  simp [unaryBertrandCandidateComputer, FinTM2.step, unaryBertrandCfg,
    unaryBertrandCandidateProgram, unaryBertrandStackContents,
    UnaryBertrandAlphabet, unaryBertrandObserved,
    unaryBertrandMarkerPresent, unaryBertrandHeldBit, Function.update]
  funext index
  cases index <;> rfl

private theorem unaryBertrand_step_count_nil
    (remaining current work output : List Bool)
    (state : UnaryBertrandState) :
    unaryBertrandCandidateComputer.step
        (unaryBertrandCfg (some .count) state [] remaining current work
          output) =
      some (unaryBertrandCfg (some .emitStart) none [] remaining current work
        output) := by
  simp [unaryBertrandCandidateComputer, FinTM2.step, unaryBertrandCfg,
    unaryBertrandCandidateProgram, unaryBertrandStackContents,
    UnaryBertrandAlphabet, unaryBertrandObserved,
    unaryBertrandMarkerPresent]

private theorem unaryBertrand_step_emitStart
    (input remaining current work output : List Bool)
    (state : UnaryBertrandState) :
    unaryBertrandCandidateComputer.step
        (unaryBertrandCfg (some .emitStart) state input remaining current work
          output) =
      some (unaryBertrandCfg (some .emitCopy) state input remaining current
        work (false :: output)) := by
  simp [unaryBertrandCandidateComputer, FinTM2.step, unaryBertrandCfg,
    unaryBertrandCandidateProgram, unaryBertrandStackContents,
    UnaryBertrandAlphabet]
  funext index
  cases index <;> rfl

private theorem unaryBertrand_step_emitCopy_cons
    (bit : Bool) (input remaining current work output : List Bool)
    (state : UnaryBertrandState) :
    unaryBertrandCandidateComputer.step
        (unaryBertrandCfg (some .emitCopy) state input remaining
          (bit :: current) work output) =
      some (unaryBertrandCfg (some .emitCopy) (some bit) input remaining
        current (bit :: work) (bit :: output)) := by
  simp [unaryBertrandCandidateComputer, FinTM2.step, unaryBertrandCfg,
    unaryBertrandCandidateProgram, unaryBertrandStackContents,
    UnaryBertrandAlphabet, unaryBertrandObserved,
    unaryBertrandMarkerPresent, unaryBertrandHeldBit, Function.update]
  funext index
  cases index <;> rfl

private theorem unaryBertrand_step_emitCopy_nil
    (input remaining work output : List Bool)
    (state : UnaryBertrandState) :
    unaryBertrandCandidateComputer.step
        (unaryBertrandCfg (some .emitCopy) state input remaining [] work
          output) =
      some (unaryBertrandCfg (some .emitRestore) none input remaining [] work
        output) := by
  simp [unaryBertrandCandidateComputer, FinTM2.step, unaryBertrandCfg,
    unaryBertrandCandidateProgram, unaryBertrandStackContents,
    UnaryBertrandAlphabet, unaryBertrandObserved,
    unaryBertrandMarkerPresent]

private theorem unaryBertrand_step_emitRestore_cons
    (bit : Bool) (input remaining current work output : List Bool)
    (state : UnaryBertrandState) :
    unaryBertrandCandidateComputer.step
        (unaryBertrandCfg (some .emitRestore) state input remaining current
          (bit :: work) output) =
      some (unaryBertrandCfg (some .emitRestore) (some bit) input remaining
        (bit :: current) work output) := by
  simp [unaryBertrandCandidateComputer, FinTM2.step, unaryBertrandCfg,
    unaryBertrandCandidateProgram, unaryBertrandStackContents,
    UnaryBertrandAlphabet, unaryBertrandObserved,
    unaryBertrandMarkerPresent, unaryBertrandHeldBit, Function.update]
  funext index
  cases index <;> rfl

private theorem unaryBertrand_step_emitRestore_nil
    (input remaining current output : List Bool)
    (state : UnaryBertrandState) :
    unaryBertrandCandidateComputer.step
        (unaryBertrandCfg (some .emitRestore) state input remaining current []
          output) =
      some (unaryBertrandCfg (some .candidates) none input remaining current
        [] output) := by
  simp [unaryBertrandCandidateComputer, FinTM2.step, unaryBertrandCfg,
    unaryBertrandCandidateProgram, unaryBertrandStackContents,
    UnaryBertrandAlphabet, unaryBertrandObserved,
    unaryBertrandMarkerPresent]

private theorem unaryBertrand_step_candidates_cons
    (bit : Bool) (input remaining current work output : List Bool)
    (state : UnaryBertrandState) :
    unaryBertrandCandidateComputer.step
        (unaryBertrandCfg (some .candidates) state input (bit :: remaining)
          current work output) =
      some (unaryBertrandCfg (some .emitStart) (some bit) input remaining
        (bit :: current) work output) := by
  simp [unaryBertrandCandidateComputer, FinTM2.step, unaryBertrandCfg,
    unaryBertrandCandidateProgram, unaryBertrandStackContents,
    UnaryBertrandAlphabet, unaryBertrandObserved,
    unaryBertrandMarkerPresent, unaryBertrandHeldBit, Function.update]
  funext index
  cases index <;> rfl

private theorem unaryBertrand_step_candidates_nil
    (input current work output : List Bool)
    (state : UnaryBertrandState) :
    unaryBertrandCandidateComputer.step
        (unaryBertrandCfg (some .candidates) state input [] current work
          output) =
      some (unaryBertrandCfg (some .cleanup) none input [] current work
        output) := by
  simp [unaryBertrandCandidateComputer, FinTM2.step, unaryBertrandCfg,
    unaryBertrandCandidateProgram, unaryBertrandStackContents,
    UnaryBertrandAlphabet, unaryBertrandObserved,
    unaryBertrandMarkerPresent]

private theorem unaryBertrand_step_cleanup_cons
    (bit : Bool) (input remaining current work output : List Bool)
    (state : UnaryBertrandState) :
    unaryBertrandCandidateComputer.step
        (unaryBertrandCfg (some .cleanup) state input remaining
          (bit :: current) work output) =
      some (unaryBertrandCfg (some .cleanup) (some bit) input remaining
        current work output) := by
  simp [unaryBertrandCandidateComputer, FinTM2.step, unaryBertrandCfg,
    unaryBertrandCandidateProgram, unaryBertrandStackContents,
    UnaryBertrandAlphabet, unaryBertrandObserved,
    unaryBertrandMarkerPresent]
  funext index
  cases index <;> rfl

private theorem unaryBertrand_step_cleanup_nil
    (input remaining work output : List Bool)
    (state : UnaryBertrandState) :
    unaryBertrandCandidateComputer.step
        (unaryBertrandCfg (some .cleanup) state input remaining [] work
          output) =
      some (unaryBertrandCfg none none input remaining [] work output) := by
  simp [unaryBertrandCandidateComputer, FinTM2.step, unaryBertrandCfg,
    unaryBertrandCandidateProgram, unaryBertrandStackContents,
    UnaryBertrandAlphabet, unaryBertrandObserved,
    unaryBertrandMarkerPresent]

private def unaryBertrandEvalsToInTimeOne
    {start finish : unaryBertrandCandidateComputer.Cfg}
    (hstep : unaryBertrandCandidateComputer.step start = some finish) :
    EvalsToInTime unaryBertrandCandidateComputer.step start (some finish) 1
    where
  steps := 1
  evals_in_steps := by
    simpa [Function.iterate_one] using hstep
  steps_le_m := Nat.le_refl 1

private def unaryBertrand_count_evals
    (input remaining current work output : List Bool)
    (state : UnaryBertrandState) :
    EvalsToInTime unaryBertrandCandidateComputer.step
      (unaryBertrandCfg (some .count) state input remaining current work output)
      (some (unaryBertrandCfg (some .emitStart) none []
        (input.reverse ++ remaining) (input.reverse ++ current) work output))
      (input.length + 1) := by
  induction input generalizing remaining current state with
  | nil =>
      simpa using unaryBertrandEvalsToInTimeOne
        (unaryBertrand_step_count_nil remaining current work output state)
  | cons bit input ih =>
      let middle := unaryBertrandCfg (some .count) (some bit) input
        (bit :: remaining) (bit :: current) work output
      have hone : EvalsToInTime unaryBertrandCandidateComputer.step
          (unaryBertrandCfg (some .count) state (bit :: input) remaining
            current work output)
          (some middle) 1 :=
        unaryBertrandEvalsToInTimeOne (by
          simpa [middle] using unaryBertrand_step_count_cons bit input
            remaining current work output state)
      have hrest := ih (bit :: remaining) (bit :: current) (some bit)
      have hall := EvalsToInTime.trans unaryBertrandCandidateComputer.step
        1 (input.length + 1)
        (unaryBertrandCfg (some .count) state (bit :: input) remaining
          current work output)
        middle
        (some (unaryBertrandCfg (some .emitStart) none []
          ((bit :: input).reverse ++ remaining)
          ((bit :: input).reverse ++ current) work output))
        hone
        (by
          simpa [middle, List.reverse_cons, List.append_assoc] using hrest)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hall

private def unaryBertrand_emitCopy_evals
    (bits input remaining work output : List Bool)
    (state : UnaryBertrandState) :
    EvalsToInTime unaryBertrandCandidateComputer.step
      (unaryBertrandCfg (some .emitCopy) state input remaining bits work output)
      (some (unaryBertrandCfg (some .emitRestore) none input remaining []
        (bits.reverse ++ work) (bits.reverse ++ output)))
      (bits.length + 1) := by
  induction bits generalizing work output state with
  | nil =>
      simpa using unaryBertrandEvalsToInTimeOne
        (unaryBertrand_step_emitCopy_nil input remaining work output state)
  | cons bit bits ih =>
      let middle := unaryBertrandCfg (some .emitCopy) (some bit) input
        remaining bits (bit :: work) (bit :: output)
      have hone : EvalsToInTime unaryBertrandCandidateComputer.step
          (unaryBertrandCfg (some .emitCopy) state input remaining
            (bit :: bits) work output)
          (some middle) 1 :=
        unaryBertrandEvalsToInTimeOne (by
          simpa [middle] using unaryBertrand_step_emitCopy_cons bit input
            remaining bits work output state)
      have hrest := ih (bit :: work) (bit :: output) (some bit)
      have hall := EvalsToInTime.trans unaryBertrandCandidateComputer.step
        1 (bits.length + 1)
        (unaryBertrandCfg (some .emitCopy) state input remaining
          (bit :: bits) work output)
        middle
        (some (unaryBertrandCfg (some .emitRestore) none input remaining []
          ((bit :: bits).reverse ++ work)
          ((bit :: bits).reverse ++ output)))
        hone
        (by
          simpa [middle, List.reverse_cons, List.append_assoc] using hrest)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hall

private def unaryBertrand_emitRestore_evals
    (work input remaining current output : List Bool)
    (state : UnaryBertrandState) :
    EvalsToInTime unaryBertrandCandidateComputer.step
      (unaryBertrandCfg (some .emitRestore) state input remaining current work
        output)
      (some (unaryBertrandCfg (some .candidates) none input remaining
        (work.reverse ++ current) [] output))
      (work.length + 1) := by
  induction work generalizing current state with
  | nil =>
      simpa using unaryBertrandEvalsToInTimeOne
        (unaryBertrand_step_emitRestore_nil input remaining current output state)
  | cons bit work ih =>
      let middle := unaryBertrandCfg (some .emitRestore) (some bit) input
        remaining (bit :: current) work output
      have hone : EvalsToInTime unaryBertrandCandidateComputer.step
          (unaryBertrandCfg (some .emitRestore) state input remaining current
            (bit :: work) output)
          (some middle) 1 :=
        unaryBertrandEvalsToInTimeOne (by
          simpa [middle] using unaryBertrand_step_emitRestore_cons bit input
            remaining current work output state)
      have hrest := ih (bit :: current) (some bit)
      have hall := EvalsToInTime.trans unaryBertrandCandidateComputer.step
        1 (work.length + 1)
        (unaryBertrandCfg (some .emitRestore) state input remaining current
          (bit :: work) output)
        middle
        (some (unaryBertrandCfg (some .candidates) none input remaining
          ((bit :: work).reverse ++ current) [] output))
        hone
        (by
          simpa [middle, List.reverse_cons, List.append_assoc] using hrest)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hall

private def unaryBertrand_emit_evals
    (bits remaining output : List Bool) (state : UnaryBertrandState) :
    EvalsToInTime unaryBertrandCandidateComputer.step
      (unaryBertrandCfg (some .emitStart) state [] remaining bits [] output)
      (some (unaryBertrandCfg (some .candidates) none [] remaining bits []
        (bits.reverse ++ false :: output)))
      (2 * bits.length + 3) := by
  let afterStart := unaryBertrandCfg (some .emitCopy) state [] remaining bits []
    (false :: output)
  have hstart : EvalsToInTime unaryBertrandCandidateComputer.step
      (unaryBertrandCfg (some .emitStart) state [] remaining bits [] output)
      (some afterStart) 1 :=
    unaryBertrandEvalsToInTimeOne (by
      simpa [afterStart] using unaryBertrand_step_emitStart [] remaining bits
        [] output state)
  have hcopy := unaryBertrand_emitCopy_evals bits [] remaining []
    (false :: output) state
  let afterCopy := unaryBertrandCfg (some .emitRestore) none [] remaining []
    bits.reverse (bits.reverse ++ false :: output)
  have hfirst := EvalsToInTime.trans unaryBertrandCandidateComputer.step
    1 (bits.length + 1)
    (unaryBertrandCfg (some .emitStart) state [] remaining bits [] output)
    afterStart
    (some afterCopy)
    hstart
    (by simpa [afterStart, afterCopy] using hcopy)
  have hrestore := unaryBertrand_emitRestore_evals bits.reverse [] remaining []
    (bits.reverse ++ false :: output) none
  have hall := EvalsToInTime.trans unaryBertrandCandidateComputer.step
    (1 + (bits.length + 1)) (bits.reverse.length + 1)
    (unaryBertrandCfg (some .emitStart) state [] remaining bits [] output)
    afterCopy
    (some (unaryBertrandCfg (some .candidates) none [] remaining bits []
      (bits.reverse ++ false :: output)))
    (by simpa [Nat.add_comm] using hfirst)
    (by simpa [afterCopy] using hrestore)
  simpa [two_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hall

private def unaryBertrand_cleanup_evals
    (current input remaining work output : List Bool)
    (state : UnaryBertrandState) :
    EvalsToInTime unaryBertrandCandidateComputer.step
      (unaryBertrandCfg (some .cleanup) state input remaining current work
        output)
      (some (unaryBertrandCfg none none input remaining [] work output))
      (current.length + 1) := by
  induction current generalizing state with
  | nil =>
      simpa using unaryBertrandEvalsToInTimeOne
        (unaryBertrand_step_cleanup_nil input remaining work output state)
  | cons bit current ih =>
      let middle := unaryBertrandCfg (some .cleanup) (some bit) input remaining
        current work output
      have hone : EvalsToInTime unaryBertrandCandidateComputer.step
          (unaryBertrandCfg (some .cleanup) state input remaining
            (bit :: current) work output)
          (some middle) 1 :=
        unaryBertrandEvalsToInTimeOne (by
          simpa [middle] using unaryBertrand_step_cleanup_cons bit input
            remaining current work output state)
      have hrest := ih (some bit)
      have hall := EvalsToInTime.trans unaryBertrandCandidateComputer.step
        1 (current.length + 1)
        (unaryBertrandCfg (some .cleanup) state input remaining
          (bit :: current) work output)
        middle
        (some (unaryBertrandCfg none none input remaining [] work output))
        hone
        (by simpa [middle] using hrest)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hall

theorem unaryEncodeNat_eq_replicate_true (n : ℕ) :
    unaryEncodeNat n = List.replicate n true := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [unaryEncodeNat, List.replicate_succ, ih]

private theorem unaryEncodeNat_reverse_eq (n : ℕ) :
    (unaryEncodeNat n).reverse = unaryEncodeNat n := by
  rw [unaryEncodeNat_eq_replicate_true, List.reverse_replicate]

private theorem unaryBertrand_segment_append (n : ℕ)
    (output : List Bool) :
    (unaryEncodeNat n).reverse ++ false :: output =
      RawUnaryNatList.segment n ++ output := by
  simp [RawUnaryNatList.segment, unaryEncodeNat_eq_replicate_true,
    List.append_assoc]

private def encodedUnaryIntervalSuffix (count current : ℕ) : List Bool :=
  (intervalFrom count current).reverse.flatMap RawUnaryNatList.segment

private theorem encodedUnaryIntervalSuffix_succ (count current : ℕ) :
    encodedUnaryIntervalSuffix (count + 1) current =
      encodedUnaryIntervalSuffix count (current + 1) ++
        RawUnaryNatList.segment (current + 1) := by
  simp [encodedUnaryIntervalSuffix, intervalFrom, List.reverse_cons,
    List.flatMap_append]

private def unaryBertrandLoopTime : ℕ → ℕ → ℕ
  | 0, current => current + 2
  | count + 1, current =>
      1 + (2 * (current + 1) + 3) +
        unaryBertrandLoopTime count (current + 1)

private def unaryBertrand_candidates_evals
    (count current : ℕ) (output : List Bool)
    (state : UnaryBertrandState) :
    EvalsToInTime unaryBertrandCandidateComputer.step
      (unaryBertrandCfg (some .candidates) state [] (unaryEncodeNat count)
        (unaryEncodeNat current) [] output)
      (some (unaryBertrandCfg none none [] [] [] []
        (encodedUnaryIntervalSuffix count current ++ output)))
      (unaryBertrandLoopTime count current) := by
  induction count generalizing current output state with
  | zero =>
      let afterCandidates := unaryBertrandCfg (some .cleanup) none [] []
        (unaryEncodeNat current) [] output
      have hcandidates : EvalsToInTime unaryBertrandCandidateComputer.step
          (unaryBertrandCfg (some .candidates) state [] []
            (unaryEncodeNat current) [] output)
          (some afterCandidates) 1 :=
        unaryBertrandEvalsToInTimeOne (by
          simpa [afterCandidates] using unaryBertrand_step_candidates_nil []
            (unaryEncodeNat current) [] output state)
      have hcleanup := unaryBertrand_cleanup_evals
        (unaryEncodeNat current) [] [] [] output none
      have hall := EvalsToInTime.trans unaryBertrandCandidateComputer.step
        1 ((unaryEncodeNat current).length + 1)
        (unaryBertrandCfg (some .candidates) state [] []
          (unaryEncodeNat current) [] output)
        afterCandidates
        (some (unaryBertrandCfg none none [] [] [] [] output))
        hcandidates
        (by simpa [afterCandidates] using hcleanup)
      simpa [unaryBertrandLoopTime, encodedUnaryIntervalSuffix,
        unaryEncodeNat_length, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using hall
  | succ count ih =>
      let afterCandidates := unaryBertrandCfg (some .emitStart) (some true) []
        (unaryEncodeNat count) (unaryEncodeNat (current + 1)) [] output
      have hcandidates : EvalsToInTime unaryBertrandCandidateComputer.step
          (unaryBertrandCfg (some .candidates) state []
            (unaryEncodeNat (count + 1)) (unaryEncodeNat current) [] output)
          (some afterCandidates) 1 :=
        unaryBertrandEvalsToInTimeOne (by
          simpa [afterCandidates, unaryEncodeNat] using
            unaryBertrand_step_candidates_cons true []
              (unaryEncodeNat count) (unaryEncodeNat current) [] output state)
      have hemit := unaryBertrand_emit_evals
        (unaryEncodeNat (current + 1)) (unaryEncodeNat count) output
        (some true)
      let afterEmit := unaryBertrandCfg (some .candidates) none []
        (unaryEncodeNat count) (unaryEncodeNat (current + 1)) []
        (RawUnaryNatList.segment (current + 1) ++ output)
      have hfirst := EvalsToInTime.trans unaryBertrandCandidateComputer.step
        1 (2 * (unaryEncodeNat (current + 1)).length + 3)
        (unaryBertrandCfg (some .candidates) state []
          (unaryEncodeNat (count + 1)) (unaryEncodeNat current) [] output)
        afterCandidates
        (some afterEmit)
        hcandidates
        (by
          simpa [afterCandidates, afterEmit, unaryBertrand_segment_append]
            using hemit)
      have hrest := ih (current + 1)
        (RawUnaryNatList.segment (current + 1) ++ output) none
      have hall := EvalsToInTime.trans unaryBertrandCandidateComputer.step
        (1 + (2 * (unaryEncodeNat (current + 1)).length + 3))
        (unaryBertrandLoopTime count (current + 1))
        (unaryBertrandCfg (some .candidates) state []
          (unaryEncodeNat (count + 1)) (unaryEncodeNat current) [] output)
        afterEmit
        (some (unaryBertrandCfg none none [] [] [] []
          (encodedUnaryIntervalSuffix (count + 1) current ++ output)))
        (by simpa [Nat.add_comm] using hfirst)
        (by
          rw [encodedUnaryIntervalSuffix_succ]
          simpa [afterEmit, List.append_assoc] using hrest)
      simpa [unaryBertrandLoopTime, unaryEncodeNat_length, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using hall

private theorem unaryBertrandLoopTime_eq (count current : ℕ) :
    unaryBertrandLoopTime count current =
      2 * count * current + count ^ 2 + 6 * count + current + 2 := by
  induction count generalizing current with
  | zero => simp [unaryBertrandLoopTime]
  | succ count ih =>
      rw [unaryBertrandLoopTime, ih (current + 1)]
      ring

private def unaryBertrandTotalTime (q : ℕ) : ℕ :=
  (q + 1) + (2 * q + 3) + unaryBertrandLoopTime q q

private theorem unaryBertrandTotalTime_le (q : ℕ) :
    unaryBertrandTotalTime q ≤ 6 * (q + 1) ^ 2 := by
  rw [unaryBertrandTotalTime, unaryBertrandLoopTime_eq]
  nlinarith

private theorem rawUnaryNatList_encode_bertrandCandidates (q : ℕ) :
    RawUnaryNatList.encode (bertrandCandidates q) =
      encodedUnaryIntervalSuffix q q ++ RawUnaryNatList.segment q := by
  simp [RawUnaryNatList.encode, RawUnaryNatList.payloads,
    bertrandCandidates, encodedUnaryIntervalSuffix, List.reverse_cons,
    List.flatMap_append]

theorem unaryBertrand_initList_eq_cfg (input : List Bool) :
    initList unaryBertrandCandidateComputer input =
      unaryBertrandCfg (some .count) none input [] [] [] [] := by
  unfold initList unaryBertrandCfg
  congr
  funext index
  cases index <;> rfl

theorem unaryBertrand_haltList_eq_cfg (output : List Bool) :
    haltList unaryBertrandCandidateComputer output =
      unaryBertrandCfg none none [] [] [] [] output := by
  unfold haltList unaryBertrandCfg
  congr
  funext index
  cases index <;> rfl

/-- The unary-stream producer emits exactly `[q+1, ..., 2q]` in at most
`6(q+1)^2` steps, including the empty `q = 0` stream. -/
def unaryBertrandCandidate_outputsInTime (q : ℕ) :
    TM2OutputsInTime unaryBertrandCandidateComputer (unaryEncodeNat q)
      (some (RawUnaryNatList.encode (bertrandCandidates q)))
      (6 * (q + 1) ^ 2) := by
  have hcount := unaryBertrand_count_evals (unaryEncodeNat q) [] [] [] [] none
  let afterCount := unaryBertrandCfg (some .emitStart) none []
    (unaryEncodeNat q) (unaryEncodeNat q) [] []
  have hcount' : EvalsToInTime unaryBertrandCandidateComputer.step
      (unaryBertrandCfg (some .count) none (unaryEncodeNat q) [] [] [] [])
      (some afterCount) (q + 1) := by
    simpa [afterCount, unaryEncodeNat_length, unaryEncodeNat_reverse_eq] using
      hcount
  have hemit := unaryBertrand_emit_evals (unaryEncodeNat q)
    (unaryEncodeNat q) [] none
  let afterEmit := unaryBertrandCfg (some .candidates) none []
    (unaryEncodeNat q) (unaryEncodeNat q) []
    (RawUnaryNatList.segment q)
  have hemit' : EvalsToInTime unaryBertrandCandidateComputer.step
      afterCount (some afterEmit) (2 * q + 3) := by
    simpa [afterCount, afterEmit, unaryEncodeNat_length,
      unaryBertrand_segment_append] using hemit
  have hfirst := EvalsToInTime.trans unaryBertrandCandidateComputer.step
    (q + 1) (2 * q + 3)
    (unaryBertrandCfg (some .count) none (unaryEncodeNat q) [] [] [] [])
    afterCount
    (some afterEmit)
    hcount' hemit'
  have hcandidates := unaryBertrand_candidates_evals q q
    (RawUnaryNatList.segment q) none
  have hall := EvalsToInTime.trans unaryBertrandCandidateComputer.step
    ((q + 1) + (2 * q + 3)) (unaryBertrandLoopTime q q)
    (unaryBertrandCfg (some .count) none (unaryEncodeNat q) [] [] [] [])
    afterEmit
    (some (unaryBertrandCfg none none [] [] [] []
      (RawUnaryNatList.encode (bertrandCandidates q))))
    (by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hfirst)
    (by
      rw [rawUnaryNatList_encode_bertrandCandidates]
      simpa [afterEmit] using hcandidates)
  have hmono : EvalsToInTime unaryBertrandCandidateComputer.step
      (unaryBertrandCfg (some .count) none (unaryEncodeNat q) [] [] [] [])
      (some (unaryBertrandCfg none none [] [] [] []
        (RawUnaryNatList.encode (bertrandCandidates q))))
      (6 * (q + 1) ^ 2) :=
    evalsToInTimeMono
      (by
        simpa [unaryBertrandTotalTime, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using hall)
      (unaryBertrandTotalTime_le q)
  rw [TM2OutputsInTime, unaryBertrand_initList_eq_cfg]
  simp only [Option.map_some]
  rw [unaryBertrand_haltList_eq_cfg]
  exact hmono

/-- Genuine quadratic-time generation of the internal unary candidate stream
from the unary full-input bound. -/
noncomputable def unaryBertrandCandidatesComputableInPolyTime :
    @TM2ComputableInPolyTime ℕ (List ℕ) unaryFinEncodingNat
      RawUnaryNatList.finEncoding bertrandCandidates where
  tm := unaryBertrandCandidateComputer
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := 6 * (Polynomial.X + 1) ^ 2
  outputsFun q := by
    simpa [unaryFinEncodingNat, RawUnaryNatList.finEncoding, Equiv.refl,
      Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add,
      Polynomial.eval_natCast, Polynomial.eval_one, Polynomial.eval_X] using
        unaryBertrandCandidate_outputsInTime q

/-- The complete unary candidate stream remains quadratic in the unary scan
bound. -/
theorem unaryBertrandCandidateStream_length_le (q : ℕ) :
    (RawUnaryNatList.encode (bertrandCandidates q)).length ≤
      2 * q ^ 2 + 2 * q + 1 := by
  have hsum := List.sum_le_card_nsmul (bertrandCandidates q) (2 * q) (by
    intro value hvalue
    exact (mem_bertrandCandidates_iff q value).mp hvalue |>.2)
  have hsum' : (bertrandCandidates q).sum ≤ 2 * q ^ 2 := by
    simpa [bertrandCandidates_length, Nat.mul_assoc, Nat.mul_comm,
      Nat.mul_left_comm, pow_two] using hsum
  rw [RawUnaryNatList.encode_length, bertrandCandidates_length]
  nlinarith [hsum']


end LeanNPHardness.MachinePrimitives
