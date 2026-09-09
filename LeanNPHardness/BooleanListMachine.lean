import LeanNPHardness.MachineRun

namespace LeanNPHardness.MachinePrimitives

open Computability Turing

namespace RawBoolList

/-- The literal Boolean stream encoding used between the future repeated
divisibility driver and the checked aggregation pass. -/
def finEncoding : FinEncoding (List Bool) where
  Γ := Bool
  encode := id
  decode := some
  decode_encode := fun _ => rfl
  ΓFin := Bool.fintype

@[simp]
theorem encode_eq (results : List Bool) :
    finEncoding.encode results = results :=
  rfl

end RawBoolList

def allFalseFrom : Bool → List Bool → Bool
  | aggregate, [] => aggregate
  | aggregate, result :: results =>
      allFalseFrom (aggregate && !result) results

/-- `true` exactly when the input stream contains no `true` result. -/
def allFalse (results : List Bool) : Bool :=
  allFalseFrom true results

@[simp]
theorem allFalseFrom_false (results : List Bool) :
    allFalseFrom false results = false := by
  induction results with
  | nil => rfl
  | cons result results ih => simp [allFalseFrom, ih]


/-- Input and output stacks for the Boolean result fold. -/
inductive AllFalseStack
  | input
  | output
  deriving DecidableEq, Fintype

/-- The fold needs a single scanning label. -/
inductive AllFalseLabel
  | scan
  deriving DecidableEq, Fintype

/-- Finite control records the most recent pop and the running conjunction. -/
structure AllFalseState where
  observed : Option Bool
  aggregate : Bool
  deriving DecidableEq, Fintype

private def allFalseInitialState : AllFalseState :=
  ⟨none, true⟩

private def allFalseObserve
    (state : AllFalseState) : Option Bool → AllFalseState
  | some result => ⟨some result, state.aggregate && !result⟩
  | none => ⟨none, state.aggregate⟩

private def allFalseObservedPresent : AllFalseState → Bool
  | ⟨some _, _⟩ => true
  | _ => false

private def allFalseAggregate (state : AllFalseState) : Bool :=
  state.aggregate

private def AllFalseAlphabet (_index : AllFalseStack) : Type :=
  Bool

/-- Scan the result stream once, conjoin the negated results in finite control,
and emit the final Boolean. -/
def allFalseProgram :
    AllFalseLabel → TM2.Stmt AllFalseAlphabet AllFalseLabel AllFalseState
  | .scan =>
      .pop .input allFalseObserve <|
        .branch allFalseObservedPresent
          (.goto fun _ => .scan)
          (.push .output allFalseAggregate <|
            .load (fun _ => allFalseInitialState) .halt)

/-- Concrete two-stack finite machine for Boolean result aggregation. -/
def allFalseComputer : FinTM2 where
  K := AllFalseStack
  k₀ := .input
  k₁ := .output
  Γ := AllFalseAlphabet
  Λ := AllFalseLabel
  main := .scan
  σ := AllFalseState
  initialState := allFalseInitialState
  Γk₀Fin := Bool.fintype
  m := allFalseProgram

private def allFalseStackContents
    (input output : List Bool) :
    (index : AllFalseStack) → List (AllFalseAlphabet index)
  | .input => input
  | .output => output

private def allFalseCfg (label : Option AllFalseLabel)
    (state : AllFalseState) (input output : List Bool) :
    allFalseComputer.Cfg where
  l := label
  var := state
  stk := allFalseStackContents input output

private def allFalseEvalsToInTimeOne
    {start finish : allFalseComputer.Cfg}
    (hstep : allFalseComputer.step start = some finish) :
    EvalsToInTime allFalseComputer.step start (some finish) 1 where
  steps := 1
  evals_in_steps := by
    simpa [Function.iterate_one] using hstep
  steps_le_m := Nat.le_refl 1

private theorem allFalse_step_cons
    (result : Bool) (results output : List Bool) (state : AllFalseState) :
    allFalseComputer.step
        (allFalseCfg (some .scan) state (result :: results) output) =
      some (allFalseCfg (some .scan)
        (allFalseObserve state (some result)) results output) := by
  rcases state with ⟨observed, aggregate⟩
  simp [allFalseComputer, FinTM2.step, allFalseCfg, allFalseProgram,
    allFalseStackContents, AllFalseAlphabet, allFalseObserve,
    allFalseObservedPresent, Function.update]
  funext index
  cases index <;> rfl

private theorem allFalse_step_nil
    (output : List Bool) (state : AllFalseState) :
    allFalseComputer.step
        (allFalseCfg (some .scan) state [] output) =
      some (allFalseCfg none allFalseInitialState []
        (state.aggregate :: output)) := by
  rcases state with ⟨observed, aggregate⟩
  simp [allFalseComputer, FinTM2.step, allFalseCfg, allFalseProgram,
    allFalseStackContents, AllFalseAlphabet, allFalseObserve,
    allFalseObservedPresent, allFalseAggregate, allFalseInitialState,
    Function.update]
  funext index
  cases index <;> rfl

private def allFalse_scan_evals
    (results output : List Bool) (state : AllFalseState) :
    EvalsToInTime allFalseComputer.step
      (allFalseCfg (some .scan) state results output)
      (some (allFalseCfg none allFalseInitialState []
        (allFalseFrom state.aggregate results :: output)))
      (results.length + 1) := by
  induction results generalizing state with
  | nil =>
      simpa [allFalseFrom] using allFalseEvalsToInTimeOne
        (allFalse_step_nil output state)
  | cons result results ih =>
      let middle := allFalseCfg (some .scan)
        (allFalseObserve state (some result)) results output
      have hone : EvalsToInTime allFalseComputer.step
          (allFalseCfg (some .scan) state (result :: results) output)
          (some middle) 1 :=
        allFalseEvalsToInTimeOne (by
          simpa [middle] using allFalse_step_cons result results output state)
      have hrest := ih (allFalseObserve state (some result))
      have htrans := EvalsToInTime.trans allFalseComputer.step
        1 (results.length + 1)
        (allFalseCfg (some .scan) state (result :: results) output)
        middle
        (some (allFalseCfg none allFalseInitialState []
          (allFalseFrom state.aggregate (result :: results) :: output)))
        hone
        (by
          simpa [middle, allFalseFrom, allFalseObserve] using hrest)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htrans

private theorem allFalse_initList_eq_cfg (results : List Bool) :
    initList allFalseComputer results =
      allFalseCfg (some .scan) allFalseInitialState results [] := by
  unfold initList allFalseCfg
  congr
  funext index
  cases index <;> rfl

private theorem allFalse_haltList_eq_cfg (result : Bool) :
    haltList allFalseComputer [result] =
      allFalseCfg none allFalseInitialState [] [result] := by
  unfold haltList allFalseCfg
  congr
  funext index
  cases index <;> rfl

/-- Boolean aggregation takes at most one scan step per result plus the final
empty-input step. -/
def allFalse_outputsInTime (results : List Bool) :
    TM2OutputsInTime allFalseComputer results
      (some (encodeBool (allFalse results))) (results.length + 1) := by
  have hscan := allFalse_scan_evals results [] allFalseInitialState
  rw [TM2OutputsInTime, allFalse_initList_eq_cfg]
  simp only [Option.map_some, encodeBool, List.pure_def]
  rw [allFalse_haltList_eq_cfg]
  simpa [allFalse, allFalseInitialState, encodeBool] using hscan

/-- Genuine linear-time finite-machine aggregation of a Boolean result list. -/
noncomputable def allFalseComputableInPolyTime :
    @TM2ComputableInPolyTime (List Bool) Bool RawBoolList.finEncoding
      finEncodingBoolBool allFalse where
  tm := allFalseComputer
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := Polynomial.X + 1
  outputsFun results := by
    simpa [RawBoolList.finEncoding, finEncodingBoolBool, Equiv.refl,
      Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_X] using
        allFalse_outputsInTime results


end LeanNPHardness.MachinePrimitives
