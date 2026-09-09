import LeanNPHardness.UnaryDivisibilityMachine
import LeanNPHardness.BooleanListMachine

/-!
Bounded number-theory components extracted from phd-thesis-lean at 84be78d.
All enumeration, trial-division and prime-selection runtime bounds use the
explicit unary/padded input encodings; no binary-input polynomial bound is
asserted for these algorithms.
-/

namespace LeanNPHardness.MachinePrimitives

open Computability Turing
open LeanNPHardness.MachineComposition LeanNPHardness.BoundedPrime

/-! ## Repeated padded divisibility

The pair generator emits a stack-oriented list of complete unary-pair fields.
The driver below restores one field at a time on the existing divisibility
machine's input stack, runs that checked program, and resumes scanning after
the component halt.  Processing the reversed field stream while pushing each
Boolean result restores the source pair order on the output stack.
-/

/-- Apply the divisibility predicate to every pair in source order. -/
def pairDivisionResults (pairs : List (ℕ × ℕ)) : List Bool :=
  pairs.map fun pair => decide (pair.2 ∣ pair.1)

/-- The raw outer input plus every stack of the existing divisibility
machine. -/
abbrev PairDvdStack := Unit ⊕ DvdStack

/-- Outer field scanning or execution of one divisibility-machine label. -/
inductive PairDvdLabel
  | scan
  | dvd (label : DvdLabel)
  deriving DecidableEq, Fintype

/-- The outer scanner remembers its last pop; the component state is kept
unchanged while a raw field is restored. -/
structure PairDvdState where
  observed : Option (Option Bool)
  dvd : DvdState
  deriving DecidableEq, Fintype

private def pairDvdInitialState : PairDvdState :=
  ⟨none, dvdInitialState⟩

private def pairDvdObserve
    (state : PairDvdState) (observed : Option (Option Bool)) : PairDvdState :=
  { state with observed := observed }

private def pairDvdResetObserved (state : PairDvdState) : PairDvdState :=
  { state with observed := none }

private def pairDvdSetComponent
    (state : PairDvdState) (dvd : DvdState) : PairDvdState :=
  { state with dvd := dvd }

private def pairDvdObservedPresent : PairDvdState → Bool
  | ⟨some _, _⟩ => true
  | _ => false

private def pairDvdObservedSymbol : PairDvdState → Bool
  | ⟨some (some _), _⟩ => true
  | _ => false

private def pairDvdObservedBit : PairDvdState → Bool
  | ⟨some (some bit), _⟩ => bit
  | _ => false

private def PairDvdAlphabet : PairDvdStack → Type
  | .inl _ => Option Bool
  | .inr index => DvdAlphabet index

/-- Lift a statement of the checked divisibility machine.  Reaching its halt
resets the outer observation and returns to the raw-field scanner. -/
private def liftDvdStmt :
    TM2.Stmt DvdAlphabet DvdLabel DvdState →
      TM2.Stmt PairDvdAlphabet PairDvdLabel PairDvdState
  | .push index write next =>
      .push (.inr index) (fun state => write state.dvd) (liftDvdStmt next)
  | .peek index read next =>
      .peek (.inr index)
        (fun state observed => pairDvdSetComponent state (read state.dvd observed))
        (liftDvdStmt next)
  | .pop index read next =>
      .pop (.inr index)
        (fun state observed => pairDvdSetComponent state (read state.dvd observed))
        (liftDvdStmt next)
  | .load update next =>
      .load (fun state => pairDvdSetComponent state (update state.dvd))
        (liftDvdStmt next)
  | .branch test yes no =>
      .branch (fun state => test state.dvd) (liftDvdStmt yes) (liftDvdStmt no)
  | .goto next => .goto (fun state => .dvd (next state.dvd))
  | .halt =>
      .load pairDvdResetObserved (.goto fun _ => .scan)

/-- Scan one reversed raw field into the component input stack, or halt when
the complete outer stream is exhausted. -/
def pairDvdProgram :
    PairDvdLabel → TM2.Stmt PairDvdAlphabet PairDvdLabel PairDvdState
  | .scan =>
      .pop (.inl ()) pairDvdObserve <|
        .branch pairDvdObservedPresent
          (.branch pairDvdObservedSymbol
            (.push (.inr .input) pairDvdObservedBit <|
              .load pairDvdResetObserved <|
                .goto fun _ => .scan)
            (.load pairDvdResetObserved <|
              .goto fun _ => .dvd .scanDividend))
          .halt
  | .dvd label => liftDvdStmt (unaryDvdProgram label)

/-- Concrete finite machine mapping a padded pair stream to its divisibility
result stream. -/
def pairDvdComputer : FinTM2 where
  K := PairDvdStack
  k₀ := .inl ()
  k₁ := .inr .output
  Γ := PairDvdAlphabet
  Λ := PairDvdLabel
  main := .scan
  σ := PairDvdState
  initialState := pairDvdInitialState
  Γk₀Fin := inferInstanceAs (Fintype (Option Bool))
  m := pairDvdProgram

private def pairDvdStackContents
    (input : List (Option Bool))
    (contents : (index : DvdStack) → List (DvdAlphabet index)) :
    (index : PairDvdStack) → List (PairDvdAlphabet index)
  | .inl _ => input
  | .inr index => contents index

/-- Embed a component configuration while fixing the unconsumed raw stream.
A component halt is represented by the outer scan label. -/
private def pairDvdLiftCfg (input : List (Option Bool))
    (cfg : unaryDvdComputer.Cfg) : pairDvdComputer.Cfg where
  l := match cfg.l with
    | none => some .scan
    | some label => some (.dvd label)
  var := ⟨none, cfg.var⟩
  stk := pairDvdStackContents input cfg.stk

private theorem pairDvdStackContents_update
    (input : List (Option Bool))
    (contents : (index : DvdStack) → List (DvdAlphabet index))
    (index : DvdStack) (value : List (DvdAlphabet index)) :
    Function.update (pairDvdStackContents input contents) (.inr index) value =
      pairDvdStackContents input (Function.update contents index value) := by
  funext target
  cases target with
  | inl _ =>
      simp [pairDvdStackContents, Function.update]
  | inr other =>
      by_cases h : other = index
      · subst other
        simp [pairDvdStackContents, Function.update]
      · simp [pairDvdStackContents, Function.update, h]

private theorem liftDvd_stepAux
    (stmt : TM2.Stmt DvdAlphabet DvdLabel DvdState)
    (state : DvdState)
    (contents : (index : DvdStack) → List (DvdAlphabet index))
    (input : List (Option Bool)) :
    TM2.stepAux (liftDvdStmt stmt) ⟨none, state⟩
        (pairDvdStackContents input contents) =
      pairDvdLiftCfg input (TM2.stepAux stmt state contents) := by
  induction stmt generalizing state contents with
  | push index write next ih =>
      simp only [liftDvdStmt, TM2.stepAux]
      rw [pairDvdStackContents_update]
      exact ih _ _
  | peek index read next ih =>
      simpa only [liftDvdStmt, TM2.stepAux, pairDvdStackContents,
        pairDvdSetComponent] using
          ih (read state (contents index).head?) contents
  | pop index read next ih =>
      simp only [liftDvdStmt, TM2.stepAux, pairDvdStackContents,
        pairDvdSetComponent]
      rw [pairDvdStackContents_update]
      exact ih _ _
  | load update next ih =>
      simpa only [liftDvdStmt, TM2.stepAux, pairDvdSetComponent] using
        ih (update state) contents
  | branch test yes no ihYes ihNo =>
      by_cases h : test state
      · simpa only [liftDvdStmt, TM2.stepAux, h, cond_true] using
          ihYes state contents
      · simpa only [liftDvdStmt, TM2.stepAux, h, cond_false] using
          ihNo state contents
  | goto next =>
      rfl
  | halt =>
      rfl

private theorem pairDvd_lift_step
    (input : List (Option Bool)) (label : DvdLabel) (state : DvdState)
    (contents : (index : DvdStack) → List (DvdAlphabet index)) :
    pairDvdComputer.step
        (pairDvdLiftCfg input ⟨some label, state, contents⟩) =
      some (pairDvdLiftCfg input
        (TM2.stepAux (unaryDvdProgram label) state contents)) := by
  simp only [pairDvdComputer, FinTM2.step, pairDvdLiftCfg,
    pairDvdProgram, unaryDvdComputer, TM2.step]
  exact congrArg some (liftDvd_stepAux _ _ _ _)

private theorem unaryDvd_iterate_none (steps : ℕ) :
    (flip Option.bind unaryDvdComputer.step)^[steps]
        (none : Option unaryDvdComputer.Cfg) = none := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
      rw [Function.iterate_succ_apply']
      rw [ih]
      rfl

private theorem pairDvd_iterate_lift
    (steps : ℕ) (input : List (Option Bool))
    (start finish : unaryDvdComputer.Cfg)
    (hrun :
      (flip Option.bind unaryDvdComputer.step)^[steps] (some start) =
        some finish) :
    (flip Option.bind pairDvdComputer.step)^[steps]
        (some (pairDvdLiftCfg input start)) =
      some (pairDvdLiftCfg input finish) := by
  induction steps generalizing start with
  | zero =>
      simpa using congrArg (Option.map (pairDvdLiftCfg input)) hrun
  | succ steps ih =>
      rw [Function.iterate_succ_apply] at hrun ⊢
      change (flip Option.bind unaryDvdComputer.step)^[steps]
          (unaryDvdComputer.step start) = some finish at hrun
      change (flip Option.bind pairDvdComputer.step)^[steps]
          (pairDvdComputer.step (pairDvdLiftCfg input start)) =
        some (pairDvdLiftCfg input finish)
      cases hlabel : start.l with
      | none =>
          have hnone : unaryDvdComputer.step start = none := by
            rcases start with ⟨current, state, contents⟩
            change current = none at hlabel
            subst current
            rfl
          rw [hnone] at hrun
          rw [unaryDvd_iterate_none] at hrun
          contradiction
      | some label =>
          let middle := TM2.stepAux (unaryDvdProgram label) start.var start.stk
          have hstep : unaryDvdComputer.step start = some middle := by
            rcases start with ⟨current, state, contents⟩
            simp [unaryDvdComputer, FinTM2.step] at hlabel ⊢
            subst current
            rfl
          rw [hstep] at hrun
          have hcfg :
              start = ⟨some label, start.var, start.stk⟩ := by
            rcases start with ⟨current, state, contents⟩
            change current = some label at hlabel
            subst current
            rfl
          rw [show pairDvdComputer.step (pairDvdLiftCfg input start) =
              some (pairDvdLiftCfg input middle) by
            rw [hcfg]
            simpa [middle] using
              pairDvd_lift_step input label start.var start.stk]
          exact ih middle hrun

private def pairDvd_lift_evals
    (input : List (Option Bool)) {start finish : unaryDvdComputer.Cfg}
    {bound : ℕ}
    (hrun : EvalsToInTime unaryDvdComputer.step start (some finish) bound) :
    EvalsToInTime pairDvdComputer.step
      (pairDvdLiftCfg input start) (some (pairDvdLiftCfg input finish)) bound where
  steps := hrun.steps
  evals_in_steps := pairDvd_iterate_lift hrun.steps input start finish
    hrun.evals_in_steps
  steps_le_m := hrun.steps_le_m

private def pairDvdEvalsToInTimeOne
    {start finish : pairDvdComputer.Cfg}
    (hstep : pairDvdComputer.step start = some finish) :
    EvalsToInTime pairDvdComputer.step start (some finish) 1 where
  steps := 1
  evals_in_steps := by
    simpa [Function.iterate_one] using hstep
  steps_le_m := Nat.le_refl 1

private theorem pairDvd_step_scan_some
    (bit : Bool) (input : List (Option Bool)) (field output : List Bool) :
    pairDvdComputer.step
        (pairDvdLiftCfg (some bit :: input)
          (dvdCfg none dvdInitialState field [] [] [] output)) =
      some (pairDvdLiftCfg input
        (dvdCfg none dvdInitialState (bit :: field) [] [] [] output)) := by
  simp [pairDvdComputer, FinTM2.step, pairDvdLiftCfg, pairDvdProgram,
    pairDvdStackContents, dvdCfg, dvdStackContents, PairDvdAlphabet,
    pairDvdInitialState, pairDvdObserve, pairDvdObservedPresent,
    pairDvdObservedSymbol, pairDvdObservedBit, pairDvdResetObserved,
    Function.update]
  funext index
  cases index with
  | inl _ => rfl
  | inr index =>
      cases index <;> rfl

private theorem pairDvd_step_scan_separator
    (input : List (Option Bool)) (field output : List Bool) :
    pairDvdComputer.step
        (pairDvdLiftCfg (none :: input)
          (dvdCfg none dvdInitialState field [] [] [] output)) =
      some (pairDvdLiftCfg input
        (dvdCfg (some .scanDividend) dvdInitialState
          field [] [] [] output)) := by
  simp [pairDvdComputer, FinTM2.step, pairDvdLiftCfg, pairDvdProgram,
    pairDvdStackContents, dvdCfg, dvdStackContents, PairDvdAlphabet,
    pairDvdInitialState, pairDvdObserve, pairDvdObservedPresent,
    pairDvdObservedSymbol, pairDvdResetObserved, Function.update]
  funext index
  cases index with
  | inl _ => rfl
  | inr index =>
      cases index <;> rfl

private def pairDvd_scan_bits_evals
    (bits : List Bool) (input : List (Option Bool))
    (field output : List Bool) :
    EvalsToInTime pairDvdComputer.step
      (pairDvdLiftCfg (bits.map some ++ input)
        (dvdCfg none dvdInitialState field [] [] [] output))
      (some (pairDvdLiftCfg input
        (dvdCfg none dvdInitialState
          (bits.reverse ++ field) [] [] [] output)))
      bits.length := by
  induction bits generalizing field with
  | nil =>
      exact
        { steps := 0
          evals_in_steps := rfl
          steps_le_m := Nat.le_refl 0 }
  | cons bit bits ih =>
      let middle := pairDvdLiftCfg (bits.map some ++ input)
        (dvdCfg none dvdInitialState (bit :: field) [] [] [] output)
      have hone : EvalsToInTime pairDvdComputer.step
          (pairDvdLiftCfg ((bit :: bits).map some ++ input)
            (dvdCfg none dvdInitialState field [] [] [] output))
          (some middle) 1 :=
        pairDvdEvalsToInTimeOne (by
          simpa [middle] using pairDvd_step_scan_some bit
            (bits.map some ++ input) field output)
      have hrest := ih (bit :: field)
      have htrans := EvalsToInTime.trans pairDvdComputer.step
        1 bits.length
        (pairDvdLiftCfg ((bit :: bits).map some ++ input)
          (dvdCfg none dvdInitialState field [] [] [] output))
        middle
        (some (pairDvdLiftCfg input
          (dvdCfg none dvdInitialState
            ((bit :: bits).reverse ++ field) [] [] [] output)))
        hone
        (by simpa [middle, List.reverse_cons, List.append_assoc] using hrest)
      simpa [Nat.add_comm] using htrans

private def pairDvd_parse_segment_evals
    (bits : List Bool) (input : List (Option Bool)) (output : List Bool) :
    EvalsToInTime pairDvdComputer.step
      (pairDvdLiftCfg (RawNatList.segment bits ++ input)
        (dvdCfg none dvdInitialState [] [] [] [] output))
      (some (pairDvdLiftCfg input
        (dvdCfg (some .scanDividend) dvdInitialState
          bits [] [] [] output)))
      (bits.length + 1) := by
  let middle := pairDvdLiftCfg (none :: input)
    (dvdCfg none dvdInitialState bits [] [] [] output)
  have hbits := pairDvd_scan_bits_evals bits.reverse (none :: input) [] output
  have hseparator := pairDvdEvalsToInTimeOne
    (pairDvd_step_scan_separator input bits output)
  have htrans := EvalsToInTime.trans pairDvdComputer.step
    bits.length 1
    (pairDvdLiftCfg (RawNatList.segment bits ++ input)
      (dvdCfg none dvdInitialState [] [] [] [] output))
    middle
    (some (pairDvdLiftCfg input
      (dvdCfg (some .scanDividend) dvdInitialState
        bits [] [] [] output)))
    (by simpa [middle, RawNatList.segment] using hbits)
    (by simpa [middle] using hseparator)
  exact evalsToInTimeMono htrans (by omega)

private noncomputable def pairDvd_pair_evals
    (pair : ℕ × ℕ) (input : List (Option Bool)) (output : List Bool) :
    EvalsToInTime pairDvdComputer.step
      (pairDvdLiftCfg
        (RawNatList.segment (UnaryNatPair.encode pair) ++ input)
        (dvdCfg none dvdInitialState [] [] [] [] output))
      (some (pairDvdLiftCfg input
        (dvdCfg none dvdInitialState [] [] [] []
          (decide (pair.2 ∣ pair.1) :: output))))
      (7 * (UnaryNatPair.encode pair).length + 17) := by
  have hparse := pairDvd_parse_segment_evals
    (UnaryNatPair.encode pair) input output
  have hcomponent := pairDvd_lift_evals input
    (unaryDvd_evals_with_output pair output)
  have htrans := EvalsToInTime.trans pairDvdComputer.step
    ((UnaryNatPair.encode pair).length + 1)
    (6 * (UnaryNatPair.encode pair).length + 16)
    (pairDvdLiftCfg
      (RawNatList.segment (UnaryNatPair.encode pair) ++ input)
      (dvdCfg none dvdInitialState [] [] [] [] output))
    (pairDvdLiftCfg input
      (dvdCfg (some .scanDividend) dvdInitialState
        (UnaryNatPair.encode pair) [] [] [] output))
    (some (pairDvdLiftCfg input
      (dvdCfg none dvdInitialState [] [] [] []
        (decide (pair.2 ∣ pair.1) :: output))))
    hparse hcomponent
  exact evalsToInTimeMono htrans (by omega)

@[simp]
theorem RawUnaryPairList.encode_cons
    (pair : ℕ × ℕ) (pairs : List (ℕ × ℕ)) :
    RawUnaryPairList.encode (pair :: pairs) =
      RawUnaryPairList.encode pairs ++
        RawNatList.segment (UnaryNatPair.encode pair) := by
  simp [RawUnaryPairList.encode, List.reverse_cons, List.flatMap_append]

@[simp]
theorem RawUnaryPairList.encode_length (pairs : List (ℕ × ℕ)) :
    (RawUnaryPairList.encode pairs).length =
      ((pairs.map fun pair => (UnaryNatPair.encode pair).length).sum +
        pairs.length) := by
  induction pairs with
  | nil => simp [RawUnaryPairList.encode]
  | cons pair pairs ih =>
      rw [RawUnaryPairList.encode_cons, List.length_append, ih]
      simp [RawNatList.segment]
      omega

/-- Including one separator per pair, the complete driver input for candidate
`n` remains quadratic in the padded candidate. -/
theorem trialDivisionPairStream_length_le (n : ℕ) :
    (RawUnaryPairList.encode (trialDivisionPairs n)).length ≤
      (2 * n + 1) * (n - 2) := by
  rw [RawUnaryPairList.encode_length, trialDivisionPairs_length]
  calc
    ((trialDivisionPairs n).map fun pair =>
        (UnaryNatPair.encode pair).length).sum + (n - 2) =
        trialDivisionInputSize n + (n - 2) := by
          rfl
    _ ≤ 2 * n * (n - 2) + (n - 2) :=
      Nat.add_le_add_right (trialDivisionInputSize_le n) (n - 2)
    _ = (2 * n + 1) * (n - 2) := by ring

private noncomputable def pairDvd_pairs_evals
    (pairs : List (ℕ × ℕ)) (input : List (Option Bool))
    (output : List Bool) :
    EvalsToInTime pairDvdComputer.step
      (pairDvdLiftCfg (RawUnaryPairList.encode pairs ++ input)
        (dvdCfg none dvdInitialState [] [] [] [] output))
      (some (pairDvdLiftCfg input
        (dvdCfg none dvdInitialState [] [] [] []
          (pairDivisionResults pairs ++ output))))
      (17 * (RawUnaryPairList.encode pairs).length) := by
  induction pairs generalizing input output with
  | nil =>
      exact
        { steps := 0
          evals_in_steps := rfl
          steps_le_m := Nat.le_refl 0 }
  | cons pair pairs ih =>
      let middle := pairDvdLiftCfg
        (RawNatList.segment (UnaryNatPair.encode pair) ++ input)
        (dvdCfg none dvdInitialState [] [] [] []
          (pairDivisionResults pairs ++ output))
      have hfirst : EvalsToInTime pairDvdComputer.step
          (pairDvdLiftCfg
            (RawUnaryPairList.encode (pair :: pairs) ++ input)
            (dvdCfg none dvdInitialState [] [] [] [] output))
          (some middle)
          (17 * (RawUnaryPairList.encode pairs).length) := by
        simpa [middle, RawUnaryPairList.encode_cons, List.append_assoc] using
          ih (RawNatList.segment (UnaryNatPair.encode pair) ++ input) output
      have hsecond : EvalsToInTime pairDvdComputer.step middle
          (some (pairDvdLiftCfg input
            (dvdCfg none dvdInitialState [] [] [] []
              (pairDivisionResults (pair :: pairs) ++ output))))
          (7 * (UnaryNatPair.encode pair).length + 17) := by
        simpa [middle, pairDivisionResults, List.append_assoc] using
          pairDvd_pair_evals pair input
            (pairDivisionResults pairs ++ output)
      have htrans := EvalsToInTime.trans pairDvdComputer.step
        (17 * (RawUnaryPairList.encode pairs).length)
        (7 * (UnaryNatPair.encode pair).length + 17)
        (pairDvdLiftCfg
          (RawUnaryPairList.encode (pair :: pairs) ++ input)
          (dvdCfg none dvdInitialState [] [] [] [] output))
        middle
        (some (pairDvdLiftCfg input
          (dvdCfg none dvdInitialState [] [] [] []
            (pairDivisionResults (pair :: pairs) ++ output))))
        hfirst hsecond
      apply evalsToInTimeMono htrans
      simp [RawUnaryPairList.encode_cons, RawNatList.segment]
      omega

private theorem pairDvd_step_scan_nil (output : List Bool) :
    pairDvdComputer.step
        (pairDvdLiftCfg []
          (dvdCfg none dvdInitialState [] [] [] [] output)) =
      some (haltList pairDvdComputer output) := by
  simp [pairDvdComputer, FinTM2.step, pairDvdLiftCfg, pairDvdProgram,
    pairDvdStackContents, dvdCfg, dvdStackContents, PairDvdAlphabet,
    pairDvdInitialState, pairDvdObserve, pairDvdObservedPresent,
    haltList, Function.update]
  funext index
  cases index with
  | inl _ => rfl
  | inr index =>
      cases index <;> rfl

private theorem pairDvd_initList_eq_cfg (input : List (Option Bool)) :
    initList pairDvdComputer input =
      pairDvdLiftCfg input
        (dvdCfg none dvdInitialState [] [] [] [] []) := by
  unfold initList pairDvdLiftCfg pairDvdComputer pairDvdInitialState dvdCfg
  congr
  funext index
  cases index with
  | inl _ => rfl
  | inr index =>
      cases index <;> rfl

/-- The repeated driver maps every padded pair field to its divisibility bit
in at most `17s + 1` steps for actual stream length `s`. -/
noncomputable def pairDvd_outputsInTime (pairs : List (ℕ × ℕ)) :
    TM2OutputsInTime pairDvdComputer (RawUnaryPairList.encode pairs)
      (some (pairDivisionResults pairs))
      (17 * (RawUnaryPairList.encode pairs).length + 1) := by
  have hpairs := pairDvd_pairs_evals pairs [] []
  have hfinal := pairDvdEvalsToInTimeOne
    (pairDvd_step_scan_nil (pairDivisionResults pairs))
  have htrans := EvalsToInTime.trans pairDvdComputer.step
    (17 * (RawUnaryPairList.encode pairs).length) 1
    (pairDvdLiftCfg (RawUnaryPairList.encode pairs)
      (dvdCfg none dvdInitialState [] [] [] [] []))
    (pairDvdLiftCfg []
      (dvdCfg none dvdInitialState [] [] [] []
        (pairDivisionResults pairs)))
    (some (haltList pairDvdComputer (pairDivisionResults pairs)))
    (by simpa using hpairs) hfinal
  rw [TM2OutputsInTime, pairDvd_initList_eq_cfg]
  simp only [Option.map_some]
  exact evalsToInTimeMono htrans (by omega)

/-- Genuine linear time in the padded pair-stream representation.  Combined
with the separate quadratic stream-size bound, this is the repeated
divisibility stage needed by bounded trial division. -/
noncomputable def pairDivisionResultsComputableInPolyTime :
    @TM2ComputableInPolyTime (List (ℕ × ℕ)) (List Bool)
      RawUnaryPairList.finEncoding RawBoolList.finEncoding
      pairDivisionResults where
  tm := pairDvdComputer
  inputAlphabet := Equiv.refl (Option Bool)
  outputAlphabet := Equiv.refl Bool
  time := 17 * Polynomial.X + 1
  outputsFun pairs := by
    simpa [RawUnaryPairList.finEncoding, RawBoolList.finEncoding, Equiv.refl,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_one,
      Polynomial.eval_natCast, Polynomial.eval_X] using
        pairDvd_outputsInTime pairs

/-- The exact Boolean result stream produced by applying divisibility to every
padded trial pair for `n`. -/
def trialDivisionResults (n : ℕ) : List Bool :=
  (trialDivisionPairs n).map fun pair => decide (pair.2 ∣ pair.1)

@[simp]
theorem pairDivisionResults_trialDivisionPairs (n : ℕ) :
    pairDivisionResults (trialDivisionPairs n) = trialDivisionResults n :=
  rfl

private theorem allFalse_map_dvd (n : ℕ) (divisors : List ℕ) :
    allFalse (divisors.map fun d => decide (d ∣ n)) =
      divisors.all fun d => decide (¬d ∣ n) := by
  induction divisors with
  | nil => rfl
  | cons d divisors ih =>
      by_cases hd : d ∣ n
      · simp [allFalse, allFalseFrom, hd, allFalseFrom_false]
      · simpa [allFalse, allFalseFrom, hd] using ih

/-- Folding the concrete divisibility-result stream is the Boolean
proper-divisor test used by `trialPrime`. -/
theorem allFalse_trialDivisionResults (n : ℕ) :
    allFalse (trialDivisionResults n) =
      (trialDivisors n).all fun d => decide (¬d ∣ n) := by
  rw [trialDivisionResults, trialDivisionPairs, List.map_map]
  simpa [Function.comp_def] using allFalse_map_dvd n (trialDivisors n)

/-- The executable prime predicate separates the lower-bound check from the
checked Boolean aggregation of all divisibility results. -/
theorem trialPrime_eq_lowerBound_and_allFalse (n : ℕ) :
    trialPrime n =
      (decide (2 ≤ n) && allFalse (trialDivisionResults n)) := by
  rw [trialPrime, allFalse_trialDivisionResults]

/-- Bertrand candidates are at least two, so their trial-prime decision is
exactly the aggregate of their divisibility results. -/
theorem trialPrime_eq_allFalse_trialDivisionResults
    {n : ℕ} (hn : 2 ≤ n) :
    trialPrime n = allFalse (trialDivisionResults n) := by
  rw [trialPrime_eq_lowerBound_and_allFalse]
  simp [hn]

/-- On candidates at least two, the Boolean fold accepts exactly the natural
primes. -/
theorem allFalse_trialDivisionResults_eq_true_iff
    {n : ℕ} (hn : 2 ≤ n) :
    allFalse (trialDivisionResults n) = true ↔ n.Prime := by
  rw [← trialPrime_eq_allFalse_trialDivisionResults hn]
  exact trialPrime_eq_true_iff n

/-! ## Fused repeated divisibility and Boolean aggregation

The standalone repeated-divisibility and Boolean-fold machines expose useful
component contracts. For the prime filter it is cheaper to fuse them: after
each invocation of `unaryDvdComputer`, consume its one-bit output immediately
and retain only the running conjunction in finite control. This avoids an
intermediate result list while preserving the exact padded-pair input syntax.
-/

/-- The Boolean accepted by the fused padded-pair divisibility pass. -/
def allFalseDivisibilityResults (pairs : List (ℕ × ℕ)) : Bool :=
  allFalse (pairDivisionResults pairs)

/-- On the exact trial-pair stream for a candidate at least two, the fused
pass accepts exactly the natural primes. -/
theorem allFalseDivisibilityResults_trialDivisionPairs_eq_true_iff
    {n : ℕ} (hn : 2 ≤ n) :
    allFalseDivisibilityResults (trialDivisionPairs n) = true ↔ n.Prime := by
  simpa [allFalseDivisibilityResults,
    pairDivisionResults_trialDivisionPairs] using
      allFalse_trialDivisionResults_eq_true_iff hn

/-- The fused machine uses the repeated driver's raw input and divisibility
stacks. The divisibility output stack is reused as the final Boolean output
after every intermediate result has been consumed. -/
abbrev PairAllFalseStack := PairDvdStack

/-- Raw-field scanning, one divisibility invocation, and result aggregation. -/
inductive PairAllFalseLabel
  | scan
  | dvd (label : DvdLabel)
  | aggregate
  deriving DecidableEq, Fintype

/-- Finite control combines the outer raw-field observation, the component
state, and the running assertion that no processed divisor succeeded. -/
structure PairAllFalseState where
  observed : Option (Option Bool)
  dvd : DvdState
  aggregate : Bool
  deriving DecidableEq, Fintype

private def pairAllFalseInitialState : PairAllFalseState :=
  ⟨none, dvdInitialState, true⟩

private def pairAllFalseObserve
    (state : PairAllFalseState)
    (observed : Option (Option Bool)) : PairAllFalseState :=
  { state with observed := observed }

private def pairAllFalseResetObserved
    (state : PairAllFalseState) : PairAllFalseState :=
  { state with observed := none }

private def pairAllFalseSetComponent
    (state : PairAllFalseState) (dvd : DvdState) : PairAllFalseState :=
  { state with dvd := dvd }

private def pairAllFalseObserveResult
    (state : PairAllFalseState) : Option Bool → PairAllFalseState
  | some result =>
      { state with
        observed := none
        aggregate := state.aggregate && !result }
  | none => { state with observed := none }

private def pairAllFalseObservedPresent : PairAllFalseState → Bool
  | ⟨some _, _, _⟩ => true
  | _ => false

private def pairAllFalseObservedSymbol : PairAllFalseState → Bool
  | ⟨some (some _), _, _⟩ => true
  | _ => false

private def pairAllFalseObservedBit : PairAllFalseState → Bool
  | ⟨some (some bit), _, _⟩ => bit
  | _ => false

private def pairAllFalseAggregate (state : PairAllFalseState) : Bool :=
  state.aggregate

private def PairAllFalseAlphabet : PairAllFalseStack → Type :=
  PairDvdAlphabet

/-- Lift the checked unary divisibility program, redirecting its halt to the
one-step aggregate phase rather than accumulating a result list. -/
private def liftDvdAllFalseStmt :
    TM2.Stmt DvdAlphabet DvdLabel DvdState →
      TM2.Stmt PairAllFalseAlphabet PairAllFalseLabel PairAllFalseState
  | .push index write next =>
      .push (.inr index) (fun state => write state.dvd)
        (liftDvdAllFalseStmt next)
  | .peek index read next =>
      .peek (.inr index)
        (fun state observed =>
          pairAllFalseSetComponent state (read state.dvd observed))
        (liftDvdAllFalseStmt next)
  | .pop index read next =>
      .pop (.inr index)
        (fun state observed =>
          pairAllFalseSetComponent state (read state.dvd observed))
        (liftDvdAllFalseStmt next)
  | .load update next =>
      .load (fun state =>
        pairAllFalseSetComponent state (update state.dvd))
        (liftDvdAllFalseStmt next)
  | .branch test yes no =>
      .branch (fun state => test state.dvd)
        (liftDvdAllFalseStmt yes) (liftDvdAllFalseStmt no)
  | .goto next => .goto (fun state => .dvd (next state.dvd))
  | .halt => .goto fun _ => .aggregate

/-- Repeatedly restore one padded pair, run divisibility, fold its output bit,
and finally emit the single aggregate Boolean. -/
def pairAllFalseProgram :
    PairAllFalseLabel →
      TM2.Stmt PairAllFalseAlphabet PairAllFalseLabel PairAllFalseState
  | .scan =>
      .pop (.inl ()) pairAllFalseObserve <|
        .branch pairAllFalseObservedPresent
          (.branch pairAllFalseObservedSymbol
            (.push (.inr .input) pairAllFalseObservedBit <|
              .load pairAllFalseResetObserved <|
                .goto fun _ => .scan)
            (.load pairAllFalseResetObserved <|
              .goto fun _ => .dvd .scanDividend))
          (.push (.inr .output) pairAllFalseAggregate <|
            .load (fun _ => pairAllFalseInitialState) .halt)
  | .dvd label => liftDvdAllFalseStmt (unaryDvdProgram label)
  | .aggregate =>
      .pop (.inr .output) pairAllFalseObserveResult <|
        .goto fun _ => .scan

/-- Concrete finite machine fusing repeated padded divisibility with the
Boolean no-divisor fold. -/
def pairAllFalseComputer : FinTM2 where
  K := PairAllFalseStack
  k₀ := .inl ()
  k₁ := .inr .output
  Γ := PairAllFalseAlphabet
  Λ := PairAllFalseLabel
  main := .scan
  σ := PairAllFalseState
  initialState := pairAllFalseInitialState
  Γk₀Fin := inferInstanceAs (Fintype (Option Bool))
  m := pairAllFalseProgram

private def pairAllFalseStackContents
    (input : List (Option Bool))
    (contents : (index : DvdStack) → List (DvdAlphabet index)) :
    (index : PairAllFalseStack) → List (PairAllFalseAlphabet index) :=
  pairDvdStackContents input contents

private def pairAllFalseCfg (label : Option PairAllFalseLabel)
    (state : PairAllFalseState) (input : List (Option Bool))
    (contents : (index : DvdStack) → List (DvdAlphabet index)) :
    pairAllFalseComputer.Cfg where
  l := label
  var := state
  stk := pairAllFalseStackContents input contents

private def pairAllFalseScanCfg
    (input : List (Option Bool)) (aggregate : Bool)
    (field output : List Bool) : pairAllFalseComputer.Cfg :=
  pairAllFalseCfg (some .scan) ⟨none, dvdInitialState, aggregate⟩ input
    (dvdStackContents field [] [] [] output)

/-- Embed a divisibility configuration while fixing the raw stream and the
running aggregate. A component halt enters the aggregate phase. -/
private def pairAllFalseLiftCfg (input : List (Option Bool))
    (aggregate : Bool) (cfg : unaryDvdComputer.Cfg) :
    pairAllFalseComputer.Cfg where
  l := match cfg.l with
    | none => some .aggregate
    | some label => some (.dvd label)
  var := ⟨none, cfg.var, aggregate⟩
  stk := pairAllFalseStackContents input cfg.stk

private theorem pairAllFalseStackContents_update
    (input : List (Option Bool))
    (contents : (index : DvdStack) → List (DvdAlphabet index))
    (index : DvdStack) (value : List (DvdAlphabet index)) :
    Function.update (pairAllFalseStackContents input contents)
        (.inr index) value =
      pairAllFalseStackContents input
        (Function.update contents index value) := by
  exact pairDvdStackContents_update input contents index value

private theorem liftDvdAllFalse_stepAux
    (stmt : TM2.Stmt DvdAlphabet DvdLabel DvdState)
    (state : DvdState)
    (contents : (index : DvdStack) → List (DvdAlphabet index))
    (input : List (Option Bool)) (aggregate : Bool) :
    TM2.stepAux (liftDvdAllFalseStmt stmt) ⟨none, state, aggregate⟩
        (pairAllFalseStackContents input contents) =
      pairAllFalseLiftCfg input aggregate
        (TM2.stepAux stmt state contents) := by
  induction stmt generalizing state contents with
  | push index write next ih =>
      simp only [liftDvdAllFalseStmt, TM2.stepAux]
      rw [pairAllFalseStackContents_update]
      exact ih _ _
  | peek index read next ih =>
      simpa only [liftDvdAllFalseStmt, TM2.stepAux,
        pairAllFalseStackContents, pairDvdStackContents,
        pairAllFalseSetComponent] using
          ih (read state (contents index).head?) contents
  | pop index read next ih =>
      simp only [liftDvdAllFalseStmt, TM2.stepAux,
        pairAllFalseStackContents, pairDvdStackContents,
        pairAllFalseSetComponent]
      rw [pairDvdStackContents_update]
      simpa only [pairAllFalseStackContents] using ih _ _
  | load update next ih =>
      simpa only [liftDvdAllFalseStmt, TM2.stepAux,
        pairAllFalseSetComponent] using ih (update state) contents
  | branch test yes no ihYes ihNo =>
      by_cases h : test state
      · simpa only [liftDvdAllFalseStmt, TM2.stepAux, h, cond_true] using
          ihYes state contents
      · simpa only [liftDvdAllFalseStmt, TM2.stepAux, h, cond_false] using
          ihNo state contents
  | goto next => rfl
  | halt => rfl

private theorem pairAllFalse_lift_step
    (input : List (Option Bool)) (aggregate : Bool)
    (label : DvdLabel) (state : DvdState)
    (contents : (index : DvdStack) → List (DvdAlphabet index)) :
    pairAllFalseComputer.step
        (pairAllFalseLiftCfg input aggregate
          ⟨some label, state, contents⟩) =
      some (pairAllFalseLiftCfg input aggregate
        (TM2.stepAux (unaryDvdProgram label) state contents)) := by
  simp only [pairAllFalseComputer, FinTM2.step, pairAllFalseLiftCfg,
    pairAllFalseProgram, unaryDvdComputer, TM2.step]
  exact congrArg some (liftDvdAllFalse_stepAux _ _ _ _ _)

private theorem pairAllFalse_iterate_lift
    (steps : ℕ) (input : List (Option Bool)) (aggregate : Bool)
    (start finish : unaryDvdComputer.Cfg)
    (hrun :
      (flip Option.bind unaryDvdComputer.step)^[steps] (some start) =
        some finish) :
    (flip Option.bind pairAllFalseComputer.step)^[steps]
        (some (pairAllFalseLiftCfg input aggregate start)) =
      some (pairAllFalseLiftCfg input aggregate finish) := by
  induction steps generalizing start with
  | zero =>
      simpa using congrArg
        (Option.map (pairAllFalseLiftCfg input aggregate)) hrun
  | succ steps ih =>
      rw [Function.iterate_succ_apply] at hrun ⊢
      change (flip Option.bind unaryDvdComputer.step)^[steps]
          (unaryDvdComputer.step start) = some finish at hrun
      change (flip Option.bind pairAllFalseComputer.step)^[steps]
          (pairAllFalseComputer.step
            (pairAllFalseLiftCfg input aggregate start)) =
        some (pairAllFalseLiftCfg input aggregate finish)
      cases hlabel : start.l with
      | none =>
          have hnone : unaryDvdComputer.step start = none := by
            rcases start with ⟨current, state, contents⟩
            change current = none at hlabel
            subst current
            rfl
          rw [hnone] at hrun
          rw [unaryDvd_iterate_none] at hrun
          contradiction
      | some label =>
          let middle :=
            TM2.stepAux (unaryDvdProgram label) start.var start.stk
          have hstep : unaryDvdComputer.step start = some middle := by
            rcases start with ⟨current, state, contents⟩
            simp [unaryDvdComputer, FinTM2.step] at hlabel ⊢
            subst current
            rfl
          rw [hstep] at hrun
          have hcfg :
              start = ⟨some label, start.var, start.stk⟩ := by
            rcases start with ⟨current, state, contents⟩
            change current = some label at hlabel
            subst current
            rfl
          rw [show pairAllFalseComputer.step
              (pairAllFalseLiftCfg input aggregate start) =
                some (pairAllFalseLiftCfg input aggregate middle) by
            rw [hcfg]
            simpa [middle] using pairAllFalse_lift_step input aggregate
              label start.var start.stk]
          exact ih middle hrun

private def pairAllFalse_lift_evals
    (input : List (Option Bool)) (aggregate : Bool)
    {start finish : unaryDvdComputer.Cfg} {bound : ℕ}
    (hrun : EvalsToInTime unaryDvdComputer.step start
      (some finish) bound) :
    EvalsToInTime pairAllFalseComputer.step
      (pairAllFalseLiftCfg input aggregate start)
      (some (pairAllFalseLiftCfg input aggregate finish)) bound where
  steps := hrun.steps
  evals_in_steps := pairAllFalse_iterate_lift hrun.steps input aggregate
    start finish hrun.evals_in_steps
  steps_le_m := hrun.steps_le_m

private def pairAllFalseEvalsToInTimeOne
    {start finish : pairAllFalseComputer.Cfg}
    (hstep : pairAllFalseComputer.step start = some finish) :
    EvalsToInTime pairAllFalseComputer.step start (some finish) 1 where
  steps := 1
  evals_in_steps := by
    simpa [Function.iterate_one] using hstep
  steps_le_m := Nat.le_refl 1

private theorem pairAllFalse_step_scan_some
    (bit : Bool) (input : List (Option Bool))
    (aggregate : Bool) (field output : List Bool) :
    pairAllFalseComputer.step
        (pairAllFalseScanCfg (some bit :: input) aggregate field output) =
      some (pairAllFalseScanCfg input aggregate (bit :: field) output) := by
  simp [pairAllFalseComputer, FinTM2.step, pairAllFalseScanCfg,
    pairAllFalseCfg, pairAllFalseProgram, pairAllFalseStackContents,
    pairDvdStackContents, dvdStackContents, PairAllFalseAlphabet,
    PairDvdAlphabet, pairAllFalseObserve, pairAllFalseObservedPresent,
    pairAllFalseObservedSymbol, pairAllFalseObservedBit,
    pairAllFalseResetObserved, Function.update]
  funext index
  cases index with
  | inl _ => rfl
  | inr index => cases index <;> rfl

private theorem pairAllFalse_step_scan_separator
    (input : List (Option Bool)) (aggregate : Bool)
    (field output : List Bool) :
    pairAllFalseComputer.step
        (pairAllFalseScanCfg (none :: input) aggregate field output) =
      some (pairAllFalseLiftCfg input aggregate
        (dvdCfg (some .scanDividend) dvdInitialState
          field [] [] [] output)) := by
  simp [pairAllFalseComputer, FinTM2.step, pairAllFalseScanCfg,
    pairAllFalseCfg, pairAllFalseLiftCfg, pairAllFalseProgram,
    pairAllFalseStackContents, pairDvdStackContents, dvdCfg,
    dvdStackContents, PairAllFalseAlphabet, PairDvdAlphabet,
    pairAllFalseObserve, pairAllFalseObservedPresent,
    pairAllFalseObservedSymbol, pairAllFalseResetObserved, Function.update]
  funext index
  cases index with
  | inl _ => rfl
  | inr index => cases index <;> rfl

private def pairAllFalse_scan_bits_evals
    (bits : List Bool) (input : List (Option Bool))
    (aggregate : Bool) (field output : List Bool) :
    EvalsToInTime pairAllFalseComputer.step
      (pairAllFalseScanCfg (bits.map some ++ input) aggregate field output)
      (some (pairAllFalseScanCfg input aggregate
        (bits.reverse ++ field) output)) bits.length := by
  induction bits generalizing field with
  | nil => exact EvalsToInTime.refl _ _
  | cons bit bits ih =>
      let middle := pairAllFalseScanCfg (bits.map some ++ input)
        aggregate (bit :: field) output
      have hone : EvalsToInTime pairAllFalseComputer.step
          (pairAllFalseScanCfg ((bit :: bits).map some ++ input)
            aggregate field output)
          (some middle) 1 :=
        pairAllFalseEvalsToInTimeOne (by
          simpa [middle] using pairAllFalse_step_scan_some bit
            (bits.map some ++ input) aggregate field output)
      have hrest := ih (bit :: field)
      have htrans := EvalsToInTime.trans pairAllFalseComputer.step
        1 bits.length
        (pairAllFalseScanCfg ((bit :: bits).map some ++ input)
          aggregate field output)
        middle
        (some (pairAllFalseScanCfg input aggregate
          ((bit :: bits).reverse ++ field) output))
        hone
        (by simpa [middle, List.reverse_cons, List.append_assoc] using hrest)
      simpa [Nat.add_comm] using htrans

private def pairAllFalse_parse_segment_evals
    (bits : List Bool) (input : List (Option Bool))
    (aggregate : Bool) (output : List Bool) :
    EvalsToInTime pairAllFalseComputer.step
      (pairAllFalseScanCfg (RawNatList.segment bits ++ input)
        aggregate [] output)
      (some (pairAllFalseLiftCfg input aggregate
        (dvdCfg (some .scanDividend) dvdInitialState
          bits [] [] [] output)))
      (bits.length + 1) := by
  let middle := pairAllFalseScanCfg (none :: input) aggregate bits output
  have hbits := pairAllFalse_scan_bits_evals bits.reverse (none :: input)
    aggregate [] output
  have hseparator := pairAllFalseEvalsToInTimeOne
    (pairAllFalse_step_scan_separator input aggregate bits output)
  have htrans := EvalsToInTime.trans pairAllFalseComputer.step
    bits.length 1
    (pairAllFalseScanCfg (RawNatList.segment bits ++ input)
      aggregate [] output)
    middle
    (some (pairAllFalseLiftCfg input aggregate
      (dvdCfg (some .scanDividend) dvdInitialState
        bits [] [] [] output)))
    (by simpa [middle, RawNatList.segment] using hbits)
    (by simpa [middle] using hseparator)
  exact evalsToInTimeMono htrans (by omega)

private theorem pairAllFalse_step_aggregate
    (input : List (Option Bool)) (aggregate result : Bool) :
    pairAllFalseComputer.step
        (pairAllFalseLiftCfg input aggregate
          (dvdCfg none dvdInitialState [] [] [] [] [result])) =
      some (pairAllFalseScanCfg input (aggregate && !result) [] []) := by
  simp [pairAllFalseComputer, FinTM2.step, pairAllFalseLiftCfg,
    pairAllFalseScanCfg, pairAllFalseCfg, pairAllFalseProgram,
    pairAllFalseStackContents, pairDvdStackContents, dvdCfg,
    dvdStackContents, PairAllFalseAlphabet, PairDvdAlphabet,
    pairAllFalseObserveResult]
  funext index
  cases index with
  | inl _ => rfl
  | inr index => cases index <;> rfl

private noncomputable def pairAllFalse_pair_evals
    (pair : ℕ × ℕ) (input : List (Option Bool)) (aggregate : Bool) :
    EvalsToInTime pairAllFalseComputer.step
      (pairAllFalseScanCfg
        (RawNatList.segment (UnaryNatPair.encode pair) ++ input)
        aggregate [] [])
      (some (pairAllFalseScanCfg input
        (aggregate && !decide (pair.2 ∣ pair.1)) [] []))
      (7 * (UnaryNatPair.encode pair).length + 18) := by
  let componentStart := pairAllFalseLiftCfg input aggregate
    (dvdCfg (some .scanDividend) dvdInitialState
      (UnaryNatPair.encode pair) [] [] [] [])
  let componentFinish := pairAllFalseLiftCfg input aggregate
    (dvdCfg none dvdInitialState [] [] [] []
      [decide (pair.2 ∣ pair.1)])
  have hparse := pairAllFalse_parse_segment_evals
    (UnaryNatPair.encode pair) input aggregate []
  have hcomponent := pairAllFalse_lift_evals input aggregate
    (unaryDvd_evals_with_output pair [])
  have haggregate := pairAllFalseEvalsToInTimeOne
    (pairAllFalse_step_aggregate input aggregate
      (decide (pair.2 ∣ pair.1)))
  have hfirst := EvalsToInTime.trans pairAllFalseComputer.step
    ((UnaryNatPair.encode pair).length + 1)
    (6 * (UnaryNatPair.encode pair).length + 16)
    (pairAllFalseScanCfg
      (RawNatList.segment (UnaryNatPair.encode pair) ++ input)
      aggregate [] [])
    componentStart (some componentFinish)
    (by simpa [componentStart] using hparse)
    (by simpa [componentStart, componentFinish] using hcomponent)
  have htrans := EvalsToInTime.trans pairAllFalseComputer.step
    (7 * (UnaryNatPair.encode pair).length + 17) 1
    (pairAllFalseScanCfg
      (RawNatList.segment (UnaryNatPair.encode pair) ++ input)
      aggregate [] [])
    componentFinish
    (some (pairAllFalseScanCfg input
      (aggregate && !decide (pair.2 ∣ pair.1)) [] []))
    (evalsToInTimeMono hfirst (by omega))
    (by simpa [componentFinish] using haggregate)
  exact evalsToInTimeMono htrans (by omega)

private theorem allFalseFrom_eq_and_allFalse
    (aggregate : Bool) (results : List Bool) :
    allFalseFrom aggregate results =
      (aggregate && allFalse results) := by
  cases aggregate with
  | false => exact allFalseFrom_false results
  | true => rfl

private theorem allFalse_cons (result : Bool) (results : List Bool) :
    allFalse (result :: results) = (!result && allFalse results) := by
  simpa [allFalse, allFalseFrom] using
    allFalseFrom_eq_and_allFalse (!result) results

private noncomputable def pairAllFalse_pairs_evals
    (pairs : List (ℕ × ℕ)) (input : List (Option Bool))
    (aggregate : Bool) :
    EvalsToInTime pairAllFalseComputer.step
      (pairAllFalseScanCfg (RawUnaryPairList.encode pairs ++ input)
        aggregate [] [])
      (some (pairAllFalseScanCfg input
        (aggregate && allFalse (pairDivisionResults pairs)) [] []))
      (18 * (RawUnaryPairList.encode pairs).length) := by
  induction pairs generalizing input aggregate with
  | nil =>
      simpa [RawUnaryPairList.encode, pairDivisionResults,
        allFalse, allFalseFrom] using
        (EvalsToInTime.refl pairAllFalseComputer.step
          (pairAllFalseScanCfg input aggregate [] []))
  | cons pair pairs ih =>
      let tailAggregate :=
        aggregate && allFalse (pairDivisionResults pairs)
      let middle := pairAllFalseScanCfg
        (RawNatList.segment (UnaryNatPair.encode pair) ++ input)
        tailAggregate [] []
      have hfirst : EvalsToInTime pairAllFalseComputer.step
          (pairAllFalseScanCfg
            (RawUnaryPairList.encode (pair :: pairs) ++ input)
            aggregate [] [])
          (some middle)
          (18 * (RawUnaryPairList.encode pairs).length) := by
        simpa [middle, tailAggregate, RawUnaryPairList.encode_cons,
          List.append_assoc] using
            ih (RawNatList.segment (UnaryNatPair.encode pair) ++ input)
              aggregate
      have hsecond : EvalsToInTime pairAllFalseComputer.step middle
          (some (pairAllFalseScanCfg input
            (aggregate && allFalse
              (pairDivisionResults (pair :: pairs))) [] []))
          (7 * (UnaryNatPair.encode pair).length + 18) := by
        have hpair := pairAllFalse_pair_evals pair input tailAggregate
        simpa [middle, tailAggregate, pairDivisionResults, allFalse_cons,
          Bool.and_assoc, Bool.and_comm, Bool.and_left_comm] using hpair
      have htrans := EvalsToInTime.trans pairAllFalseComputer.step
        (18 * (RawUnaryPairList.encode pairs).length)
        (7 * (UnaryNatPair.encode pair).length + 18)
        (pairAllFalseScanCfg
          (RawUnaryPairList.encode (pair :: pairs) ++ input)
          aggregate [] [])
        middle
        (some (pairAllFalseScanCfg input
          (aggregate && allFalse
            (pairDivisionResults (pair :: pairs))) [] []))
        hfirst hsecond
      apply evalsToInTimeMono htrans
      simp [RawUnaryPairList.encode_cons, RawNatList.segment]
      omega

private theorem pairAllFalse_step_scan_nil (aggregate : Bool) :
    pairAllFalseComputer.step
        (pairAllFalseScanCfg [] aggregate [] []) =
      some (haltList pairAllFalseComputer [aggregate]) := by
  simp [pairAllFalseComputer, FinTM2.step, pairAllFalseScanCfg,
    pairAllFalseCfg, pairAllFalseProgram, pairAllFalseStackContents,
    pairDvdStackContents, dvdStackContents, PairAllFalseAlphabet,
    PairDvdAlphabet, pairAllFalseObserve, pairAllFalseObservedPresent,
    pairAllFalseAggregate, pairAllFalseInitialState, haltList,
    Function.update]
  funext index
  cases index with
  | inl _ => rfl
  | inr index => cases index <;> rfl

private theorem pairAllFalse_initList_eq_cfg
    (input : List (Option Bool)) :
    initList pairAllFalseComputer input =
      pairAllFalseScanCfg input true [] [] := by
  unfold initList pairAllFalseScanCfg pairAllFalseCfg
    pairAllFalseComputer pairAllFalseInitialState
  congr
  funext index
  cases index with
  | inl _ => rfl
  | inr index => cases index <;> rfl

/-- The fused machine decides whether every padded pair is nondividing in at
most `18s + 1` steps for actual raw stream length `s`. -/
noncomputable def pairAllFalse_outputsInTime
    (pairs : List (ℕ × ℕ)) :
    TM2OutputsInTime pairAllFalseComputer (RawUnaryPairList.encode pairs)
      (some (encodeBool (allFalseDivisibilityResults pairs)))
      (18 * (RawUnaryPairList.encode pairs).length + 1) := by
  have hpairs := pairAllFalse_pairs_evals pairs [] true
  have hfinal := pairAllFalseEvalsToInTimeOne
    (pairAllFalse_step_scan_nil (allFalse (pairDivisionResults pairs)))
  have htrans := EvalsToInTime.trans pairAllFalseComputer.step
    (18 * (RawUnaryPairList.encode pairs).length) 1
    (pairAllFalseScanCfg (RawUnaryPairList.encode pairs) true [] [])
    (pairAllFalseScanCfg []
      (allFalse (pairDivisionResults pairs)) [] [])
    (some (haltList pairAllFalseComputer
      [allFalse (pairDivisionResults pairs)]))
    (by simpa using hpairs) hfinal
  rw [TM2OutputsInTime, pairAllFalse_initList_eq_cfg]
  simp only [Option.map_some, encodeBool, List.pure_def]
  simpa [allFalseDivisibilityResults, Nat.add_comm] using htrans

/-- Genuine linear time for the fused repeated-divisibility/no-divisor pass. -/
noncomputable def allFalseDivisibilityResultsComputableInPolyTime :
    @TM2ComputableInPolyTime (List (ℕ × ℕ)) Bool
      RawUnaryPairList.finEncoding finEncodingBoolBool
      allFalseDivisibilityResults where
  tm := pairAllFalseComputer
  inputAlphabet := Equiv.refl (Option Bool)
  outputAlphabet := Equiv.refl Bool
  time := 18 * Polynomial.X + 1
  outputsFun pairs := by
    simpa [RawUnaryPairList.finEncoding, finEncodingBoolBool, Equiv.refl,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_one,
      Polynomial.eval_natCast, Polynomial.eval_X] using
        pairAllFalse_outputsInTime pairs

/-! ## Unary candidate primality composition

The checked generic control and order-preserving transfer machinery from
`lean-np-hardness` composes the trial-pair generator with the fused
no-divisor pass.  The concrete machine below chooses the second component's
reset state as its external halt state.  Its first generator statement
immediately installs the generator's initial state, so this state choice does
not alter the component execution and makes the final configuration satisfy
mathlib's `haltList` convention.
-/

private def trialDivisionPairsAux :
    TM2ComputableAux Bool (Option Bool) where
  tm := trialDivisionPairComputer
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl (Option Bool)

private def pairAllFalseAux :
    TM2ComputableAux (Option Bool) Bool where
  tm := pairAllFalseComputer
  inputAlphabet := Equiv.refl (Option Bool)
  outputAlphabet := Equiv.refl Bool

/-- Concrete sequential machine for generating every padded divisor test and
then accepting exactly when none of them divides the candidate. -/
def unaryCandidatePrimeComputer : FinTM2 :=
  compositionMachine trialDivisionPairsAux pairAllFalseAux

private def unaryCandidatePrimeStartCfg
    (state : ControlState trialDivisionPairsAux pairAllFalseAux)
    (input : List Bool) : unaryCandidatePrimeComputer.Cfg where
  l := some (leftLabel trialDivisionPairsAux pairAllFalseAux .scan)
  var := state
  stk := transferLeftStacks trialDivisionPairsAux pairAllFalseAux
    (trialPairStackContents input [] [] [] [] [])

private theorem unaryCandidatePrime_initList_eq_cfg (input : List Bool) :
    initList unaryCandidatePrimeComputer input =
      unaryCandidatePrimeStartCfg
        (leftState trialDivisionPairsAux pairAllFalseAux
          trialDivisionPairsAux.tm.initialState) input := by
  unfold initList unaryCandidatePrimeComputer compositionMachine
    unaryCandidatePrimeStartCfg trialDivisionPairsAux pairAllFalseAux
    trialDivisionPairComputer pairAllFalseComputer transferLeftStacks
    trialPairStackContents extendStacks leftStacks transferLeftIndex
  congr 2
  funext index
  rcases index with (index | index)
  · rcases index with (index | index)
    · cases index <;> rfl
    · rfl
  · cases index
    rfl

private theorem unaryCandidatePrime_left_init_eq_cfg (input : List Bool) :
    liftScratchCfg trialDivisionPairsAux pairAllFalseAux []
        (liftLeftControlCfg trialDivisionPairsAux pairAllFalseAux
          (initList trialDivisionPairsAux.tm input)) =
      unaryCandidatePrimeStartCfg
        (leftState trialDivisionPairsAux pairAllFalseAux
          trialDivisionPairsAux.tm.initialState) input := by
  simp only [trialDivisionPairsAux]
  rw [trialPair_initList_eq_cfg]
  rfl

private theorem unaryCandidatePrime_init_step (input : List Bool) :
    unaryCandidatePrimeComputer.step
        (initList unaryCandidatePrimeComputer input) =
      unaryCandidatePrimeComputer.step
        (liftScratchCfg trialDivisionPairsAux pairAllFalseAux []
          (liftLeftControlCfg trialDivisionPairsAux pairAllFalseAux
            (initList trialDivisionPairsAux.tm input))) := by
  rw [unaryCandidatePrime_initList_eq_cfg,
    unaryCandidatePrime_left_init_eq_cfg]

private theorem unaryCandidatePrime_haltList_eq (result : Bool) :
    haltList unaryCandidatePrimeComputer [result] =
      rightPhaseCfg trialDivisionPairsAux pairAllFalseAux (fun _ => []) []
        (haltList pairAllFalseAux.tm [result]) := by
  unfold unaryCandidatePrimeComputer compositionMachine haltList rightPhaseCfg
    trialDivisionPairsAux pairAllFalseAux pairAllFalseComputer
  congr 2
  funext index
  rcases index with (index | index)
  · rcases index with (index | index)
    · cases index <;> simp [extendStacks, rightPhaseStacks,
        transferRightIndex]
      all_goals
        intro h
        cases h
    · rcases index with (index | index)
      · cases index
        simp [extendStacks, rightPhaseStacks, transferRightIndex]
        intro h
        cases h
      · cases index <;> simp [extendStacks, rightPhaseStacks,
          transferRightIndex]
        all_goals
          intro h
          cases h
  · cases index
    simp [extendStacks, transferRightIndex]

private theorem unaryCandidatePrime_iterate_init
    (steps : ℕ) (hsteps : 0 < steps) (input : List Bool) :
    (flip Option.bind unaryCandidatePrimeComputer.step)^[steps]
        (some (initList unaryCandidatePrimeComputer input)) =
      (flip Option.bind unaryCandidatePrimeComputer.step)^[steps]
        (some (liftScratchCfg trialDivisionPairsAux pairAllFalseAux []
          (liftLeftControlCfg trialDivisionPairsAux pairAllFalseAux
            (initList trialDivisionPairsAux.tm input)))) := by
  obtain ⟨remaining, rfl⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.ne_of_gt hsteps)
  rw [Function.iterate_succ_apply]
  change
    (flip Option.bind unaryCandidatePrimeComputer.step)^[remaining]
        (unaryCandidatePrimeComputer.step
          (initList unaryCandidatePrimeComputer input)) =
      (flip Option.bind unaryCandidatePrimeComputer.step)^[remaining]
        (unaryCandidatePrimeComputer.step
          (liftScratchCfg trialDivisionPairsAux pairAllFalseAux []
            (liftLeftControlCfg trialDivisionPairsAux pairAllFalseAux
              (initList trialDivisionPairsAux.tm input))))
  rw [unaryCandidatePrime_init_step]

private noncomputable def unaryCandidatePrime_generator_evals (n : ℕ) :
    EvalsToInTime unaryCandidatePrimeComputer.step
      (initList unaryCandidatePrimeComputer (unaryEncodeNat n))
      (some (liftScratchCfg trialDivisionPairsAux pairAllFalseAux []
        (leftTransferEntryCfg trialDivisionPairsAux pairAllFalseAux
          (haltList trialDivisionPairsAux.tm
            (RawUnaryPairList.encode (trialDivisionPairs n))).var
          (haltList trialDivisionPairsAux.tm
            (RawUnaryPairList.encode (trialDivisionPairs n))).stk)))
      (8 * (n + 1) ^ 2) := by
  let output := RawUnaryPairList.encode (trialDivisionPairs n)
  have hgenerator :
      EvalsToInTime trialDivisionPairsAux.tm.step
        (initList trialDivisionPairsAux.tm (unaryEncodeNat n))
        (some (haltList trialDivisionPairsAux.tm output))
        (8 * (n + 1) ^ 2) := by
    simpa [trialDivisionPairsAux, output] using
      trialDivisionPairs_outputsInTime n
  have hpositive : 0 < hgenerator.steps := by
    apply Nat.pos_of_ne_zero
    intro hzero
    have heq := hgenerator.evals_in_steps
    rw [hzero, Function.iterate_zero_apply] at heq
    injection heq with hcfg
    have hlabels := congrArg
      (fun cfg : trialDivisionPairsAux.tm.Cfg => cfg.l) hcfg
    simp [initList, haltList] at hlabels
  have hleftRun := compositionProgram_left_run_to_transfer
    trialDivisionPairsAux pairAllFalseAux hgenerator.steps
    (initList trialDivisionPairsAux.tm (unaryEncodeNat n))
    (haltList trialDivisionPairsAux.tm output)
    trialDivisionPairsAux.tm.main [] rfl hgenerator.evals_in_steps rfl
  refine
    { steps := hgenerator.steps
      evals_in_steps := ?_
      steps_le_m := hgenerator.steps_le_m }
  rw [show unaryCandidatePrimeComputer.step =
      TM2.step (compositionProgram trialDivisionPairsAux pairAllFalseAux) by
    rfl]
  calc
    (flip Option.bind
        (TM2.step (compositionProgram trialDivisionPairsAux pairAllFalseAux)))^[
          hgenerator.steps]
        (some (initList unaryCandidatePrimeComputer (unaryEncodeNat n))) =
      (flip Option.bind unaryCandidatePrimeComputer.step)^[hgenerator.steps]
        (some (liftScratchCfg trialDivisionPairsAux pairAllFalseAux []
          (liftLeftControlCfg trialDivisionPairsAux pairAllFalseAux
            (initList trialDivisionPairsAux.tm (unaryEncodeNat n))))) := by
        exact unaryCandidatePrime_iterate_init hgenerator.steps hpositive _
    _ = some (liftScratchCfg trialDivisionPairsAux pairAllFalseAux []
        (leftTransferEntryCfg trialDivisionPairsAux pairAllFalseAux
          (haltList trialDivisionPairsAux.tm output).var
          (haltList trialDivisionPairsAux.tm output).stk)) :=
      hleftRun

private def unaryCandidatePrimeRightContents
    (input : List (Option Bool)) :
    (index : StackIndex trialDivisionPairsAux.tm pairAllFalseAux.tm) →
      List (StackAlphabet trialDivisionPairsAux.tm pairAllFalseAux.tm index) :=
  rightStacks trialDivisionPairsAux.tm pairAllFalseAux.tm
    (initList pairAllFalseAux.tm input).stk

private theorem unaryCandidatePrime_rightEntryMachineCfg
    (input : List (Option Bool)) :
    rightEntryMachineCfg trialDivisionPairsAux pairAllFalseAux
        (unaryCandidatePrimeRightContents input) =
      initList pairAllFalseAux.tm input := by
  rfl

private theorem unaryCandidatePrime_transferStart_eq
    (output : List (Option Bool)) :
    liftScratchCfg trialDivisionPairsAux pairAllFalseAux []
        (leftTransferEntryCfg trialDivisionPairsAux pairAllFalseAux
          (haltList trialDivisionPairsAux.tm output).var
          (haltList trialDivisionPairsAux.tm output).stk) =
      transferActionCfg trialDivisionPairsAux pairAllFalseAux
        (.phase .reverseOutput)
        (leftState trialDivisionPairsAux pairAllFalseAux
          trialDivisionPairsAux.tm.initialState)
        (Function.update
          (Function.update (fun _ => []) (Sum.inr pairAllFalseAux.tm.k₀) [])
          (Sum.inl trialDivisionPairsAux.tm.k₁) output) [] := by
  simp only [trialDivisionPairsAux]
  rw [trialPair_haltList_eq_cfg]
  unfold liftScratchCfg leftTransferEntryCfg transferActionCfg trialPairCfg
    trialPairStackContents pairAllFalseAux pairAllFalseComputer leftStacks
    extendStacks
  congr 2
  funext index
  rcases index with (index | index)
  · rcases index with (index | index)
    · cases index <;> rfl
    · rcases index with (index | index)
      · cases index
        rfl
      · cases index <;> rfl
  · cases index
    rfl

private theorem unaryCandidatePrime_transferFinish_eq
    (output : List (Option Bool)) :
    rightEntryCfg trialDivisionPairsAux pairAllFalseAux
        (unaryCandidatePrimeRightContents output) [] =
      rightEntryCfg trialDivisionPairsAux pairAllFalseAux
        (Function.update
          (Function.update (fun _ => []) (Sum.inl trialDivisionPairsAux.tm.k₁) [])
          (Sum.inr pairAllFalseAux.tm.k₀)
          (output.map (middleAlphabetEquiv trialDivisionPairsAux
            pairAllFalseAux) ++ [])) [] := by
  congr 2
  unfold unaryCandidatePrimeRightContents
  simp only [pairAllFalseAux]
  rw [pairAllFalse_initList_eq_cfg]
  unfold pairAllFalseScanCfg pairAllFalseCfg pairAllFalseStackContents
    pairDvdStackContents dvdStackContents rightStacks middleAlphabetEquiv
    trialDivisionPairsAux pairAllFalseComputer trialDivisionPairComputer
  funext index
  rcases index with (index | index)
  · cases index <;> rfl
  · rcases index with (index | index)
    · cases index
      simp [Function.update]
      change output = output.map id
      simp
    · cases index <;> rfl

private def unaryCandidatePrime_transfer_evals (n : ℕ) :
    EvalsToInTime unaryCandidatePrimeComputer.step
      (liftScratchCfg trialDivisionPairsAux pairAllFalseAux []
        (leftTransferEntryCfg trialDivisionPairsAux pairAllFalseAux
          (haltList trialDivisionPairsAux.tm
            (RawUnaryPairList.encode (trialDivisionPairs n))).var
          (haltList trialDivisionPairsAux.tm
            (RawUnaryPairList.encode (trialDivisionPairs n))).stk))
      (some (rightEntryCfg trialDivisionPairsAux pairAllFalseAux
        (unaryCandidatePrimeRightContents
          (RawUnaryPairList.encode (trialDivisionPairs n))) []))
      (4 * (RawUnaryPairList.encode (trialDivisionPairs n)).length + 4) := by
  let output := RawUnaryPairList.encode (trialDivisionPairs n)
  refine
    { steps := 4 * output.length + 4
      evals_in_steps := ?_
      steps_le_m := Nat.le_refl _ }
  rw [unaryCandidatePrime_transferStart_eq output,
    unaryCandidatePrime_transferFinish_eq output]
  exact compositionProgram_transfer_whole_list trialDivisionPairsAux
      pairAllFalseAux
      (leftState trialDivisionPairsAux pairAllFalseAux
        trialDivisionPairsAux.tm.initialState)
      (fun _ => []) output []

/-- Candidate-only primality bit.  This omits the lower-bound guard because
every generated Bertrand candidate is at least two. -/
def unaryCandidatePrime (n : ℕ) : Bool :=
  allFalseDivisibilityResults (trialDivisionPairs n)

theorem unaryCandidatePrime_eq_true_iff
    {n : ℕ} (hn : 2 ≤ n) :
    unaryCandidatePrime n = true ↔ n.Prime := by
  exact allFalseDivisibilityResults_trialDivisionPairs_eq_true_iff hn

/-- Every value emitted by the Bertrand enumerator is a valid input for the
candidate-only primality machine.  This includes the edge cases: the interval
is empty at `q = 0`, while its sole value at `q = 1` is `2`. -/
theorem two_le_of_mem_bertrandCandidates
    {q n : ℕ} (hn : n ∈ bertrandCandidates q) :
    2 ≤ n := by
  have hbounds := (mem_bertrandCandidates_iff q n).mp hn
  omega

/-- On the generated candidate stream, the composed machine predicate agrees
exactly with the guarded trial-division specification.  Thus the lower-bound
guard is supplied by the enumerator invariant rather than by another machine
pass. -/
theorem unaryCandidatePrime_eq_trialPrime_of_mem_bertrandCandidates
    {q n : ℕ} (hn : n ∈ bertrandCandidates q) :
    unaryCandidatePrime n = trialPrime n := by
  rw [Bool.eq_iff_iff,
    unaryCandidatePrime_eq_true_iff
      (two_le_of_mem_bertrandCandidates hn),
    trialPrime_eq_true_iff]

/-- Filtering the checked Bertrand enumeration with the composed machine's
candidate predicate yields exactly the semantic prime-candidate list. -/
theorem filter_unaryCandidatePrime_bertrandCandidates (q : ℕ) :
    (bertrandCandidates q).filter unaryCandidatePrime =
      bertrandPrimeCandidates q := by
  rw [bertrandPrimeCandidates]
  exact List.filter_congr fun _ hn =>
    unaryCandidatePrime_eq_trialPrime_of_mem_bertrandCandidates hn

private theorem unaryCandidatePrime_rightEntry_eq
    (input : List (Option Bool)) :
    rightEntryCfg trialDivisionPairsAux pairAllFalseAux
        (unaryCandidatePrimeRightContents input) [] =
      rightPhaseCfg trialDivisionPairsAux pairAllFalseAux (fun _ => []) []
        (initList pairAllFalseAux.tm input) := by
  rw [rightEntryCfg_eq_rightPhaseCfg,
    unaryCandidatePrime_rightEntryMachineCfg]
  congr 1

private noncomputable def unaryCandidatePrime_second_evals (n : ℕ) :
    EvalsToInTime unaryCandidatePrimeComputer.step
      (rightEntryCfg trialDivisionPairsAux pairAllFalseAux
        (unaryCandidatePrimeRightContents
          (RawUnaryPairList.encode (trialDivisionPairs n))) [])
      (some (haltList unaryCandidatePrimeComputer
        (encodeBool (unaryCandidatePrime n))))
      (18 * (RawUnaryPairList.encode (trialDivisionPairs n)).length + 1) := by
  let input := RawUnaryPairList.encode (trialDivisionPairs n)
  let result := unaryCandidatePrime n
  have hsecond : EvalsToInTime pairAllFalseAux.tm.step
      (initList pairAllFalseAux.tm input)
      (some (haltList pairAllFalseAux.tm (encodeBool result)))
      (18 * input.length + 1) := by
    simpa [pairAllFalseAux, input, result, unaryCandidatePrime] using
      pairAllFalse_outputsInTime (trialDivisionPairs n)
  have hrightRun := compositionProgram_right_run trialDivisionPairsAux
    pairAllFalseAux hsecond.steps
    (initList pairAllFalseAux.tm input)
    (haltList pairAllFalseAux.tm (encodeBool result))
    (fun _ => []) [] hsecond.evals_in_steps
  refine
    { steps := hsecond.steps
      evals_in_steps := ?_
      steps_le_m := hsecond.steps_le_m }
  rw [unaryCandidatePrime_rightEntry_eq]
  change (flip Option.bind unaryCandidatePrimeComputer.step)^[hsecond.steps]
      (some (rightPhaseCfg trialDivisionPairsAux pairAllFalseAux
        (fun _ => []) [] (initList pairAllFalseAux.tm input))) =
    some (haltList unaryCandidatePrimeComputer [result])
  rw [unaryCandidatePrime_haltList_eq]
  exact hrightRun

/-- The composed machine generates the complete padded trial stream, transfers
it in source order, and runs the fused no-divisor pass in quadratic time in
the unary candidate length. -/
noncomputable def unaryCandidatePrime_outputsInTime (n : ℕ) :
    TM2OutputsInTime unaryCandidatePrimeComputer (unaryEncodeNat n)
      (some (encodeBool (unaryCandidatePrime n)))
      (64 * (n + 1) ^ 2) := by
  let stream := RawUnaryPairList.encode (trialDivisionPairs n)
  have hgenerator := unaryCandidatePrime_generator_evals n
  have htransfer := unaryCandidatePrime_transfer_evals n
  have hsecond := unaryCandidatePrime_second_evals n
  have hfirst := EvalsToInTime.trans unaryCandidatePrimeComputer.step
    (8 * (n + 1) ^ 2) (4 * stream.length + 4)
    (initList unaryCandidatePrimeComputer (unaryEncodeNat n))
    (liftScratchCfg trialDivisionPairsAux pairAllFalseAux []
      (leftTransferEntryCfg trialDivisionPairsAux pairAllFalseAux
        (haltList trialDivisionPairsAux.tm stream).var
        (haltList trialDivisionPairsAux.tm stream).stk))
    (some (rightEntryCfg trialDivisionPairsAux pairAllFalseAux
      (unaryCandidatePrimeRightContents stream) []))
    (by simpa [stream] using hgenerator)
    (by simpa [stream] using htransfer)
  have hall := EvalsToInTime.trans unaryCandidatePrimeComputer.step
    (4 * stream.length + 4 + 8 * (n + 1) ^ 2)
    (18 * stream.length + 1)
    (initList unaryCandidatePrimeComputer (unaryEncodeNat n))
    (rightEntryCfg trialDivisionPairsAux pairAllFalseAux
      (unaryCandidatePrimeRightContents stream) [])
    (some (haltList unaryCandidatePrimeComputer
      (encodeBool (unaryCandidatePrime n))))
    (by simpa [Nat.add_comm] using hfirst)
    (by simpa [stream] using hsecond)
  have hstream := trialDivisionPairStream_length_le n
  have hbound :
      (18 * stream.length + 1) +
          (4 * stream.length + 4 + 8 * (n + 1) ^ 2) ≤
        64 * (n + 1) ^ 2 := by
    cases n with
    | zero =>
        norm_num [stream, trialDivisionPairs, trialDivisors,
          RawUnaryPairList.encode]
    | succ n =>
        cases n with
        | zero =>
            norm_num [stream, trialDivisionPairs, trialDivisors,
              RawUnaryPairList.encode]
        | succ k =>
            simp only [stream] at hstream ⊢
            have hsub : k + 1 + 1 - 2 = k := by omega
            rw [hsub] at hstream
            nlinarith
  exact evalsToInTimeMono hall hbound

/-- Genuine polynomial-time finite-machine computation of the candidate-only
primality bit on unary input.  The enumerator supplies the lower-bound
invariant, so `filter_unaryCandidatePrime_bertrandCandidates` connects this
predicate directly to the guarded semantic filter. -/
noncomputable def unaryCandidatePrimeComputableInPolyTime :
    @TM2ComputableInPolyTime ℕ Bool unaryFinEncodingNat
      finEncodingBoolBool unaryCandidatePrime where
  tm := unaryCandidatePrimeComputer
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := 64 * (Polynomial.X + 1) ^ 2
  outputsFun n := by
    simpa [unaryFinEncodingNat, finEncodingBoolBool, Equiv.refl,
      Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add,
      Polynomial.eval_natCast, Polynomial.eval_one, Polynomial.eval_X] using
        unaryCandidatePrime_outputsInTime n

/-! ## First-prime selection from the unary candidate stream

The outer driver below scans the stack-oriented candidate fields from largest
to smallest.  Whenever the checked candidate-primality component accepts, the
driver overwrites its saved value.  The last accepted value is therefore the
first accepted value in the source-order list.  The trailing length field is
recognized by one-symbol lookahead and discarded without a primality test.
-/

/-- The first candidate accepted by the checked candidate-primality predicate. -/
def firstUnaryCandidatePrime? : List ℕ → Option ℕ
  | [] => none
  | candidate :: candidates =>
      if unaryCandidatePrime candidate then some candidate
      else firstUnaryCandidatePrime? candidates

/-- The selected candidate, using the compiler's explicit empty-list
convention `2`. -/
def selectUnaryCandidatePrime (candidates : List ℕ) : ℕ :=
  (firstUnaryCandidatePrime? candidates).getD 2

@[simp]
theorem firstUnaryCandidatePrime?_eq_head?_filter (candidates : List ℕ) :
    firstUnaryCandidatePrime? candidates =
      (candidates.filter unaryCandidatePrime).head? := by
  induction candidates with
  | nil => rfl
  | cons candidate candidates ih =>
      by_cases hprime : unaryCandidatePrime candidate
      · simp [firstUnaryCandidatePrime?, hprime]
      · simp [firstUnaryCandidatePrime?, hprime, ih]

theorem firstUnaryCandidatePrime?_mem {candidates : List ℕ} {candidate : ℕ}
    (hselected : firstUnaryCandidatePrime? candidates = some candidate) :
    candidate ∈ candidates := by
  induction candidates with
  | nil => simp [firstUnaryCandidatePrime?] at hselected
  | cons head tail ih =>
      by_cases hprime : unaryCandidatePrime head
      · simp [firstUnaryCandidatePrime?, hprime] at hselected
        simpa [hselected]
      · simp only [firstUnaryCandidatePrime?, hprime, ↓reduceIte] at hselected
        exact List.mem_cons_of_mem head (ih hselected)

theorem head?_getD_eq_head {candidates : List ℕ}
    (hne : candidates ≠ []) (fallback : ℕ) :
    candidates.head?.getD fallback = candidates.head hne := by
  cases candidates with
  | nil => contradiction
  | cons candidate candidates => rfl

/-- The native unary scan selects the semantic first Bertrand prime. -/
theorem selectUnaryCandidatePrime_bertrandCandidates (q : ℕ) :
    selectUnaryCandidatePrime (bertrandCandidates q) = firstBertrandPrime q := by
  rw [selectUnaryCandidatePrime, firstUnaryCandidatePrime?_eq_head?_filter,
    filter_unaryCandidatePrime_bertrandCandidates]
  by_cases hq : q = 0
  · subst q
    simp [firstBertrandPrime, bertrandPrimeCandidates,
      bertrandCandidates, intervalFrom]
  · rw [firstBertrandPrime, dif_neg hq]
    exact head?_getD_eq_head (bertrandPrimeCandidates_ne_nil hq) 2

private instance primeSelectorComponentKDecidableEq :
    DecidableEq unaryCandidatePrimeComputer.K :=
  unaryCandidatePrimeComputer.kDecidableEq

private instance primeSelectorComponentKFintype :
    Fintype unaryCandidatePrimeComputer.K :=
  unaryCandidatePrimeComputer.kFin

private instance primeSelectorComponentLabelFintype :
    Fintype unaryCandidatePrimeComputer.Λ :=
  unaryCandidatePrimeComputer.ΛFin

private instance primeSelectorComponentStateFintype :
    Fintype unaryCandidatePrimeComputer.σ :=
  unaryCandidatePrimeComputer.σFin

/-- Driver-owned stacks plus all stacks of the checked candidate-primality
component. -/
inductive PrimeSelectorOuterStack
  | input
  | candidate
  | output
  deriving DecidableEq, Fintype

abbrev PrimeSelectorStack :=
  PrimeSelectorOuterStack ⊕ unaryCandidatePrimeComputer.K

/-- Outer parsing, component execution, result handling, and final cleanup. -/
inductive PrimeSelectorLabel
  | scan
  | lookahead
  | prime (label : unaryCandidatePrimeComputer.Λ)
  | result
  | clearCandidate
  | clearSelected
  | moveCandidate
  | discardCount
  | finalize
  deriving Fintype

/-- Finite control remembers the most recent outer pop, the component state,
and whether an accepted candidate has been saved. -/
structure PrimeSelectorState where
  observed : Option Bool
  prime : unaryCandidatePrimeComputer.σ
  found : Bool
  deriving Fintype

private def primeSelectorInitialState : PrimeSelectorState :=
  ⟨none, unaryCandidatePrimeComputer.initialState, false⟩

private def primeSelectorObserve
    (state : PrimeSelectorState) (observed : Option Bool) :
    PrimeSelectorState :=
  { state with observed := observed }

private def primeSelectorResetObserved
    (state : PrimeSelectorState) : PrimeSelectorState :=
  { state with observed := none }

private def primeSelectorSetComponent
    (state : PrimeSelectorState) (prime : unaryCandidatePrimeComputer.σ) :
    PrimeSelectorState :=
  { state with prime := prime }

private def primeSelectorSetFound
    (state : PrimeSelectorState) : PrimeSelectorState :=
  { state with observed := none, found := true }

private def primeSelectorObservedPresent : PrimeSelectorState → Bool
  | ⟨some _, _, _⟩ => true
  | _ => false

private def primeSelectorObservedBit : PrimeSelectorState → Bool
  | ⟨some bit, _, _⟩ => bit
  | _ => false

private def PrimeSelectorAlphabet : PrimeSelectorStack → Type
  | .inl _ => Bool
  | .inr index => unaryCandidatePrimeComputer.Γ index

/-- Lift one statement of the checked candidate-primality component.  Its halt
is redirected to the outer result handler. -/
private def liftCandidatePrimeStmt :
    TM2.Stmt unaryCandidatePrimeComputer.Γ
      unaryCandidatePrimeComputer.Λ unaryCandidatePrimeComputer.σ →
      TM2.Stmt PrimeSelectorAlphabet PrimeSelectorLabel PrimeSelectorState
  | .push index write next =>
      .push (.inr index) (fun state => write state.prime)
        (liftCandidatePrimeStmt next)
  | .peek index read next =>
      .peek (.inr index)
        (fun state observed =>
          primeSelectorSetComponent state (read state.prime observed))
        (liftCandidatePrimeStmt next)
  | .pop index read next =>
      .pop (.inr index)
        (fun state observed =>
          primeSelectorSetComponent state (read state.prime observed))
        (liftCandidatePrimeStmt next)
  | .load update next =>
      .load (fun state => primeSelectorSetComponent state (update state.prime))
        (liftCandidatePrimeStmt next)
  | .branch test yes no =>
      .branch (fun state => test state.prime)
        (liftCandidatePrimeStmt yes) (liftCandidatePrimeStmt no)
  | .goto next => .goto (fun state => .prime (next state.prime))
  | .halt => .goto (fun _ => .result)

/-- Scan unary fields, invoke candidate primality once per value field, keep
the first source-order survivor, discard the trailing count, and emit a unary
natural. -/
def primeSelectorProgram :
    PrimeSelectorLabel →
      TM2.Stmt PrimeSelectorAlphabet PrimeSelectorLabel PrimeSelectorState
  | .scan =>
      .pop (.inl .input) primeSelectorObserve <|
        .branch primeSelectorObservedPresent
          (.branch primeSelectorObservedBit
            (.push (.inl .candidate) (fun _ => true) <|
              .push (.inr unaryCandidatePrimeComputer.k₀) (fun _ => true) <|
                .load primeSelectorResetObserved <|
                  .goto fun _ => .scan)
            (.load primeSelectorResetObserved <|
              .goto fun _ => .lookahead))
          (.load primeSelectorResetObserved <|
            .goto fun _ => .discardCount)
  | .lookahead =>
      .pop (.inl .input) primeSelectorObserve <|
        .branch primeSelectorObservedPresent
          (.push (.inl .input) primeSelectorObservedBit <|
            .load primeSelectorResetObserved <|
              .goto fun _ => .prime unaryCandidatePrimeComputer.main)
          (.load primeSelectorResetObserved <|
            .goto fun _ => .discardCount)
  | .prime label =>
      liftCandidatePrimeStmt (unaryCandidatePrimeComputer.m label)
  | .result =>
      .pop (.inr unaryCandidatePrimeComputer.k₁) primeSelectorObserve <|
        .branch primeSelectorObservedBit
          (.load primeSelectorSetFound <| .goto fun _ => .clearSelected)
          (.load primeSelectorResetObserved <|
            .goto fun _ => .clearCandidate)
  | .clearCandidate =>
      .pop (.inl .candidate) primeSelectorObserve <|
        .branch primeSelectorObservedPresent
          (.load primeSelectorResetObserved <|
            .goto fun _ => .clearCandidate)
          (.load primeSelectorResetObserved <| .goto fun _ => .scan)
  | .clearSelected =>
      .pop (.inl .output) primeSelectorObserve <|
        .branch primeSelectorObservedPresent
          (.load primeSelectorResetObserved <|
            .goto fun _ => .clearSelected)
          (.load primeSelectorResetObserved <|
            .goto fun _ => .moveCandidate)
  | .moveCandidate =>
      .pop (.inl .candidate) primeSelectorObserve <|
        .branch primeSelectorObservedPresent
          (.push (.inl .output) primeSelectorObservedBit <|
            .load primeSelectorResetObserved <|
              .goto fun _ => .moveCandidate)
          (.load primeSelectorResetObserved <| .goto fun _ => .scan)
  | .discardCount =>
      .pop (.inl .candidate) primeSelectorObserve <|
        .branch primeSelectorObservedPresent
          (.pop (.inr unaryCandidatePrimeComputer.k₀)
            (fun state _ => primeSelectorResetObserved state) <|
              .goto fun _ => .discardCount)
          (.load primeSelectorResetObserved <| .goto fun _ => .finalize)
  | .finalize =>
      .branch (fun state => state.found)
        (.load (fun _ => primeSelectorInitialState) .halt)
        (.push (.inl .output) (fun _ => true) <|
          .push (.inl .output) (fun _ => true) <|
            .load (fun _ => primeSelectorInitialState) .halt)

/-- Concrete finite machine selecting the first accepted candidate from a
checked `RawUnaryNatList` stream. -/
def primeSelectorComputer : FinTM2 where
  K := PrimeSelectorStack
  k₀ := .inl .input
  k₁ := .inl .output
  Γ := PrimeSelectorAlphabet
  Λ := PrimeSelectorLabel
  main := .scan
  σ := PrimeSelectorState
  initialState := primeSelectorInitialState
  Γk₀Fin := Bool.fintype
  m := primeSelectorProgram

private def primeSelectorStackContents
    (input candidate output : List Bool)
    (contents : (index : unaryCandidatePrimeComputer.K) →
      List (unaryCandidatePrimeComputer.Γ index)) :
    (index : PrimeSelectorStack) → List (PrimeSelectorAlphabet index)
  | .inl .input => input
  | .inl .candidate => candidate
  | .inl .output => output
  | .inr index => contents index

private def primeSelectorCfg (label : Option PrimeSelectorLabel)
    (state : PrimeSelectorState) (input candidate output : List Bool)
    (contents : (index : unaryCandidatePrimeComputer.K) →
      List (unaryCandidatePrimeComputer.Γ index)) :
    primeSelectorComputer.Cfg where
  l := label
  var := state
  stk := primeSelectorStackContents input candidate output contents

private def primeSelectorIdleCfg (label : PrimeSelectorLabel)
    (input candidate output : List Bool) (found : Bool) :
    primeSelectorComputer.Cfg :=
  primeSelectorCfg (some label)
    ⟨none, unaryCandidatePrimeComputer.initialState, found⟩
    input candidate output (fun _ => [])

private def primeSelectorScanCfg
    (input candidate output : List Bool) (found : Bool) :
    primeSelectorComputer.Cfg :=
  primeSelectorCfg (some .scan)
    ⟨none, unaryCandidatePrimeComputer.initialState, found⟩
    input candidate output (initList unaryCandidatePrimeComputer candidate).stk

private def primeSelectorLookaheadCfg
    (input candidate output : List Bool) (found : Bool) :
    primeSelectorComputer.Cfg :=
  primeSelectorCfg (some .lookahead)
    ⟨none, unaryCandidatePrimeComputer.initialState, found⟩
    input candidate output (initList unaryCandidatePrimeComputer candidate).stk

private def primeSelectorDiscardCfg
    (candidate output : List Bool) (found : Bool) :
    primeSelectorComputer.Cfg :=
  primeSelectorCfg (some .discardCount)
    ⟨none, unaryCandidatePrimeComputer.initialState, found⟩
    [] candidate output (initList unaryCandidatePrimeComputer candidate).stk

private def primeSelectorLiftCfg (input candidate output : List Bool)
    (found : Bool) (cfg : unaryCandidatePrimeComputer.Cfg) :
    primeSelectorComputer.Cfg :=
  primeSelectorCfg
    (match cfg.l with
      | none => some .result
      | some label => some (.prime label))
    ⟨none, cfg.var, found⟩ input candidate output cfg.stk

@[simp]
private theorem primeSelectorStackContents_update
    (input candidate output : List Bool)
    (contents : (index : unaryCandidatePrimeComputer.K) →
      List (unaryCandidatePrimeComputer.Γ index))
    (index : unaryCandidatePrimeComputer.K)
    (value : List (unaryCandidatePrimeComputer.Γ index)) :
    Function.update
        (primeSelectorStackContents input candidate output contents)
        (.inr index) value =
      primeSelectorStackContents input candidate output
        (Function.update contents index value) := by
  funext target
  cases target with
  | inl outer =>
      cases outer <;> simp [primeSelectorStackContents, Function.update]
  | inr other =>
      by_cases h : other = index
      · subst other
        simp [primeSelectorStackContents, Function.update]
      · simp [primeSelectorStackContents, Function.update, h]

@[simp]
private theorem primeSelectorStackContents_update_input
    (input candidate output value : List Bool)
    (contents : (index : unaryCandidatePrimeComputer.K) →
      List (unaryCandidatePrimeComputer.Γ index)) :
    Function.update
        (primeSelectorStackContents input candidate output contents)
        (.inl .input) value =
      primeSelectorStackContents value candidate output contents := by
  funext target
  rcases target with outer | index
  · cases outer <;> simp [primeSelectorStackContents, Function.update]
  · simp [primeSelectorStackContents, Function.update]

@[simp]
private theorem primeSelectorStackContents_update_candidate
    (input candidate output value : List Bool)
    (contents : (index : unaryCandidatePrimeComputer.K) →
      List (unaryCandidatePrimeComputer.Γ index)) :
    Function.update
        (primeSelectorStackContents input candidate output contents)
        (.inl .candidate) value =
      primeSelectorStackContents input value output contents := by
  funext target
  rcases target with outer | index
  · cases outer <;> simp [primeSelectorStackContents, Function.update]
  · simp [primeSelectorStackContents, Function.update]

@[simp]
private theorem primeSelectorStackContents_update_output
    (input candidate output value : List Bool)
    (contents : (index : unaryCandidatePrimeComputer.K) →
      List (unaryCandidatePrimeComputer.Γ index)) :
    Function.update
        (primeSelectorStackContents input candidate output contents)
        (.inl .output) value =
      primeSelectorStackContents input candidate value contents := by
  funext target
  rcases target with outer | index
  · cases outer <;> simp [primeSelectorStackContents, Function.update]
  · simp [primeSelectorStackContents, Function.update]

private theorem liftCandidatePrime_stepAux
    (stmt : TM2.Stmt unaryCandidatePrimeComputer.Γ
      unaryCandidatePrimeComputer.Λ unaryCandidatePrimeComputer.σ)
    (state : unaryCandidatePrimeComputer.σ)
    (contents : (index : unaryCandidatePrimeComputer.K) →
      List (unaryCandidatePrimeComputer.Γ index))
    (input candidate output : List Bool) (found : Bool) :
    TM2.stepAux (liftCandidatePrimeStmt stmt) ⟨none, state, found⟩
        (primeSelectorStackContents input candidate output contents) =
      primeSelectorLiftCfg input candidate output found
        (TM2.stepAux stmt state contents) := by
  induction stmt generalizing state contents with
  | push index write next ih =>
      simp only [liftCandidatePrimeStmt, TM2.stepAux]
      rw [primeSelectorStackContents_update]
      exact ih _ _
  | peek index read next ih =>
      simpa only [liftCandidatePrimeStmt, TM2.stepAux,
        primeSelectorStackContents, primeSelectorSetComponent] using
          ih (read state (contents index).head?) contents
  | pop index read next ih =>
      simp only [liftCandidatePrimeStmt, TM2.stepAux,
        primeSelectorStackContents, primeSelectorSetComponent]
      rw [primeSelectorStackContents_update]
      exact ih _ _
  | load update next ih =>
      simpa only [liftCandidatePrimeStmt, TM2.stepAux,
        primeSelectorSetComponent] using ih (update state) contents
  | branch test yes no ihYes ihNo =>
      by_cases h : test state
      · simpa only [liftCandidatePrimeStmt, TM2.stepAux, h, cond_true] using
          ihYes state contents
      · simpa only [liftCandidatePrimeStmt, TM2.stepAux, h, cond_false] using
          ihNo state contents
  | goto next => rfl
  | halt => rfl

private theorem primeSelector_lift_step
    (input candidate output : List Bool) (found : Bool)
    (label : unaryCandidatePrimeComputer.Λ)
    (state : unaryCandidatePrimeComputer.σ)
    (contents : (index : unaryCandidatePrimeComputer.K) →
      List (unaryCandidatePrimeComputer.Γ index)) :
    primeSelectorComputer.step
        (primeSelectorLiftCfg input candidate output found
          ⟨some label, state, contents⟩) =
      some (primeSelectorLiftCfg input candidate output found
        (TM2.stepAux (unaryCandidatePrimeComputer.m label) state contents)) := by
  simp only [primeSelectorComputer, FinTM2.step, primeSelectorLiftCfg,
    primeSelectorProgram, TM2.step]
  exact congrArg some
    (liftCandidatePrime_stepAux _ _ _ _ _ _ _)

private theorem candidatePrime_iterate_none (steps : ℕ) :
    (flip Option.bind unaryCandidatePrimeComputer.step)^[steps]
        (none : Option unaryCandidatePrimeComputer.Cfg) = none := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
      rw [Function.iterate_succ_apply']
      rw [ih]
      rfl

private theorem primeSelector_iterate_lift
    (steps : ℕ) (input candidate output : List Bool) (found : Bool)
    (start finish : unaryCandidatePrimeComputer.Cfg)
    (hrun :
      (flip Option.bind unaryCandidatePrimeComputer.step)^[steps]
          (some start) = some finish) :
    (flip Option.bind primeSelectorComputer.step)^[steps]
        (some (primeSelectorLiftCfg input candidate output found start)) =
      some (primeSelectorLiftCfg input candidate output found finish) := by
  induction steps generalizing start with
  | zero =>
      simpa using congrArg
        (Option.map (primeSelectorLiftCfg input candidate output found)) hrun
  | succ steps ih =>
      rw [Function.iterate_succ_apply] at hrun ⊢
      change (flip Option.bind unaryCandidatePrimeComputer.step)^[steps]
          (unaryCandidatePrimeComputer.step start) = some finish at hrun
      change (flip Option.bind primeSelectorComputer.step)^[steps]
          (primeSelectorComputer.step
            (primeSelectorLiftCfg input candidate output found start)) =
        some (primeSelectorLiftCfg input candidate output found finish)
      cases hlabel : start.l with
      | none =>
          have hnone : unaryCandidatePrimeComputer.step start = none := by
            rcases start with ⟨current, state, contents⟩
            change current = none at hlabel
            subst current
            rfl
          rw [hnone] at hrun
          rw [candidatePrime_iterate_none] at hrun
          contradiction
      | some label =>
          let middle := TM2.stepAux
            (unaryCandidatePrimeComputer.m label) start.var start.stk
          have hstep : unaryCandidatePrimeComputer.step start = some middle := by
            rcases start with ⟨current, state, contents⟩
            simp [unaryCandidatePrimeComputer, FinTM2.step] at hlabel ⊢
            subst current
            rfl
          rw [hstep] at hrun
          have hcfg : start = ⟨some label, start.var, start.stk⟩ := by
            rcases start with ⟨current, state, contents⟩
            change current = some label at hlabel
            subst current
            rfl
          rw [show primeSelectorComputer.step
              (primeSelectorLiftCfg input candidate output found start) =
                some (primeSelectorLiftCfg input candidate output found middle) by
            rw [hcfg]
            simpa [middle] using primeSelector_lift_step input candidate output
              found label start.var start.stk]
          exact ih middle hrun

private def primeSelector_lift_evals
    (input candidate output : List Bool) (found : Bool)
    {start finish : unaryCandidatePrimeComputer.Cfg} {bound : ℕ}
    (hrun : EvalsToInTime unaryCandidatePrimeComputer.step start
      (some finish) bound) :
    EvalsToInTime primeSelectorComputer.step
      (primeSelectorLiftCfg input candidate output found start)
      (some (primeSelectorLiftCfg input candidate output found finish))
      bound where
  steps := hrun.steps
  evals_in_steps := primeSelector_iterate_lift hrun.steps input candidate
    output found start finish hrun.evals_in_steps
  steps_le_m := hrun.steps_le_m

private def primeSelectorEvalsToInTimeOne
    {start finish : primeSelectorComputer.Cfg}
    (hstep : primeSelectorComputer.step start = some finish) :
    EvalsToInTime primeSelectorComputer.step start (some finish) 1 where
  steps := 1
  evals_in_steps := by simpa [Function.iterate_one] using hstep
  steps_le_m := Nat.le_refl 1

private theorem primeSelector_step_scan_true
    (input candidate output : List Bool) (found : Bool) :
    primeSelectorComputer.step
        (primeSelectorScanCfg (true :: input) candidate output found) =
      some (primeSelectorScanCfg input (true :: candidate) output found) := by
  simp [primeSelectorComputer, FinTM2.step, primeSelectorScanCfg,
    primeSelectorCfg, primeSelectorProgram, primeSelectorStackContents,
    primeSelectorObserve, primeSelectorObservedPresent,
    primeSelectorObservedBit, primeSelectorResetObserved,
    initList, haltList, Function.update]
  funext index
  rcases index with outer | index
  · cases outer <;> simp [primeSelectorStackContents, Function.update]
  · by_cases h : index = unaryCandidatePrimeComputer.k₀
    · subst index
      simp [primeSelectorStackContents, Function.update]
    · simp [primeSelectorStackContents, Function.update, h]

private theorem primeSelector_step_scan_false
    (input candidate output : List Bool) (found : Bool) :
    primeSelectorComputer.step
        (primeSelectorScanCfg (false :: input) candidate output found) =
      some (primeSelectorLookaheadCfg input candidate output found) := by
  simp [primeSelectorComputer, FinTM2.step, primeSelectorScanCfg,
    primeSelectorLookaheadCfg, primeSelectorCfg, primeSelectorProgram,
    primeSelectorStackContents, primeSelectorObserve,
    primeSelectorObservedPresent, primeSelectorObservedBit,
    primeSelectorResetObserved, initList, haltList, Function.update]

private theorem primeSelector_step_lookahead_present
    (bit : Bool) (input candidate output : List Bool) (found : Bool) :
    primeSelectorComputer.step
        (primeSelectorLookaheadCfg (bit :: input) candidate output found) =
      some (primeSelectorLiftCfg (bit :: input) candidate output found
        (initList unaryCandidatePrimeComputer candidate)) := by
  simp [primeSelectorComputer, FinTM2.step, primeSelectorLookaheadCfg,
    primeSelectorLiftCfg, primeSelectorCfg, primeSelectorProgram,
    primeSelectorStackContents, primeSelectorObserve,
    primeSelectorObservedPresent, primeSelectorObservedBit,
    primeSelectorResetObserved, initList, Function.update]

private theorem primeSelector_step_lookahead_nil
    (candidate output : List Bool) (found : Bool) :
    primeSelectorComputer.step
        (primeSelectorLookaheadCfg [] candidate output found) =
      some (primeSelectorDiscardCfg candidate output found) := by
  simp [primeSelectorComputer, FinTM2.step, primeSelectorLookaheadCfg,
    primeSelectorDiscardCfg, primeSelectorCfg, primeSelectorProgram,
    primeSelectorStackContents, primeSelectorObserve,
    primeSelectorObservedPresent, primeSelectorResetObserved,
    initList, haltList, Function.update]

private def encodePrimeSelection : Option ℕ → List Bool
  | none => []
  | some candidate => unaryEncodeNat candidate

private def primeSelectionFound : Option ℕ → Bool
  | none => false
  | some _ => true

@[simp]
private theorem candidatePrime_initList_empty_stacks :
    (initList unaryCandidatePrimeComputer []).stk = (fun _ => []) := by
  funext index
  by_cases h : index = unaryCandidatePrimeComputer.k₀
  · subst index
    simp [initList]
  · simp [initList, h]

@[simp]
private theorem candidatePrime_initList_pop_input
    (bit : Bool) (input : List Bool) :
    Function.update (initList unaryCandidatePrimeComputer (bit :: input)).stk
        unaryCandidatePrimeComputer.k₀ input =
      (initList unaryCandidatePrimeComputer input).stk := by
  funext index
  by_cases h : index = unaryCandidatePrimeComputer.k₀
  · subst index
    simp [initList, Function.update]
  · simp [initList, Function.update, h]

@[simp]
private theorem candidatePrime_haltList_pop_result (result : Bool) :
    Function.update (haltList unaryCandidatePrimeComputer [result]).stk
        unaryCandidatePrimeComputer.k₁ [] = (fun _ => []) := by
  funext index
  by_cases h : index = unaryCandidatePrimeComputer.k₁
  · subst index
    simp [haltList, Function.update]
  · simp [haltList, Function.update, h]

private theorem primeSelector_haltList_eq_cfg (output : List Bool) :
    haltList primeSelectorComputer output =
      primeSelectorCfg none primeSelectorInitialState [] [] output
        (fun _ => []) := by
  unfold haltList primeSelectorCfg primeSelectorComputer
  congr 2
  funext index
  rcases index with outer | index
  · cases outer <;> simp [primeSelectorStackContents]
  · simp [primeSelectorStackContents]

private theorem primeSelector_step_result_true
    (input candidate output : List Bool) (found : Bool) :
    primeSelectorComputer.step
        (primeSelectorLiftCfg input candidate output found
          (haltList unaryCandidatePrimeComputer [true])) =
      some (primeSelectorIdleCfg .clearSelected input candidate output true) := by
  simp [primeSelectorComputer, FinTM2.step, primeSelectorLiftCfg,
    primeSelectorIdleCfg, primeSelectorCfg, primeSelectorProgram,
    primeSelectorStackContents, primeSelectorObserve,
    primeSelectorObservedBit, primeSelectorSetFound, haltList,
    Function.update]
  funext index
  rcases index with outer | index
  · cases outer <;> simp [primeSelectorStackContents, Function.update]
  · by_cases h : index = unaryCandidatePrimeComputer.k₁
    · subst index
      simp [primeSelectorStackContents, Function.update]
    · simp [primeSelectorStackContents, Function.update, h]

private theorem primeSelector_step_result_false
    (input candidate output : List Bool) (found : Bool) :
    primeSelectorComputer.step
        (primeSelectorLiftCfg input candidate output found
          (haltList unaryCandidatePrimeComputer [false])) =
      some (primeSelectorIdleCfg .clearCandidate input candidate output found) := by
  simp [primeSelectorComputer, FinTM2.step, primeSelectorLiftCfg,
    primeSelectorIdleCfg, primeSelectorCfg, primeSelectorProgram,
    primeSelectorStackContents, primeSelectorObserve,
    primeSelectorObservedBit, primeSelectorResetObserved, haltList,
    Function.update]
  funext index
  rcases index with outer | index
  · cases outer <;> simp [primeSelectorStackContents, Function.update]
  · by_cases h : index = unaryCandidatePrimeComputer.k₁
    · subst index
      simp [primeSelectorStackContents, Function.update]
    · simp [primeSelectorStackContents, Function.update, h]

private theorem primeSelector_step_clearCandidate_cons
    (bit : Bool) (input candidate output : List Bool) (found : Bool) :
    primeSelectorComputer.step
        (primeSelectorIdleCfg .clearCandidate input (bit :: candidate)
          output found) =
      some (primeSelectorIdleCfg .clearCandidate input candidate output found) := by
  simp [primeSelectorComputer, FinTM2.step, primeSelectorIdleCfg,
    primeSelectorCfg, primeSelectorProgram, primeSelectorStackContents,
    primeSelectorObserve, primeSelectorObservedPresent,
    primeSelectorResetObserved, haltList, Function.update]

private theorem primeSelector_step_clearCandidate_nil
    (input output : List Bool) (found : Bool) :
    primeSelectorComputer.step
        (primeSelectorIdleCfg .clearCandidate input [] output found) =
      some (primeSelectorScanCfg input [] output found) := by
  simp [primeSelectorComputer, FinTM2.step, primeSelectorIdleCfg,
    primeSelectorScanCfg, primeSelectorCfg, primeSelectorProgram,
    primeSelectorStackContents, primeSelectorObserve,
    primeSelectorObservedPresent, primeSelectorResetObserved,
    Function.update]
  rw [candidatePrime_initList_empty_stacks]

private theorem primeSelector_step_clearSelected_cons
    (bit : Bool) (input candidate output : List Bool) :
    primeSelectorComputer.step
        (primeSelectorIdleCfg .clearSelected input candidate (bit :: output)
          true) =
      some (primeSelectorIdleCfg .clearSelected input candidate output true) := by
  simp [primeSelectorComputer, FinTM2.step, primeSelectorIdleCfg,
    primeSelectorCfg, primeSelectorProgram, primeSelectorStackContents,
    primeSelectorObserve, primeSelectorObservedPresent,
    primeSelectorResetObserved, haltList, Function.update]

private theorem primeSelector_step_clearSelected_nil
    (input candidate : List Bool) :
    primeSelectorComputer.step
        (primeSelectorIdleCfg .clearSelected input candidate [] true) =
      some (primeSelectorIdleCfg .moveCandidate input candidate [] true) := by
  simp [primeSelectorComputer, FinTM2.step, primeSelectorIdleCfg,
    primeSelectorCfg, primeSelectorProgram, primeSelectorStackContents,
    primeSelectorObserve, primeSelectorObservedPresent,
    primeSelectorResetObserved, haltList, Function.update]

private theorem primeSelector_step_moveCandidate_cons
    (bit : Bool) (input candidate output : List Bool) :
    primeSelectorComputer.step
        (primeSelectorIdleCfg .moveCandidate input (bit :: candidate)
          output true) =
      some (primeSelectorIdleCfg .moveCandidate input candidate
        (bit :: output) true) := by
  simp [primeSelectorComputer, FinTM2.step, primeSelectorIdleCfg,
    primeSelectorCfg, primeSelectorProgram, primeSelectorStackContents,
    primeSelectorObserve, primeSelectorObservedPresent,
    primeSelectorObservedBit, primeSelectorResetObserved, haltList,
    Function.update]

private theorem primeSelector_step_moveCandidate_nil
    (input output : List Bool) :
    primeSelectorComputer.step
        (primeSelectorIdleCfg .moveCandidate input [] output true) =
      some (primeSelectorScanCfg input [] output true) := by
  simp [primeSelectorComputer, FinTM2.step, primeSelectorIdleCfg,
    primeSelectorScanCfg, primeSelectorCfg, primeSelectorProgram,
    primeSelectorStackContents, primeSelectorObserve,
    primeSelectorObservedPresent, primeSelectorResetObserved,
    Function.update]
  rw [candidatePrime_initList_empty_stacks]

private theorem primeSelector_step_discardCount_cons
    (bit : Bool) (candidate output : List Bool) (found : Bool) :
    primeSelectorComputer.step
        (primeSelectorDiscardCfg (bit :: candidate) output found) =
      some (primeSelectorDiscardCfg candidate output found) := by
  simp [primeSelectorComputer, FinTM2.step, primeSelectorDiscardCfg,
    primeSelectorCfg, primeSelectorProgram, primeSelectorStackContents,
    primeSelectorObserve, primeSelectorObservedPresent,
    primeSelectorResetObserved, Function.update]
  rw [show ((initList unaryCandidatePrimeComputer
      (bit :: candidate)).stk unaryCandidatePrimeComputer.k₀).tail =
        candidate by simp [initList]]
  rw [candidatePrime_initList_pop_input]

private theorem primeSelector_step_discardCount_nil
    (output : List Bool) (found : Bool) :
    primeSelectorComputer.step
        (primeSelectorDiscardCfg [] output found) =
      some (primeSelectorIdleCfg .finalize [] [] output found) := by
  simp [primeSelectorComputer, FinTM2.step, primeSelectorDiscardCfg,
    primeSelectorIdleCfg, primeSelectorCfg, primeSelectorProgram,
    primeSelectorStackContents, primeSelectorObserve,
    primeSelectorObservedPresent, primeSelectorResetObserved,
    Function.update]
  rw [candidatePrime_initList_empty_stacks]

private theorem primeSelector_step_finalize_found (output : List Bool) :
    primeSelectorComputer.step
        (primeSelectorIdleCfg .finalize [] [] output true) =
      some (haltList primeSelectorComputer output) := by
  rw [primeSelector_haltList_eq_cfg]
  simp [primeSelectorComputer, FinTM2.step, primeSelectorIdleCfg,
    primeSelectorCfg, primeSelectorProgram, primeSelectorStackContents,
    primeSelectorInitialState, Function.update]

private theorem primeSelector_step_finalize_none :
    primeSelectorComputer.step
        (primeSelectorIdleCfg .finalize [] [] [] false) =
      some (haltList primeSelectorComputer (unaryEncodeNat 2)) := by
  rw [primeSelector_haltList_eq_cfg]
  simp [primeSelectorComputer, FinTM2.step, primeSelectorIdleCfg,
    primeSelectorCfg, primeSelectorProgram, primeSelectorStackContents,
    primeSelectorInitialState, unaryEncodeNat, Function.update]

private def primeSelector_scan_unary_evals
    (n : ℕ) (input candidate output : List Bool) (found : Bool) :
    EvalsToInTime primeSelectorComputer.step
      (primeSelectorScanCfg
        (List.replicate n true ++ input) candidate output found)
      (some (primeSelectorScanCfg input
        (List.replicate n true ++ candidate) output found)) n := by
  induction n generalizing candidate with
  | zero =>
      exact EvalsToInTime.refl primeSelectorComputer.step _
  | succ n ih =>
      let middle := primeSelectorScanCfg
        (List.replicate n true ++ input) (true :: candidate) output found
      have hone : EvalsToInTime primeSelectorComputer.step
          (primeSelectorScanCfg
            (List.replicate (n + 1) true ++ input) candidate output found)
          (some middle) 1 :=
        primeSelectorEvalsToInTimeOne (by
          simpa [middle, List.replicate_succ] using
            primeSelector_step_scan_true
              (List.replicate n true ++ input) candidate output found)
      have hrest := ih (true :: candidate)
      have htrans := EvalsToInTime.trans primeSelectorComputer.step
        1 n
        (primeSelectorScanCfg
          (List.replicate (n + 1) true ++ input) candidate output found)
        middle
        (some (primeSelectorScanCfg input
          (List.replicate (n + 1) true ++ candidate) output found))
        hone
        (by
          simpa [middle, List.replicate_succ', List.replicate_add,
            List.append_assoc] using hrest)
      simpa [Nat.add_comm] using htrans

private def primeSelector_clearCandidate_evals
    (candidate input output : List Bool) (found : Bool) :
    EvalsToInTime primeSelectorComputer.step
      (primeSelectorIdleCfg .clearCandidate input candidate output found)
      (some (primeSelectorScanCfg input [] output found))
      (candidate.length + 1) := by
  induction candidate with
  | nil =>
      exact primeSelectorEvalsToInTimeOne
        (primeSelector_step_clearCandidate_nil input output found)
  | cons bit candidate ih =>
      let middle := primeSelectorIdleCfg .clearCandidate input candidate
        output found
      have hone := primeSelectorEvalsToInTimeOne
        (primeSelector_step_clearCandidate_cons bit input candidate output found)
      have htrans := EvalsToInTime.trans primeSelectorComputer.step
        1 (candidate.length + 1)
        (primeSelectorIdleCfg .clearCandidate input (bit :: candidate)
          output found)
        middle
        (some (primeSelectorScanCfg input [] output found))
        (by simpa [middle] using hone)
        (by simpa [middle] using ih)
      simpa [Nat.add_assoc, Nat.add_comm] using htrans

private def primeSelector_clearSelected_evals
    (output input candidate : List Bool) :
    EvalsToInTime primeSelectorComputer.step
      (primeSelectorIdleCfg .clearSelected input candidate output true)
      (some (primeSelectorIdleCfg .moveCandidate input candidate [] true))
      (output.length + 1) := by
  induction output with
  | nil =>
      exact primeSelectorEvalsToInTimeOne
        (primeSelector_step_clearSelected_nil input candidate)
  | cons bit output ih =>
      let middle := primeSelectorIdleCfg .clearSelected input candidate
        output true
      have hone := primeSelectorEvalsToInTimeOne
        (primeSelector_step_clearSelected_cons bit input candidate output)
      have htrans := EvalsToInTime.trans primeSelectorComputer.step
        1 (output.length + 1)
        (primeSelectorIdleCfg .clearSelected input candidate (bit :: output)
          true)
        middle
        (some (primeSelectorIdleCfg .moveCandidate input candidate [] true))
        (by simpa [middle] using hone)
        (by simpa [middle] using ih)
      simpa [Nat.add_assoc, Nat.add_comm] using htrans

private def primeSelector_moveCandidate_evals
    (candidate input output : List Bool) :
    EvalsToInTime primeSelectorComputer.step
      (primeSelectorIdleCfg .moveCandidate input candidate output true)
      (some (primeSelectorScanCfg input [] (candidate.reverse ++ output) true))
      (candidate.length + 1) := by
  induction candidate generalizing output with
  | nil =>
      simpa using primeSelectorEvalsToInTimeOne
        (primeSelector_step_moveCandidate_nil input output)
  | cons bit candidate ih =>
      let middle := primeSelectorIdleCfg .moveCandidate input candidate
        (bit :: output) true
      have hone := primeSelectorEvalsToInTimeOne
        (primeSelector_step_moveCandidate_cons bit input candidate output)
      have hrest := ih (bit :: output)
      have htrans := EvalsToInTime.trans primeSelectorComputer.step
        1 (candidate.length + 1)
        (primeSelectorIdleCfg .moveCandidate input (bit :: candidate)
          output true)
        middle
        (some (primeSelectorScanCfg input []
          ((bit :: candidate).reverse ++ output) true))
        (by simpa [middle] using hone)
        (by simpa [middle, List.reverse_cons, List.append_assoc] using hrest)
      simpa [Nat.add_assoc, Nat.add_comm] using htrans

private def primeSelector_discardCount_evals
    (candidate output : List Bool) (found : Bool) :
    EvalsToInTime primeSelectorComputer.step
      (primeSelectorDiscardCfg candidate output found)
      (some (primeSelectorIdleCfg .finalize [] [] output found))
      (candidate.length + 1) := by
  induction candidate with
  | nil =>
      exact primeSelectorEvalsToInTimeOne
        (primeSelector_step_discardCount_nil output found)
  | cons bit candidate ih =>
      let middle := primeSelectorDiscardCfg candidate output found
      have hone := primeSelectorEvalsToInTimeOne
        (primeSelector_step_discardCount_cons bit candidate output found)
      have htrans := EvalsToInTime.trans primeSelectorComputer.step
        1 (candidate.length + 1)
        (primeSelectorDiscardCfg (bit :: candidate) output found)
        middle
        (some (primeSelectorIdleCfg .finalize [] [] output found))
        (by simpa [middle] using hone)
        (by simpa [middle] using ih)
      simpa [Nat.add_assoc, Nat.add_comm] using htrans

private def primeSelectorFinalizeEvals (selection : Option ℕ) :
    EvalsToInTime primeSelectorComputer.step
      (primeSelectorIdleCfg .finalize [] []
        (encodePrimeSelection selection) (primeSelectionFound selection))
      (some (haltList primeSelectorComputer
        (unaryEncodeNat (selection.getD 2)))) 1 := by
  cases selection with
  | none =>
      simpa [encodePrimeSelection, primeSelectionFound] using
        primeSelectorEvalsToInTimeOne primeSelector_step_finalize_none
  | some candidate =>
      simpa [encodePrimeSelection, primeSelectionFound] using
        primeSelectorEvalsToInTimeOne
          (primeSelector_step_finalize_found (unaryEncodeNat candidate))

/-- A coarse exact stage budget.  The old selected value is included because
an accepted candidate first erases that output before installing itself. -/
private def primeSelectorCandidateTime
    (candidate : ℕ) (selection : Option ℕ) : ℕ :=
  64 * (candidate + 1) ^ 2 + 2 * candidate +
    (encodePrimeSelection selection).length + 5

private noncomputable def primeSelector_candidate_evals
    (candidate : ℕ) (input : List Bool) (hinput : input ≠ [])
    (selection : Option ℕ) :
    EvalsToInTime primeSelectorComputer.step
      (primeSelectorScanCfg
        (RawUnaryNatList.segment candidate ++ input) []
        (encodePrimeSelection selection) (primeSelectionFound selection))
      (some (primeSelectorScanCfg input []
        (encodePrimeSelection
          (if unaryCandidatePrime candidate then some candidate else selection))
        (primeSelectionFound
          (if unaryCandidatePrime candidate then some candidate else selection))))
      (primeSelectorCandidateTime candidate selection) := by
  rcases input with _ | ⟨bit, input⟩
  · contradiction
  let output := encodePrimeSelection selection
  let found := primeSelectionFound selection
  have hscan := primeSelector_scan_unary_evals candidate
    (false :: bit :: input) [] output found
  let afterScan := primeSelectorScanCfg (false :: bit :: input)
    (unaryEncodeNat candidate) output found
  have hscan' : EvalsToInTime primeSelectorComputer.step
      (primeSelectorScanCfg
        (RawUnaryNatList.segment candidate ++ bit :: input) [] output found)
      (some afterScan) candidate := by
    simpa [afterScan, RawUnaryNatList.segment,
      unaryEncodeNat_eq_replicate_true] using hscan
  have hseparator := primeSelectorEvalsToInTimeOne
    (primeSelector_step_scan_false (bit :: input)
      (unaryEncodeNat candidate) output found)
  let afterSeparator := primeSelectorLookaheadCfg (bit :: input)
    (unaryEncodeNat candidate) output found
  have hlookahead := primeSelectorEvalsToInTimeOne
    (primeSelector_step_lookahead_present bit input
      (unaryEncodeNat candidate) output found)
  let componentStart := primeSelectorLiftCfg (bit :: input)
    (unaryEncodeNat candidate) output found
    (initList unaryCandidatePrimeComputer (unaryEncodeNat candidate))
  have hparseFirst := EvalsToInTime.trans primeSelectorComputer.step
    candidate 1
    (primeSelectorScanCfg
      (RawUnaryNatList.segment candidate ++ bit :: input) [] output found)
    afterScan (some afterSeparator)
    hscan' (by simpa [afterScan, afterSeparator] using hseparator)
  have hparseFirst' : EvalsToInTime primeSelectorComputer.step
      (primeSelectorScanCfg
        (RawUnaryNatList.segment candidate ++ bit :: input) [] output found)
      (some afterSeparator) (candidate + 1) :=
    evalsToInTimeMono hparseFirst (by omega)
  have hparse := EvalsToInTime.trans primeSelectorComputer.step
    (candidate + 1) 1
    (primeSelectorScanCfg
      (RawUnaryNatList.segment candidate ++ bit :: input) [] output found)
    afterSeparator (some componentStart)
    hparseFirst'
    (by simpa [afterSeparator, componentStart] using hlookahead)
  have hparse' : EvalsToInTime primeSelectorComputer.step
      (primeSelectorScanCfg
        (RawUnaryNatList.segment candidate ++ bit :: input) [] output found)
      (some componentStart) (candidate + 2) :=
    evalsToInTimeMono hparse (by omega)
  have hcomponentBase : EvalsToInTime unaryCandidatePrimeComputer.step
      (initList unaryCandidatePrimeComputer (unaryEncodeNat candidate))
      (some (haltList unaryCandidatePrimeComputer
        [unaryCandidatePrime candidate]))
      (64 * (candidate + 1) ^ 2) := by
    simpa [TM2OutputsInTime, encodeBool, List.pure_def] using
      unaryCandidatePrime_outputsInTime candidate
  have hcomponent := primeSelector_lift_evals
    (bit :: input) (unaryEncodeNat candidate) output found hcomponentBase
  have hfirst := EvalsToInTime.trans primeSelectorComputer.step
    (candidate + 2) (64 * (candidate + 1) ^ 2)
    (primeSelectorScanCfg
      (RawUnaryNatList.segment candidate ++ bit :: input) [] output found)
    componentStart
    (some (primeSelectorLiftCfg (bit :: input)
      (unaryEncodeNat candidate) output found
      (haltList unaryCandidatePrimeComputer [unaryCandidatePrime candidate])))
    hparse'
    (by simpa [componentStart] using hcomponent)
  by_cases hprime : unaryCandidatePrime candidate
  · have hfirstTrue : EvalsToInTime primeSelectorComputer.step
        (primeSelectorScanCfg
          (RawUnaryNatList.segment candidate ++ bit :: input) [] output found)
        (some (primeSelectorLiftCfg (bit :: input)
          (unaryEncodeNat candidate) output found
          (haltList unaryCandidatePrimeComputer [true])))
        (64 * (candidate + 1) ^ 2 + (candidate + 2)) := by
      simpa [hprime] using hfirst
    have hresult := primeSelectorEvalsToInTimeOne
      (primeSelector_step_result_true (bit :: input)
        (unaryEncodeNat candidate) output found)
    have hclear := primeSelector_clearSelected_evals output
      (bit :: input) (unaryEncodeNat candidate)
    have hmove := primeSelector_moveCandidate_evals
      (unaryEncodeNat candidate) (bit :: input) []
    have hsecond := EvalsToInTime.trans primeSelectorComputer.step
      1 (output.length + 1)
      (primeSelectorLiftCfg (bit :: input) (unaryEncodeNat candidate)
        output found (haltList unaryCandidatePrimeComputer [true]))
      (primeSelectorIdleCfg .clearSelected (bit :: input)
        (unaryEncodeNat candidate) output true)
      (some (primeSelectorIdleCfg .moveCandidate (bit :: input)
        (unaryEncodeNat candidate) [] true))
      (by simpa using hresult) (by simpa using hclear)
    have hsecond' : EvalsToInTime primeSelectorComputer.step
        (primeSelectorLiftCfg (bit :: input) (unaryEncodeNat candidate)
          output found (haltList unaryCandidatePrimeComputer [true]))
        (some (primeSelectorIdleCfg .moveCandidate (bit :: input)
          (unaryEncodeNat candidate) [] true))
        (output.length + 2) :=
      evalsToInTimeMono hsecond (by omega)
    have hcleanup := EvalsToInTime.trans primeSelectorComputer.step
      (output.length + 2) (candidate + 1)
      (primeSelectorLiftCfg (bit :: input) (unaryEncodeNat candidate)
        output found (haltList unaryCandidatePrimeComputer [true]))
      (primeSelectorIdleCfg .moveCandidate (bit :: input)
        (unaryEncodeNat candidate) [] true)
      (some (primeSelectorScanCfg (bit :: input) []
        (unaryEncodeNat candidate) true))
      hsecond'
      (by simpa [unaryEncodeNat_length, unaryEncodeNat_reverse] using hmove)
    have hcleanup' : EvalsToInTime primeSelectorComputer.step
        (primeSelectorLiftCfg (bit :: input) (unaryEncodeNat candidate)
          output found (haltList unaryCandidatePrimeComputer [true]))
        (some (primeSelectorScanCfg (bit :: input) []
          (unaryEncodeNat candidate) true))
        (candidate + output.length + 3) :=
      evalsToInTimeMono hcleanup (by omega)
    have hall := EvalsToInTime.trans primeSelectorComputer.step
      (64 * (candidate + 1) ^ 2 + (candidate + 2))
      (candidate + output.length + 3)
      (primeSelectorScanCfg
        (RawUnaryNatList.segment candidate ++ bit :: input) [] output found)
      (primeSelectorLiftCfg (bit :: input) (unaryEncodeNat candidate)
        output found (haltList unaryCandidatePrimeComputer [true]))
      (some (primeSelectorScanCfg (bit :: input) []
        (unaryEncodeNat candidate) true))
      hfirstTrue hcleanup'
    have hmono : EvalsToInTime primeSelectorComputer.step
        (primeSelectorScanCfg
          (RawUnaryNatList.segment candidate ++ bit :: input) [] output found)
        (some (primeSelectorScanCfg (bit :: input) []
          (unaryEncodeNat candidate) true))
        (primeSelectorCandidateTime candidate selection) :=
      evalsToInTimeMono hall (by
        unfold primeSelectorCandidateTime
        simp only [output]
        omega)
    simpa [output, found, hprime, encodePrimeSelection,
      primeSelectionFound] using hmono
  · have hfirstFalse : EvalsToInTime primeSelectorComputer.step
        (primeSelectorScanCfg
          (RawUnaryNatList.segment candidate ++ bit :: input) [] output found)
        (some (primeSelectorLiftCfg (bit :: input)
          (unaryEncodeNat candidate) output found
          (haltList unaryCandidatePrimeComputer [false])))
        (64 * (candidate + 1) ^ 2 + (candidate + 2)) := by
      simpa [hprime] using hfirst
    have hresult := primeSelectorEvalsToInTimeOne
      (primeSelector_step_result_false (bit :: input)
        (unaryEncodeNat candidate) output found)
    have hclear := primeSelector_clearCandidate_evals
      (unaryEncodeNat candidate) (bit :: input) output found
    have hcleanup := EvalsToInTime.trans primeSelectorComputer.step
      1 (candidate + 1)
      (primeSelectorLiftCfg (bit :: input) (unaryEncodeNat candidate)
        output found (haltList unaryCandidatePrimeComputer [false]))
      (primeSelectorIdleCfg .clearCandidate (bit :: input)
        (unaryEncodeNat candidate) output found)
      (some (primeSelectorScanCfg (bit :: input) [] output found))
      (by simpa using hresult)
      (by simpa [unaryEncodeNat_length] using hclear)
    have hcleanup' : EvalsToInTime primeSelectorComputer.step
        (primeSelectorLiftCfg (bit :: input) (unaryEncodeNat candidate)
          output found (haltList unaryCandidatePrimeComputer [false]))
        (some (primeSelectorScanCfg (bit :: input) [] output found))
        (candidate + 2) :=
      evalsToInTimeMono hcleanup (by omega)
    have hall := EvalsToInTime.trans primeSelectorComputer.step
      (64 * (candidate + 1) ^ 2 + (candidate + 2))
      (candidate + 2)
      (primeSelectorScanCfg
        (RawUnaryNatList.segment candidate ++ bit :: input) [] output found)
      (primeSelectorLiftCfg (bit :: input) (unaryEncodeNat candidate)
        output found (haltList unaryCandidatePrimeComputer [false]))
      (some (primeSelectorScanCfg (bit :: input) [] output found))
      hfirstFalse hcleanup'
    exact evalsToInTimeMono
      (by simpa [output, found, hprime] using hall)
      (by simp [primeSelectorCandidateTime]; omega)

private def encodedUnaryCandidateFields (candidates : List ℕ) : List Bool :=
  candidates.reverse.flatMap RawUnaryNatList.segment

@[simp]
private theorem encodedUnaryCandidateFields_cons
    (candidate : ℕ) (candidates : List ℕ) :
    encodedUnaryCandidateFields (candidate :: candidates) =
      encodedUnaryCandidateFields candidates ++
        RawUnaryNatList.segment candidate := by
  simp [encodedUnaryCandidateFields, List.reverse_cons, List.flatMap_append]

private def primeSelectorCandidatesTime : List ℕ → ℕ
  | [] => 0
  | candidate :: candidates =>
      primeSelectorCandidateTime candidate
          (firstUnaryCandidatePrime? candidates) +
        primeSelectorCandidatesTime candidates

private noncomputable def primeSelector_candidates_evals
    (candidates : List ℕ) (input : List Bool) (hinput : input ≠ []) :
    EvalsToInTime primeSelectorComputer.step
      (primeSelectorScanCfg
        (encodedUnaryCandidateFields candidates ++ input) [] [] false)
      (some (primeSelectorScanCfg input []
        (encodePrimeSelection (firstUnaryCandidatePrime? candidates))
        (primeSelectionFound (firstUnaryCandidatePrime? candidates))))
      (primeSelectorCandidatesTime candidates) := by
  induction candidates generalizing input with
  | nil =>
      exact EvalsToInTime.refl primeSelectorComputer.step _
  | cons candidate candidates ih =>
      let fieldInput := RawUnaryNatList.segment candidate ++ input
      have hfieldInput : fieldInput ≠ [] := by
        simp [fieldInput, RawUnaryNatList.segment]
      have hrest := ih fieldInput hfieldInput
      let selection := firstUnaryCandidatePrime? candidates
      let middle := primeSelectorScanCfg fieldInput []
        (encodePrimeSelection selection) (primeSelectionFound selection)
      have hcandidate := primeSelector_candidate_evals
        candidate input hinput selection
      have htrans := EvalsToInTime.trans primeSelectorComputer.step
        (primeSelectorCandidatesTime candidates)
        (primeSelectorCandidateTime candidate selection)
        (primeSelectorScanCfg
          (encodedUnaryCandidateFields (candidate :: candidates) ++ input)
          [] [] false)
        middle
        (some (primeSelectorScanCfg input []
          (encodePrimeSelection
            (firstUnaryCandidatePrime? (candidate :: candidates)))
          (primeSelectionFound
            (firstUnaryCandidatePrime? (candidate :: candidates)))))
        (by
          simpa [middle, fieldInput, encodedUnaryCandidateFields_cons,
            List.append_assoc, selection] using hrest)
        (by
          by_cases hprime : unaryCandidatePrime candidate
          · simpa [middle, fieldInput, selection, firstUnaryCandidatePrime?,
              hprime] using hcandidate
          · simpa [middle, fieldInput, selection, firstUnaryCandidatePrime?,
              hprime] using hcandidate)
      simpa [primeSelectorCandidatesTime, selection, Nat.add_comm] using htrans

private noncomputable def primeSelector_count_evals
    (count : ℕ) (selection : Option ℕ) :
    EvalsToInTime primeSelectorComputer.step
      (primeSelectorScanCfg (RawUnaryNatList.segment count) []
        (encodePrimeSelection selection) (primeSelectionFound selection))
      (some (haltList primeSelectorComputer
        (unaryEncodeNat (selection.getD 2))))
      (2 * count + 4) := by
  let output := encodePrimeSelection selection
  let found := primeSelectionFound selection
  have hscan := primeSelector_scan_unary_evals count [false] [] output found
  let afterScan := primeSelectorScanCfg [false]
    (unaryEncodeNat count) output found
  have hscan' : EvalsToInTime primeSelectorComputer.step
      (primeSelectorScanCfg (RawUnaryNatList.segment count) [] output found)
      (some afterScan) count := by
    simpa [afterScan, RawUnaryNatList.segment,
      unaryEncodeNat_eq_replicate_true] using hscan
  have hseparator := primeSelectorEvalsToInTimeOne
    (primeSelector_step_scan_false [] (unaryEncodeNat count) output found)
  let afterSeparator := primeSelectorLookaheadCfg []
    (unaryEncodeNat count) output found
  have hlookahead := primeSelectorEvalsToInTimeOne
    (primeSelector_step_lookahead_nil (unaryEncodeNat count) output found)
  let afterLookahead := primeSelectorDiscardCfg (unaryEncodeNat count)
    output found
  have hdiscard := primeSelector_discardCount_evals
    (unaryEncodeNat count) output found
  let beforeFinalize := primeSelectorIdleCfg .finalize [] [] output found
  have hfinal := primeSelectorFinalizeEvals selection
  have hfirst := EvalsToInTime.trans primeSelectorComputer.step
    count 1
    (primeSelectorScanCfg (RawUnaryNatList.segment count) [] output found)
    afterScan (some afterSeparator)
    hscan' (by simpa [afterScan, afterSeparator] using hseparator)
  have hfirst' : EvalsToInTime primeSelectorComputer.step
      (primeSelectorScanCfg (RawUnaryNatList.segment count) [] output found)
      (some afterSeparator) (count + 1) :=
    evalsToInTimeMono hfirst (by omega)
  have hsecond := EvalsToInTime.trans primeSelectorComputer.step
    (count + 1) 1
    (primeSelectorScanCfg (RawUnaryNatList.segment count) [] output found)
    afterSeparator (some afterLookahead)
    hfirst' (by simpa [afterSeparator, afterLookahead] using hlookahead)
  have hsecond' : EvalsToInTime primeSelectorComputer.step
      (primeSelectorScanCfg (RawUnaryNatList.segment count) [] output found)
      (some afterLookahead) (count + 2) :=
    evalsToInTimeMono hsecond (by omega)
  have hthird := EvalsToInTime.trans primeSelectorComputer.step
    (count + 2) (count + 1)
    (primeSelectorScanCfg (RawUnaryNatList.segment count) [] output found)
    afterLookahead (some beforeFinalize)
    (by simpa [afterLookahead] using hsecond')
    (by simpa [afterLookahead, beforeFinalize, unaryEncodeNat_length] using
      hdiscard)
  have hthird' : EvalsToInTime primeSelectorComputer.step
      (primeSelectorScanCfg (RawUnaryNatList.segment count) [] output found)
      (some beforeFinalize) (2 * count + 3) :=
    evalsToInTimeMono hthird (by omega)
  have hall := EvalsToInTime.trans primeSelectorComputer.step
    (2 * count + 3) 1
    (primeSelectorScanCfg (RawUnaryNatList.segment count) [] output found)
    beforeFinalize
    (some (haltList primeSelectorComputer
      (unaryEncodeNat (selection.getD 2))))
    (by simpa [beforeFinalize] using hthird')
    (by simpa [beforeFinalize, output, found] using hfinal)
  exact evalsToInTimeMono
    (by simpa [output, found] using hall) (by omega)

private theorem rawUnaryNatList_encode_eq_fields (candidates : List ℕ) :
    RawUnaryNatList.encode candidates =
      encodedUnaryCandidateFields candidates ++
        RawUnaryNatList.segment candidates.length := by
  simp [RawUnaryNatList.encode, RawUnaryNatList.payloads,
    encodedUnaryCandidateFields, List.reverse_cons, List.flatMap_append]

private theorem primeSelector_initList_eq_scanCfg (input : List Bool) :
    initList primeSelectorComputer input =
      primeSelectorScanCfg input [] [] false := by
  unfold initList primeSelectorScanCfg primeSelectorCfg
    primeSelectorComputer primeSelectorInitialState
  congr 2
  funext index
  rcases index with outer | index
  · cases outer <;> rfl
  · rw [primeSelectorStackContents, candidatePrime_initList_empty_stacks]
    rfl

/-- The driver computes the first accepted unary candidate with a concrete
stage-sensitive runtime bound. -/
noncomputable def primeSelector_outputsInTime (candidates : List ℕ) :
    TM2OutputsInTime primeSelectorComputer
      (RawUnaryNatList.encode candidates)
      (some (unaryEncodeNat (selectUnaryCandidatePrime candidates)))
      (primeSelectorCandidatesTime candidates + 2 * candidates.length + 4) := by
  let countInput := RawUnaryNatList.segment candidates.length
  have hcountInput : countInput ≠ [] := by
    simp [countInput, RawUnaryNatList.segment]
  have hcandidates := primeSelector_candidates_evals
    candidates countInput hcountInput
  let selection := firstUnaryCandidatePrime? candidates
  have hcount := primeSelector_count_evals candidates.length selection
  have htrans := EvalsToInTime.trans primeSelectorComputer.step
    (primeSelectorCandidatesTime candidates) (2 * candidates.length + 4)
    (primeSelectorScanCfg (RawUnaryNatList.encode candidates) [] [] false)
    (primeSelectorScanCfg countInput []
      (encodePrimeSelection selection) (primeSelectionFound selection))
    (some (haltList primeSelectorComputer
      (unaryEncodeNat (selectUnaryCandidatePrime candidates))))
    (by
      rw [rawUnaryNatList_encode_eq_fields]
      simpa [countInput, selection] using hcandidates)
    (by simpa [countInput, selection, selectUnaryCandidatePrime] using hcount)
  rw [TM2OutputsInTime, primeSelector_initList_eq_scanCfg]
  simp only [Option.map_some]
  exact evalsToInTimeMono htrans (by omega)

private theorem nat_le_list_sum_of_mem {value : ℕ} {values : List ℕ}
    (hvalue : value ∈ values) : value ≤ values.sum := by
  induction values with
  | nil => simp at hvalue
  | cons head tail ih =>
      rcases List.mem_cons.mp hvalue with rfl | htail
      · simp
      · have hle := ih htail
        simp only [List.sum_cons]
        omega

private theorem encodePrimeSelection_firstUnaryCandidatePrime?_length_le
    (candidates : List ℕ) (bound : ℕ)
    (hbound : ∀ candidate ∈ candidates, candidate ≤ bound) :
    (encodePrimeSelection
      (firstUnaryCandidatePrime? candidates)).length ≤ bound := by
  cases hselection : firstUnaryCandidatePrime? candidates with
  | none => simp [encodePrimeSelection]
  | some candidate =>
      have hmem := firstUnaryCandidatePrime?_mem hselection
      simpa [encodePrimeSelection, unaryEncodeNat_length] using
        hbound candidate hmem

private theorem primeSelectorCandidateTime_le
    (candidate bound : ℕ) (selection : Option ℕ)
    (hcandidate : candidate ≤ bound)
    (hselection : (encodePrimeSelection selection).length ≤ bound) :
    primeSelectorCandidateTime candidate selection ≤
      70 * (bound + 1) ^ 2 := by
  have hpow : (candidate + 1) ^ 2 ≤ (bound + 1) ^ 2 :=
    Nat.pow_le_pow_left (by omega) 2
  unfold primeSelectorCandidateTime
  nlinarith

private theorem primeSelectorCandidatesTime_le
    (candidates : List ℕ) (bound : ℕ)
    (hbound : ∀ candidate ∈ candidates, candidate ≤ bound) :
    primeSelectorCandidatesTime candidates ≤
      candidates.length * (70 * (bound + 1) ^ 2) := by
  induction candidates with
  | nil => simp [primeSelectorCandidatesTime]
  | cons candidate candidates ih =>
      have hcandidate : candidate ≤ bound :=
        hbound candidate (List.mem_cons_self)
      have htail : ∀ value ∈ candidates, value ≤ bound := by
        intro value hvalue
        exact hbound value (List.mem_cons_of_mem candidate hvalue)
      have hselection :=
        encodePrimeSelection_firstUnaryCandidatePrime?_length_le
          candidates bound htail
      have hstep := primeSelectorCandidateTime_le candidate bound
        (firstUnaryCandidatePrime? candidates) hcandidate hselection
      have hrest := ih htail
      simp only [primeSelectorCandidatesTime, List.length_cons]
      nlinarith

private theorem primeSelectorTime_le_cubic (candidates : List ℕ) :
    primeSelectorCandidatesTime candidates + 2 * candidates.length + 4 ≤
      80 * ((RawUnaryNatList.encode candidates).length + 1) ^ 3 := by
  let size := (RawUnaryNatList.encode candidates).length
  have hsum : candidates.sum ≤ size := by
    simp only [size, RawUnaryNatList.encode_length]
    omega
  have hlength : candidates.length ≤ size := by
    simp only [size, RawUnaryNatList.encode_length]
    omega
  have hvalues : ∀ candidate ∈ candidates, candidate ≤ size := by
    intro candidate hcandidate
    exact (nat_le_list_sum_of_mem hcandidate).trans hsum
  have hfields := primeSelectorCandidatesTime_le candidates size hvalues
  have hfields' : primeSelectorCandidatesTime candidates ≤
      size * (70 * (size + 1) ^ 2) :=
    hfields.trans (Nat.mul_le_mul_right (70 * (size + 1) ^ 2) hlength)
  have hone : 1 ≤ (size + 1) ^ 2 := by
    exact Nat.one_le_pow' 2 size
  calc
    primeSelectorCandidatesTime candidates + 2 * candidates.length + 4
        ≤ size * (70 * (size + 1) ^ 2) + 2 * size + 4 := by omega
    _ ≤ 80 * (size + 1) ^ 3 := by
      rw [show (size + 1) ^ 3 = (size + 1) * (size + 1) ^ 2 by ring]
      nlinarith

/-- Genuine polynomial time in the complete unary-list wire length for the
first-survivor driver.  This is independent of the separate producer/runtime
composition still needed by the full compiler. -/
noncomputable def primeSelectorComputableInPolyTime :
    @TM2ComputableInPolyTime (List ℕ) ℕ RawUnaryNatList.finEncoding
      unaryFinEncodingNat selectUnaryCandidatePrime where
  tm := primeSelectorComputer
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := 80 * (Polynomial.X + 1) ^ 3
  outputsFun candidates := by
    have hrun := primeSelector_outputsInTime candidates
    have hmono := evalsToInTimeMono hrun
      (primeSelectorTime_le_cubic candidates)
    simpa [RawUnaryNatList.finEncoding, unaryFinEncodingNat, Equiv.refl,
      Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add,
      Polynomial.eval_natCast, Polynomial.eval_one, Polynomial.eval_X] using
        hmono

/-- On the checked Bertrand stream, the driver emits exactly the selected
compiler prime. -/
theorem primeSelector_selects_firstBertrandPrime (q : ℕ) :
    selectUnaryCandidatePrime (bertrandCandidates q) =
      firstBertrandPrime q :=
  selectUnaryCandidatePrime_bertrandCandidates q

/-! ## Compiler-selected prime composition

The final prime-selection pass composes the native unary Bertrand producer
with the checked first-survivor selector.  The intermediate stream is
quadratic in the unary bound, so the selector's cubic wire-length bound gives
a degree-six bound in that bound.  This remains separate from the structural
CSP pass that must produce the unary distinct-symbol count.
-/

private def unaryBertrandCandidateAux :
    TM2ComputableAux Bool Bool where
  tm := unaryBertrandCandidateComputer
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool

private def primeSelectorAux :
    TM2ComputableAux Bool Bool where
  tm := primeSelectorComputer
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool

/-- Concrete sequential machine that chooses the compiler prime from a unary
distinct-symbol bound. -/
def selectedPrimeComputer : FinTM2 :=
  compositionMachine unaryBertrandCandidateAux primeSelectorAux

private def selectedPrimeStartCfg
    (state : ControlState unaryBertrandCandidateAux primeSelectorAux)
    (input : List Bool) : selectedPrimeComputer.Cfg where
  l := some (leftLabel unaryBertrandCandidateAux primeSelectorAux .count)
  var := state
  stk := transferLeftStacks unaryBertrandCandidateAux primeSelectorAux
    (unaryBertrandStackContents input [] [] [] [])

private theorem selectedPrime_initList_eq_cfg (input : List Bool) :
    initList selectedPrimeComputer input =
      selectedPrimeStartCfg
        (leftState unaryBertrandCandidateAux primeSelectorAux
          unaryBertrandCandidateAux.tm.initialState) input := by
  unfold initList selectedPrimeComputer compositionMachine
    selectedPrimeStartCfg unaryBertrandCandidateAux primeSelectorAux
    unaryBertrandCandidateComputer primeSelectorComputer transferLeftStacks
    unaryBertrandStackContents extendStacks leftStacks transferLeftIndex
  congr 2
  funext index
  rcases index with (index | index)
  · rcases index with (index | index)
    · cases index <;> rfl
    · rfl
  · cases index
    rfl

private theorem selectedPrime_left_init_eq_cfg (input : List Bool) :
    liftScratchCfg unaryBertrandCandidateAux primeSelectorAux []
        (liftLeftControlCfg unaryBertrandCandidateAux primeSelectorAux
          (initList unaryBertrandCandidateAux.tm input)) =
      selectedPrimeStartCfg
        (leftState unaryBertrandCandidateAux primeSelectorAux
          unaryBertrandCandidateAux.tm.initialState) input := by
  simp only [unaryBertrandCandidateAux]
  rw [unaryBertrand_initList_eq_cfg]
  rfl

private theorem selectedPrime_init_step (input : List Bool) :
    selectedPrimeComputer.step (initList selectedPrimeComputer input) =
      selectedPrimeComputer.step
        (liftScratchCfg unaryBertrandCandidateAux primeSelectorAux []
          (liftLeftControlCfg unaryBertrandCandidateAux primeSelectorAux
            (initList unaryBertrandCandidateAux.tm input))) := by
  rw [selectedPrime_initList_eq_cfg, selectedPrime_left_init_eq_cfg]

private theorem selectedPrime_haltList_eq (output : List Bool) :
    haltList selectedPrimeComputer output =
      rightPhaseCfg unaryBertrandCandidateAux primeSelectorAux (fun _ => []) []
        (haltList primeSelectorAux.tm output) := by
  unfold selectedPrimeComputer compositionMachine haltList rightPhaseCfg
    unaryBertrandCandidateAux primeSelectorAux unaryBertrandCandidateComputer
    primeSelectorComputer
  congr 2
  funext index
  rcases index with (index | index)
  · rcases index with (index | index)
    · cases index <;> simp [extendStacks, rightPhaseStacks,
        transferRightIndex]
      all_goals
        intro h
        cases h
    · rcases index with (outer | component)
      · cases outer <;> simp [extendStacks, rightPhaseStacks,
          transferRightIndex]
        all_goals
          intro h
          cases h
      · simp [extendStacks, rightPhaseStacks, transferRightIndex]
        intro h
        cases h
  · cases index
    simp [extendStacks, transferRightIndex]

private theorem selectedPrime_iterate_init
    (steps : ℕ) (hsteps : 0 < steps) (input : List Bool) :
    (flip Option.bind selectedPrimeComputer.step)^[steps]
        (some (initList selectedPrimeComputer input)) =
      (flip Option.bind selectedPrimeComputer.step)^[steps]
        (some (liftScratchCfg unaryBertrandCandidateAux primeSelectorAux []
          (liftLeftControlCfg unaryBertrandCandidateAux primeSelectorAux
            (initList unaryBertrandCandidateAux.tm input)))) := by
  obtain ⟨remaining, rfl⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.ne_of_gt hsteps)
  rw [Function.iterate_succ_apply]
  change
    (flip Option.bind selectedPrimeComputer.step)^[remaining]
        (selectedPrimeComputer.step (initList selectedPrimeComputer input)) =
      (flip Option.bind selectedPrimeComputer.step)^[remaining]
        (selectedPrimeComputer.step
          (liftScratchCfg unaryBertrandCandidateAux primeSelectorAux []
            (liftLeftControlCfg unaryBertrandCandidateAux primeSelectorAux
              (initList unaryBertrandCandidateAux.tm input))))
  rw [selectedPrime_init_step]

private noncomputable def selectedPrime_generator_evals (q : ℕ) :
    EvalsToInTime selectedPrimeComputer.step
      (initList selectedPrimeComputer (unaryEncodeNat q))
      (some (liftScratchCfg unaryBertrandCandidateAux primeSelectorAux []
        (leftTransferEntryCfg unaryBertrandCandidateAux primeSelectorAux
          (haltList unaryBertrandCandidateAux.tm
            (RawUnaryNatList.encode (bertrandCandidates q))).var
          (haltList unaryBertrandCandidateAux.tm
            (RawUnaryNatList.encode (bertrandCandidates q))).stk)))
      (6 * (q + 1) ^ 2) := by
  let output := RawUnaryNatList.encode (bertrandCandidates q)
  have hgenerator : EvalsToInTime unaryBertrandCandidateAux.tm.step
      (initList unaryBertrandCandidateAux.tm (unaryEncodeNat q))
      (some (haltList unaryBertrandCandidateAux.tm output))
      (6 * (q + 1) ^ 2) := by
    simpa [unaryBertrandCandidateAux, output] using
      unaryBertrandCandidate_outputsInTime q
  have hpositive : 0 < hgenerator.steps := by
    apply Nat.pos_of_ne_zero
    intro hzero
    have heq := hgenerator.evals_in_steps
    rw [hzero, Function.iterate_zero_apply] at heq
    injection heq with hcfg
    have hlabels := congrArg
      (fun cfg : unaryBertrandCandidateAux.tm.Cfg => cfg.l) hcfg
    simp [initList, haltList] at hlabels
  have hleftRun := compositionProgram_left_run_to_transfer
    unaryBertrandCandidateAux primeSelectorAux hgenerator.steps
    (initList unaryBertrandCandidateAux.tm (unaryEncodeNat q))
    (haltList unaryBertrandCandidateAux.tm output)
    unaryBertrandCandidateAux.tm.main [] rfl hgenerator.evals_in_steps rfl
  refine
    { steps := hgenerator.steps
      evals_in_steps := ?_
      steps_le_m := hgenerator.steps_le_m }
  rw [show selectedPrimeComputer.step =
      TM2.step (compositionProgram unaryBertrandCandidateAux primeSelectorAux) by
    rfl]
  calc
    (flip Option.bind
        (TM2.step
          (compositionProgram unaryBertrandCandidateAux primeSelectorAux)))^[
            hgenerator.steps]
        (some (initList selectedPrimeComputer (unaryEncodeNat q))) =
      (flip Option.bind selectedPrimeComputer.step)^[hgenerator.steps]
        (some (liftScratchCfg unaryBertrandCandidateAux primeSelectorAux []
          (liftLeftControlCfg unaryBertrandCandidateAux primeSelectorAux
            (initList unaryBertrandCandidateAux.tm
              (unaryEncodeNat q))))) := by
        exact selectedPrime_iterate_init hgenerator.steps hpositive _
    _ = some (liftScratchCfg unaryBertrandCandidateAux primeSelectorAux []
        (leftTransferEntryCfg unaryBertrandCandidateAux primeSelectorAux
          (haltList unaryBertrandCandidateAux.tm output).var
          (haltList unaryBertrandCandidateAux.tm output).stk)) := hleftRun

private def selectedPrimeRightContents (input : List Bool) :
    (index : StackIndex unaryBertrandCandidateAux.tm primeSelectorAux.tm) →
      List (StackAlphabet unaryBertrandCandidateAux.tm primeSelectorAux.tm
        index) :=
  rightStacks unaryBertrandCandidateAux.tm primeSelectorAux.tm
    (initList primeSelectorAux.tm input).stk

private theorem selectedPrime_rightEntryMachineCfg (input : List Bool) :
    rightEntryMachineCfg unaryBertrandCandidateAux primeSelectorAux
        (selectedPrimeRightContents input) =
      initList primeSelectorAux.tm input := by
  rfl

private theorem selectedPrime_transferStart_eq (output : List Bool) :
    liftScratchCfg unaryBertrandCandidateAux primeSelectorAux []
        (leftTransferEntryCfg unaryBertrandCandidateAux primeSelectorAux
          (haltList unaryBertrandCandidateAux.tm output).var
          (haltList unaryBertrandCandidateAux.tm output).stk) =
      transferActionCfg unaryBertrandCandidateAux primeSelectorAux
        (.phase .reverseOutput)
        (leftState unaryBertrandCandidateAux primeSelectorAux
          unaryBertrandCandidateAux.tm.initialState)
        (Function.update
          (Function.update (fun _ => []) (Sum.inr primeSelectorAux.tm.k₀) [])
          (Sum.inl unaryBertrandCandidateAux.tm.k₁) output) [] := by
  simp only [unaryBertrandCandidateAux]
  rw [unaryBertrand_haltList_eq_cfg]
  unfold liftScratchCfg leftTransferEntryCfg transferActionCfg
    unaryBertrandCfg unaryBertrandStackContents primeSelectorAux
    primeSelectorComputer leftStacks extendStacks
  congr 2
  funext index
  rcases index with (index | index)
  · rcases index with (index | index)
    · cases index <;> rfl
    · rcases index with (outer | component)
      · cases outer <;> rfl
      · rfl
  · cases index
    rfl

private theorem selectedPrime_transferFinish_eq (output : List Bool) :
    rightEntryCfg unaryBertrandCandidateAux primeSelectorAux
        (selectedPrimeRightContents output) [] =
      rightEntryCfg unaryBertrandCandidateAux primeSelectorAux
        (Function.update
          (Function.update (fun _ => [])
            (Sum.inl unaryBertrandCandidateAux.tm.k₁) [])
          (Sum.inr primeSelectorAux.tm.k₀)
          (output.map (middleAlphabetEquiv unaryBertrandCandidateAux
            primeSelectorAux) ++ [])) [] := by
  congr 2
  unfold selectedPrimeRightContents
  unfold rightStacks middleAlphabetEquiv unaryBertrandCandidateAux
    unaryBertrandCandidateComputer primeSelectorAux primeSelectorComputer
  funext index
  rcases index with (index | index)
  · simp [Function.update]
    intro h
    cases h
    rfl
  · by_cases hindex : index = (Sum.inl PrimeSelectorOuterStack.input)
    · subst index
      simp [initList, Function.update]
      induction output with
      | nil => rfl
      | cons head tail ih =>
          simp only [List.map_cons]
          exact congrArg (fun xs : List Bool => head :: xs) ih
    · simp [initList, Function.update, hindex]
      intro h
      exact (hindex (Sum.inr.inj h)).elim

private def selectedPrime_transfer_evals (q : ℕ) :
    EvalsToInTime selectedPrimeComputer.step
      (liftScratchCfg unaryBertrandCandidateAux primeSelectorAux []
        (leftTransferEntryCfg unaryBertrandCandidateAux primeSelectorAux
          (haltList unaryBertrandCandidateAux.tm
            (RawUnaryNatList.encode (bertrandCandidates q))).var
          (haltList unaryBertrandCandidateAux.tm
            (RawUnaryNatList.encode (bertrandCandidates q))).stk))
      (some (rightEntryCfg unaryBertrandCandidateAux primeSelectorAux
        (selectedPrimeRightContents
          (RawUnaryNatList.encode (bertrandCandidates q))) []))
      (4 * (RawUnaryNatList.encode (bertrandCandidates q)).length + 4) := by
  let output := RawUnaryNatList.encode (bertrandCandidates q)
  refine
    { steps := 4 * output.length + 4
      evals_in_steps := ?_
      steps_le_m := Nat.le_refl _ }
  rw [selectedPrime_transferStart_eq output,
    selectedPrime_transferFinish_eq output]
  exact compositionProgram_transfer_whole_list unaryBertrandCandidateAux
    primeSelectorAux
    (leftState unaryBertrandCandidateAux primeSelectorAux
      unaryBertrandCandidateAux.tm.initialState)
    (fun _ => []) output []

private theorem selectedPrime_rightEntry_eq (input : List Bool) :
    rightEntryCfg unaryBertrandCandidateAux primeSelectorAux
        (selectedPrimeRightContents input) [] =
      rightPhaseCfg unaryBertrandCandidateAux primeSelectorAux (fun _ => []) []
        (initList primeSelectorAux.tm input) := by
  rw [rightEntryCfg_eq_rightPhaseCfg,
    selectedPrime_rightEntryMachineCfg]
  congr 1

private noncomputable def selectedPrime_second_evals (q : ℕ) :
    EvalsToInTime selectedPrimeComputer.step
      (rightEntryCfg unaryBertrandCandidateAux primeSelectorAux
        (selectedPrimeRightContents
          (RawUnaryNatList.encode (bertrandCandidates q))) [])
      (some (haltList selectedPrimeComputer
        (unaryEncodeNat (selectPrimeAbove q))))
      (80 *
        ((RawUnaryNatList.encode (bertrandCandidates q)).length + 1) ^ 3) := by
  let input := RawUnaryNatList.encode (bertrandCandidates q)
  let selected := selectUnaryCandidatePrime (bertrandCandidates q)
  have hsecondExact : EvalsToInTime primeSelectorAux.tm.step
      (initList primeSelectorAux.tm input)
      (some (haltList primeSelectorAux.tm (unaryEncodeNat selected)))
      (primeSelectorCandidatesTime (bertrandCandidates q) + 2 * q + 4) := by
    simpa [primeSelectorAux, input, selected, bertrandCandidates_length] using
      primeSelector_outputsInTime (bertrandCandidates q)
  have hsecond : EvalsToInTime primeSelectorAux.tm.step
      (initList primeSelectorAux.tm input)
      (some (haltList primeSelectorAux.tm (unaryEncodeNat selected)))
      (80 * (input.length + 1) ^ 3) :=
    evalsToInTimeMono hsecondExact (by
      simpa [input, bertrandCandidates_length] using
        primeSelectorTime_le_cubic (bertrandCandidates q))
  have hrightRun := compositionProgram_right_run unaryBertrandCandidateAux
    primeSelectorAux hsecond.steps
    (initList primeSelectorAux.tm input)
    (haltList primeSelectorAux.tm (unaryEncodeNat selected))
    (fun _ => []) [] hsecond.evals_in_steps
  refine
    { steps := hsecond.steps
      evals_in_steps := ?_
      steps_le_m := hsecond.steps_le_m }
  rw [selectedPrime_rightEntry_eq]
  change (flip Option.bind selectedPrimeComputer.step)^[hsecond.steps]
      (some (rightPhaseCfg unaryBertrandCandidateAux primeSelectorAux
        (fun _ => []) [] (initList primeSelectorAux.tm input))) =
    some (haltList selectedPrimeComputer (unaryEncodeNat (selectPrimeAbove q)))
  rw [selectedPrime_haltList_eq]
  simpa [input, selected, primeSelector_selects_firstBertrandPrime,
    firstBertrandPrime_eq_selectPrimeAbove] using hrightRun

private theorem selectedPrimeTime_le_degreeSix (q : ℕ) :
    (80 * ((RawUnaryNatList.encode (bertrandCandidates q)).length + 1) ^ 3) +
        (4 * (RawUnaryNatList.encode (bertrandCandidates q)).length + 4 +
          6 * (q + 1) ^ 2) ≤
      1000 * (q + 1) ^ 6 := by
  have hstream := unaryBertrandCandidateStream_length_le q
  have hstream' :
      (RawUnaryNatList.encode (bertrandCandidates q)).length + 1 ≤
        2 * (q + 1) ^ 2 := by
    nlinarith
  have hcubic := Nat.pow_le_pow_left hstream' 3
  have hlinear :
      (RawUnaryNatList.encode (bertrandCandidates q)).length ≤
        2 * (q + 1) ^ 2 := by
    omega
  calc
    80 * ((RawUnaryNatList.encode (bertrandCandidates q)).length + 1) ^ 3 +
          (4 * (RawUnaryNatList.encode (bertrandCandidates q)).length + 4 +
            6 * (q + 1) ^ 2)
        ≤ 80 * (2 * (q + 1) ^ 2) ^ 3 +
          (4 * (2 * (q + 1) ^ 2) + 4 + 6 * (q + 1) ^ 2) := by
            omega
    _ ≤ 1000 * (q + 1) ^ 6 := by
      rw [show (2 * (q + 1) ^ 2) ^ 3 = 8 * (q + 1) ^ 6 by ring]
      have hqpow : (q + 1) ^ 2 ≤ (q + 1) ^ 6 :=
        Nat.pow_le_pow_right (by omega) (by omega)
      have hpone : 1 ≤ (q + 1) ^ 6 := Nat.one_le_pow' 6 q
      have hrest :
          4 * (2 * (q + 1) ^ 2) + 4 + 6 * (q + 1) ^ 2 ≤
            18 * (q + 1) ^ 6 := by
        calc
          4 * (2 * (q + 1) ^ 2) + 4 + 6 * (q + 1) ^ 2 =
              14 * (q + 1) ^ 2 + 4 := by ring
          _ ≤ 14 * (q + 1) ^ 6 + 4 :=
            Nat.add_le_add_right (Nat.mul_le_mul_left 14 hqpow) 4
          _ ≤ 18 * (q + 1) ^ 6 := by omega
      omega

/-- The composed machine emits the compiler-selected prime in polynomial time
from the unary distinct-symbol bound, including the explicit `q = 0, 1`
conventions. -/
noncomputable def selectedPrime_outputsInTime (q : ℕ) :
    TM2OutputsInTime selectedPrimeComputer (unaryEncodeNat q)
      (some (unaryEncodeNat (selectPrimeAbove q)))
      (1000 * (q + 1) ^ 6) := by
  let stream := RawUnaryNatList.encode (bertrandCandidates q)
  have hgenerator := selectedPrime_generator_evals q
  have htransfer := selectedPrime_transfer_evals q
  have hsecond := selectedPrime_second_evals q
  have hfirst := EvalsToInTime.trans selectedPrimeComputer.step
    (6 * (q + 1) ^ 2) (4 * stream.length + 4)
    (initList selectedPrimeComputer (unaryEncodeNat q))
    (liftScratchCfg unaryBertrandCandidateAux primeSelectorAux []
      (leftTransferEntryCfg unaryBertrandCandidateAux primeSelectorAux
        (haltList unaryBertrandCandidateAux.tm stream).var
        (haltList unaryBertrandCandidateAux.tm stream).stk))
    (some (rightEntryCfg unaryBertrandCandidateAux primeSelectorAux
      (selectedPrimeRightContents stream) []))
    (by simpa [stream] using hgenerator)
    (by simpa [stream] using htransfer)
  have hall := EvalsToInTime.trans selectedPrimeComputer.step
    (4 * stream.length + 4 + 6 * (q + 1) ^ 2)
    (80 * (stream.length + 1) ^ 3)
    (initList selectedPrimeComputer (unaryEncodeNat q))
    (rightEntryCfg unaryBertrandCandidateAux primeSelectorAux
      (selectedPrimeRightContents stream) [])
    (some (haltList selectedPrimeComputer
      (unaryEncodeNat (selectPrimeAbove q))))
    (by simpa [Nat.add_comm] using hfirst)
    (by simpa [stream] using hsecond)
  exact evalsToInTimeMono (by simpa [stream] using hall)
    (selectedPrimeTime_le_degreeSix q)

/-- Genuine polynomial-time compiler-owned selection of the prime used by the
p-adic objective. -/
noncomputable def selectedPrimeComputableInPolyTime :
    @TM2ComputableInPolyTime ℕ ℕ unaryFinEncodingNat
      unaryFinEncodingNat selectPrimeAbove where
  tm := selectedPrimeComputer
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := 1000 * (Polynomial.X + 1) ^ 6
  outputsFun q := by
    simpa [unaryFinEncodingNat, Equiv.refl,
      Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add,
      Polynomial.eval_natCast, Polynomial.eval_one, Polynomial.eval_X] using
        selectedPrime_outputsInTime q


end LeanNPHardness.MachinePrimitives
