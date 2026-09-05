import LeanNPHardness.PairReductionOutputProgram

namespace LeanNPHardness.MachineAdapters

open Turing

private theorem initList_eq_update (tm : FinTM2)
    (input : List (tm.Γ tm.k₀)) :
    initList tm input = TM2.Cfg.mk (some tm.main) tm.initialState
      (Function.update (fun _ => []) tm.k₀ input) := by
  unfold initList
  congr 1
  funext index
  by_cases h : index = tm.k₀
  · subst index
    simp
  · simp [Function.update, h]

private theorem haltList_eq_update (tm : FinTM2)
    (output : List (tm.Γ tm.k₁)) :
    haltList tm output = TM2.Cfg.mk none tm.initialState
      (Function.update (fun _ => []) tm.k₁ output) := by
  unfold haltList
  congr 1
  funext index
  by_cases h : index = tm.k₁
  · subst index
    simp
  · simp [Function.update, h]

/-- The finite pair-left machine. Its input is the tagged source stack and its
output is the separate tagged result stack. Computation and runtime witnesses
are supplied separately. -/
def pairReductionMachine {Γ₀ Γ₁ Δ : Type}
    [Fintype Γ₀] [Fintype Γ₁] [Fintype Δ]
    (computer : TM2ComputableAux Γ₀ Γ₁) : FinTM2 where
  K := PairOutputStackIndex computer
  k₀ := Sum.inl (Sum.inl .source)
  k₁ := Sum.inr .output
  Γ := PairOutputStackAlphabet computer Δ
  Λ := PairReductionOutputControlLabel (Δ := Δ) computer
  main := pairReductionOutputReductionLabel computer
    (pairAdapterControlLabel computer (.split .scan))
  σ := PairReductionOutputControlState (Δ := Δ) computer
  initialState := pairReductionOutputReductionState computer
    (pairAdapterControlState computer none)
  Γk₀Fin := inferInstanceAs (Fintype (Sum Γ₀ Δ))
  m := pairReductionOutputProgram computer

/-- The external alphabets of the pair-left machine are already canonical. -/
def pairReductionAux {Γ₀ Γ₁ Δ : Type}
    [Fintype Γ₀] [Fintype Γ₁] [Fintype Δ]
    (computer : TM2ComputableAux Γ₀ Γ₁) :
    TM2ComputableAux (Sum Γ₀ Δ) (Sum Γ₁ Δ) where
  tm := pairReductionMachine computer
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _

/-- The canonical machine input is exactly the start of the checked dispatcher
execution, with every private reduction stack empty. -/
theorem pairReductionMachine_initList {Γ₀ Γ₁ Δ : Type}
    [Fintype Γ₀] [Fintype Γ₁] [Fintype Δ]
    (computer : TM2ComputableAux Γ₀ Γ₁) (source : List (Sum Γ₀ Δ)) :
    initList (pairReductionMachine computer) source =
      liftPairReductionThenOutputCfg computer [] []
        (liftPairAdapterThenTransferCfg computer
          (liftPairAdapterCfg computer (fun _ => [])
            (pairAdapterCfg (.split .scan) none source [] [] [] []))) := by
  unfold initList pairReductionMachine liftPairReductionThenOutputCfg
    liftPairAdapterThenTransferCfg liftPairAdapterCfg pairAdapterCfg
  congr 1
  funext index
  cases index with
  | inl workingIndex =>
      cases workingIndex with
      | inl adapterIndex =>
          cases adapterIndex <;>
            simp [PairOutputStackIndex, PairReductionStackIndex,
              pairOutputStacks, pairReductionStacks, pairAdapterStacks]
      | inr machineIndex =>
          simp [PairOutputStackIndex, PairReductionStackIndex,
            pairOutputStacks, pairReductionStacks]
  | inr extraIndex =>
      cases extraIndex <;> simp [PairOutputStackIndex, PairReductionStackIndex, pairOutputStacks]

/-- With the work stacks empty, the reassembly `done` configuration takes one
final step to the canonical halt, including the initial-state reset. -/
theorem pairReductionMachine_done_step {Γ₀ Γ₁ Δ : Type}
    [Fintype Γ₀] [Fintype Γ₁] [Fintype Δ]
    (computer : TM2ComputableAux Γ₀ Γ₁) (output : List (Sum Γ₁ Δ)) :
    (pairReductionMachine (Δ := Δ) computer).step
        (liftPairOutputTransferControlCfg computer
          (pairOutputTransferCfg computer .done none [] [] [] [] []
            (fun _ => []) [] output)) =
      some (haltList (pairReductionMachine computer) output) := by
  change some (TM2.Cfg.mk none
    (pairReductionOutputReductionState computer
      (pairAdapterControlState computer none))
    (pairOutputStacks computer
      (pairReductionStacks computer
        (pairAdapterStacks [] [] [] [] []) (fun _ => [])) [] output)) = _
  congr 1
  unfold haltList pairReductionMachine
  congr 1
  funext index
  cases index with
  | inl workingIndex =>
      cases workingIndex with
      | inl adapterIndex =>
          cases adapterIndex <;>
            simp [PairOutputStackIndex, PairReductionStackIndex,
              pairOutputStacks, pairReductionStacks, pairAdapterStacks]
      | inr machineIndex =>
          simp [PairOutputStackIndex, PairReductionStackIndex,
            pairOutputStacks, pairReductionStacks]
  | inr extraIndex =>
      cases extraIndex <;> simp [PairOutputStackIndex, PairReductionStackIndex, pairOutputStacks]

/-- A canonical list-output witness for the reduction yields a canonical
list-output witness for the pair-left machine. The exact count includes the
final step from the live reassembly `done` label to `haltList`. -/
def pairReductionMachine_outputs {Γ₀ Γ₁ Δ : Type}
    [Fintype Γ₀] [Fintype Γ₁] [Fintype Δ]
    (computer : TM2ComputableAux Γ₀ Γ₁) (source : List (Sum Γ₀ Δ))
    (privateOutput : List (computer.tm.Γ computer.tm.k₁))
    (reductionRun : TM2Outputs computer.tm
      ((PairEncoding.leftSymbols source).map computer.inputAlphabet.symm)
      (some privateOutput)) :
    TM2Outputs (pairReductionMachine computer) source
      (some ((privateOutput.map computer.outputAlphabet).map
          (Sum.inl : Γ₁ → Sum Γ₁ Δ) ++
        (PairEncoding.rightSymbols source).map (Sum.inr : Δ → Sum Γ₁ Δ))) := by
  let canonicalReductionRun : EvalsTo (TM2.step computer.tm.m)
      (TM2.Cfg.mk (some computer.tm.main) computer.tm.initialState
        (Function.update (fun _ => []) computer.tm.k₀
          ((PairEncoding.leftSymbols source).map computer.inputAlphabet.symm ++ [])))
      (some (TM2.Cfg.mk none computer.tm.initialState
        (Function.update (fun _ => []) computer.tm.k₁ privateOutput))) := by
    refine ⟨reductionRun.steps, ?_⟩
    simpa only [TM2Outputs, initList_eq_update, haltList_eq_update,
      List.append_nil, FinTM2.step, Option.map_some] using
      reductionRun.evals_in_steps
  let complete := pairReductionOutputProgram_complete_evalsTo computer source
    (fun _ => []) (fun _ => []) computer.tm.initialState privateOutput
    canonicalReductionRun
  refine ⟨complete.steps + 1, ?_⟩
  change (flip Option.bind (TM2.step (pairReductionOutputProgram computer)))^[
    complete.steps + 1]
    (some (initList (pairReductionMachine computer) source)) = _
  rw [pairReductionMachine_initList, Function.iterate_succ_apply']
  refine (congrArg (flip Option.bind
    (TM2.step (pairReductionOutputProgram computer)))
      complete.evals_in_steps).trans ?_
  simpa only [flip, Option.bind_some, Function.update_eq_self] using
    pairReductionMachine_done_step computer
      ((privateOutput.map computer.outputAlphabet).map
          (Sum.inl : Γ₁ → Sum Γ₁ Δ) ++
        (PairEncoding.rightSymbols source).map (Sum.inr : Δ → Sum Γ₁ Δ))

/-- The list-output witness has an exact linear overhead in the tagged source
and private reduced output lengths. Polynomial runtime packaging remains
separate from this equality. -/
theorem pairReductionMachine_outputs_steps {Γ₀ Γ₁ Δ : Type}
    [Fintype Γ₀] [Fintype Γ₁] [Fintype Δ]
    (computer : TM2ComputableAux Γ₀ Γ₁) (source : List (Sum Γ₀ Δ))
    (privateOutput : List (computer.tm.Γ computer.tm.k₁))
    (reductionRun : TM2Outputs computer.tm
      ((PairEncoding.leftSymbols source).map computer.inputAlphabet.symm)
      (some privateOutput)) :
    (pairReductionMachine_outputs computer source privateOutput
      reductionRun).steps =
      reductionRun.steps + 8 * source.length + 4 * privateOutput.length + 22 := by
  change (4 * privateOutput.length +
      4 * (PairEncoding.rightSymbols source).length + 8) +
    (reductionRun.steps + (4 * source.length +
      4 * (PairEncoding.leftSymbols source).length + 13)) + 1 = _
  have partition := PairEncoding.leftSymbols_length_add_rightSymbols_length source
  omega

end LeanNPHardness.MachineAdapters
