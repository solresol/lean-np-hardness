# Theorem status

| Result | Status | Lean declaration or completion criterion |
|---|---|---|
| Semantic many-one reduction | Complete | `LeanNPHardness.ManyOneReduction` |
| Semantic identity reduction | Complete | `ManyOneReduction.refl` |
| Semantic composition | Complete | `ManyOneReduction.comp` |
| Polynomial-time many-one reduction structure | Complete | `LeanNPHardness.PolytimeManyOneReduction` |
| Polynomial-time identity reduction | Complete | `PolytimeManyOneReduction.refl` |
| Composition from an explicit machine witness | Complete | `PolytimeManyOneReduction.compOfWitness` |
| Polynomial-time composition after identity | Complete | `PolytimeManyOneReduction.reflComp` |
| Polynomial-time composition before identity | Complete | `PolytimeManyOneReduction.compRefl` |
| Left-machine combined-stack embedding | Complete | `MachineComposition.liftLeft_step` |
| Right-machine combined-stack embedding | Complete | `MachineComposition.liftRight_step` |
| Finite combined control and middle-alphabet bridge | Complete | `MachineComposition.ControlLabel`, `ControlState`, and `middleAlphabetEquiv` |
| Left-component combined-control simulation | Complete | `MachineComposition.liftLeftControl_step` |
| Right-component combined-control simulation | Complete | `MachineComposition.liftRightControl_step` |
| Left halt-to-transfer control | Complete | `MachineComposition.liftLeftThenTransfer_step` and `liftLeftThenTransfer_step_of_halt` |
| Two-stage transfer control and scratch-stack layout | Complete | `MachineComposition.TransferPhase`, `TransferStackIndex`, `transferLeftStacks_update`, and `transferRightStacks_update` |
| Combined-control scratch-stack simulation | Complete | `MachineComposition.liftScratch_step` |
| Reverse-output transfer iteration | Complete | `MachineComposition.reverseOutput_iteration_nonempty` and `reverseOutput_iteration_empty` |
| Reverse-output whole-list execution | Complete | `MachineComposition.reverseOutput_whole_list` |
| Fill-input transfer iteration | Complete | `MachineComposition.fillInput_iteration_nonempty` and `fillInput_iteration_empty` |
| Fill-input whole-list execution | Complete | `MachineComposition.fillInput_whole_list` |
| Intermediate-output transfer loop | Complete | `MachineComposition.transfer_whole_list` |
| Total scratch-layout program dispatch | Complete | `MachineComposition.compositionProgram` |
| Composed finite machine structure | Complete | `MachineComposition.compositionMachine` and `compositionAux` |
| Component steps under total dispatch | Complete | `MachineComposition.compositionProgram_left_step` and `compositionProgram_right_step` |
| Transfer execution under total dispatch | Complete | `MachineComposition.compositionProgram_transfer_whole_list` |
| First-component repeated execution under total dispatch | Complete | `MachineComposition.compositionProgram_left_run`, `compositionProgram_left_run_to_transfer`, and `compositionProgram_left_evalsTo_transfer` |
| Second-component repeated execution under total dispatch | Complete | `MachineComposition.liftRightThenHalt_stepAux`, `compositionProgram_right_step_preserving_left`, `compositionProgram_right_run`, `compositionProgram_right_evalsTo`, and `compositionProgram_rightEntry_evalsTo` |
| Three-phase exact composition execution | Complete | `MachineComposition.compositionProgram_complete_run` and `compositionProgram_complete_evalsTo` |
| Canonical list-output composition correctness | Complete | `MachineComposition.compositionMachine_outputs` |
| Function-level machine composition correctness | Complete | `MachineComposition.map_outputAlphabet_invFun_middleAlphabetEquiv` and `compositionComputable` |
| Polynomial-time encoded-output length bound | Complete | `MachineRuntime.computableInPolyTime_output_length_le` bounds encoded output length by encoded input length plus the declared time bound times a finite machine push constant. |
| Generic polynomial-time machine composition | Complete | `MachineComposition.compositionComputableInPolyTime` uses the concrete sequential machine, the checked first-output size polynomial, and the exact three-phase runtime. |
| Closed polynomial-time reduction composition | Complete | `PolytimeManyOneReduction.comp` derives its witness from `compositionComputableInPolyTime`. |
| Tagged finite encoding of pairs | Complete | `PairEncoding.finEncoding` uses disjoint component alphabets; `finEncoding_encode_length` proves exact additive encoded length. |
| Encoded decision language | Complete | `EncodedLanguage` bundles a predicate with the `FinEncoding` that fixes its input-size measure; `EncodedLanguage.PolytimeReducesTo` specializes the checked reduction relation. |
| P | Complete | `EncodedLanguage.PolytimeDecider` specifies both Boolean outcomes and a `TM2ComputableInPolyTime` witness; `EncodedLanguage.InP` is deterministic polynomial-time decidability. |
| NP | Complete | `EncodedLanguage.PolytimeVerifier` separates soundness, bounded completeness, and the checked polynomial-time verifier; `EncodedLanguage.InNP` existentially quantifies the finitely encoded certificate type, with constructor `PolytimeVerifier.toInNP`. |
| NP-hardness and NP-completeness | Pending | Define using the checked polynomial reduction relation and prove foundational transport lemmas. |
| CNF-SAT language and encoding | Pending | Concrete syntax, semantics, and finite encoding. |
| Exact 3-SAT is in NP | Pending | Checked verifier and runtime bound. |
| Cook--Levin | Pending | Polynomial reduction from every NP language to SAT. |
| Exact 3-SAT is NP-complete | Pending | Checked SAT-to-3-SAT normalization and final composition. |

## Initial audit

The initial declarations build with the pinned Lean and mathlib revisions.
`LeanNPHardness.Audit` reports:

- `ManyOneReduction.comp` depends on no axioms;
- `PolytimeManyOneReduction.refl` depends on `propext`,
  `Classical.choice`, and `Quot.sound`; and
- `PolytimeManyOneReduction.compOfWitness` depends on `propext` and
  `Quot.sound`; and
- `PolytimeManyOneReduction.reflComp` and
  `PolytimeManyOneReduction.compRefl` depend on `propext`,
  `Classical.choice`, and `Quot.sound`; and
- `MachineComposition.liftLeft_step` depends on `propext` and
  `Quot.sound`; and
- `MachineComposition.liftRight_step` depends on `propext` and
  `Quot.sound`; and
- `MachineComposition.middleAlphabetEquiv_symm_apply_apply` depends on
  `propext` and `Quot.sound`; and
- `MachineComposition.liftLeftControl_step` depends on `propext` and
  `Quot.sound`.
- `MachineComposition.liftLeftThenTransfer_step` and
  `MachineComposition.liftLeftThenTransfer_step_of_halt` depend on `propext`
  and `Quot.sound`.
- `MachineComposition.liftRightControl_step` depends on `propext` and
  `Quot.sound`.
- `MachineComposition.liftRightThenHalt_stepAux` depends on `propext` and
  `Quot.sound`.
- `MachineComposition.transferLabel_ne_fillInputLabel`,
  `transferLeftStacks_update`, and `transferRightStacks_update` depend on
  `propext` and `Quot.sound`.
- `MachineComposition.liftScratch_step` depends on `propext` and
  `Quot.sound`.
- `MachineComposition.reverseOutput_iteration_nonempty` and
  `reverseOutput_iteration_empty` depend on `propext`, `Classical.choice`, and
  `Quot.sound`.
- `MachineComposition.reverseOutput_whole_list` depends on `propext`,
  `Classical.choice`, and `Quot.sound`.
- `MachineComposition.fillInput_iteration_nonempty` depends on `propext`,
  `Classical.choice`, and `Quot.sound`; and
  `fillInput_iteration_empty` depends on `propext` and `Quot.sound`.
- `MachineComposition.fillInput_whole_list` depends on `propext`,
  `Classical.choice`, and `Quot.sound`.
- `MachineComposition.transfer_whole_list` depends on `propext`,
  `Classical.choice`, and `Quot.sound`.
- `MachineComposition.compositionProgram_left_step` and
  `compositionProgram_right_step` depend on `propext` and `Quot.sound`.
- `MachineComposition.compositionProgram_transfer_step` depends on `propext`
  and `Quot.sound`; and `compositionProgram_reverseOutput_whole_list`,
  `compositionProgram_fillInput_whole_list`, and
  `compositionProgram_transfer_whole_list` depend on `propext`,
  `Classical.choice`, and `Quot.sound`.
- `MachineComposition.compositionProgram_left_run` and
  `compositionProgram_left_run_to_transfer`, and
  `compositionProgram_left_evalsTo_transfer` depend on `propext` and
  `Quot.sound`.
- `MachineComposition.rightPhaseStacks_update`,
  `compositionProgram_right_step_preserving_left`,
  `compositionProgram_right_run`, `compositionProgram_right_evalsTo`,
  `rightEntryCfg_eq_rightPhaseCfg`, and
  `compositionProgram_rightEntry_evalsTo` depend on `propext` and
  `Quot.sound`.
- `MachineComposition.liftScratch_leftTransferEntryCfg_eq_transferStart`
  depends on `propext` and `Quot.sound`; and
  `compositionProgram_complete_run` and
  `compositionProgram_complete_evalsTo` depend on `propext`,
  `Classical.choice`, and `Quot.sound`.
- `MachineComposition.rightPhaseCfg_haltList` and
  `compositionMachine_outputs` depend on `propext`, `Classical.choice`, and
  `Quot.sound`.
- `MachineComposition.map_outputAlphabet_invFun_middleAlphabetEquiv` depends
  on `propext` and `Quot.sound`; `compositionComputable` additionally depends
  on `Classical.choice`.
- `MachineRuntime.stepAux_stack_length_le`, `run_stack_length_le`,
  `outputsInTime_output_length_le`, and
  `computableInPolyTime_output_length_le` depend on `propext`,
  `Classical.choice`, and `Quot.sound`.
- `MachineRuntime.polynomial_eval_mono`,
  `MachineComposition.outputSizePolynomial_eval`,
  `compositionTimePolynomial_eval`, `compositionMachine_outputsInTime`, and
  `compositionComputableInPolyTime` depend on `propext`,
  `Classical.choice`, and `Quot.sound`.
- `PolytimeManyOneReduction.comp` depends on `propext`, `Classical.choice`,
  and `Quot.sound`.
- `EncodedLanguage.PolytimeReducesTo`, `EncodedLanguage.InP`,
  `EncodedLanguage.PolytimeDecider.ofAcceptsIff`, and
  `EncodedLanguage.PolytimeDecider.toInP` depend on `propext` and
  `Quot.sound`.
- `PairEncoding.finEncoding`, `finEncoding_encode_length`,
  `EncodedLanguage.PolytimeVerifier.accepts_iff_exists_certificate`, and
  `EncodedLanguage.InNP`, and `EncodedLanguage.PolytimeVerifier.toInNP` depend
  on `propext`, `Classical.choice`, and `Quot.sound`.
- `MachineComposition.compositionAux` depends on `propext`,
  `Classical.choice`, and `Quot.sound`.

The source tree contains no `sorry`, `admit`, project-defined `axiom`, or
`unsafe` declaration.
