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
| Tagged-pair classification pass | Complete | `MachineAdapters.pairSplit_whole_list` consumes an arbitrary tagged list in exactly two steps per symbol plus two exhaustion steps and separates its projections onto private reverse stacks; `pairSplit_finEncoding_whole_list` specializes this to the canonical input/certificate encoding. |
| Tagged-pair order restoration | Complete | `MachineAdapters.pairRestore_whole_list` reverses both private component stacks into ordered stacks in exactly two steps per symbol plus two exhaustion steps per component; `pairRestore_finEncoding_whole_list` recovers the canonical input and certificate encodings. The standalone theorem is now integrated with classification by `pairAdapter_whole_list`. |
| Integrated tagged-pair preprocessing | Complete | `MachineAdapters.pairAdapter_whole_list` runs classification, the phase transition, and order restoration under one finite total dispatcher and one five-stack layout in exactly `4 * source.length + 7` steps; `pairAdapter_finEncoding_whole_list` recovers the canonical input and certificate encodings. |
| Reduction-machine pair-stack embedding | Complete | `MachineAdapters.PairReductionStackIndex` extends the five-stack preprocessing layout with every private reduction stack; `liftReduction_step` simulates one reduction-program step while preserving all preprocessing stacks, including the ordered certificate. |
| Ordered reduction-input transfer | Complete | `MachineAdapters.pairInputTransfer_whole_list` reverses the restored input through the emptied left scratch stack and fills the reduction machine's private input stack through `computer.inputAlphabet.symm` in exactly `4 * input.length + 4` steps, preserving the certificate and all other stacks. |
| Extended-layout pair preprocessing | Complete | `MachineAdapters.liftPairAdapter_whole_list` lifts the complete tagged-pair preprocessing run into `PairReductionStackAlphabet` with the same exact `4 * source.length + 7` cost while preserving every private reduction-machine stack. |
| Total pair-reduction preprocessing and input transfer | Complete | `MachineAdapters.pairReductionProgram` dispatches preprocessing, ordered-input transfer, and reduction-machine control under one finite phase-tagged label/state space; `pairReductionProgram_preprocess_transfer_whole_list` enters the reduction machine's declared `main` label and `initialState` in exactly `4 * source.length + 4 * (PairEncoding.leftSymbols source).length + 13` steps while preserving the ordered right projection. |
| Reduction execution under total pair dispatcher | Complete | `MachineAdapters.pairReductionProgram_machine_step_preserving_adapter`, `pairReductionProgram_machine_run`, and `pairReductionProgram_machine_evalsTo` lift any exact finite reduction-machine execution with the same step count while preserving all five adapter stacks, including the ordered certificate. |
| Standalone reduced-output/certificate reassembly | Complete | `MachineAdapters.pairOutputTransferProgram` extends the working layout with a canonical-output scratch stack and tagged result stack; `pairOutputTransfer_whole_list` empties the private reduction output and ordered certificate and constructs `reduced.map Sum.inl ++ certificate.map Sum.inr` in exactly `4 * reduced.length + 4 * certificate.length + 8` steps. |
| Total reduction-to-output dispatcher | Complete | `MachineAdapters.pairReductionOutputProgram` lifts the existing pair/reduction dispatcher onto `PairOutputStackAlphabet`, preserves the two output-only stacks, redirects a reached reduction halt into `certificateReverseScan` in the same counted step, and exactly lifts finite runs of both component dispatchers. |
| End-to-end pair-left execution | Complete | `MachineAdapters.pairReductionOutputProgram_complete_run` and `pairReductionOutputProgram_complete_evalsTo` compose preprocessing, ordered input transfer, an arbitrary exact reduction-machine run, and canonical output/certificate reassembly with the explicit sum of their exact costs. |
| Encoded decision language | Complete | `EncodedLanguage` bundles a predicate with the `FinEncoding` that fixes its input-size measure; `EncodedLanguage.PolytimeReducesTo` specializes the checked reduction relation. |
| P | Complete | `EncodedLanguage.PolytimeDecider` specifies both Boolean outcomes and a `TM2ComputableInPolyTime` witness; `EncodedLanguage.InP` is deterministic polynomial-time decidability. |
| NP | Complete | `EncodedLanguage.PolytimeVerifier` separates soundness, bounded completeness, and the checked polynomial-time verifier; `EncodedLanguage.InNP` existentially quantifies the finitely encoded certificate type, with constructor `PolytimeVerifier.toInNP`. |
| P is contained in NP | Complete | `EncodedLanguage.inP_toInNP` uses `PolytimeDecider.toUnitVerifier`, the zero-length `UnitEncoding.finEncoding`, and `MachineAdapters.ignoreUnitCertificate` to reuse the checked decider machine and runtime. |
| P transport along reductions | Complete | `PolytimeDecider.pullback` composes a checked reduction map with the target Boolean decider, preserving both Boolean semantics; `EncodedLanguage.InP.of_reduction` transports deterministic polynomial-time membership backward. |
| NP certificate-bound transport along reductions | Complete | `PolytimeVerifier.pullbackCertificateBound` composes the target certificate polynomial with the reduction machine's checked encoded-output-size polynomial; `pullback_complete` proves that transported completeness certificates satisfy that bound. |
| NP transport along reductions | Pending | The total dispatcher now has an exact end-to-end execution theorem with canonical tagged output. Expose its finite machine and canonical input/result stacks, prove the complete polynomial runtime, and combine the adapter with the checked certificate-bound transport. |
| NP-hardness and NP-completeness | Complete | `EncodedLanguage.NPHard` universally supplies nonempty checked reductions from encoded NP languages; `EncodedLanguage.NPComplete` pairs hardness with NP membership. `NPHard.of_reduction` transports hardness forward by `PolytimeManyOneReduction.comp`, and `NPComplete.of_reduction` combines that transport with separate target membership. |
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
- `MachineAdapters.pairSplit_whole_list` and `pairSplit_evalsTo` depend on
  `propext` and `Quot.sound`; the canonical-encoding specialization
  `pairSplit_finEncoding_whole_list` additionally depends on
  `Classical.choice`.
- `MachineAdapters.pairRestore_whole_list`, `pairRestore_evalsTo`, and
  `pairRestore_finEncoding_whole_list` depend on `propext` and `Quot.sound`.
- `PairEncoding.leftSymbols_length_add_rightSymbols_length`,
  `MachineAdapters.pairAdapter_whole_list`, and `pairAdapter_evalsTo` depend
  on `propext` and `Quot.sound`; `pairAdapter_finEncoding_whole_list`
  additionally depends on `Classical.choice`.
- `MachineAdapters.pairReductionStacks_machine_update`,
  `pairReductionStacks_adapter_update`, `liftReduction_step`, and
  `pairInputTransfer_reverse_whole_list` depend on `propext` and
  `Quot.sound`; `pairInputTransfer_fill_whole_list` and
  `pairInputTransfer_whole_list` additionally depend on `Classical.choice`.
- `MachineAdapters.liftPairAdapter_stepAux`, `liftPairAdapter_step`,
  `liftPairAdapter_run`, and `liftPairAdapter_whole_list` depend on `propext`
  and `Quot.sound`.
- `MachineAdapters.liftPairAdapterThenTransfer_stepAux`,
  `liftPairInputTransferThenReduction_stepAux`,
  `liftReductionMachineControl_stepAux`, `pairReductionProgram_adapter_run`,
  `pairReductionProgram_transfer_run`,
  `pairReductionProgram_machine_step_preserving_adapter`,
  `pairReductionProgram_machine_run`, and
  `pairReductionProgram_machine_evalsTo` depend on `propext` and
  `Quot.sound`; `pairReductionProgram_preprocess_transfer_whole_list`
  additionally depends on `Classical.choice`.
- `MachineAdapters.pairOutputTransfer_whole_list` depends on `propext`,
  `Classical.choice`, and `Quot.sound`.
- `MachineAdapters.liftPairReductionThenOutput_stepAux`,
  `pairReductionOutputProgram_reduction_run`,
  `pairReductionOutputProgram_halt_to_output`,
  `liftPairOutputTransferControl_stepAux`, and
  `pairReductionOutputProgram_output_run` depend on `propext` and
  `Quot.sound`.
- `MachineAdapters.pairReductionOutputProgram_complete_run` and
  `pairReductionOutputProgram_complete_evalsTo` depend on `propext`,
  `Classical.choice`, and `Quot.sound`.
- `EncodedLanguage.PolytimeReducesTo`, `EncodedLanguage.InP`,
  `EncodedLanguage.PolytimeDecider.ofAcceptsIff`, and
  `EncodedLanguage.PolytimeDecider.toInP` depend on `propext` and
  `Quot.sound`.
- `EncodedLanguage.PolytimeDecider.pullback` and
  `EncodedLanguage.InP.of_reduction` depend on `propext`,
  `Classical.choice`, and `Quot.sound`.
- `EncodedLanguage.PolytimeVerifier.pullbackCertificateBound`,
  `pullbackCertificateBound_eval`, and `pullback_complete` depend on `propext`,
  `Classical.choice`, and `Quot.sound`.
- `PairEncoding.finEncoding`, `finEncoding_encode_length`,
  `EncodedLanguage.PolytimeVerifier.accepts_iff_exists_certificate`, and
  `EncodedLanguage.InNP`, and `EncodedLanguage.PolytimeVerifier.toInNP` depend
  on `propext`, `Classical.choice`, and `Quot.sound`.
- `UnitEncoding.finEncoding` depends on `propext` and `Quot.sound`;
  `MachineAdapters.ignoreUnitCertificate`,
  `EncodedLanguage.PolytimeDecider.toUnitVerifier`, and
  `EncodedLanguage.inP_toInNP` additionally depend on `Classical.choice`.
- `EncodedLanguage.NPHard`, `EncodedLanguage.NPComplete`,
  `EncodedLanguage.NPHard.of_reduction`, and the `EncodedLanguage.NPComplete`
  projection and construction theorems depend on `propext`,
  `Classical.choice`, and `Quot.sound`.
- `MachineComposition.compositionAux` depends on `propext`,
  `Classical.choice`, and `Quot.sound`.

The source tree contains no `sorry`, `admit`, project-defined `axiom`, or
`unsafe` declaration.
