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
| Canonical pair-left machine output | Complete | `MachineAdapters.pairReductionMachine` and `pairReductionAux` expose the finite machine and canonical alphabets; `pairReductionMachine_initList`, `pairReductionMachine_done_step`, and `pairReductionMachine_outputs` prove canonical list output with all work stacks empty and the initial control state restored. `pairReductionMachine_outputs_steps` proves the exact cost `reductionRun.steps + 8 * source.length + 4 * privateOutput.length + 22`, including the final halt step. |
| Function-level pair-left computation | Complete | `MachineAdapters.pairReductionComputable` specializes the canonical machine to `(a, c) ↦ (f a, c)` under `PairEncoding.finEncoding`; `pairReductionComputable_outputs_steps` preserves the exact reduction step count plus the linear input/output overhead. |
| Polynomial-time pair-left computation | Complete | `MachineAdapters.pairReductionComputableInPolyTime` uses the same checked machine and the explicit `pairReductionTimePolynomial`, evaluating to `T(N) + 8 * N + 4 * S(N) + 22`, where `N` is the full tagged input length, `T` is the reduction time polynomial, and `S` is its checked encoded-output-size polynomial. No certificate-length restriction is assumed. |
| Encoded decision language | Complete | `EncodedLanguage` bundles a predicate with the `FinEncoding` that fixes its input-size measure; `EncodedLanguage.PolytimeReducesTo` specializes the checked reduction relation. |
| P | Complete | `EncodedLanguage.PolytimeDecider` specifies both Boolean outcomes and a `TM2ComputableInPolyTime` witness; `EncodedLanguage.InP` is deterministic polynomial-time decidability. |
| NP | Complete | `EncodedLanguage.PolytimeVerifier` separates soundness, bounded completeness, and the checked polynomial-time verifier; `EncodedLanguage.InNP` existentially quantifies the finitely encoded certificate type, with constructor `PolytimeVerifier.toInNP`. |
| P is contained in NP | Complete | `EncodedLanguage.inP_toInNP` uses `PolytimeDecider.toUnitVerifier`, the zero-length `UnitEncoding.finEncoding`, and `MachineAdapters.ignoreUnitCertificate` to reuse the checked decider machine and runtime. |
| P transport along reductions | Complete | `PolytimeDecider.pullback` composes a checked reduction map with the target Boolean decider, preserving both Boolean semantics; `EncodedLanguage.InP.of_reduction` transports deterministic polynomial-time membership backward. |
| NP certificate-bound transport along reductions | Complete | `PolytimeVerifier.pullbackCertificateBound` composes the target certificate polynomial with the reduction machine's checked encoded-output-size polynomial; `pullback_complete` proves that transported completeness certificates satisfy that bound. |
| NP transport along reductions | Complete | `PolytimeVerifier.pullback` composes the checked pair-left machine with the target verifier, transports soundness through reduction correctness, and uses `pullback_complete` for polynomially bounded completeness. `pullback_verify` and `pullback_certificateEncoding` expose the unchanged certificate interface; `EncodedLanguage.InNP.of_reduction` transports verifier-based NP membership backward. |
| NP-hardness and NP-completeness | Complete | `EncodedLanguage.NPHard` universally supplies nonempty checked reductions from encoded NP languages; `EncodedLanguage.NPComplete` pairs hardness with NP membership. `NPHard.of_reduction` transports hardness forward by `PolytimeManyOneReduction.comp`, and `NPComplete.of_reduction` combines that transport with separate target membership. |
| CNF syntax and Boolean evaluation correctness | Complete | `CNF.Literal`, `Clause`, and `Formula` retain all occurrences in lists; `Literal.eval_eq_true`, `Clause.eval_eq_true`, and `Formula.eval_eq_true` prove agreement with independently defined propositional satisfaction. `Formula.satisfiable_iff_exists_eval` characterizes satisfying assignments; empty-formula and empty-clause theorems cover the boundary cases. |
| Semantic SAT and exact k-SAT languages | Complete | `CNF.SAT`, `ExactKSAT`, and `ExactThreeSAT` are predicates over formulas with natural-number variables. `Formula.ExactWidth` counts repeated occurrences; `exactWidth_repeated_triple` proves that three copies of a literal have width three. Exact k-SAT requires positive k, matching the Coq comparison convention. |
| CNF-SAT finite encoding | Complete | `CNF.Literal.ofNat_toNat` checks even/odd polarity packing; `Formula.ofNatLists_toNatLists` and `toNatLists_clause_lengths` preserve nested-list syntax and widths. `Formula.finEncoding` reuses `BinaryNatLists` over `Bool`; `decode_encode` and `encode_injective` establish lossless serialization, and `encode_length` / `finEncoding_encode_length` prove the exact bit measure `encodedSize`. `encodedSAT`, `encodedExactKSAT`, and `encodedExactThreeSAT` bundle the semantic languages with this encoding. |
| Finite SAT certificates and linear bit bound | Complete | `CNF.Formula.eval_congr` restricts evaluation dependence to occurring variables; `assignment_trueVariables` and `eval_trueVariables` prove agreement with the finite list of true occurrences. `Certificate.finEncoding` reuses framed binary natural lists, and `Certificate.verify_sound` proves semantic soundness. `Formula.trueVariables_encode_length_le` bounds certificates by `3 * encodedSize + 1`; `satisfiable_iff_exists_bounded_certificate` gives the bounded finite-witness characterization. Repetitions are retained, and no maximum-variable-index bound is used. |
| Exact 3-SAT is in NP | Pending | A polynomial-time TM2 verifier, including the exact-width check; finite certificates and their linear bit bound are checked separately. |
| At-most-three to exact-three SAT semantics and output size | Complete | `CNF.Clause.normalizeThree` pads one/two-literal clauses, replaces an empty clause by contradictory triples, and retains longer clauses. `Formula.eval_normalizeThree` and `satisfiable_normalizeThree` preserve every assignment's evaluation and satisfiability. `exactWidth_normalizeThree` characterizes exact output width by `AtMostWidth 3` on the input. `atMostThreeToExactThree` packages the semantic reduction, with `normalizeThree_encode_length_le` bounding encoded output by `26 * encodedSize + 1`. The TM2 implementation/runtime and arbitrary-width SAT reduction remain pending. |
| Cook--Levin | Pending | Polynomial reduction from every NP language to SAT. |
| Exact 3-SAT is NP-complete | Pending | A polynomial-time arbitrary-width SAT-to-3-SAT reduction and final composition; short-clause padding semantics and size are checked separately. |

## Reusable encoding and machine library

| Result | Status | Checked declaration or encoding boundary |
|---|---|---|
| Binary natural/list/nested-list encoding | Complete | `BinaryNatLists.finEncoding`, `decode_encode`, and `encode_length`; raw encodings in `RawNatEncoding`. |
| Framing and raw-field conversion | Complete | `MachinePrimitives.framedNatComputableInPolyTime`, `framedNatListComputableInPolyTime`, `unframedNatListsComputableInPolyTime`, and `sourceOrderRawFieldsComputableInPolyTime`. |
| Binary arithmetic | Complete | `MachinePrimitives.binarySuccComputableInPolyTime`, `binaryPredComputableInPolyTime`, `binaryLEComputableInPolyTime`, and `binaryAddComputableInPolyTime`; the latter two use `BinaryNatPair.finEncoding`. |
| Separate-stack binary equality kernel | Complete | `MachinePrimitives.BinaryEquality.computer` is a finite three-stack TM2 machine. `scan_run` and `whole_list` prove exact execution in `max left.length right.length + 1` steps, exhausting both input words, preserving the output suffix, and restoring initial control. `natural_run` specializes to canonical `Computability.encodeNat`; `evalsToInTime` and `natural_evalsToInTime` bound runtime by the sum of supplied bit lengths plus one. The preloaded-count certificate loop is checked in `CertificateMembershipLoop`; serialized input loading and full verifier integration remain pending. |
| Binary equality with query restoration | Complete | `MachinePrimitives.PreservingBinaryEquality.computer` has four Boolean stacks and finite scan/restore control. `scan_run` saves the reversed query; `restore_run` restores its order. `whole_list` preserves the query, consumes the candidate, empties scratch, and pushes equality above the unchanged output suffix in exactly `max q c + q + 2` steps for supplied bit lengths `q` and `c`. `evalsToInTime` bounds this by `2q + c + 2`; `natural_run` and `natural_evalsToInTime` specialize to canonical binary naturals. The preloaded-count certificate loop is checked in `CertificateMembershipLoop`; serialized loading and verifier integration remain pending. |
| Counted-row representation and payload extraction | Complete | `CountedNatRows.rowPayloadFinEncoding`, `rowFields_injective`, and `MachinePrimitives.countedRowPayloadStructuredComputableInPolyTime`; empty rows remain distinct. |
| Ordered extraction of one binary frame | Complete | `MachinePrimitives.FrameExtraction.computer` has five Boolean stacks and finite prefix/payload/restore control. `prefix_run`, `payload_run`, and `restore_run` give exact phase invariants; `whole_frame` extracts `BinaryNatLists.frame bits ++ suffix` in exactly `3 * bits.length + 3` steps, preserving the query, input suffix, and candidate suffix, emptying both work stacks, and resetting control. `evalsToInTime` bounds runtime by twice the consumed frame length plus one; `natural_run` and `natural_evalsToInTime` load the canonical unframed natural encoding. The contract assumes a complete frame; `CertificateStep` integrates comparison and decrement, and `CertificateMembershipLoop` supplies the preloaded-count loop; header integration and the verifier remain pending. |
| Query-preserving comparison of one framed candidate | Complete | `MachinePrimitives.FrameComparison.computer` combines extraction and equality on six Boolean stacks. `extract_stepAux`, `compare_stepAux`, `extract_run`, and `compare_run` preserve exact component costs. `whole_frame` consumes one complete frame and emits equality while preserving the query, unread input, and output suffix, emptying candidate/scratch/count, and resetting control in exactly `3c + max(q, c) + q + 5` steps. `evalsToInTime` bounds this by `2q + 2f + 3`, for query/payload/frame bit lengths `q`/`c`/`f`; `natural_run` and `natural_evalsToInTime` specialize to canonical naturals. `CertificateStep` now integrates comparison and count decrement; the preloaded-count loop is checked in `CertificateMembershipLoop`, while header integration and the verifier remain pending. |
| Retained certificate-list count and zero test | Complete | `MachinePrimitives.CertificateCount.computer` lifts extraction to seven Boolean stacks, directing the header to a dedicated `remaining` stack. `extract_stepAux` and `extract_run` preserve the private candidate/output stacks and exact costs. `whole_frame` loads the header; `check_step` peeks without consuming it; `checked_frame` and `natural_run` reach the correct zero/nonzero continuation in exactly `3b + 4` steps for binary count length `b`. `list_run` preserves all framed elements and trailing input. `natural_evalsToInTime` gives bound `2h + 2` in framed-header bits; `list_evalsToInTime` gives `2N + 2` in full certificate bits. Work stacks empty and control resets. The continuation halt is not counted; canonical complete headers are assumed. The header-to-traversal dispatcher and malformed-input rejection remain pending. |
| Framed comparison with retained certificate count | Complete | `MachinePrimitives.CertificateComparison.computer` reuses the seven-stack `CertificateCount.Stack` layout. `compare_stepAux` and `compare_run` preserve arbitrary `remaining` contents with unchanged exact cost. `whole_frame` consumes one frame, restores the query, preserves the count and input/output suffixes, and empties candidate/scratch/count in exactly `3c + max(q, c) + q + 5` steps. `evalsToInTime` gives bound `2q + 2f + 3` in query/payload/frame bit lengths; `natural_run` and `natural_evalsToInTime` specialize to canonical naturals. `list_head_run` preserves every later certificate frame and the original count. Execution ends at a live continuation before its halt. `CertificateStep` connects comparison to in-place decrement and `CertificateMembershipStep` adds Boolean accumulation; the preloaded-count loop is checked in `CertificateMembershipLoop`; header dispatch remains pending. |
| Certificate-count predecessor into a separate stack | Complete | `MachinePrimitives.CertificatePredecessor.computer` reuses the seven-stack certificate layout. `pred_stepAux` and `pred_run` preserve arbitrary input/query/count/output contents with unchanged component step count. `whole_word` consumes `remaining`, empties scratch, and writes `binaryPredBits` onto `candidate`; `evalsToInTime` bounds the run by `2b + 3` for count bit length `b`. `natural_evalsToInTime` gives saturated predecessor including zero and one; `list_tail_evalsToInTime` produces the tail length after one element, preserving all unread frames. The final continuation halt is excluded. `CertificateDecrement` now connects this execution to ordered transfer for in-place decrement; header-to-traversal integration remains pending. |
| Ordered certificate-count result transfer | Complete | `MachinePrimitives.CertificateCountTransfer.computer` reuses the seven-stack layout. `reverse_run`, `restore_run`, and `whole_word` transfer candidate through scratch onto remaining in original order in exactly `2p + 2` steps for `p` candidate bits, preserving arbitrary input/query/count/output contents and the remaining-stack suffix. Candidate and scratch finish empty and control resets at a live continuation before its halt. `predecessor_evalsToInTime` and `natural_predecessor_evalsToInTime` bound transfer of an already computed predecessor by `2b + 2` in original count bit length `b`, using the now-public `MachinePrimitives.binaryPredBits_length_le`. `CertificateDecrement` now connects predecessor execution and transfer under one dispatcher; header-to-traversal integration remains pending. |
| In-place retained certificate-count decrement | Complete | `MachinePrimitives.CertificateDecrement.computer` combines predecessor and ordered transfer under finite control on the same seven stacks. `pred_stepAux` / `pred_run` and `transfer_stepAux` / `transfer_run` preserve component costs; `predecessor_run` enters transfer in the predecessor's final step. `whole_word` returns `binaryPredBits` to `remaining` in the exact predecessor witness's steps plus `2p + 2` for result length `p`. `evalsToInTime` bounds the total by `4b + 5` for original count length `b`. Input/query/count/output survive unchanged; candidate/scratch empty and control resets at a live continuation before its halt. `natural_evalsToInTime` covers saturated predecessor including zero and one; `list_tail_evalsToInTime` retains the tail count and all unread frames, including repetitions. `CertificateStep` supplies comparison/decrement integration and `CertificateMembershipStep` adds Boolean accumulation; the preloaded-count loop is checked in `CertificateMembershipLoop`; header dispatch remains pending. |
| Certificate comparison and in-place count decrement | Complete | `MachinePrimitives.CertificateStep.computer` combines framed comparison and decrement under finite control on the same seven stacks. `compare_stepAux` / `compare_run` and `decrement_stepAux` / `decrement_run` preserve exact component costs; `comparison_run` enters decrement in the final comparison step. `whole_frame` proves exact summed execution; `evalsToInTime` bounds the total by `2q + 2f + 4b + 8` for query, consumed-frame, and original count bit lengths. Equality is pushed onto output, query and unread suffixes survive, and all three work stacks finish empty. `natural_evalsToInTime` handles canonical naturals and saturated decrement; `list_head_evalsToInTime` preserves all later frames, including repetitions, and restores the exact tail count. The final continuation halt is excluded. `CertificateMembershipStep` now adds Boolean accumulation; header dispatch, malformed-input handling, and full verifier integration remain pending. |
| Certificate membership accumulation step | Complete | `MachinePrimitives.CertificateMembershipStep.computer` connects comparison/decrement to a Boolean output accumulator on the same seven stacks. `accumulate_stepAux` and `accumulate_step` replace the leading equality and accumulator bits by their OR in one TM2 step, preserving all other stacks and the output suffix. `lift_stepAux` / `lift_run` preserve exact component costs while replacing a reached halt with accumulation. `comparison_decrement_run` and `whole_frame` prove the connected execution; `evalsToInTime` bounds it by `2q + 2f + 4b + 9` for query/frame/original-count bit lengths. `natural_evalsToInTime` handles canonical naturals and saturated decrement; `list_head_evalsToInTime` restores the exact tail count and retains every later frame, including duplicates. `accumulated_eq_true_iff` identifies the output as equality or a prior match. Work stacks empty and control resets at a live continuation; its halt is excluded. `CertificateMembershipLoop` now connects count-controlled repetition; header dispatch, malformed-input rejection, and the full verifier remain pending. |
| Count-controlled certificate membership traversal | Complete | `MachinePrimitives.CertificateMembershipLoop.computer` repeats the membership step on seven stacks under finite control. `lift_stepAux` / `lift_run` preserve component costs; `check_step` peeks without consuming count, and `return_step` counts the jump back. `entry_run` restores the exact tail count; `whole_list` consumes the complete canonical body, including repetitions, returning membership OR the prior accumulator while preserving the query and arbitrary input/output suffixes and emptying count/work stacks. `runSteps` records exact costs; `runSteps_le` / `evalsToInTime` give `n * (2q + 4b + 11) + 2F + 1` for entry count, query bits, initial count bits, and framed body bits. `count_bits_mono` bounds all tail counts; `runSteps_le_bit_bound` gives `F * (2q + 4F + 11) + 2F + 1`. `result_eq_true_iff` gives separate Boolean semantics. The canonical count, query, and accumulator are preloaded, and the final continuation halt is excluded. Header dispatch, accumulator initialization, malformed-input rejection, and the full verifier remain pending. |
| Boolean aggregation | Complete | `MachinePrimitives.allFalseComputableInPolyTime`, linear in the complete Boolean stream length. |
| Generic pair exchange and right-component computation | Complete | `PairExchange.outputsInTime`, `PairExchange.computableInPolyTime`, and `MachineAdapters.pairRightComputableInPolyTime`; finite alphabets can differ or be empty, with exchange bound `4s+6`. |

The bounded number-theory extraction is also checked:
`BoundedPrime.selectPrimeAbove_prime`, `lt_selectPrimeAbove`, and
`selectPrimeAbove_lt_two_mul` give the semantic prime contract, including the
zero/one conventions. `MachinePrimitives.bertrandCandidatesComputableInPolyTime`,
`unaryDvdComputableInPolyTime`, `trialDivisionPairsComputableInPolyTime`,
`unaryCandidatePrimeComputableInPolyTime`, `primeSelectorComputableInPolyTime`,
and `selectedPrimeComputableInPolyTime` provide actual finite-machine witnesses.
The final selection bound is `1000(q+1)^6` for **unary** input/output naturals.
These number-theory components do not complete the SAT verifier or Cook--Levin.

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
- `MachineAdapters.pairReductionMachine`, `pairReductionAux`,
  `pairReductionMachine_initList`, `pairReductionMachine_done_step`,
  `pairReductionMachine_outputs`, and `pairReductionMachine_outputs_steps`
  depend on `propext`, `Classical.choice`, and `Quot.sound`.
- `MachineAdapters.pairReductionComputable`,
  `pairReductionComputable_outputs_steps`, `pairReductionTimePolynomial`,
  `pairReductionTimePolynomial_eval`, and `pairReductionComputableInPolyTime`
  depend on `propext`, `Classical.choice`, and `Quot.sound`.
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
- `EncodedLanguage.PolytimeVerifier.pullback`, `pullback_verify`,
  `pullback_certificateEncoding`, and `EncodedLanguage.InNP.of_reduction`
  depend on `propext`, `Classical.choice`, and `Quot.sound`.
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
- `CNF.Literal.eval_eq_true` depends on `propext`; `Clause.eval_eq_true`,
  `Formula.eval_eq_true`, `Formula.satisfiable_iff_exists_eval`,
  `Formula.satisfiable_nil`, `Formula.not_satisfiable_of_nil_mem`, and
  `Formula.exactWidth_repeated_triple` depend on `propext` and `Quot.sound`.
  The semantic language definitions `CNF.SAT` and `CNF.ExactKSAT` depend on
  no axioms. These results do not supply a finite certificate encoding or a
  polynomial-time machine for evaluating formulas.
- The fourteen `CNFEncoding` audits cover literal packing, nested-list
  round-trip and clause lengths, the formula decoder, finite encoding,
  injectivity and exact encoded length, and the encoded language interfaces.
  `Formula.toNatLists_clause_lengths` and `Formula.encode_length` use only
  `propext` and `Quot.sound`; the other twelve use only `propext`,
  `Classical.choice`, and `Quot.sound`. These encoding results do not supply
  a verifier machine or its runtime bound.
- The fourteen new finite-certificate and supporting binary-size audits pass.
  `BinaryNatLists.encodeNat_length_eq_size`, `natWireSize_mono`,
  `Formula.vars_payloadSize_le_encodedSize`, `vars_length_le_encodedSize`,
  `trueVariables_encode_length_le`, and
  `satisfiable_iff_exists_bounded_certificate` use only `propext`,
  `Classical.choice`, and `Quot.sound`. `Literal.eval_congr` and
  `Formula.assignment_trueVariables` use only `propext`; the other six use
  only `propext` and `Quot.sound`. The full build passed 2,197 jobs on
  2026-09-11. These results establish certificate semantics and bit bounds;
  they do not supply the polynomial-time TM2 verifier.

- The fifteen `CNFNormalization` audits pass. Clause/formula
  `eval_normalizeThree` use only `propext`; `Formula.encodedSize_eq` and
  `satisfiable_normalizeThree` use only `propext` and `Quot.sound`; the other
  eleven use only `propext`, `Classical.choice`, and `Quot.sound`.
  Full `lake build` passed 2,198 jobs on 2026-09-12. These results establish
  short-clause normalization semantics and a linear encoded-output bound,
  with no TM2 runtime or arbitrary-width SAT reduction claimed.

- The seven `BinaryEqualityMachine` audits pass. `encodeNat_eq_iff` uses
  only `propext` and `Quot.sound`; the other six use only `propext`,
  `Classical.choice`, and `Quot.sound`. Full `lake build` passed 2,199 jobs
  on 2026-09-13. The 44-file source/config scan found only the existing
  explanatory `proof_wanted` comment. Equality starts with two independently
  supplied Boolean stacks; no serialized-input adapter or SAT verifier is
  asserted by these kernel results.

- The seven `PreservingBinaryEqualityMachine` audits pass with only
  `propext`, `Classical.choice`, and `Quot.sound`. Full `lake build` passed
  2,200 jobs on 2026-09-14; all 229 reported axiom lists contain only these
  standard axioms. The 45-file source/config scan found only the existing
  explanatory `proof_wanted` comment. These results include the scan,
  restoration, complete word/natural execution, and linear bit bounds;
  serialized certificate traversal and a polynomial-time verifier remain
  separate obligations.

- The eight `FrameExtractionMachine` audits pass with only `propext`,
  `Classical.choice`, and `Quot.sound`. Full `lake build` passed 2,201 jobs
  on 2026-09-15; all 237 reported axiom lists contain only these standard
  axioms, with three additional axiom-free reports. The 46-file source/config
  scan found only the existing explanatory `proof_wanted` comment. These
  results establish exact ordered extraction and a linear bound for a
  complete frame, including the empty payload. Outer list counting,
  certificate traversal, and the full verifier remain separate obligations.

- The nine `FrameComparisonMachine` audits pass with only `propext`,
  `Classical.choice`, and `Quot.sound`. Full `lake build` passed 2,202 jobs
  on 2026-09-16; all 246 reported axiom lists contain only these standard
  axioms, with three additional axiom-free reports. The 47-file source/config
  scan found only the existing explanatory `proof_wanted` comment. Both
  component simulations and exact/linear complete-frame comparison costs
  are checked. The query is preloaded; outer list counting, certificate
  traversal, and the full verifier remain separate obligations.

- The eleven `CertificateCountMachine` audits pass with only `propext`,
  `Classical.choice`, and `Quot.sound`; the canonical zero characterization
  uses only `propext` and `Quot.sound`. Full `lake build` passed 2,203 jobs
  on 2026-09-17. All 257 reported axiom lists use only these standard axioms,
  with three additional axiom-free reports. The 48-file source/config scan
  found only the existing explanatory `proof_wanted` comment. The checked
  header loader retains the binary count and unread list body and selects
  the zero/nonzero continuation with exact and linear bounds. It assumes
  canonical complete headers; decrement, traversal, and the full verifier
  remain separate obligations.

- The eight `CertificateComparisonMachine` audits pass with only `propext`,
  `Classical.choice`, and `Quot.sound`. Full `lake build` passed 2,204 jobs
  on 2026-09-18; all 265 reported axiom lists use only these standard axioms,
  with three additional axiom-free reports. The 49-file source/config scan
  found only the existing explanatory `proof_wanted` comment. Exact finite
  runs preserve arbitrary remaining-count contents, with the same comparison
  runtime and a checked nonempty certificate-body interface. Execution ends
  at a continuation before its halt; decrement, membership accumulation,
  the traversal dispatcher, and the full SAT verifier remain pending.

- The seven `CertificatePredecessorMachine` audits pass with only `propext`,
  `Classical.choice`, and `Quot.sound`. Full `lake build` passed 2,205 jobs
  on 2026-09-19; all 272 reported axiom lists use only these standard axioms,
  with three additional axiom-free reports. The 50-file source/config scan
  found only the existing explanatory `proof_wanted` comment. The predecessor
  preserves four unrelated stacks with unchanged component step count and
  bound `2b + 3`; the canonical-natural and certificate-tail interfaces are
  checked. The result is on `candidate`, so ordered transfer to `remaining`
  and a complete in-place decrement remain separate obligations.

- The eight ordered-transfer and predecessor-length audits pass with only
  `propext`, `Classical.choice`, and `Quot.sound`. Full `lake build` passed
  2,206 jobs on 2026-09-20; all 280 reported axiom lists use only these
  standard axioms, with three further axiom-free reports. The 51-file
  source/config scan found only the existing explanatory `proof_wanted`
  comment. `CertificateCountTransfer.whole_word` proves exact ordered
  transfer in `2p + 2` steps; the predecessor-result interfaces bound this
  by `2b + 2` in the original count's bit length. Predecessor execution
  and transfer still require a shared dispatcher before in-place decrement
  or complete certificate traversal can be claimed.

- The ten `CertificateDecrementMachine` audits pass with only `propext`,
  `Classical.choice`, and `Quot.sound`. Full `lake build` passed 2,207 jobs
  on 2026-09-21; all 290 reported axiom lists use only these standard
  axioms, with three further axiom-free reports. The 52-file source/config
  scan found only the existing explanatory `proof_wanted` comment.
  `whole_word` connects predecessor and ordered transfer with exact summed
  cost, and `evalsToInTime` bounds in-place decrement by `4b + 5` for
  original count bit length `b`. The natural and certificate-tail interfaces
  retain query, unread frames, and prior output. Comparison/decrement
  integration, membership accumulation, header dispatch, full traversal,
  and the SAT verifier remain separate obligations.

- The ten `CertificateStepMachine` audits pass with only `propext`,
  `Classical.choice`, and `Quot.sound`. Full `lake build` passed 2,208 jobs
  on 2026-09-22; all 300 reported axiom lists use only these standard
  axioms, with three further axiom-free reports. The 53-file source/config
  scan found only the existing explanatory `proof_wanted` comment.
  `whole_frame` connects framed comparison and in-place decrement with
  exact summed cost; `evalsToInTime` bounds it by `2q + 2f + 4b + 8`.
  `list_head_evalsToInTime` consumes one certificate entry, retains the
  equality result and query, and restores the tail count while preserving
  all later frames. The final continuation halt is excluded. Membership
  accumulation, header dispatch, malformed-input handling, full traversal,
  and the SAT verifier remain separate obligations.

- The eleven `CertificateMembershipStepMachine` audits pass. The semantic
  `accumulated_eq_true_iff` uses only `propext`; the ten machine/execution
  declarations use only `propext`, `Classical.choice`, and `Quot.sound`.
  Full `lake build` passed 2,209 jobs on 2026-09-23; all 311 reported axiom
  lists contain only those standard axioms, with three further axiom-free
  reports. The 54-file source/config scan found only the existing explanatory
  `proof_wanted` comment. `accumulate_step` combines the two leading output
  bits in one step, and `whole_frame` connects it to comparison/decrement
  with exact cost plus one. `evalsToInTime` bounds the total by
  `2q + 2f + 4b + 9`; the natural and certificate-head interfaces preserve
  prior matches, query, unread frames, and the exact tail count. Execution
  ends at a live continuation before its halt. Header dispatch, repeated
  membership steps, malformed-input rejection, and the verifier remain pending.

- The fifteen `CertificateMembershipLoopMachine` audits pass. The Boolean
  lemmas `membership_cons` and `result_eq_true_iff` use only `propext` and
  `Quot.sound`; the other thirteen declarations use only `propext`,
  `Classical.choice`, and `Quot.sound`. Full `lake build` passed 2,210 jobs
  on 2026-09-24; all 326 reported axiom lists contain only these standard
  axioms, with three further axiom-free reports. The 55-file Lean source/config
  scan found only the existing explanatory `proof_wanted` comment. `whole_list`
  checks complete repeated execution with exact count, membership semantics,
  query/suffix preservation, and empty final work stacks. `runSteps_le_bit_bound`
  gives the polynomial `F * (2q + 4F + 11) + 2F + 1` in query/body bits.
  Canonical count, query, and accumulator are preloaded; header dispatch,
  accumulator initialization, malformed-input rejection, and the full verifier
  remain separate obligations. The final continuation halt is excluded.

The source tree contains no `sorry`, `admit`, project-defined `axiom`, or
`unsafe` declaration.
