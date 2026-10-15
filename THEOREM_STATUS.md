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
| P is contained in NP | Complete | `EncodedLanguage.inP_toInNP` uses `PolytimeDecider.toVerifier`: the decider runs on the input component through the checked pair-left adapter and `MachinePrimitives.BoolPairFirst.computableInPolyTime` projects the Boolean result past the Boolean-string certificate in `bits.length + 2` steps. NP now uses Boolean-string certificates (`EncodedLanguage.certificateEncoding`) with verifier machines total on all paired inputs, as the Cook--Levin tableau requires; earlier text referring to `toUnitVerifier` and `ignoreUnitCertificate` is superseded. It previously reuse the checked decider machine and runtime. |
| P transport along reductions | Complete | `PolytimeDecider.pullback` composes a checked reduction map with the target Boolean decider, preserving both Boolean semantics; `EncodedLanguage.InP.of_reduction` transports deterministic polynomial-time membership backward. |
| NP certificate-bound transport along reductions | Complete | `PolytimeVerifier.pullbackCertificateBound` composes the target certificate polynomial with the reduction machine's checked encoded-output-size polynomial; `pullback_complete` proves that transported completeness certificates satisfy that bound. |
| NP transport along reductions | Complete | `PolytimeVerifier.pullback` composes the checked pair-left machine with the target verifier, transports soundness through reduction correctness, and uses `pullback_complete` for polynomially bounded completeness. `pullback_verify` and `pullback_certificateEncoding` expose the unchanged certificate interface; `EncodedLanguage.InNP.of_reduction` transports verifier-based NP membership backward. |
| NP-hardness and NP-completeness | Complete | `EncodedLanguage.NPHard` universally supplies nonempty checked reductions from encoded NP languages; `EncodedLanguage.NPComplete` pairs hardness with NP membership. `NPHard.of_reduction` transports hardness forward by `PolytimeManyOneReduction.comp`, and `NPComplete.of_reduction` combines that transport with separate target membership. |
| CNF syntax and Boolean evaluation correctness | Complete | `CNF.Literal`, `Clause`, and `Formula` retain all occurrences in lists; `Literal.eval_eq_true`, `Clause.eval_eq_true`, and `Formula.eval_eq_true` prove agreement with independently defined propositional satisfaction. `Formula.satisfiable_iff_exists_eval` characterizes satisfying assignments; empty-formula and empty-clause theorems cover the boundary cases. |
| Semantic SAT and exact k-SAT languages | Complete | `CNF.SAT`, `ExactKSAT`, and `ExactThreeSAT` are predicates over formulas with natural-number variables. `Formula.ExactWidth` counts repeated occurrences; `exactWidth_repeated_triple` proves that three copies of a literal have width three. Exact k-SAT requires positive k, matching the Coq comparison convention. |
| CNF-SAT finite encoding | Complete | `CNF.Literal.ofNat_toNat` checks even/odd polarity packing; `Formula.ofNatLists_toNatLists` and `toNatLists_clause_lengths` preserve nested-list syntax and widths. `Formula.finEncoding` reuses `BinaryNatLists` over `Bool`; `decode_encode` and `encode_injective` establish lossless serialization, and `encode_length` / `finEncoding_encode_length` prove the exact bit measure `encodedSize`. `encodedSAT`, `encodedExactKSAT`, and `encodedExactThreeSAT` bundle the semantic languages with this encoding. |
| Finite SAT certificates and linear bit bound | Complete | `CNF.Formula.eval_congr` restricts evaluation dependence to occurring variables; `assignment_trueVariables` and `eval_trueVariables` prove agreement with the finite list of true occurrences. `Certificate.finEncoding` reuses framed binary natural lists, and `Certificate.verify_sound` proves semantic soundness. `Formula.trueVariables_encode_length_le` bounds certificates by `3 * encodedSize + 1`; `satisfiable_iff_exists_bounded_certificate` gives the bounded finite-witness characterization. Repetitions are retained, and no maximum-variable-index bound is used. |
| Max-Cut is in NP and NP-complete | Complete | Semantics: `MaxCutVerify.verifyMC` reads two claimed colour bits per edge (missing bits `false`) and accepts when the claims are consistent (`consistent` on claims encoded as literals by `occLit`) and the number of edges with differing claimed colours reaches the threshold; `verifyMC_sound` and `verifyMC_complete` characterize `MaxCutLang` with `2 * |E|` certificate bits. Machine: the binary threshold is converted to unary with saturation at `2|E| + 1` against a unary budget stack (`readLenSat_exits`, `satFold_eq`), so a large binary threshold costs only polynomial time; endpoint codes become colour-tagged entries (`readKeepC_exits`), cut edges are counted in unary, and the shared pairwise check verifies consistency. `vmainMC_exits` runs within `3000 * (n + 1) ^ 3` steps; `polytimeVerifier`, `encodedMaxCut_inNP`, and `encodedMaxCut_NPComplete` package it. |
| Max-Cut is NP-hard | Complete | Language: `MaxCut.MaxCutLang` on edge lists over natural-number vertices (repeated edges and self-loops retained) with a threshold; instances are encoded as CNF formulas (`graphFormula`: one two-literal clause per edge, then `[K]`) under the unary-index (`unaryEncoding`) and binary (`binaryEncoding`) CNF encodings, with checked decoders. Semantics: `MaxCut.gadget` gives each clause a block of fresh odd vertices (occurrence vertices linked to the variable vertex `2v`, two triangles joined by a forcing edge, a pendant edge) with threshold `|E| - 2m`; `sat_iff_maxCut_gadget` proves satisfiability equals reaching the threshold for exact-width-three formulas. Machine: `MaxCutJob.render_job` and `MaxCutMachine.mcMachineR_exits` stream the gadget through the generator's input loop and interpreter within `10⁶ (n + 1)²` steps (`cost_le`). Hardness transfer: `satReduction` composes the chain reduction with the gadget (`MachineComposition.compositionComputableInPolyTime`), giving `encodedUnaryMaxCut_NPHard`; `binaryReduction` re-encodes with the CNF converter, giving `encodedMaxCut_NPHard`. |
| CNF-SAT is in NP and NP-complete | Complete | Semantics: `SatVerify.verifySat` selects one literal per clause by unary certificate bits (`false` skips, `true` selects) and accepts when every clause selects and no two selections are complementary; `verifySat_sound` and `verifySat_complete` characterize `SAT` with certificates of at most twice the binary input length. Machine: per clause the framed binary length is converted to unary by Horner's scheme (`readLen_exits`), then the codes are walked with a selection marker (`select_exits`, `skipRest_exits`); `clauseLoopSat_exits` matches `satWalk`, and the pairwise check is shared with the exact 3-SAT verifier. `vmainSat_exits` runs within `2000 * (n + 1) ^ 3` steps; `polytimeVerifier`, `encodedSAT_inNP`, and `encodedSAT_NPComplete` (with `BinaryConvert.encodedSAT_NPHard`) package it. |
| Exact 3-SAT is in NP | Complete | Semantics: `ExactThreeVerify.verify` reads two certificate bits per clause selecting a literal to make true (missing bits read as `false`) and accepts exactly when every clause has width three and no two selected literals are complementary; `verify_sound` and `verify_complete` characterize `ExactThreeSAT`, with certificates of `2 * F.length` bits, at most twice the binary input length (`witness_length_le`). Machine: `vmain_exits` is the bounded TM2 run on the paired binary input (input split, certificate padding, width check against the frame `11011`, normalized literal entries, pairwise lockstep comparison counting conflicts) to the single output bit `verify (F, w)`; runtime `2000 * (n + 1) ^ 3` (`vCost`). `computableInPolyTime`, `polytimeVerifier`, and `encodedExactThreeSAT_inNP` package it. |
| At-most-three to exact-three SAT semantics and output size | Complete | `CNF.Clause.normalizeThree` pads one/two-literal clauses, replaces an empty clause by contradictory triples, and retains longer clauses. `Formula.eval_normalizeThree` and `satisfiable_normalizeThree` preserve every assignment's evaluation and satisfiability. `exactWidth_normalizeThree` characterizes exact output width by `AtMostWidth 3` on the input. `atMostThreeToExactThree` packages the semantic reduction, with `normalizeThree_encode_length_le` bounding encoded output by `26 * encodedSize + 1`. The TM2 implementation/runtime and arbitrary-width SAT reduction remain pending. |
| Cook--Levin semantic reduction and tableau | Complete | `CookLevin.reduction` is a checked `ManyOneReduction` from any `InNP` language (Boolean-string certificates, `EncodedLanguage.PolytimeVerifier`) to `CNF.SAT`; `CookLevin.accepts_iff_sat` and `CookLevin.tableau_satisfiable_iff` prove correctness. The tableau is built generically: `CNF.Constraint.relationCNF` writes any finite relation as CNF (`eval_relationCNF`), `registerCNF` lifts it to bit-register values, `Tableau.LocalSystem.satisfiable_iff` is the generic fixed-horizon tableau theorem for register-local systems, and `MachineTableau.Params.localSystem` instantiates it for any bundled TM2 machine using `MachineLocality.stepAux_append` (one statement touches only a depth-bounded stack prefix), the finite `symbols` lists, and `MachinePaddedRun` (padded runs versus mathlib's exact runs, with unique halting time). The machine computing the tableau is the row below. |
| Cook--Levin generator machine and unary SAT NP-hardness | Complete | Computational model: mathlib `FinTM2` with `TM2ComputableInPolyTime`; input size is the length of the source encoding. The tableau is written in the unary-index CNF encoding `CNF.Unary.finEncoding` (`decode_encode`). The generator is one routine over the stack family `TableauStacks.GStack` built with the exact-step routine combinators of `Routines` (`seq_exits`, `loop_exits`, `dispatch_exits`, `toMachine_outputsInTime`): `parameterStage_exits` materializes the input length, the certificate bound and the horizon by Horner evaluation in unary (`evalPoly_exits`, `hornerFold_coeffList`); `Instance.emitter_exits` pushes the reversed skeleton job (`Instance.render_skeleton`: the job renders to `encode tableau`) chunk by chunk from the finitely many constant cell templates (`range_P_map_cellTrans`, `range_P_map_initCellDesc`, `range_P_map_finalCellDesc`); `interpret_exits` renders the job; `generator_exits` chains these with the cleanup drains into an exact run from the input alone to the encoded tableau alone in `generatorCost` steps. `Instance.emitter_template` shows the emitter depends only on the verifier machine, so `CookLevin.machine` is one machine for all inputs (`machine_outputsInTime`). Runtime: `Instance.generatorCost_le` bounds the cost by `K * sizeParam ^ 4`, where `sizeParam` is the value of the polynomial `sizePoly` in the input length built from the verifier's certificate bound and time polynomial (register bounds `prefixLE_skeleton`, `interpSteps_skeleton_le`; size bounds `skeleton_length_le`); `CookLevin.cost_le` and `computableInPolyTime` package the machine with `timePoly`. Hardness transfer: `CookLevin.polytimeReduction` is the checked reduction and `CookLevin.encodedUnarySAT_NPHard` proves `encodedUnarySAT.NPHard`. Axioms: `propext`, `Classical.choice`, `Quot.sound` only. |
| SAT to exact 3-SAT semantics | Complete | `CNF.Formula.split` renames variables to even numbers and splits every clause with fresh odd variables (`splitClause`); `splitClause_sound`, `splitClause_complete`, and `Formula.satisfiable_split` prove satisfiability is preserved, `Formula.atMostWidth_split` bounds every output clause by width three, and `Formula.toExactThree` pads with `normalizeThree`. `sat_iff_exactThreeSAT_toExactThree` and `satToExactThree` package the semantic reduction `SAT ≤ ExactThreeSAT`. The encoded-size bound and TM2 runtime remain separate. |
| Unary exact 3-SAT NP-hardness | Complete | Semantics: `CNF.Chain.chainThree` doubles original variables and replaces each clause `l₁ ∨ … ∨ lⱼ` by a chain over fresh odd variables `yₖ` (`¬y₀³`, `y₀ ∨ ¬y₁ ∨ y₀`, `lᵢ ∨ ¬yᵢ₊₁ ∨ yᵢ`, `yⱼ₊₁³`) plus a satisfiable tail; `exactWidth_chainThree` and `satisfiable_chainThree` prove exact width three (repetitions counted) and satisfiability preservation, including empty clauses. Encoding: `ChainJob.render_job` shows the per-symbol interpreter job of `encode F` renders to `encode (chainThree F)`. Machine: `ChainMachine.splitter_exits` is the exact TM2 run (input loop, interpreter, cleanup) from the unary input alone to the unary output alone; runtime `cost_le` bounds it by `10000 * (n + 1) ^ 2` in the input length, giving `computableInPolyTime`. Hardness transfer: `ChainMachine.reduction` and `encodedUnaryExactThreeSAT_NPHard` (from `CookLevin.encodedUnarySAT_NPHard` by `NPHard.of_reduction`). |
| Binary SAT and exact 3-SAT NP-hardness | Complete | Computational model: `FinTM2`, input size the length of the unary-index encoding. `BinaryConvert.conv_exits` is a bounded run of one converter routine from the unary encoding alone to `CNF.Formula.encode F` (`Formula.finEncoding`) alone: it counts the clauses (`countLoop_exits`), emits framed binary naturals by unary halving (`emitNat_exits`, digits checked against mathlib by `bitsOf_eq`), and per clause emits the framed literal count and each code `2v` / `2v + 1` (`clauseLoop_exits`, `litLoop_exits`). Runtime: `convBound_le` bounds it by `10000 * (n + 1) ^ 3`; output size is bounded by `encode_length_le`. `computableInPolyTime` packages the identity re-encoding, and `encodedSAT_NPHard` and `encodedExactThreeSAT_NPHard` follow from the unary results by `NPHard.of_reduction`. |
| Exact 3-SAT is NP-complete | Complete | `ExactThreeVerify.encodedExactThreeSAT_NPComplete` combines `BinaryConvert.encodedExactThreeSAT_NPHard` (Cook--Levin, the chain reduction, and unary-to-binary re-encoding) with `encodedExactThreeSAT_inNP`. |

## Reusable encoding and machine library

| Result | Status | Checked declaration or encoding boundary |
|---|---|---|
| Binary natural/list/nested-list encoding | Complete | `BinaryNatLists.finEncoding`, `decode_encode`, and `encode_length`; raw encodings in `RawNatEncoding`. |
| Framing and raw-field conversion | Complete | `MachinePrimitives.framedNatComputableInPolyTime`, `framedNatListComputableInPolyTime`, `unframedNatListsComputableInPolyTime`, and `sourceOrderRawFieldsComputableInPolyTime`. |
| Binary arithmetic | Complete | `MachinePrimitives.binarySuccComputableInPolyTime`, `binaryPredComputableInPolyTime`, `binaryLEComputableInPolyTime`, and `binaryAddComputableInPolyTime`; the latter two use `BinaryNatPair.finEncoding`. |
| Separate-stack binary equality kernel | Complete | `MachinePrimitives.BinaryEquality.computer` is a finite three-stack TM2 machine. `scan_run` and `whole_list` prove exact execution in `max left.length right.length + 1` steps, exhausting both input words, preserving the output suffix, and restoring initial control. `natural_run` specializes to canonical `Computability.encodeNat`; `evalsToInTime` and `natural_evalsToInTime` bound runtime by the sum of supplied bit lengths plus one. Complete encoded-certificate traversal is checked in `CertificateMembership`; serialized query loading is checked in `SerializedMembership`; full verifier integration remains pending. |
| Binary equality with query restoration | Complete | `MachinePrimitives.PreservingBinaryEquality.computer` has four Boolean stacks and finite scan/restore control. `scan_run` saves the reversed query; `restore_run` restores its order. `whole_list` preserves the query, consumes the candidate, empties scratch, and pushes equality above the unchanged output suffix in exactly `max q c + q + 2` steps for supplied bit lengths `q` and `c`. `evalsToInTime` bounds this by `2q + c + 2`; `natural_run` and `natural_evalsToInTime` specialize to canonical binary naturals. Complete encoded-certificate traversal is checked in `CertificateMembership`; serialized query loading is checked in `SerializedMembership`; verifier integration remains pending. |
| Counted-row representation and payload extraction | Complete | `CountedNatRows.rowPayloadFinEncoding`, `rowFields_injective`, and `MachinePrimitives.countedRowPayloadStructuredComputableInPolyTime`; empty rows remain distinct. |
| Ordered extraction of one binary frame | Complete | `MachinePrimitives.FrameExtraction.computer` has five Boolean stacks and finite prefix/payload/restore control. `prefix_run`, `payload_run`, and `restore_run` give exact phase invariants; `whole_frame` extracts `BinaryNatLists.frame bits ++ suffix` in exactly `3 * bits.length + 3` steps, preserving the query, input suffix, and candidate suffix, emptying both work stacks, and resetting control. `evalsToInTime` bounds runtime by twice the consumed frame length plus one; `natural_run` and `natural_evalsToInTime` load the canonical unframed natural encoding. The contract assumes a complete frame; `CertificateStep` integrates comparison and decrement, and `CertificateMembershipLoop` supplies the preloaded-count loop; header integration is checked in `CertificateMembership`, and serialized query loading in `SerializedMembership`; the verifier remains pending. |
| Query-preserving comparison of one framed candidate | Complete | `MachinePrimitives.FrameComparison.computer` combines extraction and equality on six Boolean stacks. `extract_stepAux`, `compare_stepAux`, `extract_run`, and `compare_run` preserve exact component costs. `whole_frame` consumes one complete frame and emits equality while preserving the query, unread input, and output suffix, emptying candidate/scratch/count, and resetting control in exactly `3c + max(q, c) + q + 5` steps. `evalsToInTime` bounds this by `2q + 2f + 3`, for query/payload/frame bit lengths `q`/`c`/`f`; `natural_run` and `natural_evalsToInTime` specialize to canonical naturals. `CertificateStep` now integrates comparison and count decrement; the preloaded-count loop is checked in `CertificateMembershipLoop` and header integration in `CertificateMembership`; serialized query loading is checked in `SerializedMembership`; the verifier remains pending. |
| Retained certificate-list count and zero test | Complete | `MachinePrimitives.CertificateCount.computer` lifts extraction to seven Boolean stacks, directing the header to a dedicated `remaining` stack. `extract_stepAux` and `extract_run` preserve the private candidate/output stacks and exact costs. `whole_frame` loads the header; `check_step` peeks without consuming it; `checked_frame` and `natural_run` reach the correct zero/nonzero continuation in exactly `3b + 4` steps for binary count length `b`. `list_run` preserves all framed elements and trailing input. `natural_evalsToInTime` gives bound `2h + 2` in framed-header bits; `list_evalsToInTime` gives `2N + 2` in full certificate bits. Work stacks empty and control resets. The continuation halt is not counted; canonical complete headers are assumed. `CertificateMembership` now connects the header to traversal; malformed-input rejection remains pending. |
| Framed comparison with retained certificate count | Complete | `MachinePrimitives.CertificateComparison.computer` reuses the seven-stack `CertificateCount.Stack` layout. `compare_stepAux` and `compare_run` preserve arbitrary `remaining` contents with unchanged exact cost. `whole_frame` consumes one frame, restores the query, preserves the count and input/output suffixes, and empties candidate/scratch/count in exactly `3c + max(q, c) + q + 5` steps. `evalsToInTime` gives bound `2q + 2f + 3` in query/payload/frame bit lengths; `natural_run` and `natural_evalsToInTime` specialize to canonical naturals. `list_head_run` preserves every later certificate frame and the original count. Execution ends at a live continuation before its halt. `CertificateStep` connects comparison to in-place decrement and `CertificateMembershipStep` adds Boolean accumulation; the preloaded-count loop is checked in `CertificateMembershipLoop`; `CertificateMembership` supplies header dispatch and accumulator initialization. |
| Certificate-count predecessor into a separate stack | Complete | `MachinePrimitives.CertificatePredecessor.computer` reuses the seven-stack certificate layout. `pred_stepAux` and `pred_run` preserve arbitrary input/query/count/output contents with unchanged component step count. `whole_word` consumes `remaining`, empties scratch, and writes `binaryPredBits` onto `candidate`; `evalsToInTime` bounds the run by `2b + 3` for count bit length `b`. `natural_evalsToInTime` gives saturated predecessor including zero and one; `list_tail_evalsToInTime` produces the tail length after one element, preserving all unread frames. The final continuation halt is excluded. `CertificateDecrement` now connects this execution to ordered transfer for in-place decrement; `CertificateMembership` supplies header-to-traversal integration. |
| Ordered certificate-count result transfer | Complete | `MachinePrimitives.CertificateCountTransfer.computer` reuses the seven-stack layout. `reverse_run`, `restore_run`, and `whole_word` transfer candidate through scratch onto remaining in original order in exactly `2p + 2` steps for `p` candidate bits, preserving arbitrary input/query/count/output contents and the remaining-stack suffix. Candidate and scratch finish empty and control resets at a live continuation before its halt. `predecessor_evalsToInTime` and `natural_predecessor_evalsToInTime` bound transfer of an already computed predecessor by `2b + 2` in original count bit length `b`, using the now-public `MachinePrimitives.binaryPredBits_length_le`. `CertificateDecrement` now connects predecessor execution and transfer under one dispatcher; `CertificateMembership` supplies header-to-traversal integration. |
| In-place retained certificate-count decrement | Complete | `MachinePrimitives.CertificateDecrement.computer` combines predecessor and ordered transfer under finite control on the same seven stacks. `pred_stepAux` / `pred_run` and `transfer_stepAux` / `transfer_run` preserve component costs; `predecessor_run` enters transfer in the predecessor's final step. `whole_word` returns `binaryPredBits` to `remaining` in the exact predecessor witness's steps plus `2p + 2` for result length `p`. `evalsToInTime` bounds the total by `4b + 5` for original count length `b`. Input/query/count/output survive unchanged; candidate/scratch empty and control resets at a live continuation before its halt. `natural_evalsToInTime` covers saturated predecessor including zero and one; `list_tail_evalsToInTime` retains the tail count and all unread frames, including repetitions. `CertificateStep` supplies comparison/decrement integration and `CertificateMembershipStep` adds Boolean accumulation; the preloaded-count loop is checked in `CertificateMembershipLoop`; `CertificateMembership` supplies header dispatch and accumulator initialization. |
| Certificate comparison and in-place count decrement | Complete | `MachinePrimitives.CertificateStep.computer` combines framed comparison and decrement under finite control on the same seven stacks. `compare_stepAux` / `compare_run` and `decrement_stepAux` / `decrement_run` preserve exact component costs; `comparison_run` enters decrement in the final comparison step. `whole_frame` proves exact summed execution; `evalsToInTime` bounds the total by `2q + 2f + 4b + 8` for query, consumed-frame, and original count bit lengths. Equality is pushed onto output, query and unread suffixes survive, and all three work stacks finish empty. `natural_evalsToInTime` handles canonical naturals and saturated decrement; `list_head_evalsToInTime` preserves all later frames, including repetitions, and restores the exact tail count. The final continuation halt is excluded. `CertificateMembershipStep` now adds Boolean accumulation; `CertificateMembership` supplies header dispatch; malformed-input handling and full verifier integration remain pending. |
| Certificate membership accumulation step | Complete | `MachinePrimitives.CertificateMembershipStep.computer` connects comparison/decrement to a Boolean output accumulator on the same seven stacks. `accumulate_stepAux` and `accumulate_step` replace the leading equality and accumulator bits by their OR in one TM2 step, preserving all other stacks and the output suffix. `lift_stepAux` / `lift_run` preserve exact component costs while replacing a reached halt with accumulation. `comparison_decrement_run` and `whole_frame` prove the connected execution; `evalsToInTime` bounds it by `2q + 2f + 4b + 9` for query/frame/original-count bit lengths. `natural_evalsToInTime` handles canonical naturals and saturated decrement; `list_head_evalsToInTime` restores the exact tail count and retains every later frame, including duplicates. `accumulated_eq_true_iff` identifies the output as equality or a prior match. Work stacks empty and control resets at a live continuation; its halt is excluded. `CertificateMembershipLoop` now connects count-controlled repetition; `CertificateMembership` supplies header dispatch; malformed-input rejection and the full verifier remain pending. |
| Count-controlled certificate membership traversal | Complete | `MachinePrimitives.CertificateMembershipLoop.computer` repeats the membership step on seven stacks under finite control. `lift_stepAux` / `lift_run` preserve component costs; `check_step` peeks without consuming count, and `return_step` counts the jump back. `entry_run` restores the exact tail count; `whole_list` consumes the complete canonical body, including repetitions, returning membership OR the prior accumulator while preserving the query and arbitrary input/output suffixes and emptying count/work stacks. `runSteps` records exact costs; `runSteps_le` / `evalsToInTime` give `n * (2q + 4b + 11) + 2F + 1` for entry count, query bits, initial count bits, and framed body bits. `count_bits_mono` bounds all tail counts; `runSteps_le_bit_bound` gives `F * (2q + 4F + 11) + 2F + 1`. `result_eq_true_iff` gives separate Boolean semantics. The canonical count, query, and accumulator are preloaded, and the final continuation halt is excluded. `CertificateMembership` now supplies header dispatch and accumulator initialization; malformed-input rejection and the full verifier remain pending. |
| Membership from a complete encoded certificate | Complete | `MachinePrimitives.CertificateMembership.computer` connects framed header extraction and the membership loop on seven stacks. `header_stepAux` / `header_run` initialize false and enter the loop in the extractor's final counted step; `loop_stepAux` / `loop_run` preserve exact loop costs. `header_whole_frame` loads the retained count in exactly `3b + 3` steps, including initialization. `whole_list` consumes the full `BinaryNatLists.encodeNatList` certificate, including repetitions, emits precisely membership, preserves query and input/output suffixes, empties count/work stacks, and resets control. Exact `runSteps` is header cost plus loop cost; `runSteps_le_bit_bound` / `evalsToInTime` give `N * (2q + 4N + 16) + 4` in query/full-certificate bits. `result_eq_true_iff` states separate Boolean semantics. Query is preloaded, canonical complete encodings are assumed, and the final continuation halt is excluded. Serialized query loading is checked in `SerializedMembership`; malformed-input rejection, serialized literal/formula evaluation, and the full verifier remain pending. |
| Membership from a serialized query and certificate | Complete | `MachinePrimitives.SerializedMembership.computer` loads a leading framed query and enters the certificate-membership machine on the same seven stacks. `query_stepAux` / `query_run` and `membership_stepAux` / `membership_run` retain exact component costs. `query_whole_frame` loads the query in original order in exactly `3q + 3` steps, preserving the following input and private stacks. `whole_input` consumes `encodeInput query xs`, including all repeated entries, emits membership, retains query and arbitrary input/output suffixes, empties count/work stacks, and resets control. Exact `runSteps` is query extraction plus certificate membership; `runSteps_le_bit_bound` / `evalsToInTime` give `M * (4M + 19) + 7` in complete serialized input bits `M`. `result_eq_true_iff` states separate Boolean semantics. Canonical complete encodings are assumed and the final continuation halt is excluded. Query cleanup and canonical halting output are checked in `CanonicalMembership`; function-level packaging is checked in `MembershipComputable`; malformed-input rejection and the full verifier remain pending. |
| Canonical halting membership output | Complete | `MachinePrimitives.CanonicalMembership.computer` connects serialized membership to query cleanup on the same seven stacks. `lift_stepAux` / `lift_run` retain component costs; `cleanup_entry_step` counts the one-step transition. `cleanup_run` drains any query in exactly `q + 1` steps, preserving all six other stacks, resetting control, and halting. `whole_input` gives exact combined execution with input/output suffix preservation. `initList_eq_cfg` / `haltList_eq_cfg` identify canonical configurations; `outputsInTime` proves `TM2OutputsInTime` membership with all non-output stacks empty and bound `M * (4M + 20) + 9` in complete serialized input bits, including cleanup and final halt. Zero queries, empty certificates, and repetitions are covered. Function-level packaging is checked in `MembershipComputable`; malformed-input rejection and the full verifier remain pending. |
| Polynomial-time membership function | Complete | `FramedNatListQuery.finEncoding` supplies the framed Boolean encoding of `Nat × List Nat`; `decodePrefix_encode_append`, `decode_encode`, and `encode_length` check parsing and the full additive bit measure. `decode_encode_append_nonempty` rejects trailing data at the decoder level. `CanonicalMembership.membership_eq_true_iff` and `membership_eq_false_iff` state the two Boolean outcomes separately. `timePolynomial_eval` evaluates `X * (4 * X + 20) + 9`; `computableInPolyTime` packages the existing canonical seven-stack machine under this input encoding and mathlib Boolean output. Repetitions, zero queries, and empty certificates are covered. This is a canonical-encoding machine contract, not malformed-stream rejection or a complete SAT verifier. |
| Ordered Boolean copying with source restoration | Complete | `MachinePrimitives.BooleanCopy.computer` has three Boolean stacks and finite reverse/restore control. `reverse_run`, `restore_run`, and `whole_word` restore an arbitrary source word and prepend an ordered copy to the supplied target suffix in exactly `2n + 2` steps for source bit length `n`. Scratch finishes empty and control resets at a live continuation before its halt. `evalsToInTime` gives the same linear bound; `certificate_run` and `certificate_evalsToInTime` copy the complete framed natural-list certificate, retaining its header and repetitions. The source must already occupy its own stack; `PreservingMembership` now connects one copy and membership run, while `QueryMembershipLoop` supplies repeated-query dispatch and `SerializedQueryMembership` supplies dedicated-stack loading. |
| Membership with a retained complete certificate | Complete | `MachinePrimitives.PreservingMembership.computer` connects copying and membership on eight Boolean stacks. `copy_stepAux` / `copy_run` and `membership_stepAux` / `membership_run` preserve exact component costs and private data. `copy_whole_word` restores backup while copying onto input; `membership_entry_step` counts the transition. `whole_list` emits membership while retaining the full framed certificate, query, and input/output suffixes, emptying all count/work stacks, and resetting control. Exact cost is `2N + 3 + CertificateMembership.runSteps`; `runSteps_le_bit_bound` / `evalsToInTime` give `N * (2q + 4N + 18) + 7` for full certificate bits `N` and raw query bits `q`. Empty certificates, zero queries, and repetitions are covered. Query and backup are preloaded; the final live continuation halt is excluded. `QueryMembershipLoop` supplies repeated-query dispatch; canonical full-verifier output remains separate. |
| Framed membership with reusable query workspace | Complete | `MachinePrimitives.ReusableMembership.computer` connects framed query extraction, certificate-preserving membership, and query cleanup on eight Boolean stacks. `query_stepAux` / `query_run` preserve private stacks including backup; `membership_stepAux` / `membership_run` retain component costs and redirect halt to cleanup. `query_whole_frame` loads the query in exactly `3q + 3` steps; `cleanup_entry_step` counts the transition; `cleanup_run` drains it in exactly `q + 1` steps while preserving all other stacks. `whole_query` emits membership, retains the full certificate and arbitrary unread input/output suffixes, empties query/count/work stacks, and resets control at a live `done` label. Exact `runSteps` is query extraction plus preserved membership plus `q + 2`; `runSteps_le_bit_bound` / `evalsToInTime` give `N * (2q + 4N + 18) + 4q + 12` in raw query/full-certificate bits. `result_eq_true_iff` states separate Boolean semantics. Zero queries, empty certificates, and repetitions are covered. `SerializedQueryMembership` supplies backup loading; the full verifier remains pending; `QueryMembershipLoop` supplies repeated-query dispatch; the final continuation halt is excluded. |
| Literal evaluation with reusable certificate | Complete | `MachinePrimitives.LiteralEvaluation.computer` retains a supplied polarity through framed lookup on eight Boolean stacks. `lift_stepAux` / `lift_run` preserve exact component costs; `sign_stepAux` / `sign_step` apply conditional negation and reset control in one step, changing only output. `whole_query` and `whole_literal` preserve the full certificate and arbitrary input/output suffixes, empty query/count/work stacks, and emit the value of `CNF.Literal.eval` under `Certificate.assignment`. `result_eq_eval` / `result_eq_true_iff` state independent Boolean semantics. Exact cost is `ReusableMembership.runSteps + 1`; `runSteps_le_bit_bound` / `literal_evalsToInTime` give `N * (2q + 4N + 18) + 4q + 13` in raw variable/full-certificate bits. Polarity and backup are supplied; parsing the encoded literal, clause aggregation, exact-width checking, full verifier integration, and the final continuation halt are outside this contract. |
| Packed literal frame loading | Complete | `MachinePrimitives.PackedLiteral.computer` extracts one complete packed-literal frame and splits its low bit on five Boolean stacks. `head_encode_toNat` / `tail_encode_toNat` recover the polarity and canonical raw variable, including positive zero's empty payload. `lift_stepAux` / `lift_run` retain extraction costs; `split_step` counts the one-step pop. `whole_frame` / `whole_literal` preserve arbitrary unread input and query contents and empty scratch/count, with candidate initially empty and finally holding the raw variable. Exact cost is `3b + 4` for packed payload bits `b`; `literal_evalsToInTime` bounds it by `2L + 2` for the full literal frame length `L`. `PackedLiteralEvaluation` supplies injection and combined evaluation. The final live continuation halt and full verifier remain separate obligations. |
| Packed literal evaluation with reusable certificate | Complete | `MachinePrimitives.PackedLiteralEvaluation.computer` connects packed loading directly to raw-variable lookup, query cleanup, and conditional negation on eight Boolean stacks. `ReusableMembership.whole_raw_query` / `LiteralEvaluation.whole_raw_query` expose the checked entry after extraction. `loader_stepAux` / `loader_run` preserve private stacks; `evaluation_stepAux` / `evaluation_run` preserve exact component costs. `loader_whole_literal` retains arbitrary remaining-count/candidate/output/backup data; `evaluation_entry_step` counts the polarity transfer. `whole_literal` consumes the actual framed code and returns `CNF.Literal.eval` under `Certificate.assignment`, preserving the complete certificate and input/output suffixes and emptying query/count/workspace. Exact `runSteps` is `3b + q + PreservingMembership.runSteps + 8`; `runSteps_le_frame_bound` / `literal_evalsToInTime` give `N * (2L + 4N + 18) + 2L + 13` in complete literal-frame/certificate bits. Both signs, zero, empty certificates, and repetitions are covered. `ClauseEvaluationStep` supplies one disjunctive accumulation step. Backup is preloaded; the final live continuation halt, repeated clause traversal, exact-width checking, and the full verifier remain separate. |
| One packed-literal clause accumulation step | Complete | `MachinePrimitives.ClauseEvaluationStep.computer` wraps packed evaluation on the same eight Boolean stacks. `accumulate_stepAux` / `accumulate_step` OR two leading output bits in one counted step, preserving all other stacks and resetting control. `lift_stepAux` / `lift_run` retain exact evaluation costs; `whole_literal` consumes the literal frame, preserves the complete certificate and arbitrary input/output suffixes, and clears workspace. `accumulated_eq_true_iff` gives independent satisfaction semantics; `accumulated_eq_clause_append` / `whole_literal_append` identify the result as the value of the processed clause with this literal appended, retaining occurrences. Exact `runSteps` is `PackedLiteralEvaluation.runSteps + 1`; `runSteps_le_frame_bound` / `literal_evalsToInTime` give `N * (2L + 4N + 18) + 2L + 14` in complete literal-frame/certificate bits. Backup and accumulator are preloaded; `ClauseLiteral` supplies independent outer literal-count preservation. Final live continuation halt, repeated clause traversal, exact-width checking, and full verifier remain separate. |
| Packed-literal accumulation preserving an outer literal count | Complete | `MachinePrimitives.ClauseLiteral.computer` embeds the eight-stack accumulation machine on nine Boolean stacks. `lift_stepAux`, `lift_step`, and `lift_run` retain arbitrary outer contents with exactly the component cost, including reached halts. `whole_literal` preserves the full certificate, outer word, and both suffixes while emptying inner count/query/workspace. `clause_head` consumes the head literal frame and retains all unread frames and the original literal count; `clause_head_append` identifies the updated processed-prefix value without removing repeated occurrences. `runSteps_le_frame_bound` / `literal_evalsToInTime` retain `N * (2L + 4N + 18) + 2L + 14` in full literal-frame/certificate bits, independent of outer contents. Certificate, accumulator, and outer count are preloaded; outer decrement, repeated clause traversal, header loading, exact-width checking, and full verifier remain pending. The final live continuation halt is excluded. |
| Framed membership preserving an outer query count | Complete | `MachinePrimitives.QueryMembership.computer` adds a ninth Boolean stack independent of certificate traversal. `lift_stepAux`, `lift_step`, and `lift_run` preserve arbitrary outer contents with the exact original cost, including reached halts. `whole_query` retains the full certificate, outer count, and input/output suffixes while clearing lookup query/count/work stacks at a live continuation. `list_head` preserves all unread query frames, including repetitions, and the original list count. `runSteps_le_bit_bound` / `evalsToInTime` retain `N * (2q + 4N + 18) + 4q + 12` for raw query/full-certificate bit lengths; the bound is independent of the outer word. `QueryMembershipStep` now supplies outer decrement; `EncodedQueryMembership` supplies count loading; `SerializedQueryMembership` supplies certificate loading; the full verifier remains pending; `QueryMembershipLoop` supplies repeated-query dispatch. |
| Framed membership and outer query-count decrement | Complete | `MachinePrimitives.QueryMembershipStep.computer` connects lookup and outer decrement on nine Boolean stacks under finite control. `lookup_stepAux` / `lookup_run` and `decrement_stepAux` / `decrement_run` retain component costs; decrement preserves arbitrary inner count and backup contents. `lookup_whole_query`, `decrement_entry_step`, and `decrement_whole_word` isolate the phases and the one-step transition. `whole_query` proves their exact summed execution, emitting membership and retaining backup and input/output suffixes with query/count/work stacks empty. `list_head` restores the exact tail count while preserving repeated query and certificate occurrences. `runSteps_le_bit_bound`, `evalsToInTime`, and `list_head_evalsToInTime` give `N * (2q + 4N + 18) + 4q + 4b + 18` for raw query/full-certificate/outer-count bit lengths. `QueryMembershipLoop` supplies count-controlled repetition; `EncodedQueryMembership` supplies count loading; `SerializedQueryMembership` supplies certificate loading; the full verifier remains pending; the final live continuation halt is excluded. |
| Count-controlled reusable membership queries | Complete | `MachinePrimitives.QueryMembershipLoop.computer` repeats lookup and outer decrement under finite control on nine Boolean stacks. `lift_stepAux` / `lift_run` retain component costs; `check_step` peeks without consuming the outer count, and `entry_run` includes the return jump and restores the exact tail count. `whole_list` consumes the complete canonical query body, preserves the complete certificate and arbitrary input/output suffixes, emits one membership bit per occurrence in reverse query order, and empties all count/workspace stacks. `results_cons` and `results_length` record output order and multiplicity separately. Exact `runSteps` counts every peek and return; `runSteps_le` gives a uniform body-budget bound, and `runSteps_le_bit_bound` / `evalsToInTime` give `Q * (N * (2Q + 4N + 18) + 8Q + 20) + 1` in framed query-body/full-certificate bits `Q`/`N`. Count and certificate are preloaded; `EncodedQueryMembership` supplies header loading. `SerializedQueryMembership` supplies backup loading; the full SAT verifier remains pending. The final live continuation halt is excluded. |
| Membership from a complete encoded query list | Complete | `MachinePrimitives.EncodedQueryMembership.computer` loads the outer header and enters the repeated-query loop under one finite nine-stack dispatcher. `header_stepAux` / `header_run` preserve private data including backup and the independent inner count; `loop_stepAux` / `loop_run` retain exact component costs. `header_whole_frame` includes loop entry in the exact `3b + 3` extraction cost. `whole_list` consumes the full canonical query encoding, preserves the certificate and arbitrary input/output suffixes, emits one membership bit per occurrence in reverse query order, and empties count/workspace stacks. Exact `runSteps` sums header extraction and loop execution; `runSteps_le_bit_bound` / `evalsToInTime` give `M * (N * (2M + 4N + 18) + 8M + 23) + 4` in full framed query-list/certificate bits `M`/`N`. The certificate remains preloaded; `SerializedQueryMembership` supplies its loading. The full SAT verifier remains pending. The final live continuation halt is excluded. |
| Repeated membership from serialized certificate and queries | Complete | `MachinePrimitives.SerializedQueryMembership.computer` loads the complete certificate from a leading outer frame, then processes the complete query-list encoding on nine Boolean stacks. `certificate_stepAux` / `certificate_run` preserve query, output, both counts, and candidate; `membership_stepAux` / `membership_run` retain exact component costs. `certificate_whole_frame` includes dispatcher entry in exactly `3N + 3` steps for certificate bits `N`. `encodeInput_length` gives `2N + 1 + M` for full certificate/query-list lengths `N`/`M`. `whole_input` starts with empty backup/count/workspace, consumes both serialized components including repetitions, retains the loaded certificate and arbitrary input/output suffixes, emits membership bits in reverse query order, and clears count/workspace. `runSteps` records exact summed execution; `runSteps_le_bit_bound` / `evalsToInTime` give `S * (S * (2S + 18) + 8S + 26) + 7` in complete serialized bits `S`. The final live continuation halt is excluded; `CanonicalQueryMembership` supplies backup cleanup and canonical halting output. Malformed-input rejection and the full SAT verifier remain pending. |
| Canonical halting output for repeated membership queries | Complete | `MachinePrimitives.CanonicalQueryMembership.computer` connects serialized repeated membership to backup cleanup on the same nine Boolean stacks. `lift_stepAux` / `lift_run` preserve component costs; `cleanup_entry_step` counts the one-step transition. `cleanup_run` drains any backup in exactly `N + 1` steps while retaining all eight other stacks, resetting control, and halting. `whole_input` proves exact combined execution and input/output suffix preservation. `initList_eq_cfg` / `haltList_eq_cfg` identify canonical configurations; `outputsInTime` gives `TM2OutputsInTime` with all non-output stacks empty and bound `S * (S * (2S + 18) + 8S + 27) + 9` in complete serialized input bits, including cleanup and final halt. Output contains one membership bit per query occurrence in reverse order; empty lists, zero, and repetitions are covered. Function-level encoding/witness packaging is checked in `QueryMembershipComputable`; malformed-input rejection and the full SAT verifier remain pending. |
| Polynomial-time repeated-membership function | Complete | `FramedNatListQueries.finEncoding` matches the serialized `(queries, certificate) : List Nat × List Nat` input. `decodePrefix_encode_append`, `decode_encode`, `encode_injective`, and `decode_encode_append_nonempty` prove prefix parsing, the round trip, injectivity, and decoder suffix rejection. `encode_length` gives `2N + 1 + M` in full certificate/query-list bits. `CanonicalQueryMembership.membershipResults_reverse` and `membershipResults_length` give reverse-order semantics and one output bit per occurrence. `CanonicalQueryMembership.computableInPolyTime` packages the existing nine-stack machine with `RawBoolList.finEncoding` and polynomial `X * (X * (2 * X + 18) + 8 * X + 27) + 9`, including cleanup and final halting. This is the serialized encoding, not automatically the verifier's tagged pair encoding; that conversion, serialized literal/formula evaluation, exact-width checking, and malformed-stream machine rejection remain pending. |
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

- The ten `CertificateMembershipMachine` audits pass. `result_eq_true_iff`
  uses only `propext` and `Quot.sound`; the other nine declarations use only
  `propext`, `Classical.choice`, and `Quot.sound`. Full `lake build` passed
  2,211 jobs on 2026-09-25; all 336 reported axiom lists contain only these
  standard axioms, with three further axiom-free reports. The 56-file Lean
  source/config scan found only the existing explanatory `proof_wanted`
  comment. `header_whole_frame` includes false initialization and loop entry
  in the exact `3b + 3` extraction cost. `whole_list` proves membership from
  the complete encoded certificate, and `runSteps_le_bit_bound` gives
  `N * (2q + 4N + 16) + 4` in query/full-certificate bit lengths. The query
  remains preloaded; canonical complete encodings are assumed, and the final
  continuation halt is excluded. Serialized query loading, malformed-input
  rejection, literal/formula evaluation, and the full verifier remain pending.

- The ten `SerializedMembershipMachine` audits pass. `result_eq_true_iff`
  uses only `propext` and `Quot.sound`; the other nine declarations use only
  `propext`, `Classical.choice`, and `Quot.sound`. Full `lake build` passed
  2,212 jobs on 2026-09-27; all 346 reported axiom lists contain only those
  standard axioms, with three further axiom-free reports. The 57-file Lean
  source/config scan found only the existing explanatory `proof_wanted`
  comment. `query_whole_frame` loads a leading framed query in exact cost
  `3q + 3`; `whole_input` joins it to complete certificate traversal while
  preserving query and input/output suffixes and emptying count/work stacks.
  `runSteps_le_bit_bound` proves `M * (4M + 19) + 7` in full serialized
  input bits. Canonical complete encodings are assumed, and the final
  continuation halt is excluded. Query cleanup, function-level encoding and
  polynomial-time witness packaging, malformed-input rejection, and the full
  SAT verifier remain separate obligations.

- The ten `CanonicalMembershipMachine` audits pass with only `propext`,
  `Classical.choice`, and `Quot.sound`. Full `lake build` passed 2,213 jobs
  on 2026-09-28; all 356 reported axiom lists contain only those standard
  axioms, with three further axiom-free reports. The 58-file Lean source/config
  scan found only the existing explanatory `proof_wanted` comment.
  `cleanup_run` preserves all six other stacks and halts after exactly
  `q + 1` steps. `whole_input` joins serialized membership, one cleanup-entry
  step, and that drain. `outputsInTime` reaches canonical `haltList` output,
  with all non-output stacks empty and initial control restored, within
  `M * (4M + 20) + 9` steps in full serialized input bits, including the final
  halt. Function-level encoding/witness packaging, malformed-input rejection,
  literal/formula evaluation, exact-width checking, the full SAT verifier,
  exact 3-SAT NP membership, and Cook--Levin remain pending.

- The ten `MembershipComputable` audits pass. The six encoding declarations
  and two Boolean semantic lemmas use only `propext` and `Quot.sound`;
  `timePolynomial_eval` and `computableInPolyTime` additionally use
  `Classical.choice`. Full `lake build` passed 2,214 jobs on 2026-09-29;
  all 366 reported axiom lists contain only these standard axioms, with
  three further axiom-free reports. The 59-file Lean source/config scan
  found only the existing explanatory `proof_wanted` comment. The framed
  `Nat × List Nat` encoding has a checked round trip and exact additive
  bit length; the polynomial-time witness uses the already checked seven-stack
  membership machine, including cleanup and the final halt. Its bound is
  `M * (4M + 20) + 9` in full encoded input bits. Malformed-stream machine
  rejection, certificate preservation/copying, literal/formula evaluation,
  exact-width checking, the full SAT verifier, exact 3-SAT NP membership,
  and Cook--Levin remain pending.

- The seven `BooleanCopyMachine` audits pass with only `propext`,
  `Classical.choice`, and `Quot.sound`. Full `lake build` passed 2,215 jobs
  on 2026-09-30; all 373 reported axiom lists contain only these standard
  axioms, with three further axiom-free reports. The 60-file Lean
  source/config scan found only the existing explanatory `proof_wanted`
  comment. `whole_word` restores the source and provides an ordered working
  copy above an arbitrary target suffix in exactly `2n + 2` steps, including
  both exhaustion transitions. Scratch empties and control resets at a live
  continuation before its halt. The certificate interface retains the entire
  framed encoding, including count and repetitions. Dedicated-stack loading,
  repeated-membership integration, literal/formula evaluation, exact-width
  checking, the full SAT verifier, exact 3-SAT NP membership, and Cook--Levin
  remain pending.

- The ten `PreservingMembershipMachine` audits pass with only `propext`,
  `Classical.choice`, and `Quot.sound`. Full `lake build` passed 2,216 jobs
  on 2026-10-01; all 383 reported axiom lists contain only these standard
  axioms, with three further axiom-free reports. The 61-file Lean source/config
  scan found only the existing explanatory `proof_wanted` comment.
  `whole_list` retains the complete certificate and query while emitting
  membership from a working copy, with arbitrary input/output suffixes and
  empty count/work stacks. The exact cost includes copying and its entry
  transition; `runSteps_le_bit_bound` gives `N * (2q + 4N + 18) + 7`.
  The final live continuation halt is excluded. Dedicated-stack loading,
  repeated-query dispatch, literal/formula evaluation, exact-width checking,
  the full SAT verifier, exact 3-SAT NP membership, and Cook--Levin remain pending.

The source tree contains no `sorry`, `admit`, project-defined `axiom`, or
`unsafe` declaration.


- The twelve `ReusableMembershipMachine` audits pass. `result_eq_true_iff`
  uses only `propext` and `Quot.sound`; the eleven machine/execution results
  use only `propext`, `Classical.choice`, and `Quot.sound`. Full `lake build`
  passed 2,217 jobs on 2026-10-02; all 395 reported axiom lists use only these
  standard axioms, with three further axiom-free reports. The 62-file Lean
  source/config scan found only the existing explanatory `proof_wanted`
  comment. The checked framed lookup retains backup and suffixes and clears
  query/work stacks with exact cost and a polynomial bit bound. Backup loading,
  repeated-query dispatch, and the full SAT verifier remain separate obligations.

- The eight `QueryMembershipMachine` audits pass with only `propext`,
  `Classical.choice`, and `Quot.sound`. Full `lake build` passed 2,218 jobs
  on 2026-10-03; all 403 reported axiom lists use only these standard axioms,
  with three further axiom-free reports. The 63-file Lean source/config scan
  found only the existing explanatory `proof_wanted` comment. Arbitrary
  contents on the ninth stack survive every lifted statement and exact run,
  with the original runtime bound. `list_head` retains the unread query frames
  and original outer count; decrementing that count and dispatching repeated
  queries are still pending. This is a preserved-data kernel with a preloaded
  certificate, not a completed SAT verifier or canonical full-verifier output.

- The thirteen `QueryMembershipStepMachine` audits pass with only `propext`,
  `Classical.choice`, and `Quot.sound`. Full `lake build` passed 2,219 jobs
  on 2026-10-04; all 416 reported axiom lists use only these standard axioms,
  with three further axiom-free reports. The 64-file Lean source/config scan
  found only the existing explanatory `proof_wanted` comment. The combined
  lookup/decrement restores the exact query-tail count, retains backup and
  suffixes, and clears the workspace with exact execution and a polynomial
  bit bound. Its one-step phase transition is counted; final continuation
  halt, header loading, repeated dispatch, and the full verifier remain outside
  this contract.

- The twelve `QueryMembershipLoopMachine` audits pass. `results_cons` and
  `results_length` use only `propext` and `Quot.sound`; the ten machine/runtime
  declarations additionally use `Classical.choice`. Full `lake build` passed
  2,220 jobs on 2026-10-05; all 428 reported axiom lists use only those standard
  axioms, with three further axiom-free reports. The 65-file Lean source/config
  scan found only the existing explanatory `proof_wanted` comment. Complete
  canonical query-body traversal now has exact execution and a polynomial
  bound in query-body/full-certificate bits, with preserved backup and suffixes,
  empty count/workspace stacks, and one output bit per query occurrence in
  reverse query order. Count/certificate loading and the full verifier remain
  separate obligations; the final live continuation halt is excluded.

- The nine `EncodedQueryMembershipMachine` audits pass with only `propext`,
  `Classical.choice`, and `Quot.sound`. Full `lake build` passed 2,221 jobs
  on 2026-10-06; all 437 reported axiom lists use only these standard axioms,
  with three further axiom-free reports. The 66-file Lean source/config scan
  found only the existing explanatory `proof_wanted` comment. Complete query
  encodings now include header loading and loop entry, with exact summed cost
  and the polynomial bound in full query-list/certificate bits. The retained
  certificate, suffixes, repeated output occurrences, and empty final workspace
  are checked. Only the certificate remains preloaded; its loading, full verifier
  integration, and canonical halting output remain separate obligations.


- The ten `SerializedQueryMembershipMachine` audits pass. `encodeInput_length`
  uses only `propext` and `Quot.sound`; the nine machine/runtime declarations
  additionally use `Classical.choice`. Full `lake build` passed 2,222 jobs on
  2026-10-07; all 447 reported axiom lists use only those standard axioms, with
  three further axiom-free reports. The 67-file Lean source/config scan found
  only the existing explanatory `proof_wanted` comment. The leading outer
  certificate frame is loaded into backup before complete query-list processing,
  with exact summed execution and the cubic bound in total serialized input
  bits. No certificate or count is preloaded; backup, suffixes, and repeated
  output occurrences are retained. Backup cleanup, canonical halting output,
  and the full SAT verifier remain separate obligations. The final live
  continuation halt is excluded.

- The ten `CanonicalQueryMembershipMachine` audits pass with only `propext`,
  `Classical.choice`, and `Quot.sound`. Full `lake build` passed 2,223 jobs
  on 2026-10-08; all 457 reported axiom lists contain only these standard
  axioms, with three further axiom-free reports. The 68-file Lean source/config
  scan found only the existing explanatory `proof_wanted` comment. The checked
  backup drain preserves all other stacks in exactly `N + 1` steps. Complete
  serialized execution includes cleanup entry and reaches canonical `haltList`
  output with initial control and all non-output stacks empty, bounded by
  `S * (S * (2S + 18) + 8S + 27) + 9` in total serialized input bits. Repeated
  occurrences and reverse query order are retained. Function-level packaging,
  malformed-input rejection, and the full SAT verifier remain separate.

- The twelve `QueryMembershipComputable` audits pass. Seven encoding results
  and three list-semantic results use only `propext` and `Quot.sound`;
  `timePolynomial_eval` and `computableInPolyTime` additionally use
  `Classical.choice`. Full `lake build` passed 2,224 jobs on 2026-10-09;
  all 469 reported axiom lists contain only these standard axioms, with three
  further axiom-free reports. The 69-file Lean source/config scan found only
  the existing explanatory `proof_wanted` comment. The serialized pair has
  checked prefix parsing, round trip, injectivity, decoder suffix rejection,
  and exact bit length. The polynomial-time witness uses the existing canonical
  nine-stack machine and raw Boolean-list output, retaining one bit per query
  occurrence in reverse order, including cleanup and final halt in its cubic
  bit bound. Conversion from the verifier's tagged pair encoding,
  literal/formula evaluation, exact-width checking, malformed-stream machine
  rejection, exact 3-SAT NP membership, and Cook--Levin remain pending.


- The eleven `LiteralEvaluationMachine` audits pass. The two independent
  semantic results use only `propext` and `Quot.sound`; the nine machine/runtime
  declarations additionally use `Classical.choice`. Full `lake build` passed
  2,225 jobs on 2026-10-10; all 480 reported axiom lists contain only these
  standard axioms, with three further axiom-free reports. The 70-file Lean
  source/config scan found only the existing explanatory `proof_wanted` comment.
  The eight-stack wrapper retains supplied polarity through the exact lookup
  run and applies conditional negation in one additional step. `whole_literal`
  agrees with `CNF.Literal.eval` under the certificate assignment, preserving
  backup and suffixes and clearing workspace. Its bound is
  `N * (2q + 4N + 18) + 4q + 13` in raw variable/full-certificate bits.
  Polarity and backup remain preloaded; serialized literal extraction, clause
  aggregation, exact-width checking, canonical full-verifier output, exact
  3-SAT NP membership, and Cook--Levin remain pending. The live continuation's
  final halt is excluded.


- The nine `PackedLiteralMachine` audits pass. The two encoding identities
  use only `propext` and `Quot.sound`; the seven machine/execution results
  additionally use `Classical.choice`. Full `lake build` passed 2,226 jobs
  on 2026-10-11; all 489 reported axiom lists contain only these standard
  axioms, with three further axiom-free reports. The 71-file Lean source/config
  scan found only the existing explanatory `proof_wanted` comment.
  `whole_literal` loads the formula encoding's packed literal into its polarity
  and raw variable in exactly `3b + 4` steps, covering both signs and positive
  zero's empty payload. The full-frame bound is `2L + 2`; unread input and
  arbitrary query contents survive and both work stacks empty. This five-stack
  loader remains separate from the eight-stack evaluation machine; combined
  packed-literal evaluation, clause aggregation, exact-width checking, and the
  full verifier remain pending. The final live continuation halt is excluded.


- The thirteen new packed-evaluation audits pass: both `whole_raw_query`
  entry theorems and the eleven `PackedLiteralEvaluationMachine` declarations
  use only `propext`, `Classical.choice`, and `Quot.sound`. Full `lake build`
  passed 2,227 jobs on 2026-10-12; all 502 reported axiom lists contain only
  those standard axioms, with three further axiom-free reports. The 72-file
  Lean source/config scan found only the existing explanatory `proof_wanted`
  comment. The combined eight-stack machine consumes a canonical packed
  literal frame, carries the extracted polarity into raw lookup, drains the
  query, and emits the exact literal value while retaining the full certificate
  and arbitrary input/output suffixes. Exact cost is
  `3b + q + PreservingMembership.runSteps + 8`; the complete-frame bound is
  `N * (2L + 4N + 18) + 2L + 13`. Both signs, positive zero's empty payload,
  empty certificates, and repeated entries are covered. Backup remains
  preloaded; the final live continuation halt, clause aggregation, exact-width
  checking, the full verifier, exact 3-SAT NP membership, and Cook--Levin remain
  separate obligations.


- The twelve `ClauseEvaluationStepMachine` audits pass. The two independent
  semantic lemmas use only `propext`; the ten machine/runtime declarations
  use only `propext`, `Classical.choice`, and `Quot.sound`. Full `lake build`
  passed 2,228 jobs on 2026-10-13; all 514 reported axiom lists contain only
  those standard axioms, with three further axiom-free reports. The 73-file
  Lean source/config scan found only the existing explanatory `proof_wanted`
  comment. `whole_literal` adds exactly one accumulation step to checked
  packed evaluation; `whole_literal_append` connects its result to the value
  of the processed clause with this literal appended. The full-frame bound
  is `N * (2L + 4N + 18) + 2L + 14`. Both signs, zero, empty certificates,
  arbitrary prior accumulators, and repetitions are covered; certificate,
  unread input, and output suffix survive and workspace empties. Backup and
  accumulator remain preloaded. An independent outer literal count, repeated
  clause/formula traversal, exact-width checking, canonical full-verifier
  output, exact 3-SAT NP membership, and Cook--Levin remain pending; the final
  live continuation halt is excluded.


- The nine `ClauseLiteralMachine` audits pass with only `propext`,
  `Classical.choice`, and `Quot.sound`. Full `lake build` passed 2,229 jobs
  on 2026-10-14; all 523 reported axiom lists contain only those standard
  axioms, with three further axiom-free reports. The 74-file Lean source/config
  scan found only the existing explanatory `proof_wanted` comment.
  Every component statement and exact run preserves an arbitrary ninth-stack
  word without extra steps. `clause_head` retains all unread literal frames
  and the original outer count; `clause_head_append` connects the accumulated
  result to the value of the processed prefix with this literal appended.
  Both signs, zero, empty certificates, and repeated occurrences are covered.
  The bound remains `N * (2L + 4N + 18) + 2L + 14`, independent of the outer
  word. Certificate, accumulator, and count are preloaded; outer decrement,
  repeated clause/formula traversal, exact-width checking, canonical full-verifier
  output, exact 3-SAT NP membership, and Cook--Levin remain pending. The final
  live continuation halt is excluded.

- The ten `UnarySplitMachine` audits pass on 2026-10-15. Four literal/mark
  encoding lemmas use only `propext`; `flatMap_dbl_clause` and
  `signCount_clause` additionally use `Quot.sound`; the four machine-run
  results (`extractHandlers_exits`, `extract_exits`, `extract_clause_exits`,
  `moveLit_exits`) also use `Classical.choice`. Full `lake build` passed
  2,265 jobs, including the newly registered module. All 589 reported axiom
  lists use only these three standard axioms, with three further axiom-free
  reports. The 110-file Lean source/config scan found only the existing
  explanatory `proof_wanted` comment. No warnings in the repaired module;
  existing dependency-module linter warnings remain. These are bounded
  runs of clause-processing routines, with explicit initial stack and flag
  conditions; full exact-3-SAT compilation and its polynomial bound remain
  pending. The existing unary Cook--Levin hardness audits also pass.
