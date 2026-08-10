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
| Generic polynomial-time machine composition | Pending | Prove that `compositionAux` computes function composition with a polynomial runtime; do not rely on mathlib's `proof_wanted` declaration as a completed proof. |
| Closed polynomial-time reduction composition | Pending | Derive `PolytimeManyOneReduction.comp` from the preceding machine theorem. |
| P | Pending | Define deterministic polynomial-time decidability for encoded languages. |
| NP | Pending | Define verifier-based NP with polynomial certificate bounds. |
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
- `MachineComposition.compositionAux` depends on `propext`,
  `Classical.choice`, and `Quot.sound`.

The source tree contains no `sorry`, `admit`, project-defined `axiom`, or
`unsafe` declaration.
