# Automation progress log

This journal records bounded daily attempts so later runs can reuse discoveries,
avoid failed routes, and choose a materially different experiment when blocked.

## 2026-07-26 — identity cases at the machine-composition boundary

- **Starting commit:** `4c4912e2e36a0ad49be30befe14bf3f303291961`
- **Goal:** advance Milestone 1 without relying on mathlib's unfinished generic
  polynomial-time machine-composition declaration.
- **Checked increment:** added `PolytimeManyOneReduction.reflComp` and
  `PolytimeManyOneReduction.compRefl`. Both compose a reduction with the
  polynomial-time identity reduction by reusing the original checked machine
  witness; no sequential-machine construction or unproved composition result is
  used. Added pointwise map simplification theorems and axiom audits.
- **Files:** `LeanNPHardness/PolytimeComposition.lean`,
  `LeanNPHardness/Audit.lean`, `LeanNPHardness.lean`, `README.md`, and
  `THEOREM_STATUS.md`.
- **Successful checks:** targeted composition-module build passed; full
  `lake build` passed 1,133 jobs. Axiom audit reports only `propext`,
  `Classical.choice`, and `Quot.sound` for the two new constructors. The source
  scan found no `sorry`, `admit`, project-defined `axiom`, or `unsafe`;
  `proof_wanted` occurs only in a comment describing the dependency boundary.
- **Failed approaches/blockers:** no failed implementation route today. The
  generic case remains blocked on constructing and verifying a sequential
  `FinTM2`; neither the pinned mathlib revision nor
  [current upstream mathlib](https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Computability/TuringMachine/Computable.lean)
  implements `TM2ComputableInPolyTime.comp` (both still mark it
  `proof_wanted`). Current upstream has also generalized the encoding arguments,
  so an eventual upstream contribution will need rebasing after the pinned proof
  works.
- **Useful API discovery:** the identity cases are definitionally the original
  function (`f ∘ id = f` and `id ∘ f = f`), so their exact
  `TM2ComputableInPolyTime` witnesses can be reused. The generic machine must
  instead combine stack indices, labels, and states, copy the first output
  through the intermediate encoding equivalences, and prove a summed polynomial
  runtime.
- **Ending state:** the identity cases are machine-checked and documented; the
  generic composition theorem and the milestone remain pending.
- **Best next experiment:** define a small machine-level lifting construction
  that embeds one `FinTM2` into a disjoint-union stack index, and prove a
  one-step simulation lemma before attempting sequential control or runtime
  composition.

## 2026-07-27 — left-machine stack embedding and step simulation

- **Starting commit:** `9193996cc34a4f0039bfabe5db5c8a315d1de0a1`
- **Goal:** implement the first machine-level component named by the previous
  entry: embed one `FinTM2` into a disjoint-union stack family and prove
  one-step preservation.
- **Checked increment:** added finite `StackIndex` and dependent
  `StackAlphabet` definitions for a pair of machines; `leftStacks` and its
  dependent-update compatibility theorem; recursive `liftLeftStmt` and
  `liftLeftCfg`; and the `liftLeft_stepAux` and `liftLeft_step` simulation
  theorems. The lift preserves the first machine's labels and state while
  leaving every second-machine stack empty.
- **Files:** `LeanNPHardness/MachineEmbedding.lean`,
  `LeanNPHardness/Audit.lean`, `LeanNPHardness.lean`,
  `THEOREM_STATUS.md`, and this journal.
- **Successful checks:** targeted machine-embedding build passed; full
  `lake build` passed 1,134 jobs. `#print axioms` reports only `propext` and
  `Quot.sound` for `MachineComposition.liftLeft_step`. The project scan found
  no `sorry`, `admit`, project-defined `axiom`, or `unsafe`; `proof_wanted`
  remains only in the explanatory dependency-boundary comment.
- **Failed approaches/blockers:** initial instance synthesis did not recover
  the component machines' `DecidableEq` and `Fintype` fields through the
  `StackIndex` definition; explicit local projection instances fixed it.
  `stacks` parsed as a reserved token in this Lean toolchain and was renamed
  `contents`. The dependent `Function.update` proof also required an explicit
  proof that `Sum.inl j ≠ Sum.inl k`; plain simplification did not derive it.
  Finally, the lifted `Option.map` step goal needed one explicit definitional
  reduction after rewriting the statement simulation.
- **Useful API discovery:** `TM2.stepAux` recursively evaluates an entire
  statement tree within one counted machine step. Consequently the statement
  lift must commute with every `push`, `peek`, `pop`, `load`, and `branch`
  constructor, while `goto` and `halt` are definitional. Dependent stack
  updates are the only nontrivial structural case in the left embedding.
- **Ending state:** one step of the first program is now simulated exactly in
  the combined stack family. No sequential control, intermediate-output copy,
  or runtime claim has been made.
- **Best next experiment:** implement the symmetric right-stack embedding and
  one-step simulation. Then use both simulations to design label and state
  injections for a genuinely combined program, keeping the later copy phase
  separate.

## 2026-07-28 — right-machine stack embedding and step simulation

- **Starting commit:** `0869697c5e61a9198fd8978b38d90281826ba2a2`
- **Goal:** complete the symmetric stack-level simulation needed before
  designing one combined sequential program.
- **Checked increment:** added `rightStacks`, its injection and dependent-update
  lemmas, recursive `liftRightStmt`, `liftRightCfg`, and the
  `liftRight_stepAux` and `liftRight_step` simulation theorems. The second
  machine now runs unchanged on the right side of `StackIndex first second`,
  with all first-machine stacks empty.
- **Files:** `LeanNPHardness/MachineEmbedding.lean`,
  `LeanNPHardness/Audit.lean`, `README.md`, `THEOREM_STATUS.md`, and this
  journal.
- **Successful checks:** targeted machine-embedding build passed; full
  `lake build` passed 1,134 jobs. `#print axioms` reports only `propext` and
  `Quot.sound` for `MachineComposition.liftRight_step`. The project scan found
  no `sorry`, `admit`, project-defined `axiom`, or `unsafe`; `proof_wanted`
  remains only in the explanatory dependency-boundary comment.
- **Failed approaches/blockers:** no failed route today; the right proof reused
  the explicit component instances, non-reserved `contents` name, injected
  inequality, and final definitional reduction identified on 2026-07-27.
  The remaining blocker is no longer stack simulation: a combined machine must
  inject both label and internal-state types and add a distinct transfer phase.
- **Useful API discovery:** the left and right `TM2.stepAux` simulations are
  structurally identical after exchanging `Sum.inl` and `Sum.inr`. The
  intermediate-symbol conversion cannot be defined from two raw `FinTM2`
  values alone; it must use the first `TM2ComputableAux.outputAlphabet` and
  second `TM2ComputableAux.inputAlphabet` equivalences through the shared
  middle encoding.
- **Ending state:** either component machine now has a checked exact one-step
  simulation on its side of the combined stack family. Sequential control,
  transfer, multi-step correctness, and runtime bounds remain pending.
- **Best next experiment:** define finite combined control-label and
  phase-tagged state types, including a separate transfer label/state, at the
  `TM2ComputableAux` layer where the middle-alphabet equivalence is available.
  First prove the label and state injections preserve one component step; defer
  the actual output-copy loop.

## 2026-07-29 — finite phase control and middle-alphabet bridge

- **Starting commit:** `bf3487b76ecac4875a2b2721e4400fe6495fe8f5`
- **Goal:** define the finite control types and checked alphabet conversion
  needed before either component program can be injected into one sequential
  machine.
- **Checked increment:** added `ControlLabel` with disjoint left, transfer, and
  right phases; finite `ControlState` with phase-tagged component states and an
  optional canonical middle-alphabet symbol; total component-state projections
  with injection round trips; and `middleAlphabetEquiv`, which composes the
  first witness's output equivalence with the inverse of the second witness's
  input equivalence. Added bridge round-trip theorems and label-separation
  proofs.
- **Files:** `LeanNPHardness/MachineControl.lean`,
  `LeanNPHardness/Audit.lean`, `LeanNPHardness.lean`, `README.md`,
  `THEOREM_STATUS.md`, and this journal.
- **Successful checks:** targeted control-module build passed; full
  `lake build` passed 1,135 jobs. `#print axioms` reports only `propext` and
  `Quot.sound` for `middleAlphabetEquiv_symm_apply_apply`. The project scan
  found no `sorry`, `admit`, project-defined `axiom`, or `unsafe`;
  `proof_wanted` remains only in the explanatory dependency-boundary comment.
- **Failed approaches/blockers:** simplification did not prove that a nested
  right-component label differs from the nested transfer label. Injecting the
  outer `Sum.inr` equality and eliminating the resulting impossible inner
  `Sum.inr = Sum.inl` equality closed the proof. No other implementation route
  failed.
- **Useful API discovery:** `FinTM2` requires only its input-stack alphabet to
  be finite; its output alphabet need not expose `Fintype`. Transfer state
  should therefore hold an `Option` symbol from the shared `FinEncoding`
  alphabet, whose finiteness is available, rather than a private output-stack
  symbol. The executable bridge is exactly
  `first.outputAlphabet.trans second.inputAlphabet.symm`.
- **Ending state:** the combined machine now has checked finite phase labels,
  finite phase state, and a reversible middle-symbol bridge. No component
  statement has yet been rewritten to use those control types, and no transfer
  loop or runtime result is claimed.
- **Best next experiment:** define a phase-preserving left-control statement
  and program lift, using `leftStateValue` to totalize state-dependent
  operations, and prove an exact one-step simulation from a left-phase
  configuration. Keep `halt` unchanged in that lemma; introduce the
  halt-to-transfer transition only in a later sequential variant.

## 2026-07-30 — first-component combined-control simulation

- **Starting commit:** `7169f0588d58c42f73f5a01a39e2d76add95cc78`
- **Goal:** inject the first machine's statements, configurations, and program
  into the combined stack, label, and state types and prove exact one-step
  preservation without yet changing halting behavior.
- **Checked increment:** added `liftLeftControlStmt`, which rewrites every stack
  index, state-dependent operation, branch, and jump into combined control;
  `liftLeftControlCfg`; total `liftLeftControlProgram`; and the
  `liftLeftControl_stepAux` and `liftLeftControl_step` simulation theorems.
  The lift deliberately maps `halt` to `halt`, isolating phase-preserving
  correctness from the later sequential halt-to-transfer transition.
- **Files:** `LeanNPHardness/MachineControlSimulation.lean`,
  `LeanNPHardness/Audit.lean`, `LeanNPHardness.lean`, `README.md`,
  `THEOREM_STATUS.md`, and this journal.
- **Successful checks:** targeted control-simulation build passed; full
  `lake build` passed 1,136 jobs. `#print axioms` reports only `propext` and
  `Quot.sound` for `liftLeftControl_step`. The project scan found no `sorry`,
  `admit`, project-defined `axiom`, or `unsafe`; `proof_wanted` remains only in
  the explanatory dependency-boundary comment.
- **Failed approaches/blockers:** the final program-step rewrite initially
  failed because the total program still contained a match on
  `leftLabel first second label`; unfolding `leftLabel` exposed `Sum.inl` and
  reduced the match. No statement-constructor proof failed.
- **Useful API discovery:** `leftStateValue` makes all lifted state functions
  total by returning the first machine's declared initial state outside the
  left phase. On an injected `leftState`, its round-trip simp theorem reduces
  every `push`, `peek`, `pop`, `load`, branch, and jump exactly to the original
  operation. A phase-preserving halt theorem can therefore be proved before
  introducing any sequential behavior.
- **Ending state:** the first component now executes exactly inside the full
  combined control types. The second component still has only the earlier
  stack-level simulation; transfer control, multi-step correctness, and
  runtime bounds remain pending.
- **Best next experiment:** implement the symmetric phase-preserving
  right-control statement, configuration, and total-program lift with exact
  one-step simulation. Reuse the explicit `rightLabel` unfolding at the final
  program match, then begin a separate left-halt-to-transfer variant.

## 2026-08-02 — second-component combined-control simulation

- **Starting commit:** `a28b57f2eba67abdfb175d134f683399ac525cd9`
- **Goal:** complete the symmetric phase-preserving injection of the second
  machine into the combined stack, label, and state types before introducing
  transfer behavior.
- **Checked increment:** added `liftRightControlStmt`, which rewrites every
  second-machine stack index, state-dependent operation, branch, and jump into
  combined control; `liftRightControlCfg`; total
  `liftRightControlProgram`; and the `liftRightControl_stepAux` and
  `liftRightControl_step` simulation theorems. Like the left lift, the
  construction preserves `halt`, keeping transfer semantics separate.
- **Files:** `LeanNPHardness/MachineControlSimulation.lean`,
  `LeanNPHardness/Audit.lean`, `README.md`, `THEOREM_STATUS.md`, and this
  journal.
- **Successful checks:** targeted control-simulation and audit builds passed;
  full `lake build` passed 1,136 jobs. `#print axioms` reports only `propext`
  and `Quot.sound` for `liftRightControl_step`. The Lean-source scan found no
  `sorry`, `admit`, project-defined `axiom`, or `unsafe`; `proof_wanted`
  occurs only in the explanatory dependency-boundary comment.
- **Failed approaches/blockers:** the first final-step proof did not unfold
  `liftRightControlProgram`, so rewriting with `liftRightControl_stepAux`
  could not match the target. Adding that definition to the explicit
  simplification list reduced the nested injected label and closed the proof.
  No transfer or runtime blocker was attempted in this increment.
- **Useful API discovery:** unfolding `rightLabel` alone exposes the nested
  `Sum.inr (Sum.inr label)`, but the total program match still needs
  `liftRightControlProgram` unfolded explicitly. Once reduced, all statement
  cases follow the left proof with `rightStateValue_rightState` and
  `rightStacks_update`.
- **Ending state:** both component programs now have exact, checked one-step
  simulations in the full combined control types. Transfer control,
  multi-step correctness, and polynomial runtime bounds remain pending.
- **Best next experiment:** define a separate first-program lift that changes
  only `halt` into a jump to `transferLabel`, then prove that non-halting
  statements still simulate the first machine and that a halting statement
  enters a canonical transfer configuration. Do not combine output copying or
  runtime accounting into that first transfer increment.
