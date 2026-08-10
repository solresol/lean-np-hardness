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

## 2026-08-03 — checked left-halt transition into transfer control

- **Starting commit:** `1e90d19f6c58deec211e7e878ca439ae5bf38ac8`
- **Goal:** implement the previously isolated control transition from a
  completed first-machine statement into the transfer phase, without yet
  claiming output copying or runtime composition.
- **Checked increment:** added `liftLeftThenTransferStmt`, which differs from
  the phase-preserving lift only by redirecting reached `halt` leaves to
  `transferLabel`; `liftLeftThenTransferCfg` and `leftTransferEntryCfg`; the
  exact statement theorem `liftLeftThenTransfer_stepAux`; and the program
  theorem `liftLeftThenTransfer_step` with separate running and halted
  corollaries. Continuing steps reduce to `liftLeftControlCfg`, while a
  halting result enters the canonical transfer-labelled configuration with
  the injected first-machine state and stacks.
- **Files:** `LeanNPHardness/MachineControlSimulation.lean`,
  `LeanNPHardness/Audit.lean`, `README.md`, `THEOREM_STATUS.md`, and this
  journal.
- **Successful checks:** targeted control-simulation and audit build passed;
  full `lake build` passed 1,136 jobs. `#print axioms` reports only `propext`
  and `Quot.sound` for `liftLeftThenTransfer_step` and
  `liftLeftThenTransfer_step_of_halt`. The Lean-source scan found no `sorry`,
  `admit`, project-defined `axiom`, or `unsafe`; `proof_wanted` occurs only in
  the explanatory dependency-boundary comment.
- **Failed approaches/blockers:** no proof route failed in this increment.
  The Coq comparison development composes its reduction at the library
  relation level and does not provide evidence for this mathlib-specific
  machine construction. The new combined program deliberately still halts if
  the transfer label itself is stepped: transfer execution and its runtime
  remain unimplemented.
- **Useful API discovery:** because `TM2.stepAux` evaluates a whole statement
  tree in one counted step, recursively replacing `halt` gives one exact
  theorem covering nested branches; no static no-halt predicate is needed.
  Mathlib's `TMToPartrec.move₂` preserves stack order using a dedicated
  reversal stack and two moves, indicating that the generic middle-output
  transfer will need explicit scratch storage rather than a single direct
  source-to-target move.
- **Ending state:** execution of the first component can now continue at an
  injected left label or enter transfer control on halt, with both cases
  machine-checked and audited. No middle symbols are copied yet.
- **Best next experiment:** define finite scratch-stack and two-stage transfer
  control types sufficient for an order-preserving copy. First prove that the
  existing left and right stack injections still embed into the extended
  layout; defer the transfer loop and multi-step runtime proof until those
  structural lemmas build.

## 2026-08-04 — two-stage transfer control and scratch-stack embedding

- **Starting commit:** `d56e608fa83fac95d89ae9ceac17b8173242909d`
- **Goal:** add the finite control and stack structure needed for an
  order-preserving intermediate-output copy, while deferring the copy loop and
  runtime proof.
- **Checked increment:** replaced the single transfer label payload with finite
  `TransferPhase.reverseOutput` and `TransferPhase.fillInput` stages, preserving
  `transferLabel` as the entry stage and adding the distinct `fillInputLabel`.
  Added `TransferStackIndex` and `TransferStackAlphabet`, which extend the two
  component stack families with one scratch stack over the shared middle
  alphabet. Added first- and second-machine embeddings, their projection
  lemmas, the generic `extendStacks_update` theorem, and checked
  `transferLeftStacks_update` and `transferRightStacks_update` corollaries.
- **Files:** `LeanNPHardness/MachineControl.lean`,
  `LeanNPHardness/MachineTransfer.lean`, `LeanNPHardness/Audit.lean`,
  `LeanNPHardness.lean`, `README.md`, `THEOREM_STATUS.md`, and this journal.
- **Successful checks:** targeted transfer, control-simulation, and audit build
  passed 1,135 jobs; full `lake build` passed 1,137 jobs. The new axiom audits
  report only `propext` and `Quot.sound` for the label-separation and
  component-update theorems. The Lean-source scan found no `sorry`, `admit`,
  project-defined `axiom`, or `unsafe`; `proof_wanted` remains only in the
  explanatory dependency-boundary comment.
- **Failed approaches/blockers:** directly proving each nested component update
  by case-splitting the extended index left residual dependent
  `Function.update` goals. Factoring out the generic `extendStacks_update`
  theorem removed the duplicate nested reasoning and both corollaries then
  reduced by rewriting. No transfer execution or runtime result was attempted.
- **Useful API discovery:** mathlib's `TMToPartrec.move₂` performs an
  order-preserving move as two reversals through a dedicated scratch stack.
  Here the scratch alphabet can be the shared finite `FinEncoding` alphabet
  `Γ₁`; transfer state already holds `Option Γ₁`, so later steps can convert
  private output symbols into canonical symbols and then into private input
  symbols without identifying the component alphabets. The comparison Coq
  development constructs its concrete compiler reduction with
  `reducesPolyMO_intro` and composes at the reduction-relation level; it does
  not supply a reusable machine-stack transfer construction for this Lean API.
- **Ending state:** the combined control has two checked transfer stages and the
  component stacks have checked embeddings into a finite scratch-extended
  layout. The transfer statements, multi-step correctness, composed `FinTM2`,
  and polynomial runtime remain pending.
- **Best next experiment:** define a generic statement/configuration lift from
  `StackAlphabet` to `TransferStackAlphabet` that leaves the scratch stack
  untouched, and prove a one-step simulation. This should transport both
  existing component-control simulations to the final stack layout before the
  transfer loop is implemented.

## 2026-08-05 — generic scratch-stack program simulation

- **Starting commit:** `6473f3bc46d10d2ea34d8ca1009b612cda47ae5d`
- **Goal:** transport arbitrary combined-control statements and configurations
  into the scratch-extended stack layout without yet implementing the transfer
  loop.
- **Checked increment:** added `liftScratchStmt`, `liftScratchCfg`, and
  `liftScratchProgram`, together with exact statement- and program-step
  simulations `liftScratch_stepAux` and `liftScratch_step`. The configuration
  lift preserves an arbitrary scratch-stack value, so the theorem applies both
  before transfer (empty scratch) and around later phases with live scratch
  contents.
- **Files:** `LeanNPHardness/MachineTransfer.lean`,
  `LeanNPHardness/Audit.lean`, `README.md`, `THEOREM_STATUS.md`, and this
  journal.
- **Successful checks:** targeted transfer and audit builds passed; full
  `lake build` passed 1,137 jobs. `#print axioms` reports only `propext` and
  `Quot.sound` for `liftScratch_step`. `git diff --check` passed. The
  Lean-source scan found no `sorry`, `admit`, project-defined `axiom`, or
  `unsafe`; `proof_wanted` remains only in the explanatory
  dependency-boundary comment.
- **Failed approaches/blockers:** no proof route failed. The actual output-copy
  statement and its multi-step correctness were deliberately not attempted in
  this increment. The Coq comparison still supplies only relation-level
  composition, not this mathlib-specific machine construction.
- **Useful API discovery:** `TM2.stepAux` again permits a constructor-by-
  constructor simulation, and `extendStacks_update` is sufficient for both
  dependent update cases. For the next transfer loop, `FinEncoding` supplies a
  `Fintype` alphabet but not an arbitrary inhabitant. A statement that branches
  on `Option Γ₁` therefore cannot totalize its later `push` writer by assuming a
  default symbol; a finite control label carrying the actual symbol is the
  cleaner route.
- **Ending state:** every existing combined-control program can now execute
  unchanged on the final scratch-extended stack family with an exact checked
  one-step theorem. Intermediate symbols are not yet copied and no runtime
  claim has been made.
- **Best next experiment:** introduce a finite transfer-action label carrying
  a canonical `Γ₁` symbol for push steps, then prove one reverse-output
  iteration for both nonempty and empty source stacks. This avoids an
  unjustified `Inhabited Γ₁` assumption and keeps the fill-input stage separate.

## 2026-08-06 — checked reverse-output transfer iteration

- **Starting commit:** `745b81a3f188e12060ffccbfba979740abcb9f25`.
- **Goal:** implement the first executable transfer loop increment: finite
  symbol-carrying control plus exact nonempty and empty reverse-output cases.
- **Checked increment:** added finite `TransferAction`, including a
  `reversePush (Option Γ₁)` action that needs no arbitrary middle-alphabet
  inhabitant; total transfer-state projection; generic scratch replacement;
  `reverseOutputStmt`, `reversePushStmt`, and the isolated
  `reverseOutputProgram`; and exact two-step theorems
  `reverseOutput_iteration_nonempty` and `reverseOutput_iteration_empty`.
  The nonempty case removes the first output head, converts it with
  `first.outputAlphabet`, and pushes it onto scratch. The empty case advances
  to `fillInput` without changing scratch.
- **Files:** `LeanNPHardness/MachineControl.lean`,
  `LeanNPHardness/MachineTransfer.lean`, `LeanNPHardness/Audit.lean`,
  `README.md`, `THEOREM_STATUS.md`, and this journal.
- **Successful checks:** targeted control, transfer, and audit builds passed;
  full `lake build` passed 1,137 jobs; `git diff --check` passed. The new axiom
  audits report `propext`, `Classical.choice`, and `Quot.sound`. The Lean-source
  scan found no `sorry`, `admit`, project-defined `axiom`, or `unsafe`;
  `proof_wanted` remains only in the existing explanatory comment.
- **Failed approaches/blockers:** initial label-separation simplification did
  not unfold the new nested action injection, so the proof now injects the
  `Sum` equality and the `TransferAction.phase` equality explicitly. Initial
  transfer-step simplification also left dependent `Function.update` terms;
  unfolding `transferLeftIndex` after `extendStacks_update` closed them. A
  scratch-update lemma oriented with an unconstrained old scratch value made
  rewriting ambiguous; orienting it from the explicit update to the extended
  stack and adding `extendStacks_scratch` removed the metavariable. The
  fill-input loop and multi-step whole-list theorem remain unimplemented.
- **Useful API discovery:** one `TM2.step` can pop and translate the source
  symbol, but a second label is required to push it because a state-dependent
  push writer must be total. Carrying `Option Γ₁` in the finite label handles
  both the concrete-symbol and exhausted-source cases without `Inhabited Γ₁`.
  Rechecking `phd-thesis-coq/theories/Hardness.v` confirmed that the comparison
  development still composes through `reducesPolyMO_intro` and `red_NPhard`; it
  provides no machine-stack copy proof for this mathlib API.
- **Ending state:** one reverse-output iteration is executable, checked, and
  audited for both source shapes. Repeated execution, the scratch-to-second-
  input phase, composed `FinTM2`, and polynomial runtime remain pending.
- **Best next experiment:** add a finite fill-input push action carrying the
  canonical scratch head, convert it with `second.inputAlphabet.symm`, and
  prove exact nonempty and empty two-step fill-input iterations. Then formulate
  whole-list reachability separately.

## 2026-08-07 — checked fill-input transfer iteration

- **Starting commit:** `5bcaa737ed38c260124506e1e0aad080c93edd5b`.
- **Goal:** implement the second executable transfer stage with exact
  nonempty and empty two-step behavior, without yet claiming whole-list
  reachability or a composed machine.
- **Checked increment:** added the finite symbol-carrying `fillPush` action,
  `fillInputStmt`, `fillPushStmt`, the complete two-stage `transferProgram`,
  and `rightEntryCfg`. Proved `fillInput_iteration_nonempty`, which pops the
  canonical scratch head, converts it with `second.inputAlphabet.symm`, and
  pushes it onto `second.tm.k₀`; and `fillInput_iteration_empty`, which resets
  the second state to `second.tm.initialState` and enters `second.tm.main`.
- **Files:** `LeanNPHardness/MachineControl.lean`,
  `LeanNPHardness/MachineTransfer.lean`, `LeanNPHardness/Audit.lean`,
  `README.md`, `THEOREM_STATUS.md`, and this journal.
- **Successful checks:** targeted transfer and audit builds passed; full
  `lake build` passed 1,137 jobs; `git diff --check` passed. The new axiom
  audits report `propext`, `Classical.choice`, and `Quot.sound` for the
  nonempty theorem, and `propext` and `Quot.sound` for the empty theorem. The
  Lean-source scan found no `sorry`, `admit`, project-defined `axiom`, or
  `unsafe`; `proof_wanted` remains only in the existing explanatory comment.
- **Failed approaches/blockers:** initially retaining the old program name as
  an abbreviation did not unfold the new dispatcher far enough in existing
  proofs; stating the iteration theorems directly over `transferProgram`
  exposed the concrete action cases. The scratch-pop goals also needed
  explicit list simplification, and the dependent second-stack push needed
  `transferRightIndex` exposed before applying `extendStacks_update`. No
  semantic or API blocker remains for this stage. Whole-list execution and
  runtime accounting are still unproved.
- **Useful API discovery:** `FinTM2.main` and `FinTM2.initialState` are exactly
  the control values required after transfer exhaustion. A canonical `Γ₁`
  symbol is converted to the private second-input alphabet by
  `second.inputAlphabet.symm`; two stack reversals therefore restore the
  original encoded-list order. Rechecking
  `phd-thesis-coq/theories/Hardness.v` again found only relation-level
  construction via `reducesPolyMO_intro` and `red_NPhard`, not a reusable
  machine-stack transfer proof.
- **Ending state:** both per-symbol transfer phases and both exhaustion
  transitions are executable, checked, and audited. The intermediate-output
  transfer loop remains pending until repeated whole-list execution is proved.
- **Best next experiment:** prove a whole-list `fillInput` reachability theorem
  by induction, with an exact `2 * scratch.length + 2` step count and an input
  accumulator; then prove the reverse-output whole-list theorem and combine
  them into the order-preserving transfer result.

## 2026-08-08 — exact whole-list fill-input execution

- **Starting commit:** `3f2ccabb51f9804e403ccb4b3046805e17c269db`.
- **Goal:** lift the checked two-step fill-input iterations to an exact
  whole-list execution theorem while preserving an existing second-input
  accumulator.
- **Checked increment:** added `fillInput_whole_list`. For arbitrary scratch
  contents, it proves that iterating the lifted transfer step exactly
  `2 * scratch.length + 2` times empties scratch, enters the second machine's
  initial control configuration, and replaces its input stack by
  `(scratch.map second.inputAlphabet.symm).reverse ++ input`. The theorem is
  proved by list induction using the existing nonempty and exhaustion
  iterations, so it records both execution and output order.
- **Files:** `LeanNPHardness/MachineTransfer.lean`,
  `LeanNPHardness/Audit.lean`, `README.md`, `THEOREM_STATUS.md`, and this
  journal.
- **Successful checks:** a standalone proof probe passed; targeted transfer
  and audit builds passed; full `lake build` passed 1,137 jobs;
  `git diff --check` passed. `#print axioms` reports only `propext`,
  `Classical.choice`, and `Quot.sound` for `fillInput_whole_list`. The
  Lean-source scan found no `sorry`, `admit`, project-defined `axiom`, or
  `unsafe`; `proof_wanted` remains only in the existing explanatory comment.
- **Failed approaches/blockers:** no proof route failed. An exploratory API
  check confirmed that this pinned mathlib has no `Function.update_same`
  theorem under that name, but the induction does not need it. The full
  order-preserving transfer theorem remains pending on the symmetric
  reverse-output whole-list execution result.
- **Useful API discovery:** `Function.iterate_add_apply` composes the exact
  two-step iteration with the induction hypothesis in the needed order.
  `List.reverse_cons` and associativity then normalize the accumulator result.
  Rechecking `phd-thesis-coq/theories/Hardness.v` found only relation-level
  construction through `reducesPolyMO_intro` and `red_NPhard`, not a reusable
  machine-stack transfer proof for this mathlib API.
- **Ending state:** whole-list fill-input execution is machine-checked,
  documented, and audited; the broader intermediate-output transfer loop and
  composed machine remain pending.
- **Best next experiment:** prove an exact whole-list reverse-output theorem
  with source and scratch accumulators, yielding the converted source in
  reverse order on scratch after `2 * output.length + 2` steps. Then compose it
  with `fillInput_whole_list` to obtain the first complete order-preserving
  transfer theorem and its summed exact step count.

## 2026-08-09 — exact whole-list reverse-output execution

- **Starting commit:** `d675fe391b9f19684d90a983082e87d6d0bf5a1c`.
- **Goal:** lift the checked two-step reverse-output iterations to an exact
  whole-list execution theorem while preserving existing scratch contents.
- **Checked increment:** added `reverseOutput_whole_list`. For an arbitrary
  first-output list and scratch accumulator, it proves that iterating the
  transfer step exactly `2 * output.length + 2` times empties the first output
  stack, enters `fillInput`, and produces
  `(output.map first.outputAlphabet).reverse ++ scratch`. The theorem is proved
  by list induction from the existing nonempty and exhaustion iterations.
- **Files:** `LeanNPHardness/MachineTransfer.lean`,
  `LeanNPHardness/Audit.lean`, `README.md`, `THEOREM_STATUS.md`, and this
  journal.
- **Successful checks:** targeted transfer and audit build passed 1,135 jobs;
  full `lake build` passed 1,137 jobs; `git diff --check` passed.
  `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`
  for `reverseOutput_whole_list`. The Lean-source scan found no `sorry`,
  `admit`, project-defined `axiom`, or `unsafe`; `proof_wanted` remains only in
  the existing explanatory dependency-boundary comment.
- **Failed approaches/blockers:** no proof route failed. The complete
  order-preserving transfer theorem remains pending on composing this result
  with `fillInput_whole_list`; the composed `FinTM2` and polynomial runtime
  remain later blockers.
- **Useful API discovery:** the same `Function.iterate_add_apply` decomposition
  used by the fill-input proof composes each exact two-step reverse iteration
  with the induction hypothesis. `List.reverse_cons` and append associativity
  normalize the scratch accumulator without an auxiliary list lemma.
  Rechecking `phd-thesis-coq/theories/Hardness.v` found only relation-level
  construction through `reducesPolyMO_intro` and `red_NPhard`, not a reusable
  whole-list machine-transfer proof for this mathlib API.
- **Ending state:** both transfer phases now have exact whole-list execution
  theorems with accumulator and step-count specifications, but the combined
  order-preserving theorem is not yet claimed.
- **Best next experiment:** compose `reverseOutput_whole_list` with
  `fillInput_whole_list`, simplifying the two reversals and both alphabet
  equivalences to prove that a source output list is prepended in its original
  order to the second input stack with the summed exact step count.

## 2026-08-10 — complete order-preserving intermediate transfer

- **Starting commit:** `2a95106fdfa11258046ce9457d65536407942def`.
- **Goal:** compose the two checked whole-list transfer phases into one exact,
  order-preserving intermediate-output theorem.
- **Checked increment:** added `transfer_whole_list`. Starting with empty
  scratch storage, it consumes the first output stack, converts its symbols
  through `middleAlphabetEquiv`, prepends them in their original order to the
  existing second input stack, empties scratch, and enters the second machine's
  initial control configuration in exactly `4 * output.length + 4` steps.
- **Files:** `LeanNPHardness/MachineTransfer.lean`,
  `LeanNPHardness/Audit.lean`, `README.md`, `THEOREM_STATUS.md`, and this
  journal.
- **Successful checks:** direct transfer-module checking passed; targeted
  transfer and audit build passed 1,135 jobs; full `lake build` passed 1,137
  jobs; `git diff --check` passed. `#print axioms` reports only `propext`,
  `Classical.choice`, and `Quot.sound` for `transfer_whole_list`. The
  Lean-source scan found no `sorry`, `admit`, project-defined `axiom`, or
  `unsafe`; `proof_wanted` remains only in the existing explanatory comment.
- **Failed approaches/blockers:** implicit inference for the dependent
  `Function.update_comm` call selected `Type` as the index; explicitly naming
  the two disjoint `Sum` indices fixed it. The first phase theorem retained a
  syntactic `scratch ++ []`, so a typed `simpa` intermediate was needed before
  rewriting with `fillInput_whole_list`. Running the audit directly before
  rebuilding the transfer module read its stale `.olean` and could not find
  the new declaration; the targeted Lake build refreshed dependencies. Generic
  machine construction and polynomial runtime accounting remain pending.
- **Useful API discovery:** `Function.iterate_add_apply` composes the fill
  phase after the reverse phase when the total count is written as fill steps
  plus reverse steps. `Function.update_comm` works for the dependent stack
  family once both distinct indices are explicit. `List.map_reverse`,
  `List.map_map`, and the definition of `middleAlphabetEquiv` reduce the two
  reversals and alphabet conversions to the order-preserving map. The Coq
  comparison still composes `reducesPolyMO` through its higher-level
  `polyTimeComputable` relation and provides no corresponding TM2 stack-copy
  proof.
- **Ending state:** the intermediate-output transfer loop is complete,
  machine-checked, documented, and audited. A total composed `FinTM2`, its
  multi-step component simulation, and its polynomial runtime bound remain.
- **Best next experiment:** define the final scratch-layout program that
  dispatches left labels through the halt-to-transfer lift, transfer labels
  through `transferProgram`, and right labels through the right-control lift.
  First prove exact one-step simulations for the left and right dispatch cases;
  defer the `FinTM2` runtime witness until that total program builds.

## 2026-08-11 — total composition program and finite machine

- **Starting commit:** `516000d93cafcab18e084b67fb787c9244fb0a50`.
- **Goal:** assemble the checked component and transfer programs on the final
  scratch layout, then verify exact left- and right-phase dispatch before
  attempting whole-computation or runtime proofs.
- **Checked increment:** added `compositionProgram`, a total dispatcher for
  left, transfer-action, and right labels; `compositionMachine`, the resulting
  finite machine with the first input and second output stacks exposed; and
  `compositionAux`, which records the external alphabet equivalences without
  claiming computation or runtime. Proved the pointwise dispatch lemmas and
  exact `compositionProgram_left_step` and `compositionProgram_right_step`
  simulations, preserving arbitrary scratch contents.
- **Files:** `LeanNPHardness/MachineCompositionProgram.lean`,
  `LeanNPHardness/Audit.lean`, `LeanNPHardness.lean`, `README.md`,
  `THEOREM_STATUS.md`, and this journal.
- **Successful checks:** targeted program and audit builds passed; full
  `lake build` passed 1,138 jobs; `git diff --check` passed. Axiom audit reports
  `propext`, `Classical.choice`, and `Quot.sound` for `compositionAux`, and only
  `propext` and `Quot.sound` for both component-step theorems. The Lean-source
  scan found no `sorry`, `admit`, project-defined `axiom`, or `unsafe`;
  `proof_wanted` remains only in the existing explanatory comment.
- **Failed approaches/blockers:** after rewriting with the two existing
  statement simulations, Lean retained explicit configuration structure on one
  side of each component-step goal; a final definitional `rfl` closed both.
  No semantic blocker was encountered. Whole-run component simulation,
  transfer execution under the total dispatcher, and polynomial runtime remain
  unproved.
- **Useful API discovery:** the final machine requires only `[Fintype Γ₁]`,
  which is available from the shared middle `FinEncoding`; the input-stack
  finiteness field reduces definitionally to `first.tm.Γk₀Fin`. Transfer actions
  can be delegated definitionally to `transferProgram`, while left and right
  statements reuse `liftScratchStmt`. The Coq comparison still composes via
  `reducesPolyMO_intro` and `polyTimeComputable`, and pinned mathlib still marks
  `TM2ComputableInPolyTime.comp` as `proof_wanted`, so neither supplies Lean
  evidence for this machine layer.
- **Ending state:** the full finite machine structure now builds and both
  component phases have exact one-step semantics under its total program. No
  claim yet states that `compositionAux` computes function composition or has a
  polynomial runtime.
- **Best next experiment:** transport `transfer_whole_list` from
  `transferProgram` to `compositionProgram` by proving that every reachable
  transfer-action configuration takes the same next step. Then lift the left
  and right one-step simulations to exact repeated execution before combining
  the phase runtimes.
