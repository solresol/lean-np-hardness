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
