# Proving a reduction NP-hard with this library

This guide records the pattern used for Cook--Levin, exact 3-SAT, and
Max-Cut, so that downstream projects (for example `phd-thesis-lean`) can
transfer hardness to their own problems.

## 1. Pick the source language

| Source | Theorem | Encoding |
| --- | --- | --- |
| CNF-SAT | `UnaryNPComplete.encodedUnarySAT_NPComplete` | unary-index CNF |
| Exact 3-SAT | `UnaryNPComplete.encodedUnaryExactThreeSAT_NPComplete` | unary-index CNF |
| Max-Cut | `UnaryNPComplete.encodedUnaryMaxCut_NPComplete` | unary-index graph formula |
| CNF-SAT | `SatVerify.encodedSAT_NPComplete` | binary (`Formula.finEncoding`) |
| Exact 3-SAT | `ExactThreeVerify.encodedExactThreeSAT_NPComplete` | binary |
| Max-Cut | `MaxCutVerify.encodedMaxCut_NPComplete` | binary |

Prefer the unary sources when the target's size depends on the number of
variables or vertices: in the unary-index encoding every index is at most
the input length, while a binary index can be exponentially larger than its
encoding. Exact 3-SAT under the unary encoding still contains formulas of
any width; when a construction needs width three, compose with the chain
reduction (`ChainMachine.computableInPolyTime`) as `MaxCutMachine.satReduction`
does, and use `exactWidth_chainThree`.

## 2. Prove the semantics separately

State the map `f : α → β` and prove `source x ↔ target (f x)`, restricted to
the inputs the composition can produce (for instance exact-width formulas).
Keep this file free of machines; see `CNFChain.lean` and `MaxCutSpec.lean`.

## 3. Build the machine

If the output is a CNF-like symbol stream (formulas, or graphs encoded as
two-literal clauses), write an interpreter *job*: one fixed instruction
chunk per input symbol, with registers (`base`, `win`, `w`, `pw`) for fresh
indices, offsets, the constant one, and accumulated counts. Prove
`render initRegs (job (encode x)) = targetEncode (f x)` by telescoping, as
in `ChainJob.render_out` and `MaxCutJob.render_out`. The machine is then the
template of `ChainMachine.lean` (input loop, interpreter, drains), with the
step bound from `TableauJobs.interpSteps_le` and `render_fst_length_le`.

For other outputs, write routines with the combinators of `MachineRoutine`
and `MachineRoutineBound`:

- state each component lemma on an arbitrary stack family `S` with
  hypotheses on the stacks it touches, and give the result as a
  `Function.update` chain;
- prove loops by induction on the data with `loop_exitsLE_nil` and
  `loop_exitsLE_cons`, and bound costs with `Routine.ExitsLE`;
- close state equalities with `funext k; cases k <;> simp [...]`;
- give intermediate states explicitly to induction hypotheses, and keep the
  `seq` nesting of a routine identical to the nesting used in its proof.

Package the run with `Routines.toMachine_outputsInTime_le` (or
`TableauStacks.toGenMachine_outputsInTime` for the generator stack family)
and `MachinePrimitives.evalsToInTimeMono`.

## 4. Transfer hardness

Build `source.PolytimeReducesTo target` from the semantics and the machine;
compose machines with `MachineComposition.compositionComputableInPolyTime`;
conclude with `EncodedLanguage.NPHard.of_reduction`. NP membership transports
backward with `EncodedLanguage.InNP.of_reduction`.
