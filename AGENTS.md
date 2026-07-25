# Repository working instructions

## Purpose

This repository develops reusable Lean 4 foundations for machine-checked
complexity theory, NP-hardness, and eventually Cook--Levin and concrete
NP-complete problems.

The intended progression is:

1. encoded languages and semantic many-one reductions;
2. polynomial-time machines and compositional polynomial reductions;
3. P, verifier-based NP, NP-hardness, and NP-completeness;
4. Boolean formulas, CNF-SAT, and exact 3-SAT;
5. a kernel-checked Cook--Levin theorem; and
6. adapters for downstream formalisation projects.

Do not describe a milestone as complete until its Lean declarations build and
its axiom audit is recorded.

## Related repositories

- `../phd-thesis-lean` proves the mathematical correctness of a concrete
  `p = 5` reduction from 3-SAT to signed affine regression.
- `../phd-thesis-coq` contains a completed Coq proof of the corresponding
  end-to-end NP-hardness theorem using the Saarland Coq complexity library.
- `../phd-thesis` owns the thesis prose and published claims.
- `https://github.com/leanprover-community/mathlib4` supplies the finite
  encodings and Turing-machine API on which this project currently builds.

The Coq development is a design oracle and comparison target, not a trusted
Lean dependency. Do not edit sibling repositories unless the current task
explicitly includes them.

## Proof standards

- Do not use `sorry`, `admit`, project-defined axioms, or `unsafe` declarations
  in completed foundations.
- Treat declarations marked `proof_wanted` in dependencies as unfinished.
  Depending on their proposition does not make the corresponding project
  milestone complete.
- Keep semantic correctness, executable encodings, runtime bounds, and
  hardness transfer as separately named results.
- State the computational model and encoded input-size measure explicitly.
- Preserve repeated variables, literals, clauses, and observations unless a
  proved normalization theorem justifies removing them.
- Audit headline results with `#print axioms`.
- Keep `THEOREM_STATUS.md` synchronized with the checked declarations.

## Working practice

- Run `lake build` and the unfinished-proof scan before committing.
- Commit and push completed, verified increments regularly.
- Keep `main` buildable. Record blockers precisely instead of replacing
  missing theory with hidden assumptions.
- Prefer small modules with explicit imports. Do not import the downstream
  thesis formalisation into the foundations library.
