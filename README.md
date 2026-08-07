# NP-hardness foundations in Lean

This repository develops reusable Lean 4 foundations for formal complexity
theory: polynomial-time many-one reductions, P and NP, NP-hardness,
NP-completeness, Boolean satisfiability, and eventually a kernel-checked
Cook--Levin theorem.

It is intentionally independent of any one downstream theorem. The first
consumer is expected to be the formalisation of fixed-prime p-adic regression
hardness, but the definitions and theorems here should support unrelated
reductions as well.

## Why this repository exists

Mathlib already provides:

- finite encodings;
- finite two-stack Turing machines;
- bounded-time computation; and
- a structure for polynomial-time computation.

It does not yet provide a complete reusable chain from encoded languages
through P, NP, polynomial-time many-one reduction, and Cook--Levin. At the
pinned revision, even the composition declaration for polynomial-time
machines is marked `proof_wanted`.

This repository treats that gap as a standalone formalisation project rather
than hiding it inside a downstream NP-hardness proof.

## Current status

The initial checked layer contains:

- `Language`, a predicate on an input type;
- `ManyOneReduction`, with identity and composition proved semantically;
- `PolytimeManyOneReduction`, tied directly to mathlib's
  `FinEncoding` and `TM2ComputableInPolyTime`;
- a polynomial-time identity reduction;
- composition from an explicit verified machine-composition witness, with
  unconditional left- and right-identity special cases; and
- checked lifts of both finite machines into the two sides of a disjoint-union
  stack layout, including exact one-step simulations, finite phase control,
  the checked intermediate-alphabet equivalence, and exact simulations of
  both components after injection into the combined control types; and
- a checked first-program variant that preserves continuing steps and
  redirects a reached halt to a canonical transfer-labelled configuration;
  and
- finite reverse-output/fill-input transfer phases plus a scratch-extended
  stack layout over the canonical middle alphabet, with checked update lemmas
  for both component stack embeddings; and
- a generic checked statement and configuration lift that runs any combined
  control program unchanged in the scratch-extended layout while preserving
  arbitrary scratch contents; and
- finite symbol-carrying reverse-transfer actions with checked nonempty and
  empty two-step iterations from the first output stack onto scratch storage;
  and
- finite symbol-carrying fill-transfer actions with checked nonempty and empty
  two-step iterations from scratch into the second input stack, including the
  checked transition to the second machine's initial control configuration;
  and
- exact whole-list fill-input execution in `2 * scratch.length + 2` steps,
  preserving an existing second-input accumulator and proving the resulting
  converted-list order.

The generic polynomial-time composition theorem, P, NP, SAT, exact 3-SAT, and
Cook--Levin remain pending. See [THEOREM_STATUS.md](THEOREM_STATUS.md) and
[ROADMAP.md](ROADMAP.md).

## Toolchain

The repository initially shares its toolchain with `phd-thesis-lean`:

- Lean `v4.27.0-rc1`;
- mathlib commit `cd479940d5ab509f094f7e55ed6433b5aaa37870`.

Build with:

```sh
lake exe cache get
lake build
```

The default target builds the complete `LeanNPHardness` library, including
the axiom-audit module.

## Related formalisation projects

### [`solresol/phd-thesis-lean`](https://github.com/solresol/phd-thesis-lean)

This Lean companion proves the concrete mathematical reduction from 3-SAT to
signed affine regression at `p = 5`, including semantic equivalence and
polynomial unit-cell size bounds. It currently lacks the reusable Lean
complexity-theory foundation that this repository is intended to supply.

### [`solresol/phd-thesis-coq`](https://github.com/solresol/phd-thesis-coq)

This Coq repository now proves the complete fixed-prime signed-regression
NP-hardness theorem. It imports the Saarland formal Cook--Levin theorem,
implements the regression compiler, verifies concrete `5`-adic semantics and
polynomial runtime, and composes the resulting reduction with exact 3-SAT
hardness.

Its architecture is a valuable guide, but Coq proof terms are not consumed by
the Lean kernel.

### Mathlib

This project uses mathlib's current `FinEncoding`, finite Turing-machine, and
`TM2ComputableInPolyTime` definitions rather than creating an unrelated cost
model. Any generally useful results should be designed with eventual upstream
contribution in mind.

## Completion policy

A headline theorem is complete only when:

- the relevant source and target languages have explicit encodings;
- the reduction is implemented by a checked polynomial-time machine;
- semantic correctness holds in both directions;
- all needed reduction composition is proved;
- no hardness fact is supplied as an undeclared external premise; and
- `#print axioms` reveals no project-defined assumption or unfinished proof.

The repository is public, but no licence has yet been selected.
