# Architecture

## Typed languages

A language is initially a predicate `α → Prop`. Source and target input types
may differ, so reductions carry their input and output types explicitly.

Encoding is added at the polynomial-time layer rather than baked into the
semantic definition. This keeps elementary reduction algebra independent of a
particular machine model while ensuring that complexity claims use concrete
finite encodings.

## Semantic reductions

`ManyOneReduction A B` contains:

- a map from source instances to target instances; and
- an equivalence proving that the map preserves yes-instances and
  no-instances.

Identity and composition are purely logical and are already closed.

## Polynomial reductions

`PolytimeManyOneReduction eα eβ A B` additionally contains a
`TM2ComputableInPolyTime` witness for its map. It uses mathlib's finite
two-stack Turing machines and encoded input length.

At the pinned revision, mathlib's `TM2ComputableInPolyTime` is defined for
input and output types in `Type`, not arbitrary higher universes. The semantic
layer remains universe-polymorphic; the machine-backed layer deliberately
matches this universe-zero API.

The initial library proves identity directly. Composition is available only
when the caller supplies a checked polynomial-time witness for the composed
function. Closing this witness generically is the first substantial
formalisation milestone.

## Why composition comes first

NP-hardness developments are chains of reductions. Without a closed
composition theorem, every downstream theorem either repeats machine
plumbing or assumes the most important infrastructure result.

Mathlib describes the intended sequential machine construction, but the
corresponding declaration is marked `proof_wanted` at the pinned revision.
This repository treats its implementation as foundational work, not as an
available theorem.

## P and NP

The project should distinguish:

- a language;
- a decider or verifier as an ordinary Lean function;
- a finite encoding for every input and certificate type;
- a machine proving that function computable;
- a polynomial runtime bound; and
- the semantic theorem connecting the function to the language.

Certificate length must be explicitly polynomial in encoded input length.
Avoid definitions that make NP membership true merely because an
unconstrained witness exists.

## SAT and Cook--Levin

The base Boolean syntax should retain repeated literals and clauses.
Restricted conventions such as three distinct variables per clause require
verified normalization rather than an implicit change of source language.

The Cook--Levin development should separate:

1. machine normalisation;
2. bounded computation tableaux;
3. local Boolean constraints;
4. semantic correctness of the tableau encoding;
5. executable formula generation;
6. encoded output-size and runtime bounds; and
7. the final NP-hardness composition.

The completed Coq development in `../phd-thesis-coq` supplies a tested
decomposition and many useful proof ideas. Lean definitions should nevertheless
fit mathlib's APIs and idioms instead of mechanically transliterating Coq.

## Axiom policy

Every headline module should be imported by the default library target and
audited with `#print axioms`. Static scans reject unfinished project proofs.
Dependency axioms and classical principles should be reported, not silently
conflated with project-defined assumptions.
