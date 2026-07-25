# Roadmap

## Milestone 0: reduction core

- Define typed languages as predicates.
- Define semantic many-one reductions.
- Prove identity and composition.
- Bind polynomial reductions to mathlib `FinEncoding` and
  `TM2ComputableInPolyTime`.
- Prove polynomial-time identity.
- Prove a composition constructor from an explicit machine witness.

## Milestone 1: polynomial-time composition

- Audit mathlib's `FinTM2` and `TM2ComputableInPolyTime` APIs.
- Implement sequential composition of two finite machines.
- Prove the composed machine computes function composition.
- Construct and bound a polynomial runtime.
- Replace the current explicit-witness composition boundary with a closed
  `PolytimeManyOneReduction.comp`.
- Prepare the generally useful machine-composition result for upstreaming.

## Milestone 2: complexity classes

- Define encoded decision languages.
- Define deterministic polynomial-time decidability.
- Define verifier-based NP with an explicit polynomial certificate bound.
- Prove closure and transport lemmas required by reductions.
- Define NP-hardness and NP-completeness.
- Prove that polynomial reductions preserve membership in P and NP where
  appropriate.

## Milestone 3: satisfiability languages

- Define Boolean variables, literals, clauses, CNF formulas, and assignments.
- Preserve repeated literals and clauses in the base syntax.
- Define SAT and exact `k`-SAT as encoded languages.
- Implement and verify normalization between useful formula conventions.
- Prove exact 3-SAT belongs to NP.

## Milestone 4: Cook--Levin

- Select and document the verifier-machine normal form.
- Encode bounded accepting computations as Boolean constraints.
- Prove local consistency is equivalent to a valid accepting computation.
- Implement the formula generator.
- Prove its output size and runtime polynomial.
- Derive SAT NP-hardness and NP-completeness.
- Derive exact 3-SAT NP-completeness through a checked polynomial reduction.

## Milestone 5: downstream adapters

- Connect `phd-thesis-lean`'s concrete regression compiler to the common
  encoded exact-3-SAT language.
- Re-express its construction bound in the shared bit-level computational
  model.
- Compose it with exact 3-SAT hardness.
- Add further NP-hardness reductions without coupling them to thesis-specific
  mathematics.

## Non-goals for the initial foundation

- Reproducing every theorem in the Coq Undecidability Library.
- Defining a second p-adic mathematics library.
- Treating raw source-code operation counts as polynomial Turing time.
- Calling a conditional hardness theorem an end-to-end NP-hardness proof.
