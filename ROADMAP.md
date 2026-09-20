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
  At-most-three to exact-three padding now has checked semantics and a linear
  encoded-output bound in `CNFNormalization`; its TM2 runtime and the
  arbitrary-width SAT transformation remain pending.
- Prove exact 3-SAT belongs to NP.
  Finite certificates and their bit bound are checked. `BinaryEqualityMachine`
  now supplies a linear-time equality kernel on separate Boolean stacks;
  `PreservingBinaryEqualityMachine` adds query restoration with an exact
  linear runtime. `FrameExtractionMachine` now extracts one framed value in
  original bit order, preserving the query and remaining input with exact
  linear runtime. `FrameComparisonMachine` now connects both kernels under
  one finite dispatcher, with exact summed runtime and preserved query and
  unread suffix. `CertificateCountMachine` now loads the outer framed binary
  list count onto a dedicated stack and selects the zero/nonzero continuation
  without consuming it, with exact linear runtime. `CertificateComparisonMachine`
  now lifts framed comparison into that same seven-stack layout with unchanged
  exact cost, retaining the count, query, and unread suffixes. Its list-head
  interface preserves every remaining frame, including repetitions.
  `CertificatePredecessorMachine` now consumes the retained count and writes
  its saturated predecessor onto `candidate` in at most `2b + 3` steps for
  `b` count bits, preserving query, unread input, the `count` stack, and output.
  `CertificateCountTransferMachine` now transfers that result through scratch
  back to `remaining` in original order in exactly `2p + 2` steps for `p`
  result bits, bounded by `2b + 2`. `CertificateDecrementMachine` now combines
  predecessor execution and ordered transfer under one finite dispatcher,
  proving in-place saturated decrement in at most `4b + 5` steps while
  retaining all traversal data. Header dispatch, repeated comparison and
  membership accumulation, literal/formula evaluation,
  and exact-width checking remain to be connected in a polynomial-time TM2
  verifier.

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

## Milestone 6: Palomar registration

Long-term publication target: register one or more research-level results from
this repository in [Palomar](https://palomar-registry.org/) once the relevant
foundations and headline theorems are mature. Palomar records an individual
result at an immutable public-repository commit rather than registering a
repository as a whole.

- Select a self-contained headline theorem with a concise informal account.
- Expose the statement in a small, readable `Challenge.lean` module and the
  proved declaration in a matching `Solution.lean` module.
- Add the Comparator configuration, `formalization.yaml`, and a root licence,
  with accurate provenance, automation, review, and limitation disclosures.
- Pass the full build, unfinished-proof scan, axiom audit, and Palomar's
  Comparator checks.
- Commit and push the exact public snapshot before submission.

This milestone records a future target; it does not claim that the repository
has been submitted to or registered by Palomar.

## Non-goals for the initial foundation

- Reproducing every theorem in the Coq Undecidability Library.
- Defining a second p-adic mathematics library.
- Treating raw source-code operation counts as polynomial Turing time.
- Calling a conditional hardness theorem an end-to-end NP-hardness proof.
