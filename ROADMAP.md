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
  retaining all traversal data. `CertificateStepMachine` now connects framed
  comparison to in-place decrement under one finite dispatcher with exact
  summed cost bounded by `2q + 2f + 4b + 8` for query/frame/count bit lengths.
  It retains equality on output, preserves the query and unread frames,
  and restores the exact tail count after one certificate entry.
  `CertificateMembershipStepMachine` now ORs each equality bit with the
  supplied prior accumulator at that continuation in one further step,
  bounding the combined run by `2q + 2f + 4b + 9` while preserving the query,
  exact tail count, unread frames, and output suffix. `CertificateMembershipLoopMachine`
  now repeats that step under finite count-controlled dispatch, proving exact
  execution over the complete canonical body and membership-accumulator semantics.
  It preserves the query and suffixes, consumes repetitions, and has bit-runtime
  bound `F * (2q + 4F + 11) + 2F + 1` for query/body bit lengths `q`/`F`.
  `CertificateMembershipMachine` now connects header extraction and false
  accumulator initialization to that loop under one finite dispatcher. It
  consumes the complete encoded certificate with exact summed cost, bounded
  by `N * (2q + 4N + 16) + 4` in query/full-certificate bit lengths `q`/`N`.
  `SerializedMembershipMachine` now loads a leading framed query and enters
  membership under one finite dispatcher, proving exact summed execution and
  bound `M * (4M + 19) + 7` in complete serialized input bits `M`. The query
  and input/output suffixes survive; count/work stacks finish empty.
  `CanonicalMembershipMachine` now drains the retained query and halts with
  initial control and every non-output stack empty. `outputsInTime` supplies
  canonical list output with bound `M * (4M + 20) + 9`, including cleanup and
  the final halt. `MembershipComputable` now proves the framed `Nat × List Nat`
  encoding round trip and packages this same machine as
  `CanonicalMembership.computableInPolyTime`, with polynomial
  `X * (4 * X + 20) + 9`. `BooleanCopyMachine` now restores a separately
  supplied certificate and provides an ordered working copy in exactly
  `2N + 2` steps for full certificate bit length `N`, preserving a target
  suffix and emptying scratch. `PreservingMembershipMachine` now connects
  copying and membership under one eight-stack dispatcher, preserving the
  complete backup, query, and input/output suffixes. Exact cost is copying
  plus one entry step plus membership, bounded by `N * (2q + 4N + 18) + 7`.
  `ReusableMembershipMachine` now loads one framed query, performs this lookup,
  and drains the query under one finite dispatcher. `whole_query` retains the
  complete backup and unread input/output suffixes, with query/count/work
  stacks empty at a live continuation. Exact execution is bounded by
  `N * (2q + 4N + 18) + 4q + 12` in raw query/full-certificate bit lengths.
  `QueryMembershipMachine` now adds a separate outer query-count stack;
  `lift_run` and `whole_query` preserve it with exactly the same lookup cost.
  `list_head` retains the original outer count and all unread query frames,
  including repetitions. Loading/decrementing that count and connecting
  repeated-query control remain pending.
  Loading the dedicated certificate stack, dispatching repeated queries,
  literal/formula evaluation, and exact-width checking remain to be assembled
  in a polynomial-time TM2 verifier.

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
