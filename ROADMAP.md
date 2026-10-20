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

SAT and exact 3-SAT NP membership are now complete through the routine-based
verifiers in Milestone 4. The component-machine sequence below records the
earlier alternative implementation; its remaining assembly is not a blocker
for those membership results.

- Define Boolean variables, literals, clauses, CNF formulas, and assignments.
- Preserve repeated literals and clauses in the base syntax.
- Define SAT and exact `k`-SAT as encoded languages.
- Implement and verify normalization between useful formula conventions.
  At-most-three to exact-three padding now has checked semantics and a linear
  encoded-output bound in `CNFNormalization`; its standalone TM2 runtime
  remains pending. The arbitrary-width SAT transformation is complete through
  `ChainMachine` in Milestone 4.
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
  including repetitions. `QueryMembershipStepMachine` now connects lookup to
  outer decrement under one finite dispatcher, preserving backup, both suffixes,
  and the empty inner count/workspace. `list_head` restores the exact tail count;
  `whole_query` proves the exact sum including one entry step, bounded by
  `N * (2q + 4N + 18) + 4q + 4b + 18` for raw query/full-certificate/outer-count
  bit lengths `q`/`N`/`b`. `QueryMembershipLoopMachine` now repeats this step
  under finite count-controlled dispatch. `whole_list` consumes the complete
  canonical query body, preserves the certificate and both suffixes, emits
  membership bits in reverse query order, and empties count/workspace stacks.
  Exact `runSteps` counts every peek and return; the bit bound is
  `Q * (N * (2Q + 4N + 18) + 8Q + 20) + 1` in framed query-body/full-certificate
  bits `Q`/`N`. `EncodedQueryMembershipMachine` now loads the outer header
  and enters this loop in the extractor's final step. `whole_list` consumes
  the full canonical query encoding while retaining the certificate and both
  suffixes, with exact summed cost bounded by
  `M * (N * (2M + 4N + 18) + 8M + 23) + 4` in full framed query-list and
  certificate bits `M`/`N`. `SerializedQueryMembershipMachine` now loads a
  leading outer frame containing the complete certificate and enters that
  dispatcher in its final extraction step. `whole_input` consumes the serialized
  certificate and query list with initially empty backup/count/workspace,
  preserves the loaded certificate and both suffixes, and emits all membership
  bits in reverse query order. Exact summed execution is bounded by
  `S * (S * (2S + 18) + 8S + 26) + 7` in complete serialized bits `S`.
  `CanonicalQueryMembershipMachine` now drains the retained backup, resets
  control, and halts with every non-output stack empty. `whole_input` proves
  exact combined execution; `outputsInTime` gives canonical reverse membership
  output within `S * (S * (2S + 18) + 8S + 27) + 9` steps, including cleanup
  entry and the final halt. `QueryMembershipComputable` now proves the
  serialized `List Nat × List Nat` encoding round trip and exact bit length,
  and packages this machine as `CanonicalQueryMembership.computableInPolyTime`
  with raw Boolean-list output and polynomial
  `X * (X * (2 * X + 18) + 8 * X + 27) + 9`. Separate semantic lemmas retain
  one bit per query occurrence and identify reverse query order. This witness
  uses `FramedNatListQueries.finEncoding`; a conversion from the verifier's
  tagged pair encoding, serialized literal/formula evaluation, and exact-width
  checking remain to be assembled in a polynomial-time TM2 verifier.
  `LiteralEvaluationMachine` now retains a supplied negative-polarity bit
  through reusable framed lookup and applies conditional negation in one
  counted step. `whole_literal` proves agreement with `CNF.Literal.eval`
  under `Certificate.assignment`, with preserved backup and suffixes, empty
  workspace, and bound `N * (2q + 4N + 18) + 4q + 13` in raw variable bits
  `q` and full certificate bits `N`. `PackedLiteralMachine` now extracts the
  even/odd literal code and splits its low bit into finite control on five
  Boolean stacks. `head_encode_toNat` / `tail_encode_toNat` cover both signs
  and positive zero's empty payload. `whole_literal` preserves the unread
  input and arbitrary query contents, exposing the raw variable and emptying
  both work stacks in exactly `3b + 4` steps for packed payload bits `b`,
  bounded by `2L + 2` in the full literal frame length `L`.
  `PackedLiteralEvaluationMachine` now connects this loader directly to raw
  lookup, query cleanup, and sign application. `whole_literal` consumes the
  actual encoded literal, agrees with `CNF.Literal.eval`, preserves the full
  certificate and both suffixes, and clears workspace. Exact summed cost
  includes the one-step loader-to-evaluation transition; the complete-frame
  bound is `N * (2L + 4N + 18) + 2L + 13`. Backup remains preloaded and the
  final live continuation halt is excluded. `ClauseEvaluationStepMachine`
  now combines the leading literal value and supplied clause accumulator in
  one further step, preserving the certificate and both suffixes and clearing
  workspace. `whole_literal_append` identifies the result as the value of the
  processed clause with this literal appended. The complete-frame bound is
  `N * (2L + 4N + 18) + 2L + 14`. `ClauseLiteralMachine` now embeds this
  accumulation on nine Boolean stacks, preserving an independent outer literal
  count with unchanged exact cost. `clause_head` retains all unread frames and
  the original count; `clause_head_append` gives processed-prefix semantics.
  Outer decrement, repeated clause traversal, exact-width checking, and full
  verifier assembly remain pending.

## Milestone 4: Cook--Levin

- Select and document the verifier-machine normal form. Done: mathlib
  `FinTM2` with `TM2ComputableInPolyTime` over Boolean-string certificates.
- Encode bounded accepting computations as Boolean constraints. Done:
  `MachineTableau.Params.localSystem` and `Instance.tableau`.
- Prove local consistency is equivalent to a valid accepting computation.
  Done: `Tableau.LocalSystem.satisfiable_iff`, `CookLevin.accepts_iff_sat`.
- Implement the formula generator. Done: `TableauStacks.generator`,
  `generator_exits`, `CookLevin.machine_outputsInTime` (unary-index CNF).
- Prove its output size and runtime polynomial. Done:
  `Instance.generatorCost_le`, `CookLevin.computableInPolyTime`.
- Derive SAT NP-hardness and NP-completeness. Hardness done for both
  encodings: `CookLevin.encodedUnarySAT_NPHard`,
  `BinaryConvert.encodedSAT_NPHard`; NP-completeness:
  `SatVerify.encodedSAT_NPComplete`.
- Derive exact 3-SAT NP-completeness through a checked polynomial reduction.
  Done: the chain reduction `ChainMachine.reduction`, the re-encoding
  `BinaryConvert.exactThreeReduction`, and
  `ExactThreeVerify.encodedExactThreeSAT_NPComplete`.

## Milestone 5: downstream adapters

- Supply dense variable renaming for binary instances whose downstream
  constructions depend on variable indices. Semantic and output-size layers
  are checked in `CNFRenaming`: `Formula.denseRename` preserves satisfiability,
  exact widths, and all occurrences; variables occupy exactly the dictionary
  index range, below the original binary input length `n`. Its unary output
  has at most `n * (n + 1)` symbols. `FirstMatch.firstMemberComputableInPolyTime`
  now supplies serialized first-member lookup with unary output; singleton
  queries give `List.idxOf` and agree with `denseIndex`. Its comparison
  postprocessor takes exactly `3m + 2` steps for `m` bits.
  `DictionaryLookup.computableInPolyTime` now packages direct `(query, dictionary)`
  lookup under `FramedNatLookup.finEncoding`, reusing the identical machine
  and polynomial; the decoder checks singleton shape and stream exhaustion,
  and the unary result size is bounded by the full input bit length.
  `PairDuplication.computableInPolyTime` now duplicates any finitely encoded
  input into its tagged pair in exactly `6n + 3` TM2 steps, including cleanup
  and halt, without requiring a nonempty alphabet. Its checked composition
  `retainInputComputableInPolyTime` computes `(f a, a)` from a single input;
  `DictionaryLookup.preservingComputableInPolyTime` returns the unary lookup
  result alongside the original query and dictionary, polynomial in the
  original input bits. `DictionaryLookupEncoding.computableInPolyTime` now
  converts the tagged pair of `FramedNat` and `FramedNatList` into the lookup
  encoding in exactly `3q + 2d + 8` steps for the complete component bit
  lengths, bounded by `3n + 8` in tagged input length `n = q + d`.
  `lookupComputableInPolyTime` and `preservingLookupComputableInPolyTime`
  compose conversion, lookup, and original tagged-input retention with all
  costs charged. `FramedSucc.routine_exits` now supplies exact framed-count
  successor in `2b + 2b' + 4` steps, bounded by `2L + 4` in consumed frame
  length `L`, while preserving unread input and output suffixes.
  `listCount_exits` retains all dictionary entry frames while emitting the
  incremented header separately; `computableInPolyTime` packages standalone
  framed successor with polynomial `2X + 4`. Tagged-pair list cons, dictionary
  construction, updating the retained query, and occurrence-preserving formula
  traversal remain pending; full renaming is not yet a polynomial-time
  re-encoding reduction.
- Connect `phd-thesis-lean`'s concrete regression compiler to the common
  encoded exact-3-SAT language.
- Re-express its construction bound in the shared bit-level computational
  model.
- Compose it with exact 3-SAT hardness.
- Add further NP-hardness reductions without coupling them to thesis-specific
  mathematics. Done for Max-Cut: `MaxCutMachine.encodedMaxCut_NPHard`, which the
  thesis's Max-Cut based results (`thm:fixed-prime-hardness`, `thm:main`,
  `thm:nested-easy-hard-easy`) can use for their NP-hardness transfer.

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
