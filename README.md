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

## Reusable encodings and machine operations

`CNFRenaming` supplies executable dense variable renaming for binary CNF
instances. It preserves satisfiability, exact clause widths, polarity, order,
and repeated occurrences. Only its auxiliary variable dictionary is
deduplicated. The renamed variables occupy precisely the dictionary index
range, and the unary output has at most `n * (n + 1)` symbols for original
binary input length `n`. Its TM2 implementation and runtime proof remain
pending; the checked bound is on output size.

`FirstMatchMachine` supplies a polynomial-time dictionary lookup component.
It composes the serialized repeated-membership machine with a three-stack
postprocessor that restores comparison order and emits the first match's
position in unary, in exactly `3m + 2` steps for `m` comparison bits.
`FirstMatch.firstMemberComputableInPolyTime` uses the full bit length of
`FramedNatListQueries.finEncoding`. With a singleton query list, the result
is `List.idxOf`, including the dictionary-length sentinel when absent;
`firstMember_denseIndex` connects this to dense CNF renaming.

`DictionaryLookup.computableInPolyTime` exposes direct `(query, dictionary)`
lookup using that same machine and polynomial. `FramedNatLookup.finEncoding`
serializes the input as `(dictionary, [query])`, with checked round trip,
injectivity, exact bit length, and decoder rejection of non-singleton queries
and trailing data. The unary result size is at most the input bit length;
`lookup_denseIndex` supplies the dense-renaming interface. Dictionary
construction and formula traversal remain pending.

`PairDuplication.computableInPolyTime` copies one encoded value into its
canonical tagged pair in exactly `6n + 3` TM2 steps for input length `n`,
including workspace cleanup and halting. It supports any finite alphabet,
including an empty one. `retainInputComputableInPolyTime` composes duplication
with the pair-left adapter to compute `(f a, a)` from one input.
`DictionaryLookup.preservingComputableInPolyTime` specializes this to return
the unary index alongside the complete original query and dictionary, with
polynomial runtime in the original `FramedNatLookup` input bits. Changing the
retained query and connecting repeated lookups to CNF traversal remain pending.

`DictionaryLookupEncoding.computableInPolyTime` converts the tagged pair
`PairEncoding.finEncoding FramedNat.finEncoding FramedNatList.finEncoding`
to the serialized lookup encoding. Its five-stack TM2 takes exactly
`3q + 2d + 8` steps for complete query/dictionary bit lengths `q`/`d`, including
cleanup and halt, bounded by `3n + 8` in tagged input symbols `n = q + d`.
`lookupComputableInPolyTime` composes conversion with lookup;
`preservingLookupComputableInPolyTime` additionally retains the original
tagged query/dictionary pair alongside the unary result. All conversion and
copying costs are charged to the original input. The contract covers canonical
component encodings and does not assert rejection of malformed streams.

`TaggedMembership.computableInPolyTime` converts the same tagged pair to
`FramedNatListQuery.finEncoding` in exactly `4n + 2` steps, using two transfers
on three finite TM2 stacks. `encode_eq` and `encode_length` check that removing
the tags preserves the complete serialized query/dictionary word and its
length. `membershipComputableInPolyTime` composes this with the checked Boolean
membership machine; `preservingMembershipComputableInPolyTime` also retains
the original tagged pair, charging copying as well as conversion and lookup.
The `4X + 2` polynomial belongs to conversion alone. The composed membership
witnesses use the generic checked composition bounds in original input length.
`DictionaryConstruction.insert_eq_membership` supplies the semantic branch
contract used by the insertion machine below.

`FramedSucc.computableInPolyTime` increments a natural under `FramedNat.finEncoding`
with polynomial `2X + 4` in the complete framed input bit length. Its four-stack
routine reads one frame and emits its successor in exactly `2b + 2b' + 4`
steps for old/new payload lengths `b`/`b'`, retaining arbitrary unread input
and output suffixes. `listCount_exits` applies this to a list header while
preserving all entry frames, including repetitions. The new header is emitted
separately; the tagged-pair cons wrapper below assembles the complete result.

`FramedListCons.routine_exits` now constructs the complete encoding of
`x :: xs` from separately supplied framed-query and dictionary stacks.
`Routines.extend_exits` lifts the count updater while preserving arbitrary
extra stacks at the same exact cost. Six subsequent transfers assemble the
new header, query, and old entries in order, preserving repetitions and
clearing workspace. `runSteps_le` bounds the total by `6(q + d) + 18` in the
complete supplied component bit lengths.

`TaggedFramedListCons.computableInPolyTime` now computes `(x, xs) ↦ x :: xs`
from `PairEncoding.finEncoding FramedNat.finEncoding FramedNatList.finEncoding`
to `FramedNatList.finEncoding`. Its six-stack finite TM2 scans into the cons
kernel's empty count/work stacks and restores each component with one transfer.
`load_exits` proves exact loading cost `3n + 3`; `routine_exits` composes this
with the cons kernel, preserving repetitions. `runSteps_le` and `outputsInTime`
give the bound `9n + 21`, including empty workspace, reset control, and halt,
where `n` counts the original tagged symbols (the sum of complete component
bit lengths). The polynomial witness uses `9X + 21`. Malformed-stream rejection,
the dictionary-construction machine, and full dense-renaming runtime remain
separate obligations.

`DictionaryConstruction` supplies the conditional insertion and tail-first
fold specification for that machine. `insert_eq_lookup` connects insertion
to the checked lookup's absence sentinel. `extend_eq_dedup_append` proves
agreement with `List.dedup` for a duplicate-free seed; `suffix_extend` retains
an arbitrary seed verbatim, including its repetitions. `build_eq_dedup` and
`build_vars` recover the exact dictionary used by dense renaming, in rightmost
occurrence order. `build_encode_length_le` proves the complete framed output
cannot exceed the input length, including the binary count header, and
`Formula.variableDictionary_encode_length_le` bounds it by `3n + 1` bits in
the original formula size. These are executable, semantic and output-size
results; the seeded fold still needs a TM2 runtime proof.

`DictionaryInsert.computableInPolyTime` now computes conditional insertion
from that original tagged query/dictionary input: return the dictionary when
the query is present, otherwise prepend it. It composes retained-input
membership with `selectComputableInPolyTime`, an eight-stack finite TM2 on the
nested tagged `(present, (query, dictionary))` encoding. `load_exits` removes
the outer tags in exactly `4m + 2` steps for the inner pair length `m`;
`branch_exits` checks both dictionary projection and cons, preserving all
existing entries and their order, including repetitions. `routine_exits`
counts the dispatch and both phases exactly; `outputsInTime` includes empty
workspace, reset and halt. The selector has bound `13n + 24` in its entire
input length `n = m + 1`. This linear bound is for selection alone; the full
insertion uses the checked composition polynomial in the original pair size.

`FrameReverse.natural_body_exits` now reverses an isolated stream of complete
natural-number frames, preserving bit order inside every frame and retaining
all occurrences. Its four-stack routine costs exactly `2B + 3m + 1` for `B`
body bits and `m` frames, bounded by `5B + 1`, including all loop tests and
canonical halting cleanup. `FrameMove.routine_exits` supplies the one-frame
transfer with arbitrary unread-input and output suffixes in exactly `4b + 4`
steps for `b` payload bits. The reversal pass preserves an output suffix and
empties both workspace stacks; it expects the input body to be isolated.
`DictionaryConstruction.extend_eq_foldl_reverse` identifies left-to-right
insertion over that reversed stream with the required tail-first semantics.
`FramedListReverse.prepare_exits` now separates the complete count header and
reverses the body while preserving an arbitrary seed. Its six-stack routine
takes exactly `6H + 2B + 3m + 5` steps for header/body lengths `H`/`B` and
entry count `m`, bounded by `6n + 5` in full source length `n = H + B`.
`routine_exits` reattaches the unchanged header, and `computableInPolyTime`
packages full list reversal under `FramedNatList.finEncoding` with `10X + 7`,
including empty workspace, reset and halt. `output_length` proves unchanged
encoded size. Seeded dictionary folding and full dense-renaming runtime
remain pending.

`DictionaryInsertInput.natural_head_exits` now extracts one intact query frame
and serializes it with the current dictionary as exactly the tagged input
expected by insertion. Its seven-stack routine costs `6q + 4d + 6` TM2 steps
for complete query/dictionary lengths `q`/`d`, retaining the arbitrary unread
stream and original count header while clearing workspace. `prepare_exits`
places the reversed source body on this adapter's input stack within `10n + 7`
steps in full source bits, preserving the seed. `prepare_head_exits` connects
both routines: the last source occurrence is the first tagged query, and every
remaining frame survives in reverse order. These costs cover preparation and
serialization. `DictionaryInsertCall.checked_exits` now consumes the prepared
tagged word, runs the complete insertion machine, and returns its framed result
to the dictionary stack while preserving unread input and the original header.
Loading and return take exactly `4N + 2` and `4M + 2` steps in tagged input and
framed output lengths. The separate size lemma gives `M ≤ N + 2`, so the whole
call is bounded by `P(N) + 8N + 12`, where `P` is the checked insertion
polynomial. Private machine stacks and caller scratch finish empty. The generic
`Routines.ofMachine_extended_exits` supplies the unchanged-cost call interface.
Lifting frame extraction/serialization into this extended layout, iterating the
seeded fold, and full dense-renaming runtime remain pending.

The component verifier machines listed in this section predate the complete
verifiers `SatVerify` and `ExactThreeVerify` (see the Cook--Levin section),
which are built directly on the routine framework. Remarks below that a full
verifier remains pending refer to composing these particular components.

The checked library extends reusable modules extracted from the downstream
thesis formalisation. It imports no thesis or p-adic definitions:

- `BinaryNatLists` and `RawNatEncoding`: self-delimiting binary natural/list/
  nested-list encodings, raw field representations, exact round trips and
  encoded-length bounds.
- `FramingMachine` and `SourceOrderMachine`: linear-time framing, unframing,
  list serialization, and source-order conversion under those exact encodings.
- `BinaryArithmetic`: linear-time binary successor, saturated predecessor,
  comparison and addition. Comparison/addition consume the explicitly aligned
  `MachinePrimitives.BinaryNatPair.finEncoding`; no conversion from the
  separate tagged `PairEncoding` is implicit.
- `CountedNatRows` and `CountedRowMachine`: exact counted-row parsing, including
  empty rows, and a linear-time outer-header removal machine.
- `BooleanListMachine`: a linear-time Boolean `allFalse` fold.
- `BinaryEqualityMachine`: a finite TM2 equality kernel on two separately
  supplied Boolean stacks. It consumes both words in exactly
  `max(left.length, right.length) + 1` steps and specializes to canonical
  binary natural equality. Loading a serialized pair and traversing a SAT
  certificate remain separate obligations.
- `PreservingBinaryEqualityMachine`: a finite TM2 comparison kernel that
  saves query bits while scanning and restores their exact order afterwards.
  It consumes the candidate, empties scratch, preserves the output suffix,
  and restores initial control in exactly `max(q, c) + q + 2` steps for
  supplied bit lengths `q` and `c`, bounded by `2q + c + 2`. The natural
  interface uses canonical binary encodings. Framed certificate traversal
  and the composed SAT verifier remain pending.
- `FrameExtractionMachine`: a finite TM2 kernel extracting one framed word
  in original bit order while preserving the query, remaining input, and
  candidate suffix. It empties scratch and the unary counter in exactly
  `3n + 3` steps for `n` payload bits, bounded by twice the consumed frame's
  bit length plus one. Its natural interface loads canonical binary words
  for the equality kernels; counted traversal remains pending.
- `FrameComparisonMachine`: one finite six-stack dispatcher extracts a framed
  candidate and compares it with a preloaded query, preserving the query,
  unread input, and output suffix. Exact runtime is `3c + max(q, c) + q + 5`
  for query/payload bit lengths `q`/`c`, bounded by `2q + 2f + 3` for consumed
  frame length `f`. The candidate and work stacks finish empty. Canonical
  natural equality is checked; `CertificateMembershipMachine` connects complete
  encoded-certificate traversal.
- `CertificateCountMachine`: a finite seven-stack dispatcher loads the outer
  framed binary list count onto a dedicated stack and tests whether it is
  empty, preserving the count, query, candidate, output, and unread body.
  `list_run` reaches the correct zero/nonzero continuation in exactly
  `3b + 4` steps for binary count length `b`; the header bound is `2h + 2`
  for framed-header length `h`, also bounded by `2N + 2` for certificate
  length `N`. The continuation's halt is not included. Canonical headers
  are assumed; `CertificateMembershipMachine` connects extraction to traversal.
- `CertificateComparisonMachine`: the framed comparator runs on the same
  seven-stack layout as count initialization, preserving arbitrary bits on
  the remaining-count stack. It reaches a continuation in exactly
  `3c + max(q, c) + q + 5` steps, bounded by `2q + 2f + 3`, retaining the
  query and unread suffixes and emptying candidate/scratch/count. Its
  `list_head_run` consumes one certificate-body entry and retains all later
  frames, including duplicates. `CertificateStepMachine` connects this
  comparison to count decrement; `CertificateMembershipStepMachine` adds
  Boolean accumulation. `CertificateMembershipMachine` connects header loading
  and complete traversal.
- `CertificatePredecessorMachine`: the binary predecessor runs on the same
  seven-stack layout, consuming `remaining`, using `scratch`, and writing
  the result in original bit order onto `candidate`. It preserves arbitrary
  input/query/count/output contents with unchanged predecessor step count,
  bounded by `2b + 3` for count bit length `b`. Canonical counts, including
  zero and one, yield saturated predecessor; the certificate-tail interface
  preserves every unread frame. `CertificateDecrementMachine` connects this
  predecessor execution to ordered transfer.
- `CertificateCountTransferMachine`: a finite two-pass kernel transfers
  `candidate` through `scratch` onto `remaining` in original bit order in
  exactly `2p + 2` steps for `p` result bits. It preserves arbitrary
  input/query/count/output contents and the remaining-stack suffix, empties
  candidate and scratch, and reaches a live continuation. For an already
  computed predecessor, the transfer costs at most `2b + 2` for original
  count bit length `b`, using the now-public `binaryPredBits_length_le`.
  `CertificateDecrementMachine` supplies the predecessor-to-transfer dispatcher.
- `CertificateDecrementMachine`: one finite dispatcher decrements the retained
  count in place, preserving arbitrary input/query/count/output contents and
  emptying candidate/scratch. `whole_word` proves exact execution in the
  predecessor witness's step count plus `2p + 2` for result length `p`;
  `evalsToInTime` bounds the total by `4b + 5` for original count length `b`.
  Canonical counts saturate at zero; `list_tail_evalsToInTime` restores the
  tail length to `remaining` while preserving all unread frames and prior
  comparison output. Execution ends at a live continuation before its halt.
  `CertificateStepMachine` connects framed comparison to this decrement.
- `CertificateStepMachine`: one finite dispatcher compares a framed candidate
  with the query and decrements the retained count in place. The comparison
  halt enters decrement in the same counted step; `whole_frame` proves exact
  summed cost and `evalsToInTime` bounds it by `2q + 2f + 4b + 8` for query,
  consumed-frame, and original count bit lengths. Equality is pushed onto
  output; the query and unread suffixes survive and all three work stacks
  finish empty. `list_head_evalsToInTime` consumes one certificate entry,
  restores the exact tail count, and preserves every later frame, including
  repetitions. Execution ends at a live continuation before its halt.
  `CertificateMembershipStepMachine` connects Boolean accumulation at that
  continuation.
- `CertificateMembershipStepMachine`: compares one framed certificate entry,
  decrements its retained count, and ORs equality with the supplied prior
  accumulator. `accumulate_step` proves the two-pop/one-push update takes one
  TM2 step and preserves all other stacks. `whole_frame` adds exactly one to
  the comparison/decrement cost; `evalsToInTime` bounds it by
  `2q + 2f + 4b + 9` in query/frame/count bit lengths.
  `list_head_evalsToInTime` retains the query, exact tail count, every later
  frame (including repetitions), and output suffix; all work stacks empty and
  control resets at a live continuation. `CertificateMembershipLoopMachine`
  connects this step to count-controlled repetition.
- `CertificateMembershipLoopMachine`: traverses a complete framed certificate
  body with its canonical count, query, and prior accumulator preloaded.
  `whole_list` proves exact repeated execution, returning membership OR the
  prior accumulator while preserving query and input/output suffixes, consuming
  every entry including duplicates, and emptying count and work stacks.
  `runSteps_le` bounds runtime by `n * (2q + 4b + 11) + 2F + 1`, for entry
  count `n`, query bits `q`, initial count bits `b`, and framed body bits `F`.
  `runSteps_le_bit_bound` gives the polynomial `F * (2q + 4F + 11) + 2F + 1`.
  The final continuation halt is excluded. `CertificateMembershipMachine`
  connects header extraction and accumulator initialization.
- `CertificateMembershipMachine`: runs membership from a complete framed
  certificate encoding with the query preloaded. The header extractor pushes
  the initial false accumulator and enters the loop in its final counted step.
  `whole_list` proves exact cost `3b + 3 + CertificateMembershipLoop.runSteps`
  for count bit length `b`, preserving the query and input/output suffixes, consuming all entries
  including duplicates, and emptying count/work stacks. `runSteps_le_bit_bound`
  and `evalsToInTime` give `N * (2q + 4N + 16) + 4` in query bits `q` and
  full certificate bits `N`. The final continuation halt is excluded; canonical
  complete encodings are assumed. `SerializedMembershipMachine` now supplies
  leading-query loading and traversal under one dispatcher.
- `SerializedMembershipMachine`: consumes a framed query followed by a complete
  encoded certificate on the input stack. `query_whole_frame` loads the query
  in order in exactly `3q + 3` steps; `whole_input` connects it to membership
  with exact summed cost, preserving query and input/output suffixes and
  emptying count/work stacks. `runSteps_le_bit_bound` and `evalsToInTime` give
  `M * (4M + 19) + 7` in the full serialized input's bit length `M`.
  Repeated entries, zero queries, and empty certificates are covered. The final
  continuation halt is excluded and canonical complete encodings are assumed.
  `CanonicalMembershipMachine` supplies query cleanup and canonical halting output.
  `MembershipComputable` supplies function-level encoding/witness packaging.
  Malformed-input rejection, serialized literal/formula evaluation, and the
  full verifier remain pending.
- `CanonicalMembershipMachine`: connects serialized membership to a query drain
  on the same seven stacks. `cleanup_run` takes exactly `q + 1` steps for `q`
  query bits, preserves the other six stacks, resets control, and halts.
  `whole_input` includes membership, the one-step cleanup entry, and the drain.
  `outputsInTime` proves canonical `TM2OutputsInTime` membership output with all
  non-output stacks empty, bounded by `M * (4M + 20) + 9` in complete serialized
  input bits `M`, including the final halt. Zero queries, empty certificates,
  and repeated entries are covered. `MembershipComputable` packages this machine
  as a polynomial-time function witness. Malformed-input rejection and the full
  SAT verifier remain pending.
- `MembershipComputable`: `FramedNatListQuery.finEncoding` encodes `Nat × List Nat`
  as a framed query followed by a complete framed list, with checked decoding
  and exact additive bit length. `CanonicalMembership.computableInPolyTime`
  computes Boolean membership with polynomial `X * (4 * X + 20) + 9` under
  that encoding and mathlib's Boolean output encoding. Acceptance and rejection
  semantics are separate lemmas. Its canonical-input contract does not assert
  machine rejection of malformed streams. `BooleanCopyMachine` supplies a
  certificate-copying kernel; `PreservingMembershipMachine` connects it to
  membership while retaining the certificate. Serialized literal/formula
  evaluation and the full SAT verifier remain pending.
- `BooleanCopyMachine`: a finite three-stack kernel that restores a separately
  supplied source word and prepends an ordered copy to an arbitrary target
  suffix. `reverse_run`, `restore_run`, and `whole_word` prove exact execution
  in `2n + 2` steps for source bit length `n`, emptying scratch and resetting
  control at a live continuation before its halt. `certificate_run` and
  `certificate_evalsToInTime` copy the complete framed certificate, including
  its count header and repeated entries. `PreservingMembershipMachine` now
  connects this copying pass to one membership query. `SerializedQueryMembershipMachine`
  loads the dedicated source stack; `QueryMembershipLoopMachine` supplies repeated
  queries.
- `PreservingMembershipMachine`: an eight-stack finite dispatcher that copies
  a preloaded certificate, runs membership on the working copy, and retains
  the complete original certificate, query, and arbitrary input/output
  suffixes. `copy_whole_word` and `whole_list` prove exact execution;
  `runSteps_le_bit_bound` and `evalsToInTime` bound it by
  `N * (2q + 4N + 18) + 7` in full certificate bits `N` and raw query bits `q`.
  The bound includes the copy-to-membership transition and excludes the final
  live continuation halt. Work stacks empty and control resets.
  `SerializedQueryMembershipMachine` supplies certificate loading and
  `QueryMembershipLoopMachine` supplies repeated-query dispatch. Serialized
  literal/formula evaluation and canonical full-verifier output remain pending.
- `ReusableMembershipMachine`: loads one framed natural query, runs the
  preserved-certificate lookup, then clears the query. `whole_query` preserves
  the full certificate and arbitrary input/output suffixes while leaving all
  query/count/work stacks empty at a live continuation. `query_whole_frame`
  and `cleanup_run` prove the phase invariants; `runSteps_le_bit_bound` and
  `evalsToInTime` give `N * (2q + 4N + 18) + 4q + 12`, for raw query bits `q`
  and full certificate bits `N`. Both entry transitions and cleanup exhaustion
  are counted; the final continuation halt is excluded. The backup must already
  be loaded. `QueryMembershipLoopMachine` supplies repeated-query dispatch; the
  full verifier remains pending.
- `LiteralEvaluationMachine`: retains a supplied negative-polarity bit through
  reusable framed membership lookup on the same eight stacks, then applies
  conditional negation in one counted step. `whole_literal` proves agreement
  with `CNF.Literal.eval` under `Certificate.assignment`, preserving the complete
  certificate and arbitrary input/output suffixes with query/count/work stacks
  empty and control reset. Exact cost is reusable lookup plus one;
  `runSteps_le_bit_bound` and `literal_evalsToInTime` give
  `N * (2q + 4N + 18) + 4q + 13` in raw variable/full-certificate bits.
  Polarity is preloaded in finite control; input contains the framed variable.
  `PackedLiteralMachine` supplies a separate loader for the formula encoding's
  even/odd literal code; `whole_raw_query` exposes the raw-variable entry
  used by `PackedLiteralEvaluationMachine`. Clause aggregation, exact-width
  checking, and the final continuation halt remain separate.
- `PackedLiteralMachine`: extracts one framed packed literal on five Boolean
  stacks and pops its low bit into finite control. `head_encode_toNat` and
  `tail_encode_toNat` identify the negative-polarity bit and raw variable bits,
  including positive zero's empty encoding. `whole_literal` preserves arbitrary
  unread input and query contents and empties both work stacks in exactly
  `3b + 4` steps for packed payload bits `b`. `literal_evalsToInTime` bounds this
  by `2L + 2` in the complete literal frame length `L`. The candidate starts
  empty and ends with the raw variable; execution ends at a live continuation.
  `PackedLiteralEvaluationMachine` connects this loader to reusable lookup.
- `PackedLiteralEvaluationMachine`: evaluates the actual framed even/odd
  literal code on eight Boolean stacks. The loader writes directly to the
  raw-query slot; one counted transition carries its polarity into the existing
  lookup, cleanup, and sign-application code. `whole_literal` agrees with
  `CNF.Literal.eval` under `Certificate.assignment`, retains the full certificate
  and arbitrary input/output suffixes, and empties query/count/workspace.
  Exact cost is `3b + q + PreservingMembership.runSteps + 8` in packed payload
  bits `b` and raw variable bits `q`. `runSteps_le_frame_bound` and
  `literal_evalsToInTime` bound it by `N * (2L + 4N + 18) + 2L + 13` in complete
  literal-frame/certificate bits `L`/`N`. Both signs, zero, empty certificates,
  and repetitions are covered. `ClauseEvaluationStepMachine` adds one
  accumulation step. Backup remains preloaded; repeated clause traversal,
  exact-width checking, and the full verifier remain pending. Execution ends
  at a live continuation before its final halt.
- `ClauseEvaluationStepMachine`: evaluates one packed literal and ORs its value
  with a supplied clause accumulator on the same eight Boolean stacks.
  `accumulate_step` combines two leading output bits in one counted step,
  preserving all other stacks. `whole_literal` preserves the complete
  certificate and arbitrary unread input/output suffixes and clears workspace.
  `accumulated_eq_clause_append` and `whole_literal_append` identify the result
  as the value of the processed clause with this literal appended, retaining
  every occurrence. Exact cost is `PackedLiteralEvaluation.runSteps + 1`;
  `runSteps_le_frame_bound` / `literal_evalsToInTime` give
  `N * (2L + 4N + 18) + 2L + 14` in full literal-frame/certificate bits.
  `ClauseLiteralMachine` adds preservation of an independent outer literal count.
  Backup and accumulator are preloaded. The final live continuation halt,
  repeated clause traversal, exact-width checking, and full verifier remain
  separate obligations.
- `ClauseLiteralMachine`: embeds packed-literal accumulation on nine Boolean
  stacks, retaining an independent `outerRemaining` word through every exact
  run with no extra steps. `whole_literal` preserves the full certificate,
  outer count, and both suffixes while clearing the inner count/workspace.
  `clause_head` retains all unread literal frames and the original count;
  `clause_head_append` identifies the updated processed-prefix value, including
  repeated literals. The complete-frame/certificate bound remains
  `N * (2L + 4N + 18) + 2L + 14`, independent of outer contents.
  Certificate, accumulator, and count are preloaded; outer decrement,
  repeated clause traversal, exact-width checking, and full verifier remain
  pending. The final live continuation halt is excluded.
- `QueryMembershipMachine`: extends the reusable lookup to nine stacks with a
  separate `outerRemaining` stack. `lift_stepAux`, `lift_step`, and `lift_run`
  preserve arbitrary outer contents without adding steps. `whole_query` keeps
  that count and the full certificate while clearing the lookup workspace;
  `list_head` preserves every unread query frame, including repetitions, and
  the original query-list count. The existing bit bound
  `N * (2q + 4N + 18) + 4q + 12` is unchanged and independent of the retained
  outer word. `QueryMembershipStepMachine` adds outer decrement and
  `QueryMembershipLoopMachine` repeats the combined step;
  `EncodedQueryMembershipMachine` loads its count and
  `SerializedQueryMembershipMachine` loads the certificate. The full verifier
  remains pending.
- `QueryMembershipStepMachine`: connects reusable lookup to in-place outer
  decrement on the same nine stacks. `decrement_run` preserves the inner count
  and complete backup at the original cost; `decrement_entry_step` counts the
  one-step transition. `whole_query` proves exact combined execution, retaining
  backup and input/output suffixes while clearing query/count/work stacks.
  `list_head` restores the exact tail count and retains repeated queries.
  `runSteps_le_bit_bound` and `evalsToInTime` give
  `N * (2q + 4N + 18) + 4q + 4b + 18`, for raw query bits `q`, full certificate
  bits `N`, and outer count bits `b`. The final continuation halt is excluded.
  `QueryMembershipLoopMachine` supplies count-controlled repetition;
  `EncodedQueryMembershipMachine` supplies count loading and
  `SerializedQueryMembershipMachine` supplies certificate loading. The full SAT
  verifier remains a separate obligation.
- `QueryMembershipLoopMachine`: a finite nine-stack dispatcher that repeats
  lookup and outer decrement over a canonical query-list body. `check_step`
  tests count-stack presence without consuming it; `entry_run` counts the
  return jump and restores the exact tail count. `whole_list` emits one
  membership bit per query occurrence in reverse query order, preserving the
  complete certificate and arbitrary input/output suffixes while clearing all
  count and workspace stacks. `runSteps` records exact execution;
  `runSteps_le_bit_bound` and `evalsToInTime` give
  `Q * (N * (2Q + 4N + 18) + 8Q + 20) + 1`, for framed query-body bits `Q`
  and full certificate bits `N`. Empty lists and repetitions are covered.
  The count and certificate are preloaded; `EncodedQueryMembershipMachine`
  supplies header loading. The final live continuation halt is excluded.
- `EncodedQueryMembershipMachine`: loads the framed outer count and enters
  the query loop in the extractor's final counted step, retaining the backup
  and independent inner count. `header_whole_frame` preserves arbitrary
  private stack contents. `whole_list` consumes a complete canonical query-list
  encoding, including repetitions, emits membership bits in reverse query
  order, preserves the certificate and both suffixes, and clears count/workspace
  stacks. Exact `runSteps` sums extraction and loop execution;
  `runSteps_le_bit_bound` and `evalsToInTime` give
  `M * (N * (2M + 4N + 18) + 8M + 23) + 4` in full query-list/certificate
  bits `M`/`N`. The certificate remains preloaded and the final live continuation
  halt is excluded. `SerializedQueryMembershipMachine` supplies certificate
  loading; the full SAT verifier remains pending.
- `SerializedQueryMembershipMachine`: loads a leading outer frame containing
  the complete certificate, then processes the full query-list encoding under
  one finite nine-stack dispatcher. `certificate_whole_frame` preserves arbitrary
  private data and enters query processing in exactly `3N + 3` steps for
  certificate bits `N`. `whole_input` starts with empty backup/count/workspace,
  consumes both serialized components, retains the certificate and arbitrary
  input/output suffixes, and emits one membership bit per query occurrence in
  reverse query order. `encodeInput_length` records the exact bit length;
  `runSteps_le_bit_bound` and `evalsToInTime` give
  `S * (S * (2S + 18) + 8S + 26) + 7` in total serialized bits `S`.
  Empty lists and repetitions are covered. The final live continuation halt
  is excluded. `CanonicalQueryMembershipMachine` supplies backup cleanup and
  canonical halting output; the SAT verifier remains separate.
- `CanonicalQueryMembershipMachine`: runs serialized repeated membership,
  drains the retained backup, resets initial control, and halts on the same
  nine Boolean stacks. `cleanup_run` preserves all eight other stacks and
  takes exactly `N + 1` steps for `N` backup bits. `whole_input` includes
  the one-step cleanup entry and preserves arbitrary input/output suffixes.
  `outputsInTime` gives canonical output with every non-output stack empty
  within `S * (S * (2S + 18) + 8S + 27) + 9` steps in total serialized bits,
  including the final halt. Output has one bit per query occurrence in reverse
  order; empty lists, zero, and repetitions are covered.
  `QueryMembershipComputable` supplies function-level encoding/witness packaging;
  malformed-input rejection and the full SAT verifier remain pending.
- `QueryMembershipComputable`: `FramedNatListQueries.finEncoding` encodes
  `(queries, certificate)` as a framed complete certificate followed by the
  complete query list. Prefix parsing, the round trip, injectivity, trailing
  suffix rejection, and exact bit length `2N + 1 + M` are checked. Separate
  `membershipResults_reverse` and `membershipResults_length` lemmas describe
  reverse query order and one bit per occurrence. The existing nine-stack
  machine supplies `CanonicalQueryMembership.computableInPolyTime`, with raw
  Boolean-list output and polynomial `X * (X * (2 * X + 18) + 8 * X + 27) + 9`
  in complete serialized bits, including cleanup and final halting. Conversion
  from the verifier's tagged pair encoding, serialized literal/formula evaluation,
  and exact-width checking remain pending.
- `PairExchange`: canonical pair exchange over arbitrary finite component
  alphabets in at most `4s+6` steps, including empty alphabets and words;
  `MachineAdapters.pairRightComputableInPolyTime` uses it with the existing
  pair-left adapter to process the right component while preserving the left.

`BoundedPrime`, `IntervalMachines`, `UnaryDivisibilityMachine`, and
`PrimeSelectionMachine` additionally provide checked bounded prime selection.
`MachinePrimitives.selectedPrimeComputableInPolyTime` maps unary `q` to the
selected prime in unary within `1000(q+1)^6` steps. Binary successor and
arithmetic remain binary-input results; trial division and enumeration remain
explicitly unary/padded-input results. No polynomial bound in the length of
an arbitrary standalone binary bound is claimed for the prime search.

Their runtime claims use mathlib's `EvalsToInTime` or
`TM2ComputableInPolyTime`, with actual encoded lengths and explicit input
configurations. They are reusable building blocks for SAT encodings
and downstream reductions; they do not complete the SAT verifier or Cook--Levin.

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
- exact whole-list reverse-output execution in `2 * output.length + 2` steps,
  preserving existing scratch contents and proving the resulting
  canonical-list order; and
- finite symbol-carrying fill-transfer actions with checked nonempty and empty
  two-step iterations from scratch into the second input stack, including the
  checked transition to the second machine's initial control configuration;
  and
- exact whole-list fill-input execution in `2 * scratch.length + 2` steps,
  preserving an existing second-input accumulator and proving the resulting
  converted-list order; and
- a complete order-preserving intermediate-output transfer theorem in
  `4 * output.length + 4` steps, which empties scratch storage, prepends the
  converted output to the second input stack, and enters the second machine's
  initial control configuration; and
- a total program on the final scratch layout that dispatches first-machine,
  transfer-action, and second-machine labels, with exact checked one-step
  simulations for both component phases; and
- exact whole-list execution of the order-preserving intermediate transfer
  under that total dispatcher in `4 * output.length + 4` steps; and
- exact repeated execution of the first component under the total dispatcher,
  preserving its step count and scratch contents and redirecting a halted
  endpoint to the canonical transfer entry; and
- exact repeated execution of the second component under the total dispatcher,
  preserving its step count, the first component's work stacks, and scratch
  contents from the canonical transfer-produced right entry, while resetting
  a reached halt to the composed machine's canonical initial state inside the
  same counted step; and
- one exact three-phase execution theorem that composes the first run,
  `4 * intermediate.length + 4` transfer steps, and the second run into a
  single summed step count while retaining the checked transferred layout; and
- a finite composed machine and external input/output alphabet bridge, plus a
  canonical `TM2Outputs` constructor proving list-level output composition;
  and
- a checked `TM2Computable` constructor proving function-level composition
  from the component `outputsFun` witnesses, with the middle encoding mapped
  exactly between the two machine alphabets; and
- a checked finite-program push bound, lifted from individual `TM2.stepAux`
  calls through exact and time-bounded runs, proving that a polynomial-time
  machine's encoded output length is bounded by encoded input length plus its
  declared time multiplied by a machine constant; and
- an explicit polynomial runtime for the concrete sequential machine, giving
  generic `TM2ComputableInPolyTime` composition without using mathlib's
  unfinished declaration, plus closed `PolytimeManyOneReduction.comp`; and
- encoded decision languages whose `FinEncoding` fixes the bit-level input
  size, plus deterministic polynomial-time Boolean deciders with explicit
  acceptance and rejection semantics; and
- a tagged finite encoding of input/certificate pairs with exact additive
  length, plus verifier-based NP with separate soundness, polynomially bounded
  completeness, and a checked polynomial-time Boolean verifier; and
- an executable finite-control classification pass for tagged pair encodings,
  consuming a source in exactly two steps per symbol plus two exhaustion steps
  and separating the two components onto private reverse stacks, with an exact
  specialization to the canonical input/certificate encoding; and
- an executable finite-control order-restoration phase that reverses both
  private component stacks onto ordered stacks with an exact linear step count
  and recovers the canonical input and certificate encodings; and
- one finite total preprocessing dispatcher on a shared five-stack layout,
  composing tagged classification, the phase transition, and order restoration
  in exactly four steps per tagged symbol plus seven fixed steps; and
- a finite extension of that layout with every private reduction-machine stack,
  plus an exact one-step reduction-program lift that leaves all five
  preprocessing stacks, including the ordered certificate, unchanged; and
- a finite two-phase ordered-input transfer in that extended layout, which
  reverses through the emptied left scratch stack, converts through the
  reduction machine's input equivalence, and fills its private input stack in
  exactly four steps per input symbol plus four exhaustion steps while
  preserving the certificate; and
- an exact lift of the complete tagged-pair preprocessing run to that extended
  layout, retaining the original `4 * source.length + 7` cost while preserving
  every private reduction-machine stack; and
- one finite phase-tagged dispatcher connecting preprocessing, ordered-input
  transfer, and reduction-machine control, with an exact
  `4 * source.length + 4 * left.length + 13` run that preserves the ordered
  certificate and enters the reduction machine's declared initial control; and
- exact arbitrary finite reduction-machine execution under that total
  dispatcher with the original step count and all five adapter stacks,
  including the ordered certificate, preserved; and
- a standalone finite output-reassembly program on an extended stack layout,
  with an exact `4 * reduced.length + 4 * certificate.length + 8` execution
  theorem that empties the private reduction output and preserved certificate,
  then constructs their canonical tagged pair encoding; and
- one finite total dispatcher lifting the complete pair/reduction pipeline onto
  the output-extended layout, preserving both new stacks, redirecting a reached
  reduction halt into certificate reassembly in the same counted step, and
  exactly lifting finite runs of both constituent dispatchers; and
- an exact end-to-end execution theorem for that dispatcher, composing tagged
  preprocessing, ordered input transfer, an arbitrary checked reduction run,
  and canonical reduced-output/certificate reassembly while retaining the
  explicit sum of all three phase costs; and
- a finite pair-left machine with canonical tagged input/output alphabets and
  a checked `TM2Outputs` constructor, empty work stacks, and restored initial
  control at halt, taking exactly the reduction run plus
  `8 * source.length + 4 * privateOutput.length + 22` steps; and
- checked function-level and polynomial-time pair-left computation
  `(a, c) ↦ (f a, c)`, preserving the certificate under the canonical tagged
  pair encoding, with runtime `T(N) + 8 * N + 4 * S(N) + 22` in the full tagged
  input length `N`, using the reduction time polynomial `T` and its checked
  encoded-output-size polynomial `S`; and
- a checked inclusion from P into NP using the empty encoding of the unique
  `Unit` certificate, reusing the decider machine and its runtime unchanged;
- backward closure of P under checked polynomial-time many-one reductions,
  by sequentially composing the reduction machine with the target decider; and
- the certificate-size half of backward NP transport, composing a target
  verifier's certificate polynomial with the reduction machine's checked
  encoded-output-size polynomial and proving transported bounded completeness;
  and
- a checked verifier pullback and `EncodedLanguage.InNP.of_reduction`, proving
  backward closure of NP under polynomial-time many-one reductions by composing
  the pair-left machine with the target verifier and reusing the transported
  certificate bound; and
- encoded NP-hardness and NP-completeness as propositions carrying nonempty
  checked reduction witnesses, with hardness transported forward by the
  closed polynomial-reduction composition theorem and a corresponding
  NP-completeness constructor; and
- literal syntax, list-based clauses and CNF formulas preserving repeated
  occurrences, with Boolean evaluation proved equivalent to propositional
  satisfaction, plus semantic SAT and exact k-SAT predicates on natural-number
  variables. Exact width counts repeated literals; empty conjunctions are
  satisfiable and formulas containing an empty clause are unsatisfiable; and
- a checked binary CNF encoding in `CNFEncoding.lean`, reusing the framed
  nested-list encoding with even/odd natural codes for literal polarity.
  `CNF.Formula.decode_encode` and `encode_injective` preserve the full syntax,
  and `encode_length` proves the exact bit count `encodedSize`.
  `CNF.encodedSAT`, `encodedExactKSAT`, and `encodedExactThreeSAT` bundle the
  semantic languages with this finite encoding; and
- finite assignment certificates in `CNFCertificate.lean`, listing the true
  occurring variables with repetitions retained. `Formula.eval_trueVariables`
  proves evaluation agrees with the original total assignment, and
  `satisfiable_iff_exists_bounded_certificate` characterizes satisfiability by
  a certificate of at most `3N + 1` bits for formula encoded length `N`.
  `Certificate.verify_sound` proves semantic soundness independently of that
  bound; the certificate uses the checked framed binary natural-list encoding; and
- a checked convention change in `CNFNormalization.lean` from at-most-three to
  exact-three SAT. Short nonempty clauses repeat existing literals; empty
  clauses become contradictory triples; longer clauses are retained.
  `Formula.eval_normalizeThree` preserves every assignment's evaluation,
  `exactWidth_normalizeThree` characterizes exact output width, and
  `normalizeThree_encode_length_le` bounds output bits by `26N + 1`.
  `atMostThreeToExactThree` packages the semantic reduction; its TM2 runtime
  is not checked. The checked reduction from arbitrary-width SAT to exact
  3-SAT is the chain transformation `CNF.Chain.chainThree` (next section).

Backward transport of both P and NP is checked. SAT syntax, semantic evaluation,
finite formula/certificate encodings, a linear certificate-size bound, and
short-clause padding semantics and output size are checked. Cook--Levin and
NP-completeness of CNF-SAT and exact 3-SAT under the binary encoding are
checked (next section). See [THEOREM_STATUS.md](THEOREM_STATUS.md) and
[ROADMAP.md](ROADMAP.md).

## Cook--Levin and NP-completeness

`CookLevin.encodedUnarySAT_NPHard` proves `encodedUnarySAT.NPHard`: every
encoded language with a polynomial-time verifier machine over Boolean-string
certificates has a checked polynomial-time many-one reduction
(`CookLevin.polytimeReduction`) to CNF-SAT under the unary-index encoding
`CNF.Unary.finEncoding` (a clause is a run of literals, each a sign symbol
followed by the variable index in unary marks, closed by an end-of-clause
symbol). The development is split into separately named results:

- semantic correctness: `CookLevin.accepts_iff_sat`, through the generic
  fixed-horizon tableau theorem `Tableau.LocalSystem.satisfiable_iff` and its
  instantiation `MachineTableau.Params.localSystem` for any bundled TM2
  machine (`MachineLocality`, `MachinePaddedRun`);
- the generator machine: a routine over the generator stacks
  (`TableauStacks.generator`) written with exact-step combinators
  (`Routines.seq_exits`, `loop_exits`, `dispatch_exits`). It evaluates the
  verifier's polynomials in unary by Horner's scheme (`parameterStage_exits`),
  pushes the skeleton job from finitely many constant cell templates
  (`Instance.emitter_exits`), and interprets it (`interpret_exits`);
  `generator_exits` is the exact run from the input alone to the encoded
  tableau alone, and `Instance.emitter_template` shows the routine depends
  only on the verifier machine;
- runtime: `Instance.generatorCost_le` bounds the step count by a template
  constant times the fourth power of `sizeParam`, the value of the polynomial
  `sizePoly` in the input length; `CookLevin.computableInPolyTime` packages
  the machine as `TM2ComputableInPolyTime` with time polynomial `timePoly`;
- hardness transfer: `CookLevin.polytimeReduction` and
  `CookLevin.encodedUnarySAT_NPHard`.

Exact 3-SAT under the same encoding is NP-hard as well
(`ChainMachine.encodedUnaryExactThreeSAT_NPHard`): the streaming chain
transformation `CNF.Chain.chainThree` (exact width three, satisfiability
preserved) is computed by a TM2 machine in at most `10000 * (n + 1) ^ 2`
steps (`ChainMachine.cost_le`).

Both results transfer to the library's binary CNF encoding
`Formula.finEncoding`: `BinaryConvert.computableInPolyTime` re-encodes a
unary formula in binary within `10000 * (n + 1) ^ 3` steps, giving
`BinaryConvert.encodedSAT_NPHard` and
`BinaryConvert.encodedExactThreeSAT_NPHard`.

Exact 3-SAT is in NP (`ExactThreeVerify.encodedExactThreeSAT_inNP`): a TM2
verifier reads two certificate bits per clause selecting a literal, checks
every clause has width three, and compares the selected literals pairwise in
binary, within `2000 * (n + 1) ^ 3` steps. Hence
`ExactThreeVerify.encodedExactThreeSAT_NPComplete`. CNF-SAT is in NP by a
verifier that selects one literal per clause in unary
(`SatVerify.encodedSAT_inNP`), so `SatVerify.encodedSAT_NPComplete` is the
Cook--Levin theorem in the library's binary encoding.

Max-Cut (edge lists with a threshold, encoded as two-literal clauses plus a
threshold clause) is NP-hard under both encodings
(`MaxCutMachine.encodedUnaryMaxCut_NPHard`, `MaxCutMachine.encodedMaxCut_NPHard`):
a per-clause gadget of occurrence vertices and two linked triangles
(`MaxCut.sat_iff_maxCut_gadget`) is streamed by the interpreter after the
chain reduction. Max-Cut is also in NP under the binary encoding, by a
verifier that converts the binary threshold to unary with saturation, so
`MaxCutVerify.encodedMaxCut_NPComplete`. All three problems are also
NP-complete under the unary-index encoding (`UnaryNPComplete`), where indices
are polynomial in the input size; downstream reductions whose output size
depends on the number of variables or vertices should start from these.

Axiom audit (`LeanNPHardness/Audit.lean`): `propext`, `Classical.choice`,
`Quot.sound` only.

## Toolchain

- Lean `v4.35.0`;
- mathlib tag `v4.35.0`.

mathlib unbundled the alphabet from `Encoding` in May 2026. The library keeps
the bundled interface through `LeanNPHardness.FinEncoding` and an alphabet-
supplying `TM2ComputableInPolyTime` that is definitionally mathlib's; see
[docs/MATHLIB_MIGRATION.md](docs/MATHLIB_MIGRATION.md), which also explains the
`backward.isDefEq.respectTransparency` package option.

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

This project uses mathlib's finite Turing-machine and
`TM2ComputableInPolyTime` definitions rather than creating an unrelated cost
model; `FinEncoding` is a thin bundling of mathlib's `Encoding`. Any generally useful results should be designed with eventual upstream
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
