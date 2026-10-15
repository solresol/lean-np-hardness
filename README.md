# NP-hardness foundations in Lean

Machine-checked NP-completeness proofs in Lean 4, stated in
[mathlib](https://github.com/leanprover-community/mathlib4)'s own model of
computation: finitely encoded languages (`Computability.FinEncoding`) and
polynomial-time multi-stack Turing machines
(`Turing.TM2ComputableInPolyTime`).

The library proves the Cook--Levin theorem and the NP-completeness of CNF-SAT,
exact 3-SAT and Max-Cut, each through an explicit polynomial-time machine. No
declaration uses `sorry`, `admit`, a project-defined axiom or `unsafe`, and the
headline results depend only on Lean's standard axioms `propext`,
`Classical.choice` and `Quot.sound`.

## Main results

Declaration names are relative to the `LeanNPHardness` namespace.

| Result | Lean declaration | File |
|---|---|---|
| Cook--Levin: CNF-SAT is NP-hard | `CookLevin.encodedUnarySAT_NPHard` | [`CookLevinHardness.lean`](LeanNPHardness/CookLevinHardness.lean) |
| CNF-SAT is NP-complete | `SatVerify.encodedSAT_NPComplete` | [`SatVerifyMachine.lean`](LeanNPHardness/SatVerifyMachine.lean) |
| Exact 3-SAT is NP-complete | `ExactThreeVerify.encodedExactThreeSAT_NPComplete` | [`VerifierMachine.lean`](LeanNPHardness/VerifierMachine.lean) |
| Max-Cut is NP-complete | `MaxCutVerify.encodedMaxCut_NPComplete` | [`MaxCutVerifyMachine.lean`](LeanNPHardness/MaxCutVerifyMachine.lean) |
| The same three problems under the unary-index encoding | `UnaryNPComplete.encodedUnarySAT_NPComplete`, `UnaryNPComplete.encodedUnaryExactThreeSAT_NPComplete`, `UnaryNPComplete.encodedUnaryMaxCut_NPComplete` | [`UnaryNPComplete.lean`](LeanNPHardness/UnaryNPComplete.lean) |
| Polynomial-time TM2 machines compose | `MachineComposition.compositionComputableInPolyTime` | [`MachineCompositionRuntime.lean`](LeanNPHardness/MachineCompositionRuntime.lean) |
| Polynomial-time reductions compose | `PolytimeManyOneReduction.comp` | [`PolytimeComposition.lean`](LeanNPHardness/PolytimeComposition.lean) |
| P is contained in NP | `EncodedLanguage.inP_toInNP` | [`ComplexityClasses.lean`](LeanNPHardness/ComplexityClasses.lean) |

The composition result constructs the composed machine explicitly, which
proves the statement mathlib records as
`proof_wanted TM2ComputableInPolyTime.comp` at the pinned revision.

## What the statements mean

The kernel checks the proofs; what a reader should check is that the
definitions say what is intended. They are short.

**Model of computation.** mathlib's `Turing.FinTM2` machines with
`Turing.TM2ComputableInPolyTime`. Input size is the length of the input's
`FinEncoding`.

**Languages and reductions.** An `EncodedLanguage` bundles a predicate with the
encoding that fixes its input size
([`ComplexityClasses.lean`](LeanNPHardness/ComplexityClasses.lean)). A
`PolytimeManyOneReduction` is a map, a proof that it preserves yes- and
no-instances, and a polynomial-time machine computing it
([`PolytimeReduction.lean`](LeanNPHardness/PolytimeReduction.lean)).

**NP, NP-hardness and NP-completeness**, from
[`ComplexityClasses.lean`](LeanNPHardness/ComplexityClasses.lean):

```lean
structure PolytimeVerifier {α : Type} (problem : EncodedLanguage α) where
  verify : α × List Bool → Bool
  certificateBound : Polynomial ℕ
  sound : ∀ input witness, verify (input, witness) = true → problem.accepts input
  complete : ∀ input, problem.accepts input → ∃ witness : List Bool,
    witness.length ≤ certificateBound.eval (problem.encoding.encode input).length ∧
      verify (input, witness) = true
  polytime :
    Nonempty
      (Turing.TM2ComputableInPolyTime
        (PairEncoding.finEncoding problem.encoding certificateEncoding)
        finEncodingBoolBool verify)

def InNP {α : Type} (problem : EncodedLanguage α) : Prop :=
  Nonempty (PolytimeVerifier problem)

def NPHard {α : Type} (problem : EncodedLanguage α) : Prop :=
  ∀ {β : Type} (source : EncodedLanguage β),
    source.InNP → Nonempty (source.PolytimeReducesTo problem)

def NPComplete {α : Type} (problem : EncodedLanguage α) : Prop :=
  problem.NPHard ∧ problem.InNP
```

**Problem encodings.**

- *Binary* ([`CNFEncoding.lean`](LeanNPHardness/CNFEncoding.lean)): a literal
  on variable `v` is the natural number `2v` (positive) or `2v + 1`
  (negative), written in binary inside a framed list-of-lists encoding.
  `CNF.encodedSAT` is CNF-SAT and `CNF.encodedExactThreeSAT` requires every
  clause to have exactly three literal occurrences.
- *Unary-index* ([`UnaryCNF.lean`](LeanNPHardness/UnaryCNF.lean)): each
  variable index is written in unary, so every index is bounded by the input
  length. This is the convenient source for downstream reductions whose output
  grows with the number of variables or vertices. A checked re-encoding
  machine (`BinaryConvert`) connects it to the binary encoding.
- *Max-Cut* ([`MaxCutSpec.lean`](LeanNPHardness/MaxCutSpec.lean)): a list of
  edges and a threshold, encoded as one two-literal clause per edge followed by
  a threshold clause, under either CNF encoding.

Repeated literals, clauses and edges are retained, never silently normalized.

## Relation to other formalisations

Cook--Levin has been formalised before: in Coq by Gäher and Kunze (ITP 2021),
in Isabelle/HOL by Balbach ([AFP, 2023](https://isa-afp.org/entries/Cook_Levin.html)),
and in Lean 4 by several projects developed independently of this one during
2026:

- [Complexitylib](https://github.com/SamuelSchlesinger/complexitylib)
  (Samuel Schlesinger) is a much larger library built on mathlib and CSLib,
  with its own Arora--Barak multi-tape Turing machines and its own
  definitions of P, NP and FP. It proved SAT and 3SAT NP-complete in July 2026,
  before this repository began, and covers far more of complexity theory.
- [millennium-cook-levin](https://github.com/JoshuaTan42/millennium-cook-levin)
  (Joshua Tan) proves Cook--Levin for SAT under a dense CNF encoding, against
  the definitions of
  [LeanMillenniumPrizeProblems](https://github.com/lean-dojo/LeanMillenniumPrizeProblems),
  which also use mathlib's `FinTM2` and `FinEncoding`. It also proves
  composition of polynomial-time TM2 machines.
- [NPCompleteness-Lean4](https://github.com/RBarish-UTokyo/NPCompleteness-Lean4)
  proves SAT variants NP-complete for an explicit Turing-machine model using
  only Lean core.
- [descriptive-complexity](https://github.com/PierreSenellart/descriptive-complexity)
  (Pierre Senellart) proves a machine-free Cook--Levin and Karp's 21 problems
  by first-order reductions.

This repository does not depend on any of them. Within that landscape it
offers results stated directly in mathlib's `FinEncoding` and
`TM2ComputableInPolyTime` model; NP-completeness of exact 3-SAT and Max-Cut as
well as SAT, under standard binary encodings, with the conversion between
encodings checked in Lean rather than argued on paper; a documented pattern
for adding further reductions ([REDUCTION_GUIDE.md](docs/REDUCTION_GUIDE.md));
and a downstream use, described next.

## Downstream use

The library supplies the hardness sources for a machine-checked NP-hardness
proof of fixed-prime p-adic signed affine regression:

- [`phd-thesis-lean`](https://github.com/solresol/phd-thesis-lean) proves the
  concrete `p = 5` reduction from 3-SAT correct. Connecting its compiler to
  this library's exact 3-SAT or Max-Cut sources through a polynomial-time
  machine is the remaining step; see
  [RELATED_REPOS.md](docs/RELATED_REPOS.md).
- [`phd-thesis-coq`](https://github.com/solresol/phd-thesis-coq) proves the
  complete end-to-end NP-hardness theorem in Coq, using the Saarland
  complexity library's Cook--Levin theorem.

## How this was made

This repository was developed almost entirely by AI coding agents: a daily
scheduled agent from July to October 2026, whose runs are recorded in
[AUTOMATION_LOG.md](AUTOMATION_LOG.md), followed by interactive sessions with
Claude (credited in commit trailers). The agents work under the rules in
[AGENTS.md](AGENTS.md).

The proofs do not need to be trusted on that account: Lean's kernel checks
every proof, CI rebuilds the library and rejects unfinished proofs on every
push, and [`Audit.lean`](LeanNPHardness/Audit.lean) prints the axioms of each
headline result. What the kernel cannot check is whether the definitions and
statements above say what is intended. They have not yet had independent
expert review.

## Checking the proofs

Install [elan](https://github.com/leanprover/elan), then:

```sh
lake exe cache get
lake build
```

The toolchain (Lean `v4.27.0-rc1`) and mathlib commit
(`cd479940d5ab509f094f7e55ed6433b5aaa37870`) are pinned in `lean-toolchain`
and `lake-manifest.json`. The default target includes the axiom-audit module.
[CI](.github/workflows/lean.yml) runs the same build and rejects any `sorry`,
`admit`, project-defined `axiom` or `unsafe` declaration.

## Completion policy

A headline theorem counts as complete only when:

- the source and target languages have explicit encodings;
- the reduction is implemented by a checked polynomial-time machine;
- semantic correctness holds in both directions;
- all needed reduction composition is proved;
- no hardness fact is supplied as an undeclared external premise; and
- `#print axioms` reveals no project-defined assumption or unfinished proof.

## Status and further reading

Milestones 0--4 of the [roadmap](ROADMAP.md) are complete: reductions,
polynomial-time composition, P and NP, SAT languages, and Cook--Levin.
Connecting the downstream thesis reduction is in progress; upstreaming the
composition result to mathlib and registering a headline result with
[Palomar](https://palomar-registry.org/) are planned.

- [THEOREM_STATUS.md](THEOREM_STATUS.md): every checked result, its Lean
  declarations and the axiom audit.
- [docs/COMPONENTS.md](docs/COMPONENTS.md): the encodings and machine
  components, and how the Cook--Levin and NP-completeness proofs are
  decomposed.
- [docs/ARCHITECTURE.md](docs/ARCHITECTURE.md): design of languages,
  reductions and encodings.
- [docs/REDUCTION_GUIDE.md](docs/REDUCTION_GUIDE.md): how to prove a new
  problem NP-hard with the library.

## Licence

Licensed under the [Apache License 2.0](LICENSE), the licence mathlib uses.
