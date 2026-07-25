# Related repositories

## `phd-thesis-lean`

- Local: `../phd-thesis-lean`
- Remote: <https://github.com/solresol/phd-thesis-lean>

Relevant completed results:

- explicit finite exact-3-CNF syntax under a distinct-variable convention;
- a concrete `p = 5` signed affine regression compiler;
- satisfiability if and only if the target threshold is attainable;
- exact observation counts; and
- polynomial unit-cell output and construction bounds.

This repository should eventually supply the common encoded language,
bit-level polynomial-time compiler framework, and checked 3-SAT hardness
theorem needed to turn that reduction into a library-native Lean NP-hardness
result.

## `phd-thesis-coq`

- Local: `../phd-thesis-coq`
- Remote: <https://github.com/solresol/phd-thesis-coq>

This repository contains the completed end-to-end Coq theorem
`Hardness.fixed_prime_signed_regression_is_NP_hard`. It resolves the
repeated-literal source boundary, defines concrete `5`-adic semantics,
implements the encoded compiler, proves polynomial runtime, and composes with
the formal Coq exact-3-SAT hardness theorem.

It is the strongest architectural reference for the first downstream Lean
application. It is not imported or trusted by Lean.

## `phd-thesis`

- Local: `../phd-thesis`
- Remote: <https://github.com/solresol/phd-thesis>

This remains the authority for the thesis's prose and mathematical claim.
General-purpose complexity foundations should not inherit thesis-specific
notation merely to mirror the document.

## Mathlib

Remote: <https://github.com/leanprover-community/mathlib4>

This project currently builds on mathlib's:

- `Mathlib.Computability.Encoding`;
- `Mathlib.Computability.TuringMachine`; and
- `Mathlib.Computability.TMComputable`.

The toolchain is initially pinned to the same revision as
`phd-thesis-lean` so that future adapters can share definitions without a
premature dependency upgrade.

## External Lean design references

`LeanMillenniumPrizeProblems` contains experimental language, P/NP, and
reduction definitions over the mathlib machine API. It is useful prior art,
but its published development does not supply a concrete Cook--Levin theorem
or close the missing polynomial-machine composition proof. It is therefore a
reference rather than a dependency.
