# Lean 4.35 / mathlib v4.35.0 migration notes

The library moved from Lean `v4.27.0-rc1` (mathlib `cd47994`) to Lean and
mathlib `v4.35.0` in October 2026. Downstream projects (in particular
`phd-thesis-lean`) need the same changes.

## Bundled encodings

mathlib (2026-05-07) made the alphabet an explicit parameter of
`Computability.Encoding α Γ`, deprecated `FinEncoding`, and changed
`Turing.TM2ComputableInPolyTime` to take bare encoding functions
`ea : α → List αΓ`. `LeanNPHardness/FinEncoding.lean` restores the old surface:

| old mathlib name | replacement |
| --- | --- |
| `Computability.FinEncoding α` | `LeanNPHardness.FinEncoding α` (same fields: `Γ`, `encode`, `decode`, `decode_encode`, `ΓFin`) |
| `Turing.TM2ComputableInPolyTime ea eb f` | `LeanNPHardness.TM2ComputableInPolyTime ea eb f` (an `abbrev` for mathlib's, with `αΓ := ea.Γ`) |
| `Turing.TM2Computable`, `Turing.TM2ComputableInTime` | `LeanNPHardness.TM2Computable`, `LeanNPHardness.TM2ComputableInTime` |
| `Turing.idComputableInPolyTime e` | `LeanNPHardness.idComputableInPolyTime e` |
| `finEncodingNatBool`, `finEncodingBoolBool`, `unaryFinEncodingNat`, `finEncodingNatΓ'` | same names in `LeanNPHardness`, built with `FinEncoding.ofEncoding` |

The machine model and the input-size measure are unchanged: the abbreviation
unfolds to mathlib's definition, so the runtime is still measured in the length
of `ea.encode x`. Simp lemmas such as `encodingNatBool_encode` restore the field
reductions that the old structure-literal definitions provided.

In a file that also opens `Computability`, the deprecated mathlib names can be
ambiguous; open the replacements explicitly or hide the old ones:

```lean
open Computability hiding FinEncoding finEncodingNatBool finEncodingBoolBool unaryFinEncodingNat
open LeanNPHardness (FinEncoding finEncodingNatBool finEncodingBoolBool unaryFinEncodingNat)
```

Other moves: `Mathlib.Computability.TMComputable` is now
`Mathlib.Computability.TuringMachine.Computable`, and `EvalsTo`,
`EvalsToInTime`, `Reaches`, `eval` live in namespace `StateTransition`.

## Transparency

Lean 4.35 makes `isDefEq` respect the ambient transparency. The machine proofs
rely heavily on unfolding aliases such as `FinTM2.Cfg` and machine-specific
alphabet families, so `lakefile.lean` sets

```lean
leanOptions := #[⟨`backward.isDefEq.respectTransparency, false⟩]
```

the switch mathlib itself uses during this transition. It changes elaboration
only; the kernel still checks every proof, and the axiom audit is unchanged.
`leanOptions` are not inherited by dependants, so a downstream package that
re-proves machine facts should set it too. `lake env lean FILE` also ignores
it; pass `-Dbackward.isDefEq.respectTransparency=false`.

Recurring repairs that the option does not cover:

- `simpa … using h` now closes at reducible transparency. Where the simplified
  types differ only by unfolding a definition, use `simpa … using! h`.
- `convert h using n` (via `congr!`) no longer closes `myRoutine = seq …` by
  unfolding. Either `unfold myRoutine` before `convert`, or use
  `convert (config := {preTransparency := .default}) h using n`.
- `congr 1` on large machine configurations can loop in `whnf`; use
  `apply congrArg` instead.
- `simp` no longer unfolds `flip`; add it to simp sets for
  `(flip Option.bind f)^[n]` goals.
- In a structure instance, `toParent := e` is bound opaquely in later tactic
  fields; write the parent's fields out instead.
- `dsimp only` lines that only performed beta/eta steps now report "no
  progress" and can be deleted.
