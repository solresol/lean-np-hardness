import Lake

open Lake DSL

package lean_np_hardness where
  version := v!"0.1.0"
  -- Lean 4.35 makes `isDefEq` respect transparency. The machine-composition
  -- proofs rely on unfolding type aliases such as `FinTM2.Cfg`; this is the
  -- migration switch mathlib itself uses. It affects elaboration only: the
  -- kernel still checks every proof.
  leanOptions := #[⟨`backward.isDefEq.respectTransparency, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.35.0"

@[default_target]
lean_lib «LeanNPHardness» where
  -- Reusable NP-hardness and complexity-theory foundations.
