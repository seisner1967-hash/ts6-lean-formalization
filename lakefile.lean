import Lake
open Lake DSL

package «horizon» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.16.0"

-- HorizonMT: the original scaffold (45 axioms closed, 0 sorry)
@[default_target]
lean_lib «HorizonMT» where
  srcDir := "."

-- HorizonMFE: the MFE bootstrap pipeline (S0–S5)
@[default_target]
lean_lib «HorizonMFE» where
  srcDir := "."
-- TS6: formalization layer for the TS programme
lean_lib TS6 where
  srcDir := "."
  roots := #[`TS6.Exact.FiniteCharacterVariance,
             `TS6.Exact.DirichletVariance,
             `TS6.Exact.CenteringShift,
             `TS6.Structure.RankinSelbergDecomp,
             `TS6.Effective.AveragedBounds]

-- TS6_scratch/*.lean files are kept on disk as a methodological archive
-- of the sorry-closure session (2026-05-03), but are no longer in the build.
-- See SESSION_2026-05-03_BILAN.md for the trajectory.