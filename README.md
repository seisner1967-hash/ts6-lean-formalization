# TS6 - Lean 4 Formalization (v4.1)

Lean 4 formalization of the exact, spectral, and conditional effective
Dirichlet-character variance layers of the TS programme.

## Status

| Module | Layer | Status | Sorry |
|--------|-------|--------|-------|
| `TS6/Exact/FiniteCharacterVariance.lean` | TS6-A | GREEN | 0 |
| `TS6/Exact/DirichletVariance.lean` | TS6-B | GREEN | 0 |
| `TS6/Exact/CenteringShift.lean` | TS6-C | GREEN | 0 |
| `TS6/Structure/RankinSelbergDecomp.lean` | TS6-D | GREEN | 0 |
| `TS6/Effective/AveragedBounds.lean` | TS6-E/F/G | GREEN CONDITIONAL | 0 |

All five modules are Lean-closed without sorry. The effective layer
(TS6-E/F/G) is GREEN-CONDITIONAL: closed conditionally on a typed
`LargeSieveInequality` interface, which this repository does NOT itself prove.

## What this repository proves

- **TS6-A** Parseval/Plancherel for `MulChar G ℂ` over a finite abelian group.
- **TS6-B** Exact identities `TS1_exact_identity` (q prime) and `TS2_exact_identity` (q ≥ 2).
- **TS6-C** Centering shift / Huygens decomposition.
- **TS6-D** Rankin-Selberg decomposition with diagonal/off-diagonal split.
- **TS6-E/F/G** Effective bounds `TS4_weighted`, `TS4_unweighted`, `TS3_first`
  from typed `LargeSieveInequality` and `ChebyshevThetaBound` interfaces.

## What this repository does NOT prove

- **The Large Sieve inequality itself.** The structure `LargeSieveInequality`
  is intentionally uninhabited within TS6: an instance must be supplied
  externally (e.g., from a future Mathlib release exposing Iwaniec-Kowalski
  Theorem 7.13, or from an external proof bridge).
- **Goldbach's conjecture.** TS6 is a certification layer for the variance
  identities underlying the TS programme; it does not prove Goldbach.
- **The Riemann Hypothesis.** Out of scope.

## Audit

`#print axioms` for `TS4_weighted_effective_bound`, `TS4_unweighted_effective_bound`,
`TS3_first_effective_bound`: only Lean kernel axioms (`propext`,
`Classical.choice`, `Quot.sound`).

No `sorryAx`. No user-added axioms.

Audit tool: `horizon-proof-agent v0.1.4`. Final report:
`reports/report_20260503T124108Z.md`. Freeze manifest:
`TS6_FROZEN_v4.1_2026-05-03.txt` (with SHA-256 hashes).

## Reproduce

Requires `elan` + `lake`. Lean toolchain is pinned in `lean-toolchain`.

```
lake build TS6
```

Expected output: `Build SUCCESS`.

## Environment

- Lean toolchain: `leanprover/lean4:v4.16.0`
- Mathlib revision: `a6276f4c6097675b1cf5ebd49b1146b735f38c02` (v4.16.0 pinned)

## Trajectory

v3 (2026-04-22) → v4 (2026-05-03 morning) → v4.1 (2026-05-03 freeze).

See `SESSION_2026-05-03_BILAN.md` for the full closure sequence:
8 → 7 → 6 → 5 → 4 → 3 → 0 primary REAL sorrys.

## Citation

If you use or reference this formalization, please cite:

> Serge Durand, *TS6 v4.1 - Lean 4 Certification of the Exact, Spectral, and
> Conditional Effective Variance Layers* (2026).
> https://github.com/seisner1967-hash/ts6-lean-formalization
> Tag: `v4.1`

## License

- Lean source code (`*.lean` files): MIT License - see `LICENSE`.
- Documents (PDFs, LaTeX, Markdown, manifests): CC BY 4.0 - see `LICENSE-DOCS`.
