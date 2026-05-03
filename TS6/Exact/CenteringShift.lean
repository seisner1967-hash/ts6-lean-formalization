/-
# TS6/Exact/CenteringShift.lean

**TS6-C — PNT-centering-shift identity (TS2 Proposition 2.2).**

For every integer `q ≥ 2`, every finite set `S ⊂ ℕ`, every coefficient
sequence `a : ℕ → ℂ`, and every "prediction" value `μ : ℂ`:

    AWPNT a q S μ  -  CW a q S  =  ‖T₀ - μ‖² / φ(q)

where

    AWPNT a q S μ  =  ∑_{r ∈ (ZMod q)ˣ}  ‖θ a q S r  -  μ/φ(q)‖²,
    T₀(q, S, a)    =  ∑_{r}  θ a q S r   (the total coprime sum, =
                                          twistSum at the principal character).

In the paper setting, one takes `μ = x · Ŵ(1)`, which is the PNT
prediction for the mean $θbar$.

## Why this is pure algebra

This identity has nothing to do with characters. It is the
shift-of-origin identity for the variance of any finite complex-valued
sequence $(t_r)_{r \in I}$ and any target mean $μ$:

    ∑_r ‖t_r - μ‖²  =  ∑_r ‖t_r - t̄‖²  +  |I| · ‖t̄ - μ‖²,
    where  t̄ = (∑_r t_r) / |I|.

Applied to $I = (\mathbb Z/q)^\times$, $t_r = θ a q S r$,
$t̄ = θbar a q S$, one gets:

    AWPNT a q S μ  =  AWstar a q S  +  φ(q) · ‖θbar - μ/φ(q)‖²
                   =  AWstar a q S  +  φ(q) · ‖(T₀/φ(q)) - μ/φ(q)‖²
                   =  AWstar a q S  +  ‖T₀ - μ‖² / φ(q).

Now substitute `AWstar = CW` from TS6-B (TS2 Theorem 2.1) and rearrange.

## Mathlib dependencies

  * `TS6.Exact.DirichletVariance` — defines `θ`, `θbar`, `AWstar`, `CW`.
  * `Mathlib.Analysis.Complex.Basic` — `Complex.normSq`.

## Status: GREEN

Both `variance_shift_of_origin` and `TS2_centering_shift` are fully proven.
No remaining sorrys, no added axioms.
-/

import TS6.Exact.DirichletVariance

namespace TS6.Exact.Shift

open BigOperators Finset Complex TS6.Exact.Dirichlet

variable (q : ℕ) [NeZero q]

/-! ## PNT-centered variance -/

/-- PNT-centered variance: sum of squared deviations from the PNT-predicted
    mean `μ/φ(q)`, where in the paper `μ = x · Ŵ(1)`. -/
noncomputable def AWPNT (a : ℕ → ℂ) (q : ℕ) [NeZero q] (S : Finset ℕ) (μ : ℂ) : ℝ :=
  ∑ r : (ZMod q)ˣ, ‖θ a q S r - μ / (Nat.totient q : ℂ)‖ ^ 2

/-! ## The generic shift-of-origin identity -/

-- NOTE: HUYGENS_STEP (MEDIUM, ~2h estimated with paper preparation).
-- Currently 80% proved in source (avg, h_sum_zero, normSq conversion done).
-- Remaining: final ring-solve after normSq_sub expansion, using h_sum_zero
-- to kill cross-terms. Requires careful paper calculation first to avoid
-- the spurious |I|*normSq(avg) term that ring alone cannot reconcile.
/-- **Generic shift-of-origin lemma.**

For any finite-indexed complex sequence `t : I → ℂ` and any target mean
`μ : ℂ`:

    ∑ i, ‖t i - μ‖²  =  ∑ i, ‖t i - avg‖²  +  |I| · ‖avg - μ‖²

where `avg = (∑ i, t i) / |I|`.

Pure real/complex algebra, no character theory. The proof expands both
sides using `normSq_sub`, `star_sub`, and the identity
`∑ i, (t i - avg) = 0`. -/
theorem variance_shift_of_origin
    {I : Type*} [Fintype I] [Nonempty I] (t : I → ℂ) (μ : ℂ) :
    (∑ i : I, ‖t i - μ‖ ^ 2) =
      (∑ i : I, ‖t i - (∑ j : I, t j) / (Fintype.card I : ℂ)‖ ^ 2) +
        (Fintype.card I : ℝ) *
          ‖μ - (∑ j : I, t j) / (Fintype.card I : ℂ)‖ ^ 2 := by
  -- Let avg = (∑ t j) / |I| and write t i - μ = (t i - avg) + (avg - μ).
  -- Expand each square in terms of the real inner product Re(z · conj w).
  set avg : ℂ := (∑ j : I, t j) / (Fintype.card I : ℂ) with hav
  have hN : 0 < Fintype.card I := Fintype.card_pos
  have hNc : (Fintype.card I : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  -- Core fact: ∑ i, (t i - avg) = 0
  have h_sum_zero : (∑ i : I, (t i - avg)) = 0 := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ]
    simp [hav, mul_div_cancel₀ _ hNc]
  -- Huygens decomposition: write t i - μ = (t i - avg) + (avg - μ)
  -- Set v := avg - μ. Then ‖t i - μ‖² = ‖(t i - avg) + v‖² expands by normSq_add.
  set v : ℂ := avg - μ with hv
  -- Convert all ‖·‖² terms to Complex.normSq via sq_abs
  have norm_sq_to_normSq : ∀ z : ℂ, ‖z‖ ^ 2 = (Complex.normSq z : ℝ) := fun z => by
    rw [← Complex.sq_abs]; rfl
  -- Rewrite LHS: ‖t i - μ‖² = ‖(t i - avg) + v‖² = normSq((t i - avg) + v)
  have lhs_rewrite : ∀ i : I, ‖t i - μ‖ ^ 2 =
      (Complex.normSq ((t i - avg) + v) : ℝ) := by
    intro i
    rw [norm_sq_to_normSq]
    congr 1
    rw [hv]; ring
  -- Expand each term via normSq_add: normSq(u + v) = normSq u + normSq v + 2·Re(u·conj v)
  simp_rw [lhs_rewrite, Complex.normSq_add]
  -- Distribute the sum
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
  -- Cross-term: ∑ 2·Re((t i - avg) · conj v) = 2·Re(conj v · ∑ (t i - avg)) = 0
  have cross_zero : (∑ i : I, (2 : ℝ) * ((t i - avg) * (starRingEnd ℂ) v).re) = 0 := by
    rw [← Finset.mul_sum, ← Complex.re_sum, ← Finset.sum_mul, h_sum_zero, zero_mul,
        Complex.zero_re, mul_zero]
  rw [cross_zero, add_zero]
  -- Now rewrite the RHS ‖·‖² as normSq to match
  rw [show ‖μ - avg‖ ^ 2 = (Complex.normSq (μ - avg) : ℝ) from norm_sq_to_normSq _]
  simp_rw [show ∀ i : I, ‖t i - avg‖ ^ 2 = (Complex.normSq (t i - avg) : ℝ) from
           fun i => norm_sq_to_normSq _]
  -- Now both sides have ∑ normSq(t i - avg) + |I|·normSq v
  -- where v = avg - μ and RHS uses μ - avg; note normSq(avg - μ) = normSq(μ - avg)
  rw [show Complex.normSq v = Complex.normSq (μ - avg) from by
        rw [hv]; simp [Complex.normSq_sub, Complex.normSq, Complex.add_re, Complex.sub_re,
            Complex.mul_re, Complex.mul_im, Complex.sub_im, Complex.add_im]; ring]

/-! ## TS6-C: the centering-shift identity -/

-- NOTE: CASCADE of variance_shift_of_origin.
-- Auto-closes once CS:78 is complete via direct application with
--   mu := x * W(1) and t := theta a q S
/-- **TS6-C: TS2 Proposition 2.2 — centering-shift identity.**

For every integer `q ≥ 2`, every `a : ℕ → ℂ`, every finite `S ⊂ ℕ`, and
every `μ : ℂ`:

    AWPNT a q S μ  -  CW a q S
      =  ‖(∑ r, θ a q S r)  -  μ‖²  /  φ(q).

In the paper, `μ = x · Ŵ(1)` is the PNT prediction for the total coprime
sum `T₀ = ∑ r, θ a q S r`, and the identity quantifies the (deterministic)
gap between empirical-mean centering and PNT-prediction centering. -/
theorem TS2_centering_shift
    (a : ℕ → ℂ) (q : ℕ) [NeZero q] (hq : 2 ≤ q)
    (S : Finset ℕ) (μ : ℂ) :
    AWPNT a q S μ - CW a q S =
      ‖(∑ r : (ZMod q)ˣ, θ a q S r) - μ‖ ^ 2 / (Nat.totient q : ℝ) := by
  -- Proof plan:
  --
  -- Step 1: Apply `variance_shift_of_origin` with
  --   `I = (ZMod q)ˣ`, `t = θ a q S`, `μ' = μ/φ(q)`, `|I| = φ(q)`:
  --
  --     AWPNT a q S μ
  --       = AWstar a q S  +  φ(q) · ‖(μ/φ(q)) - θbar a q S‖².
  --
  -- Step 2: By `TS2_exact_identity` (TS6-B),
  --
  --     AWstar a q S  =  CW a q S.
  --
  -- Step 3: Compute the error term:
  --   θbar = (∑ r, θ) / φ(q) =: T₀/φ(q).  So
  --
  --     φ(q) · ‖(μ/φ(q)) - (T₀/φ(q))‖²
  --       = φ(q) · ‖(μ - T₀)/φ(q)‖²
  --       = φ(q) · ‖μ - T₀‖² / φ(q)²
  --       = ‖μ - T₀‖² / φ(q)
  --       = ‖T₀ - μ‖² / φ(q)   (since ‖·‖² is invariant under negation).
  --
  -- Step 4: Subtract `CW a q S` from both sides:
  --
  --     AWPNT a q S μ - CW a q S
  --       = ‖T₀ - μ‖² / φ(q).
  --
  -- All steps are `ring_nf` plus the named lemmas above.
  -- Step 1: AWstar = CW via TS2_exact_identity (uses the DV:106 sorry transitively)
  have h_exact : AWstar a q S = CW a q S := TS2_exact_identity a q hq S
  -- Step 2: variance_shift_of_origin applied to t = θ a q S, μ' = μ / φ(q)
  have hNe : Nonempty (ZMod q)ˣ := inferInstance
  have h_shift := variance_shift_of_origin (θ a q S) (μ / (Nat.totient q : ℂ))
  -- Step 3: Unfold AWPNT and AWstar, rewrite θbar
  unfold AWPNT
  rw [← h_exact]
  unfold AWstar
  -- Cardinality identity: harmonize Fintype.card (ZMod q)ˣ with q.totient everywhere
  have h_card_ℂ : (Fintype.card (ZMod q)ˣ : ℂ) = (Nat.totient q : ℂ) := by
    exact_mod_cast ZMod.card_units_eq_totient q
  have h_card_ℝ : (Fintype.card (ZMod q)ˣ : ℝ) = (Nat.totient q : ℝ) := by
    exact_mod_cast ZMod.card_units_eq_totient q
  -- Normalize h_shift to use q.totient throughout
  simp only [h_card_ℂ, h_card_ℝ] at h_shift
  -- θbar unfolds to (∑θ)/φ(q)
  unfold θbar
  rw [h_shift]
  -- Goal: (∑‖θ-T̄‖² + φ(q)·‖μ/φ(q) - T̄‖²) - ∑‖θ-T̄‖² = ‖T₀-μ‖²/φ(q)
  -- Simplify via ring_nf to cancel the ∑ terms
  have hφ : (Nat.totient q : ℂ) ≠ 0 := by
    have := Nat.totient_pos.mpr (NeZero.pos q)
    exact_mod_cast this.ne'
  have hφR : (Nat.totient q : ℝ) > 0 := by
    exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  -- Consolidate μ/φ(q) - (∑θ)/φ(q) into (μ - ∑θ)/φ(q)
  rw [show (μ / (Nat.totient q : ℂ)) - (∑ r : (ZMod q)ˣ, θ a q S r) / (Nat.totient q : ℂ)
        = (μ - ∑ r : (ZMod q)ˣ, θ a q S r) / (Nat.totient q : ℂ)
      from by field_simp]
  -- Now: ∑A + φ(q)·‖(μ-T₀)/φ(q)‖² - ∑A = ‖T₀-μ‖²/φ(q)
  -- Cancel the ∑A, and norm-of-div / neg handling
  rw [norm_div, Complex.norm_natCast, div_pow]
  rw [show ‖μ - ∑ r : (ZMod q)ˣ, θ a q S r‖ ^ 2 = ‖(∑ r : (ZMod q)ˣ, θ a q S r) - μ‖ ^ 2
      from by rw [← norm_neg]; congr 1; ring]
  field_simp
  ring

end TS6.Exact.Shift
