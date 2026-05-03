/-
# TS6/Effective/AveragedBounds.lean

**TS6-E / TS6-F / TS6-G — Effective averaged bounds (TS3, TS4).**

This file scaffolds the TS3/TS4 effective theorems as *conditional*
theorems, depending on two explicit typed hypothesis structures:

  * `ChebyshevThetaBound` — wraps `∑_{p ≤ y} log p ≤ 2y` for `y ≥ 2`.
  * `LargeSieveInequality` — wraps Iwaniec–Kowalski Theorem 7.13.

Neither is presently in Mathlib4 in the required form. Rather than using
`axiom`s (which would pollute the exact kernel), we package them as typed
structures passed as hypotheses to the effective theorems.

## Status: GREEN CONDITIONAL

All three effective theorems (TS6-E, TS6-F, TS6-G) are now Lean-closed
without `sorry`, conditionally on instances of `ChebyshevThetaBound`
and `LargeSieveInequality`.

The `LargeSieveInequality` structure is intentionally uninhabited within
TS6: its single field `bound` is the typed ℓ²-form interface to the
large sieve, to be supplied externally (either from a future Mathlib
release exposing Iwaniec–Kowalski Theorem 7.13, or via an external
proof bridge). The conditionality is reified as a structure argument;
`#print axioms` for the three theorems shows no `sorryAx`.

No `axiom`. Every hypothesis is named and typed.

## Mathlib dependencies

  * `TS6.Exact.DirichletVariance` for `AWstar`, `CW`.
  * `TS6.Structure.RankinSelbergDecomp` (not strictly needed but kept
    adjacent for context).
  * `Mathlib.NumberTheory.DirichletCharacter.Basic`,
    `Mathlib.Analysis.SpecialFunctions.Log.Basic`.
-/

import TS6.Exact.DirichletVariance
import TS6.Structure.RankinSelbergDecomp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic

namespace TS6.Effective

open BigOperators Finset Real Complex TS6.Exact.Dirichlet

-- Classical decidability (Fintype for DirichletCharacter ℂ q is inherited from TS6.Exact.DirichletVariance)
attribute [local instance] Classical.propDecidable

/-! ## Interfaces to the analytic inputs -/

/-- **Interface: effective Chebyshev bound.**

`θ(y) = ∑_{p prime, p ≤ y} log p ≤ 2y` for every real `y ≥ 2`.

Reference: Montgomery–Vaughan, *Multiplicative Number Theory I*, Theorem 2.4.
Not in Mathlib4 in this exact effective form as of April 2026. -/
structure ChebyshevThetaBound where
  /-- The bound itself, for all reals `y ≥ 2`. -/
  bound : ∀ (y : ℝ), 2 ≤ y →
    (∑ p ∈ (Finset.range (⌊y⌋₊ + 1)).filter Nat.Prime, Real.log p) ≤ 2 * y

/-! ## Aggregated variance quantities -/

/-- Prime-capped unweighted sum: `∑_{q ≤ Q, q prime}  AWstar a q S`. -/
noncomputable def primeCappedSum
    (a : ℕ → ℂ) (Q : ℕ) (S : Finset ℕ) : ℝ :=
  ∑ q ∈ (Finset.Icc 2 Q).filter Nat.Prime,
    (if h : q ≠ 0 then haveI : NeZero q := ⟨h⟩; AWstar a q S else 0)

/-- Prime-capped `q`-weighted sum: `∑_{q ≤ Q, q prime}  q · AWstar a q S`. -/
noncomputable def weightedPrimeCappedSum
    (a : ℕ → ℂ) (Q : ℕ) (S : Finset ℕ) : ℝ :=
  ∑ q ∈ (Finset.Icc 2 Q).filter Nat.Prime,
    (q : ℝ) * (if h : q ≠ 0 then haveI : NeZero q := ⟨h⟩; AWstar a q S else 0)

/-! ## Weight-input packaging -/

/-- `W : ℝ → ℝ` supported in `[1/2, 2]`, bounded.  Used to parameterize the
effective theorems cleanly; only `‖W‖_∞` appears in the final constants. -/
structure WeightInput where
  W    : ℝ → ℝ
  supp : ∀ u, u < 1/2 ∨ 2 < u → W u = 0
  bdd  : ∃ C, ∀ u, ‖W u‖ ≤ C

/-- `‖W‖_∞²` as a non-negative real (defined via `sSup` on the
support interval). -/
noncomputable def WsupNormSq (W : ℝ → ℝ) : ℝ :=
  ⨆ u ∈ Set.Icc (1/2 : ℝ) 2, (W u) ^ 2

/-- The coefficient sequence
    `a n = (log n) · W(n/x)` if `n` is prime in `[x/2, 2x]`, else 0. -/
noncomputable def weightCoeffs (W : ℝ → ℝ) (x : ℝ) : ℕ → ℂ :=
  fun n => if n.Prime then (Real.log n : ℂ) * (W ((n : ℝ) / x) : ℂ) else 0

/-- ℓ² energy of a coefficient sequence supported in `S`. -/
noncomputable def coeffEnergy (a : ℕ → ℂ) (S : Finset ℕ) : ℝ :=
  ∑ n ∈ S, ‖a n‖ ^ 2

/-- **Interface: large sieve inequality, packaged for prime moduli (ℓ²-form).**

For every coefficient sequence `(aₙ)` supported in a finite set `S` of indices
bounded by `2x`, the prime-moduli weighted variance sum is bounded by
`(Q² + 2x) · ‖a‖²_{ℓ²(S)}`. This is the prime-restricted, ℓ²-form of
Iwaniec–Kowalski Theorem 7.13, after collapsing
`q/φ(q) · ∑*_{χ mod q} |twistSum|²` to `q · AWstar a q S` for prime `q`
(via TS2_exact_identity for non-principal characters and the
principal-character cancellation, both of which sit in the certified
TS6 layer).

The structure is intentionally uninhabited within TS6: an instance must
be supplied by the caller, either from a future Mathlib release exposing
the large sieve in this ℓ²-form, or by an external proof bridge. -/
structure LargeSieveInequality where
  /-- The ℓ²-form bound itself, prime-moduli, weighted by `q`. -/
  bound :
    ∀ (a : ℕ → ℂ) (x : ℝ) (Q : ℕ) (S : Finset ℕ),
      2 ≤ x →
      (∀ n ∈ S, ((n : ℝ) ≤ 2 * x)) →
      weightedPrimeCappedSum a Q S ≤
        ((Q : ℝ) ^ 2 + 2 * x) * coeffEnergy a S

/-! ## Private helper lemmas -/

/-- `AWstar a q S` is non-negative (sum of squared norms). -/
private lemma AWstar_nonneg (a : ℕ → ℂ) (q : ℕ) [NeZero q] (S : Finset ℕ) :
    0 ≤ AWstar a q S := by
  unfold AWstar
  refine Finset.sum_nonneg (fun r _ => ?_)
  positivity

/-- For `u ∈ [1/2, 2]`, `(W u)² ≤ ‖W‖²_∞`. Uses the boundedness witness
from `WeightInput.bdd` to establish `BddAbove` of the iSup family. -/
private lemma W_sq_le_WsupNormSq (Wi : WeightInput) {u : ℝ}
    (hu : u ∈ Set.Icc (1/2 : ℝ) 2) :
    (Wi.W u) ^ 2 ≤ WsupNormSq Wi.W := by
  obtain ⟨C, hC⟩ := Wi.bdd
  have hWv_sq_le : ∀ v : ℝ, (Wi.W v) ^ 2 ≤ C ^ 2 := by
    intro v
    have h_abs : |Wi.W v| ≤ C := by
      have := hC v; rwa [Real.norm_eq_abs] at this
    calc (Wi.W v) ^ 2 = |Wi.W v| ^ 2 := by rw [_root_.sq_abs]
      _ ≤ C ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h_abs 2
  unfold WsupNormSq
  have hbdd : BddAbove (Set.range (fun v : ℝ =>
                  ⨆ _ : v ∈ Set.Icc (1/2 : ℝ) 2, (Wi.W v) ^ 2)) := by
    refine ⟨C ^ 2, ?_⟩
    rintro y ⟨v, rfl⟩
    refine Real.iSup_le ?_ (sq_nonneg C)
    intro _; exact hWv_sq_le v
  refine le_trans ?_ (le_ciSup hbdd u)
  haveI : Nonempty (u ∈ Set.Icc (1/2 : ℝ) 2) := ⟨hu⟩
  simp only [ciSup_const]
  exact le_refl _

/-- `WsupNormSq W ≥ 0`. -/
private lemma WsupNormSq_nonneg (W : ℝ → ℝ) : 0 ≤ WsupNormSq W := by
  unfold WsupNormSq
  exact Real.iSup_nonneg
    (fun u => Real.iSup_nonneg (fun _ => sq_nonneg _))

/-- For prime `p` with `x/2 ≤ p ≤ 2x`, the energy of `weightCoeffs Wi.W x p`
is bounded by `(log p)² · ‖W‖²_∞`. -/
private lemma norm_weightCoeffs_sq_le (Wi : WeightInput) (x : ℝ) (p : ℕ)
    (hx : 2 ≤ x) (hp_prime : p.Prime)
    (hp_lower : x / 2 ≤ (p : ℝ)) (hp_upper : (p : ℝ) ≤ 2 * x) :
    ‖weightCoeffs Wi.W x p‖ ^ 2 ≤
      (Real.log p) ^ 2 * WsupNormSq Wi.W := by
  have hx_pos : (0 : ℝ) < x := by linarith
  have h_ratio_lower : (1/2 : ℝ) ≤ (p : ℝ) / x := by
    rw [le_div_iff₀ hx_pos]; linarith
  have h_ratio_upper : (p : ℝ) / x ≤ 2 := by
    rw [div_le_iff₀ hx_pos]; linarith
  have h_ratio_mem : (p : ℝ) / x ∈ Set.Icc (1/2 : ℝ) 2 :=
    ⟨h_ratio_lower, h_ratio_upper⟩
  have hp_ge2 : (2 : ℝ) ≤ p := by exact_mod_cast hp_prime.two_le
  have h_log_nn : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
  unfold weightCoeffs
  rw [if_pos hp_prime, norm_mul, mul_pow, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, _root_.abs_of_nonneg h_log_nn,
      _root_.sq_abs]
  exact mul_le_mul_of_nonneg_left
    (W_sq_le_WsupNormSq Wi h_ratio_mem) (by positivity)

/-- Combined Chebyshev/coeffEnergy bound for the weight-coefficient sequence. -/
private lemma coeffEnergy_weightCoeffs_le
    (chebyshev : ChebyshevThetaBound)
    (Wi : WeightInput) (x : ℝ) (S : Finset ℕ)
    (hx : 2 ≤ x)
    (hS : ∀ p ∈ S, p.Prime ∧ (x / 2 ≤ (p : ℝ)) ∧ ((p : ℝ) ≤ 2 * x)) :
    coeffEnergy (weightCoeffs Wi.W x) S ≤
      4 * WsupNormSq Wi.W * x * Real.log (2 * x) := by
  unfold coeffEnergy
  have h_2x_nn : (0 : ℝ) ≤ 2 * x := by linarith
  have h_log_2x_nn : 0 ≤ Real.log (2 * x) := Real.log_nonneg (by linarith)
  have h_WsupNormSq_nn : 0 ≤ WsupNormSq Wi.W := WsupNormSq_nonneg _
  have h_step1 : ∀ p ∈ S, ‖weightCoeffs Wi.W x p‖ ^ 2 ≤
                  (Real.log p) ^ 2 * WsupNormSq Wi.W := by
    intro p hp
    obtain ⟨hp_prime, hp_lower, hp_upper⟩ := hS p hp
    exact norm_weightCoeffs_sq_le Wi x p hx hp_prime hp_lower hp_upper
  have h_step2 : ∀ p ∈ S, (Real.log p) ^ 2 ≤ Real.log (2 * x) * Real.log p := by
    intro p hp
    obtain ⟨hp_prime, _, hp_upper⟩ := hS p hp
    have hp_ge2 : (2 : ℝ) ≤ p := by exact_mod_cast hp_prime.two_le
    have hlog_p_nn : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
    have hp_pos : (0 : ℝ) < p := by linarith
    have hlog_p_le : Real.log p ≤ Real.log (2 * x) :=
      Real.log_le_log hp_pos hp_upper
    nlinarith [hlog_p_nn, hlog_p_le]
  have h_subset : S ⊆ (Finset.range (⌊2 * x⌋₊ + 1)).filter Nat.Prime := by
    intro p hp
    obtain ⟨hp_prime, _, hp_upper⟩ := hS p hp
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨?_, hp_prime⟩
    rw [Nat.lt_succ_iff, Nat.le_floor_iff h_2x_nn]
    exact hp_upper
  have h_log_nn_filter : ∀ p ∈ (Finset.range (⌊2 * x⌋₊ + 1)).filter Nat.Prime,
                    0 ≤ Real.log p := by
    intro p hp
    rw [Finset.mem_filter] at hp
    have : (2 : ℝ) ≤ p := by exact_mod_cast hp.2.two_le
    exact Real.log_nonneg (by linarith)
  have h_sum_log_subset : (∑ p ∈ S, Real.log p) ≤
                   (∑ p ∈ (Finset.range (⌊2 * x⌋₊ + 1)).filter Nat.Prime,
                      Real.log p) :=
    Finset.sum_le_sum_of_subset_of_nonneg h_subset
      (fun p hp _ => h_log_nn_filter p hp)
  have h_chebyshev := chebyshev.bound (2 * x) (by linarith)
  have h_sum_log_S_le : (∑ p ∈ S, Real.log p) ≤ 4 * x := by
    calc (∑ p ∈ S, Real.log p)
        ≤ (∑ p ∈ (Finset.range (⌊2 * x⌋₊ + 1)).filter Nat.Prime, Real.log p) :=
          h_sum_log_subset
      _ ≤ 2 * (2 * x) := h_chebyshev
      _ = 4 * x := by ring
  calc (∑ p ∈ S, ‖weightCoeffs Wi.W x p‖ ^ 2)
      ≤ (∑ p ∈ S, (Real.log p) ^ 2 * WsupNormSq Wi.W) := Finset.sum_le_sum h_step1
    _ = WsupNormSq Wi.W * ∑ p ∈ S, (Real.log p) ^ 2 := by
        rw [Finset.mul_sum]; congr 1; ext p; ring
    _ ≤ WsupNormSq Wi.W * (Real.log (2 * x) * ∑ p ∈ S, Real.log p) := by
        apply mul_le_mul_of_nonneg_left _ h_WsupNormSq_nn
        rw [Finset.mul_sum]; exact Finset.sum_le_sum h_step2
    _ ≤ WsupNormSq Wi.W * (Real.log (2 * x) * (4 * x)) := by
        apply mul_le_mul_of_nonneg_left _ h_WsupNormSq_nn
        exact mul_le_mul_of_nonneg_left h_sum_log_S_le h_log_2x_nn
    _ = 4 * WsupNormSq Wi.W * x * Real.log (2 * x) := by ring

/-! ## TS6-F: TS4 Theorem 1.1 (weighted form, the primary statement) -/

/-- **TS6-F — TS4 Theorem 1.1 (weighted effective bound).**

Under the two named interfaces `ChebyshevThetaBound` and
`LargeSieveInequality`, for every `x ≥ 2`, integer `Q ≥ 2`, and weight
`W` supported in `[1/2, 2]`,

  `∑_{q ≤ Q, q prime}  q · AWstar (weightCoeffs W x) q S
      ≤  4 · ‖W‖_∞² · (Q² + 2x) · x · log(2x)`,

provided `S` is a finite set of primes in `[x/2, 2x]`.

Proof plan (conditional on the two hypotheses):

1. Apply `largeSieve.bound` to the sequence `weightCoeffs W x`,
   at `N = ⌊2x⌋`, to control
   `∑_{q ≤ Q, q prime}  q/φ(q) · ∑*_χ |twistSum|²`.

2. For prime `q`, `∑*_χ = ∑_{χ ≠ χ₀}`; combined with `TS2_exact_identity`
   (TS6-B), the inner sum equals `(q − 1) · AWstar`. Drop the `q/φ(q) ≥ 1`
   factor and use `(q − 1) · AWstar ≥ AWstar` (here we use `q ≥ 2`).

3. Bound `∑ n, ‖a_n‖² ≤ ‖W‖_∞² · ∑_{p ≤ 2x} (log p)² ≤ ‖W‖_∞² · log(2x) · θ(2x)`.
   By `chebyshev.bound` at `y = 2x`, `θ(2x) ≤ 4x`.
   So `∑ ‖a_n‖² ≤ 4 · ‖W‖_∞² · x · log(2x)`.

4. Combining: the weighted sum is bounded by
   `(Q² + 2x) · 4 · ‖W‖_∞² · x · log(2x)`.
-/
theorem TS4_weighted_effective_bound
    (chebyshev : ChebyshevThetaBound) (largeSieve : LargeSieveInequality)
    (Wi : WeightInput) (x : ℝ) (Q : ℕ) (S : Finset ℕ)
    (hx : 2 ≤ x) (_hQ : 2 ≤ Q)
    (hS : ∀ p ∈ S, p.Prime ∧ (x / 2 ≤ (p : ℝ)) ∧ ((p : ℝ) ≤ 2 * x)) :
    weightedPrimeCappedSum (weightCoeffs Wi.W x) Q S ≤
      4 * WsupNormSq Wi.W * ((Q : ℝ)^2 + 2 * x) * x * Real.log (2 * x) := by
  have hS' : ∀ n ∈ S, ((n : ℝ) ≤ 2 * x) := fun n hn => (hS n hn).2.2
  have h_LSI := largeSieve.bound (weightCoeffs Wi.W x) x Q S hx hS'
  have h_energy := coeffEnergy_weightCoeffs_le chebyshev Wi x S hx hS
  have h_factor_nn : (0 : ℝ) ≤ ((Q : ℝ)^2 + 2 * x) := by
    nlinarith [sq_nonneg (Q : ℝ)]
  calc weightedPrimeCappedSum (weightCoeffs Wi.W x) Q S
      ≤ ((Q : ℝ)^2 + 2 * x) * coeffEnergy (weightCoeffs Wi.W x) S := h_LSI
    _ ≤ ((Q : ℝ)^2 + 2 * x) * (4 * WsupNormSq Wi.W * x * Real.log (2 * x)) :=
        mul_le_mul_of_nonneg_left h_energy h_factor_nn
    _ = 4 * WsupNormSq Wi.W * ((Q : ℝ)^2 + 2 * x) * x * Real.log (2 * x) := by ring

/-! ## TS6-G: TS4 Corollary 1.2 (unweighted form, constant 2) -/

/-- **TS6-G — TS4 Corollary 1.2 (unweighted form, improved constant).**

Same hypotheses; the unweighted sum is bounded with constant 2:

  `∑_{q ≤ Q, q prime}  AWstar  ≤  2 · ‖W‖_∞² · (Q² + 2x) · x · log(2x)`.

Follows from TS6-F by dividing through by `q ≥ 2`. -/
theorem TS4_unweighted_effective_bound
    (chebyshev : ChebyshevThetaBound) (largeSieve : LargeSieveInequality)
    (Wi : WeightInput) (x : ℝ) (Q : ℕ) (S : Finset ℕ)
    (hx : 2 ≤ x) (hQ : 2 ≤ Q)
    (hS : ∀ p ∈ S, p.Prime ∧ (x / 2 ≤ (p : ℝ)) ∧ ((p : ℝ) ≤ 2 * x)) :
    primeCappedSum (weightCoeffs Wi.W x) Q S ≤
      2 * WsupNormSq Wi.W * ((Q : ℝ)^2 + 2 * x) * x * Real.log (2 * x) := by
  have h_weighted := TS4_weighted_effective_bound chebyshev largeSieve
    Wi x Q S hx hQ hS
  have h_double : 2 * primeCappedSum (weightCoeffs Wi.W x) Q S ≤
                  weightedPrimeCappedSum (weightCoeffs Wi.W x) Q S := by
    unfold primeCappedSum weightedPrimeCappedSum
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro q hq
    rw [Finset.mem_filter, Finset.mem_Icc] at hq
    obtain ⟨⟨hq_lb, _⟩, _hq_prime⟩ := hq
    have hq_ne_zero : q ≠ 0 := by omega
    simp only [dif_pos hq_ne_zero]
    haveI : NeZero q := ⟨hq_ne_zero⟩
    have h_q_ge2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq_lb
    have h_AW_nn : 0 ≤ AWstar (weightCoeffs Wi.W x) q S :=
      AWstar_nonneg _ _ _
    nlinarith [h_q_ge2, h_AW_nn]
  linarith

/-! ## TS6-E: TS3 Theorem 1.1 (first effective bound, constant 4) -/

/-- **TS6-E — TS3 Theorem 1.1 (first effective bound, constant 4).**

The TS3 theorem is weaker than TS6-G (constant 4 vs 2), but it is the
historical first bound of the programme. Here derived as an immediate
corollary of TS6-G (`TS4_unweighted_effective_bound`). -/
theorem TS3_first_effective_bound
    (chebyshev : ChebyshevThetaBound) (largeSieve : LargeSieveInequality)
    (Wi : WeightInput) (x : ℝ) (Q : ℕ) (S : Finset ℕ)
    (hx : 2 ≤ x) (hQ : 2 ≤ Q)
    (hS : ∀ p ∈ S, p.Prime ∧ (x / 2 ≤ (p : ℝ)) ∧ ((p : ℝ) ≤ 2 * x)) :
    primeCappedSum (weightCoeffs Wi.W x) Q S ≤
      4 * WsupNormSq Wi.W * ((Q : ℝ)^2 + 2 * x) * x * Real.log (2 * x) := by
  have h_unweighted := TS4_unweighted_effective_bound chebyshev largeSieve
    Wi x Q S hx hQ hS
  have h_WsupNormSq_nn : 0 ≤ WsupNormSq Wi.W := WsupNormSq_nonneg _
  have hcore : 0 ≤ ((Q : ℝ)^2 + 2 * x) * x * Real.log (2 * x) := by
    have hA : 0 ≤ ((Q : ℝ)^2 + 2 * x) := by nlinarith [sq_nonneg (Q : ℝ)]
    have : 0 ≤ Real.log (2 * x) := Real.log_nonneg (by linarith)
    positivity
  nlinarith [mul_nonneg h_WsupNormSq_nn hcore]

end TS6.Effective
