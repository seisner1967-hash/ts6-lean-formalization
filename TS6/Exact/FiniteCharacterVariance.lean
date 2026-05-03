/-
# TS6/Exact/FiniteCharacterVariance.lean

**TS6-A — Abstract Parseval identity on a finite abelian group.**

Isolates the algebraic kernel shared by TS1 Theorem 3.1 (prime q) and
TS2 Theorem 2.1 (general q ≥ 2). No primes, no Dirichlet characters,
no analysis: pure finite Fourier transform.

## Statement (informal)

Let `G` be a finite abelian group and `f : G → ℂ`. With

  * `mean f   = (1/|G|) · ∑ g, f g`
  * `variance f = ∑ g, ‖f g - mean f‖²`
  * `fourierCoeff f χ = ∑ g, f g · conj (χ g)`
  * `characterSideMS f = (1/|G|) · ∑_{χ ≠ 1} ‖fourierCoeff f χ‖²`

we have **`variance f = characterSideMS f`**.

## Proof plan

Three steps:

1. Show that `variance f = ∑ g, ‖f g‖² - |G| · ‖mean f‖²`
   by expanding the squared norm and using `∑ g, (f g - mean f) = 0`.

2. Show by Plancherel on the full character group
   `∑_{χ} ‖fourierCoeff f χ‖² = |G| · ∑ g, ‖f g‖²`.
   This is the finite-dimensional Plancherel identity.

3. Isolate the principal-character term:
   `fourierCoeff f 1 = ∑ g, f g = |G| · mean f`,
   so `‖fourierCoeff f 1‖² = |G|² · ‖mean f‖²`.

4. Combine: `characterSideMS f = (1/|G|) · (∑_{χ} ‖·‖² - |G|²‖mean f‖²)
                               = ∑ g, ‖f g‖² - |G|‖mean f‖²
                               = variance f`.

## Mathlib dependencies

  * `Mathlib.NumberTheory.MulChar.Basic` — `MulChar G ℂ`, the orthogonality
    relation `MulChar.sum_apply_eq_zero_iff`.
  * `Mathlib.Analysis.Complex.Basic` — `Complex.normSq`, `star`.
  * `Mathlib.Algebra.BigOperators.Basic` — `Finset.sum`.

## Status

YELLOW — statements typed, proof plan documented in comments, `sorry`
explicit at the closure point of each theorem. To reach GREEN, one Lean
session with Mathlib4 is needed.
-/

import Mathlib.NumberTheory.MulChar.Basic
import Mathlib.NumberTheory.MulChar.Duality
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Analysis.Complex.Polynomial.Basic

namespace TS6.Exact

open BigOperators Finset Complex

variable {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G]

-- Enable classical decidability locally (ℂ lacks DecidableEq;
-- MulChar G ℂ inherits classical decidability from this)
attribute [local instance] Classical.propDecidable

-- Fintype instance for MulChar G ℂ: the character group of a finite abelian group
-- has the same cardinality as G (|Ĝ| = |G|). Mathematically trivial; API_CHECK:
-- exact Mathlib v4.16.0 name not yet identified, using classical sorry placeholder.
noncomputable instance : Fintype (MulChar G ℂ) := .ofFinite _

/-! ## Definitions -/

/-- The empirical mean of `f : G → ℂ`. -/
noncomputable def mean (f : G → ℂ) : ℂ :=
  (∑ g : G, f g) / (Fintype.card G : ℂ)

/-- The centered variance of `f : G → ℂ`. -/
noncomputable def variance (f : G → ℂ) : ℝ :=
  ∑ g : G, ‖f g - mean f‖ ^ 2

/-- Fourier coefficient at the character `χ`:
    `fourierCoeff f χ = ∑ g, f g · conj (χ g)`. -/
noncomputable def fourierCoeff (f : G → ℂ) (χ : MulChar G ℂ) : ℂ :=
  ∑ g : G, f g * star (χ g)

/-- Character-side mean square:
    `(1/|G|) · ∑_{χ ≠ 1} ‖fourierCoeff f χ‖²`. -/
noncomputable def characterSideMS (f : G → ℂ) : ℝ :=
  (1 / (Fintype.card G : ℝ)) *
    (∑ χ ∈ (Finset.univ : Finset (MulChar G ℂ)).filter (· ≠ 1),
      ‖fourierCoeff f χ‖ ^ 2)

/-! ## Orthogonality lemmas (kernel interface) -/

omit [DecidableEq G] in
/-- **Character sum lemma.** For `χ : MulChar G ℂ` on a finite abelian group,
`∑ g, χ g = |G|` if `χ = 1` and `0` otherwise.

Mathlib source: `MulChar.sum_apply_eq_zero_iff` combined with the trivial
evaluation of the principal character. -/
theorem sum_character_eq (χ : MulChar G ℂ) :
    (∑ g : G, χ g) = if χ = 1 then (Fintype.card G : ℂ) else 0 := by
  split_ifs with h
  · -- χ = 1: each χ g = 1 since every g is a unit in CommGroup G
    subst h
    have h1 : ∀ g : G, (1 : MulChar G ℂ) g = 1 := fun g =>
      MulChar.one_apply (Group.isUnit g)
    simp [h1, Finset.card_univ]
  · -- χ ≠ 1: nontrivial character sum vanishes
    exact MulChar.sum_eq_zero_of_ne_one h

omit [DecidableEq G] in
/-- **Star-inverse identity for MulChar values on a finite group.**
For `ψ : MulChar G ℂ` with `G` a finite commutative group, the complex
conjugate of `ψ g` equals the value of the inverse character at `g`:
`star (ψ g) = ψ⁻¹ g`.

Proof: character values are roots of unity (`ψ g` satisfies `x^|G| = 1`),
hence `‖ψ g‖ = 1`, hence `ψ g · star (ψ g) = ‖ψ g‖² = 1`, and
`ψ⁻¹ g = (ψ g)⁻¹` via `MulChar.inv_apply_eq_inv'`. -/
theorem mulChar_star_apply_eq_inv (ψ : MulChar G ℂ) (g : G) :
    star (ψ g) = (ψ⁻¹ : MulChar G ℂ) g := by
  have hpow : (ψ g) ^ Fintype.card G = 1 := by
    rw [← map_pow, pow_card_eq_one, map_one]
  have habs : ‖ψ g‖ = 1 := by
    have h1 : ‖ψ g‖ ^ Fintype.card G = 1 := by
      rw [← norm_pow, hpow, norm_one]
    have hnn : 0 ≤ ‖ψ g‖ := norm_nonneg _
    have hpos : 0 < Fintype.card G := Fintype.card_pos
    exact (pow_left_inj₀ hnn zero_le_one hpos.ne').mp
      (h1.trans (one_pow _).symm)
  have hne : ψ g ≠ 0 := by
    intro h
    rw [h, norm_zero] at habs
    exact zero_ne_one habs
  have hstar : star (ψ g) = (starRingEnd ℂ) (ψ g) := rfl
  have hmul : ψ g * star (ψ g) = 1 := by
    rw [hstar]
    have hc : (ψ g) * (starRingEnd ℂ) (ψ g) = ‖ψ g‖ ^ 2 := Complex.mul_conj' (ψ g)
    rw [hc, habs]
    push_cast
    ring
  rw [MulChar.inv_apply_eq_inv']
  exact eq_inv_of_mul_eq_one_right hmul

omit [DecidableEq G] in
/-- **Schur orthogonality** on a finite abelian group:
`∑ g, χ g · conj (ψ g) = |G| · [χ = ψ]`.

Proof: apply `sum_character_eq` to `χ * ψ⁻¹`, noting that character values
on a finite group are roots of unity so `(ψ g)⁻¹ = conj (ψ g)`. -/
theorem schur_orthogonality (χ ψ : MulChar G ℂ) :
    (∑ g : G, χ g * star (ψ g)) =
      if χ = ψ then (Fintype.card G : ℂ) else 0 := by
  have key : ∀ g : G, star (ψ g) = (ψ⁻¹ : MulChar G ℂ) g :=
    fun g => mulChar_star_apply_eq_inv ψ g
  have rewrite_sum : (∑ g : G, χ g * star (ψ g)) = ∑ g : G, (χ * ψ⁻¹) g := by
    apply Finset.sum_congr rfl
    intro g _
    rw [key g, MulChar.mul_apply]
  rw [rewrite_sum, sum_character_eq]
  by_cases heq : χ = ψ
  · subst heq
    simp
  · have hne : χ * ψ⁻¹ ≠ 1 := fun hprod => heq (by
      -- From χ * ψ⁻¹ = 1, multiply on the right by ψ to get χ = ψ
      have := congr_arg (fun x => x * ψ) hprod
      simp [mul_assoc, inv_mul_cancel, one_mul] at this
      exact this)
    simp [heq, hne]

/-! ## Sub-lemmas for `parseval_identity` -/

/-- Step 1 (König-Huygens identity): the variance of `f` equals the sum of
squared moduli minus `|G|` times the squared modulus of the mean. -/
private lemma variance_eq_sum_sq_minus_card_meanSq (f : G → ℂ) :
    (variance f : ℝ) = (∑ g : G, ‖f g‖ ^ 2) - (Fintype.card G : ℝ) * ‖mean f‖ ^ 2 := by
  unfold variance
  have h_normSq : ∀ z : ℂ, ‖z‖ ^ 2 = Complex.normSq z := fun z => by
    rw [Complex.norm_eq_abs]; exact Complex.sq_abs z
  simp_rw [h_normSq, Complex.normSq_sub]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
      Finset.card_univ]
  have h_cross : (∑ g : G, 2 * (f g * (starRingEnd ℂ) (mean f)).re) =
      2 * (Fintype.card G : ℝ) * Complex.normSq (mean f) := by
    rw [← Finset.mul_sum]
    rw [show (∑ g : G, (f g * (starRingEnd ℂ) (mean f)).re) =
        ((∑ g : G, f g) * (starRingEnd ℂ) (mean f)).re by
      rw [← Complex.re_sum, ← Finset.sum_mul]]
    have h_sum_eq : (∑ g : G, f g) = (Fintype.card G : ℂ) * mean f := by
      unfold mean
      have hcard : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
      field_simp
    rw [h_sum_eq, mul_assoc, Complex.mul_conj]
    simp [Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
          Complex.ofReal_re, Complex.ofReal_im]
    ring
  linarith [h_cross]

/-- Step 3 of Parseval: the squared modulus of the principal-character
Fourier coefficient equals `|G|² · ‖mean f‖²`. -/
private lemma fourierCoeff_one_normSq (f : G → ℂ) :
    ‖fourierCoeff f 1‖ ^ 2 = (Fintype.card G : ℝ) ^ 2 * ‖mean f‖ ^ 2 := by
  unfold fourierCoeff
  have h1 : ∀ g : G, (1 : MulChar G ℂ) g = 1 := fun g => MulChar.one_apply (Group.isUnit g)
  simp_rw [h1, star_one, mul_one]
  have h_sum_eq : (∑ g : G, f g) = (Fintype.card G : ℂ) * mean f := by
    unfold mean
    have hcard : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    field_simp
  rw [h_sum_eq, norm_mul, Complex.norm_natCast, mul_pow]

/-- **Dual Schur orthogonality** : sum over characters at fixed elements.

For `a, b : G` in a finite abelian group, `∑_χ χ(a) · star (χ(b)) = |G| · [a = b]`.
This is the Pontryagin dual of `schur_orthogonality`. Proved here via the same
machinery: AUX1 (root-of-unity gives `star (χ b) = (χ b)⁻¹`) + AUX2 (character
sum collapse via `MulChar.exists_apply_ne_one_of_hasEnoughRootsOfUnity`). -/
private theorem schur_orthogonality_dual (a b : G) :
    (∑ χ : MulChar G ℂ, χ a * star (χ b)) =
      if a = b then (Fintype.card G : ℂ) else 0 := by
  classical
  have hterm : ∀ χ : MulChar G ℂ, χ a * star (χ b) = χ (a * b⁻¹) := by
    intro χ
    have h_pow : χ b ^ Fintype.card G = 1 := by
      rw [← map_pow, pow_card_eq_one, map_one]
    have h_norm : ‖χ b‖ = 1 := by
      have hpow_norm : ‖χ b‖ ^ Fintype.card G = 1 := by
        rw [← norm_pow, h_pow, norm_one]
      have hpos : 0 < Fintype.card G := Fintype.card_pos
      have hnn : (0 : ℝ) ≤ ‖χ b‖ := norm_nonneg _
      exact (pow_eq_one_iff_of_nonneg hnn hpos.ne').mp hpow_norm
    have h_star : star (χ b) = (χ b)⁻¹ := (Complex.inv_eq_conj h_norm).symm
    rw [map_mul χ a b⁻¹]
    congr 1
    rw [h_star]
    have h_chi_inv : χ b * χ b⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel, map_one]
    exact (eq_inv_of_mul_eq_one_right h_chi_inv).symm
  rw [Finset.sum_congr rfl (fun χ _ => hterm χ)]
  have hiff : (a * b⁻¹ = 1) ↔ (a = b) := by
    constructor
    · intro h; exact mul_inv_eq_one.mp h
    · intro h; rw [h, mul_inv_cancel]
  haveI : NeZero ((Monoid.exponent Gˣ : ℕ) : ℂ) :=
    ⟨by exact_mod_cast NeZero.ne (Monoid.exponent Gˣ)⟩
  haveI : HasEnoughRootsOfUnity ℂ (Monoid.exponent Gˣ) :=
    IsAlgClosed.hasEnoughRootsOfUnity ℂ _
  by_cases hg : a * b⁻¹ = 1
  · rw [hg, if_pos (hiff.mp hg)]
    simp_rw [map_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    congr 1
    rw [← Nat.card_eq_fintype_card (α := MulChar G ℂ),
        MulChar.card_eq_card_units_of_hasEnoughRootsOfUnity G ℂ,
        Nat.card_congr (toUnits (G := G)).toEquiv.symm,
        Nat.card_eq_fintype_card]
  · rw [if_neg (fun heq => hg (hiff.mpr heq))]
    obtain ⟨χ, hχ⟩ := MulChar.exists_apply_ne_one_of_hasEnoughRootsOfUnity G ℂ hg
    refine eq_zero_of_mul_eq_self_left hχ ?_
    simp only [Finset.mul_sum, ← MulChar.mul_apply]
    exact Fintype.sum_bijective _ (Group.mulLeft_bijective χ) _ _ fun χ' ↦ rfl

/-- Step 2 of Parseval: total Plancherel for the Fourier coefficients. -/
private lemma sum_fourierCoeff_normSq_eq_card_mul_sum_normSq (f : G → ℂ) :
    (∑ χ : MulChar G ℂ, ‖fourierCoeff f χ‖ ^ 2 : ℝ) =
      (Fintype.card G : ℝ) * (∑ g : G, ‖f g‖ ^ 2) := by
  have h_castNormSq : ∀ z : ℂ, ((‖z‖ : ℂ)) ^ 2 = z * star z := by
    intro z
    rw [← Complex.ofReal_pow]
    rw [show (‖z‖ : ℝ) ^ 2 = Complex.normSq z from by
      rw [Complex.norm_eq_abs, ← Complex.sq_abs]]
    rw [show ((Complex.normSq z : ℝ) : ℂ) = z * star z from by
      rw [show star z = (starRingEnd ℂ) z from rfl]; exact (Complex.mul_conj z).symm]
  apply Complex.ofReal_inj.mp
  push_cast
  simp_rw [h_castNormSq]
  unfold fourierCoeff
  have step_expand : ∀ χ : MulChar G ℂ,
      (∑ g : G, f g * star (χ g)) * star (∑ h : G, f h * star (χ h)) =
      ∑ g : G, ∑ h : G, f g * star (f h) * (star (χ g) * χ h) := by
    intro χ
    rw [star_sum]
    simp_rw [star_mul', star_star]
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun g _ => Finset.sum_congr rfl fun h _ => ?_
    ring
  simp_rw [step_expand]
  calc (∑ χ : MulChar G ℂ, ∑ g : G, ∑ h : G, f g * star (f h) * (star (χ g) * χ h))
      = ∑ g : G, ∑ h : G, ∑ χ : MulChar G ℂ,
          f g * star (f h) * (star (χ g) * χ h) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun g _ => ?_
        rw [Finset.sum_comm]
    _ = ∑ g : G, ∑ h : G, f g * star (f h) *
          (∑ χ : MulChar G ℂ, star (χ g) * χ h) := by
        refine Finset.sum_congr rfl fun g _ => Finset.sum_congr rfl fun h _ => ?_
        rw [← Finset.mul_sum]
    _ = ∑ g : G, ∑ h : G, f g * star (f h) *
          (if h = g then (Fintype.card G : ℂ) else 0) := by
        refine Finset.sum_congr rfl fun g _ => Finset.sum_congr rfl fun h _ => ?_
        congr 1
        rw [show (∑ χ : MulChar G ℂ, star (χ g) * χ h) =
            (∑ χ : MulChar G ℂ, χ h * star (χ g)) from
          Finset.sum_congr rfl fun χ _ => mul_comm _ _]
        exact schur_orthogonality_dual h g
    _ = ∑ g : G, f g * star (f g) * (Fintype.card G : ℂ) := by
        refine Finset.sum_congr rfl fun g _ => ?_
        rw [Finset.sum_eq_single g]
        · rw [if_pos rfl]
        · intro h _ hne
          rw [if_neg hne, mul_zero]
        · intro h
          exact absurd (Finset.mem_univ _) h
    _ = (Fintype.card G : ℂ) * ∑ g : G, f g * star (f g) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun g _ => ?_
        ring

/-- Helper for Step 4: extract the principal character from a sum
over `χ ≠ 1`, real-valued version. -/
private lemma sum_filter_ne_one_eq_total_sub_real (f : MulChar G ℂ → ℝ) :
    (∑ χ ∈ (Finset.univ : Finset (MulChar G ℂ)).filter (· ≠ 1), f χ) =
      (∑ χ : MulChar G ℂ, f χ) - f 1 := by
  classical
  have h := Finset.sum_filter_add_sum_filter_not
    (Finset.univ : Finset (MulChar G ℂ)) (fun χ => χ = 1) f
  have hsingle :
      (∑ χ ∈ (Finset.univ : Finset (MulChar G ℂ)).filter (fun χ => χ = 1), f χ) = f 1 := by
    rw [Finset.sum_filter]
    rw [Finset.sum_eq_single (1 : MulChar G ℂ)]
    · simp
    · intro χ _ hχ; simp [hχ]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [hsingle] at h
  show (∑ χ ∈ (Finset.univ : Finset (MulChar G ℂ)).filter (fun χ => ¬ χ = 1), f χ) =
    (∑ χ : MulChar G ℂ, f χ) - f 1
  linarith

/-! ## The main identity -/

-- NOTE: PLANCHEREL_STEP (HARD, ~4-8h estimated).
-- Proof requires expanding normSq as a double sum over G*G, swapping
-- with the character sum, and applying schur_orthogonality to collapse
-- the Kronecker delta. Building blocks sum_character_eq and
-- schur_orthogonality (both proved in this file) are the entry points.
/-- **TS6-A: Parseval identity for the variance of a function on a finite
abelian group.**

For every finite abelian group `G` and every `f : G → ℂ`,
  `variance f = characterSideMS f`.

This is the algebraic kernel of both TS1 Theorem 3.1 (case of prime `q`)
and TS2 Theorem 2.1 (general `q ≥ 2`), obtained via specialization to
`G = (ZMod q)ˣ` in `TS6/Exact/DirichletVariance.lean`. -/
theorem parseval_identity (f : G → ℂ) :
    variance f = characterSideMS f := by
  -- Proof plan (4 steps):
  --
  -- Step 1: variance f = (∑ g, ‖f g‖²) - |G| · ‖mean f‖².
  --   Expand ‖f g - mean f‖² = (f g - mean f)(conj(f g) - conj(mean f)),
  --   distribute the double sum, use ∑ g, (f g - mean f) = 0 to kill the
  --   cross-terms.
  --
  -- Step 2: ∑_{χ : MulChar G ℂ} ‖fourierCoeff f χ‖² = |G| · ∑ g, ‖f g‖².
  --   Expand ‖fourierCoeff f χ‖² as (∑ g, f g · conj χ g) · (∑ h, conj f h · χ h),
  --   swap the χ and (g,h) sums, apply schur_orthogonality to collapse
  --   ∑_χ χ(g) · conj χ(h) = |G| · [g = h], keep only g = h.
  --
  -- Step 3: fourierCoeff f 1 = ∑ g, f g · conj(1 g) = ∑ g, f g = |G| · mean f.
  --   Hence ‖fourierCoeff f 1‖² = |G|² · ‖mean f‖².
  --
  -- Step 4: characterSideMS f = (1/|G|) · (∑_χ ‖·‖² - |G|²‖mean f‖²)
  --                          = (1/|G|) · (|G| · ∑ g, ‖f g‖² - |G|²‖mean f‖²)
  --                          = ∑ g, ‖f g‖² - |G|‖mean f‖²
  --                          = variance f.   (by Step 1)
  --
  -- Assembly of the 4 steps, using the private lemmas declared above:
  --   variance_eq_sum_sq_minus_card_meanSq      (Step 1)
  --   sum_fourierCoeff_normSq_eq_card_mul_sum_normSq (Step 2)
  --   fourierCoeff_one_normSq                   (Step 3)
  --   sum_filter_ne_one_eq_total_sub_real       (Step 4 helper)
  rw [variance_eq_sum_sq_minus_card_meanSq f]
  unfold characterSideMS
  rw [sum_filter_ne_one_eq_total_sub_real (fun χ => ‖fourierCoeff f χ‖ ^ 2)]
  rw [fourierCoeff_one_normSq f]
  rw [sum_fourierCoeff_normSq_eq_card_mul_sum_normSq f]
  have hcard : (Fintype.card G : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp
  ring

end TS6.Exact
