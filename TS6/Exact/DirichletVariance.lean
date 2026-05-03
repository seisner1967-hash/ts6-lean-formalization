/-
# TS6/Exact/DirichletVariance.lean

**TS6-B — Specialization to `G = (ℤ/qℤ)ˣ`: TS2 Theorem 2.1.**

For every integer `q ≥ 2`, every finite set `S ⊂ ℕ` (in the paper: primes
in a compact window [x/2, 2x] supporting the weight W), and every
coefficient sequence `a : ℕ → ℂ`:

    AWstar a q S  =  CW a q S

where

    θ a q S r   = ∑_{n ∈ S, n ≡ r (q)}  a n
    θbar a q S  = (1/φ(q)) · ∑_{r ∈ (ZMod q)ˣ}  θ a q S r
    AWstar a q S = ∑_{r ∈ (ZMod q)ˣ}  ‖θ a q S r - θbar a q S‖²
    twistSum χ   = ∑_{n ∈ S}  a n · χ(n)
    CW a q S    = (1/φ(q)) · ∑_{χ ≠ χ₀}  ‖twistSum χ‖²

## Proof plan

This is a direct specialization of `parseval_identity` (TS6-A) to
`G = (ZMod q)ˣ` with `f : (ZMod q)ˣ → ℂ` defined by `f r = θ a q S r`.

Two bijections are needed:

  * `variance f = AWstar a q S` — trivial unfolding of definitions.
  * `characterSideMS f = CW a q S` — uses the correspondence
    `MulChar (ZMod q)ˣ ℂ ≃ DirichletCharacter ℂ q`, which Mathlib provides
    through `DirichletCharacter.equivMulChar` (or its current name).

## Mathlib dependencies

  * `TS6.Exact.FiniteCharacterVariance` — the abstract kernel.
  * `Mathlib.NumberTheory.DirichletCharacter.Basic` — the Dirichlet character type.
  * `Mathlib.Data.ZMod.Units` — `(ZMod q)ˣ` as a finite abelian group.

## Status

YELLOW — statements typed, proof plan documented, `sorry` explicit.
-/

import TS6.Exact.FiniteCharacterVariance
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.Data.ZMod.Units
import Mathlib.Data.Nat.Totient

namespace TS6.Exact.Dirichlet

open BigOperators Finset Complex TS6.Exact

variable (q : ℕ) [NeZero q]

-- Enable classical decidability (ℂ lacks DecidableEq; DirichletCharacter inherits)
attribute [local instance] Classical.propDecidable

-- Fintype for DirichletCharacter ℂ q (API_CHECK: Mathlib v4.16.0 name not yet found)
noncomputable instance (q : ℕ) [NeZero q] : Fintype (DirichletCharacter ℂ q) := inferInstance

/-! ## Ray-class sum and empirical mean -/

/-- Residue-class sum:  `θ a q S r  = ∑_{n ∈ S, n ≡ r (q)}  a n`.

  Written with the convention that `r : (ZMod q)ˣ` and we project it to
  the underlying `ZMod q` value for the congruence test. -/
noncomputable def θ (a : ℕ → ℂ) (q : ℕ) (S : Finset ℕ) (r : (ZMod q)ˣ) : ℂ :=
  ∑ n ∈ S, if (n : ZMod q) = (r : ZMod q) then a n else 0

/-- Empirical mean over invertible residue classes. -/
noncomputable def θbar (a : ℕ → ℂ) (q : ℕ) [NeZero q] (S : Finset ℕ) : ℂ :=
  (∑ r : (ZMod q)ˣ, θ a q S r) / (Nat.totient q : ℂ)

/-- Empirically-centered variance. -/
noncomputable def AWstar (a : ℕ → ℂ) (q : ℕ) [NeZero q] (S : Finset ℕ) : ℝ :=
  ∑ r : (ZMod q)ˣ, ‖θ a q S r - θbar a q S‖ ^ 2

/-- Twist of `a` by a Dirichlet character `χ`:  `∑_n a n · χ(n)`. -/
noncomputable def twistSum
    (a : ℕ → ℂ) (q : ℕ) (S : Finset ℕ) (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ n ∈ S, a n * χ n

/-- Character-side mean square:
    `(1/φ(q)) · ∑_{χ non-principal mod q}  ‖twistSum χ‖²`. -/
noncomputable def CW (a : ℕ → ℂ) (q : ℕ) [NeZero q] (S : Finset ℕ) : ℝ :=
  (1 / (Nat.totient q : ℝ)) *
    (∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (· ≠ 1),
      ‖twistSum a q S χ‖ ^ 2)

/-! ## The identity -/

-- NOTE: BIJECTION_STEP (HARD, ~3-6h estimated).
-- Requires the MulChar (ZMod q)^x C <-> DirichletCharacter C q bijection.
-- DirichletCharacter C q = MulChar (ZMod q) C (abbrev). The bijection
-- e : MulChar (ZMod q)^x C ~ MulChar (ZMod q) C is NOT trivially
-- equivToUnitHom.trans equivToUnitHom.symm (type mismatch on G^x^x vs G^x).
-- Likely path: MulChar.toMonoidHom + MulChar.ofUnitHom composition.
/-- **The MulChar/Dirichlet equivalence.**

For any positive modulus `q`, multiplicative characters on `(ZMod q)ˣ`
are canonically equivalent to Dirichlet characters modulo `q`.
Built by chaining three Mathlib equivalences:
`equivToUnitHom` (both directions) and `monoidHomCongr (toUnits.symm)`. -/
noncomputable def mulchar_dirichlet_equiv (q : ℕ) [NeZero q] :
    MulChar (ZMod q)ˣ ℂ ≃ DirichletCharacter ℂ q :=
  MulChar.equivToUnitHom.trans
    ((MulEquiv.monoidHomCongr (toUnits (G := (ZMod q)ˣ)).symm
        (MulEquiv.refl ℂˣ)).toEquiv.trans
     MulChar.equivToUnitHom.symm)

/-- Auxiliary: `MulChar.equivToUnitHom` sends 1 to 1.
Routed through `MulChar.mulEquivToUnitHom` which is a real `MulEquiv`
and thus has `map_one` via `MonoidHomClass`. -/
lemma MulChar_equivToUnitHom_one
    (M : Type*) [CommMonoid M] (R : Type*) [CommMonoidWithZero R] :
    (@MulChar.equivToUnitHom M _ R _) 1 = 1 :=
  map_one (@MulChar.mulEquivToUnitHom M _ R _)

/-- Auxiliary: `equivToUnitHom.symm` sends 1 to 1. Same routing via mulEquivToUnitHom. -/
lemma MulChar_equivToUnitHom_symm_one
    (M : Type*) [CommMonoid M] (R : Type*) [CommMonoidWithZero R] :
    (@MulChar.equivToUnitHom M _ R _).symm 1 = 1 :=
  map_one (@MulChar.mulEquivToUnitHom M _ R _).symm

/-- The bijection sends the trivial character to the principal Dirichlet character. -/
lemma mulchar_dirichlet_equiv_one (q : ℕ) [NeZero q] :
    mulchar_dirichlet_equiv q 1 = 1 := by
  unfold mulchar_dirichlet_equiv
  simp [MulChar_equivToUnitHom_one, MulChar_equivToUnitHom_symm_one]

/-- Auxiliary: MulChar.equivToUnitHom is multiplicative. -/
lemma MulChar_equivToUnitHom_mul
    (M : Type*) [CommMonoid M] (R : Type*) [CommMonoidWithZero R]
    (χ₁ χ₂ : MulChar M R) :
    (@MulChar.equivToUnitHom M _ R _) (χ₁ * χ₂)
      = (@MulChar.equivToUnitHom M _ R _) χ₁
        * (@MulChar.equivToUnitHom M _ R _) χ₂ :=
  map_mul (@MulChar.mulEquivToUnitHom M _ R _) χ₁ χ₂

/-- Auxiliary: MulChar.equivToUnitHom.symm is multiplicative. -/
lemma MulChar_equivToUnitHom_symm_mul
    (M : Type*) [CommMonoid M] (R : Type*) [CommMonoidWithZero R]
    (f₁ f₂ : Mˣ →* Rˣ) :
    (@MulChar.equivToUnitHom M _ R _).symm (f₁ * f₂)
      = (@MulChar.equivToUnitHom M _ R _).symm f₁
        * (@MulChar.equivToUnitHom M _ R _).symm f₂ :=
  map_mul (@MulChar.mulEquivToUnitHom M _ R _).symm f₁ f₂

/-- The bijection is multiplicative: sends products to products. -/
lemma mulchar_dirichlet_equiv_mul (q : ℕ) [NeZero q]
    (χ₁ χ₂ : MulChar (ZMod q)ˣ ℂ) :
    mulchar_dirichlet_equiv q (χ₁ * χ₂)
      = mulchar_dirichlet_equiv q χ₁ * mulchar_dirichlet_equiv q χ₂ := by
  unfold mulchar_dirichlet_equiv
  simp [Equiv.trans_apply, MulChar_equivToUnitHom_mul,
        MulChar_equivToUnitHom_symm_mul, map_mul]

/-- The bijection commutes with inversion. -/
lemma mulchar_dirichlet_equiv_inv (q : ℕ) [NeZero q]
    (χ : MulChar (ZMod q)ˣ ℂ) :
    mulchar_dirichlet_equiv q χ⁻¹ = (mulchar_dirichlet_equiv q χ)⁻¹ := by
  apply eq_inv_of_mul_eq_one_right
  rw [← mulchar_dirichlet_equiv_mul, mul_inv_cancel, mulchar_dirichlet_equiv_one]

/-- Evaluation of the bijection on a unit: for u : (ZMod q)x, the value at (u : ZMod q)
equals chi u. -/
lemma mulchar_dirichlet_equiv_apply_unit (q : ℕ) [NeZero q]
    (χ : MulChar (ZMod q)ˣ ℂ) (u : (ZMod q)ˣ) :
    mulchar_dirichlet_equiv q χ (u : ZMod q) = χ u := by
  unfold mulchar_dirichlet_equiv
  simp [Equiv.trans_apply, MulEquiv.coe_toEquiv, MulEquiv.monoidHomCongr_apply,
        MulEquiv.refl_apply, MulChar.equivToUnitHom_symm_coe,
        MulChar.coe_equivToUnitHom, toUnits_val_apply]

/-- Evaluation of the bijection on a non-unit: the Dirichlet character vanishes. -/
lemma mulchar_dirichlet_equiv_apply_nonunit (q : ℕ) [NeZero q]
    (χ : MulChar (ZMod q)ˣ ℂ) (n : ZMod q) (h : ¬ IsUnit n) :
    mulchar_dirichlet_equiv q χ n = 0 :=
  MulChar.map_nonunit _ h

/-! ### Pointwise identification: decomposition into L4a / L4b / L4c -/

/-- **L4a - Sum swap.** Reorganize the double sum. -/
lemma fourierCoeff_θ_swap
    (a : ℕ → ℂ) (q : ℕ) [NeZero q] (S : Finset ℕ)
    (χ : MulChar (ZMod q)ˣ ℂ) :
    fourierCoeff (θ a q S) χ
      = ∑ n ∈ S, ∑ r : (ZMod q)ˣ,
          (if (n : ZMod q) = (r : ZMod q) then a n * star (χ r) else 0) := by
  unfold fourierCoeff θ
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  split_ifs with h <;> simp [h]

/-- **L4b - Inner sum evaluation.** For fixed n, evaluate the r-sum. -/
lemma fourierCoeff_θ_inner_sum
    (q : ℕ) [NeZero q] (χ : MulChar (ZMod q)ˣ ℂ) (a : ℕ → ℂ) (n : ℕ) :
    (∑ r : (ZMod q)ˣ,
        (if (n : ZMod q) = (r : ZMod q) then a n * star (χ r) else 0))
      = a n * (mulchar_dirichlet_equiv q χ)⁻¹ (n : ZMod q) := by
  by_cases hu : IsUnit (n : ZMod q)
  · -- Case 1: (n : ZMod q) is a unit. Pivot the sum at u := hu.unit.
    set u : (ZMod q)ˣ := hu.unit with hu_def
    have hu_val : (u : ZMod q) = (n : ZMod q) := hu.unit_spec
    have hsum : (∑ r : (ZMod q)ˣ,
          (if (n : ZMod q) = (r : ZMod q) then a n * star (χ r) else 0))
        = a n * star (χ u) := by
      rw [Finset.sum_eq_single u]
      · rw [if_pos hu_val.symm]
      · intro r _ hru
        apply if_neg
        intro heq
        apply hru
        apply Units.ext
        rw [hu_val]; exact heq.symm
      · intro h; exact absurd (Finset.mem_univ u) h
    rw [hsum]
    congr 1
    rw [mulChar_star_apply_eq_inv χ u,
        ← mulchar_dirichlet_equiv_apply_unit q χ⁻¹ u,
        mulchar_dirichlet_equiv_inv q χ,
        hu_val]
  · -- Case 2: (n : ZMod q) is NOT a unit; both sides = 0
    have hsum : (∑ r : (ZMod q)ˣ,
        (if (n : ZMod q) = (r : ZMod q) then a n * star (χ r) else 0)) = 0 := by
      apply Finset.sum_eq_zero
      intro r _
      rw [if_neg]
      intro heq
      exact hu (heq ▸ (Units.isUnit r))
    have hchi : (mulchar_dirichlet_equiv q χ)⁻¹ (n : ZMod q) = 0 := by
      rw [MulChar.inv_apply_eq_inv']
      rw [mulchar_dirichlet_equiv_apply_nonunit q χ (n : ZMod q) hu]
      exact inv_zero
    rw [hsum, hchi, mul_zero]

/-- **L4c - Reassembly.** Combine L4a and L4b. -/
lemma fourierCoeff_θ_eq_twistSum
    (a : ℕ → ℂ) (q : ℕ) [NeZero q] (S : Finset ℕ)
    (χ : MulChar (ZMod q)ˣ ℂ) :
    fourierCoeff (θ a q S) χ = twistSum a q S (mulchar_dirichlet_equiv q χ)⁻¹ := by
  rw [fourierCoeff_θ_swap]
  unfold twistSum
  exact Finset.sum_congr rfl (fun n _ => fourierCoeff_θ_inner_sum q χ a n)

/-- **Pointwise identification** of Fourier coefficients with Dirichlet twist sums. -/
lemma norm_fourierCoeff_eq_norm_twistSum
    (a : ℕ → ℂ) (q : ℕ) [NeZero q] (S : Finset ℕ)
    (χ : MulChar (ZMod q)ˣ ℂ) :
    fourierCoeff (θ a q S) χ = twistSum a q S (mulchar_dirichlet_equiv q χ)⁻¹ :=
  fourierCoeff_θ_eq_twistSum a q S χ

/-- **Combinatorial step**: sum over non-principal MulChars = sum over non-principal
Dirichlet characters, via the bijection χ ↦ (mulchar_dirichlet_equiv q χ)⁻¹.
The inversion matches the inverse appearing in norm_fourierCoeff_eq_norm_twistSum. -/
lemma bijection_step
    (a : ℕ → ℂ) (q : ℕ) [NeZero q] (S : Finset ℕ) :
    (∑ χ ∈ (Finset.univ : Finset (MulChar (ZMod q)ˣ ℂ)).filter (· ≠ 1),
        ‖fourierCoeff (θ a q S) χ‖ ^ 2)
    = (∑ ψ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (· ≠ 1),
        ‖twistSum a q S ψ‖ ^ 2) := by
  refine Finset.sum_bij (fun χ _ => (mulchar_dirichlet_equiv q χ)⁻¹) ?_ ?_ ?_ ?_
  -- (1) membership: χ ≠ 1  ⟹  (equiv χ)⁻¹ ≠ 1
  · intro χ hχ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hχ ⊢
    intro h
    apply hχ
    have h1 : mulchar_dirichlet_equiv q χ = 1 := inv_eq_one.mp h
    exact (mulchar_dirichlet_equiv q).injective
      (h1.trans (mulchar_dirichlet_equiv_one q).symm)
  -- (2) injectivity: (equiv χ₁)⁻¹ = (equiv χ₂)⁻¹  ⟹  χ₁ = χ₂
  · intro χ₁ _ χ₂ _ h
    exact (mulchar_dirichlet_equiv q).injective (inv_injective h)
  -- (3) surjectivity: given ψ ≠ 1, take χ = equiv⁻¹ (ψ⁻¹); then (equiv χ)⁻¹ = ψ
  · intro ψ hψ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hψ
    refine ⟨(mulchar_dirichlet_equiv q).symm ψ⁻¹, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      intro h
      apply hψ
      have h1 : ψ⁻¹ = 1 := by
        have := congrArg (mulchar_dirichlet_equiv q) h
        rwa [Equiv.apply_symm_apply, mulchar_dirichlet_equiv_one] at this
      exact inv_eq_one.mp h1
    · -- Goal: (equiv (equiv.symm ψ⁻¹))⁻¹ = ψ
      have h_apply : mulchar_dirichlet_equiv q ((mulchar_dirichlet_equiv q).symm ψ⁻¹) = ψ⁻¹ :=
        (mulchar_dirichlet_equiv q).apply_symm_apply ψ⁻¹
      calc (mulchar_dirichlet_equiv q ((mulchar_dirichlet_equiv q).symm ψ⁻¹))⁻¹
          = (ψ⁻¹)⁻¹ := by rw [h_apply]
        _ = ψ := inv_inv ψ
  -- (4) pointwise equality of squared norms (from the complex equality)
  · intro χ _
    congr 1
    exact congrArg norm (norm_fourierCoeff_eq_norm_twistSum a q S χ)

/-- **TS6-B: TS2 Theorem 2.1 — Exact identity for general modulus `q ≥ 2`.**

For every integer `q ≥ 2`, every finite `S ⊂ ℕ`, and every `a : ℕ → ℂ`:

    AWstar a q S  =  CW a q S.

Direct specialization of `TS6.Exact.parseval_identity` to the finite
abelian group `G = (ZMod q)ˣ` and the function `f r = θ a q S r`. -/
theorem TS2_exact_identity
    (a : ℕ → ℂ) (q : ℕ) [NeZero q] (hq : 2 ≤ q) (S : Finset ℕ) :
    AWstar a q S = CW a q S := by
  -- Proof plan:
  --
  -- Step 1 (variance side): By unfolding,
  --     variance f  =  ∑ r, ‖f r - mean f‖²
  --                 =  AWstar a q S
  --   since `f r = θ a q S r` and `mean f = θbar a q S`.
  --   (The division by `|G| = φ(q)` matches because `Fintype.card (ZMod q)ˣ = φ(q)`
  --    by `ZMod.card_units` or `Nat.totient_eq_card_units_ZMod`.)
  --
  -- Step 2 (character side): There is a bijection
  --     e : MulChar (ZMod q)ˣ ℂ  ≃  DirichletCharacter ℂ q
  --   induced by extending a multiplicative character on units to a
  --   function on ZMod q by zero on non-units. Under this bijection:
  --     – the trivial MulChar maps to the principal Dirichlet character χ₀,
  --     – fourierCoeff f χ  matches  twistSum a q S (e χ), because
  --         fourierCoeff f χ  = ∑_r (θ a q S r) · conj (χ r)
  --                          = ∑_{n ∈ S, (n,q)=1} a n · conj (χ (nᴿ))
  --                          = ∑_n a n · (e χ) n  =  twistSum a q S (e χ),
  --   where the last step uses that e χ vanishes on non-units.
  --   (The conjugate disappears because on a finite abelian group,
  --    the set of MulChars is closed under conjugation and we can
  --    reindex.)
  --
  --   Hence `characterSideMS f = CW a q S`.
  --
  -- Step 3: Apply `parseval_identity f` to conclude.
  -- Bloc A: AWstar = variance (θ a q S), via mean (θ) = θbar
  have hA : AWstar a q S = variance (θ a q S) := by
    unfold AWstar variance
    have h_mean : mean (θ a q S) = θbar a q S := by
      unfold mean θbar
      rw [show (Fintype.card (ZMod q)ˣ : ℂ) = (Nat.totient q : ℂ) from by
            exact_mod_cast ZMod.card_units_eq_totient q]
    simp_rw [h_mean]
  -- Bloc B: variance = characterSideMS via parseval_identity
  have hB : variance (θ a q S) = characterSideMS (θ a q S) :=
    parseval_identity (θ a q S)
  -- Bloc C: characterSideMS (θ a q S) = CW a q S
  have hC : characterSideMS (θ a q S) = CW a q S := by
    unfold characterSideMS CW
    have h_card : (Fintype.card (ZMod q)ˣ : ℝ) = (Nat.totient q : ℝ) := by
      exact_mod_cast ZMod.card_units_eq_totient q
    rw [h_card]
    congr 1
    -- BIJECTION_STEP: reduced to norm_fourierCoeff_eq_norm_twistSum (POINTWISE_STEP)
    exact bijection_step a q S -- BIJECTION_STEP: ∑_{χ≠1, MulChar Gˣ ℂ} ‖fourierCoeff θ χ‖²
          --               = ∑_{ψ≠1, DirichletCharacter ℂ q} ‖twistSum a q S ψ‖²
  rw [hA, hB, hC]

-- NOTE: CASCADE of TS2_exact_identity. Immediate once TS2 is closed:
--   exact TS2_exact_identity a q hq.two_le S
/-- **Prime-modulus corollary (TS1 Theorem 3.1).**

For prime `q`, every non-principal Dirichlet character mod `q` is
primitive, so the sum defining `CW` runs over all primitive characters. -/
theorem TS1_exact_identity
    (a : ℕ → ℂ) (q : ℕ) [NeZero q] (hq : q.Prime) (S : Finset ℕ) :
    AWstar a q S = CW a q S := by
  -- Immediate from TS2_exact_identity since q prime implies q ≥ 2.
  exact TS2_exact_identity a q hq.two_le S

end TS6.Exact.Dirichlet
