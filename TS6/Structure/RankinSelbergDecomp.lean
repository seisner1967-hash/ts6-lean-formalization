/-
# TS6/Structure/RankinSelbergDecomp.lean

**TS6-D — Rankin–Selberg decomposition (TS5 Proposition 3.7).**

For every integer `q ≥ 2`:

    AWstar a q S  =  DW a q S  -  |T₀|²/φ(q)  +  SW_q a q S

where

    DW a q S      =  ∑_{n ∈ S, (n,q) = 1}  ‖a n‖²           (diagonal)
    T₀ a q S      =  ∑_{n ∈ S, (n,q) = 1}  a n              (coprime sum)
    SW_q a q S    =  ∑_{m, n ∈ S, m ≠ n, m ≡ n (q), (mn, q) = 1}
                      a m · conj(a n)                       (off-diagonal)

This is the three-term decomposition of `CW` (hence `AWstar`, by TS6-B)
into PNT-controlled diagonal, mean-correction, and the off-diagonal
"correlation" term whose size controls the asymptotic law.

## Paper context

TS5 Proposition 3.7 and TS4's decision request document the key numerical
fact:

  – D_W  ~  10^7   (diagonal, PNT scale)
  – |T₀|²/φ(q)  ~  10^{11}   (dominates by 10⁴; subtract)
  – S_{W,q}  ~  +10^{11}     (cancels the subtraction to 5 orders of magnitude)
  – AWstar  ~  10^6 (observed)

So the naive diagonal-only candidate `M_W = D_W` overestimates `AWstar` by
a factor of ~10⁴; the cancellation between the mean correction and the
off-diagonal is what produces the observed scale. TS6-D formalizes the
identity; the numerical observations are not in scope for TS6.

## Proof plan

The identity is elementary. Expand `CW`:

    CW = (1/φ(q)) · ∑_{χ ≠ χ₀} ‖twistSum χ‖²
       = (1/φ(q)) · [∑_{χ} ‖twistSum χ‖² - ‖twistSum χ₀‖²].

The principal-character twist `twistSum χ₀` is exactly `T₀` (the coprime
sum), so the last term is `|T₀|²/φ(q)`.

For the full sum `∑_χ`: expand each norm squared as a double sum over
(m, n), use Schur orthogonality to get

    ∑_χ χ(m) · conj(χ(n)) = φ(q) · [m ≡ n (q) ∧ (mn, q) = 1].

So `∑_χ ‖twistSum χ‖² = φ(q) · ∑_{m ≡ n (q), (mn,q)=1} a(m) · conj(a(n))`.

Split this double sum by m = n (diagonal = D_W · φ(q)) vs m ≠ n
(off-diagonal = S_W · φ(q)). Divide by φ(q):

    (1/φ(q)) · ∑_χ ‖twistSum χ‖²  =  D_W + S_W.

Subtract `|T₀|²/φ(q)` to get `CW = D_W - |T₀|²/φ(q) + S_W`. Apply
TS6-B (`AWstar = CW`) and we are done.

## Status

YELLOW — statement typed, long proof plan documented, one `sorry`.

## Mathlib dependencies

  * `TS6.Exact.DirichletVariance` — for `AWstar`, `CW`, `twistSum`.
-/

import TS6.Exact.DirichletVariance
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Analysis.Complex.Polynomial.Basic

namespace TS6.Structure

open BigOperators Finset Complex TS6.Exact.Dirichlet

/-! ## The three pieces -/

/-- Diagonal part: `∑_{n ∈ S, (n,q) = 1}  ‖a n‖²`. -/
noncomputable def DW (a : ℕ → ℂ) (q : ℕ) (S : Finset ℕ) : ℝ :=
  ∑ n ∈ S, if Nat.Coprime n q then ‖a n‖ ^ 2 else 0

/-- Principal-character twist: the total coprime-to-q sum
    `T₀ = ∑_{n ∈ S, (n,q) = 1}  a n`.  This equals
    `twistSum a q S (1 : DirichletCharacter ℂ q)`. -/
noncomputable def T₀ (a : ℕ → ℂ) (q : ℕ) (S : Finset ℕ) : ℂ :=
  ∑ n ∈ S, if Nat.Coprime n q then a n else 0

/-- Off-diagonal part: `∑_{m ≠ n, m ≡ n (q), (mn,q)=1}  a m · conj(a n)`.

Note: this is a *complex* quantity a priori, but under the symmetry
`(m, n) ↔ (n, m)`, pairing `a m · conj(a n)` with `a n · conj(a m)`
gives a conjugate pair, so the sum is real. We expose it as a complex
quantity and let the real-valued equation in the theorem take care of
the rest. -/
noncomputable def SW (a : ℕ → ℂ) (q : ℕ) (S : Finset ℕ) : ℂ :=
  ∑ m ∈ S, ∑ n ∈ S,
    if m ≠ n ∧ Nat.Coprime m q ∧ Nat.Coprime n q ∧
         (m : ZMod q) = (n : ZMod q) then
      a m * star (a n)
    else 0

/-! ## The decomposition -/

/-! ## Sub-lemmas for Rankin–Selberg decomposition

Three building blocks for `rankin_selberg_decomposition`:

  * `RS_L1 twistSum_one_eq_T₀` — the principal-character twist is `T₀`.
  * `RS_L2 sum_all_twistSum_sq` — Schur orthogonality expansion of
    the full-character sum `∑_χ ‖twistSum χ‖²`.
  * `RS_L3 diag_offdiag_split` — split the resulting (m,n)-double-sum
    into diagonal (`DW`) and off-diagonal (`SW`) parts.
-/

-- NOTE: RS_L1 (EASY, ~30min). Pure unfolding.
/-- **RS_L1.** The twist of `a` by the principal Dirichlet character mod `q`
is exactly the coprime-to-`q` partial sum `T₀ a q S`. -/
lemma twistSum_one_eq_T₀ (a : ℕ → ℂ) (q : ℕ) [NeZero q] (S : Finset ℕ) :
    twistSum a q S 1 = T₀ a q S := by
  classical
  unfold twistSum T₀
  refine Finset.sum_congr rfl (fun n _ => ?_)
  by_cases h : Nat.Coprime n q
  · have hu : IsUnit ((n : ZMod q)) := (ZMod.isUnit_iff_coprime n q).mpr h
    rw [if_pos h, MulChar.one_apply hu, mul_one]
  · have hu : ¬ IsUnit ((n : ZMod q)) := fun hu =>
      h ((ZMod.isUnit_iff_coprime n q).mp hu)
    rw [if_neg h, MulChar.map_nonunit _ hu, mul_zero]

/-! ### RS_L2 sub-lemmas -/

-- NOTE: L2_NORM (EASY, ~30min). Complex.mul_conj + push_cast.
/-- **L2_NORM.** For any z : ℂ, (↑‖z‖)² = z * star z (cast then square form). -/
lemma normSq_cast_eq_mul_conj (z : ℂ) :
    ((‖z‖ : ℂ)) ^ 2 = z * star z := by
  have key : z * star z = ((Complex.normSq z : ℝ) : ℂ) := by
    rw [show star z = (starRingEnd ℂ) z from rfl]
    exact Complex.mul_conj z
  rw [key]
  have hnorm : (‖z‖ : ℝ) ^ 2 = Complex.normSq z := by
    rw [Complex.norm_eq_abs]; exact Complex.sq_abs z
  exact_mod_cast hnorm

-- NOTE: L2_SCHUR_DUAL_CORE decompose en 2 sous-sorrys localises.
-- AUX1 : star (chi b) = chi b^-1 (racines de l'unite sur groupe fini)
-- AUX2 : Sum chi, chi g = card G si g = 1, 0 sinon (identite standard Mathlib MulChar.Duality)
/-- Forme duale de Schur sur groupe abelien fini : somme sur caracteres, element fixe. -/
lemma schur_orthogonality_dual {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G]
    (a b : G) :
    (∑ χ : MulChar G ℂ, χ a * star (χ b)) =
      if a = b then (Fintype.card G : ℂ) else 0 := by
  classical
  have hterm : ∀ χ : MulChar G ℂ, χ a * star (χ b) = χ (a * b⁻¹) := by
    intro χ
    -- AUX1 closed: χ b is a |G|-th root of unity, so star (χ b) = (χ b)⁻¹.
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
  -- AUX2 closed: ∑_χ χ g = if g = 1 then |G| else 0, applied to g := a * b⁻¹.
  haveI : NeZero ((Monoid.exponent Gˣ : ℕ) : ℂ) :=
    ⟨by exact_mod_cast NeZero.ne (Monoid.exponent Gˣ)⟩
  haveI : HasEnoughRootsOfUnity ℂ (Monoid.exponent Gˣ) :=
    IsAlgClosed.hasEnoughRootsOfUnity ℂ _
  by_cases hg : a * b⁻¹ = 1
  · -- Case a * b⁻¹ = 1 → a = b via hiff
    rw [hg, if_pos (hiff.mp hg)]
    simp_rw [map_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    congr 1
    rw [← Nat.card_eq_fintype_card (α := MulChar G ℂ),
        MulChar.card_eq_card_units_of_hasEnoughRootsOfUnity G ℂ,
        Nat.card_congr (toUnits (G := G)).toEquiv.symm,
        Nat.card_eq_fintype_card]
  · -- Case a * b⁻¹ ≠ 1 → a ≠ b via hiff
    rw [if_neg (fun heq => hg (hiff.mpr heq))]
    obtain ⟨χ, hχ⟩ := MulChar.exists_apply_ne_one_of_hasEnoughRootsOfUnity G ℂ hg
    refine eq_zero_of_mul_eq_self_left hχ ?_
    simp only [Finset.mul_sum, ← MulChar.mul_apply]
    exact Fintype.sum_bijective _ (Group.mulLeft_bijective χ) _ _ fun χ' ↦ rfl

-- NOTE: L2_SCHUR (MEDIUM, branche both-units fermee via schur_orthogonality_dual).
/-- **L2_SCHUR.** Schur orthogonality for Dirichlet characters evaluated on ℕ. -/
lemma schur_orthogonality_dirichlet (q : ℕ) [NeZero q] (m n : ℕ) :
    (∑ χ : DirichletCharacter ℂ q, χ (m : ZMod q) * star (χ (n : ZMod q)))
      = if Nat.Coprime m q ∧ Nat.Coprime n q ∧ (m : ZMod q) = (n : ZMod q) then
          (Nat.totient q : ℂ)
        else 0 := by
  classical
  rw [← (mulchar_dirichlet_equiv q).sum_comp
        (fun χ => χ (m : ZMod q) * star (χ (n : ZMod q)))]
  by_cases hm : IsUnit ((m : ZMod q))
  · by_cases hn : IsUnit ((n : ZMod q))
    · set u_m : (ZMod q)ˣ := hm.unit with hu_m_def
      set u_n : (ZMod q)ˣ := hn.unit with hu_n_def
      have hu_m_val : (u_m : ZMod q) = (m : ZMod q) := hm.unit_spec
      have hu_n_val : (u_n : ZMod q) = (n : ZMod q) := hn.unit_spec
      have hm_cop : Nat.Coprime m q := (ZMod.isUnit_iff_coprime m q).mp hm
      have hn_cop : Nat.Coprime n q := (ZMod.isUnit_iff_coprime n q).mp hn
      have hterm : ∀ μ : MulChar (ZMod q)ˣ ℂ,
          mulchar_dirichlet_equiv q μ (m : ZMod q)
              * star (mulchar_dirichlet_equiv q μ (n : ZMod q))
            = μ u_m * star (μ u_n) := by
        intro μ
        rw [← hu_m_val, ← hu_n_val,
            mulchar_dirichlet_equiv_apply_unit q μ u_m,
            mulchar_dirichlet_equiv_apply_unit q μ u_n]
      rw [Finset.sum_congr rfl (fun μ _ => hterm μ)]
      rw [schur_orthogonality_dual u_m u_n]
      have hcard : (Fintype.card (ZMod q)ˣ : ℂ) = (Nat.totient q : ℂ) := by
        exact_mod_cast ZMod.card_units_eq_totient q
      by_cases huv : u_m = u_n
      · have heq_zmod : (m : ZMod q) = (n : ZMod q) := by
          rw [← hu_m_val, ← hu_n_val, huv]
        rw [if_pos huv, if_pos ⟨hm_cop, hn_cop, heq_zmod⟩, hcard]
      · have hne_zmod : (m : ZMod q) ≠ (n : ZMod q) := by
          intro heq
          apply huv
          apply Units.ext
          rw [hu_m_val, hu_n_val]; exact heq
        rw [if_neg huv, if_neg (fun h => hne_zmod h.2.2)]
    · have hne_coprime : ¬ Nat.Coprime n q := fun hcop =>
        hn ((ZMod.isUnit_iff_coprime n q).mpr hcop)
      have hzero : ∀ μ : MulChar (ZMod q)ˣ ℂ,
          mulchar_dirichlet_equiv q μ (m : ZMod q)
            * star (mulchar_dirichlet_equiv q μ (n : ZMod q)) = 0 := by
        intro μ
        rw [mulchar_dirichlet_equiv_apply_nonunit q μ _ hn, star_zero, mul_zero]
      rw [Finset.sum_eq_zero (fun μ _ => hzero μ)]
      rw [if_neg (fun h => hne_coprime h.2.1)]
  · have hne_coprime : ¬ Nat.Coprime m q := fun hcop =>
      hm ((ZMod.isUnit_iff_coprime m q).mpr hcop)
    have hzero : ∀ μ : MulChar (ZMod q)ˣ ℂ,
        mulchar_dirichlet_equiv q μ (m : ZMod q)
          * star (mulchar_dirichlet_equiv q μ (n : ZMod q)) = 0 := by
      intro μ
      rw [mulchar_dirichlet_equiv_apply_nonunit q μ _ hm, zero_mul]
    rw [Finset.sum_eq_zero (fun μ _ => hzero μ)]
    rw [if_neg (fun h => hne_coprime h.1)]

-- NOTE: RS_L2 assembly.
/-- **RS_L2.** Expansion of the full-character sum. -/
lemma sum_all_twistSum_sq (a : ℕ → ℂ) (q : ℕ) [NeZero q] (S : Finset ℕ) :
    (∑ χ : DirichletCharacter ℂ q, (‖twistSum a q S χ‖ ^ 2 : ℂ))
      = (Nat.totient q : ℂ) *
          ∑ m ∈ S, ∑ n ∈ S,
            if Nat.Coprime m q ∧ Nat.Coprime n q ∧ (m : ZMod q) = (n : ZMod q) then
              a m * star (a n)
            else 0 := by
  classical
  have step1 : ∀ χ : DirichletCharacter ℂ q,
      (‖twistSum a q S χ‖ ^ 2 : ℂ)
        = ∑ m ∈ S, ∑ n ∈ S, (a m * χ (m : ZMod q)) * star (a n * χ (n : ZMod q)) := by
    intro χ
    rw [normSq_cast_eq_mul_conj]
    unfold twistSum
    rw [star_sum, Finset.sum_mul_sum]
  calc (∑ χ : DirichletCharacter ℂ q, (‖twistSum a q S χ‖ ^ 2 : ℂ))
      = ∑ χ : DirichletCharacter ℂ q, ∑ m ∈ S, ∑ n ∈ S,
          (a m * χ (m : ZMod q)) * star (a n * χ (n : ZMod q)) := by
            exact Finset.sum_congr rfl (fun χ _ => step1 χ)
    _ = ∑ m ∈ S, ∑ n ∈ S, ∑ χ : DirichletCharacter ℂ q,
          (a m * χ (m : ZMod q)) * star (a n * χ (n : ZMod q)) := by
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl (fun m _ => Finset.sum_comm)
    _ = ∑ m ∈ S, ∑ n ∈ S, (a m * star (a n)) *
          ∑ χ : DirichletCharacter ℂ q, χ (m : ZMod q) * star (χ (n : ZMod q)) := by
            refine Finset.sum_congr rfl (fun m _ => Finset.sum_congr rfl (fun n _ => ?_))
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl (fun χ _ => ?_)
            rw [star_mul']
            ring
    _ = ∑ m ∈ S, ∑ n ∈ S, (a m * star (a n)) *
          (if Nat.Coprime m q ∧ Nat.Coprime n q ∧ (m : ZMod q) = (n : ZMod q) then
             (Nat.totient q : ℂ) else 0) := by
            refine Finset.sum_congr rfl (fun m _ => Finset.sum_congr rfl (fun n _ => ?_))
            rw [schur_orthogonality_dirichlet]
    _ = (Nat.totient q : ℂ) *
          ∑ m ∈ S, ∑ n ∈ S,
            if Nat.Coprime m q ∧ Nat.Coprime n q ∧ (m : ZMod q) = (n : ZMod q) then
              a m * star (a n)
            else 0 := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl (fun m _ => ?_)
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl (fun n _ => ?_)
            split_ifs with h
            · ring
            · ring

/-- Helper for `diag_offdiag_split`: the diagonal sum (filter `n = m`) equals `(DW : ℂ)`. -/
private lemma diag_part_eq_DW (a : ℕ → ℂ) (q : ℕ) (S : Finset ℕ) :
    (∑ m ∈ S, ∑ n ∈ S with n = m,
        if Nat.Coprime m q ∧ Nat.Coprime n q ∧ (m : ZMod q) = (n : ZMod q) then
          a m * star (a n) else 0)
    = (DW a q S : ℂ) := by
  classical
  -- Step A: collapse each inner filter-sum to the n = m term.
  have hdiag : ∀ m ∈ S,
      (∑ n ∈ S with n = m,
          if Nat.Coprime m q ∧ Nat.Coprime n q ∧ (m : ZMod q) = (n : ZMod q) then
            a m * star (a n) else 0)
      = if Nat.Coprime m q then ((‖a m‖ ^ 2 : ℝ) : ℂ) else 0 := by
    intro m hm
    rw [Finset.sum_filter]
    have hval : a m * star (a m) = ((‖a m‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.ofReal_pow]; exact (normSq_cast_eq_mul_conj _).symm
    rw [Finset.sum_eq_single m]
    · rw [if_pos rfl]
      by_cases hc : Nat.Coprime m q
      · have h_cond : Nat.Coprime m q ∧ Nat.Coprime m q ∧ (m : ZMod q) = (m : ZMod q) :=
          ⟨hc, hc, rfl⟩
        rw [if_pos h_cond, if_pos hc, hval]
      · have h_cond : ¬ (Nat.Coprime m q ∧ Nat.Coprime m q ∧ (m : ZMod q) = (m : ZMod q)) :=
          fun ⟨h, _, _⟩ => hc h
        rw [if_neg h_cond, if_neg hc]
    · intro n _ hne; simp [hne]
    · intro h; exact absurd hm h
  rw [Finset.sum_congr rfl hdiag]
  -- Step B: the indicator-sum equals `(DW : ℂ)` via `Complex.ofReal_sum`.
  unfold DW
  rw [Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  by_cases hc : Nat.Coprime m q
  · rw [if_pos hc, if_pos hc]
  · rw [if_neg hc, if_neg hc, Complex.ofReal_zero]

/-- Helper for `diag_offdiag_split`: the off-diagonal sum (filter `n ≠ m`) equals `SW`. -/
private lemma offdiag_part_eq_SW (a : ℕ → ℂ) (q : ℕ) (S : Finset ℕ) :
    (∑ m ∈ S, ∑ n ∈ S with n ≠ m,
        if Nat.Coprime m q ∧ Nat.Coprime n q ∧ (m : ZMod q) = (n : ZMod q) then
          a m * star (a n) else 0)
    = SW a q S := by
  classical
  unfold SW
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  by_cases hne : n = m
  · rw [if_neg (fun h_ne => h_ne hne), if_neg]
    rintro ⟨h_mn, _⟩
    exact h_mn hne.symm
  · rw [if_pos hne]
    by_cases hc : Nat.Coprime m q ∧ Nat.Coprime n q ∧ (m : ZMod q) = (n : ZMod q)
    · rw [if_pos hc, if_pos ⟨fun h => hne h.symm, hc⟩]
    · rw [if_neg hc, if_neg]
      rintro ⟨_, h⟩; exact hc h

-- NOTE: RS_L3 (MEDIUM, ~1-2h). Diagonal/off-diagonal split.
/-- **RS_L3.** Diagonal/off-diagonal decomposition. The diagonal `m = n`
contributes `DW a q S` (cast to ℂ), the off-diagonal `m ≠ n` contributes `SW a q S`. -/
lemma diag_offdiag_split (a : ℕ → ℂ) (q : ℕ) (S : Finset ℕ) :
    (∑ m ∈ S, ∑ n ∈ S,
        if Nat.Coprime m q ∧ Nat.Coprime n q ∧ (m : ZMod q) = (n : ZMod q) then
          a m * star (a n)
        else 0)
      = (DW a q S : ℂ) + SW a q S := by
  classical
  rw [show (∑ m ∈ S, ∑ n ∈ S, if Nat.Coprime m q ∧ Nat.Coprime n q ∧ (m : ZMod q) = (n : ZMod q)
          then a m * star (a n) else 0)
       = ∑ m ∈ S,
           ((∑ n ∈ S with n = m, if Nat.Coprime m q ∧ Nat.Coprime n q ∧ (m : ZMod q) = (n : ZMod q)
               then a m * star (a n) else 0) +
            (∑ n ∈ S with n ≠ m, if Nat.Coprime m q ∧ Nat.Coprime n q ∧ (m : ZMod q) = (n : ZMod q)
               then a m * star (a n) else 0))
     from Finset.sum_congr rfl fun m _ =>
       (Finset.sum_filter_add_sum_filter_not S (· = m) _).symm]
  rw [Finset.sum_add_distrib, diag_part_eq_DW, offdiag_part_eq_SW]

attribute [local instance] Classical.propDecidable

/-- Helper for `rankin_selberg_decomposition`: the sum over non-principal
characters equals the total sum minus the principal-character term. -/
private lemma sum_filter_ne_one_eq_total_sub
    (q : ℕ) [NeZero q] (f : DirichletCharacter ℂ q → ℂ) :
    (∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (· ≠ 1), f χ) =
      (∑ χ : DirichletCharacter ℂ q, f χ) - f 1 := by
  classical
  have h := Finset.sum_filter_add_sum_filter_not
    (Finset.univ : Finset (DirichletCharacter ℂ q)) (fun χ => χ = 1) f
  have hsingle :
      (∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ = 1), f χ) = f 1 := by
    rw [Finset.sum_filter]
    rw [Finset.sum_eq_single (1 : DirichletCharacter ℂ q)]
    · simp
    · intro χ _ hχ; simp [hχ]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [hsingle] at h
  show (∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => ¬ χ = 1), f χ) =
    (∑ χ : DirichletCharacter ℂ q, f χ) - f 1
  linear_combination h

/-- Helper for `rankin_selberg_decomposition`: complex-side decomposition of CW
combining RS_L1 (`twistSum 1 = T₀`) + RS_L2 (`sum_all_twistSum_sq`) +
RS_L3 (`diag_offdiag_split`). -/
private lemma CW_eq_complex_decomp (a : ℕ → ℂ) (q : ℕ) [NeZero q] (S : Finset ℕ) :
    ((CW a q S : ℝ) : ℂ) =
      (DW a q S : ℂ) + SW a q S - (‖T₀ a q S‖ ^ 2 : ℂ) / (Nat.totient q : ℂ) := by
  have hφ_pos : 0 < Nat.totient q := Nat.totient_pos.mpr (Nat.pos_of_neZero q)
  have hφ_ne : (Nat.totient q : ℂ) ≠ 0 := by exact_mod_cast hφ_pos.ne'
  unfold CW
  push_cast
  rw [sum_filter_ne_one_eq_total_sub q (fun χ => (‖twistSum a q S χ‖ ^ 2 : ℂ))]
  rw [twistSum_one_eq_T₀]
  rw [sum_all_twistSum_sq]
  rw [diag_offdiag_split]
  field_simp
  ring

/-- **TS6-D: TS5 Proposition 3.7 — Rankin–Selberg decomposition.**

For every `q ≥ 2`, every `a : ℕ → ℂ`, every finite `S ⊂ ℕ`:

    AWstar a q S
      =  DW a q S  -  |T₀|²/φ(q)  +  Re (SW a q S).

The equation is written with `Re (SW a q S)` because `SW a q S` is
conjugate-symmetric under `(m, n) ↔ (n, m)`, so its value is real; but
since `SW` is packaged as a complex sum, we extract the real part
explicitly for typing.

In the paper (TS5 Prop 3.7), the identity is stated with a real-valued
`S_{W,q}`. The Lean form here matches that, via `SW.re`. -/
theorem rankin_selberg_decomposition
    (a : ℕ → ℂ) (q : ℕ) [NeZero q] (hq : 2 ≤ q) (S : Finset ℕ) :
    AWstar a q S =
      DW a q S - ‖T₀ a q S‖ ^ 2 / (Nat.totient q : ℝ) + (SW a q S).re := by
  -- Proof plan:
  --
  -- Step 1: `AWstar a q S = CW a q S` by TS6-B (TS2_exact_identity).
  --
  -- Step 2: Expand `CW`:
  --     CW a q S = (1/φ(q)) · ∑_{χ ≠ 1}  ‖twistSum χ‖²
  --              = (1/φ(q)) · [∑_χ ‖twistSum χ‖² - ‖twistSum 1‖²]
  --              = (1/φ(q)) · ∑_χ ‖twistSum χ‖² - (1/φ(q)) · ‖T₀‖²
  -- because `twistSum a q S (1 : DirichletCharacter ℂ q) = T₀ a q S`
  -- (the principal character vanishes on multiples of q and equals 1
  -- on coprimes).
  --
  -- Step 3: Expand the full-character sum by double sum:
  --     ∑_χ ‖twistSum χ‖²
  --       = ∑_χ (∑_m a m · χ m) · conj (∑_n a n · χ n)
  --       = ∑_{m, n} a m · conj (a n) · ∑_χ χ(m) · conj (χ(n)).
  --
  -- Step 4: Apply Schur orthogonality on `MulChar (ZMod q)ˣ ℂ` (via the
  -- DirichletCharacter bijection):
  --     ∑_χ χ(m) · conj (χ(n))  =  φ(q) · [m ≡ n (q) ∧ (mn, q) = 1].
  -- For pairs (m, n) with m ≡ n (q) and both coprime to q, the coefficient
  -- is φ(q); all other pairs contribute 0.
  --
  -- Step 5: Split the (m, n)-sum by m = n vs m ≠ n:
  --     ∑_{m = n, (m, q) = 1} |a m|²   =  DW a q S,
  --     ∑_{m ≠ n, m ≡ n (q), (mn, q) = 1}  a m · conj (a n) = SW a q S.
  -- Hence ∑_{m,n: m≡n, (mn,q)=1} a m · conj (a n) = DW + SW (as a complex
  -- combination; DW is real, SW is real-valued by pair symmetry, and
  -- the left side is real because `A * conj A + A' * conj A'` types
  -- cancel correctly).
  --
  -- Step 6: Putting it together:
  --     CW a q S
  --       =  φ(q) · (DW + SW) / φ(q)  -  ‖T₀‖² / φ(q)
  --       =  DW + SW - ‖T₀‖² / φ(q).
  --
  -- Step 7: Take real parts (DW is real, SW.re is real, ‖T₀‖² is real),
  -- and combine with AWstar = CW to conclude.
  --
  -- Lean tactics: assembly of TS2_exact_identity + CW_eq_complex_decomp
  -- + real-part extraction via Complex.add_re/sub_re/ofReal_re/div_natCast_re.
  rw [TS2_exact_identity a q hq S]
  have hcomplex := CW_eq_complex_decomp a q S
  have h := congr_arg Complex.re hcomplex
  simp only [Complex.add_re, Complex.sub_re, Complex.div_natCast_re,
             ← Complex.ofReal_pow, Complex.ofReal_re] at h
  linarith [h]

end TS6.Structure
