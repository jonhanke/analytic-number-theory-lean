/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import NTKB.Analytic.Apostol.PNT.ZetaBounds

/-!
# Inequalities for `|1/ζ(s)|` and `|ζ'(s)/ζ(s)|` (Apostol, Theorem 13.7)

**Theorem 13.7.** There is `M > 0` with `|1/ζ(s)| ≤ M log⁷ t` and `|ζ'(s)/ζ(s)| ≤ M log⁹ t`
whenever `σ ≥ 1` and `t ≥ e`.

Proof as in Apostol: trivial for `σ ≥ 2`; for `1 < σ < 2` the inequality of Theorem 13.5
(`|ζ(σ)³ ζ(σ+it)⁴ ζ(σ+2it)| ≥ 1`, Mathlib's `DirichletCharacter.norm_LSeries_product_ge_one`
for the character mod 1) with `(σ-1)ζ(σ) = O(1)` and Theorem 13.4 gives
`|ζ(σ+it)| ≥ B (σ-1)^{3/4}/log^{1/4} t`; then the mean value inequality with `|ζ'| ≤ M log² t`
and the choice `α - 1 ≍ 1/log⁹ t`.
-/

open Complex Filter Topology Finset HurwitzZeta
open scoped Real ArithmeticFunction.vonMangoldt LSeries.notation

namespace NTKB.Apostol

/-- `|ζ(s) - 1| ≤ ζ(2) - 1 < 2/3` for `σ ≥ 2`, hence `|1/ζ(s)| ≤ 3`. -/
lemma norm_inv_riemannZeta_le_three {s : ℂ} (hs : 2 ≤ s.re) : ‖(riemannZeta s)⁻¹‖ ≤ 3 := by
  have hs1 : 1 < s.re := by linarith
  -- `ζ(s) = 1 + ∑_{n ≥ 0} (n+2)^{-s}`
  have hz := zeta_eq_tsum_one_div_nat_add_one_cpow hs1
  have hsum : Summable (fun n : ℕ ↦ 1 / ((n : ℂ) + 1) ^ s) := by
    have := (summable_nat_add_iff 1).2 (Complex.summable_one_div_nat_cpow.2 hs1)
    simpa [Nat.cast_add, Nat.cast_one] using this
  rw [hsum.tsum_eq_zero_add] at hz
  simp only [Nat.cast_zero, zero_add, one_cpow, div_one] at hz
  -- the real series `∑ (n+2)^{-2} = ζ(2) - 1`
  have hR := hasSum_rpow_riemannZeta (show (0 : ℝ) < 1 by norm_num)
  rw [← hasSum_nat_add_iff' 1] at hR
  simp only [range_one, sum_singleton, Nat.cast_zero, zero_add, Real.one_rpow] at hR
  have hz2 : (riemannZeta ((1 + 1 : ℝ) : ℂ)).re = π ^ 2 / 6 := by
    rw [show ((1 + 1 : ℝ) : ℂ) = 2 by norm_num, riemannZeta_two]
    rw [show ((π : ℂ) ^ 2 / 6) = (((π : ℝ) ^ 2 / 6 : ℝ) : ℂ) by push_cast; ring, ofReal_re]
  have hpi : π ^ 2 / 6 - 1 ≤ 2 / 3 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
  have hbound : ‖riemannZeta s - 1‖ ≤ 2 / 3 := by
    rw [hz, add_sub_cancel_left]
    have hf : HasSum (fun n : ℕ ↦ 1 / (((n + 1 : ℕ) : ℂ) + 1) ^ s)
        (∑' b : ℕ, 1 / (((b + 1 : ℕ) : ℂ) + 1) ^ s) :=
      ((summable_nat_add_iff 1).mpr hsum).hasSum
    have hb := hf.norm_le_of_bounded hR (fun n ↦ by
      simp only [one_div, norm_inv]
      push_cast
      rw [show (n : ℂ) + 1 + 1 = (((n : ℝ) + 1 + 1 : ℝ) : ℂ) by push_cast; ring,
        norm_cpow_eq_rpow_re_of_pos (by positivity), ← Real.rpow_neg (by positivity)]
      exact Real.rpow_le_rpow_of_exponent_le (by linarith [n.cast_nonneg (α := ℝ)])
        (by linarith))
    linarith [hz2, hpi]
  have hlow : 1 / 3 ≤ ‖riemannZeta s‖ := by
    have := norm_sub_norm_le (1 : ℂ) (1 - riemannZeta s)
    rw [norm_sub_rev] at hbound
    simp at this
    linarith [norm_sub_rev (1 : ℂ) (riemannZeta s)]
  rw [norm_inv]
  rw [inv_le_comm₀ (by linarith) (by norm_num)]
  linarith

/-- `|ζ'(s)/ζ(s)| ≤ ∑ Λ(n) n^{-2}` for `σ ≥ 2`. -/
lemma norm_logDeriv_riemannZeta_le_right {s : ℂ} (hs : 2 ≤ s.re) :
    ‖deriv riemannZeta s / riemannZeta s‖ ≤ ∑' n : ℕ, ‖LSeries.term (fun n ↦ (Λ n : ℂ)) 2 n‖ := by
  have hs1 : 1 < s.re := by linarith
  have h := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs1
  have h2 : deriv riemannZeta s / riemannZeta s = -L ↗Λ s := by rw [h]; ring
  rw [h2, norm_neg, LSeries]
  have hsum2 := (ArithmeticFunction.LSeriesSummable_vonMangoldt (s := 2) (by norm_num)).norm
  refine (norm_tsum_le_tsum_norm ?_).trans (Summable.tsum_le_tsum (fun n ↦ ?_) ?_ hsum2)
  · refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun n ↦ ?_) hsum2
    exact LSeries.norm_term_le_of_re_le_re _ (by simpa using hs) n
  · exact LSeries.norm_term_le_of_re_le_re _ (by simpa using hs) n
  · refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun n ↦ ?_) hsum2
    exact LSeries.norm_term_le_of_re_le_re _ (by simpa using hs) n

/-- `(σ - 1) |ζ(σ)| ≤ 6` for `1 < σ ≤ 2` (from Theorem 12.21 with `a = 1`, `N = 0`). -/
lemma sub_one_mul_norm_riemannZeta_le {σ : ℝ} (h1 : 1 < σ) (h2 : σ ≤ 2) :
    (σ - 1) * ‖riemannZeta σ‖ ≤ 6 := by
  have hs1 : (σ : ℂ) ≠ 1 := fun h ↦ by
    have := congrArg re h; simp at this; linarith
  have hrep := hurwitzZeta_eq_J one_pos le_rfl 0 (s := σ) (by simp; linarith) hs1
  rw [show hurwitzZeta ((1 : ℝ) : UnitAddCircle) σ = riemannZeta σ from
    congrFun riemannZeta_eq_hurwitz_one σ] at hrep
  simp only [zero_add, range_one, sum_singleton, Nat.cast_zero, one_cpow, ofReal_one] at hrep
  have hR := hasSum_rpow_riemannZeta (show (0 : ℝ) < 1 by norm_num)
  have hz2 : (riemannZeta ((1 + 1 : ℝ) : ℂ)).re ≤ 2 := by
    rw [show ((1 + 1 : ℝ) : ℂ) = 2 by norm_num, riemannZeta_two]
    rw [show ((π : ℂ) ^ 2 / 6) = (((π : ℝ) ^ 2 / 6 : ℝ) : ℂ) by push_cast; ring, ofReal_re]
    nlinarith [Real.pi_lt_d2, Real.pi_pos]
  have hJ : ‖hurwitzJSum 1 0 σ‖ ≤ 2 * (riemannZeta ((1 + 1 : ℝ) : ℂ)).re := by
    refine tsum_of_norm_bounded (hR.mul_left 2) fun n ↦ ?_
    refine (norm_hurwitzJ_le (by positivity) hs1 (by simp; linarith)).trans ?_
    simp only [Nat.cast_zero, zero_add, ofReal_re, norm_real, Real.norm_eq_abs,
      abs_of_pos (by linarith : (0 : ℝ) < σ)]
    rw [show (n : ℝ) + 1 = (n : ℝ) + 1 by ring]
    have hx : (1 : ℝ) ≤ n + 1 := by linarith [n.cast_nonneg (α := ℝ)]
    have := Real.rpow_le_rpow_of_exponent_le hx (show -σ - 1 ≤ -(1 + 1) by linarith)
    nlinarith [Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ n + 1) (-σ - 1)]
  have hden : ‖(1 : ℂ) / ((σ : ℂ) - 1)‖ = 1 / (σ - 1) := by
    rw [norm_div, norm_one, show (σ : ℂ) - 1 = ((σ - 1 : ℝ) : ℂ) by push_cast; ring,
      norm_real, Real.norm_of_nonneg (by linarith)]
  have hnorm : ‖riemannZeta σ‖ ≤ 1 + 1 / (σ - 1) + 4 := by
    rw [hrep]
    calc ‖1 + (1 : ℂ) / ((σ : ℂ) - 1) - hurwitzJSum 1 0 σ‖
        ≤ ‖(1 : ℂ)‖ + ‖(1 : ℂ) / ((σ : ℂ) - 1)‖ + ‖hurwitzJSum 1 0 σ‖ :=
          (norm_sub_le _ _).trans (by gcongr; exact norm_add_le _ _)
      _ ≤ 1 + 1 / (σ - 1) + 4 := by rw [norm_one, hden]; linarith
  have hσ1 : 0 < σ - 1 := by linarith
  calc (σ - 1) * ‖riemannZeta σ‖ ≤ (σ - 1) * (1 + 1 / (σ - 1) + 4) := by gcongr
    _ = 5 * (σ - 1) + 1 := by field_simp; ring
    _ ≤ 6 := by linarith

/-- **Apostol, Theorem 13.5** for `ζ`: `|ζ(σ)³ ζ(σ+it)⁴ ζ(σ+2it)| ≥ 1` for `σ > 1`
(Mathlib's `DirichletCharacter.norm_LFunction_product_ge_one` for the character mod `1`). -/
lemma one_le_norm_zeta_product {x : ℝ} (hx : 0 < x) (y : ℝ) :
    1 ≤ ‖riemannZeta (1 + x)‖ ^ 3 * ‖riemannZeta (1 + x + I * y)‖ ^ 4 *
      ‖riemannZeta (1 + x + 2 * I * y)‖ := by
  have h := DirichletCharacter.norm_LFunction_product_ge_one (N := 1) (1 : DirichletCharacter ℂ 1)
    hx y
  simp only [DirichletCharacter.LFunctionTrivChar, DirichletCharacter.LFunction_modOne_eq,
    norm_mul, norm_pow] at h
  exact h

/-- Apostol (23), in fourth powers: `|ζ(σ+it)|⁴ ≥ K₀ (σ-1)³ / log t` for `1 < σ ≤ 2`, `t ≥ e`. -/
lemma zeta_lower_fourth : ∃ K₀ : ℝ, 0 < K₀ ∧ ∀ σ t : ℝ, 1 < σ → σ ≤ 2 → Real.exp 1 ≤ t →
    K₀ * (σ - 1) ^ 3 / Real.log t ≤ ‖riemannZeta (σ + t * I)‖ ^ 4 := by
  obtain ⟨M₄, hM₄, hM₄b⟩ := apostol_thm_13_4 (A := 1) one_pos
  refine ⟨1 / (432 * M₄), by positivity, fun σ t h1 h2 ht ↦ ?_⟩
  have he : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have ht2 : 2 ≤ t := he.trans ht
  have hlt1 : 1 ≤ Real.log t := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) ht
  have hσ1 : 0 < σ - 1 := by linarith
  have h := one_le_norm_zeta_product hσ1 t
  rw [show (1 : ℂ) + ((σ - 1 : ℝ) : ℂ) = (σ : ℂ) by push_cast; ring,
    show (σ : ℂ) + I * t = σ + t * I by ring] at h
  set z := ‖riemannZeta (σ + t * I)‖
  have ha : ‖riemannZeta σ‖ ≤ 6 / (σ - 1) := by
    rw [le_div_iff₀ hσ1, mul_comm]; exact sub_one_mul_norm_riemannZeta_le h1 h2
  have hb : ‖riemannZeta (σ + 2 * I * t)‖ ≤ 2 * M₄ * Real.log t := by
    have hs2 : (σ + 2 * I * t : ℂ).im = 2 * t := by simp
    have hs2' : (σ + 2 * I * t : ℂ).re = σ := by simp
    have hlog2 : 0 < Real.log (2 * t) := Real.log_pos (by linarith)
    have hb' := (hM₄b (σ + 2 * I * t) (by rw [hs2']; linarith)
      (by rw [hs2', hs2]; have := div_pos one_pos hlog2; linarith)
      (by rw [hs2]; linarith)).1
    rw [hs2] at hb'
    have hl2 : Real.log (2 * t) ≤ 2 * Real.log t := by
      rw [← Real.log_rpow (by linarith), Real.rpow_two]
      exact Real.log_le_log (by linarith) (by nlinarith)
    calc ‖riemannZeta (σ + 2 * I * t)‖ ≤ M₄ * Real.log (2 * t) := hb'
      _ ≤ M₄ * (2 * Real.log t) := by gcongr
      _ = 2 * M₄ * Real.log t := by ring
  have hz0 : 0 ≤ z := norm_nonneg _
  have hX : 1 ≤ (6 / (σ - 1)) ^ 3 * z ^ 4 * (2 * M₄ * Real.log t) := by
    refine h.trans ?_
    gcongr
  have key : (σ - 1) ^ 3 ≤ 432 * M₄ * Real.log t * z ^ 4 := by
    have h6 : (6 / (σ - 1)) ^ 3 * z ^ 4 * (2 * M₄ * Real.log t) * (σ - 1) ^ 3 =
        432 * M₄ * Real.log t * z ^ 4 := by field_simp; ring
    have hp : 0 < (σ - 1) ^ 3 := by positivity
    nlinarith
  rw [div_le_iff₀ (by linarith)]
  have : 1 / (432 * M₄) * (σ - 1) ^ 3 = (σ - 1) ^ 3 / (432 * M₄) := by ring
  rw [this, div_le_iff₀ (by positivity)]
  nlinarith

/-- The mean value step: `|ζ(σ+it) - ζ(α+it)| ≤ (α - σ) M log² t` for `1 ≤ σ ≤ α`, `t ≥ e`,
where `M` bounds `|ζ'|` as in Theorem 13.4. -/
lemma norm_zeta_sub_le {M₄ : ℝ} (hM₄b : ∀ s : ℂ, 1 / 2 ≤ s.re → 1 - 1 / Real.log s.im < s.re →
      Real.exp 1 ≤ s.im →
      ‖riemannZeta s‖ ≤ M₄ * Real.log s.im ∧ ‖deriv riemannZeta s‖ ≤ M₄ * Real.log s.im ^ 2)
    {σ α t : ℝ} (hσ : 1 ≤ σ) (hσα : σ ≤ α) (ht : Real.exp 1 ≤ t) :
    ‖riemannZeta (α + t * I) - riemannZeta (σ + t * I)‖ ≤ M₄ * Real.log t ^ 2 * (α - σ) := by
  have ht0 : 0 < t := lt_of_lt_of_le (Real.exp_pos 1) ht
  have hlt : 0 < Real.log t := Real.log_pos (by linarith [Real.add_one_le_exp (1 : ℝ)])
  have hne : ∀ u : ℝ, (u : ℂ) + t * I ≠ 1 := fun u h ↦ by
    have := congrArg im h; simp at this; linarith
  have hderiv : ∀ u ∈ Set.Icc σ α, HasDerivWithinAt (fun u : ℝ ↦ riemannZeta (u + t * I))
      (deriv riemannZeta (u + t * I)) (Set.Icc σ α) u := by
    intro u _
    have h1 := (differentiableAt_riemannZeta (hne u)).hasDerivAt
    have h2 : HasDerivAt (fun z : ℂ ↦ riemannZeta (z + t * I)) (deriv riemannZeta (u + t * I))
        (u : ℂ) := h1.comp_add_const (u : ℂ) (t * I)
    exact h2.comp_ofReal.hasDerivWithinAt
  have hbound : ∀ u ∈ Set.Ico σ α, ‖deriv riemannZeta (u + t * I)‖ ≤ M₄ * Real.log t ^ 2 := by
    intro u hu
    have h := (hM₄b (u + t * I) (by simp; linarith [hu.1]) (by
      simp; have := inv_pos.mpr hlt; linarith [hu.1]) (by simpa using ht)).2
    simpa using h
  have := norm_image_sub_le_of_norm_deriv_le_segment' hderiv hbound α ⟨hσα, le_rfl⟩
  simpa using this

/-- **Apostol, Theorem 13.7**: there is `M > 0` such that `|1/ζ(s)| ≤ M log⁷ t` and
`|ζ'(s)/ζ(s)| ≤ M log⁹ t` whenever `σ ≥ 1` and `t ≥ e`. -/
@[kb "apostol1976" "Thm 13.7, p. 287"]
theorem apostol_thm_13_7 :
    ∃ M : ℝ, 0 < M ∧ ∀ s : ℂ, 1 ≤ s.re → Real.exp 1 ≤ s.im →
      ‖(riemannZeta s)⁻¹‖ ≤ M * Real.log s.im ^ 7 ∧
        ‖deriv riemannZeta s / riemannZeta s‖ ≤ M * Real.log s.im ^ 9 := by
  obtain ⟨M₄, hM₄, hM₄b⟩ := apostol_thm_13_4 (A := 1) one_pos
  obtain ⟨K₀, hK₀, hK₀b⟩ := zeta_lower_fourth
  set K : ℝ := ∑' n : ℕ, ‖LSeries.term (fun n ↦ (Λ n : ℂ)) 2 n‖
  have hK : 0 ≤ K := tsum_nonneg fun _ ↦ norm_nonneg _
  set c : ℝ := min (1 / 2) (K₀ / (16 * M₄ ^ 4))
  have hc0 : 0 < c := lt_min (by norm_num) (by positivity)
  have hc2 : c ≤ 1 / 2 := min_le_left _ _
  have hcK : c ≤ K₀ / (16 * M₄ ^ 4) := min_le_right _ _
  refine ⟨3 + K + 1 / (c * M₄) + 1 / c, by positivity, fun s hσ ht ↦ ?_⟩
  set t := s.im
  set σ := s.re
  have he : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hlt1 : 1 ≤ Real.log t := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) ht
  set lg := Real.log t
  have hL7 : 1 ≤ lg ^ 7 := one_le_pow₀ hlt1
  have hL9 : 1 ≤ lg ^ 9 := one_le_pow₀ hlt1
  have hs : s = σ + t * I := (re_add_im s).symm
  rcases le_or_gt 2 σ with h2 | h2
  · -- trivial range `σ ≥ 2`
    have h1 := norm_inv_riemannZeta_le_three h2
    have h3 := norm_logDeriv_riemannZeta_le_right h2
    have hpos : 0 ≤ 1 / (c * M₄) + 1 / c := by positivity
    constructor
    · calc ‖(riemannZeta s)⁻¹‖ ≤ 3 := h1
        _ ≤ (3 + K + 1 / (c * M₄) + 1 / c) * 1 := by nlinarith
        _ ≤ (3 + K + 1 / (c * M₄) + 1 / c) * lg ^ 7 := by gcongr
    · calc ‖deriv riemannZeta s / riemannZeta s‖ ≤ K := h3
        _ ≤ (3 + K + 1 / (c * M₄) + 1 / c) * 1 := by nlinarith
        _ ≤ (3 + K + 1 / (c * M₄) + 1 / c) * lg ^ 9 := by gcongr
  · -- `1 ≤ σ < 2`: the lower bound `|ζ(s)| ≥ c M₄ / L⁷`
    set dl := c / lg ^ 9
    have hdl0 : 0 < dl := by positivity
    have hdl : dl ≤ 1 / 2 := by
      simp only [dl]; rw [div_le_iff₀ (by positivity)]; nlinarith
    set α := 1 + dl
    set m := c * M₄ / lg ^ 7
    have hm0 : 0 < m := by positivity
    -- `(2m)^4 ≤ K₀ dl³ / lg`
    have hfour : (2 * m) ^ 4 ≤ K₀ * dl ^ 3 / lg := by
      have hL0 : 0 < lg := by linarith
      have e1 : (2 * m) ^ 4 = 16 * c ^ 4 * M₄ ^ 4 / lg ^ 28 := by simp only [m]; field_simp; ring
      have e2 : K₀ * dl ^ 3 / lg = K₀ * c ^ 3 / lg ^ 28 := by simp only [dl]; field_simp
      rw [e1, e2]
      apply div_le_div_of_nonneg_right _ (by positivity)
      have h16 : 16 * M₄ ^ 4 * c ≤ K₀ := by
        rw [le_div_iff₀ (by positivity)] at hcK; linarith
      have := mul_le_mul_of_nonneg_left h16 (pow_pos hc0 3).le
      nlinarith
    have hlow : m ≤ ‖riemannZeta s‖ := by
      rcases le_or_gt α σ with hα | hα
      · -- `σ ≥ α`: directly from (23)
        have h4 := hK₀b σ t (by linarith) h2.le ht
        rw [← hs] at h4
        have : (2 * m) ^ 4 ≤ ‖riemannZeta s‖ ^ 4 := by
          refine hfour.trans (le_trans ?_ h4)
          gcongr
          simp only [α] at hα; linarith
        have h2m := le_of_pow_le_pow_left₀ (by norm_num) (norm_nonneg _) this
        linarith
      · -- `σ < α`: the mean value step from `α`
        have h4 := hK₀b α t (by simp only [α]; linarith) (by simp only [α]; linarith) ht
        have hα1 : α - 1 = dl := by simp only [α]; ring
        rw [hα1] at h4
        have hw : 2 * m ≤ ‖riemannZeta (α + t * I)‖ :=
          le_of_pow_le_pow_left₀ (by norm_num) (norm_nonneg _) (hfour.trans h4)
        have hmv := norm_zeta_sub_le hM₄b hσ hα.le ht
        rw [← hs] at hmv
        have hdiff : M₄ * lg ^ 2 * (α - σ) ≤ m := by
          have : α - σ ≤ dl := by simp only [α]; linarith
          calc M₄ * lg ^ 2 * (α - σ) ≤ M₄ * lg ^ 2 * dl := by gcongr
            _ = m := by simp only [m, dl]; field_simp
        have := norm_sub_norm_le (riemannZeta (α + t * I)) (riemannZeta s)
        linarith
    have hζ0 : 0 < ‖riemannZeta s‖ := lt_of_lt_of_le hm0 hlow
    have hinv : ‖(riemannZeta s)⁻¹‖ ≤ lg ^ 7 / (c * M₄) := by
      rw [norm_inv, inv_le_comm₀ hζ0 (by positivity)]
      calc (lg ^ 7 / (c * M₄))⁻¹ = m := by simp only [m]; field_simp
        _ ≤ ‖riemannZeta s‖ := hlow
    have hd := (hM₄b s (by linarith) (by
      have := div_pos one_pos (show 0 < lg by linarith); linarith) ht).2
    constructor
    · calc ‖(riemannZeta s)⁻¹‖ ≤ lg ^ 7 / (c * M₄) := hinv
        _ = 1 / (c * M₄) * lg ^ 7 := by ring
        _ ≤ (3 + K + 1 / (c * M₄) + 1 / c) * lg ^ 7 := by
            gcongr; have : 0 ≤ 1 / c := by positivity
            linarith
    · rw [div_eq_mul_inv, norm_mul]
      calc ‖deriv riemannZeta s‖ * ‖(riemannZeta s)⁻¹‖ ≤ (M₄ * lg ^ 2) * (lg ^ 7 / (c * M₄)) :=
            mul_le_mul hd hinv (norm_nonneg _) (by positivity)
        _ = 1 / c * lg ^ 9 := by field_simp
        _ ≤ (3 + K + 1 / (c * M₄) + 1 / c) * lg ^ 9 := by
            gcongr; have : 0 ≤ 1 / (c * M₄) := by positivity
            linarith

end NTKB.Apostol
