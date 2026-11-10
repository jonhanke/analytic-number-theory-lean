/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import NTKB.Analytic.Davenport.Hadamard.ZeroFree
import NTKB.Analytic.Davenport.Hadamard.CanonicalProduct

/-!
# Hadamard's factorization for entire functions of order one (Davenport, Chapter 11, p. 76–78)

**Davenport, p. 77, (6).** An entire function `f` of order (at most) `1` with `f(0) ≠ 0` and zeros
`z₁, z₂, …` (with multiplicity) is
`f(z) = e^{A + Bz} ∏ (1 - z/z_n) e^{z/z_n}`.
**p. 78, (7).** If moreover `∑ r_n⁻¹` converges, then `|f(z)| < e^{C|z|}`.

## Proof (Davenport's)

* `P` is the canonical product over the zeros (`canonicalProductOne`), and `F = f / P` is entire
  without zeros (`exists_differentiable_eq_mul`: the orders of vanishing agree).
* There are arbitrarily large radii `R` with `|R - r_n| ≥ r_n⁻²` for all `n` (Davenport's (5):
  the intervals around the `r_n` have finite total length) — `exists_good_radius`.
* On such circles, `|P(z)| ≥ exp(-K(R) ∑ r_n^{-1-ε})` with `K(R) = (3 log 2R + 2)(2R)^{1+ε}`
  (Davenport's sub-products `P₁, P₂, P₃`, handled factor by factor:
  `norm_weierstrassFactorOne_ge`), hence `|F(z)| ≤ exp(C R^{7/4})` there.
* By the zero-free case (Chapter 11, p. 75, `exists_polynomial_of_norm_le_on_circles`),
  `F = e^{g}` with `deg g ≤ 7/4`, so `deg g ≤ 1`.
-/

open Filter Topology Metric Complex Set MeasureTheory
open scoped ENNReal NNReal

namespace NTKB

/-! ### The quotient `f / P` -/

/-- If two entire functions `f` and `P` (with `P(0) ≠ 0`) have the same order of vanishing at every
point, then `f = P F` with `F` entire and zero-free. -/
theorem exists_differentiable_eq_mul {f P : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hP : Differentiable ℂ P) (hP0 : P 0 ≠ 0)
    (hord : ∀ z, analyticOrderAt f z = analyticOrderAt P z) :
    ∃ F : ℂ → ℂ, Differentiable ℂ F ∧ (∀ z, F z ≠ 0) ∧ ∀ z, f z = P z * F z := by
  set g : ℂ → ℂ := f * P⁻¹
  have hgm : MeromorphicOn g univ := fun z _ ↦
    (hf.analyticAt z).meromorphicAt.mul (hP.analyticAt z).meromorphicAt.inv
  have hPfin : ∀ z, analyticOrderAt P z ≠ ⊤ := fun z ↦
    AnalyticOnNhd.analyticOrderAt_ne_top_of_isPreconnected (fun w _ ↦ hP.analyticAt w)
      isPreconnected_univ
      (mem_univ 0) (mem_univ z) (by rw [(hP.analyticAt 0).analyticOrderAt_eq_zero.mpr hP0]; simp)
  have hg0 : ∀ z, meromorphicOrderAt g z = 0 := by
    intro z
    rw [meromorphicOrderAt_mul (hf.analyticAt z).meromorphicAt (hP.analyticAt z).meromorphicAt.inv,
      meromorphicOrderAt_inv, (hf.analyticAt z).meromorphicOrderAt_eq,
      (hP.analyticAt z).meromorphicOrderAt_eq, hord z]
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (hPfin z)
    rw [← hn]
    simp only [ENat.map_natCast]
    rw [← WithTop.LinearOrderedAddCommGroup.coe_neg, ← WithTop.coe_add]
    simp
  set F := toMeromorphicNFOn g univ
  have hFan : ∀ z, AnalyticAt ℂ F z := fun z ↦ by
    have h1 := ((hgm z trivial).meromorphicOrderAt_nonneg_iff_analyticAt_toMeromorphicNFAt).mp
      (by rw [hg0 z])
    exact h1.congr (toMeromorphicNFOn_eq_toMeromorphicNFAt_on_nhds hgm (mem_univ z)).symm
  have hFne : ∀ z, F z ≠ 0 := fun z ↦ by
    rw [show F z = toMeromorphicNFOn g univ z from rfl,
      toMeromorphicNFOn_eq_toMeromorphicNFAt hgm (mem_univ z)]
    exact ((hgm z trivial).meromorphicOrderAt_eq_zero_iff_toMeromorphicNFAt_ne_zero).mp (hg0 z)
  refine ⟨F, fun z ↦ (hFan z).differentiableAt, hFne, ?_⟩
  -- identity theorem: `f = P F` near `0`, hence everywhere
  have h1 := hgm.toMeromorphicNFOn_eq_self_on_nhdsNE (mem_univ 0)
  have h2 : ∀ᶠ z in 𝓝[≠] (0 : ℂ), P z ≠ 0 :=
    (hP.continuous.continuousAt.eventually_ne hP0).filter_mono nhdsWithin_le_nhds
  have hfreq : ∃ᶠ z in 𝓝[≠] (0 : ℂ), f z = (P * F) z := by
    refine (h1.and h2).frequently.mono fun z hz ↦ ?_
    rw [Pi.mul_apply, show F z = toMeromorphicNFOn g univ z from rfl, hz.1]
    simp only [g, Pi.mul_apply, Pi.inv_apply]
    field_simp [hz.2]
  have := AnalyticOnNhd.eq_of_frequently_eq (fun z _ ↦ hf.analyticAt z)
    (fun z _ ↦ (hP.analyticAt z).mul (hFan z)) hfreq
  exact fun z ↦ congr_fun this z

/-! ### Good radii (Davenport's (5)) -/

/-- **Davenport, p. 76, (5).** If `∑ r_n⁻²` converges, there are arbitrarily large `R` with
`|R - r_n| > r_n⁻²` for all `n`. -/
theorem exists_good_radius {ι : Type*} [Countable ι] (r : ι → ℝ)
    (hr : Summable fun i ↦ (r i)⁻¹ ^ 2) (T : ℝ) :
    ∃ R ≥ T, ∀ i, (r i)⁻¹ ^ 2 < |R - r i| := by
  set B := ⋃ i, Icc (r i - (r i)⁻¹ ^ 2) (r i + (r i)⁻¹ ^ 2)
  have hB : volume B < ⊤ := by
    refine lt_of_le_of_lt (measure_iUnion_le _) ?_
    simp only [Real.volume_Icc]
    have : ∀ i, r i + (r i)⁻¹ ^ 2 - (r i - (r i)⁻¹ ^ 2) = 2 * (r i)⁻¹ ^ 2 := fun i ↦ by ring
    simp only [this]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun i ↦ by positivity) (hr.mul_left 2)]
    exact ENNReal.ofReal_lt_top
  have hnot : ¬ Ici T ⊆ B := by
    intro h
    have := measure_mono (μ := volume) h
    rw [Real.volume_Ici] at this
    exact absurd (lt_of_le_of_lt this hB) (lt_irrefl _)
  obtain ⟨R, hRT, hRB⟩ := not_subset.mp hnot
  refine ⟨R, hRT, fun i ↦ ?_⟩
  have hi : R ∉ Icc (r i - (r i)⁻¹ ^ 2) (r i + (r i)⁻¹ ^ 2) := fun h ↦
    hRB (mem_iUnion.mpr ⟨i, h⟩)
  simp only [mem_Icc, not_and_or, not_le] at hi
  have := sq_nonneg (r i)⁻¹
  rcases hi with h | h
  · rw [abs_sub_comm, abs_of_pos (by linarith)]; linarith
  · rw [abs_of_pos (by linarith)]; linarith

/-! ### Lower bound for the canonical product on good circles -/

/-- **Davenport, p. 77**, the three kinds of factors `P₁, P₂, P₃`, one factor at a time: on
`|z| = R ≥ 1`, for a zero `α` with `r = |α|` and `|R - r| ≥ r⁻²`,
`|E₁(z/α)| ≥ exp(-K r^{-1-ε})` with `K = (3 log 2R + 2)(2R)^{1+ε}`. -/
theorem norm_weierstrassFactorOne_ge {ε R r : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (hR : 1 ≤ R)
    {z α : ℂ} (hz : ‖z‖ = R) (hα : ‖α‖ = r) (hr : 0 < r) (hgood : r⁻¹ ^ 2 ≤ |R - r|) :
    Real.exp (-((3 * Real.log (2 * R) + 2) * (2 * R) ^ (1 + ε) * r ^ (-(1 + ε)))) ≤
      ‖weierstrassFactorOne (z / α)‖ := by
  have hR0 : 0 < R := by linarith
  have h2R : 0 < 2 * R := by linarith
  have hα0 : α ≠ 0 := by rintro rfl; simp at hα; linarith
  set c := 3 * Real.log (2 * R) + 2
  have hc : 2 ≤ c := by
    have : 0 ≤ Real.log (2 * R) := Real.log_nonneg (by linarith)
    simp only [c]; linarith
  -- notation for the powers
  set s := r ^ ε
  set t := (2 * R) ^ ε
  have hs : 0 < s := Real.rpow_pos_of_pos hr ε
  have ht : 1 ≤ t := Real.one_le_rpow (by linarith) hε0.le
  have hpow : (2 * R) ^ (1 + ε) = 2 * R * t := by
    rw [Real.rpow_add h2R, Real.rpow_one]
  have hrpow : r ^ (-(1 + ε)) = (r * s)⁻¹ := by
    rw [Real.rpow_neg hr.le, Real.rpow_add hr, Real.rpow_one]
  rw [hpow, hrpow]
  set w := z / α
  have hw : ‖w‖ = R / r := by simp only [w, norm_div, hz, hα]
  have hE : ‖weierstrassFactorOne w‖ = ‖1 - w‖ * Real.exp w.re := by
    simp only [weierstrassFactorOne, norm_mul, Complex.norm_exp]
  have hre : -(R / r) ≤ w.re := by
    rw [← hw]; exact neg_le_of_abs_le (Complex.abs_re_le_norm w)
  rcases lt_or_ge r (R / 2) with h1 | h1
  · -- `P₁`: `r < R / 2`, `|1 - w| ≥ 1`
    have hw1 : 1 ≤ ‖1 - w‖ := by
      have : ‖w‖ - ‖(1 : ℂ)‖ ≤ ‖w - 1‖ := norm_sub_norm_le w 1
      rw [norm_sub_rev] at this
      have h2 : 2 ≤ R / r := by rw [le_div_iff₀ hr]; linarith
      simp only [norm_one, hw] at this
      linarith
    rw [hE]
    calc Real.exp (-(c * (2 * R * t) * (r * s)⁻¹)) ≤ Real.exp (-(R / r)) := by
          refine Real.exp_le_exp.mpr (neg_le_neg ?_)
          rw [← div_eq_mul_inv, div_le_div_iff₀ hr (by positivity)]
          have hst : s ≤ t := Real.rpow_le_rpow hr.le (by linarith) hε0.le
          have : R * (r * s) ≤ c * (2 * R * t) * r := by
            have e1 : R * s ≤ R * t := mul_le_mul_of_nonneg_left hst hR0.le
            have e2 : R * t ≤ c * (2 * R * t) := by
              have : 0 ≤ R * t := by positivity
              nlinarith
            have : R * s ≤ c * (2 * R * t) := e1.trans e2
            nlinarith
          linarith
      _ ≤ Real.exp w.re := Real.exp_le_exp.mpr hre
      _ = 1 * Real.exp w.re := (one_mul _).symm
      _ ≤ ‖1 - w‖ * Real.exp w.re := by gcongr
  rcases le_or_gt r (2 * R) with h2 | h2
  · -- `P₂`: `R / 2 ≤ r ≤ 2R`, `|1 - w| ≥ r⁻³ ≥ (2R)⁻³`
    have hw1 : (2 * R)⁻¹ ^ 3 ≤ ‖1 - w‖ := by
      have heq : 1 - w = (α - z) / α := by simp only [w]; field_simp
      have hdist : |R - r| ≤ ‖α - z‖ := by
        rw [← hz, ← hα, abs_sub_comm]; exact abs_norm_sub_norm_le α z
      rw [heq, norm_div, hα, le_div_iff₀ hr]
      calc (2 * R)⁻¹ ^ 3 * r ≤ r⁻¹ ^ 3 * r := by
            gcongr
        _ = r⁻¹ ^ 2 := by field_simp
        _ ≤ ‖α - z‖ := hgood.trans hdist
    have hexp : Real.exp (-2) ≤ Real.exp w.re := by
      refine Real.exp_le_exp.mpr (le_trans ?_ hre)
      rw [neg_le_neg_iff, div_le_iff₀ hr]; linarith
    rw [hE]
    have hlog : (2 * R)⁻¹ ^ 3 = Real.exp (-(3 * Real.log (2 * R))) := by
      rw [Real.exp_neg, ← Real.log_rpow h2R, Real.exp_log (by positivity), inv_pow]
      norm_cast
    calc Real.exp (-(c * (2 * R * t) * (r * s)⁻¹)) ≤ Real.exp (-c) := by
          refine Real.exp_le_exp.mpr (neg_le_neg ?_)
          rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
          have hst : s ≤ t := Real.rpow_le_rpow hr.le h2 hε0.le
          have : r * s ≤ 2 * R * t := by nlinarith
          nlinarith
      _ = (2 * R)⁻¹ ^ 3 * Real.exp (-2) := by
          rw [hlog, ← Real.exp_add]; congr 1; simp only [c]; ring
      _ ≤ ‖1 - w‖ * Real.exp w.re := by gcongr
  · -- `P₃`: `r > 2R`, `|w| < 1/2`, `|E₁(w)| ≥ e^{-|w|²}`
    have hwlt : ‖w‖ ≤ 1 / 2 := by
      rw [hw, div_le_iff₀ hr]; linarith
    have hw1 : 1 - w ≠ 0 := by
      intro h
      have : w = 1 := (sub_eq_zero.mp h).symm
      rw [this, norm_one] at hwlt
      norm_num at hwlt
    have hlogeq : weierstrassFactorOne w = Complex.exp (Complex.log (1 + -w) - -w) := by
      rw [Complex.exp_sub, ← sub_eq_add_neg, Complex.exp_log hw1, Complex.exp_neg]
      simp [weierstrassFactorOne, div_inv_eq_mul]
    have hbound := Complex.norm_log_one_add_sub_self_le (z := -w) (by rw [norm_neg]; linarith)
    rw [norm_neg] at hbound
    have hbound' : ‖Complex.log (1 + -w) - -w‖ ≤ ‖w‖ ^ 2 := by
      refine hbound.trans ?_
      have : (1 - ‖w‖)⁻¹ ≤ 2 := by
        rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
      nlinarith [sq_nonneg ‖w‖]
    rw [hlogeq, Complex.norm_exp]
    refine Real.exp_le_exp.mpr ?_
    have hre' : -‖Complex.log (1 + -w) - -w‖ ≤ (Complex.log (1 + -w) - -w).re :=
      neg_le_of_abs_le (Complex.abs_re_le_norm _)
    refine le_trans ?_ hre'
    refine neg_le_neg (hbound'.trans ?_)
    -- `R²/r² ≤ c (2R) t / (r s)`
    rw [hw, ← div_eq_mul_inv, div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
    -- `R² (r s) ≤ c (2R t) r²`, using `r^{1-ε} ≥ (2R)^{1-ε}`
    set u := r ^ (1 - ε)
    set v := (2 * R) ^ (1 - ε)
    have hsu : s * u = r := by
      simp only [s, u]; rw [← Real.rpow_add hr]; simp
    have htv : t * v = 2 * R := by
      simp only [t, v]; rw [← Real.rpow_add h2R]; simp
    have huv : v ≤ u := Real.rpow_le_rpow h2R.le h2.le (by linarith)
    have hv : 0 < v := by positivity
    have key : R ^ 2 ≤ c * (2 * R * t) * u := by
      have e1 : R ^ 2 ≤ 2 * R * t * v := by
        rw [mul_assoc, htv]; nlinarith
      have e2 : 2 * R * t * v ≤ 2 * R * t * u := by gcongr
      have e3 : 2 * R * t * u ≤ c * (2 * R * t) * u := by
        have : 0 ≤ 2 * R * t * u := by positivity
        nlinarith
      linarith
    calc R ^ 2 * (r * s) = R ^ 2 * s * r := by ring
      _ ≤ c * (2 * R * t) * u * s * r := by gcongr
      _ = c * (2 * R * t) * (s * u) * r := by ring
      _ = c * (2 * R * t) * r ^ 2 := by rw [hsu]; ring

/-- **Davenport, p. 77 (row 11-9).** On a circle `|z| = R ≥ 1` with `|R - r_n| ≥ r_n⁻²` for all
zeros, the canonical product satisfies `|P(z)| ≥ exp(-K(R) ∑ r_n^{-1-ε})`,
`K(R) = (3 log 2R + 2)(2R)^{1+ε}`; in particular `|P(z)| ≥ exp(-R^{1+2ε})` for large `R`. -/
@[kb "davenport1980" "Ch 11, p. 77"]
theorem norm_canonicalProductOne_ge {ι : Type*} {a : ι → ℂ} (ha : Summable fun i ↦ ‖a i‖⁻¹ ^ 2)
    (ha0 : ∀ i, a i ≠ 0) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    (hS : Summable fun i ↦ ‖a i‖ ^ (-(1 + ε))) {R : ℝ} (hR : 1 ≤ R)
    (hgood : ∀ i, ‖a i‖⁻¹ ^ 2 ≤ |R - ‖a i‖|) {z : ℂ} (hz : ‖z‖ = R) :
    Real.exp (-((3 * Real.log (2 * R) + 2) * (2 * R) ^ (1 + ε) * ∑' i, ‖a i‖ ^ (-(1 + ε)))) ≤
      ‖canonicalProductOne a z‖ := by
  set K := (3 * Real.log (2 * R) + 2) * (2 * R) ^ (1 + ε)
  have hK : 0 ≤ K := by
    have : 0 ≤ Real.log (2 * R) := Real.log_nonneg (by linarith)
    positivity
  have hfac : ∀ i, Real.exp (-(K * ‖a i‖ ^ (-(1 + ε)))) ≤ ‖weierstrassFactorOne (z / a i)‖ :=
    fun i ↦ norm_weierstrassFactorOne_ge hε0 hε1 hR hz rfl (norm_pos_iff.mpr (ha0 i)) (hgood i)
  have hfin : ∀ s : Finset ι, Real.exp (-(K * ∑' i, ‖a i‖ ^ (-(1 + ε)))) ≤
      ‖∏ i ∈ s, weierstrassFactorOne (z / a i)‖ := by
    intro s
    rw [norm_prod]
    calc Real.exp (-(K * ∑' i, ‖a i‖ ^ (-(1 + ε))))
        ≤ Real.exp (-(K * ∑ i ∈ s, ‖a i‖ ^ (-(1 + ε)))) := by
          refine Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_left ?_ hK))
          exact hS.sum_le_tsum s fun i _ ↦ Real.rpow_nonneg (norm_nonneg _) _
      _ = ∏ i ∈ s, Real.exp (-(K * ‖a i‖ ^ (-(1 + ε)))) := by
          rw [← Real.exp_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
      _ ≤ ∏ i ∈ s, ‖weierstrassFactorOne (z / a i)‖ :=
          Finset.prod_le_prod₀ (fun i _ ↦ (Real.exp_pos _).le) fun i _ ↦ hfac i
  have hlim := (continuous_norm.tendsto _).comp (hasProd_canonicalProductOne ha z)
  exact ge_of_tendsto' hlim hfin

/-- An explicit bound used with `ε = 1/2`: `(3 log 2R + 2)(2R)^{3/2} ≤ 56 R^{7/4}` for `R ≥ 1`. -/
lemma hadamard_K_le {R : ℝ} (hR : 1 ≤ R) :
    (3 * Real.log (2 * R) + 2) * (2 * R) ^ (1 + 1 / 2 : ℝ) ≤ 56 * R ^ (7 / 4 : ℝ) := by
  have h2R : 0 < 2 * R := by linarith
  have hlog : Real.log (2 * R) ≤ (2 * R) ^ (1 / 4 : ℝ) / (1 / 4) :=
    Real.log_le_rpow_div h2R.le (by norm_num)
  have hq : 1 ≤ (2 * R) ^ (1 / 4 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  have h1 : 3 * Real.log (2 * R) + 2 ≤ 14 * (2 * R) ^ (1 / 4 : ℝ) := by
    have : (2 * R) ^ (1 / 4 : ℝ) / (1 / 4) = 4 * (2 * R) ^ (1 / 4 : ℝ) := by ring
    linarith
  have h2 : (2 * R) ^ (1 / 4 : ℝ) * (2 * R) ^ (1 + 1 / 2 : ℝ) = (2 * R) ^ (7 / 4 : ℝ) := by
    rw [← Real.rpow_add h2R]; norm_num
  have h3 : (2 * R) ^ (7 / 4 : ℝ) = 2 ^ (7 / 4 : ℝ) * R ^ (7 / 4 : ℝ) :=
    Real.mul_rpow (by norm_num) (by linarith)
  have h4 : (2 : ℝ) ^ (7 / 4 : ℝ) ≤ 4 := by
    calc (2 : ℝ) ^ (7 / 4 : ℝ) ≤ 2 ^ (2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 4 := by norm_num
  have hpos : 0 ≤ (2 * R) ^ (1 + 1 / 2 : ℝ) := by positivity
  have hRpos : 0 ≤ R ^ (7 / 4 : ℝ) := by positivity
  calc (3 * Real.log (2 * R) + 2) * (2 * R) ^ (1 + 1 / 2 : ℝ)
      ≤ 14 * (2 * R) ^ (1 / 4 : ℝ) * (2 * R) ^ (1 + 1 / 2 : ℝ) := by gcongr
    _ = 14 * (2 ^ (7 / 4 : ℝ) * R ^ (7 / 4 : ℝ)) := by rw [mul_assoc, h2, h3]
    _ ≤ 14 * (4 * R ^ (7 / 4 : ℝ)) := by gcongr
    _ = 56 * R ^ (7 / 4 : ℝ) := by ring

/-- The number of indices of `ZeroIndex f` sitting at `z` is the order of vanishing. -/
lemma card_zeroIndex_fiber (f : ℂ → ℂ) (z : ℂ) (S : Finset (ZeroIndex f))
    (hS : ∀ i, i ∈ S ↔ i.val = z) : S.card = analyticOrderNatAt f z := by
  classical
  have : S = Finset.univ.image (fun k : Fin (analyticOrderNatAt f z) ↦ (⟨z, k⟩ : ZeroIndex f)) := by
    ext ⟨w, k⟩
    simp only [hS, ZeroIndex.val, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro rfl; exact ⟨k, rfl⟩
    · rintro ⟨k', hk'⟩; exact (congrArg Sigma.fst hk').symm
  rw [this, Finset.card_image_of_injective _ sigma_mk_injective]
  simp

/-- The canonical product over the zeros of `f` vanishes to the same order as `f`. -/
theorem analyticOrderAt_canonicalProductOne_zeroIndex {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hf0 : f 0 ≠ 0) (ha : Summable fun i : ZeroIndex f ↦ ‖i.val‖⁻¹ ^ 2)
    (ha0 : ∀ i : ZeroIndex f, i.val ≠ 0) (z : ℂ) :
    analyticOrderAt (canonicalProductOne fun i : ZeroIndex f ↦ i.val) z = analyticOrderAt f z := by
  obtain ⟨S, hS, hord⟩ := analyticOrderAt_canonicalProductOne ha ha0 z
  rw [hord, card_zeroIndex_fiber f z S hS]
  have hfin : analyticOrderAt f z ≠ ⊤ :=
    AnalyticOnNhd.analyticOrderAt_ne_top_of_isPreconnected (fun w _ ↦ hf.analyticAt w)
      isPreconnected_univ (mem_univ 0) (mem_univ z)
      (by rw [(hf.analyticAt 0).analyticOrderAt_eq_zero.mpr hf0]; simp)
  rw [analyticOrderNatAt, ENat.natCast_toNat hfin]

/-- Summability facts for an entire function of order at most one with `f(0) ≠ 0`. -/
lemma summable_of_entireOrder_le_one {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hf0 : f 0 ≠ 0)
    (hord : entireOrder f ≤ 1) :
    (Summable fun i : ZeroIndex f ↦ ‖i.val‖⁻¹ ^ 2) ∧ (∀ i : ZeroIndex f, i.val ≠ 0) := by
  have hρ : entireOrder f ≤ ((1 : ℝ≥0) : ℝ≥0∞) := by simpa using hord
  have h2 := Davenport.summable_norm_zero_rpow_neg hf hf0 hρ (β := 2) (by norm_num)
  refine ⟨h2.congr fun i ↦ ?_, fun i h ↦ ?_⟩
  · rw [Real.rpow_neg (norm_nonneg _), inv_pow]
    norm_cast
  · obtain ⟨r₀, hr₀, hr₀le⟩ := exists_pos_le_norm_val hf hf0
    have := hr₀le i
    rw [h, norm_zero] at this
    linarith

/-- Hadamard's factorization with the canonical product written as `canonicalProductOne`. -/
theorem exists_eq_exp_mul_canonicalProductOne {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hf0 : f 0 ≠ 0) (hord : entireOrder f ≤ 1) :
    ∃ A B : ℂ, ∀ z, f z = Complex.exp (A + B * z) *
      canonicalProductOne (fun i : ZeroIndex f ↦ i.val) z := by
  have hρ : entireOrder f ≤ ((1 : ℝ≥0) : ℝ≥0∞) := by simpa using hord
  obtain ⟨ha, ha0⟩ := summable_of_entireOrder_le_one hf hf0 hord
  have hS : Summable fun i : ZeroIndex f ↦ ‖i.val‖ ^ (-(1 + 1 / 2 : ℝ)) :=
    Davenport.summable_norm_zero_rpow_neg hf hf0 hρ (by norm_num)
  have hP := differentiable_canonicalProductOne ha
  obtain ⟨F, hF, hFne, hfPF⟩ := exists_differentiable_eq_mul hf hP (by simp)
    fun z ↦ (analyticOrderAt_canonicalProductOne_zeroIndex hf hf0 ha ha0 z).symm
  have : Fact (Differentiable ℂ f) := ⟨hf⟩
  -- growth of `f`
  have hev := eventually_norm_le_exp_of_entireOrder_le hρ (a := 5 / 4) (by norm_num)
  obtain ⟨R₀, hR₀⟩ := (Metric.hasBasis_cobounded_compl_closedBall (0 : ℂ)).eventually_iff.mp hev
    |>.imp fun r hr ↦ hr.2
  set Ssum := ∑' i : ZeroIndex f, ‖i.val‖ ^ (-(1 + 1 / 2 : ℝ))
  have hSsum : 0 ≤ Ssum := tsum_nonneg fun i ↦ Real.rpow_nonneg (norm_nonneg _) _
  have hcirc : ∀ T : ℝ, ∃ R ≥ T, ∀ z : ℂ, ‖z‖ = R →
      ‖F z‖ ≤ Real.exp ((1 + 56 * Ssum) * R ^ (7 / 4 : ℝ)) := by
    intro T
    obtain ⟨R, hRT, hRgood⟩ :=
      exists_good_radius (fun i : ZeroIndex f ↦ ‖i.val‖) ha (max T (max R₀ 1) + 1)
    have hR1 : 1 ≤ R := by linarith [le_max_right T (max R₀ 1), le_max_right R₀ 1]
    refine ⟨R, by linarith [le_max_left T (max R₀ 1)], fun z hz ↦ ?_⟩
    have hPlow := norm_canonicalProductOne_ge ha ha0 (ε := 1 / 2) (by norm_num) (by norm_num) hS
      hR1 (fun i ↦ (hRgood i).le) hz
    have hfz : ‖f z‖ ≤ Real.exp (‖z‖ ^ (5 / 4 : ℝ)) := hR₀ (by
      simp only [mem_compl_iff, mem_closedBall, dist_zero_right, not_le, hz]
      linarith [le_max_left R₀ 1, le_max_right T (max R₀ 1)])
    rw [hz] at hfz
    have hPpos : 0 < ‖canonicalProductOne (fun i : ZeroIndex f ↦ i.val) z‖ :=
      lt_of_lt_of_le (Real.exp_pos _) hPlow
    have hFz : ‖F z‖ = ‖f z‖ / ‖canonicalProductOne (fun i : ZeroIndex f ↦ i.val) z‖ := by
      rw [hfPF z, norm_mul]; field_simp
    rw [hFz, div_le_iff₀ hPpos]
    have hK := hadamard_K_le hR1
    have h54 : R ^ (5 / 4 : ℝ) ≤ R ^ (7 / 4 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hR1 (by norm_num)
    have hR74 : 0 ≤ R ^ (7 / 4 : ℝ) := by positivity
    calc ‖f z‖ ≤ Real.exp (R ^ (5 / 4 : ℝ)) := hfz
      _ ≤ Real.exp ((1 + 56 * Ssum) * R ^ (7 / 4 : ℝ) +
            -((3 * Real.log (2 * R) + 2) * (2 * R) ^ (1 + 1 / 2 : ℝ) * Ssum)) := by
          refine Real.exp_le_exp.mpr ?_
          have : (3 * Real.log (2 * R) + 2) * (2 * R) ^ (1 + 1 / 2 : ℝ) * Ssum ≤
              56 * R ^ (7 / 4 : ℝ) * Ssum := mul_le_mul_of_nonneg_right hK hSsum
          nlinarith
      _ = Real.exp ((1 + 56 * Ssum) * R ^ (7 / 4 : ℝ)) *
            Real.exp (-((3 * Real.log (2 * R) + 2) * (2 * R) ^ (1 + 1 / 2 : ℝ) * Ssum)) :=
          Real.exp_add _ _
      _ ≤ Real.exp ((1 + 56 * Ssum) * R ^ (7 / 4 : ℝ)) *
            ‖canonicalProductOne (fun i : ZeroIndex f ↦ i.val) z‖ := by
          gcongr
  obtain ⟨Q, hQdeg, hQ⟩ := exists_polynomial_of_norm_le_on_circles hF hFne (by norm_num) hcirc
  have hQ1 : Q.natDegree ≤ 1 := by
    have : (Q.natDegree : ℝ) < 2 := lt_of_le_of_lt hQdeg (by norm_num)
    have : Q.natDegree < 2 := by exact_mod_cast this
    omega
  obtain ⟨B, A, hBA⟩ := Polynomial.exists_eq_X_add_C_of_natDegree_le_one hQ1
  refine ⟨A, B, fun z ↦ ?_⟩
  rw [hfPF z, hQ z, hBA]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  ring_nf

/-- **Hadamard's factorization theorem for order one** (Davenport, Ch. 11, p. 77, (6);
row 11-10). An entire function `f` of order at most `1` with `f(0) ≠ 0` is
`f(z) = e^{A + Bz} ∏ (1 - z/z_n) e^{z/z_n}`, the product running over the zeros `z_n` of `f`
repeated according to multiplicity (and converging absolutely, locally uniformly). -/
@[kb "davenport1980" "Ch 11, p. 77"]
theorem Davenport.hadamard_factorization_order_one {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hf0 : f 0 ≠ 0) (hord : entireOrder f ≤ 1) :
    ∃ A B : ℂ, ∀ z, f z = Complex.exp (A + B * z) *
      ∏' i : ZeroIndex f, (1 - z / i.val) * Complex.exp (z / i.val) :=
  exists_eq_exp_mul_canonicalProductOne hf hf0 hord

/-- `|E₁(w)| ≤ e^{2|w|}`. -/
lemma norm_weierstrassFactorOne_le (w : ℂ) :
    ‖weierstrassFactorOne w‖ ≤ Real.exp (2 * ‖w‖) := by
  rw [weierstrassFactorOne, norm_mul, Complex.norm_exp, two_mul, Real.exp_add]
  refine mul_le_mul ?_ (Real.exp_le_exp.mpr (Complex.re_le_norm w)) (Real.exp_pos _).le
    (Real.exp_pos _).le
  calc ‖1 - w‖ ≤ ‖(1 : ℂ)‖ + ‖w‖ := norm_sub_le _ _
    _ = ‖w‖ + 1 := by simp [add_comm]
    _ ≤ Real.exp ‖w‖ := Real.add_one_le_exp _

/-- If `∑ ‖a i‖⁻¹` converges, `|P(z)| ≤ exp(2|z| ∑ ‖a i‖⁻¹)`. -/
theorem norm_canonicalProductOne_le {ι : Type*} {a : ι → ℂ} (ha : Summable fun i ↦ ‖a i‖⁻¹ ^ 2)
    (h1 : Summable fun i ↦ ‖a i‖⁻¹) (z : ℂ) :
    ‖canonicalProductOne a z‖ ≤ Real.exp (2 * ‖z‖ * ∑' i, ‖a i‖⁻¹) := by
  have hfin : ∀ s : Finset ι, ‖∏ i ∈ s, weierstrassFactorOne (z / a i)‖ ≤
      Real.exp (2 * ‖z‖ * ∑' i, ‖a i‖⁻¹) := by
    intro s
    rw [norm_prod]
    calc ∏ i ∈ s, ‖weierstrassFactorOne (z / a i)‖ ≤ ∏ i ∈ s, Real.exp (2 * ‖z / a i‖) :=
          Finset.prod_le_prod₀ (fun i _ ↦ norm_nonneg _) fun i _ ↦ norm_weierstrassFactorOne_le _
      _ = Real.exp (2 * ‖z‖ * ∑ i ∈ s, ‖a i‖⁻¹) := by
          rw [← Real.exp_sum, Finset.mul_sum]
          simp only [div_eq_mul_inv, norm_mul, norm_inv, mul_assoc]
      _ ≤ Real.exp (2 * ‖z‖ * ∑' i, ‖a i‖⁻¹) := by
          gcongr
          exact h1.sum_le_tsum s fun i _ ↦ inv_nonneg.mpr (norm_nonneg _)
  have hlim := (continuous_norm.tendsto _).comp (hasProd_canonicalProductOne ha z)
  exact le_of_tendsto' hlim hfin

/-- **Davenport, Ch. 11, p. 78, (7) (row 11-11).** If `f` is entire of order at most `1`,
`f(0) ≠ 0`, and `∑ r_n⁻¹` converges over its zeros, then `|f(z)| ≤ e^{C|z|}` for `|z| ≥ 1`. -/
@[kb "davenport1980" "Ch 11, p. 78"]
theorem Davenport.norm_le_exp_of_summable_inv {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hf0 : f 0 ≠ 0) (hord : entireOrder f ≤ 1)
    (h1 : Summable fun i : ZeroIndex f ↦ ‖i.val‖⁻¹) :
    ∃ C : ℝ, ∀ z : ℂ, 1 ≤ ‖z‖ → ‖f z‖ ≤ Real.exp (C * ‖z‖) := by
  obtain ⟨ha, -⟩ := summable_of_entireOrder_le_one hf hf0 hord
  obtain ⟨A, B, hAB⟩ := exists_eq_exp_mul_canonicalProductOne hf hf0 hord
  set S₁ := ∑' i : ZeroIndex f, ‖i.val‖⁻¹
  refine ⟨‖A‖ + ‖B‖ + 2 * S₁, fun z hz ↦ ?_⟩
  have hS₁ : 0 ≤ S₁ := tsum_nonneg fun i ↦ inv_nonneg.mpr (norm_nonneg _)
  rw [hAB z, norm_mul, Complex.norm_exp]
  have hP := norm_canonicalProductOne_le ha h1 z
  have hre : (A + B * z).re ≤ ‖A‖ + ‖B‖ * ‖z‖ := by
    refine (Complex.re_le_norm _).trans ((norm_add_le _ _).trans ?_)
    rw [norm_mul]
  calc Real.exp (A + B * z).re * ‖canonicalProductOne (fun i : ZeroIndex f ↦ i.val) z‖
      ≤ Real.exp (‖A‖ + ‖B‖ * ‖z‖) * Real.exp (2 * ‖z‖ * S₁) := by
        gcongr
    _ = Real.exp (‖A‖ + ‖B‖ * ‖z‖ + 2 * ‖z‖ * S₁) := (Real.exp_add _ _).symm
    _ ≤ Real.exp ((‖A‖ + ‖B‖ + 2 * S₁) * ‖z‖) := by
        refine Real.exp_le_exp.mpr ?_
        have : ‖A‖ ≤ ‖A‖ * ‖z‖ := le_mul_of_one_le_right (norm_nonneg _) hz
        nlinarith

/-- **Davenport, Ch. 11, p. 78, summary (row 11-12).** An entire function `f` of order (at most)
`1` with `f(0) ≠ 0` has the form `e^{A + Bz} ∏ (1 - z/z_n) e^{z/z_n}`; if `r_n = |z_n|`, then
`∑ r_n^{-1-ε}` converges for every `ε > 0`; and if `∑ r_n⁻¹` converges, then `|f(z)| ≤ e^{C|z|}`
for `|z| ≥ 1`. -/
@[kb "davenport1980" "Ch 11, p. 78"]
theorem Davenport.entire_order_one_summary {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hf0 : f 0 ≠ 0) (hord : entireOrder f ≤ 1) :
    (∃ A B : ℂ, ∀ z, f z = Complex.exp (A + B * z) *
      ∏' i : ZeroIndex f, (1 - z / i.val) * Complex.exp (z / i.val)) ∧
    (∀ ε : ℝ, 0 < ε → Summable fun i : ZeroIndex f ↦ ‖i.val‖ ^ (-1 - ε)) ∧
    ((Summable fun i : ZeroIndex f ↦ ‖i.val‖⁻¹) →
      ∃ C : ℝ, ∀ z : ℂ, 1 ≤ ‖z‖ → ‖f z‖ ≤ Real.exp (C * ‖z‖)) := by
  have hρ : entireOrder f ≤ ((1 : ℝ≥0) : ℝ≥0∞) := by simpa using hord
  refine ⟨Davenport.hadamard_factorization_order_one hf hf0 hord, fun ε hε ↦ ?_,
    Davenport.norm_le_exp_of_summable_inv hf hf0 hord⟩
  have := Davenport.summable_norm_zero_rpow_neg hf hf0 hρ (β := 1 + ε) (by simpa using hε)
  convert this using 3
  ring

end NTKB
