/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.NumberTheory.LSeries.HurwitzZetaOdd
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Analytic.Uniqueness
import NTKB.Attr

/-!
# The odd Hurwitz zeta function at `s = 1`

For `0 < a < 1`,
$$\zeta_{\mathrm{odd}}(a, 1) = \frac{1}{2}\sum_{n\ge0}\Bigl(\frac{1}{n+a}-\frac{1}{n+1-a}\Bigr)
  = \frac{\pi}{2}\cot(\pi a),$$
where `ζ_odd(a, s)` is Mathlib's `HurwitzZeta.hurwitzZetaOdd a s` (the entire function equal to
`½ ∑_{n ∈ ℤ} sign(n + a) |n + a|^{-s}` for `Re s > 1`).

Mathlib only gives the series for `Re s > 1`, where it converges absolutely. Here the paired series
`½ ∑_{n ≥ 0} ((n + a)^{-s} - (n + 1 - a)^{-s})` is shown to converge locally uniformly on
`Re s > 0` (by the mean value theorem its terms are `O(|s| n^{-Re s - 1})`), hence to be
holomorphic there, and it agrees with `ζ_odd(a, s)` on `Re s > 0` by the identity theorem. At
`s = 1` it is Mathlib's partial-fraction expansion of the cotangent (`cot_series_rep'`) up to a
telescoping series.

This is the analytic input of `L(0, χ) = -B_{1,χ}` for odd `χ`
(`NTKB.Elementary.SpecialValues.ValueAtZero`).
-/

noncomputable section

open Complex HurwitzZeta Set Filter Topology
open scoped Real

namespace NTKB

/-- The paired term `((n + a)^{-s} - (n + 1 - a)^{-s}) / 2` of the odd Hurwitz zeta series. -/
def hurwitzOddTerm (a : ℝ) (n : ℕ) (s : ℂ) : ℂ :=
  (((n : ℂ) + a) ^ (-s) - ((n : ℂ) + 1 - a) ^ (-s)) / 2

/-- Mean value bound: for `x, y ≥ p > 0` and `Re s ≥ 0`,
`‖x^{-s} - y^{-s}‖ ≤ ‖s‖ p^{-Re s - 1} |x - y|`. -/
theorem norm_cpow_neg_sub_cpow_neg_le {p x y : ℝ} (hp : 0 < p) (hx : p ≤ x) (hy : p ≤ y)
    {s : ℂ} (hs : 0 ≤ s.re) :
    ‖(x : ℂ) ^ (-s) - (y : ℂ) ^ (-s)‖ ≤ ‖s‖ * p ^ (-s.re - 1) * |x - y| := by
  rcases eq_or_ne s 0 with rfl | hs0
  · simp
  have hderiv : ∀ t ∈ Ici p, HasDerivWithinAt (fun t : ℝ ↦ (t : ℂ) ^ (-s))
      (-s * (t : ℂ) ^ (-s - 1)) (Ici p) t := by
    intro t ht
    have ht0 : t ≠ 0 := (hp.trans_le ht).ne'
    exact (hasDerivAt_ofReal_cpow_const ht0 (neg_ne_zero.mpr hs0)).hasDerivWithinAt
  have hbound : ∀ t ∈ Ici p, ‖-s * (t : ℂ) ^ (-s - 1)‖ ≤ ‖s‖ * p ^ (-s.re - 1) := by
    intro t ht
    have ht0 : 0 < t := hp.trans_le ht
    rw [norm_mul, norm_neg, norm_cpow_eq_rpow_re_of_pos ht0]
    gcongr
    · simp only [sub_re, neg_re, one_re]
      exact Real.rpow_le_rpow_of_nonpos hp ht (by linarith)
  have h := (convex_Ici p).norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound hy hx
  simpa [Real.norm_eq_abs] using h

/-- The shifted terms `n ↦ term (n + 1)` are bounded by `½ ‖s‖ (n + 1)^{-Re s - 1}`. -/
theorem norm_hurwitzOddTerm_succ_le {a : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) (n : ℕ) {s : ℂ}
    (hs : 0 ≤ s.re) :
    ‖hurwitzOddTerm a (n + 1) s‖ ≤ ‖s‖ / 2 * ((n : ℝ) + 1) ^ (-s.re - 1) := by
  have hp : (0 : ℝ) < n + 1 := by positivity
  have hx : ((n : ℝ) + 1) ≤ ((n + 1 : ℕ) : ℝ) + a := by push_cast; linarith [ha.1]
  have hy : ((n : ℝ) + 1) ≤ ((n + 1 : ℕ) : ℝ) + 1 - a := by push_cast; linarith [ha.2]
  have h := norm_cpow_neg_sub_cpow_neg_le hp hx hy hs
  have hxy : |(((n + 1 : ℕ) : ℝ) + a) - (((n + 1 : ℕ) : ℝ) + 1 - a)| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [ha.1, ha.2]
  unfold hurwitzOddTerm
  rw [norm_div, Complex.norm_two]
  have hcast : ((((n + 1 : ℕ) : ℝ) + a : ℝ) : ℂ) = ((n + 1 : ℕ) : ℂ) + a := by push_cast; ring
  have hcast' : ((((n + 1 : ℕ) : ℝ) + 1 - a : ℝ) : ℂ) = ((n + 1 : ℕ) : ℂ) + 1 - a := by
    push_cast; ring
  rw [hcast, hcast'] at h
  have hnn : 0 ≤ ‖s‖ * ((n : ℝ) + 1) ^ (-s.re - 1) := by positivity
  calc ‖(((n + 1 : ℕ) : ℂ) + a) ^ (-s) - (((n + 1 : ℕ) : ℂ) + 1 - a) ^ (-s)‖ / 2
      ≤ ‖s‖ * ((n : ℝ) + 1) ^ (-s.re - 1) * 1 / 2 := by
        gcongr
        exact h.trans (mul_le_mul_of_nonneg_left hxy hnn)
    _ = ‖s‖ / 2 * ((n : ℝ) + 1) ^ (-s.re - 1) := by ring

/-- Each term is an entire function of `s`. -/
theorem differentiable_hurwitzOddTerm {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (n : ℕ) :
    Differentiable ℂ (hurwitzOddTerm a n) := by
  have h1 : ((n : ℂ) + a) ≠ 0 := by
    have : (0 : ℝ) < n + a := by linarith [ha.1, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    exact_mod_cast this.ne'
  have h2 : ((n : ℂ) + 1 - a) ≠ 0 := by
    have : (0 : ℝ) < n + 1 - a := by linarith [ha.2, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    exact_mod_cast this.ne'
  intro s
  unfold hurwitzOddTerm
  refine ((DifferentiableAt.sub ?_ ?_).div_const 2)
  · exact (differentiableAt_id.neg).const_cpow (Or.inl h1)
  · exact (differentiableAt_id.neg).const_cpow (Or.inl h2)

/-- The shifted paired series is holomorphic on `Re s > 0`. -/
theorem differentiableOn_tsum_hurwitzOddTerm_succ {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    DifferentiableOn ℂ (fun s ↦ ∑' n : ℕ, hurwitzOddTerm a (n + 1) s) {s | 0 < s.re} := by
  intro s₀ hs₀
  simp only [mem_setOf_eq] at hs₀
  set σ := s₀.re / 2 with hσ
  set R := ‖s₀‖ + 1 with hR
  set V : Set ℂ := {s | σ < s.re} ∩ Metric.ball 0 R with hV
  have hVopen : IsOpen V :=
    (isOpen_lt continuous_const continuous_re).inter Metric.isOpen_ball
  have hs₀V : s₀ ∈ V := by
    refine ⟨?_, ?_⟩
    · simp only [mem_setOf_eq, hσ]; linarith
    · simp [hR]
  have hsum : Summable fun n : ℕ ↦ R / 2 * ((n : ℝ) + 1) ^ (-σ - 1) := by
    refine Summable.mul_left _ ?_
    have h := (Real.summable_nat_rpow (p := -σ - 1)).mpr (by linarith)
    have h' := (summable_nat_add_iff 1).mpr h
    simpa using h'
  have hdiff : DifferentiableOn ℂ (fun s ↦ ∑' n : ℕ, hurwitzOddTerm a (n + 1) s) V := by
    refine differentiableOn_tsum_of_summable_norm hsum
      (fun n ↦ (differentiable_hurwitzOddTerm ha (n + 1)).differentiableOn) hVopen ?_
    intro n s hs
    have hre : σ < s.re := hs.1
    have hnorm : ‖s‖ < R := by simpa using hs.2
    have hσ0 : 0 ≤ s.re := by linarith
    refine (norm_hurwitzOddTerm_succ_le (Ioo_subset_Icc_self ha) n hσ0).trans ?_
    have h1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have hpow : ((n : ℝ) + 1) ^ (-s.re - 1) ≤ ((n : ℝ) + 1) ^ (-σ - 1) :=
      Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
    have hpos : 0 ≤ ((n : ℝ) + 1) ^ (-s.re - 1) := by positivity
    calc ‖s‖ / 2 * ((n : ℝ) + 1) ^ (-s.re - 1) ≤ R / 2 * ((n : ℝ) + 1) ^ (-s.re - 1) := by
          gcongr
      _ ≤ R / 2 * ((n : ℝ) + 1) ^ (-σ - 1) := by
          gcongr
  exact (hdiff s₀ hs₀V).differentiableAt (hVopen.mem_nhds hs₀V) |>.differentiableWithinAt

/-- The paired series converges for `Re s ≥ 0`. -/
theorem summable_hurwitzOddTerm {a : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) {s : ℂ} (hs : 0 < s.re) :
    Summable fun n : ℕ ↦ hurwitzOddTerm a n s := by
  refine (summable_nat_add_iff 1).mp ?_
  refine Summable.of_norm_bounded (g := fun n : ℕ ↦ ‖s‖ / 2 * ((n : ℝ) + 1) ^ (-s.re - 1)) ?_
    fun n ↦ norm_hurwitzOddTerm_succ_le ha n hs.le
  refine Summable.mul_left _ ?_
  have h := (Real.summable_nat_rpow (p := -s.re - 1)).mpr (by linarith)
  simpa using (summable_nat_add_iff 1).mpr h

/-- For `Re s > 1`, Mathlib's series for `ζ_odd(a, s)` is the paired series. -/
theorem hasSum_hurwitzOddTerm_of_one_lt_re {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) {s : ℂ}
    (hs : 1 < s.re) :
    HasSum (fun n : ℕ ↦ hurwitzOddTerm a n s) (hurwitzZetaOdd a s) := by
  refine (hasSum_nat_hurwitzZetaOdd_of_mem_Icc (Ioo_subset_Icc_self ha) hs).congr_fun fun n ↦ ?_
  unfold hurwitzOddTerm
  rw [cpow_neg, cpow_neg, one_div, one_div]

/-- **The paired series represents `ζ_odd(a, s)` on `Re s > 0`.** -/
theorem hasSum_hurwitzOddTerm {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) {s : ℂ} (hs : 0 < s.re) :
    HasSum (fun n : ℕ ↦ hurwitzOddTerm a n s) (hurwitzZetaOdd a s) := by
  set U : Set ℂ := {s | 0 < s.re}
  set G : ℂ → ℂ := fun s ↦ hurwitzOddTerm a 0 s + ∑' n : ℕ, hurwitzOddTerm a (n + 1) s
  have hUopen : IsOpen U := isOpen_lt continuous_const continuous_re
  have hG : DifferentiableOn ℂ G U :=
    (differentiable_hurwitzOddTerm ha 0).differentiableOn.add
      (differentiableOn_tsum_hurwitzOddTerm_succ ha)
  have hGsum (s : ℂ) (hs : 0 < s.re) : HasSum (fun n : ℕ ↦ hurwitzOddTerm a n s) (G s) := by
    have hsm := summable_hurwitzOddTerm (Ioo_subset_Icc_self ha) hs
    have h := hsm.hasSum
    rwa [hsm.tsum_eq_zero_add] at h
  have hZ : DifferentiableOn ℂ (fun s ↦ hurwitzZetaOdd a s) U :=
    (differentiable_hurwitzZetaOdd a).differentiableOn
  have heq : EqOn (fun s ↦ hurwitzZetaOdd a s) G U := by
    refine (hZ.analyticOnNhd hUopen).eqOn_of_preconnected_of_eventuallyEq
      (hG.analyticOnNhd hUopen) (convex_halfSpace_re_gt 0).isPreconnected
      (z₀ := 2) (by simp [U]) ?_
    have hmem : {s : ℂ | 1 < s.re} ∈ 𝓝 (2 : ℂ) :=
      (isOpen_lt continuous_const continuous_re).mem_nhds (by simp)
    filter_upwards [hmem] with s hs
    have hs' : 1 < s.re := hs
    exact (hasSum_hurwitzOddTerm_of_one_lt_re ha hs').unique (hGsum s (by linarith))
  have h := heq (show s ∈ U from hs)
  simp only at h
  rw [h]
  exact hGsum s hs

/-- A telescoping series. -/
theorem hasSum_sub_succ_of_tendsto_zero {f : ℕ → ℂ} (hf : Tendsto f atTop (𝓝 0))
    (hs : Summable fun n ↦ f n - f (n + 1)) : HasSum (fun n ↦ f n - f (n + 1)) (f 0) := by
  rw [hs.hasSum_iff_tendsto_nat]
  have h : (fun n ↦ ∑ i ∈ Finset.range n, (f i - f (i + 1))) = fun n ↦ f 0 - f n := by
    funext n
    exact Finset.sum_range_sub' f n
  rw [h]
  simpa using (tendsto_const_nhds (x := f 0)).sub hf

/-- `1 / (n + a) → 0`. -/
theorem tendsto_one_div_natCast_add {a : ℝ} (ha : 0 ≤ a) :
    Tendsto (fun n : ℕ ↦ 1 / ((n : ℂ) + a)) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hnorm (n : ℕ) : ‖1 / ((n : ℂ) + a)‖ = 1 / ((n : ℝ) + a) := by
    rw [show ((n : ℂ) + a) = (((n : ℝ) + a : ℝ) : ℂ) by push_cast; ring, norm_div, norm_one,
      norm_real, Real.norm_of_nonneg (by positivity)]
  simp_rw [hnorm]
  refine tendsto_const_nhds.div_atTop ?_
  exact tendsto_atTop_add_const_right _ a tendsto_natCast_atTop_atTop

/-- **`ζ_odd(a, 1) = (π/2) cot(πa)` for `0 < a < 1`.** -/
@[kb "washington1997" "§4.1 (the value L(1, χ) for odd χ via the cotangent)"]
theorem hurwitzZetaOdd_one {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    hurwitzZetaOdd a 1 = π / 2 * Complex.cot (π * a) := by
  have h1 := hasSum_hurwitzOddTerm ha (s := 1) (by simp)
  -- the terms at `s = 1`
  have hterm (n : ℕ) : hurwitzOddTerm a n 1 =
      ((1 / ((n : ℂ) + a) - 1 / ((n : ℂ) + 1 + a)) +
        (1 / ((a : ℂ) - (n + 1)) + 1 / ((a : ℂ) + (n + 1)))) / 2 := by
    have hb : ((a : ℂ) - (n + 1)) = -((n : ℂ) + 1 - a) := by ring
    unfold hurwitzOddTerm
    rw [cpow_neg_one, cpow_neg_one, hb]
    field_simp
    ring
  -- `a` is not an integer
  have haZ : (a : ℂ) ∈ integerComplement := by
    rw [mem_integerComplement_iff]
    rintro ⟨z, hz⟩
    have hz' : (z : ℝ) = a := by exact_mod_cast hz
    have h0 : (0 : ℝ) < z := hz' ▸ ha.1
    have h1' : (z : ℝ) < 1 := hz' ▸ ha.2
    have : (0 : ℤ) < z := by exact_mod_cast h0
    have : z < (1 : ℤ) := by exact_mod_cast h1'
    omega
  -- Mathlib's partial fractions: `∑ (1/(a - (n+1)) + 1/(a + (n+1))) = π cot(πa) - 1/a`
  have hcot : HasSum (fun n : ℕ ↦ 1 / ((a : ℂ) - (n + 1)) + 1 / ((a : ℂ) + (n + 1)))
      (π * Complex.cot (π * a) - 1 / a) := by
    rw [cot_series_rep' haZ]
    exact (summable_cotTerm haZ).hasSum
  -- the telescoping part sums to `1/a`
  have htel : HasSum (fun n : ℕ ↦ 1 / ((n : ℂ) + a) - 1 / ((n : ℂ) + 1 + a)) (1 / a) := by
    have hf := tendsto_one_div_natCast_add ha.1.le
    have hsum : Summable fun n : ℕ ↦ 1 / ((n : ℂ) + a) - 1 / ((n : ℂ) + 1 + a) := by
      have hs2 := (h1.summable.mul_left 2).sub hcot.summable
      refine hs2.congr fun n ↦ ?_
      simp only [hterm]
      ring
    have h := hasSum_sub_succ_of_tendsto_zero hf (by
      refine hsum.congr fun n ↦ ?_
      push_cast
      ring_nf)
    convert h using 1
    · funext n
      push_cast
      ring_nf
    · simp
  have htot := (htel.add hcot).div_const 2
  have hval := h1.unique (htot.congr_fun fun n ↦ (hterm n).symm ▸ rfl)
  rw [hval]
  ring
