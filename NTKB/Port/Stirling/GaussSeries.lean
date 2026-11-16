/-
Copyright (c) 2026 The Tau Ceti contributors. Released under Apache 2.0 license.
Copied into NTKB with credit from Tau Ceti (`TauCeti/Analysis/SpecialFunctions/Gamma/Real.lean`
and `TauCeti/Analysis/SpecialFunctions/Gamma/GaussSeries.lean`, main `1ff53249`); NTKB does not
depend on Tau Ceti. Changes: namespace `NTKB.Port`, only the declarations needed for Gauss' series
(real digamma is the private `realDigamma`, only the bound `|ψ(x) - log x| ≤ 1/x` is kept).
Original authors: OpenAI Codex.
-/
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Complex.HalfPlane
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn
import NTKB.Port.Stirling.Helpers

/-!
# Gauss' series for digamma (port from Tau Ceti)

The paired reciprocal series `∑' n, (1 / (n + 1) - 1 / (s + n))` converges absolutely at
every complex point, and outside the nonpositive integers it equals `digamma s + γ`.

The proof first identifies the sum on the positive real axis using the digamma recurrence
and the bound `|ψ(x) - log x| ≤ 1 / x` (from log-convexity of Gamma). Local uniform convergence
extends the identity through the right half-plane by the identity theorem. Recurrences for the
sum and digamma then extend it to every regular complex point.

## References

* [NIST DLMF, equation 5.7.6](https://dlmf.nist.gov/5.7.E6).
* T. Tao, [Mathlib PR #43556](https://github.com/leanprover-community/mathlib4/pull/43556),
  for the Gauss series theorem statements.
-/

open Filter Set Topology Asymptotics

namespace NTKB.Port

/-! ### Real digamma on the positive axis -/

/-- The real digamma function is the logarithmic derivative of real Gamma. -/
private noncomputable def realDigamma : ℝ → ℝ := logDeriv Real.Gamma

private theorem real_ne_neg_nat_of_pos {x : ℝ} (hx : 0 < x) :
    ∀ m : ℕ, x ≠ -(m : ℝ) := by
  intro m
  linarith

private theorem ofReal_ne_neg_nat {x : ℝ} (hx : ∀ m : ℕ, x ≠ -(m : ℝ)) :
    ∀ m : ℕ, (x : ℂ) ≠ -(m : ℂ) := by
  intro m hm
  exact hx m (by exact_mod_cast hm)

/-- At every regular real point, the complex Gamma derivative is the complex coercion
of the derivative of real Gamma. -/
theorem deriv_Gamma_ofReal {x : ℝ} (hx : ∀ m : ℕ, x ≠ -(m : ℝ)) :
    deriv Complex.Gamma (x : ℂ) = ((deriv Real.Gamma x : ℝ) : ℂ) := by
  have hpoles := ofReal_ne_neg_nat hx
  have hc := (Complex.differentiableAt_Gamma _ hpoles).hasDerivAt.comp_ofReal
  have hr := (Real.differentiableAt_Gamma hx).hasDerivAt.ofReal_comp
  have heq : (fun y : ℝ ↦ Complex.Gamma (y : ℂ)) = fun y ↦ (Real.Gamma y : ℂ) :=
    funext Complex.Gamma_ofReal
  rw [heq] at hc
  exact hc.unique hr

/-- At every real point, complex digamma is the coercion of the real Gamma logarithmic
derivative. -/
private theorem digamma_ofReal' {x : ℝ} :
    Complex.digamma (x : ℂ) = (realDigamma x : ℂ) := by
  unfold realDigamma
  by_cases hx : ∀ m : ℕ, x ≠ -(m : ℝ)
  · rw [Complex.digamma_def, logDeriv_apply, deriv_Gamma_ofReal hx, Complex.Gamma_ofReal,
      logDeriv_apply, Complex.ofReal_div]
  · push Not at hx
    obtain ⟨m, rfl⟩ := hx
    simp [Complex.digamma_def, logDeriv_apply, Complex.Gamma_neg_nat_eq_zero,
      Real.Gamma_neg_nat_eq_zero]

private theorem hasDerivAt_log_Gamma {x : ℝ} (hx : ∀ m : ℕ, x ≠ -(m : ℝ)) :
    HasDerivAt (Real.log ∘ Real.Gamma) (realDigamma x) x := by
  simpa only [realDigamma, Function.comp_def, logDeriv_apply] using
    (Real.differentiableAt_Gamma hx).hasDerivAt.log (Real.Gamma_ne_zero hx)

private theorem realDigamma_apply_add_one {x : ℝ} (hx : ∀ m : ℕ, x ≠ -(m : ℝ)) :
    realDigamma (x + 1) = realDigamma x + 1 / x := by
  apply Complex.ofReal_injective
  push_cast
  simpa [← digamma_ofReal', one_div] using
    Complex.digamma_apply_add_one (x : ℂ) (ofReal_ne_neg_nat hx)

private theorem log_Gamma_slope {x : ℝ} (hx : 0 < x) :
    slope (Real.log ∘ Real.Gamma) x (x + 1) = Real.log x := by
  rw [slope_def_field, Function.comp_apply, Function.comp_apply,
    show x + 1 - x = 1 by ring, div_one,
    Real.Gamma_add_one hx.ne', Real.log_mul hx.ne' (Real.Gamma_pos_of_pos hx).ne']
  ring

private theorem realDigamma_le_log_le {x : ℝ} (hx : 0 < x) :
    realDigamma x ≤ Real.log x ∧ Real.log x ≤ realDigamma (x + 1) := by
  have hu := Real.convexOn_log_Gamma.le_slope_of_hasDerivAt (Set.mem_Ioi.mpr hx)
    (Set.mem_Ioi.mpr (by linarith : 0 < x + 1)) (by linarith)
    (hasDerivAt_log_Gamma (real_ne_neg_nat_of_pos hx))
  have hl := Real.convexOn_log_Gamma.slope_le_of_hasDerivAt (Set.mem_Ioi.mpr hx)
    (Set.mem_Ioi.mpr (by linarith : 0 < x + 1)) (by linarith)
    (hasDerivAt_log_Gamma (real_ne_neg_nat_of_pos (by linarith : 0 < x + 1)))
  rw [log_Gamma_slope hx] at hu hl
  exact ⟨hu, hl⟩

private theorem abs_realDigamma_sub_log_le {x : ℝ} (hx : 0 < x) :
    |realDigamma x - Real.log x| ≤ 1 / x := by
  obtain ⟨hu, hl⟩ := realDigamma_le_log_le hx
  rw [realDigamma_apply_add_one (real_ne_neg_nat_of_pos hx)] at hl
  rw [abs_le]
  constructor <;> linarith

/-- An explicit error bound for complex digamma on the positive real axis. -/
theorem norm_digamma_ofReal_sub_log_le {x : ℝ} (hx : 0 < x) :
    ‖Complex.digamma (x : ℂ) - Complex.log (x : ℂ)‖ ≤ x⁻¹ := by
  rw [digamma_ofReal', ← Complex.ofReal_log hx.le, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs]
  simpa only [one_div] using abs_realDigamma_sub_log_le hx

/-- Complex digamma differs from the principal logarithm by `O(1 / x)` on the positive axis. -/
theorem isBigO_digamma_ofReal_sub_log :
    (fun x : ℝ ↦ Complex.digamma (x : ℂ) - Complex.log (x : ℂ)) =O[atTop]
      (fun x : ℝ ↦ x⁻¹) := by
  apply Asymptotics.IsBigO.of_bound 1
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  simpa only [one_mul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hx)] using
    norm_digamma_ofReal_sub_log_le hx

/-! ### Gauss' series -/

open Complex Real

private noncomputable def gaussTerm (s : ℂ) (n : ℕ) : ℂ :=
  1 / ((n : ℂ) + 1) - 1 / (s + n)

private theorem gaussTerm_eq {s : ℂ} {n : ℕ} (hsn : s + n ≠ 0) :
    gaussTerm s n = (s - 1) / (((n : ℂ) + 1) * (s + n)) := by
  rw [gaussTerm, div_sub_div _ _ n.cast_add_one_ne_zero hsn]
  ring

private theorem norm_natCast_add_one (n : ℕ) : ‖(n : ℂ) + 1‖ = (n : ℝ) + 1 := by
  simpa only [Nat.cast_add, Nat.cast_one] using Complex.norm_natCast (n + 1)

private theorem summable_gaussTerm (s : ℂ) : Summable (gaussTerm s) := by
  have hu : Summable (fun n : ℕ ↦ (2 * ‖s - 1‖) / (n : ℝ) ^ 2) := by
    exact ((Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2 : ℕ))).mul_left
      (2 * ‖s - 1‖)).congr (fun n ↦ by ring)
  apply hu.of_norm_bounded_eventually_nat
  filter_upwards [eventually_ge_atTop (2 * ⌈‖s‖⌉₊ + 1)] with n hn
  have hnR : (2 : ℝ) * (⌈‖s‖⌉₊ : ℝ) + 1 ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith [Nat.cast_nonneg (α := ℝ) ⌈‖s‖⌉₊]
  have hnorm : (n : ℝ) - ‖s‖ ≤ ‖s + n‖ := by
    simpa only [Complex.norm_natCast, add_comm] using norm_sub_le_norm_add (n : ℂ) s
  have hlow : (n : ℝ) / 2 ≤ ‖s + n‖ := by linarith [Nat.le_ceil ‖s‖]
  have hsn : s + n ≠ 0 := norm_pos_iff.mp (by linarith)
  rw [gaussTerm_eq hsn, norm_div, norm_mul, norm_natCast_add_one]
  have hden : 0 < ((n : ℝ) + 1) * ‖s + n‖ :=
    mul_pos (by linarith) (by linarith)
  apply (div_le_div_iff₀ hden (by positivity : 0 < (n : ℝ) ^ 2)).mpr
  have hprod : (n : ℝ) ^ 2 / 2 ≤ ((n : ℝ) + 1) * ‖s + n‖ := by
    nlinarith [mul_le_mul_of_nonneg_left hlow (by positivity : 0 ≤ (n : ℝ) + 1)]
  nlinarith only [mul_le_mul_of_nonneg_left hprod (norm_nonneg (s - 1))]

private theorem gaussTerm_sum (s : ℂ) (hs : ∀ m : ℕ, s ≠ -(m : ℂ)) (N : ℕ) :
    ∑ n ∈ Finset.range N, gaussTerm s n =
      digamma s + Real.eulerMascheroniConstant + digamma (N + 1) - digamma (s + N) := by
  rw [add_comm (N : ℂ) 1, digamma_apply_add_nat (ne_neg_natCast_of_re_pos (by norm_num)) N,
    digamma_apply_add_nat hs N, digamma_one]
  simp only [gaussTerm, Finset.sum_sub_distrib, add_comm (1 : ℂ), one_div]
  ring

private noncomputable def gaussSeries (s : ℂ) : ℂ :=
  -Real.eulerMascheroniConstant + ∑' n, gaussTerm s n

private theorem hasSumLocallyUniformlyOn_gaussTerm :
    HasSumLocallyUniformlyOn (fun n s ↦ gaussTerm s n)
      (fun s ↦ ∑' n, gaussTerm s n) {s : ℂ | 0 < s.re} := by
  apply hasSumLocallyUniformlyOn_of_forall_compact (isOpen_re_gt 0)
  intro K hKU hK
  obtain ⟨R, hR⟩ := hK.exists_bound_of_continuousOn continuous_id.continuousOn
  let C := max (R + 1) 1
  have hC : 0 ≤ C := le_trans zero_le_one (le_max_right _ _)
  have hu : Summable (fun n : ℕ ↦ C / (n : ℝ) ^ 2) := by
    exact ((Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2 : ℕ))).mul_left C).congr
      (fun n ↦ by ring)
  apply HasSumUniformlyOn.of_norm_le_summable_eventually hu
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn s hs
  have hs0 : 0 < s.re := hKU hs
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hnum' : ‖s - 1‖ ≤ C := by
    calc ‖s - 1‖ ≤ ‖s‖ + 1 := by simpa using norm_sub_le s 1
         _ ≤ R + 1 := by simpa using add_le_add_right (hR s hs) 1
         _ ≤ C := le_max_left _ _
  have hden : (n : ℝ) ≤ ‖s + n‖ := by
    have h := Complex.re_le_norm (s + n)
    simp only [Complex.add_re, Complex.natCast_re] at h
    linarith
  have hsn : s + n ≠ 0 := norm_pos_iff.mp (by linarith)
  rw [gaussTerm_eq hsn, norm_div, norm_mul, norm_natCast_add_one]
  apply (div_le_div_iff₀ (by nlinarith : 0 < ((n : ℝ) + 1) * ‖s + n‖)
    (by positivity : 0 < (n : ℝ) ^ 2)).mpr
  have hprod : (n : ℝ) ^ 2 ≤ ((n : ℝ) + 1) * ‖s + n‖ := by
    nlinarith [mul_le_mul_of_nonneg_left hden (by positivity : 0 ≤ (n : ℝ) + 1)]
  nlinarith only [mul_le_mul_of_nonneg_right hnum' (sq_nonneg (n : ℝ)),
    mul_le_mul_of_nonneg_left hprod hC]

private theorem differentiableOn_gaussSeries :
    DifferentiableOn ℂ gaussSeries {s : ℂ | 0 < s.re} := by
  have hfinite (N : Finset ℕ) : DifferentiableOn ℂ
      (fun s ↦ ∑ n ∈ N, gaussTerm s n) {s : ℂ | 0 < s.re} := by
    apply DifferentiableOn.fun_sum
    intro n _
    unfold gaussTerm
    refine DifferentiableOn.sub (differentiableOn_const _) ?_
    refine DifferentiableOn.div (c := fun _ : ℂ ↦ (1 : ℂ)) (d := fun s : ℂ ↦ s + n)
      (differentiableOn_const _) (by fun_prop) ?_
    intro s hs
    simpa only [ne_eq, add_eq_zero_iff_eq_neg] using ne_neg_natCast_of_re_pos hs n
  exact (hasSumLocallyUniformlyOn_gaussTerm.differentiableOn
    (Eventually.of_forall hfinite) (isOpen_re_gt 0)).const_add _

private theorem tendsto_psi_error :
    Tendsto (fun x : ℝ ↦ digamma (x : ℂ) - Complex.log (x : ℂ)) atTop (𝓝 0) :=
  isBigO_digamma_ofReal_sub_log.trans_tendsto tendsto_inv_atTop_zero

private theorem tendsto_digamma_nat_shift_diff {x : ℝ} (hx : 0 < x) :
    Tendsto (fun N : ℕ ↦ digamma ((N : ℝ) + 1) - digamma ((N : ℝ) + x)) atTop (𝓝 0) := by
  have ht1 : Tendsto (fun N : ℕ ↦ (N : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have htx : Tendsto (fun N : ℕ ↦ (N : ℝ) + x) atTop atTop :=
    tendsto_atTop_add_const_right atTop x tendsto_natCast_atTop_atTop
  have hlogs : Tendsto (fun N : ℕ ↦ Complex.log (((N : ℝ) + 1) : ℂ) -
      Complex.log (((N : ℝ) + x) : ℂ)) atTop (𝓝 0) := by
    have hr : Tendsto (fun N : ℕ ↦ Real.log ((N : ℝ) + 1) - Real.log ((N : ℝ) + x)) atTop
        (𝓝 0) := by
      simpa only [Function.comp_def, sub_sub_sub_cancel_right, sub_zero] using
        ((Real.tendsto_log_comp_add_sub_log 1).sub
          (Real.tendsto_log_comp_add_sub_log x)).comp tendsto_natCast_atTop_atTop
    have h := continuous_ofReal.continuousAt.tendsto.comp hr
    convert h using 1
    ext N
    dsimp only [Function.comp_apply]
    rw [Complex.ofReal_sub, ofReal_log (by positivity), ofReal_log (by positivity)]
    simp only [Complex.ofReal_add, Complex.ofReal_one]
  have h := ((tendsto_psi_error.comp ht1).sub (tendsto_psi_error.comp htx)).add hlogs
  convert h using 1
  · ext N
    simp only [Function.comp_apply]
    push_cast
    ring
  · simp

private theorem digamma_ofReal_eq_gaussSeries {x : ℝ} (hx : 0 < x) :
    digamma (x : ℂ) = gaussSeries x := by
  have hs := ne_neg_natCast_of_re_pos (by simpa using hx : 0 < (x : ℂ).re)
  have ht : Tendsto (fun N : ℕ ↦ ∑ n ∈ Finset.range N, gaussTerm x n) atTop
      (𝓝 (digamma (x : ℂ) + Real.eulerMascheroniConstant)) := by
    have h := (tendsto_digamma_nat_shift_diff hx).const_add
      (digamma (x : ℂ) + Real.eulerMascheroniConstant)
    convert h using 1
    · ext N
      rw [gaussTerm_sum (x : ℂ) hs]
      push_cast
      rw [add_comm (x : ℂ) (N : ℂ)]
      ring
    · simp
  have he := tendsto_nhds_unique (summable_gaussTerm _).hasSum.tendsto_sum_nat ht
  dsimp [gaussSeries]
  rw [he]
  ring

private theorem analyticOnNhd_digamma_pos :
    AnalyticOnNhd ℂ digamma {s : ℂ | 0 < s.re} := by
  have hΓ : AnalyticOnNhd ℂ Complex.Gamma {s : ℂ | 0 < s.re} := by
    apply DifferentiableOn.analyticOnNhd _ (isOpen_re_gt 0)
    intro s hs
    exact (differentiableAt_Gamma s (ne_neg_natCast_of_re_pos hs)).differentiableWithinAt
  simpa only [digamma_def, logDeriv, Pi.div_def] using
    hΓ.deriv.div hΓ (fun s hs ↦ Gamma_ne_zero (ne_neg_natCast_of_re_pos hs))

private theorem digamma_eq_gaussSeries_of_re_pos {s : ℂ} (hs : 0 < s.re) :
    digamma s = gaussSeries s := by
  let v : ℕ → ℝ := fun n ↦ 1 + ((n : ℝ) + 1)⁻¹
  have hv : Tendsto v atTop (𝓝 1) := by
    have hn : Tendsto (fun n : ℕ ↦ (n : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
    simpa only [v, add_zero, Function.comp_def] using (tendsto_inv_atTop_zero.comp hn).const_add 1
  have hvc : Tendsto (fun n ↦ (v n : ℂ)) atTop (𝓝 (1 : ℂ)) := by
    simpa only [Function.comp_def, ofReal_one] using continuous_ofReal.continuousAt.tendsto.comp hv
  have hvp : Tendsto (fun n ↦ (v n : ℂ)) atTop (𝓝[≠] (1 : ℂ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨hvc, Eventually.of_forall fun n ↦ ?_⟩
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro h
    have hr := congrArg Complex.re h
    simp only [ofReal_re, one_re, v] at hr
    have hn : 0 < ((n : ℝ) + 1)⁻¹ := by positivity
    linarith
  have hfreq : ∃ᶠ z in 𝓝[≠] (1 : ℂ), digamma z = gaussSeries z := by
    apply hvp.frequently
    exact (Eventually.of_forall fun n ↦ digamma_ofReal_eq_gaussSeries
      (show 0 < v n by dsimp [v]; positivity)).frequently
  exact (analyticOnNhd_digamma_pos.eqOn_of_preconnected_of_frequently_eq
    (differentiableOn_gaussSeries.analyticOnNhd (isOpen_re_gt 0))
    (convex_halfSpace_re_gt 0).isPreconnected (by norm_num : (1 : ℂ) ∈ {s : ℂ | 0 < s.re})
    hfreq) hs

private theorem tendsto_inv_add_nat (s : ℂ) :
    Tendsto (fun N : ℕ ↦ (s + N)⁻¹) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp only [norm_inv]
  apply tendsto_inv_atTop_zero.comp
  apply tendsto_atTop_mono (fun n ↦ ?_)
    (tendsto_atTop_add_const_right atTop (-‖s‖) tendsto_natCast_atTop_atTop)
  simpa only [add_comm, Complex.norm_natCast, sub_eq_add_neg] using norm_sub_le_norm_add (n : ℂ) s

private theorem gaussSeries_add_one (s : ℂ) :
    gaussSeries (s + 1) = gaussSeries s + s⁻¹ := by
  have hsub := (summable_gaussTerm (s + 1)).sub (summable_gaussTerm s)
  have hfinite (N : ℕ) : ∑ n ∈ Finset.range N, (gaussTerm (s + 1) n - gaussTerm s n) =
      s⁻¹ - (s + N)⁻¹ := by
    have heq (n : ℕ) : gaussTerm (s + 1) n - gaussTerm s n =
        (s + n)⁻¹ - (s + (n + 1 : ℕ))⁻¹ := by
      simp only [gaussTerm, one_div, Nat.cast_add, Nat.cast_one]
      rw [add_right_comm s 1 (n : ℂ)]
      ring
    simp_rw [heq]
    simpa using Finset.sum_range_sub' (fun n : ℕ ↦ (s + n)⁻¹) N
  have ht : Tendsto (fun N : ℕ ↦ ∑ n ∈ Finset.range N,
      (gaussTerm (s + 1) n - gaussTerm s n)) atTop (𝓝 (s⁻¹)) := by
    simp_rw [hfinite]
    simpa using tendsto_const_nhds.sub (tendsto_inv_add_nat s)
  have hsum : ∑' n, (gaussTerm (s + 1) n - gaussTerm s n) = s⁻¹ :=
    tendsto_nhds_unique hsub.hasSum.tendsto_sum_nat ht
  rw [(summable_gaussTerm (s + 1)).tsum_sub (summable_gaussTerm s)] at hsum
  dsimp [gaussSeries]
  linear_combination hsum

private theorem gaussSeries_add_nat (s : ℂ) (N : ℕ) :
    gaussSeries (s + N) = gaussSeries s + ∑ n ∈ Finset.range N, (s + n)⁻¹ := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Nat.cast_add, Nat.cast_one, ← add_assoc, gaussSeries_add_one,
      ih, Finset.sum_range_succ]
    ring

private theorem digamma_eq_gaussSeries_regular {s : ℂ} (hs : ∀ m : ℕ, s ≠ -(m : ℂ)) :
    digamma s = gaussSeries s := by
  let N := ⌈1 - s.re⌉₊
  have hpos : 0 < (s + N).re := by
    simp only [add_re, natCast_re]
    have hN := Nat.le_ceil (1 - s.re)
    dsimp only [N]
    linarith
  have h := digamma_eq_gaussSeries_of_re_pos hpos
  rw [digamma_apply_add_nat hs N, gaussSeries_add_nat s N] at h
  exact add_right_cancel h

/-- The paired summands in Gauss' digamma series form an absolutely convergent complex series
for every `s`. At a pole `s = -m`, the single term `1 / (s + m)` is `0` by convention. -/
theorem summable_gaussSeries (s : ℂ) :
    Summable (fun n : ℕ ↦ 1 / ((n : ℂ) + 1) - 1 / (s + n)) := summable_gaussTerm s

/-- Gauss' paired reciprocal series equals complex digamma away from its poles. -/
theorem digamma_eq_gaussSeries {s : ℂ} (hs : ∀ m : ℕ, s ≠ -(m : ℂ)) :
    digamma s = -Real.eulerMascheroniConstant +
      ∑' n : ℕ, (1 / ((n : ℂ) + 1) - 1 / (s + n)) := by
  simpa only [gaussSeries, gaussTerm] using digamma_eq_gaussSeries_regular hs

end NTKB.Port
