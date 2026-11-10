/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Apostol.Primes.Shapiro
import Mathlib.NumberTheory.AbelSummation
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Function.Floor

/-!
# `∑_{p ≤ x} 1/p = log log x + A + O(1/log x)` (Apostol, Theorem 4.12)

Apostol's proof: Abel summation (Theorem 4.2) with `a(n) = log p / p` on primes and
`f(t) = 1/log t`, fed with Theorem 4.10 (`∑_{p ≤ x} log p/p = log x + R(x)`, `R = O(1)`):
`∑_{p ≤ x} 1/p = 1 + R(x)/log x + log log x - log log 2 + ∫_2^x R(t)/(t log² t) dt`,
and the integral converges with tail `∫_x^∞ = O(1/log x)`.
(Also in PrimeNumberTheoremAnd, `Mertens.sum_prime_div_eq_log_log`; re-derived here by Apostol's
route, since NTKB depends on Mathlib only.)
-/

open Finset Real MeasureTheory Filter Topology

namespace NTKB.Apostol

/-- The coefficients `log p / p` on primes, `0` elsewhere. -/
noncomputable def primeLogCoeff (k : ℕ) : ℝ := if k.Prime then Real.log k / k else 0

/-- `∑_{p ≤ t} log p / p`. -/
noncomputable def primeLogSum (t : ℝ) : ℝ := ∑ k ∈ Icc 0 ⌊t⌋₊, primeLogCoeff k

lemma sum_Icc_eq_sum_filter_prime (n : ℕ) (F : ℕ → ℝ) :
    ∑ k ∈ Icc 0 n, (if k.Prime then F k else 0) = ∑ p ∈ Ioc 0 n with p.Prime, F p := by
  rw [Finset.sum_filter, Icc_eq_cons_Ioc (Nat.zero_le _), sum_cons]
  simp [Nat.not_prime_zero]

lemma exists_abs_primeLogSum_sub_le : ∃ C, 0 ≤ C ∧ ∀ t : ℝ, 1 ≤ t →
    |primeLogSum t - Real.log t| ≤ C := by
  obtain ⟨C, hC⟩ := apostol_thm_4_10.1
  refine ⟨C, (abs_nonneg _).trans (hC 1 le_rfl), fun t ht => ?_⟩
  have := hC t ht
  rwa [primeLogSum, show ∑ k ∈ Icc 0 ⌊t⌋₊, primeLogCoeff k =
      ∑ k ∈ Icc 0 ⌊t⌋₊, (if k.Prime then Real.log k / k else 0) from rfl,
    sum_Icc_eq_sum_filter_prime]

lemma measurable_primeLogSum : Measurable primeLogSum :=
  (measurable_from_nat (f := fun n => ∑ k ∈ Icc 0 n, primeLogCoeff k)).comp Nat.measurable_floor

/-- `-C/log t` has derivative `C/(t log² t)` for `t > 1`. -/
lemma hasDerivAt_neg_div_log (C : ℝ) {t : ℝ} (ht : 1 < t) :
    HasDerivAt (fun y => -C / Real.log y) (C / (t * Real.log t ^ 2)) t := by
  have hlog : Real.log t ≠ 0 := (Real.log_pos ht).ne'
  have ht0 : t ≠ 0 := by linarith
  have := ((Real.hasDerivAt_log ht0).inv hlog).const_mul (-C)
  convert this using 1
  · ext y; simp [div_eq_mul_inv]
  · field_simp

lemma tendsto_neg_div_log (C : ℝ) : Tendsto (fun y => -C / Real.log y) atTop (𝓝 0) :=
  tendsto_const_nhds.div_atTop Real.tendsto_log_atTop

lemma integrableOn_div_mul_log_sq (C : ℝ) {a : ℝ} (ha : 1 < a) (hC : 0 ≤ C) :
    IntegrableOn (fun t => C / (t * Real.log t ^ 2)) (Set.Ioi a) :=
  integrableOn_Ioi_deriv_of_nonneg' (fun t ht => hasDerivAt_neg_div_log C (ha.trans_le ht))
    (fun t ht => by
      have : 0 < t := by linarith [ht.out]
      positivity) (tendsto_neg_div_log C)

lemma integral_div_mul_log_sq (C : ℝ) {a : ℝ} (ha : 1 < a) (hC : 0 ≤ C) :
    ∫ t in Set.Ioi a, C / (t * Real.log t ^ 2) = C / Real.log a := by
  rw [integral_Ioi_of_hasDerivAt_of_nonneg' (fun t ht => hasDerivAt_neg_div_log C (ha.trans_le ht))
    (fun t ht => by
      have : 0 < t := by linarith [ht.out]
      positivity) (tendsto_neg_div_log C)]
  ring

/-- **Theorem 4.12**: there is a constant `A` such that
`∑_{p ≤ x} 1/p = log log x + A + O(1/log x)` for `x ≥ 2`. -/
@[kb "apostol1976" "Thm 4.12, p. 90"]
theorem apostol_thm_4_12 : ∃ A C : ℝ, ∀ x : ℝ, 2 ≤ x →
    |∑ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, (1 : ℝ) / p - Real.log (Real.log x) - A| ≤
      C / Real.log x := by
  obtain ⟨C₀, hC₀, hR⟩ := exists_abs_primeLogSum_sub_le
  set R : ℝ → ℝ := fun t => primeLogSum t - Real.log t with hRdef
  set g : ℝ → ℝ := fun t => R t / (t * Real.log t ^ 2) with hgdef
  have hgmeas : AEStronglyMeasurable g := by
    refine (Measurable.div ?_ ?_).aestronglyMeasurable
    · exact measurable_primeLogSum.sub Real.measurable_log
    · exact measurable_id.mul (Real.measurable_log.pow_const 2)
  have hgint : ∀ a, 1 < a → IntegrableOn g (Set.Ioi a) := fun a ha => by
    refine Integrable.mono' (integrableOn_div_mul_log_sq C₀ ha hC₀) hgmeas.restrict ?_
    refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
    have ht1 : 1 < t := ha.trans ht
    have hpos : 0 < t * Real.log t ^ 2 := by
      have := Real.log_pos ht1; positivity
    rw [Real.norm_eq_abs, hgdef, abs_div, abs_of_pos hpos]
    exact div_le_div_of_nonneg_right (hR t ht1.le) hpos.le
  set I := ∫ t in Set.Ioi 2, g t
  refine ⟨1 - Real.log (Real.log 2) + I, 2 * C₀, fun x hx => ?_⟩
  have hx1 : 1 < x := by linarith
  have hlogx : 0 < Real.log x := Real.log_pos hx1
  have hlog : ∀ t : ℝ, 1 < t → Real.log t ≠ 0 := fun t ht => (Real.log_pos ht).ne'
  have hderivf : ∀ t : ℝ, 1 < t → HasDerivAt (fun t => (Real.log t)⁻¹)
      (-(t⁻¹) / Real.log t ^ 2) t := fun t ht =>
    (Real.hasDerivAt_log (by linarith)).inv (hlog t ht)
  have hcont1 : ContinuousOn (fun t : ℝ => -(t⁻¹) / Real.log t ^ 2) (Set.Icc 2 x) := by
    refine ContinuousOn.div ?_ ?_ fun t ht => pow_ne_zero 2 (hlog t (by linarith [ht.1]))
    · exact (continuousOn_inv₀.mono fun t ht => by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; linarith [ht.1]).neg
    · exact (Real.continuousOn_log.mono fun t ht => by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; linarith [ht.1]).pow 2
  have hcont2 : ContinuousOn (fun t : ℝ => t⁻¹ / Real.log t) (Set.Icc 2 x) := by
    refine ContinuousOn.div ?_ ?_ fun t ht => hlog t (by linarith [ht.1])
    · exact continuousOn_inv₀.mono fun t ht => by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; linarith [ht.1]
    · exact Real.continuousOn_log.mono fun t ht => by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; linarith [ht.1]
  have hint : IntegrableOn (deriv fun t => (Real.log t)⁻¹) (Set.Icc 2 x) := by
    refine (hcont1.integrableOn_Icc).congr_fun (fun t ht => ?_) measurableSet_Icc
    exact ((hderivf t (by linarith [ht.1])).deriv).symm
  have habel := sum_mul_eq_sub_integral_mul₁ (𝕜 := ℝ) primeLogCoeff (f := fun t => (Real.log t)⁻¹)
    (by simp [primeLogCoeff, Nat.not_prime_zero]) (by simp [primeLogCoeff, Nat.not_prime_one]) x
    (fun t ht => (hderivf t (by linarith [ht.1])).differentiableAt) hint
  -- the left side is `∑_{p ≤ x} 1/p`
  have hlhs : ∑ k ∈ Icc 0 ⌊x⌋₊, (Real.log k)⁻¹ * primeLogCoeff k =
      ∑ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, (1 : ℝ) / p := by
    rw [← sum_Icc_eq_sum_filter_prime]
    refine sum_congr rfl fun k _ => ?_
    simp only [primeLogCoeff]
    split_ifs with hk
    · have : Real.log k ≠ 0 := hlog k (by exact_mod_cast hk.one_lt)
      field_simp
    · simp
  -- the integral
  have hI1 : IntegrableOn (fun t : ℝ => t⁻¹ / Real.log t) (Set.Ioc 2 x) :=
    hcont2.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have hI2 : IntegrableOn g (Set.Ioc 2 x) := (hgint 2 one_lt_two).mono_set Set.Ioc_subset_Ioi_self
  have hintegral : ∫ t in Set.Ioc 2 x, deriv (fun t => (Real.log t)⁻¹) t *
      ∑ k ∈ Icc 0 ⌊t⌋₊, primeLogCoeff k =
      -((∫ t in Set.Ioc 2 x, t⁻¹ / Real.log t) + ∫ t in Set.Ioc 2 x, g t) := by
    rw [← integral_add hI1 hI2, ← integral_neg]
    refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
    have ht1 : 1 < t := by linarith [ht.1]
    have hl := hlog t ht1
    have ht0 : t ≠ 0 := by linarith
    rw [(hderivf t ht1).deriv]
    simp only [hgdef, hRdef, primeLogSum]
    field_simp
    ring
  have hloglog : ∫ t in Set.Ioc 2 x, t⁻¹ / Real.log t =
      Real.log (Real.log x) - Real.log (Real.log 2) := by
    rw [← intervalIntegral.integral_of_le hx]
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t => Real.log (Real.log t))
      (fun t ht => ?_)
      (hcont2.intervalIntegrable_of_Icc hx)
    rw [Set.uIcc_of_le hx] at ht
    exact (Real.hasDerivAt_log (by linarith [ht.1])).log (hlog t (by linarith [ht.1]))
  have hsplit : ∫ t in Set.Ioc 2 x, g t = I - ∫ t in Set.Ioi x, g t := by
    have := setIntegral_union (Set.Ioc_disjoint_Ioi_same (a := (2 : ℝ)) (b := x)) measurableSet_Ioi
      hI2 (hgint x hx1)
    rw [Set.Ioc_union_Ioi_eq_Ioi hx] at this
    simp only [I, this]
    ring
  have htail : |∫ t in Set.Ioi x, g t| ≤ C₀ / Real.log x := by
    rw [← integral_div_mul_log_sq C₀ hx1 hC₀, ← Real.norm_eq_abs]
    refine norm_integral_le_of_norm_le (integrableOn_div_mul_log_sq C₀ hx1 hC₀) ?_
    refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
    have ht1 : 1 < t := hx1.trans ht
    have hpos : 0 < t * Real.log t ^ 2 := by
      have := Real.log_pos ht1; positivity
    rw [Real.norm_eq_abs, hgdef, abs_div, abs_of_pos hpos]
    exact div_le_div_of_nonneg_right (hR t ht1.le) hpos.le
  have hRx : |R x / Real.log x| ≤ C₀ / Real.log x := by
    rw [abs_div, abs_of_pos hlogx]
    exact div_le_div_of_nonneg_right (hR x hx1.le) hlogx.le
  rw [hlhs, hintegral, hloglog, hsplit] at habel
  have hS : ∑ k ∈ Icc 0 ⌊x⌋₊, primeLogCoeff k = Real.log x + R x := by simp [hRdef, primeLogSum]
  rw [habel, hS]
  have key : (Real.log x)⁻¹ * (Real.log x + R x) - -(Real.log (Real.log x) - Real.log (Real.log 2) +
      (I - ∫ t in Set.Ioi x, g t)) - Real.log (Real.log x) - (1 - Real.log (Real.log 2) + I) =
      R x / Real.log x - ∫ t in Set.Ioi x, g t := by
    field_simp
    ring
  rw [key]
  calc |R x / Real.log x - ∫ t in Set.Ioi x, g t|
      ≤ |R x / Real.log x| + |∫ t in Set.Ioi x, g t| := abs_sub _ _
    _ ≤ C₀ / Real.log x + C₀ / Real.log x := add_le_add hRx htail
    _ = 2 * C₀ / Real.log x := by ring

end NTKB.Apostol
