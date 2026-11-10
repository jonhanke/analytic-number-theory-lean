/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import NTKB.Analytic.Davenport.Hadamard.ZeroCount

/-!
# Jensen's formula with the counting function (Davenport, Chapter 11, p. 75)

**Davenport, p. 75.** An alternative expression for the right side `log(Rⁿ/(|z₁| ⋯ |zₙ|))` of
Jensen's formula is `∫₀ᴿ n(r)/r dr`, where `n(r)` counts the zeros in `|z| < r`:
the integral is `log(r₂/r₁) + 2 log(r₃/r₂) + ⋯ + n log(R/rₙ)`.

Mathlib states Jensen's formula with the divisor (`AnalyticOnNhd.circleAverage_log_norm`); this
file proves the identity `∫₀ᴿ n(r)/r dr = ∑_{|z_n| < R} log(R/|z_n|)`.
-/

open MeasureTheory Set

namespace NTKB

lemma intervalIntegrable_ite_inv {a R : ℝ} (ha : 0 < a) (haR : a < R) :
    IntervalIntegrable (fun r : ℝ ↦ if a < r then r⁻¹ else 0) volume 0 R := by
  have h1 : IntervalIntegrable (fun r : ℝ ↦ if a < r then r⁻¹ else 0) volume 0 a := by
    refine (intervalIntegrable_iff_integrableOn_Ioc_of_le ha.le).mpr ?_
    refine (integrableOn_zero).congr_fun (fun r hr ↦ ?_) measurableSet_Ioc
    simp [not_lt.mpr hr.2]
  have h2 : IntervalIntegrable (fun r : ℝ ↦ if a < r then r⁻¹ else 0) volume a R := by
    refine (intervalIntegrable_iff_integrableOn_Ioc_of_le haR.le).mpr ?_
    have hc : IntegrableOn (fun r : ℝ ↦ r⁻¹) (Icc a R) :=
      (continuousOn_inv₀.mono fun x (hx : x ∈ Icc a R) ↦
        (show x ∈ ({0} : Set ℝ)ᶜ by simp; exact ne_of_gt (ha.trans_le hx.1))).integrableOn_Icc
    exact (hc.mono_set Ioc_subset_Icc_self).congr_fun (fun r hr ↦ by simp [hr.1]) measurableSet_Ioc
  exact h1.trans h2

/-- `∫₀ᴿ 1[a < r] / r dr = log(R/a)` for `0 < a < R`. -/
lemma integral_ite_inv {a R : ℝ} (ha : 0 < a) (haR : a < R) :
    ∫ r in (0 : ℝ)..R, (if a < r then r⁻¹ else 0) = Real.log (R / a) := by
  have h1 : IntervalIntegrable (fun r : ℝ ↦ if a < r then r⁻¹ else 0) volume 0 a := by
    refine (intervalIntegrable_iff_integrableOn_Ioc_of_le ha.le).mpr ?_
    refine (integrableOn_zero).congr_fun (fun r hr ↦ ?_) measurableSet_Ioc
    simp [not_lt.mpr hr.2]
  have h2 : IntervalIntegrable (fun r : ℝ ↦ if a < r then r⁻¹ else 0) volume a R := by
    refine (intervalIntegrable_iff_integrableOn_Ioc_of_le haR.le).mpr ?_
    have hc : IntegrableOn (fun r : ℝ ↦ r⁻¹) (Icc a R) :=
      (continuousOn_inv₀.mono fun x (hx : x ∈ Icc a R) ↦
        (show x ∈ ({0} : Set ℝ)ᶜ by simp; exact ne_of_gt (ha.trans_le hx.1))).integrableOn_Icc
    exact (hc.mono_set Ioc_subset_Icc_self).congr_fun (fun r hr ↦ by simp [hr.1]) measurableSet_Ioc
  rw [← intervalIntegral.integral_add_adjacent_intervals h1 h2]
  have e1 : ∫ r in (0 : ℝ)..a, (if a < r then r⁻¹ else 0) = 0 := by
    rw [intervalIntegral.integral_of_le ha.le]
    refine (setIntegral_congr_fun measurableSet_Ioc (fun r hr ↦ ?_)).trans (integral_zero _ _)
    simp [not_lt.mpr hr.2]
  have e2 : ∫ r in a..R, (if a < r then r⁻¹ else 0) = ∫ r in a..R, r⁻¹ := by
    rw [intervalIntegral.integral_of_le haR.le, intervalIntegral.integral_of_le haR.le]
    exact setIntegral_congr_fun measurableSet_Ioc (fun r hr ↦ by simp [hr.1])
  rw [e1, e2, integral_inv_of_pos ha (ha.trans haR), zero_add]

/-- **Davenport, Ch. 11, p. 75 (row 11-5)**: for an entire `f` with `f(0) ≠ 0` and `R > 0`,
`∫₀ᴿ n(r)/r dr = ∑_{|z_n| < R} log(R/|z_n|) = log(Rⁿ/(|z₁| ⋯ |zₙ|))`, the right side of Jensen's
formula. -/
@[kb "davenport1980" "Ch 11, p. 75"]
theorem Davenport.integral_zeroCount_div {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hf0 : f 0 ≠ 0)
    {R : ℝ} (hR : 0 < R) :
    ∫ r in (0 : ℝ)..R, (zeroCount f r : ℝ) / r =
      ∑ᶠ i ∈ {i : ZeroIndex f | ‖i.val‖ < R}, Real.log (R / ‖i.val‖) := by
  classical
  have hfin : {i : ZeroIndex f | ‖i.val‖ < R}.Finite := by
    have := finite_zeroIndex_ball hf R
    exact Set.toFinite _
  obtain ⟨r₀, hr₀, hr₀le⟩ := exists_pos_le_norm_val hf hf0
  set S := hfin.toFinset
  have hS : ∀ i, i ∈ S ↔ ‖i.val‖ < R := fun i ↦ by simp [S]
  -- `n(r) / r` as a finite sum on `[0, R]`
  have hcount : Set.EqOn (fun r : ℝ ↦ (zeroCount f r : ℝ) / r)
      (fun r ↦ ∑ i ∈ S, (if ‖i.val‖ < r then r⁻¹ else 0)) (uIcc 0 R) := by
    intro r hr
    rw [uIcc_of_le hR.le] at hr
    have hcard : zeroCount f r = (S.filter fun i ↦ ‖i.val‖ < r).card := by
      rw [zeroCount, ← Nat.card_eq_finsetCard]
      refine Nat.card_congr (Equiv.subtypeEquivRight fun i ↦ ?_)
      simp only [Finset.mem_filter, hS]
      constructor
      · intro h; exact ⟨lt_of_lt_of_le h hr.2, h⟩
      · intro h; exact h.2
    simp only [hcard, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]
  rw [intervalIntegral.integral_congr hcount, intervalIntegral.integral_finsetSum fun i hi ↦
    intervalIntegrable_ite_inv (hr₀.trans_le (hr₀le i)) ((hS i).mp hi)]
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
  exact Finset.sum_congr rfl fun i hi ↦
    integral_ite_inv (hr₀.trans_le (hr₀le i)) ((hS i).mp hi)

end NTKB
