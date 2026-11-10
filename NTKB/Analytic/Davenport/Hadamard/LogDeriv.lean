/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.Analysis.Calculus.LogDerivUniformlyOn
import NTKB.Analytic.Davenport.Hadamard.Factorization

/-!
# Logarithmic derivative of a canonical product of genus one

**Davenport, Ch. 12, p. 80.** Logarithmic differentiation of `e^{A+Bs} ∏ (1 - s/ρ) e^{s/ρ}` gives
`B + ∑_ρ (1/(s - ρ) + 1/ρ)`.

## Main results

* `NTKB.logDeriv_weierstrassFactorOne_div`: `E₁(z/a)'/E₁(z/a) = 1/(z - a) + 1/a`.
* `NTKB.logDeriv_canonicalProductOne`: the logarithmic derivative of the canonical product is the
  (absolutely convergent) sum of the logarithmic derivatives of the factors (Mathlib's
  `logDeriv_tprod_eq_tsum`).
* `NTKB.logDeriv_exp_mul_canonicalProductOne`: the same for `e^{A + Bz} P(z)`.
-/

open Filter Topology Metric Complex Set

namespace NTKB

variable {ι : Type*} {a : ι → ℂ}

lemma hasDerivAt_weierstrassFactorOne_div {α : ℂ} (z : ℂ) :
    HasDerivAt (fun w ↦ weierstrassFactorOne (w / α))
      (-(z / α ^ 2) * Complex.exp (z / α)) z := by
  have h1 : HasDerivAt (fun w ↦ w / α) (1 / α) z := by
    simpa using (hasDerivAt_id z).div_const α
  have h2 := ((hasDerivAt_const z (1 : ℂ)).sub h1).mul h1.cexp
  convert h2 using 1
  · ext w; simp [weierstrassFactorOne]
  · by_cases hα : α = 0
    · simp [hα]
    · simp only [Pi.sub_apply]; field_simp; ring

/-- `E₁(z/α)'/E₁(z/α) = 1/(z - α) + 1/α`. -/
lemma logDeriv_weierstrassFactorOne_div {α z : ℂ} (hα : α ≠ 0) (hz : z ≠ α) :
    logDeriv (fun w ↦ weierstrassFactorOne (w / α)) z = 1 / (z - α) + 1 / α := by
  rw [logDeriv_apply, (hasDerivAt_weierstrassFactorOne_div z).deriv]
  have hzα : z - α ≠ 0 := sub_ne_zero.mpr hz
  simp only [weierstrassFactorOne]
  have h1 : 1 - z / α ≠ 0 := by
    rw [sub_ne_zero, ne_comm, Ne, div_eq_one_iff_eq hα]; exact hz
  field_simp
  ring

/-- The series `∑ (1/(x - a i) + 1/a i)` converges absolutely. -/
lemma summable_inv_sub_add_inv (ha : Summable fun i ↦ ‖a i‖⁻¹ ^ 2) (ha0 : ∀ i, a i ≠ 0)
    {x : ℂ} (hx : ∀ i, a i ≠ x) : Summable fun i ↦ 1 / (x - a i) + 1 / a i := by
  refine Summable.of_norm_bounded_eventually (ha.mul_left (2 * ‖x‖)) ?_
  filter_upwards [eventually_mul_inv_norm_le_one ha (2 * ‖x‖)] with i hi
  have hai : 0 < ‖a i‖ := norm_pos_iff.mpr (ha0 i)
  have h2 : 2 * ‖x‖ ≤ ‖a i‖ := by
    rwa [mul_inv_le_iff₀ hai, one_mul] at hi
  have hxa : x - a i ≠ 0 := sub_ne_zero.mpr (hx i).symm
  have hai' : a i ≠ 0 := ha0 i
  have heq : 1 / (x - a i) + 1 / a i = x / (a i * (x - a i)) := by
    field_simp; ring
  have hlow : ‖a i‖ / 2 ≤ ‖x - a i‖ := by
    have := norm_sub_norm_le (a i) x
    rw [norm_sub_rev (a i) x] at this
    linarith
  rw [heq, norm_div, norm_mul, div_le_iff₀ (by positivity)]
  calc ‖x‖ = 2 * ‖x‖ * ‖a i‖⁻¹ ^ 2 * (‖a i‖ * (‖a i‖ / 2)) := by
        field_simp
    _ ≤ 2 * ‖x‖ * ‖a i‖⁻¹ ^ 2 * (‖a i‖ * ‖x - a i‖) := by gcongr

/-- **Logarithmic derivative of the canonical product** (Davenport, Ch. 12, p. 80):
`P'(x)/P(x) = ∑ (1/(x - a i) + 1/a i)` off the zeros, the sum converging absolutely. -/
theorem logDeriv_canonicalProductOne (ha : Summable fun i ↦ ‖a i‖⁻¹ ^ 2) (ha0 : ∀ i, a i ≠ 0)
    {x : ℂ} (hx : ∀ i, a i ≠ x) :
    logDeriv (canonicalProductOne a) x = ∑' i, (1 / (x - a i) + 1 / a i) := by
  have hsum := summable_inv_sub_add_inv ha ha0 hx
  have hm : Summable fun i ↦ logDeriv (fun w ↦ weierstrassFactorOne (w / a i)) x :=
    hsum.congr fun i ↦ (logDeriv_weierstrassFactorOne_div (ha0 i) (hx i).symm).symm
  have hne : ∀ i, weierstrassFactorOne (x / a i) ≠ 0 := by
    intro i h
    rw [weierstrassFactorOne_eq_zero_iff, div_eq_one_iff_eq (ha0 i)] at h
    exact hx i h.symm
  have h := logDeriv_tprod_eq_tsum (s := univ) isOpen_univ (mem_univ x)
    (f := fun i w ↦ weierstrassFactorOne (w / a i)) hne
    (fun i ↦ (differentiable_weierstrassFactorOne.comp
      (differentiable_id.div_const (a i))).differentiableOn) hm
    (hasProdLocallyUniformlyOn_canonicalProductOne ha).multipliableLocallyUniformlyOn
    (canonicalProductOne_ne_zero ha hx)
  have hfun : (fun z ↦ ∏' i, weierstrassFactorOne (z / a i)) = canonicalProductOne a := rfl
  rw [hfun] at h
  rw [h]
  exact tsum_congr fun i ↦ logDeriv_weierstrassFactorOne_div (ha0 i) (hx i).symm

/-- Logarithmic derivative of `e^{A + Bz} P(z)`: `B + ∑ (1/(x - a i) + 1/a i)`. -/
theorem logDeriv_exp_mul_canonicalProductOne (ha : Summable fun i ↦ ‖a i‖⁻¹ ^ 2)
    (ha0 : ∀ i, a i ≠ 0) (A B : ℂ) {x : ℂ} (hx : ∀ i, a i ≠ x) :
    logDeriv (fun z ↦ Complex.exp (A + B * z) * canonicalProductOne a z) x =
      B + ∑' i, (1 / (x - a i) + 1 / a i) := by
  have hE : HasDerivAt (fun z ↦ Complex.exp (A + B * z)) (Complex.exp (A + B * x) * B) x := by
    have : HasDerivAt (fun z ↦ A + B * z) B x := by
      simpa using ((hasDerivAt_id x).const_mul B).const_add A
    exact this.cexp
  have hP := differentiable_canonicalProductOne ha
  have hfun : (fun z ↦ Complex.exp (A + B * z) * canonicalProductOne a z) =
      (fun z ↦ Complex.exp (A + B * z)) * canonicalProductOne a := rfl
  rw [hfun, logDeriv_mul (f := fun z ↦ Complex.exp (A + B * z)) (g := canonicalProductOne a) x
    (Complex.exp_ne_zero _) (canonicalProductOne_ne_zero ha hx) hE.differentiableAt
    (hP x), logDeriv_canonicalProductOne ha ha0 hx, logDeriv_apply, hE.deriv]
  field_simp [Complex.exp_ne_zero]

end NTKB
