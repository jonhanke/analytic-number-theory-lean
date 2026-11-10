/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Davenport.Hadamard.Xi

/-!
# The constant `B` as a sum over the zeros of `ζ` (Davenport, Chapter 12, (11))

**Davenport, Ch. 12, p. 81–82, (11).** The series `∑ 1/ρ` converges when `ρ` and `ρ̄` are grouped,
and `B = -∑_ρ 1/ρ = -2 ∑_{γ > 0} β/(β² + γ²)`.

We prove the absolutely convergent form `B = -∑_ρ Re(1/ρ)` (with `Re(1/ρ) = β/|ρ|² ≥ 0`;
grouping `ρ` with `ρ̄` turns `∑ 1/ρ` into `∑ Re(1/ρ)`). As in Davenport, the proof combines
the logarithmic derivative of the product at `s = 0` and `s = 1` with the functional equation and
the symmetry `ρ ↦ 1 - ρ` of the zeros (here an explicit involution of `ZeroIndex riemannXi`).
-/

open Complex Filter Topology
open scoped Real

namespace NTKB

/-- `ξ` vanishes to the same order at `z` and at `1 - z`. -/
lemma analyticOrderNatAt_riemannXi_one_sub (z : ℂ) :
    analyticOrderNatAt riemannXi (1 - z) = analyticOrderNatAt riemannXi z := by
  have hcomp : riemannXi ∘ (fun w ↦ 1 - w) = riemannXi := funext fun w ↦ riemannXi_one_sub w
  have hg : AnalyticAt ℂ (fun w : ℂ ↦ 1 - w) z := analyticAt_const.sub analyticAt_id
  have hg' : deriv (fun w : ℂ ↦ 1 - w) z ≠ 0 := by
    rw [deriv_const_sub]; simp
  have := analyticOrderAt_comp_of_deriv_ne_zero (f := riemannXi) hg hg'
  rw [hcomp] at this
  simp only [analyticOrderNatAt, this]

/-- The involution `ρ ↦ 1 - ρ` of the zeros of `ξ` (with multiplicity). -/
noncomputable def riemannXiZeroReflect : ZeroIndex riemannXi ≃ ZeroIndex riemannXi :=
  Equiv.sigmaCongr (Equiv.subLeft (1 : ℂ)) fun z ↦
    finCongr (analyticOrderNatAt_riemannXi_one_sub z).symm

@[simp] lemma riemannXiZeroReflect_val (ρ : ZeroIndex riemannXi) :
    (riemannXiZeroReflect ρ).val = 1 - ρ.val := rfl

/-- `0 ≤ Re(1/ρ) ≤ |ρ|⁻²` for a zero `ρ` in the critical strip. -/
lemma re_inv_le {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    0 ≤ (1 / ρ).re ∧ (1 / ρ).re ≤ ‖ρ‖⁻¹ ^ 2 := by
  have hρ : ρ ≠ 0 := by rintro rfl; simp at h0
  have hns : 0 < Complex.normSq ρ := Complex.normSq_pos.mpr hρ
  rw [one_div, Complex.inv_re]
  refine ⟨div_nonneg h0.le hns.le, ?_⟩
  rw [inv_pow, ← Complex.normSq_eq_norm_sq, div_le_iff₀ hns, inv_mul_cancel₀ hns.ne']
  exact h1.le

/-- **Davenport, Ch. 12, (11) (row 12-11)**: in `ξ(s) = e^{A+Bs} ∏ (1 - s/ρ) e^{s/ρ}`,
`B = -∑_ρ Re(1/ρ)` (absolutely convergent; this is `-∑ 1/ρ` with `ρ` and `ρ̄` grouped). -/
@[kb "davenport1980" "Ch 12, p. 82"]
theorem Davenport.riemannXi_B_eq_neg_tsum {A B : ℂ}
    (h : ∀ s, riemannXi s = Complex.exp (A + B * s) *
      ∏' ρ : ZeroIndex riemannXi, (1 - s / ρ.val) * Complex.exp (s / ρ.val)) :
    B = ((-∑' ρ : ZeroIndex riemannXi, (1 / ρ.val).re : ℝ) : ℂ) := by
  obtain ⟨ha, ha0⟩ := summable_riemannXi_zeros
  have hstrip := (Davenport.riemannXi_zeros).2.1
  -- the logarithmic derivative at `0` and `1`
  have hl0 := Davenport.logDeriv_riemannXi h (s := 0) (by simp)
  simp only [zero_sub, one_div, inv_neg, neg_add_cancel, tsum_zero, add_zero] at hl0
  have hl1 := Davenport.logDeriv_riemannXi h (s := 1) (by simp)
  -- the functional equation: `ξ'(1) = -ξ'(0)`
  have hd0 : HasDerivAt riemannXi (deriv riemannXi 0) 0 :=
    (differentiable_riemannXi 0).hasDerivAt
  have hcomp : HasDerivAt (fun w ↦ riemannXi (1 - w)) (deriv riemannXi 0 * (-1)) 1 := by
    have hin : HasDerivAt (fun w : ℂ ↦ 1 - w) (-1) 1 := by
      simpa using (hasDerivAt_id (1 : ℂ)).const_sub 1
    have : HasDerivAt riemannXi (deriv riemannXi 0) ((fun w : ℂ ↦ 1 - w) 1) := by
      simpa using hd0
    exact this.comp 1 hin
  have hfun : (fun w ↦ riemannXi (1 - w)) = riemannXi := funext riemannXi_one_sub
  rw [hfun] at hcomp
  have hFE : logDeriv riemannXi 1 = -logDeriv riemannXi 0 := by
    rw [logDeriv_apply, logDeriv_apply, hcomp.deriv, riemannXi_zero, riemannXi_one]
    ring
  rw [hl0, hl1] at hFE
  -- `2B = -T` with `T = ∑ (1/(1 - ρ) + 1/ρ)`
  set T := ∑' ρ : ZeroIndex riemannXi, (1 / (1 - ρ.val) + 1 / ρ.val)
  have hT : T = -2 * B := by linear_combination hFE
  -- real parts
  have hR : Summable fun ρ : ZeroIndex riemannXi ↦ (1 / ρ.val).re :=
    ha.of_nonneg_of_le (fun ρ ↦ (re_inv_le (hstrip ρ).2.1 (hstrip ρ).2.2).1)
      fun ρ ↦ (re_inv_le (hstrip ρ).2.1 (hstrip ρ).2.2).2
  have hR' : Summable fun ρ : ZeroIndex riemannXi ↦ (1 / (1 - ρ.val)).re := by
    have := hR.comp_injective riemannXiZeroReflect.injective
    simpa [Function.comp_def] using this
  have hsumT : Summable fun ρ : ZeroIndex riemannXi ↦ 1 / (1 - ρ.val) + 1 / ρ.val :=
    summable_inv_sub_add_inv ha ha0 fun ρ h1 ↦ by
      have := (hstrip ρ).2.2; rw [h1] at this; simp at this
  have hTre : T.re = 2 * ∑' ρ : ZeroIndex riemannXi, (1 / ρ.val).re := by
    rw [Complex.re_tsum hsumT]
    simp only [Complex.add_re]
    rw [hR'.tsum_add hR]
    have heq : ∑' ρ : ZeroIndex riemannXi, (1 / (1 - ρ.val)).re =
        ∑' ρ : ZeroIndex riemannXi, (1 / ρ.val).re := by
      have := riemannXiZeroReflect.tsum_eq (fun ρ : ZeroIndex riemannXi ↦ (1 / ρ.val).re)
      simpa using this
    rw [heq]; ring
  -- `B` is real
  have hBval := (Davenport.riemannXi_hadamard_constants h).2
  have hBim : B.im = 0 := by
    rw [hBval]
    have : Complex.log (4 * π) = ((Real.log (4 * π) : ℝ) : ℂ) := by
      rw [Complex.ofReal_log (by positivity)]; push_cast; ring_nf
    rw [this]
    simp
  apply Complex.ext
  · have := congrArg Complex.re hT
    rw [hTre] at this
    simp only [Complex.mul_re, Complex.neg_re, Complex.re_ofNat, Complex.neg_im,
      Complex.im_ofNat, hBim] at this
    simp only [Complex.ofReal_re]
    linarith
  · simp [hBim]

end NTKB
