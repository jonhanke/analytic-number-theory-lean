/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Davenport.Zeros.ZeroCountVertical

/-!
# The horizontal side for `N(T)`: `S(T) = O(log T)`

**Davenport, Ch. 15, pp. 98-99 (row 15-5).** For `T ≥ 2` not an ordinate,
`|∫_{1/2}^2 Im ξ'/ξ(x + iT) dx| ≤ A log T` (`Davenport.abs_integral_im_logDeriv_riemannXi_le`).
This integral is the change of argument of `ξ` along `2 + iT → 1/2 + iT`, i.e. (up to `O(1)`)
`π S(T)`. As in Davenport, by 15-9 `ξ'/ξ(s) = ∑_{|γ - T| < 1} 1/(s - ρ) + O(log T)` on the
segment; each term changes the argument by at most `π`, and there are `O(log T)` terms (15-7).
-/

open Filter Topology Complex Set MeasureTheory
open scoped Real Interval

namespace NTKB

/-- `|∫_a^b Im 1/(x + iT - ρ) dx| ≤ π` for `Im ρ ≠ T`. -/
lemma abs_integral_im_inv_sub_le {ρ : ℂ} {T : ℝ} (h : ρ.im ≠ T) (a b : ℝ) :
    |∫ x in a..b, (1 / ((x : ℂ) + T * I - ρ)).im| ≤ π := by
  have hc : T - ρ.im ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
  set F : ℝ → ℂ := fun u ↦ 1 / ((u : ℂ) + ((T - ρ.im : ℝ) : ℂ) * I) with hF
  have hFc : Continuous F := by
    have hg : Continuous fun u : ℝ ↦ (u : ℂ) + ((T - ρ.im : ℝ) : ℂ) * I := by fun_prop
    have h0 : ∀ u : ℝ, (u : ℂ) + ((T - ρ.im : ℝ) : ℂ) * I ≠ 0 := fun u h' ↦
      hc (by simpa using congrArg Complex.im h')
    exact (hg.inv₀ h0).congr fun u ↦ (one_div _).symm
  have e : ∀ x : ℝ, 1 / ((x : ℂ) + T * I - ρ) = F (x - ρ.re) := by
    intro x
    simp only [hF]
    congr 1
    apply Complex.ext <;> simp
  have h1 : ∫ x in a..b, (1 / ((x : ℂ) + T * I - ρ)).im =
      (∫ u in (a - ρ.re)..(b - ρ.re), F u).im := by
    simp only [e]
    have h1a : ∫ x in a..b, (F (x - ρ.re)).im = ∫ u in (a - ρ.re)..(b - ρ.re), (F u).im :=
      intervalIntegral.integral_comp_sub_right (fun u ↦ (F u).im) ρ.re
    rw [h1a, ← Complex.imCLM_apply, ← ContinuousLinearMap.intervalIntegral_comp_comm]
    · rfl
    · exact hFc.intervalIntegrable _ _
  rw [h1, hF, integral_inv_add_mul_I hc]
  simp only [sub_im, ofReal_im, mul_im, I_re, I_im, ofReal_re, mul_zero, zero_add,
    zero_sub, abs_neg]
  have := Real.arctan_lt_pi_div_two ((b - ρ.re) / (T - ρ.im))
  have := Real.neg_pi_div_two_lt_arctan ((b - ρ.re) / (T - ρ.im))
  have := Real.arctan_lt_pi_div_two ((a - ρ.re) / (T - ρ.im))
  have := Real.neg_pi_div_two_lt_arctan ((a - ρ.re) / (T - ρ.im))
  rw [abs_le]; constructor <;> linarith

lemma norm_add_sub_add_le (a b c d : ℂ) : ‖a + b - c + d‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ := by
  have h1 := norm_add_le (a + b - c) d
  have h2 := norm_sub_le (a + b) c
  have h3 := norm_add_le a b
  linarith

/-- On the segment, `ζ ≠ 0` when `ξ ≠ 0`. -/
lemma riemannZeta_ne_zero_of_riemannXi_ne_zero {s : ℂ} (hs : riemannXi s ≠ 0) (hs1 : s ≠ 1)
    (hre : 0 < s.re) : riemannZeta s ≠ 0 := by
  have hΓ : Complex.Gamma (s / 2 + 1) ≠ 0 := Complex.Gamma_ne_zero fun m h ↦ by
    have := congrArg Complex.re h
    simp at this
    linarith [m.cast_nonneg (α := ℝ)]
  intro hz
  apply hs
  rw [riemannXi_eq_mul_Gamma_add_one hs1 hΓ, hz, mul_zero]

/-- **Davenport, Ch. 15, pp. 98-99 (row 15-5, `S(T) = O(log T)`)**: for `T ≥ 2` not an
ordinate, `|∫_{1/2}^2 Im ξ'/ξ(x + iT) dx| ≤ A log T`. -/
@[kb "davenport1980" "Ch 15, p. 98"]
theorem Davenport.abs_integral_im_logDeriv_riemannXi_le :
    ∃ A : ℝ, 0 < A ∧ ∀ T : ℝ, 2 ≤ T → (∀ ρ : ZeroIndex riemannXi, |ρ.val.im| ≠ T) →
      |∫ x in (1 / 2 : ℝ)..2, (logDeriv riemannXi (x + T * I)).im| ≤ A * Real.log T := by
  classical
  obtain ⟨A₁, hA₁, h₁⟩ := Davenport.logDeriv_riemannZeta_local
  obtain ⟨A₂, hA₂, h₂⟩ := Davenport.card_zeta_zeros_near_le
  set B : ℝ := A₁ + 7 with hB
  refine ⟨2 * (π * A₂ + 3 / 2 * B), by positivity, fun T hT hTz ↦ ?_⟩
  have hT0 : 0 < T := by linarith
  have hlog4 : 1 ≤ Real.log (T + 2) := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9; linarith
  have hlogT : Real.log (T + 2) ≤ 2 * Real.log T := by
    rw [← Real.log_rpow hT0]
    exact Real.log_le_log (by linarith) (by norm_num; nlinarith)
  obtain ⟨hfin, hcard⟩ := h₂ T
  set S := hfin.toFinset with hS
  have hSc : (S.card : ℝ) ≤ A₂ * Real.log (T + 2) := by
    rw [hS, ← Set.ncard_eq_toFinset_card _ hfin]
    simpa [abs_of_pos hT0] using hcard
  set f : ℝ → ℂ := fun x ↦ logDeriv riemannXi (x + T * I) with hf
  set g : ℝ → ℂ := fun x ↦ ∑ ρ ∈ S, 1 / ((x : ℂ) + T * I - ρ.val) with hg
  have hfc : Continuous f := continuous_logDeriv_riemannXi_horiz hTz T (abs_of_pos hT0)
  have hγ : ∀ ρ : ZeroIndex riemannXi, ρ.val.im ≠ T := fun ρ h ↦
    hTz ρ (by rw [h, abs_of_pos hT0])
  have hgc : Continuous g := by
    refine continuous_finsetSum _ fun ρ _ ↦ ?_
    have hg' : Continuous fun x : ℝ ↦ (x : ℂ) + T * I - ρ.val := by fun_prop
    have h0 : ∀ x : ℝ, (x : ℂ) + T * I - ρ.val ≠ 0 := fun x h' ↦
      hγ ρ (by have := congrArg Complex.im h'; simp at this; linarith)
    exact (hg'.inv₀ h0).congr fun x ↦ (one_div _).symm
  -- the remainder bound
  have hR : ∀ x ∈ Set.Ioc (1 / 2 : ℝ) 2, ‖(f x - g x).im‖ ≤ B * Real.log (T + 2) := by
    intro x hx
    set s : ℂ := x + T * I with hs
    have hsre : s.re = x := by simp [s]
    have hsim : s.im = T := by simp [s]
    have hs1 : s ≠ 1 := fun h ↦ by
      have := congrArg Complex.im h; rw [hsim] at this; simp at this; linarith
    have hξ : riemannXi s ≠ 0 := riemannXi_ne_zero_of_abs_im hTz (by rw [hsim, abs_of_pos hT0])
    have hz : riemannZeta s ≠ 0 :=
      riemannZeta_ne_zero_of_riemannXi_ne_zero hξ hs1 (by rw [hsre]; linarith [hx.1])
    have hΓ : ∀ m : ℕ, s / 2 + 1 ≠ -m := by
      intro m h
      have := congrArg Complex.re h
      simp [hsre] at this
      linarith [m.cast_nonneg (α := ℝ), hx.1]
    have hxi := logDeriv_riemannZeta_eq_xi hs1 hΓ hz
    have hloc := h₁ s (by rw [hsre]; linarith [hx.1]) (by rw [hsre]; exact hx.2)
      (by rw [hsim, abs_of_pos hT0]; exact hT) hz
    have htsum : ∑' ρ : ZeroIndex riemannXi,
        (if |s.im - ρ.val.im| < 1 then 1 / (s - ρ.val) else 0) = g x := by
      rw [tsum_eq_sum (s := S)]
      · refine Finset.sum_congr rfl fun ρ hρ ↦ ?_
        rw [hS, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hρ
        rw [ite_eq_left_iff.mpr fun h ↦ absurd (by rw [hsim, abs_sub_comm]; exact hρ) h]
      · intro ρ hρ
        rw [hS, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hρ
        exact ite_eq_right_iff.mpr fun h ↦ absurd (by rw [hsim, abs_sub_comm] at h; exact h) hρ
    rw [htsum] at hloc
    have hfx : f x - g x = (deriv riemannZeta s / riemannZeta s - g x) + 1 / (s - 1) -
        Complex.log π / 2 + Complex.digamma (s / 2 + 1) / 2 := by
      simp only [hf]
      rw [hxi]; ring
    have h1 : ‖1 / (s - 1)‖ ≤ 1 := by
      rw [norm_div, norm_one]
      have : 1 ≤ ‖s - 1‖ := by
        have := Complex.abs_im_le_norm (s - 1)
        rw [sub_im, hsim, one_im, sub_zero, abs_of_pos hT0] at this
        linarith
      exact div_le_one_of_le₀ this (norm_nonneg _)
    have h2 : ‖Complex.log π / 2‖ ≤ 1 := by
      rw [← Complex.ofReal_log Real.pi_pos.le, norm_div, Complex.norm_real, Real.norm_of_nonneg
        (Real.log_nonneg (by linarith [Real.pi_gt_three])), Complex.norm_ofNat]
      have : Real.log π < 2 := by
        rw [Real.log_lt_iff_lt_exp Real.pi_pos]
        have := Real.pi_lt_four
        have : (4 : ℝ) < Real.exp 2 := by
          have := Real.add_one_le_exp 2
          have h := Real.exp_one_gt_d9
          rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
          nlinarith
        linarith
      linarith
    have h3 : ‖Complex.digamma (s / 2 + 1) / 2‖ ≤ (5 + 4 * Real.log (T + 2)) / 2 := by
      rw [norm_div, Complex.norm_ofNat]
      have := norm_digamma_half_add_one_le (z := s) (by rw [hsre]; linarith [hx.1])
        (by rw [hsre]; exact hx.2) (by rw [hsim, abs_of_pos hT0]; exact hT)
      rw [hsim, abs_of_pos hT0] at this
      linarith
    have hloc' : ‖deriv riemannZeta s / riemannZeta s - g x‖ ≤ A₁ * Real.log (T + 2) := by
      rw [hsim, abs_of_pos hT0] at hloc; exact hloc
    calc ‖(f x - g x).im‖ ≤ ‖f x - g x‖ := by
          rw [Real.norm_eq_abs]; exact Complex.abs_im_le_norm _
      _ ≤ ‖deriv riemannZeta s / riemannZeta s - g x‖ + ‖1 / (s - 1)‖ +
          ‖Complex.log π / 2‖ + ‖Complex.digamma (s / 2 + 1) / 2‖ := by
          rw [hfx]
          exact norm_add_sub_add_le _ _ _ _
      _ ≤ A₁ * Real.log (T + 2) + 1 + 1 + (5 + 4 * Real.log (T + 2)) / 2 := by
          linarith [hloc', h1, h2, h3]
      _ ≤ B * Real.log (T + 2) := by
          have e : B * Real.log (T + 2) = A₁ * Real.log (T + 2) + 7 * Real.log (T + 2) := by
            rw [hB]; ring
          linarith
  -- split the integral
  have hsplit : ∫ x in (1 / 2 : ℝ)..2, (f x).im =
      (∫ x in (1 / 2 : ℝ)..2, (g x).im) + ∫ x in (1 / 2 : ℝ)..2, (f x - g x).im := by
    have i1 : IntervalIntegrable (fun x ↦ (g x).im) volume (1 / 2) 2 :=
      (Complex.continuous_im.comp hgc).intervalIntegrable _ _
    have i2 : IntervalIntegrable (fun x ↦ (f x - g x).im) volume (1 / 2) 2 :=
      (Complex.continuous_im.comp (hfc.sub hgc)).intervalIntegrable _ _
    rw [← intervalIntegral.integral_add i1 i2]
    refine intervalIntegral.integral_congr fun x _ ↦ ?_
    simp
  have hgi : |∫ x in (1 / 2 : ℝ)..2, (g x).im| ≤ π * S.card := by
    have : ∫ x in (1 / 2 : ℝ)..2, (g x).im =
        ∑ ρ ∈ S, ∫ x in (1 / 2 : ℝ)..2, (1 / ((x : ℂ) + T * I - ρ.val)).im := by
      rw [← intervalIntegral.integral_finsetSum]
      · refine intervalIntegral.integral_congr fun x _ ↦ ?_
        simp only [hg, Complex.im_sum]
      · intro ρ _
        have hg' : Continuous fun x : ℝ ↦ (x : ℂ) + T * I - ρ.val := by fun_prop
        have h0 : ∀ x : ℝ, (x : ℂ) + T * I - ρ.val ≠ 0 := fun x h' ↦
          hγ ρ (by have := congrArg Complex.im h'; simp at this; linarith)
        exact (Complex.continuous_im.comp ((hg'.inv₀ h0).congr fun x ↦ (one_div _).symm)).intervalIntegrable _ _
    rw [this]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ ρ ∈ S, |∫ x in (1 / 2 : ℝ)..2, (1 / ((x : ℂ) + T * I - ρ.val)).im|
        ≤ ∑ ρ ∈ S, π := Finset.sum_le_sum fun ρ _ ↦ abs_integral_im_inv_sub_le (hγ ρ) _ _
      _ = π * S.card := by rw [Finset.sum_const, nsmul_eq_mul]; ring
  have hri : |∫ x in (1 / 2 : ℝ)..2, (f x - g x).im| ≤ 3 / 2 * (B * Real.log (T + 2)) := by
    rw [← Real.norm_eq_abs]
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 1 / 2) (b := 2)
      (C := B * Real.log (T + 2)) (f := fun x ↦ (f x - g x).im) (fun x hx ↦ by
        rw [uIoc_of_le (by norm_num)] at hx; exact hR x hx)
    refine this.trans (le_of_eq ?_)
    norm_num
    ring
  rw [show (∫ x in (1 / 2 : ℝ)..2, (logDeriv riemannXi (x + T * I)).im) =
    ∫ x in (1 / 2 : ℝ)..2, (f x).im from rfl, hsplit]
  have hBpos : 0 ≤ B := by positivity
  calc |(∫ x in (1 / 2 : ℝ)..2, (g x).im) + ∫ x in (1 / 2 : ℝ)..2, (f x - g x).im|
      ≤ π * S.card + 3 / 2 * (B * Real.log (T + 2)) := (abs_add_le _ _).trans (add_le_add hgi hri)
    _ ≤ π * (A₂ * Real.log (T + 2)) + 3 / 2 * (B * Real.log (T + 2)) := by gcongr
    _ = (π * A₂ + 3 / 2 * B) * Real.log (T + 2) := by ring
    _ ≤ (π * A₂ + 3 / 2 * B) * (2 * Real.log T) := by gcongr
    _ = 2 * (π * A₂ + 3 / 2 * B) * Real.log T := by ring

end NTKB
