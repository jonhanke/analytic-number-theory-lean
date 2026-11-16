/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Davenport.Zeros.RiemannVonMangoldtExact

/-!
# `S(T)` is an argument of `ζ(1/2 + iT)`

**Davenport, Ch. 15, p. 98.** `πS(T)` is the value at `1/2 + iT` of the argument of `ζ(s)` obtained
by continuous variation along `2 → 2 + iT → 1/2 + iT` from the value `0` at `s = 2`. With `zetaArgS`
defined as the integral of the log-derivative along that path, this file checks that it is an
argument: `ζ(1/2 + iT) = |ζ(1/2 + iT)| e^{iπS(T)}`. The proof integrates `(f ∘ p)'/(f ∘ p)` along each
segment `p`: `f(p(b)) = f(p(a)) exp(∫_a^b (f ∘ p)'/(f ∘ p))` when `f ∘ p` does not vanish.
-/

open Filter Topology Complex Set
open scoped Real Interval

namespace NTKB

/-- Along a path on which `φ` does not vanish, `φ(b) = φ(a) exp(∫_a^b φ'/φ)`. -/
lemma eq_mul_exp_integral_logDeriv {φ ψ : ℝ → ℂ} {α β a b : ℝ} (hab : a ≤ b) (hα : α < a)
    (hβ : b < β) (hd : ∀ t ∈ Ioo α β, HasDerivAt φ (ψ t) t) (hc : ContinuousOn ψ (Ioo α β))
    (h0 : ∀ t ∈ Ioo α β, φ t ≠ 0) :
    φ b = φ a * Complex.exp (∫ t in a..b, ψ t / φ t) := by
  have hφc : ContinuousOn φ (Ioo α β) := fun t ht ↦ (hd t ht).continuousAt.continuousWithinAt
  have hcont : ContinuousOn (fun t ↦ ψ t / φ t) (Ioo α β) := hc.div hφc h0
  have ha : a ∈ Ioo α β := ⟨hα, by linarith⟩
  have hb : b ∈ Ioo α β := ⟨by linarith, hβ⟩
  set G : ℝ → ℂ := fun t ↦ ∫ u in a..t, ψ u / φ u with hGdef
  have hG : ∀ t ∈ Ioo α β, HasDerivAt G (ψ t / φ t) t := by
    intro t ht
    refine intervalIntegral.integral_hasDerivAt_right ?_ ?_ ?_
    · exact (hcont.mono (Set.OrdConnected.uIcc_subset inferInstance ha ht)).intervalIntegrable
    · exact hcont.stronglyMeasurableAtFilter isOpen_Ioo t ht
    · exact hcont.continuousAt (isOpen_Ioo.mem_nhds ht)
  set F : ℝ → ℂ := fun t ↦ φ t * Complex.exp (-G t) with hFdef
  have hF : ∀ t ∈ Ioo α β, HasDerivAt F 0 t := by
    intro t ht
    have h := (hd t ht).mul (hG t ht).neg.cexp
    convert h using 1
    field_simp [h0 t ht]
    ring
  have hsub : Icc a b ⊆ Ioo α β := fun t ht ↦ ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hconst := constant_of_has_deriv_right_zero (f := F) (a := a) (b := b)
    (fun t ht ↦ (hF t (hsub ht)).continuousAt.continuousWithinAt)
    (fun t ht ↦ (hF t (hsub (Ico_subset_Icc_self ht))).hasDerivWithinAt) b ⟨hab, le_rfl⟩
  have hGa : G a = 0 := intervalIntegral.integral_same
  simp only [hFdef, hGa, neg_zero, Complex.exp_zero, mul_one] at hconst
  calc φ b = φ b * Complex.exp (-G b) * Complex.exp (G b) := by
        rw [mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]
    _ = φ a * Complex.exp (∫ t in a..b, ψ t / φ t) := by rw [hconst]

set_option maxHeartbeats 4000000 in
/-- **Davenport, Ch. 15, p. 98**: for `T > 0` not an ordinate, `πS(T)` is an argument of
`ζ(1/2 + iT)`: `ζ(1/2 + iT) = |ζ(1/2 + iT)| e^{iπS(T)}`. -/
@[kb "davenport1980" "Ch 15, p. 98"]
theorem Davenport.riemannZeta_eq_norm_mul_exp_zetaArgS {T : ℝ} (hT : 0 < T)
    (hTz : ∀ ρ : ZeroIndex riemannXi, |ρ.val.im| ≠ T) :
    riemannZeta (1 / 2 + T * I) =
      ‖riemannZeta (1 / 2 + T * I)‖ * Complex.exp (π * zetaArgS T * I) := by
  have hπ := Real.pi_pos
  have hU : IsOpen {s : ℂ | s ≠ 1} := isOpen_ne
  have hζdiff : DifferentiableOn ℂ riemannZeta {s : ℂ | s ≠ 1} := fun s hs ↦
    (differentiableAt_riemannZeta hs).differentiableWithinAt
  have hζc : ContinuousOn (deriv riemannZeta) {s : ℂ | s ≠ 1} :=
    ((hζdiff.analyticOnNhd hU).deriv).continuousOn
  have hζd : ∀ s : ℂ, s ≠ 1 → HasDerivAt riemannZeta (deriv riemannZeta s) s := fun s hs ↦
    (differentiableAt_riemannZeta hs).hasDerivAt
  have hneV : ∀ y : ℝ, (2 : ℂ) + y * I ≠ 1 := fun y h ↦ by
    have := congrArg Complex.re h; simp at this
  have hneH : ∀ x : ℝ, (x : ℂ) + T * I ≠ 1 := fun x h ↦ by
    have := congrArg Complex.im h; simp at this; linarith
  have hpV : ∀ y : ℝ, HasDerivAt (fun y : ℝ ↦ (2 : ℂ) + y * I) I y := fun y ↦ by
    simpa using ((hasDerivAt_id (y : ℝ)).ofReal_comp.mul_const I).const_add (2 : ℂ)
  have hpH : ∀ x : ℝ, HasDerivAt (fun x : ℝ ↦ (x : ℂ) + T * I) 1 x := fun x ↦ by
    simpa using (hasDerivAt_id (x : ℝ)).ofReal_comp.add_const ((T : ℂ) * I)
  have cV : ∀ y : ℝ, ContinuousAt (fun y : ℝ ↦ deriv riemannZeta (2 + y * I)) y := fun y ↦
    ContinuousAt.comp (f := fun y : ℝ ↦ (2 : ℂ) + y * I) (x := y)
      (hζc.continuousAt (hU.mem_nhds (hneV y))) (by fun_prop)
  have zV : ∀ y : ℝ, ContinuousAt (fun y : ℝ ↦ riemannZeta (2 + y * I)) y := fun y ↦
    ContinuousAt.comp (f := fun y : ℝ ↦ (2 : ℂ) + y * I) (x := y)
      (differentiableAt_riemannZeta (hneV y)).continuousAt (by fun_prop)
  have cH : ∀ x : ℝ, ContinuousAt (fun x : ℝ ↦ deriv riemannZeta (x + T * I)) x := fun x ↦
    ContinuousAt.comp (f := fun x : ℝ ↦ (x : ℂ) + T * I) (x := x)
      (hζc.continuousAt (hU.mem_nhds (hneH x))) (by fun_prop)
  have zH : ∀ x : ℝ, ContinuousAt (fun x : ℝ ↦ riemannZeta (x + T * I)) x := fun x ↦
    ContinuousAt.comp (f := fun x : ℝ ↦ (x : ℂ) + T * I) (x := x)
      (differentiableAt_riemannZeta (hneH x)).continuousAt (by fun_prop)
  have hcV : ContinuousOn (fun y : ℝ ↦ deriv riemannZeta (2 + y * I) * I) (Ioo (-1) (T + 1)) :=
    fun y _ ↦ ((cV y).mul continuousAt_const).continuousWithinAt
  have hcH : ContinuousOn (fun x : ℝ ↦ deriv riemannZeta (x + T * I)) (Ioo (1 / 4) 3) :=
    fun x _ ↦ (cH x).continuousWithinAt
  have h0V : ∀ y : ℝ, riemannZeta (2 + y * I) ≠ 0 := fun y ↦
    riemannZeta_ne_zero_of_one_lt_re (by simp)
  have h0H : ∀ x ∈ Ioo (1 / 4 : ℝ) 3, riemannZeta (x + T * I) ≠ 0 := fun x hx ↦
    riemannZeta_ne_zero_of_riemannXi_ne_zero
      (riemannXi_ne_zero_of_abs_im hTz (by simp [abs_of_pos hT])) (hneH x)
      (by simp; linarith [hx.1])
  have hV := eq_mul_exp_integral_logDeriv (φ := fun y : ℝ ↦ riemannZeta (2 + y * I))
    (ψ := fun y : ℝ ↦ deriv riemannZeta (2 + y * I) * I) (α := -1) (β := T + 1) hT.le
    (by norm_num) (by linarith)
    (fun y _ ↦ (hζd _ (hneV y)).comp y (hpV y)) hcV (fun y _ ↦ h0V y)
  have hH := eq_mul_exp_integral_logDeriv (φ := fun x : ℝ ↦ riemannZeta (x + T * I))
    (ψ := fun x : ℝ ↦ deriv riemannZeta (x + T * I)) (α := 1 / 4) (β := 3) (a := 1 / 2) (b := 2)
    (by norm_num) (by norm_num) (by norm_num)
    (fun x _ ↦ by have h := (hζd _ (hneH x)).comp x (hpH x); rw [mul_one] at h; exact h) hcH h0H
  set Iv := ∫ y in (0 : ℝ)..T, deriv riemannZeta (2 + y * I) / riemannZeta (2 + y * I) with hIv
  set Ih := ∫ x in (1 / 2 : ℝ)..2, deriv riemannZeta (x + T * I) / riemannZeta (x + T * I)
    with hIh
  have hIvI : ∫ y in (0 : ℝ)..T, deriv riemannZeta (2 + y * I) * I / riemannZeta (2 + y * I) =
      Iv * I := by
    rw [hIv, ← intervalIntegral.integral_mul_const]
    refine intervalIntegral.integral_congr fun y _ ↦ ?_
    ring
  rw [hIvI] at hV
  have h2 : riemannZeta (2 + ((0 : ℝ) : ℂ) * I) = ((π ^ 2 / 6 : ℝ) : ℂ) := by
    rw [ofReal_zero, zero_mul, add_zero, riemannZeta_two]; push_cast; ring
  rw [h2] at hV
  set w := Iv * I - Ih with hw
  have hmain : riemannZeta (1 / 2 + T * I) = ((π ^ 2 / 6 : ℝ) : ℂ) * Complex.exp w := by
    have hH' : riemannZeta ((2 : ℝ) + T * I) = riemannZeta (((1 / 2 : ℝ) : ℂ) + T * I) *
        Complex.exp Ih := hH
    have e1 : ((2 : ℝ) : ℂ) + T * I = 2 + T * I := by push_cast; rfl
    have e2 : ((1 / 2 : ℝ) : ℂ) + T * I = 1 / 2 + T * I := by push_cast; rfl
    rw [e1, e2] at hH'
    rw [hw, Complex.exp_sub, ← mul_div_assoc, ← hV, hH', mul_div_assoc,
      div_self (Complex.exp_ne_zero _), mul_one]
  -- the imaginary part of `w`
  have hintV : IntervalIntegrable
      (fun y : ℝ ↦ deriv riemannZeta (2 + y * I) / riemannZeta (2 + y * I)) MeasureTheory.volume 0 T := by
    refine ContinuousOn.intervalIntegrable fun y _ ↦ ?_
    exact ((cV y).div (zV y) (h0V y)).continuousWithinAt
  have hintH : IntervalIntegrable
      (fun x : ℝ ↦ deriv riemannZeta (x + T * I) / riemannZeta (x + T * I)) MeasureTheory.volume (1 / 2) 2 := by
    refine ContinuousOn.intervalIntegrable fun x hx ↦ ?_
    rw [uIcc_of_le (by norm_num)] at hx
    exact ((cH x).div (zH x) (h0H x ⟨by linarith [hx.1], by linarith [hx.2]⟩)).continuousWithinAt
  have hre : (∫ y in (0 : ℝ)..T, (deriv riemannZeta (2 + y * I) / riemannZeta (2 + y * I)).re) =
      Iv.re := Complex.reCLM.intervalIntegral_comp_comm hintV
  have him : (∫ x in (1 / 2 : ℝ)..2, (deriv riemannZeta (x + T * I) /
      riemannZeta (x + T * I)).im) = Ih.im := Complex.imCLM.intervalIntegral_comp_comm hintH
  have hwim : w.im = π * zetaArgS T := by
    rw [zetaArgS, hre, him, mul_div_cancel₀ _ hπ.ne', hw]
    simp
  have hpos : (0 : ℝ) < π ^ 2 / 6 := by positivity
  have hnorm : ‖riemannZeta (1 / 2 + T * I)‖ = π ^ 2 / 6 * Real.exp w.re := by
    rw [hmain, norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_of_nonneg hpos.le]
  rw [hnorm, hmain]
  conv_lhs => rw [← Complex.re_add_im w, Complex.exp_add, hwim]
  push_cast
  ring

end NTKB
