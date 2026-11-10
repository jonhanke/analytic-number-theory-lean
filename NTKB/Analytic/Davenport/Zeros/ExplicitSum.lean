/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Davenport.Zeros.GoodHeight
import Mathlib.NumberTheory.Chebyshev

/-!
# `J(x, T)` as a sum over prime powers

**Davenport, Ch. 17, p. 106 (row 17-7).** For `c > 1`,
`J(x, T) = (1/2πi) ∫_{c-iT}^{c+iT} (-ζ'(s)/ζ(s)) x^s/s ds = ∑_n Λ(n) I(x/n, T)`,
by termwise integration of the Dirichlet series `-ζ'/ζ(s) = ∑ Λ(n) n^{-s}`, which converges
absolutely and uniformly on `σ = c`.
-/

open Filter Topology Complex Set DirichletCharacter LSeries MeasureTheory
open scoped Real LSeries.notation ArithmeticFunction.vonMangoldt Interval

namespace NTKB

/-- `J(x, T) = (1/2π) ∫_{-T}^{T} F(c + it) dt`. -/
noncomputable def explicitJ (x c T : ℝ) : ℂ :=
  (1 / (2 * π)) * ∫ t : ℝ in -T..T, explicitIntegrand x (c + t * I)

lemma perronKernel_div_nat {x : ℝ} (hx : 0 ≤ x) {n : ℕ} (hn : n ≠ 0) (s : ℂ) :
    (Λ n : ℂ) / (n : ℂ) ^ s * perronKernel x s = Λ n * perronKernel (x / n) s := by
  have hn' : (n : ℂ) ^ s ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]; push Not; intro h; exact absurd h (by exact_mod_cast hn)
  simp only [perronKernel]
  rw [show ((x / n : ℝ) : ℂ) = ((x : ℝ) : ℂ) / ((n : ℝ) : ℂ) by push_cast; ring,
    div_cpow_ofReal_nonneg hx n.cast_nonneg, Complex.ofReal_natCast]
  field_simp

/-- **Davenport, Ch. 17, p. 106, (C) (row 17-7)**, the first step:
`J(x, T) = ∑_n Λ(n) I(x/n, T)` for `x > 0`, `c > 1`. -/
@[kb "davenport1980" "Ch 17, p. 106"]
theorem Davenport.hasSum_explicitJ {x c : ℝ} (T : ℝ) (hx : 0 < x) (hc : 1 < c) :
    HasSum (fun n : ℕ ↦ (Λ n : ℂ) * perronIntegral (x / n) c T) (explicitJ x c T) := by
  have hc0 : 0 < c := by linarith
  have hc1 : 1 < ((c : ℝ) : ℂ).re := by simpa using hc
  -- the Dirichlet series on `σ = c`
  have hsumΛ := (DirichletCharacter.LSeriesSummable_twist_vonMangoldt
    (1 : DirichletCharacter ℂ 1) hc1)
  set b : ℕ → ℝ := fun n ↦ ‖term (↗(1 : DirichletCharacter ℂ 1) * ↗Λ) (c : ℂ) n‖ * x ^ c / c
  have hb : Summable b := (hsumΛ.norm.mul_right (x ^ c)).div_const c
  -- the integrand as a series
  have hF : ∀ t : ℝ, HasSum (fun n : ℕ ↦ (Λ n : ℂ) * perronKernel (x / n) (c + t * I))
      (explicitIntegrand x (c + t * I)) := by
    intro t
    have h1 : 1 < ((c : ℂ) + t * I).re := by simpa using hc
    have hs := (DirichletCharacter.LSeriesSummable_twist_vonMangoldt
      (1 : DirichletCharacter ℂ 1) h1).LSeriesHasSum
    have he := neg_logDeriv_LFunction_eq_LSeries (1 : DirichletCharacter ℂ 1) h1
    rw [LFunction_modOne_eq] at he
    have := hs.mul_right (perronKernel x (c + t * I))
    rw [← he] at this
    have e : explicitIntegrand x (c + t * I) = -deriv riemannZeta (c + t * I) /
        riemannZeta (c + t * I) * perronKernel x (c + t * I) := by
      simp [explicitIntegrand, neg_div]
    rw [e]
    convert this using 1
    funext n
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · rw [term_of_ne_zero hn]
      simp only [Pi.mul_apply, MulChar.one_apply (isUnit_of_subsingleton _), one_mul]
      exact (perronKernel_div_nat hx.le hn _).symm
  -- dominated convergence on `[-T, T]`
  have hbound : ∀ n : ℕ, ∀ t : ℝ, ‖(Λ n : ℂ) * perronKernel (x / n) (c + t * I)‖ ≤ b n := by
    intro n t
    rcases eq_or_ne n 0 with rfl | hn
    · simp [b]
    have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    rw [← perronKernel_div_nat hx.le hn, norm_mul]
    simp only [b]
    rw [mul_div_assoc]
    refine mul_le_mul ?_ ?_ (norm_nonneg _) (norm_nonneg _)
    · rw [term_of_ne_zero hn]
      simp only [Pi.mul_apply, MulChar.one_apply (isUnit_of_subsingleton _), one_mul, norm_div]
      rw [Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn),
        Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn)]
      simp
    · rw [norm_perronKernel hx]
      simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
        add_zero]
      apply div_le_div_of_nonneg_left (Real.rpow_nonneg hx.le _) hc0
      have := Complex.re_le_norm ((c : ℂ) + t * I)
      simpa using this
  have hmeas : ∀ n : ℕ, AEStronglyMeasurable
      (fun t : ℝ ↦ (Λ n : ℂ) * perronKernel (x / n) (c + t * I)) (volume.restrict (Ι (-T) T)) := by
    intro n
    refine (Continuous.aestronglyMeasurable ?_)
    rcases eq_or_ne n 0 with rfl | hn
    · simp only [ArithmeticFunction.map_zero, Complex.ofReal_zero, zero_mul]
      exact continuous_const
    refine continuous_const.mul ?_
    have hy : 0 < x / n := div_pos hx (by exact_mod_cast Nat.pos_of_ne_zero hn)
    have hg : Continuous fun t : ℝ ↦ (c : ℂ) + t * I :=
      continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
    have hne : ∀ t : ℝ, (c : ℂ) + t * I ≠ 0 := fun t h ↦ by
      have := congrArg Complex.re h; simp at this; linarith
    have hy' : ((x / n : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
    have h1 : Continuous fun t : ℝ ↦ ((x / n : ℝ) : ℂ) ^ ((c : ℂ) + t * I) :=
      hg.const_cpow (Or.inl hy')
    have h2 : Continuous fun t : ℝ ↦ ((c : ℂ) + t * I)⁻¹ := hg.inv₀ hne
    exact (h1.mul h2).congr fun t ↦ by simp only [perronKernel, div_eq_mul_inv, Pi.mul_apply]
  have h := intervalIntegral.hasSum_integral_of_dominated_convergence (μ := volume) (a := -T)
    (b := T) (fun n _ ↦ b n) hmeas (fun n ↦ Eventually.of_forall fun t _ ↦ hbound n t)
    (Eventually.of_forall fun t _ ↦ hb) intervalIntegrable_const
    (Eventually.of_forall fun t _ ↦ hF t)
  unfold explicitJ
  have := h.mul_left (1 / (2 * π) : ℂ)
  refine this.congr_fun fun n ↦ ?_
  rw [intervalIntegral.integral_const_mul]
  show (Λ n : ℂ) * ((1 / (2 * π)) * ∫ t : ℝ in -T..T, perronKernel (x / n) (c + t * I)) = _
  ring

end NTKB
