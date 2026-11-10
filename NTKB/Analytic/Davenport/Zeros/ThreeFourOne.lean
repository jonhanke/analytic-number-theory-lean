/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import NTKB.Attr

/-!
# The 3-4-1 inequality for logarithmic derivatives

**Davenport, Ch. 13, pp. 94-95 and Ch. 14, p. 98.** For `σ > 1`,
`-ζ'/ζ(s) = ∑ Λ(n) n^{-s}`, so that
`3 (-ζ'/ζ(σ)) + 4 Re(-ζ'/ζ(σ + it)) + Re(-ζ'/ζ(σ + 2it)) ≥ 0`
by `3 + 4 cos θ + cos 2θ = 2(1 + cos θ)² ≥ 0`; and in general
`3 (-L'/L(σ, χ₀)) + 4 Re(-L'/L(σ + it, χ)) + Re(-L'/L(σ + 2it, χ²)) ≥ 0`.

Tau Ceti has the trigonometric inequality as `TauCeti.LSeries.threeFourOneCombination_nonneg`
(public) and Mathlib as a private lemma; it is reproved here (two lines).
-/

open Complex LSeries
open scoped LSeries.notation ArithmeticFunction.vonMangoldt

namespace NTKB

/-- **Mertens' inequality** (Davenport, Ch. 13, p. 94, row 13-3):
`3 + 4 cos θ + cos 2θ = 2 (1 + cos θ)² ≥ 0`. -/
@[kb "davenport1980" "Ch 13, p. 94"]
theorem Davenport.three_add_four_cos_add_cos_two_mul (θ : ℝ) :
    3 + 4 * Real.cos θ + Real.cos (2 * θ) = 2 * (1 + Real.cos θ) ^ 2 ∧
      0 ≤ 3 + 4 * Real.cos θ + Real.cos (2 * θ) := by
  have h : 3 + 4 * Real.cos θ + Real.cos (2 * θ) = 2 * (1 + Real.cos θ) ^ 2 := by
    rw [Real.cos_two_mul]; ring
  exact ⟨h, h ▸ by positivity⟩

/-- The complex form: `Re(3 + 4z + z²) = 2 (1 + Re z)² ≥ 0` for `‖z‖ = 1`. -/
lemma re_three_add_four_mul_add_sq_nonneg {z : ℂ} (hz : ‖z‖ = 1) :
    0 ≤ (3 + 4 * z + z ^ 2).re := by
  have h1 : z.re * z.re + z.im * z.im = 1 := by
    rw [← Complex.normSq_apply, ← Complex.sq_norm, hz, one_pow]
  have : (3 + 4 * z + z ^ 2).re = 2 * (1 + z.re) ^ 2 := by
    simp only [add_re, mul_re, pow_two]
    simp
    nlinarith
  rw [this]; positivity

/-- For `Re s > 1`: `-L'/L(s, χ) = ∑ χ(n) Λ(n) n^{-s}` (Mathlib, stated for `LFunction`). -/
lemma neg_logDeriv_LFunction_eq_LSeries {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {s : ℂ}
    (hs : 1 < s.re) :
    -deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s =
      L (↗χ * ↗Λ) s := by
  rw [DirichletCharacter.LSeries_twist_vonMangoldt_eq χ hs,
    DirichletCharacter.LFunction_eq_LSeries χ hs]
  congr 2
  refine Filter.EventuallyEq.deriv_eq <| Filter.eventuallyEq_iff_exists_mem.mpr ?_
  exact ⟨{z | 1 < z.re}, (isOpen_lt continuous_const continuous_re).mem_nhds hs,
    fun z hz ↦ DirichletCharacter.LFunction_eq_LSeries χ hz⟩

/-- The real part of the term `χ(n) Λ(n) n^{-(σ + it)}`. -/
lemma term_twist_vonMangoldt_eq {N : ℕ} (χ : DirichletCharacter ℂ N) (σ t : ℝ) {n : ℕ}
    (hn : n ≠ 0) :
    term (↗χ * ↗Λ) (σ + t * I) n = χ n * ((Λ n * (n : ℝ) ^ (-σ) : ℝ) : ℂ) *
      Complex.exp (-(t * Real.log n) * I) := by
  rw [term_of_ne_zero hn]
  simp only [Pi.mul_apply]
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  rw [Complex.cpow_def_of_ne_zero hn', ← Complex.ofReal_natCast,
    ← Complex.ofReal_log n.cast_nonneg, Real.rpow_def_of_pos (by positivity)]
  push_cast
  have h : Complex.exp (-(Complex.log n * (σ + t * I))) =
      Complex.exp (Complex.log n * -σ) * Complex.exp (-(t * Complex.log n) * I) := by
    rw [← Complex.exp_add]; ring_nf
  rw [div_eq_mul_inv, ← Complex.exp_neg, h]
  ring

/-- Pointwise 3-4-1 inequality for the terms. -/
lemma three_four_one_term {N : ℕ} (χ : DirichletCharacter ℂ N) {σ : ℝ} (t : ℝ) (n : ℕ) :
    0 ≤ 3 * (term (↗(1 : DirichletCharacter ℂ N) * ↗Λ) (σ : ℂ) n).re +
      4 * (term (↗χ * ↗Λ) (σ + t * I) n).re +
      (term (↗(χ ^ 2) * ↗Λ) (σ + (2 * t : ℝ) * I) n).re := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  have h0 := term_twist_vonMangoldt_eq (1 : DirichletCharacter ℂ N) σ 0 hn
  simp only [Complex.ofReal_zero, zero_mul, add_zero, neg_zero, Complex.exp_zero,
    mul_one] at h0
  rw [h0, term_twist_vonMangoldt_eq χ σ t hn, term_twist_vonMangoldt_eq (χ ^ 2) σ (2 * t) hn]
  set e := Complex.exp (-(t * Real.log n) * I)
  have he : Complex.exp (-((2 * t : ℝ) * Real.log n) * I) = e ^ 2 := by
    rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring
  have hen : ‖e‖ = 1 := by
    have : -((t : ℂ) * (Real.log n : ℝ)) * I = ((-(t * Real.log n) : ℝ) : ℂ) * I := by
      push_cast; ring
    simp only [e]; rw [this]; exact Complex.norm_exp_ofReal_mul_I _
  rw [he]
  set c : ℝ := Λ n * (n : ℝ) ^ (-σ)
  have hc : 0 ≤ c := mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg n.cast_nonneg _)
  rw [MulChar.pow_apply' χ two_ne_zero]
  by_cases hu : IsUnit (n : ZMod N)
  · rw [MulChar.one_apply hu]
    have hχ : ‖χ n * e‖ = 1 := by rw [norm_mul, ← hu.unit_spec, χ.unit_norm_eq_one, hen, one_mul]
    have key := re_three_add_four_mul_add_sq_nonneg hχ
    have : 3 * (1 * (c : ℂ)).re + 4 * (χ n * c * e).re + ((χ n) ^ 2 * c * e ^ 2).re =
        c * (3 + 4 * (χ n * e) + (χ n * e) ^ 2).re := by
      simp only [add_re, mul_re, ofReal_re, ofReal_im, pow_two]
      simp
      ring
    rw [this]
    exact mul_nonneg hc key
  · rw [MulChar.map_nonunit _ hu, MulChar.map_nonunit _ hu]
    simp

/-- **Davenport, Ch. 14, p. 98, (A) (row 14-2)**: for `σ > 1` and real `t`,
`3 Re(-L'/L(σ, χ₀)) + 4 Re(-L'/L(σ + it, χ)) + Re(-L'/L(σ + 2it, χ²)) ≥ 0`. -/
@[kb "davenport1980" "Ch 14, p. 98"]
theorem Davenport.three_four_one_LFunction {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    0 ≤ 3 * (-deriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ N)) σ /
          DirichletCharacter.LFunction (1 : DirichletCharacter ℂ N) σ).re +
      4 * (-deriv (DirichletCharacter.LFunction χ) (σ + t * I) /
          DirichletCharacter.LFunction χ (σ + t * I)).re +
      (-deriv (DirichletCharacter.LFunction (χ ^ 2)) (σ + (2 * t : ℝ) * I) /
          DirichletCharacter.LFunction (χ ^ 2) (σ + (2 * t : ℝ) * I)).re := by
  have h1 : 1 < (σ : ℂ).re := by simpa using hσ
  have h2 : 1 < (σ + t * I : ℂ).re := by simpa using hσ
  have h3 : 1 < (σ + (2 * t : ℝ) * I : ℂ).re := by simpa using hσ
  rw [neg_logDeriv_LFunction_eq_LSeries _ h1, neg_logDeriv_LFunction_eq_LSeries _ h2,
    neg_logDeriv_LFunction_eq_LSeries _ h3]
  have s1 := DirichletCharacter.LSeriesSummable_twist_vonMangoldt (1 : DirichletCharacter ℂ N) h1
  have s2 := DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ h2
  have s3 := DirichletCharacter.LSeriesSummable_twist_vonMangoldt (χ ^ 2) h3
  have h1' := Complex.reCLM.hasSum s1.LSeriesHasSum
  have h2' := Complex.reCLM.hasSum s2.LSeriesHasSum
  have h3' := Complex.reCLM.hasSum s3.LSeriesHasSum
  refine (((h1'.mul_left 3).add (h2'.mul_left 4)).add h3').nonneg fun n ↦ ?_
  simpa using three_four_one_term χ t n

/-- **Davenport, Ch. 13, p. 95, (C) (row 13-7)**: for `σ > 1` and real `t`,
`3 (-ζ'/ζ(σ)) + 4 Re(-ζ'/ζ(σ + it)) + Re(-ζ'/ζ(σ + 2it)) ≥ 0`. -/
@[kb "davenport1980" "Ch 13, p. 95"]
theorem Davenport.three_four_one_riemannZeta {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    0 ≤ 3 * (-deriv riemannZeta σ / riemannZeta σ).re +
      4 * (-deriv riemannZeta (σ + t * I) / riemannZeta (σ + t * I)).re +
      (-deriv riemannZeta (σ + (2 * t : ℝ) * I) / riemannZeta (σ + (2 * t : ℝ) * I)).re := by
  have h := Davenport.three_four_one_LFunction (1 : DirichletCharacter ℂ 1) hσ t
  simpa [DirichletCharacter.LFunction_modOne_eq] using h

end NTKB
