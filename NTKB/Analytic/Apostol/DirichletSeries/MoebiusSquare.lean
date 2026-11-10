/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Apostol.DirichletSeries.MeanValues
import NTKB.Analytic.Apostol.DirichletSeries.Products
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries

/-!
# `∑ μ(n)² n^{-s} = ζ(s)/ζ(2s)` and Theorem 11.16 (c)

Apostol (proof of Theorem 11.16 (c)): by Euler products (Theorem 11.7),
`∑ μ(n)² n^{-s} = ∏_p (1 + p^{-s}) = ∏_p (1 - p^{-2s})/(1 - p^{-s}) = ζ(s)/ζ(2s)` for `σ > 1`.
Then Theorem 11.16 with `f = μ` (`∑ μ(n) n^{-s} = 1/ζ(s)`) gives
`(1/2T) ∫_{-T}^{T} |ζ(σ+it)|^{-2} dt → ζ(2σ)/ζ(4σ)` for `σ > 1`.
-/

open Complex Filter Topology LSeries ArithmeticFunction
open scoped ArithmeticFunction.Moebius

namespace NTKB.Apostol

/-- `μ²` as a complex arithmetic function. -/
noncomputable def moebiusSq : ArithmeticFunction ℂ :=
  (μ : ArithmeticFunction ℂ).pmul (μ : ArithmeticFunction ℂ)

lemma moebiusSq_apply (n : ℕ) : moebiusSq n = ((μ n : ℤ) : ℂ) ^ 2 := by
  simp [moebiusSq, sq]

lemma isMultiplicative_moebiusSq : moebiusSq.IsMultiplicative :=
  isMultiplicative_moebius.intCast.pmul isMultiplicative_moebius.intCast

/-- The local factor: `∑_e μ(p^e)² p^{-es} = 1 + p^{-s}`. -/
lemma tsum_term_moebiusSq_prime_pow {p : ℕ} (hp : p.Prime) (s : ℂ) :
    ∑' e : ℕ, term (fun n => moebiusSq n) s (p ^ e) = 1 + (p : ℂ) ^ (-s) := by
  rw [tsum_eq_sum (s := Finset.range 2) (fun e he => ?_)]
  · simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add, pow_zero,
      pow_one]
    rw [term_of_ne_zero one_ne_zero, term_of_ne_zero hp.ne_zero, moebiusSq_apply, moebiusSq_apply,
      moebius_apply_one, moebius_apply_prime hp, cpow_neg]
    simp
  · have he2 : 2 ≤ e := by simp at he; omega
    rw [term_of_ne_zero (pow_ne_zero _ hp.ne_zero), moebiusSq_apply,
      moebius_apply_prime_pow hp (by omega), ite_eq_right (by omega)]
    simp

/-- `∑ μ(n)² n^{-s} = ζ(s)/ζ(2s)` for `σ > 1`. -/
theorem LSeries_moebiusSq {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => moebiusSq n) s = riemannZeta s / riemannZeta (2 * s) := by
  have hs2 : 1 < (2 * s).re := by simp; linarith
  have hsum : LSeriesSummable (fun n => moebiusSq n) s := by
    refine LSeriesSummable_of_le_const_mul_rpow (x := 1) hs ⟨1, fun n hn => ?_⟩
    rw [moebiusSq_apply]
    simp only [Real.rpow_zero, sub_self, mul_one, norm_pow, Complex.norm_intCast]
    have := abs_moebius_le_one (n := n)
    have h0 : (0 : ℝ) ≤ |(μ n : ℝ)| := abs_nonneg _
    have h1 : |((μ n : ℤ) : ℝ)| ≤ 1 := by exact_mod_cast this
    nlinarith
  have hE := apostol_thm_11_7 isMultiplicative_moebiusSq hsum
  have hZ := (riemannZeta_eulerProduct_hasProd hs).div₀ (riemannZeta_eulerProduct_hasProd hs2)
    (riemannZeta_ne_zero_of_one_lt_re hs2)
  have hfun : (fun p : Nat.Primes => ∑' e : ℕ, term (fun n => moebiusSq n) s ((p : ℕ) ^ e)) =
      fun p : Nat.Primes => (1 - ((p : ℕ) : ℂ) ^ (-s))⁻¹ / (1 - ((p : ℕ) : ℂ) ^ (-(2 * s)))⁻¹ := by
    funext p
    rw [tsum_term_moebiusSq_prime_pow p.prop]
    set x := ((p : ℕ) : ℂ) ^ (-s) with hxdef
    have hx2 : ((p : ℕ) : ℂ) ^ (-(2 * s)) = x ^ 2 := by
      rw [hxdef, show -(2 * s) = ((2 : ℕ) : ℂ) * (-s) by push_cast; ring, cpow_nat_mul]
    have hxn : ‖x‖ < 1 := by
      rw [hxdef, norm_natCast_cpow_of_pos p.prop.pos, neg_re]
      have hp2 : (1 : ℝ) < (p : ℕ) := by exact_mod_cast p.prop.one_lt
      exact Real.rpow_lt_one_of_one_lt_of_neg hp2 (by linarith)
    have hx1 : 1 - x ≠ 0 := by
      intro h; rw [sub_eq_zero] at h; rw [← h, norm_one] at hxn; exact lt_irrefl _ hxn
    have hx1' : 1 + x ≠ 0 := by
      intro h; rw [add_eq_zero_iff_eq_neg] at h
      rw [show x = -1 by linear_combination h, norm_neg, norm_one] at hxn; exact lt_irrefl _ hxn
    have hx3 : 1 - x ^ 2 ≠ 0 := by
      rw [show 1 - x ^ 2 = (1 - x) * (1 + x) by ring]; exact mul_ne_zero hx1 hx1'
    rw [hx2]
    field_simp
    ring
  rw [hfun] at hE
  exact hE.unique hZ

/-- **Theorem 11.16 (c)**: for `σ > 1`,
`(1/2T) ∫_{-T}^{T} |ζ(σ+it)|^{-2} dt → ζ(2σ)/ζ(4σ)`. -/
@[kb "apostol1976" "Thm 11.16(c), p. 241"]
theorem apostol_thm_11_16_c {σ : ℝ} (hσ : 1 < σ) :
    Tendsto (fun T : ℝ => 1 / (2 * T) * ∫ t in (-T)..T, ‖(riemannZeta (σ + t * I))⁻¹‖ ^ 2)
      atTop (𝓝 (riemannZeta (2 * σ) / riemannZeta (4 * σ)).re) := by
  set f : ℕ → ℂ := fun n => ((μ n : ℤ) : ℂ)
  have hf : LSeriesSummable f σ := LSeriesSummable_moebius_iff.mpr (by simpa using hσ)
  have h := apostol_thm_11_16 hf
  have e1 : ∀ t : ℝ, ‖LSeries f (σ + t * I)‖ = ‖(riemannZeta (σ + t * I))⁻¹‖ := by
    intro t
    have hre : 1 < ((σ : ℂ) + t * I).re := by simpa using hσ
    have hm := LSeries_zeta_mul_Lseries_moebius hre
    rw [LSeries_zeta_eq_riemannZeta hre] at hm
    rw [eq_inv_of_mul_eq_one_right hm]
  simp_rw [e1] at h
  convert h using 2
  have hfun : (fun n => moebiusSq n) = fun n => f n * (starRingEnd ℂ) (f n) := by
    funext n; rw [moebiusSq_apply]; simp [f, sq]
  have hL : LSeries (fun n => moebiusSq n) (σ + σ) = ((∑' n : ℕ, ‖term f σ n‖ ^ 2 : ℝ) : ℂ) := by
    rw [hfun, LSeries, ofReal_tsum]
    refine tsum_congr fun n => ?_
    rw [← term_mul_term, term_conj, mul_conj, Complex.normSq_eq_norm_sq, ofReal_pow]
  have h2 : 1 < ((σ : ℂ) + σ).re := by simp; linarith
  rw [LSeries_moebiusSq h2] at hL
  rw [show (2 : ℂ) * σ = σ + σ by ring, show (4 : ℂ) * σ = 2 * (σ + σ) by ring, hL, ofReal_re]

end NTKB.Apostol
