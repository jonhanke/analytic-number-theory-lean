/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Apostol.DirichletSeries.MoebiusSquare
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Nat.Choose.Cast

/-!
# `∑ d(n)² n^{-s} = ζ⁴(s)/ζ(2s)` and Theorem 11.16 (d)

Apostol (proof of Theorem 11.16 (d)): with Euler products,
`∑ d(n)² n^{-s} = ∏_p ∑_e (e+1)² p^{-es} = ∏_p (1 + p^{-s})/(1 - p^{-s})³ = ζ⁴(s)/ζ(2s)`
(`∑ (e+1)² x^e = (1 + x)/(1 - x)³`). With `∑ d(n) n^{-s} = ζ²(s)`, Theorem 11.16 gives
`(1/2T) ∫_{-T}^{T} |ζ(σ+it)|⁴ dt → ζ⁴(2σ)/ζ(4σ)` for `σ > 1`.
-/

open Complex Filter Topology LSeries ArithmeticFunction
open scoped ArithmeticFunction.sigma LSeries.notation

namespace NTKB.Apostol

/-- `d(n)²` as a complex arithmetic function. -/
noncomputable def divisorSq : ArithmeticFunction ℂ :=
  (σ 0 : ArithmeticFunction ℂ).pmul (σ 0 : ArithmeticFunction ℂ)

lemma divisorSq_apply (n : ℕ) : divisorSq n = ((σ 0 n : ℕ) : ℂ) ^ 2 := by
  simp [divisorSq, sq]

lemma isMultiplicative_divisorSq : divisorSq.IsMultiplicative :=
  isMultiplicative_sigma.natCast.pmul isMultiplicative_sigma.natCast

lemma natCast_pow_cpow (p e : ℕ) (s : ℂ) : (((p ^ e : ℕ) : ℂ)) ^ s = ((p : ℂ) ^ s) ^ e := by
  induction e with
  | zero => simp
  | succ e ih => rw [pow_succ, Nat.cast_mul, natCast_mul_natCast_cpow, ih, pow_succ]

lemma term_divisorSq_prime_pow {p : ℕ} (hp : p.Prime) (s : ℂ) (e : ℕ) :
    term (fun n => divisorSq n) s (p ^ e) = ((e : ℂ) + 1) ^ 2 * ((p : ℂ) ^ (-s)) ^ e := by
  rw [term_of_ne_zero (pow_ne_zero _ hp.ne_zero), divisorSq_apply, sigma_zero_apply_prime_pow hp,
    natCast_pow_cpow, cpow_neg, inv_pow, div_eq_mul_inv]
  push_cast; ring

lemma hasSum_succ_sq_mul_geometric {x : ℂ} (hx : ‖x‖ < 1) :
    HasSum (fun e : ℕ => ((e : ℂ) + 1) ^ 2 * x ^ e) ((1 + x) / (1 - x) ^ 3) := by
  have h2 := hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℂ) 2 hx
  have h1 := hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℂ) 1 hx
  have h := (h2.mul_left 2).sub h1
  have hx1 : 1 - x ≠ 0 := by
    intro h0; rw [sub_eq_zero] at h0; rw [← h0, norm_one] at hx; exact lt_irrefl _ hx
  convert h using 1
  · funext e
    rw [Nat.cast_choose_two, Nat.choose_one_right]
    push_cast
    ring
  · field_simp
    ring

/-- `d(n)` as a complex function. -/
noncomputable def divisorC (n : ℕ) : ℂ := ((σ 0 n : ℕ) : ℂ)

lemma divisorC_eq_convolution {n : ℕ} (_hn : n ≠ 0) : divisorC n = ((1 : ℕ → ℂ) ⍟ 1) n := by
  rw [convolution_def]
  simp only [Pi.one_apply, mul_one, Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [divisorC, sigma_zero_apply, ← Nat.map_div_right_divisors, Finset.card_map]

lemma LSeriesSummable_divisorC {s : ℂ} (hs : 1 < s.re) : LSeriesSummable divisorC s := by
  have h1 : LSeriesSummable 1 s := LSeriesSummable_one_iff.mpr hs
  exact (LSeriesSummable_congr s fun {n} hn => divisorC_eq_convolution hn).mpr (h1.convolution h1)

lemma LSeries_divisorC {s : ℂ} (hs : 1 < s.re) : LSeries divisorC s = riemannZeta s ^ 2 := by
  have h1 : LSeriesSummable 1 s := LSeriesSummable_one_iff.mpr hs
  rw [LSeries_congr (fun {n} hn => divisorC_eq_convolution hn) s, LSeries_convolution' h1 h1,
    LSeries_one_eq_riemannZeta hs, sq]

lemma card_divisors_mul_le (m n : ℕ) : (m * n).divisors.card ≤ m.divisors.card * n.divisors.card := by
  rw [Nat.divisors_mul]; exact Finset.card_mul_le

lemma norm_divisorSq_le (n : ℕ) : ‖divisorSq n‖ ≤ ‖(divisorC ⍟ divisorC) n‖ := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [divisorSq_apply, convolution_def]
  simp only [divisorC]
  have hreal : ∀ m : ℕ, ‖((m : ℕ) : ℂ)‖ = m := fun m => by simp
  have e : (∑ x ∈ n.divisorsAntidiagonal, ((σ 0 x.1 : ℕ) : ℂ) * ((σ 0 x.2 : ℕ) : ℂ)) =
      ((∑ x ∈ n.divisorsAntidiagonal, σ 0 x.1 * σ 0 x.2 : ℕ) : ℂ) := by push_cast; rfl
  rw [norm_pow, hreal, e, hreal]
  have hle : (σ 0 n) ^ 2 ≤ ∑ x ∈ n.divisorsAntidiagonal, σ 0 x.1 * σ 0 x.2 := by
    calc (σ 0 n) ^ 2 = ∑ _x ∈ n.divisorsAntidiagonal, σ 0 n := by
          rw [Finset.sum_const, smul_eq_mul, sq, sigma_zero_apply, ← Nat.map_div_right_divisors,
            Finset.card_map]
      _ ≤ ∑ x ∈ n.divisorsAntidiagonal, σ 0 x.1 * σ 0 x.2 := by
          refine Finset.sum_le_sum fun x hx => ?_
          obtain ⟨hx1, -⟩ := Nat.mem_divisorsAntidiagonal.mp hx
          rw [← hx1, sigma_zero_apply, sigma_zero_apply, sigma_zero_apply]
          exact card_divisors_mul_le _ _
  exact_mod_cast hle

lemma LSeriesSummable_divisorSq {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n => divisorSq n) s := by
  have hD := LSeriesSummable_divisorC hs
  have hDD : LSeriesSummable (divisorC ⍟ divisorC) s := hD.convolution hD
  refine Summable.of_norm_bounded (g := fun n => ‖term (divisorC ⍟ divisorC) s n‖)
    (summable_norm_iff.mpr hDD) fun n => ?_
  exact norm_term_le s (norm_divisorSq_le n)

/-- `∑ d(n)² n^{-s} = ζ⁴(s)/ζ(2s)` for `σ > 1`. -/
theorem LSeries_divisorSq {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => divisorSq n) s = riemannZeta s ^ 4 / riemannZeta (2 * s) := by
  have hs2 : 1 < (2 * s).re := by simp; linarith
  have hsum : LSeriesSummable (fun n => divisorSq n) s := LSeriesSummable_divisorSq hs
  have hE := apostol_thm_11_7 isMultiplicative_divisorSq hsum
  have hz := riemannZeta_eulerProduct_hasProd hs
  have hZ := ((((hz.mul hz).mul hz).mul hz).div₀ (riemannZeta_eulerProduct_hasProd hs2)
    (riemannZeta_ne_zero_of_one_lt_re hs2))
  have hfun : (fun p : Nat.Primes => ∑' e : ℕ, term (fun n => divisorSq n) s ((p : ℕ) ^ e)) =
      fun p : Nat.Primes => (1 - ((p : ℕ) : ℂ) ^ (-s))⁻¹ * (1 - ((p : ℕ) : ℂ) ^ (-s))⁻¹ *
        (1 - ((p : ℕ) : ℂ) ^ (-s))⁻¹ * (1 - ((p : ℕ) : ℂ) ^ (-s))⁻¹ /
          (1 - ((p : ℕ) : ℂ) ^ (-(2 * s)))⁻¹ := by
    funext p
    set x := ((p : ℕ) : ℂ) ^ (-s) with hxdef
    have hxn : ‖x‖ < 1 := by
      rw [hxdef, norm_natCast_cpow_of_pos p.prop.pos, neg_re]
      have hp2 : (1 : ℝ) < (p : ℕ) := by exact_mod_cast p.prop.one_lt
      exact Real.rpow_lt_one_of_one_lt_of_neg hp2 (by linarith)
    simp_rw [term_divisorSq_prime_pow p.prop s]
    rw [(hasSum_succ_sq_mul_geometric hxn).tsum_eq]
    have hx2 : ((p : ℕ) : ℂ) ^ (-(2 * s)) = x ^ 2 := by
      rw [hxdef, show -(2 * s) = ((2 : ℕ) : ℂ) * (-s) by push_cast; ring, cpow_nat_mul]
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
  rw [hE.unique hZ]
  ring

/-- **Theorem 11.16 (d)**: for `σ > 1`,
`(1/2T) ∫_{-T}^{T} |ζ(σ+it)|⁴ dt → ζ⁴(2σ)/ζ(4σ)`. -/
@[kb "apostol1976" "Thm 11.16(d), p. 241"]
theorem apostol_thm_11_16_d {a : ℝ} (ha : 1 < a) :
    Tendsto (fun T : ℝ => 1 / (2 * T) * ∫ t in (-T)..T, ‖riemannZeta (a + t * I)‖ ^ 4)
      atTop (𝓝 (riemannZeta (2 * a) ^ 4 / riemannZeta (4 * a)).re) := by
  have hf : LSeriesSummable divisorC a := LSeriesSummable_divisorC (by simpa using ha)
  have h := apostol_thm_11_16 hf
  have e1 : ∀ t : ℝ, ‖LSeries divisorC (a + t * I)‖ ^ 2 = ‖riemannZeta (a + t * I)‖ ^ 4 := by
    intro t
    have hre : 1 < ((a : ℂ) + t * I).re := by simpa using ha
    rw [LSeries_divisorC hre, norm_pow, ← pow_mul]
  simp_rw [e1] at h
  convert h using 2
  have hfun : (fun n => divisorSq n) = fun n => divisorC n * (starRingEnd ℂ) (divisorC n) := by
    funext n; rw [divisorSq_apply]; simp [divisorC, sq]
  have hL : LSeries (fun n => divisorSq n) (a + a) =
      ((∑' n : ℕ, ‖term divisorC a n‖ ^ 2 : ℝ) : ℂ) := by
    rw [hfun, LSeries, ofReal_tsum]
    refine tsum_congr fun n => ?_
    rw [← term_mul_term, term_conj, mul_conj, Complex.normSq_eq_norm_sq, ofReal_pow]
  have h2 : 1 < ((a : ℂ) + a).re := by simp; linarith
  rw [LSeries_divisorSq h2] at hL
  rw [show (2 : ℂ) * a = a + a by ring, show (4 : ℂ) * a = 2 * (a + a) by ring, hL, ofReal_re]

end NTKB.Apostol
