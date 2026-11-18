/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.Nonvanishing
import NTKB.Attr

/-!
# `log ζ(s)` as a double sum over prime powers

**Davenport, Ch. 13, p. 84 (row 13-2).** For `σ > 1`,
`log ζ(s) = ∑_p ∑_{m ≥ 1} m⁻¹ p^{-ms}`, so that
`Re log ζ(σ + it) = log |ζ(σ + it)| = ∑_p ∑_{m ≥ 1} m⁻¹ p^{-mσ} cos(mt log p)`: the input of the
classical zero-free region (the `3 + 4 cos θ + cos 2θ` argument). From Mathlib's
`riemannZeta_eulerProduct_exp_log` and the power series of `-log(1 - z)`.
Source text unavailable: the statement follows the map's paraphrase.
-/

open Complex

namespace NTKB

lemma norm_primePow_lt_one {s : ℂ} (hs : 1 < s.re) (p : Nat.Primes) : ‖(p : ℂ) ^ (-s)‖ < 1 := by
  rw [norm_natCast_cpow_of_pos (mod_cast p.prop.pos), neg_re]
  exact Real.rpow_lt_one_of_one_lt_of_neg (mod_cast p.prop.one_lt) (by linarith)

lemma tsum_primePow_eq {s : ℂ} (hs : 1 < s.re) (p : Nat.Primes) :
    ∑' m : ℕ, ((p : ℂ) ^ (-s)) ^ (m + 1) / (m + 1) = -Complex.log (1 - (p : ℂ) ^ (-s)) :=
  (hasSum_taylorSeries_neg_log' (norm_primePow_lt_one hs p)).tsum_eq

lemma re_primePow_term (σ t : ℝ) (p : Nat.Primes) (m : ℕ) :
    ((((p : ℂ) ^ (-((σ : ℂ) + t * I))) ^ (m + 1) / (m + 1)) : ℂ).re =
      (p : ℝ) ^ (-((m + 1 : ℝ) * σ)) / (m + 1) * Real.cos ((m + 1 : ℝ) * t * Real.log p) := by
  have hp : (0 : ℝ) < p := by exact_mod_cast p.prop.pos
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast p.prop.ne_zero
  have h1 : ((p : ℂ) ^ (-((σ : ℂ) + t * I))) ^ (m + 1) =
      Complex.exp (((-((m + 1 : ℝ) * σ * Real.log p) : ℝ) : ℂ) +
        ((-((m + 1 : ℝ) * t * Real.log p) : ℝ) : ℂ) * I) := by
    rw [cpow_def_of_ne_zero hp0, ← Complex.exp_nat_mul]
    congr 1
    have : Complex.log (p : ℂ) = ((Real.log p : ℝ) : ℂ) := by
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_log hp.le]
    rw [this]
    push_cast
    ring
  have h2 : (((m : ℂ) + 1)) = (((m + 1 : ℝ)) : ℂ) := by push_cast; ring
  rw [h1, h2, Complex.div_ofReal_re, Complex.exp_re]
  simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
    add_zero, add_im, mul_im, zero_add]
  rw [Real.rpow_def_of_pos hp, Real.cos_neg]
  have : -((m + 1 : ℝ) * σ * Real.log p) = Real.log p * -((m + 1 : ℝ) * σ) := by ring
  rw [this]
  ring

/-- **Davenport, Ch. 13, p. 84 (row 13-2)**: for `Re s > 1`, `ζ(s) = exp(∑_p ∑_{m ≥ 1} p^{-ms}/m)`,
the double series converging (as an iterated sum). -/
@[kb "davenport1980" "Ch 13, p. 84"]
theorem Davenport.riemannZeta_eq_exp_tsum_primePow {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s =
      exp (∑' p : Nat.Primes, ∑' m : ℕ, ((p : ℂ) ^ (-s)) ^ (m + 1) / (m + 1)) := by
  rw [← riemannZeta_eulerProduct_exp_log hs]
  congr 1
  exact tsum_congr fun p ↦ (tsum_primePow_eq hs p).symm

/-- **Davenport, Ch. 13, p. 84 (row 13-2)**: for `σ > 1` and real `t`,
`log |ζ(σ + it)| = ∑_p ∑_{m ≥ 1} m⁻¹ p^{-mσ} cos(mt log p)`. -/
@[kb "davenport1980" "Ch 13, p. 84"]
theorem Davenport.log_norm_riemannZeta_eq_tsum {σ t : ℝ} (hσ : 1 < σ) :
    Real.log ‖riemannZeta (σ + t * I)‖ =
      ∑' p : Nat.Primes, ∑' m : ℕ,
        (p : ℝ) ^ (-((m + 1 : ℝ) * σ)) / (m + 1) * Real.cos ((m + 1 : ℝ) * t * Real.log p) := by
  have hs : 1 < ((σ : ℂ) + t * I).re := by simpa using hσ
  rw [Davenport.riemannZeta_eq_exp_tsum_primePow hs, Complex.norm_exp, Real.log_exp,
    Complex.re_tsum (by
      simpa only [tsum_primePow_eq hs] using
        (DirichletCharacter.summable_neg_log_one_sub_mul_prime_cpow (1 : DirichletCharacter ℂ 1) hs
          |>.congr fun p ↦ by simp [MulChar.one_apply (isUnit_of_subsingleton _)])
        )]
  refine tsum_congr fun p ↦ ?_
  have hsum : HasSum (fun m : ℕ ↦ ((p : ℂ) ^ (-((σ : ℂ) + t * I))) ^ (m + 1) / (m + 1))
      (-Complex.log (1 - (p : ℂ) ^ (-((σ : ℂ) + t * I)))) :=
    hasSum_taylorSeries_neg_log' (norm_primePow_lt_one hs p)
  rw [Complex.re_tsum hsum.summable]
  exact tsum_congr (re_primePow_term σ t p)

end NTKB
