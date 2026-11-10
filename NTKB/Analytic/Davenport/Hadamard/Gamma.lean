/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Crude bounds for the Gamma function

Davenport (Ch. 12, p. 79) bounds `|Γ(s/2)|` for `σ ≥ 1/2` by Stirling's formula:
`|Γ(s/2)| < exp(C|s| log|s|)`. Only this crude consequence is needed; we prove it directly:

* `NTKB.norm_Gamma_le_Gamma_re`: `|Γ(w)| ≤ Γ(Re w)` for `Re w > 0` (Euler's integral);
* `NTKB.Gamma_le_rpow`: `Γ(x) ≤ 20 (x + 1)^{x + 1}` for real `x ≥ 1/4` (monotonicity of `Γ` on
  `[2, ∞)` and `n! ≤ n^n`).
-/

open Real Set MeasureTheory

namespace NTKB

/-- `|Γ(w)| ≤ Γ(Re w)` for `Re w > 0`. -/
theorem norm_Gamma_le_Gamma_re {w : ℂ} (hw : 0 < w.re) :
    ‖Complex.Gamma w‖ ≤ Real.Gamma w.re := by
  rw [Complex.Gamma_eq_integral hw, Real.Gamma_eq_integral hw, Complex.GammaIntegral]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx ↦ ?_
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp

/-- `Γ(x) ≤ 20 (x + 1)^{x+1}` for `x ≥ 1/4`. -/
theorem Gamma_le_rpow {x : ℝ} (hx : 1 / 4 ≤ x) : Real.Gamma x ≤ 20 * (x + 1) ^ (x + 1) := by
  have hx1 : 1 ≤ (x + 1) ^ (x + 1) := Real.one_le_rpow (by linarith) (by linarith)
  rcases lt_or_ge x 2 with h | h
  · -- `Γ(x) = Γ(x + 2) / (x (x + 1)) ≤ Γ(4) / (5/16)`
    have hx0 : 0 < x := by linarith
    have h2 : Real.Gamma (x + 2) = x * (x + 1) * Real.Gamma x := by
      rw [show x + 2 = (x + 1) + 1 by ring, Real.Gamma_add_one (by linarith),
        Real.Gamma_add_one hx0.ne']
      ring
    have h4 : Real.Gamma (x + 2) ≤ Real.Gamma 4 :=
      Real.Gamma_strictMonoOn_Ici.monotoneOn (by simp; linarith) (by simp; norm_num)
        (by linarith)
    have hG4 : Real.Gamma 4 = 6 := by
      rw [show (4 : ℝ) = (3 : ℕ) + 1 by norm_num, Real.Gamma_nat_eq_factorial]
      norm_num [Nat.factorial]
    have hprod : 5 / 16 ≤ x * (x + 1) := by nlinarith
    have hG : 0 < Real.Gamma x := Real.Gamma_pos_of_pos hx0
    have : Real.Gamma x ≤ 20 := by nlinarith
    nlinarith
  · -- `Γ(x) ≤ Γ(n + 1) = n! ≤ n^n ≤ (x+1)^{x+1}` with `n = ⌈x⌉`
    set n := ⌈x⌉₊
    have hxn : x ≤ n := Nat.le_ceil x
    have hnx : (n : ℝ) < x + 1 := Nat.ceil_lt_add_one (by linarith)
    have hmono : Real.Gamma x ≤ Real.Gamma (n + 1) :=
      Real.Gamma_strictMonoOn_Ici.monotoneOn (by simpa using h) (by simp; linarith)
        (by linarith)
    rw [Real.Gamma_nat_eq_factorial] at hmono
    have hfac : ((n.factorial : ℕ) : ℝ) ≤ (n : ℝ) ^ n := by exact_mod_cast Nat.factorial_le_pow n
    have hpow : (n : ℝ) ^ n ≤ (x + 1) ^ (x + 1) := by
      rw [← Real.rpow_natCast]
      calc (n : ℝ) ^ (n : ℝ) ≤ (x + 1) ^ (n : ℝ) :=
            Real.rpow_le_rpow (by positivity) hnx.le (by positivity)
        _ ≤ (x + 1) ^ (x + 1) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith) hnx.le
    linarith

end NTKB
