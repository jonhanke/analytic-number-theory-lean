/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Apostol.Primes.Shapiro
import NTKB.Analytic.Apostol.Averages.DivisorSums
import NTKB.Analytic.Apostol.ArithmeticFunctions.GeneralizedConvolution

/-!
# Selberg's asymptotic formula (Apostol, Chapter 4, §4.11)

* **Theorem 4.17** (Tatuzawa–Iseki inversion). For `F : (0, ∞) → ℝ` and
  `G(x) = log x ∑_{n ≤ x} F(x/n)`, for `x ≥ 1`
  `F(x) log x + ∑_{n ≤ x} F(x/n) Λ(n) = ∑_{d ≤ x} μ(d) G(x/d)`.
  (Apostol allows complex `F`; the complex case is the real case applied to real and imaginary
  parts. Here `F : ℝ → ℝ`.)
* **Theorem 4.18** (Selberg's asymptotic formula).
  `ψ(x) log x + ∑_{n ≤ x} Λ(n) ψ(x/n) = 2x log x + O(x)` for `x ≥ 1`.

Proof of 4.18 (Apostol's): apply 4.17 to `F(x) = ψ(x) - (x - C - 1)` (`C` Euler's constant); by
Theorems 4.11 and 3.2(a) the corresponding `G` is `O(log² x) = O(√x)`, so the right side is
`O(∑_{d ≤ x} √(x/d)) = O(x)`; the left side is rearranged with Theorem 4.9.
-/

open Finset ArithmeticFunction Real Chebyshev
open scoped ArithmeticFunction.Moebius

namespace NTKB.Apostol

/-- `∑_{d ∣ k} μ(d) log(x/d) = [k = 1] log x + Λ(k)` (for `x > 0`, `k ≥ 1`). -/
theorem sum_divisors_moebius_mul_log_div (x : ℝ) (k : ℕ) :
    ∑ d ∈ k.divisors, (μ d : ℝ) * (Real.log x - Real.log d) =
      (if k = 1 then Real.log x else 0) + Λ k := by
  have h1 := sum_divisors_moebius (R := ℝ) k
  have h2 := sum_moebius_mul_log_eq (n := k)
  simp only [ArithmeticFunction.log_apply] at h2
  simp only [mul_sub, sum_sub_distrib, ← sum_mul]
  rw [h1, h2, ArithmeticFunction.one_apply]
  split_ifs <;> ring

/-- **Apostol, Theorem 4.17.** For `F : ℝ → ℝ` and `G(x) = log x ∑_{n ≤ x} F(x/n)`, for `x ≥ 1`,
`F(x) log x + ∑_{n ≤ x} F(x/n) Λ(n) = ∑_{d ≤ x} μ(d) G(x/d)`. -/
@[kb "apostol1976" "Thm 4.17, p. 99"]
theorem tatuzawa_iseki (F : ℝ → ℝ) {x : ℝ} (hx : 1 ≤ x) :
    F x * Real.log x + ∑ n ∈ Ioc 0 ⌊x⌋₊, F (x / n) * Λ n =
      ∑ d ∈ Ioc 0 ⌊x⌋₊, (μ d : ℝ) *
        (Real.log (x / d) * ∑ q ∈ Ioc 0 ⌊x / d⌋₊, F (x / d / q)) := by
  have hx0 : 0 < x := by linarith
  set N := ⌊x⌋₊
  have hN1 : 1 ≤ N := Nat.le_floor (by exact_mod_cast hx)
  -- left side as `∑_k F(x/k) ∑_{d ∣ k} μ(d) log(x/d)`
  have hL : F x * Real.log x + ∑ n ∈ Ioc 0 N, F (x / n) * Λ n =
      ∑ k ∈ Ioc 0 N, ∑ p ∈ k.divisorsAntidiagonal,
        (μ p.1 : ℝ) * (Real.log x - Real.log p.1) * F (x / (p.1 * p.2 : ℕ)) := by
    have : ∀ k ∈ Ioc 0 N, ∑ p ∈ k.divisorsAntidiagonal,
        (μ p.1 : ℝ) * (Real.log x - Real.log p.1) * F (x / (p.1 * p.2 : ℕ)) =
        F (x / k) * ((if k = 1 then Real.log x else 0) + Λ k) := by
      intro k hk
      rw [← sum_divisors_moebius_mul_log_div x k, mul_sum,
        Nat.sum_divisorsAntidiagonal (fun a b ↦ (μ a : ℝ) * (Real.log x - Real.log a) *
          F (x / (a * b : ℕ)))]
      refine sum_congr rfl fun d hd ↦ ?_
      rw [Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)]
      ring
    rw [sum_congr rfl this]
    simp only [mul_add, sum_add_distrib, mul_ite, mul_zero]
    rw [sum_ite_eq' (Ioc 0 N) 1, if_pos (by simp [hN1])]
    simp
  rw [hL, sum_Ioc_sum_divisorsAntidiagonal (fun a b ↦ (μ a : ℝ) * (Real.log x - Real.log a) *
    F (x / (a * b : ℕ))) N]
  refine sum_congr rfl fun d hd ↦ ?_
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (mem_Ioc.1 hd).1
  rw [Nat.floor_div_natCast, Real.log_div hx0.ne' hd0.ne', mul_sum, mul_sum]
  refine sum_congr rfl fun q _ ↦ ?_
  rw [Nat.cast_mul, div_div]
  ring

/-- `log y (log y + 5) ≤ 36 √y` for `y ≥ 1` (via `log y ≤ 4 y^{1/4}`). -/
theorem log_mul_log_add_five_le {y : ℝ} (hy : 1 ≤ y) :
    Real.log y * (Real.log y + 5) ≤ 36 * √y := by
  have h0 : 0 ≤ Real.log y := Real.log_nonneg hy
  have h1 : Real.log y ≤ y ^ (1 / 4 : ℝ) / (1 / 4) :=
    Real.log_le_rpow_div (by linarith) (by norm_num)
  set t := y ^ (1 / 4 : ℝ) with ht
  have ht2 : t ^ 2 = √y := by
    rw [Real.sqrt_eq_rpow, ht, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
    norm_num
  have ht1 : 1 ≤ t := Real.one_le_rpow hy (by norm_num)
  have h1' : Real.log y ≤ 4 * t := by linarith
  nlinarith

/-- The function `F(x) = ψ(x) - (x - C - 1)` of Apostol's proof of Theorem 4.18 has
`|∑_{n ≤ y} F(y/n)| ≤ log y + 5` for `y ≥ 1` (Theorems 4.11 and 3.2(a)). -/
theorem abs_sum_psi_sub_div_le {y : ℝ} (hy : 1 ≤ y) :
    |∑ n ∈ Ioc 0 ⌊y⌋₊, (ψ (y / n) - (y / n - eulerMascheroniConstant - 1))| ≤
      Real.log y + 5 := by
  have hy0 : 0 < y := by linarith
  have e : ∑ n ∈ Ioc 0 ⌊y⌋₊, (ψ (y / n) - (y / n - eulerMascheroniConstant - 1)) =
      ∑ n ∈ Ioc 0 ⌊y⌋₊, ψ (y / n) - y * ∑ n ∈ Ioc 0 ⌊y⌋₊, (1 / n : ℝ) +
        (eulerMascheroniConstant + 1) * ⌊y⌋₊ := by
    rw [sum_sub_distrib, mul_sum]
    have : ∑ n ∈ Ioc 0 ⌊y⌋₊, (y / n - eulerMascheroniConstant - 1) =
        ∑ n ∈ Ioc 0 ⌊y⌋₊, y * (1 / n : ℝ) - (eulerMascheroniConstant + 1) * ⌊y⌋₊ := by
      rw [show (eulerMascheroniConstant + 1) * (⌊y⌋₊ : ℝ) =
          ∑ n ∈ Ioc 0 ⌊y⌋₊, (eulerMascheroniConstant + 1) by
        rw [sum_const, Nat.card_Ioc, nsmul_eq_mul, Nat.sub_zero, mul_comm]]
      rw [← sum_sub_distrib]
      exact sum_congr rfl fun n _ ↦ by ring
    rw [this]; ring
  rw [e]
  have h1 := abs_le.1 (abs_sum_psi_div_sub_le hy)
  have h2 := abs_le.1 (abs_sum_inv_sub_log_sub_eulerMascheroni_le hy)
  have h3 := Nat.floor_le hy0.le
  have h4 := Nat.lt_floor_add_one y
  have hγ1 := eulerMascheroniConstant_lt_two_thirds
  have hγ0 : 0 < eulerMascheroniConstant := by
    have := one_half_lt_eulerMascheroniConstant; linarith
  have h2' : |y * ∑ n ∈ Ioc 0 ⌊y⌋₊, (1 / n : ℝ) - y * Real.log y - eulerMascheroniConstant * y|
      ≤ 2 := by
    have : y * ∑ n ∈ Ioc 0 ⌊y⌋₊, (1 / n : ℝ) - y * Real.log y - eulerMascheroniConstant * y =
        y * (∑ n ∈ Ioc 0 ⌊y⌋₊, (1 / n : ℝ) - Real.log y - eulerMascheroniConstant) := by ring
    rw [this, abs_mul, abs_of_pos hy0]
    calc y * |∑ n ∈ Ioc 0 ⌊y⌋₊, (1 / n : ℝ) - Real.log y - eulerMascheroniConstant|
        ≤ y * (2 / y) := mul_le_mul_of_nonneg_left
          (abs_sum_inv_sub_log_sub_eulerMascheroni_le hy) hy0.le
      _ = 2 := by field_simp
  rw [abs_le] at h2' ⊢
  constructor <;> nlinarith

/-- **Apostol, Theorem 4.18** (Selberg's asymptotic formula).
`ψ(x) log x + ∑_{n ≤ x} Λ(n) ψ(x/n) = 2x log x + O(x)` for `x ≥ 1`. -/
@[kb "apostol1976" "Thm 4.18, p. 100"]
theorem selberg_asymptotic_formula :
    ∃ K, ∀ x : ℝ, 1 ≤ x →
      |ψ x * Real.log x + ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n * ψ (x / n) - 2 * x * Real.log x| ≤ K * x := by
  obtain ⟨⟨M, hM⟩, ⟨c₁, hc₁, hψ⟩, -⟩ := apostol_thm_4_9
  refine ⟨72 + |M| + 2 + 2 * c₁, fun x hx ↦ ?_⟩
  have hx0 : 0 < x := by linarith
  set γ := eulerMascheroniConstant
  set D : ℝ → ℝ := fun y ↦ ψ y - (y - γ - 1) with hD
  have h417 := tatuzawa_iseki D hx
  -- the right side of 4.17 is `O(x)`
  set R := ∑ d ∈ Ioc 0 ⌊x⌋₊, (μ d : ℝ) *
    (Real.log (x / d) * ∑ q ∈ Ioc 0 ⌊x / d⌋₊, D (x / d / q))
  have hR : |R| ≤ 72 * x := by
    calc |R| ≤ ∑ d ∈ Ioc 0 ⌊x⌋₊, |(μ d : ℝ) *
          (Real.log (x / d) * ∑ q ∈ Ioc 0 ⌊x / d⌋₊, D (x / d / q))| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ d ∈ Ioc 0 ⌊x⌋₊, 36 * (√x * (1 / √(d : ℝ))) := by
          refine sum_le_sum fun d hd ↦ ?_
          have hd0 : (0 : ℝ) < d := by exact_mod_cast (mem_Ioc.1 hd).1
          have hdx : (d : ℝ) ≤ x := by
            have := Nat.floor_le hx0.le
            have : (d : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast (mem_Ioc.1 hd).2
            linarith
          have hy : 1 ≤ x / d := by rw [le_div_iff₀ hd0]; linarith
          have hl0 : 0 ≤ Real.log (x / d) := Real.log_nonneg hy
          have hS := abs_sum_psi_sub_div_le hy
          rw [abs_mul, abs_mul, abs_of_nonneg hl0]
          have hμ : |(μ d : ℝ)| ≤ 1 := by exact_mod_cast abs_moebius_le_one
          calc |(μ d : ℝ)| * (Real.log (x / d) * |∑ q ∈ Ioc 0 ⌊x / d⌋₊, D (x / d / q)|)
              ≤ 1 * (Real.log (x / d) * (Real.log (x / d) + 5)) := by
                refine mul_le_mul hμ (mul_le_mul_of_nonneg_left ?_ hl0)
                  (mul_nonneg hl0 (abs_nonneg _)) zero_le_one
                simpa [hD] using hS
            _ ≤ 36 * √(x / d) := by rw [one_mul]; exact log_mul_log_add_five_le hy
            _ = 36 * (√x * (1 / √(d : ℝ))) := by
                rw [Real.sqrt_div' _ hd0.le, mul_one_div]
      _ = 36 * √x * ∑ d ∈ Ioc 0 ⌊x⌋₊, 1 / √(d : ℝ) := by
          rw [mul_sum]; exact sum_congr rfl fun d _ ↦ by ring
      _ ≤ 36 * √x * (2 * √(⌊x⌋₊ : ℝ)) :=
          mul_le_mul_of_nonneg_left (sum_Ioc_inv_sqrt_le _) (by positivity)
      _ ≤ 36 * √x * (2 * √x) := by
          gcongr; exact Nat.floor_le hx0.le
      _ = 72 * x := by
          rw [show 36 * √x * (2 * √x) = 72 * (√x * √x) by ring, Real.mul_self_sqrt hx0.le]
  -- the left side of 4.17, rearranged
  have hLHS : D x * Real.log x + ∑ n ∈ Ioc 0 ⌊x⌋₊, D (x / n) * Λ n =
      (ψ x * Real.log x + ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n * ψ (x / n)) - x * Real.log x +
        (γ + 1) * Real.log x - x * ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / n + (γ + 1) * ψ x := by
    have : ∑ n ∈ Ioc 0 ⌊x⌋₊, D (x / n) * Λ n = ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n * ψ (x / n) -
        x * ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / n + (γ + 1) * ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n := by
      rw [mul_sum, mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
      refine sum_congr rfl fun n _ ↦ ?_
      simp only [hD]; ring
    rw [this]
    simp only [hD]
    rw [show ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n = ψ x from rfl]
    ring
  rw [hLHS] at h417
  have hM' := abs_le.1 (hM x hx)
  have hψx := hψ x hx
  have hψ0 := psi_nonneg x
  have hlog : Real.log x ≤ x := by
    have := Real.log_le_sub_one_of_pos hx0; linarith
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx
  have hγ1 := eulerMascheroniConstant_lt_two_thirds
  have hγ0 : 0 < γ := by have := one_half_lt_eulerMascheroniConstant; linarith
  have hRab := abs_le.1 hR
  have hMab := le_abs_self M
  have hMab' := neg_abs_le M
  -- `x ∑ Λ(n)/n = x log x + x·O(1)`
  have hxM : |x * ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / n - x * Real.log x| ≤ |M| * x := by
    rw [← mul_sub, abs_mul, abs_of_pos hx0, mul_comm]
    exact mul_le_mul_of_nonneg_right ((hM x hx).trans (le_abs_self M)) hx0.le
  have hxM' := abs_le.1 hxM
  rw [abs_le]
  constructor <;> nlinarith

end NTKB.Apostol
