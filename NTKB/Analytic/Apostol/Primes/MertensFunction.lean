/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Apostol.Primes.Selberg

/-!
# The partial sums of the Möbius function (Apostol, Chapter 4, §4.9)

`M(x) = ∑_{n ≤ x} μ(n)` (`NTKB.Apostol.mertens`) and `H(x) = ∑_{n ≤ x} μ(n) log n`
(`NTKB.Apostol.mertensLog`).

* Theorem 4.13: `M(x)/x → 0` iff `H(x)/(x log x) → 0`;
* Theorem 4.15: `M(x) = o(x)` implies `ψ(x) ~ x`, by Apostol's proof: with
  `f = σ₀ - log - 2C` one has `⌊x⌋ - ψ(x) - 2C = ∑_{qd ≤ x} μ(d) f(q)`, the partial sums of `f` are
  `O(√x)` by Dirichlet's divisor theorem (3.3) and Theorem 3.15, and the hyperbola identity (3.17)
  shows the double sum is `o(x)`;
* Theorem 4.16: `∑_{n ≤ x} μ(n)/n → 0` implies `ψ(x) ~ x` (via `M(x) = o(x)`, by partial
  summation and a Cesàro mean in place of Apostol's integral).

The prime number theorem appears in the form `ψ(x)/x → 1` (Apostol's Theorem 4.4 equivalent).
-/

open Finset ArithmeticFunction Real Chebyshev Filter Topology
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta ArithmeticFunction.sigma

namespace NTKB.Apostol

/-- Mertens' function `M(x) = ∑_{n ≤ x} μ(n)` (Apostol, §4.9). -/
noncomputable def mertens (x : ℝ) : ℝ := ∑ n ∈ Ioc 0 ⌊x⌋₊, (μ n : ℝ)

/-- `H(x) = ∑_{n ≤ x} μ(n) log n` (Apostol, §4.9). -/
noncomputable def mertensLog (x : ℝ) : ℝ := ∑ n ∈ Ioc 0 ⌊x⌋₊, (μ n : ℝ) * Real.log n

theorem abs_sum_moebius_le (N : ℕ) : |∑ n ∈ Ioc 0 N, (μ n : ℝ)| ≤ N := by
  calc |∑ n ∈ Ioc 0 N, (μ n : ℝ)| ≤ ∑ n ∈ Ioc 0 N, |(μ n : ℝ)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ Ioc 0 N, (1 : ℝ) := sum_le_sum fun n _ ↦ by exact_mod_cast abs_moebius_le_one
    _ = N := by simp

theorem abs_mertens_le {x : ℝ} (hx : 0 ≤ x) : |mertens x| ≤ x :=
  (abs_sum_moebius_le _).trans (Nat.floor_le hx)

/-- Partial summation: `H(N) = M(N) log N - ∑_{n < N} M(n) (log(n+1) - log n)`. -/
theorem sum_moebius_mul_log_eq (N : ℕ) :
    ∑ n ∈ Ioc 0 N, (μ n : ℝ) * Real.log n =
      (∑ n ∈ Ioc 0 N, (μ n : ℝ)) * Real.log N -
        ∑ n ∈ range N, (∑ m ∈ Ioc 0 n, (μ m : ℝ)) * (Real.log (n + 1) - Real.log n) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_Ioc_succ_top (Nat.zero_le _), ih, sum_Ioc_succ_top (Nat.zero_le _), sum_range_succ]
    push_cast
    ring

/-- `|H(x) - M(x) log x| ≤ x + 1` for `x ≥ 1`. -/
theorem abs_mertensLog_sub_le {x : ℝ} (hx : 1 ≤ x) :
    |mertensLog x - mertens x * Real.log x| ≤ x + 1 := by
  have hx0 : 0 < x := by linarith
  set N := ⌊x⌋₊
  have hN1 : 1 ≤ N := Nat.le_floor (by exact_mod_cast hx)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hNx : (N : ℝ) ≤ x := Nat.floor_le hx0.le
  rw [mertensLog, mertens, sum_moebius_mul_log_eq]
  set MN := ∑ n ∈ Ioc 0 N, (μ n : ℝ)
  set E := ∑ n ∈ range N, (∑ m ∈ Ioc 0 n, (μ m : ℝ)) * (Real.log (n + 1) - Real.log n)
  have hE : |E| ≤ N := by
    calc |E| ≤ ∑ n ∈ range N, |(∑ m ∈ Ioc 0 n, (μ m : ℝ)) * (Real.log (n + 1) - Real.log n)| :=
          abs_sum_le_sum_abs _ _
      _ ≤ ∑ n ∈ range N, (1 : ℝ) := by
          refine sum_le_sum fun n _ ↦ ?_
          rcases Nat.eq_zero_or_pos n with rfl | hn
          · simp
          have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
          have hl : 0 ≤ Real.log (n + 1) - Real.log n :=
            sub_nonneg.2 (Real.log_le_log hn0 (by linarith))
          have hl2 : Real.log (n + 1) - Real.log n ≤ 1 / n := by
            rw [← Real.log_div (by positivity) hn0.ne', add_div, div_self hn0.ne']
            have := Real.log_le_sub_one_of_pos (show 0 < 1 + 1 / (n : ℝ) by positivity)
            linarith
          rw [abs_mul, abs_of_nonneg hl]
          calc |∑ m ∈ Ioc 0 n, (μ m : ℝ)| * (Real.log (n + 1) - Real.log n)
              ≤ n * (1 / n) := mul_le_mul (abs_sum_moebius_le n) hl2 hl (Nat.cast_nonneg _)
            _ = 1 := by field_simp
      _ = N := by simp
  have hM : |MN| ≤ N := abs_sum_moebius_le N
  have hl : 0 ≤ Real.log x - Real.log N := sub_nonneg.2 (Real.log_le_log hN0 hNx)
  have hl2 : Real.log x - Real.log N ≤ 1 / N := by
    have h1 := Nat.lt_floor_add_one x
    have : Real.log x - Real.log N ≤ x / N - 1 := by
      rw [← Real.log_div hx0.ne' hN0.ne']
      exact Real.log_le_sub_one_of_pos (by positivity)
    have : x / N - 1 ≤ 1 / N := by
      rw [div_sub_one hN0.ne', div_le_div_iff_of_pos_right hN0]; linarith
    linarith
  have hMl : |MN * (Real.log x - Real.log N)| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg hl]
    calc |MN| * (Real.log x - Real.log N) ≤ N * (1 / N) := mul_le_mul hM hl2 hl (by positivity)
      _ = 1 := by field_simp
  have : MN * Real.log N - E - MN * Real.log x = -(MN * (Real.log x - Real.log N)) - E := by ring
  rw [this]
  calc |-(MN * (Real.log x - Real.log N)) - E| ≤ |MN * (Real.log x - Real.log N)| + |E| := by
        rw [abs_sub_comm]
        refine (abs_sub _ _).trans ?_
        rw [abs_neg, add_comm]
    _ ≤ 1 + N := add_le_add hMl hE
    _ ≤ x + 1 := by linarith

/-- **Apostol, Theorem 4.13.** `M(x)/x → 0` if and only if `H(x)/(x log x) → 0`. -/
@[kb "apostol1976" "Thm 4.13, p. 91"]
theorem tendsto_mertens_div_iff :
    Tendsto (fun x ↦ mertens x / x) atTop (𝓝 0) ↔
      Tendsto (fun x ↦ mertensLog x / (x * Real.log x)) atTop (𝓝 0) := by
  have hdiff : Tendsto (fun x ↦ mertens x / x - mertensLog x / (x * Real.log x)) atTop (𝓝 0) := by
    have hlim : Tendsto (fun x ↦ 2 / Real.log x) atTop (𝓝 0) := by
      have := (Real.tendsto_log_atTop.inv_tendsto_atTop).const_mul 2
      simpa [div_eq_mul_inv] using this
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [eventually_gt_atTop 1] with x hx
    have hx0 : 0 < x := by linarith
    have hl : 0 < Real.log x := Real.log_pos hx
    have e : mertens x / x - mertensLog x / (x * Real.log x) =
        -(mertensLog x - mertens x * Real.log x) / (x * Real.log x) := by
      field_simp; ring
    rw [e, Real.norm_eq_abs, abs_div, abs_neg, abs_of_pos (mul_pos hx0 hl),
      div_le_div_iff₀ (mul_pos hx0 hl) hl]
    have := abs_mertensLog_sub_le hx.le
    have h2 : |mertensLog x - mertens x * Real.log x| * Real.log x ≤ (x + 1) * Real.log x :=
      mul_le_mul_of_nonneg_right this hl.le
    nlinarith
  constructor
  · intro h
    simpa using h.sub hdiff
  · intro h
    simpa using hdiff.add h

end NTKB.Apostol
