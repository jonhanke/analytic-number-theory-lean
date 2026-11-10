/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Apostol.Averages.Hyperbola
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.ZetaValues
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Mathlib.Analysis.PSeries

/-!
# Average orders of `d(n)`, `σ(n)` and `φ(n)` (Apostol, Chapter 3, §§3.4–3.7)

All error terms are explicit: `f(x) = g(x) + O(h(x))` is stated as
`∃ C, ∀ x ≥ x₀, |f(x) - g(x)| ≤ C h(x)` (Apostol's definition of `O`, §3.2).

* Theorem 3.2 (a): `∑_{n ≤ x} 1/n = log x + C + O(1/x)`, `C` Euler's constant (Mathlib has
  `H_n - log n → γ` and monotonicity, no error term);
* Theorem 3.2 (d) for `α = 0, 1`: `∑_{n ≤ x} 1 = x + O(1)`, `∑_{n ≤ x} n = x²/2 + O(x)`;
* Theorem 3.3 (Dirichlet): `∑_{n ≤ x} d(n) = x log x + (2C - 1)x + O(√x)`, by Apostol's
  hyperbola argument (Theorem 3.17 with `a = b = √x`);
* Theorem 3.4: `∑_{n ≤ x} σ(n) = (π²/12) x² + O(x log x)`;
* Theorem 3.7: `∑_{n ≤ x} φ(n) = (3/π²) x² + O(x log x)`, with `∑ μ(n)/n² = 6/π²`
  (from Mathlib's `L(μ, s) L(u, s) = 1`) and `φ = μ * N` (Theorem 2.3).

For 3.4 and 3.7 the book says "for all `x ≥ 1`"; since `x log x = 0` at `x = 1` the bound is read
for `x ≥ 2` (at `x = 1` the left side is not `0`).
-/

open Finset ArithmeticFunction Real
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta ArithmeticFunction.sigma
open scoped LSeries.notation

namespace NTKB.Apostol

/-! ## Elementary sums -/

theorem Icc_one_eq_Ioc_zero (N : ℕ) : Icc 1 N = Ioc 0 N := by
  ext n; simp [Nat.one_le_iff_ne_zero, Nat.pos_iff_ne_zero]

/-- `∑_{n ≤ x} 1/n` is the harmonic number `H_{⌊x⌋}`. -/
theorem sum_Ioc_inv_eq_harmonic (N : ℕ) : ∑ n ∈ Ioc 0 N, (1 / n : ℝ) = harmonic N := by
  rw [harmonic_eq_sum_Icc, Icc_one_eq_Ioc_zero]
  push_cast
  simp

/-- **Apostol, Theorem 3.2 (a).** For `x ≥ 1`, `∑_{n ≤ x} 1/n = log x + C + O(1/x)` with `C`
Euler's constant; explicitly the error is at most `2/x`. -/
@[kb "apostol1976" "Thm 3.2(a), p. 55"]
theorem abs_sum_inv_sub_log_sub_eulerMascheroni_le {x : ℝ} (hx : 1 ≤ x) :
    |∑ n ∈ Ioc 0 ⌊x⌋₊, (1 / n : ℝ) - Real.log x - eulerMascheroniConstant| ≤ 2 / x := by
  set N := ⌊x⌋₊ with hNdef
  have hN1 : 1 ≤ N := Nat.le_floor (by exact_mod_cast hx)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hNx : (N : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hxN : x < N + 1 := Nat.lt_floor_add_one x
  rw [sum_Ioc_inv_eq_harmonic]
  have h1 := eulerMascheroniSeq_lt_eulerMascheroniConstant N
  have h2 := eulerMascheroniConstant_lt_eulerMascheroniSeq' N
  rw [eulerMascheroniSeq] at h1
  rw [eulerMascheroniSeq', if_neg (by omega)] at h2
  have hl1 : Real.log N ≤ Real.log x := Real.log_le_log hN0 hNx
  have hl2 : Real.log x ≤ Real.log (N + 1) := Real.log_le_log (by linarith) hxN.le
  have hl3 : Real.log (N + 1) - Real.log N ≤ 1 / N := by
    rw [← Real.log_div (by positivity) hN0.ne', add_div, div_self hN0.ne']
    have := Real.log_le_sub_one_of_pos (show 0 < 1 + 1 / (N : ℝ) by positivity)
    linarith
  have hNx2 : 1 / (N : ℝ) ≤ 2 / x := by
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    rw [div_le_div_iff₀ hN0 (by linarith)]
    linarith
  rw [abs_le]
  constructor <;> linarith

/-- **Apostol, Theorem 3.2 (d)**, case `α = 0`: `∑_{n ≤ x} 1 = ⌊x⌋ = x + O(1)`. -/
theorem abs_floor_sub_le {y : ℝ} (hy : 0 ≤ y) : |(⌊y⌋₊ : ℝ) - y| ≤ 1 := by
  have h1 := Nat.floor_le hy
  have h2 := Nat.lt_floor_add_one y
  rw [abs_le]; constructor <;> linarith

theorem sum_Ioc_id_mul_two (N : ℕ) : (∑ n ∈ Ioc 0 N, (n : ℝ)) * 2 = N * (N + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_Ioc_succ_top (Nat.zero_le _), add_mul, ih]
    push_cast; ring

/-- **Apostol, Theorem 3.2 (d)**, case `α = 1`: `∑_{n ≤ x} n = x²/2 + O(x)`; explicitly the error
is at most `x` for `x ≥ 0`. -/
@[kb "apostol1976" "Thm 3.2(d), p. 55"]
theorem abs_sum_id_sub_sq_div_two_le {y : ℝ} (hy : 0 ≤ y) :
    |∑ n ∈ Ioc 0 ⌊y⌋₊, (n : ℝ) - y ^ 2 / 2| ≤ y := by
  have hs := sum_Ioc_id_mul_two ⌊y⌋₊
  have h1 := Nat.floor_le hy
  have h2 := Nat.lt_floor_add_one y
  have h0 : (0 : ℝ) ≤ ⌊y⌋₊ := Nat.cast_nonneg _
  rw [abs_le]; constructor <;> nlinarith

/-! ## Theorem 3.3: the divisor function -/

theorem sum_Ioc_zeta_real (N : ℕ) : ∑ m ∈ Ioc 0 N, (ζ : ArithmeticFunction ℝ) m = N := by
  have := sum_Ioc_zeta N
  rw [← Nat.cast_inj (R := ℝ), Nat.cast_sum] at this
  simpa [natCoe_apply] using this

theorem natCoe_sigma_zero_eq : ((σ 0 : ArithmeticFunction ℕ) : ArithmeticFunction ℝ) =
    (ζ : ArithmeticFunction ℝ) * ζ := by
  rw [← zeta_mul_pow_eq_sigma, pow_zero_eq_zeta, natCoe_mul]

/-- **Apostol, Theorem 3.3** (Dirichlet's divisor theorem). For `x ≥ 1`,
`∑_{n ≤ x} d(n) = x log x + (2C - 1) x + O(√x)`, `C` Euler's constant; explicitly the error is at
most `8 √x`. -/
@[kb "apostol1976" "Thm 3.3, p. 57"]
theorem abs_sum_sigma_zero_sub_le {x : ℝ} (hx : 1 ≤ x) :
    |∑ n ∈ Ioc 0 ⌊x⌋₊, (σ 0 n : ℝ) -
        (x * Real.log x + (2 * eulerMascheroniConstant - 1) * x)| ≤ 8 * √x := by
  have hx0 : 0 < x := by linarith
  set s := √x with hs
  have hs0 : 0 < s := Real.sqrt_pos.2 hx0
  have hss : s * s = x := Real.mul_self_sqrt hx0.le
  have hs1 : 1 ≤ s := by rw [hs]; exact Real.one_le_sqrt.2 hx
  -- hyperbola identity with `a = b = √x`, `f = g = u`
  have hhyp := sum_mul_eq_hyperbola (ζ : ArithmeticFunction ℝ) ζ hs0 hs0 hss
  have hL : ∑ n ∈ Ioc 0 ⌊x⌋₊, (σ 0 n : ℝ) =
      ∑ n ∈ Ioc 0 ⌊x⌋₊, ((ζ : ArithmeticFunction ℝ) * ζ) n := by
    rw [← natCoe_sigma_zero_eq]; simp [natCoe_apply]
  set N := ⌊s⌋₊ with hNdef
  have hN1 : 1 ≤ N := Nat.le_floor (by exact_mod_cast hs1)
  have hNs : (N : ℝ) ≤ s := Nat.floor_le hs0.le
  have hsN : s < N + 1 := Nat.lt_floor_add_one s
  set A := ∑ n ∈ Ioc 0 N, (⌊x / n⌋₊ : ℝ) with hA
  set B := ∑ n ∈ Ioc 0 N, (1 / n : ℝ) with hB
  have hcoef : ∀ n ∈ Ioc 0 N, (ζ : ArithmeticFunction ℝ) n = 1 := fun n hn ↦ by
    simp [natCoe_apply, zeta_apply, (mem_Ioc.1 hn).1.ne']
  have hS : ∑ n ∈ Ioc 0 ⌊x⌋₊, (σ 0 n : ℝ) = 2 * A - (N : ℝ) ^ 2 := by
    rw [hL, hhyp]
    have e1 : ∑ n ∈ Ioc 0 N, (ζ : ArithmeticFunction ℝ) n *
        ∑ m ∈ Ioc 0 ⌊x / n⌋₊, (ζ : ArithmeticFunction ℝ) m = A := by
      rw [hA]; refine sum_congr rfl fun n hn ↦ ?_
      rw [hcoef n hn, sum_Ioc_zeta_real, one_mul]
    have e2 : ∑ n ∈ Ioc 0 N, (ζ : ArithmeticFunction ℝ) n = N := sum_Ioc_zeta_real N
    rw [e1, e2]; ring
  -- `A = x B - E₂` with `0 ≤ E₂ ≤ N`
  have hA1 : A ≤ x * B := by
    rw [hA, hB, mul_sum]
    refine sum_le_sum fun n hn ↦ ?_
    rw [mul_one_div]
    exact Nat.floor_le (div_nonneg hx0.le (Nat.cast_nonneg _))
  have hA2 : x * B - N ≤ A := by
    have : x * B - N = ∑ n ∈ Ioc 0 N, (x / n - 1) := by
      rw [hB, mul_sum, sum_sub_distrib]; simp [div_eq_mul_inv]
    rw [this, hA]
    refine sum_le_sum fun n hn ↦ ?_
    have := Nat.lt_floor_add_one (x / n)
    linarith
  -- `B = log √x + C + E₁` with `|E₁| ≤ 2/√x`
  have hB1 := abs_sum_inv_sub_log_sub_eulerMascheroni_le hs1
  rw [← hNdef, ← hB] at hB1
  have hlog : Real.log s = Real.log x / 2 := by
    rw [hs, Real.log_sqrt hx0.le]
  rw [hlog] at hB1
  have hxB : |x * B - x * Real.log x / 2 - eulerMascheroniConstant * x| ≤ 2 * s := by
    have : x * B - x * Real.log x / 2 - eulerMascheroniConstant * x =
        x * (B - Real.log x / 2 - eulerMascheroniConstant) := by ring
    rw [this, abs_mul, abs_of_pos hx0]
    calc x * |B - Real.log x / 2 - eulerMascheroniConstant| ≤ x * (2 / s) :=
          mul_le_mul_of_nonneg_left hB1 hx0.le
      _ = 2 * s := by rw [← hss]; field_simp
  have hN2 : (N : ℝ) ^ 2 ≤ x := by nlinarith
  have hN3 : x - 2 * s ≤ (N : ℝ) ^ 2 := by nlinarith
  rw [hS, abs_le]
  rw [abs_le] at hxB
  constructor <;> nlinarith

/-! ## Tails of `∑ c(n)/n²` -/

/-- If `|c(n)| ≤ 1/n²` then `|∑' c - ∑_{n ≤ N} c(n)| ≤ 1/N` (Apostol, Theorem 3.2 (c) for
`s = 2`). -/
theorem abs_tsum_sub_sum_Ioc_le {c : ℕ → ℝ} (hc : ∀ n, |c n| ≤ 1 / (n : ℝ) ^ 2) (hc0 : c 0 = 0)
    {N : ℕ} (hN : N ≠ 0) :
    |∑' n, c n - ∑ n ∈ Ioc 0 N, c n| ≤ 1 / N := by
  have hsum2 : Summable fun n : ℕ ↦ 1 / (n : ℝ) ^ 2 := Real.summable_one_div_nat_pow.2 one_lt_two
  have hsum : Summable c := Summable.of_norm_bounded hsum2 (fun n ↦ by simpa using hc n)
  have hsplit := hsum.sum_add_tsum_nat_add (N + 1)
  have hrange : ∑ i ∈ range (N + 1), c i = ∑ n ∈ Ioc 0 N, c n := by
    rw [range_eq_Ico, ← Icc_one_eq_Ioc_zero, sum_eq_sum_Ico_succ_bot (by omega), hc0, zero_add]
    rfl
  rw [← hsplit, hrange, add_sub_cancel_left]
  have htail : Summable fun n ↦ 1 / ((n + (N + 1) : ℕ) : ℝ) ^ 2 :=
    (summable_nat_add_iff (N + 1)).2 hsum2
  calc |∑' n, c (n + (N + 1))| ≤ ∑' n, |c (n + (N + 1))| := by
        have := (summable_nat_add_iff (N + 1)).2 hsum.abs
        simpa [Real.norm_eq_abs] using norm_tsum_le_tsum_norm (f := fun n ↦ c (n + (N + 1)))
          (by simpa [Real.norm_eq_abs] using this)
    _ ≤ ∑' n, 1 / ((n + (N + 1) : ℕ) : ℝ) ^ 2 :=
        ((summable_nat_add_iff (N + 1)).2 hsum.abs).tsum_le_tsum (fun n ↦ hc _) htail
    _ ≤ 1 / N := by
        refine tsum_le_of_sum_range_le (fun n ↦ by positivity) fun k ↦ ?_
        have := sum_Ioc_inv_sq_le_sub (α := ℝ) hN (show N ≤ N + k by omega)
        calc ∑ i ∈ range k, 1 / ((i + (N + 1) : ℕ) : ℝ) ^ 2
            = ∑ i ∈ Ioc N (N + k), ((i : ℝ) ^ 2)⁻¹ := by
              clear this
              induction k with
              | zero => simp
              | succ k ih =>
                rw [sum_range_succ, ih, show N + (k + 1) = (N + k) + 1 by ring,
                  sum_Ioc_succ_top (by omega), one_div, show k + (N + 1) = N + k + 1 by ring]
          _ ≤ (N : ℝ)⁻¹ - ((N + k : ℕ) : ℝ)⁻¹ := this
          _ ≤ 1 / N := by rw [one_div]; linarith [inv_nonneg.2 (Nat.cast_nonneg (α := ℝ) (N + k))]

/-! ## Theorem 3.4: the sum of divisors -/

/-- `∑_{n ≤ x} 1/n ≤ 1 + log x` (Mathlib's `harmonic_floor_le_one_add_log`). -/
theorem sum_Ioc_inv_le_one_add_log {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ Ioc 0 ⌊x⌋₊, (1 / n : ℝ) ≤ 1 + Real.log x := by
  rw [sum_Ioc_inv_eq_harmonic]; exact harmonic_floor_le_one_add_log x hx

/-- The common step of Theorems 3.4 and 3.7: if `|w(d)| ≤ 1` then
`∑_{d ≤ x} w(d) ∑_{q ≤ x/d} q = (x²/2) ∑_{d ≤ x} w(d)/d² + O(x log x)`. -/
theorem abs_sum_mul_sum_id_sub_le {w : ℕ → ℝ} (hw : ∀ n, |w n| ≤ 1) {x : ℝ} (hx : 1 ≤ x) :
    |∑ d ∈ Ioc 0 ⌊x⌋₊, w d * ∑ q ∈ Ioc 0 ⌊x / d⌋₊, (q : ℝ) -
        x ^ 2 / 2 * ∑ d ∈ Ioc 0 ⌊x⌋₊, w d / (d : ℝ) ^ 2| ≤ x * (1 + Real.log x) := by
  have hx0 : 0 < x := by linarith
  rw [mul_sum, ← sum_sub_distrib]
  calc |∑ d ∈ Ioc 0 ⌊x⌋₊, (w d * ∑ q ∈ Ioc 0 ⌊x / d⌋₊, (q : ℝ) - x ^ 2 / 2 * (w d / (d : ℝ) ^ 2))|
      ≤ ∑ d ∈ Ioc 0 ⌊x⌋₊, |w d * ∑ q ∈ Ioc 0 ⌊x / d⌋₊, (q : ℝ) - x ^ 2 / 2 * (w d / (d : ℝ) ^ 2)| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ Ioc 0 ⌊x⌋₊, x * (1 / d) := by
        refine sum_le_sum fun d hd ↦ ?_
        have hd0 : (0 : ℝ) < d := by exact_mod_cast (mem_Ioc.1 hd).1
        have h := abs_sum_id_sub_sq_div_two_le (div_nonneg hx0.le hd0.le)
        have e : w d * ∑ q ∈ Ioc 0 ⌊x / d⌋₊, (q : ℝ) - x ^ 2 / 2 * (w d / (d : ℝ) ^ 2) =
            w d * (∑ q ∈ Ioc 0 ⌊x / d⌋₊, (q : ℝ) - (x / d) ^ 2 / 2) := by
          field_simp
        rw [e, abs_mul]
        calc |w d| * |∑ q ∈ Ioc 0 ⌊x / d⌋₊, (q : ℝ) - (x / d) ^ 2 / 2| ≤ 1 * (x / d) :=
              mul_le_mul (hw d) h (abs_nonneg _) zero_le_one
          _ = x * (1 / d) := by ring
    _ = x * ∑ d ∈ Ioc 0 ⌊x⌋₊, (1 / d : ℝ) := by rw [mul_sum]
    _ ≤ x * (1 + Real.log x) := mul_le_mul_of_nonneg_left (sum_Ioc_inv_le_one_add_log hx) hx0.le

/-- For `x ≥ 2`, `x (1 + log x) ≤ 3 x log x`. -/
theorem one_add_log_le {x : ℝ} (hx : 2 ≤ x) : x * (1 + Real.log x) ≤ 3 * (x * Real.log x) := by
  have h2 : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  have h3 : (1 : ℝ) / 2 < Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  nlinarith

theorem natCoe_sigma_one_eq : ((σ 1 : ArithmeticFunction ℕ) : ArithmeticFunction ℝ) =
    (ζ : ArithmeticFunction ℝ) * ((ArithmeticFunction.id : ArithmeticFunction ℕ) :
      ArithmeticFunction ℝ) := by
  rw [← zeta_mul_pow_eq_sigma, pow_one_eq_id, natCoe_mul]

/-- **Apostol, Theorem 3.4.** `∑_{n ≤ x} σ(n) = (π²/12) x² + O(x log x)`; explicitly the error is
at most `5 x log x` for `x ≥ 2`. -/
@[kb "apostol1976" "Thm 3.4, p. 60"]
theorem abs_sum_sigma_one_sub_le {x : ℝ} (hx : 2 ≤ x) :
    |∑ n ∈ Ioc 0 ⌊x⌋₊, (σ 1 n : ℝ) - π ^ 2 / 12 * x ^ 2| ≤ 5 * (x * Real.log x) := by
  have hx1 : 1 ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  -- `∑ σ(n) = ∑_{d ≤ x} ∑_{q ≤ x/d} q`
  have hS : ∑ n ∈ Ioc 0 ⌊x⌋₊, (σ 1 n : ℝ) =
      ∑ d ∈ Ioc 0 ⌊x⌋₊, (1 : ℝ) * ∑ q ∈ Ioc 0 ⌊x / d⌋₊, (q : ℝ) := by
    have : ∑ n ∈ Ioc 0 ⌊x⌋₊, (σ 1 n : ℝ) = ∑ n ∈ Ioc 0 ⌊x⌋₊,
        ((ζ : ArithmeticFunction ℝ) * ((ArithmeticFunction.id : ArithmeticFunction ℕ) :
          ArithmeticFunction ℝ)) n := by
      rw [← natCoe_sigma_one_eq]; simp [natCoe_apply]
    rw [this, sum_Ioc_mul_eq_sum_sum]
    refine sum_congr rfl fun d hd ↦ ?_
    rw [natCoe_apply, zeta_apply_ne (mem_Ioc.1 hd).1.ne', ← Nat.floor_div_natCast]
    simp [natCoe_apply, ArithmeticFunction.id_apply]
  have hmain := abs_sum_mul_sum_id_sub_le (w := fun _ ↦ 1) (fun _ ↦ by simp) hx1
  rw [← hS] at hmain
  -- `∑_{d ≤ x} 1/d² = π²/6 + O(1/x)`
  have hN1 : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx1)
  have htail := abs_tsum_sub_sum_Ioc_le (c := fun n ↦ 1 / (n : ℝ) ^ 2)
    (fun n ↦ by rw [abs_of_nonneg (by positivity)]) (by simp) (N := ⌊x⌋₊) (by omega)
  rw [hasSum_zeta_two.tsum_eq] at htail
  have hNx : 1 / (⌊x⌋₊ : ℝ) ≤ 2 / x := by
    have h1 := Nat.lt_floor_add_one x
    have h0 : (0 : ℝ) < ⌊x⌋₊ := by exact_mod_cast hN1
    have h2 : (1 : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast hN1
    rw [div_le_div_iff₀ h0 hx0]; linarith
  have hx2 : x ^ 2 / 2 * (2 / x) = x := by field_simp
  have hlog := one_add_log_le hx
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  simp only [one_div] at hmain htail hNx
  set T := ∑ d ∈ Ioc 0 ⌊x⌋₊, ((d : ℝ) ^ 2)⁻¹
  have hT : |x ^ 2 / 2 * T - π ^ 2 / 12 * x ^ 2| ≤ x := by
    have : x ^ 2 / 2 * T - π ^ 2 / 12 * x ^ 2 = -(x ^ 2 / 2 * (π ^ 2 / 6 - T)) := by ring
    rw [this, abs_neg, abs_mul, abs_of_nonneg (by positivity)]
    calc x ^ 2 / 2 * |π ^ 2 / 6 - T| ≤ x ^ 2 / 2 * (2 / x) :=
          mul_le_mul_of_nonneg_left (htail.trans (by simpa [one_div] using hNx)) (by positivity)
      _ = x := hx2
  calc |∑ n ∈ Ioc 0 ⌊x⌋₊, (σ 1 n : ℝ) - π ^ 2 / 12 * x ^ 2|
      ≤ |∑ n ∈ Ioc 0 ⌊x⌋₊, (σ 1 n : ℝ) - x ^ 2 / 2 * T| + |x ^ 2 / 2 * T - π ^ 2 / 12 * x ^ 2| :=
        abs_sub_le _ _ _
    _ ≤ x * (1 + Real.log x) + x := add_le_add hmain hT
    _ ≤ 5 * (x * Real.log x) := by
        have : x ≤ 2 * (x * Real.log x) := by
          have h3 : (1 : ℝ) / 2 < Real.log 2 := by have := Real.log_two_gt_d9; linarith
          have h2 : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx
          nlinarith
        linarith

/-! ## Theorem 3.7: Euler's totient -/

/-- **Apostol, Theorem 2.3.** For `n ≥ 1`, `φ(n) = ∑_{d ∣ n} μ(d) n/d`. -/
@[kb "apostol1976" "Thm 2.3, p. 26"]
theorem totient_eq_sum_moebius_mul {n : ℕ} (hn : 0 < n) :
    (n.totient : ℤ) = ∑ d ∈ n.divisors, μ d * ((n / d : ℕ) : ℤ) := by
  have h := (sum_eq_iff_sum_mul_moebius_eq (f := fun n ↦ (n.totient : ℤ))
    (g := fun n ↦ (n : ℤ))).1 (fun n _ ↦ by exact_mod_cast Nat.sum_totient n) n hn
  simp only [Int.cast_id] at h
  rw [← h]
  exact Nat.sum_divisorsAntidiagonal (fun a b ↦ (μ a : ℤ) * (b : ℤ))

/-- `∑_{n ≥ 1} μ(n)/n² = 1/ζ(2) = 6/π²` (Apostol, §3.7, equation (12), proved in the book later
via Euler products; here from Mathlib's `L(μ, s) L(u, s) = 1`). -/
@[kb "apostol1976" "§3.7, (12), p. 61"]
theorem hasSum_moebius_div_sq : HasSum (fun n : ℕ ↦ (μ n : ℝ) / (n : ℝ) ^ 2) (6 / π ^ 2) := by
  have h := LSeries_zeta_mul_Lseries_moebius (s := 2) (by norm_num)
  rw [LSeries_zeta_eq_riemannZeta (by norm_num), riemannZeta_two] at h
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hL : L ↗μ 2 = ((6 / π ^ 2 : ℝ) : ℂ) := by
    push_cast
    field_simp
    linear_combination 6 * h
  have hs : LSeriesSummable ↗μ 2 := LSeriesSummable_moebius_iff.2 (by norm_num)
  have hsum : HasSum (LSeries.term ↗μ 2) (L ↗μ 2) := hs.hasSum
  rw [hL] at hsum
  rw [← Complex.hasSum_ofReal]
  convert hsum using 1
  ext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [LSeries.term_of_ne_zero hn]
    push_cast
    norm_cast

/-- **Apostol, Theorem 3.7.** `∑_{n ≤ x} φ(n) = (3/π²) x² + O(x log x)`; explicitly the error is
at most `5 x log x` for `x ≥ 2`. -/
@[kb "apostol1976" "Thm 3.7, p. 62"]
theorem abs_sum_totient_sub_le {x : ℝ} (hx : 2 ≤ x) :
    |∑ n ∈ Ioc 0 ⌊x⌋₊, (n.totient : ℝ) - 3 / π ^ 2 * x ^ 2| ≤ 5 * (x * Real.log x) := by
  have hx1 : 1 ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  -- `∑ φ(n) = ∑_{d ≤ x} μ(d) ∑_{q ≤ x/d} q`
  have hS : ∑ n ∈ Ioc 0 ⌊x⌋₊, (n.totient : ℝ) =
      ∑ d ∈ Ioc 0 ⌊x⌋₊, (μ d : ℝ) * ∑ q ∈ Ioc 0 ⌊x / d⌋₊, (q : ℝ) := by
    have : ∑ n ∈ Ioc 0 ⌊x⌋₊, (n.totient : ℝ) = ∑ n ∈ Ioc 0 ⌊x⌋₊,
        ((μ : ArithmeticFunction ℝ) * ((ArithmeticFunction.id : ArithmeticFunction ℕ) :
          ArithmeticFunction ℝ)) n := by
      refine sum_congr rfl fun n hn ↦ ?_
      rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal (fun a b ↦ (μ : ArithmeticFunction ℝ) a *
        ((ArithmeticFunction.id : ArithmeticFunction ℕ) : ArithmeticFunction ℝ) b)]
      have := totient_eq_sum_moebius_mul (mem_Ioc.1 hn).1
      have := congrArg (fun z : ℤ ↦ (z : ℝ)) this
      simp only [Int.cast_sum, Int.cast_mul, Int.cast_natCast] at this
      rw [this]
      simp [natCoe_apply, intCoe_apply, ArithmeticFunction.id_apply]
    rw [this, sum_Ioc_mul_eq_sum_sum]
    refine sum_congr rfl fun d hd ↦ ?_
    rw [intCoe_apply, ← Nat.floor_div_natCast]
    simp [natCoe_apply, ArithmeticFunction.id_apply]
  have hmain := abs_sum_mul_sum_id_sub_le (w := fun d ↦ (μ d : ℝ))
    (fun n ↦ by exact_mod_cast abs_moebius_le_one) hx1
  rw [← hS] at hmain
  -- `∑_{d ≤ x} μ(d)/d² = 6/π² + O(1/x)`
  have hN1 : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx1)
  have htail := abs_tsum_sub_sum_Ioc_le (c := fun n ↦ (μ n : ℝ) / (n : ℝ) ^ 2)
    (fun n ↦ by
      rw [abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ 2)]
      exact div_le_div_of_nonneg_right (by exact_mod_cast abs_moebius_le_one) (by positivity))
    (by simp) (N := ⌊x⌋₊) (by omega)
  rw [hasSum_moebius_div_sq.tsum_eq] at htail
  have hNx : 1 / (⌊x⌋₊ : ℝ) ≤ 2 / x := by
    have h1 := Nat.lt_floor_add_one x
    have h0 : (0 : ℝ) < ⌊x⌋₊ := by exact_mod_cast hN1
    have h2 : (1 : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast hN1
    rw [div_le_div_iff₀ h0 hx0]; linarith
  have hx2 : x ^ 2 / 2 * (2 / x) = x := by field_simp
  set T := ∑ d ∈ Ioc 0 ⌊x⌋₊, (μ d : ℝ) / (d : ℝ) ^ 2
  have hT : |x ^ 2 / 2 * T - 3 / π ^ 2 * x ^ 2| ≤ x := by
    have : x ^ 2 / 2 * T - 3 / π ^ 2 * x ^ 2 = -(x ^ 2 / 2 * (6 / π ^ 2 - T)) := by ring
    rw [this, abs_neg, abs_mul, abs_of_nonneg (by positivity)]
    calc x ^ 2 / 2 * |6 / π ^ 2 - T| ≤ x ^ 2 / 2 * (2 / x) :=
          mul_le_mul_of_nonneg_left (htail.trans hNx) (by positivity)
      _ = x := hx2
  have hlog := one_add_log_le hx
  calc |∑ n ∈ Ioc 0 ⌊x⌋₊, (n.totient : ℝ) - 3 / π ^ 2 * x ^ 2|
      ≤ |∑ n ∈ Ioc 0 ⌊x⌋₊, (n.totient : ℝ) - x ^ 2 / 2 * T| + |x ^ 2 / 2 * T - 3 / π ^ 2 * x ^ 2| :=
        abs_sub_le _ _ _
    _ ≤ x * (1 + Real.log x) + x := add_le_add hmain hT
    _ ≤ 5 * (x * Real.log x) := by
        have : x ≤ 2 * (x * Real.log x) := by
          have h3 : (1 : ℝ) / 2 < Real.log 2 := by have := Real.log_two_gt_d9; linarith
          have h2 : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx
          nlinarith
        linarith

end NTKB.Apostol
