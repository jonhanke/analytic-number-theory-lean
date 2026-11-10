/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Analysis.Complex.ExponentialBounds
import NTKB.Attr

/-!
# Chebyshev-type bounds for `π(n)` and `p_n` (Apostol, Chapter 4, Theorems 4.6 and 4.7)

* Theorem 4.6: `(1/6) n/log n < π(n) < 6 n/log n` for `n ≥ 2`, deduced here from Mathlib's
  sharper Chebyshev bounds (`Chebyshev.pi_ge_of_four_le`, `Chebyshev.pi_le_log4_mul_div`) and
  `log x ≤ (2/e) √x`;
* Theorem 4.7: `(1/6) n log n < p_n < 12 (n log n + n log(12/e))` for `n ≥ 1`, by Apostol's proof
  from 4.6 (`p_n = Nat.nth Nat.Prime (n - 1)`).

Apostol writes `log x < (2/e)√x` for `x > 1`; equality holds at `x = e²`, so the inequality is used
here in the non-strict form, which suffices.
-/

open Nat Chebyshev

namespace NTKB.Apostol

/-- `log x ≤ (2/e) √x` for `x > 0`. -/
theorem log_le_two_div_exp_mul_sqrt {x : ℝ} (hx : 0 < x) :
    Real.log x ≤ 2 / Real.exp 1 * √x := by
  have hs : 0 < √x := Real.sqrt_pos.2 hx
  have h := Real.log_le_sub_one_of_pos (show 0 < √x / Real.exp 1 by positivity)
  rw [Real.log_div hs.ne' (Real.exp_pos 1).ne', Real.log_exp, Real.log_sqrt hx.le] at h
  have : 2 / Real.exp 1 * √x = 2 * (√x / Real.exp 1) := by ring
  rw [this]; linarith

/-- `π(p_{m+1}) = m + 1`, with `p_{m+1} = Nat.nth Nat.Prime m`. -/
theorem primeCounting_nth (m : ℕ) : Nat.primeCounting (nth Nat.Prime m) = m + 1 := by
  rw [Nat.primeCounting, Nat.primeCounting', Nat.count_succ, Nat.count_nth_of_infinite
    Nat.infinite_setOf_prime, if_pos (Nat.prime_nth_prime m)]

/-- **Apostol, Theorem 4.6**, lower bound: `π(n) > (1/6) n/log n` for `n ≥ 2`. -/
@[kb "apostol1976" "Thm 4.6, p. 82"]
theorem primeCounting_gt {n : ℕ} (hn : 2 ≤ n) : 1 / 6 * (n / Real.log n) < Nat.primeCounting n := by
  have hl2 : (1 / 2 : ℝ) < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  rcases Nat.lt_or_ge n 4 with h4 | h4
  · interval_cases n
    · have : Nat.primeCounting 2 = 1 := by decide
      rw [this]
      have : (2 : ℝ) / Real.log 2 < 4 := by rw [div_lt_iff₀ (by linarith)]; linarith
      push_cast; linarith
    · have : Nat.primeCounting 3 = 2 := by decide
      rw [this]
      have hl3 : (1 : ℝ) / 2 < Real.log 3 :=
        lt_of_lt_of_le hl2 (Real.log_le_log (by norm_num) (by norm_num))
      have : (3 : ℝ) / Real.log 3 < 6 := by rw [div_lt_iff₀ (by linarith)]; linarith
      push_cast; linarith
  · have h := pi_ge_of_four_le h4
    have hln : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
    have hpos : (0 : ℝ) < n / Real.log n := by positivity
    calc 1 / 6 * (n / Real.log n) < Real.log 2 * (n / Real.log n) := by
          refine mul_lt_mul_of_pos_right ?_ hpos; linarith
      _ = n * Real.log 2 / Real.log n := by ring
      _ ≤ Nat.primeCounting n := h

/-- **Apostol, Theorem 4.6**, upper bound: `π(n) < 6 n/log n` for `n ≥ 2`. -/
@[kb "apostol1976" "Thm 4.6, p. 82"]
theorem primeCounting_lt {n : ℕ} (hn : 2 ≤ n) : (Nat.primeCounting n : ℝ) < 6 * (n / Real.log n) := by
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
  have hn0 : (0 : ℝ) < n := by linarith
  have hln : 0 < Real.log n := Real.log_pos hn1
  have h := pi_le_log4_mul_div hn1
  rw [Nat.floor_natCast, Real.log_sqrt hn0.le] at h
  -- `√n ≤ (2/e) n / log n`
  have hs : √(n : ℝ) ≤ 2 / Real.exp 1 * (n / Real.log n) := by
    have hl := log_le_two_div_exp_mul_sqrt hn0
    have hsq : √(n : ℝ) * √(n : ℝ) = n := Real.mul_self_sqrt hn0.le
    rw [mul_div_assoc', le_div_iff₀ hln]
    calc √(n : ℝ) * Real.log n ≤ √(n : ℝ) * (2 / Real.exp 1 * √(n : ℝ)) :=
          mul_le_mul_of_nonneg_left hl (Real.sqrt_nonneg _)
      _ = 2 / Real.exp 1 * (√(n : ℝ) * √(n : ℝ)) := by ring
      _ = 2 / Real.exp 1 * n := by rw [hsq]
  have he : 2 / Real.exp 1 < 1 := by
    rw [div_lt_one (Real.exp_pos 1)]
    have := Real.add_one_le_exp 1; linarith [Real.add_one_lt_exp (one_ne_zero (α := ℝ))]
  have hl4 : Real.log 4 < 2 := by
    have : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    have := Real.log_two_lt_d9; linarith
  have hpos : (0 : ℝ) < n / Real.log n := by positivity
  calc (Nat.primeCounting n : ℝ) ≤ Real.log 4 * n / (Real.log n / 2) + √(n : ℝ) := h
    _ = 2 * Real.log 4 * (n / Real.log n) + √(n : ℝ) := by field_simp
    _ ≤ 2 * Real.log 4 * (n / Real.log n) + 2 / Real.exp 1 * (n / Real.log n) := by linarith
    _ < 6 * (n / Real.log n) := by nlinarith

/-- **Apostol, Theorem 4.7.** For `n ≥ 1` the `n`th prime `p_n = Nat.nth Nat.Prime (n - 1)`
satisfies `(1/6) n log n < p_n < 12 (n log n + n log(12/e))`. -/
@[kb "apostol1976" "Thm 4.7, p. 84"]
theorem nth_prime_bounds {n : ℕ} (hn : 1 ≤ n) :
    1 / 6 * (n * Real.log n) < (nth Nat.Prime (n - 1) : ℝ) ∧
      (nth Nat.Prime (n - 1) : ℝ) < 12 * (n * Real.log n + n * Real.log (12 / Real.exp 1)) := by
  set k := nth Nat.Prime (n - 1)
  have hk2 : 2 ≤ k := (Nat.prime_nth_prime (n - 1)).two_le
  have hπ : (Nat.primeCounting k : ℝ) = n := by
    rw [primeCounting_nth]; push_cast; rw [Nat.cast_sub hn]; ring
  have hk1 : (1 : ℝ) < k := by exact_mod_cast (by omega : 1 < k)
  have hk0 : (0 : ℝ) < k := by linarith
  have hlk : 0 < Real.log k := Real.log_pos hk1
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  -- `n < 6 k / log k`, i.e. `k > (1/6) n log k`
  have hup := primeCounting_lt hk2
  rw [hπ] at hup
  -- `n > (1/6) k / log k`, i.e. `k < 6 n log k`  (20)
  have hlow := primeCounting_gt hk2
  rw [hπ] at hlow
  have h20 : (k : ℝ) < 6 * n * Real.log k := by
    rw [div_eq_mul_inv] at hlow
    have := mul_lt_mul_of_pos_right hlow (by positivity : (0 : ℝ) < 6 * Real.log k)
    field_simp at this
    linarith
  -- `p_n ≥ n + 1`
  have hge : ∀ m, m + 2 ≤ nth Nat.Prime m := by
    intro m
    induction m with
    | zero => simp [Nat.nth_prime_zero_eq_two]
    | succ m ih =>
      have := Nat.nth_strictMono (p := Nat.Prime) Nat.infinite_setOf_prime (Nat.lt_succ_self m)
      simp only [Nat.succ_eq_add_one] at this
      omega
  have hkn : (n : ℝ) < k := by
    have := hge (n - 1)
    exact_mod_cast (show n < k by omega)
  have hlogn : Real.log n < Real.log k := Real.log_lt_log hn0 hkn
  constructor
  · -- lower bound: `k > (1/6) n log k > (1/6) n log n`
    have h1 : 1 / 6 * (n * Real.log k) < k := by
      rw [div_eq_mul_inv] at hup
      have := mul_lt_mul_of_pos_right hup hlk
      field_simp at this
      linarith
    nlinarith
  · -- upper bound
    have hsk : 0 < √(k : ℝ) := Real.sqrt_pos.2 hk0
    have hsq : √(k : ℝ) * √(k : ℝ) = k := Real.mul_self_sqrt hk0.le
    have hl := log_le_two_div_exp_mul_sqrt hk0
    have he0 : 0 < Real.exp 1 := Real.exp_pos 1
    -- `√k < (12/e) n`
    have hroot : √(k : ℝ) < 12 / Real.exp 1 * n := by
      have h1 : √(k : ℝ) * √(k : ℝ) < 6 * n * (2 / Real.exp 1 * √(k : ℝ)) := by
        rw [hsq]; exact lt_of_lt_of_le h20 (mul_le_mul_of_nonneg_left hl (by positivity))
      have h2 : √(k : ℝ) * √(k : ℝ) < (12 / Real.exp 1 * n) * √(k : ℝ) := by
        calc √(k : ℝ) * √(k : ℝ) < 6 * n * (2 / Real.exp 1 * √(k : ℝ)) := h1
          _ = (12 / Real.exp 1 * n) * √(k : ℝ) := by ring
      exact lt_of_mul_lt_mul_right h2 hsk.le
    have hlog : Real.log k / 2 < Real.log n + Real.log (12 / Real.exp 1) := by
      have := Real.log_lt_log hsk hroot
      rw [Real.log_sqrt hk0.le, Real.log_mul (by positivity) hn0.ne'] at this
      linarith
    calc (k : ℝ) < 6 * n * Real.log k := h20
      _ < 6 * n * (2 * (Real.log n + Real.log (12 / Real.exp 1))) := by
          refine mul_lt_mul_of_pos_left ?_ (by positivity); linarith
      _ = 12 * (n * Real.log n + n * Real.log (12 / Real.exp 1)) := by ring

end NTKB.Apostol
