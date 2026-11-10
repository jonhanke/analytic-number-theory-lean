/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Log.Sum
import NTKB.Attr

/-!
# `∑_{p ≤ x} ⌊x/p⌋ log p = x log x + O(x)` (Apostol, Chapter 3, §3.11, Theorem 3.16)

* Theorem 3.12, second identity: `∑_{n ≤ x} Λ(n) ⌊x/n⌋ = log ⌊x⌋! = ∑_{n ≤ x} log n`;
* Theorem 3.16: `∑_{p ≤ x} ⌊x/p⌋ log p = x log x + O(x)` for `x ≥ 2`.

Proof (Apostol's, with one change): by 3.12 and Mathlib's `Real.le_sum_log'`/`Real.sum_log_le'`
(Theorem 3.15) the full sum is `x log x + O(x)`; the prime powers `p^m`, `m ≥ 2`, contribute
`∑_{m ≤ x} (ψ - ϑ)(x/m)` (interchanging the order of summation), and Mathlib's
`ψ(y) - ϑ(y) ≤ C √y` with `∑_{m ≤ x} 1/√m ≤ 2√x` makes this `O(x)`. Apostol bounds the same
contribution by `x ∑_p log p/(p(p-1))`.
-/

open Finset ArithmeticFunction Real Chebyshev
open scoped ArithmeticFunction.zeta

namespace NTKB.Apostol

/-- `∑_{n ≤ N} a(n) ⌊N/n⌋ = ∑_{m ≤ N} ∑_{n ≤ N/m} a(n)` (Apostol, Theorem 3.11). -/
theorem sum_mul_div_eq_sum_sum (a : ArithmeticFunction ℝ) (N : ℕ) :
    ∑ n ∈ Ioc 0 N, a n * ((N / n : ℕ) : ℝ) = ∑ m ∈ Ioc 0 N, ∑ n ∈ Ioc 0 (N / m), a n := by
  rw [← sum_Ioc_mul_zeta_eq_sum, ← coe_zeta_mul_comm, sum_Ioc_mul_eq_sum_sum]
  refine sum_congr rfl fun m hm ↦ ?_
  rw [natCoe_apply, zeta_apply_ne (mem_Ioc.1 hm).1.ne', Nat.cast_one, one_mul]

/-- **Apostol, Theorem 3.12**, second identity:
`∑_{n ≤ x} Λ(n) ⌊x/n⌋ = ∑_{n ≤ x} log n = log ⌊x⌋!`. -/
@[kb "apostol1976" "Thm 3.12, p. 66"]
theorem sum_vonMangoldt_mul_floor (x : ℝ) :
    ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n * (⌊x / n⌋₊ : ℝ) = ∑ n ∈ Ioc 0 ⌊x⌋₊, Real.log n := by
  have h := sum_Ioc_mul_zeta_eq_sum Λ ⌊x⌋₊
  rw [vonMangoldt_mul_zeta] at h
  simp only [log_apply] at h
  rw [h]
  refine sum_congr rfl fun n _ ↦ ?_
  rw [Nat.floor_div_natCast]

/-- `∑_{m ≤ N} 1/√m ≤ 2√N`. -/
theorem sum_Ioc_inv_sqrt_le (N : ℕ) : ∑ m ∈ Ioc 0 N, 1 / √(m : ℝ) ≤ 2 * √(N : ℝ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_Ioc_succ_top (Nat.zero_le _)]
    have ha := Real.sqrt_nonneg (N : ℝ)
    have hb : 0 < √((N + 1 : ℕ) : ℝ) := Real.sqrt_pos.2 (by positivity)
    have ha2 : √(N : ℝ) ^ 2 = N := Real.sq_sqrt (Nat.cast_nonneg _)
    have hb2 : √((N + 1 : ℕ) : ℝ) ^ 2 = N + 1 := by
      rw [Real.sq_sqrt (Nat.cast_nonneg _)]; push_cast; ring
    have key : 1 / √((N + 1 : ℕ) : ℝ) ≤ 2 * √((N + 1 : ℕ) : ℝ) - 2 * √(N : ℝ) := by
      rw [div_le_iff₀ hb]
      nlinarith [sq_nonneg (√((N + 1 : ℕ) : ℝ) - √(N : ℝ))]
    linarith

/-- **Apostol, Theorem 3.16.** For `x ≥ 2`, `∑_{p ≤ x} ⌊x/p⌋ log p = x log x + O(x)`. -/
@[kb "apostol1976" "Thm 3.16, p. 68"]
theorem exists_abs_sum_prime_floor_mul_log_sub_le :
    ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x →
      |∑ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, (⌊x / p⌋₊ : ℝ) * Real.log p - x * Real.log x| ≤ C * x := by
  obtain ⟨C₀, hC₀⟩ := psi_sub_theta_le_mul_sqrt
  set C := max C₀ 0
  refine ⟨2 + 2 * C, fun x hx ↦ ?_⟩
  have hx1 : 1 ≤ x := by linarith
  set N := ⌊x⌋₊
  -- the non-prime part of `Λ`
  let a : ArithmeticFunction ℝ := ⟨fun n ↦ if n.Prime then 0 else Λ n, by simp⟩
  have hsplit : ∑ n ∈ Ioc 0 N, Λ n * (⌊x / n⌋₊ : ℝ) =
      ∑ p ∈ Ioc 0 N with p.Prime, (⌊x / p⌋₊ : ℝ) * Real.log p +
        ∑ n ∈ Ioc 0 N, a n * ((N / n : ℕ) : ℝ) := by
    rw [sum_filter, ← sum_add_distrib]
    refine sum_congr rfl fun n _ ↦ ?_
    rw [← Nat.floor_div_natCast]
    by_cases hp : n.Prime
    · simp [a, hp, vonMangoldt_apply_prime hp, mul_comm]
    · simp [a, hp]
  -- the non-prime part is `∑_{m ≤ x} (ψ - ϑ)(x/m) ≤ C ∑ √(x/m) ≤ 2 C x`
  have hE0 : 0 ≤ ∑ n ∈ Ioc 0 N, a n * ((N / n : ℕ) : ℝ) := by
    refine sum_nonneg fun n _ ↦ mul_nonneg ?_ (Nat.cast_nonneg _)
    show 0 ≤ (if n.Prime then 0 else Λ n)
    split_ifs
    · exact le_rfl
    · exact vonMangoldt_nonneg
  have hE1 : ∑ n ∈ Ioc 0 N, a n * ((N / n : ℕ) : ℝ) ≤ 2 * C * x := by
    rw [sum_mul_div_eq_sum_sum]
    have hterm : ∀ m ∈ Ioc 0 N, ∑ n ∈ Ioc 0 (N / m), a n ≤ C * (√(N : ℝ) * (1 / √(m : ℝ))) := by
      intro m hm
      have hm0 : (0 : ℝ) < m := by exact_mod_cast (mem_Ioc.1 hm).1
      have h1 := psi_sub_theta_eq_sum_not_prime ((N / m : ℕ) : ℝ)
      rw [Nat.floor_natCast, sum_filter] at h1
      have h2 : ∑ n ∈ Ioc 0 (N / m), a n = ψ ((N / m : ℕ) : ℝ) - θ ((N / m : ℕ) : ℝ) := by
        rw [h1]
        exact sum_congr rfl fun n _ ↦ by by_cases hp : n.Prime <;> simp [a, hp]
      rw [h2]
      calc ψ ((N / m : ℕ) : ℝ) - θ ((N / m : ℕ) : ℝ) ≤ C₀ * √((N / m : ℕ) : ℝ) := hC₀ _
        _ ≤ C * √((N / m : ℕ) : ℝ) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)
        _ ≤ C * (√(N : ℝ) * (1 / √(m : ℝ))) := by
            refine mul_le_mul_of_nonneg_left ?_ (le_max_right _ _)
            rw [mul_one_div, ← Real.sqrt_div' _ hm0.le]
            exact Real.sqrt_le_sqrt (Nat.cast_div_le)
    calc ∑ m ∈ Ioc 0 N, ∑ n ∈ Ioc 0 (N / m), a n
        ≤ ∑ m ∈ Ioc 0 N, C * (√(N : ℝ) * (1 / √(m : ℝ))) := sum_le_sum hterm
      _ = C * √(N : ℝ) * ∑ m ∈ Ioc 0 N, 1 / √(m : ℝ) := by
          rw [mul_sum]; exact sum_congr rfl fun m _ ↦ by ring
      _ ≤ C * √(N : ℝ) * (2 * √(N : ℝ)) :=
          mul_le_mul_of_nonneg_left (sum_Ioc_inv_sqrt_le N)
            (mul_nonneg (le_max_right _ _) (Real.sqrt_nonneg _))
      _ = 2 * C * N := by rw [show C * √(N : ℝ) * (2 * √(N : ℝ)) = 2 * C * (√(N : ℝ) ^ 2) by ring,
            Real.sq_sqrt (Nat.cast_nonneg _)]
      _ ≤ 2 * C * x := mul_le_mul_of_nonneg_left (Nat.floor_le (by linarith))
            (by have := le_max_right C₀ 0; linarith)
  have hL := sum_vonMangoldt_mul_floor x
  have hup := Real.sum_log_le' hx1
  have hlow := Real.le_sum_log' hx1
  rw [hsplit] at hL
  rw [abs_le]
  constructor <;> nlinarith [le_max_right C₀ 0]

end NTKB.Apostol
