/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Apostol.ArithmeticFunctions.Multiplicative

/-!
# Small results of Apostol's Chapter 2 (Theorem 2.5 (f), Examples of §2.9)

* Theorem 2.5 (f): if `n` has `r` distinct odd prime factors then `2^r ∣ φ(n)` (Mathlib has the
  other parts of 2.5);
* §2.9, Example 1: `N^α` is completely multiplicative (`isCompletelyMultiplicative_powC`);
  Example 2: the identity `I(n) = [1/n]` is completely multiplicative;
  Examples 3 and 4: `μ` and `φ` are multiplicative but not completely multiplicative
  (`μ(4) ≠ μ(2)²`, `φ(4) ≠ φ(2)²`).
-/

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius

namespace NTKB.Apostol

/-- **Apostol, Theorem 2.5 (f).** If `n ≥ 1` has `r` distinct odd prime factors then
`2^r ∣ φ(n)`. -/
@[kb "apostol1976" "Thm 2.5(f), p. 28"]
theorem two_pow_card_odd_primeFactors_dvd_totient {n : ℕ} (hn : n ≠ 0) :
    2 ^ #(n.primeFactors.filter (· ≠ 2)) ∣ n.totient := by
  classical
  rw [Nat.totient_eq_prod_factorization hn, Finsupp.prod, Nat.support_factorization,
    ← prod_filter_mul_prod_filter_not n.primeFactors (· ≠ 2)]
  refine dvd_mul_of_dvd_left ?_ _
  rw [← prod_const]
  refine prod_dvd_prod_of_dvd _ _ fun p hp ↦ ?_
  obtain ⟨hp1, hp2⟩ := mem_filter.1 hp
  have hpp := Nat.prime_of_mem_primeFactors hp1
  have hodd : Odd p := hpp.odd_of_ne_two hp2
  refine dvd_mul_of_dvd_right ?_ _
  obtain ⟨m, hm⟩ := hodd
  exact ⟨m, by omega⟩

/-- **Apostol, §2.9, Example 2.** The identity function `I(n) = [1/n]` is completely
multiplicative. -/
@[kb "apostol1976" "§2.9, Example 2, p. 33"]
theorem isCompletelyMultiplicative_one {R : Type*} [MonoidWithZero R] [Nontrivial R] :
    IsCompletelyMultiplicative (1 : ArithmeticFunction R) := by
  refine ⟨one_one, fun m n ↦ ?_⟩
  simp only [ArithmeticFunction.one_apply, mul_eq_one]
  by_cases hm : m = 1 <;> by_cases hn : n = 1 <;> simp [hm, hn]

/-- **Apostol, §2.9, Example 3.** `μ` is not completely multiplicative: `μ(4) = 0 ≠ 1 = μ(2)²`. -/
@[kb "apostol1976" "§2.9, Example 3, p. 33"]
theorem not_isCompletelyMultiplicative_moebius :
    ¬ IsCompletelyMultiplicative (μ : ArithmeticFunction ℤ) := by
  intro h
  have := h.2 2 2
  rw [show (2 * 2 : ℕ) = 2 ^ 2 by norm_num, moebius_apply_prime_pow Nat.prime_two two_ne_zero,
    moebius_apply_prime Nat.prime_two] at this
  norm_num at this

/-- **Apostol, §2.9, Example 4.** `φ` is not completely multiplicative: `φ(4) = 2 ≠ 1 = φ(2)²`. -/
@[kb "apostol1976" "§2.9, Example 4, p. 33"]
theorem totient_four_ne : Nat.totient (2 * 2) ≠ Nat.totient 2 * Nat.totient 2 := by
  decide

end NTKB.Apostol
