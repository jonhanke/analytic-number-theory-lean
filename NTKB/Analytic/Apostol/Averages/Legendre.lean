/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import NTKB.Attr

/-!
# Legendre's identity for `⌊x⌋!` (Apostol, Theorem 3.14)

**Theorem 3.14**: for `x ≥ 1`, `⌊x⌋! = ∏_{p ≤ x} p^{α(p)}` with `α(p) = ∑_{m ≥ 1} ⌊x/p^m⌋`
(the sum is finite: the terms vanish once `p^m > x`; we sum over `1 ≤ m ≤ ⌊x⌋`, which contains
all nonzero terms). From Mathlib's `Nat.factorization_factorial` (the exponent of `p` in `n!`).
-/

open Finset

namespace NTKB.Apostol

/-- **Theorem 3.14** (Legendre). -/
@[kb "apostol1976" "Thm 3.14, p. 67"]
theorem factorial_floor_eq_prod (x : ℝ) :
    (⌊x⌋₊).factorial = ∏ p ∈ Nat.primesLE ⌊x⌋₊, p ^ (∑ m ∈ Ico 1 (⌊x⌋₊ + 1), ⌊x / (p ^ m : ℕ)⌋₊) := by
  set n := ⌊x⌋₊
  have hsupp : n.factorial.factorization.support ⊆ Nat.primesLE n := by
    intro p hp
    rw [Nat.support_factorization, Nat.mem_primeFactors] at hp
    exact Nat.mem_primesLE.mpr ⟨(Nat.Prime.dvd_factorial hp.1).mp hp.2.1, hp.1⟩
  conv_lhs => rw [← Nat.prod_factorization_pow_eq_self (Nat.factorial_ne_zero n)]
  rw [Finsupp.prod_of_support_subset _ hsupp _ (fun _ _ => pow_zero _)]
  refine prod_congr rfl fun p hp => ?_
  have hpr := (Nat.mem_primesLE.mp hp).2
  rw [Nat.factorization_factorial hpr (Nat.lt_succ_of_le (Nat.log_le_self p n))]
  congr 1
  refine sum_congr rfl fun m _ => ?_
  rw [Nat.floor_div_natCast]

end NTKB.Apostol
