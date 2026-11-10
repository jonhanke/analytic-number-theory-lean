/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Apostol.ArithmeticFunctions.Multiplicative

/-!
# Multiplicative functions are determined by prime powers (Apostol, Theorem 2.13)

**Theorem 2.13**: (a) `f` is multiplicative iff `f(p₁^{a₁} ⋯ p_r^{a_r}) = f(p₁^{a₁}) ⋯ f(p_r^{a_r})`
for all `n ≥ 1` (with `f(1) = 1`, the empty product); (b) a multiplicative `f` is completely
multiplicative iff `f(p^a) = f(p)^a` for all primes `p` and `a ≥ 1`.
(The forward direction of (a) is Mathlib's `ArithmeticFunction.IsMultiplicative.multiplicative_factorization`;
(b) uses `isCompletelyMultiplicative_of_prime_pow` of `Multiplicative.lean`.)
-/

open ArithmeticFunction

namespace NTKB.Apostol

variable {R : Type*}

/-- **Theorem 2.13 (a)**. -/
@[kb "apostol1976" "Thm 2.13, p. 34"]
theorem isMultiplicative_iff_factorization [CommMonoidWithZero R] (f : ArithmeticFunction R) :
    f.IsMultiplicative ↔ ∀ n : ℕ, n ≠ 0 → f n = n.factorization.prod fun p k => f (p ^ k) := by
  refine ⟨fun hf n hn => hf.multiplicative_factorization f hn, fun h => ⟨?_, fun {m n} hmn => ?_⟩⟩
  · rw [h 1 one_ne_zero, Nat.factorization_one, Finsupp.prod_zero_index]
  · rcases eq_or_ne m 0 with rfl | hm
    · simp
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    rw [h _ (mul_ne_zero hm hn), h m hm, h n hn, Nat.factorization_mul hm hn,
      Finsupp.prod_add_index_of_disjoint]
    simpa [Nat.support_factorization] using hmn.disjoint_primeFactors

/-- **Theorem 2.13 (b)**. -/
@[kb "apostol1976" "Thm 2.13, p. 34"]
theorem isCompletelyMultiplicative_iff_prime_pow [CommMonoidWithZero R] {f : ArithmeticFunction R}
    (hf : f.IsMultiplicative) :
    IsCompletelyMultiplicative f ↔ ∀ p a : ℕ, p.Prime → 1 ≤ a → f (p ^ a) = f p ^ a := by
  refine ⟨fun h p a _ _ => h.map_pow p a, fun h => isCompletelyMultiplicative_of_prime_pow hf
    fun p a hp => ?_⟩
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp [hf.map_one]
  · exact h p a hp ha

end NTKB.Apostol
