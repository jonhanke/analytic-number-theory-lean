/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Apostol.ArithmeticFunctions.Multiplicative
import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Bell series (Apostol, Chapter 2, §§2.16–2.17)

The Bell series of an arithmetical function `f` modulo a prime `p` is the formal power series
`f_p(x) = ∑_{n ≥ 0} f(p^n) xⁿ` (`NTKB.Apostol.bellSeries`; not in Mathlib).

* Theorem 2.24: multiplicative `f, g` are equal iff their Bell series agree for every prime;
* Theorem 2.25: `(f * g)_p = f_p g_p`;
* the examples of §2.16: `μ_p(x) = 1 - x`, and for completely multiplicative `f`,
  `f_p(x) = 1/(1 - f(p) x)`.
-/

open Finset ArithmeticFunction PowerSeries
open scoped ArithmeticFunction.Moebius

namespace NTKB.Apostol

variable {R : Type*}

/-- The Bell series `f_p(x) = ∑_{n ≥ 0} f(pⁿ) xⁿ` of `f` modulo `p` (Apostol, §2.16). -/
noncomputable def bellSeries [Semiring R] (f : ArithmeticFunction R) (p : ℕ) : PowerSeries R :=
  PowerSeries.mk fun n ↦ f (p ^ n)

@[simp]
theorem coeff_bellSeries [Semiring R] (f : ArithmeticFunction R) (p n : ℕ) :
    coeff n (bellSeries f p) = f (p ^ n) := by
  simp [bellSeries]

/-- **Apostol, Theorem 2.24** (uniqueness theorem). Two multiplicative functions are equal iff
their Bell series modulo `p` agree for every prime `p`. -/
@[kb "apostol1976" "Thm 2.24, p. 43"]
theorem eq_iff_bellSeries_eq [CommSemiring R] {f g : ArithmeticFunction R}
    (hf : f.IsMultiplicative) (hg : g.IsMultiplicative) :
    f = g ↔ ∀ p : ℕ, p.Prime → bellSeries f p = bellSeries g p := by
  rw [IsMultiplicative.eq_iff_eq_on_prime_powers f hf g hg]
  constructor
  · intro h p hp
    ext n
    simp [h p n hp]
  · intro h p n hp
    simpa using congrArg (coeff n) (h p hp)

/-- **Apostol, Theorem 2.25.** For every prime `p`, `(f * g)_p(x) = f_p(x) g_p(x)`. -/
@[kb "apostol1976" "Thm 2.25, p. 44"]
theorem bellSeries_mul [CommSemiring R] (f g : ArithmeticFunction R) {p : ℕ} (hp : p.Prime) :
    bellSeries (f * g) p = bellSeries f p * bellSeries g p := by
  ext n
  rw [coeff_bellSeries, mul_apply_eq_sum_divisors, Nat.sum_divisors_prime_pow hp, coeff_mul,
    Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  refine sum_congr rfl fun k hk ↦ ?_
  rw [coeff_bellSeries, coeff_bellSeries, Nat.pow_div (by simpa [Nat.lt_succ_iff] using hk) hp.pos]

/-- Bell series of the Möbius function: `μ_p(x) = 1 - x` (Apostol, §2.16, Example 1). -/
@[kb "apostol1976" "§2.16, Example 1, p. 43"]
theorem bellSeries_moebius [CommRing R] {p : ℕ} (hp : p.Prime) :
    bellSeries (μ : ArithmeticFunction R) p = 1 - X := by
  ext n
  rw [coeff_bellSeries, intCoe_apply, map_sub, coeff_one, coeff_X]
  rcases n with _ | _ | n
  · simp
  · simp [moebius_apply_prime hp]
  · rw [moebius_apply_prime_pow hp (by omega)]
    simp

/-- Bell series of a completely multiplicative function: `f_p(x) (1 - f(p) x) = 1`, i.e.
`f_p(x) = 1/(1 - f(p) x)` (Apostol, §2.16, Example 3). -/
@[kb "apostol1976" "§2.16, Example 3, p. 43"]
theorem bellSeries_mul_one_sub_of_isCompletelyMultiplicative [CommRing R]
    {f : ArithmeticFunction R} (hf : IsCompletelyMultiplicative f) (p : ℕ) :
    bellSeries f p * (1 - C (f p) * X) = 1 := by
  ext n
  rw [mul_sub, mul_one, map_sub, coeff_one]
  rcases n with _ | n
  · simp [hf.1]
  · rw [show bellSeries f p * (C (f p) * X) = (C (f p) * bellSeries f p) * X by ring,
      coeff_succ_mul_X, coeff_C_mul, coeff_bellSeries, coeff_bellSeries, hf.map_pow, hf.map_pow,
      pow_succ]
    simp [mul_comm]

end NTKB.Apostol
