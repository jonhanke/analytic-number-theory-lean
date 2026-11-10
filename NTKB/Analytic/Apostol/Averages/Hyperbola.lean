/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import NTKB.Attr

/-!
# The hyperbola identity (Apostol, Chapter 3, §3.12, Theorem 3.17)

For arithmetical functions `f, g` with partial sums `F(x) = ∑_{n ≤ x} f(n)`,
`G(x) = ∑_{n ≤ x} g(n)` and positive reals `a, b` with `ab = x`,
$$\sum_{qd \le x} f(d) g(q) = \sum_{n \le a} f(n) G(x/n) + \sum_{n \le b} g(n) F(x/n) - F(a) G(b).$$
Mathlib has the unrestricted form `ArithmeticFunction.sum_Ioc_mul_eq_sum_sum` (Apostol's
Theorem 3.10) and a TODO for the hyperbola method. Sums `∑_{n ≤ y}` over positive integers are
written `∑ n ∈ Ioc 0 ⌊y⌋₊`.

Proof (Apostol's): split the lattice points under the hyperbola into those with `d ≤ a` and
those with `q ≤ b`; the points with both are counted twice and form the box `[1, a] × [1, b]`.
-/

open Finset ArithmeticFunction

namespace NTKB.Apostol

variable {R : Type*}

/-- A sum over `1 ≤ n ≤ y` as a filtered sum over `1 ≤ n ≤ M`, for any `M ≥ ⌊y⌋₊`. -/
theorem sum_Ioc_floor_eq_sum_ite {M : Type*} [AddCommMonoid M] (u : ℕ → M) {y : ℝ} {K : ℕ}
    (hK : ⌊y⌋₊ ≤ K) :
    ∑ n ∈ Ioc 0 ⌊y⌋₊, u n = ∑ n ∈ Ioc 0 K, if (n : ℝ) ≤ y then u n else 0 := by
  rw [← sum_filter]
  congr 1
  ext n
  simp only [mem_Ioc, mem_filter]
  constructor
  · rintro ⟨h0, h⟩
    have hy : 0 ≤ y := by
      by_contra hy
      rw [Nat.floor_eq_zero.2 (by linarith)] at h
      omega
    exact ⟨⟨h0, h.trans hK⟩, (Nat.le_floor_iff hy).1 h⟩
  · rintro ⟨⟨h0, -⟩, h⟩
    exact ⟨h0, Nat.le_floor h⟩

/-- **Apostol, Theorem 3.17** (the hyperbola identity). If `a, b > 0` and `ab = x`, then
`∑_{n ≤ x} (f * g)(n) = ∑_{qd ≤ x} f(d) g(q)` equals
`∑_{n ≤ a} f(n) G(x/n) + ∑_{n ≤ b} g(n) F(x/n) - F(a) G(b)`. -/
@[kb "apostol1976" "Thm 3.17, p. 69"]
theorem sum_mul_eq_hyperbola [CommRing R] (f g : ArithmeticFunction R) {a b x : ℝ} (ha : 0 < a)
    (hb : 0 < b) (hab : a * b = x) :
    ∑ n ∈ Ioc 0 ⌊x⌋₊, (f * g) n =
      ∑ n ∈ Ioc 0 ⌊a⌋₊, f n * ∑ m ∈ Ioc 0 ⌊x / n⌋₊, g m +
        ∑ n ∈ Ioc 0 ⌊b⌋₊, g n * ∑ m ∈ Ioc 0 ⌊x / n⌋₊, f m -
          (∑ n ∈ Ioc 0 ⌊a⌋₊, f n) * ∑ n ∈ Ioc 0 ⌊b⌋₊, g n := by
  have hx : 0 < x := hab ▸ mul_pos ha hb
  set K := ⌊x⌋₊ + ⌊a⌋₊ + ⌊b⌋₊ with hK
  have hxK : ⌊x⌋₊ ≤ K := by omega
  have haK : ⌊a⌋₊ ≤ K := by omega
  have hbK : ⌊b⌋₊ ≤ K := by omega
  have hdiv : ∀ n : ℕ, ⌊x / n⌋₊ ≤ K := fun n ↦ by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · refine le_trans (Nat.floor_le_floor (div_le_self hx.le (by exact_mod_cast hn))) hxK
  -- everything as a sum over the box `[1, K]²` with indicator conditions
  set h : ℕ → ℕ → R := fun d q ↦ f d * g q
  have hL : ∑ n ∈ Ioc 0 ⌊x⌋₊, (f * g) n =
      ∑ d ∈ Ioc 0 K, ∑ q ∈ Ioc 0 K, if ((d * q : ℕ) : ℝ) ≤ x then h d q else 0 := by
    rw [sum_Ioc_mul_eq_sum_sum]
    rw [sum_Ioc_floor_eq_sum_ite _ hxK]
    refine sum_congr rfl fun d hd ↦ ?_
    have hd0 : (0 : ℝ) < d := by exact_mod_cast (mem_Ioc.1 hd).1
    rw [mul_sum]
    rw [show ⌊x⌋₊ / d = ⌊x / d⌋₊ from (Nat.floor_div_natCast x d).symm,
      sum_Ioc_floor_eq_sum_ite _ (hdiv d)]
    split_ifs with hdx
    · refine sum_congr rfl fun q hq ↦ ?_
      simp only [Nat.cast_mul, (le_div_iff₀' hd0).symm]
      split_ifs <;> simp [h]
    · symm
      refine sum_eq_zero fun q hq ↦ ?_
      have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (mem_Ioc.1 hq).1
      refine if_neg fun hle ↦ ?_
      apply hdx
      rw [Nat.cast_mul] at hle
      nlinarith
  have hA : ∑ n ∈ Ioc 0 ⌊a⌋₊, f n * ∑ m ∈ Ioc 0 ⌊x / n⌋₊, g m =
      ∑ d ∈ Ioc 0 K, ∑ q ∈ Ioc 0 K,
        if (d : ℝ) ≤ a ∧ ((d * q : ℕ) : ℝ) ≤ x then h d q else 0 := by
    rw [sum_Ioc_floor_eq_sum_ite _ haK]
    refine sum_congr rfl fun d hd ↦ ?_
    have hd0 : (0 : ℝ) < d := by exact_mod_cast (mem_Ioc.1 hd).1
    rw [sum_Ioc_floor_eq_sum_ite _ (hdiv d)]
    split_ifs with hda
    · rw [mul_sum]
      refine sum_congr rfl fun q hq ↦ ?_
      simp only [Nat.cast_mul, (le_div_iff₀' hd0).symm]
      split_ifs with h1 h2 h2
      · rfl
      · exact absurd ⟨hda, h1⟩ h2
      · exact absurd h2.2 h1
      · simp
    · symm
      refine sum_eq_zero fun q hq ↦ ?_
      rw [if_neg (fun h' ↦ hda h'.1)]
  have hB : ∑ n ∈ Ioc 0 ⌊b⌋₊, g n * ∑ m ∈ Ioc 0 ⌊x / n⌋₊, f m =
      ∑ d ∈ Ioc 0 K, ∑ q ∈ Ioc 0 K,
        if (q : ℝ) ≤ b ∧ ((d * q : ℕ) : ℝ) ≤ x then h d q else 0 := by
    rw [sum_comm, sum_Ioc_floor_eq_sum_ite _ hbK]
    refine sum_congr rfl fun q hq ↦ ?_
    have hq0 : (0 : ℝ) < q := by exact_mod_cast (mem_Ioc.1 hq).1
    rw [sum_Ioc_floor_eq_sum_ite _ (hdiv q)]
    split_ifs with hqb
    · rw [mul_sum]
      refine sum_congr rfl fun d hd ↦ ?_
      simp only [Nat.cast_mul, mul_comm (d : ℝ), (le_div_iff₀' hq0).symm]
      split_ifs with h1 h2 h2
      · simp [h, mul_comm]
      · exact absurd ⟨hqb, h1⟩ h2
      · exact absurd h2.2 h1
      · simp
    · symm
      refine sum_eq_zero fun d hd ↦ ?_
      rw [if_neg (fun h' ↦ hqb h'.1)]
  have hC : (∑ n ∈ Ioc 0 ⌊a⌋₊, f n) * ∑ n ∈ Ioc 0 ⌊b⌋₊, g n =
      ∑ d ∈ Ioc 0 K, ∑ q ∈ Ioc 0 K, if (d : ℝ) ≤ a ∧ (q : ℝ) ≤ b then h d q else 0 := by
    rw [sum_Ioc_floor_eq_sum_ite _ haK, sum_Ioc_floor_eq_sum_ite _ hbK, sum_mul]
    refine sum_congr rfl fun d _ ↦ ?_
    rw [mul_sum]
    refine sum_congr rfl fun q _ ↦ ?_
    split_ifs <;> simp_all [h]
  rw [hL, hA, hB, hC, ← sum_add_distrib, ← sum_sub_distrib]
  refine sum_congr rfl fun d hd ↦ ?_
  rw [← sum_add_distrib, ← sum_sub_distrib]
  refine sum_congr rfl fun q hq ↦ ?_
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (mem_Ioc.1 hd).1
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (mem_Ioc.1 hq).1
  rw [Nat.cast_mul]
  by_cases hda : (d : ℝ) ≤ a <;> by_cases hqb : (q : ℝ) ≤ b
  · have : (d : ℝ) * q ≤ x := hab ▸ mul_le_mul hda hqb (by linarith) ha.le
    simp [hda, hqb, this]
  · simp [hda, hqb]
  · simp [hda, hqb]
  · have : ¬ (d : ℝ) * q ≤ x := by
      rw [not_le, ← hab]
      exact mul_lt_mul'' (lt_of_not_ge hda) (lt_of_not_ge hqb) ha.le hb.le
    simp [hda, hqb, this]

end NTKB.Apostol
