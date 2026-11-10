/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Apostol.PrimitiveRoots.Index
import Mathlib.FieldTheory.Finite.Basic

/-!
# Odd numbers modulo `2^a` and powers of a primitive root (Apostol, Theorems 10.3, 10.5)

* **Theorem 10.3**: for odd `x` and `a ≥ 3`, `x^{φ(2^a)/2} ≡ 1 (mod 2^a)` (so there is no
  primitive root modulo `2^a`, `a ≥ 3`; the non-cyclicity itself is Mathlib's
  `ZMod.isCyclic_units_two_pow_iff`). Apostol's proof: induction on `a` from `x² ≡ 1 (mod 8)`.
* **Theorem 10.5**: if `g` is a primitive root modulo an odd prime `p`, then `g^k` is a quadratic
  residue iff `k` is even.
-/

namespace NTKB.Apostol

/-- **Theorem 10.3**: `x^{2^{a-2}} ≡ 1 (mod 2^a)` for odd `x` and `a ≥ 3` (`φ(2^a)/2 = 2^{a-2}`). -/
@[kb "apostol1976" "Thm 10.3, p. 207"]
theorem pow_two_pow_sub_two_modEq_one {x : ℤ} (hx : Odd x) {a : ℕ} (ha : 3 ≤ a) :
    x ^ (2 ^ (a - 2)) ≡ 1 [ZMOD 2 ^ a] := by
  induction a, ha using Nat.le_induction with
  | base =>
    rw [Int.modEq_iff_dvd, ← neg_sub, dvd_neg]
    simpa using Int.eight_dvd_sq_sub_one_of_odd hx
  | succ a ha ih =>
    rw [Int.modEq_iff_dvd, ← neg_sub, dvd_neg] at ih ⊢
    set y := x ^ (2 ^ (a - 2))
    have hy : Odd y := hx.pow
    have e : x ^ (2 ^ (a + 1 - 2)) = y ^ 2 := by
      rw [show a + 1 - 2 = (a - 2) + 1 by omega, pow_succ, pow_mul]
    rw [e, show y ^ 2 - 1 = (y - 1) * (y + 1) by ring, pow_succ]
    refine mul_dvd_mul ih ?_
    obtain ⟨t, ht⟩ := hy
    exact ⟨t + 1, by rw [ht]; ring⟩

/-- `φ(2^a)/2 = 2^{a-2}` for `a ≥ 2`. -/
lemma totient_two_pow_div_two {a : ℕ} (ha : 2 ≤ a) : (2 ^ a).totient / 2 = 2 ^ (a - 2) := by
  rw [Nat.totient_prime_pow Nat.prime_two (by omega), show a - 1 = (a - 2) + 1 by omega, pow_succ]
  simp

/-- **Theorem 10.5**: if `g` is a primitive root modulo an odd prime `p`, then `g^k` is a
quadratic residue modulo `p` iff `k` is even. -/
@[kb "apostol1976" "Thm 10.5, p. 209"]
theorem isSquare_pow_primitiveRoot_iff {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {g : (ZMod p)ˣ}
    (hg : IsPrimitiveRootMod p g) (k : ℕ) : IsSquare ((g : ZMod p) ^ k) ↔ Even k := by
  have hpp := (Fact.out : p.Prime)
  have hord : orderOf g = p - 1 := by rw [hg, Nat.totient_prime hpp]
  have hodd : Odd p := hpp.odd_of_ne_two hp
  obtain ⟨m, hm⟩ := hodd
  have hp1 : p - 1 = 2 * m := by omega
  constructor
  · rintro ⟨y, hy⟩
    have hy0 : y ≠ 0 := by
      rintro rfl
      simp only [mul_zero] at hy
      exact (pow_ne_zero k g.ne_zero) hy
    have h1 : ((g : ZMod p) ^ k) ^ m = 1 := by
      rw [hy, ← sq, ← pow_mul, ← hp1]
      exact ZMod.pow_card_sub_one_eq_one hy0
    have h2 : g ^ (k * m) = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, pow_mul, h1, Units.val_one]
    have h3 := orderOf_dvd_of_pow_eq_one h2
    rw [hord, hp1] at h3
    have hm0 : 0 < m := by
      rcases Nat.eq_zero_or_pos m with rfl | h
      · exfalso; simp at hm; exact hpp.ne_one hm
      · exact h
    exact even_iff_two_dvd.mpr (Nat.dvd_of_mul_dvd_mul_right hm0 h3)
  · rintro ⟨j, rfl⟩
    exact ⟨(g : ZMod p) ^ j, by rw [pow_add]⟩

end NTKB.Apostol
