/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.NumberTheory.LegendreSymbol.Basic
import NTKB.Attr

/-!
# The equation `y² = x³ + k` (Apostol, Chapter 9, §9.8, Theorem 9.12)

**Theorem 9.12.** The Diophantine equation `y² = x³ + k` has no integer solutions if
`k = (4n - 1)³ - 4m²` with `m, n` integers such that no prime `p ≡ -1 (mod 4)` divides `m`.

Apostol's proof: modulo 4, `x ≡ 1`; with `a = 4n - 1`, `y² + 4m² = (x + a)(x² - ax + a²)` and
`x² - ax + a² ≡ -1 (mod 4)` has a prime factor `p ≡ -1 (mod 4)`; then `y² ≡ -(2m)² (mod p)` with
`p ∤ 2m`, so `-1` is a square mod `p`, impossible (Mathlib's `ZMod.mod_four_ne_three_of_sq_eq_neg_sq'`).
-/

namespace NTKB.Apostol

/-- A positive integer `≡ 3 (mod 4)` has a prime factor `≡ 3 (mod 4)`. -/
theorem exists_prime_mod_four_eq_three_dvd {q : ℕ} (hq : q % 4 = 3) :
    ∃ p, p.Prime ∧ p % 4 = 3 ∧ p ∣ q := by
  by_contra hcon
  push_neg at hcon
  have hq0 : q ≠ 0 := by omega
  have hodd : ¬ 2 ∣ q := by omega
  -- every prime factor is `≡ 1 (mod 4)`, so `q ≡ 1`
  have hall : ∀ p ∈ q.primeFactorsList, ((p : ℕ) : ZMod 4) = 1 := by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactorsList hp
    have hpq := Nat.dvd_of_mem_primeFactorsList hp
    have h3 := hcon p hpp
    have h2 : p ≠ 2 := fun h ↦ hodd (h ▸ hpq)
    have hpodd := hpp.eq_one_or_self_of_dvd 2
    have h1 : p % 4 = 1 := by
      have := hpp.eq_two_or_odd
      rcases this with h | h
      · exact absurd h h2
      · have : p % 4 ≠ 3 := fun h' ↦ h3 h' hpq
        omega
    have : ((p : ℕ) : ZMod 4) = ((p % 4 : ℕ) : ZMod 4) := (ZMod.natCast_mod p 4).symm
    rw [this, h1]; rfl
  have hprod : ((q : ℕ) : ZMod 4) = 1 := by
    rw [← Nat.prod_primeFactorsList hq0, Nat.cast_list_prod]
    apply List.prod_eq_one
    intro x hx
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
    exact hall p hp
  have : ((q : ℕ) : ZMod 4) = ((q % 4 : ℕ) : ZMod 4) := (ZMod.natCast_mod q 4).symm
  rw [this, hq] at hprod
  exact absurd hprod (by decide)

/-- **Apostol, Theorem 9.12.** If `k = (4n - 1)³ - 4m²` where no prime `p ≡ -1 (mod 4)` divides
`m`, then `y² = x³ + k` has no integer solutions. -/
@[kb "apostol1976" "Thm 9.12, p. 191"]
theorem sq_ne_cube_add {m n : ℤ} (hm : ∀ p : ℕ, p.Prime → p % 4 = 3 → ¬ (p : ℤ) ∣ m)
    (x y : ℤ) : y ^ 2 ≠ x ^ 3 + ((4 * n - 1) ^ 3 - 4 * m ^ 2) := by
  intro h
  set a := 4 * n - 1 with ha
  -- modulo 4: `x ≡ 1`
  have hx : x % 4 = 1 := by
    have h4 := congrArg (fun z : ℤ ↦ z % 4) h
    have hy : y ^ 2 % 4 = 0 ∨ y ^ 2 % 4 = 1 := by
      rcases Int.emod_two_eq_zero_or_one y with h2 | h2 <;>
      · have : y % 4 = 0 ∨ y % 4 = 1 ∨ y % 4 = 2 ∨ y % 4 = 3 := by omega
        rcases this with h' | h' | h' | h' <;> simp [pow_two, Int.mul_emod, h']
    have hxm : x % 4 = 0 ∨ x % 4 = 1 ∨ x % 4 = 2 ∨ x % 4 = 3 := by omega
    have hk : ((4 * n - 1) ^ 3 - 4 * m ^ 2) % 4 = 3 := by
      have : (4 * n - 1) ^ 3 - 4 * m ^ 2 = 4 * (16 * n ^ 3 - 12 * n ^ 2 + 3 * n - m ^ 2 - 1) + 3 := by
        ring
      rw [this]; omega
    rcases hxm with h' | h' | h' | h'
    · exfalso
      have : (x ^ 3 + ((4 * n - 1) ^ 3 - 4 * m ^ 2)) % 4 = 3 := by
        rw [Int.add_emod, hk, pow_succ, pow_two, Int.mul_emod, Int.mul_emod x x, h']; norm_num
      have hy' := hy
      rw [show y ^ 2 % 4 = (x ^ 3 + ((4 * n - 1) ^ 3 - 4 * m ^ 2)) % 4 from h4] at hy'
      rcases hy' with e | e <;> rw [e] at this <;> norm_num at this
    · exact h'
    · exfalso
      have : (x ^ 3 + ((4 * n - 1) ^ 3 - 4 * m ^ 2)) % 4 = 3 := by
        rw [Int.add_emod, hk, pow_succ, pow_two, Int.mul_emod, Int.mul_emod x x, h']; norm_num
      have hy' := hy
      rw [show y ^ 2 % 4 = (x ^ 3 + ((4 * n - 1) ^ 3 - 4 * m ^ 2)) % 4 from h4] at hy'
      rcases hy' with e | e <;> rw [e] at this <;> norm_num at this
    · exfalso
      have : (x ^ 3 + ((4 * n - 1) ^ 3 - 4 * m ^ 2)) % 4 = 2 := by
        rw [Int.add_emod, hk, pow_succ, pow_two, Int.mul_emod, Int.mul_emod x x, h']; norm_num
      have hy' := hy
      rw [show y ^ 2 % 4 = (x ^ 3 + ((4 * n - 1) ^ 3 - 4 * m ^ 2)) % 4 from h4] at hy'
      rcases hy' with e | e <;> rw [e] at this <;> norm_num at this
  -- the factor `Q = x² - ax + a² ≡ 3 (mod 4)`, `Q > 0`
  set Q := x ^ 2 - a * x + a ^ 2 with hQ
  have hfac : y ^ 2 + 4 * m ^ 2 = (x + a) * Q := by rw [hQ]; linear_combination h
  have hQ4 : Q % 4 = 3 := by
    obtain ⟨u, hu⟩ : ∃ u, x = 4 * u + 1 := ⟨x / 4, by omega⟩
    have : Q = 4 * (4 * u ^ 2 + 2 * u - (4 * n - 1) * u + 4 * n ^ 2 - 3 * n) + 3 := by
      rw [hQ, hu, ha]; ring
    rw [this]; omega
  have hQpos : 0 < Q := by
    have h1 : 0 ≤ Q := by
      rw [hQ]; nlinarith [sq_nonneg (2 * x - a), sq_nonneg a]
    rcases eq_or_lt_of_le h1 with h0 | h0
    · rw [← h0] at hQ4; norm_num at hQ4
    · exact h0
  -- a prime `p ≡ 3 (mod 4)` divides `Q`
  obtain ⟨p, hp, hp3, hpQ⟩ := exists_prime_mod_four_eq_three_dvd (q := Q.toNat) (by omega)
  have hpQ' : (p : ℤ) ∣ Q := by
    have := Int.natCast_dvd_natCast.2 hpQ
    rwa [Int.toNat_of_nonneg hQpos.le] at this
  have hpm := hm p hp hp3
  have : Fact p.Prime := ⟨hp⟩
  -- in `ZMod p`: `y² = -(2m)²` with `2m ≠ 0`
  have hdiv : (p : ℤ) ∣ y ^ 2 + 4 * m ^ 2 := by
    rw [hfac]; exact Dvd.dvd.mul_left hpQ' _
  have hz : ((y : ℤ) : ZMod p) ^ 2 = -(((2 * m : ℤ) : ZMod p)) ^ 2 := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).2 hdiv
    push_cast at this ⊢
    linear_combination this
  have h2m : (((2 * m : ℤ)) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    intro hd
    have hp2 : p ≠ 2 := by omega
    rcases (Nat.prime_iff_prime_int.mp hp).dvd_or_dvd hd with h2 | h2
    · have : (p : ℤ) ≤ 2 := Int.le_of_dvd (by norm_num) h2
      have : 2 ≤ p := hp.two_le
      omega
    · exact hpm h2
  exact ZMod.mod_four_ne_three_of_sq_eq_neg_sq' h2m hz hp3

end NTKB.Apostol
