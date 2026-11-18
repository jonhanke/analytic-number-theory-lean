/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Davenport.Ch1to6.Kronecker
import NTKB.Elementary.SpecialValues.KroneckerSymbol
import NTKB.Elementary.QuadraticField.KroneckerPrime

/-!
# Kronecker's extension of the Legendre–Jacobi symbol (Davenport, Chapter 5, pp. 39–40)

Davenport (p. 39) removes the restriction to odd `n` in (8), `(n/p) = (p*/n)`, by Kronecker's
extension of the symbol: `(d/2) = 0` for even `d`, `(d/2) = 1` for `d ≡ ±1 (mod 8)`,
`(d/2) = -1` for `d ≡ ±3 (mod 8)`, and `(d/n)` multiplicative in `n`. Mathlib's `jacobiSym a b` is
only meaningful for odd `b`; here
`kroneckerSym d n = (d/2)^{v₂(n)} J(d | n/2^{v₂(n)})`.

* `kroneckerSym_of_odd`, `kroneckerSym_two`, `kroneckerSym_mul_right`: the definition
  (row 5-12);
* `jacobiSym_eq_kroneckerSym`: **(8) for every `n ≥ 1`**, `J(n | P) = (P*/n)` with
  `P* = (-1)^{(P-1)/2} P`, for every odd `P ≥ 1` (Davenport states it for `P` squarefree;
  row 5-12);
* `kroneckerSym_neg_four`, `kroneckerSym_eight`, `kroneckerSym_neg_eight`: the basic characters
  `(-4/n) = χ₄(n)`, `(8/n) = χ₈(n)`, `(-8/n) = χ₄(n) χ₈(n)` (Mathlib's `χ₈'`) for every `n`
  (row 5-13);
* `kroneckerSym_mul_left`: `(d₁ d₂/n) = (d₁/n)(d₂/n)` for all integers `d₁, d₂` (row 5-13;
  Davenport states it for relatively prime `d₁, d₂`);
* `kroneckerChar_eq_kroneckerSym`: for a fundamental discriminant `D` the character
  `NTKB.kroneckerChar D` of modulus `|D|` is `n ↦ (D/n)` for every `n` (rows 5-12, 5-13; with
  `NTKB.kroneckerChar_isPrimitive`, the symbol is a real primitive character to the modulus `|D|`).
-/

namespace NTKB.Davenport

/-- Kronecker's value `(d/2)`: `0` for even `d`, otherwise `χ₈(d)` (`1` for `d ≡ ±1`, `-1` for
`d ≡ ±3 (mod 8)`). -/
def kroneckerTwo (d : ℤ) : ℤ := if d % 2 = 0 then 0 else ZMod.χ₈ (d : ZMod 8)

/-- **Kronecker's symbol** `(d/n) = (d/2)^{v₂(n)} J(d | n/2^{v₂(n)})` (Davenport, Ch. 5, p. 39). -/
def kroneckerSym (d : ℤ) (n : ℕ) : ℤ :=
  kroneckerTwo d ^ n.factorization 2 * jacobiSym d (n / 2 ^ n.factorization 2)

/-- `(d/2^k m) = (d/2)^k J(d | m)` for odd `m`. -/
theorem kroneckerSym_two_pow_mul (d : ℤ) (k : ℕ) {m : ℕ} (hm : Odd m) :
    kroneckerSym d (2 ^ k * m) = kroneckerTwo d ^ k * jacobiSym d m := by
  have hm0 : m ≠ 0 := by have := Nat.odd_iff.mp hm; omega
  have h2m : ¬ 2 ∣ m := by have := Nat.odd_iff.mp hm; omega
  have hf : (2 ^ k * m).factorization 2 = k := by
    rw [Nat.factorization_mul (by positivity) hm0, Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd h2m, add_zero]
  rw [kroneckerSym, hf, Nat.mul_div_cancel_left _ (by positivity)]

theorem kroneckerTwo_of_odd {d : ℤ} (hd : d % 2 = 1) :
    kroneckerTwo d = ZMod.χ₈ (d : ZMod 8) := by
  rw [kroneckerTwo, if_neg (by omega)]

theorem kroneckerTwo_mul (d₁ d₂ : ℤ) :
    kroneckerTwo (d₁ * d₂) = kroneckerTwo d₁ * kroneckerTwo d₂ := by
  unfold kroneckerTwo
  rcases Int.emod_two_eq_zero_or_one d₁ with h₁ | h₁ <;>
    rcases Int.emod_two_eq_zero_or_one d₂ with h₂ | h₂
  · rw [if_pos h₁, if_pos (by rw [Int.mul_emod, h₁]; simp), zero_mul]
  · rw [if_pos h₁, if_pos (by rw [Int.mul_emod, h₁]; simp), zero_mul]
  · rw [if_pos h₂, if_pos (by rw [Int.mul_emod, h₂]; simp), mul_zero]
  · have h12 : d₁ * d₂ % 2 = 1 := by rw [Int.mul_emod, h₁, h₂]; rfl
    rw [if_neg (by rw [h12]; decide), if_neg (by rw [h₁]; decide), if_neg (by rw [h₂]; decide),
      Int.cast_mul, map_mul]

/-- For odd `n`, `(d/n)` is Jacobi's symbol. -/
@[kb "davenport1980" "Ch 5, p. 39"]
theorem kroneckerSym_of_odd (d : ℤ) {n : ℕ} (hn : Odd n) : kroneckerSym d n = jacobiSym d n := by
  have := kroneckerSym_two_pow_mul d 0 hn
  simpa using this

/-- `(d/2)` is Kronecker's value. -/
@[kb "davenport1980" "Ch 5, p. 39"]
theorem kroneckerSym_two (d : ℤ) : kroneckerSym d 2 = kroneckerTwo d := by
  have := kroneckerSym_two_pow_mul d 1 (m := 1) odd_one
  simpa using this

/-- `(d/n)` is multiplicative in `n`. -/
@[kb "davenport1980" "Ch 5, p. 39"]
theorem kroneckerSym_mul_right (d : ℤ) {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    kroneckerSym d (m * n) = kroneckerSym d m * kroneckerSym d n := by
  obtain ⟨a, m', hm', rfl⟩ := Nat.exists_eq_two_pow_mul_odd hm
  obtain ⟨b, n', hn', rfl⟩ := Nat.exists_eq_two_pow_mul_odd hn
  have hm0 : m' ≠ 0 := by rintro rfl; simp at hm'
  have hn0 : n' ≠ 0 := by rintro rfl; simp at hn'
  rw [show 2 ^ a * m' * (2 ^ b * n') = 2 ^ (a + b) * (m' * n') by ring,
    kroneckerSym_two_pow_mul d _ (hm'.mul hn'), kroneckerSym_two_pow_mul d _ hm',
    kroneckerSym_two_pow_mul d _ hn', jacobiSym.mul_right' d hm0 hn0, pow_add]
  ring

/-- **Davenport, Ch. 5, (8), for every `n ≥ 1`** (Kronecker's extension): for odd `P ≥ 1` and
`P* = (-1)^{(P-1)/2} P`, `J(n | P) = (P*/n)`. -/
@[kb "davenport1980" "Ch 5, p. 39, (8)"]
theorem jacobiSym_eq_kroneckerSym {P : ℕ} (hP : Odd P) {n : ℕ} (hn : n ≠ 0) :
    jacobiSym n P = kroneckerSym ((-1) ^ (P / 2) * P) n := by
  obtain ⟨k, m, hm, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hn
  have hP2 : (P : ℤ) % 2 = 1 := by have := Nat.odd_iff.mp hP; omega
  have hPs : ((-1) ^ (P / 2) * (P : ℤ)) % 2 = 1 := by
    rcases neg_one_pow_eq_or ℤ (P / 2) with h | h <;> rw [h] <;> omega
  rw [kroneckerSym_two_pow_mul _ _ hm, kroneckerTwo_of_odd hPs, Nat.cast_mul, Nat.cast_pow,
    jacobiSym.mul_left, jacobiSym.pow_left, Nat.cast_ofNat, jacobiSym.at_two hP,
    jacobiSym.mul_left, jacobiSym.pow_left, jacobiSym.at_neg_one hm,
    jacobiSym.quadratic_reciprocity hm hP, ZMod.χ₄_eq_neg_one_pow (Nat.odd_iff.mp hm)]
  have h8 : ZMod.χ₈ (((-1) ^ (P / 2) * (P : ℤ) : ℤ) : ZMod 8) = ZMod.χ₈ (P : ZMod 8) := by
    rw [Int.cast_mul, map_mul, Int.cast_pow, map_pow, Int.cast_neg, Int.cast_one,
      show ZMod.χ₈ (-1) = 1 by decide, one_pow, one_mul, Int.cast_natCast]
  rw [h8, ← pow_mul, mul_comm (m / 2)]

/-- **Davenport, Ch. 5, p. 39**: `(-4/n) = χ₄(n)` for every `n`. -/
@[kb "davenport1980" "Ch 5, p. 39"]
theorem kroneckerSym_neg_four {n : ℕ} (hn : n ≠ 0) :
    kroneckerSym (-4) n = ZMod.χ₄ (n : ZMod 4) := by
  obtain ⟨k, m, hm, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hn
  have hm2 := Nat.odd_iff.mp hm
  rw [kroneckerSym_two_pow_mul _ _ hm]
  rcases k with _ | k
  · simp only [pow_zero, one_mul]
    rw [show (-4 : ℤ) = -1 * 2 ^ 2 by norm_num, jacobiSym.mul_left,
      jacobiSym.pow_left, jacobiSym.at_neg_one hm, jacobiSym.at_two hm,
      ZMod.χ₈_nat_eq_if_mod_eight]
    split_ifs <;> first | (exfalso; omega) | simp
  · rw [show kroneckerTwo (-4) = 0 by decide, zero_pow (by omega), zero_mul,
      ZMod.χ₄_nat_eq_if_mod_four, if_pos (by rw [pow_succ]; simp [Nat.mul_mod])]

/-- **Davenport, Ch. 5, p. 39**: `(8/n) = χ₈(n)` for every `n`. -/
@[kb "davenport1980" "Ch 5, p. 39"]
theorem kroneckerSym_eight {n : ℕ} (hn : n ≠ 0) : kroneckerSym 8 n = ZMod.χ₈ (n : ZMod 8) := by
  obtain ⟨k, m, hm, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hn
  have hm2 := Nat.odd_iff.mp hm
  rw [kroneckerSym_two_pow_mul _ _ hm]
  rcases k with _ | k
  · simp only [pow_zero, one_mul]
    rw [show (8 : ℤ) = 2 ^ 3 by norm_num,
      jacobiSym.pow_left, jacobiSym.at_two hm, ZMod.χ₈_nat_eq_if_mod_eight]
    split_ifs <;> first | (exfalso; omega) | simp
  · rw [show kroneckerTwo 8 = 0 by decide, zero_pow (by omega), zero_mul,
      ZMod.χ₈_nat_eq_if_mod_eight, if_pos (by rw [pow_succ]; simp [Nat.mul_mod])]

/-- **Davenport, Ch. 5, p. 39**: `(-8/n) = χ₄(n) χ₈(n)` (Mathlib's `χ₈'`) for every `n`. -/
@[kb "davenport1980" "Ch 5, p. 39"]
theorem kroneckerSym_neg_eight {n : ℕ} (hn : n ≠ 0) :
    kroneckerSym (-8) n = ZMod.χ₈' (n : ZMod 8) := by
  obtain ⟨k, m, hm, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hn
  have hm2 := Nat.odd_iff.mp hm
  rw [kroneckerSym_two_pow_mul _ _ hm]
  rcases k with _ | k
  · simp only [pow_zero, one_mul]
    rw [show (-8 : ℤ) = -1 * 2 ^ 3 by norm_num, jacobiSym.mul_left,
      jacobiSym.pow_left, jacobiSym.at_neg_one hm, jacobiSym.at_two hm,
      ZMod.χ₈_nat_eq_if_mod_eight, ZMod.χ₄_nat_eq_if_mod_four, ZMod.χ₈'_nat_eq_if_mod_eight]
    split_ifs <;> first | (exfalso; omega) | simp
  · rw [show kroneckerTwo (-8) = 0 by decide, zero_pow (by omega), zero_mul,
      ZMod.χ₈'_nat_eq_if_mod_eight, if_pos (by rw [pow_succ]; simp [Nat.mul_mod])]

/-- **Davenport, Ch. 5, p. 40**: `(d₁ d₂/n) = (d₁/n)(d₂/n)`, for all integers `d₁, d₂`. -/
@[kb "davenport1980" "Ch 5, p. 40"]
theorem kroneckerSym_mul_left (d₁ d₂ : ℤ) (n : ℕ) :
    kroneckerSym (d₁ * d₂) n = kroneckerSym d₁ n * kroneckerSym d₂ n := by
  rw [kroneckerSym, kroneckerSym, kroneckerSym, kroneckerTwo_mul, jacobiSym.mul_left, mul_pow]
  ring

/-- **Davenport, Ch. 5, p. 40**: for a fundamental discriminant `D`, the real primitive character
`NTKB.kroneckerChar D` modulo `|D|` is Kronecker's symbol `n ↦ (D/n)` at every `n ≥ 1`. -/
@[kb "davenport1980" "Ch 5, p. 40"]
theorem kroneckerChar_eq_kroneckerSym {D : ℤ} (hD : IsFundamentalDiscriminant D) {n : ℕ}
    (hn : n ≠ 0) : kroneckerChar D (n : ZMod D.natAbs) = (kroneckerSym D n : ℂ) := by
  have := NTKB.QuadraticField.natAbs_ne_zero_of_fundamental hD
  obtain ⟨k, m, hm, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hn
  rw [kroneckerSym_two_pow_mul _ _ hm, Nat.cast_mul, Nat.cast_pow, map_mul, map_pow,
    kroneckerChar_apply_odd hD hm, Int.cast_mul, Int.cast_pow]
  congr 1
  rcases k with _ | k
  · simp
  congr 1
  rcases Int.emod_two_eq_zero_or_one D with h | h
  · have h0 := kroneckerChar_natCast_eq_zero_of_even h (n := 2) (dvd_refl 2)
    rw [h0, kroneckerTwo, if_pos h, Int.cast_zero]
  · have h2 := NTKB.QuadraticField.kroneckerChar_two hD h
    have h41 : D % 4 = 1 := by
      rcases NTKB.QuadraticField.emod_four_of_isFundamental hD with h' | h' <;> omega
    rw [h2, kroneckerTwo_of_odd h, ZMod.χ₈_int_eq_if_mod_eight]
    have h2' : ¬ D % 2 = 0 := by omega
    rcases (show D % 8 = 1 ∨ D % 8 = 5 by omega) with h8 | h8 <;> simp [h8, h2']

end NTKB.Davenport
