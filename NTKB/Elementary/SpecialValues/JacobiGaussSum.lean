/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Elementary.SpecialValues.KroneckerChar

/-!
# The Gauss sum of the Jacobi character of an odd squarefree modulus

For an odd squarefree `m ≥ 1`,
$$\tau\bigl((\cdot/m)\bigr) = \sum_{a \bmod m} J(a\,|\,m)\, e^{2\pi i a/m}
  = \begin{cases}\sqrt m & m \equiv 1 \pmod 4,\\ i\sqrt m & m\equiv 3 \pmod 4.\end{cases}$$

Proof by induction on the number of prime factors: for `m = p m'`, the Chinese remainder theorem
gives `τ((·/m)) = J(m'|p) J(p|m') τ((·/p)) τ((·/m'))` (`NTKB.gaussSum_eq_mul_of_coprime`),
quadratic reciprocity gives `J(m'|p) J(p|m') = (-1)^{(p-1)/2 · (m'-1)/2}`, and the prime case is
Gauss's sign (`NTKB.gaussSum_legendreChar`). The sign `-1` of the reciprocity law exactly corrects
`(i√p)(i√m') = -√(pm')` when `p ≡ m' ≡ 3 (mod 4)`.
-/

noncomputable section

open Complex
open scoped Real

namespace NTKB

/-- The values of `√m` or `i√m` according to `m mod 4`. -/
def sqrtSign (m : ℕ) : ℂ := if m % 4 = 1 then (√m : ℂ) else I * √m

/-- `jacobiChar N`, `N = p m`, has the values `J(a|p) J(a|m)`. -/
theorem jacobiChar_mul_apply {p m N : ℕ} [NeZero p] [NeZero m] [NeZero N] (hN : N = p * m)
    (a : ZMod N) :
    jacobiChar N a = jacobiChar p (ZMod.cast a) * jacobiChar m (ZMod.cast a) := by
  have hJ : ∀ z : ℤ, jacobiSym z N = jacobiSym z p * jacobiSym z m := fun z ↦
    hN ▸ jacobiSym.mul_right z p m
  rw [jacobiChar_apply, jacobiChar_apply, jacobiChar_apply, hJ, Int.cast_mul]
  congr 2
  · refine (jacobiSym_cast_eq (ZMod.cast a : ZMod p) (ZMod.cast a : ℤ) ?_).symm
    rw [ZMod.cast_eq_val (R := ℤ), ZMod.cast_eq_val (R := ZMod p), Int.cast_natCast]
  · refine (jacobiSym_cast_eq (ZMod.cast a : ZMod m) (ZMod.cast a : ℤ) ?_).symm
    rw [ZMod.cast_eq_val (R := ℤ), ZMod.cast_eq_val (R := ZMod m), Int.cast_natCast]

/-- The reciprocity sign: `J(m'|p) J(p|m') = -1` exactly when `p ≡ m' ≡ 3 (mod 4)`. -/
theorem jacobiSym_mul_jacobiSym_eq {p m : ℕ} (hp : Odd p) (hm : Odd m) (hcop : p.Coprime m) :
    jacobiSym m p * jacobiSym p m = if p % 4 = 3 ∧ m % 4 = 3 then -1 else 1 := by
  rw [jacobiSym.quadratic_reciprocity' hm hp, mul_assoc, ← pow_two,
    jacobiSym.sq_one (by rw [Int.gcd_natCast_natCast]; exact hcop), mul_one,
    qrSign.neg_one_pow hp hm]
  have hp2 : p % 2 = 1 := Nat.odd_iff.mp hp
  have hm2 : m % 2 = 1 := Nat.odd_iff.mp hm
  split_ifs with h
  · apply Odd.neg_one_pow
    rw [Nat.odd_mul]
    constructor <;> rw [Nat.odd_iff] <;> omega
  · apply Even.neg_one_pow
    rw [Nat.even_mul]
    by_cases h1 : p % 4 = 3
    · right; rw [Nat.even_iff]; omega
    · left; rw [Nat.even_iff]; omega

/-- Auxiliary form of `gaussSum_jacobiChar`, by strong induction on `m`. -/
theorem gaussSum_jacobiChar_aux : ∀ m : ℕ, Odd m → Squarefree m → ∀ [NeZero m],
    gaussSum (jacobiChar m) ZMod.stdAddChar = sqrtSign m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro hm hsq _
  rcases eq_or_ne m 1 with rfl | hm1
  · -- modulus one
    rw [gaussSum, Fintype.sum_subsingleton _ 0, sqrtSign, if_pos (by norm_num)]
    have hu : IsUnit (0 : ZMod 1) := by
      rw [Subsingleton.elim (0 : ZMod 1) 1]; exact isUnit_one
    rw [jacobiChar_apply_of_isUnit hu, AddChar.map_zero_eq_one, jacobiSym.one_right]
    simp
  -- split off the least prime factor
  set p := m.minFac with hpdef
  have hp : p.Prime := Nat.minFac_prime hm1
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨m', hm'⟩ : p ∣ m := Nat.minFac_dvd m
  have hm'0 : m' ≠ 0 := by
    rintro rfl; rw [mul_zero] at hm'; exact NeZero.ne m hm'
  have : NeZero m' := ⟨hm'0⟩
  have hpodd : Odd p := hm.of_dvd_nat ⟨m', hm'⟩
  have hp2 : p ≠ 2 := by
    rintro h; rw [h] at hpodd; exact absurd hpodd (by decide)
  have hm'odd : Odd m' := hm.of_dvd_nat ⟨p, by rw [hm', mul_comm]⟩
  have hm'sq : Squarefree m' := hsq.squarefree_of_dvd ⟨p, by rw [hm', mul_comm]⟩
  have hcop : p.Coprime m' := by
    rw [Nat.Prime.coprime_iff_not_dvd hp]
    rintro ⟨c, rfl⟩
    have := hsq p ⟨c, by rw [hm']; ring⟩
    exact hp.not_isUnit (Nat.isUnit_iff.mpr (Nat.isUnit_iff.mp this))
  have hlt : m' < m := by
    rw [hm']
    exact lt_mul_left (Nat.pos_of_ne_zero hm'0) hp.one_lt
  have ihm' := @ih m' hlt hm'odd hm'sq ⟨hm'0⟩
  -- the product formula
  have hG := gaussSum_eq_mul_of_coprime hm' hcop (jacobiChar p) (jacobiChar m')
    (jacobiChar m) (jacobiChar_mul_apply hm')
  rw [hG, hm', ihm', jacobiChar_prime, gaussSum_legendreChar p hp2, ← jacobiChar_prime]
  have h1 : jacobiChar p (m' : ZMod p) = (jacobiSym m' p : ℂ) := by
    rw [← jacobiChar_intCast]; simp
  have h2 : jacobiChar m' (p : ZMod m') = (jacobiSym p m' : ℂ) := by
    rw [← jacobiChar_intCast]; simp
  rw [h1, h2]
  have hrec := jacobiSym_mul_jacobiSym_eq hpodd hm'odd hcop
  have hrecC : (jacobiSym m' p : ℂ) * (jacobiSym p m' : ℂ) =
      if p % 4 = 3 ∧ m' % 4 = 3 then -1 else 1 := by
    rw [← Int.cast_mul, hrec]; split_ifs <;> simp
  rw [hrecC]
  have hsqrt : ((√((p * m' : ℕ) : ℝ) : ℝ) : ℂ) = (√(p : ℝ) : ℂ) * (√(m' : ℝ) : ℂ) := by
    rw [Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg _), ofReal_mul]
  have hp4 : p % 4 = 1 ∨ p % 4 = 3 := by have := Nat.odd_iff.mp hpodd; omega
  have hm4 : m' % 4 = 1 ∨ m' % 4 = 3 := by have := Nat.odd_iff.mp hm'odd; omega
  unfold sqrtSign
  rw [hsqrt]
  rcases hp4 with h | h <;> rcases hm4 with h' | h'
  · rw [if_neg (by omega), if_pos h, if_pos h', if_pos (by rw [Nat.mul_mod, h, h'])]; ring
  · rw [if_neg (by omega), if_pos h, if_neg (by omega), if_neg (by rw [Nat.mul_mod, h, h']; norm_num)]
    ring
  · rw [if_neg (by omega), if_neg (by omega), if_pos h', if_neg (by rw [Nat.mul_mod, h, h']; norm_num)]
    ring
  · rw [if_pos ⟨h, h'⟩, if_neg (by omega), if_neg (by omega), if_pos (by rw [Nat.mul_mod, h, h'])]
    ring_nf
    rw [I_sq]
    ring

/-- **Gauss sum of the Jacobi character** of an odd squarefree modulus `m`: `√m` if
`m ≡ 1 (mod 4)` and `i√m` if `m ≡ 3 (mod 4)`. -/
theorem gaussSum_jacobiChar {m : ℕ} [NeZero m] (hm : Odd m) (hsq : Squarefree m) :
    gaussSum (jacobiChar m) ZMod.stdAddChar = sqrtSign m :=
  gaussSum_jacobiChar_aux m hm hsq

end NTKB
