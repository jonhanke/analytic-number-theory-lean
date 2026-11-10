/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Elementary.SpecialValues.QuadraticValues
import NTKB.Elementary.SpecialValues.QuadraticGaussSum
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.FieldTheory.Finite.Basic

/-!
# Davenport, Chapters 1 and 6: `L(1, χ)` for a real character as a finite sum

Davenport, *Multiplicative Number Theory*, §1 and §6.

* `L(1, χ) > 0` for every real nonprincipal character (§1, p. 7: the Euler product makes
  `L(s) > 0` for `s > 1`, and `L` is continuous at `1` with `L(1) ≠ 0`; §6, p. 50).
* Formula (17) of §6: for a fundamental discriminant `d < 0`,
  `L(1, χ) = -(π / |d|^{3/2}) ∑_{m=1}^{|d|} m (d/m)`.
* Formula (7) of §1: its case `d = -q`, `q ≡ 3 (mod 4)` prime:
  `L(1) = -(π / q^{3/2}) ∑_{m=1}^{q-1} m (m/q)`.
* §1, p. 9: the sum `∑ m (m/q)` is odd, hence `L(1) ≠ 0` (Dirichlet's proof for `q ≡ 3 mod 4`).
* §6, p. 51: for `q > 3` the sum is divisible by `q` (Euler's criterion), so the number
  `H = -(1/q) ∑ m (m/q)` of Jacobi's formula (19) is a positive integer.

The value of `L(1, χ)` for odd primitive `χ` is `NTKB.LFunction_one_of_odd` (the special
values) and Gauss's sign is `NTKB.gaussSum_kroneckerChar`, `NTKB.gaussSum_legendreChar`.
-/

noncomputable section

open Complex DirichletCharacter Finset
open scoped Real ComplexOrder

namespace NTKB.Davenport

variable {N : ℕ} [NeZero N]

/-- `∑_{a mod N} χ(a) a = ∑_{m=1}^{N} m χ(m)` for `N ≠ 1` (residues represented by `0 ≤ a < N`;
the terms `m = 0` and `m = N` vanish). -/
theorem sum_zmod_mul_val_eq_sum_Icc (χ : DirichletCharacter ℂ N) (hN : N ≠ 1) :
    ∑ a : ZMod N, χ⁻¹ a * (a.val : ℂ) = ∑ m ∈ Icc 1 N, (m : ℂ) * χ⁻¹ m := by
  have h1 : ∑ a : ZMod N, χ⁻¹ a * (a.val : ℂ) = ∑ m ∈ range N, (m : ℂ) * χ⁻¹ m := by
    rw [← sum_val_eq_sum_range (fun m ↦ (m : ℂ) * χ⁻¹ m)]
    refine sum_congr rfl fun a _ ↦ ?_
    rw [ZMod.natCast_zmod_val, mul_comm]
  have hpos : 0 < N := NeZero.pos N
  rw [h1, range_eq_Ico, sum_eq_sum_Ico_succ_bot hpos, ← Finset.Ico_add_one_right_eq_Icc,
    sum_Ico_succ_top (Nat.succ_le_of_lt hpos), ZMod.natCast_self, (χ⁻¹).map_zero' hN, mul_zero,
    add_zero]
  simp

omit [NeZero N] in
/-- An odd character is nontrivial. -/
theorem ne_one_of_odd {χ : DirichletCharacter ℂ N} (hodd : χ.Odd) : χ ≠ 1 := by
  rintro rfl
  exact DirichletCharacter.Odd.not_even _ hodd DirichletCharacter.even_one

/-- For a primitive odd character `χ` modulo `N`:
`L(1, χ) = (π i τ(χ) / N²) ∑_{m=1}^{N} m χ̄(m)`. -/
theorem LFunction_one_of_odd_eq_sum {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive)
    (hodd : χ.Odd) :
    LFunction χ 1 =
      π * I * gaussSum χ ZMod.stdAddChar / (N : ℂ) ^ 2 * ∑ m ∈ Icc 1 N, (m : ℂ) * χ⁻¹ m := by
  have hχ1 : χ ≠ 1 := ne_one_of_odd hodd
  have hinv : χ⁻¹ ≠ 1 := inv_ne_one.mpr hχ1
  have hN1 : N ≠ 1 := fun h ↦ hχ1 (χ.level_one' h)
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hB := natCast_mul_generalizedBernoulli_one_of_ne_one hinv
  rw [sum_zmod_mul_val_eq_sum_Icc χ hN1] at hB
  rw [LFunction_one_of_odd hχ hodd, ← hB]
  field_simp

/-- **Davenport §6, formula (17).** For a fundamental discriminant `d < 0` and `χ = (d/·)`:
`L(1, χ) = -(π / |d|^{3/2}) ∑_{m=1}^{|d|} m χ(m)`. -/
@[kb "davenport1980" "Ch 6, p. 50, (17)"]
theorem LFunction_one_kroneckerChar_of_neg {D : ℤ} (hD : IsFundamentalDiscriminant D)
    (hneg : D < 0) [NeZero D.natAbs] :
    LFunction (kroneckerChar D) 1 =
      -((π / (D.natAbs : ℝ) ^ ((3 : ℝ) / 2) : ℝ) : ℂ) *
        ∑ m ∈ Icc 1 D.natAbs, (m : ℂ) * kroneckerChar D m := by
  have hodd : (kroneckerChar D).Odd := by
    rw [DirichletCharacter.Odd, kroneckerChar_neg_one hD, if_neg (not_lt.mpr hneg.le)]
  rw [LFunction_one_of_odd_eq_sum (kroneckerChar_isPrimitive hD) hodd, kroneckerChar_inv hD,
    gaussSum_kroneckerChar hD, if_neg (not_lt.mpr hneg.le)]
  have hDabs : (-D : ℝ) = (D.natAbs : ℝ) := by
    rw [Nat.cast_natAbs, Int.cast_abs, abs_of_neg (Int.cast_lt_zero.mpr hneg)]
  rw [hDabs]
  set n : ℝ := (D.natAbs : ℝ)
  have hn : 0 < n := by
    simp only [n]; exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne _)
  have hpow : n ^ ((3 : ℝ) / 2) = n * √n := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_one_add' hn.le (by norm_num)]
    norm_num
  have hsq : (√n : ℂ) * √n = n := by
    rw [← ofReal_mul, Real.mul_self_sqrt hn.le]
  have hs0 : (√n : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hn).ne'
  have hn0 : (n : ℂ) ≠ 0 := ofReal_ne_zero.mpr hn.ne'
  rw [hpow, ofReal_div, ofReal_mul]
  have hnat : ((D.natAbs : ℕ) : ℂ) = (n : ℂ) := by simp only [n, ofReal_natCast]
  rw [hnat]
  field_simp
  rw [I_sq, ← hsq]
  ring

/-! ### The prime case `q ≡ 3 (mod 4)` (§1) -/

section Prime

variable {q : ℕ} [Fact q.Prime]

theorem legendreChar_natCast (m : ℕ) : legendreChar q m = (legendreSym q m : ℂ) := by
  rw [legendreChar_apply, legendreSym, Int.cast_natCast]

theorem legendreChar_isQuadratic : (legendreChar q).IsQuadratic :=
  (quadraticChar_isQuadratic (ZMod q)).comp _

theorem legendreChar_odd (hq : q % 4 = 3) : (legendreChar q).Odd := by
  rw [DirichletCharacter.Odd, legendreChar_apply, quadraticChar_neg_one, ZMod.card,
    ZMod.χ₄_nat_three_mod_four hq]
  · simp
  · rw [ZMod.ringChar_zmod_n]; omega

/-- **Davenport §1, formula (7).** For a prime `q ≡ 3 (mod 4)`:
`L(1) = -(π / q^{3/2}) ∑_{m=1}^{q-1} m (m/q)`. -/
@[kb "davenport1980" "Ch 1, p. 8, (7)"]
theorem LFunction_one_legendreChar (hq : q % 4 = 3) :
    LFunction (legendreChar q) 1 =
      -((π / (q : ℝ) ^ ((3 : ℝ) / 2) : ℝ) : ℂ) *
        ∑ m ∈ Ico 1 q, (m : ℂ) * (legendreSym q m : ℂ) := by
  have hq2 : q ≠ 2 := by omega
  have hprim : (legendreChar q).IsPrimitive := by
    rw [← jacobiChar_prime]; exact isPrimitive_jacobiChar_prime q hq2
  rw [LFunction_one_of_odd_eq_sum hprim (legendreChar_odd hq), legendreChar_isQuadratic.inv,
    gaussSum_legendreChar q hq2, if_neg (by omega)]
  have hq1 : 1 ≤ q := (Fact.out : q.Prime).one_lt.le
  have hq1' : q ≠ 1 := (Fact.out : q.Prime).one_lt.ne'
  rw [← Finset.Ico_add_one_right_eq_Icc, sum_Ico_succ_top hq1, ZMod.natCast_self,
    (legendreChar q).map_zero' hq1', mul_zero, add_zero]
  simp_rw [legendreChar_natCast]
  set n : ℝ := (q : ℝ)
  have hn : 0 < n := by simp only [n]; exact_mod_cast (Fact.out : q.Prime).pos
  have hpow : n ^ ((3 : ℝ) / 2) = n * √n := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_one_add' hn.le (by norm_num)]
    norm_num
  have hsq : (√n : ℂ) * √n = n := by
    rw [← ofReal_mul, Real.mul_self_sqrt hn.le]
  have hs0 : (√n : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hn).ne'
  have hn0 : (n : ℂ) ≠ 0 := ofReal_ne_zero.mpr hn.ne'
  rw [hpow, ofReal_div, ofReal_mul]
  have hnat : ((q : ℕ) : ℂ) = (n : ℂ) := by simp only [n, ofReal_natCast]
  rw [hnat]
  field_simp
  rw [I_sq, ← hsq]
  ring

/-- `(m/q) = ±1` for `0 < m < q`. -/
theorem legendreSym_eq_one_or_neg_one_of_mem_Ico {m : ℕ} (hm : m ∈ Ico 1 q) :
    legendreSym q m = 1 ∨ legendreSym q m = -1 := by
  rw [mem_Ico] at hm
  refine legendreSym.eq_one_or_neg_one q ?_
  rw [Int.cast_natCast, Ne, ZMod.natCast_eq_zero_iff]
  exact fun h ↦ absurd (Nat.le_of_dvd (by omega) h) (by omega)

/-- **Davenport §1, p. 9.** For a prime `q ≡ 3 (mod 4)` the sum `∑_{m=1}^{q-1} m (m/q)` is an
odd integer: it has the parity of `∑ m = q(q-1)/2`. -/
@[kb "davenport1980" "Ch 1, p. 9"]
theorem odd_sum_mul_legendreSym (hq : q % 4 = 3) :
    Odd (∑ m ∈ Ico 1 q, (m : ℤ) * legendreSym q m) := by
  rw [← ZMod.intCast_eq_one_iff_odd, Int.cast_sum]
  have hterm : ∀ m ∈ Ico 1 q, (((m : ℤ) * legendreSym q m : ℤ) : ZMod 2) = ((m : ℕ) : ZMod 2) := by
    intro m hm
    rcases legendreSym_eq_one_or_neg_one_of_mem_Ico hm with h | h <;> rw [h] <;> push_cast
    · ring
    · rw [show (-1 : ZMod 2) = 1 from rfl, mul_one]
  rw [sum_congr rfl hterm, ← Nat.cast_sum]
  have hsum : ∑ m ∈ Ico 1 q, m = ∑ m ∈ range q, m := by
    rw [range_eq_Ico, sum_eq_sum_Ico_succ_bot (Fact.out : q.Prime).pos]
    simp
  rw [hsum, ZMod.natCast_eq_one_iff_odd, Nat.odd_iff]
  have h2 := sum_range_id_mul_two q
  have : (∑ i ∈ range q, i) = q * ((q - 1) / 2) := by
    have h4 : q - 1 = (q - 1) / 2 * 2 := by omega
    have h5 : (∑ i ∈ range q, i) * 2 = q * ((q - 1) / 2) * 2 := by
      rw [h2, mul_assoc, ← h4]
    omega
  rw [this, Nat.mul_mod]
  have h1 : q % 2 = 1 := by omega
  have h3 : (q - 1) / 2 % 2 = 1 := by omega
  rw [h1, h3]

/-- **Davenport §1, p. 9.** Dirichlet's proof that `L(1) ≠ 0` for `q ≡ 3 (mod 4)`: by (7),
`L(1)` is a nonzero multiple of the odd, hence nonzero, integer `∑ m (m/q)`. -/
@[kb "davenport1980" "Ch 1, p. 9"]
theorem LFunction_one_legendreChar_ne_zero (hq : q % 4 = 3) :
    LFunction (legendreChar q) 1 ≠ 0 := by
  rw [LFunction_one_legendreChar hq]
  have hpos : (0 : ℝ) < π / (q : ℝ) ^ ((3 : ℝ) / 2) :=
    div_pos Real.pi_pos (Real.rpow_pos_of_pos (by exact_mod_cast (Fact.out : q.Prime).pos) _)
  refine mul_ne_zero (neg_ne_zero.mpr (ofReal_ne_zero.mpr hpos.ne')) ?_
  have hne : (∑ m ∈ Ico 1 q, (m : ℤ) * legendreSym q m) ≠ 0 := by
    intro h
    have hodd := odd_sum_mul_legendreSym hq
    rw [h] at hodd
    exact absurd hodd (by decide)
  intro h0
  apply hne
  have : ((∑ m ∈ Ico 1 q, (m : ℤ) * legendreSym q m : ℤ) : ℂ) = 0 := by
    rw [← h0]; push_cast; rfl
  exact_mod_cast this

/-- **Davenport §6, p. 51.** For a prime `q > 3`, `q` divides `∑_{m=1}^{q-1} m (m/q)`: by Euler's
criterion the sum is `≡ ∑ m^{(q+1)/2} ≡ 0 (mod q)`. -/
@[kb "davenport1980" "Ch 6, p. 51"]
theorem dvd_sum_mul_legendreSym (hq3 : 3 < q) :
    (q : ℤ) ∣ ∑ m ∈ Ico 1 q, (m : ℤ) * legendreSym q m := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sum]
  have hterm : ∀ m ∈ Ico 1 q,
      (((m : ℤ) * legendreSym q m : ℤ) : ZMod q) = ((m : ℕ) : ZMod q) ^ (q / 2 + 1) := by
    intro m _
    rw [Int.cast_mul, legendreSym.eq_pow, Int.cast_natCast, pow_succ']
  rw [sum_congr rfl hterm]
  have hsum : ∑ m ∈ Ico 1 q, ((m : ℕ) : ZMod q) ^ (q / 2 + 1) =
      ∑ m ∈ range q, ((m : ℕ) : ZMod q) ^ (q / 2 + 1) := by
    rw [range_eq_Ico, sum_eq_sum_Ico_succ_bot (Fact.out : q.Prime).pos]
    simp
  rw [hsum, ← sum_val_eq_sum_range (fun m ↦ ((m : ℕ) : ZMod q) ^ (q / 2 + 1))]
  simp only [ZMod.natCast_zmod_val]
  apply FiniteField.sum_pow_lt_card_sub_one
  rw [ZMod.card]
  have : q % 2 = 1 := Nat.odd_iff.mp ((Fact.out : q.Prime).odd_of_ne_two (by omega))
  omega

end Prime

end NTKB.Davenport
