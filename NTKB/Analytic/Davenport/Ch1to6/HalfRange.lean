/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Davenport.Ch1to6.LOneOdd

/-!
# Davenport, Chapter 1: Dirichlet's second finite expression (8)

For a prime `q ≡ 3 (mod 4)`,
$$L(1) = \frac{\pi}{(2 - (2/q))\sqrt q}\sum_{0 < m < q/2}\Big(\frac mq\Big)$$
(§1, p. 9, (8)); in particular, since `L(1) > 0`, there are more quadratic residues than
nonresidues in `(0, q/2)`.

Davenport derives (8) from the Euler product with the factor at `2` removed. Here it is derived
from formula (7) and the elementary identity `((2/q) - 2) ∑_{m<q} m (m/q) = q ∑_{m<q/2} (m/q)`,
which follows by grouping the terms `m`, `q - m` and the even and odd `m`.
-/

noncomputable section

open Complex Finset DirichletCharacter
open scoped Real

namespace NTKB.Davenport

/-- Reflection split: `∑_{m < 2h+1} g(m) = ∑_{k ≤ h} g(k) + ∑_{k < h} g(2h - k)`. -/
theorem sum_range_two_mul_add_one_reflect {M : Type*} [AddCommMonoid M] (g : ℕ → M) (h : ℕ) :
    ∑ m ∈ range (2 * h + 1), g m = ∑ k ∈ range (h + 1), g k + ∑ k ∈ range h, g (2 * h - k) := by
  rw [show 2 * h + 1 = (h + 1) + h by ring, sum_range_add]
  congr 1
  rw [← sum_range_reflect]
  refine sum_congr rfl fun k hk ↦ ?_
  have := mem_range.mp hk
  congr 1
  omega

/-- Parity split: `∑_{m < 2h+1} g(m) = ∑_{k ≤ h} g(2k) + ∑_{k < h} g(2k+1)`. -/
theorem sum_range_two_mul_add_one_parity {M : Type*} [AddCommMonoid M] (g : ℕ → M) (h : ℕ) :
    ∑ m ∈ range (2 * h + 1), g m =
      ∑ k ∈ range (h + 1), g (2 * k) + ∑ k ∈ range h, g (2 * k + 1) := by
  induction h with
  | zero => simp
  | succ h ih =>
    have e1 : 2 * (h + 1) + 1 = 2 * h + 1 + 1 + 1 := by ring
    rw [e1, sum_range_succ, sum_range_succ, ih, sum_range_succ (fun k ↦ g (2 * k)) (h + 1),
      sum_range_succ (fun k ↦ g (2 * k + 1)) h]
    have e2 : 2 * h + 1 + 1 = 2 * (h + 1) := by ring
    rw [e2]
    abel

variable {q : ℕ} [Fact q.Prime]

theorem legendreSym_natCast_sub {m : ℕ} (hm : m ≤ q) (hq : q % 4 = 3) :
    legendreSym q ((q - m : ℕ) : ℤ) = -legendreSym q m := by
  have hq2 : ringChar (ZMod q) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; omega
  have hcast : (((q - m : ℕ) : ℤ) : ZMod q) = -((m : ℤ) : ZMod q) := by
    push_cast [Nat.cast_sub hm]
    rw [ZMod.natCast_self, zero_sub]
  rw [legendreSym, legendreSym, hcast, neg_eq_neg_one_mul, map_mul,
    quadraticChar_neg_one hq2, ZMod.card, ZMod.χ₄_nat_three_mod_four hq]
  ring

/-- **The finite identity behind Davenport §1, (8).** For a prime `q ≡ 3 (mod 4)`:
`((2/q) - 2) ∑_{m=1}^{q-1} m (m/q) = q ∑_{m=1}^{(q-1)/2} (m/q)`. -/
theorem legendreSym_two_sub_two_mul_sum (hq : q % 4 = 3) :
    (legendreSym q 2 - 2) * ∑ m ∈ range q, (m : ℤ) * legendreSym q m =
      q * ∑ m ∈ range ((q - 1) / 2 + 1), legendreSym q m := by
  set h := (q - 1) / 2
  have hq' : q = 2 * h + 1 := by omega
  set c : ℕ → ℤ := fun m ↦ legendreSym q m
  have hc0 : c 0 = 0 := by simp [c, legendreSym.at_zero]
  have hrefl : ∀ j ≤ q, c (q - j) = -c j := fun j hj ↦ legendreSym_natCast_sub hj hq
  have hmul : ∀ k : ℕ, c (2 * k) = c 2 * c k := by
    intro k; simp only [c]; push_cast; exact legendreSym.mul q 2 k
  set S := ∑ m ∈ range q, (m : ℤ) * c m
  set A := ∑ m ∈ range (h + 1), c m
  set T := ∑ m ∈ range (h + 1), (m : ℤ) * c m
  -- shifted sums: `∑_{k<h} f(k+1) = ∑_{k ≤ h} f(k)` when `f 0 = 0`
  have hshift : ∀ f : ℕ → ℤ, f 0 = 0 → ∑ k ∈ range h, f (k + 1) = ∑ k ∈ range (h + 1), f k := by
    intro f hf; rw [sum_range_succ', hf, add_zero]
  -- reflection: `S = 2T - qA`
  have hR : S = 2 * T - q * A := by
    simp only [S]
    rw [hq', sum_range_two_mul_add_one_reflect, ← hq']
    have : ∑ k ∈ range h, ((2 * h - k : ℕ) : ℤ) * c (2 * h - k) =
        ∑ k ∈ range h, -(((q : ℤ) - ((k + 1 : ℕ) : ℤ)) * c (k + 1)) := by
      refine sum_congr rfl fun k hk ↦ ?_
      have hk := mem_range.mp hk
      have e : 2 * h - k = q - (k + 1) := by omega
      rw [e, hrefl (k + 1) (by omega), Nat.cast_sub (by omega)]
      ring
    rw [this, hshift (fun j ↦ -(((q : ℤ) - (j : ℤ)) * c j)) (by simp [hc0])]
    simp only [A, T, sub_mul, sum_neg_distrib, sum_sub_distrib, ← mul_sum]
    ring
  -- parity: `S = (2/q)(4T - qA)`
  have hP : S = c 2 * (4 * T - q * A) := by
    simp only [S]
    rw [hq', sum_range_two_mul_add_one_parity, ← hq']
    have h1 : ∑ k ∈ range (h + 1), ((2 * k : ℕ) : ℤ) * c (2 * k) =
        c 2 * (2 * T) := by
      simp only [T, mul_sum]
      refine sum_congr rfl fun k _ ↦ ?_
      rw [hmul]; push_cast; ring
    have h2 : ∑ k ∈ range h, ((2 * k + 1 : ℕ) : ℤ) * c (2 * k + 1) =
        c 2 * (2 * T - q * A) := by
      rw [← sum_range_reflect]
      have : ∀ k ∈ range h, ((2 * (h - 1 - k) + 1 : ℕ) : ℤ) * c (2 * (h - 1 - k) + 1) =
          -(c 2 * (((q : ℤ) - 2 * ((k + 1 : ℕ) : ℤ)) * c (k + 1))) := by
        intro k hk
        have hk := mem_range.mp hk
        have e : 2 * (h - 1 - k) + 1 = q - 2 * (k + 1) := by omega
        rw [e, hrefl _ (by omega), hmul, Nat.cast_sub (by omega)]
        push_cast; ring
      rw [sum_congr rfl this, hshift (fun j ↦ -(c 2 * (((q : ℤ) - 2 * (j : ℤ)) * c j)))
        (by simp [hc0])]
      simp only [A, T, sum_neg_distrib, ← mul_sum, sub_mul, sum_sub_distrib]
      rw [mul_sum, mul_sum]
      simp only [mul_assoc]
      ring
    rw [h1, h2]; ring
  -- combine, using `(2/q)² = 1`
  have hc2 : c 2 * c 2 = 1 := by
    have h2 : (((2 : ℕ) : ℤ) : ZMod q) ≠ 0 := by
      rw [Int.cast_natCast, Ne, ZMod.natCast_eq_zero_iff]
      intro h
      have := Nat.le_of_dvd two_pos h
      omega
    have := legendreSym.sq_one q h2
    simp only [c]
    rw [← sq]
    exact this
  show (c 2 - 2) * S = q * A
  have : S = c 2 * (2 * S + q * A) := by
    rw [show 2 * S + q * A = 4 * T - q * A by rw [hR]; ring]
    exact hP
  have : c 2 * S = 2 * S + q * A := by
    calc c 2 * S = c 2 * (c 2 * (2 * S + q * A)) := by rw [← this]
      _ = (c 2 * c 2) * (2 * S + q * A) := by ring
      _ = 2 * S + q * A := by rw [hc2, one_mul]
  linarith

/-- **Davenport §1, p. 9, (8).** For a prime `q ≡ 3 (mod 4)`:
`L(1) = π / ((2 - (2/q)) √q) · ∑_{0 < m < q/2} (m/q)`. -/
@[kb "davenport1980" "Ch 1, p. 9, (8)"]
theorem LFunction_one_legendreChar_half (hq : q % 4 = 3) :
    LFunction (legendreChar q) 1 =
      ((π / ((2 - legendreSym q 2) * √(q : ℝ)) : ℝ) : ℂ) *
        ∑ m ∈ Icc 1 ((q - 1) / 2), (legendreSym q m : ℂ) := by
  have hid := legendreSym_two_sub_two_mul_sum hq
  rw [LFunction_one_legendreChar hq]
  set c2 : ℤ := legendreSym q 2
  have hc2 : c2 ≠ 2 := by
    have h2 : ((2 : ℤ) : ZMod q) ≠ 0 := by
      have : ((2 : ℕ) : ZMod q) ≠ 0 := by
        rw [Ne, ZMod.natCast_eq_zero_iff]
        intro h
        have := Nat.le_of_dvd two_pos h
        omega
      exact_mod_cast this
    rcases legendreSym.eq_one_or_neg_one q h2 with h | h <;> simp only [c2, h] <;> norm_num
  -- the sums as complex numbers
  have hS : ∑ m ∈ Ico 1 q, (m : ℂ) * (legendreSym q m : ℂ) =
      ((∑ m ∈ range q, (m : ℤ) * legendreSym q m : ℤ) : ℂ) := by
    rw [range_eq_Ico, sum_eq_sum_Ico_succ_bot (Fact.out : q.Prime).pos]
    push_cast; simp
  have hA : ∑ m ∈ Icc 1 ((q - 1) / 2), (legendreSym q m : ℂ) =
      ((∑ m ∈ range ((q - 1) / 2 + 1), legendreSym q m : ℤ) : ℂ) := by
    rw [range_eq_Ico, sum_eq_sum_Ico_succ_bot (Nat.succ_pos _), ← Finset.Ico_add_one_right_eq_Icc]
    push_cast; simp [legendreSym.at_zero]
  rw [hS, hA]
  set S := ∑ m ∈ range q, (m : ℤ) * legendreSym q m
  set A := ∑ m ∈ range ((q - 1) / 2 + 1), legendreSym q m
  have hidC : ((c2 : ℂ) - 2) * S = q * A := by exact_mod_cast hid
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (Fact.out : q.Prime).pos
  have hsq : (0 : ℝ) < √(q : ℝ) := Real.sqrt_pos.mpr hq0
  have hpow : (q : ℝ) ^ ((3 : ℝ) / 2) = q * √(q : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_one_add' hq0.le (by norm_num)]
    norm_num
  have hc2C : ((c2 : ℂ) - 2) ≠ 0 := by
    intro h; apply hc2; exact_mod_cast sub_eq_zero.mp h
  have h2c : ((2 : ℂ) - c2) ≠ 0 := by
    intro h; apply hc2C; linear_combination -h
  rw [hpow]
  push_cast
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq0.ne'
  have hsC : ((√(q : ℝ) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hsq.ne'
  have hAS : (A : ℂ) = ((c2 : ℂ) - 2) * S / q := by rw [hidC]; field_simp
  rw [hAS]
  field_simp
  ring

end NTKB.Davenport
