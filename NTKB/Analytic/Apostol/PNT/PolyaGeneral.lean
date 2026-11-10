/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Apostol.GaussSums.Polya
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

/-!
# Pólya's inequality for all nonprincipal characters (Apostol, Theorem 13.15)

**Theorem 13.15**: for every nonprincipal character `χ` mod `k` and every `x`,
`|∑_{m ≤ x} χ(m)| = O(√k log k)`; here with the explicit constant `2`.

Apostol's proof: `χ = ψ χ₁` with `ψ` primitive mod the conductor `c` (`1 < c ∣ k`), so
`∑_{m ≤ x} χ(m) = ∑_{d ∣ k} μ(d) ψ(d) ∑_{q ≤ x/d} ψ(q)` (Möbius inversion of the condition
`(m, k) = 1`); the inner sums are `< √c log c` by Pólya's inequality for primitive characters
(Theorem 8.21, `polya`), and the `d` with `ψ(d) ≠ 0` divide `k/c`, so there are at most
`d(k/c) ≤ 2√(k/c)` of them.
-/

open Finset Real ArithmeticFunction
open scoped ArithmeticFunction.Moebius

namespace NTKB.Apostol

/-- `d(n) ≤ 2 √n`. -/
lemma card_divisors_le_two_sqrt (n : ℕ) : (n.divisors.card : ℝ) ≤ 2 * √(n : ℝ) := by
  classical
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  set A := n.divisors.filter fun d => d ≤ Nat.sqrt n
  set B := n.divisors.filter fun d => ¬ d ≤ Nat.sqrt n
  have hA : A.card ≤ Nat.sqrt n := by
    refine (card_le_card fun d hd => ?_).trans (Nat.card_Icc 1 (Nat.sqrt n)).le
    obtain ⟨hd1, hd2⟩ := mem_filter.mp hd
    exact mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hd1, hd2⟩
  have hB : B.card ≤ A.card := by
    refine card_le_card_of_injOn (fun d => n / d) (fun d hd => ?_) (fun d₁ hd₁ d₂ hd₂ h => ?_)
    · obtain ⟨hd1, hd2⟩ := mem_filter.mp hd
      have hdn := Nat.dvd_of_mem_divisors hd1
      have hd0 := Nat.pos_of_mem_divisors hd1
      refine mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd hdn, hn⟩, ?_⟩
      rw [Nat.le_sqrt]
      rw [Nat.le_sqrt, not_le] at hd2
      obtain ⟨e, he⟩ := hdn
      have : n / d = e := by rw [he, Nat.mul_div_cancel_left _ hd0]
      show n / d * (n / d) ≤ n
      rw [this]
      have : e < d := by
        by_contra h; push Not at h
        have : d * d ≤ d * e := Nat.mul_le_mul_left d h
        omega
      calc e * e ≤ d * e := Nat.mul_le_mul_right e this.le
        _ = n := he.symm
    · have h1 := Nat.dvd_of_mem_divisors (mem_filter.mp hd₁).1
      have h2 := Nat.dvd_of_mem_divisors (mem_filter.mp hd₂).1
      simp only at h
      rw [← Nat.div_div_self h1 hn, h, Nat.div_div_self h2 hn]
  have hsplit : A.card + B.card = n.divisors.card := card_filter_add_card_filter_not _
  have hcard : n.divisors.card ≤ 2 * Nat.sqrt n := by omega
  have hsq : (Nat.sqrt n : ℝ) ≤ √(n : ℝ) := by
    rw [Real.le_sqrt (by positivity) (by positivity)]
    exact_mod_cast Nat.sqrt_le' n
  calc (n.divisors.card : ℝ) ≤ ((2 * Nat.sqrt n : ℕ) : ℝ) := by exact_mod_cast hcard
    _ = 2 * (Nat.sqrt n : ℝ) := by push_cast; ring
    _ ≤ 2 * √(n : ℝ) := by gcongr

lemma sum_divisors_moebius_complex (g : ℕ) :
    ∑ d ∈ g.divisors, ((μ d : ℤ) : ℂ) = if g = 1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℤ => f g) moebius_mul_coe_zeta
  simp only [coe_mul_zeta_apply, ArithmeticFunction.one_apply] at h
  have := congrArg (Int.cast : ℤ → ℂ) h
  push_cast at this
  rw [this]

/-- The Möbius decomposition: for `χ` induced by `ψ` mod `c`,
`∑_{m ≤ N} χ(m) = ∑_{d ∣ k} μ(d) ψ(d) ∑_{q ≤ N/d} ψ(q)`. -/
lemma sum_changeLevel_eq {k c : ℕ} [NeZero k] (hck : c ∣ k) (ψ : DirichletCharacter ℂ c)
    (N : ℕ) :
    ∑ m ∈ Icc 1 N, DirichletCharacter.changeLevel hck ψ (m : ZMod k) =
      ∑ d ∈ k.divisors, ((μ d : ℤ) : ℂ) * ψ (d : ZMod c) *
        ∑ q ∈ Icc 1 (N / d), ψ (q : ZMod c) := by
  classical
  have hk : k ≠ 0 := NeZero.ne k
  -- Step A: `χ(m) = ∑_{d ∣ (m, k)} μ(d) ψ(m)`
  have hA : ∀ m ∈ Icc 1 N, DirichletCharacter.changeLevel hck ψ (m : ZMod k) =
      ∑ d ∈ k.divisors, if d ∣ m then ((μ d : ℤ) : ℂ) * ψ (m : ZMod c) else 0 := by
    intro m hm
    have hm0 : m ≠ 0 := by have := (mem_Icc.mp hm).1; omega
    rw [← sum_filter, ← sum_mul]
    have hfilt : k.divisors.filter (· ∣ m) = (Nat.gcd m k).divisors := by
      ext d
      simp only [mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff]
      constructor
      · rintro ⟨⟨h1, -⟩, h2⟩; exact ⟨⟨h2, h1⟩, Nat.gcd_ne_zero_left hm0⟩
      · rintro ⟨⟨h1, h2⟩, -⟩; exact ⟨⟨h2, hk⟩, h1⟩
    rw [hfilt, sum_divisors_moebius_complex _]
    split_ifs with hg
    · rw [one_mul]
      have hcop : IsCoprime (m : ℤ) (k : ℤ) := Nat.isCoprime_iff_coprime.mpr hg
      have := DirichletCharacter.changeLevel_eq_cast_of_dvd' ψ hck hcop
      simpa using this
    · rw [zero_mul]
      apply MulChar.map_nonunit
      rwa [ZMod.isUnit_iff_coprime]
  rw [sum_congr rfl hA, sum_comm]
  refine sum_congr rfl fun d hd => ?_
  have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
  rw [← sum_filter, ← mul_sum, mul_assoc]
  congr 1
  -- Step C: substitute `m = d q`
  have himage : (Icc 1 (N / d)).image (d * ·) = (Icc 1 N).filter (d ∣ ·) := by
    ext m
    simp only [mem_image, mem_Icc, mem_filter]
    constructor
    · rintro ⟨q, ⟨hq1, hq2⟩, rfl⟩
      refine ⟨⟨by nlinarith, ?_⟩, dvd_mul_right d q⟩
      calc d * q ≤ d * (N / d) := Nat.mul_le_mul_left d hq2
        _ ≤ N := Nat.mul_div_le N d
    · rintro ⟨⟨hm1, hm2⟩, q, rfl⟩
      refine ⟨q, ⟨?_, ?_⟩, rfl⟩
      · rcases Nat.eq_zero_or_pos q with rfl | h
        · simp at hm1
        · exact h
      · rw [Nat.le_div_iff_mul_le hd0, mul_comm]; exact hm2
  rw [← himage, sum_image (fun a _ b _ h => Nat.eq_of_mul_eq_mul_left hd0 h), mul_sum]
  refine sum_congr rfl fun q _ => ?_
  rw [Nat.cast_mul, map_mul]

/-- **Theorem 13.15**: for every nonprincipal character `χ` mod `k` and every real `x`,
`|∑_{m ≤ x} χ(m)| ≤ 2 √k log k`. -/
@[kb "apostol1976" "Thm 13.15, p. 299"]
theorem apostol_thm_13_15 {k : ℕ} [NeZero k] {χ : DirichletCharacter ℂ k} (hχ : χ ≠ 1) (x : ℝ) :
    ‖∑ m ∈ Icc 1 ⌊x⌋₊, χ (m : ZMod k)‖ ≤ 2 * √(k : ℝ) * Real.log k := by
  classical
  set c := χ.conductor
  have hcdvd : c ∣ k := χ.conductor_dvd_level
  have hk0 : k ≠ 0 := NeZero.ne k
  have hc0 : c ≠ 0 := fun h0 => hk0 (Nat.eq_zero_of_zero_dvd (h0 ▸ hcdvd))
  have hc1 : c ≠ 1 := fun h1 => hχ ((DirichletCharacter.eq_one_iff_conductor_eq_one (χ := χ)).mpr h1)
  have hc : 1 < c := by omega
  have : NeZero c := ⟨hc0⟩
  set ψ := χ.primitiveCharacter
  have hψ : ψ.IsPrimitive := χ.primitiveCharacter_isPrimitive
  set N := ⌊x⌋₊
  have hχeq : DirichletCharacter.changeLevel hcdvd ψ = χ := χ.changeLevel_primitiveCharacter
  rw [← hχeq, sum_changeLevel_eq hcdvd ψ N]
  set B := √(c : ℝ) * Real.log c
  have hB0 : 0 ≤ B := mul_nonneg (Real.sqrt_nonneg _) (Real.log_nonneg (by exact_mod_cast hc.le))
  -- each term is at most `B` if `(d, c) = 1`, and `0` otherwise
  have hterm : ∀ d ∈ k.divisors, ‖((μ d : ℤ) : ℂ) * ψ (d : ZMod c) *
      ∑ q ∈ Icc 1 (N / d), ψ (q : ZMod c)‖ ≤ if IsUnit (d : ZMod c) then B else 0 := by
    intro d _
    split_ifs with hu
    · rw [norm_mul, norm_mul]
      have h1 : ‖((μ d : ℤ) : ℂ)‖ ≤ 1 := by
        rw [Complex.norm_intCast]
        exact_mod_cast abs_moebius_le_one
      have h2 : ‖ψ (d : ZMod c)‖ ≤ 1 := DirichletCharacter.norm_le_one ψ _
      have h3 : ‖∑ q ∈ Icc 1 (N / d), ψ (q : ZMod c)‖ ≤ B := by
        have := polya hψ hc ((N / d : ℕ) : ℝ)
        rw [Nat.floor_natCast] at this
        exact this.le
      calc ‖((μ d : ℤ) : ℂ)‖ * ‖ψ (d : ZMod c)‖ * ‖∑ q ∈ Icc 1 (N / d), ψ (q : ZMod c)‖
          ≤ 1 * 1 * B := by gcongr
        _ = B := by ring
    · rw [MulChar.map_nonunit _ hu, mul_zero, zero_mul, norm_zero]
  have hcount : ((k.divisors.filter fun d : ℕ => IsUnit (d : ZMod c)).card : ℝ) ≤
      2 * √((k / c : ℕ) : ℝ) := by
    refine le_trans ?_ (card_divisors_le_two_sqrt (k / c))
    have hkc : k / c ≠ 0 := (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hk0) hcdvd)
      (Nat.pos_of_ne_zero hc0)).ne'
    refine Nat.cast_le.mpr (card_le_card fun d hd => ?_)
    obtain ⟨hd1, hd2⟩ := mem_filter.mp hd
    rw [ZMod.isUnit_iff_coprime] at hd2
    have hdk := Nat.dvd_of_mem_divisors hd1
    rw [← Nat.mul_div_cancel' hcdvd] at hdk
    exact Nat.mem_divisors.mpr ⟨hd2.dvd_of_dvd_mul_left hdk, hkc⟩
  calc ‖∑ d ∈ k.divisors, ((μ d : ℤ) : ℂ) * ψ (d : ZMod c) * ∑ q ∈ Icc 1 (N / d), ψ (q : ZMod c)‖
      ≤ ∑ d ∈ k.divisors, ‖((μ d : ℤ) : ℂ) * ψ (d : ZMod c) *
          ∑ q ∈ Icc 1 (N / d), ψ (q : ZMod c)‖ := norm_sum_le _ _
    _ ≤ ∑ d ∈ k.divisors, (if IsUnit (d : ZMod c) then B else 0) := sum_le_sum hterm
    _ = ((k.divisors.filter fun d : ℕ => IsUnit (d : ZMod c)).card : ℝ) * B := by
        rw [← sum_filter, sum_const, nsmul_eq_mul]
    _ ≤ 2 * √((k / c : ℕ) : ℝ) * B := by gcongr
    _ = 2 * √(k : ℝ) * Real.log c := by
        have hkc : ((k / c : ℕ) : ℝ) * c = k := by
          exact_mod_cast Nat.div_mul_cancel hcdvd
        rw [show 2 * √((k / c : ℕ) : ℝ) * B = 2 * (√((k / c : ℕ) : ℝ) * √(c : ℝ)) * Real.log c by
          ring, ← Real.sqrt_mul (Nat.cast_nonneg _), hkc]
    _ ≤ 2 * √(k : ℝ) * Real.log k := by
        gcongr
        exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hk0) hcdvd

end NTKB.Apostol
