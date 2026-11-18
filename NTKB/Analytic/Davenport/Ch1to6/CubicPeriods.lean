/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Davenport.Ch1to6.Periods
import NTKB.IrelandRosen.R4.CubicPeriod

/-!
# Kummer's cubic periods (Davenport, Chapter 3, pp. 21–25)

For a prime `q ≡ 1 (mod 3)`, a primitive root `g` modulo `q` and a cubic character `χ`, put
`τ = ∑_n χ(n) e(n/q)` (Mathlib's `gaussSum χ ZMod.stdAddChar`) and `z_j = 1 + 3η_j`, where `η_j` is
the period over the `n` with index `≡ j (mod 3)` (`NTKB.Davenport.gaussianPeriod g 3 j`, with
`ζ = e(1/q)`). Davenport proves:

* `|τ|² = q` (`norm_gaussSum_cubic_sq`), and `τ̄ = τ(χ̄)` since `χ(-1) = 1`
  (`conj_gaussSum_cubic`);
* `z_j = ω^{-j} τ + ω^j τ̄` with `ω = χ(g)` (`one_add_three_mul_gaussianPeriod`), so
  `z_0 = τ + τ̄ = 2√q cos θ`;
* `τ³ = q J`, `J = J(χ, χ) = A + Bω` (Ireland–Rosen's `gaussSum_cube`), `q = A² - AB + B²`,
  `3 ∣ B`, so `4q = a² + 27b²` with `a = 2A - B`, `b = B/3` (`four_mul_eq_sq_add`);
* every `z_j` is a root of `z³ - 3qz - qa = 0` (`one_add_three_mul_gaussianPeriod_cubic`);
* **the sign of `a` (row 3-19)**: `a ≡ 1 (mod 3)`, by counting the solutions of `v³ = u(u + 1)`
  in two ways: `N ≡ 2 (mod 3)` (`card_cube_eq_mul_succ_modEq`) and `N = q + a`
  (`card_cube_eq_mul_succ`), whence `a ≡ 2 - q ≡ 1` (`two_mul_sub_modEq_one`).

The cubic period `∑_x e(x³/q) = τ + τ̄` and the cubic equation for it are Ireland–Rosen's
Chapter 9, §12 (`NTKB.IrelandRosen.cubicPeriod_eq`, `cubicPeriod_cubic_eq`), and the congruence
`a ≡ 1 (mod 3)` is also proved there from `J ≡ -1 (mod 3)` (`cubic_four_mul_card_eq`); here the
sign follows Davenport's count.
-/

open Finset Complex
open scoped Real ComplexConjugate

namespace NTKB.Davenport

variable {q : ℕ} [Fact q.Prime]

section Helpers

/-- `ψ(x) = e(x/q)^{val x}`-form: the standard additive character is `ζ ^ x.val`. -/
theorem stdAddChar_eq_pow (x : ZMod q) :
    (ZMod.stdAddChar : AddChar (ZMod q) ℂ) x = cexp (2 * π * I / q) ^ x.val := by
  rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply, cexp_pow]

/-- A sum over `ℤ/q` against a multiplicative character is a sum over the units. -/
theorem sum_mulChar_eq_sum_units (χ : MulChar (ZMod q) ℂ) (F : ZMod q → ℂ) :
    ∑ x : ZMod q, χ x * F x = ∑ u : (ZMod q)ˣ, χ u * F u := by
  rw [sum_zmod_eq_add_sum_units (F := fun x ↦ χ x * F x), MulChar.map_zero, zero_mul, zero_add]

theorem cubic_gen_cube {χ : MulChar (ZMod q) ℂ} (hχ : orderOf χ = 3) (g : (ZMod q)ˣ) :
    χ g ^ 3 = 1 := by
  rw [← MulChar.pow_apply' χ (by norm_num), ← hχ, pow_orderOf_eq_one,
    MulChar.one_apply g.isUnit]

theorem cubic_unit_apply {g : (ZMod q)ˣ} (hg : ∀ x, x ∈ Subgroup.zpowers g)
    (χ : MulChar (ZMod q) ℂ) (n : (ZMod q)ˣ) : χ n = χ g ^ index g n := by
  conv_lhs => rw [← pow_index hg n]
  rw [Units.val_pow_eq_pow_val, map_pow]

theorem cubic_gen_ne_one {g : (ZMod q)ˣ} (hg : ∀ x, x ∈ Subgroup.zpowers g)
    {χ : MulChar (ZMod q) ℂ} (hχ : orderOf χ = 3) : χ g ≠ 1 := by
  intro h
  refine NTKB.IrelandRosen.cubic_ne_one hχ (MulChar.ext fun x ↦ ?_)
  have := cubic_unit_apply hg χ x
  rw [h, one_pow] at this
  rw [this, MulChar.one_apply x.isUnit]

end Helpers

section Count

/-- `N = ∑_u #{v : v³ = u(u+1)}`. -/
theorem card_cube_eq_sum :
    (univ.filter (fun x : ZMod q × ZMod q ↦ x.2 ^ 3 = x.1 * (x.1 + 1))).card =
      ∑ u : ZMod q, NTKB.IrelandRosen.numSolPow 3 (u * (u + 1)) := by
  classical
  rw [Finset.card_filter, Fintype.sum_prod_type]
  refine sum_congr rfl fun u _ ↦ ?_
  unfold NTKB.IrelandRosen.numSolPow
  rw [Finset.card_filter]
  refine sum_congr rfl fun y _ ↦ ?_
  by_cases h : y ^ 3 = u * (u + 1) <;> simp [h]

theorem numSolPow_three_mod (hq : q % 3 = 1) (c : ZMod q) :
    NTKB.IrelandRosen.numSolPow 3 c % 3 = if c = 0 then 1 else 0 := by
  have h3 : 3 ∣ Fintype.card (ZMod q) - 1 := by rw [ZMod.card]; omega
  by_cases hc : c = 0
  · subst hc
    rw [if_pos rfl]
    have : NTKB.IrelandRosen.numSolPow 3 (0 : ZMod q) = 1 := by
      unfold NTKB.IrelandRosen.numSolPow
      rw [Finset.card_eq_one]
      exact ⟨0, by ext x; simp⟩
    rw [this]
  · rw [if_neg hc]
    obtain ⟨χ, hχ⟩ := NTKB.IrelandRosen.exists_orderOf_eq h3
    have h1 := NTKB.IrelandRosen.cubic_ne_one hχ
    have key := NTKB.IrelandRosen.numSolPow_eq_sum_range h3 hχ c
    simp only [sum_range_succ, range_zero, sum_empty, zero_add, pow_zero, pow_one,
      NTKB.IrelandRosen.bookChar_one, NTKB.IrelandRosen.cubic_sq_eq_inv hχ,
      NTKB.IrelandRosen.bookChar_of_ne_one h1,
      NTKB.IrelandRosen.bookChar_of_ne_one (inv_ne_one.mpr h1)] at key
    have hw : χ c ^ 3 = 1 := cubic_gen_cube hχ (Units.mk0 c hc)
    have hinv : χ⁻¹ c = χ c ^ 2 := by
      rw [← NTKB.IrelandRosen.cubic_sq_eq_inv hχ, MulChar.pow_apply' χ (by norm_num)]
    rw [hinv] at key
    by_cases hw1 : χ c = 1
    · rw [hw1] at key
      have h' : ((NTKB.IrelandRosen.numSolPow 3 c : ℕ) : ℂ) = ((3 : ℕ) : ℂ) := by
        rw [key]; norm_num
      rw [Nat.cast_injective h']
    · have : (χ c - 1) * (1 + χ c + χ c ^ 2) = 0 := by linear_combination hw
      have h0 := (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hw1)
      have h' : ((NTKB.IrelandRosen.numSolPow 3 c : ℕ) : ℂ) = ((0 : ℕ) : ℂ) := by
        rw [key, Nat.cast_zero]; exact h0
      rw [Nat.cast_injective h']

end Count

/-- **Davenport, Ch. 3, p. 22**: `τ̄ = τ(χ̄)` (since `χ(-1) = 1`). -/
@[kb "davenport1980" "Ch 3, p. 22"]
theorem conj_gaussSum_cubic {χ : MulChar (ZMod q) ℂ} (hχ : orderOf χ = 3) :
    conj (gaussSum χ (ZMod.stdAddChar : AddChar (ZMod q) ℂ)) =
      gaussSum χ⁻¹ (ZMod.stdAddChar : AddChar (ZMod q) ℂ) := by
  rw [gaussSum_inv_eq_conj, NTKB.IrelandRosen.cubic_apply_neg_one hχ, one_mul]

/-- **Davenport, Ch. 3, p. 22**: `|τ|² = q` for a cubic character. -/
@[kb "davenport1980" "Ch 3, p. 22"]
theorem norm_gaussSum_cubic_sq {χ : MulChar (ZMod q) ℂ} (hχ : orderOf χ = 3) :
    ‖gaussSum χ (ZMod.stdAddChar : AddChar (ZMod q) ℂ)‖ ^ 2 = q := by
  have h1 := NTKB.IrelandRosen.cubic_ne_one hχ
  have hinv := NTKB.IrelandRosen.gaussSum_mul_gaussSum_inv h1
    (ZMod.isPrimitive_stdAddChar q)
  rw [NTKB.IrelandRosen.cubic_apply_neg_one hχ, one_mul, ZMod.card, ← conj_gaussSum_cubic hχ,
    Complex.mul_conj, Complex.normSq_eq_norm_sq] at hinv
  exact_mod_cast hinv

/-- **Davenport, Ch. 3, p. 23**: for a primitive root `g` and `ω = χ(g)`,
`z_j = 1 + 3 η_j = ω^{-j} τ + ω^j τ̄` (`ω^{-j} = ω^{2j}`). -/
@[kb "davenport1980" "Ch 3, p. 23"]
theorem one_add_three_mul_gaussianPeriod (hq : q % 3 = 1) {g : (ZMod q)ˣ}
    (hg : ∀ x, x ∈ Subgroup.zpowers g) {χ : MulChar (ZMod q) ℂ} (hχ : orderOf χ = 3) (j : ℕ) :
    1 + 3 * gaussianPeriod g 3 j (cexp (2 * π * I / q)) =
      χ g ^ (2 * j) * gaussSum χ (ZMod.stdAddChar : AddChar (ZMod q) ℂ) +
        χ g ^ j * conj (gaussSum χ (ZMod.stdAddChar : AddChar (ZMod q) ℂ)) := by
  set ω := χ g with hω
  have h3 : ω ^ 3 = 1 := cubic_gen_cube hχ g
  have hne : ω ≠ 1 := cubic_gen_ne_one hg hχ
  have hsum3 : 1 + ω + ω ^ 2 = 0 := by
    have : (ω - 1) * (1 + ω + ω ^ 2) = 0 := by linear_combination h3
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hne)
  have hpow : ∀ m, ω ^ m = ω ^ (m % 3) := fun m ↦ by
    conv_lhs => rw [← Nat.mod_add_div m 3, pow_add, pow_mul, h3, one_pow, mul_one]
  set ζ : ℂ := cexp (2 * π * I / q) with hζ
  have hτ : gaussSum χ (ZMod.stdAddChar : AddChar (ZMod q) ℂ) =
      ∑ u : (ZMod q)ˣ, ω ^ index g u * ζ ^ (u : ZMod q).val := by
    unfold gaussSum
    rw [sum_mulChar_eq_sum_units]
    exact sum_congr rfl fun u _ ↦ by rw [cubic_unit_apply hg χ u, stdAddChar_eq_pow]
  have hτ' : gaussSum χ⁻¹ (ZMod.stdAddChar : AddChar (ZMod q) ℂ) =
      ∑ u : (ZMod q)ˣ, ω ^ (2 * index g u) * ζ ^ (u : ZMod q).val := by
    unfold gaussSum
    rw [sum_mulChar_eq_sum_units]
    refine sum_congr rfl fun u _ ↦ ?_
    rw [← NTKB.IrelandRosen.cubic_sq_eq_inv hχ, MulChar.pow_apply' χ (by norm_num),
      cubic_unit_apply hg χ u, stdAddChar_eq_pow, ← pow_mul, mul_comm (index g u)]
  have e1 : 1 + 3 * gaussianPeriod g 3 j ζ =
      ∑ u : (ZMod q)ˣ, ((if index g u ≡ j [MOD 3] then (3 : ℂ) else 0) - 1) *
        ζ ^ (u : ZMod q).val := by
    have hs : ∑ u : (ZMod q)ˣ, ζ ^ (u : ZMod q).val = -1 :=
      sum_units_pow_val (isPrimitiveRoot_cexp (q := q))
    simp only [sub_mul, sum_sub_distrib, one_mul]
    rw [hs, gaussianPeriod, mul_sum, sum_filter]
    simp only [ite_mul, zero_mul]
    ring
  rw [e1, conj_gaussSum_cubic hχ, hτ, hτ', mul_sum, mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun u _ ↦ ?_
  generalize index g u = i
  have hs : ω ^ (2 * j) * ω ^ i + ω ^ j * ω ^ (2 * i) =
      (if i ≡ j [MOD 3] then (3 : ℂ) else 0) - 1 := by
    rw [← pow_add, ← pow_add, hpow (2 * j + i), hpow (j + 2 * i)]
    have : ((2 * j + i) % 3 = 0 ∧ (j + 2 * i) % 3 = 0 ∧ i % 3 = j % 3) ∨
        ((2 * j + i) % 3 = 1 ∧ (j + 2 * i) % 3 = 2 ∧ i % 3 ≠ j % 3) ∨
        ((2 * j + i) % 3 = 2 ∧ (j + 2 * i) % 3 = 1 ∧ i % 3 ≠ j % 3) := by
      rcases (by omega : i % 3 = 0 ∨ i % 3 = 1 ∨ i % 3 = 2) with hi | hi | hi <;>
        rcases (by omega : j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2) with hj | hj | hj <;> omega
    rcases this with ⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩
    · rw [a, b, if_pos (show i ≡ j [MOD 3] from c)]; norm_num
    · rw [a, b, if_neg (show ¬ i ≡ j [MOD 3] from c)]; linear_combination hsum3
    · rw [a, b, if_neg (show ¬ i ≡ j [MOD 3] from c)]; linear_combination hsum3
  rw [← hs]
  ring

/-- **Davenport, Ch. 3, p. 24**: if `J(χ, χ) = A + Bω`, then `4q = a² + 27b²` with `a = 2A - B`,
`B = 3b`. -/
@[kb "davenport1980" "Ch 3, p. 24"]
theorem four_mul_eq_sq_add (hq : q % 3 = 1) {χ : MulChar (ZMod q) ℂ} (hχ : orderOf χ = 3)
    {A B : ℤ} (hJ : NTKB.IrelandRosen.multiJacobiSum ![χ, χ] = A + B * NTKB.IrelandRosen.omega3) :
    ∃ b : ℤ, B = 3 * b ∧ 4 * (q : ℤ) = (2 * A - B) ^ 2 + 27 * b ^ 2 := by
  have h3 : 3 ∣ Fintype.card (ZMod q) - 1 := by rw [ZMod.card]; omega
  obtain ⟨a, b, hJ', hq', ⟨k, rfl⟩, -⟩ := NTKB.IrelandRosen.cubic_jacobiSum_eq h3 hχ
  rw [hJ] at hJ'
  obtain ⟨rfl, hb⟩ := NTKB.IrelandRosen.add_mul_omega3_inj hJ'
  rw [ZMod.card] at hq'
  refine ⟨k, hb, ?_⟩
  rw [hb]
  linear_combination 4 * hq'

/-- **Davenport, Ch. 3, p. 25**: every `z_j = 1 + 3η_j` is a root of `z³ - 3qz - qa`,
`a = 2A - B`. -/
@[kb "davenport1980" "Ch 3, p. 25"]
theorem one_add_three_mul_gaussianPeriod_cubic (hq : q % 3 = 1) {g : (ZMod q)ˣ}
    (hg : ∀ x, x ∈ Subgroup.zpowers g) {χ : MulChar (ZMod q) ℂ} (hχ : orderOf χ = 3) {A B : ℤ}
    (hJ : NTKB.IrelandRosen.multiJacobiSum ![χ, χ] = A + B * NTKB.IrelandRosen.omega3) (j : ℕ) :
    (1 + 3 * gaussianPeriod g 3 j (cexp (2 * π * I / q))) ^ 3 -
        3 * q * (1 + 3 * gaussianPeriod g 3 j (cexp (2 * π * I / q))) - q * (2 * A - B) = 0 := by
  have h3 := cubic_gen_cube hχ g
  rw [one_add_three_mul_gaussianPeriod hq hg hχ j]
  have hψ := ZMod.isPrimitive_stdAddChar q
  have g1 := NTKB.IrelandRosen.gaussSum_cube hχ hψ
  rw [ZMod.card, hJ] at g1
  set τ := gaussSum χ (ZMod.stdAddChar : AddChar (ZMod q) ℂ)
  have g2 : conj τ ^ 3 = q * conj (A + B * NTKB.IrelandRosen.omega3 : ℂ) := by
    rw [← map_pow, g1, map_mul, map_natCast]
  have g3 : τ * conj τ = q := by
    rw [Complex.mul_conj, ← Complex.sq_norm, norm_gaussSum_cubic_sq hχ]
    simp
  have hsum : (A + B * NTKB.IrelandRosen.omega3 : ℂ) + conj (A + B * NTKB.IrelandRosen.omega3 : ℂ)
      = 2 * A - B := by
    rw [Complex.add_conj]
    have := NTKB.IrelandRosen.re_add_mul_omega3 A B
    exact_mod_cast this
  set ω := χ g
  have h6 : ω ^ (6 * j) = 1 := by rw [pow_mul, show ω ^ 6 = 1 by linear_combination (ω ^ 3 + 1) * h3, one_pow]
  have h3j : ω ^ (3 * j) = 1 := by rw [pow_mul, h3, one_pow]
  have e1 : (ω ^ (2 * j) * τ) ^ 3 = τ ^ 3 := by
    rw [mul_pow, ← pow_mul, show 2 * j * 3 = 6 * j by ring, h6, one_mul]
  have e2 : (ω ^ j * conj τ) ^ 3 = conj τ ^ 3 := by
    rw [mul_pow, ← pow_mul, show j * 3 = 3 * j by ring, h3j, one_mul]
  have e3 : (ω ^ (2 * j) * τ) * (ω ^ j * conj τ) = q := by
    rw [show ω ^ (2 * j) * τ * (ω ^ j * conj τ) = ω ^ (3 * j) * (τ * conj τ) by
      rw [show 3 * j = 2 * j + j by ring, pow_add]; ring, h3j, g3, one_mul]
  rw [← hsum]
  linear_combination e1 + e2 + 3 * (ω ^ (2 * j) * τ + ω ^ j * conj τ) * e3 + g1 + g2

/-- **Davenport, Ch. 3, p. 25**: the number `N` of solutions of `v³ = u(u + 1)` in `ℤ/q` is
`≡ 2 (mod 3)` (one `v` for `u = 0, -1`; three or none for the other `u`). -/
@[kb "davenport1980" "Ch 3, p. 25"]
theorem card_cube_eq_mul_succ_modEq (hq : q % 3 = 1) :
    ((univ.filter (fun x : ZMod q × ZMod q ↦ x.2 ^ 3 = x.1 * (x.1 + 1))).card : ℤ) ≡ 2 [ZMOD 3] := by
  have h := card_cube_eq_sum (q := q)
  have hm : (∑ u : ZMod q, NTKB.IrelandRosen.numSolPow 3 (u * (u + 1))) % 3 = 2 := by
    rw [Finset.sum_nat_mod]
    simp_rw [numSolPow_three_mod hq]
    rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one]
    have : (univ.filter fun u : ZMod q ↦ u * (u + 1) = 0) = {0, -1} := by
      ext u
      simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton, mul_eq_zero]
      rw [add_eq_zero_iff_eq_neg]
    rw [this, Finset.card_pair (by simp)]
  rw [h]
  exact_mod_cast (show _ ≡ 2 [MOD 3] from hm)

/-- **Davenport, Ch. 3, p. 25**: `N = q + a`, `a = 2A - B`. -/
@[kb "davenport1980" "Ch 3, p. 25"]
theorem card_cube_eq_mul_succ (hq : q % 3 = 1) {χ : MulChar (ZMod q) ℂ} (hχ : orderOf χ = 3)
    {A B : ℤ} (hJ : NTKB.IrelandRosen.multiJacobiSum ![χ, χ] = A + B * NTKB.IrelandRosen.omega3) :
    ((univ.filter (fun x : ZMod q × ZMod q ↦ x.2 ^ 3 = x.1 * (x.1 + 1))).card : ℤ) =
      q + (2 * A - B) := by
  have h3 : 3 ∣ Fintype.card (ZMod q) - 1 := by rw [ZMod.card]; omega
  have h1 := NTKB.IrelandRosen.cubic_ne_one hχ
  have hχ' : orderOf χ⁻¹ = 3 := by rw [orderOf_inv]; exact hχ
  have key : ∀ u : ZMod q, (NTKB.IrelandRosen.numSolPow 3 (u * (u + 1)) : ℂ) =
      1 + χ (u * (u + 1)) + χ⁻¹ (u * (u + 1)) := by
    intro u
    rw [NTKB.IrelandRosen.numSolPow_eq_sum_range h3 hχ]
    simp only [sum_range_succ, range_zero, sum_empty, zero_add, pow_zero, pow_one,
      NTKB.IrelandRosen.bookChar_one, NTKB.IrelandRosen.cubic_sq_eq_inv hχ,
      NTKB.IrelandRosen.bookChar_of_ne_one h1,
      NTKB.IrelandRosen.bookChar_of_ne_one (inv_ne_one.mpr h1)]
  have hJs : ∀ ψ : MulChar (ZMod q) ℂ, ψ ≠ 1 → ψ (-1) = 1 →
      ∑ u : ZMod q, ψ (u * (u + 1)) = NTKB.IrelandRosen.multiJacobiSum ![ψ, ψ] := by
    intro ψ hψ1 hψ
    rw [NTKB.IrelandRosen.multiJacobiSum_pair, ← Equiv.sum_comp (Equiv.neg (ZMod q))]
    refine sum_congr rfl fun a _ ↦ ?_
    simp only [Equiv.neg_apply, NTKB.IrelandRosen.bookChar_of_ne_one hψ1]
    rw [show -a * (-a + 1) = (-1) * (a * (1 - a)) by ring, map_mul, map_mul, hψ, one_mul]
  have hsum : NTKB.IrelandRosen.multiJacobiSum ![χ, χ] +
      conj (NTKB.IrelandRosen.multiJacobiSum ![χ, χ]) = 2 * A - B := by
    rw [Complex.add_conj, hJ]
    have := NTKB.IrelandRosen.re_add_mul_omega3 A B
    exact_mod_cast this
  have hC : ((univ.filter (fun x : ZMod q × ZMod q ↦ x.2 ^ 3 = x.1 * (x.1 + 1))).card : ℂ) =
      q + (2 * A - B) := by
    rw [card_cube_eq_sum, Nat.cast_sum]
    simp_rw [key]
    rw [sum_add_distrib, sum_add_distrib, hJs χ h1 (NTKB.IrelandRosen.cubic_apply_neg_one hχ),
      hJs χ⁻¹ (inv_ne_one.mpr h1) (NTKB.IrelandRosen.cubic_apply_neg_one hχ'),
      NTKB.IrelandRosen.multiJacobiSum_pair_inv_inv, ← hsum]
    simp [add_assoc]
  exact_mod_cast hC

/-- **The sign of `a` (Davenport, Ch. 3, p. 25)**: `a = 2A - B ≡ 1 (mod 3)`. -/
@[kb "davenport1980" "Ch 3, p. 25"]
theorem two_mul_sub_modEq_one (hq : q % 3 = 1) {χ : MulChar (ZMod q) ℂ} (hχ : orderOf χ = 3)
    {A B : ℤ} (hJ : NTKB.IrelandRosen.multiJacobiSum ![χ, χ] = A + B * NTKB.IrelandRosen.omega3) :
    2 * A - B ≡ 1 [ZMOD 3] := by
  have h := card_cube_eq_mul_succ_modEq hq
  rw [card_cube_eq_mul_succ hq hχ hJ] at h
  unfold Int.ModEq at h ⊢
  omega

end NTKB.Davenport
