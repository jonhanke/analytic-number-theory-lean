/-
Copyright (c) 2026 The Tau Ceti contributors (`gaussSum_mul_tsum_inv_pow_eq_generalizedBernoulli`,
`gaussSum_mul_gaussSum_inv_eq_card_of_isPrimitive`,
`gaussSum_mul_gaussSum_inv_eq_neg_one_mul_card_of_isPrimitive`); the NTKB authors (the rest).
Released under Apache 2.0 license.
-/
import Mathlib.NumberTheory.ZetaValues
import Mathlib.NumberTheory.DirichletCharacter.GaussSum
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import NTKB.Elementary.SpecialValues.GeneralizedBernoulli

/-!
# Values of primitive Dirichlet L-functions at positive integers, `k ≥ 2`

For a primitive Dirichlet character `χ` modulo `f` and `k ≥ 2` with `χ(-1) = (-1)^k`
(write `δ ∈ {0, 1}` for the parity, `χ(-1) = (-1)^δ`, so `k ≡ δ mod 2`),
$$L(k,\chi) = (-1)^{1+(k-\delta)/2}\,\frac{\tau(\chi)}{2 i^{\delta}}
  \left(\frac{2\pi}{f}\right)^{k}\frac{B_{k,\bar\chi}}{k!}$$
(Washington, Chapter 4, from the functional equation; the original request cites Theorem 4.2 and Corollary 4.4, locator not checked against the book), with `τ(χ) = ∑_{a mod f} χ(a) e^{2πi a/f}`, which is Mathlib's
`gaussSum χ ZMod.stdAddChar`, and `χ̄ = χ⁻¹`. The case `k = 1` (odd `χ`) is in
`NTKB.Elementary.SpecialValues.ValueAtOne`.

The factor `i^δ` is essential: the formula without it (as written in the original request) is false for every
odd primitive character, see `NTKB.Elementary.SpecialValues.Statements`.

## Provenance

`gaussSum_mul_tsum_inv_pow_eq_generalizedBernoulli` is copied (Apache 2.0, with credit) from Tau
Ceti, `TauCeti/NumberTheory/DirichletCharacter/LValues.lean`, main `d7b4780` (2026-11-07), and
`gaussSum_mul_gaussSum_inv_eq_card_of_isPrimitive`,
`gaussSum_mul_gaussSum_inv_eq_neg_one_mul_card_of_isPrimitive` from
`TauCeti/NumberTheory/DirichletCharacter/GaussSum.lean`; namespace moved to `NTKB`, with
`NTKB.generalizedBernoulli χ k` for Tau Ceti's `χ.generalizedBernoulli k`; proofs otherwise
unchanged. The passage from the integer-indexed sum to `L(k, χ)` is new.
-/

noncomputable section

open Complex AddChar
open scoped Real

namespace NTKB

/-! ### Gauss sums of primitive characters (Tau Ceti) -/

/-- The Gauss sums of a primitive Dirichlet character and its inverse, taken against inverse
additive characters, multiply to the level. (Tau Ceti.) -/
theorem gaussSum_mul_gaussSum_inv_eq_card_of_isPrimitive
    {R : Type*} [CommRing R] [IsDomain R] {n : ℕ} [NeZero n]
    {χ : DirichletCharacter R n} (hχ : χ.IsPrimitive)
    {e : AddChar (ZMod n) R} (he : e.IsPrimitive) :
    gaussSum χ e * gaussSum χ⁻¹ e⁻¹ = Fintype.card (ZMod n) := by
  classical
  simp only [gaussSum]
  rw [Finset.mul_sum]
  calc
    ∑ b, gaussSum χ e * (χ⁻¹ b * e⁻¹ b) =
        ∑ b, gaussSum χ (e.mulShift b) * e⁻¹ b := by
      apply Finset.sum_congr rfl
      intro b _
      rw [gaussSum_mulShift_of_isPrimitive e hχ b]
      ring
    _ = ∑ b, ∑ a, χ a * e (b * a) * e (-b) := by
      apply Finset.sum_congr rfl
      intro b _
      simp only [gaussSum, AddChar.mulShift_apply, AddChar.inv_apply, Finset.sum_mul]
    _ = ∑ a, χ a * ∑ b, e (b * (a - 1)) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      rw [mul_assoc, ← e.map_add_eq_mul]
      congr 2
      ring
    _ = Fintype.card (ZMod n) := by
      simp_rw [AddChar.sum_mulShift _ he]
      rw [Finset.sum_eq_single 1]
      · simp
      · intro b _ hb
        simp [sub_eq_zero, hb]
      · simp

/-- `τ(χ) τ(χ⁻¹) = χ(-1) N` for a primitive character and a primitive additive character.
(Tau Ceti.) -/
theorem gaussSum_mul_gaussSum_inv_eq_neg_one_mul_card_of_isPrimitive
    {R : Type*} [CommRing R] [IsDomain R] {n : ℕ} [NeZero n]
    {χ : DirichletCharacter R n} (hχ : χ.IsPrimitive)
    {e : AddChar (ZMod n) R} (he : e.IsPrimitive) :
    gaussSum χ e * gaussSum χ⁻¹ e = χ (-1) * Fintype.card (ZMod n) := by
  have hshift : gaussSum χ⁻¹ e⁻¹ = χ (-1) * gaussSum χ⁻¹ e := by
    rw [e.inv_mulShift, ← Units.coe_neg_one, gaussSum_mulShift_eq, inv_inv]
  have hprod := gaussSum_mul_gaussSum_inv_eq_card_of_isPrimitive hχ he
  rw [hshift] at hprod
  calc
    _ = χ (-1) * (gaussSum χ e * (χ (-1) * gaussSum χ⁻¹ e)) := by
      symm
      calc
        _ = (χ (-1) * χ (-1)) * (gaussSum χ e * gaussSum χ⁻¹ e) := by ring
        _ = _ := by rw [← map_mul, neg_one_mul, neg_neg, map_one, one_mul]
    _ = _ := by rw [hprod]

/-! ### The integer-indexed critical sum (Tau Ceti) -/

variable {N k : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)

/-- The integer-indexed critical-value sum of a primitive character, multiplied by its Gauss
sum: `τ(χ) ∑' n : ℤ, χ⁻¹(n) n⁻ᵏ = -(2πi)ᵏ B_{k,χ} / (k! Nᵏ⁻¹)` for `k ≥ 2`. (Tau Ceti.) -/
theorem gaussSum_mul_tsum_inv_pow_eq_generalizedBernoulli (hχ : χ.IsPrimitive)
    (hk : 2 ≤ k) :
    gaussSum χ ZMod.stdAddChar *
        (∑' n : ℤ, χ⁻¹ (n : ZMod N) * (n : ℂ) ^ (-(k : ℤ))) =
      -(2 * π * I) ^ k / ((k.factorial : ℂ) * (N : ℂ) ^ (k - 1)) *
        generalizedBernoulli χ k := by
  classical
  have hNk : (N : ℂ) ^ (k - 1) ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.mpr (NeZero.ne N))
  have hfourier (a : ZMod N) (n : ℤ) :
      fourier n ((a.val / (N : ℝ) : ℝ) : UnitAddCircle) =
        ZMod.stdAddChar ((n : ZMod N) * a) := by
    rw [fourier_coe_apply, ZMod.stdAddChar_apply]
    have h := ZMod.toCircle_intCast (N := N) (n * a.val)
    rw [Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val] at h
    rw [h]
    push_cast
    congr 1
    ring
  have hx (a : ZMod N) : (a.val / (N : ℝ) : ℝ) ∈ Set.Icc 0 1 :=
    ⟨div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _),
      (div_le_one (Nat.cast_pos.mpr (NeZero.pos N))).mpr
        (by exact_mod_cast (ZMod.val_lt a).le)⟩
  have hs (a : ZMod N) :=
    (hasSum_one_div_pow_mul_fourier_mul_bernoulliFun hk (hx a)).mul_left (χ a)
  have hsum := hasSum_sum (s := Finset.univ) fun a _ ↦ hs a
  have hterm (n : ℤ) :
      (∑ a : ZMod N, χ a *
        (1 / (n : ℂ) ^ k * fourier n ((a.val / (N : ℝ) : ℝ) : UnitAddCircle))) =
      gaussSum χ ZMod.stdAddChar * (χ⁻¹ (n : ZMod N) * (n : ℂ) ^ (-(k : ℤ))) := by
    simp_rw [hfourier]
    have hgauss := gaussSum_mulShift_of_isPrimitive ZMod.stdAddChar hχ (n : ZMod N)
    simp only [gaussSum, AddChar.mulShift_apply] at hgauss
    simp_rw [← mul_assoc, mul_right_comm (χ _) (1 / (n : ℂ) ^ k)]
    rw [← Finset.sum_mul, hgauss]
    simp only [zpow_neg, zpow_natCast, one_div, gaussSum]
    ring
  have hB : generalizedBernoulli χ k =
      (N : ℂ) ^ (k - 1) *
        ∑ a : ZMod N, χ a * bernoulliFun k (a.val / (N : ℝ)) := by
    rw [generalizedBernoulli_def]
    have hexp : (k : ℤ) - 1 = ((k - 1 : ℕ) : ℤ) := by omega
    rw [hexp, zpow_natCast, map_pow, map_natCast]
    congr 1
    apply Finset.sum_congr rfl
    intro a _
    congr 1
    have hcast (x : ℚ) :
        algebraMap ℚ ℂ ((Polynomial.bernoulli k).eval x) =
          bernoulliFun k (x : ℝ) := by
      simp only [bernoulliFun, Polynomial.eval_map, ← map_ratCast (algebraMap ℚ ℝ),
        Polynomial.eval₂_at_apply]
      norm_cast
    by_cases ha : a = 0
    · subst a
      simp only [ite_true, div_self (Nat.cast_ne_zero.mpr (NeZero.ne N) : (N : ℚ) ≠ 0),
        hcast, Rat.cast_one, ZMod.val_zero, Nat.cast_zero, zero_div]
      exact congrArg ((↑) : ℝ → ℂ)
        (bernoulliFun_endpoints_eq_of_ne_one (by omega : k ≠ 1))
    · simp only [ha, ite_false, hcast, Rat.cast_div, Rat.cast_natCast]
  have hresult := hsum.congr_fun (fun n ↦ (hterm n).symm)
  rw [← tsum_mul_left, hresult.tsum_eq, hB]
  simp_rw [← mul_assoc, mul_comm (χ _ : ℂ) (-(2 * π * I) ^ k / (k.factorial : ℂ)),
    mul_assoc]
  rw [← Finset.mul_sum]
  field_simp

/-! ### From the integer-indexed sum to `L(k, χ)` -/

/-- For `k ≥ 2`, `∑_{n ≥ 0} χ(n) n^{-k}` converges to `L(k, χ)`. -/
theorem hasSum_LFunction_natCast (hk : 2 ≤ k) :
    HasSum (fun n : ℕ ↦ χ (n : ZMod N) * (n : ℂ) ^ (-(k : ℤ)))
      (DirichletCharacter.LFunction χ k) := by
  have hre : 1 < (k : ℂ).re := by
    simp only [natCast_re]
    exact_mod_cast hk
  rw [DirichletCharacter.LFunction_eq_LSeries χ hre]
  have h := (DirichletCharacter.LSeriesSummable_of_one_lt_re χ hre).hasSum
  refine h.congr_fun fun n ↦ ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [Nat.cast_zero, LSeries.term_zero]
    rw [zero_zpow _ (by omega), mul_zero]
  · rw [LSeries.term_of_ne_zero hn, cpow_natCast, zpow_neg, zpow_natCast, div_eq_mul_inv]

/-- For `k ≥ 2` and `χ(-1) = (-1)^k`, the integer-indexed sum `∑_{n ∈ ℤ} χ(n) n^{-k}` is
`2 L(k, χ)` (the term `n = 0` is `0` since `0^{-k} = 0` in Lean). -/
theorem hasSum_int_eq_two_mul_LFunction (hk : 2 ≤ k) (hpar : χ (-1) = (-1) ^ k) :
    HasSum (fun n : ℤ ↦ χ (n : ZMod N) * (n : ℂ) ^ (-(k : ℤ)))
      (2 * DirichletCharacter.LFunction χ k) := by
  have h1 := hasSum_LFunction_natCast χ hk
  have h1' : HasSum (fun n : ℕ ↦ χ ((n : ℤ) : ZMod N) * ((n : ℤ) : ℂ) ^ (-(k : ℤ)))
      (DirichletCharacter.LFunction χ k) := by
    simpa only [Int.cast_natCast] using h1
  have h2 : HasSum (fun n : ℕ ↦ χ ((-(n : ℤ) : ℤ) : ZMod N) * ((-(n : ℤ) : ℤ) : ℂ) ^ (-(k : ℤ)))
      (DirichletCharacter.LFunction χ k) := by
    refine h1.congr_fun fun n ↦ ?_
    have hneg : ((-(n : ℤ) : ℤ) : ZMod N) = -1 * (n : ZMod N) := by push_cast; ring
    have hc : ((-(n : ℤ) : ℤ) : ℂ) = (-1) * (n : ℂ) := by push_cast; ring
    rw [hneg, map_mul, hpar, hc, mul_zpow, zpow_neg (-1 : ℂ), zpow_natCast]
    have hne : ((-1 : ℂ) ^ k) ≠ 0 := pow_ne_zero _ (by norm_num)
    field_simp
  have h := HasSum.of_nat_of_neg
    (f := fun n : ℤ ↦ χ (n : ZMod N) * (n : ℂ) ^ (-(k : ℤ))) h1' h2
  have h0 : χ ((0 : ℤ) : ZMod N) * ((0 : ℤ) : ℂ) ^ (-(k : ℤ)) = 0 := by
    rw [Int.cast_zero, Int.cast_zero, zero_zpow _ (by omega), mul_zero]
  rw [h0, sub_zero, ← two_mul] at h
  exact h

/-- **`L(k, χ)` for `k ≥ 2`, primitive `χ`, `χ(-1) = (-1)^k`** (Washington, Chapter 4): with
`δ = k mod 2` (so `χ(-1) = (-1)^δ`),
`L(k, χ) = (-1)^{1+(k-δ)/2} τ(χ) / (2 i^δ) · (2π/N)^k · B_{k,χ̄} / k!`. -/
theorem LFunction_natCast_of_two_le (hχ : χ.IsPrimitive) (hk : 2 ≤ k)
    (hpar : χ (-1) = (-1) ^ k) :
    DirichletCharacter.LFunction χ k =
      (-1) ^ (1 + (k - k % 2) / 2) * gaussSum χ ZMod.stdAddChar / (2 * I ^ (k % 2)) *
        (2 * π / N) ^ k * generalizedBernoulli χ⁻¹ k / k.factorial := by
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hk! : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  -- Tau Ceti's identity for `χ⁻¹`
  have hT := gaussSum_mul_tsum_inv_pow_eq_generalizedBernoulli χ⁻¹ hχ.inv hk
  rw [inv_inv, (hasSum_int_eq_two_mul_LFunction χ hk hpar).tsum_eq] at hT
  -- `τ(χ) τ(χ⁻¹) = χ(-1) N`
  have hG := gaussSum_mul_gaussSum_inv_eq_neg_one_mul_card_of_isPrimitive hχ
    (ZMod.isPrimitive_stdAddChar N)
  rw [ZMod.card, hpar] at hG
  -- the sign: `-i^k (-1)^k = (-1)^{1+(k-δ)/2} / i^δ`
  have hsign : -(I ^ k) * (-1) ^ k = (-1) ^ (1 + (k - k % 2) / 2) / I ^ (k % 2) := by
    obtain ⟨j, hj | hj⟩ := Nat.even_or_odd' k
    · subst hj
      have h1 : (2 * j) % 2 = 0 := by omega
      have h2 : (2 * j - 0) / 2 = j := by omega
      rw [h1, h2, pow_zero, div_one, pow_mul, pow_mul, I_sq]
      ring
    · subst hj
      have h1 : (2 * j + 1) % 2 = 1 := by omega
      have h2 : (2 * j + 1 - 1) / 2 = j := by omega
      rw [h1, h2, pow_one, pow_succ, pow_succ, pow_mul, pow_mul, I_sq]
      field_simp
      ring_nf
      rw [I_sq]
      ring
  have hNk1 : (N : ℂ) ^ k = (N : ℂ) ^ (k - 1) * N := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega)]
  have hI : I ^ (k % 2) ≠ 0 := pow_ne_zero _ I_ne_zero
  set L := DirichletCharacter.LFunction χ k
  set τ := gaussSum χ ZMod.stdAddChar
  set B := generalizedBernoulli χ⁻¹ k
  set c : ℂ := (-1) ^ k with hc
  -- multiply `hT` by `τ(χ)` and use `hG`
  have hmain : c * (N : ℂ) * (2 * L) =
      τ * (-(2 * π * I) ^ k / ((k.factorial : ℂ) * (N : ℂ) ^ (k - 1)) * B) := by
    rw [← hT, ← mul_assoc τ, hG]
  have hpow : c * c = 1 := by rw [hc, ← mul_pow]; norm_num
  have hL : 2 * N * L = c * (τ * (-(2 * π * I) ^ k /
      ((k.factorial : ℂ) * (N : ℂ) ^ (k - 1)) * B)) := by
    rw [← hmain]
    linear_combination (-(2 * N * L)) * hpow
  have hL' : L = c * (τ * (-(2 * π * I) ^ k /
      ((k.factorial : ℂ) * (N : ℂ) ^ (k - 1)) * B)) / (2 * N) := by
    rw [eq_div_iff (mul_ne_zero two_ne_zero hN)]
    linear_combination hL
  have hsign' : (-1 : ℂ) ^ (1 + (k - k % 2) / 2) = -(I ^ k) * c * I ^ (k % 2) := by
    rw [hsign]
    field_simp
  rw [hL', hsign', mul_pow, mul_pow, div_pow, hNk1]
  field_simp
  ring
