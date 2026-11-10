/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Elementary.SpecialValues.ValueAtZero
import NTKB.Elementary.SpecialValues.PositiveValues

/-!
# `L(k, χ)` for primitive `χ`, every `k ≥ 1` with `χ(-1) = (-1)^k`

The case `k = 1` (odd `χ`): `L(1, χ) = π i τ(χ) B_{1,χ̄} / f`, obtained from Mathlib's functional
equation for primitive characters (`DirichletCharacter.IsPrimitive.completedLFunction_one_sub`) and
`L(0, χ̄) = -B_{1,χ̄}` (`NTKB.LFunction_zero`). Together with `NTKB.LFunction_natCast_of_two_le`:

**Washington, Chapter 4** (locator of the original request: Theorem 4.2, Corollary 4.4; not checked against the book). For a primitive Dirichlet character `χ` modulo `f` and `k ≥ 1`
with `χ(-1) = (-1)^k`, writing `δ = k mod 2` (so `χ(-1) = (-1)^δ`),
$$L(k,\chi) = (-1)^{1+(k-\delta)/2}\,\frac{\tau(\chi)}{2 i^{\delta}}
  \left(\frac{2\pi}{f}\right)^{k}\frac{B_{k,\bar\chi}}{k!}.$$
-/

noncomputable section

open Complex
open scoped Real

namespace NTKB

variable {N : ℕ} [NeZero N]

private lemma Gammaℝ_two : Gammaℝ 2 = (π : ℂ)⁻¹ := by
  rw [Gammaℝ_def]
  norm_num [Complex.Gamma_one, cpow_neg_one]

/-- **`L(1, χ) = π i τ(χ) B_{1,χ̄} / f`** for a primitive odd character `χ` modulo `f`. -/
theorem LFunction_one_of_odd {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (hodd : χ.Odd) :
    DirichletCharacter.LFunction χ 1 =
      π * I * gaussSum χ ZMod.stdAddChar * generalizedBernoulli χ⁻¹ 1 / N := by
  have hχ1 : χ ≠ 1 := by
    rintro rfl
    exact DirichletCharacter.Odd.not_even _ hodd DirichletCharacter.even_one
  have hN1 : N ≠ 1 := fun h ↦ hχ1 (χ.level_one' h)
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hinvodd : χ⁻¹.Odd := by
    rw [DirichletCharacter.Odd, MulChar.inv_apply_eq_inv', hodd, inv_neg, inv_one]
  have hinvnoteven : ¬ χ⁻¹.Even := DirichletCharacter.Odd.not_even _ hinvodd
  -- the functional equation for `χ⁻¹` at `s = 1`
  have hFE := hχ.inv.completedLFunction_one_sub 1
  rw [inv_inv, sub_self] at hFE
  -- completed values in terms of `L`-values
  have h0 := DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ⁻¹ 0 (Or.inr hN1)
  have h1 := DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ 1 (Or.inl one_ne_zero)
  rw [hinvodd.gammaFactor_def, zero_add, Gammaℝ_one, div_one] at h0
  rw [hodd.gammaFactor_def, one_add_one_eq_two, Gammaℝ_two, div_inv_eq_mul] at h1
  rw [← h0, LFunction_zero χ⁻¹] at hFE
  -- the root number
  have hroot : DirichletCharacter.rootNumber χ⁻¹ =
      gaussSum χ⁻¹ ZMod.stdAddChar / I / (N : ℂ) ^ (1 / 2 : ℂ) := by
    simp [DirichletCharacter.rootNumber, hinvnoteven]
  have hsqrt : (N : ℂ) ^ (1 - 1 / 2 : ℂ) = (N : ℂ) ^ (1 / 2 : ℂ) := by norm_num
  have hsqrt0 : (N : ℂ) ^ (1 / 2 : ℂ) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hN)
  rw [hroot, hsqrt] at hFE
  -- `τ(χ) τ(χ⁻¹) = -N`
  have hG := gaussSum_mul_gaussSum_inv_eq_neg_one_mul_card_of_isPrimitive hχ
    (ZMod.isPrimitive_stdAddChar N)
  rw [ZMod.card, hodd] at hG
  -- solve
  have hC : DirichletCharacter.completedLFunction χ 1 =
      DirichletCharacter.LFunction χ 1 / π := by
    rw [h1]
    have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
    field_simp
  rw [hC] at hFE
  have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  -- hFE : -B = √N * (τ(χ⁻¹)/I/√N) * (L/π)
  have key : gaussSum χ⁻¹ ZMod.stdAddChar * DirichletCharacter.LFunction χ 1 =
      -(I * π * generalizedBernoulli χ⁻¹ 1) := by
    field_simp at hFE
    linear_combination -hFE
  have hτ : gaussSum χ ZMod.stdAddChar * gaussSum χ⁻¹ ZMod.stdAddChar = -(N : ℂ) := by
    rw [hG]; ring
  have hL : (N : ℂ) * DirichletCharacter.LFunction χ 1 =
      π * I * gaussSum χ ZMod.stdAddChar * generalizedBernoulli χ⁻¹ 1 := by
    linear_combination (DirichletCharacter.LFunction χ 1) * hτ -
      gaussSum χ ZMod.stdAddChar * key
  rw [eq_div_iff hN, mul_comm]
  exact hL

/-- **Washington, Chapter 4**: for a primitive Dirichlet character `χ` modulo `N` and
`k ≥ 1` with `χ(-1) = (-1)^k`, with `δ = k mod 2`,
`L(k, χ) = (-1)^{1+(k-δ)/2} τ(χ) / (2 i^δ) · (2π/N)^k · B_{k,χ̄} / k!`,
where `τ(χ) = gaussSum χ ZMod.stdAddChar = ∑_a χ(a) e^{2πia/N}` and `χ̄ = χ⁻¹`. -/
@[kb "washington1997" "Ch. 4 (L(n, χ) from the functional equation; locator unverified)"]
theorem LFunction_natCast (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) {k : ℕ}
    (hk : 1 ≤ k) (hpar : χ (-1) = (-1) ^ k) :
    DirichletCharacter.LFunction χ k =
      (-1) ^ (1 + (k - k % 2) / 2) * gaussSum χ ZMod.stdAddChar / (2 * I ^ (k % 2)) *
        (2 * π / N) ^ k * generalizedBernoulli χ⁻¹ k / k.factorial := by
  rcases eq_or_lt_of_le hk with rfl | hk2
  · have hodd : χ.Odd := by rw [DirichletCharacter.Odd, hpar, pow_one]
    rw [Nat.cast_one, LFunction_one_of_odd hχ hodd]
    have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
    norm_num
    field_simp
    ring_nf
    rw [I_sq]
    ring
  · exact LFunction_natCast_of_two_le χ hχ hk2 hpar

end NTKB
