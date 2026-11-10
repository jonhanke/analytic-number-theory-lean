/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.Analysis.Fourier.ZMod
import NTKB.Analytic.Apostol.Zeta.LZero

/-!
# Hurwitz's formula at rational points; `L(s, χ)` through the periodic zeta function
(Apostol, Theorems 12.8 and 12.10)

`F(x, s) = ∑_{n ≥ 1} e^{2πinx} n^{-s}` is Mathlib's `expZeta x s` (the periodic zeta function).

* **Theorem 12.8**: for integers `1 ≤ h ≤ k`,
  `ζ(1-s, h/k) = 2Γ(s)/(2πk)^s ∑_{r=1}^{k} cos(πs/2 - 2πrh/k) ζ(s, r/k)`
  (for `s ≠ 0, -1, -2, …`, the poles of `Γ`, and `s ≠ 1` when `h = k`: at these points the two
  sides of Apostol's "for all s" are understood as limits).
* **Theorem 12.10**: for a primitive character `χ` mod `k`,
  `∑_{h mod k} χ(h) F(h/k, s) = G(1, χ) L(s, χ̄)` (Apostol states it for `σ > 1`; it holds for
  `s ≠ 1`).

Both follow from Mathlib's expression of `F(h/k, s)` as a combination of Hurwitz zeta functions
(`ZMod.LFunction_stdAddChar_eq_expZeta`) and Mathlib's functional equation `hurwitzZeta_one_sub`
(Theorem 12.6), as in Apostol.
-/

open Complex Finset HurwitzZeta ZMod
open scoped Real

namespace NTKB.Apostol

/-- `∑_{r mod k} g(r) = ∑_{r=1}^{k} g(r)` for `g` with `g(k) = g(0)`. -/
lemma sum_zmod_val_eq_sum_Icc {M : Type*} [AddCommMonoid M] (k : ℕ) [NeZero k] (g : ℕ → M)
    (hg : g k = g 0) : ∑ r : ZMod k, g r.val = ∑ r ∈ Icc 1 k, g r := by
  rw [sum_Icc_one_eq_sum_range g k hg]
  symm
  refine sum_nbij' (fun r ↦ (r : ZMod k)) (fun x ↦ x.val) (by simp) (fun x _ ↦ by
    simpa using ZMod.val_lt x) (fun r hr ↦ ?_) (fun x _ ↦ by simp) (fun r hr ↦ ?_)
  · rw [ZMod.val_natCast, Nat.mod_eq_of_lt (mem_range.mp hr)]
  · rw [ZMod.val_natCast, Nat.mod_eq_of_lt (mem_range.mp hr)]

lemma stdAddChar_natCast_mul (k : ℕ) [NeZero k] (h : ℕ) (r : ZMod k) :
    stdAddChar ((h : ZMod k) * r) = cexp (2 * π * I * (h * r.val : ℕ) / k) := by
  have : (h : ZMod k) * r = (((h * r.val : ℕ) : ℤ) : ZMod k) := by push_cast; simp
  rw [this, ZMod.stdAddChar_coe]
  push_cast
  ring_nf

/-- **Apostol, Theorem 12.8**: for integers `1 ≤ h ≤ k`,
`ζ(1-s, h/k) = 2Γ(s)/(2πk)^s ∑_{r=1}^{k} cos(πs/2 - 2πrh/k) ζ(s, r/k)`. -/
@[kb "apostol1976" "Thm 12.8, p. 261"]
theorem apostol_thm_12_8 {h k : ℕ} (hh : 1 ≤ h) (hhk : h ≤ k) {s : ℂ} (hs : ∀ n : ℕ, s ≠ -n)
    (hs1 : h ≠ k ∨ s ≠ 1) :
    hurwitzZeta ((h : ℝ) / (k : ℝ)) (1 - s) = 2 * Gamma s / (2 * π * (k : ℂ)) ^ s *
      ∑ r ∈ Icc 1 k, Complex.cos (π * s / 2 - 2 * π * (r : ℂ) * (h : ℂ) / (k : ℂ)) *
        hurwitzZeta ((r : ℝ) / (k : ℝ)) s := by
  have hk : 0 < k := by omega
  have : NeZero k := ⟨hk.ne'⟩
  have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  set j : ZMod k := (h : ZMod k)
  have hja : toAddCircle j = (((h : ℝ) / k : ℝ) : UnitAddCircle) := toAddCircle_natCast h
  have hj0 : j ≠ 0 ∨ s ≠ 1 := by
    rcases hs1 with h1 | h1
    · left
      intro hj
      rw [ZMod.natCast_eq_zero_iff] at hj
      exact h1 (Nat.le_antisymm hhk (Nat.le_of_dvd (by omega) hj))
    · exact Or.inr h1
  have ha0 : toAddCircle j ≠ 0 ∨ s ≠ 1 := hj0.imp_left (toAddCircle_eq_zero.not.mpr)
  rw [← hja, hurwitzZeta_one_sub _ hs ha0, ← map_neg,
    ← LFunction_stdAddChar_eq_expZeta j s hj0,
    ← LFunction_stdAddChar_eq_expZeta (-j) s (hj0.imp_left neg_ne_zero.mpr)]
  rw [ZMod.LFunction, ZMod.LFunction]
  -- the cosine combination
  have hcos : ∀ r : ZMod k, cexp (-π * I * s / 2) * stdAddChar (j * r) +
      cexp (π * I * s / 2) * stdAddChar (-j * r) =
      2 * Complex.cos (π * s / 2 - 2 * π * (r.val : ℕ) * h / k) := by
    intro r
    have e1 := stdAddChar_natCast_mul k h r
    have e2 : stdAddChar (-j * r) = cexp (-(2 * π * I * (h * r.val : ℕ) / k)) := by
      rw [neg_mul, AddChar.map_neg_eq_inv, e1, Complex.exp_neg]
    rw [e1, e2, Complex.cos, ← Complex.exp_add, ← Complex.exp_add]
    push_cast
    ring_nf
  have hsum : ∀ r : ZMod k, cexp (-π * I * s / 2) * (stdAddChar (j * r) *
      hurwitzZeta (toAddCircle r) s) + cexp (π * I * s / 2) * (stdAddChar (-j * r) *
      hurwitzZeta (toAddCircle r) s) =
      2 * (Complex.cos (π * s / 2 - 2 * π * (r.val : ℕ) * h / k) *
        hurwitzZeta (((r.val : ℕ) : ℝ) / k : ℝ) s) := by
    intro r
    rw [← mul_assoc, ← mul_assoc, ← add_mul, hcos r, toAddCircle_apply]
    ring
  have hg : Complex.cos (π * s / 2 - 2 * π * ((k : ℕ) : ℂ) * h / k) *
      hurwitzZeta (((k : ℕ) : ℝ) / k : ℝ) s = Complex.cos (π * s / 2 - 2 * π * ((0 : ℕ) : ℂ) * h / k) *
      hurwitzZeta (((0 : ℕ) : ℝ) / k : ℝ) s := by
    have hk' : ((k : ℝ) / k : ℝ) = 1 := div_self (by exact_mod_cast hk.ne')
    have hc : π * s / 2 - 2 * π * (k : ℂ) * h / k = π * s / 2 - (h : ℤ) * (2 * π) := by
      push_cast; field_simp
    rw [hk', hc, Complex.cos_sub_int_mul_two_pi]
    simp only [Nat.cast_zero, mul_zero, zero_mul, zero_div, sub_zero]
    rw [show ((1 : ℝ) : UnitAddCircle) = ((0 : ℝ) : UnitAddCircle) by
      rw [AddCircle.coe_period, QuotientAddGroup.mk_zero]]
  have hcomb : cexp (-π * I * s / 2) * ∑ r : ZMod k, stdAddChar (j * r) *
      hurwitzZeta (toAddCircle r) s + cexp (π * I * s / 2) * ∑ r : ZMod k,
      stdAddChar (-j * r) * hurwitzZeta (toAddCircle r) s =
      2 * ∑ r ∈ Icc 1 k, Complex.cos (π * s / 2 - 2 * π * (r : ℂ) * (h : ℂ) / (k : ℂ)) *
        hurwitzZeta ((r : ℝ) / (k : ℝ)) s := by
    rw [mul_sum, mul_sum, ← sum_add_distrib]
    simp_rw [hsum]
    have := sum_zmod_val_eq_sum_Icc k (fun r : ℕ ↦ Complex.cos (π * s / 2 - 2 * π * (r : ℂ) * h / k) *
      hurwitzZeta ((r : ℝ) / k : ℝ) s) hg
    rw [← mul_sum, this]
  have h2 : (2 * π * k : ℂ) ^ (-s) = (2 * π : ℂ) ^ (-s) * (k : ℂ) ^ (-s) := by
    have := mul_cpow_ofReal_nonneg (by positivity : (0 : ℝ) ≤ 2 * π)
      (by positivity : (0 : ℝ) ≤ k) (-s)
    push_cast at this
    exact this
  rw [div_eq_mul_inv (2 * Gamma s), ← cpow_neg, h2]
  linear_combination ((2 * π : ℂ) ^ (-s) * Gamma s * (k : ℂ) ^ (-s)) * hcomb

/-- **Apostol, Theorem 12.10**: for a primitive character `χ` mod `k`,
`∑_{h mod k} χ(h) F(h/k, s) = G(1, χ) L(s, χ̄)`, `F` the periodic zeta function and
`G(1, χ) = ∑_r χ(r) e^{2πir/k}`; for `σ > 1` (as in Apostol), indeed for all `s ≠ 1`. -/
@[kb "apostol1976" "Thm 12.10, p. 262"]
theorem apostol_thm_12_10 {k : ℕ} [NeZero k] {χ : DirichletCharacter ℂ k} (hχ : χ.IsPrimitive)
    {s : ℂ} (hs : s ≠ 1) :
    ∑ h : ZMod k, χ h * expZeta (toAddCircle h) s =
      gaussSum χ stdAddChar * (χ⁻¹).LFunction s := by
  have hdft := LFunction_dft (χ : ZMod k → ℂ) (s := s) (Or.inr hs)
  -- `L(𝓕 χ) = G(1, χ) χ⁻¹(-1) L(χ⁻¹)`
  have hF : (𝓕 (χ : ZMod k → ℂ)) = fun r ↦ χ⁻¹ (-1) * gaussSum χ stdAddChar * χ⁻¹ r := by
    funext r
    rw [hχ.fourierTransform_eq_inv_mul_gaussSum, ← neg_one_mul r, map_mul]
    ring
  have hL : ZMod.LFunction (𝓕 (χ : ZMod k → ℂ)) s =
      χ⁻¹ (-1) * gaussSum χ stdAddChar * (χ⁻¹).LFunction s := by
    rw [hF]
    simp only [DirichletCharacter.LFunction, ZMod.LFunction]
    rw [Finset.mul_sum (s := univ) (f := fun j : ZMod k ↦ χ⁻¹ j * hurwitzZeta (toAddCircle j) s),
      Finset.mul_sum, Finset.mul_sum]
    refine sum_congr rfl fun r _ ↦ ?_
    ring
  -- reindex `h ↦ -h`
  have hre : ∑ h : ZMod k, χ h * expZeta (toAddCircle h) s =
      χ (-1) * ∑ j : ZMod k, χ j * expZeta (toAddCircle (-j)) s := by
    rw [mul_sum]
    refine Fintype.sum_equiv (Equiv.neg (ZMod k)) _ _ fun j ↦ ?_
    simp only [Equiv.neg_apply, neg_neg]
    have hsq : χ (-1) * χ (-1) = 1 := by rw [← map_mul]; simp
    rw [← neg_one_mul j, map_mul]
    linear_combination (-(χ j * expZeta (toAddCircle j) s)) * hsq
  rw [hre, ← hdft, hL]
  have h1 : χ (-1) * χ⁻¹ (-1) = 1 := by
    have := congrArg (fun ψ : DirichletCharacter ℂ k ↦ ψ (-1)) (MulChar.inv_mul χ)
    simp only [MulChar.coeToFun_mul, Pi.mul_apply] at this
    rw [mul_comm, this, MulChar.one_apply isUnit_one.neg]
  linear_combination (gaussSum χ stdAddChar * (χ⁻¹).LFunction s) * h1

/-- Theorem 12.10 in Apostol's form for `σ > 1`, with `L(s, χ̄) = ∑ χ̄(n) n^{-s}`. -/
@[kb "apostol1976" "Thm 12.10, p. 262"]
theorem apostol_thm_12_10_LSeries {k : ℕ} [NeZero k] {χ : DirichletCharacter ℂ k}
    (hχ : χ.IsPrimitive) {s : ℂ} (hs : 1 < s.re) :
    ∑ h : ZMod k, χ h * expZeta (toAddCircle h) s =
      gaussSum χ stdAddChar * LSeries (fun n ↦ χ⁻¹ n) s := by
  rw [apostol_thm_12_10 hχ (fun h ↦ by simp [h] at hs),
    DirichletCharacter.LFunction_eq_LSeries _ hs]

end NTKB.Apostol
