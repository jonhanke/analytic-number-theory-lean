/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import NTKB.Analytic.Davenport.Hadamard.XiChar

/-!
# The unsymmetric functional equation of `L(s, χ)` (Davenport, Chapter 19)

**Davenport, Ch. 19, p. 116 (row 19-4).** For `χ` primitive mod `q > 1`, with `a = 0` or `1`
according as `χ(-1) = 1` or `-1`,
`L(1 - s, χ̄) = ε(χ̄) 2^{1-s} π^{-s} q^{s-1/2} cos(½π(s - a)) Γ(s) L(s, χ)`, `|ε(χ̄)| = 1`.
From Mathlib's completed form `DirichletCharacter.IsPrimitive.completedLFunction_one_sub` (for `χ̄`)
and `Complex.Gammaℝ_div_Gammaℝ_one_sub` (Legendre's duplication and the reflection formula).
The constant is Mathlib's root number `ε(χ̄) = τ(χ̄)/(i^a q^{1/2})`, and `ε(χ̄) = ε(χ)⁻¹`.
-/

open Complex DirichletCharacter
open scoped Real

namespace NTKB

lemma inv_Gammaℝ_one_sub_parity {a s : ℂ} (ha : a = 0 ∨ a = 1) (hs : ∀ n : ℕ, s ≠ -n) :
    (Gammaℝ (1 - s + a))⁻¹ * Gammaℝ (s + a) =
      Gammaℂ s * Complex.cos (π * (s - a) / 2) := by
  have hG : Gammaℝ (s + a) ≠ 0 := by
    rw [Ne, Gammaℝ_eq_zero_iff, not_exists]
    intro n h
    rcases ha with rfl | rfl
    · exact hs (2 * n) (by simpa using h)
    · apply hs (2 * n + 1)
      push_cast
      linear_combination h
  rcases ha with rfl | rfl
  · rw [add_zero] at hG
    rw [add_zero, add_zero, inv_Gammaℝ_one_sub hs, sub_zero]
    field_simp
  · have h1 : 1 - s + 1 = 2 - s := by ring
    rw [h1, inv_Gammaℝ_two_sub hs]
    have h2 : π * (s - 1) / 2 = π * s / 2 - π / 2 := by ring
    rw [h2, Complex.cos_sub_pi_div_two]
    field_simp

lemma Gammaℂ_eq_two_pow (s : ℂ) :
    Gammaℂ s = 2 ^ (1 - s) * (π : ℂ) ^ (-s) * Complex.Gamma s := by
  have h : (2 * (π : ℂ)) = ((2 : ℝ) : ℂ) * (π : ℂ) := by push_cast; ring
  rw [Gammaℂ_def, h, Complex.mul_cpow_ofReal_nonneg (by norm_num) Real.pi_pos.le]
  push_cast
  rw [Complex.cpow_sub _ _ two_ne_zero, Complex.cpow_one, Complex.cpow_neg]
  field_simp

/-- **Davenport, Ch. 19, p. 116 (row 19-4)**: for `χ` primitive mod `N > 1` and `s` not in
`{0, -1, -2, …}`, `L(1 - s, χ̄) = ε 2^{1-s} π^{-s} N^{s-1/2} cos(π(s - a)/2) Γ(s) L(s, χ)` with
`ε = rootNumber χ⁻¹`, `|ε| = 1` and `ε = (rootNumber χ)⁻¹`. -/
@[kb "davenport1980" "Ch 19, p. 116"]
theorem Davenport.LFunction_one_sub_unsymmetric {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ.IsPrimitive) (hN : N ≠ 1) {s : ℂ} (hs : ∀ n : ℕ, s ≠ -n) :
    LFunction χ⁻¹ (1 - s) = rootNumber χ⁻¹ * 2 ^ (1 - s) * (π : ℂ) ^ (-s) * (N : ℂ) ^ (s - 1 / 2) *
        Complex.cos (π * (s - dirichletParity χ) / 2) * Complex.Gamma s * LFunction χ s ∧
      ‖rootNumber χ⁻¹‖ = 1 ∧ rootNumber χ⁻¹ = (rootNumber χ)⁻¹ := by
  have hψ : (χ⁻¹).IsPrimitive := hχ.inv
  have hpar : dirichletParity χ = 0 ∨ dirichletParity χ = 1 := by
    unfold dirichletParity; split_ifs <;> simp
  refine ⟨?_, norm_rootNumber hψ, ?_⟩
  · have hG : Gammaℝ (s + dirichletParity χ) ≠ 0 := by
      rw [Ne, Gammaℝ_eq_zero_iff, not_exists]
      intro n h
      rcases hpar with h0 | h0
      · rw [h0] at h; exact hs (2 * n) (by simpa using h)
      · rw [h0] at h
        apply hs (2 * n + 1)
        push_cast
        linear_combination h
    have e1 := hψ.completedLFunction_one_sub s
    rw [inv_inv] at e1
    have e2 : completedLFunction χ s = LFunction χ s * Gammaℝ (s + dirichletParity χ) := by
      rw [LFunction_eq_completed_div_gammaFactor χ s (Or.inr hN), gammaFactor_eq]
      field_simp
    rw [LFunction_eq_completed_div_gammaFactor χ⁻¹ (1 - s) (Or.inr hN), gammaFactor_eq,
      dirichletParity_inv, e1, e2]
    have := inv_Gammaℝ_one_sub_parity hpar hs
    rw [Gammaℂ_eq_two_pow] at this
    calc (N : ℂ) ^ (s - 1 / 2) * rootNumber χ⁻¹ *
          (LFunction χ s * Gammaℝ (s + dirichletParity χ)) / Gammaℝ (1 - s + dirichletParity χ)
        = (N : ℂ) ^ (s - 1 / 2) * rootNumber χ⁻¹ * LFunction χ s *
          ((Gammaℝ (1 - s + dirichletParity χ))⁻¹ * Gammaℝ (s + dirichletParity χ)) := by
          rw [div_eq_mul_inv]; ring
      _ = _ := by rw [this]; ring
  · exact eq_inv_of_mul_eq_one_right (rootNumber_mul_rootNumber_inv hχ)

end NTKB
