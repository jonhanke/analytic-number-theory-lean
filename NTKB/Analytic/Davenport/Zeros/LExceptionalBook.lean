/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Davenport.Zeros.LExceptional

/-!
# The exceptional zero in the book's form

**Davenport, Ch. 19, p. 118 (row 19-11).** There is an absolute constant `c > 0` such that for every
`q` and every nonprincipal character `χ` mod `q`, `L(s, χ)` has no zero `β + iγ` with `|γ| < 1` and
`β > 1 - c/log q`, unless `χ` is real; then there is at most one such zero, it is real (`β₁`), and
for primitive `χ` it is simple and `1 - β₁` is also a zero. Here `c = 1/16200`, uniformly in `q`.

Assembled from the zero-free region 14-11 (`Davenport.LFunction_zero_free_theorem_complex`,
`Davenport.LFunction_zero_free_theorem_real`, `Davenport.LFunction_zero_free_theorem_real_simple`)
and the functional equation of `ξ(s, χ)` (`dirichletXi_one_sub`). Simplicity is proved as a zero of
`ξ(s, χ)` for primitive `χ`. Source text unavailable: the statement follows the
map's paraphrase.
-/

open Filter Topology Complex Set DirichletCharacter
open scoped Real

namespace NTKB

/-- **Davenport, Ch. 19, p. 118 (row 19-11)**, the exceptional zero, uniformly in `q`
(`c = 1/16200`): for `χ ≠ χ₀` mod `q`, (1) a zero `s` of `L(s, χ)` with `|Im s| < 1` and
`Re s > 1 - c/log q` occurs only for real `χ`, is real, and is the only zero in that region;
(2) for `χ` primitive, such a zero `β₁` is a simple zero of `ξ(s, χ)` and `L(1 - β₁, χ) = 0`. -/
@[kb "davenport1980" "Ch 19, p. 118"]
theorem Davenport.exceptional_zero_uniform :
    ∃ c : ℝ, 0 < c ∧ ∀ {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}, χ ≠ 1 →
      (∀ s : ℂ, LFunction χ s = 0 → |s.im| < 1 → 1 - c / Real.log q < s.re →
        χ ^ 2 = 1 ∧ s.im = 0 ∧
          ∀ s' : ℂ, LFunction χ s' = 0 → |s'.im| < 1 → 1 - c / Real.log q < s'.re → s' = s) ∧
      (χ.IsPrimitive → ∀ ρ : ZeroIndex (dirichletXi χ), |ρ.val.im| < 1 →
        1 - c / Real.log q < ρ.val.re →
        analyticOrderNatAt (dirichletXi χ) ρ.val = 1 ∧ LFunction χ (1 - ρ.val) = 0) := by
  refine ⟨1 / 16200, by norm_num, ?_⟩
  intro q _ χ hχ1
  have hq2 := two_le_of_ne_one hχ1
  have hq1 : (1 : ℝ) ≤ q := by linarith
  have hreg : ∀ s : ℂ, |s.im| < 1 → (1 - 1 / 16200 / Real.log q < s.re ↔ IsExcPoint q s) := by
    intro s hs
    unfold IsExcPoint
    rw [logQT_of_lt_one hq1 hs]
  have part1 : ∀ s : ℂ, LFunction χ s = 0 → |s.im| < 1 → 1 - 1 / 16200 / Real.log q < s.re →
      χ ^ 2 = 1 ∧ s.im = 0 ∧
        ∀ s' : ℂ, LFunction χ s' = 0 → |s'.im| < 1 → 1 - 1 / 16200 / Real.log q < s'.re →
          s' = s := by
    intro s hs him hre
    have hE := (hreg s him).1 hre
    obtain ⟨h2, h0⟩ := Davenport.exceptional_zero_real hχ1 hs hE
    refine ⟨h2, h0, fun s' hs' him' hre' ↦ ?_⟩
    have := (Davenport.LFunction_zero_free_theorem_real hχ1 h2 hs hE).2 s' hs'
    rw [logQT_of_lt_one hq1 him'] at this
    exact this (by simpa [logQT_of_lt_one hq1 him'] using hre')
  refine ⟨part1, fun hχ ρ him hre ↦ ?_⟩
  have hN : q ≠ 1 := by rintro rfl; norm_num at hq2
  obtain ⟨hz, h0, h1⟩ := dirichletXi_zero_mem hχ hN ρ
  have h2 := (part1 _ hz him hre).1
  refine ⟨?_, ?_⟩
  · apply Davenport.LFunction_zero_free_theorem_real_simple hχ hχ1 h2 ρ
    rw [logQT_of_lt_one hq1 him]; exact hre
  · have hinv : χ⁻¹ = χ := by
      have : χ * χ = 1 := by rw [← pow_two]; exact h2
      exact inv_eq_of_mul_eq_one_right this
    have hx : dirichletXi χ ρ.val = 0 := ZeroIndex.apply_val_eq_zero
      ((differentiable_dirichletXi hχ1).analyticAt _)
    have := dirichletXi_one_sub hχ ρ.val
    rw [hinv, hx, mul_zero] at this
    exact ((dirichletXi_eq_zero_iff hχ hN).1 this).1

end NTKB
