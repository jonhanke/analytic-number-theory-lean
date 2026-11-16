/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Davenport.ClassNumber.Bounds
import NTKB.Analytic.Davenport.ClassNumber.Finite
import NTKB.Elementary.QuadraticField.IdealCount

/-!
# The class number formulas of quadratic fields with no assumed input

The two named statements of the conditional class number formulas are theorems:

* `NTKB.Davenport.quadraticFieldDiscriminants` (Davenport §5, p. 41, row 5-15): from `NTKB.QuadraticField.isFundamental_discr` (every quadratic number field is
  `ℚ(√D)` with `D` fundamental, of discriminant `D`, via Mathlib's `QuadraticAlgebra`) and
  `NTKB.QuadraticField.exists_field_discr_eq`;
* `NTKB.Davenport.quadraticIdealCount` (Davenport §6, p. 52): from the
  decomposition law and `NTKB.QuadraticField.card_absNorm_eq`.

So every theorem of `NTKB.Davenport.ClassNumber` that takes `hF`, `hI` holds unconditionally; the
`…_unconditional` versions below are those theorems with the two inputs discharged (the
conditional statements are unchanged).
-/

noncomputable section

open Complex DirichletCharacter Module NumberField NumberField.InfinitePlace NumberField.Units
  Finset
open scoped Real

namespace NTKB.Davenport

/-- **Davenport §5, p. 41 (row 5-15)**: the discriminant of a quadratic number field is a
fundamental discriminant, and every fundamental discriminant `D ≠ 1` is the discriminant of a
quadratic number field. -/
@[kb "davenport1980" "Ch 5, p. 41"]
theorem quadraticFieldDiscriminants : QuadraticFieldDiscriminants where
  isFundamental K _ _ hK := (QuadraticField.isFundamental_discr K hK).1
  exists_field _ hD h1 := QuadraticField.exists_field_discr_eq hD h1

/-- **The decomposition law, counted** (Davenport §6, p. 52): in a quadratic number field of
discriminant `d`, the number of ideals of norm `n ≥ 1` is `∑_{m ∣ n} (d/m)`. -/
@[kb "davenport1980" "Ch 6, p. 52"]
theorem quadraticIdealCount : QuadraticIdealCount where
  card_eq _ _ _ hK _ hn := QuadraticField.card_absNorm_eq hK hn

variable {K : Type} [Field K] [NumberField K]

/-- The Kronecker character of a quadratic field is not principal. -/
theorem kroneckerChar_discr_ne_one_unconditional (hK : finrank ℚ K = 2) :
    kroneckerChar (discr K) ≠ 1 :=
  kroneckerChar_discr_ne_one quadraticFieldDiscriminants hK

/-- **Davenport §6, p. 52, (27)**, unconditional: `ζ_K(s) = ζ(s) L(s, χ)` for `Re s > 1`. -/
@[kb "davenport1980" "Ch 6, p. 52, (27)"]
theorem dedekindZeta_eq_riemannZeta_mul_LFunction_unconditional (hK : finrank ℚ K = 2) {s : ℂ}
    (hs : 1 < s.re) :
    dedekindZeta K s = riemannZeta s * LFunction (kroneckerChar (discr K)) s :=
  dedekindZeta_eq_riemannZeta_mul_LFunction quadraticIdealCount hK hs

/-- **Davenport §6, p. 52**, unconditional: the residue of `ζ_K` at `1` is `L(1, χ)`. -/
@[kb "davenport1980" "Ch 6, p. 52"]
theorem dedekindZeta_residue_eq_LFunction_one_unconditional (hK : finrank ℚ K = 2) :
    (dedekindZeta_residue K : ℂ) = LFunction (kroneckerChar (discr K)) 1 :=
  dedekindZeta_residue_eq_LFunction_one quadraticFieldDiscriminants quadraticIdealCount hK

theorem LFunction_one_eq_residue_unconditional (hK : finrank ℚ K = 2) :
    LFunction (kroneckerChar (discr K)) 1 = (dedekindZeta_residue K : ℂ) :=
  LFunction_one_eq_residue quadraticFieldDiscriminants quadraticIdealCount hK

/-- **Davenport §6, p. 49, (15)**, unconditional: for `d < 0`, `h = w √|d| L(1, χ) / (2π)`. -/
@[kb "davenport1980" "Ch 6, p. 49, (15)"]
theorem classNumber_eq_of_discr_neg_unconditional (hK : finrank ℚ K = 2) (hD : discr K < 0) :
    (classNumber K : ℂ) =
      torsionOrder K * √|(discr K : ℝ)| * LFunction (kroneckerChar (discr K)) 1 / (2 * π) :=
  classNumber_eq_of_discr_neg quadraticFieldDiscriminants quadraticIdealCount hK hD

/-- **Davenport §6, p. 49, (16)**, unconditional: for `d > 0`, `2 h R = √d L(1, χ)`. -/
@[kb "davenport1980" "Ch 6, p. 49, (16)"]
theorem two_mul_classNumber_mul_regulator_eq_of_discr_pos_unconditional (hK : finrank ℚ K = 2)
    (hD : 0 < discr K) :
    ((2 * classNumber K * regulator K : ℝ) : ℂ) =
      √(discr K : ℝ) * LFunction (kroneckerChar (discr K)) 1 :=
  two_mul_classNumber_mul_regulator_eq_of_discr_pos quadraticFieldDiscriminants
    quadraticIdealCount hK hD

/-- **Davenport §6, p. 49, (16)**, unconditional, with a fundamental unit `ε`:
`h · |log w(ε)| = √d L(1, χ) / 2`. -/
@[kb "davenport1980" "Ch 6, p. 49, (16)"]
theorem classNumber_mul_log_eq_of_discr_pos_unconditional (hK : finrank ℚ K = 2)
    (hD : 0 < discr K) (ε : (𝓞 K)ˣ) (hε : Subgroup.closure {ε} ⊔ torsion K = ⊤)
    (w : InfinitePlace K) :
    ((classNumber K * |Real.log (w (ε : K))| : ℝ) : ℂ) =
      √(discr K : ℝ) * LFunction (kroneckerChar (discr K)) 1 / 2 :=
  classNumber_mul_log_eq_of_discr_pos quadraticFieldDiscriminants quadraticIdealCount hK hD ε hε w

/-- **Davenport §6, p. 51: the finite class number formula for `d < 0`**, unconditional:
`h(d) = -(w / (2|d|)) ∑_{m=1}^{|d|} m (d/m)`. -/
@[kb "davenport1980" "Ch 6, p. 51"]
theorem classNumber_eq_sum_of_discr_neg_unconditional (hK : finrank ℚ K = 2)
    (hD : discr K < 0) :
    (classNumber K : ℂ) = -((torsionOrder K : ℂ) / (2 * (discr K).natAbs)) *
      ∑ m ∈ Icc 1 (discr K).natAbs, (m : ℂ) * kroneckerChar (discr K) m :=
  classNumber_eq_sum_of_discr_neg quadraticFieldDiscriminants quadraticIdealCount hK hD

/-- **Davenport §6, p. 51: the finite class number formula for `d > 0`**, unconditional:
`h R = -(1/2) ∑_{m=1}^{d-1} (d/m) log sin(πm/d)`. -/
@[kb "davenport1980" "Ch 6, p. 51"]
theorem classNumber_mul_regulator_eq_sum_of_discr_pos_unconditional (hK : finrank ℚ K = 2)
    (hD : 0 < discr K) :
    ((classNumber K * regulator K : ℝ) : ℂ) = -(1 / 2) *
      ∑ m ∈ Ico 1 (discr K).natAbs,
        kroneckerChar (discr K) m * (Real.log (Real.sin (π * m / discr K)) : ℂ) :=
  classNumber_mul_regulator_eq_sum_of_discr_pos quadraticFieldDiscriminants quadraticIdealCount
    hK hD

/-- **Davenport §6, p. 51**, unconditional, with a fundamental unit `ε`:
`h |log w(ε)| = -(1/2) ∑_{m=1}^{d-1} (d/m) log sin(πm/d)`. -/
@[kb "davenport1980" "Ch 6, p. 51"]
theorem classNumber_mul_log_eq_sum_of_discr_pos_unconditional (hK : finrank ℚ K = 2)
    (hD : 0 < discr K) (ε : (𝓞 K)ˣ) (hε : Subgroup.closure {ε} ⊔ torsion K = ⊤)
    (w : InfinitePlace K) :
    ((classNumber K * |Real.log (w (ε : K))| : ℝ) : ℂ) = -(1 / 2) *
      ∑ m ∈ Ico 1 (discr K).natAbs,
        kroneckerChar (discr K) m * (Real.log (Real.sin (π * m / discr K)) : ℂ) :=
  classNumber_mul_log_eq_sum_of_discr_pos quadraticFieldDiscriminants quadraticIdealCount hK hD ε
    hε w

/-- **Davenport §6, p. 51, (19): Jacobi's class number formula**, unconditional. For a prime
`q ≡ 3 (mod 4)`, `q > 3`, and the quadratic field of discriminant `-q`:
`q h(-q) = -∑_{m=1}^{q-1} m (m/q)`. -/
@[kb "davenport1980" "Ch 6, p. 51, (19)"]
theorem classNumber_eq_jacobi_unconditional {q : ℕ} [Fact q.Prime] (hq : q % 4 = 3) (hq3 : 3 < q)
    (hK : finrank ℚ K = 2) (hDq : discr K = -q) :
    (q : ℤ) * classNumber K = -∑ m ∈ Ico 1 q, (m : ℤ) * legendreSym q m :=
  classNumber_eq_jacobi quadraticFieldDiscriminants quadraticIdealCount hq hq3 hK hDq

theorem LFunction_one_re_eq_residue_unconditional (hK : finrank ℚ K = 2) :
    (LFunction (kroneckerChar (discr K)) 1).re = dedekindZeta_residue K :=
  LFunction_one_re_eq_residue quadraticFieldDiscriminants quadraticIdealCount hK

/-- **Davenport §14, (16)**, unconditional: `L(1, χ) > c q^{-1/2}` for every real primitive
`χ ≠ 1` modulo `q`. -/
@[kb "davenport1980" "Ch 14, p. 96, (16)"]
theorem LFunction_one_re_gt_div_sqrt_unconditional :
    ∃ c : ℝ, 0 < c ∧ ∀ {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}, χ.IsPrimitive →
      χ.IsQuadratic → χ ≠ 1 → c / √(q : ℝ) < (χ.LFunction 1).re :=
  LFunction_one_re_gt_div_sqrt quadraticFieldDiscriminants quadraticIdealCount

/-- **Davenport §14, (18)**, unconditional, for primitive real `χ`:
`β < 1 - c / (q^{1/2} log² q)`. -/
@[kb "davenport1980" "Ch 14, p. 96, (18)"]
theorem real_zero_lt_unconditional :
    ∃ c : ℝ, 0 < c ∧ ∀ {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}, χ.IsPrimitive →
      χ.IsQuadratic → χ ≠ 1 → ∀ β : ℝ, χ.LFunction β = 0 →
        β < 1 - c / (√(q : ℝ) * Real.log q ^ 2) :=
  real_zero_lt quadraticFieldDiscriminants quadraticIdealCount

/-- **Davenport §14, (18)**, unconditional, for every real nonprincipal `χ`. -/
@[kb "davenport1980" "Ch 14, p. 96, (18)"]
theorem real_zero_lt_of_isQuadratic_unconditional :
    ∃ c : ℝ, 0 < c ∧ ∀ {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q},
      χ.IsQuadratic → χ ≠ 1 → ∀ β : ℝ, χ.LFunction β = 0 →
        β < 1 - c / (√(q : ℝ) * Real.log q ^ 2) :=
  real_zero_lt_of_isQuadratic quadraticFieldDiscriminants quadraticIdealCount

/-- **Davenport §21, (2): Siegel's bound for `d < 0`**, unconditional: for every `ε > 0` there is
`C(ε) > 0` with `h(d) > C(ε) |d|^{1/2 - ε}` for every imaginary quadratic field. -/
@[kb "davenport1980" "Ch 21, p. 126, (2)"]
theorem classNumber_gt_of_discr_neg_unconditional {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : Type) [Field K] [NumberField K], finrank ℚ K = 2 → discr K < 0 →
      C * |(discr K : ℝ)| ^ ((1 : ℝ) / 2 - ε) < classNumber K :=
  classNumber_gt_of_discr_neg quadraticFieldDiscriminants quadraticIdealCount hε

/-- **Davenport §21, (3): Siegel's bound for `d > 0`**, unconditional:
`h(d) R > C(ε) d^{1/2 - ε}`. -/
@[kb "davenport1980" "Ch 21, p. 126, (3)"]
theorem classNumber_mul_regulator_gt_of_discr_pos_unconditional {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : Type) [Field K] [NumberField K], finrank ℚ K = 2 → 0 < discr K →
      C * (discr K : ℝ) ^ ((1 : ℝ) / 2 - ε) < classNumber K * regulator K :=
  classNumber_mul_regulator_gt_of_discr_pos quadraticFieldDiscriminants quadraticIdealCount hε

/-- **Davenport §21, (3)**, unconditional, with the fundamental unit `η`:
`h(d) log η > C(ε) d^{1/2 - ε}`. -/
@[kb "davenport1980" "Ch 21, p. 126, (3)"]
theorem classNumber_mul_log_gt_of_discr_pos_unconditional {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : Type) [Field K] [NumberField K], finrank ℚ K = 2 → 0 < discr K →
      ∀ (η : (𝓞 K)ˣ), Subgroup.closure {η} ⊔ torsion K = ⊤ → ∀ w : InfinitePlace K,
        C * (discr K : ℝ) ^ ((1 : ℝ) / 2 - ε) < classNumber K * |Real.log (w (η : K))| :=
  classNumber_mul_log_gt_of_discr_pos quadraticFieldDiscriminants quadraticIdealCount hε

/-- **The class number of an imaginary quadratic field tends to infinity** with `|d|`
(Ireland–Rosen 20.6.1, a corollary of Siegel's bound): for every `B` there is `X` with `h(d) > B`
for every imaginary quadratic field of discriminant `|d| > X`. -/
theorem classNumber_tendsto_atTop_of_discr_neg (B : ℝ) :
    ∃ X : ℝ, ∀ (K : Type) [Field K] [NumberField K], finrank ℚ K = 2 → discr K < 0 →
      X < |(discr K : ℝ)| → B < classNumber K := by
  obtain ⟨C, hC, h⟩ := classNumber_gt_of_discr_neg_unconditional (ε := 1 / 4) (by norm_num)
  refine ⟨max 1 ((max B 0 / C) ^ (4 : ℝ)), fun K _ _ hK hD hX ↦ ?_⟩
  have hX1 : 1 < |(discr K : ℝ)| := lt_of_le_of_lt (le_max_left _ _) hX
  have hpos : 0 < |(discr K : ℝ)| := by linarith
  have hB0 : 0 ≤ max B 0 / C := div_nonneg (le_max_right _ _) hC.le
  have hX2 : (max B 0 / C) ^ (4 : ℝ) < |(discr K : ℝ)| := lt_of_le_of_lt (le_max_right _ _) hX
  have h14 : max B 0 / C < |(discr K : ℝ)| ^ ((1 : ℝ) / 2 - 1 / 4) := by
    have : ((max B 0 / C) ^ (4 : ℝ)) ^ ((1 : ℝ) / 4) < |(discr K : ℝ)| ^ ((1 : ℝ) / 4) :=
      Real.rpow_lt_rpow (by positivity) hX2 (by norm_num)
    rw [← Real.rpow_mul hB0] at this
    norm_num at this ⊢
    exact this
  have := h K hK hD
  calc B ≤ max B 0 := le_max_left _ _
    _ = C * (max B 0 / C) := by field_simp
    _ < C * |(discr K : ℝ)| ^ ((1 : ℝ) / 2 - 1 / 4) := by gcongr
    _ < classNumber K := this

end NTKB.Davenport
