/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Davenport.ClassNumber.Finite
import NTKB.Analytic.Davenport.ClassNumber.RealCharacters
import NTKB.Analytic.Davenport.Siegel.Siegel

/-!
# Davenport, Chapters 14 and 21: lower bounds from the class number formula

Davenport, *Multiplicative Number Theory*, §14, p. 96 and §21, p. 126. Conditional on the two
named statements of `NTKB.Davenport.ClassNumber.Formula`:

* `LFunction_one_re_gt_div_sqrt` (§14, (16)): `L(1, χ) > c q^{-1/2}` for every real primitive
  character `χ ≠ χ₀` modulo `q`: by Chapter 5 (`exists_kroneckerChar_of_isPrimitive`)
  `χ = (d/·)` with `|d| = q`; with `h ≥ 1`, `w ≤ 6` and `R ≥ log (3/2)` the class number formulas
  give `L(1, χ) ≥ (π/3) |d|^{-1/2}` for `d < 0` and `L(1, χ) ≥ 2 log(3/2) d^{-1/2}` for `d > 0`;
* `real_zero_lt` (§14, (18)): a real zero `β` of `L(s, χ)`, `χ` real primitive, satisfies
  `β < 1 - c / (q^{1/2} log² q)`: the mean value theorem with `|L'(σ)| ≪ log² q` near `1`;
* `classNumber_gt_of_discr_neg` (§21, (2), **Siegel**): `h(d) > C(ε) |d|^{1/2 - ε}` for `d < 0`;
* `classNumber_mul_regulator_gt_of_discr_pos` and `classNumber_mul_log_gt_of_discr_pos`
  (§21, (3), **Siegel**): `h(d) log ε > C(ε) d^{1/2 - ε}` for `d > 0`;
  both from Siegel's theorem `siegel` (`L(1, χ) > C(ε) q^{-ε}`).
-/

noncomputable section

open Complex DirichletCharacter Module NumberField NumberField.InfinitePlace NumberField.Units
  Finset Set
open scoped Real

namespace NTKB.Davenport

variable {K : Type} [Field K] [NumberField K]

/-- `L(1, χ_d)` is real and equals the residue of `ζ_K`. -/
theorem LFunction_one_re_eq_residue (hF : QuadraticFieldDiscriminants) (hI : QuadraticIdealCount)
    (hK : finrank ℚ K = 2) :
    (LFunction (kroneckerChar (discr K)) 1).re = dedekindZeta_residue K := by
  rw [LFunction_one_eq_residue hF hI hK, ofReal_re]

/-- The residue of `ζ_K` is at least `min (π/3) (2 log (3/2)) / √|d|`: `h ≥ 1`, `w ≤ 6` for
`d < 0`, `R ≥ log (3/2)` for `d > 0`. -/
theorem residue_ge (hK : finrank ℚ K = 2) :
    min (π / 3) (2 * Real.log (3 / 2)) / √|(discr K : ℝ)| ≤ dedekindZeta_residue K := by
  have hs : 0 < √|(discr K : ℝ)| :=
    Real.sqrt_pos.mpr (abs_pos.mpr (Int.cast_ne_zero.mpr (discr_ne_zero K)))
  have hh : (1 : ℝ) ≤ classNumber K := by exact_mod_cast classNumber_pos K
  rcases lt_or_gt_of_ne (discr_ne_zero K) with hD | hD
  · rw [dedekindZeta_residue_of_discr_neg hK hD]
    have hw6 : (torsionOrder K : ℝ) ≤ 6 := by exact_mod_cast torsionOrder_le_six hK
    have hw0 : (0 : ℝ) < torsionOrder K := by exact_mod_cast torsionOrder_pos K
    calc min (π / 3) (2 * Real.log (3 / 2)) / √|(discr K : ℝ)|
        ≤ π / 3 / √|(discr K : ℝ)| := by gcongr; exact min_le_left _ _
      _ ≤ 2 * π * classNumber K / (torsionOrder K * √|(discr K : ℝ)|) := by
        rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
        have h1 : π * (torsionOrder K : ℝ) ≤ π * 6 := by gcongr
        have h2 : 2 * π ≤ 2 * π * classNumber K := by nlinarith [Real.pi_pos]
        have h3 : π / 3 * (torsionOrder K * √|(discr K : ℝ)|) ≤ 2 * π * √|(discr K : ℝ)| := by
          nlinarith
        nlinarith
  · rw [dedekindZeta_residue_of_discr_pos hK hD, abs_of_pos (by exact_mod_cast hD : (0 : ℝ) < _)]
    have hs' : 0 < √(discr K : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hD)
    have hR := log_three_halves_le_regulator hK hD
    have hl : 0 < Real.log (3 / 2) := Real.log_pos (by norm_num)
    calc min (π / 3) (2 * Real.log (3 / 2)) / √(discr K : ℝ)
        ≤ 2 * Real.log (3 / 2) / √(discr K : ℝ) := by gcongr; exact min_le_right _ _
      _ ≤ 2 * classNumber K * regulator K / √(discr K : ℝ) := by
        gcongr
        nlinarith

/-- A real primitive character equal to `(d/·)` on the naturals is `(d/·)`. -/
theorem eq_kroneckerChar_of_forall {D : ℤ} [NeZero D.natAbs] {χ : DirichletCharacter ℂ D.natAbs}
    (h : ∀ m : ℕ, χ m = kroneckerChar D m) : χ = kroneckerChar D := by
  refine MulChar.ext fun u ↦ ?_
  have := h (u : ZMod D.natAbs).val
  rwa [ZMod.natCast_zmod_val] at this

/-- **Davenport §14, (16).** There is `c > 0` with `L(1, χ) > c q^{-1/2}` for every real
primitive character `χ ≠ χ₀` modulo `q`. -/
@[kb "davenport1980" "Ch 14, p. 96, (16)"]
theorem LFunction_one_re_gt_div_sqrt (hF : QuadraticFieldDiscriminants)
    (hI : QuadraticIdealCount) :
    ∃ c : ℝ, 0 < c ∧ ∀ {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}, χ.IsPrimitive →
      χ.IsQuadratic → χ ≠ 1 → c / √(q : ℝ) < (χ.LFunction 1).re := by
  set m := min (π / 3) (2 * Real.log (3 / 2))
  have hm : 0 < m := lt_min (by positivity) (by have := Real.log_pos (by norm_num : (1:ℝ) < 3 / 2); linarith)
  refine ⟨m / 2, by positivity, fun {q} _ {χ} hp hq h1 ↦ ?_⟩
  obtain ⟨D, hDf, hD1, hDq, hval⟩ := exists_kroneckerChar_of_isPrimitive hp hq h1
  subst hDq
  have hχ := eq_kroneckerChar_of_forall hval
  subst hχ
  obtain ⟨K, _, _, hK, hKD⟩ := hF.exists_field D hDf hD1
  subst hKD
  rw [LFunction_one_re_eq_residue hF hI hK]
  have hr := residue_ge hK
  rw [abs_discr_eq_natAbs] at hr
  have hs : 0 < √((discr K).natAbs : ℝ) :=
    Real.sqrt_pos.mpr (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne _))
  refine lt_of_lt_of_le ?_ hr
  gcongr
  linarith

/-- **Davenport §14, (18).** There is `c > 0` such that every real zero `β` of `L(s, χ)`, `χ` a
real primitive character `≠ χ₀` modulo `q`, satisfies `β < 1 - c / (q^{1/2} log² q)`. -/
@[kb "davenport1980" "Ch 14, p. 96, (18)"]
theorem real_zero_lt (hF : QuadraticFieldDiscriminants) (hI : QuadraticIdealCount) :
    ∃ c : ℝ, 0 < c ∧ ∀ {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}, χ.IsPrimitive →
      χ.IsQuadratic → χ ≠ 1 → ∀ β : ℝ, χ.LFunction β = 0 →
        β < 1 - c / (√(q : ℝ) * Real.log q ^ 2) := by
  obtain ⟨c₀, hc₀, hL⟩ := LFunction_one_re_gt_div_sqrt hF hI
  obtain ⟨cd, hcd, hD⟩ := Davenport.norm_deriv_LFunction_near_one_le
  set c := min (1 / 2) (c₀ / cd) with hc
  refine ⟨c, by positivity, fun {q} _ {χ} hp hq hχ β hβ ↦ ?_⟩
  have hq3 : 3 ≤ q := three_le_of_ne_one hχ
  have hq3' : (3 : ℝ) ≤ q := by exact_mod_cast hq3
  have hq0 : (0 : ℝ) < q := by linarith
  have hlog1 : 1 < Real.log q :=
    (by norm_num : (1 : ℝ) < 1.0986122885).trans
      (Real.log_three_gt_d9.trans_le (Real.log_le_log (by norm_num) hq3'))
  have hlog0 : 0 < Real.log q := by linarith
  have hsq1 : 1 ≤ √(q : ℝ) := by
    rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt (by linarith)
  have hβ1 : β < 1 := by
    by_contra h
    push Not at h
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) (by simpa using h) hβ
  have hc12 : c ≤ 1 / 2 := min_le_left _ _
  have hcd' : c ≤ c₀ / cd := min_le_right _ _
  have hden : 0 < √(q : ℝ) * Real.log q ^ 2 := by positivity
  rcases le_or_gt β (1 - 1 / Real.log q) with hcase | hcase
  · -- far from `1`: `c / (√q log² q) ≤ c / log q < 1 / log q`
    have h1 : c / (√(q : ℝ) * Real.log q ^ 2) < 1 / Real.log q := by
      rw [div_lt_div_iff₀ hden hlog0]
      have : Real.log q ≤ √(q : ℝ) * Real.log q ^ 2 := by nlinarith
      nlinarith
    linarith
  · -- near `1`: the mean value theorem with `|L'| ≪ log² q`
    have hmvt : ‖χ.LFunction 1‖ ≤ cd * Real.log q ^ 2 * (1 - β) := by
      have hf : ∀ x ∈ Icc β 1, HasDerivWithinAt (fun x : ℝ ↦ χ.LFunction x)
          (deriv χ.LFunction x) (Icc β 1) x := fun x _ ↦
        (((DirichletCharacter.differentiable_LFunction hχ) x).hasDerivAt.comp_ofReal).hasDerivWithinAt
      have hb : ∀ x ∈ Ico β 1, ‖deriv χ.LFunction x‖ ≤ cd * Real.log q ^ 2 := fun x hx ↦
        hD hχ hq3 x (by linarith [hx.1]) hx.2
      have := norm_image_sub_le_of_norm_deriv_le_segment' hf hb 1 ⟨hβ1.le, le_rfl⟩
      simpa [hβ] using this
    have hre : (χ.LFunction 1).re ≤ ‖χ.LFunction 1‖ := Complex.re_le_norm _
    have hkey : c₀ / √(q : ℝ) < cd * Real.log q ^ 2 * (1 - β) :=
      (hL hp hq hχ).trans_le (hre.trans hmvt)
    have hkey2 : c₀ / cd / (√(q : ℝ) * Real.log q ^ 2) < 1 - β := by
      have hsq0 : 0 < √(q : ℝ) := by positivity
      rw [div_lt_iff₀ hsq0] at hkey
      rw [div_div, div_lt_iff₀ (by positivity)]
      nlinarith
    have : c / (√(q : ℝ) * Real.log q ^ 2) ≤ c₀ / cd / (√(q : ℝ) * Real.log q ^ 2) := by
      gcongr
    linarith

/-- **Davenport §14, (18), for every real nonprincipal character**: there is `c > 0` such that
every real zero `β` of `L(s, χ)`, `χ` a real character `≠ χ₀` modulo `q`, satisfies
`β < 1 - c / (q^{1/2} log² q)`. The zeros in `(0, 1)` are those of the primitive character
inducing `χ`, whose modulus `q* ≤ q` has `√q* log² q* ≤ √q log² q`. -/
@[kb "davenport1980" "Ch 14, p. 96, (18)"]
theorem real_zero_lt_of_isQuadratic (hF : QuadraticFieldDiscriminants)
    (hI : QuadraticIdealCount) :
    ∃ c : ℝ, 0 < c ∧ ∀ {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q},
      χ.IsQuadratic → χ ≠ 1 → ∀ β : ℝ, χ.LFunction β = 0 →
        β < 1 - c / (√(q : ℝ) * Real.log q ^ 2) := by
  obtain ⟨c, hc, h⟩ := real_zero_lt hF hI
  refine ⟨min c (1 / 2), by positivity, fun {q} _ {χ} hq hχ β hβ ↦ ?_⟩
  have hq3 : (3 : ℝ) ≤ q := by exact_mod_cast three_le_of_ne_one hχ
  have hlog1 : 1 < Real.log q :=
    (by norm_num : (1 : ℝ) < 1.0986122885).trans
      (Real.log_three_gt_d9.trans_le (Real.log_le_log (by norm_num) hq3))
  have hsq1 : 1 ≤ √(q : ℝ) := by
    rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt (by linarith)
  have hden1 : 1 ≤ √(q : ℝ) * Real.log q ^ 2 := by nlinarith
  have hmin : min c (1 / 2) ≤ c := min_le_left _ _
  have hmin2 : min c (1 / 2) ≤ 1 / 2 := min_le_right _ _
  rcases le_or_gt β 0 with h0 | h0
  · have : min c (1 / 2) / (√(q : ℝ) * Real.log q ^ 2) ≤ 1 / 2 :=
      (div_le_self (by positivity) hden1).trans hmin2
    linarith
  have : NeZero χ.conductor := ⟨DirichletCharacter.conductor_ne_zero χ⟩
  have hz := NTKB.LFunction_primitiveCharacter_eq_zero hχ hβ (by simpa using h0)
  have hχ' := NTKB.primitiveCharacter_ne_one hχ
  have hb := h (DirichletCharacter.primitiveCharacter_isPrimitive χ)
    (MulChar.isQuadratic_iff_sq_eq_one.mpr
      (NTKB.primitiveCharacter_sq_eq_one (MulChar.isQuadratic_iff_sq_eq_one.mp hq))) hχ' β hz
  have hd3 : (3 : ℝ) ≤ χ.conductor := by exact_mod_cast three_le_of_ne_one hχ'
  have hdq : (χ.conductor : ℝ) ≤ q := by
    exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) χ.conductor_dvd_level
  have hld : 0 < Real.log χ.conductor := Real.log_pos (by linarith)
  have hmono : √(χ.conductor : ℝ) * Real.log χ.conductor ^ 2 ≤
      √(q : ℝ) * Real.log q ^ 2 := by
    gcongr
  have hdpos : 0 < √(χ.conductor : ℝ) * Real.log χ.conductor ^ 2 := by positivity
  have : min c (1 / 2) / (√(q : ℝ) * Real.log q ^ 2) ≤
      c / (√(χ.conductor : ℝ) * Real.log χ.conductor ^ 2) :=
    div_le_div₀ hc.le hmin hdpos hmono
  linarith

/-- `|d|^{1/2 - ε} = √|d| |d|^{-ε}`. -/
theorem rpow_half_sub_eq {a ε : ℝ} (ha : 0 < a) : a ^ ((1 : ℝ) / 2 - ε) = √a * a ^ (-ε) := by
  rw [sub_eq_add_neg, Real.rpow_add ha, Real.sqrt_eq_rpow]

/-- **Davenport §21, (2): Siegel's lower bound for the class number, `d < 0`.** For every
`ε > 0` there is `C(ε) > 0` with `h(d) > C(ε) |d|^{1/2 - ε}` for every imaginary quadratic field
of discriminant `d`. -/
@[kb "davenport1980" "Ch 21, p. 126, (2)"]
theorem classNumber_gt_of_discr_neg (hF : QuadraticFieldDiscriminants) (hI : QuadraticIdealCount)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : Type) [Field K] [NumberField K], finrank ℚ K = 2 → discr K < 0 →
      C * |(discr K : ℝ)| ^ ((1 : ℝ) / 2 - ε) < classNumber K := by
  obtain ⟨C₁, hC₁, hS⟩ := siegel hε
  refine ⟨C₁ / π, by positivity, fun K _ _ hK hD ↦ ?_⟩
  have hfund := hF.isFundamental K hK
  have hL := hS (kroneckerChar_isPrimitive hfund) (kroneckerChar_isQuadratic hfund)
    (kroneckerChar_discr_ne_one hF hK)
  rw [LFunction_one_re_eq_residue hF hI hK, dedekindZeta_residue_of_discr_neg hK hD,
    ← abs_discr_eq_natAbs] at hL
  set a := |(discr K : ℝ)|
  have ha : 0 < a := abs_pos.mpr (Int.cast_ne_zero.mpr (discr_ne_zero K))
  have hs : 0 < √a := Real.sqrt_pos.mpr ha
  have hae : 0 < a ^ (-ε) := Real.rpow_pos_of_pos ha _
  have hw2 : (2 : ℝ) ≤ torsionOrder K := by
    rcases torsionOrder_eq_two_or_four_or_six hK with h | h | h <;> rw [h] <;> norm_num
  rw [lt_div_iff₀ (by positivity)] at hL
  rw [rpow_half_sub_eq ha, div_mul_eq_mul_div, div_lt_iff₀ Real.pi_pos]
  have h1 : C₁ * a ^ (-ε) * √a * 2 ≤ C₁ * a ^ (-ε) * (torsionOrder K * √a) := by
    have := mul_le_mul_of_nonneg_left hw2 (by positivity : (0 : ℝ) ≤ C₁ * a ^ (-ε) * √a)
    nlinarith
  nlinarith

/-- **Davenport §21, (3): Siegel's lower bound, `d > 0`, with the regulator.** For every `ε > 0`
there is `C(ε) > 0` with `h(d) R > C(ε) d^{1/2 - ε}` for every real quadratic field. -/
@[kb "davenport1980" "Ch 21, p. 126, (3)"]
theorem classNumber_mul_regulator_gt_of_discr_pos (hF : QuadraticFieldDiscriminants)
    (hI : QuadraticIdealCount) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : Type) [Field K] [NumberField K], finrank ℚ K = 2 → 0 < discr K →
      C * (discr K : ℝ) ^ ((1 : ℝ) / 2 - ε) < classNumber K * regulator K := by
  obtain ⟨C₁, hC₁, hS⟩ := siegel hε
  refine ⟨C₁ / 2, by positivity, fun K _ _ hK hD ↦ ?_⟩
  have hfund := hF.isFundamental K hK
  have hL := hS (kroneckerChar_isPrimitive hfund) (kroneckerChar_isQuadratic hfund)
    (kroneckerChar_discr_ne_one hF hK)
  have hn : ((discr K).natAbs : ℝ) = (discr K : ℝ) := by
    rw [Nat.cast_natAbs, Int.cast_abs, abs_of_pos (by exact_mod_cast hD)]
  rw [LFunction_one_re_eq_residue hF hI hK, dedekindZeta_residue_of_discr_pos hK hD, hn] at hL
  have ha : 0 < (discr K : ℝ) := Int.cast_pos.mpr hD
  set a := (discr K : ℝ)
  have hs : 0 < √a := Real.sqrt_pos.mpr ha
  have hae : 0 < a ^ (-ε) := Real.rpow_pos_of_pos ha _
  rw [lt_div_iff₀ hs] at hL
  rw [rpow_half_sub_eq ha]
  nlinarith

/-- **Davenport §21, (3), with the fundamental unit**: `h(d) log ε > C(ε) d^{1/2 - ε}` for every
real quadratic field, `ε` a fundamental unit, `log ε = |log w(ε)|` at any infinite place `w`. -/
@[kb "davenport1980" "Ch 21, p. 126, (3)"]
theorem classNumber_mul_log_gt_of_discr_pos (hF : QuadraticFieldDiscriminants)
    (hI : QuadraticIdealCount) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : Type) [Field K] [NumberField K], finrank ℚ K = 2 → 0 < discr K →
      ∀ (η : (𝓞 K)ˣ), Subgroup.closure {η} ⊔ torsion K = ⊤ → ∀ w : InfinitePlace K,
        C * (discr K : ℝ) ^ ((1 : ℝ) / 2 - ε) < classNumber K * |Real.log (w (η : K))| := by
  obtain ⟨C, hC, h⟩ := classNumber_mul_regulator_gt_of_discr_pos hF hI hε
  exact ⟨C, hC, fun K _ _ hK hD η hη w ↦ regulator_eq_abs_log hK hD η hη w ▸ h K hK hD⟩

end NTKB.Davenport
