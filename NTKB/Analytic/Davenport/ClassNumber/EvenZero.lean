/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Davenport.ClassNumber.Unconditional
import NTKB.Analytic.Davenport.Forms.RealUnits
import NTKB.Elementary.QuadraticField.Classification

/-!
# Davenport §14, (18): the improvement by a factor `log q` for even characters

Davenport, *Multiplicative Number Theory*, §14, p. 96 (row 14-18). A real zero `β` of `L(s, χ)`,
`χ` a real nonprincipal character modulo `q`, satisfies `β < 1 - c/(q^{1/2} log² q)`
(`real_zero_lt_of_isQuadratic_unconditional`); for even `χ` the bound improves by a factor
`log q`: `β < 1 - c/(q^{1/2} log q)`. Davenport's argument: for even `χ` the class number formula
reads `L(1, χ) = 2 h log ε / √d`, and `log ε ≫ log d`.

* `log_sqrt_sub_one_le_regulator`: for a real quadratic field of discriminant `d`,
  `log(√d - 1) ≤ R`. If `ε = x` and `ε' = y` are the two real embeddings of the fundamental unit
  (`ε = a + bω` in `ℤ[ω]`), then `x - y = b √d` with `b ≠ 0` and `|x y| = 1`, so
  `max(|x|, |y|) + 1 ≥ |x| + |y| ≥ √d`.
* `log_div_six_le_regulator`: `R ≥ (1/6) log d` (from the above for `d ≥ 8`, from `R ≥ log(3/2)`
  for `d < 8`).
* `LFunction_one_re_ge_log_div_sqrt`: `L(1, χ) ≥ (1/3) log q / √q` for every even real primitive
  `χ ≠ χ₀` modulo `q`.
* `real_zero_lt_of_even` (primitive) and `real_zero_lt_of_isQuadratic_of_even` (every even real
  nonprincipal character): `β < 1 - c/(q^{1/2} log q)`, by the mean value theorem with
  `|L'(σ, χ)| ≪ log² q` near `1` (row 14-17), as in `real_zero_lt`.
* `real_zero_lt_book`: row 14-18 as stated by Davenport, both bounds in one theorem.
-/

noncomputable section

open Complex DirichletCharacter Module NumberField NumberField.InfinitePlace NumberField.Units
  QuadraticAlgebra NTKB.QuadraticField
open scoped Real

namespace NTKB.Davenport

section regulator

variable {K : Type} [Field K] [NumberField K]

/-- The two real embeddings of `a + bω` differ by `b √D`. -/
theorem realEmb_sub_realEmb_star {D : ℤ} [Fact (IsFundamentalDiscriminant D)] [Fact (D ≠ 1)]
    (hD : 0 ≤ D) (z : Order D) :
    realEmb hD z - realEmb hD (star z) = z.im * √(D : ℝ) := by
  rw [realEmb_apply, realEmb_star, rootPlus]
  ring

/-- `log(√D - 1) ≤ R` for the real quadratic field `K` of discriminant `D`, given `ℤ[ω] ≅ 𝓞 K`. -/
theorem log_sqrt_sub_one_le_regulator_aux {D : ℤ} [Fact (IsFundamentalDiscriminant D)]
    [Fact (D ≠ 1)] (hK : finrank ℚ K = 2) (e : Order D ≃+* 𝓞 K) (hD : 0 < D)
    (hDK : discr K = D) :
    Real.log (√(D : ℝ) - 1) ≤ regulator K := by
  have hDK' : 0 < discr K := hDK ▸ hD
  obtain ⟨ηK, hηK⟩ := exists_fundamental_unit hK hDK'
  let E : (Order D)ˣ ≃* (𝓞 K)ˣ := Units.mapEquiv e.toMulEquiv
  set η₀ := E.symm ηK
  have hEη : E η₀ = ηK := E.apply_symm_apply ηK
  obtain ⟨w⟩ : Nonempty (InfinitePlace K) := inferInstance
  have hR : regulator K = |Real.log (abs (realEmb hD.le (η₀ : Order D)))| := by
    rw [regulator_eq_abs_log hK hDK' ηK hηK w, ← hEη, ← abs_log_place_eq hD.le e w η₀]; rfl
  have hRpos : 0 < regulator K := regulator_pos K
  set z : Order D := (η₀ : Order D)
  set x := realEmb hD.le z with hx
  set y := realEmb hD.le (star z) with hy
  have hxy : |x| * |y| = 1 := abs_realEmb_mul_abs_realEmb_star hD.le η₀
  have hdiff : x - y = z.im * √(D : ℝ) := realEmb_sub_realEmb_star hD.le z
  have hD2 : (2 : ℝ) ≤ D := by
    have h1 : D ≠ 1 := Fact.out
    exact_mod_cast (show (2 : ℤ) ≤ D by omega)
  have hs1 : 1 < √(D : ℝ) := by
    rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_lt_sqrt (by norm_num) (by linarith)
  have hs0 : 0 < √(D : ℝ) := by linarith
  -- `b ≠ 0`
  have him : z.im ≠ 0 := by
    intro h0
    rw [h0, Int.cast_zero, zero_mul, sub_eq_zero] at hdiff
    rw [← hdiff] at hxy
    have h1 : |x| = 1 := by
      have h2 : 0 ≤ |x| := abs_nonneg x
      nlinarith
    rw [hR, h1, Real.log_one, abs_zero] at hRpos
    exact lt_irrefl _ hRpos
  have him1 : (1 : ℝ) ≤ |(z.im : ℝ)| := by
    rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs him
  have hsum : √(D : ℝ) ≤ |x| + |y| := by
    calc √(D : ℝ) ≤ |(z.im : ℝ)| * √(D : ℝ) := le_mul_of_one_le_left hs0.le him1
      _ = |x - y| := by rw [hdiff, abs_mul, abs_of_pos hs0]
      _ ≤ |x| + |y| := abs_sub _ _
  have hx0 : 0 < |x| := by
    rcases eq_or_lt_of_le (abs_nonneg x) with h | h
    · rw [← h, zero_mul] at hxy; norm_num at hxy
    · exact h
  have hy0 : 0 < |y| := by
    rcases eq_or_lt_of_le (abs_nonneg y) with h | h
    · rw [← h, mul_zero] at hxy; norm_num at hxy
    · exact h
  have hlogy : Real.log |y| = -Real.log |x| := by
    rw [eq_neg_iff_add_eq_zero, ← Real.log_mul hy0.ne' hx0.ne', mul_comm, hxy, Real.log_one]
  have hpos : 0 < √(D : ℝ) - 1 := by linarith
  rw [hR]
  rcases le_or_gt 1 |x| with h1 | h1
  · -- `|y| = 1/|x| ≤ 1`
    have hy1 : |y| ≤ 1 := by nlinarith
    have : √(D : ℝ) - 1 ≤ |x| := by linarith
    exact (Real.log_le_log hpos this).trans (le_abs_self _)
  · have hy1 : 1 < |y| := by nlinarith
    have : √(D : ℝ) - 1 ≤ |y| := by linarith
    calc Real.log (√(D : ℝ) - 1) ≤ Real.log |y| := Real.log_le_log hpos this
      _ = abs (Real.log |x|) := by
        rw [hlogy, abs_of_neg (Real.log_neg hx0 h1)]

/-- **The regulator of a real quadratic field of discriminant `d` is at least `log(√d - 1)`.** -/
theorem log_sqrt_sub_one_le_regulator (hK : finrank ℚ K = 2) (hD : 0 < discr K) :
    Real.log (√(discr K : ℝ) - 1) ≤ regulator K := by
  obtain ⟨e⟩ := nonempty_ringEquiv_order K hK
  obtain ⟨hf, h1, -⟩ := isFundamental_discr K hK
  have : Fact (IsFundamentalDiscriminant (discr K)) := ⟨hf⟩
  have : Fact (discr K ≠ 1) := ⟨h1⟩
  exact log_sqrt_sub_one_le_regulator_aux hK e hD rfl

/-- **The regulator of a real quadratic field of discriminant `d` is at least `(1/6) log d`.** -/
theorem log_div_six_le_regulator (hK : finrank ℚ K = 2) (hD : 0 < discr K) :
    Real.log (discr K : ℝ) / 6 ≤ regulator K := by
  have hd0 : (0 : ℝ) < discr K := by exact_mod_cast hD
  rcases lt_or_ge (discr K : ℝ) 8 with h8 | h8
  · -- `R ≥ log(3/2) ≥ (1/2) log 2 = (1/6) log 8`
    have hR := log_three_halves_le_regulator hK hD
    have h1 : Real.log (discr K : ℝ) ≤ Real.log 8 := Real.log_le_log hd0 h8.le
    have h2 : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
    have h3 : Real.log 2 ≤ 2 * Real.log (3 / 2) := by
      rw [← Real.log_rpow (by norm_num)]
      exact Real.log_le_log (by norm_num) (by norm_num)
    linarith
  · -- `(√d - 1)² ≥ √d` for `√d ≥ √8 > (3 + √5)/2`
    have hR := log_sqrt_sub_one_le_regulator hK hD
    set s := √(discr K : ℝ) with hs
    have hss : s * s = discr K := Real.mul_self_sqrt hd0.le
    have hs0 : 0 ≤ s := Real.sqrt_nonneg _
    have hs28 : 2.8 ≤ s := by nlinarith
    have hpos : 0 < s - 1 := by linarith
    have hsq : s ≤ (s - 1) ^ 2 := by nlinarith
    have hp1 := Real.log_pow (s - 1) 2
    have hp2 := Real.log_pow s 2
    push_cast at hp1 hp2
    have hl1 : Real.log s ≤ 2 * Real.log (s - 1) := by
      rw [← hp1]; exact Real.log_le_log (by linarith) hsq
    have hl2 : Real.log (discr K : ℝ) = 2 * Real.log s := by
      rw [← hp2, sq, hss]
    have hl3 : 0 ≤ Real.log (s - 1) := Real.log_nonneg (by linarith)
    linarith

end regulator

/-- An even Kronecker character `(D/·)` of a fundamental discriminant has `D > 0`. -/
theorem pos_of_kroneckerChar_even {D : ℤ} (hD : IsFundamentalDiscriminant D) [NeZero D.natAbs]
    (h : (kroneckerChar D).Even) : 0 < D := by
  rw [DirichletCharacter.Even, kroneckerChar_neg_one hD] at h
  by_contra hneg
  rw [if_neg hneg] at h
  norm_num at h

/-- **Davenport §14, p. 96**: `L(1, χ) ≥ (1/3) log q / √q` for every even real primitive character
`χ ≠ χ₀` modulo `q` (`L(1, χ) = 2 h R/√q` with `h ≥ 1` and `R ≥ (1/6) log q`). -/
@[kb "davenport1980" "Ch 14, p. 96"]
theorem LFunction_one_re_ge_log_div_sqrt {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hp : χ.IsPrimitive) (hq : χ.IsQuadratic) (h1 : χ ≠ 1) (he : χ.Even) :
    Real.log q / 3 / √(q : ℝ) ≤ (χ.LFunction 1).re := by
  obtain ⟨D, hDf, hD1, hDq, hval⟩ := exists_kroneckerChar_of_isPrimitive hp hq h1
  subst hDq
  have hχ := eq_kroneckerChar_of_forall hval
  subst hχ
  have hDpos := pos_of_kroneckerChar_even hDf he
  obtain ⟨K, _, _, hK, hKD⟩ := quadraticFieldDiscriminants.exists_field D hDf hD1
  subst hKD
  rw [LFunction_one_re_eq_residue_unconditional hK, dedekindZeta_residue_of_discr_pos hK hDpos]
  have hn : ((discr K).natAbs : ℝ) = (discr K : ℝ) := by
    rw [Nat.cast_natAbs, Int.cast_abs, abs_of_pos (by exact_mod_cast hDpos)]
  rw [hn]
  have hR := log_div_six_le_regulator hK hDpos
  have hh : (1 : ℝ) ≤ classNumber K := by exact_mod_cast classNumber_pos K
  have hs : 0 < √(discr K : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hDpos)
  have hl : 0 ≤ Real.log (discr K : ℝ) := Real.log_nonneg (by exact_mod_cast hDpos)
  rw [div_le_div_iff_of_pos_right hs]
  have hR0 : 0 ≤ regulator K := (regulator_pos K).le
  nlinarith

/-- **Davenport §14, p. 96, (18), even characters**: there is `c > 0` such that every real zero
`β` of `L(s, χ)`, `χ` an even real primitive character `≠ χ₀` modulo `q`, satisfies
`β < 1 - c / (q^{1/2} log q)`. -/
@[kb "davenport1980" "Ch 14, p. 96, (18)"]
theorem real_zero_lt_of_even :
    ∃ c : ℝ, 0 < c ∧ ∀ {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}, χ.IsPrimitive →
      χ.IsQuadratic → χ ≠ 1 → χ.Even → ∀ β : ℝ, χ.LFunction β = 0 →
        β < 1 - c / (√(q : ℝ) * Real.log q) := by
  obtain ⟨cd, hcd, hD⟩ := Davenport.norm_deriv_LFunction_near_one_le
  set c := min (1 / 2) (1 / 6 / cd) with hc
  refine ⟨c, by positivity, fun {q} _ {χ} hp hq hχ he β hβ ↦ ?_⟩
  have hq3 : 3 ≤ q := three_le_of_ne_one hχ
  have hq3' : (3 : ℝ) ≤ q := by exact_mod_cast hq3
  have hq0 : (0 : ℝ) < q := by linarith
  have hlog1 : 1 < Real.log q :=
    (by norm_num : (1 : ℝ) < 1.0986122885).trans
      (Real.log_three_gt_d9.trans_le (Real.log_le_log (by norm_num) hq3'))
  have hlog0 : 0 < Real.log q := by linarith
  have hsq1 : 1 ≤ √(q : ℝ) := by
    rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt (by linarith)
  have hsq0 : 0 < √(q : ℝ) := by linarith
  have hβ1 : β < 1 := by
    by_contra h
    push Not at h
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) (by simpa using h) hβ
  have hc12 : c ≤ 1 / 2 := min_le_left _ _
  have hcd' : c ≤ 1 / 6 / cd := min_le_right _ _
  have hden : 0 < √(q : ℝ) * Real.log q := by positivity
  rcases le_or_gt β (1 - 1 / Real.log q) with hcase | hcase
  · -- far from `1`: `c / (√q log q) ≤ c / log q < 1 / log q`
    have h1 : c / (√(q : ℝ) * Real.log q) < 1 / Real.log q := by
      rw [div_lt_div_iff₀ hden hlog0]
      have : Real.log q ≤ √(q : ℝ) * Real.log q := by nlinarith
      nlinarith
    linarith
  · -- near `1`: the mean value theorem with `|L'| ≪ log² q`
    have hmvt : ‖χ.LFunction 1‖ ≤ cd * Real.log q ^ 2 * (1 - β) := by
      have hf : ∀ x ∈ Set.Icc β 1, HasDerivWithinAt (fun x : ℝ ↦ χ.LFunction x)
          (deriv χ.LFunction x) (Set.Icc β 1) x := fun x _ ↦
        (((DirichletCharacter.differentiable_LFunction hχ) x).hasDerivAt.comp_ofReal).hasDerivWithinAt
      have hb : ∀ x ∈ Set.Ico β 1, ‖deriv χ.LFunction x‖ ≤ cd * Real.log q ^ 2 := fun x hx ↦
        hD hχ hq3 x (by linarith [hx.1]) hx.2
      have := norm_image_sub_le_of_norm_deriv_le_segment' hf hb 1 ⟨hβ1.le, le_rfl⟩
      simpa [hβ] using this
    have hre : (χ.LFunction 1).re ≤ ‖χ.LFunction 1‖ := Complex.re_le_norm _
    have hkey : Real.log q / 3 / √(q : ℝ) ≤ cd * Real.log q ^ 2 * (1 - β) :=
      (LFunction_one_re_ge_log_div_sqrt hp hq hχ he).trans (hre.trans hmvt)
    have hkey2 : 1 / 3 / cd / (√(q : ℝ) * Real.log q) ≤ 1 - β := by
      rw [div_le_iff₀ hsq0] at hkey
      rw [div_div, div_div, div_le_iff₀ (by positivity)]
      have h3 : Real.log q * 1 ≤
          Real.log q * ((1 - β) * (3 * (cd * (√(q : ℝ) * Real.log q)))) := by nlinarith
      exact le_of_mul_le_mul_left h3 hlog0
    have hlt : c / (√(q : ℝ) * Real.log q) < 1 / 3 / cd / (√(q : ℝ) * Real.log q) := by
      gcongr
      calc c ≤ 1 / 6 / cd := hcd'
        _ < 1 / 3 / cd := by gcongr; norm_num
    linarith

/-- The primitive character inducing an even character is even. -/
theorem even_primitiveCharacter {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (h : χ.Even) :
    χ.primitiveCharacter.Even := by
  have e := changeLevel_eq_cast_of_dvd' χ.primitiveCharacter χ.conductor_dvd_level
    (a := -1) isCoprime_one_left.neg_left
  rw [changeLevel_primitiveCharacter] at e
  simp only [Int.cast_neg, Int.cast_one] at e
  unfold DirichletCharacter.Even at h ⊢
  rw [← e]; exact h

/-- **Davenport §14, p. 96, (18), every even real nonprincipal character**: there is `c > 0` such
that every real zero `β` of `L(s, χ)`, `χ` an even real character `≠ χ₀` modulo `q`, satisfies
`β < 1 - c / (q^{1/2} log q)`. The zeros in `(0, 1)` are those of the primitive character inducing
`χ`, which is even, of modulus `q* ≤ q`. -/
@[kb "davenport1980" "Ch 14, p. 96, (18)"]
theorem real_zero_lt_of_isQuadratic_of_even :
    ∃ c : ℝ, 0 < c ∧ ∀ {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q},
      χ.IsQuadratic → χ ≠ 1 → χ.Even → ∀ β : ℝ, χ.LFunction β = 0 →
        β < 1 - c / (√(q : ℝ) * Real.log q) := by
  obtain ⟨c, hc, h⟩ := real_zero_lt_of_even
  refine ⟨min c (1 / 2), by positivity, fun {q} _ {χ} hq hχ he β hβ ↦ ?_⟩
  have hq3 : (3 : ℝ) ≤ q := by exact_mod_cast three_le_of_ne_one hχ
  have hlog1 : 1 < Real.log q :=
    (by norm_num : (1 : ℝ) < 1.0986122885).trans
      (Real.log_three_gt_d9.trans_le (Real.log_le_log (by norm_num) hq3))
  have hsq1 : 1 ≤ √(q : ℝ) := by
    rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt (by linarith)
  have hden1 : 1 ≤ √(q : ℝ) * Real.log q := by nlinarith
  have hmin : min c (1 / 2) ≤ c := min_le_left _ _
  have hmin2 : min c (1 / 2) ≤ 1 / 2 := min_le_right _ _
  rcases le_or_gt β 0 with h0 | h0
  · have : min c (1 / 2) / (√(q : ℝ) * Real.log q) ≤ 1 / 2 :=
      (div_le_self (by positivity) hden1).trans hmin2
    linarith
  have : NeZero χ.conductor := ⟨DirichletCharacter.conductor_ne_zero χ⟩
  have hz := NTKB.LFunction_primitiveCharacter_eq_zero hχ hβ (by simpa using h0)
  have hχ' := NTKB.primitiveCharacter_ne_one hχ
  have hb := h (DirichletCharacter.primitiveCharacter_isPrimitive χ)
    (MulChar.isQuadratic_iff_sq_eq_one.mpr
      (NTKB.primitiveCharacter_sq_eq_one (MulChar.isQuadratic_iff_sq_eq_one.mp hq))) hχ'
    (even_primitiveCharacter he) β hz
  have hd3 : (3 : ℝ) ≤ χ.conductor := by exact_mod_cast three_le_of_ne_one hχ'
  have hdq : (χ.conductor : ℝ) ≤ q := by
    exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) χ.conductor_dvd_level
  have hld : 0 < Real.log χ.conductor := Real.log_pos (by linarith)
  have hmono : √(χ.conductor : ℝ) * Real.log χ.conductor ≤ √(q : ℝ) * Real.log q := by
    gcongr
  have hdpos : 0 < √(χ.conductor : ℝ) * Real.log χ.conductor := by positivity
  have : min c (1 / 2) / (√(q : ℝ) * Real.log q) ≤
      c / (√(χ.conductor : ℝ) * Real.log χ.conductor) :=
    div_le_div₀ hc.le hmin hdpos hmono
  linarith

/-- **Davenport §14, p. 96, (18) (row 14-18), as stated**: there is `c > 0` such that every real
zero `β` of `L(s, χ)`, `χ` a real nonprincipal character modulo `q`, satisfies
`β < 1 - c/(q^{1/2} log² q)`, and `β < 1 - c/(q^{1/2} log q)` if `χ` is even. -/
@[kb "davenport1980" "Ch 14, p. 96, (18)"]
theorem real_zero_lt_book :
    ∃ c : ℝ, 0 < c ∧ ∀ {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q},
      χ.IsQuadratic → χ ≠ 1 → ∀ β : ℝ, χ.LFunction β = 0 →
        β < 1 - c / (√(q : ℝ) * Real.log q ^ 2) ∧
          (χ.Even → β < 1 - c / (√(q : ℝ) * Real.log q)) := by
  obtain ⟨c₁, hc₁, h₁⟩ := real_zero_lt_of_isQuadratic_unconditional
  obtain ⟨c₂, hc₂, h₂⟩ := real_zero_lt_of_isQuadratic_of_even
  refine ⟨min c₁ c₂, lt_min hc₁ hc₂, fun {q} _ {χ} hq hχ β hβ ↦ ⟨?_, fun he ↦ ?_⟩⟩
  · have hq3 : (3 : ℝ) ≤ q := by exact_mod_cast three_le_of_ne_one hχ
    have : 0 < √(q : ℝ) * Real.log q ^ 2 := by
      have := Real.log_pos (by linarith : (1 : ℝ) < q); positivity
    have := h₁ hq hχ β hβ
    have : min c₁ c₂ / (√(q : ℝ) * Real.log q ^ 2) ≤ c₁ / (√(q : ℝ) * Real.log q ^ 2) := by
      gcongr; exact min_le_left _ _
    linarith
  · have hq3 : (3 : ℝ) ≤ q := by exact_mod_cast three_le_of_ne_one hχ
    have : 0 < √(q : ℝ) * Real.log q := by
      have := Real.log_pos (by linarith : (1 : ℝ) < q); positivity
    have := h₂ hq hχ he β hβ
    have : min c₁ c₂ / (√(q : ℝ) * Real.log q) ≤ c₂ / (√(q : ℝ) * Real.log q) := by
      gcongr; exact min_le_right _ _
    linarith

end NTKB.Davenport
