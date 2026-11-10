/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Davenport.Zeros.LZeroFreeTheorem

/-!
# Landau's theorem on real zeros; Page's theorem

**Davenport, Ch. 14, pp. 93-95.**

* (row 14-12, Landau) If `χ₁`, `χ₂` are distinct real primitive characters mod `q₁`, `q₂` with
  real zeros `β₁`, `β₂`, then `min(β₁, β₂) ≤ 1 - c/log(q₁ q₂)` (`c = 1/400`). The proof uses
  `χ₁ χ₂` (a nonprincipal character mod `q₁ q₂`) and
  `-ζ'/ζ - L'/L(·, χ₁) - L'/L(·, χ₂) - L'/L(·, χ₁χ₂) = ∑ Λ(n)(1 + χ₁(n))(1 + χ₂(n)) n^{-σ} ≥ 0`.
* (row 14-13) at most one real nonprincipal `χ` mod `q` has a real zero `β > 1 - c/log q`.
* (row 14-14) if real primitive `χ`, `χ'` mod `q ≤ q'` have real zeros `> 1 - c/log q`, resp.
  `> 1 - c/log q'`, then `q' > q²`.
* (row 14-15, Page) for `z ≥ 3`, at most one real primitive character to a modulus `q ≤ z` has a
  real zero `β > 1 - c/log z`.

"Distinct" for primitive characters of possibly different moduli is expressed as: they induce
different characters modulo `q₁ q₂` (`Davenport.landau_hne_of_ne_level`,
`Davenport.landau_hne_of_ne` show that this holds for different moduli, resp. different
characters to the same modulus).
-/

open Filter Topology Complex Set DirichletCharacter LSeries
open scoped Real LSeries.notation ArithmeticFunction.vonMangoldt

namespace NTKB

/-- The values of a real character (`χ² = χ₀`) are `0` or `±1`; in particular they are real. -/
lemma real_char_im_eq_zero {q : ℕ} {χ : DirichletCharacter ℂ q} (hreal : χ ^ 2 = 1) (n : ℕ) :
    (χ n).im = 0 ∧ -1 ≤ (χ n).re := by
  by_cases hu : IsUnit (n : ZMod q)
  · have h : χ n * χ n = 1 := by
      rw [← sq, ← MulChar.pow_apply' χ two_ne_zero, hreal, MulChar.one_apply hu]
    rcases mul_self_eq_one_iff.mp h with h1 | h1 <;> rw [h1] <;> norm_num
  · rw [MulChar.map_nonunit _ hu]; simp

/-- The product of two characters lifted to the modulus `q₁ q₂`, evaluated at `n`. -/
lemma changeLevel_mul_changeLevel_natCast {q₁ q₂ : ℕ} (χ₁ : DirichletCharacter ℂ q₁)
    (χ₂ : DirichletCharacter ℂ q₂) (n : ℕ) :
    (changeLevel (dvd_mul_right q₁ q₂) χ₁ * changeLevel (dvd_mul_left q₂ q₁) χ₂) (n : ZMod (q₁ * q₂)) =
      χ₁ n * χ₂ n := by
  rw [MulChar.mul_apply]
  by_cases hc : n.Coprime (q₁ * q₂)
  · have hcz : IsCoprime (n : ℤ) ((q₁ * q₂ : ℕ) : ℤ) := Nat.isCoprime_iff_coprime.mpr hc
    have h1 := changeLevel_eq_cast_of_dvd' χ₁ (dvd_mul_right q₁ q₂) hcz
    have h2 := changeLevel_eq_cast_of_dvd' χ₂ (dvd_mul_left q₂ q₁) hcz
    simp only [Int.cast_natCast] at h1 h2
    rw [h1, h2]
  · have hu : ¬ IsUnit (n : ZMod (q₁ * q₂)) := by rwa [ZMod.isUnit_iff_coprime]
    rw [MulChar.map_nonunit _ hu, zero_mul]
    rw [Nat.coprime_mul_iff_right, not_and_or] at hc
    rcases hc with hc | hc
    · rw [MulChar.map_nonunit χ₁ (by rwa [ZMod.isUnit_iff_coprime]), zero_mul]
    · rw [MulChar.map_nonunit χ₂ (by rwa [ZMod.isUnit_iff_coprime]), mul_zero]

/-- **Davenport, Ch. 14, p. 94**: for real characters `χ₁`, `χ₂` and `σ > 1`,
`-ζ'/ζ(σ) - L'/L(σ, χ₁) - L'/L(σ, χ₂) - L'/L(σ, χ₁χ₂) ≥ 0`
(the Dirichlet series has coefficients `Λ(n)(1 + χ₁(n))(1 + χ₂(n)) ≥ 0`). -/
@[kb "davenport1980" "Ch 14, p. 94"]
theorem Davenport.landau_positivity {q₁ q₂ : ℕ} [NeZero q₁] [NeZero q₂]
    {χ₁ : DirichletCharacter ℂ q₁} {χ₂ : DirichletCharacter ℂ q₂} (hr₁ : χ₁ ^ 2 = 1)
    (hr₂ : χ₂ ^ 2 = 1) {σ : ℝ} (hσ : 1 < σ) :
    0 ≤ -(deriv riemannZeta σ / riemannZeta σ).re - (deriv (LFunction χ₁) σ / LFunction χ₁ σ).re -
      (deriv (LFunction χ₂) σ / LFunction χ₂ σ).re -
      (deriv (LFunction (changeLevel (dvd_mul_right q₁ q₂) χ₁ *
          changeLevel (dvd_mul_left q₂ q₁) χ₂)) σ /
        LFunction (changeLevel (dvd_mul_right q₁ q₂) χ₁ *
          changeLevel (dvd_mul_left q₂ q₁) χ₂) σ).re := by
  set ψ := changeLevel (dvd_mul_right q₁ q₂) χ₁ * changeLevel (dvd_mul_left q₂ q₁) χ₂
  have h1 : 1 < (σ : ℂ).re := by simpa using hσ
  have e0 := neg_logDeriv_LFunction_eq_LSeries (1 : DirichletCharacter ℂ 1) h1
  rw [LFunction_modOne_eq] at e0
  have e1 := neg_logDeriv_LFunction_eq_LSeries χ₁ h1
  have e2 := neg_logDeriv_LFunction_eq_LSeries χ₂ h1
  have e3 := neg_logDeriv_LFunction_eq_LSeries ψ h1
  have s0 := Complex.reCLM.hasSum (DirichletCharacter.LSeriesSummable_twist_vonMangoldt
    (1 : DirichletCharacter ℂ 1) h1).LSeriesHasSum
  have s1 := Complex.reCLM.hasSum (DirichletCharacter.LSeriesSummable_twist_vonMangoldt
    χ₁ h1).LSeriesHasSum
  have s2 := Complex.reCLM.hasSum (DirichletCharacter.LSeriesSummable_twist_vonMangoldt
    χ₂ h1).LSeriesHasSum
  have s3 := Complex.reCLM.hasSum (DirichletCharacter.LSeriesSummable_twist_vonMangoldt
    ψ h1).LSeriesHasSum
  have hsum := ((s0.add s1).add s2).add s3
  have hnn := hsum.nonneg fun n ↦ by
    simp only [Complex.reCLM_apply]
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    have t0 := term_twist_vonMangoldt_eq (1 : DirichletCharacter ℂ 1) σ 0 hn
    have t1 := term_twist_vonMangoldt_eq χ₁ σ 0 hn
    have t2 := term_twist_vonMangoldt_eq χ₂ σ 0 hn
    have t3 := term_twist_vonMangoldt_eq ψ σ 0 hn
    simp only [Complex.ofReal_zero, zero_mul, add_zero, neg_zero, Complex.exp_zero,
      mul_one] at t0 t1 t2 t3
    rw [t0, t1, t2, t3, MulChar.one_apply (isUnit_of_subsingleton _),
      changeLevel_mul_changeLevel_natCast]
    set c : ℝ := Λ n * (n : ℝ) ^ (-σ)
    have hc : 0 ≤ c := mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
      (Real.rpow_nonneg n.cast_nonneg _)
    obtain ⟨i1, r1⟩ := real_char_im_eq_zero hr₁ n
    obtain ⟨i2, r2⟩ := real_char_im_eq_zero hr₂ n
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
      sub_zero, one_re, i1, i2]
    have : 0 ≤ (1 + (χ₁ n).re) * (1 + (χ₂ n).re) := mul_nonneg (by linarith) (by linarith)
    nlinarith
  simp only [Complex.reCLM_apply] at hnn
  rw [← e0, ← e1, ← e2, ← e3] at hnn
  simp only [neg_div, Complex.neg_re] at hnn
  linarith

/-- The term of a real zero: for primitive `χ` mod `q > 1`, a real zero `0 < β` and
`1 < σ ≤ 2`, `-Re L'/L(σ, χ) ≤ 6 (log q + log 2) - 1/(σ - β)`. -/
lemma neg_re_logDeriv_LFunction_le_real_zero {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (hq : q ≠ 1) {β : ℝ} (hβ : LFunction χ β = 0) (hβ0 : 0 < β) {σ : ℝ}
    (h1 : 1 < σ) (h2 : σ ≤ 2) :
    -(deriv (LFunction χ) σ / LFunction χ σ).re ≤ 6 * (Real.log q + Real.log 2) - 1 / (σ - β) := by
  obtain ⟨ρ, hρ⟩ := exists_zeroIndex_dirichletXi hχ hq hβ (by simpa using hβ0)
  have h := neg_re_logDeriv_LFunction_le_zero hχ hq ρ h1 h2
  have him : ρ.val.im = 0 := by rw [hρ]; simp
  have hre : ρ.val.re = β := by rw [hρ]; simp
  rw [him, hre] at h
  simpa using h

lemma changeLevel_mul_ne_one {q₁ q₂ : ℕ} [NeZero q₁] [NeZero q₂] {χ₁ : DirichletCharacter ℂ q₁}
    {χ₂ : DirichletCharacter ℂ q₂} (hr₂ : χ₂ ^ 2 = 1)
    (hne : changeLevel (dvd_mul_right q₁ q₂) χ₁ ≠ changeLevel (dvd_mul_left q₂ q₁) χ₂) :
    changeLevel (dvd_mul_right q₁ q₂) χ₁ * changeLevel (dvd_mul_left q₂ q₁) χ₂ ≠ 1 := by
  intro h
  apply hne
  have h2 : (changeLevel (dvd_mul_left q₂ q₁) χ₂) ^ 2 = 1 := by rw [← map_pow, hr₂, map_one]
  have hinv : (changeLevel (dvd_mul_left q₂ q₁) χ₂)⁻¹ = changeLevel (dvd_mul_left q₂ q₁) χ₂ :=
    inv_eq_of_mul_eq_one_left (by rw [← sq, h2])
  rw [eq_inv_of_mul_eq_one_left h, hinv]

/-- **Landau's theorem** (Davenport, Ch. 14, p. 93, (7), row 14-12): if `χ₁`, `χ₂` are real
primitive nonprincipal characters mod `q₁`, `q₂`, inducing distinct characters mod `q₁ q₂`, and
`β₁`, `β₂` are real zeros of `L(s, χ₁)`, `L(s, χ₂)`, then
`min(β₁, β₂) ≤ 1 - c/log(q₁ q₂)` with `c = 1/400`. -/
@[kb "davenport1980" "Ch 14, p. 93"]
theorem Davenport.landau_real_zeros {q₁ q₂ : ℕ} [NeZero q₁] [NeZero q₂]
    {χ₁ : DirichletCharacter ℂ q₁} {χ₂ : DirichletCharacter ℂ q₂} (hp₁ : χ₁.IsPrimitive)
    (hp₂ : χ₂.IsPrimitive) (h₁ : χ₁ ≠ 1) (h₂ : χ₂ ≠ 1) (hr₁ : χ₁ ^ 2 = 1) (hr₂ : χ₂ ^ 2 = 1)
    (hne : changeLevel (dvd_mul_right q₁ q₂) χ₁ ≠ changeLevel (dvd_mul_left q₂ q₁) χ₂)
    {β₁ β₂ : ℝ} (hz₁ : LFunction χ₁ β₁ = 0) (hz₂ : LFunction χ₂ β₂ = 0) :
    min β₁ β₂ ≤ 1 - 1 / 400 / Real.log (q₁ * q₂) := by
  have hq₁ := two_le_of_ne_one h₁
  have hq₂ := two_le_of_ne_one h₂
  have hl2 := log_two_gt_two_thirds
  obtain ⟨lQ, hlQ⟩ : ∃ lQ, lQ = Real.log ((q₁ : ℝ) * q₂) := ⟨_, rfl⟩
  rw [← hlQ]
  have hlog := Real.log_mul (show (q₁ : ℝ) ≠ 0 by positivity) (show (q₂ : ℝ) ≠ 0 by positivity)
  have hl1 : Real.log 2 ≤ Real.log q₁ := Real.log_le_log two_pos hq₁
  have hl2' : Real.log 2 ≤ Real.log q₂ := Real.log_le_log two_pos hq₂
  have hlQ2 : 2 * Real.log 2 ≤ lQ := by rw [hlQ, hlog]; linarith
  have hlQ0 : 0 < lQ := by linarith
  -- trivial cases
  by_contra hcon
  push Not at hcon
  have hb₁ : 1 - 1 / 400 / lQ < β₁ := hcon.trans_le (min_le_left _ _)
  have hb₂ : 1 - 1 / 400 / lQ < β₂ := hcon.trans_le (min_le_right _ _)
  have hsmall : 1 / 400 / lQ ≤ 1 / 2 := by
    rw [div_le_iff₀ hlQ0]; linarith
  have hβ₁0 : 0 < β₁ := by linarith
  have hβ₂0 : 0 < β₂ := by linarith
  have hq₁1 : q₁ ≠ 1 := by rintro rfl; norm_num at hq₁
  have hq₂1 : q₂ ≠ 1 := by rintro rfl; norm_num at hq₂
  have hβ₁1 : β₁ < 1 := by
    by_contra h
    exact LFunction_ne_zero_of_one_le_re χ₁ (Or.inl h₁) (by simpa using not_lt.mp h) hz₁
  have hβ₂1 : β₂ < 1 := by
    by_contra h
    exact LFunction_ne_zero_of_one_le_re χ₂ (Or.inl h₂) (by simpa using not_lt.mp h) hz₂
  -- `σ = 1 + d`, `d = 1/(100 lQ)`
  obtain ⟨d, hd⟩ : ∃ d : ℝ, d = 1 / 100 / lQ := ⟨_, rfl⟩
  have hd0 : 0 < d := by rw [hd]; positivity
  have hdl : d * lQ = 1 / 100 := by rw [hd]; field_simp
  have hd1 : d ≤ 1 := by rw [hd, div_le_one hlQ0]; linarith
  have hb₁' : 1 - d / 4 < β₁ := by
    rw [show d / 4 = 1 / 400 / lQ by rw [hd]; ring]; exact hb₁
  have hb₂' : 1 - d / 4 < β₂ := by
    rw [show d / 4 = 1 / 400 / lQ by rw [hd]; ring]; exact hb₂
  set σ : ℝ := 1 + d with hσ
  have hσ1 : 1 < σ := by linarith
  have hσ2 : σ ≤ 2 := by linarith
  have key := Davenport.landau_positivity hr₁ hr₂ hσ1
  have e0 := Davenport.neg_logDeriv_riemannZeta_real_le hσ1 hσ2
  have e1 := neg_re_logDeriv_LFunction_le_real_zero hp₁ hq₁1 hz₁ hβ₁0 hσ1 hσ2
  have e2 := neg_re_logDeriv_LFunction_le_real_zero hp₂ hq₂1 hz₂ hβ₂0 hσ1 hσ2
  have hψ := changeLevel_mul_ne_one hr₂ hne
  have e3 := neg_re_logDeriv_LFunction_le_of_ne_one hψ (s := σ) (by simpa using hσ1)
    (by simpa using hσ2)
  simp only [Complex.ofReal_im, abs_zero, zero_add] at e3
  push_cast at e3
  rw [← hlQ] at e3
  have hσm1 : 1 / (σ - 1) = 1 / d := by rw [hσ]; ring_nf
  rw [hσm1] at e0
  -- `1/(σ - β₁) + 1/(σ - β₂) ≤ 1/d + 43 lQ`
  have hsum : 1 / (σ - β₁) + 1 / (σ - β₂) ≤ 1 / d + 43 * lQ := by
    have : Real.log q₁ ≤ lQ := by rw [hlQ, hlog]; linarith
    have : Real.log q₂ ≤ lQ := by rw [hlQ, hlog]; linarith
    linarith
  -- each `1/(σ - βᵢ) > 4/(5d)`
  have hu₁ : 1 / (σ - β₁) ≥ 4 / 5 * (1 / d) := by
    rw [ge_iff_le, show 4 / 5 * (1 / d) = 1 / (5 / 4 * d) by field_simp]
    exact one_div_le_one_div_of_le (by linarith) (by linarith)
  have hu₂ : 1 / (σ - β₂) ≥ 4 / 5 * (1 / d) := by
    rw [ge_iff_le, show 4 / 5 * (1 / d) = 1 / (5 / 4 * d) by field_simp]
    exact one_div_le_one_div_of_le (by linarith) (by linarith)
  have h3 : 3 / 5 * (1 / d) ≤ 43 * lQ := by linarith
  have : 3 / 5 * (1 / d) * d = 3 / 5 := by field_simp
  nlinarith

/-- Primitive characters to different moduli induce different characters mod `q₁ q₂`. -/
theorem Davenport.landau_hne_of_ne_level {q₁ q₂ : ℕ} [NeZero q₁] [NeZero q₂]
    {χ₁ : DirichletCharacter ℂ q₁} {χ₂ : DirichletCharacter ℂ q₂} (hp₁ : χ₁.IsPrimitive)
    (hp₂ : χ₂.IsPrimitive) (hq : q₁ ≠ q₂) :
    changeLevel (dvd_mul_right q₁ q₂) χ₁ ≠ changeLevel (dvd_mul_left q₂ q₁) χ₂ := by
  intro h
  have h1 := conductor_changeLevel χ₁ (dvd_mul_right q₁ q₂)
  have h2 := conductor_changeLevel χ₂ (dvd_mul_left q₂ q₁)
  rw [h, h2] at h1
  exact hq (hp₁ ▸ hp₂ ▸ h1.symm)

/-- Distinct characters to the same modulus induce different characters mod `q²`. -/
theorem Davenport.landau_hne_of_ne {q : ℕ} [NeZero q] {χ₁ χ₂ : DirichletCharacter ℂ q}
    (hne : χ₁ ≠ χ₂) :
    changeLevel (dvd_mul_right q q) χ₁ ≠ changeLevel (dvd_mul_left q q) χ₂ :=
  fun h ↦ hne (changeLevel_injective (dvd_mul_right q q) h)

/-- `χ` lifted to a multiple level agrees with `χ` at integers coprime to the new level. -/
lemma changeLevel_natCast_of_coprime {q m : ℕ} (hm : q ∣ m) (χ : DirichletCharacter ℂ q) {n : ℕ}
    (hn : n.Coprime m) : changeLevel hm χ (n : ZMod m) = χ n := by
  have h := changeLevel_eq_cast_of_dvd' χ hm (a := (n : ℤ)) (Nat.isCoprime_iff_coprime.mpr hn)
  simpa using h

/-- If the primitive characters inducing `χ`, `χ'` mod `q` induce the same character
mod `q₁ q₁'`, then `χ = χ'`. -/
lemma eq_of_primitiveCharacter_changeLevel_eq {q : ℕ} [NeZero q] {χ χ' : DirichletCharacter ℂ q}
    (h : changeLevel (dvd_mul_right χ.conductor χ'.conductor) χ.primitiveCharacter =
      changeLevel (dvd_mul_left χ'.conductor χ.conductor) χ'.primitiveCharacter) : χ = χ' := by
  refine MulChar.ext fun u ↦ ?_
  set n := (u : ZMod q).val
  have hn : (n : ZMod q) = u := ZMod.natCast_zmod_val _
  have hcop : n.Coprime q := by
    rw [← ZMod.isUnit_iff_coprime, hn]; exact u.isUnit
  have hc₁ : n.Coprime χ.conductor := Nat.Coprime.coprime_dvd_right (conductor_dvd_level χ) hcop
  have hc₂ : n.Coprime χ'.conductor :=
    Nat.Coprime.coprime_dvd_right (conductor_dvd_level χ') hcop
  have hcQ : n.Coprime (χ.conductor * χ'.conductor) := Nat.Coprime.mul_right hc₁ hc₂
  have e := congrArg (fun ψ : DirichletCharacter ℂ (χ.conductor * χ'.conductor) ↦
    ψ (n : ZMod (χ.conductor * χ'.conductor))) h
  rw [changeLevel_natCast_of_coprime _ _ hcQ, changeLevel_natCast_of_coprime _ _ hcQ] at e
  rw [← hn, ← changeLevel_primitiveCharacter χ, ← changeLevel_primitiveCharacter χ',
    changeLevel_natCast_of_coprime _ _ hcop, changeLevel_natCast_of_coprime _ _ hcop, e]

/-- **Davenport, Ch. 14, p. 94 (row 14-13)**: at most one real nonprincipal character `χ`
mod `q` has `L(s, χ)` with a real zero `β > 1 - c/log q` (`c = 1/800`). -/
@[kb "davenport1980" "Ch 14, p. 94"]
theorem Davenport.at_most_one_exceptional_character {q : ℕ} [NeZero q]
    {χ χ' : DirichletCharacter ℂ q} (h₁ : χ ≠ 1) (h₂ : χ' ≠ 1) (hr₁ : χ ^ 2 = 1)
    (hr₂ : χ' ^ 2 = 1) {β β' : ℝ} (hz : LFunction χ β = 0) (hz' : LFunction χ' β' = 0)
    (hb : 1 - 1 / 800 / Real.log q < β) (hb' : 1 - 1 / 800 / Real.log q < β') : χ = χ' := by
  by_contra hne
  have hq := two_le_of_ne_one h₁
  have hl2 := log_two_gt_two_thirds
  have hlq : Real.log 2 ≤ Real.log q := Real.log_le_log two_pos hq
  have hsmall : 1 / 800 / Real.log q ≤ 1 / 2 := by
    rw [div_le_iff₀ (by linarith)]; linarith
  have : NeZero χ.conductor := ⟨conductor_ne_zero χ⟩
  have : NeZero χ'.conductor := ⟨conductor_ne_zero χ'⟩
  have hz₁ := LFunction_primitiveCharacter_eq_zero h₁ hz (by simp; linarith)
  have hz₁' := LFunction_primitiveCharacter_eq_zero h₂ hz' (by simp; linarith)
  have hL := Davenport.landau_real_zeros (primitiveCharacter_isPrimitive χ)
    (primitiveCharacter_isPrimitive χ') (primitiveCharacter_ne_one h₁)
    (primitiveCharacter_ne_one h₂) (primitiveCharacter_sq_eq_one hr₁)
    (primitiveCharacter_sq_eq_one hr₂)
    (fun h ↦ hne (eq_of_primitiveCharacter_changeLevel_eq h)) hz₁ hz₁'
  have hM := log_conductor_le χ
  have hM' := log_conductor_le χ'
  have hlog := Real.log_mul (show (χ.conductor : ℝ) ≠ 0 by
    exact_mod_cast conductor_ne_zero χ) (show (χ'.conductor : ℝ) ≠ 0 by
    exact_mod_cast conductor_ne_zero χ')
  have hM2 := Real.log_le_log two_pos (two_le_conductor h₁)
  have hM2' := Real.log_le_log two_pos (two_le_conductor h₂)
  have hpos : 0 < Real.log ((χ.conductor : ℝ) * χ'.conductor) := by rw [hlog]; linarith
  have : 1 / 800 / Real.log q ≤ 1 / 400 / Real.log ((χ.conductor : ℝ) * χ'.conductor) := by
    rw [div_le_div_iff₀ (by linarith) hpos, hlog]; linarith
  have := min_le_iff.mp hL
  rcases this with h | h <;> linarith

/-- **Davenport, Ch. 14, pp. 94-95 (row 14-14)**: if real primitive nonprincipal characters
`χ` mod `q` and `χ'` mod `q'` (distinct, `q ≤ q'`) have real zeros `β > 1 - c/log q` and
`β' > 1 - c/log q'` with `c = 1/1200`, then `q' > q²`. -/
@[kb "davenport1980" "Ch 14, p. 95"]
theorem Davenport.exceptional_moduli_grow {q q' : ℕ} [NeZero q] [NeZero q']
    {χ : DirichletCharacter ℂ q} {χ' : DirichletCharacter ℂ q'} (hp : χ.IsPrimitive)
    (hp' : χ'.IsPrimitive) (h₁ : χ ≠ 1) (h₂ : χ' ≠ 1) (hr₁ : χ ^ 2 = 1) (hr₂ : χ' ^ 2 = 1)
    (hne : changeLevel (dvd_mul_right q q') χ ≠ changeLevel (dvd_mul_left q' q) χ')
    (hqq : q ≤ q') {β β' : ℝ} (hz : LFunction χ β = 0) (hz' : LFunction χ' β' = 0)
    (hb : 1 - 1 / 1200 / Real.log q < β) (hb' : 1 - 1 / 1200 / Real.log q' < β') :
    q ^ 2 < q' := by
  have hq := two_le_of_ne_one h₁
  have hq' := two_le_of_ne_one h₂
  have hl2 := log_two_gt_two_thirds
  have hlq : Real.log 2 ≤ Real.log q := Real.log_le_log two_pos hq
  have hlqq : Real.log q ≤ Real.log q' := Real.log_le_log (by linarith) (by exact_mod_cast hqq)
  have hL := Davenport.landau_real_zeros hp hp' h₁ h₂ hr₁ hr₂ hne hz hz'
  have hlog := Real.log_mul (show (q : ℝ) ≠ 0 by positivity) (show (q' : ℝ) ≠ 0 by positivity)
  rw [hlog] at hL
  have hb'' : 1 - 1 / 1200 / Real.log q < β' := by
    have : 1 / 1200 / Real.log q' ≤ 1 / 1200 / Real.log q :=
      div_le_div_of_nonneg_left (by norm_num) (by linarith) hlqq
    linarith
  have hmin : 1 - 1 / 1200 / Real.log q < min β β' := lt_min hb hb''
  have h1 : 1 / 400 / (Real.log q + Real.log q') < 1 / 1200 / Real.log q := by linarith
  rw [div_lt_div_iff₀ (by linarith) (by linarith)] at h1
  -- `2 log q < log q'`
  have h2 : Real.log ((q : ℝ) ^ 2) < Real.log q' := by
    rw [Real.log_pow]; push_cast; linarith
  have := (Real.log_lt_log_iff (by positivity) (by linarith)).mp h2
  exact_mod_cast this

/-- **Page's theorem** (Davenport, Ch. 14, p. 95, (9), row 14-15): for `z ≥ 3` there is at most
one real primitive nonprincipal character `χ` to a modulus `q ≤ z` for which `L(s, χ)` has a
real zero `β > 1 - c/log z` (`c = 1/800`): any two such coincide. -/
@[kb "davenport1980" "Ch 14, p. 95"]
theorem Davenport.page_exceptional_character {z : ℝ} (_hz3 : 3 ≤ z) {q₁ q₂ : ℕ} [NeZero q₁]
    [NeZero q₂] {χ₁ : DirichletCharacter ℂ q₁} {χ₂ : DirichletCharacter ℂ q₂}
    (hp₁ : χ₁.IsPrimitive) (hp₂ : χ₂.IsPrimitive) (h₁ : χ₁ ≠ 1) (h₂ : χ₂ ≠ 1)
    (hr₁ : χ₁ ^ 2 = 1) (hr₂ : χ₂ ^ 2 = 1) (hq₁ : (q₁ : ℝ) ≤ z) (hq₂ : (q₂ : ℝ) ≤ z)
    {β₁ β₂ : ℝ} (hz₁ : LFunction χ₁ β₁ = 0) (hz₂ : LFunction χ₂ β₂ = 0)
    (hb₁ : 1 - 1 / 800 / Real.log z < β₁) (hb₂ : 1 - 1 / 800 / Real.log z < β₂) :
    q₁ = q₂ ∧ HEq χ₁ χ₂ := by
  have hne_or : changeLevel (dvd_mul_right q₁ q₂) χ₁ = changeLevel (dvd_mul_left q₂ q₁) χ₂ := by
    by_contra hne
    have hq₁2 := two_le_of_ne_one h₁
    have hq₂2 := two_le_of_ne_one h₂
    have hL := Davenport.landau_real_zeros hp₁ hp₂ h₁ h₂ hr₁ hr₂ hne hz₁ hz₂
    have hlog := Real.log_mul (show (q₁ : ℝ) ≠ 0 by positivity)
      (show (q₂ : ℝ) ≠ 0 by positivity)
    have hl1 : Real.log q₁ ≤ Real.log z := Real.log_le_log (by linarith) hq₁
    have hl2 : Real.log q₂ ≤ Real.log z := Real.log_le_log (by linarith) hq₂
    have hl2' := log_two_gt_two_thirds
    have hlq1 : Real.log 2 ≤ Real.log q₁ := Real.log_le_log two_pos hq₁2
    have hlq2 : Real.log 2 ≤ Real.log q₂ := Real.log_le_log two_pos hq₂2
    rw [hlog] at hL
    have : 1 / 800 / Real.log z ≤ 1 / 400 / (Real.log q₁ + Real.log q₂) := by
      rw [div_le_div_iff₀ (by linarith) (by linarith)]; linarith
    have := min_le_iff.mp hL
    rcases this with h | h <;> linarith
  by_cases hq : q₁ = q₂
  · subst hq
    exact ⟨rfl, heq_of_eq (changeLevel_injective (dvd_mul_right q₁ q₁) hne_or)⟩
  · exact absurd hne_or (Davenport.landau_hne_of_ne_level hp₁ hp₂ hq)

end NTKB
