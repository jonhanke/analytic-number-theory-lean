/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Davenport.Zeros.PNTAPExceptional
import NTKB.Analytic.Davenport.ClassNumber.EvenZero

/-!
# The size of the exceptional term and of the exceptional modulus

**Davenport, Ch. 20, pp. 123-124 (rows 20-6, 20-9).**

* Row 20-6 (`Davenport.norm_exceptional_term_le`): the only upper bound known for `β₁` is
  `β₁ < 1 - c/(q^{1/2} log² q)` (14-18), so the exceptional term of 20-5 is at most
  `(2x/φ(q)) exp(-c log x/(q^{1/2} log² q))`; for even `χ₁` with `q^{1/2} log q` (the improvement of
  14-18 for even characters).
* Row 20-9 (`Davenport.page_modulus_large`, `Davenport.page_modulus_large_of_log`): a real
  primitive character modulo `q₁ ≤ z` with a real zero `β > 1 - c₂₀/log z` (Page's modulus, 20-8)
  has `q₁^{1/2} log² q₁ > c log z` by 14-18; with `z = exp(C √log x)`, `q₁ log⁴ q₁ > c' log x`, and
  `q₁ log² q₁ > c' log x` if the character is even.
-/

open Complex DirichletCharacter
open scoped Real

namespace NTKB

/-- **Davenport, Ch. 20, p. 123 (row 20-6)**: there is `c > 0` such that for every exceptional
pair `(χ₁, β₁)` modulo `q`, every `a` and every real `x ≥ 1`,
`|χ₁(a) x^{β₁}/(φ(q) β₁)| ≤ (2x/φ(q)) exp(-c log x/(q^{1/2} log² q))`, and
`≤ (2x/φ(q)) exp(-c log x/(q^{1/2} log q))` if `χ₁` is even. -/
@[kb "davenport1980" "Ch 20, p. 123"]
theorem Davenport.norm_exceptional_term_le :
    ∃ c : ℝ, 0 < c ∧ ∀ {q : ℕ} [NeZero q] {χ₁ : DirichletCharacter ℂ q} {β₁ : ℝ},
      IsExceptional χ₁ β₁ → ∀ (a : ZMod q) (x : ℝ), 1 ≤ x →
      ‖χ₁ a * (x : ℂ) ^ (β₁ : ℂ) / (q.totient * β₁)‖ ≤
          2 * x / q.totient * Real.exp (-(c * Real.log x / (√(q : ℝ) * Real.log q ^ 2))) ∧
        (χ₁.Even → ‖χ₁ a * (x : ℂ) ^ (β₁ : ℂ) / (q.totient * β₁)‖ ≤
          2 * x / q.totient * Real.exp (-(c * Real.log x / (√(q : ℝ) * Real.log q)))) := by
  obtain ⟨c, hc, h⟩ := Davenport.real_zero_lt_book
  refine ⟨c, hc, fun {q} _ {χ₁} {β₁} h₁ a x hx ↦ ?_⟩
  have hquad : χ₁.IsQuadratic := MulChar.isQuadratic_iff_sq_eq_one.mpr h₁.2.1
  obtain ⟨hb, hbe⟩ := h hquad h₁.1 β₁ h₁.2.2.1
  have hx0 : 0 < x := by linarith
  have hhalf := h₁.half_lt
  have hφ : (0 : ℝ) < q.totient := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
  -- `|χ₁(a) x^β/(φ β)| ≤ 2 x^β/φ`
  have hnorm : ‖χ₁ a * (x : ℂ) ^ (β₁ : ℂ) / (q.totient * β₁)‖ ≤ 2 * x ^ β₁ / q.totient := by
    rw [norm_div, norm_mul, norm_mul, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by linarith : (0 : ℝ) < β₁),
      ← Complex.ofReal_cpow hx0.le, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.rpow_pos_of_pos hx0 _)]
    have h1 := DirichletCharacter.norm_le_one χ₁ a
    have hxb : 0 < x ^ β₁ := Real.rpow_pos_of_pos hx0 _
    rw [div_le_div_iff₀ (by positivity) hφ]
    have : ‖χ₁ a‖ * x ^ β₁ ≤ x ^ β₁ := by nlinarith [norm_nonneg (χ₁ a)]
    have k1 : ‖χ₁ a‖ * x ^ β₁ * q.totient ≤ x ^ β₁ * q.totient :=
      mul_le_mul_of_nonneg_right this hφ.le
    have k2 : x ^ β₁ * q.totient ≤ 2 * x ^ β₁ * (q.totient * β₁) := by
      have := mul_pos hxb hφ; nlinarith
    linarith
  -- `x^β ≤ x exp(-δ log x)` for `β ≤ 1 - δ`
  have hpow : ∀ δ : ℝ, β₁ ≤ 1 - δ → x ^ β₁ ≤ x * Real.exp (-(δ * Real.log x)) := by
    intro δ hδ
    calc x ^ β₁ ≤ x ^ (1 - δ) := Real.rpow_le_rpow_of_exponent_le hx hδ
      _ = x * Real.exp (-(δ * Real.log x)) := by
        rw [Real.rpow_sub hx0, Real.rpow_one, Real.rpow_def_of_pos hx0, div_eq_mul_inv,
          ← Real.exp_neg]
        congr 2; ring
  constructor
  · refine hnorm.trans ?_
    have := hpow _ hb.le
    have e : c * Real.log x / (√(q : ℝ) * Real.log q ^ 2) =
        c / (√(q : ℝ) * Real.log q ^ 2) * Real.log x := by ring
    rw [e]
    calc 2 * x ^ β₁ / q.totient ≤ 2 * (x * Real.exp (-(c / (√(q : ℝ) * Real.log q ^ 2) *
          Real.log x))) / q.totient := by gcongr
      _ = _ := by ring
  · intro he
    refine hnorm.trans ?_
    have := hpow _ (hbe he).le
    have e : c * Real.log x / (√(q : ℝ) * Real.log q) =
        c / (√(q : ℝ) * Real.log q) * Real.log x := by ring
    rw [e]
    calc 2 * x ^ β₁ / q.totient ≤ 2 * (x * Real.exp (-(c / (√(q : ℝ) * Real.log q) *
          Real.log x))) / q.totient := by gcongr
      _ = _ := by ring

/-- **Davenport, Ch. 20, p. 124 (row 20-9)**: there is `c > 0` such that for every `z ≥ 3` and
every real primitive character `χ ≠ χ₀` modulo `q₁ ≤ z` with a real zero `β > 1 - 1/(800 log z)`
(Page's modulus, `IsPageModulus`): `c log z < q₁^{1/2} log² q₁`, and `c log z < q₁^{1/2} log q₁` if
`χ` is even. -/
@[kb "davenport1980" "Ch 20, p. 124"]
theorem Davenport.page_modulus_large :
    ∃ c : ℝ, 0 < c ∧ ∀ {z : ℝ}, 3 ≤ z → ∀ {q₁ : ℕ} [NeZero q₁] {χ : DirichletCharacter ℂ q₁}
      {β : ℝ}, χ ≠ 1 → χ ^ 2 = 1 → LFunction χ β = 0 → 1 - 1 / 800 / Real.log z < β →
      c * Real.log z < √(q₁ : ℝ) * Real.log q₁ ^ 2 ∧
        (χ.Even → c * Real.log z < √(q₁ : ℝ) * Real.log q₁) := by
  obtain ⟨c, hc, h⟩ := Davenport.real_zero_lt_book
  refine ⟨800 * c, by positivity, fun {z} hz {q₁} _ {χ} {β} hχ hsq hβ hb ↦ ?_⟩
  have hquad : χ.IsQuadratic := MulChar.isQuadratic_iff_sq_eq_one.mpr hsq
  obtain ⟨h1, h2⟩ := h hquad hχ β hβ
  have hlz : 0 < Real.log z := Real.log_pos (by linarith)
  have hq3 : (3 : ℝ) ≤ q₁ := by exact_mod_cast three_le_of_ne_one hχ
  have hlq : 0 < Real.log q₁ := Real.log_pos (by linarith)
  have hs : 0 < √(q₁ : ℝ) := Real.sqrt_pos.mpr (by linarith)
  -- `c/D < 1/(800 log z)` gives `800 c log z < D`
  have key : ∀ D : ℝ, 0 < D → β < 1 - c / D → 800 * c * Real.log z < D := by
    intro D hD hβD
    have : c / D < 1 / 800 / Real.log z := by linarith
    rw [div_lt_div_iff₀ hD (by positivity)] at this
    nlinarith
  exact ⟨key _ (by positivity) h1, fun he ↦ key _ (by positivity) (h2 he)⟩

/-- **Davenport, Ch. 20, p. 124, (12) (row 20-9)** with `z = exp(C √log x)`: there is `c > 0`
such that for every `C > 0` and `x ≥ e^{(log 3/C)²}` (so `z ≥ 3`), Page's modulus `q₁` satisfies
`q₁ log⁴ q₁ > c C² log x`, and `q₁ log² q₁ > c C² log x` if its character is even. -/
@[kb "davenport1980" "Ch 20, p. 124, (12)"]
theorem Davenport.page_modulus_large_of_log :
    ∃ c : ℝ, 0 < c ∧ ∀ {C x : ℝ}, 0 < C → 3 ≤ Real.exp (C * √(Real.log x)) →
      ∀ {q₁ : ℕ} [NeZero q₁] {χ : DirichletCharacter ℂ q₁} {β : ℝ}, χ ≠ 1 → χ ^ 2 = 1 →
      LFunction χ β = 0 → 1 - 1 / 800 / (C * √(Real.log x)) < β →
      c * C ^ 2 * Real.log x < q₁ * Real.log q₁ ^ 4 ∧
        (χ.Even → c * C ^ 2 * Real.log x < q₁ * Real.log q₁ ^ 2) := by
  obtain ⟨c, hc, h⟩ := Davenport.page_modulus_large
  refine ⟨c ^ 2, by positivity, fun {C x} hC hz {q₁} _ {χ} {β} hχ hsq hβ hb ↦ ?_⟩
  have hlog : Real.log (Real.exp (C * √(Real.log x))) = C * √(Real.log x) := Real.log_exp _
  have e := h hz hχ hsq hβ (by rw [hlog]; exact hb)
  rw [hlog] at e
  have hlz : 0 < C * √(Real.log x) := by
    have := Real.log_le_log (by norm_num) hz
    rw [hlog] at this
    have := Real.log_pos (by norm_num : (1 : ℝ) < 3)
    linarith
  have hs0 : 0 < √(Real.log x) := pos_of_mul_pos_right hlz hC.le
  have hLx : √(Real.log x) ^ 2 = Real.log x := Real.sq_sqrt (by
    by_contra hneg; push Not at hneg
    rw [Real.sqrt_eq_zero_of_nonpos hneg.le] at hs0; exact lt_irrefl _ hs0)
  have hq0 : (0 : ℝ) ≤ q₁ := Nat.cast_nonneg _
  have hsq1 : √(q₁ : ℝ) ^ 2 = q₁ := Real.sq_sqrt hq0
  have hA : 0 < c * (C * √(Real.log x)) := by positivity
  -- square both sides
  have sq_lt : ∀ {a b : ℝ}, 0 < a → a < b → a ^ 2 < b ^ 2 := fun ha hab ↦
    pow_lt_pow_left₀ hab ha.le (by norm_num)
  have e1 : (c * (C * √(Real.log x))) ^ 2 = c ^ 2 * C ^ 2 * Real.log x := by
    rw [mul_pow, mul_pow, hLx]; ring
  constructor
  · have := sq_lt hA e.1
    rw [e1] at this
    calc c ^ 2 * C ^ 2 * Real.log x < (√(q₁ : ℝ) * Real.log q₁ ^ 2) ^ 2 := this
      _ = q₁ * Real.log q₁ ^ 4 := by rw [mul_pow, hsq1]; ring
  · intro he
    have := sq_lt hA (e.2 he)
    rw [e1] at this
    calc c ^ 2 * C ^ 2 * Real.log x < (√(q₁ : ℝ) * Real.log q₁) ^ 2 := this
      _ = q₁ * Real.log q₁ ^ 2 := by rw [mul_pow, hsq1]

/-- **Davenport, Ch. 14, p. 104 (row 14-13), in the region of 14-11**: at most one nonprincipal
character modulo `q` has `L(s, χ)` with a zero in the region `σ > 1 - c/log(q max(1, |t|))` of the
zero-free theorem 14-11 (`c = 1/16200`); such a character is real and the zero is real. -/
@[kb "davenport1980" "Ch 14, p. 104"]
theorem Davenport.at_most_one_character_with_exc_zero {q : ℕ} [NeZero q]
    {χ χ' : DirichletCharacter ℂ q} (h₁ : χ ≠ 1) (h₂ : χ' ≠ 1) {s s' : ℂ}
    (hs : LFunction χ s = 0) (hs' : LFunction χ' s' = 0) (he : IsExcPoint q s)
    (he' : IsExcPoint q s') : χ = χ' := by
  have hq := two_le_of_ne_one h₁
  have toExc : ∀ {ψ : DirichletCharacter ℂ q} {z : ℂ}, ψ ≠ 1 → LFunction ψ z = 0 →
      IsExcPoint q z → IsExceptional ψ z.re := by
    intro ψ z hψ hz hez
    obtain ⟨hsq, him⟩ := Davenport.exceptional_zero_real hψ hz hez
    have hzr : z = (z.re : ℂ) := by apply Complex.ext <;> simp [him]
    refine ⟨hψ, hsq, by rw [← hzr]; exact hz, ?_⟩
    have := hez
    unfold IsExcPoint at this
    rwa [him, logQT_of_lt_one (by linarith) (by simp)] at this
  exact (Davenport.isExceptional_unique (toExc h₁ hs he) (toExc h₂ hs' he')).1

/-- **Davenport, Ch. 14, p. 101 (row 14-9), with the strict inequality of the book**: for a real
nonprincipal character `χ` modulo `q` and `0 < δ ≤ 2/245`, every zero `β + iγ` of `L(s, χ)` with
`|γ| ≥ δ/log q` has `β < 1 - δ/(10 𝔏)`, `𝔏 = log q + log(|γ| + 2)`. -/
@[kb "davenport1980" "Ch 14, p. 101"]
theorem Davenport.LFunction_zero_free_real_lt {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ1 : χ ≠ 1) (hreal : χ ^ 2 = 1) {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 2 / 245) {s : ℂ}
    (hs : LFunction χ s = 0) (hγ : δ / Real.log q ≤ |s.im|) :
    s.re < 1 - δ / (10 * (Real.log q + Real.log (|s.im| + 2))) := by
  have h := Davenport.LFunction_zero_free_real' hχ1 hreal hδ hδ' hs hγ
  have hq := two_le_of_ne_one hχ1
  have hl : 0 < Real.log q + Real.log (|s.im| + 2) := by
    have := Real.log_pos (by linarith : (1 : ℝ) < q)
    have := Real.log_nonneg (by linarith [abs_nonneg s.im] : (1 : ℝ) ≤ |s.im| + 2)
    linarith
  have : δ / (10 * (Real.log q + Real.log (|s.im| + 2))) <
      δ / (9 * (Real.log q + Real.log (|s.im| + 2))) := by
    apply div_lt_div_of_pos_left hδ (by positivity); linarith
  linarith

end NTKB
