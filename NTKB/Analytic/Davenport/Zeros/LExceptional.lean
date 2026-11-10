/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Davenport.Zeros.LZeroSum
import NTKB.Analytic.Davenport.Zeros.LZeroFreeTheorem
import NTKB.Analytic.Davenport.Hadamard.XiCharConj

/-!
# Exceptional zeros and the zeros near `0`

**Davenport, Ch. 19, pp. 118-119 (rows 19-11, 19-15) and Ch. 20, p. 122.** By the zero-free
region (14-11), a zero `ρ = β + iγ` of `L(s, χ)` with `β > 1 - c/log(q max(1, |γ|))`
(`c = 1/16200`) is *exceptional*: `χ` is real and `ρ = β₁` is real (and simple, unique). By the
symmetry `ρ ↦ 1 - ρ̄` (12-19) a zero whose mirror is not exceptional has `β ≥ c/log(q max(1,|γ|))`,
so `|ρ|⁻¹ ≪ log q` for the zeros with `|γ| < 1` other than `1 - β₁`.
-/

open Filter Topology Complex Set DirichletCharacter
open scoped Real ComplexConjugate

namespace NTKB

variable {N : ℕ} [NeZero N]

/-- A point in the region of 14-11 where only the exceptional zero can lie. -/
def IsExcPoint (N : ℕ) (s : ℂ) : Prop := 1 - 1 / 16200 / logQT N s.im < s.re

/-- **Davenport, Ch. 19, p. 118 (row 19-11)**: an exceptional zero is real, and occurs only for
a real character. -/
@[kb "davenport1980" "Ch 19, p. 118"]
theorem Davenport.exceptional_zero_real {χ : DirichletCharacter ℂ N} (hχ1 : χ ≠ 1) {s : ℂ}
    (hs : LFunction χ s = 0) (h : IsExcPoint N s) : χ ^ 2 = 1 ∧ s.im = 0 := by
  by_cases hχ2 : χ ^ 2 = 1
  · exact ⟨hχ2, (Davenport.LFunction_zero_free_theorem_real hχ1 hχ2 hs h).1⟩
  · exfalso
    have := Davenport.LFunction_zero_free_theorem_complex hχ2 hs
    exact absurd h (not_lt.mpr this)

/-- An exceptional point has `σ > 1/2` (for `q ≥ 2`). -/
lemma IsExcPoint.re_gt_half {χ : DirichletCharacter ℂ N} (hχ1 : χ ≠ 1) {s : ℂ}
    (h : IsExcPoint N s) : 1 / 2 < s.re := by
  have hN := two_le_of_ne_one hχ1
  have hp := logQT_pos hχ1 s.im
  have hl : Real.log 2 ≤ logQT N s.im := by
    rw [logQT_eq (by linarith)]
    have := Real.log_le_log two_pos hN
    have := Real.log_nonneg (le_max_left 1 |s.im|)
    linarith
  have hl2 := log_two_gt_two_thirds
  have : 1 / 16200 / logQT N s.im ≤ 1 / 2 := by
    rw [div_le_iff₀ hp]; nlinarith
  unfold IsExcPoint at h
  linarith

/-- If the mirror `1 - ρ̄` of a zero is not exceptional, then `β ≥ c/log(q max(1, |γ|))`. -/
lemma re_ge_of_mirror_not_exc {s : ℂ} (h : ¬ IsExcPoint N (1 - conj s)) :
    1 / 16200 / logQT N s.im ≤ s.re := by
  unfold IsExcPoint at h
  push Not at h
  simp only [sub_re, one_re, conj_re, sub_im, one_im, conj_im, zero_sub, neg_neg] at h
  linarith

/-- The mirror of a zero (in the critical strip) of `L(s, χ)` is a zero. -/
lemma LFunction_mirror_eq_zero {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (hN : N ≠ 1)
    (ρ : ZeroIndex (dirichletXi χ)) : LFunction χ (1 - conj ρ.val) = 0 := by
  obtain ⟨e, he⟩ := Davenport.dirichletXi_zero_symm hχ hN
  obtain ⟨ρ', hρ'⟩ := e.surjective ρ
  have := (dirichletXi_zero_mem hχ hN (e ρ)).1
  rw [he] at this
  exact this

/-- A zero whose mirror is exceptional is real, with `0 < β < 1/2`. -/
lemma mirror_exc_real {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (hN : N ≠ 1)
    (ρ : ZeroIndex (dirichletXi χ)) (h : IsExcPoint N (1 - conj ρ.val)) :
    ρ.val.im = 0 ∧ ρ.val.re < 1 / 2 := by
  have hχ1 := ne_one_of_isPrimitive hχ hN
  have hz := LFunction_mirror_eq_zero hχ hN ρ
  have h1 := (Davenport.exceptional_zero_real hχ1 hz h).2
  have h2 := h.re_gt_half hχ1
  simp only [sub_im, one_im, conj_im, zero_sub, neg_neg, sub_re, one_re, conj_re] at h1 h2
  exact ⟨h1, by linarith⟩

/-- For `|t| < T` (`T ≥ 1`), `log(q max(1, |t|)) ≤ log(q T)`. -/
lemma logQT_le {t T : ℝ} (hN : (1 : ℝ) ≤ N) (hT : 1 ≤ T) (ht : |t| < T) :
    logQT N t ≤ logQT N T := by
  rw [logQT_eq hN, logQT_eq hN]
  have h1 : |t| ≤ |T| := by rw [abs_of_pos (by linarith : (0 : ℝ) < T)]; exact ht.le
  have := Real.log_le_log (by positivity) (max_le_max (le_refl (1 : ℝ)) h1)
  linarith

/-- `(x^β - 1)/β ≤ x^β log x` for `0 < β`, `x ≥ 1`. -/
lemma rpow_sub_one_div_le {x β : ℝ} (hx : 1 ≤ x) (hβ : 0 < β) :
    (x ^ β - 1) / β ≤ x ^ β * Real.log x := by
  have hx0 : 0 < x := by linarith
  rw [div_le_iff₀ hβ]
  have hl : 0 ≤ Real.log x := Real.log_nonneg hx
  set u := β * Real.log x
  have hxb : x ^ β = Real.exp u := by rw [Real.rpow_def_of_pos hx0, mul_comm]
  rw [hxb]
  -- `e^u - 1 ≤ u e^u` for `u ≥ 0`
  have h1 := Real.add_one_le_exp (-u)
  have h2 : Real.exp u * Real.exp (-u) = 1 := by rw [← Real.exp_add]; simp
  have hu : 0 ≤ u := by positivity
  nlinarith [Real.exp_pos u]

end NTKB
