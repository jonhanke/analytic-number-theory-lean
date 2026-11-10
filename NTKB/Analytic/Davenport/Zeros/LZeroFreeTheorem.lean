/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Davenport.Zeros.LZeroFreeReal

/-!
# The zero-free region for `L(s, χ)` (Gronwall, Titchmarsh)

**Davenport, Ch. 14, p. 93 (row 14-11).** There is an absolute constant `c > 0` such that, for
`χ` a complex character mod `q`, `L(s, χ)` has no zero in the region
`σ > 1 - c/log(q |t|)` (`|t| ≥ 1`), `σ > 1 - c/log q` (`|t| < 1`), that is
`σ > 1 - c/log(q max(1, |t|))`; for `χ` real nonprincipal the only possible zero in this region
is a single real zero, simple when `χ` is primitive. We may take `c = 1/16200`.
-/

open Filter Topology Complex Set DirichletCharacter
open scoped Real

namespace NTKB

variable {N : ℕ} [NeZero N]

/-- `log(q max(1, |t|))`, Davenport's `log q|t|` for `|t| ≥ 1` and `log q` for `|t| < 1`. -/
noncomputable def logQT (N : ℕ) (t : ℝ) : ℝ := Real.log (N * max 1 |t|)

omit [NeZero N] in
lemma logQT_eq (hN : (1 : ℝ) ≤ N) (t : ℝ) :
    logQT N t = Real.log N + Real.log (max 1 |t|) := by
  unfold logQT
  rw [Real.log_mul (by positivity) (by positivity)]

omit [NeZero N] in
lemma logQT_of_lt_one (hN : (1 : ℝ) ≤ N) {t : ℝ} (ht : |t| < 1) : logQT N t = Real.log N := by
  rw [logQT_eq hN, max_eq_left ht.le, Real.log_one, add_zero]

omit [NeZero N] in
/-- `log q + log(|t| + 2) ≤ 3 log(q max(1, |t|))` for `q ≥ 2`. -/
lemma log_add_log_le_three_logQT (hN : (2 : ℝ) ≤ N) (t : ℝ) :
    Real.log N + Real.log (|t| + 2) ≤ 3 * logQT N t := by
  rw [logQT_eq (by linarith)]
  have hm : 1 ≤ max 1 |t| := le_max_left _ _
  have h1 : Real.log (|t| + 2) ≤ Real.log 3 + Real.log (max 1 |t|) := by
    rw [← Real.log_mul (by norm_num) (by positivity)]
    exact Real.log_le_log (by positivity) (by linarith [le_max_right 1 |t|])
  have h3 : Real.log 3 ≤ 2 * Real.log 2 := by
    rw [← Real.log_rpow two_pos]; exact Real.log_le_log (by norm_num) (by norm_num)
  have h2 : Real.log 2 ≤ Real.log N := Real.log_le_log two_pos hN
  have hm0 : 0 ≤ Real.log (max 1 |t|) := Real.log_nonneg hm
  linarith

lemma two_le_of_ne_one {χ : DirichletCharacter ℂ N} (hχ1 : χ ≠ 1) : (2 : ℝ) ≤ N := by
  have h0 := NeZero.ne N
  have h1 : N ≠ 1 := by rintro rfl; exact hχ1 (Subsingleton.elim _ _)
  exact_mod_cast (show 2 ≤ N by omega)

lemma logQT_pos {χ : DirichletCharacter ℂ N} (hχ1 : χ ≠ 1) (t : ℝ) : 0 < logQT N t := by
  have hN := two_le_of_ne_one hχ1
  rw [logQT_eq (by linarith)]
  have := Real.log_pos (show (1 : ℝ) < N by linarith)
  have := Real.log_nonneg (le_max_left 1 |t|)
  linarith

/-- **Davenport, Ch. 14, p. 93 (row 14-11)**, complex characters: no zero of `L(s, χ)` in
`σ > 1 - c/log(q max(1, |t|))`, `c = 1/16200`. -/
@[kb "davenport1980" "Ch 14, p. 93"]
theorem Davenport.LFunction_zero_free_theorem_complex {χ : DirichletCharacter ℂ N}
    (hχ2 : χ ^ 2 ≠ 1) {s : ℂ} (hs : LFunction χ s = 0) :
    s.re ≤ 1 - 1 / 16200 / logQT N s.im := by
  have hχ1 : χ ≠ 1 := fun h ↦ hχ2 (by rw [h, one_pow])
  have hN := two_le_of_ne_one hχ1
  have h := Davenport.LFunction_zero_free_complex hχ2 hs
  have hb := log_add_log_le_three_logQT hN s.im
  have hp := logQT_pos hχ1 s.im
  have hl2 := log_two_gt_two_thirds
  have hlT : Real.log 2 ≤ Real.log (|s.im| + 2) :=
    Real.log_le_log two_pos (by linarith [abs_nonneg s.im])
  have hlN : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  have : 1 / 16200 / logQT N s.im ≤ 1 / 714 / (Real.log N + Real.log (|s.im| + 2)) := by
    rw [div_le_div_iff₀ hp (by linarith)]
    nlinarith
  linarith

/-- The real-character part, first step: a zero in the region is `IsNearOne (1/600) q₁` for the
inducing primitive character `χ₁` mod `q₁`. -/
lemma isNearOne_of_region {χ : DirichletCharacter ℂ N} (hχ1 : χ ≠ 1) (hreal : χ ^ 2 = 1)
    {s : ℂ} (hs : LFunction χ s = 0) (hreg : 1 - 1 / 16200 / logQT N s.im < s.re) :
    have : NeZero χ.conductor := ⟨conductor_ne_zero χ⟩
    LFunction χ.primitiveCharacter s = 0 ∧ 0 < s.re ∧ IsNearOne (1 / 600) χ.conductor s := by
  have : NeZero χ.conductor := ⟨conductor_ne_zero χ⟩
  have hN := two_le_of_ne_one hχ1
  have hp := logQT_pos hχ1 s.im
  have hb := log_add_log_le_three_logQT hN s.im
  have hl2 := log_two_gt_two_thirds
  have hlT : Real.log 2 ≤ Real.log (|s.im| + 2) :=
    Real.log_le_log two_pos (by linarith [abs_nonneg s.im])
  have hlN : Real.log 2 ≤ Real.log N := Real.log_le_log two_pos hN
  have hL : 0 < Real.log N + Real.log (|s.im| + 2) := by linarith
  have h0 : 0 < s.re := by
    have : 1 / 16200 / logQT N s.im ≤ 1 := by
      rw [div_le_one hp]; nlinarith
    linarith
  -- zeros off the real axis are excluded by row 14-9
  have hγ : |s.im| < 1 / 600 / (Real.log N + Real.log (|s.im| + 2)) := by
    by_contra hγ
    push Not at hγ
    have h := Davenport.LFunction_zero_free_real hχ1 hreal (κ := 1 / 600) (by norm_num)
      (by norm_num) hs hγ
    have : 1 / 16200 / logQT N s.im ≤ 1 / 600 / (9 * (Real.log N + Real.log (|s.im| + 2))) := by
      rw [div_le_div_iff₀ hp (by positivity)]
      nlinarith
    linarith
  have hz := LFunction_primitiveCharacter_eq_zero hχ1 hs h0
  refine ⟨hz, h0, ?_, ?_⟩
  · have hM2 := two_le_conductor hχ1
    have hlM : Real.log 2 ≤ Real.log χ.conductor := Real.log_le_log two_pos hM2
    have hMN := log_conductor_le χ
    refine hγ.trans_le (div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith))
  · have ht1 : |s.im| < 1 := by
      refine hγ.trans_le ?_
      rw [div_le_one hL]; linarith
    rw [logQT_of_lt_one (by linarith) ht1] at hreg
    have hM2 := two_le_conductor hχ1
    have hlM : Real.log 2 ≤ Real.log χ.conductor := Real.log_le_log two_pos hM2
    have hMN := log_conductor_le χ
    have : 1 / 600 / Real.log χ.conductor ≥ 1 / 16200 / Real.log N := by
      rw [ge_iff_le, div_le_div_iff₀ (by linarith) (by linarith)]
      nlinarith
    linarith

/-- **Davenport, Ch. 14, p. 93 (row 14-11)**, real characters: for `χ ≠ χ₀` real mod `q`
(primitive or not), a zero of `L(s, χ)` in `σ > 1 - c/log(q max(1, |t|))` (`c = 1/16200`)
is real, and there is at most one such zero. -/
@[kb "davenport1980" "Ch 14, p. 93"]
theorem Davenport.LFunction_zero_free_theorem_real {χ : DirichletCharacter ℂ N} (hχ1 : χ ≠ 1)
    (hreal : χ ^ 2 = 1) {s : ℂ} (hs : LFunction χ s = 0)
    (hreg : 1 - 1 / 16200 / logQT N s.im < s.re) :
    s.im = 0 ∧ ∀ s' : ℂ, LFunction χ s' = 0 → 1 - 1 / 16200 / logQT N s'.im < s'.re → s' = s := by
  have : NeZero χ.conductor := ⟨conductor_ne_zero χ⟩
  have hprim := primitiveCharacter_isPrimitive χ
  have hχ1' := primitiveCharacter_ne_one hχ1
  have hreal' := primitiveCharacter_sq_eq_one hreal
  have hM1 := conductor_ne_one_of_ne_one hχ1
  obtain ⟨hz, h0, hnear⟩ := isNearOne_of_region hχ1 hreal hs hreg
  obtain ⟨ρ, hρ⟩ := exists_zeroIndex_dirichletXi hprim hM1 hz h0
  refine ⟨?_, fun s' hs' hreg' ↦ ?_⟩
  · have := (Davenport.LFunction_exceptional_zero_real_simple hprim hχ1' hreal'
      (κ := 1 / 600) (by norm_num) (by norm_num) ρ (hρ ▸ hnear)).1
    rwa [hρ] at this
  · obtain ⟨hz', h0', hnear'⟩ := isNearOne_of_region hχ1 hreal hs' hreg'
    obtain ⟨ρ', hρ'⟩ := exists_zeroIndex_dirichletXi hprim hM1 hz' h0'
    have := Davenport.LFunction_exceptional_zero_unique hprim hχ1' (κ := 1 / 600) (by norm_num)
      (by norm_num) ρ' ρ (hρ' ▸ hnear') (hρ ▸ hnear)
    rw [← hρ, ← hρ', this]

/-- **Davenport, Ch. 14, p. 93 (row 14-11)**, real primitive characters: the zero in the region,
if any, is simple (as a zero of `ξ(s, χ)`). -/
@[kb "davenport1980" "Ch 14, p. 93"]
theorem Davenport.LFunction_zero_free_theorem_real_simple {χ : DirichletCharacter ℂ N}
    (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1) (hreal : χ ^ 2 = 1) (ρ : ZeroIndex (dirichletXi χ))
    (hreg : 1 - 1 / 16200 / logQT N ρ.val.im < ρ.val.re) :
    analyticOrderNatAt (dirichletXi χ) ρ.val = 1 := by
  have hN := two_le_of_ne_one hχ1
  have hz := (dirichletXi_zero_mem hχ (by rintro rfl; norm_num at hN) ρ).1
  obtain ⟨hz', h0, hnear⟩ := isNearOne_of_region hχ1 hreal hz hreg
  -- for primitive `χ` the conductor is `q` itself
  have hc : χ.conductor = N := hχ
  have hnear' : IsNearOne (1 / 600) N ρ.val := by
    unfold IsNearOne at hnear ⊢; rw [hc] at hnear; exact hnear
  exact (Davenport.LFunction_exceptional_zero_real_simple hχ hχ1 hreal (by norm_num)
    (by norm_num) ρ hnear').2

end NTKB
