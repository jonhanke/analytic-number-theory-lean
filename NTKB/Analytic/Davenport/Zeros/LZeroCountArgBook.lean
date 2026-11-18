/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Davenport.Zeros.ArgVariation
import NTKB.Analytic.Davenport.Zeros.LZeroCount

/-!
# `N(T, χ)` and `arg L(1/2 + iT, χ)` as changes of argument

**Davenport, Ch. 16, pp. 101-102 (rows 16-3, 16-4).** For `χ` primitive mod `q > 1` and `T > 0`
not the ordinate of a zero, `2π N(T, χ)` is the change of argument of `ξ(s, χ)` by continuous
variation around the rectangle with vertices `3/2 - iT, 3/2 + iT, -1/2 + iT, -1/2 - iT`
(`Davenport.two_pi_mul_LZeroCount_eq_argChange`); and the argument of `L(1/2 + iT, χ)` obtained by
continuous variation is `O(log q + log T)` (`Davenport.abs_argChange_LFunction_le`): along the
horizontal segment from `3/2 ± iT` to `1/2 ± iT`, and along the whole path
`3/2 → 3/2 ± iT → 1/2 ± iT`.

The library had these as integrals of the log-derivative (`Davenport.pi_mul_LZeroCount_eq`,
`Davenport.abs_integral_im_logDeriv_dirichletXi_le`); here they are in the book's wording. The map's paraphrase of 16-3 reads `2π[N(T, χ) + 1]` ("one trivial zero inside");
the function `ξ(s, χ)` has no zero outside the critical strip, so the count proved here (and in
`Davenport.rectIntegral_logDeriv_dirichletXi`) is `2π N(T, χ)`; the book's wording is to be checked when the source text is available.
-/

open Filter Topology Complex Set MeasureTheory DirichletCharacter
open scoped Real Interval

namespace NTKB

variable {N : ℕ} [NeZero N]

lemma im_intervalIntegral {f : ℝ → ℂ} {a b : ℝ} (hf : Continuous f) :
    (∫ x in a..b, f x).im = ∫ x in a..b, (f x).im := by
  rw [← Complex.imCLM_apply, ← ContinuousLinearMap.intervalIntegral_comp_comm _
    (hf.intervalIntegrable _ _)]
  rfl

/-- Change of argument along a vertical line. -/
lemma argChange_vert {F : ℂ → ℂ} (hF : Differentiable ℂ F) (c : ℂ) (a b : ℝ)
    (h0 : ∀ y : ℝ, F (c + y * I) ≠ 0) :
    argChange (fun y : ℝ ↦ F (c + y * I)) a b =
      (I * ∫ y in a..b, logDeriv F (c + y * I)).im := by
  have hd : ∀ y : ℝ, HasDerivAt (fun y : ℝ ↦ F (c + y * I)) (deriv F (c + y * I) * I) y := by
    intro y
    have h2 : HasDerivAt (fun y : ℝ ↦ c + (y : ℂ) * I) I y := by
      simpa using ((hasDerivAt_id y).ofReal_comp.mul_const I).const_add c
    exact HasDerivAt.comp y (hF (c + y * I)).hasDerivAt h2
  have hc : Continuous fun y : ℝ ↦ deriv F (c + y * I) * I := by
    have : Continuous (deriv F) :=
      continuous_iff_continuousAt.mpr fun z ↦ (hF.analyticAt z).deriv.continuousAt
    fun_prop
  rw [argChange_eq_im_integral (α := min a b - 1) (β := max a b + 1) (ψ := fun y : ℝ ↦ deriv F (c + y * I) * I)
    (by linarith) (by linarith) (fun t _ ↦ hd t) hc.continuousOn (fun t _ ↦ h0 t)]
  congr 2
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun t _ ↦ ?_
  simp only [logDeriv_apply]
  ring

/-- Change of argument along a horizontal line. -/
lemma argChange_horiz {F : ℂ → ℂ} (hF : Differentiable ℂ F) (c : ℂ) (a b : ℝ)
    (h0 : ∀ x : ℝ, F (x + c) ≠ 0) :
    argChange (fun x : ℝ ↦ F (x + c)) a b = (∫ x in a..b, logDeriv F (x + c)).im := by
  have hd : ∀ x : ℝ, HasDerivAt (fun x : ℝ ↦ F (x + c)) (deriv F (x + c)) x := by
    intro x
    have h2 : HasDerivAt (fun x : ℝ ↦ (x : ℂ) + c) 1 x := by
      simpa using (hasDerivAt_id x).ofReal_comp.add_const c
    have h3 := HasDerivAt.comp x (hF (x + c)).hasDerivAt h2
    rw [mul_one] at h3
    exact h3
  have hc : Continuous fun x : ℝ ↦ deriv F (x + c) := by
    have : Continuous (deriv F) :=
      continuous_iff_continuousAt.mpr fun z ↦ (hF.analyticAt z).deriv.continuousAt
    fun_prop
  rw [argChange_eq_im_integral (α := min a b - 1) (β := max a b + 1) (ψ := fun x : ℝ ↦ deriv F (x + c))
    (by linarith) (by linarith) (fun t _ ↦ hd t) hc.continuousOn (fun t _ ↦ h0 t)]
  simp only [logDeriv_apply]


lemma continuous_logDeriv_comp_of_ne {F : ℂ → ℂ} (hF : Differentiable ℂ F) {g : ℝ → ℂ}
    (hg : Continuous g) (h : ∀ y, F (g y) ≠ 0) : Continuous fun y ↦ logDeriv F (g y) :=
  continuous_iff_continuousAt.mpr fun y ↦
    (((hF.analyticAt (g y)).deriv.continuousAt.div (hF.analyticAt (g y)).continuousAt (h y)).comp
      hg.continuousAt)

/-- `L(s, χ) ≠ 0` on the lines `|Im s| = T` (`T > 0`) for non-ordinate `T`. -/
lemma LFunction_ne_zero_of_abs_im {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (hN : N ≠ 1)
    {T : ℝ} (hT : 0 < T) (hTz : ∀ ρ : ZeroIndex (dirichletXi χ), |ρ.val.im| ≠ T) {s : ℂ}
    (hs : |s.im| = T) : LFunction χ s ≠ 0 := by
  have hpar : ∀ m : ℕ, s + dirichletParity χ ≠ -(2 * m) := by
    intro m e
    have := congrArg Complex.im e
    simp [dirichletParity_im] at this
    rw [this] at hs; simp at hs; linarith
  have hG : Gammaℝ (s + dirichletParity χ) ≠ 0 := by
    rw [Ne, Gammaℝ_eq_zero_iff, not_exists]; exact hpar
  intro e
  apply dirichletXi_ne_zero_of_abs_im hχ hN hTz hs
  rw [dirichletXi_eq_mul_LFunction χ hN hG, e, mul_zero]

/-- The horizontal change of argument of `L` is `-∫ Im L'/L`, and `∫ Im L'/L` differs from
`∫ Im ξ'/ξ` by at most `3 + 2 log (T + 2)`. -/
lemma abs_integral_im_logDeriv_LFunction_sub_le {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive)
    (hN : N ≠ 1) {T : ℝ} (hT : 2 ≤ T) (hTz : ∀ ρ : ZeroIndex (dirichletXi χ), |ρ.val.im| ≠ T)
    {h : ℝ} (hh : |h| = T) :
    argChange (fun x : ℝ ↦ LFunction χ (x + h * I)) (3 / 2) (1 / 2) =
        (∫ x in (1 / 2 : ℝ)..3 / 2,
            ((logDeriv (dirichletXi χ) (x + h * I)).im - (logDeriv (LFunction χ) (x + h * I)).im)) -
          ∫ x in (1 / 2 : ℝ)..3 / 2, (logDeriv (dirichletXi χ) (x + h * I)).im ∧
      ∀ x ∈ Ι (1 / 2 : ℝ) (3 / 2),
        |(logDeriv (dirichletXi χ) (x + h * I)).im - (logDeriv (LFunction χ) (x + h * I)).im| ≤
          3 + 2 * Real.log (T + 2) := by
  have hT0 : 0 < T := by linarith
  have hχ1 := ne_one_of_isPrimitive hχ hN
  have hdL := differentiable_LFunction hχ1
  have hξ : ∀ x : ℝ, dirichletXi χ (x + h * I) ≠ 0 := fun x ↦
    dirichletXi_ne_zero_of_abs_im hχ hN hTz (by simpa using hh)
  have hL : ∀ x : ℝ, LFunction χ (x + h * I) ≠ 0 := fun x ↦
    LFunction_ne_zero_of_abs_im hχ hN hT0 hTz (by simpa using hh)
  have cξ : Continuous fun x : ℝ ↦ logDeriv (dirichletXi χ) (x + h * I) :=
    continuous_logDeriv_dirichletXi_comp hχ1 (by fun_prop) hξ
  have cL : Continuous fun x : ℝ ↦ logDeriv (LFunction χ) (x + h * I) :=
    continuous_logDeriv_comp_of_ne hdL (by fun_prop) hL
  constructor
  · have ia : IntervalIntegrable (fun x : ℝ ↦ (logDeriv (dirichletXi χ) (x + h * I)).im)
        MeasureTheory.volume (1 / 2) (3 / 2) :=
      (Complex.continuous_im.comp cξ).intervalIntegrable _ _
    have ic : IntervalIntegrable (fun x : ℝ ↦ (logDeriv (LFunction χ) (x + h * I)).im)
        MeasureTheory.volume (1 / 2) (3 / 2) :=
      (Complex.continuous_im.comp cL).intervalIntegrable _ _
    rw [argChange_horiz hdL (h * I) _ _ hL, intervalIntegral.integral_symm (1 / 2 : ℝ) (3 / 2),
      Complex.neg_im, im_intervalIntegral cL, intervalIntegral.integral_sub ia ic]
    ring
  · intro x hx
    have hx' : x ∈ Set.Ioc (1 / 2 : ℝ) (3 / 2) := by
      rwa [Set.uIoc_of_le (by norm_num)] at hx
    set s : ℂ := x + h * I with hs
    have hsre : s.re = x := by simp [s]
    have hsim : s.im = h := by simp [s]
    have hpar : ∀ m : ℕ, s + dirichletParity χ ≠ -(2 * m) := by
      intro m e
      have := congrArg Complex.im e
      simp [dirichletParity_im, hsim] at this
      rw [this] at hh; simp at hh; linarith
    have hxi := logDeriv_dirichletXi_eq hχ hN hpar (hL x) (hξ x)
    have hlN : Complex.log N = ((Real.log N : ℝ) : ℂ) := by
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_log (Nat.cast_nonneg N)]
    have hlπ : Complex.log π = ((Real.log π : ℝ) : ℂ) := by
      rw [← Complex.ofReal_log Real.pi_pos.le]
    have hdig := norm_digamma_parity_le χ (z := s) (by rw [hsre]; linarith [hx'.1])
      (by rw [hsre]; linarith [hx'.2]) (by rw [hsim, hh]; exact hT)
    rw [hsim] at hdig
    have hlog : Real.log (|h| + 2) = Real.log (T + 2) := by rw [hh]
    rw [hlog] at hdig
    have him : (logDeriv (dirichletXi χ) s).im - (logDeriv (LFunction χ) s).im =
        (Complex.digamma ((s + dirichletParity χ) / 2) / 2).im := by
      rw [hxi, hlN, hlπ, logDeriv_apply]
      simp only [Complex.sub_im, Complex.add_im, Complex.div_ofNat_im, Complex.ofReal_im]
      ring
    show |(logDeriv (dirichletXi χ) s).im - (logDeriv (LFunction χ) s).im| ≤ _
    rw [him]
    calc _ ≤ ‖Complex.digamma ((s + dirichletParity χ) / 2) / 2‖ := Complex.abs_im_le_norm _
      _ ≤ _ := by
        rw [norm_div, Complex.norm_ofNat]; linarith

/-- **Davenport, Ch. 16, p. 101 (row 16-3)**, the argument principle in the book's form: for `χ`
primitive mod `q > 1` and `T > 0` not an ordinate, `2π N(T, χ)` is the change of argument of
`ξ(s, χ)` by continuous variation around the rectangle `3/2 - iT → 3/2 + iT → -1/2 + iT →
-1/2 - iT → 3/2 - iT`, the sum of the changes along the four sides. -/
@[kb "davenport1980" "Ch 16, p. 101"]
theorem Davenport.two_pi_mul_LZeroCount_eq_argChange {χ : DirichletCharacter ℂ N}
    (hχ : χ.IsPrimitive) (hN : N ≠ 1) {T : ℝ} (hT : 0 < T)
    (hTz : ∀ ρ : ZeroIndex (dirichletXi χ), |ρ.val.im| ≠ T) :
    2 * π * LZeroCount χ T =
      argChange (fun y : ℝ ↦ dirichletXi χ (3 / 2 + y * I)) (-T) T +
      argChange (fun x : ℝ ↦ dirichletXi χ (x + T * I)) (3 / 2) (-1 / 2) +
      argChange (fun y : ℝ ↦ dirichletXi χ (-1 / 2 + y * I)) T (-T) +
      argChange (fun x : ℝ ↦ dirichletXi χ (x + (-T) * I)) (-1 / 2) (3 / 2) := by
  have hχ1 := ne_one_of_isPrimitive hχ hN
  have hd := differentiable_dirichletXi hχ1
  have hχ1' : χ⁻¹ ≠ 1 := fun h ↦ hχ1 (inv_eq_one.mp h)
  have hz1 : ∀ y : ℝ, dirichletXi χ (3 / 2 + y * I) ≠ 0 := fun y ↦
    dirichletXi_ne_zero_of_one_le_re hχ1 hN (by simp; norm_num)
  have hz2 : ∀ y : ℝ, dirichletXi χ (-1 / 2 + y * I) ≠ 0 := by
    intro y
    have : dirichletXi χ (-1 / 2 + y * I) = rootNumber χ * dirichletXi χ⁻¹ (1 - (-1 / 2 + y * I)) := by
      rw [← dirichletXi_one_sub hχ, sub_sub_cancel]
    rw [this]
    exact mul_ne_zero (rootNumber_ne_zero hχ)
      (dirichletXi_ne_zero_of_one_le_re hχ1' hN (by simp; norm_num))
  have hz3 : ∀ x : ℝ, dirichletXi χ (x + T * I) ≠ 0 := fun x ↦
    dirichletXi_ne_zero_of_abs_im hχ hN hTz (by simp [abs_of_pos hT])
  have hz4 : ∀ x : ℝ, dirichletXi χ (x + (-T : ℝ) * I) ≠ 0 := fun x ↦
    dirichletXi_ne_zero_of_abs_im hχ hN hTz (by simp [abs_of_pos hT])
  have hz4' : ∀ x : ℝ, dirichletXi χ (x + (-T) * I) ≠ 0 := fun x ↦ by
    simpa using hz4 x
  have c1 : Continuous fun y : ℝ ↦ logDeriv (dirichletXi χ) (3 / 2 + y * I) :=
    continuous_logDeriv_dirichletXi_comp hχ1 (by fun_prop) hz1
  have c2 : Continuous fun y : ℝ ↦ logDeriv (dirichletXi χ) (-1 / 2 + y * I) :=
    continuous_logDeriv_dirichletXi_comp hχ1 (by fun_prop) hz2
  have c3 : Continuous fun x : ℝ ↦ logDeriv (dirichletXi χ) (x + T * I) :=
    continuous_logDeriv_dirichletXi_comp hχ1 (by fun_prop) hz3
  have c4 : Continuous fun x : ℝ ↦ logDeriv (dirichletXi χ) (x + (-T) * I) :=
    continuous_logDeriv_dirichletXi_comp hχ1 (by fun_prop) hz4'
  rw [argChange_vert hd _ _ _ hz1, argChange_horiz hd _ _ _ hz3, argChange_vert hd _ _ _ hz2,
    argChange_horiz hd _ _ _ hz4']
  have h1 := Davenport.rectIntegral_logDeriv_dirichletXi hχ hN hT hTz
  have e1 : ((-1 / 2 : ℂ) - T * I).re = -1 / 2 := by simp
  have e2 : ((-1 / 2 : ℂ) - T * I).im = -T := by simp
  have e3 : ((3 / 2 : ℂ) + T * I).re = 3 / 2 := by simp
  have e4 : ((3 / 2 : ℂ) + T * I).im = T := by simp
  simp only [rectIntegral, e1, e2, e3, e4] at h1
  push_cast at h1
  have h2 := congrArg Complex.im h1
  rw [intervalIntegral.integral_symm (-1 / 2 : ℝ) (3 / 2), intervalIntegral.integral_symm (-T) T]
  simp only [Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.neg_im] at h2 ⊢
  simp at h2 ⊢
  linarith

/-- **Davenport, Ch. 16, p. 102 (row 16-4)**: there is an absolute `A > 0` such that for `χ`
primitive mod `q > 1`, `T ≥ 2` not an ordinate and `h = ±T`, the argument of `L(1/2 + ih, χ)`
obtained by continuous variation is `O(log q + log T)`: both its change along the horizontal
segment from `3/2 + ih` to `1/2 + ih`, and its change along the path `3/2 → 3/2 + ih → 1/2 + ih`,
are at most `A (log q + log(T + 2))` in absolute value. -/
@[kb "davenport1980" "Ch 16, p. 102"]
theorem Davenport.abs_argChange_LFunction_le :
    ∃ A : ℝ, 0 < A ∧ ∀ {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}, χ.IsPrimitive → N ≠ 1 →
      ∀ T : ℝ, 2 ≤ T → (∀ ρ : ZeroIndex (dirichletXi χ), |ρ.val.im| ≠ T) →
      ∀ h : ℝ, |h| = T →
      |argChange (fun x : ℝ ↦ LFunction χ (x + h * I)) (3 / 2) (1 / 2)| ≤
          A * (Real.log N + Real.log (T + 2)) ∧
      |argChange (fun y : ℝ ↦ LFunction χ (3 / 2 + y * I)) 0 h +
          argChange (fun x : ℝ ↦ LFunction χ (x + h * I)) (3 / 2) (1 / 2)| ≤
          A * (Real.log N + Real.log (T + 2)) := by
  obtain ⟨A₀, hA₀, h₀⟩ := Davenport.abs_integral_im_logDeriv_dirichletXi_le
  obtain ⟨C, hC, hZ⟩ := exists_norm_integral_logDeriv_LFunction_le
  refine ⟨A₀ + 5 + C, by positivity, fun {N} _ {χ} hχ hN T hT hTz h hh ↦ ?_⟩
  have hχ1 := ne_one_of_isPrimitive hχ hN
  have hT0 : 0 < T := by linarith
  have hlog4 : 1 ≤ Real.log (T + 2) := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9; linarith
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg hN1
  obtain ⟨he, hb⟩ := abs_integral_im_logDeriv_LFunction_sub_le hχ hN hT hTz hh
  have h1 := h₀ hχ hN T hT hTz h hh
  have h2 : |∫ x in (1 / 2 : ℝ)..3 / 2,
      ((logDeriv (dirichletXi χ) (x + h * I)).im - (logDeriv (LFunction χ) (x + h * I)).im)| ≤
        3 + 2 * Real.log (T + 2) := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (1 / 2 : ℝ)) (b := 3 / 2)
      (f := fun x : ℝ ↦
        ((logDeriv (dirichletXi χ) (x + h * I)).im - (logDeriv (LFunction χ) (x + h * I)).im))
      (C := 3 + 2 * Real.log (T + 2)) (fun x hx ↦ by simpa using hb x hx)
    rw [Real.norm_eq_abs, show |(3 / 2 : ℝ) - 1 / 2| = 1 by norm_num, mul_one] at this
    exact this
  have hH : |argChange (fun x : ℝ ↦ LFunction χ (x + h * I)) (3 / 2) (1 / 2)| ≤
      (A₀ + 5) * (Real.log N + Real.log (T + 2)) := by
    rw [he]
    calc _ ≤ |∫ x in (1 / 2 : ℝ)..3 / 2,
          ((logDeriv (dirichletXi χ) (x + h * I)).im - (logDeriv (LFunction χ) (x + h * I)).im)| +
          |∫ x in (1 / 2 : ℝ)..3 / 2, (logDeriv (dirichletXi χ) (x + h * I)).im| := abs_sub _ _
      _ ≤ _ := by nlinarith
  have hV : |argChange (fun y : ℝ ↦ LFunction χ (3 / 2 + y * I)) 0 h| ≤ C := by
    have hL : ∀ y : ℝ, LFunction χ (3 / 2 + y * I) ≠ 0 := fun y ↦
      LFunction_ne_zero_of_one_le_re χ (Or.inl hχ1) (by simp; norm_num)
    rw [argChange_vert (differentiable_LFunction hχ1) _ _ _ hL]
    have : (I * ∫ y in (0 : ℝ)..h, logDeriv (LFunction χ) (3 / 2 + y * I)).im =
        (∫ y in (0 : ℝ)..h, logDeriv (LFunction χ) (3 / 2 + y * I)).re := by simp
    rw [this]
    refine (Complex.abs_re_le_norm _).trans ?_
    simpa [logDeriv_apply] using hZ χ 0 h
  refine ⟨hH.trans (by nlinarith), ?_⟩
  calc _ ≤ |argChange (fun y : ℝ ↦ LFunction χ (3 / 2 + y * I)) 0 h| +
        |argChange (fun x : ℝ ↦ LFunction χ (x + h * I)) (3 / 2) (1 / 2)| := abs_add_le _ _
    _ ≤ _ := by nlinarith

end NTKB
