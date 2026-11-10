/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Davenport.Zeros.LContour
import NTKB.Analytic.Davenport.Zeros.ZeroCountArg
import NTKB.Analytic.Davenport.Hadamard.XiCharConj

/-!
# The argument principle for `N(T, χ)`

**Davenport, Ch. 16, p. 101 (row 16-3).** For `χ` primitive mod `q > 1` and `T > 0` not an
ordinate, the integral of `ξ'/ξ(s, χ)` around the rectangle with vertices `-1/2 ± iT`,
`3/2 ± iT` is `2πi N(T, χ)`, where `N(T, χ)` is the number of zeros of `L(s, χ)` (with
multiplicity) with `0 < β < 1`, `|γ| < T` (`Davenport.rectIntegral_logDeriv_dirichletXi`).
(Davenport's `ξ(s, χ)` has no zero at `s = 0`, so the count is `N(T, χ)` exactly; his `+1` in
16-3 refers to a variant contour.)

Here `L(s, χ)` is not symmetric under `s ↦ s̄`, but `ξ(1 - s̄, χ) = ε(χ) conj ξ(s, χ)`, so
`ξ'/ξ(1 - s̄, χ) = -conj ξ'/ξ(s, χ)` (`logDeriv_dirichletXi_reflect`), and
`π N(T, χ) = ∫_{-T}^T Re ξ'/ξ(3/2 + iy, χ) dy + ∫_{1/2}^{3/2} (Im ξ'/ξ(x - iT, χ) - Im ξ'/ξ(x + iT, χ)) dx`
(`Davenport.pi_mul_LZeroCount_eq`).
-/

open Filter Topology Complex Set MeasureTheory DirichletCharacter
open scoped Real Interval ComplexConjugate

namespace NTKB

variable {N : ℕ} [NeZero N]

/-- Davenport's `N(T, χ)` (Ch. 16, p. 101): the number of zeros of `L(s, χ)` in `0 < σ < 1`
with `|γ| < T`, counted with multiplicity. -/
noncomputable def LZeroCount (χ : DirichletCharacter ℂ N) (T : ℝ) : ℕ :=
  Nat.card {ρ : ZeroIndex (dirichletXi χ) // |ρ.val.im| < T}

lemma LZeroCount_eq_card {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (hN : N ≠ 1) (T : ℝ) :
    LZeroCount χ T = (zerosBelowL hχ hN T).card := by
  have h : ∀ ρ : ZeroIndex (dirichletXi χ), |ρ.val.im| < T ↔ ρ ∈ zerosBelowL hχ hN T :=
    fun ρ ↦ mem_zerosBelowL.symm
  rw [LZeroCount, Nat.card_congr (Equiv.subtypeEquivRight h), Nat.card_eq_finsetCard]

lemma eventually_ne_zero_of_differentiable {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hf0 : f 0 ≠ 0)
    (p : ℂ) : ∀ᶠ s : ℂ in 𝓝[≠] p, f s ≠ 0 := by
  have han : AnalyticOnNhd ℂ f univ := fun z _ ↦ hf.analyticAt z
  rcases (han p (mem_univ p)).eventually_eq_zero_or_eventually_ne_zero with h | h
  · have := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (mem_univ p) h
      (mem_univ 0)
    exact absurd this hf0
  · exact h

lemma analyticOrderAt_ne_top_of_differentiable {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hf0 : f 0 ≠ 0) (z : ℂ) : analyticOrderAt f z ≠ ⊤ := by
  have han : AnalyticOnNhd ℂ f univ := fun w _ ↦ hf.analyticAt w
  exact han.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ (mem_univ 0)
    (mem_univ z) (by
      rw [(hf.analyticAt 0).analyticOrderAt_eq_zero.mpr hf0]
      exact ENat.zero_ne_top)

/-- `ξ'/ξ(1 - w, χ) = -ξ'/ξ(w, χ̄)`. -/
lemma logDeriv_dirichletXi_one_sub {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive)
    (hN : N ≠ 1) (w : ℂ) :
    logDeriv (dirichletXi χ) (1 - w) = -logDeriv (dirichletXi χ⁻¹) w := by
  have hχ1 := ne_one_of_isPrimitive hχ hN
  have hχ1' : χ⁻¹ ≠ 1 := fun h ↦ hχ1 (inv_eq_one.mp h)
  have hF : (fun w ↦ dirichletXi χ (1 - w)) = fun w ↦ rootNumber χ * dirichletXi χ⁻¹ w :=
    funext (dirichletXi_one_sub hχ)
  have h1 : HasDerivAt (fun w ↦ dirichletXi χ (1 - w))
      (deriv (dirichletXi χ) (1 - w) * (-1)) w :=
    (differentiable_dirichletXi hχ1 (1 - w)).hasDerivAt.comp w ((hasDerivAt_id w).const_sub 1)
  rw [hF] at h1
  have h2 : HasDerivAt (fun w ↦ rootNumber χ * dirichletXi χ⁻¹ w)
      (rootNumber χ * deriv (dirichletXi χ⁻¹) w) w :=
    (differentiable_dirichletXi hχ1' w).hasDerivAt.const_mul _
  have hu := h1.unique h2
  have hε := rootNumber_ne_zero hχ
  have e : deriv (dirichletXi χ) (1 - w) = -(rootNumber χ * deriv (dirichletXi χ⁻¹) w) := by
    linear_combination -hu
  rw [logDeriv_apply, logDeriv_apply, e, dirichletXi_one_sub hχ]
  by_cases h0 : dirichletXi χ⁻¹ w = 0
  · simp [h0]
  · field_simp

/-- `ξ'/ξ(w, χ̄) = conj ξ'/ξ(w̄, χ)`. -/
lemma logDeriv_dirichletXi_inv {χ : DirichletCharacter ℂ N} (hχ1 : χ ≠ 1) (hN : N ≠ 1) (w : ℂ) :
    logDeriv (dirichletXi χ⁻¹) w = conj (logDeriv (dirichletXi χ) (conj w)) := by
  have h := (differentiable_dirichletXi hχ1 (conj w)).hasDerivAt.conj_conj
  rw [← dirichletXi_inv_conj hχ1 hN, conj_conj] at h
  rw [logDeriv_apply, logDeriv_apply, h.deriv, dirichletXi_inv_conj hχ1 hN]
  simp [map_div₀]

/-- **The reflection `s ↦ 1 - s̄`**: `ξ'/ξ(1 - s̄, χ) = -conj ξ'/ξ(s, χ)`. -/
lemma logDeriv_dirichletXi_reflect {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive)
    (hN : N ≠ 1) (s : ℂ) :
    logDeriv (dirichletXi χ) (1 - conj s) = -conj (logDeriv (dirichletXi χ) s) := by
  rw [logDeriv_dirichletXi_one_sub hχ hN, logDeriv_dirichletXi_inv (ne_one_of_isPrimitive hχ hN) hN,
    conj_conj]

lemma dirichletXi_ne_zero_of_abs_im {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (hN : N ≠ 1)
    {T : ℝ} (hTz : ∀ ρ : ZeroIndex (dirichletXi χ), |ρ.val.im| ≠ T) {s : ℂ} (hs : |s.im| = T) :
    dirichletXi χ s ≠ 0 := by
  intro h
  obtain ⟨ρ, hρ⟩ := exists_zeroIndex_val_eq
    (differentiable_dirichletXi (ne_one_of_isPrimitive hχ hN)) (dirichletXi_zero_ne_zero hχ hN) h
  exact hTz ρ (hρ ▸ hs)

lemma continuousAt_logDeriv_dirichletXi {χ : DirichletCharacter ℂ N} (hχ1 : χ ≠ 1) {p : ℂ}
    (hp : dirichletXi χ p ≠ 0) : ContinuousAt (logDeriv (dirichletXi χ)) p := by
  have han := (differentiable_dirichletXi hχ1).analyticAt p
  exact han.deriv.continuousAt.div han.continuousAt hp

lemma continuous_logDeriv_dirichletXi_comp {χ : DirichletCharacter ℂ N} (hχ1 : χ ≠ 1)
    {g : ℝ → ℂ} (hg : Continuous g) (h : ∀ y, dirichletXi χ (g y) ≠ 0) :
    Continuous fun y ↦ logDeriv (dirichletXi χ) (g y) :=
  continuous_iff_continuousAt.mpr fun y ↦
    (continuousAt_logDeriv_dirichletXi hχ1 (h y)).comp hg.continuousAt

/-- **Davenport, Ch. 16, p. 101 (row 16-3)**, the argument principle: for primitive `χ` mod
`q > 1` and `T > 0` not an ordinate, `∮ ξ'/ξ(s, χ) ds = 2πi N(T, χ)` around `[-1/2, 3/2] × [-T, T]`. -/
@[kb "davenport1980" "Ch 16, p. 101"]
theorem Davenport.rectIntegral_logDeriv_dirichletXi {χ : DirichletCharacter ℂ N}
    (hχ : χ.IsPrimitive) (hN : N ≠ 1) {T : ℝ} (hT : 0 < T)
    (hTz : ∀ ρ : ZeroIndex (dirichletXi χ), |ρ.val.im| ≠ T) :
    rectIntegral (logDeriv (dirichletXi χ)) (-1 / 2 - T * I) (3 / 2 + T * I) =
      2 * π * I * LZeroCount χ T := by
  classical
  have hχ1 := ne_one_of_isPrimitive hχ hN
  have hd := differentiable_dirichletXi hχ1
  have h0 := dirichletXi_zero_ne_zero hχ hN
  set z₀ : ℂ := -1 / 2 - T * I with hz₀
  set w₀ : ℂ := 3 / 2 + T * I with hw₀
  have hz₀re : z₀.re = -1 / 2 := by simp [z₀]
  have hz₀im : z₀.im = -T := by simp [z₀]
  have hw₀re : w₀.re = 3 / 2 := by simp [w₀]
  have hw₀im : w₀.im = T := by simp [w₀]
  set V : Finset ℂ := (zerosBelowL hχ hN T).image ZeroIndex.val with hV
  have hVre : ∀ p ∈ V, 0 < p.re ∧ p.re < 1 ∧ |p.im| < T := by
    intro p hp
    obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.mp hp
    exact ⟨(dirichletXi_zero_mem hχ hN ρ).2.1, (dirichletXi_zero_mem hχ hN ρ).2.2,
      mem_zerosBelowL.mp hρ⟩
  set U : Set ℂ := {s | dirichletXi χ s ≠ 0} ∪ ↑V with hU
  have hUopen : IsOpen U := by
    rw [isOpen_iff_mem_nhds]
    intro s hs
    rcases hs with hs | hs
    · exact mem_of_superset ((isOpen_ne_fun hd.continuous continuous_const).mem_nhds hs)
        subset_union_left
    · have h := eventually_ne_zero_of_differentiable hd h0 s
      rw [eventually_nhdsWithin_iff] at h
      filter_upwards [h] with x hx
      by_cases hxs : x = s
      · right; rw [hxs]; exact hs
      · left; exact hx hxs
  have hRU : [[z₀.re, w₀.re]] ×ℂ [[z₀.im, w₀.im]] ⊆ U := by
    intro s hs
    rw [mem_reProdIm, hz₀re, hw₀re, hz₀im, hw₀im, uIcc_of_le (by norm_num),
      uIcc_of_le (by linarith)] at hs
    by_cases h : dirichletXi χ s = 0
    · right
      obtain ⟨ρ, hρ⟩ := exists_zeroIndex_val_eq hd h0 h
      refine Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨ρ, mem_zerosBelowL.mpr ?_, hρ⟩)
      have h1 : |ρ.val.im| ≤ T := by rw [hρ]; exact abs_le.mpr ⟨hs.2.1, hs.2.2⟩
      exact lt_of_le_of_ne h1 (hTz ρ)
    · left; exact h
  have hPin : ∀ p ∈ V, p ∈ Ioo z₀.re w₀.re ×ℂ Ioo z₀.im w₀.im := by
    intro p hp
    rw [mem_reProdIm, hz₀re, hw₀re, hz₀im, hw₀im]
    obtain ⟨h1, h2, h3⟩ := hVre p hp
    rw [abs_lt] at h3
    exact ⟨⟨by linarith, by linarith⟩, h3⟩
  have hdiff : DifferentiableOn ℂ (logDeriv (dirichletXi χ)) (U \ ↑V) := by
    intro s ⟨hsU, hsV⟩
    have hs : dirichletXi χ s ≠ 0 := by
      rcases hsU with h | h
      · exact h
      · exact absurd h hsV
    have han := hd.analyticAt s
    rw [show logDeriv (dirichletXi χ) = fun w ↦ deriv (dirichletXi χ) w / dirichletXi χ w from rfl]
    exact (han.deriv.differentiableAt.div han.differentiableAt hs).differentiableWithinAt
  set r : ℂ → ℂ := fun p ↦ (analyticOrderNatAt (dirichletXi χ) p : ℂ) with hr
  have hres : ∀ p ∈ V, ∃ V' ∈ 𝓝 p, BddAbove (norm ∘ (fun s ↦ logDeriv (dirichletXi χ) s -
      r p / (s - p)) '' (V' \ {p})) := by
    intro p _
    exact bddNear_logDeriv_sub (hd.analyticAt p)
      (Nat.cast_analyticOrderNatAt (analyticOrderAt_ne_top_of_differentiable hd h0 p)).symm
  have hrect := rectIntegral_eq_sum_residues (z := z₀) (w := w₀) (by rw [hz₀re, hw₀re]; norm_num)
    (by rw [hz₀im, hw₀im]; linarith) hUopen hRU r V hPin (logDeriv (dirichletXi χ)) hdiff hres
  rw [hrect, LZeroCount_eq_card hχ hN]
  congr 1
  rw [Finset.card_eq_sum_card_fiberwise (f := ZeroIndex.val) (t := V)
    (fun ρ hρ ↦ Finset.mem_image_of_mem _ hρ)]
  push_cast
  refine Finset.sum_congr rfl fun p hp ↦ ?_
  rw [hr]
  simp only
  rw [← card_fiber_zerosBelowL (hVre p hp).2.2]

/-- The horizontal side at height `h`: `∫_{-1/2}^{3/2} ξ'/ξ(x + ih, χ) dx = 2i ∫_{1/2}^{3/2} Im ξ'/ξ(x + ih, χ) dx`. -/
lemma integral_logDeriv_dirichletXi_horiz {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive)
    (hN : N ≠ 1) {h : ℝ} (hh : ∀ x : ℝ, dirichletXi χ (x + h * I) ≠ 0) :
    ∫ x in (-1 / 2 : ℝ)..3 / 2, logDeriv (dirichletXi χ) (x + h * I) =
      2 * I * ((∫ x in (1 / 2 : ℝ)..3 / 2, (logDeriv (dirichletXi χ) (x + h * I)).im : ℝ) : ℂ) := by
  have hχ1 := ne_one_of_isPrimitive hχ hN
  set F : ℝ → ℂ := fun x ↦ logDeriv (dirichletXi χ) (x + h * I) with hF
  have hFc : Continuous F := continuous_logDeriv_dirichletXi_comp hχ1 (by fun_prop) hh
  have hsym : ∀ x : ℝ, F x = -conj (F (1 - x)) := by
    intro x
    simp only [hF]
    rw [← logDeriv_dirichletXi_reflect hχ hN]
    congr 1
    apply Complex.ext <;> simp
  rw [← intervalIntegral.integral_add_adjacent_intervals (hFc.intervalIntegrable (-1 / 2) (1 / 2))
    (hFc.intervalIntegrable (1 / 2) (3 / 2))]
  have h1 : ∫ x in (-1 / 2 : ℝ)..1 / 2, F x = ∫ x in (1 / 2 : ℝ)..3 / 2, -conj (F x) := by
    have : ∫ x in (-1 / 2 : ℝ)..1 / 2, F x = ∫ x in (-1 / 2 : ℝ)..1 / 2, -conj (F (1 - x)) :=
      intervalIntegral.integral_congr fun x _ ↦ hsym x
    rw [this, intervalIntegral.integral_comp_sub_left (fun x ↦ -conj (F x))]
    norm_num
  rw [h1, ← intervalIntegral.integral_add (f := fun x ↦ -conj (F x)) (g := F)
    ((Complex.continuous_conj.comp hFc).neg.intervalIntegrable _ _) (hFc.intervalIntegrable _ _)]
  have h2 : ∫ x in (1 / 2 : ℝ)..3 / 2, (-conj (F x) + F x) =
      ∫ x in (1 / 2 : ℝ)..3 / 2, ((2 * (F x).im : ℝ) : ℂ) * I := by
    refine intervalIntegral.integral_congr fun x _ ↦ ?_
    rw [← Complex.sub_conj]; ring
  rw [h2, intervalIntegral.integral_mul_const, intervalIntegral.integral_ofReal,
    intervalIntegral.integral_const_mul]
  push_cast
  ring

/-- **Davenport, Ch. 16, p. 101 (row 16-3)**: for primitive `χ` mod `q > 1` and `T > 0` not an
ordinate, `π N(T, χ) = ∫_{-T}^T Re ξ'/ξ(3/2 + iy, χ) dy +
∫_{1/2}^{3/2} (Im ξ'/ξ(x - iT, χ) - Im ξ'/ξ(x + iT, χ)) dx`. -/
@[kb "davenport1980" "Ch 16, p. 101"]
theorem Davenport.pi_mul_LZeroCount_eq {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive)
    (hN : N ≠ 1) {T : ℝ} (hT : 0 < T) (hTz : ∀ ρ : ZeroIndex (dirichletXi χ), |ρ.val.im| ≠ T) :
    π * LZeroCount χ T =
      (∫ y in (-T)..T, (logDeriv (dirichletXi χ) (3 / 2 + y * I)).re) +
        ((∫ x in (1 / 2 : ℝ)..3 / 2, (logDeriv (dirichletXi χ) (x + (-T) * I)).im) -
          ∫ x in (1 / 2 : ℝ)..3 / 2, (logDeriv (dirichletXi χ) (x + T * I)).im) := by
  have hχ1 := ne_one_of_isPrimitive hχ hN
  have h1 := Davenport.rectIntegral_logDeriv_dirichletXi hχ hN hT hTz
  have e1 : ((-1 / 2 : ℂ) - T * I).re = -1 / 2 := by simp
  have e2 : ((-1 / 2 : ℂ) - T * I).im = -T := by simp
  have e3 : ((3 / 2 : ℂ) + T * I).re = 3 / 2 := by simp
  have e4 : ((3 / 2 : ℂ) + T * I).im = T := by simp
  simp only [rectIntegral, e1, e2, e3, e4] at h1
  have hT1 : ∀ x : ℝ, dirichletXi χ (x + T * I) ≠ 0 := fun x ↦
    dirichletXi_ne_zero_of_abs_im hχ hN hTz (by simp [abs_of_pos hT])
  have hT2 : ∀ x : ℝ, dirichletXi χ (x + ((-T : ℝ) : ℂ) * I) ≠ 0 := fun x ↦
    dirichletXi_ne_zero_of_abs_im hχ hN hTz (by simp [abs_of_pos hT])
  rw [integral_logDeriv_dirichletXi_horiz hχ hN hT1,
    integral_logDeriv_dirichletXi_horiz hχ hN hT2] at h1
  -- the vertical sides
  set g : ℝ → ℂ := fun y ↦ logDeriv (dirichletXi χ) (3 / 2 + y * I) with hg
  have hgc : Continuous g := continuous_logDeriv_dirichletXi_comp hχ1 (by fun_prop) fun y ↦
    dirichletXi_ne_zero_of_one_le_re hχ1 hN (by norm_num)
  have hleft : ∫ y in (-T)..T, logDeriv (dirichletXi χ) (((-1 / 2 : ℝ) : ℂ) + y * I) =
      ∫ y in (-T)..T, -conj (g y) := by
    refine intervalIntegral.integral_congr fun y _ ↦ ?_
    simp only [hg]
    rw [← logDeriv_dirichletXi_reflect hχ hN]
    congr 1
    apply Complex.ext <;> simp [map_ofNat] <;> norm_num
  have hright : ∫ y in (-T)..T, logDeriv (dirichletXi χ) (((3 / 2 : ℝ) : ℂ) + y * I) =
      ∫ y in (-T)..T, g y := by
    refine intervalIntegral.integral_congr fun y _ ↦ ?_
    simp only [hg]
    push_cast; rfl
  rw [hleft, hright, intervalIntegral.integral_neg] at h1
  have hV : (∫ y in (-T)..T, g y) + ∫ y in (-T)..T, conj (g y) =
      ((2 * ∫ y in (-T)..T, (g y).re : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_add (f := g) (g := fun y ↦ conj (g y))
      (hgc.intervalIntegrable _ _) ((Complex.continuous_conj.comp hgc).intervalIntegrable _ _)]
    have : ∫ y in (-T)..T, (g y + conj (g y)) = ∫ y in (-T)..T, ((2 * (g y).re : ℝ) : ℂ) :=
      intervalIntegral.integral_congr fun y _ ↦ Complex.add_conj _
    rw [this, intervalIntegral.integral_ofReal, intervalIntegral.integral_const_mul]
  have h3 := congrArg Complex.im h1
  have hV' := congrArg Complex.re hV
  simp only [sub_im, add_im, mul_im, I_re, I_im, ofReal_re, ofReal_im, re_ofNat, im_ofNat,
    natCast_re, natCast_im, mul_zero, zero_mul, add_zero, sub_zero, zero_add, mul_one, neg_im,
    mul_re, neg_re, sub_re, add_re, ofReal_re] at h3 hV'
  have hre : (∫ y in (-T)..T, g y).re = ∫ y in (-T)..T, (g y).re := by
    rw [← Complex.reCLM_apply, ← ContinuousLinearMap.intervalIntegral_comp_comm]
    · rfl
    · exact hgc.intervalIntegrable _ _
  have hcre : (∫ y in (-T)..T, conj (g y)).re = ∫ y in (-T)..T, (g y).re := by
    rw [← Complex.reCLM_apply, ← ContinuousLinearMap.intervalIntegral_comp_comm]
    · simp
    · exact (Complex.continuous_conj.comp hgc).intervalIntegrable _ _
  push_cast at h3
  nlinarith [h3, hre, hcre, Real.pi_pos]

end NTKB
