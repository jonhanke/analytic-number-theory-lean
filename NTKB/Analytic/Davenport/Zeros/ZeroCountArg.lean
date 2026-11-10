/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Davenport.Zeros.ExplicitContour
import NTKB.Analytic.Davenport.Hadamard.XiCharConj
import NTKB.Analytic.Davenport.Hadamard.XiSum
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Analysis.Calculus.Deriv.Star

/-!
# The argument principle for `N(T)`

**Davenport, Ch. 15, p. 97 (rows 15-1, 15-2).** For `T > 0` not the ordinate of a zero, the
integral of `ξ'/ξ` around the rectangle with vertices `-1 - iT`, `2 - iT`, `2 + iT`, `-1 + iT` is
`2πi` times the number of zeros (with multiplicity) with `|γ| < T`
(`Davenport.rectIntegral_logDeriv_riemannXi`). Davenport writes this as a change of argument of
`ξ`; we keep the integral of `ξ'/ξ`, whose imaginary part is that change of argument.

By `ξ(s) = ξ(1 - s)` and `ξ(s̄) = conj ξ(s)`, the integral is four times the integral along
`2 → 2 + iT → 1/2 + iT` (`Davenport.rectIntegral_logDeriv_riemannXi_eq`), so that
`π N(T) = ∫_0^T Re ξ'/ξ(2 + iy) dy - ∫_{1/2}^2 Im ξ'/ξ(x + iT) dx - π N₀/2`
(`Davenport.pi_mul_zetaZeroCount_eq`), with `N₀` the (fixed, finite) number of real zeros of `ξ`.
-/

open Filter Topology Complex Set MeasureTheory
open scoped Real Interval ComplexConjugate

namespace NTKB

/-- `ξ(s̄) = conj ξ(s)`. -/
lemma riemannXi_conj (s : ℂ) : riemannXi (conj s) = conj (riemannXi s) := by
  by_cases h0 : s = 0
  · subst h0; simp [map_ofNat]
  by_cases h1 : s = 1
  · subst h1; simp [map_ofNat]
  have h0' : conj s ≠ 0 := by simpa using h0
  have h1' : conj s ≠ 1 := fun h ↦ h1 (by simpa using congrArg conj h)
  rw [riemannXi_eq_completed h0' h1', riemannXi_eq_completed h0 h1, completedRiemannZeta_conj,
    map_mul, map_div₀, map_mul, map_sub, map_one, map_ofNat]

lemma analyticOrderAt_riemannXi_ne_top (z : ℂ) : analyticOrderAt riemannXi z ≠ ⊤ := by
  have han : AnalyticOnNhd ℂ riemannXi univ := fun w _ ↦ differentiable_riemannXi.analyticAt w
  exact han.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ (mem_univ 0)
    (mem_univ z) (by
      rw [(differentiable_riemannXi.analyticAt 0).analyticOrderAt_eq_zero.mpr (by simp)]
      exact ENat.zero_ne_top)

lemma conj_comp_riemannXi_comp_conj : (conj ∘ riemannXi ∘ conj) = riemannXi :=
  funext fun w ↦ by simp [riemannXi_conj]

/-- `ξ` vanishes to the same order at `z` and at `z̄`. -/
lemma analyticOrderNatAt_riemannXi_conj (z : ℂ) :
    analyticOrderNatAt riemannXi (conj z) = analyticOrderNatAt riemannXi z := by
  have := analyticOrderAt_conj_conj (differentiable_riemannXi.analyticAt z)
    (analyticOrderAt_riemannXi_ne_top z)
  rw [conj_comp_riemannXi_comp_conj] at this
  simp only [analyticOrderNatAt, this]

/-- Complex conjugation as an equivalence of `ℂ`. -/
def conjEquiv : ℂ ≃ ℂ := ⟨conj, conj, fun z ↦ conj_conj z, fun z ↦ conj_conj z⟩

/-- The involution `ρ ↦ ρ̄` of the zeros of `ξ` (with multiplicity). -/
noncomputable def riemannXiZeroConj : ZeroIndex riemannXi ≃ ZeroIndex riemannXi :=
  Equiv.sigmaCongr conjEquiv fun z ↦ finCongr (analyticOrderNatAt_riemannXi_conj z).symm

@[simp] lemma riemannXiZeroConj_val (ρ : ZeroIndex riemannXi) :
    (riemannXiZeroConj ρ).val = conj ρ.val := rfl

lemma deriv_riemannXi_one_sub (s : ℂ) : deriv riemannXi (1 - s) = -deriv riemannXi s := by
  have h := (differentiable_riemannXi (1 - s)).hasDerivAt
  have h2 : HasDerivAt (fun w ↦ riemannXi (1 - w)) (deriv riemannXi (1 - s) * (-1)) s :=
    h.comp s ((hasDerivAt_id s).const_sub 1)
  have h3 : (fun w ↦ riemannXi (1 - w)) = riemannXi := funext riemannXi_one_sub
  rw [h3] at h2
  rw [h2.deriv]; ring

/-- `ξ'/ξ(1 - s) = -ξ'/ξ(s)`. -/
lemma logDeriv_riemannXi_one_sub (s : ℂ) :
    logDeriv riemannXi (1 - s) = -logDeriv riemannXi s := by
  rw [logDeriv_apply, logDeriv_apply, deriv_riemannXi_one_sub, riemannXi_one_sub, neg_div]

lemma deriv_riemannXi_conj (s : ℂ) : deriv riemannXi (conj s) = conj (deriv riemannXi s) := by
  have h := (differentiable_riemannXi s).hasDerivAt.conj_conj
  rw [conj_comp_riemannXi_comp_conj] at h
  exact h.deriv

/-- `ξ'/ξ(s̄) = conj ξ'/ξ(s)`. -/
lemma logDeriv_riemannXi_conj (s : ℂ) :
    logDeriv riemannXi (conj s) = conj (logDeriv riemannXi s) := by
  rw [logDeriv_apply, logDeriv_apply, deriv_riemannXi_conj, riemannXi_conj, map_div₀]

lemma riemannXi_ne_zero_of_abs_im {T : ℝ} (hTz : ∀ ρ : ZeroIndex riemannXi, |ρ.val.im| ≠ T)
    {s : ℂ} (hs : |s.im| = T) : riemannXi s ≠ 0 := by
  intro h
  obtain ⟨ρ, hρ⟩ := exists_zeroIndex_val_eq differentiable_riemannXi (by simp) h
  exact hTz ρ (hρ ▸ hs)

lemma continuous_logDeriv_riemannXi_comp {g : ℝ → ℂ} (hg : Continuous g)
    (h : ∀ y, riemannXi (g y) ≠ 0) : Continuous fun y ↦ logDeriv riemannXi (g y) :=
  continuous_iff_continuousAt.mpr fun y ↦
    (continuousAt_logDeriv_riemannXi (h y)).comp hg.continuousAt

lemma riemannXi_two_add_ne_zero (y : ℝ) : riemannXi (2 + y * I) ≠ 0 :=
  riemannXi_ne_zero_of_one_le_re (by norm_num)

lemma continuous_logDeriv_riemannXi_two : Continuous fun y : ℝ ↦ logDeriv riemannXi (2 + y * I) :=
  continuous_logDeriv_riemannXi_comp (by fun_prop) riemannXi_two_add_ne_zero

lemma continuous_logDeriv_riemannXi_horiz {T : ℝ} (hTz : ∀ ρ : ZeroIndex riemannXi, |ρ.val.im| ≠ T)
    (h : ℝ) (hh : |h| = T) : Continuous fun x : ℝ ↦ logDeriv riemannXi (x + h * I) :=
  continuous_logDeriv_riemannXi_comp (by fun_prop) fun x ↦
    riemannXi_ne_zero_of_abs_im hTz (by simpa using hh)

/-- **Davenport, Ch. 15, p. 97 (row 15-1)**, the argument principle: for `T > 0` not an
ordinate, `∮ ξ'/ξ = 2πi · #{ρ : |γ| < T}` around the rectangle `[-1, 2] × [-T, T]`. -/
@[kb "davenport1980" "Ch 15, p. 97"]
theorem Davenport.rectIntegral_logDeriv_riemannXi {T : ℝ} (hT : 0 < T)
    (hTz : ∀ ρ : ZeroIndex riemannXi, |ρ.val.im| ≠ T) :
    rectIntegral (logDeriv riemannXi) (-1 - T * I) (2 + T * I) =
      2 * π * I * (zerosBelow T).card := by
  classical
  set z₀ : ℂ := -1 - T * I with hz₀
  set w₀ : ℂ := 2 + T * I with hw₀
  have hz₀re : z₀.re = -1 := by simp [z₀]
  have hz₀im : z₀.im = -T := by simp [z₀]
  have hw₀re : w₀.re = 2 := by simp [w₀]
  have hw₀im : w₀.im = T := by simp [w₀]
  set V : Finset ℂ := (zerosBelow T).image ZeroIndex.val with hV
  have hVre : ∀ p ∈ V, 0 < p.re ∧ p.re < 1 ∧ |p.im| < T := by
    intro p hp
    obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.mp hp
    exact ⟨(riemannXi_zero_mem ρ).2.1, (riemannXi_zero_mem ρ).2.2, mem_zerosBelow.mp hρ⟩
  set U : Set ℂ := {s | riemannXi s ≠ 0} ∪ ↑V with hU
  have hUopen : IsOpen U := by
    rw [isOpen_iff_mem_nhds]
    intro s hs
    rcases hs with hs | hs
    · exact mem_of_superset
        ((isOpen_ne_fun differentiable_riemannXi.continuous continuous_const).mem_nhds hs)
        subset_union_left
    · have h := riemannXi_eventually_ne_zero s
      rw [eventually_nhdsWithin_iff] at h
      filter_upwards [h] with x hx
      by_cases hxs : x = s
      · right; rw [hxs]; exact hs
      · left; exact hx hxs
  have hRU : [[z₀.re, w₀.re]] ×ℂ [[z₀.im, w₀.im]] ⊆ U := by
    intro s hs
    rw [mem_reProdIm, hz₀re, hw₀re, hz₀im, hw₀im, uIcc_of_le (by norm_num),
      uIcc_of_le (by linarith)] at hs
    by_cases h : riemannXi s = 0
    · right
      obtain ⟨ρ, hρ⟩ := exists_zeroIndex_val_eq differentiable_riemannXi (by simp) h
      refine Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨ρ, mem_zerosBelow.mpr ?_, hρ⟩)
      have h1 : |ρ.val.im| ≤ T := by rw [hρ]; exact abs_le.mpr ⟨hs.2.1, hs.2.2⟩
      exact lt_of_le_of_ne h1 (hTz ρ)
    · left; exact h
  have hPin : ∀ p ∈ V, p ∈ Ioo z₀.re w₀.re ×ℂ Ioo z₀.im w₀.im := by
    intro p hp
    rw [mem_reProdIm, hz₀re, hw₀re, hz₀im, hw₀im]
    obtain ⟨h1, h2, h3⟩ := hVre p hp
    rw [abs_lt] at h3
    exact ⟨⟨by linarith, by linarith⟩, h3⟩
  have hdiff : DifferentiableOn ℂ (logDeriv riemannXi) (U \ ↑V) := by
    intro s ⟨hsU, hsV⟩
    have hs : riemannXi s ≠ 0 := by
      rcases hsU with h | h
      · exact h
      · exact absurd h hsV
    have han := differentiable_riemannXi.analyticAt s
    rw [show logDeriv riemannXi = fun w ↦ deriv riemannXi w / riemannXi w from rfl]
    exact (han.deriv.differentiableAt.div han.differentiableAt hs).differentiableWithinAt
  set r : ℂ → ℂ := fun p ↦ (analyticOrderNatAt riemannXi p : ℂ) with hr
  have hres : ∀ p ∈ V, ∃ V' ∈ 𝓝 p, BddAbove (norm ∘ (fun s ↦ logDeriv riemannXi s -
      r p / (s - p)) '' (V' \ {p})) := by
    intro p _
    exact bddNear_logDeriv_sub (differentiable_riemannXi.analyticAt p)
      (Nat.cast_analyticOrderNatAt (analyticOrderAt_riemannXi_ne_top p)).symm
  have hrect := rectIntegral_eq_sum_residues (z := z₀) (w := w₀) (by rw [hz₀re, hw₀re]; norm_num)
    (by rw [hz₀im, hw₀im]; linarith) hUopen hRU r V hPin (logDeriv riemannXi) hdiff hres
  rw [hrect]
  congr 1
  rw [Finset.card_eq_sum_card_fiberwise (f := ZeroIndex.val) (t := V)
    (fun ρ hρ ↦ Finset.mem_image_of_mem _ hρ)]
  push_cast
  refine Finset.sum_congr rfl fun p hp ↦ ?_
  rw [hr]
  simp only
  rw [← card_fiber_zerosBelow (hVre p hp).2.2]

/-- **Davenport, Ch. 15, p. 97 (row 15-2)**: by the symmetries of `ξ`, the integral around the
rectangle is four times the integral along `2 → 2 + iT → 1/2 + iT`:
`∮ ξ'/ξ = 4i (∫_0^T Re ξ'/ξ(2 + iy) dy - ∫_{1/2}^2 Im ξ'/ξ(x + iT) dx)`. -/
@[kb "davenport1980" "Ch 15, p. 97"]
theorem Davenport.rectIntegral_logDeriv_riemannXi_eq {T : ℝ}
    (hTz : ∀ ρ : ZeroIndex riemannXi, |ρ.val.im| ≠ T) (hT : 0 < T) :
    rectIntegral (logDeriv riemannXi) (-1 - T * I) (2 + T * I) =
      4 * I * (((∫ y in (0 : ℝ)..T, (logDeriv riemannXi (2 + y * I)).re) -
        ∫ x in (1 / 2 : ℝ)..2, (logDeriv riemannXi (x + T * I)).im : ℝ) : ℂ) := by
  set f := logDeriv riemannXi with hf
  have e1 : ((-1 : ℂ) - T * I).re = -1 := by simp
  have e2 : ((-1 : ℂ) - T * I).im = -T := by simp
  have e3 : ((2 : ℂ) + T * I).re = 2 := by simp
  have e4 : ((2 : ℂ) + T * I).im = T := by simp
  simp only [rectIntegral, e1, e2, e3, e4]
  -- continuity
  have hc2 := continuous_logDeriv_riemannXi_two
  have hcT := continuous_logDeriv_riemannXi_horiz hTz T (abs_of_pos hT)
  have hcmT := continuous_logDeriv_riemannXi_horiz hTz (-T) (by rw [abs_neg, abs_of_pos hT])
  -- the symmetries
  have sym1 : ∀ y : ℝ, f ((-1 : ℝ) + y * I) = -f (2 + ((-y : ℝ) : ℂ) * I) := by
    intro y
    rw [← logDeriv_riemannXi_one_sub]
    congr 1; push_cast; ring
  have conjV : ∀ y : ℝ, f (2 + ((-y : ℝ) : ℂ) * I) = conj (f (2 + y * I)) := by
    intro y
    rw [← logDeriv_riemannXi_conj]
    congr 1; apply Complex.ext <;> simp
  have conjH : ∀ x : ℝ, f (x + ((-T : ℝ) : ℂ) * I) = conj (f (x + T * I)) := by
    intro x
    rw [← logDeriv_riemannXi_conj]
    congr 1; apply Complex.ext <;> simp
  have symH : ∀ x : ℝ, (f (x + T * I)).im = (f (((1 - x : ℝ) : ℂ) + T * I)).im := by
    intro x
    have h1 : f (x + T * I) = -f (1 - (x + T * I)) := by
      rw [hf, logDeriv_riemannXi_one_sub, neg_neg]
    have h2 : (1 : ℂ) - (x + T * I) = conj (((1 - x : ℝ) : ℂ) + T * I) := by
      apply Complex.ext <;> simp
    rw [h1, h2, hf, logDeriv_riemannXi_conj]
    simp
  -- the vertical sides
  set g : ℝ → ℂ := fun y ↦ f (2 + y * I) with hg
  have hgi : ∀ a b : ℝ, IntervalIntegrable g volume a b := fun a b ↦ hc2.intervalIntegrable a b
  have hreg : Continuous fun y ↦ (g y).re := Complex.continuous_re.comp hc2
  have hV1 : ∫ y in (-T : ℝ)..T, f (((-1 : ℝ) : ℂ) + y * I) =
      -∫ y in (-T : ℝ)..T, g y := by
    have : ∫ y in (-T : ℝ)..T, f (((-1 : ℝ) : ℂ) + y * I) =
        ∫ y in (-T : ℝ)..T, -g (-y) := by
      refine intervalIntegral.integral_congr fun y _ ↦ ?_
      simp only [g]
      rw [sym1]
    rw [this, intervalIntegral.integral_neg, intervalIntegral.integral_comp_neg, neg_neg]
  have hV2 : ∫ y in (-T : ℝ)..T, g y = ((2 * ∫ y in (0 : ℝ)..T, (g y).re : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (hgi (-T) 0) (hgi 0 T)]
    have h1 : ∫ y in (-T : ℝ)..0, g y = ∫ y in (0 : ℝ)..T, g (-y) := by
      rw [intervalIntegral.integral_comp_neg, neg_zero]
    have h2 : ∫ y in (0 : ℝ)..T, g (-y) = ∫ y in (0 : ℝ)..T, conj (g y) := by
      refine intervalIntegral.integral_congr fun y _ ↦ ?_
      simp only [g]
      rw [← conjV]
    rw [h1, h2, add_comm, ← intervalIntegral.integral_add (f := g) (g := fun y ↦ conj (g y)) (hgi 0 T)
      ((Complex.continuous_conj.comp hc2).intervalIntegrable 0 T)]
    have h3 : ∫ y in (0 : ℝ)..T, (g y + conj (g y)) = ∫ y in (0 : ℝ)..T, ((2 * (g y).re : ℝ) : ℂ) := by
      refine intervalIntegral.integral_congr fun y _ ↦ ?_
      rw [Complex.add_conj]
    rw [h3, intervalIntegral.integral_ofReal, intervalIntegral.integral_const_mul]
  -- the horizontal sides
  set h : ℝ → ℂ := fun x ↦ f (x + T * I) with hh
  have hhim : Continuous fun x ↦ (h x).im := Complex.continuous_im.comp hcT
  have hH1 : (∫ x in (-1 : ℝ)..2, f (x + ((-T : ℝ) : ℂ) * I)) - ∫ x in (-1 : ℝ)..2, h x =
      -(I * ((2 * ∫ x in (-1 : ℝ)..2, (h x).im : ℝ) : ℂ)) := by
    rw [← intervalIntegral.integral_sub (hcmT.intervalIntegrable _ _) (hcT.intervalIntegrable _ _)]
    have : ∫ x in (-1 : ℝ)..2, (f (x + ((-T : ℝ) : ℂ) * I) - h x) =
        ∫ x in (-1 : ℝ)..2, -(I * ((2 * (h x).im : ℝ) : ℂ)) := by
      refine intervalIntegral.integral_congr fun x _ ↦ ?_
      simp only [h]
      rw [conjH]
      have := Complex.sub_conj (f (x + T * I))
      linear_combination -this
    rw [this, intervalIntegral.integral_neg, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_ofReal, intervalIntegral.integral_const_mul]
  have hH2 : ∫ x in (-1 : ℝ)..2, (h x).im = 2 * ∫ x in (1 / 2 : ℝ)..2, (h x).im := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (hhim.intervalIntegrable (-1) (1 / 2))
      (hhim.intervalIntegrable (1 / 2) 2)]
    have : ∫ x in (-1 : ℝ)..1 / 2, (h x).im = ∫ x in (1 / 2 : ℝ)..2, (h x).im := by
      have h1 : ∫ x in (-1 : ℝ)..1 / 2, (h x).im = ∫ x in (-1 : ℝ)..1 / 2, (h (1 - x)).im := by
        refine intervalIntegral.integral_congr fun x _ ↦ ?_
        simp only [h]
        rw [symH]
      rw [h1, intervalIntegral.integral_comp_sub_left (fun x ↦ (h x).im)]
      norm_num
    rw [this]; ring
  -- assemble
  rw [hH2] at hH1
  have e5 : (∫ y in (-T : ℝ)..T, f (((2 : ℝ) : ℂ) + ↑y * I)) = ∫ y in (-T : ℝ)..T, g y := by
    simp only [g, Complex.ofReal_ofNat]
  have e6 : (∫ y in (0 : ℝ)..T, (f (2 + ↑y * I)).re) = ∫ y in (0 : ℝ)..T, (g y).re := rfl
  have e7 : (∫ x in (1 / 2 : ℝ)..2, (f (↑x + ↑T * I)).im) = ∫ x in (1 / 2 : ℝ)..2, (h x).im := rfl
  have e8 : intervalIntegral h (-1) 2 volume = ∫ x in (-1 : ℝ)..2, h x := rfl
  rw [e5, hV1, hV2, e6, e7, e8]
  push_cast at hH1 ⊢
  linear_combination hH1

/-- **Davenport's `N(T)`** (Ch. 15, p. 97): the number of zeros `ρ = β + iγ` of `ζ` in the
critical strip with `0 < γ < T`, counted with multiplicity. -/
noncomputable def zetaZeroCount (T : ℝ) : ℕ :=
  Nat.card {ρ : ZeroIndex riemannXi // 0 < ρ.val.im ∧ ρ.val.im < T}

/-- The number of real zeros of `ξ` (with multiplicity); it is in fact `0`, but only its
finiteness is used. -/
noncomputable def zetaRealZeroCount : ℕ := ((zerosBelow 1).filter fun ρ ↦ ρ.val.im = 0).card

lemma zetaZeroCount_eq_card (T : ℝ) :
    zetaZeroCount T = ((zerosBelow T).filter fun ρ ↦ 0 < ρ.val.im).card := by
  classical
  have h : ∀ ρ : ZeroIndex riemannXi, (0 < ρ.val.im ∧ ρ.val.im < T) ↔
      ρ ∈ (zerosBelow T).filter fun ρ ↦ 0 < ρ.val.im := by
    intro ρ
    rw [Finset.mem_filter, mem_zerosBelow]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨by rw [abs_of_pos h1]; exact h2, h1⟩
    · rintro ⟨h1, h2⟩; exact ⟨h2, by rw [abs_of_pos h2] at h1; exact h1⟩
  rw [zetaZeroCount, Nat.card_congr (Equiv.subtypeEquivRight h), Nat.card_eq_finsetCard]

/-- `#{|γ| < T} = 2 N(T) + N₀`, by the symmetry `ρ ↦ ρ̄`. -/
lemma card_zerosBelow_eq {T : ℝ} (hT : 0 < T) :
    (zerosBelow T).card = 2 * zetaZeroCount T + zetaRealZeroCount := by
  classical
  set S := zerosBelow T with hS
  have e1 := Finset.card_filter_add_card_filter_not (s := S) (fun ρ ↦ 0 < ρ.val.im)
  have e2 := Finset.card_filter_add_card_filter_not
    (s := S.filter fun ρ ↦ ¬ 0 < ρ.val.im) (fun ρ ↦ ρ.val.im = 0)
  rw [Finset.filter_filter, Finset.filter_filter] at e2
  have hzero : (S.filter fun ρ ↦ ¬ 0 < ρ.val.im ∧ ρ.val.im = 0) =
      (zerosBelow 1).filter fun ρ ↦ ρ.val.im = 0 := by
    ext ρ
    simp only [Finset.mem_filter, hS, mem_zerosBelow]
    constructor
    · rintro ⟨-, -, h⟩; exact ⟨by rw [h]; simp, h⟩
    · rintro ⟨-, h⟩; exact ⟨by rw [h]; simpa using hT, by rw [h]; simp, h⟩
  have hneg : (S.filter fun ρ ↦ ¬ 0 < ρ.val.im ∧ ¬ ρ.val.im = 0).card =
      (S.filter fun ρ ↦ 0 < ρ.val.im).card := by
    refine Finset.card_bij (fun ρ _ ↦ riemannXiZeroConj ρ) ?_ ?_ ?_
    · intro ρ hρ
      simp only [Finset.mem_filter, hS, mem_zerosBelow] at hρ ⊢
      simp only [riemannXiZeroConj_val, Complex.conj_im, abs_neg]
      refine ⟨hρ.1, ?_⟩
      have := lt_of_le_of_ne (not_lt.mp hρ.2.1) hρ.2.2
      linarith
    · intro a _ b _ h
      exact riemannXiZeroConj.injective h
    · intro b hb
      refine ⟨riemannXiZeroConj.symm b, ?_, by simp⟩
      have hv : (riemannXiZeroConj.symm b).val = conj b.val := by
        have := congrArg ZeroIndex.val (riemannXiZeroConj.apply_symm_apply b)
        rw [riemannXiZeroConj_val] at this
        rw [← this, conj_conj]
      simp only [Finset.mem_filter, hS, mem_zerosBelow] at hb ⊢
      rw [hv]
      simp only [Complex.conj_im, abs_neg]
      refine ⟨hb.1, by linarith [hb.2], by linarith [hb.2]⟩
  rw [zetaRealZeroCount, ← hzero, zetaZeroCount_eq_card, ← hS]
  omega

/-- **Davenport, Ch. 15, p. 97 (rows 15-1, 15-2)**: for `T > 0` not an ordinate,
`π N(T) = ∫_0^T Re ξ'/ξ(2 + iy) dy - ∫_{1/2}^2 Im ξ'/ξ(x + iT) dx - π N₀/2`, where `N₀` is the
number of real zeros of `ξ`. -/
@[kb "davenport1980" "Ch 15, p. 97"]
theorem Davenport.pi_mul_zetaZeroCount_eq {T : ℝ} (hT : 0 < T)
    (hTz : ∀ ρ : ZeroIndex riemannXi, |ρ.val.im| ≠ T) :
    π * zetaZeroCount T = (∫ y in (0 : ℝ)..T, (logDeriv riemannXi (2 + y * I)).re) -
      (∫ x in (1 / 2 : ℝ)..2, (logDeriv riemannXi (x + T * I)).im) -
        π * zetaRealZeroCount / 2 := by
  have h1 := Davenport.rectIntegral_logDeriv_riemannXi hT hTz
  have h2 := Davenport.rectIntegral_logDeriv_riemannXi_eq hTz hT
  rw [h1, card_zerosBelow_eq hT] at h2
  have h3 := congrArg Complex.im h2
  simp only [mul_im, mul_re, ofReal_re, ofReal_im, I_re, I_im, re_ofNat, im_ofNat,
    natCast_re, natCast_im, add_re, add_im, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at h3
  linarith

end NTKB
