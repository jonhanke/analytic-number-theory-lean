/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Integrals around rectangles; simple poles

Contour integration tools for Davenport, Ch. 17 and 19.

* `rectIntegral f z w`: the integral of `f` around the boundary of the rectangle with opposite
  corners `z`, `w` (counterclockwise when `z.re < w.re`, `z.im < w.im`), in the form of Mathlib's
  Cauchy-Goursat theorem `Complex.integral_boundary_rect_eq_zero_of_differentiable_on_off_countable`.
* `rectIntegral_inv_sub`: `∮ 1/(s - p) ds = 2πi` for `p` inside, by explicit integration
  (`½ log(x² + c²)` and `arctan`), as in PrimeNumberTheoremAnd's `ResidueTheoremAtOrigin`
  (written independently here).
* `rectIntegral_eq_of_simple_poles`: the residue theorem for finitely many simple poles in the
  open rectangle.
-/

open Complex Set Filter Topology MeasureTheory intervalIntegral
open scoped Real Interval

namespace NTKB

/-- The integral of `f` around the boundary of the rectangle with corners `z` and `w`. -/
noncomputable def rectIntegral (f : ℂ → ℂ) (z w : ℂ) : ℂ :=
  (∫ x : ℝ in z.re..w.re, f (x + z.im * I)) - (∫ x : ℝ in z.re..w.re, f (x + w.im * I)) +
    I * (∫ y : ℝ in z.im..w.im, f (w.re + y * I)) - I * ∫ y : ℝ in z.im..w.im, f (z.re + y * I)

/-- **Cauchy-Goursat for rectangles** (Mathlib). -/
lemma rectIntegral_eq_zero {f : ℂ → ℂ} {z w : ℂ} {s : Set ℂ} (hs : s.Countable)
    (Hc : ContinuousOn f ([[z.re, w.re]] ×ℂ [[z.im, w.im]]))
    (Hd : ∀ x ∈ Ioo (min z.re w.re) (max z.re w.re) ×ℂ Ioo (min z.im w.im) (max z.im w.im) \ s,
      DifferentiableAt ℂ f x) :
    rectIntegral f z w = 0 := by
  have := Complex.integral_boundary_rect_eq_zero_of_differentiable_on_off_countable f z w s hs Hc Hd
  simpa [rectIntegral, smul_eq_mul] using this

/-- `1/(x + ic) = x/(x² + c²) - i c/(x² + c²)`. -/
lemma one_div_ofReal_add_mul_I {x c : ℝ} (h : x ^ 2 + c ^ 2 ≠ 0) :
    1 / ((x : ℂ) + c * I) = ((x / (x ^ 2 + c ^ 2) : ℝ) : ℂ) - I * ((c / (x ^ 2 + c ^ 2) : ℝ) : ℂ) := by
  have hp : ((x : ℂ) ^ 2 + (c : ℂ) ^ 2) ≠ 0 := by exact_mod_cast h
  have hne : (x : ℂ) + c * I ≠ 0 := fun h' ↦ by
    have h1 := congrArg Complex.re h'
    have h2 := congrArg Complex.im h'
    simp at h1 h2
    exact h (by rw [h1, h2]; ring)
  rw [div_eq_iff hne]
  push_cast
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring

lemma hasDerivAt_log_sq_add (c x : ℝ) (hc : c ≠ 0) :
    HasDerivAt (fun x : ℝ ↦ Real.log (x ^ 2 + c ^ 2) / 2) (x / (x ^ 2 + c ^ 2)) x := by
  have hpos : 0 < x ^ 2 + c ^ 2 := by positivity
  have := ((hasDerivAt_pow 2 x).add_const (c ^ 2)).log hpos.ne'
  refine (this.div_const 2).congr_deriv ?_
  field_simp
  push_cast
  ring

lemma hasDerivAt_arctan_div (c x : ℝ) (hc : c ≠ 0) :
    HasDerivAt (fun x : ℝ ↦ Real.arctan (x / c)) (c / (x ^ 2 + c ^ 2)) x := by
  have := ((hasDerivAt_id x).div_const c).arctan
  simp only [id] at this
  refine this.congr_deriv ?_
  field_simp
  ring

/-- The horizontal integral of `1/s`: `∫_a^b dx/(x + ic) = ½ log((b² + c²)/(a² + c²)) - i (arctan(b/c)
- arctan(a/c))` for `c ≠ 0`. -/
lemma integral_inv_add_mul_I {c : ℝ} (hc : c ≠ 0) (a b : ℝ) :
    ∫ x : ℝ in a..b, 1 / ((x : ℂ) + c * I) =
      ((Real.log (b ^ 2 + c ^ 2) / 2 - Real.log (a ^ 2 + c ^ 2) / 2 : ℝ) : ℂ) -
        I * ((Real.arctan (b / c) - Real.arctan (a / c) : ℝ) : ℂ) := by
  set F : ℝ → ℂ := fun x ↦ ((Real.log (x ^ 2 + c ^ 2) / 2 : ℝ) : ℂ) -
    I * ((Real.arctan (x / c) : ℝ) : ℂ) with hF
  have hd : ∀ x : ℝ, HasDerivAt F (1 / ((x : ℂ) + c * I)) x := by
    intro x
    have hx : x ^ 2 + c ^ 2 ≠ 0 := by
      have := sq_nonneg x; have := pow_pos (abs_pos.mpr hc) 2; rw [sq_abs] at this; linarith
    rw [one_div_ofReal_add_mul_I hx]
    exact ((hasDerivAt_log_sq_add c x hc).ofReal_comp).sub
      ((hasDerivAt_arctan_div c x hc).ofReal_comp.const_mul I)
  have hcont : Continuous fun x : ℝ ↦ 1 / ((x : ℂ) + c * I) := by
    have hg : Continuous fun x : ℝ ↦ (x : ℂ) + c * I :=
      Complex.continuous_ofReal.add continuous_const
    have h0 : ∀ x : ℝ, (x : ℂ) + c * I ≠ 0 := fun x h ↦ hc (by simpa using congrArg Complex.im h)
    exact (hg.inv₀ h0).congr fun x ↦ (one_div _).symm
  rw [integral_eq_sub_of_hasDerivAt (fun x _ ↦ hd x) (hcont.intervalIntegrable _ _), hF]
  push_cast
  ring

/-- The vertical integral of `1/s`: `∫_c^d dy/(b + iy) = arctan(d/b) - arctan(c/b) - i ½ log((b² + d²)/
(b² + c²))` for `b ≠ 0`. -/
lemma integral_inv_add_mul_I' {b : ℝ} (hb : b ≠ 0) (c d : ℝ) :
    ∫ y : ℝ in c..d, 1 / ((b : ℂ) + y * I) =
      ((Real.arctan (d / b) - Real.arctan (c / b) : ℝ) : ℂ) -
        I * ((Real.log (b ^ 2 + d ^ 2) / 2 - Real.log (b ^ 2 + c ^ 2) / 2 : ℝ) : ℂ) := by
  set F : ℝ → ℂ := fun y ↦ ((Real.arctan (y / b) : ℝ) : ℂ) -
    I * ((Real.log (y ^ 2 + b ^ 2) / 2 : ℝ) : ℂ) with hF
  have hd : ∀ y : ℝ, HasDerivAt F (1 / ((b : ℂ) + y * I)) y := by
    intro y
    have hx : b ^ 2 + y ^ 2 ≠ 0 := by
      have := sq_nonneg y; have := pow_pos (abs_pos.mpr hb) 2; rw [sq_abs] at this; linarith
    rw [one_div_ofReal_add_mul_I hx]
    have e : b / (b ^ 2 + y ^ 2) = b / (y ^ 2 + b ^ 2) := by ring_nf
    have e' : y / (b ^ 2 + y ^ 2) = y / (y ^ 2 + b ^ 2) := by ring_nf
    rw [e, e']
    exact ((hasDerivAt_arctan_div b y hb).ofReal_comp).sub
      ((hasDerivAt_log_sq_add b y hb).ofReal_comp.const_mul I)
  have hcont : Continuous fun y : ℝ ↦ 1 / ((b : ℂ) + y * I) := by
    have hg : Continuous fun y : ℝ ↦ (b : ℂ) + y * I :=
      continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
    have h0 : ∀ y : ℝ, (b : ℂ) + y * I ≠ 0 := fun y h ↦ hb (by simpa using congrArg Complex.re h)
    exact (hg.inv₀ h0).congr fun y ↦ (one_div _).symm
  rw [integral_eq_sub_of_hasDerivAt (fun y _ ↦ hd y) (hcont.intervalIntegrable _ _), hF]
  simp only
  rw [add_comm (d ^ 2), add_comm (c ^ 2)]
  push_cast
  ring

/-- **`∮ ds/s = 2πi`** around a rectangle containing `0` in its interior. -/
lemma rectIntegral_inv {z w : ℂ} (hzr : z.re < 0) (hwr : 0 < w.re) (hzi : z.im < 0)
    (hwi : 0 < w.im) : rectIntegral (fun s ↦ 1 / s) z w = 2 * π * I := by
  unfold rectIntegral
  have e1 := integral_inv_add_mul_I hzi.ne z.re w.re
  have e2 := integral_inv_add_mul_I hwi.ne' z.re w.re
  have e3 := integral_inv_add_mul_I' hwr.ne' z.im w.im
  have e4 := integral_inv_add_mul_I' hzr.ne z.im w.im
  simp only [one_div] at e1 e2 e3 e4 ⊢
  rw [e1, e2, e3, e4]
  -- the arctangent identities `arctan x + arctan (1/x) = ± π/2`
  have a1 : Real.arctan (z.im / w.re) = -(π / 2) - Real.arctan (w.re / z.im) := by
    rw [← Real.arctan_inv_of_neg (div_neg_of_pos_of_neg hwr hzi), inv_div]
  have a2 : Real.arctan (z.im / z.re) = π / 2 - Real.arctan (z.re / z.im) := by
    rw [← Real.arctan_inv_of_pos (div_pos_of_neg_of_neg hzr hzi), inv_div]
  have a3 : Real.arctan (w.im / w.re) = π / 2 - Real.arctan (w.re / w.im) := by
    rw [← Real.arctan_inv_of_pos (div_pos hwr hwi), inv_div]
  have a4 : Real.arctan (w.im / z.re) = -(π / 2) - Real.arctan (z.re / w.im) := by
    rw [← Real.arctan_inv_of_neg (div_neg_of_neg_of_pos hzr hwi), inv_div]
  rw [a1, a2, a3, a4]
  apply Complex.ext <;> simp <;> ring

lemma integral_shift_h (f : ℂ → ℂ) (a b y : ℝ) (p : ℂ) :
    ∫ x : ℝ in a..b, f (x + y * I - p) =
      ∫ x : ℝ in a - p.re..b - p.re, f (x + ((y - p.im : ℝ) : ℂ) * I) := by
  rw [← intervalIntegral.integral_comp_sub_right]
  refine intervalIntegral.integral_congr fun x _ ↦ ?_
  congr 1
  apply Complex.ext <;> simp

lemma integral_shift_v (f : ℂ → ℂ) (c d x : ℝ) (p : ℂ) :
    ∫ y : ℝ in c..d, f (x + y * I - p) =
      ∫ y : ℝ in c - p.im..d - p.im, f (((x - p.re : ℝ) : ℂ) + y * I) := by
  rw [← intervalIntegral.integral_comp_sub_right]
  refine intervalIntegral.integral_congr fun y _ ↦ ?_
  congr 1
  apply Complex.ext <;> simp

/-- Translation. -/
lemma rectIntegral_sub (f : ℂ → ℂ) (z w p : ℂ) :
    rectIntegral (fun s ↦ f (s - p)) z w = rectIntegral f (z - p) (w - p) := by
  unfold rectIntegral
  simp only [Complex.sub_re, Complex.sub_im]
  rw [integral_shift_h f z.re w.re z.im p, integral_shift_h f z.re w.re w.im p,
    integral_shift_v f z.im w.im w.re p, integral_shift_v f z.im w.im z.re p]

/-- **`∮ ds/(s - p) = 2πi`** for `p` in the open rectangle. -/
lemma rectIntegral_inv_sub {z w p : ℂ} (h1 : z.re < p.re) (h2 : p.re < w.re) (h3 : z.im < p.im)
    (h4 : p.im < w.im) : rectIntegral (fun s ↦ 1 / (s - p)) z w = 2 * π * I := by
  rw [rectIntegral_sub (fun s ↦ 1 / s) z w p]
  exact rectIntegral_inv (by simp; linarith) (by simp; linarith) (by simp; linarith)
    (by simp; linarith)

/-- The four edge integrals exist. -/
def RectIntegrable (f : ℂ → ℂ) (z w : ℂ) : Prop :=
  IntervalIntegrable (fun x : ℝ ↦ f (x + z.im * I)) volume z.re w.re ∧
  IntervalIntegrable (fun x : ℝ ↦ f (x + w.im * I)) volume z.re w.re ∧
  IntervalIntegrable (fun y : ℝ ↦ f (w.re + y * I)) volume z.im w.im ∧
  IntervalIntegrable (fun y : ℝ ↦ f (z.re + y * I)) volume z.im w.im

lemma rectIntegral_add {f g : ℂ → ℂ} {z w : ℂ} (hf : RectIntegrable f z w)
    (hg : RectIntegrable g z w) :
    rectIntegral (fun s ↦ f s + g s) z w = rectIntegral f z w + rectIntegral g z w := by
  unfold rectIntegral
  rw [intervalIntegral.integral_add hf.1 hg.1, intervalIntegral.integral_add hf.2.1 hg.2.1,
    intervalIntegral.integral_add hf.2.2.1 hg.2.2.1, intervalIntegral.integral_add hf.2.2.2 hg.2.2.2]
  ring

lemma rectIntegral_const_mul (f : ℂ → ℂ) (c z w : ℂ) :
    rectIntegral (fun s ↦ c * f s) z w = c * rectIntegral f z w := by
  unfold rectIntegral
  simp only [intervalIntegral.integral_const_mul]
  ring

/-- A point of the closed rectangle that is not in the open rectangle (a boundary point). -/
def OnRectBoundary (z w s : ℂ) : Prop :=
  s ∈ [[z.re, w.re]] ×ℂ [[z.im, w.im]] ∧
    s ∉ Ioo (min z.re w.re) (max z.re w.re) ×ℂ Ioo (min z.im w.im) (max z.im w.im)

lemma rectIntegrable_of_continuousAt {f : ℂ → ℂ} {z w : ℂ}
    (h : ∀ s, OnRectBoundary z w s → ContinuousAt f s) : RectIntegrable f z w := by
  have hb1 : ∀ x ∈ [[z.re, w.re]], OnRectBoundary z w (x + z.im * I) := fun x hx ↦
    ⟨by simp [mem_reProdIm, hx, left_mem_uIcc], fun h' ↦ by
      have := (mem_reProdIm.mp h').2; simp at this; linarith [this.1, this.2]⟩
  have hb2 : ∀ x ∈ [[z.re, w.re]], OnRectBoundary z w (x + w.im * I) := fun x hx ↦
    ⟨by simp [mem_reProdIm, hx, right_mem_uIcc], fun h' ↦ by
      have := (mem_reProdIm.mp h').2; simp at this; linarith [this.1, this.2]⟩
  have hb3 : ∀ y ∈ [[z.im, w.im]], OnRectBoundary z w (w.re + y * I) := fun y hy ↦
    ⟨by simp [mem_reProdIm, hy, right_mem_uIcc], fun h' ↦ by
      have := (mem_reProdIm.mp h').1; simp at this; linarith [this.1, this.2]⟩
  have hb4 : ∀ y ∈ [[z.im, w.im]], OnRectBoundary z w (z.re + y * I) := fun y hy ↦
    ⟨by simp [mem_reProdIm, hy, left_mem_uIcc], fun h' ↦ by
      have := (mem_reProdIm.mp h').1; simp at this; linarith [this.1, this.2]⟩
  refine ⟨?_, ?_, ?_, ?_⟩ <;> apply ContinuousOn.intervalIntegrable <;> intro t ht <;>
    refine ContinuousAt.continuousWithinAt ?_
  · exact (h _ (hb1 t ht)).comp (f := fun x : ℝ ↦ (x : ℂ) + z.im * I)
      (Complex.continuous_ofReal.add continuous_const).continuousAt
  · exact (h _ (hb2 t ht)).comp (f := fun x : ℝ ↦ (x : ℂ) + w.im * I)
      (Complex.continuous_ofReal.add continuous_const).continuousAt
  · exact (h _ (hb3 t ht)).comp (f := fun y : ℝ ↦ (w.re : ℂ) + y * I)
      (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).continuousAt
  · exact (h _ (hb4 t ht)).comp (f := fun y : ℝ ↦ (z.re : ℂ) + y * I)
      (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).continuousAt

/-- Functions agreeing on the boundary have the same rectangle integral. -/
lemma rectIntegral_congr {f g : ℂ → ℂ} {z w : ℂ} (h : ∀ s, OnRectBoundary z w s → f s = g s) :
    rectIntegral f z w = rectIntegral g z w := by
  unfold rectIntegral
  have hb1 : ∀ x ∈ [[z.re, w.re]], f (x + z.im * I) = g (x + z.im * I) := fun x hx ↦ h _
    ⟨by simp [mem_reProdIm, hx, left_mem_uIcc], fun h' ↦ by
      have := (mem_reProdIm.mp h').2; simp at this; linarith [this.1, this.2]⟩
  have hb2 : ∀ x ∈ [[z.re, w.re]], f (x + w.im * I) = g (x + w.im * I) := fun x hx ↦ h _
    ⟨by simp [mem_reProdIm, hx, right_mem_uIcc], fun h' ↦ by
      have := (mem_reProdIm.mp h').2; simp at this; linarith [this.1, this.2]⟩
  have hb3 : ∀ y ∈ [[z.im, w.im]], f (w.re + y * I) = g (w.re + y * I) := fun y hy ↦ h _
    ⟨by simp [mem_reProdIm, hy, right_mem_uIcc], fun h' ↦ by
      have := (mem_reProdIm.mp h').1; simp at this; linarith [this.1, this.2]⟩
  have hb4 : ∀ y ∈ [[z.im, w.im]], f (z.re + y * I) = g (z.re + y * I) := fun y hy ↦ h _
    ⟨by simp [mem_reProdIm, hy, left_mem_uIcc], fun h' ↦ by
      have := (mem_reProdIm.mp h').1; simp at this; linarith [this.1, this.2]⟩
  rw [intervalIntegral.integral_congr hb1, intervalIntegral.integral_congr hb2,
    intervalIntegral.integral_congr hb3, intervalIntegral.integral_congr hb4]

/-- **Residue theorem for simple poles in a rectangle.** Let `f` be holomorphic on an open set
`U` containing the closed rectangle, except at finitely many points `P` of the open rectangle,
and suppose that near each `p ∈ P`, `f(s) - r(p)/(s - p)` is bounded. Then
`∮ f = 2πi ∑_{p ∈ P} r(p)`. -/
theorem rectIntegral_eq_sum_residues {z w : ℂ} (hre : z.re < w.re) (him : z.im < w.im)
    {U : Set ℂ} (hU : IsOpen U) (hRU : [[z.re, w.re]] ×ℂ [[z.im, w.im]] ⊆ U) (r : ℂ → ℂ) :
    ∀ (P : Finset ℂ), (∀ p ∈ P, p ∈ Ioo z.re w.re ×ℂ Ioo z.im w.im) →
      ∀ f : ℂ → ℂ, DifferentiableOn ℂ f (U \ ↑P) →
      (∀ p ∈ P, ∃ V ∈ 𝓝 p, BddAbove (norm ∘ (fun s ↦ f s - r p / (s - p)) '' (V \ {p}))) →
      rectIntegral f z w = 2 * π * I * ∑ p ∈ P, r p := by
  have hmin1 : min z.re w.re = z.re := min_eq_left hre.le
  have hmax1 : max z.re w.re = w.re := max_eq_right hre.le
  have hmin2 : min z.im w.im = z.im := min_eq_left him.le
  have hmax2 : max z.im w.im = w.im := max_eq_right him.le
  -- boundary points are not in the open rectangle, hence not in `P`
  have hbdP : ∀ (P : Finset ℂ), (∀ p ∈ P, p ∈ Ioo z.re w.re ×ℂ Ioo z.im w.im) →
      ∀ s, OnRectBoundary z w s → s ∈ U \ ↑P := by
    intro P hP s hs
    refine ⟨hRU hs.1, fun hsP ↦ hs.2 ?_⟩
    rw [hmin1, hmax1, hmin2, hmax2]
    exact hP s hsP
  intro P
  induction P using Finset.induction_on with
  | empty =>
    intro _ f hf _
    simp only [Finset.sum_empty, mul_zero]
    refine rectIntegral_eq_zero (s := ∅) countable_empty ?_ ?_
    · exact (hf.mono (by simpa using hRU)).continuousOn
    · intro x hx
      have hxU : x ∈ U := hRU (by
        have h1 := (mem_reProdIm.mp hx.1).1
        have h2 := (mem_reProdIm.mp hx.1).2
        rw [hmin1, hmax1] at h1; rw [hmin2, hmax2] at h2
        rw [uIcc_of_le hre.le, uIcc_of_le him.le]
        exact ⟨Ioo_subset_Icc_self h1, Ioo_subset_Icc_self h2⟩)
      exact (hf x (by simpa using hxU)).differentiableAt (by simpa using hU.mem_nhds hxU)
  | insert p P' hpP' ih =>
    intro hP f hf hb
    have hp := hP p (Finset.mem_insert_self p P')
    have hP' : ∀ q ∈ P', q ∈ Ioo z.re w.re ×ℂ Ioo z.im w.im := fun q hq ↦
      hP q (Finset.mem_insert_of_mem hq)
    set g : ℂ → ℂ := fun s ↦ f s - r p / (s - p) with hg
    set gt : ℂ → ℂ := Function.update g p (limUnder (𝓝[≠] p) g) with hgt
    have hopen' : IsOpen (U \ ↑P') := hU.sdiff P'.finite_toSet.isClosed
    have hopen : IsOpen (U \ ↑(insert p P')) := hU.sdiff (insert p P').finite_toSet.isClosed
    -- `g` is holomorphic off `insert p P'`
    have hgd : DifferentiableOn ℂ g (U \ ↑(insert p P')) := by
      intro x hx
      have hxp : x ≠ p := fun h ↦ hx.2 (by simp [h])
      have hinv : DifferentiableAt ℂ (fun s : ℂ ↦ r p * (s - p)⁻¹) x :=
        (differentiableAt_const _).mul ((differentiableAt_id.sub_const p).inv (sub_ne_zero.mpr hxp))
      have hdiv : DifferentiableAt ℂ (fun s : ℂ ↦ r p / (s - p)) x :=
        hinv.congr_of_eventuallyEq (Eventually.of_forall fun s ↦ div_eq_mul_inv _ _)
      exact (((hf x hx).differentiableAt (hopen.mem_nhds hx)).sub hdiv).differentiableWithinAt
    -- `gt` is holomorphic off `P'`
    have hgtd : DifferentiableOn ℂ gt (U \ ↑P') := by
      intro x hx
      by_cases hxp : x = p
      · subst hxp
        obtain ⟨V, hV, hVb⟩ := hb x (Finset.mem_insert_self x P')
        have hS : V ∩ (U \ ↑P') ∈ 𝓝 x := Filter.inter_mem hV (hopen'.mem_nhds hx)
        have hdS : DifferentiableOn ℂ g ((V ∩ (U \ ↑P')) \ {x}) := by
          refine hgd.mono ?_
          intro y hy
          refine ⟨hy.1.2.1, ?_⟩
          simp only [Finset.coe_insert, mem_insert_iff, not_or]
          exact ⟨hy.2, hy.1.2.2⟩
        have hbS : BddAbove (norm ∘ g '' ((V ∩ (U \ ↑P')) \ {x})) :=
          hVb.mono (image_mono (show (V ∩ (U \ ↑P')) \ {x} ⊆ V \ {x} from
            fun y hy ↦ ⟨hy.1.1, hy.2⟩))
        have hD := Complex.differentiableOn_update_limUnder_of_bddAbove hS hdS hbS
        exact ((hD x (mem_of_mem_nhds hS)).differentiableAt hS).differentiableWithinAt
      · have hx' : x ∈ U \ ↑(insert p P') := ⟨hx.1, by
          simp only [Finset.coe_insert, mem_insert_iff, not_or]; exact ⟨hxp, hx.2⟩⟩
        have heq : gt =ᶠ[𝓝 x] g := by
          filter_upwards [isOpen_ne.mem_nhds hxp] with y hy
          simp [hgt, Function.update_of_ne hy]
        exact ((hgd x hx').differentiableAt (hopen.mem_nhds hx')).congr_of_eventuallyEq
          heq |>.differentiableWithinAt
    -- boundedness of `gt` near the other poles
    have hbt : ∀ q ∈ P', ∃ V ∈ 𝓝 q,
        BddAbove (norm ∘ (fun s ↦ gt s - r q / (s - q)) '' (V \ {q})) := by
      intro q hq
      have hqp : q ≠ p := fun h ↦ hpP' (h ▸ hq)
      obtain ⟨V, hV, ⟨B, hB⟩⟩ := hb q (Finset.mem_insert_of_mem hq)
      set δ := ‖q - p‖ / 2 with hδdef
      have hδ : 0 < δ := by
        have := norm_pos_iff.mpr (sub_ne_zero.mpr hqp); rw [hδdef]; linarith
      refine ⟨V ∩ Metric.ball q δ, Filter.inter_mem hV (Metric.ball_mem_nhds q hδ),
        B + ‖r p‖ / δ, ?_⟩
      rintro _ ⟨s, ⟨⟨hsV, hsb⟩, hsq⟩, rfl⟩
      rw [Metric.mem_ball, dist_eq_norm] at hsb
      have h3 : ‖q - p‖ ≤ ‖s - p‖ + ‖s - q‖ := by
        calc ‖q - p‖ = ‖(s - p) - (s - q)‖ := by congr 1; ring
          _ ≤ ‖s - p‖ + ‖s - q‖ := norm_sub_le _ _
      have hsp' : δ ≤ ‖s - p‖ := by linarith
      have hsp : s ≠ p := by
        intro h; rw [h, sub_self, norm_zero] at hsp'; linarith
      have hgts : gt s = f s - r p / (s - p) := by
        simp [hgt, Function.update_of_ne hsp, hg]
      have hB' := hB ⟨s, ⟨hsV, hsq⟩, rfl⟩
      simp only [Function.comp_apply] at hB' ⊢
      rw [hgts]
      calc ‖f s - r p / (s - p) - r q / (s - q)‖ = ‖(f s - r q / (s - q)) - r p / (s - p)‖ := by
            congr 1; ring
        _ ≤ ‖f s - r q / (s - q)‖ + ‖r p / (s - p)‖ := norm_sub_le _ _
        _ ≤ B + ‖r p‖ / δ := by
            refine add_le_add hB' ?_
            rw [norm_div]
            exact div_le_div_of_nonneg_left (norm_nonneg _) hδ hsp'
    have hIH := ih hP' gt hgtd hbt
    -- assemble
    have hbd : ∀ s, OnRectBoundary z w s → s ∈ U \ ↑P' ∧ s ≠ p := fun s hs ↦
      ⟨⟨(hbdP _ hP s hs).1, fun h ↦ (hbdP _ hP s hs).2 (by simp [h])⟩,
        fun h ↦ (hbdP _ hP s hs).2 (by simp [h])⟩
    have hcongr : rectIntegral f z w = rectIntegral (fun s ↦ gt s + r p * (1 / (s - p))) z w := by
      refine rectIntegral_congr fun s hs ↦ ?_
      simp only [hgt, Function.update_of_ne (hbd s hs).2, hg]
      rw [div_eq_mul_inv, one_div]
      ring
    have hint1 : RectIntegrable gt z w := rectIntegrable_of_continuousAt fun s hs ↦
      ((hgtd s (hbd s hs).1).differentiableAt (hopen'.mem_nhds (hbd s hs).1)).continuousAt
    have hint2 : RectIntegrable (fun s ↦ r p * (1 / (s - p))) z w :=
      rectIntegrable_of_continuousAt fun s hs ↦ by
        have h1 : ContinuousAt (fun s : ℂ ↦ r p * (s - p)⁻¹) s :=
          continuousAt_const.mul ((continuousAt_id.sub continuousAt_const).inv₀
            (sub_ne_zero.mpr (hbd s hs).2))
        exact h1.congr (Eventually.of_forall fun s ↦ by simp only [one_div])
    rw [hcongr, rectIntegral_add hint1 hint2, hIH, rectIntegral_const_mul,
      rectIntegral_inv_sub (mem_reProdIm.mp hp).1.1 (mem_reProdIm.mp hp).1.2
        (mem_reProdIm.mp hp).2.1 (mem_reProdIm.mp hp).2.2, Finset.sum_insert hpP']
    ring

end NTKB
