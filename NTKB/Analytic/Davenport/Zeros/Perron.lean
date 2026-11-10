/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Davenport.Zeros.Rectangle
import NTKB.Attr
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# The discontinuous integral (Perron's formula with truncation)

**Davenport, Ch. 17, pp. 104-106 (rows 17-5, 17-6).** For `y > 0`, `c > 0`, `T > 0` let
`I(y, T) = (1/2πi) ∫_{c-iT}^{c+iT} y^s/s ds = (1/2π) ∫_{-T}^{T} y^{c+it}/(c+it) dt` and
`δ(y) = 0, 1/2, 1` for `y < 1`, `y = 1`, `y > 1`. Then
`|I(y, T) - δ(y)| ≤ y^c min(1, 1/(π T |log y|))` for `y ≠ 1` (when `c ≤ T`) and
`|I(1, T) - 1/2| ≤ c/(π T)`.

The proof follows Davenport: the vertical segment is replaced by the other three sides of a
rectangle to the right (`y < 1`, no pole) or to the left (`y > 1`, residue `1` at `s = 0`);
for the bound `y^c` we take the rectangle of width `T` instead of Davenport's circular arc.
The case `y = 1` is the direct computation `I(1, T) = arctan(T/c)/π`.
-/

open Complex Set Filter Topology MeasureTheory intervalIntegral
open scoped Real Interval

namespace NTKB

/-- `I(y, T) = (1/2π) ∫_{-T}^{T} y^{c+it}/(c+it) dt`, i.e. `(1/2πi) ∫_{c-iT}^{c+iT} y^s/s ds`. -/
noncomputable def perronIntegral (y c T : ℝ) : ℂ :=
  (1 / (2 * π)) * ∫ t : ℝ in -T..T, (y : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I)

/-- The integrand `y^s/s`. -/
noncomputable def perronKernel (y : ℝ) (s : ℂ) : ℂ := (y : ℂ) ^ s / s

lemma norm_perronKernel {y : ℝ} (hy : 0 < y) (s : ℂ) :
    ‖perronKernel y s‖ = y ^ s.re / ‖s‖ := by
  rw [perronKernel, norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hy]

/-- On a horizontal line `Im s = h ≠ 0`: `|y^s/s| ≤ y^σ/|h|`. -/
lemma norm_perronKernel_le_horiz {y : ℝ} (hy : 0 < y) (x h : ℝ) (hh : h ≠ 0) :
    ‖perronKernel y (x + h * I)‖ ≤ y ^ x / |h| := by
  rw [norm_perronKernel hy]
  have hre : ((x : ℂ) + h * I).re = x := by simp
  rw [hre]
  apply div_le_div_of_nonneg_left (Real.rpow_nonneg hy.le _) (abs_pos.mpr hh)
  have := Complex.abs_im_le_norm ((x : ℂ) + h * I)
  simpa using this

/-- On a vertical line `Re s = X ≠ 0`: `|y^s/s| ≤ y^X/|X|`. -/
lemma norm_perronKernel_le_vert {y : ℝ} (hy : 0 < y) (X t : ℝ) (hX : X ≠ 0) :
    ‖perronKernel y (X + t * I)‖ ≤ y ^ X / |X| := by
  rw [norm_perronKernel hy]
  have hre : ((X : ℂ) + t * I).re = X := by simp
  rw [hre]
  apply div_le_div_of_nonneg_left (Real.rpow_nonneg hy.le _) (abs_pos.mpr hX)
  have := Complex.abs_re_le_norm ((X : ℂ) + t * I)
  simpa using this

/-- `∫_a^b y^x dx = (y^b - y^a)/log y` for `y > 0`, `y ≠ 1`. -/
lemma integral_rpow_const {y : ℝ} (hy : 0 < y) (hy1 : y ≠ 1) (a b : ℝ) :
    ∫ x : ℝ in a..b, y ^ x = (y ^ b - y ^ a) / Real.log y := by
  have hl : Real.log y ≠ 0 := by
    intro h
    rcases Real.log_eq_zero.mp h with h | h | h <;> [linarith; exact hy1 h; linarith]
  have hd : ∀ x : ℝ, HasDerivAt (fun x : ℝ ↦ y ^ x / Real.log y) (y ^ x) x := by
    intro x
    have := (Real.hasStrictDerivAt_const_rpow hy x).hasDerivAt
    convert this.div_const (Real.log y) using 1
    field_simp
  rw [integral_eq_sub_of_hasDerivAt (fun x _ ↦ hd x)
    ((Real.continuous_const_rpow hy.ne').intervalIntegrable _ _)]
  ring

/-- Horizontal sides: `‖∫_a^b y^{x+ih}/(x+ih) dx‖ ≤ (1/|h|) ∫_a^b y^x dx`. -/
lemma norm_integral_horiz_le {y : ℝ} (hy : 0 < y) {a b h : ℝ} (hab : a ≤ b) (hh : h ≠ 0) :
    ‖∫ x : ℝ in a..b, perronKernel y (x + h * I)‖ ≤ (∫ x : ℝ in a..b, y ^ x) / |h| := by
  rw [← intervalIntegral.integral_div]
  refine intervalIntegral.norm_integral_le_of_norm_le hab
    (Eventually.of_forall fun x _ ↦ norm_perronKernel_le_horiz hy x h hh) ?_
  exact ((Real.continuous_const_rpow hy.ne').div_const _).intervalIntegrable _ _

/-- Vertical sides: `‖∫_{-T}^{T} y^{X+it}/(X+it) dt‖ ≤ 2T y^X/|X|`. -/
lemma norm_integral_vert_le {y : ℝ} (hy : 0 < y) {X T : ℝ} (hT : 0 ≤ T) (hX : X ≠ 0) :
    ‖∫ t : ℝ in -T..T, perronKernel y (X + t * I)‖ ≤ 2 * T * (y ^ X / |X|) := by
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := -T) (b := T)
    (C := y ^ X / |X|) (f := fun t : ℝ ↦ perronKernel y (X + t * I))
    (fun t _ ↦ norm_perronKernel_le_vert hy X t hX)
  rw [show T - -T = 2 * T by ring, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 * T)] at this
  linarith

lemma differentiableAt_perronKernel {y : ℝ} (hy : 0 < y) {s : ℂ} (hs : s ≠ 0) :
    DifferentiableAt ℂ (perronKernel y) s := by
  have hy' : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  have h1 : DifferentiableAt ℂ (fun s : ℂ ↦ (y : ℂ) ^ s) s :=
    differentiableAt_id.const_cpow (Or.inl hy')
  have h2 : DifferentiableAt ℂ (fun s : ℂ ↦ (y : ℂ) ^ s * s⁻¹) s :=
    h1.mul (differentiableAt_id.inv hs)
  exact h2.congr_of_eventuallyEq (Eventually.of_forall fun s ↦ by simp [perronKernel, div_eq_mul_inv])

/-- The rectangle to the right: for `0 < c < X`,
`∫_{-T}^{T} y^{c+it}/(c+it) dt = -i (∫_c^X y^{x-iT}/(x-iT) dx - ∫_c^X y^{x+iT}/(x+iT) dx)
+ ∫_{-T}^{T} y^{X+it}/(X+it) dt`. -/
lemma perron_rect_right {y : ℝ} (hy : 0 < y) {c X T : ℝ} (hc : 0 < c) (hcX : c < X) :
    ∫ t : ℝ in -T..T, perronKernel y (c + t * I) =
      -I * ((∫ x : ℝ in c..X, perronKernel y (x + (-T : ℝ) * I)) -
        ∫ x : ℝ in c..X, perronKernel y (x + T * I)) +
      ∫ t : ℝ in -T..T, perronKernel y (X + t * I) := by
  have h := rectIntegral_eq_zero (f := perronKernel y) (z := (c : ℂ) + (-T : ℝ) * I)
    (w := (X : ℂ) + T * I) (s := ∅) countable_empty ?_ ?_
  · unfold rectIntegral at h
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      add_zero, add_im, mul_im, zero_add] at h
    linear_combination I * h + ((∫ t : ℝ in -T..T, perronKernel y (c + t * I)) -
      ∫ t : ℝ in -T..T, perronKernel y (X + t * I)) * Complex.I_sq
  · intro s hs
    have : 0 < s.re := by
      have := (mem_reProdIm.mp hs).1
      simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
        add_zero] at this
      rw [uIcc_of_le hcX.le] at this
      linarith [this.1]
    exact (differentiableAt_perronKernel hy (fun h ↦ by rw [h] at this; simp at this)).continuousAt
      |>.continuousWithinAt
  · intro s hs
    have : 0 < s.re := by
      have := (mem_reProdIm.mp hs.1).1
      simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
        add_zero] at this
      rw [min_eq_left hcX.le] at this
      linarith [this.1]
    exact differentiableAt_perronKernel hy (fun h ↦ by rw [h] at this; simp at this)

/-- `‖I(y, T)‖ ≤ y^c / (π T |log y|)` for `y < 1`. -/
lemma norm_perronIntegral_lt_one_log {y c T : ℝ} (hy : 0 < y) (hy1 : y < 1) (hc : 0 < c)
    (hT : 0 < T) : ‖perronIntegral y c T‖ ≤ y ^ c / (π * T * |Real.log y|) := by
  have hl : Real.log y < 0 := Real.log_neg hy hy1
  have hπ := Real.pi_pos
  -- the bound for each `X > c`
  have hX : ∀ X : ℝ, c < X → ‖perronIntegral y c T‖ ≤
      (1 / (2 * π)) * (2 * (y ^ c / -Real.log y / T) + 2 * T * (y ^ X / X)) := by
    intro X hcX
    have h := perron_rect_right (T := T) hy hc hcX
    have hb := norm_integral_horiz_le hy hcX.le (h := -T) (by linarith)
    have ht := norm_integral_horiz_le hy hcX.le (h := T) hT.ne'
    have hv := norm_integral_vert_le hy hT.le (X := X) (by linarith)
    rw [integral_rpow_const hy hy1.ne] at hb ht
    rw [abs_neg, abs_of_pos hT] at hb
    rw [abs_of_pos hT] at ht
    rw [abs_of_pos (by linarith : 0 < X)] at hv
    have hyX : 0 ≤ y ^ X := Real.rpow_nonneg hy.le _
    have hint : (y ^ X - y ^ c) / Real.log y ≤ y ^ c / -Real.log y := by
      rw [show (y ^ X - y ^ c) / Real.log y = (y ^ c - y ^ X) / -Real.log y by
        rw [div_neg, ← neg_div]; ring_nf]
      exact div_le_div_of_nonneg_right (by linarith) (by linarith)
    have hint' : (y ^ X - y ^ c) / Real.log y / T ≤ y ^ c / -Real.log y / T :=
      div_le_div_of_nonneg_right hint hT.le
    show ‖(1 / (2 * π) : ℂ) * ∫ t : ℝ in -T..T, perronKernel y (c + t * I)‖ ≤ _
    rw [h, norm_mul]
    have hn : ‖(1 : ℂ) / (2 * π)‖ = 1 / (2 * π) := by
      rw [norm_div, norm_one, norm_mul, Complex.norm_two, Complex.norm_real,
        Real.norm_of_nonneg hπ.le]
    rw [hn]
    gcongr
    calc ‖-I * ((∫ x : ℝ in c..X, perronKernel y (x + (-T : ℝ) * I)) -
          ∫ x : ℝ in c..X, perronKernel y (x + T * I)) +
          ∫ t : ℝ in -T..T, perronKernel y (X + t * I)‖
        ≤ ‖∫ x : ℝ in c..X, perronKernel y (x + (-T : ℝ) * I)‖ +
          ‖∫ x : ℝ in c..X, perronKernel y (x + T * I)‖ +
          ‖∫ t : ℝ in -T..T, perronKernel y (X + t * I)‖ := by
          refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
          rw [norm_mul, norm_neg, Complex.norm_I, one_mul]
          exact norm_sub_le _ _
      _ ≤ 2 * (y ^ c / -Real.log y / T) + 2 * T * (y ^ X / X) := by linarith
  -- let `X → ∞`
  have hlim : Tendsto (fun X : ℝ ↦ (1 / (2 * π)) *
      (2 * (y ^ c / -Real.log y / T) + 2 * T * (y ^ X / X))) atTop
      (𝓝 ((1 / (2 * π)) * (2 * (y ^ c / -Real.log y / T) + 2 * T * 0))) := by
    refine tendsto_const_nhds.mul (tendsto_const_nhds.add (tendsto_const_nhds.mul ?_))
    have h1 : Tendsto (fun X : ℝ ↦ y ^ X) atTop (𝓝 0) :=
      tendsto_rpow_atTop_of_base_lt_one y (by linarith) hy1
    have h2 : Tendsto (fun X : ℝ ↦ X⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
    simpa [div_eq_mul_inv] using h1.mul h2
  have := ge_of_tendsto hlim ((eventually_gt_atTop c).mono fun X hX' ↦ hX X hX')
  rw [abs_of_neg hl]
  calc ‖perronIntegral y c T‖ ≤ 1 / (2 * π) * (2 * (y ^ c / -Real.log y / T) + 2 * T * 0) :=
        this
    _ = y ^ c / (π * T * -Real.log y) := by field_simp; ring

lemma norm_one_div_two_pi : ‖(1 : ℂ) / (2 * π)‖ = 1 / (2 * π) := by
  rw [norm_div, norm_one, norm_mul, Complex.norm_two, Complex.norm_real,
    Real.norm_of_nonneg Real.pi_pos.le]

/-- `‖I(y, T)‖ ≤ y^c` for `y < 1` (rectangle of width `T`). -/
lemma norm_perronIntegral_lt_one_le {y c T : ℝ} (hy : 0 < y) (hy1 : y < 1) (hc : 0 < c)
    (hT : 0 < T) : ‖perronIntegral y c T‖ ≤ y ^ c := by
  have hπ := Real.pi_gt_three
  have h := perron_rect_right (T := T) hy hc (by linarith : c < c + T)
  have hyc : 0 ≤ y ^ c := Real.rpow_nonneg hy.le _
  have hhor : ∀ h : ℝ, |h| = T → ‖∫ x : ℝ in c..c + T, perronKernel y (x + h * I)‖ ≤ y ^ c := by
    intro h hh
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := c) (b := c + T)
      (C := y ^ c / T) (f := fun x : ℝ ↦ perronKernel y (x + h * I)) fun x hx ↦ by
        rw [uIoc_of_le (by linarith)] at hx
        refine (norm_perronKernel_le_horiz hy x h (by rw [← abs_pos, hh]; exact hT)).trans ?_
        rw [hh]
        exact div_le_div_of_nonneg_right
          (Real.rpow_le_rpow_of_exponent_ge hy hy1.le hx.1.le) hT.le
    rw [show c + T - c = T by ring, abs_of_pos hT, div_mul_cancel₀ _ hT.ne'] at this
    exact this
  have hb := hhor (-T) (by rw [abs_neg, abs_of_pos hT])
  have ht := hhor T (abs_of_pos hT)
  have hv := norm_integral_vert_le hy hT.le (X := c + T) (by linarith)
  rw [abs_of_pos (by linarith : 0 < c + T)] at hv
  have hv' : 2 * T * (y ^ (c + T) / (c + T)) ≤ 2 * y ^ c := by
    have h1 : y ^ (c + T) ≤ y ^ c := Real.rpow_le_rpow_of_exponent_ge hy hy1.le (by linarith)
    have h2 : y ^ (c + T) / (c + T) ≤ y ^ c / T :=
      div_le_div₀ hyc h1 hT (by linarith)
    calc 2 * T * (y ^ (c + T) / (c + T)) ≤ 2 * T * (y ^ c / T) := by gcongr
      _ = 2 * y ^ c := by field_simp
  show ‖(1 / (2 * π) : ℂ) * ∫ t : ℝ in -T..T, perronKernel y (c + t * I)‖ ≤ _
  rw [h, norm_mul, norm_one_div_two_pi]
  have htri : ‖-I * ((∫ x : ℝ in c..c + T, perronKernel y (x + (-T : ℝ) * I)) -
        ∫ x : ℝ in c..c + T, perronKernel y (x + T * I)) +
        ∫ t : ℝ in -T..T, perronKernel y ((c + T : ℝ) + t * I)‖ ≤ 4 * y ^ c := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_neg, Complex.norm_I, one_mul]
    have := norm_sub_le (∫ x : ℝ in c..c + T, perronKernel y (x + (-T : ℝ) * I))
      (∫ x : ℝ in c..c + T, perronKernel y (x + T * I))
    linarith
  calc 1 / (2 * π) * _ ≤ 1 / (2 * π) * (4 * y ^ c) := by gcongr
    _ ≤ y ^ c := by
        rw [show 1 / (2 * π) * (4 * y ^ c) = (2 / π) * y ^ c by ring]
        exact mul_le_of_le_one_left hyc (by rw [div_le_one (by linarith)]; linarith)

/-- `y^s/s - 1/s` is bounded near `0`. -/
lemma perronKernel_sub_bdd {y : ℝ} (hy : 0 < y) :
    ∃ V ∈ 𝓝 (0 : ℂ), BddAbove (norm ∘ (fun s ↦ perronKernel y s - 1 / (s - 0)) '' (V \ {0})) := by
  have hy' : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  have hd : HasDerivAt (fun s : ℂ ↦ (y : ℂ) ^ s) ((y : ℂ) ^ (0 : ℂ) * Complex.log y * 1) 0 :=
    (hasDerivAt_id (0 : ℂ)).const_cpow (Or.inl hy')
  have ht := hasDerivAt_iff_tendsto_slope_zero.mp hd
  set L := (y : ℂ) ^ (0 : ℂ) * Complex.log y * 1
  have hev : ∀ᶠ t in 𝓝[≠] (0 : ℂ), ‖t⁻¹ • ((y : ℂ) ^ (0 + t) - (y : ℂ) ^ (0 : ℂ))‖ < ‖L‖ + 1 :=
    ht.norm.eventually (gt_mem_nhds (by linarith))
  rw [eventually_nhdsWithin_iff] at hev
  refine ⟨_, hev, ‖L‖ + 1, ?_⟩
  rintro _ ⟨s, ⟨hs, hs0⟩, rfl⟩
  have hs0' : s ≠ 0 := hs0
  have := (hs hs0').le
  simp only [zero_add, Complex.cpow_zero, smul_eq_mul] at this
  simp only [Function.comp_apply, sub_zero, perronKernel]
  convert this using 2
  field_simp

/-- The rectangle to the left (residue `1` at `s = 0`): for `X > 0`, `T > 0`,
`∫_{-T}^{T} y^{c+it}/(c+it) dt = 2π + i (∫_{-X}^c y^{x-iT}/(x-iT) dx - ∫_{-X}^c y^{x+iT}/(x+iT) dx)
+ ∫_{-T}^{T} y^{-X+it}/(-X+it) dt`. -/
lemma perron_rect_left {y : ℝ} (hy : 0 < y) {c X T : ℝ} (hc : 0 < c) (hX : 0 < X) (hT : 0 < T) :
    ∫ t : ℝ in -T..T, perronKernel y (c + t * I) =
      2 * π + I * ((∫ x : ℝ in -X..c, perronKernel y (x + (-T : ℝ) * I)) -
        ∫ x : ℝ in -X..c, perronKernel y (x + T * I)) +
      ∫ t : ℝ in -T..T, perronKernel y ((-X : ℝ) + t * I) := by
  have hre : ((-X : ℝ) + (-T : ℝ) * I : ℂ).re < ((c : ℂ) + T * I).re := by simp; linarith
  have him : ((-X : ℝ) + (-T : ℝ) * I : ℂ).im < ((c : ℂ) + T * I).im := by simp; linarith
  have h := rectIntegral_eq_sum_residues hre him isOpen_univ (subset_univ _) (fun _ ↦ 1) {0}
    (by
      intro p hp
      rw [Finset.mem_singleton] at hp
      subst hp
      simp only [mem_reProdIm, zero_re, zero_im, add_re, ofReal_re, mul_re, I_re, mul_zero,
        ofReal_im, I_im, mul_one, sub_self, add_zero, add_im, mul_im, zero_add, mem_Ioo]
      exact ⟨⟨by linarith, hc⟩, ⟨by linarith, hT⟩⟩)
    (perronKernel y) (fun s hs ↦ (differentiableAt_perronKernel hy (by
      simpa using hs.2)).differentiableWithinAt)
    (by
      intro p hp
      rw [Finset.mem_singleton] at hp
      subst hp
      exact perronKernel_sub_bdd hy)
  unfold rectIntegral at h
  simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
    add_zero, add_im, mul_im, zero_add, Finset.sum_singleton] at h
  linear_combination (-I) * h + ((∫ t : ℝ in -T..T, perronKernel y (c + t * I)) -
    (∫ t : ℝ in -T..T, perronKernel y ((-X : ℝ) + t * I)) - 2 * π) * Complex.I_sq

/-- `‖I(y, T) - 1‖ ≤ y^c / (π T log y)` for `y > 1`. -/
lemma norm_perronIntegral_gt_one_log {y c T : ℝ} (hy1 : 1 < y) (hc : 0 < c) (hT : 0 < T) :
    ‖perronIntegral y c T - 1‖ ≤ y ^ c / (π * T * |Real.log y|) := by
  have hy : 0 < y := by linarith
  have hl : 0 < Real.log y := Real.log_pos hy1
  have hπ := Real.pi_pos
  have hX : ∀ X : ℝ, 0 < X → ‖perronIntegral y c T - 1‖ ≤
      (1 / (2 * π)) * (2 * (y ^ c / Real.log y / T) + 2 * T * (y ^ (-X) / X)) := by
    intro X hX0
    have h := perron_rect_left hy hc hX0 hT
    have hb := norm_integral_horiz_le hy (by linarith : -X ≤ c) (h := -T) (by linarith)
    have ht := norm_integral_horiz_le hy (by linarith : -X ≤ c) (h := T) hT.ne'
    have hv := norm_integral_vert_le hy hT.le (X := -X) (by linarith)
    rw [integral_rpow_const hy hy1.ne'] at hb ht
    rw [abs_neg, abs_of_pos hT] at hb
    rw [abs_of_pos hT] at ht
    rw [abs_neg, abs_of_pos hX0] at hv
    have hyX : 0 ≤ y ^ (-X) := Real.rpow_nonneg hy.le _
    have hint : (y ^ c - y ^ (-X)) / Real.log y / T ≤ y ^ c / Real.log y / T :=
      div_le_div_of_nonneg_right (div_le_div_of_nonneg_right (by linarith) hl.le) hT.le
    have heq : perronIntegral y c T - 1 = (1 / (2 * π)) * (I * ((∫ x : ℝ in -X..c,
        perronKernel y (x + (-T : ℝ) * I)) - ∫ x : ℝ in -X..c, perronKernel y (x + T * I)) +
        ∫ t : ℝ in -T..T, perronKernel y ((-X : ℝ) + t * I)) := by
      show (1 / (2 * π) : ℂ) * (∫ t : ℝ in -T..T, perronKernel y (c + t * I)) - 1 = _
      rw [h]
      have : (π : ℂ) ≠ 0 := by exact_mod_cast hπ.ne'
      field_simp
      ring
    rw [heq, norm_mul, norm_one_div_two_pi]
    gcongr
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, Complex.norm_I, one_mul]
    have := norm_sub_le (∫ x : ℝ in -X..c, perronKernel y (x + (-T : ℝ) * I))
      (∫ x : ℝ in -X..c, perronKernel y (x + T * I))
    linarith
  have hlim : Tendsto (fun X : ℝ ↦ (1 / (2 * π)) *
      (2 * (y ^ c / Real.log y / T) + 2 * T * (y ^ (-X) / X))) atTop
      (𝓝 ((1 / (2 * π)) * (2 * (y ^ c / Real.log y / T) + 2 * T * 0))) := by
    refine tendsto_const_nhds.mul (tendsto_const_nhds.add (tendsto_const_nhds.mul ?_))
    have h1 : Tendsto (fun X : ℝ ↦ y ^ (-X)) atTop (𝓝 0) := by
      have := tendsto_rpow_atTop_of_base_lt_one y⁻¹ (by
        have : 0 < y⁻¹ := inv_pos.mpr hy; linarith) (inv_lt_one_of_one_lt₀ hy1)
      refine this.congr fun X ↦ ?_
      rw [Real.inv_rpow hy.le, Real.rpow_neg hy.le]
    have h2 : Tendsto (fun X : ℝ ↦ X⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
    simpa [div_eq_mul_inv] using h1.mul h2
  have := ge_of_tendsto hlim ((eventually_gt_atTop 0).mono fun X hX' ↦ hX X hX')
  rw [abs_of_pos hl]
  calc ‖perronIntegral y c T - 1‖ ≤ 1 / (2 * π) * (2 * (y ^ c / Real.log y / T) + 2 * T * 0) :=
        this
    _ = y ^ c / (π * T * Real.log y) := by field_simp; ring

/-- `‖I(y, T) - 1‖ ≤ y^c` for `y > 1` and `c ≤ T` (rectangle of width `T + c`). -/
lemma norm_perronIntegral_gt_one_le {y c T : ℝ} (hy1 : 1 < y) (hc : 0 < c) (hcT : c ≤ T) :
    ‖perronIntegral y c T - 1‖ ≤ y ^ c := by
  have hy : 0 < y := by linarith
  have hT : 0 < T := by linarith
  have hπ := Real.pi_gt_three
  have h := perron_rect_left hy hc hT hT
  have hyc1 : 1 ≤ y ^ c := Real.one_le_rpow hy1.le hc.le
  have hhor : ∀ h : ℝ, |h| = T →
      ‖∫ x : ℝ in -T..c, perronKernel y (x + h * I)‖ ≤ y ^ c * ((c + T) / T) := by
    intro h hh
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := -T) (b := c)
      (C := y ^ c / T) (f := fun x : ℝ ↦ perronKernel y (x + h * I)) fun x hx ↦ by
        rw [uIoc_of_le (by linarith)] at hx
        refine (norm_perronKernel_le_horiz hy x h (by rw [← abs_pos, hh]; exact hT)).trans ?_
        rw [hh]
        exact div_le_div_of_nonneg_right
          (Real.rpow_le_rpow_of_exponent_le hy1.le hx.2) hT.le
    rw [show c - -T = c + T by ring, abs_of_pos (by linarith : 0 < c + T)] at this
    calc _ ≤ y ^ c / T * (c + T) := this
      _ = y ^ c * ((c + T) / T) := by ring
  have hb := hhor (-T) (by rw [abs_neg, abs_of_pos hT])
  have ht := hhor T (abs_of_pos hT)
  have hv := norm_integral_vert_le hy hT.le (X := -T) (by linarith)
  rw [abs_neg, abs_of_pos hT] at hv
  have hv' : 2 * T * (y ^ (-T) / T) ≤ 2 * y ^ c := by
    have h1 : y ^ (-T) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hy1.le (by linarith)
    rw [mul_div_assoc', mul_div_right_comm, mul_div_cancel_right₀ _ hT.ne']
    linarith
  have hcT' : (c + T) / T ≤ 2 := by rw [div_le_iff₀ hT]; linarith
  have heq : perronIntegral y c T - 1 = (1 / (2 * π)) * (I * ((∫ x : ℝ in -T..c,
      perronKernel y (x + (-T : ℝ) * I)) - ∫ x : ℝ in -T..c, perronKernel y (x + T * I)) +
      ∫ t : ℝ in -T..T, perronKernel y ((-T : ℝ) + t * I)) := by
    show (1 / (2 * π) : ℂ) * (∫ t : ℝ in -T..T, perronKernel y (c + t * I)) - 1 = _
    rw [h]
    have : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
    field_simp
    ring
  rw [heq, norm_mul, norm_one_div_two_pi]
  have htri : ‖I * ((∫ x : ℝ in -T..c, perronKernel y (x + (-T : ℝ) * I)) -
      ∫ x : ℝ in -T..c, perronKernel y (x + T * I)) +
      ∫ t : ℝ in -T..T, perronKernel y ((-T : ℝ) + t * I)‖ ≤ 6 * y ^ c := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, Complex.norm_I, one_mul]
    have := norm_sub_le (∫ x : ℝ in -T..c, perronKernel y (x + (-T : ℝ) * I))
      (∫ x : ℝ in -T..c, perronKernel y (x + T * I))
    have h2 : y ^ c * ((c + T) / T) ≤ y ^ c * 2 := by gcongr
    linarith
  have hyc : 0 ≤ y ^ c := by linarith
  calc 1 / (2 * π) * _ ≤ 1 / (2 * π) * (6 * y ^ c) := by gcongr
    _ ≤ y ^ c := by
        rw [show 1 / (2 * π) * (6 * y ^ c) = (3 / π) * y ^ c by ring]
        exact mul_le_of_le_one_left hyc (by rw [div_le_one (by linarith)]; linarith)

/-- `I(1, T) = arctan(T/c)/π`. -/
lemma perronIntegral_one {c T : ℝ} (hc : 0 < c) :
    perronIntegral 1 c T = ((Real.arctan (T / c) / π : ℝ) : ℂ) := by
  unfold perronIntegral
  simp only [Complex.ofReal_one, Complex.one_cpow]
  rw [integral_inv_add_mul_I' hc.ne' (-T) T]
  rw [neg_div, Real.arctan_neg]
  have : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
  push_cast
  rw [show (-T) ^ 2 = T ^ 2 by ring]
  field_simp
  ring

/-- `|I(1, T) - 1/2| ≤ c/(π T)`. -/
lemma norm_perronIntegral_one_sub_half {c T : ℝ} (hc : 0 < c) (hT : 0 < T) :
    ‖perronIntegral 1 c T - 1 / 2‖ ≤ c / (π * T) := by
  rw [perronIntegral_one hc]
  have hπ := Real.pi_pos
  have ha : Real.arctan (T / c) = π / 2 - Real.arctan (c / T) := by
    rw [← Real.arctan_inv_of_pos (div_pos hc hT), inv_div]
  have hb := Real.arctan_le_self (div_pos hc hT).le
  have hb0 : 0 ≤ Real.arctan (c / T) := Real.arctan_nonneg.mpr (div_pos hc hT).le
  have hs : ((Real.arctan (T / c) / π : ℝ) : ℂ) - 1 / 2 =
      ((-(Real.arctan (c / T) / π) : ℝ) : ℂ) := by
    rw [ha]; push_cast; field_simp; ring
  rw [hs]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_nonneg (by positivity)]
  rw [div_le_div_iff₀ hπ (by positivity)]
  calc Real.arctan (c / T) * (π * T) ≤ c / T * (π * T) := by gcongr
    _ = c * π := by field_simp

/-- **Davenport, Ch. 17, p. 105, Lemma (row 17-6)**: for `y > 0`, `0 < c ≤ T`,
`|I(y, T) - δ(y)| ≤ y^c min(1, 1/(π T |log y|))` for `y ≠ 1` and `|I(1, T) - 1/2| ≤ c/(π T)`. -/
@[kb "davenport1980" "Ch 17, p. 105"]
theorem Davenport.perron_truncated {y c T : ℝ} (hy : 0 < y) (hc : 0 < c) (hcT : c ≤ T) :
    (y < 1 → ‖perronIntegral y c T‖ ≤ y ^ c * min 1 (1 / (π * T * |Real.log y|))) ∧
    (1 < y → ‖perronIntegral y c T - 1‖ ≤ y ^ c * min 1 (1 / (π * T * |Real.log y|))) ∧
    (y = 1 → ‖perronIntegral y c T - 1 / 2‖ ≤ c / (π * T)) := by
  have hT : 0 < T := by linarith
  refine ⟨fun hy1 ↦ ?_, fun hy1 ↦ ?_, fun hy1 ↦ hy1 ▸ norm_perronIntegral_one_sub_half hc hT⟩
  · rw [mul_min_of_nonneg _ _ (Real.rpow_nonneg hy.le _), mul_one, le_min_iff,
      ← div_eq_mul_one_div]
    exact ⟨norm_perronIntegral_lt_one_le hy hy1 hc hT,
      norm_perronIntegral_lt_one_log hy hy1 hc hT⟩
  · rw [mul_min_of_nonneg _ _ (Real.rpow_nonneg hy.le _), mul_one, le_min_iff,
      ← div_eq_mul_one_div]
    exact ⟨norm_perronIntegral_gt_one_le hy1 hc hcT, norm_perronIntegral_gt_one_log hy1 hc hT⟩

/-- **Davenport, Ch. 17, p. 104, (B) (row 17-5)**: the discontinuous integral
`(1/2πi) ∫_{c-i∞}^{c+i∞} y^s/s ds = 0, 1/2, 1` for `0 < y < 1`, `y = 1`, `y > 1` (`c > 0`),
as the limit of the symmetric integrals `I(y, T)` as `T → ∞`. -/
@[kb "davenport1980" "Ch 17, p. 104"]
theorem Davenport.perron_discontinuous_integral {y c : ℝ} (hy : 0 < y) (hc : 0 < c) :
    Tendsto (fun T ↦ perronIntegral y c T) atTop
      (𝓝 (if y < 1 then 0 else if y = 1 then 1 / 2 else 1)) := by
  have hπ := Real.pi_pos
  rcases lt_trichotomy y 1 with hy1 | hy1 | hy1
  · rw [show (if y < 1 then (0 : ℂ) else if y = 1 then 1 / 2 else 1) = 0 from (by simp [hy1])]
    have hl : 0 < |Real.log y| := abs_pos.mpr (Real.log_neg hy hy1).ne
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun T ↦ norm_nonneg _)
      ((eventually_gt_atTop 0).mono fun T hT ↦ norm_perronIntegral_lt_one_log hy hy1 hc hT) ?_
    have : Tendsto (fun T : ℝ ↦ y ^ c / (π * |Real.log y|) * T⁻¹) atTop (𝓝 (y ^ c /
        (π * |Real.log y|) * 0)) := tendsto_const_nhds.mul tendsto_inv_atTop_zero
    rw [mul_zero] at this
    refine this.congr' ((eventually_gt_atTop 0).mono fun T hT ↦ ?_)
    field_simp
  · subst hy1
    rw [show (if (1 : ℝ) < 1 then (0 : ℂ) else if (1 : ℝ) = 1 then 1 / 2 else 1) = 1 / 2 from
      (by simp)]
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun T ↦ norm_nonneg _)
      ((eventually_gt_atTop 0).mono fun T hT ↦ norm_perronIntegral_one_sub_half hc hT) ?_
    have : Tendsto (fun T : ℝ ↦ c / π * T⁻¹) atTop (𝓝 (c / π * 0)) :=
      tendsto_const_nhds.mul tendsto_inv_atTop_zero
    rw [mul_zero] at this
    refine this.congr' ((eventually_gt_atTop 0).mono fun T hT ↦ ?_)
    field_simp
  · rw [show (if y < 1 then (0 : ℂ) else if y = 1 then 1 / 2 else 1) = 1 from
      (by simp [not_lt.mpr hy1.le, hy1.ne'])]
    have hl : 0 < |Real.log y| := abs_pos.mpr (Real.log_pos hy1).ne'
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun T ↦ norm_nonneg _)
      ((eventually_gt_atTop 0).mono fun T hT ↦ norm_perronIntegral_gt_one_log hy1 hc hT) ?_
    have : Tendsto (fun T : ℝ ↦ y ^ c / (π * |Real.log y|) * T⁻¹) atTop (𝓝 (y ^ c /
        (π * |Real.log y|) * 0)) := tendsto_const_nhds.mul tendsto_inv_atTop_zero
    rw [mul_zero] at this
    refine this.congr' ((eventually_gt_atTop 0).mono fun T hT ↦ ?_)
    field_simp

end NTKB
