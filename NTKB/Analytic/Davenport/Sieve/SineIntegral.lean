/- Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import NTKB.Attr

/-!
# The sine integral (Davenport, Chapter 17)

Let `F(X) = ∫₀^X sin u / u du`. We prove, by elementary means:

* `sineInt_tail_bound`: `|∫_X^Y sin u / u du| ≤ 2 / X` for `0 < X ≤ Y` (integration by parts);
* `sineInt_exists_limit`: `F(X)` converges as `X → ∞` to some `K`, with `|F(X) - K| ≤ 2 / X`;
* `sineInt_tendsto_pi_div_two`: the limit is `π / 2` (the Dirichlet integral), and so
  `|F(X) - π / 2| ≤ 2 / X` (`sineInt_error_pi_div_two`).

The value of the limit is found along `X = (n + ½) π` using the Dirichlet kernel
`sin((n+½)x) = 2 sin(x/2) (½ + ∑_{k=1}^n cos(kx))` and a Riemann–Lebesgue argument for
`h(x) = 1/x - 1/(2 sin(x/2))` (one integration by parts on `[ε, π]`, and the bound `|h x| ≤ x`
on `(0, 1]`).
-/

open Real MeasureTheory Filter Topology

namespace NTKB.Davenport

/-! ### Basic integrability -/

lemma sineInt_abs_le_one (u : ℝ) : |sin u / u| ≤ 1 := by
  by_cases hu : u = 0
  · simp [hu]
  · rw [← sinc_of_ne_zero hu]; exact abs_sinc_le_one u

lemma sineInt_intervalIntegrable (a b : ℝ) :
    IntervalIntegrable (fun u : ℝ => sin u / u) volume a b := by
  refine (intervalIntegrable_const (c := (1:ℝ))).mono_fun ?_ ?_
  · exact (by fun_prop : Measurable fun u : ℝ => sin u / u).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun u => by
      simp only [Real.norm_eq_abs, abs_one]; exact sineInt_abs_le_one u

lemma sineInt_scale_eq {l : ℝ} (hl : l ≠ 0) (x : ℝ) :
    sin (l * x) / x = l * (sin (l * x) / (l * x)) := by
  by_cases hx : x = 0
  · simp [hx]
  · field_simp

lemma sineInt_integrable_scaled {l : ℝ} (hl : 0 < l) (a b : ℝ) :
    IntervalIntegrable (fun x : ℝ => sin (l * x) / x) volume a b := by
  refine (intervalIntegrable_const (c := l)).mono_fun ?_ ?_
  · exact (by fun_prop : Measurable fun x : ℝ => sin (l * x) / x).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun x => ?_
    simp only [Real.norm_eq_abs]
    rw [sineInt_scale_eq hl.ne', abs_mul, abs_of_pos hl]
    exact mul_le_of_le_one_right hl.le (sineInt_abs_le_one _)

/-! ### Part 1: the tail bound -/

lemma sineInt_mem_aux {X Y x : ℝ} (hXY : X ≤ Y) (hx : x ∈ Set.uIcc X Y) : X ≤ x := by
  rw [Set.uIcc_of_le hXY] at hx; exact hx.1

lemma sineInt_tail_aux {X Y : ℝ} (hX : 0 < X) (hXY : X ≤ Y) :
    ∫ u in X..Y, sin u / u =
      Y⁻¹ * (-cos Y) - X⁻¹ * (-cos X) - ∫ u in X..Y, (-(u ^ 2)⁻¹) * (-cos u) := by
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := X) (b := Y)
    (u := fun x : ℝ => x⁻¹) (u' := fun x => -(x ^ 2)⁻¹) (v := fun x => -cos x) (v' := sin)
    (fun x hx => hasDerivAt_inv (lt_of_lt_of_le hX (sineInt_mem_aux hXY hx)).ne')
    (fun x _ => by convert (hasDerivAt_cos x).neg using 1; simp)
    (ContinuousOn.intervalIntegrable
      (((by fun_prop : ContinuousOn (fun x : ℝ => x ^ 2) _).inv₀
        (fun x hx => pow_ne_zero 2 (lt_of_lt_of_le hX (sineInt_mem_aux hXY hx)).ne')).neg))
    (continuous_sin.intervalIntegrable _ _)
  calc ∫ u in X..Y, sin u / u = ∫ u in X..Y, u⁻¹ * sin u := by simp_rw [div_eq_inv_mul]
    _ = _ := h

lemma sineInt_inv_sq_integral {X Y : ℝ} (hX : 0 < X) (hXY : X ≤ Y) :
    ∫ u in X..Y, (u ^ 2)⁻¹ = X⁻¹ - Y⁻¹ := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := X) (b := Y)
    (f := fun x : ℝ => -x⁻¹) (f' := fun x => (x ^ 2)⁻¹)
    (fun x hx => by
      convert (hasDerivAt_inv (lt_of_lt_of_le hX (sineInt_mem_aux hXY hx)).ne').neg using 1
      simp)
    (ContinuousOn.intervalIntegrable
      ((by fun_prop : ContinuousOn (fun x : ℝ => x ^ 2) _).inv₀
        (fun x hx => pow_ne_zero 2 (lt_of_lt_of_le hX (sineInt_mem_aux hXY hx)).ne')))
  rw [h]; ring

/-- Tail bound for the sine integral: `|∫_X^Y sin u / u du| ≤ 2 / X` for `0 < X ≤ Y`. -/
@[kb "davenport1980" "Ch 17, p. 105"]
theorem sineInt_tail_bound {X Y : ℝ} (hX : 0 < X) (hXY : X ≤ Y) :
    |∫ u in X..Y, sin u / u| ≤ 2 / X := by
  rw [sineInt_tail_aux hX hXY]
  have hY : 0 < Y := lt_of_lt_of_le hX hXY
  have hint : ∫ u in X..Y, (-(u ^ 2)⁻¹) * (-cos u) = ∫ u in X..Y, (u ^ 2)⁻¹ * cos u := by
    congr 1; funext u; ring
  have hI : |∫ u in X..Y, (u ^ 2)⁻¹ * cos u| ≤ X⁻¹ - Y⁻¹ := by
    rw [← sineInt_inv_sq_integral hX hXY]
    have := intervalIntegral.norm_integral_le_of_norm_le (a := X) (b := Y) (μ := volume)
      (f := fun u : ℝ => (u ^ 2)⁻¹ * cos u) (g := fun u : ℝ => (u ^ 2)⁻¹) hXY
      (Filter.Eventually.of_forall fun u hu => by
        have hu0 : 0 < u := lt_trans hX hu.1
        rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact mul_le_of_le_one_right (by positivity) (abs_cos_le_one u))
      (ContinuousOn.intervalIntegrable
        ((by fun_prop : ContinuousOn (fun x : ℝ => x ^ 2) _).inv₀
          (fun x hx => pow_ne_zero 2 (lt_of_lt_of_le hX (sineInt_mem_aux hXY hx)).ne')))
    simpa [Real.norm_eq_abs] using this
  have hab : Y⁻¹ ≤ X⁻¹ := inv_anti₀ hX hXY
  have hA : |Y⁻¹ * (-cos Y)| ≤ Y⁻¹ := by
    rw [abs_mul, abs_neg, abs_of_pos (inv_pos.2 hY)]
    exact mul_le_of_le_one_right (inv_pos.2 hY).le (abs_cos_le_one Y)
  have hB : |X⁻¹ * (-cos X)| ≤ X⁻¹ := by
    rw [abs_mul, abs_neg, abs_of_pos (inv_pos.2 hX)]
    exact mul_le_of_le_one_right (inv_pos.2 hX).le (abs_cos_le_one X)
  rw [hint, div_eq_mul_inv]
  rw [abs_le] at hA hB hI ⊢
  constructor <;> linarith [hA.1, hA.2, hB.1, hB.2, hI.1, hI.2]

/-! ### Part 2: existence of the limit -/

/-- The improper integral `∫₀^∞ sin u / u du` converges, with error `≤ 2 / X`. -/
@[kb "davenport1980" "Ch 17, p. 105"]
theorem sineInt_exists_limit :
    ∃ K : ℝ, Tendsto (fun X : ℝ ↦ ∫ u in (0:ℝ)..X, sin u / u) atTop (𝓝 K) ∧
      ∀ X : ℝ, 0 < X → |(∫ u in (0:ℝ)..X, sin u / u) - K| ≤ 2 / X := by
  set F : ℝ → ℝ := fun X ↦ ∫ u in (0:ℝ)..X, sin u / u with hF
  have hdiff : ∀ X Y : ℝ, X ≤ Y → F Y - F X = ∫ u in X..Y, sin u / u := fun X Y _ ↦
    intervalIntegral.integral_interval_sub_left (sineInt_intervalIntegrable _ _)
      (sineInt_intervalIntegrable _ _)
  have hdiff' : ∀ X Y : ℝ, 0 < X → X ≤ Y → |F X - F Y| ≤ 2 / X := fun X Y hX hXY ↦ by
    rw [abs_sub_comm, hdiff X Y hXY]; exact sineInt_tail_bound hX hXY
  have hcauchy : CauchySeq F := by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    refine ⟨4 / ε, fun n hn ↦ ?_⟩
    have hN : 0 < 4 / ε := by positivity
    rw [Real.dist_eq]
    have := hdiff' (4 / ε) n hN hn
    have e : (2:ℝ) / (4 / ε) = ε / 2 := by
      rw [div_div_eq_mul_div]; ring
    rw [abs_sub_comm]
    linarith
  obtain ⟨K, hK⟩ := cauchySeq_tendsto_of_complete hcauchy
  refine ⟨K, hK, fun X hX ↦ ?_⟩
  have hlim : Tendsto (fun Y ↦ |F X - F Y|) atTop (𝓝 |F X - K|) :=
    (tendsto_const_nhds.sub hK).abs
  exact le_of_tendsto hlim (eventually_atTop.2 ⟨X, fun Y hY ↦ hdiff' X Y hX hY⟩)

/-! ### Part 3: the value `π / 2` -/

/-- The Dirichlet kernel identity `sin((n+½)x) = 2 sin(x/2) (½ + ∑_{k=1}^n cos(kx))`. -/
lemma sineInt_dirichlet_id (n : ℕ) (x : ℝ) :
    sin (((n:ℝ) + 1 / 2) * x) =
      2 * sin (x / 2) * (1 / 2 + ∑ k ∈ Finset.range n, cos (((k:ℝ) + 1) * x)) := by
  induction n with
  | zero =>
    rw [show (((0:ℕ):ℝ) + 1 / 2) * x = x / 2 by push_cast; ring, Finset.sum_range_zero]
    ring
  | succ n ih =>
    have e1 : (((n + 1 : ℕ) : ℝ) + 1 / 2) * x = ((n:ℝ) + 1) * x + x / 2 := by push_cast; ring
    have e2 : ((n:ℝ) + 1 / 2) * x = ((n:ℝ) + 1) * x - x / 2 := by ring
    have key : sin (((n:ℝ) + 1) * x + x / 2) =
        sin (((n:ℝ) + 1) * x - x / 2) + 2 * sin (x / 2) * cos (((n:ℝ) + 1) * x) := by
      rw [sin_add, sin_sub]; ring
    rw [Finset.sum_range_succ, e1, key, ← e2, ih]; ring

lemma sineInt_dirichlet_integral (n : ℕ) :
    ∫ x in (0:ℝ)..π, (1 / 2 + ∑ k ∈ Finset.range n, cos (((k:ℝ) + 1) * x)) = π / 2 := by
  have hk : ∀ k ∈ Finset.range n,
      ∫ x in (0:ℝ)..π, cos (((k:ℝ) + 1) * x) = 0 := by
    intro k _
    have hc : ((k:ℝ) + 1) ≠ 0 := by positivity
    have h2 : ∫ x in (0:ℝ)..π, cos (((k:ℝ) + 1) * x) =
        ((k:ℝ) + 1)⁻¹ • ∫ u in ((k:ℝ) + 1) * 0..((k:ℝ) + 1) * π, cos u :=
      intervalIntegral.integral_comp_mul_left (fun u => cos u) hc
    rw [h2, integral_cos]
    have := Real.sin_nat_mul_pi (k + 1)
    push_cast at this
    simp [this]
  rw [intervalIntegral.integral_add (by simp)
    (Continuous.intervalIntegrable
      (by fun_prop : Continuous fun x : ℝ =>
        ∑ k ∈ Finset.range n, cos (((k:ℝ) + 1) * x)) _ _),
    intervalIntegral.integral_finsetSum (f := fun (k : ℕ) (x : ℝ) => cos (((k:ℝ) + 1) * x))
      (fun k _ => (by fun_prop : Continuous fun x : ℝ =>
      cos (((k:ℝ) + 1) * x)).intervalIntegrable _ _), Finset.sum_congr rfl hk]
  simp
  ring

lemma sineInt_subst {l : ℝ} (hl : 0 < l) :
    ∫ x in (0:ℝ)..π, sin (l * x) / x = ∫ u in (0:ℝ)..(l * π), sin u / u := by
  have h2 : ∫ x in (0:ℝ)..π, sin (l * x) / (l * x) =
      l⁻¹ • ∫ u in l * 0..l * π, sin u / u :=
    intervalIntegral.integral_comp_mul_left (fun u => sin u / u) hl.ne'
  rw [mul_zero] at h2
  have h3 : (fun x : ℝ => sin (l * x) / x) = fun x => l * (sin (l * x) / (l * x)) :=
    funext (sineInt_scale_eq hl.ne')
  rw [h3, intervalIntegral.integral_const_mul, h2, smul_eq_mul, ← mul_assoc,
    mul_inv_cancel₀ hl.ne', one_mul]

/-- `h(x) = 1/x - 1/(2 sin(x/2))`, extended by `0` at `0` (the continuous extension). -/
noncomputable abbrev sineInt_h (x : ℝ) : ℝ := x⁻¹ - (2 * sin (x / 2))⁻¹

lemma sineInt_h_small {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) : |sineInt_h x| ≤ x := by
  have hs : sin (x / 2) ≤ x / 2 := Real.sin_le (by positivity)
  have hs2 : x / 2 - (x / 2) ^ 3 / 6 < sin (x / 2) := Real.sin_gt_sub_cube (by positivity)
  have hx2 : x ^ 2 ≤ 1 := by nlinarith
  have hx3 : x ^ 3 ≤ x := by nlinarith [mul_le_mul_of_nonneg_left hx2 hx.le]
  have hs3 : x / 4 ≤ sin (x / 2) := by nlinarith
  have hs0 : 0 < sin (x / 2) := by linarith
  have hh : sineInt_h x = (2 * sin (x / 2) - x) / (2 * x * sin (x / 2)) := by
    unfold sineInt_h; field_simp
  have hpos : 0 < 2 * x * sin (x / 2) := by positivity
  rw [hh, abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
  have hxs : x ^ 2 * (x / 4) ≤ x ^ 2 * sin (x / 2) := mul_le_mul_of_nonneg_left hs3 (sq_nonneg x)
  have hx3' : 0 ≤ x ^ 3 := by positivity
  rw [abs_le]
  constructor <;> nlinarith

lemma sineInt_h_deriv {x : ℝ} (hx : 0 < x) (hx2 : x ≤ π) :
    HasDerivAt sineInt_h (-(x ^ 2)⁻¹ + cos (x / 2) / (4 * sin (x / 2) ^ 2)) x := by
  have hs : sin (x / 2) ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_pos])).ne'
  have h1 : HasDerivAt (fun y : ℝ => y⁻¹) (-(x ^ 2)⁻¹) x := hasDerivAt_inv hx.ne'
  have h2 : HasDerivAt (fun y : ℝ => 2 * sin (y / 2)) (2 * (cos (x / 2) * (1 / 2))) x := by
    have := (((hasDerivAt_id' x).div_const 2).sin).const_mul 2
    simpa using this
  have h3 := h2.inv (mul_ne_zero two_ne_zero hs)
  convert h1.sub h3 using 1
  field_simp
  ring

lemma sineInt_h'_cont {ε : ℝ} (hε : 0 < ε) :
    ContinuousOn (fun x : ℝ => -(x ^ 2)⁻¹ + cos (x / 2) / (4 * sin (x / 2) ^ 2))
      (Set.Icc ε π) := by
  have hne : ∀ x ∈ Set.Icc ε π, x ≠ 0 := fun x hx => (lt_of_lt_of_le hε hx.1).ne'
  have hs : ∀ x ∈ Set.Icc ε π, sin (x / 2) ≠ 0 := fun x hx =>
    (Real.sin_pos_of_pos_of_lt_pi (by linarith [hx.1]) (by linarith [hx.2, Real.pi_pos])).ne'
  apply ContinuousOn.add
  · exact ((by fun_prop : ContinuousOn (fun x : ℝ => x ^ 2) _).inv₀
      (fun x hx => pow_ne_zero 2 (hne x hx))).neg
  · have hc : Continuous (fun x : ℝ => cos (x / 2)) :=
      continuous_cos.comp (continuous_id.div_const 2)
    have hd : Continuous (fun x : ℝ => 4 * sin (x / 2) ^ 2) :=
      continuous_const.mul ((continuous_sin.comp (continuous_id.div_const 2)).pow 2)
    exact hc.continuousOn.div hd.continuousOn
      (fun x hx => mul_ne_zero (ne_of_gt (by norm_num : (0:ℝ) < 4)) (pow_ne_zero 2 (hs x hx)))

/-- Riemann–Lebesgue on `[ε, π]` for `h`, by one integration by parts. -/
lemma sineInt_tail_osc {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ C : ℝ, ∀ l : ℝ, 0 < l →
      |∫ x in ε..π, sineInt_h x * sin (l * x)| ≤ C / l := by
  have hεπ : ε ≤ π := by linarith [Real.pi_gt_three]
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := ε) (b := π)).exists_bound_of_continuousOn
    (sineInt_h'_cont hε)
  refine ⟨|sineInt_h π| + |sineInt_h ε| + M * π, fun l hl => ?_⟩
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM ε ⟨le_rfl, hεπ⟩)
  have hpos : ∀ x ∈ Set.uIcc ε π, 0 < x := fun x hx => by
    rw [Set.uIcc_of_le hεπ] at hx; exact lt_of_lt_of_le hε hx.1
  have hle : ∀ x ∈ Set.uIcc ε π, x ≤ π := fun x hx => by
    rw [Set.uIcc_of_le hεπ] at hx; exact hx.2
  have hv : ∀ x : ℝ, HasDerivAt (fun y : ℝ => -cos (l * y) / l) (sin (l * x)) x := by
    intro x
    have := (((hasDerivAt_id' x).const_mul l).cos.neg).div_const l
    convert this using 1
    field_simp
  have hbyp := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := ε) (b := π)
    (u := sineInt_h) (u' := fun x => -(x ^ 2)⁻¹ + cos (x / 2) / (4 * sin (x / 2) ^ 2))
    (v := fun y : ℝ => -cos (l * y) / l) (v' := fun x => sin (l * x))
    (fun x hx => sineInt_h_deriv (hpos x hx) (hle x hx)) (fun x _ => hv x)
    ((sineInt_h'_cont hε).intervalIntegrable_of_Icc hεπ)
    (by apply Continuous.intervalIntegrable; fun_prop)
  rw [hbyp]
  have hvb : ∀ x : ℝ, |-cos (l * x) / l| ≤ 1 / l := fun x => by
    rw [abs_div, abs_neg, abs_of_pos hl]
    exact div_le_div_of_nonneg_right (abs_cos_le_one _) hl.le
  have hI : ‖∫ x in ε..π, (-(x ^ 2)⁻¹ + cos (x / 2) / (4 * sin (x / 2) ^ 2)) *
      (-cos (l * x) / l)‖ ≤ (M * (1 / l)) * |π - ε| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    rw [Set.uIoc_of_le hεπ] at hx
    rw [norm_mul]
    refine mul_le_mul (hM x ⟨hx.1.le, hx.2⟩) ?_ (norm_nonneg _) hM0
    rw [Real.norm_eq_abs]; exact hvb x
  have hc : 0 ≤ 1 / l := by positivity
  have hpe : |π - ε| ≤ π := by
    rw [abs_of_nonneg (by linarith)]; linarith
  have hA : |sineInt_h π * (-cos (l * π) / l)| ≤ |sineInt_h π| * (1 / l) := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hvb π) (abs_nonneg _)
  have hB : |sineInt_h ε * (-cos (l * ε) / l)| ≤ |sineInt_h ε| * (1 / l) := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hvb ε) (abs_nonneg _)
  have hI' : |∫ x in ε..π, (-(x ^ 2)⁻¹ + cos (x / 2) / (4 * sin (x / 2) ^ 2)) *
      (-cos (l * x) / l)| ≤ M * (1 / l) * π := by
    rw [← Real.norm_eq_abs]
    exact hI.trans (mul_le_mul_of_nonneg_left hpe (by positivity))
  have hfin : (|sineInt_h π| + |sineInt_h ε| + M * π) / l =
      |sineInt_h π| * (1 / l) + |sineInt_h ε| * (1 / l) + M * (1 / l) * π := by
    field_simp
  rw [hfin]
  rw [abs_le] at hA hB hI' ⊢
  constructor <;> linarith [hA.1, hA.2, hB.1, hB.2, hI'.1, hI'.2]

/-- Approximation of `F((n+½)π)` by `π/2`. -/
lemma sineInt_approx {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ C : ℝ, ∀ n : ℕ,
      |(∫ u in (0:ℝ)..(((n:ℝ) + 1 / 2) * π), sin u / u) - π / 2| ≤
        ε * ε + C / ((n:ℝ) + 1 / 2) := by
  obtain ⟨C, hC⟩ := sineInt_tail_osc hε hε1
  refine ⟨C, fun n => ?_⟩
  set l : ℝ := (n:ℝ) + 1 / 2 with hl_def
  have hl : 0 < l := by positivity
  have hεπ : ε ≤ π := by linarith [Real.pi_gt_three]
  set D : ℝ → ℝ := fun x => 1 / 2 + ∑ k ∈ Finset.range n, cos (((k:ℝ) + 1) * x) with hD
  have hDc : Continuous D := by rw [hD]; fun_prop
  set R : ℝ → ℝ := fun x => sin (l * x) / x - D x with hR
  have hRint : ∀ a b : ℝ, IntervalIntegrable R volume a b := fun a b =>
    (sineInt_integrable_scaled hl a b).sub (hDc.intervalIntegrable a b)
  have hRsplit : ∫ x in (0:ℝ)..π, R x = (∫ u in (0:ℝ)..(l * π), sin u / u) - π / 2 := by
    rw [hR, intervalIntegral.integral_sub (sineInt_integrable_scaled hl 0 π)
      (hDc.intervalIntegrable 0 π), sineInt_subst hl, hD, sineInt_dirichlet_integral]
  have hReq : ∀ x ∈ Set.Ioc (0:ℝ) π, R x = sineInt_h x * sin (l * x) := by
    intro x hx
    have hs : sin (x / 2) ≠ 0 :=
      (Real.sin_pos_of_pos_of_lt_pi (by linarith [hx.1])
        (by linarith [hx.2, Real.pi_pos])).ne'
    have hDx : D x = sin (l * x) / (2 * sin (x / 2)) := by
      rw [hD, hl_def]
      simp only
      rw [eq_div_iff (mul_ne_zero two_ne_zero hs), sineInt_dirichlet_id n x]
      ring
    rw [hR]
    simp only
    rw [hDx]
    unfold sineInt_h
    ring
  have hsplit : ∫ x in (0:ℝ)..π, R x =
      (∫ x in (0:ℝ)..ε, R x) + ∫ x in ε..π, R x :=
    (intervalIntegral.integral_add_adjacent_intervals (hRint _ _) (hRint _ _)).symm
  have h1 : |∫ x in (0:ℝ)..ε, R x| ≤ ε * ε := by
    have e : ∫ x in (0:ℝ)..ε, R x = ∫ x in (0:ℝ)..ε, sineInt_h x * sin (l * x) := by
      rw [intervalIntegral.integral_of_le hε.le, intervalIntegral.integral_of_le hε.le]
      exact setIntegral_congr_fun measurableSet_Ioc
        (fun x hx => hReq x ⟨hx.1, hx.2.trans hεπ⟩)
    rw [e, ← Real.norm_eq_abs]
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := ε)
      (f := fun x => sineInt_h x * sin (l * x)) (C := ε) (fun x hx => by
        rw [Set.uIoc_of_le hε.le] at hx
        rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
        calc |sineInt_h x| * |sin (l * x)| ≤ x * 1 :=
              mul_le_mul (sineInt_h_small hx.1 (hx.2.trans hε1)) (abs_sin_le_one _)
                (abs_nonneg _) hx.1.le
          _ ≤ ε := by linarith [hx.2])
    simpa [abs_of_pos hε] using this
  have h2 : ∫ x in ε..π, R x = ∫ x in ε..π, sineInt_h x * sin (l * x) := by
    refine intervalIntegral.integral_congr (fun x hx => ?_)
    rw [Set.uIcc_of_le hεπ] at hx
    exact hReq x ⟨lt_of_lt_of_le hε hx.1, hx.2⟩
  have h3 := hC l hl
  rw [← hRsplit, hsplit, h2]
  calc |(∫ x in (0:ℝ)..ε, R x) + ∫ x in ε..π, sineInt_h x * sin (l * x)|
      ≤ |∫ x in (0:ℝ)..ε, R x| + |∫ x in ε..π, sineInt_h x * sin (l * x)| := abs_add_le _ _
    _ ≤ ε * ε + C / l := add_le_add h1 h3

/-- The Dirichlet integral: `∫₀^∞ sin u / u du = π / 2`. -/
@[kb "davenport1980" "Ch 17, p. 105"]
theorem sineInt_tendsto_pi_div_two :
    Tendsto (fun X : ℝ ↦ ∫ u in (0:ℝ)..X, sin u / u) atTop (𝓝 (π / 2)) := by
  obtain ⟨K, hK, hKb⟩ := sineInt_exists_limit
  have hKe : K = π / 2 := by
    refine eq_of_abs_sub_le_all (fun δ hδ => ?_)
    set ε : ℝ := min 1 (δ / 4) with hε_def
    have hε : 0 < ε := lt_min one_pos (by positivity)
    have hε1 : ε ≤ 1 := min_le_left _ _
    have hε2 : ε ≤ δ / 4 := min_le_right _ _
    obtain ⟨C, hC⟩ := sineInt_approx hε hε1
    obtain ⟨n, hn⟩ := exists_nat_gt ((4 + 4 * |C|) / δ)
    set l : ℝ := (n:ℝ) + 1 / 2 with hl_def
    have hl : 0 < l := by positivity
    have hlδ : 4 + 4 * |C| < l * δ := by
      have := (div_lt_iff₀ hδ).1 hn
      have h0 : (n:ℝ) ≤ l := by rw [hl_def]; linarith
      nlinarith
    have hX : 0 < l * π := by positivity
    have e1 := hKb (l * π) hX
    have e2 := hC n
    have hpi := Real.pi_gt_three
    have hq1 : 2 / (l * π) ≤ δ / 4 := by
      rw [div_le_iff₀ hX]
      nlinarith [abs_nonneg C]
    have hq2 : C / l ≤ δ / 4 := by
      rw [div_le_iff₀ hl]
      nlinarith [le_abs_self C]
    have hq3 : ε * ε ≤ δ / 4 := by nlinarith
    calc |K - π / 2| = |(K - ∫ u in (0:ℝ)..(l * π), sin u / u) +
            ((∫ u in (0:ℝ)..(l * π), sin u / u) - π / 2)| := by ring_nf
      _ ≤ |K - ∫ u in (0:ℝ)..(l * π), sin u / u| +
            |(∫ u in (0:ℝ)..(l * π), sin u / u) - π / 2| := abs_add_le _ _
      _ ≤ δ := by
        rw [abs_sub_comm K]
        linarith
  rw [← hKe]; exact hK

/-- `|∫₀^X sin u / u du - π / 2| ≤ 2 / X`. -/
@[kb "davenport1980" "Ch 17, p. 105"]
theorem sineInt_error_pi_div_two {X : ℝ} (hX : 0 < X) :
    |(∫ u in (0:ℝ)..X, sin u / u) - π / 2| ≤ 2 / X := by
  obtain ⟨K, hK, hKb⟩ := sineInt_exists_limit
  have hKe : K = π / 2 := tendsto_nhds_unique hK sineInt_tendsto_pi_div_two
  rw [← hKe]; exact hKb X hX

end NTKB.Davenport
