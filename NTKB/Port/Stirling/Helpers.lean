/-
Copyright (c) 2026 The Tau Ceti contributors and Robby Sneiderman. Released under Apache 2.0
license.
Copied into NTKB with credit from Tau Ceti (`TauCeti/Analysis/Calculus/Deriv/Fract.lean`,
`TauCeti/Analysis/Complex/SectorBounds.lean`, `TauCeti/Analysis/Complex/SlitPlane.lean`,
`TauCeti/Analysis/SpecialFunctions/Trigonometric/HalfAngle.lean`,
`TauCeti/Analysis/SpecialFunctions/Integrals/Basic.lean`,
`TauCeti/Analysis/SpecialFunctions/Gamma/Basic.lean`, main `1ff53249`); NTKB does not depend on
Tau Ceti. Changes: namespace `NTKB.Port`, only the declarations needed for the Stirling port
(`Int.`-, `Complex.`- and `Real.`-namespaced lemmas become `NTKB.Port.` ones).
Original authors: The Tau Ceti contributors; OpenAI Codex.
-/
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Auxiliary lemmas for the Stirling port

Small helper lemmas from Tau Ceti used by the sectorial digamma bounds and Stirling's formula:
the periodic quadratic `fract t ^ 2 - fract t`, norm bounds for real translates in sectors, the
slit plane, `1 - cos δ > 0`, and `∫ 1/(a+t)²`.
-/

open Set Filter Complex Real

namespace NTKB.Port

/-! ### The periodic quadratic `fract t ^ 2 - fract t` -/

/-- The function `t ↦ fract t ^ 2 - fract t` is continuous: `x ^ 2 - x` agrees at `0` and `1`. -/
theorem continuous_fract_sq_sub_fract :
    Continuous fun t : ℝ ↦ Int.fract t ^ 2 - Int.fract t :=
  ContinuousOn.comp_fract'' (f := fun x : ℝ ↦ x ^ 2 - x) (by fun_prop) (by norm_num)

/-- The function `t ↦ fract t ^ 2 - fract t` has right derivative `2 fract t - 1` at every
point. -/
theorem hasDerivWithinAt_fract_sq_sub_fract (t : ℝ) :
    HasDerivWithinAt (fun u : ℝ ↦ Int.fract u ^ 2 - Int.fract u) (2 * Int.fract t - 1)
      (Ioi t) t := by
  have hp : HasDerivAt (fun u : ℝ ↦ (u - ⌊t⌋) ^ 2 - (u - ⌊t⌋)) (2 * Int.fract t - 1) t := by
    have h := (((hasDerivAt_id' t).sub_const (⌊t⌋ : ℝ)).pow 2).sub
      ((hasDerivAt_id' t).sub_const (⌊t⌋ : ℝ))
    refine h.congr_deriv ?_
    rw [← Int.self_sub_floor]
    ring
  refine hp.hasDerivWithinAt.congr_of_eventuallyEq ?_ (by rw [← Int.self_sub_floor])
  filter_upwards [Ioo_mem_nhdsGT (Int.lt_floor_add_one t)] with u hu
  have hfl : ⌊u⌋ = ⌊t⌋ := by
    rw [Int.floor_eq_iff]
    exact ⟨(Int.floor_le t).trans hu.1.le, hu.2⟩
  rw [← Int.self_sub_floor, hfl]

/-- `|fract t ^ 2 - fract t| ≤ 1 / 4`, since `fract t ∈ [0, 1)`. -/
theorem abs_fract_sq_sub_fract_le (t : ℝ) : |Int.fract t ^ 2 - Int.fract t| ≤ 1 / 4 := by
  have h0 := Int.fract_nonneg t
  have h1 := Int.fract_lt_one t
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg (Int.fract t - 1 / 2)]

/-! ### Sector bounds and the slit plane -/

/-- If `(2c - 1) ‖s‖ ≤ re s` with `0 ≤ c ≤ 1`, then `c * (‖s‖ + t) ≤ ‖s + t‖` for every
nonnegative real `t`. -/
theorem mul_norm_add_le_norm_add_ofReal {s : ℂ} {c t : ℝ}
    (hc : 0 ≤ c) (hc1 : c ≤ 1) (ht : 0 ≤ t)
    (hs : (2 * c - 1) * ‖s‖ ≤ s.re) :
    c * (‖s‖ + t) ≤ ‖s + t‖ := by
  have hsq : ‖s + t‖ ^ 2 = ‖s‖ ^ 2 + 2 * t * s.re + t ^ 2 := by
    simp only [Complex.sq_norm, normSq_apply, add_re, ofReal_re, add_im, ofReal_im, add_zero]
    ring
  have h : c * (‖s‖ + t) ^ 2 ≤ ‖s + t‖ ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hc1) (sq_nonneg (‖s‖ - t)),
      mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 2 * t)]
  have hc2 : c ^ 2 ≤ c := by nlinarith
  have h2 : (c * (‖s‖ + t)) ^ 2 ≤ ‖s + t‖ ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hc2 (sq_nonneg (‖s‖ + t))]
  nlinarith [norm_nonneg (s + t)]

/-- On the closed sector `|arg s| ≤ π - δ`, translation by a nonnegative real `t` satisfies
`((1 - cos δ) / 2) * (‖s‖ + t) ≤ ‖s + t‖`. -/
theorem mul_norm_add_le_norm_add_ofReal_of_abs_arg_le {s : ℂ} {δ t : ℝ}
    (hδ : 0 < δ) (hs : |s.arg| ≤ Real.pi - δ) (ht : 0 ≤ t) :
    ((1 - Real.cos δ) / 2) * (‖s‖ + t) ≤ ‖s + t‖ := by
  apply mul_norm_add_le_norm_add_ofReal
  · linarith [Real.cos_le_one δ]
  · linarith [Real.neg_one_le_cos δ]
  · exact ht
  · have hcos := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg s.arg)
      (by linarith : Real.pi - δ ≤ Real.pi) hs
    rw [Real.cos_abs, Real.cos_pi_sub] at hcos
    have h := mul_le_mul_of_nonneg_left hcos (norm_nonneg s)
    rw [norm_mul_cos_arg] at h
    nlinarith

/-- A nonzero complex number with `|arg s| < π` lies in the slit plane. -/
theorem mem_slitPlane_of_abs_arg_lt {s : ℂ} (hs : |s.arg| < Real.pi) (hs0 : s ≠ 0) :
    s ∈ slitPlane :=
  mem_slitPlane_iff_arg.mpr ⟨fun h ↦ by rw [h, abs_of_pos Real.pi_pos] at hs; exact hs.false, hs0⟩

/-- A nonzero complex number in the closed sector `|arg s| ≤ π - δ`, with `0 < δ`, lies in the
slit plane. -/
theorem mem_slitPlane_of_abs_arg_le {s : ℂ} {δ : ℝ} (hδ : 0 < δ) (hs : |s.arg| ≤ Real.pi - δ)
    (hs0 : s ≠ 0) : s ∈ slitPlane :=
  mem_slitPlane_of_abs_arg_lt (by linarith) hs0

/-- Translating a point of the slit plane by a nonnegative real number keeps it in the slit
plane. -/
theorem ofReal_add_mem_slitPlane {z : ℂ} (hz : z ∈ slitPlane) {t : ℝ} (ht : 0 ≤ t) :
    (t : ℂ) + z ∈ slitPlane := by
  refine (mem_slitPlane_iff.mp hz).imp (fun h ↦ ?_) (fun h ↦ by simpa using h)
  rw [add_re, ofReal_re]
  positivity

/-- For `θ ∈ (0, 2π)`, `1 - cos θ` is positive. -/
theorem one_sub_cos_pos {θ : ℝ} (h₀ : 0 < θ) (h₁ : θ < 2 * π) : 0 < 1 - Real.cos θ :=
  sub_pos.2 <| (Real.cos_le_one θ).lt_of_ne fun h ↦
    h₀.ne' ((cos_eq_one_iff_of_lt_of_lt (by linarith [pi_pos]) h₁).1 h)

/-- A complex number with positive real part is not a nonpositive integer. -/
theorem ne_neg_natCast_of_re_pos {b : ℂ} (hb : 0 < b.re) (n : ℕ) :
    b ≠ -(n : ℂ) := by
  intro h
  have heq := congrArg re h
  simp only [neg_re, natCast_re] at heq
  linarith [n.cast_nonneg (α := ℝ)]

/-! ### An elementary integral -/

open intervalIntegral in
/-- The reciprocal-square kernel has an elementary integral on each nonnegative interval:
`∫ t in 0..b, 1 / (a + t)² = a⁻¹ - (a + b)⁻¹` for `a > 0` and `b ≥ 0`. -/
theorem integral_one_div_add_sq {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) :
    ∫ t : ℝ in 0..b, 1 / (a + t) ^ 2 = a⁻¹ - (a + b)⁻¹ := by
  have hd (t : ℝ) (ht : t ∈ uIcc 0 b) :
      HasDerivAt (fun u : ℝ ↦ -(a + u)⁻¹) (1 / (a + t) ^ 2) t := by
    rw [uIcc_of_le hb] at ht
    have h := (((hasDerivAt_id t).const_add a).inv
      (by linarith [ht.1] : a + t ≠ 0)).neg
    convert h using 1
    · ext u
      rfl
    · simp [neg_div]
  have hc : ContinuousOn (fun t : ℝ ↦ 1 / (a + t) ^ 2) (Icc 0 b) :=
    ContinuousOn.div (f := fun _ : ℝ ↦ (1 : ℝ)) (g := fun t : ℝ ↦ (a + t) ^ 2)
      continuousOn_const (by fun_prop) (fun t ht ↦ by have := ht.1; positivity)
  simpa [sub_eq_add_neg, add_comm] using integral_eq_sub_of_hasDerivAt hd
    (hc.intervalIntegrable_of_Icc hb)

end NTKB.Port
