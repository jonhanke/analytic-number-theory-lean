/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Davenport.Zeros.ZetaArg

/-!
# The change of argument by continuous variation

Davenport states the argument principle (Ch. 15, 16) as `2π N = Δ_R arg f(s)`, the change of the
argument of `f` "by continuous variation" around a rectangle. This file makes that notion precise
for a function `φ : ℝ → ℂ` of a real parameter (the value of `f` along one side of the contour):

* `IsContArg φ θ a b`: `θ` is a continuous real function on `[[a, b]]` with
  `φ t = |φ t| e^{iθ(t)}` there (a continuous choice of the argument);
* `IsArgChange φ a b Δ`: some continuous argument `θ` has `θ b - θ a = Δ`;
* `argChange φ a b`: that `Δ` (it does not depend on the choice of `θ` when `φ` does not vanish:
  `IsArgChange.unique`; it is `0` by convention when there is no continuous argument).

The change of argument is the imaginary part of the integral of the log-derivative
(`isArgChange_of_hasDerivAt`), and it behaves as expected under reversal of the path, complex
conjugation and the reflection `t ↦ c - t`. Source text unavailable: the notion is
the standard one, in our words.
-/

open Filter Topology Complex Set
open scoped Real Interval ComplexConjugate

namespace NTKB

/-- `θ` is a continuous argument of `φ` on `[[a, b]]`: `θ` is continuous there and
`φ t = |φ t| e^{iθ(t)}` for every `t ∈ [[a, b]]`. -/
def IsContArg (φ : ℝ → ℂ) (θ : ℝ → ℝ) (a b : ℝ) : Prop :=
  ContinuousOn θ [[a, b]] ∧ ∀ t ∈ [[a, b]], φ t = ‖φ t‖ * Complex.exp (θ t * I)

/-- `Δ` is a change of the argument of `φ` from `a` to `b` by continuous variation. -/
def IsArgChange (φ : ℝ → ℂ) (a b Δ : ℝ) : Prop :=
  ∃ θ : ℝ → ℝ, IsContArg φ θ a b ∧ θ b - θ a = Δ

open Classical in
/-- **The change of argument of `φ` from `a` to `b` by continuous variation** (Davenport's
`Δ arg`): the common value `θ b - θ a` of the continuous arguments `θ` of `φ` on `[[a, b]]`
(`0` if `φ` has no continuous argument there). -/
noncomputable def argChange (φ : ℝ → ℂ) (a b : ℝ) : ℝ :=
  if h : ∃ Δ, IsArgChange φ a b Δ then h.choose else 0

/-- An integer-valued continuous function on an interval has equal endpoint values. -/
theorem int_valued_endpoints {f : ℝ → ℝ} {a b : ℝ} (hf : ContinuousOn f [[a, b]])
    (h : ∀ t ∈ [[a, b]], ∃ n : ℤ, f t = n) : f a = f b := by
  obtain ⟨m, hm⟩ := h a left_mem_uIcc
  obtain ⟨n, hn⟩ := h b right_mem_uIcc
  by_contra hne
  have hmn : m ≠ n := by
    rintro rfl
    exact hne (hm.trans hn.symm)
  have hv : ((min m n : ℤ) : ℝ) + 1 / 2 ∈ [[f a, f b]] := by
    rw [hm, hn, Set.mem_uIcc]
    rcases lt_or_gt_of_ne hmn with h' | h'
    · have hc : (m : ℝ) + 1 ≤ n := by exact_mod_cast (by omega : m + 1 ≤ n)
      left
      rw [min_eq_left h'.le]
      constructor <;> linarith
    · have hc : (n : ℝ) + 1 ≤ m := by exact_mod_cast (by omega : n + 1 ≤ m)
      right
      rw [min_eq_right h'.le]
      constructor <;> linarith
  obtain ⟨t, ht, hft⟩ := intermediate_value_uIcc hf hv
  obtain ⟨k, hk⟩ := h t ht
  rw [hk] at hft
  have h1 : (2 * (k - min m n) : ℝ) = 1 := by linarith
  have h2 : 2 * (k - min m n) = 1 := by exact_mod_cast h1
  omega

/-- Two continuous arguments of a nonvanishing function differ by a constant, so the change of
argument does not depend on the choice. -/
theorem IsArgChange.unique {φ : ℝ → ℂ} {a b Δ₁ Δ₂ : ℝ} (h0 : ∀ t ∈ [[a, b]], φ t ≠ 0)
    (h₁ : IsArgChange φ a b Δ₁) (h₂ : IsArgChange φ a b Δ₂) : Δ₁ = Δ₂ := by
  obtain ⟨θ₁, ⟨hc1, he1⟩, hΔ1⟩ := h₁
  obtain ⟨θ₂, ⟨hc2, he2⟩, hΔ2⟩ := h₂
  have key : (fun t ↦ (θ₁ t - θ₂ t) / (2 * π)) a = (fun t ↦ (θ₁ t - θ₂ t) / (2 * π)) b := by
    refine int_valued_endpoints ((hc1.sub hc2).div_const _) fun t ht ↦ ?_
    have hn0 : (‖φ t‖ : ℂ) ≠ 0 := by
      exact_mod_cast norm_ne_zero_iff.mpr (h0 t ht)
    have hE : Complex.exp (θ₁ t * I) = Complex.exp (θ₂ t * I) := by
      refine mul_left_cancel₀ hn0 ?_
      rw [← he1 t ht, ← he2 t ht]
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp hE
    refine ⟨n, ?_⟩
    have h3 : (((θ₁ t - θ₂ t - n * (2 * π) : ℝ)) : ℂ) * I = 0 := by
      push_cast
      linear_combination hn
    rcases mul_eq_zero.mp h3 with h4 | h4
    · have h5 : θ₁ t - θ₂ t - n * (2 * π) = 0 := by exact_mod_cast h4
      show (θ₁ t - θ₂ t) / (2 * π) = n
      rw [div_eq_iff (by positivity)]
      linarith
    · exact absurd h4 I_ne_zero
  simp only at key
  have hpi : (2 * π) ≠ 0 := by positivity
  have key2 : θ₁ a - θ₂ a = θ₁ b - θ₂ b := by
    field_simp at key
    exact key
  linarith

theorem argChange_eq {φ : ℝ → ℂ} {a b Δ : ℝ} (h0 : ∀ t ∈ [[a, b]], φ t ≠ 0)
    (h : IsArgChange φ a b Δ) : argChange φ a b = Δ := by
  rw [argChange, dif_pos ⟨Δ, h⟩]
  exact IsArgChange.unique h0 (Exists.choose_spec ⟨Δ, h⟩) h

/-- **The change of argument is the imaginary part of `∫ φ'/φ`**: if `φ` has the continuous
derivative `ψ` and does not vanish on an open interval containing `[[a, b]]`, then
`Im ∫_a^b ψ/φ` is a change of argument of `φ` from `a` to `b`. -/
theorem isArgChange_of_hasDerivAt {φ ψ : ℝ → ℂ} {α β a b : ℝ} (hα : α < min a b)
    (hβ : max a b < β) (hd : ∀ t ∈ Ioo α β, HasDerivAt φ (ψ t) t) (hc : ContinuousOn ψ (Ioo α β))
    (h0 : ∀ t ∈ Ioo α β, φ t ≠ 0) :
    IsArgChange φ a b (∫ t in a..b, ψ t / φ t).im := by
  have hcont : ContinuousOn (fun t ↦ ψ t / φ t) (Ioo α β) :=
    hc.div (fun t ht ↦ (hd t ht).continuousAt.continuousWithinAt) h0
  set w : ℝ → ℂ := fun t ↦ ∫ u in a..t, ψ u / φ u with hw
  have hsub : [[a, b]] ⊆ Ioo α β := fun t ht ↦
    ⟨lt_of_lt_of_le hα ht.1, lt_of_le_of_lt ht.2 hβ⟩
  have ha : a ∈ Ioo α β := hsub left_mem_uIcc
  have hG : ∀ t ∈ Ioo α β, HasDerivAt w (ψ t / φ t) t := by
    intro t ht
    refine intervalIntegral.integral_hasDerivAt_right ?_ ?_ ?_
    · exact (hcont.mono (Set.OrdConnected.uIcc_subset inferInstance ha ht)).intervalIntegrable
    · exact hcont.stronglyMeasurableAtFilter isOpen_Ioo t ht
    · exact hcont.continuousAt (isOpen_Ioo.mem_nhds ht)
  have hwc : ContinuousOn w (Ioo α β) := fun t ht ↦ (hG t ht).continuousAt.continuousWithinAt
  have hφ : ∀ t ∈ Ioo α β, φ t = φ a * Complex.exp (w t) := by
    intro t ht
    rcases le_total a t with hat | hta
    · exact eq_mul_exp_integral_logDeriv hat ha.1 ht.2 hd hc h0
    · have h1 := eq_mul_exp_integral_logDeriv hta ht.1 ha.2 hd hc h0
      have h2 : w t = -∫ u in t..a, ψ u / φ u := by
        simp only [hw]; rw [intervalIntegral.integral_symm]
      rw [h2]
      rw [h1, mul_assoc, ← Complex.exp_add]
      simp
  refine ⟨fun t ↦ arg (φ a) + (w t).im, ⟨?_, ?_⟩, ?_⟩
  · exact (continuousOn_const.add (Complex.continuous_im.comp_continuousOn (hwc.mono hsub)))
  · intro t ht
    have h1 := hφ t (hsub ht)
    have hna : φ a = ‖φ a‖ * Complex.exp (arg (φ a) * I) :=
      (Complex.norm_mul_exp_arg_mul_I (φ a)).symm
    have hexp : Complex.exp (w t) = Complex.exp ((w t).re : ℂ) * Complex.exp ((w t).im * I) := by
      rw [← Complex.exp_add, Complex.re_add_im]
    have hnorm : ‖φ t‖ = ‖φ a‖ * Real.exp (w t).re := by
      rw [h1, norm_mul, Complex.norm_exp]
    rw [hnorm]
    conv_lhs => rw [h1, hna, hexp]
    push_cast
    rw [add_mul, Complex.exp_add]
    ring
  · simp [hw]

theorem argChange_eq_im_integral {φ ψ : ℝ → ℂ} {α β a b : ℝ} (hα : α < min a b)
    (hβ : max a b < β) (hd : ∀ t ∈ Ioo α β, HasDerivAt φ (ψ t) t) (hc : ContinuousOn ψ (Ioo α β))
    (h0 : ∀ t ∈ Ioo α β, φ t ≠ 0) :
    argChange φ a b = (∫ t in a..b, ψ t / φ t).im := by
  rw [argChange_eq (fun t ht ↦ h0 t ?_)
    (isArgChange_of_hasDerivAt hα hβ hd hc h0)]
  exact ⟨lt_of_lt_of_le hα ht.1, lt_of_le_of_lt ht.2 hβ⟩

/-- Reversing the path changes the sign of the change of argument. -/
theorem IsArgChange.symm {φ : ℝ → ℂ} {a b Δ : ℝ} (h : IsArgChange φ a b Δ) :
    IsArgChange φ b a (-Δ) := by
  obtain ⟨θ, ⟨hc, he⟩, hΔ⟩ := h
  refine ⟨θ, ⟨by rwa [Set.uIcc_comm], fun t ht ↦ he t (by rwa [Set.uIcc_comm])⟩, by linarith⟩

/-- Complex conjugation changes the sign of the change of argument. -/
theorem IsArgChange.conj {φ : ℝ → ℂ} {a b Δ : ℝ} (h : IsArgChange φ a b Δ) :
    IsArgChange (fun t ↦ conj (φ t)) a b (-Δ) := by
  obtain ⟨θ, ⟨hc, he⟩, hΔ⟩ := h
  refine ⟨fun t ↦ -θ t, ⟨hc.neg, fun t ht ↦ ?_⟩, by simp only; linarith⟩
  have h1 := he t ht
  calc conj (φ t) = conj (‖φ t‖ * Complex.exp (θ t * I)) := by rw [← h1]
    _ = _ := by
      rw [map_mul, ← Complex.exp_conj]
      simp

/-- The reflection `t ↦ c - t` of the parameter. -/
theorem IsArgChange.comp_sub {φ : ℝ → ℂ} {a b c Δ : ℝ} (h : IsArgChange φ (c - a) (c - b) Δ) :
    IsArgChange (fun t ↦ φ (c - t)) a b Δ := by
  obtain ⟨θ, ⟨hc, he⟩, hΔ⟩ := h
  have hm : ∀ t ∈ [[a, b]], c - t ∈ [[c - a, c - b]] := by
    intro t ht
    rw [Set.mem_uIcc] at ht ⊢
    rcases ht with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · right; constructor <;> linarith
    · left; constructor <;> linarith
  refine ⟨fun t ↦ θ (c - t), ⟨?_, fun t ht ↦ he _ (hm t ht)⟩, hΔ⟩
  exact hc.comp (by fun_prop) (fun t ht ↦ hm t ht)

theorem IsArgChange.congr {φ φ' : ℝ → ℂ} {a b Δ : ℝ} (h : IsArgChange φ a b Δ)
    (he : ∀ t ∈ [[a, b]], φ t = φ' t) : IsArgChange φ' a b Δ := by
  obtain ⟨θ, ⟨hc, hθ⟩, hΔ⟩ := h
  refine ⟨θ, ⟨hc, fun t ht ↦ ?_⟩, hΔ⟩
  rw [← he t ht]
  exact hθ t ht

/-- A function with positive real values has the change of argument `0`. -/
theorem isArgChange_zero_of_pos {φ : ℝ → ℂ} {a b : ℝ}
    (h : ∀ t ∈ [[a, b]], 0 < (φ t).re ∧ (φ t).im = 0) : IsArgChange φ a b 0 := by
  refine ⟨fun _ ↦ 0, ⟨continuousOn_const, fun t ht ↦ ?_⟩, by simp⟩
  have hr : φ t = (((φ t).re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [(h t ht).2])
  have hn : ‖φ t‖ = (φ t).re := by
    conv_lhs => rw [hr]
    rw [Complex.norm_real, Real.norm_of_nonneg (h t ht).1.le]
  rw [hn]
  simp
  exact hr

end NTKB
