/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import NTKB.Attr

/-!
# The Dirichlet kernel (Davenport, Chapter 2: Poisson summation)

`D_N(x) = ∑_{|ν| ≤ N} e(νx) = 1 + 2 ∑_{ν=1}^{N} cos 2πνx` (`dirichletKernel N x`), its
closed form `D_N(x) sin πx = sin (2N + 1)πx`, its periodicity and evenness, `∫_0^{1/2} D_N = 1/2`,
and the Riemann–Lebesgue lemma in the form used for Poisson summation: if `[a, b]` contains no
integer and `g` is continuous there, `∫_a^b g D_N → 0`.

Source text unavailable; written from the map row Davenport 2-6.
-/

open Real Finset MeasureTheory Filter Topology

namespace NTKB.Davenport.Poisson

/-- The Dirichlet kernel `D_N(x) = 1 + 2 ∑_{ν=1}^{N} cos 2πνx = ∑_{|ν| ≤ N} e(νx)`. -/
noncomputable def dirichletKernel (N : ℕ) (x : ℝ) : ℝ :=
  1 + 2 * ∑ ν ∈ range N, Real.cos (2 * π * (ν + 1) * x)

theorem continuous_dirichletKernel (N : ℕ) : Continuous (dirichletKernel N) := by
  unfold dirichletKernel
  fun_prop

theorem dirichletKernel_add_int (N : ℕ) (x : ℝ) (n : ℤ) :
    dirichletKernel N (x + n) = dirichletKernel N x := by
  have : ∀ ν ∈ Finset.range N, Real.cos (2 * π * ((ν : ℝ) + 1) * (x + n))
      = Real.cos (2 * π * ((ν : ℝ) + 1) * x) := by
    intro ν _
    have : 2 * π * ((ν : ℝ) + 1) * (x + n) =
        2 * π * ((ν : ℝ) + 1) * x + (((ν + 1 : ℤ) * n : ℤ) : ℝ) * (2 * π) := by
      push_cast; ring
    rw [this, Real.cos_add_int_mul_two_pi]
  unfold dirichletKernel
  rw [Finset.sum_congr rfl this]

theorem dirichletKernel_neg (N : ℕ) (x : ℝ) : dirichletKernel N (-x) = dirichletKernel N x := by
  have : ∀ ν ∈ Finset.range N, Real.cos (2 * π * ((ν : ℝ) + 1) * (-x))
      = Real.cos (2 * π * ((ν : ℝ) + 1) * x) := by
    intro ν _
    rw [mul_neg, Real.cos_neg]
  unfold dirichletKernel
  rw [Finset.sum_congr rfl this]

/-- `D_N(x) sin πx = sin (2N + 1)πx`. -/
theorem dirichletKernel_mul_sin (N : ℕ) (x : ℝ) :
    dirichletKernel N x * Real.sin (π * x) = Real.sin ((2 * N + 1) * π * x) := by
  induction N with
  | zero => simp [dirichletKernel]
  | succ N ih =>
    have h : dirichletKernel (N + 1) x = dirichletKernel N x
        + 2 * Real.cos (2 * π * ((N : ℝ) + 1) * x) := by
      unfold dirichletKernel
      rw [Finset.sum_range_succ]; ring
    rw [h, add_mul, ih]
    have h1 : ((2 * ((N + 1 : ℕ) : ℝ) + 1) * π * x) = 2 * π * ((N : ℝ) + 1) * x + π * x := by
      push_cast; ring
    have h2 : ((2 * (N : ℝ) + 1) * π * x) = 2 * π * ((N : ℝ) + 1) * x - π * x := by ring
    rw [h1, h2, Real.sin_add, Real.sin_sub]; ring

/-- `∑_{|ν| ≤ N} e(νx) = D_N(x)`. -/
theorem sum_exp_eq_dirichletKernel (N : ℕ) (x : ℝ) :
    ∑ ν ∈ Finset.Icc (-(N : ℤ)) N, Complex.exp (2 * π * Complex.I * ν * x) =
      (dirichletKernel N x : ℂ) := by
  induction N with
  | zero => simp [dirichletKernel]
  | succ N ih =>
    have hs : Finset.Icc (-((N + 1 : ℕ) : ℤ)) ((N + 1 : ℕ) : ℤ) =
        insert (-((N + 1 : ℕ) : ℤ)) (insert ((N + 1 : ℕ) : ℤ) (Finset.Icc (-(N : ℤ)) N)) := by
      ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; push_cast; omega
    have h1 : (-((N + 1 : ℕ) : ℤ)) ∉ insert ((N + 1 : ℕ) : ℤ) (Finset.Icc (-(N : ℤ)) N) := by
      simp only [Finset.mem_Icc, Finset.mem_insert]; push_cast; omega
    have h2 : ((N + 1 : ℕ) : ℤ) ∉ Finset.Icc (-(N : ℤ)) N := by
      simp only [Finset.mem_Icc]; push_cast; omega
    rw [hs, Finset.sum_insert h1, Finset.sum_insert h2, ih]
    have h : dirichletKernel (N + 1) x = dirichletKernel N x
        + 2 * Real.cos (2 * π * ((N : ℝ) + 1) * x) := by
      unfold dirichletKernel
      rw [Finset.sum_range_succ]; ring
    rw [h]
    push_cast
    rw [Complex.two_cos]
    have e1 : 2 * (π : ℂ) * Complex.I * -((N : ℂ) + 1) * x
        = -(2 * π * ((N : ℂ) + 1) * x) * Complex.I := by ring
    have e2 : 2 * (π : ℂ) * Complex.I * ((N : ℂ) + 1) * x
        = (2 * π * ((N : ℂ) + 1) * x) * Complex.I := by ring
    rw [e1, e2]; ring

/-- `∫_0^{1/2} D_N = 1/2`. -/
theorem integral_dirichletKernel_zero_half (N : ℕ) :
    ∫ x in (0 : ℝ)..(1 / 2), dirichletKernel N x = 1 / 2 := by
  unfold dirichletKernel
  rw [intervalIntegral.integral_add (by simp) ?_]
  · rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_finsetSum]
    · have : ∀ ν ∈ Finset.range N, ∫ x in (0 : ℝ)..(1 / 2), Real.cos (2 * π * ((ν : ℝ) + 1) * x) = 0 := by
        intro ν _
        have hc : (2 * π * ((ν : ℝ) + 1)) ≠ 0 := by positivity
        rw [intervalIntegral.integral_comp_mul_left (fun x => Real.cos x) hc, integral_cos]
        have : 2 * π * ((ν : ℝ) + 1) * (1 / 2) = ((ν + 1 : ℕ) : ℝ) * π := by push_cast; ring
        simp only [mul_zero, Real.sin_zero, sub_zero, this, Real.sin_nat_mul_pi, smul_zero]
      rw [Finset.sum_eq_zero this]; simp
    · intro ν _
      exact (by fun_prop : Continuous fun x : ℝ => Real.cos (2 * π * ((ν : ℝ) + 1) * x)).intervalIntegrable _ _
  · exact (Continuous.intervalIntegrable (by fun_prop) _ _)

/-- Riemann–Lebesgue for an integrable function on `ℝ`. -/
theorem tendsto_integral_mul_sin_of_integrable {F : ℝ → ℝ} (hF : Integrable F) :
    Tendsto (fun N : ℕ ↦ ∫ x, F x * Real.sin ((2 * N + 1) * π * x)) atTop (𝓝 0) := by
  have hRL := Real.tendsto_integral_exp_smul_cocompact (fun v => (F v : ℂ))
  have hN : Tendsto (fun N : ℕ ↦ ((2 * (N : ℝ) + 1) / 2)) atTop atTop := by
    refine tendsto_atTop_mono (fun N => ?_) tendsto_natCast_atTop_atTop
    linarith
  have hw : Tendsto (fun N : ℕ ↦ -((2 * (N : ℝ) + 1) / 2)) atTop (cocompact ℝ) :=
    (tendsto_neg_atTop_atBot.comp hN).mono_right atBot_le_cocompact
  have h := (Complex.continuous_im.tendsto 0).comp (hRL.comp hw)
  simp only [Complex.zero_im] at h
  refine h.congr (fun N => ?_)
  simp only [Function.comp_apply]
  have hint : Integrable (fun v : ℝ => Real.fourierChar (-(v * -((2 * (N : ℝ) + 1) / 2))) • (F v : ℂ)) := by
    refine (hF.ofReal (𝕜 := ℂ)).mono ?_ ?_
    · exact (Continuous.aestronglyMeasurable
        (Real.continuous_fourierChar.comp (by fun_prop :
          Continuous fun v : ℝ => -(v * -((2 * (N : ℝ) + 1) / 2))))).smul
        (Complex.continuous_ofReal.comp_aestronglyMeasurable hF.aestronglyMeasurable)
    · refine Eventually.of_forall fun v => ?_
      rw [Circle.smul_def, smul_eq_mul, norm_mul]; simp
  rw [← Complex.imCLM_apply, ← ContinuousLinearMap.integral_comp_comm _ hint]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  beta_reduce
  rw [Complex.imCLM_apply, Circle.smul_def, Real.fourierChar_apply, smul_eq_mul]
  have : (2 * π * -(v * -((2 * (N : ℝ) + 1) / 2)) : ℝ) = (2 * N + 1) * π * v := by ring
  rw [this, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  simp only [Complex.mul_im, Complex.add_im, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

/-- **Riemann–Lebesgue** on an interval, along the odd multiples `(2N + 1)π`. -/
theorem tendsto_integral_mul_sin {g : ℝ → ℝ} {a b : ℝ} (hg : IntervalIntegrable g volume a b) :
    Tendsto (fun N : ℕ ↦ ∫ x in a..b, g x * Real.sin ((2 * N + 1) * π * x)) atTop (𝓝 0) := by
  set s : ℕ → ℝ → ℝ := fun N x => Real.sin ((2 * N + 1) * π * x) with hs
  have hsc : ∀ N, Continuous (s N) := fun N => by simp only [hs]; fun_prop
  have hsb : ∀ N x, |s N x| ≤ 1 := fun N x => Real.abs_sin_le_one _
  set F : ℝ → ℝ := (Set.Ioc a b).indicator g - (Set.Ioc b a).indicator g with hF
  have h1 : IntegrableOn g (Set.Ioc a b) := hg.1
  have h2 : IntegrableOn g (Set.Ioc b a) := hg.2
  have hFi : Integrable F :=
    (h1.integrable_indicator measurableSet_Ioc).sub (h2.integrable_indicator measurableSet_Ioc)
  refine (tendsto_integral_mul_sin_of_integrable hFi).congr (fun N => ?_)
  have hI : ∀ {c d : ℝ}, IntegrableOn g (Set.Ioc c d) → IntegrableOn (fun x => g x * s N x) (Set.Ioc c d) := by
    intro c d h
    exact h.mul_bdd (hsc N).aestronglyMeasurable (Eventually.of_forall fun x => by simpa using hsb N x)
  have e : ∀ x, F x * s N x = (Set.Ioc a b).indicator (fun x => g x * s N x) x
      - (Set.Ioc b a).indicator (fun x => g x * s N x) x := by
    intro x
    simp only [hF, Pi.sub_apply, Set.indicator_apply]
    split_ifs <;> ring
  show (∫ x, F x * s N x) = ∫ x in a..b, g x * s N x
  refine (integral_congr_ae (Eventually.of_forall e)).trans ?_
  rw [integral_sub ((hI h1).integrable_indicator measurableSet_Ioc)
    ((hI h2).integrable_indicator measurableSet_Ioc), integral_indicator measurableSet_Ioc,
    integral_indicator measurableSet_Ioc]
  rfl

/-- Away from the integers the kernel integrates a continuous function to `0` in the limit. -/
theorem tendsto_integral_mul_dirichletKernel_of_forall_int_notMem {g : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hg : ContinuousOn g (Set.Icc a b)) (hint : ∀ n : ℤ, (n : ℝ) ∉ Set.Icc a b) :
    Tendsto (fun N : ℕ ↦ ∫ x in a..b, g x * dirichletKernel N x) atTop (𝓝 0) := by
  have hne : ∀ x ∈ Set.Icc a b, Real.sin (π * x) ≠ 0 := by
    intro x hx h
    obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp h
    apply hint n
    have : (n : ℝ) = x := mul_right_cancel₀ Real.pi_ne_zero (by linarith)
    rw [this]; exact hx
  have hc : ContinuousOn (fun x => g x / Real.sin (π * x)) (Set.Icc a b) :=
    hg.div (by fun_prop) hne
  have := tendsto_integral_mul_sin (hc.intervalIntegrable_of_Icc hab)
  refine this.congr (fun N => ?_)
  refine intervalIntegral.integral_congr (fun x hx => ?_)
  rw [Set.uIcc_of_le hab] at hx
  rw [← dirichletKernel_mul_sin]
  field_simp [hne x hx]

end NTKB.Davenport.Poisson
