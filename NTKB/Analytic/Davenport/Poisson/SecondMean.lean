/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.Analysis.Real.Pi.Bounds
import NTKB.Analytic.Davenport.Poisson.Kernel

/-!
# A second-mean-value bound and the uniform bound for the Dirichlet kernel

* `abs_intervalIntegral_mul_le_of_monotoneOn`: for `h` monotone on `[a, b]` and `φ` continuous
  with `|∫_c^b φ| ≤ M` for every `c ∈ [a, b]`, `|∫_a^b h φ| ≤ M (|h a| + (h b - h a))`
  (Bonnet's form of the second mean value theorem, as a bound; proved by the layer-cake
  decomposition of `h - h a`).
* `exists_abs_integral_dirichletKernel_le`: the integrals of `D_N` over subintervals of
  `[0, 1/2]` are bounded uniformly in `N` (through `D_N(x) = sin (2N+1)πx / sin πx` and the
  boundedness of `∫ sin t / t`).

Source text unavailable; written from the map row Davenport 2-6.
-/

open Real Finset MeasureTheory Filter Topology

namespace NTKB.Davenport.Poisson

/-- One layer of the layer-cake decomposition. -/
theorem bonnet_slice {k ψ : ℝ → ℝ} {a b M : ℝ} (hab : a ≤ b) (hk : Monotone k)
    (hM : ∀ c ∈ Set.Icc a b, |∫ x in c..b, ψ x| ≤ M) (t : ℝ) :
    ‖∫ x in Set.Ioc a b, {x | t < k x}.indicator ψ x‖ ≤ M := by
  have M0 : 0 ≤ M := by
    have := hM b ⟨hab, le_rfl⟩
    simpa using this
  have hS : MeasurableSet {x | t < k x} := measurableSet_lt measurable_const hk.measurable
  rw [setIntegral_indicator hS]
  by_cases hne : (Set.Ioc a b ∩ {x | t < k x}).Nonempty
  · set A := Set.Ioc a b ∩ {x | t < k x} with hA
    have hbdd : BddBelow A := ⟨a, fun s hs => hs.1.1.le⟩
    obtain ⟨s0, hs0⟩ := hne
    have hac : a ≤ sInf A := le_csInf ⟨s0, hs0⟩ (fun s hs => hs.1.1.le)
    have hcb : sInf A ≤ b := (csInf_le hbdd hs0).trans hs0.1.2
    have h1 : Set.Ioo (sInf A) b ⊆ A := by
      intro x hx
      obtain ⟨s, hs, hsx⟩ := exists_lt_of_csInf_lt ⟨s0, hs0⟩ hx.1
      exact ⟨⟨lt_of_le_of_lt hac hx.1, hx.2.le⟩, lt_of_lt_of_le hs.2 (hk hsx.le)⟩
    have h2 : A ⊆ Set.Icc (sInf A) b := fun s hs => ⟨csInf_le hbdd hs, hs.1.2⟩
    have hae : A =ᵐ[volume] Set.Ioo (sInf A) b := by
      rw [ae_eq_set]
      constructor
      · refine measure_mono_null (t := {sInf A, b}) ?_ ((Set.toFinite _).measure_zero _)
        intro x hx
        have := h2 hx.1
        have hx2 := hx.2
        simp only [Set.mem_Ioo, not_and, not_lt] at hx2
        by_cases h : sInf A < x
        · right; exact le_antisymm this.2 (hx2 h)
        · left; exact le_antisymm (not_lt.1 h) this.1
      · rw [Set.sdiff_eq_empty.mpr h1]; simp
    rw [setIntegral_congr_set hae, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le hcb]
    simpa [Real.norm_eq_abs] using hM _ ⟨hac, hcb⟩
  · rw [Set.not_nonempty_iff_eq_empty.mp hne]; simpa using M0

/-- Core of the second mean value bound, for a globally monotone bounded `k`. -/
theorem bonnet_core {k ψ : ℝ → ℝ} {a b K M B : ℝ} (hab : a ≤ b) (hk : Monotone k)
    (hk0 : ∀ x, 0 ≤ k x) (hkK : ∀ x, k x ≤ K) (hψ : Continuous ψ) (hB : ∀ x, ‖ψ x‖ ≤ B)
    (hM : ∀ c ∈ Set.Icc a b, |∫ x in c..b, ψ x| ≤ M) :
    |∫ x in a..b, k x * ψ x| ≤ K * M := by
  have K0 : 0 ≤ K := (hk0 0).trans (hkK 0)
  have B0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  let f : ℝ → ℝ → ℝ := fun x t => if t < k x then ψ x else 0
  have hint : Integrable (Function.uncurry f)
      ((volume.restrict (Set.Ioc a b)).prod (volume.restrict (Set.Ioc 0 K))) := by
    refine (integrable_const B).mono' ?_ (Filter.Eventually.of_forall fun p => ?_)
    · refine Measurable.aestronglyMeasurable ?_
      exact Measurable.ite (measurableSet_lt measurable_snd (hk.measurable.comp measurable_fst))
        (hψ.measurable.comp measurable_fst) measurable_const
    · simp only [Function.uncurry, f]
      split_ifs
      · exact hB _
      · simpa using B0
  have hcomp : ∀ x, ∫ t in Set.Ioc 0 K, f x t = k x * ψ x := by
    intro x
    have h1 : (fun t => f x t) = (Set.Iio (k x)).indicator (fun _ => ψ x) := by
      funext t; simp [f, Set.indicator]
    have h2 : Set.Ioc 0 K ∩ Set.Iio (k x) = Set.Ioo 0 (k x) := by
      ext t
      simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Iio, Set.mem_Ioo]
      constructor
      · rintro ⟨⟨h, _⟩, h'⟩; exact ⟨h, h'⟩
      · rintro ⟨h, h'⟩; exact ⟨⟨h, (h'.trans_le (hkK x)).le⟩, h'⟩
    rw [h1, setIntegral_indicator measurableSet_Iio, h2, setIntegral_const]
    simp [measureReal_def, Real.volume_Ioo, hk0 x]
  have hslice : ∀ t, ∫ x in Set.Ioc a b, f x t = ∫ x in Set.Ioc a b, {x | t < k x}.indicator ψ x := by
    intro t
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp [f, Set.indicator]
  rw [intervalIntegral.integral_of_le hab]
  calc |∫ x in Set.Ioc a b, k x * ψ x|
      = ‖∫ x in Set.Ioc a b, ∫ t in Set.Ioc 0 K, f x t‖ := by
        rw [Real.norm_eq_abs]; congr 2; funext x; exact (hcomp x).symm
    _ = ‖∫ t in Set.Ioc 0 K, ∫ x in Set.Ioc a b, f x t‖ := by
        rw [integral_integral_swap hint]
    _ ≤ M * volume.real (Set.Ioc 0 K) := by
        refine norm_setIntegral_le_of_norm_le_const (by simp) (fun t _ => ?_)
        rw [hslice]; exact bonnet_slice hab hk hM t
    _ = K * M := by simp [measureReal_def, K0]; ring

/-- **Second mean value bound.** -/
theorem abs_intervalIntegral_mul_le_of_monotoneOn {h φ : ℝ → ℝ} {a b M : ℝ} (hab : a ≤ b)
    (hh : MonotoneOn h (Set.Icc a b)) (hφ : ContinuousOn φ (Set.Icc a b))
    (hM : ∀ c ∈ Set.Icc a b, |∫ x in c..b, φ x| ≤ M) :
    |∫ x in a..b, h x * φ x| ≤ M * (|h a| + (h b - h a)) := by
  let cl : ℝ → ℝ := fun x => max a (min x b)
  have hcl : ∀ x, cl x ∈ Set.Icc a b := fun x =>
    ⟨le_max_left _ _, max_le hab (min_le_right _ _)⟩
  have hcl_eq : ∀ x ∈ Set.Icc a b, cl x = x := fun x hx => by
    simp only [cl]; rw [min_eq_left hx.2, max_eq_right hx.1]
  have hclc : Continuous cl := by fun_prop
  have ha : a ∈ Set.Icc a b := ⟨le_rfl, hab⟩
  have hb : b ∈ Set.Icc a b := ⟨hab, le_rfl⟩
  have hk : Monotone (fun x => h (cl x) - h a) := fun x y hxy =>
    sub_le_sub_right (hh (hcl x) (hcl y)
      (max_le_max le_rfl (min_le_min hxy le_rfl))) _
  have hk0 : ∀ x, 0 ≤ h (cl x) - h a := fun x =>
    sub_nonneg.2 (hh ha (hcl x) (le_max_left _ _))
  have hkK : ∀ x, h (cl x) - h a ≤ h b - h a := fun x =>
    sub_le_sub_right (hh (hcl x) hb (max_le hab (min_le_right _ _))) _
  have hψ : Continuous (fun x => φ (cl x)) := hφ.comp_continuous hclc hcl
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn hφ
  have hM' : ∀ c ∈ Set.Icc a b, |∫ x in c..b, φ (cl x)| ≤ M := by
    intro c hc
    rw [intervalIntegral.integral_congr (g := φ) (fun x hx => by
      rw [Set.uIcc_of_le hc.2] at hx
      show φ (cl x) = φ x
      rw [hcl_eq x ⟨hc.1.trans hx.1, hx.2⟩])]
    exact hM c hc
  have hcore := bonnet_core hab hk hk0 hkK hψ (fun x => hB _ (hcl x)) hM'
  have hφi : IntervalIntegrable φ volume a b :=
    (hφ.mono (by rw [Set.uIcc_of_le hab])).intervalIntegrable
  have hkψ : IntervalIntegrable (fun x => (h (cl x) - h a) * φ (cl x)) volume a b :=
    (hk.intervalIntegrable (a := a) (b := b)).mul_continuousOn
      (hψ.continuousOn)
  have hsplit : ∫ x in a..b, h x * φ x
      = h a * (∫ x in a..b, φ x) + ∫ x in a..b, (h (cl x) - h a) * φ (cl x) := by
    have e1 : h a * (∫ x in a..b, φ x) = ∫ x in a..b, h a * φ x :=
      (intervalIntegral.integral_const_mul _ _).symm
    rw [e1, ← intervalIntegral.integral_add (hφi.const_mul _) hkψ]
    refine intervalIntegral.integral_congr (fun x hx => ?_)
    rw [Set.uIcc_of_le hab] at hx
    show h x * φ x = h a * φ x + (h (cl x) - h a) * φ (cl x)
    rw [hcl_eq x hx]; ring
  have M0 : 0 ≤ M := by simpa using hM b hb
  have h1 : |h a * (∫ x in a..b, φ x)| ≤ |h a| * M := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hM a ha) (abs_nonneg _)
  rw [hsplit]
  calc _ ≤ |h a * (∫ x in a..b, φ x)| + |∫ x in a..b, (h (cl x) - h a) * φ (cl x)| :=
        abs_add_le _ _
    _ ≤ |h a| * M + (h b - h a) * M := add_le_add h1 hcore
    _ = _ := by ring

theorem sinc_intervalIntegrable {ω u v : ℝ} (hu : 0 < u) (huv : u ≤ v) :
    IntervalIntegrable (fun x => Real.sin (ω * x) / x) volume u v := by
  refine ContinuousOn.intervalIntegrable ?_
  rw [Set.uIcc_of_le huv]
  exact ContinuousOn.div (by fun_prop) continuousOn_id (fun x hx => (hu.trans_le hx.1).ne')

theorem abs_integral_sinc_le_large {ω c d : ℝ} (hω : 0 < ω) (hc : 0 < c) (hcd : c ≤ d)
    (h1 : 1 ≤ ω * c) : |∫ x in c..d, Real.sin (ω * x) / x| ≤ 4 := by
  have hd : 0 < d := hc.trans_le hcd
  have hmono : MonotoneOn (fun x : ℝ => -x⁻¹) (Set.Icc c d) := by
    intro x hx y hy hxy
    have hx0 : 0 < x := hc.trans_le hx.1
    simp only [neg_le_neg_iff]
    exact inv_anti₀ hx0 hxy
  have hφ : ContinuousOn (fun x : ℝ => Real.sin (ω * x)) (Set.Icc c d) := by fun_prop
  have hM : ∀ e ∈ Set.Icc c d, |∫ x in e..d, Real.sin (ω * x)| ≤ 2 / ω := by
    intro e he
    rw [intervalIntegral.integral_comp_mul_left (fun x => Real.sin x) hω.ne', integral_sin,
      smul_eq_mul, abs_mul, abs_inv, abs_of_pos hω]
    have h2 : |Real.cos (ω * e) - Real.cos (ω * d)| ≤ 2 := by
      have := Real.abs_cos_le_one (ω * e)
      have := Real.abs_cos_le_one (ω * d)
      rw [abs_le] at *
      constructor <;> linarith
    calc ω⁻¹ * |Real.cos (ω * e) - Real.cos (ω * d)| ≤ ω⁻¹ * 2 :=
          mul_le_mul_of_nonneg_left h2 (inv_nonneg.2 hω.le)
      _ = 2 / ω := by ring
  have key := abs_intervalIntegral_mul_le_of_monotoneOn hcd hmono hφ hM
  have e1 : (∫ x in c..d, (-x⁻¹) * Real.sin (ω * x)) = -∫ x in c..d, Real.sin (ω * x) / x := by
    rw [← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr (fun x _ => ?_)
    show (-x⁻¹) * Real.sin (ω * x) = -(Real.sin (ω * x) / x)
    ring
  rw [e1, abs_neg] at key
  refine key.trans ?_
  have hdi : 0 < d⁻¹ := inv_pos.2 hd
  have hci : 0 < c⁻¹ := inv_pos.2 hc
  have e2 : |-c⁻¹| = c⁻¹ := by rw [abs_neg, abs_of_pos hci]
  simp only [e2]
  have e3 : 2 / ω * (c⁻¹ + (-d⁻¹ - -c⁻¹)) ≤ 2 / ω * (2 / c) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [div_eq_mul_inv]; linarith
  refine e3.trans ?_
  have e4 : 2 / ω * (2 / c) = 4 / (ω * c) := by field_simp; ring
  rw [e4, div_le_iff₀ (by positivity)]
  linarith

theorem abs_integral_sinc_le_small {ω c d : ℝ} (hω : 0 < ω) (hc : 0 < c) (hcd : c ≤ d)
    (h1 : ω * d ≤ 1) : |∫ x in c..d, Real.sin (ω * x) / x| ≤ 1 := by
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := c) (b := d)
    (f := fun x => Real.sin (ω * x) / x) (C := ω) (fun x hx => by
      rw [Set.uIoc_of_le hcd] at hx
      have hx0 : 0 < x := hc.trans hx.1
      rw [Real.norm_eq_abs, abs_div, abs_of_pos hx0, div_le_iff₀ hx0]
      have := Real.abs_sin_le_abs (x := ω * x)
      rwa [abs_of_pos (mul_pos hω hx0)] at this)
  rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 hcd)] at this
  refine this.trans ?_
  nlinarith

theorem abs_integral_sinc_le {ω c d : ℝ} (hω : 0 < ω) (hc : 0 < c) (hcd : c ≤ d) :
    |∫ x in c..d, Real.sin (ω * x) / x| ≤ 5 := by
  by_cases h1 : 1 ≤ ω * c
  · linarith [abs_integral_sinc_le_large hω hc hcd h1]
  by_cases h2 : ω * d ≤ 1
  · linarith [abs_integral_sinc_le_small hω hc hcd h2]
  push Not at h1 h2
  have he : 0 < 1 / ω := by positivity
  have hωe : ω * (1 / ω) = 1 := by field_simp
  have hce : c ≤ 1 / ω := ((lt_div_iff₀ hω).2 (by linarith)).le
  have hed : 1 / ω ≤ d := ((div_le_iff₀ hω).2 (by linarith))
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (sinc_intervalIntegrable hc hce) (sinc_intervalIntegrable he hed)]
  have a1 := abs_integral_sinc_le_small hω hc hce (by rw [hωe])
  have a2 := abs_integral_sinc_le_large hω he hed (by rw [hωe])
  calc _ ≤ _ := abs_add_le _ _
    _ ≤ 1 + 4 := add_le_add a1 a2
    _ = 5 := by norm_num

theorem inv_sin_sub_inv_bounds {y : ℝ} (hy : 0 < y) (hy2 : y ≤ π / 2) :
    0 ≤ (Real.sin y)⁻¹ - y⁻¹ ∧ (Real.sin y)⁻¹ - y⁻¹ ≤ 1 := by
  have hpi3 := Real.pi_gt_three
  have hpi4 := Real.pi_le_four
  have hs : 0 < Real.sin y := Real.sin_pos_of_pos_of_lt_pi hy (by linarith)
  have hsy : Real.sin y ≤ y := Real.sin_le hy.le
  refine ⟨sub_nonneg.2 (inv_anti₀ hs hsy), ?_⟩
  have hcube := Real.sin_gt_sub_cube hy
  have hlin := Real.mul_le_sin hy.le hy2
  have hyp : y * π ≤ 12 := by nlinarith
  have h3 : y ^ 3 / 6 ≤ y * Real.sin y := by
    have h4 : y * (2 / π * y) ≤ y * Real.sin y := mul_le_mul_of_nonneg_left hlin hy.le
    have h5 : y ^ 3 / 6 ≤ y * (2 / π * y) := by
      have : y * (2 / π * y) = 2 * y ^ 2 / π := by field_simp
      rw [this, le_div_iff₀ (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_left hyp (sq_nonneg y)]
    exact h5.trans h4
  have key : y - Real.sin y ≤ y * Real.sin y := by linarith
  have : (Real.sin y)⁻¹ - y⁻¹ = (y - Real.sin y) / (y * Real.sin y) := by field_simp
  rw [this, div_le_one (by positivity)]
  exact key

theorem abs_integral_dirichletKernel_le_of_pos {N : ℕ} {c d : ℝ} (hc : 0 < c) (hcd : c ≤ d)
    (hd : d ≤ 1 / 2) : |∫ x in c..d, dirichletKernel N x| ≤ 6 := by
  set ω : ℝ := (2 * (N : ℝ) + 1) * π with hω
  have hωpos : 0 < ω := by positivity
  have hpi3 := Real.pi_gt_three
  let A : ℝ → ℝ := fun x => π⁻¹ * (Real.sin (ω * x) / x)
  have hAi : IntervalIntegrable A volume c d :=
    (sinc_intervalIntegrable hc hcd).const_mul _
  have hDi : IntervalIntegrable (dirichletKernel N) volume c d :=
    (continuous_dirichletKernel N).intervalIntegrable _ _
  have hpt : ∀ x ∈ Set.Ioc c d, ‖dirichletKernel N x - A x‖ ≤ 1 := by
    intro x hx
    have hx0 : 0 < x := hc.trans hx.1
    have hx2 : x ≤ 1 / 2 := hx.2.trans hd
    have hs : 0 < Real.sin (π * x) :=
      Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith)
    have hD : dirichletKernel N x = Real.sin (ω * x) / Real.sin (π * x) :=
      eq_div_of_mul_eq hs.ne' (dirichletKernel_mul_sin N x)
    have hb := inv_sin_sub_inv_bounds (y := π * x) (by positivity) (by nlinarith)
    have e : dirichletKernel N x - A x
        = Real.sin (ω * x) * ((Real.sin (π * x))⁻¹ - (π * x)⁻¹) := by
      rw [hD]; simp only [A]; field_simp
    rw [e, Real.norm_eq_abs, abs_mul, abs_of_nonneg hb.1]
    calc _ ≤ 1 * 1 := mul_le_mul (Real.abs_sin_le_one _) hb.2 hb.1 zero_le_one
      _ = 1 := one_mul 1
  have hsplit : ∫ x in c..d, dirichletKernel N x
      = (∫ x in c..d, A x) + ∫ x in c..d, (dirichletKernel N x - A x) := by
    rw [intervalIntegral.integral_sub hDi hAi]; ring
  have hB : |∫ x in c..d, (dirichletKernel N x - A x)| ≤ 1 / 2 := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := c) (b := d)
      (f := fun x => dirichletKernel N x - A x) (C := 1) (fun x hx => by
        rw [Set.uIoc_of_le hcd] at hx; exact hpt x hx)
    rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 hcd)] at this
    linarith
  have hA : |∫ x in c..d, A x| ≤ 5 := by
    have e : (∫ x in c..d, A x) = π⁻¹ * ∫ x in c..d, Real.sin (ω * x) / x :=
      intervalIntegral.integral_const_mul _ _
    rw [e, abs_mul, abs_of_pos (inv_pos.2 Real.pi_pos)]
    have h5 := abs_integral_sinc_le hωpos hc hcd
    have : π⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
    calc _ ≤ 1 * 5 := mul_le_mul this h5 (abs_nonneg _) zero_le_one
      _ = 5 := one_mul 5
  rw [hsplit]
  calc _ ≤ _ := abs_add_le _ _
    _ ≤ 5 + 1 / 2 := add_le_add hA hB
    _ ≤ 6 := by norm_num

/-- **Uniform bound** for the partial integrals of the Dirichlet kernel on `[0, 1/2]`. -/
theorem exists_abs_integral_dirichletKernel_le :
    ∃ C : ℝ, ∀ (N : ℕ) (c d : ℝ), 0 ≤ c → c ≤ d → d ≤ 1 / 2 →
      |∫ x in c..d, dirichletKernel N x| ≤ C := by
  refine ⟨6, fun N c d hc hcd hd => ?_⟩
  rcases hc.eq_or_lt with rfl | hc0
  · rcases hcd.eq_or_lt with rfl | hd0
    · simp
    · let g : ℝ → ℝ := fun c => ∫ x in c..d, dirichletKernel N x
      have hg : Continuous g := by
        have : g = fun c => -∫ x in d..c, dirichletKernel N x := by
          funext c; simp only [g]; rw [intervalIntegral.integral_symm]
        rw [this]
        exact (intervalIntegral.continuous_primitive
          (fun a b => (continuous_dirichletKernel N).intervalIntegrable a b) d).neg
      have ht : Tendsto (fun c => |g c|) (𝓝[>] 0) (𝓝 |g 0|) :=
        (hg.abs.tendsto 0).mono_left nhdsWithin_le_nhds
      refine le_of_tendsto ht ?_
      filter_upwards [Ioo_mem_nhdsGT hd0] with c hc
      exact abs_integral_dirichletKernel_le_of_pos hc.1 hc.2.le hd
  · exact abs_integral_dirichletKernel_le_of_pos hc0 hcd hd

end NTKB.Davenport.Poisson
