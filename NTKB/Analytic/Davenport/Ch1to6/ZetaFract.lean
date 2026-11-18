/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.MeasureTheory.Function.Floor
import NTKB.Attr

/-!
# `ζ(s) = 1/(s-1) + 1 - s ∫_1^∞ {x} x^{-s-1} dx` for `Re s > 0` (Davenport, Chapter 4, row 4-18)

The integral converges absolutely for `Re s > 0` (`integrableOn_fract_mul_cpow`) and defines a
holomorphic function there; the identity holds for real `s > 1` by summing over the intervals
`[n, n + 1]` (Mathlib's `ZetaAsymptotics.termTSum_of_lt`), and for `Re s > 0`, `s ≠ 1` by analytic
continuation (`riemannZeta_eq_one_div_sub_one_add_one_sub_mul_integral`). So `ζ` is meromorphic in
`Re s > 0` with a simple pole at `1` of residue `1` (Mathlib `riemannZeta_residue_one`).

Source text unavailable; written from the map row 4-18. (The map's earlier
citation of a PrimeNumberTheoremAnd name is withdrawn: the name exists in neither tree.)
-/

open Complex MeasureTheory Filter Topology

namespace NTKB.Davenport

/-- The integral `∫_1^∞ {x} x^{-s-1} dx` converges absolutely for `Re s > 0`. -/
theorem integrableOn_fract_mul_cpow {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun x : ℝ ↦ ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)) (Set.Ioi 1) := by
  have hmeas : AEStronglyMeasurable
      (fun x : ℝ ↦ ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)) (volume.restrict (Set.Ioi 1)) := by
    refine AEStronglyMeasurable.mul ?_ ?_
    · exact (Complex.measurable_ofReal.comp measurable_fract).aestronglyMeasurable
    · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
      intro x hx
      exact (Complex.continuousAt_ofReal_cpow_const x _ (Or.inr (ne_of_gt (lt_trans one_pos hx)))).continuousWithinAt
  have hint : IntegrableOn (fun x : ℝ ↦ x ^ (-s.re - 1)) (Set.Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) one_pos
  refine hint.mono' hmeas ?_
  rw [ae_restrict_iff' measurableSet_Ioi]
  refine Filter.Eventually.of_forall fun x hx => ?_
  have hx0 : (0 : ℝ) < x := lt_trans one_pos hx
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
  simp only [sub_re, neg_re, one_re]
  have h1 : ‖((Int.fract x : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Int.fract_nonneg x)]
    exact (Int.fract_lt_one x).le
  calc _ ≤ 1 * x ^ (-s.re - 1) := by gcongr
    _ = _ := one_mul _

/-- The function whose Mellin transform is the integral. -/
private noncomputable def fr (x : ℝ) : ℂ := (Set.Ioi (1 : ℝ)).indicator (fun x : ℝ => ((Int.fract x : ℝ) : ℂ)) x

private lemma fr_norm_le (x : ℝ) : ‖fr x‖ ≤ 1 := by
  unfold fr
  by_cases hx : x ∈ Set.Ioi (1 : ℝ)
  · rw [Set.indicator_of_mem hx, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Int.fract_nonneg x)]
    exact (Int.fract_lt_one x).le
  · rw [Set.indicator_of_notMem hx]; simp

private lemma fr_measurable : Measurable fr :=
  (Complex.measurable_ofReal.comp measurable_fract).indicator measurableSet_Ioi

private lemma fr_locInt : LocallyIntegrableOn fr (Set.Ioi 0) := by
  have : LocallyIntegrable fr := by
    intro x
    refine ⟨Set.Ioo (x - 1) (x + 1), Ioo_mem_nhds (by linarith) (by linarith), ?_⟩
    refine Measure.integrableOn_of_bounded (M := 1) (by simp) fr_measurable.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fr_norm_le
  exact this.locallyIntegrableOn _

private noncomputable def G (s : ℂ) : ℂ :=
  ∫ x in Set.Ioi (1 : ℝ), ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)

private lemma G_eq_mellin (s : ℂ) : G s = mellin fr (-s) := by
  unfold G mellin
  have : ∀ x : ℝ, (x : ℂ) ^ (-s - 1) • fr x =
      (Set.Ioi (1 : ℝ)).indicator
        (fun x : ℝ => ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)) x := by
    intro x
    unfold fr
    by_cases hx : x ∈ Set.Ioi (1 : ℝ)
    · simp [Set.indicator_of_mem hx, mul_comm]
    · simp [Set.indicator_of_notMem hx]
  simp_rw [this]
  rw [setIntegral_indicator measurableSet_Ioi]
  rw [Set.inter_eq_right.2 (fun x (hx : x ∈ Set.Ioi (1:ℝ)) => (by simp only [Set.mem_Ioi] at hx ⊢; linarith))]

private lemma G_differentiableAt {s : ℂ} (hs : 0 < s.re) : DifferentiableAt ℂ G s := by
  have h : DifferentiableAt ℂ (mellin fr) (-s) := by
    refine mellin_differentiableAt_of_isBigO_rpow (a := 0) (b := -s.re - 1) fr_locInt ?_
      (by simp; exact hs) ?_ (by simp)
    · refine Asymptotics.IsBigO.of_bound 1 (Filter.Eventually.of_forall fun x => ?_)
      simpa using fr_norm_le x
    · refine Asymptotics.IsBigO.of_bound 0 ?_
      have : ∀ᶠ x in 𝓝[>] (0:ℝ), x < 1 := 
        mem_nhdsGT_iff_exists_Ioo_subset.2 ⟨1, by norm_num, fun x hx => hx.2⟩
      filter_upwards [this] with x hx
      have : fr x = 0 := by
        unfold fr; apply Set.indicator_of_notMem; simp; exact hx.le
      simp [this]
  have h2 : DifferentiableAt ℂ (fun s => mellin fr (-s)) s :=
    DifferentiableAt.comp s (g := mellin fr) (f := fun s : ℂ => -s) h differentiableAt_id.neg
  have : G = fun s => mellin fr (-s) := funext G_eq_mellin
  rw [this]; exact h2

/-- Real `s > 1` case, in the form `ζ₀`-free. -/
private lemma G_real {s : ℝ} (hs : 1 < s) :
    G (s : ℂ) = ((ZetaAsymptotics.termTSum s : ℝ) : ℂ) := by
  have hs' : 0 < (s : ℂ).re := by simp; linarith
  have hint := integrableOn_fract_mul_cpow hs'
  have hU : (⋃ n : ℕ, Set.Ico ((n : ℝ) + 1) ((n : ℝ) + 1 + 1)) = Set.Ici 1 := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_Ico, Set.mem_Ici]
    constructor
    · rintro ⟨n, h1, _⟩
      have : (0:ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    · intro hx
      refine ⟨⌊x⌋₊ - 1, ?_⟩
      have h1 : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by simpa using hx)
      have a := Nat.floor_le (by linarith : (0:ℝ) ≤ x)
      have b := Nat.lt_floor_add_one x
      rw [Nat.cast_sub h1]
      simp only [Nat.cast_one]
      constructor <;> linarith
  have hd : Pairwise (Function.onFun Disjoint fun n : ℕ => Set.Ico ((n : ℝ) + 1) ((n : ℝ) + 1 + 1)) := by
    intro m n hmn
    rw [Function.onFun, Set.disjoint_left]
    intro x hx hx'
    simp only [Set.mem_Ico] at hx hx'
    rcases lt_or_gt_of_ne hmn with h | h
    · have : (m : ℝ) + 1 ≤ n := by exact_mod_cast h
      linarith [hx.2, hx'.1]
    · have : (n : ℝ) + 1 ≤ m := by exact_mod_cast h
      linarith [hx.1, hx'.2]
  have hint' : IntegrableOn (fun x : ℝ ↦ ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-(s:ℂ) - 1))
      (⋃ n : ℕ, Set.Ico ((n : ℝ) + 1) ((n : ℝ) + 1 + 1)) := by
    rw [hU]
    exact (integrableOn_Ici_iff_integrableOn_Ioi).2 hint
  unfold G
  rw [setIntegral_congr_set Ioi_ae_eq_Ici, ← hU,
    integral_iUnion (fun n => measurableSet_Ico) hd hint', ZetaAsymptotics.termTSum,
    Complex.ofReal_tsum]
  congr 1
  ext n
  have hn : (0:ℝ) < (n:ℝ) + 1 := by positivity
  have e1 : ∫ x in Set.Ico ((n : ℝ) + 1) ((n : ℝ) + 1 + 1),
        ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-(s:ℂ) - 1) =
      ∫ x in Set.Ico ((n : ℝ) + 1) ((n : ℝ) + 1 + 1), (((x - ((n:ℝ)+1)) / x ^ (s + 1) : ℝ) : ℂ) := by
    refine setIntegral_congr_fun measurableSet_Ico fun x hx => ?_
    simp only [Set.mem_Ico] at hx
    have hx0 : 0 < x := by linarith [hx.1]
    have hf : Int.fract x = x - ((n:ℝ)+1) := by
      rw [Int.fract, show ⌊x⌋ = ((n+1 : ℕ) : ℤ) from ?_]
      · push_cast; ring
      · rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith [hx.1, hx.2]
    have hc : (x : ℂ) ^ (-(s:ℂ) - 1) = ((x ^ (-(s+1)) : ℝ) : ℂ) := by
      rw [Complex.ofReal_cpow hx0.le]; push_cast; ring_nf
    rw [hc, hf, Real.rpow_neg hx0.le]
    push_cast
    simp [div_eq_mul_inv]
  rw [e1, integral_complex_ofReal, ZetaAsymptotics.term, integral_Ico_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith)]
  push_cast
  rfl

private theorem riemannZeta₀_eq_aux {s : ℂ} (hs : 0 < s.re) :
    riemannZeta₀ s = 1 - s * G s := by
  set U : Set ℂ := {s | 0 < s.re} with hUdef
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hUc : Convex ℝ U := convex_halfSpace_re_gt 0
  have hdiff : DifferentiableOn ℂ (fun s => riemannZeta₀ s - (1 - s * G s)) U := by
    intro z hz
    have : DifferentiableAt ℂ (fun s => riemannZeta₀ s - (1 - s * G s)) z :=
      (differentiable_riemannZeta₀ z).sub
        ((differentiableAt_const (1:ℂ)).sub (differentiableAt_id.mul (G_differentiableAt hz)))
    exact this.differentiableWithinAt
  have han := hdiff.analyticOnNhd hUo
  have h2 : (2 : ℂ) ∈ U := by simp [hUdef]
  have hfreq : ∃ᶠ z in 𝓝[≠] (2:ℂ), riemannZeta₀ z - (1 - z * G z) = 0 := by
    have hlim : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[≠] 2) (𝓝[≠] (2:ℂ)) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝 2) (𝓝 ((2:ℝ) : ℂ)) :=
          Complex.continuous_ofReal.tendsto 2
        exact (by simpa using this : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝 2) (𝓝 2)).mono_left
          nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with x hx h
        exact hx (by simp only [Set.mem_singleton_iff] at h ⊢; exact_mod_cast h)
    refine hlim.frequently ?_
    refine Filter.Eventually.frequently ?_
    have hev : ∀ᶠ x in 𝓝[≠] (2:ℝ), 1 < x :=
      eventually_nhdsWithin_of_eventually_nhds (lt_mem_nhds (by norm_num))
    filter_upwards [hev] with x hx
    have hx1 : (x : ℂ) ≠ 1 := by
      intro h; have : x = 1 := by exact_mod_cast h
      linarith
    rw [G_real hx, riemannZeta₀, if_neg hx1,
      zeta_eq_tsum_one_div_nat_add_one_cpow (by simpa using hx)]
    have := ZetaAsymptotics.zeta_limit_aux1 hx
    have h2 := congrArg (fun r : ℝ => (r : ℂ)) this
    simp only [Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_one, Complex.ofReal_tsum,
      Complex.ofReal_div] at h2
    have hc : ∀ n : ℕ, ((n:ℂ)+1)^(x:ℂ) = (((n+1:ℝ)^x : ℝ):ℂ) := by
      intro n; rw [Complex.ofReal_cpow (by positivity)]; push_cast; rfl
    simp_rw [hc]
    simp only [one_div] at h2 ⊢
    linear_combination h2
  have := han.eqOn_zero_of_preconnected_of_frequently_eq_zero hUc.isPreconnected h2 hfreq hs
  simpa [sub_eq_zero] using this

/-- **Davenport, Ch. 4, p. 32 (row 4-18)**: for `Re s > 0`, `s ≠ 1`,
`ζ(s) = 1/(s - 1) + 1 - s ∫_1^∞ {x} x^{-s-1} dx`. -/
@[kb "davenport1980" "Ch 4, p. 32"]
theorem riemannZeta_eq_one_div_sub_one_add_one_sub_mul_integral {s : ℂ} (hs : 0 < s.re)
    (hs1 : s ≠ 1) :
    riemannZeta s = 1 / (s - 1) + 1 -
      s * ∫ x in Set.Ioi (1 : ℝ), ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1) := by
  have h := riemannZeta₀_eq_aux hs
  rw [riemannZeta_eq_inv_sub_add hs1, h]
  change _ = _ - s * G s
  rw [one_div]; ring

end NTKB.Davenport
