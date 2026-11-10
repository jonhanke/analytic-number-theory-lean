/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Davenport.Zeros.PsiMellin
import NTKB.Analytic.Davenport.Zeros.PNTConditional
import Mathlib.Analysis.MellinTransform

/-!
# `ψ(x) = x + O(x^a)` forbids zeros with `σ > a`

**Davenport, Ch. 18, p. 113 (row 18-11).** If `|ψ(x) - x| ≤ C x^a` for `x ≥ 1`, with `a < 1`, then
`ζ(s) ≠ 0` for `σ > a`: the right side of 18-12,
`G(s) = s/(s - 1) + s ∫_1^∞ (ψ(x) - x) x^{-s-1} dx`, is holomorphic for `σ > a`, `s ≠ 1` (a Mellin
transform), and equals `-ζ'/ζ` for `σ > 1`; by the identity theorem `ζ G = -ζ'` on a convex
region containing a zero `ρ` with `β > a` and avoiding `s = 1`, which is impossible since
`-ζ'/ζ` has a pole at `ρ`.
-/

open Filter Topology Complex Set MeasureTheory Asymptotics
open scoped Real ArithmeticFunction.vonMangoldt

namespace NTKB

/-- `(ψ(t) - t) 1_{t > 1}`. -/
noncomputable def psiErr (t : ℝ) : ℂ := (Ioi (1 : ℝ)).indicator (fun t ↦ ((Chebyshev.psi t - t : ℝ) : ℂ)) t

lemma locallyIntegrableOn_psiErr : LocallyIntegrableOn psiErr (Ioi 0) := by
  have h1 : LocallyIntegrable (fun t : ℝ ↦ Chebyshev.psi t - t) volume :=
    Chebyshev.psi_mono.locallyIntegrable.sub continuous_id.locallyIntegrable
  have h2 : LocallyIntegrable (fun t : ℝ ↦ ((Chebyshev.psi t - t : ℝ) : ℂ)) volume := by
    intro x
    obtain ⟨s, hs, hint⟩ := h1 x
    exact ⟨s, hs, hint.ofReal⟩
  exact (h2.indicator measurableSet_Ioi).locallyIntegrableOn _

/-- `mellin psiErr (-s) = ∫_1^∞ (ψ(t) - t) t^{-s-1} dt`. -/
lemma mellin_psiErr (s : ℂ) :
    mellin psiErr (-s) = ∫ t in Ioi (1 : ℝ), ((Chebyshev.psi t - t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1)) := by
  unfold mellin psiErr
  rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi]
  congr 1
  funext t
  simp only [Set.indicator_apply, mem_Ioi, smul_eq_mul]
  by_cases h1 : 1 < t
  · have h0 : 0 < t := lt_trans one_pos h1
    simp [h0, h1, show -s - 1 = -(s + 1) by ring, mul_comm]
  · simp [h1]

/-- `G(s) = s/(s - 1) + s ∫_1^∞ (ψ(t) - t) t^{-s-1} dt`. -/
noncomputable def psiG (s : ℂ) : ℂ := s / (s - 1) + s * mellin psiErr (-s)

lemma psiErr_isBigO_atTop {a C : ℝ}
    (h : ∀ x : ℝ, 1 ≤ x → |Chebyshev.psi x - x| ≤ C * x ^ a) :
    psiErr =O[atTop] (fun t : ℝ ↦ t ^ (-(-a))) := by
  refine IsBigO.of_bound C ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
  have ht0 : 0 < t := lt_trans one_pos ht
  have e : psiErr t = ((Chebyshev.psi t - t : ℝ) : ℂ) := by
    unfold psiErr; rw [Set.indicator_of_mem (show t ∈ Ioi (1 : ℝ) from ht)]
  rw [e, Complex.norm_real, Real.norm_eq_abs, neg_neg, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg ht0.le _)]
  exact h t ht.le

lemma psiErr_isBigO_nhdsGT (b : ℝ) : psiErr =O[𝓝[>] 0] (fun t : ℝ ↦ t ^ (-b)) := by
  refine IsBigO.of_bound 0 ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
  have e : psiErr t = 0 := by
    unfold psiErr; rw [Set.indicator_of_notMem (show t ∉ Ioi (1 : ℝ) from not_lt.mpr ht.2.le)]
  rw [e, norm_zero, zero_mul]

lemma differentiableAt_mellin_psiErr {a C : ℝ}
    (h : ∀ x : ℝ, 1 ≤ x → |Chebyshev.psi x - x| ≤ C * x ^ a) {s : ℂ} (hs : a < s.re) :
    DifferentiableAt ℂ (mellin psiErr) (-s) :=
  mellin_differentiableAt_of_isBigO_rpow (a := -a) (b := (-s).re - 1)
    locallyIntegrableOn_psiErr (psiErr_isBigO_atTop h) (by simp; linarith)
    (psiErr_isBigO_nhdsGT _) (by linarith)

lemma differentiableAt_psiG {a C : ℝ} (h : ∀ x : ℝ, 1 ≤ x → |Chebyshev.psi x - x| ≤ C * x ^ a)
    {s : ℂ} (hs : a < s.re) (hs1 : s ≠ 1) : DifferentiableAt ℂ psiG s := by
  have hm := differentiableAt_mellin_psiErr h hs
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have h1 : DifferentiableAt ℂ (fun s : ℂ ↦ s / (s - 1)) s :=
    DifferentiableAt.div (𝕜 := ℂ) (c := fun s : ℂ ↦ s) (d := fun s : ℂ ↦ s - 1) differentiableAt_fun_id
      (differentiableAt_fun_id.sub_const 1) hs1'
  have h2 : DifferentiableAt ℂ (fun s : ℂ ↦ mellin psiErr (-s)) s :=
    hm.comp s differentiableAt_fun_id.neg
  have h3 : DifferentiableAt ℂ (fun s : ℂ ↦ s * mellin psiErr (-s)) s :=
    (differentiableAt_fun_id (x := s)).mul h2
  have e : psiG = fun s : ℂ ↦ s / (s - 1) + s * mellin psiErr (-s) := rfl
  rw [e]
  exact h1.add h3

lemma psiG_eq {s : ℂ} (hs : 1 < s.re) :
    psiG s = -deriv riemannZeta s / riemannZeta s := by
  rw [Davenport.neg_logDeriv_riemannZeta_eq_integral hs, psiG, mellin_psiErr]

/-- **Davenport, Ch. 18, p. 113 (row 18-11)**: if `|ψ(x) - x| ≤ C x^a` for all `x ≥ 1`, with
`a < 1`, then every zero of `ζ` has real part at most `a`. -/
@[kb "davenport1980" "Ch 18, p. 113"]
theorem Davenport.riemannZeta_zero_re_le_of_psi {a C : ℝ}
    (h : ∀ x : ℝ, 1 ≤ x → |Chebyshev.psi x - x| ≤ C * x ^ a) {ρ : ℂ} (hρ : riemannZeta ρ = 0) :
    ρ.re ≤ a := by
  by_contra hlt
  push Not at hlt
  have hρ1 : ρ.re < 1 := by
    by_contra h1; push Not at h1
    exact riemannZeta_ne_zero_of_one_le_re h1 hρ
  have hρne1 : ρ ≠ 1 := fun e ↦ by rw [e] at hρ1; simp at hρ1
  -- a convex open region `W` containing `ρ` and `2 ± 2i`, avoiding `1`
  set ε : ℝ := if 0 ≤ ρ.im then 1 else -1 with hε
  have hε2 : ε ^ 2 = 1 := by simp only [ε]; split_ifs <;> norm_num
  set W : Set ℂ := {s | a < s.re} ∩ {s | s.re - 1 < ε * s.im} with hW
  have hWo : IsOpen W :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt (Complex.continuous_re.sub continuous_const)
        (continuous_const.mul Complex.continuous_im))
  have hWc : Convex ℝ W := by
    refine (convex_halfSpace_gt (f := fun s : ℂ ↦ s.re) ?_ a).inter ?_
    · exact ⟨fun x y ↦ by simp, fun c x ↦ by simp⟩
    · have : {s : ℂ | s.re - 1 < ε * s.im} = {s : ℂ | s.re - ε * s.im < 1} := by
        ext s; simp only [mem_setOf_eq]; constructor <;> intro h <;> linarith
      rw [this]
      refine convex_halfSpace_lt (f := fun s : ℂ ↦ s.re - ε * s.im) ?_ 1
      exact ⟨fun x y ↦ by simp; ring, fun c x ↦ by simp; ring⟩
  have hρW : ρ ∈ W := by
    refine ⟨hlt, ?_⟩
    show ρ.re - 1 < ε * ρ.im
    simp only [ε]; split_ifs with hi
    · linarith
    · push Not at hi; linarith
  have h1W : (1 : ℂ) ∉ W := fun h ↦ by
    have := h.2; simp at this
  have hW1 : ∀ s ∈ W, s ≠ 1 := fun s hs e ↦ h1W (e ▸ hs)
  -- `ζ G = -ζ'` on `W`
  set z₀ : ℂ := 2 + 2 * ε * I with hz₀
  have hz₀W : z₀ ∈ W := by
    refine ⟨?_, ?_⟩
    · show a < z₀.re; simp [z₀]; linarith
    · show z₀.re - 1 < ε * z₀.im
      simp [z₀]; nlinarith
  have hz₀re : 1 < z₀.re := by simp [z₀]
  have hanZ : ∀ s, s ≠ 1 → AnalyticAt ℂ riemannZeta s := fun s hs ↦ analyticAt_riemannZeta hs
  have hA : AnalyticOnNhd ℂ (fun s ↦ riemannZeta s * psiG s) W := by
    intro s hs
    have hd : ∀ᶠ w in 𝓝 s, DifferentiableAt ℂ (fun s ↦ riemannZeta s * psiG s) w := by
      filter_upwards [hWo.mem_nhds hs] with w hw
      exact (differentiableAt_riemannZeta (hW1 w hw)).mul
        (differentiableAt_psiG h hw.1 (hW1 w hw))
    exact Complex.analyticAt_iff_eventually_differentiableAt.mpr hd
  have hB : AnalyticOnNhd ℂ (fun s ↦ -deriv riemannZeta s) W := fun s hs ↦
    (hanZ s (hW1 s hs)).deriv.neg
  have hev : (fun s ↦ riemannZeta s * psiG s) =ᶠ[𝓝 z₀] fun s ↦ -deriv riemannZeta s := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show z₀ ∈ {s : ℂ | 1 < s.re} from hz₀re)] with s hs
    have hs' : 1 < s.re := hs
    have hz : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs'
    rw [psiG_eq hs']
    field_simp
  have hEq := hA.eqOn_of_preconnected_of_eventuallyEq hB hWc.isPreconnected hz₀W hev
  -- near `ρ`: `G = -ζ'/ζ`, so `-ζ'/ζ` would be bounded near `ρ`
  have hρ0 : ρ ≠ 0 := fun e ↦ by
    rw [e, riemannZeta_zero] at hρ; norm_num at hρ
  have hfin : analyticOrderAt riemannZeta ρ ≠ ⊤ := by
    intro htop
    rw [analyticOrderAt_eq_top] at htop
    -- `ζ` vanishes near `ρ`, hence on the connected set `W` (where it is analytic), in
    -- particular at `z₀`
    have hZW : AnalyticOnNhd ℂ riemannZeta W := fun s hs ↦ hanZ s (hW1 s hs)
    have := hZW.eqOn_zero_of_preconnected_of_eventuallyEq_zero hWc.isPreconnected hρW htop hz₀W
    exact riemannZeta_ne_zero_of_one_lt_re hz₀re this
  set m := (analyticOrderAt riemannZeta ρ).toNat with hm
  have hmeq : analyticOrderAt riemannZeta ρ = (m : ℕ∞) := (ENat.natCast_toNat hfin).symm
  have hm1 : 1 ≤ m := by
    by_contra h0
    have : m = 0 := by omega
    rw [this, Nat.cast_zero, analyticOrderAt_eq_zero] at hmeq
    rcases hmeq with h' | h'
    · exact h' (hanZ ρ hρne1)
    · exact h' hρ
  have hbd := bddNear_logDeriv_sub (hanZ ρ hρne1) hmeq
  have hGc : ContinuousAt psiG ρ := (differentiableAt_psiG h hlt hρne1).continuousAt
  -- on a punctured neighbourhood, `logDeriv ζ = -G`
  have hloc : ∀ᶠ s in 𝓝[≠] ρ, logDeriv riemannZeta s = -psiG s := by
    have hne : ∀ᶠ s in 𝓝[≠] ρ, riemannZeta s ≠ 0 := by
      rcases (hanZ ρ hρne1).eventually_eq_zero_or_eventually_ne_zero with h0 | h0
      · exact absurd (analyticOrderAt_eq_top.mpr h0) hfin
      · exact h0
    filter_upwards [hne, nhdsWithin_le_nhds (hWo.mem_nhds hρW)] with s hs hsW
    have := hEq hsW
    simp only at this
    rw [logDeriv_apply, div_eq_iff hs]
    linear_combination this
  -- so `m/(s - ρ)` is bounded near `ρ`, which is absurd
  have hb2 : BddNear (fun s ↦ (m : ℂ) / (s - ρ)) ρ := by
    have h1 := (bddNear_of_continuousAt hGc).neg
    refine (h1.sub hbd).congr ?_
    filter_upwards [hloc] with s hs
    rw [hs]; ring
  obtain ⟨M, hM⟩ := bddNear_iff_eventually.mp hb2
  have hM' : ∀ᶠ s in 𝓝[≠] ρ, ‖s - ρ‖ < 1 / (|M| + 1) := by
    have : ∀ᶠ s in 𝓝 ρ, ‖s - ρ‖ < 1 / (|M| + 1) := by
      have hc : ContinuousAt (fun s : ℂ ↦ ‖s - ρ‖) ρ := by fun_prop
      exact hc.eventually (gt_mem_nhds (by simp; positivity))
    exact nhdsWithin_le_nhds this
  obtain ⟨s, ⟨hs1, hs2⟩, hs3⟩ := ((hM.and hM').and self_mem_nhdsWithin).exists
  have hsρ : 0 < ‖s - ρ‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hs3)
  rw [norm_div, Complex.norm_natCast] at hs1
  have hm1' : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  have : (m : ℝ) / ‖s - ρ‖ > |M| + 1 := by
    rw [gt_iff_lt, lt_div_iff₀ hsρ]
    have := (lt_div_iff₀ (by positivity)).mp hs2
    nlinarith [abs_nonneg M]
  linarith [le_abs_self M]

/-- **Davenport, Ch. 18, p. 114 (row 18-13)**: if `1/2 ≤ Θ < 1` and `ψ(x) = x + O(x^{Θ+ε})` for
every `ε > 0`, then `ψ(x) = x + O(x^Θ log² x)`. -/
@[kb "davenport1980" "Ch 18, p. 114"]
theorem Davenport.psi_sub_self_le_of_forall_eps {Θ : ℝ} (hΘ : 1 / 2 ≤ Θ) (hΘ1 : Θ < 1)
    (h : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ x : ℝ, 1 ≤ x → |Chebyshev.psi x - x| ≤ C * x ^ (Θ + ε)) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 2 ≤ x →
      |Chebyshev.psi x - x| ≤ C * x ^ Θ * Real.log x ^ 2 := by
  refine Davenport.psi_sub_self_le_of_re_le hΘ hΘ1 fun s hs _ ↦ ?_
  refine le_of_forall_pos_lt_add fun ε hε ↦ ?_
  set ε' := min (ε / 2) ((1 - Θ) / 2) with hε'
  have hε'0 : 0 < ε' := lt_min (by linarith) (by linarith)
  obtain ⟨C, hC⟩ := h ε' hε'0
  have := Davenport.riemannZeta_zero_re_le_of_psi hC hs
  have : ε' < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  linarith

end NTKB
