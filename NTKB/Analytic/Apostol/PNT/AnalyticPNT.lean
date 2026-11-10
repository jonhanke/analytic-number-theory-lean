/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import NTKB.Analytic.Apostol.PNT.ZetaInverseBounds
import NTKB.Analytic.Apostol.PNT.Psi1Integral
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma

/-!
# Toward Apostol's Theorem 13.9 (completion of the analytic proof of the PNT)

The function `h(s) = (1/(s(s+1))) (-ζ'(s)/ζ(s) - 1/(s-1))` of Theorem 13.3: bounds on the
half-plane `σ ≥ 1`. For `|t| ≥ e`, `|h(σ + it)| ≤ (M log⁹ |t| + 1)/t²` (Theorem 13.7; negative `t` by
`ζ(s̄) = conj ζ(s)`).
-/

open Complex Filter Topology ComplexConjugate MeasureTheory
open scoped Real

namespace NTKB.Apostol

/-- `h(s) = (1/(s(s+1))) (-ζ'(s)/ζ(s) - 1/(s-1))`. -/
noncomputable def hPNT (s : ℂ) : ℂ :=
  1 / (s * (s + 1)) * (-deriv riemannZeta s / riemannZeta s - 1 / (s - 1))

lemma deriv_riemannZeta_conj {s : ℂ} (hs : s ≠ 1) :
    deriv riemannZeta (conj s) = conj (deriv riemannZeta s) := by
  have hd := (differentiableAt_riemannZeta hs).hasDerivAt.conj_conj
  have hfun : (conj ∘ riemannZeta ∘ conj) = riemannZeta := by
    funext z; simp [Function.comp, riemannZeta_conj]
  rw [hfun] at hd
  exact hd.deriv

lemma hPNT_conj {s : ℂ} (hs : s ≠ 1) : hPNT (conj s) = conj (hPNT s) := by
  simp only [hPNT, deriv_riemannZeta_conj hs, riemannZeta_conj, map_mul, map_div₀, map_sub,
    map_neg, map_one, map_add]

/-- `|h(σ + it)| ≤ (M log⁹ |t| + 1)/t²` for `σ ≥ 1`, `|t| ≥ e`. -/
lemma norm_hPNT_le : ∃ M : ℝ, 0 < M ∧ ∀ s : ℂ, 1 ≤ s.re → Real.exp 1 ≤ |s.im| →
    ‖hPNT s‖ ≤ (M * Real.log |s.im| ^ 9 + 1) / s.im ^ 2 := by
  obtain ⟨M, hM, hMb⟩ := apostol_thm_13_7
  refine ⟨M, hM, fun s hσ ht ↦ ?_⟩
  -- reduce to `t > 0`
  have key : ∀ z : ℂ, 1 ≤ z.re → Real.exp 1 ≤ z.im →
      ‖hPNT z‖ ≤ (M * Real.log z.im ^ 9 + 1) / z.im ^ 2 := by
    intro z hz ht'
    have ht0 : 0 < z.im := lt_of_lt_of_le (Real.exp_pos 1) ht'
    have hz1 : z ≠ 1 := fun h ↦ by rw [h] at ht0; simp at ht0
    have h1 : ‖1 / (z * (z + 1))‖ ≤ 1 / z.im ^ 2 := by
      rw [norm_div, norm_one, norm_mul]
      have a1 : z.im ≤ ‖z‖ := (le_abs_self _).trans (abs_im_le_norm z)
      have a2 : z.im ≤ ‖z + 1‖ := by
        have := (le_abs_self _).trans (abs_im_le_norm (z + 1)); simpa using this
      have hn : 0 < ‖z‖ * ‖z + 1‖ := mul_pos (by linarith) (by linarith)
      rw [div_le_div_iff₀ hn (by positivity)]
      nlinarith
    have h2 : ‖-deriv riemannZeta z / riemannZeta z - 1 / (z - 1)‖ ≤ M * Real.log z.im ^ 9 + 1 := by
      refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
      · rw [neg_div, norm_neg]; exact (hMb z hz ht').2
      · rw [norm_div, norm_one]
        have : 1 ≤ ‖z - 1‖ := by
          have he : (1 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
          calc (1 : ℝ) ≤ z.im := he.trans ht'
            _ ≤ |(z - 1).im| := by simp [le_abs_self]
            _ ≤ ‖z - 1‖ := abs_im_le_norm _
        exact div_le_one_of_le₀ this (norm_nonneg _)
    rw [hPNT, norm_mul]
    calc ‖1 / (z * (z + 1))‖ * ‖-deriv riemannZeta z / riemannZeta z - 1 / (z - 1)‖
        ≤ 1 / z.im ^ 2 * (M * Real.log z.im ^ 9 + 1) :=
          mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      _ = (M * Real.log z.im ^ 9 + 1) / z.im ^ 2 := by ring
  rcases le_or_gt 0 s.im with h | h
  · rw [abs_of_nonneg h] at ht ⊢
    exact key s hσ ht
  · rw [abs_of_neg h] at ht ⊢
    have hs1 : s ≠ 1 := fun e ↦ by rw [e] at h; simp at h
    have := key (conj s) (by simpa using hσ) (by simpa using ht)
    rw [hPNT_conj hs1, norm_conj] at this
    simpa using this

lemma analyticAt_riemannZeta {s : ℂ} (hs : s ≠ 1) : AnalyticAt ℂ riemannZeta s :=
  DifferentiableOn.analyticAt (s := {1}ᶜ)
    (fun z hz ↦ (differentiableAt_riemannZeta hz).differentiableWithinAt)
    (isOpen_compl_singleton.mem_nhds hs)

/-- `h` is continuous at every `s ≠ 1` with `σ ≥ 1`. -/
lemma continuousAt_hPNT {s : ℂ} (hs : s ≠ 1) (hσ : 1 ≤ s.re) : ContinuousAt hPNT s := by
  have hz : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re hσ
  have h0 : s * (s + 1) ≠ 0 := by
    refine mul_ne_zero (fun h ↦ ?_) (fun h ↦ ?_)
    · have := congrArg re h; rw [zero_re] at this; linarith
    · have := congrArg re h; rw [add_re, one_re, zero_re] at this; linarith
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  have hd : ContinuousAt (deriv riemannZeta) s := (analyticAt_riemannZeta hs).deriv.continuousAt
  have hζ : ContinuousAt riemannZeta s := (differentiableAt_riemannZeta hs).continuousAt
  have c4 : ContinuousAt (fun z : ℂ ↦ 1 / (z * (z + 1)) *
      (-deriv riemannZeta z / riemannZeta z - 1 / (z - 1))) s := by
    fun_prop (disch := assumption)
  exact c4

/-- `h` is bounded on `1 ≤ σ ≤ 2`, `|t| ≤ e`, `s ≠ 1` (its singularity at `1` is removable). -/
lemma hPNT_bounded_compact : ∃ C₀ : ℝ, ∀ s : ℂ, 1 ≤ s.re → s.re ≤ 2 → |s.im| ≤ Real.exp 1 →
    s ≠ 1 → ‖hPNT s‖ ≤ C₀ := by
  -- near `1`: `h = -(ζ₁'/ζ₁)/(s(s+1))`
  set g : ℂ → ℂ := fun s ↦ -(deriv riemannZeta₁ s / riemannZeta₁ s) / (s * (s + 1))
  have hg : ContinuousAt g 1 := by
    have hd := ((differentiable_riemannZeta₁.differentiableOn (s := Set.univ)).analyticAt
      (z := 1) Filter.univ_mem).deriv.continuousAt
    exact (hd.div differentiable_riemannZeta₁.continuous.continuousAt (by simp)).neg.div
      (by fun_prop) (by norm_num)
  have hev : ∀ᶠ s in 𝓝[≠] (1 : ℂ), hPNT s = g s := by
    filter_upwards [log_deriv_riemannZeta_eq_neg_inv_sub_add] with s hs
    simp only [hPNT, g]
    rw [neg_div, hs]
    ring
  have hgb : ∀ᶠ s in 𝓝 (1 : ℂ), ‖g s‖ ≤ ‖g 1‖ + 1 := by
    filter_upwards [hg.norm.eventually (gt_mem_nhds (lt_add_one ‖g 1‖))] with s hs
    exact hs.le
  obtain ⟨ρ, hρ, hball⟩ : ∃ ρ > 0, ∀ s : ℂ, dist s 1 < ρ → s ≠ 1 → ‖hPNT s‖ ≤ ‖g 1‖ + 1 := by
    have := (hgb.filter_mono nhdsWithin_le_nhds).and hev
    rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at this
    obtain ⟨ρ, hρ, h⟩ := this
    refine ⟨ρ, hρ, fun s hs hs1 ↦ ?_⟩
    obtain ⟨h1, h2⟩ := h hs hs1
    rw [h2]; exact h1
  -- away from `1`: continuity on a compact set
  set K : Set ℂ := Set.diff ((Set.Icc 1 2) ×ℂ (Set.Icc (-Real.exp 1) (Real.exp 1)))
    (Metric.ball 1 ρ)
  have hK : IsCompact K := (isCompact_Icc.reProdIm isCompact_Icc).diff Metric.isOpen_ball
  have hcont : ContinuousOn hPNT K := by
    intro s hs
    have hs1 : s ≠ 1 := fun h ↦ hs.2 (by rw [h]; exact Metric.mem_ball_self hρ)
    exact (continuousAt_hPNT hs1 hs.1.1.1).continuousWithinAt
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont
  refine ⟨max C (‖g 1‖ + 1), fun s h1 h2 ht hs1 ↦ ?_⟩
  by_cases hd : dist s 1 < ρ
  · exact (hball s hd hs1).trans (le_max_right _ _)
  · exact (hC s ⟨⟨⟨h1, h2⟩, abs_le.mp ht⟩, fun hb ↦ hd hb⟩).trans (le_max_left _ _)

/-- `log⁹ y ≤ 18⁹ y^{1/2}` for `y ≥ 1`. -/
lemma log_pow_nine_le {y : ℝ} (hy : 1 ≤ y) : Real.log y ^ 9 ≤ 18 ^ 9 * y ^ (1 / 2 : ℝ) := by
  have h := Real.log_le_rpow_div (by linarith : (0 : ℝ) ≤ y) (show (0 : ℝ) < 1 / 18 by norm_num)
  have hl : 0 ≤ Real.log y := Real.log_nonneg hy
  have h' : Real.log y ≤ 18 * y ^ (1 / 18 : ℝ) := by
    rw [div_eq_mul_inv, show ((1 : ℝ) / 18)⁻¹ = 18 by norm_num] at h; linarith
  calc Real.log y ^ 9 ≤ (18 * y ^ (1 / 18 : ℝ)) ^ 9 := pow_le_pow_left₀ hl h' 9
    _ = 18 ^ 9 * y ^ (1 / 2 : ℝ) := by
        rw [mul_pow, ← Real.rpow_natCast (y ^ (1 / 18 : ℝ)) 9, ← Real.rpow_mul (by linarith)]
        norm_num

/-- An integrable majorant: `|h(σ+it)| ≤ C (1 + |t|)^{-3/2}` for `1 ≤ σ ≤ 2`, `s ≠ 1`. -/
lemma norm_hPNT_le_majorant : ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, 1 ≤ s.re → s.re ≤ 2 → s ≠ 1 →
    ‖hPNT s‖ ≤ C * (1 + |s.im|) ^ (-(3 / 2 : ℝ)) := by
  obtain ⟨C₀, hC₀⟩ := hPNT_bounded_compact
  obtain ⟨M, hM, hMb⟩ := norm_hPNT_le
  set C₁ : ℝ := M * 18 ^ 9 + 1
  set C : ℝ := max (|C₀| * (1 + Real.exp 1) ^ (3 / 2 : ℝ) + 1) (2 ^ (3 / 2 : ℝ) * C₁)
  have hCpos : 0 < C := lt_max_of_lt_left (by positivity)
  refine ⟨C, hCpos, fun s h1 h2 hs1 ↦ ?_⟩
  set t := |s.im|
  have ht0 : 0 ≤ t := abs_nonneg _
  have he1 : (1 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  rcases le_or_gt t (Real.exp 1) with ht | ht
  · -- compact part
    have hb := hC₀ s h1 h2 ht hs1
    have hpow : (1 + Real.exp 1) ^ (-(3 / 2 : ℝ)) ≤ (1 + t) ^ (-(3 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by norm_num)
    have hpos : 0 < (1 + Real.exp 1) ^ (-(3 / 2 : ℝ)) := by positivity
    have hinv : (1 + Real.exp 1) ^ (3 / 2 : ℝ) * (1 + Real.exp 1) ^ (-(3 / 2 : ℝ)) = 1 := by
      rw [← Real.rpow_add (by positivity)]; simp
    calc ‖hPNT s‖ ≤ |C₀| := hb.trans (le_abs_self _)
      _ ≤ (|C₀| * (1 + Real.exp 1) ^ (3 / 2 : ℝ) + 1) * (1 + Real.exp 1) ^ (-(3 / 2 : ℝ)) := by
          rw [add_mul, mul_assoc, hinv, mul_one]; linarith
      _ ≤ C * (1 + t) ^ (-(3 / 2 : ℝ)) := by
          gcongr
          · exact le_max_left _ _
  · -- `|t| ≥ e`
    have hb := hMb s h1 ht.le
    have ht1 : 1 ≤ t := he1.trans ht.le
    have hsq : s.im ^ 2 = t ^ 2 := (sq_abs _).symm
    rw [hsq] at hb
    have hlog := log_pow_nine_le ht1
    have hhalf : (1 : ℝ) ≤ t ^ (1 / 2 : ℝ) := Real.one_le_rpow ht1 (by norm_num)
    have hnum : M * Real.log t ^ 9 + 1 ≤ C₁ * t ^ (1 / 2 : ℝ) := by
      simp only [C₁]; nlinarith
    have hkey : t ^ (1 / 2 : ℝ) / t ^ 2 = t ^ (-(3 / 2 : ℝ)) := by
      rw [← Real.rpow_natCast t 2, ← Real.rpow_sub (by linarith)]; norm_num
    have h1t : t ^ (-(3 / 2 : ℝ)) ≤ 2 ^ (3 / 2 : ℝ) * (1 + t) ^ (-(3 / 2 : ℝ)) := by
      have : (1 + t) ≤ 2 * t := by linarith
      have h := Real.rpow_le_rpow_of_nonpos (by linarith) this (show -(3 / 2 : ℝ) ≤ 0 by norm_num)
      rw [Real.mul_rpow (by norm_num) (by linarith)] at h
      have h2 : (2 : ℝ) ^ (-(3 / 2 : ℝ)) * 2 ^ (3 / 2 : ℝ) = 1 := by
        rw [← Real.rpow_add (by norm_num)]; simp
      calc t ^ (-(3 / 2 : ℝ)) = 2 ^ (3 / 2 : ℝ) * (2 ^ (-(3 / 2 : ℝ)) * t ^ (-(3 / 2 : ℝ))) := by
            rw [← mul_assoc, mul_comm (2 ^ (3 / 2 : ℝ)), h2, one_mul]
        _ ≤ 2 ^ (3 / 2 : ℝ) * (1 + t) ^ (-(3 / 2 : ℝ)) := by gcongr
    calc ‖hPNT s‖ ≤ (M * Real.log t ^ 9 + 1) / t ^ 2 := hb
      _ ≤ C₁ * t ^ (1 / 2 : ℝ) / t ^ 2 := by gcongr
      _ = C₁ * t ^ (-(3 / 2 : ℝ)) := by rw [mul_div_assoc, hkey]
      _ ≤ C₁ * (2 ^ (3 / 2 : ℝ) * (1 + t) ^ (-(3 / 2 : ℝ))) := by gcongr
      _ = (2 ^ (3 / 2 : ℝ) * C₁) * (1 + t) ^ (-(3 / 2 : ℝ)) := by ring
      _ ≤ C * (1 + t) ^ (-(3 / 2 : ℝ)) := by gcongr; exact le_max_right _ _

/-- The integrand `x^{s-1} h(s)` on the line `σ = c`. -/
noncomputable def pntIntegrand (x c y : ℝ) : ℂ :=
  (x : ℂ) ^ ((c : ℂ) + y * I - 1) * hPNT (c + y * I)

lemma continuousAt_pntIntegrand {x : ℝ} (hx : 0 < x) {c y : ℝ} (hc : 1 ≤ c)
    (hne : (c : ℂ) + y * I ≠ 1) :
    ContinuousAt (fun p : ℝ × ℝ ↦ pntIntegrand x p.1 p.2) (c, y) := by
  have hz : ContinuousAt hPNT ((c : ℂ) + y * I) := continuousAt_hPNT hne (by simpa using hc)
  have hx' : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hlin : Continuous (fun p : ℝ × ℝ ↦ (p.1 : ℂ) + p.2 * I) := by fun_prop
  have h1 : ContinuousAt (fun p : ℝ × ℝ ↦ hPNT ((p.1 : ℂ) + p.2 * I)) (c, y) :=
    ContinuousAt.comp (g := hPNT) hz hlin.continuousAt
  have h3 : Continuous (fun p : ℝ × ℝ ↦ (p.1 : ℂ) + p.2 * I - 1) := hlin.sub continuous_const
  have h2 : Continuous (fun p : ℝ × ℝ ↦ (x : ℂ) ^ ((p.1 : ℂ) + p.2 * I - 1)) :=
    h3.const_cpow (Or.inl hx')
  exact h2.continuousAt.mul h1

lemma norm_pntIntegrand_le {x : ℝ} (hx : 1 ≤ x) {C : ℝ}
    (hC : ∀ s : ℂ, 1 ≤ s.re → s.re ≤ 2 → s ≠ 1 → ‖hPNT s‖ ≤ C * (1 + |s.im|) ^ (-(3 / 2 : ℝ)))
    {c y : ℝ} (hc1 : 1 ≤ c) (hc2 : c ≤ 2) (hne : (c : ℂ) + y * I ≠ 1) :
    ‖pntIntegrand x c y‖ ≤ x * (C * (1 + ‖y‖) ^ (-(3 / 2 : ℝ))) := by
  have hx0 : 0 < x := by linarith
  rw [pntIntegrand, norm_mul, norm_cpow_eq_rpow_re_of_pos hx0]
  have h1 : x ^ ((c : ℂ) + y * I - 1).re ≤ x := by
    simp only [sub_re, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero, mul_one,
      sub_self, add_zero, one_re]
    calc x ^ (c - 1) ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx (by linarith)
      _ = x := Real.rpow_one x
  have h2 := hC ((c : ℂ) + y * I) (by simpa using hc1) (by simpa using hc2) hne
  simp only [add_im, ofReal_im, mul_im, ofReal_re, I_re, I_im, mul_zero, mul_one, zero_add,
    add_zero] at h2
  rw [Real.norm_eq_abs]
  exact mul_le_mul h1 h2 (norm_nonneg _) hx0.le

/-- **Apostol, Theorem 13.9**, first part: for `x ≥ 1`,
`ψ₁(x)/x² - (1/2)(1 - 1/x)² = (1/2π) ∫_{-∞}^{∞} h(1 + it) e^{it log x} dt`, the integral
`∫ |h(1 + it)| dt` being convergent. -/
@[kb "apostol1976" "Thm 13.9, p. 289"]
theorem apostol_thm_13_9_integral {x : ℝ} (hx : 1 ≤ x) :
    Integrable (fun y : ℝ ↦ hPNT (1 + y * I)) ∧
    ((psi1 x / x ^ 2 - (1 / 2) * (1 - 1 / x) ^ 2 : ℝ) : ℂ) =
      (1 / (2 * π)) * ∫ y : ℝ, (x : ℂ) ^ (y * I) * hPNT (1 + y * I) := by
  have hx0 : 0 < x := by linarith
  obtain ⟨C, hC, hCb⟩ := norm_hPNT_le_majorant
  set c : ℕ → ℝ := fun n ↦ 1 + 1 / ((n : ℝ) + 1)
  have hc1 : ∀ n, 1 < c n := fun n ↦ by
    have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    simp only [c]; linarith
  have hc2 : ∀ n, c n ≤ 2 := fun n ↦ by
    simp only [c]
    have : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [n.cast_nonneg (α := ℝ)]
    linarith
  have hclim : Tendsto c atTop (𝓝 1) := by
    have h0 : Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have := (tendsto_const_nhds (x := (1 : ℝ))).add h0
    simpa [c] using this
  have hne : ∀ {c' : ℝ} (y : ℝ), 1 < c' → (c' : ℂ) + y * I ≠ 1 := fun y h e ↦ by
    have := congrArg re e; simp at this; linarith
  have hne0 : ∀ {y : ℝ}, y ≠ 0 → (1 : ℂ) + y * I ≠ 1 := fun hy e ↦ by
    have := congrArg im e; simp at this; exact hy this
  have hae : ∀ᵐ y : ℝ, y ≠ 0 := by
    rw [ae_iff]; simp
  -- pointwise convergence
  have hlim : ∀ y : ℝ, y ≠ 0 → Tendsto (fun n ↦ pntIntegrand x (c n) y) atTop
      (𝓝 (pntIntegrand x 1 y)) := by
    intro y hy
    have hne1 : ((1 : ℝ) : ℂ) + y * I ≠ 1 := by rw [ofReal_one]; exact hne0 hy
    have hcont := continuousAt_pntIntegrand hx0 (c := 1) (y := y) le_rfl hne1
    have hpair : Tendsto (fun n ↦ (c n, y)) atTop (𝓝 ((1 : ℝ), y)) :=
      hclim.prodMk_nhds tendsto_const_nhds
    have h := hcont.tendsto.comp hpair
    exact h
  have hcontn : ∀ n, Continuous (fun y ↦ pntIntegrand x (c n) y) := by
    intro n
    rw [continuous_iff_continuousAt]
    intro y
    exact (continuousAt_pntIntegrand hx0 (hc1 n).le (hne y (hc1 n))).comp
      (f := fun y : ℝ ↦ (c n, y)) (by fun_prop)
  have hbound_int : Integrable (fun y : ℝ ↦ x * (C * (1 + ‖y‖) ^ (-(3 / 2 : ℝ)))) :=
    ((integrable_one_add_norm (E := ℝ) (r := 3 / 2) (by simp; norm_num)).const_mul C).const_mul x
  have hDCT := tendsto_integral_of_dominated_convergence
    (F := fun n y ↦ pntIntegrand x (c n) y) (f := fun y ↦ pntIntegrand x 1 y) _
    (fun n ↦ (hcontn n).aestronglyMeasurable) hbound_int
    (fun n ↦ Eventually.of_forall fun y ↦
      norm_pntIntegrand_le hx hCb (hc1 n).le (hc2 n) (hne y (hc1 n)))
    (hae.mono fun y hy ↦ hlim y hy)
  -- integrability of `h(1 + it)`
  have hmeas : AEStronglyMeasurable (fun y : ℝ ↦ hPNT (1 + y * I)) := by
    refine aestronglyMeasurable_of_tendsto_ae atTop (f := fun n (y : ℝ) ↦ hPNT ((c n : ℂ) + y * I))
      (fun n ↦ ?_) (hae.mono fun y hy ↦ ?_)
    · refine Continuous.aestronglyMeasurable (continuous_iff_continuousAt.mpr fun y ↦ ?_)
      exact (continuousAt_hPNT (hne y (hc1 n)) (by simp; linarith [hc1 n])).comp
        (f := fun y : ℝ ↦ (c n : ℂ) + y * I) (by fun_prop)
    · have h := (continuousAt_hPNT (hne0 hy) (by simp)).tendsto
      refine h.comp ?_
      have : Tendsto (fun n ↦ ((c n : ℂ) + y * I)) atTop (𝓝 ((1 : ℝ) + y * I)) :=
        ((continuous_ofReal.tendsto 1).comp hclim).add tendsto_const_nhds
      simpa using this
  have hint : Integrable (fun y : ℝ ↦ hPNT (1 + y * I)) := by
    refine ((integrable_one_add_norm (E := ℝ) (r := 3 / 2) (by simp; norm_num)).const_mul C).mono'
      hmeas
      (hae.mono fun y hy ↦ ?_)
    have := hCb (1 + y * I) (by simp) (by simp) (hne0 hy)
    simpa [Real.norm_eq_abs] using this
  refine ⟨hint, ?_⟩
  have hfun : ∀ c' : ℝ, (fun y : ℝ ↦ (x : ℂ) ^ ((c' : ℂ) + y * I - 1) *
      (1 / (((c' : ℂ) + y * I) * ((c' : ℂ) + y * I + 1)) *
        (-deriv riemannZeta (c' + y * I) / riemannZeta (c' + y * I) - 1 / ((c' : ℂ) + y * I - 1))))
      = fun y ↦ pntIntegrand x c' y := fun c' ↦ by
    funext y; rw [pntIntegrand, hPNT]
  have hconst : ∀ n, ((psi1 x / x ^ 2 - (1 / 2) * (1 - 1 / x) ^ 2 : ℝ) : ℂ) =
      (1 / (2 * π)) * ∫ y : ℝ, pntIntegrand x (c n) y := fun n ↦ by
    rw [← hfun]; exact apostol_thm_13_3 (hc1 n) hx
  have hlim2 := hDCT.const_mul (1 / (2 * π : ℂ))
  have heq := tendsto_nhds_unique (tendsto_const_nhds.congr hconst) hlim2
  rw [heq]
  have hfun1 : (fun y : ℝ ↦ pntIntegrand x 1 y) = fun y : ℝ ↦ (x : ℂ) ^ (y * I) * hPNT (1 + y * I) := by
    funext y
    rw [pntIntegrand, ofReal_one, show (1 : ℂ) + y * I - 1 = y * I by ring]
  rw [hfun1]

/-- The Riemann–Lebesgue step: `∫ h(1 + it) e^{it log x} dt → 0` as `x → ∞`. -/
lemma tendsto_integral_pnt :
    Tendsto (fun x : ℝ ↦ ∫ y : ℝ, (x : ℂ) ^ (y * I) * hPNT (1 + y * I)) atTop (𝓝 0) := by
  set f : ℝ → ℂ := fun y ↦ hPNT (1 + y * I)
  have hRL := tendsto_integral_exp_inner_smul_cocompact f
  set g : ℝ → ℝ := fun x ↦ -(Real.log x / (2 * π))
  have hg : Tendsto g atTop (cocompact ℝ) := by
    rw [cocompact_eq_atBot_atTop]
    refine Tendsto.mono_right ?_ le_sup_left
    exact tendsto_neg_atTop_atBot.comp (Real.tendsto_log_atTop.atTop_div_const (by positivity))
  refine (hRL.comp hg).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  simp only [Function.comp, g, f]
  refine integral_congr_ae (Eventually.of_forall fun v ↦ ?_)
  simp only [Real.inner_apply, Circle.smul_def, Real.fourierChar_apply, smul_eq_mul]
  rw [cpow_def_of_ne_zero (by exact_mod_cast hx.ne'), ← ofReal_log hx.le]
  congr 1
  push_cast
  field_simp

/-- **Apostol, Theorem 13.9**: `ψ₁(x) ~ x²/2` as `x → ∞`. -/
@[kb "apostol1976" "Thm 13.9, p. 289"]
theorem apostol_thm_13_9 : Tendsto (fun x ↦ psi1 x / (x ^ 2 / 2)) atTop (𝓝 1) := by
  have h1 : Tendsto (fun x : ℝ ↦ psi1 x / x ^ 2 - (1 / 2) * (1 - 1 / x) ^ 2) atTop (𝓝 0) := by
    have h := (tendsto_integral_pnt.const_mul (1 / (2 * π : ℂ)))
    rw [mul_zero] at h
    have h' := (continuous_re.tendsto 0).comp h
    simp only [zero_re] at h'
    refine h'.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with x hx
    simp only [Function.comp]
    rw [← (apostol_thm_13_9_integral hx).2, ofReal_re]
  have h2 : Tendsto (fun x : ℝ ↦ (1 / 2) * (1 - 1 / x) ^ 2) atTop (𝓝 (1 / 2)) := by
    have : Tendsto (fun x : ℝ ↦ 1 / x) atTop (𝓝 0) := by
      simpa using tendsto_inv_atTop_zero (𝕜 := ℝ)
    have := ((tendsto_const_nhds (x := (1 : ℝ))).sub this).pow 2 |>.const_mul (1 / 2)
    simpa using this
  have h3 := (h1.add h2).mul_const 2
  simp only [zero_add] at h3
  refine (h3.congr' ?_).trans (by norm_num)
  filter_upwards [eventually_gt_atTop 0] with x hx
  field_simp
  ring

/-- **The prime number theorem** (Apostol, end of §13.7): `ψ(x)/x → 1`, by Theorems 13.9 and 13.1. -/
@[kb "apostol1976" "Thm 13.9, p. 290"]
theorem prime_number_theorem_psi : Tendsto (fun x ↦ Chebyshev.psi x / x) atTop (𝓝 1) :=
  tendsto_psi_div_of_psi1 apostol_thm_13_9

end NTKB.Apostol
