/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Davenport.Zeros.RiemannVonMangoldt
import NTKB.Analytic.Davenport.Zeros.ZetaResidues
import NTKB.Analytic.Apostol.Zeta.Alternating
import NTKB.Port.Stirling.Basic

/-!
# The Riemann-von Mangoldt formula with `7/8 + S(T)`

**Davenport, Ch. 15, pp. 97-98, (1) (rows 15-3, 15-5).** For `T > 0` not the ordinate of a zero,
`N(T) = (T/2π) log(T/2π) - T/2π + 7/8 + S(T) + O(1/T)`, where `πS(T)` is the change of the argument
of `ζ(s)` by continuous variation along the segments `2 → 2 + iT → 1/2 + iT`, starting from the value
`0` at `s = 2` (`zetaArgS`): by definition
`πS(T) = ∫_0^T Re ζ'/ζ(2 + iy) dy - ∫_{1/2}^2 Im ζ'/ζ(x + iT) dx`, and `exp_zetaArgS` checks that
`ζ(1/2 + iT) = |ζ(1/2 + iT)| e^{iπS(T)}`. The `O(1/T)` is explicit: `|error| ≤ 3/T`.

The proof follows Davenport: `πN(T)` is the change of argument of `ξ` along the same path
(`Davenport.pi_mul_zetaZeroCount_eq`, with no real zeros by `riemannZeta_neg_of_lt_one`), and
`ξ'/ξ = ζ'/ζ + 1/(s - 1) - ½ log π + ½ ψ(s/2 + 1)`. The last three terms have the primitive
`log(-i(s - 1)) - ½ s log π + log Γ(s/2 + 1)`, whose change of argument is computed exactly, and
Stirling's formula with error `O(1/|s|)` (`NTKB.Port.norm_logGamma_sub_stirling_le`, ported from
Tau Ceti) gives `Im log Γ(5/4 + iT/2) = (T/2) log(T/2) - T/2 + 3π/8 + O(1/T)`.
-/

open Filter Topology Complex Set
open scoped Real Interval

namespace NTKB

/-- **Davenport's `S(T)`** (Ch. 15, p. 98): `π^{-1}` times the argument of `ζ(1/2 + iT)` obtained by
continuous variation along `2 → 2 + iT → 1/2 + iT` starting with the value `0` at `2`, written as
the integral of the log-derivative along that path (`T` not an ordinate). -/
noncomputable def zetaArgS (T : ℝ) : ℝ :=
  ((∫ y in (0 : ℝ)..T, (deriv riemannZeta (2 + y * I) / riemannZeta (2 + y * I)).re) -
    ∫ x in (1 / 2 : ℝ)..2, (deriv riemannZeta (x + T * I) / riemannZeta (x + T * I)).im) / π

/-- `ξ` has no real zeros: `ζ(σ) < 0` for `0 < σ < 1`. -/
lemma zetaRealZeroCount_eq_zero : zetaRealZeroCount = 0 := by
  classical
  rw [zetaRealZeroCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro ρ _ hρ
  have h := riemannXi_zero_mem ρ
  have hre : ρ.val = (ρ.val.re : ℂ) := by
    apply Complex.ext <;> simp [hρ]
  have hneg := (NTKB.Apostol.riemannZeta_neg_of_lt_one h.2.1 h.2.2).2
  rw [← hre, h.1] at hneg
  simp at hneg

/-- The archimedean part of `ξ'/ξ`: `1/(s - 1) - ½ log π + ½ ψ(s/2 + 1)`. -/
noncomputable def xiGammaPart (s : ℂ) : ℂ :=
  1 / (s - 1) - Complex.log π / 2 + Complex.digamma (s / 2 + 1) / 2

/-- Its primitive `log(-i(s - 1)) - ½ s log π + log Γ(s/2 + 1)`. -/
noncomputable def xiGammaPrim (s : ℂ) : ℂ :=
  Complex.log (-I * (s - 1)) - Complex.log π / 2 * s + Port.logGamma (s / 2 + 1)

set_option maxHeartbeats 1000000 in
lemma hasDerivAt_xiGammaPrim {s : ℂ} (h1 : -I * (s - 1) ∈ slitPlane) (h2 : s / 2 + 1 ∈ slitPlane) :
    HasDerivAt xiGammaPrim (xiGammaPart s) s := by
  have ha : HasDerivAt (fun s : ℂ ↦ Complex.log (-I * (s - 1))) ((-I * (s - 1))⁻¹ * (-I * 1)) s := by
    have h0 : HasDerivAt (fun s : ℂ ↦ -I * (s - 1)) (-I * 1) s :=
      ((hasDerivAt_id s).sub_const 1).const_mul (-I)
    exact (Complex.hasDerivAt_log h1).comp s h0
  have hb : HasDerivAt (fun s : ℂ ↦ Complex.log π / 2 * s) (Complex.log π / 2 * 1) s :=
    (hasDerivAt_id s).const_mul _
  have hc : HasDerivAt (fun s : ℂ ↦ Port.logGamma (s / 2 + 1))
      (Complex.digamma (s / 2 + 1) * (1 / 2)) s := by
    have h0 : HasDerivAt (fun s : ℂ ↦ s / 2 + 1) (1 / 2) s :=
      ((hasDerivAt_id s).div_const 2).add_const 1
    exact (Port.hasDerivAt_logGamma h2).comp s h0
  have hI : -I ≠ 0 := neg_ne_zero.mpr I_ne_zero
  have e : (-I * (s - 1))⁻¹ * (-I * 1) = 1 / (s - 1) := by
    rw [mul_inv, mul_one, mul_comm, ← mul_assoc, mul_inv_cancel₀ hI, one_mul, one_div]
  have hfun : xiGammaPrim = fun s : ℂ ↦
      Complex.log (-I * (s - 1)) - Complex.log π / 2 * s + Port.logGamma (s / 2 + 1) := rfl
  have h := (ha.sub hb).add hc
  have hv : (-I * (s - 1))⁻¹ * (-I * 1) - Complex.log π / 2 * 1 +
      Complex.digamma (s / 2 + 1) * (1 / 2) = xiGammaPart s := by
    rw [e, xiGammaPart, mul_one, mul_one_div]
  rw [hv] at h
  rw [hfun]
  exact h


set_option maxHeartbeats 1000000 in
/-- `ξ'/ξ = ζ'/ζ + (archimedean part)` where `ζ ≠ 0`. -/
lemma logDeriv_riemannXi_eq_add {s : ℂ} (hs1 : s ≠ 1) (hre : 0 < s.re) (hz : riemannZeta s ≠ 0) :
    logDeriv riemannXi s = deriv riemannZeta s / riemannZeta s + xiGammaPart s := by
  have hΓ : ∀ m : ℕ, s / 2 + 1 ≠ -m := fun m h ↦ by
    have := congrArg Complex.re h
    simp at this
    linarith [m.cast_nonneg (α := ℝ)]
  rw [logDeriv_riemannZeta_eq_xi hs1 hΓ hz, xiGammaPart]
  ring

lemma continuousOn_digamma_slitPlane : ContinuousOn Complex.digamma slitPlane := by
  have h := (Port.differentiableOn_logGamma.analyticOnNhd isOpen_slitPlane).deriv
  exact h.continuousOn.congr fun z hz ↦ (Port.deriv_logGamma hz).symm

lemma half_add_one_mem_slitPlane {s : ℂ} (hs : 0 < s.re) : s / 2 + 1 ∈ slitPlane := by
  rw [mem_slitPlane_iff]; left; simp; linarith

lemma continuousAt_xiGammaPart {s : ℂ} (hs1 : s ≠ 1) (hs : 0 < s.re) :
    ContinuousAt xiGammaPart s := by
  have h1 : ContinuousAt (fun s : ℂ ↦ 1 / (s - 1)) s := by
    fun_prop (disch := exact sub_ne_zero.mpr hs1)
  have h2 : ContinuousAt (fun s : ℂ ↦ Complex.digamma (s / 2 + 1)) s := by
    have hc := continuousOn_digamma_slitPlane.continuousAt
      (isOpen_slitPlane.mem_nhds (half_add_one_mem_slitPlane hs))
    have hl : ContinuousAt (fun s : ℂ ↦ s / 2 + 1) s := by fun_prop
    exact ContinuousAt.comp (g := Complex.digamma) hc hl
  show ContinuousAt (fun s : ℂ ↦
    1 / (s - 1) - Complex.log π / 2 + Complex.digamma (s / 2 + 1) / 2) s
  exact (h1.sub continuousAt_const).add (h2.div_const 2)

/-- `∫_a^b Im g = Im (f b - f a)` for a primitive `f` of a continuous `g`. -/
lemma integral_im_eq_of_hasDerivAt {f g : ℝ → ℂ} {a b : ℝ}
    (hf : ∀ y ∈ [[a, b]], HasDerivAt f (g y) y) (hg : ContinuousOn g [[a, b]]) :
    ∫ y in a..b, (g y).im = (f b - f a).im := by
  rw [← intervalIntegral.integral_eq_sub_of_hasDerivAt hf hg.intervalIntegrable]
  exact (Complex.imCLM.intervalIntegral_comp_comm hg.intervalIntegrable)

set_option maxHeartbeats 1000000 in
/-- The vertical side: `∫_0^T Re P(2 + iy) dy = Im (G(2 + iT) - G(2))`. -/
lemma integral_re_xiGammaPart_vert {T : ℝ} (hT : 0 ≤ T) :
    ∫ y in (0 : ℝ)..T, (xiGammaPart (2 + y * I)).re =
      (xiGammaPrim (2 + T * I) - xiGammaPrim 2).im := by
  have hmem1 : ∀ y : ℝ, -I * ((2 + y * I) - 1) ∈ slitPlane := fun y ↦ by
    rw [mem_slitPlane_iff]; right; norm_num
  have hmem2 : ∀ y : ℝ, (2 + y * I) / 2 + 1 ∈ slitPlane := fun y ↦
    half_add_one_mem_slitPlane (by simp)
  have hne : ∀ y : ℝ, (2 : ℂ) + y * I ≠ 1 := fun y h ↦ by
    have := congrArg Complex.re h; simp at this
  have hd : ∀ y ∈ [[(0 : ℝ), T]], HasDerivAt (fun y : ℝ ↦ xiGammaPrim (2 + y * I))
      (xiGammaPart (2 + y * I) * I) y := fun y _ ↦ by
    have hp : HasDerivAt (fun y : ℝ ↦ (2 : ℂ) + y * I) I y := by
      simpa using ((hasDerivAt_id (y : ℝ)).ofReal_comp.mul_const I).const_add (2 : ℂ)
    exact (hasDerivAt_xiGammaPrim (hmem1 y) (hmem2 y)).comp y hp
  have hc : ContinuousOn (fun y : ℝ ↦ xiGammaPart (2 + y * I) * I) [[(0 : ℝ), T]] := by
    refine Continuous.continuousOn (continuous_iff_continuousAt.mpr fun y ↦ ?_)
    refine ContinuousAt.mul ?_ continuousAt_const
    exact ContinuousAt.comp (g := xiGammaPart) (continuousAt_xiGammaPart (hne y) (by simp))
      (by fun_prop : ContinuousAt (fun y : ℝ ↦ (2 : ℂ) + y * I) y)
  have := integral_im_eq_of_hasDerivAt hd hc
  simp only [mul_I_im] at this
  simpa using this

set_option maxHeartbeats 1000000 in
/-- The horizontal side: `∫_{1/2}^2 Im P(x + iT) dx = Im (G(2 + iT) - G(1/2 + iT))`. -/
lemma integral_im_xiGammaPart_horiz {T : ℝ} (hT : 0 < T) :
    ∫ x in (1 / 2 : ℝ)..2, (xiGammaPart (x + T * I)).im =
      (xiGammaPrim (2 + T * I) - xiGammaPrim (1 / 2 + T * I)).im := by
  have hmem1 : ∀ x : ℝ, -I * ((x + T * I) - 1) ∈ slitPlane := fun x ↦ by
    rw [mem_slitPlane_iff]; left; simp [hT]
  have hne : ∀ x : ℝ, (x : ℂ) + T * I ≠ 1 := fun x h ↦ by
    have := congrArg Complex.im h; simp at this; linarith
  have hd : ∀ x ∈ [[(1 / 2 : ℝ), 2]], HasDerivAt (fun x : ℝ ↦ xiGammaPrim (x + T * I))
      (xiGammaPart (x + T * I)) x := fun x hx ↦ by
    have hx0 : 0 < x := by
      rw [uIcc_of_le (by norm_num)] at hx; linarith [hx.1]
    have hp : HasDerivAt (fun x : ℝ ↦ (x : ℂ) + T * I) 1 x := by
      simpa using (hasDerivAt_id (x : ℝ)).ofReal_comp.add_const ((T : ℂ) * I)
    have := (hasDerivAt_xiGammaPrim (hmem1 x) (half_add_one_mem_slitPlane (by simpa))).comp x hp
    rw [mul_one] at this
    exact this
  have hc : ContinuousOn (fun x : ℝ ↦ xiGammaPart (x + T * I)) [[(1 / 2 : ℝ), 2]] := by
    intro x hx
    have hx0 : 0 < x := by
      rw [uIcc_of_le (by norm_num)] at hx; linarith [hx.1]
    exact (ContinuousAt.comp (g := xiGammaPart) (f := fun x : ℝ ↦ (x : ℂ) + T * I) (x := x)
      (continuousAt_xiGammaPart (hne x) (by simpa))
      (by fun_prop : ContinuousAt (fun x : ℝ ↦ (x : ℂ) + T * I) x)).continuousWithinAt
  have := integral_im_eq_of_hasDerivAt hd hc
  simpa using this

/-- `arg w = arctan(Im w / Re w)` for `Re w > 0`. -/
lemma arg_eq_arctan_of_re_pos {w : ℂ} (hw : 0 < w.re) : w.arg = Real.arctan (w.im / w.re) := by
  have h := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hw)
  rw [abs_lt] at h
  rw [← Complex.tan_arg, Real.arctan_tan h.1 h.2]

/-- `Im G(2) = -π/2`. -/
lemma xiGammaPrim_two_im : (xiGammaPrim 2).im = -(π / 2) := by
  have h2 : Port.logGamma ((2 : ℂ) / 2 + 1) = 0 := by
    have : (2 : ℂ) / 2 + 1 = ((2 : ℝ) : ℂ) := by norm_num
    rw [this, Port.logGamma_ofReal two_pos]
    simp
  have hl : Complex.log π = ((Real.log π : ℝ) : ℂ) := (Complex.ofReal_log Real.pi_pos.le).symm
  simp only [xiGammaPrim, h2, hl]
  have : -I * ((2 : ℂ) - 1) = -I := by ring
  simp only [this, add_zero, sub_im, Complex.log_im, Complex.arg_neg_I]
  simp

/-- `Im G(1/2 + iT) = arctan(1/(2T)) - (T/2) log π + Im log Γ(5/4 + iT/2)`. -/
lemma xiGammaPrim_half_im {T : ℝ} (hT : 0 < T) :
    (xiGammaPrim (1 / 2 + T * I)).im =
      Real.arctan (1 / (2 * T)) - T / 2 * Real.log π +
        (Port.logGamma ((5 / 4 : ℝ) + (T / 2 : ℝ) * I)).im := by
  have hl : Complex.log π = ((Real.log π : ℝ) : ℂ) := (Complex.ofReal_log Real.pi_pos.le).symm
  have e1 : -I * ((1 / 2 : ℂ) + T * I - 1) = (T : ℂ) + (1 / 2 : ℝ) * I := by
    push_cast; ring_nf; rw [I_sq]; ring
  have e2 : ((1 / 2 : ℂ) + T * I) / 2 + 1 = (5 / 4 : ℝ) + (T / 2 : ℝ) * I := by
    push_cast; ring
  simp only [xiGammaPrim, e1, e2, hl, sub_im, add_im, Complex.log_im]
  rw [arg_eq_arctan_of_re_pos (by simpa using hT)]
  simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_zero,
    add_im, mul_im, zero_add, div_ofNat_im, div_ofNat_re]
  ring_nf
  simp

/-- **Stirling's formula** at `z = 5/4 + iT/2`:
`|Im log Γ(z) - ((T/2) log|z| + (3/4) arg z - T/2)| ≤ 4/T`. -/
lemma abs_im_logGamma_sub_le {T : ℝ} (hT : 0 < T) :
    |(Port.logGamma ((5 / 4 : ℝ) + (T / 2 : ℝ) * I)).im -
      (T / 2 * Real.log ‖((5 / 4 : ℝ) + (T / 2 : ℝ) * I : ℂ)‖ +
        3 / 4 * Complex.arg ((5 / 4 : ℝ) + (T / 2 : ℝ) * I) - T / 2)| ≤ 4 / T := by
  set z : ℂ := (5 / 4 : ℝ) + (T / 2 : ℝ) * I with hz
  have hzre : z.re = 5 / 4 := by simp [z]
  have hzim : z.im = T / 2 := by simp [z]
  have hz0 : z ≠ 0 := fun h ↦ by rw [h, zero_re] at hzre; norm_num at hzre
  have harg : |z.arg| ≤ π - π / 2 := by
    have := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl (by rw [hzre]; norm_num : 0 < z.re))
    linarith
  have hS := Port.norm_logGamma_sub_stirling_le (s := z) (δ := π / 2) (by positivity)
    (by linarith [Real.pi_pos]) harg hz0
  rw [Real.cos_pi_div_two, sub_zero, one_pow, one_mul] at hS
  have hnorm : T / 2 ≤ ‖z‖ := by
    have := Complex.abs_im_le_norm z
    rw [hzim, abs_of_pos (by positivity)] at this
    exact this
  have hS' : ‖Port.logGamma z - ((z - 1 / 2) * Complex.log z - z + (Real.log (2 * π) / 2 : ℝ))‖ ≤
      4 / T := by
    refine hS.trans ?_
    rw [div_le_div_iff₀ (by linarith) hT]
    nlinarith
  have him := (Complex.abs_im_le_norm _).trans hS'
  have hmain : ((z - 1 / 2) * Complex.log z - z + (Real.log (2 * π) / 2 : ℝ)).im =
      T / 2 * Real.log ‖z‖ + 3 / 4 * z.arg - T / 2 := by
    simp only [add_im, sub_im, mul_im, Complex.log_re, Complex.log_im, ofReal_im, sub_re,
      hzre, hzim]
    norm_num
    ring
  rw [sub_im, hmain] at him
  exact him

set_option maxHeartbeats 2000000 in
/-- **Davenport, Ch. 15, p. 98, (1) (row 15-3)**, the Riemann-von Mangoldt formula: for `T > 0` not
the ordinate of a zero of `ζ`,
`|N(T) - ((T/2π) log(T/2π) - T/2π + 7/8 + S(T))| ≤ 3/T`. -/
@[kb "davenport1980" "Ch 15, p. 98"]
theorem Davenport.riemann_von_mangoldt {T : ℝ} (hT : 0 < T)
    (hTz : ∀ ρ : ZeroIndex riemannXi, |ρ.val.im| ≠ T) :
    |(zetaZeroCount T : ℝ) -
      (T / (2 * π) * Real.log (T / (2 * π)) - T / (2 * π) + 7 / 8 + zetaArgS T)| ≤ 3 / T := by
  have hπ := Real.pi_pos
  have hπ3 := Real.pi_gt_three
  -- `πN(T)` as the change of argument of `ξ`
  have h0 := Davenport.pi_mul_zetaZeroCount_eq hT hTz
  rw [zetaRealZeroCount_eq_zero, Nat.cast_zero, mul_zero, zero_div, sub_zero] at h0
  -- split off the archimedean part on both sides
  have hv : ∫ y in (0 : ℝ)..T, (deriv riemannZeta (2 + y * I) / riemannZeta (2 + y * I)).re =
      (∫ y in (0 : ℝ)..T, (logDeriv riemannXi (2 + y * I)).re) -
        ∫ y in (0 : ℝ)..T, (xiGammaPart (2 + y * I)).re := by
    rw [← intervalIntegral.integral_sub]
    · refine intervalIntegral.integral_congr fun y _ ↦ ?_
      have hre : 1 < ((2 : ℂ) + y * I).re := by simp
      have hne : (2 : ℂ) + y * I ≠ 1 := fun h ↦ by rw [h] at hre; simp at hre
      rw [logDeriv_riemannXi_eq_add hne (by linarith) (riemannZeta_ne_zero_of_one_lt_re hre),
        add_re]
      ring
    · exact (Complex.continuous_re.comp continuous_logDeriv_riemannXi_two).intervalIntegrable _ _
    · refine (Continuous.intervalIntegrable ?_ _ _)
      refine Complex.continuous_re.comp (continuous_iff_continuousAt.mpr fun y ↦ ?_)
      have hne : (2 : ℂ) + y * I ≠ 1 := fun h ↦ by
        have := congrArg Complex.re h; simp at this
      exact ContinuousAt.comp (g := xiGammaPart) (continuousAt_xiGammaPart hne (by simp))
        (by fun_prop : ContinuousAt (fun y : ℝ ↦ (2 : ℂ) + y * I) y)
  have hcT := continuous_logDeriv_riemannXi_horiz hTz T (abs_of_pos hT)
  have hh : ∫ x in (1 / 2 : ℝ)..2, (deriv riemannZeta (x + T * I) / riemannZeta (x + T * I)).im =
      (∫ x in (1 / 2 : ℝ)..2, (logDeriv riemannXi (x + T * I)).im) -
        ∫ x in (1 / 2 : ℝ)..2, (xiGammaPart (x + T * I)).im := by
    rw [← intervalIntegral.integral_sub]
    · refine intervalIntegral.integral_congr fun x hx ↦ ?_
      have hx0 : 0 < x := by
        rw [uIcc_of_le (by norm_num)] at hx; linarith [hx.1]
      have hne : (x : ℂ) + T * I ≠ 1 := fun h ↦ by
        have := congrArg Complex.im h; simp at this; linarith
      have hxi : riemannXi (x + T * I) ≠ 0 :=
        riemannXi_ne_zero_of_abs_im hTz (by simp [abs_of_pos hT])
      have hz := riemannZeta_ne_zero_of_riemannXi_ne_zero hxi hne (by simpa)
      rw [logDeriv_riemannXi_eq_add hne (by simpa) hz, add_im]
      ring
    · exact (Complex.continuous_im.comp hcT).intervalIntegrable _ _
    · refine ContinuousOn.intervalIntegrable fun x hx ↦ ?_
      have hx0 : 0 < x := by
        rw [uIcc_of_le (by norm_num)] at hx; linarith [hx.1]
      have hne : (x : ℂ) + T * I ≠ 1 := fun h ↦ by
        have := congrArg Complex.im h; simp at this; linarith
      have h1 : ContinuousAt (fun x : ℝ ↦ xiGammaPart (x + T * I)) x :=
        ContinuousAt.comp (g := xiGammaPart) (continuousAt_xiGammaPart hne (by simpa))
          (by fun_prop : ContinuousAt (fun x : ℝ ↦ (x : ℂ) + T * I) x)
      exact (Complex.continuous_im.continuousAt.comp h1).continuousWithinAt
  have hS : π * zetaArgS T = π * zetaZeroCount T -
      ((xiGammaPrim (1 / 2 + T * I)).im - (xiGammaPrim 2).im) := by
    rw [zetaArgS, mul_div_cancel₀ _ hπ.ne', hv, hh, integral_re_xiGammaPart_vert hT.le,
      integral_im_xiGammaPart_horiz hT, h0, sub_im, sub_im]
    ring
  rw [xiGammaPrim_two_im, xiGammaPrim_half_im hT] at hS
  -- Stirling
  have hst := abs_im_logGamma_sub_le hT
  set z : ℂ := (5 / 4 : ℝ) + (T / 2 : ℝ) * I with hz
  set E := (Port.logGamma z).im - (T / 2 * Real.log ‖z‖ + 3 / 4 * z.arg - T / 2) with hE
  -- `arg z = π/2 - arctan(5/(2T))`
  have harg : z.arg = π / 2 - Real.arctan (5 / (2 * T)) := by
    rw [arg_eq_arctan_of_re_pos (by simp [z]), ← Real.arctan_inv_of_pos (by positivity)]
    congr 1
    simp [z]
    field_simp
    ring
  -- `0 ≤ log|z| - log(T/2) ≤ 25/(8T²)`
  have hT2 : 0 < T / 2 := by linarith
  have hnz : ‖z‖ ^ 2 = 25 / 16 + (T / 2) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp [z]
    ring
  have hz0 : 0 ≤ ‖z‖ := norm_nonneg _
  have hzT : T / 2 ≤ ‖z‖ := by nlinarith
  have hzT' : ‖z‖ - T / 2 ≤ 25 / (16 * T) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have hlog1 : 0 ≤ Real.log ‖z‖ - Real.log (T / 2) := by
    have := Real.log_le_log hT2 hzT; linarith
  have hlog2 : Real.log ‖z‖ - Real.log (T / 2) ≤ 25 / (8 * T ^ 2) := by
    rw [← Real.log_div (by linarith) hT2.ne']
    refine (Real.log_le_sub_one_of_pos (div_pos (by linarith) hT2)).trans ?_
    rw [div_sub_one hT2.ne', div_le_iff₀ hT2]
    calc ‖z‖ - T / 2 ≤ 25 / (16 * T) := hzT'
      _ = 25 / (8 * T ^ 2) * (T / 2) := by field_simp; ring
  -- the two arctangents
  have ha1 : 0 ≤ Real.arctan (1 / (2 * T)) ∧ Real.arctan (1 / (2 * T)) ≤ 1 / (2 * T) :=
    ⟨Real.arctan_nonneg.mpr (by positivity), Real.arctan_le_self (by positivity)⟩
  have ha2 : 0 ≤ Real.arctan (5 / (2 * T)) ∧ Real.arctan (5 / (2 * T)) ≤ 5 / (2 * T) :=
    ⟨Real.arctan_nonneg.mpr (by positivity), Real.arctan_le_self (by positivity)⟩
  -- assemble
  have hmain : T / (2 * π) * Real.log (T / (2 * π)) =
      (T / 2 * (Real.log (T / 2) - Real.log π)) / π := by
    rw [show T / (2 * π) = (T / 2) / π by ring, Real.log_div hT2.ne' hπ.ne']
    ring
  set D := Real.arctan (1 / (2 * T)) - 3 / 4 * Real.arctan (5 / (2 * T)) +
    T / 2 * (Real.log ‖z‖ - Real.log (T / 2)) + E with hD
  have hkey : (zetaZeroCount T : ℝ) -
      (T / (2 * π) * Real.log (T / (2 * π)) - T / (2 * π) + 7 / 8 + zetaArgS T) = D / π := by
    rw [hmain, eq_div_iff hπ.ne']
    have hS' : zetaArgS T * π = π * zetaArgS T := mul_comm _ _
    have : (zetaZeroCount T : ℝ) * π = π * zetaZeroCount T := mul_comm _ _
    rw [sub_mul, add_mul, add_mul, sub_mul, hS', this, hS, hD, hE, harg]
    field_simp
    ring
  rw [hkey, abs_div, abs_of_pos hπ, div_le_div_iff₀ hπ hT]
  have hEb : |E| ≤ 4 / T := hst
  have hD1 : |D| ≤ 1 / (2 * T) + 3 / 4 * (5 / (2 * T)) + T / 2 * (25 / (8 * T ^ 2)) + 4 / T := by
    rw [hD]
    refine (abs_add_le _ _).trans (add_le_add ?_ hEb)
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · refine (abs_sub _ _).trans (add_le_add ?_ ?_)
      · rw [abs_of_nonneg ha1.1]; exact ha1.2
      · rw [abs_of_nonneg (by linarith [ha2.1])]; linarith [ha2.2]
    · rw [abs_of_nonneg (mul_nonneg hT2.le hlog1)]
      exact mul_le_mul_of_nonneg_left hlog2 hT2.le
  have hD2 : 1 / (2 * T) + 3 / 4 * (5 / (2 * T)) + T / 2 * (25 / (8 * T ^ 2)) + 4 / T =
      127 / 16 / T := by
    field_simp; ring
  rw [hD2] at hD1
  have : |D| * T ≤ 127 / 16 := by rwa [le_div_iff₀ hT] at hD1
  nlinarith

/-- **Davenport, Ch. 15, p. 98 (row 15-5)**: `S(T) = O(log T)`; for `T ≥ 3` not an ordinate,
`|S(T)| ≤ A log T`. -/
@[kb "davenport1980" "Ch 15, p. 98"]
theorem Davenport.abs_zetaArgS_le :
    ∃ A : ℝ, 0 < A ∧ ∀ T : ℝ, 3 ≤ T → (∀ ρ : ZeroIndex riemannXi, |ρ.val.im| ≠ T) →
      |zetaArgS T| ≤ A * Real.log T := by
  obtain ⟨A, hA, h⟩ := Davenport.zetaZeroCount_sub_le
  refine ⟨A + 2, by positivity, fun T hT hTz ↦ ?_⟩
  have hlog : 1 ≤ Real.log T := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9; linarith
  have h1 := h T hT
  have h2 := Davenport.riemann_von_mangoldt (by linarith) hTz
  have h3 : 3 / T ≤ 1 := by rw [div_le_one (by linarith)]; exact hT
  rw [abs_le] at h1 h2 ⊢
  constructor <;> nlinarith

end NTKB
