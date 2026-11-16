/-
Copyright (c) 2026 The Tau Ceti contributors. Released under Apache 2.0 license.
Copied into NTKB with credit from Tau Ceti
(`TauCeti/Analysis/SpecialFunctions/Gamma/Log.lean`, main `1ff53249`); NTKB does not depend on Tau
Ceti. Changes: namespace `NTKB.Port`; the branch is built from Mathlib's
`Complex.exists_continuousOn_eqOn_exp_comp` (continuous branch) instead of Tau Ceti's
`BranchLogRoot`/`ContinuousLog`, and holomorphy of the branch is proved directly (locally
`f w = f z + log (Γ w / Γ z)`); `logGamma_ofReal` is proved via a derivative argument.
Original authors: The Tau Ceti contributors.
-/
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.Complex.BranchLogRoot
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# The normalized holomorphic logarithm of Gamma (port from Tau Ceti)

`NTKB.Port.logGamma` is the holomorphic logarithm of `Complex.Gamma` on the slit plane
`ℂ ∖ (-∞, 0]`, normalized to vanish at `2`. It agrees with the real logarithm of Gamma on the
positive real axis, and its derivative is `Complex.digamma`.
-/

open Complex Set Filter Topology

namespace NTKB.Port

private theorem nonpole_of_mem_slitPlane' {z : ℂ} (hz : z ∈ slitPlane) (n : ℕ) :
    z ≠ -(n : ℂ) := by
  rintro rfl
  have hneg := (Complex.neg_ofReal_mem_slitPlane (x := (n : ℝ))).mp hz
  exact (Nat.cast_nonneg n).not_gt hneg

/-- A continuous logarithm of Gamma on the slit plane is holomorphic there, with derivative
digamma: near `z`, `f w = f z + log (Γ w / Γ z)`. -/
private theorem hasDerivAt_of_exp_eq_Gamma {f : ℂ → ℂ} (hfc : ContinuousOn f slitPlane)
    (hf : ∀ z ∈ slitPlane, Complex.exp (f z) = Complex.Gamma z) {z : ℂ} (hz : z ∈ slitPlane) :
    HasDerivAt f (Complex.digamma z) z := by
  have hpole := nonpole_of_mem_slitPlane' hz
  have hΓd : HasDerivAt Complex.Gamma (deriv Complex.Gamma z) z :=
    (Complex.differentiableAt_Gamma z hpole).hasDerivAt
  have hΓz : Complex.Gamma z ≠ 0 := Complex.Gamma_ne_zero hpole
  let q : ℂ → ℂ := fun w ↦ Complex.Gamma w / Complex.Gamma z
  have hqd : HasDerivAt q (deriv Complex.Gamma z / Complex.Gamma z) z := hΓd.div_const _
  have hq1 : q z = 1 := div_self hΓz
  have hqs : q z ∈ slitPlane := by rw [hq1]; exact one_mem_slitPlane
  have hlogd : HasDerivAt (fun w ↦ Complex.log (q w))
      (deriv Complex.Gamma z / Complex.Gamma z / q z) z := hqd.clog hqs
  rw [hq1, div_one] at hlogd
  have hg : HasDerivAt (fun w ↦ f z + Complex.log (q w))
      (deriv Complex.Gamma z / Complex.Gamma z) z := hlogd.const_add _
  have hfcz : ContinuousAt f z := hfc.continuousAt (isOpen_slitPlane.mem_nhds hz)
  have hhc : ContinuousAt (fun w ↦ f w - f z - Complex.log (q w)) z :=
    (hfcz.sub continuousAt_const).sub hlogd.continuousAt
  have hh0 : f z - f z - Complex.log (q z) = 0 := by rw [hq1]; simp
  have hev1 : ∀ᶠ w in 𝓝 z, f w - f z - Complex.log (q w) ∈ Metric.ball (0 : ℂ) 1 := by
    have := hhc.tendsto
    rw [hh0] at this
    exact this.eventually (Metric.ball_mem_nhds _ one_pos)
  have hev2 : ∀ᶠ w in 𝓝 z, q w ∈ slitPlane :=
    hqd.continuousAt.eventually_mem (by rw [hq1]; exact isOpen_slitPlane.mem_nhds one_mem_slitPlane)
  have hev3 : ∀ᶠ w in 𝓝 z, w ∈ slitPlane := isOpen_slitPlane.mem_nhds hz
  have hEq : f =ᶠ[𝓝 z] fun w ↦ f z + Complex.log (q w) := by
    filter_upwards [hev1, hev2, hev3] with w h1 h2 h3
    have hqw : q w ≠ 0 := slitPlane_ne_zero h2
    have hexp : Complex.exp (f w - f z - Complex.log (q w)) = 1 := by
      rw [Complex.exp_sub, Complex.exp_sub, Complex.exp_log hqw, hf w h3, hf z hz]
      change Complex.Gamma w / Complex.Gamma z / (Complex.Gamma w / Complex.Gamma z) = 1
      exact div_self (div_ne_zero (by rw [← hf w h3]; exact Complex.exp_ne_zero _) hΓz)
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp hexp
    have him : (f w - f z - Complex.log (q w)).im = n * (2 * Real.pi) := by
      rw [hn]; simp
    have hlt : |(f w - f z - Complex.log (q w)).im| < 1 :=
      (Complex.abs_im_le_norm _).trans_lt (by simpa using h1)
    rw [him, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)] at hlt
    have hn0 : n = 0 := by
      by_contra hne
      have h1' : (1 : ℝ) ≤ |(n : ℝ)| := by
        have := Int.one_le_abs hne
        exact_mod_cast this
      nlinarith [Real.pi_gt_three]
    rw [hn0] at hn
    simp only [Int.cast_zero, zero_mul] at hn
    linear_combination hn
  have hfin := hg.congr_of_eventuallyEq hEq
  convert hfin using 1
  rw [Complex.digamma_def, logDeriv_apply]

private theorem exists_normalized_logGamma :
    ∃ L : ℂ → ℂ, (∀ z ∈ slitPlane, HasDerivAt L (Complex.digamma z) z) ∧
      EqOn (Complex.exp ∘ L) Complex.Gamma slitPlane ∧ L 2 = 0 := by
  have hsc : IsSimplyConnected slitPlane := by
    let : ContractibleSpace slitPlane :=
      starConvex_one_slitPlane.contractibleSpace ⟨1, one_mem_slitPlane⟩
    exact SimplyConnectedSpace.ofContractible _
  obtain ⟨f, hfc, he⟩ := Complex.exists_continuousOn_eqOn_exp_comp hsc isOpen_slitPlane
    (g := Complex.Gamma)
    (fun z hz ↦ (Complex.differentiableAt_Gamma z
      (nonpole_of_mem_slitPlane' hz)).continuousAt.continuousWithinAt)
    (by
      rintro ⟨z, hz, hzero⟩
      exact Complex.Gamma_ne_zero (nonpole_of_mem_slitPlane' hz) hzero)
  have hf : ∀ z ∈ slitPlane, Complex.exp (f z) = Complex.Gamma z := fun z hz ↦ he hz
  have htwo : Complex.exp (f 2) = 1 := by
    simpa using hf 2 (ofNat_mem_slitPlane 2)
  refine ⟨fun z ↦ f z - f 2, fun z hz ↦ (hasDerivAt_of_exp_eq_Gamma hfc hf hz).sub_const _,
    fun z hz ↦ ?_, sub_self _⟩
  simpa [Complex.exp_sub, htwo] using hf z hz

/-- The holomorphic logarithm of Gamma on the slit plane, normalized by `logGamma 2 = 0`.
Outside the slit plane its values are unspecified. -/
noncomputable def logGamma : ℂ → ℂ := Classical.choose exists_normalized_logGamma

/-- The derivative of the normalized branch is the digamma function. -/
theorem hasDerivAt_logGamma {z : ℂ} (hz : z ∈ slitPlane) :
    HasDerivAt logGamma (Complex.digamma z) z :=
  (Classical.choose_spec exists_normalized_logGamma).1 z hz

/-- The normalized logarithm of Gamma is holomorphic on the whole slit plane. -/
theorem differentiableOn_logGamma : DifferentiableOn ℂ logGamma slitPlane :=
  fun _ hz ↦ (hasDerivAt_logGamma hz).differentiableAt.differentiableWithinAt

/-- Exponentiating the normalized logarithm recovers Gamma. -/
@[simp]
theorem exp_logGamma {z : ℂ} (hz : z ∈ slitPlane) :
    Complex.exp (logGamma z) = Complex.Gamma z :=
  (Classical.choose_spec exists_normalized_logGamma).2.1 hz

/-- The normalization of the logarithm of Gamma. -/
@[simp]
theorem logGamma_two : logGamma 2 = 0 :=
  (Classical.choose_spec exists_normalized_logGamma).2.2

/-- The derivative of the normalized branch is the digamma function. -/
theorem deriv_logGamma {z : ℂ} (hz : z ∈ slitPlane) :
    deriv logGamma z = Complex.digamma z :=
  (hasDerivAt_logGamma hz).deriv

/-- The real part of any value of the branch is the logarithm of the Gamma norm. -/
theorem logGamma_re {z : ℂ} (hz : z ∈ slitPlane) :
    (logGamma z).re = Real.log ‖Complex.Gamma z‖ := by
  rw [← exp_logGamma hz, Complex.norm_exp, Real.log_exp]

/-- On the positive real axis the holomorphic branch agrees with the real logarithm of Gamma. -/
@[simp]
theorem logGamma_ofReal {x : ℝ} (hx : 0 < x) :
    logGamma x = (Real.log (Real.Gamma x) : ℂ) := by
  let d : ℝ → ℂ := fun t ↦ logGamma t - Complex.log (Complex.Gamma t)
  have hmem {t : ℝ} (ht : 0 < t) : (t : ℂ) ∈ slitPlane := ofReal_mem_slitPlane.mpr ht
  have hGmem {t : ℝ} (ht : 0 < t) : Complex.Gamma (t : ℂ) ∈ slitPlane := by
    rw [Complex.Gamma_ofReal]
    exact ofReal_mem_slitPlane.mpr (Real.Gamma_pos_of_pos ht)
  have hd {t : ℝ} (ht : 0 < t) : HasDerivAt d 0 t := by
    have h1 : HasDerivAt (fun t : ℝ ↦ logGamma (t : ℂ)) (Complex.digamma t) t :=
      (hasDerivAt_logGamma (hmem ht)).comp_ofReal
    have hpole := nonpole_of_mem_slitPlane' (hmem ht)
    have h2 : HasDerivAt (fun t : ℝ ↦ Complex.log (Complex.Gamma (t : ℂ)))
        (deriv Complex.Gamma t / Complex.Gamma t) t :=
      (((Complex.differentiableAt_Gamma _ hpole).hasDerivAt).clog (hGmem ht)).comp_ofReal
    have h := h1.sub h2
    rw [Complex.digamma_def, logDeriv_apply, sub_self] at h
    exact h
  have hconst := isOpen_Ioi.is_const_of_deriv_eq_zero (isPreconnected_Ioi (a := (0 : ℝ)))
    (fun t ht ↦ (hd ht).differentiableAt.differentiableWithinAt)
    (fun t ht ↦ (hd ht).deriv) hx (by norm_num : (2 : ℝ) ∈ Ioi 0)
  have hd2 : d 2 = 0 := by simp [d]
  have : d x = 0 := hconst.trans hd2
  have h3 : logGamma x = Complex.log (Complex.Gamma x) := sub_eq_zero.mp this
  rw [h3, Complex.Gamma_ofReal, ← Complex.ofReal_log (Real.Gamma_pos_of_pos hx).le]

end NTKB.Port
