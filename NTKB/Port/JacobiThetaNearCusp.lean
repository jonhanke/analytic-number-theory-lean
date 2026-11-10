/-
Copyright (c) 2026 The Tau Ceti contributors. Released under Apache 2.0 license.
Copied into NTKB with credit from Tau Ceti (`TauCeti/NumberTheory/ModularForms/JacobiTheta/OneVariable.lean`,
`norm_jacobiTheta₂_sub_one_le` and `tendsto_jacobiTheta_comap_im_atTop`, and the private
`tendsto_I_div_nhdsGT_zero` of `.../JacobiTheta/GaussSum.lean`, master `686d0d7f`, staged 2026-11-07);
NTKB does not depend on Tau Ceti. Changes: namespace `NTKB.Port`; the corollary
`tendsto_jacobiTheta₂_of_im_eq_zero` added.
-/
import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable

/-!
# The theta functions tend to `1` at `i∞` (port from Tau Ceti)

* `norm_jacobiTheta₂_sub_one_le`: for real `z`, `‖θ₂(z, τ) - 1‖ ≤ ‖θ(i im τ) - 1‖`.
* `tendsto_jacobiTheta_comap_im_atTop`: `θ(τ) → 1` as `im τ → ∞`.
* `tendsto_jacobiTheta₂_of_im_eq_zero`: for real `z`, `θ₂(z, τ) → 1` as `im τ → ∞`.
* `tendsto_I_div_nhdsGT_zero`: `i/(cY) → i∞` as `Y → 0⁺`.
-/

open Complex Filter Topology
open scoped Real

namespace NTKB.Port

/-- For real `z`, the two-variable theta function `θ₂(z, τ)` is at least as close to `1` as
`θ(i im τ)`: its terms have the absolute values `e^{-π n² im τ}` of the terms of `θ(i im τ)`. -/
theorem norm_jacobiTheta₂_sub_one_le {z τ : ℂ} (hz : z.im = 0) (hτ : 0 < τ.im) :
    ‖jacobiTheta₂ z τ - 1‖ ≤ ‖jacobiTheta (I * τ.im) - 1‖ := by
  obtain ⟨b, hb⟩ : ∃ b : ℤ → ℝ, b = fun n : ℤ ↦ Real.exp (-π * (n : ℝ) ^ 2 * τ.im) := ⟨_, rfl⟩
  have hterm (n : ℤ) : jacobiTheta₂_term n 0 (I * τ.im) = b n := by
    rw [hb, jacobiTheta₂_term, ofReal_exp]
    congr 1
    push_cast
    ring_nf
    rw [I_sq]
    ring
  have hnorm (n : ℤ) : ‖jacobiTheta₂_term n z τ‖ = b n := by
    rw [norm_jacobiTheta₂_term, hz, hb]
    ring_nf
  have hsa := (summable_jacobiTheta₂_term_iff z τ).2 hτ
  have hsb : Summable b := by simpa only [hnorm] using hsa.norm
  have hb0 (n : ℤ) : 0 ≤ if n = 0 then 0 else b n := by
    split_ifs
    · exact le_rfl
    · rw [hb]
      exact (Real.exp_pos _).le
  have ha : jacobiTheta₂ z τ - 1 = ∑' n, if n = 0 then 0 else jacobiTheta₂_term n z τ := by
    rw [jacobiTheta₂, hsa.tsum_eq_add_tsum_ite 0, jacobiTheta₂_term]
    simp
  have hb' : jacobiTheta (I * τ.im) - 1 = ((∑' n, if n = 0 then 0 else b n : ℝ) : ℂ) := by
    rw [jacobiTheta_eq_jacobiTheta₂, jacobiTheta₂]
    simp_rw [hterm]
    rw [← ofReal_tsum, hsb.tsum_eq_add_tsum_ite 0, ofReal_add]
    simp [hb]
  have hupd (n : ℤ) :
      ‖if n = 0 then 0 else jacobiTheta₂_term n z τ‖ = if n = 0 then 0 else b n := by
    split_ifs
    · exact norm_zero
    · exact hnorm n
  rw [ha, hb', norm_real, Real.norm_of_nonneg (tsum_nonneg hb0)]
  refine (norm_tsum_le_tsum_norm ?_).trans_eq (tsum_congr hupd)
  simp only [hupd]
  exact (hasSum_ite_sub_hasSum hsb.hasSum 0).summable

/-- The theta function tends to `1` as `im τ → ∞`. -/
theorem tendsto_jacobiTheta_comap_im_atTop :
    Tendsto jacobiTheta (comap im atTop) (𝓝 1) := by
  have h : Tendsto (fun τ : ℂ ↦ rexp (-π * τ.im)) (comap im atTop) (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_comap.const_mul_atTop_of_neg (neg_neg_of_pos Real.pi_pos))
  simpa using (isBigO_at_im_infty_jacobiTheta_sub_one.trans_tendsto h).add_const 1

/-- For real `z`, `θ₂(z, τ) → 1` as `im τ → ∞`. -/
theorem tendsto_jacobiTheta₂_of_im_eq_zero {z : ℂ} (hz : z.im = 0) :
    Tendsto (jacobiTheta₂ z) (comap im atTop) (𝓝 1) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hI : Tendsto (fun τ : ℂ ↦ I * (τ.im : ℂ)) (comap im atTop) (comap im atTop) := by
    refine tendsto_comap_iff.2 ?_
    have : (im ∘ fun τ : ℂ ↦ I * (τ.im : ℂ)) = im := by
      funext τ; simp
    rw [this]
    exact tendsto_comap
  have hlim := tendsto_iff_norm_sub_tendsto_zero.1 (tendsto_jacobiTheta_comap_im_atTop.comp hI)
  refine squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_ hlim
  have hpos : ∀ᶠ τ : ℂ in comap im atTop, 0 < τ.im :=
    (tendsto_comap (f := im) (x := atTop)).eventually (eventually_gt_atTop 0)
  filter_upwards [hpos] with τ hτ
  exact norm_jacobiTheta₂_sub_one_le hz hτ

/-- As `Y → 0⁺`, the point `i / (cY)` tends to `i∞`. -/
theorem tendsto_I_div_nhdsGT_zero (c : ℝ) (hc : 0 < c) :
    Tendsto (fun Y : ℝ ↦ I / (c * Y)) (𝓝[>] 0) (comap im atTop) := by
  refine tendsto_comap_iff.2 ?_
  have : (fun Y : ℝ ↦ (I / (c * Y)).im) = fun Y ↦ c⁻¹ * Y⁻¹ := by
    ext Y
    rw [← ofReal_mul, div_ofReal_im, I_im, one_div, mul_inv]
  rw [Function.comp_def, this]
  exact tendsto_inv_nhdsGT_zero.const_mul_atTop (inv_pos.2 hc)

end NTKB.Port
