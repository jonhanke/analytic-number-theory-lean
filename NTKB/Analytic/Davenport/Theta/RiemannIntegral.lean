/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Attr
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# Riemann's integral for the completed zeta function

**Davenport, Multiplicative Number Theory, Ch. 8, (8), p. 62.**

With `ω(x) = ∑_{n ≥ 1} e^{-π n² x}` Riemann's formula reads
`π^{-s/2} Γ(s/2) ζ(s) = 1/(s(s-1)) + ∫_1^∞ (x^{s/2-1} + x^{-s/2-1/2}) ω(x) dx`.

Route: Mathlib realises `completedRiemannZeta₀` as the Mellin transform (at `s/2`, divided by `2`)
of the modified kernel `f_modif` of the weak FE-pair `hurwitzEvenFEPair 0`, whose kernel is
`1 + 2 ω(x)`.  We write `f_modif x = G x + x^{-1/2} G (1/x)` with `G = 2 ω · 1_{(1,∞)}`, so that
the Mellin transform splits as `mellin G z + mellin G (1/2 - z)` (by `mellin_comp_inv`), and
`mellin G w` is the integral over `(1, ∞)`.
-/

open Complex MeasureTheory Set HurwitzZeta

noncomputable section

namespace NTKB.Davenport

/-- `ω(x) = ∑_{n ≥ 1} e^{-π n² x}`. -/
def riemannOmega (x : ℝ) : ℝ := ∑' n : ℕ, Real.exp (-Real.pi * ((n : ℝ) + 1) ^ 2 * x)

lemma cosKernel_zero_eq {x : ℝ} (hx : 0 < x) : cosKernel 0 x = 1 + 2 * riemannOmega x := by
  have h := hasSum_nat_cosKernel₀ 0 hx
  simp only [mul_zero, zero_mul, Real.cos_zero, mul_one] at h
  have h0 : cosKernel ((0 : ℝ) : UnitAddCircle) x = cosKernel 0 x := by simp
  rw [h0] at h
  have h2 := h.tsum_eq
  rw [tsum_mul_left] at h2
  unfold riemannOmega
  linarith

/-- The piece `2 ω · 1_{(1,∞)}`. -/
def omegaInd : ℝ → ℂ := (Ioi (1 : ℝ)).indicator (fun x => ((2 * riemannOmega x : ℝ) : ℂ))

lemma fmodif_eq {x : ℝ} (hx : 0 < x) :
    (hurwitzEvenFEPair 0).f_modif x = omegaInd x + ((x ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * omegaInd x⁻¹ := by
  rcases lt_trichotomy x 1 with h | rfl | h
  · have h1 : 1 < x⁻¹ := one_lt_inv₀ hx |>.mpr h
    have h2 : ¬ (1 < x) := not_lt.mpr h.le
    rw [WeakFEPair.f_modif, Pi.add_apply, indicator_of_notMem (notMem_Ioi.mpr h.le),
      indicator_of_mem (mem_Ioo.mpr ⟨hx, h⟩)]
    simp only [omegaInd, indicator_of_notMem (notMem_Ioi.mpr h.le), indicator_of_mem (mem_Ioi.mpr h1),
      zero_add]
    have hf := evenKernel_functional_equation (0 : UnitAddCircle) x
    rw [evenKernel_eq_cosKernel_of_zero] at hf
    have hc := cosKernel_zero_eq (inv_pos.mpr hx)
    simp only [hurwitzEvenFEPair]
    simp only [Function.comp_apply, one_mul]
    rw [evenKernel_eq_cosKernel_of_zero, smul_eq_mul, mul_one, hf, one_div x, hc, one_div (x ^ (1 / 2 : ℝ)), Real.rpow_neg hx.le]
    push_cast
    ring
  · simp [WeakFEPair.f_modif, omegaInd]
  · have h1 : x⁻¹ < 1 := inv_lt_one_of_one_lt₀ h
    rw [WeakFEPair.f_modif, Pi.add_apply, indicator_of_mem (mem_Ioi.mpr h),
      indicator_of_notMem (notMem_Ioo_of_ge h.le)]
    simp only [omegaInd, indicator_of_mem (mem_Ioi.mpr h),
      indicator_of_notMem (notMem_Ioi.mpr h1.le)]
    have hc := cosKernel_zero_eq hx
    simp only [hurwitzEvenFEPair, Function.comp_apply, add_zero, mul_zero]
    rw [evenKernel_eq_cosKernel_of_zero, hc]
    push_cast
    simp

lemma fmodif_eq' {x : ℝ} (hx : 0 < x) :
    (hurwitzEvenFEPair 0).f_modif x = omegaInd x + (x : ℂ) ^ (-(1 / 2 : ℂ)) * omegaInd x⁻¹ := by
  rw [fmodif_eq hx, Complex.ofReal_cpow hx.le]
  push_cast
  rfl

lemma mellin_omegaInd (w : ℂ) :
    mellin omegaInd w = ∫ x in Ioi (1 : ℝ), (x : ℂ) ^ (w - 1) * ((2 * riemannOmega x : ℝ) : ℂ) := by
  have key : ∀ t : ℝ, (t : ℂ) ^ (w - 1) • omegaInd t =
      (Ioi (1 : ℝ)).indicator (fun x : ℝ => (x : ℂ) ^ (w - 1) * ((2 * riemannOmega x : ℝ) : ℂ)) t := by
    intro t
    by_cases ht : t ∈ Ioi (1 : ℝ) <;> simp [omegaInd, ht]
  unfold mellin
  simp_rw [key]
  rw [setIntegral_indicator measurableSet_Ioi, Ioi_inter_Ioi]
  simp

lemma integrableOn_omega (w : ℂ) :
    IntegrableOn (fun x : ℝ => (x : ℂ) ^ (w - 1) * ((2 * riemannOmega x : ℝ) : ℂ)) (Ioi (1 : ℝ)) := by
  have hF : MellinConvergent (hurwitzEvenFEPair 0).f_modif w :=
    ((WeakFEPair.isStrongFEPair_toStrongFEPair (P := hurwitzEvenFEPair 0)).hasMellin w).1
  have h1 := hF.mono_set (Ioi_subset_Ioi (zero_le_one : (0 : ℝ) ≤ 1))
  refine h1.congr_fun (fun t ht => ?_) measurableSet_Ioi
  have ht0 : 0 < t := lt_trans zero_lt_one ht
  have ht1 : t⁻¹ < 1 := inv_lt_one_of_one_lt₀ ht
  have : (hurwitzEvenFEPair 0).f_modif t = omegaInd t := by
    rw [fmodif_eq' ht0]
    simp [omegaInd, indicator_of_notMem (notMem_Ioi.mpr ht1.le)]
  beta_reduce
  rw [this, smul_eq_mul]
  simp [omegaInd, ht]

lemma mellinConvergent_omegaInd (w : ℂ) : MellinConvergent omegaInd w := by
  have key : ∀ t : ℝ, (t : ℂ) ^ (w - 1) • omegaInd t =
      (Ioi (1 : ℝ)).indicator (fun x : ℝ => (x : ℂ) ^ (w - 1) * ((2 * riemannOmega x : ℝ) : ℂ)) t := by
    intro t
    by_cases ht : t ∈ Ioi (1 : ℝ) <;> simp [omegaInd, ht]
  unfold MellinConvergent
  simp_rw [key]
  exact ((integrableOn_omega w).integrable_indicator measurableSet_Ioi).integrableOn

lemma mellin_fmodif (z : ℂ) :
    mellin (hurwitzEvenFEPair 0).f_modif z = mellin omegaInd z + mellin omegaInd (1 / 2 - z) := by
  have hF : MellinConvergent (hurwitzEvenFEPair 0).f_modif z :=
    ((WeakFEPair.isStrongFEPair_toStrongFEPair (P := hurwitzEvenFEPair 0)).hasMellin z).1
  have hG := mellinConvergent_omegaInd z
  have hH : mellin (fun t : ℝ => (t : ℂ) ^ (-(1 / 2 : ℂ)) • omegaInd t⁻¹) z =
      mellin omegaInd (1 / 2 - z) := by
    rw [mellin_cpow_smul (fun t : ℝ => omegaInd t⁻¹) z, mellin_comp_inv]
    congr 1
    ring
  rw [← hH]
  have : mellin (hurwitzEvenFEPair 0).f_modif z - mellin omegaInd z =
      mellin (fun t : ℝ => (t : ℂ) ^ (-(1 / 2 : ℂ)) • omegaInd t⁻¹) z := by
    unfold mellin
    rw [← integral_sub hF hG]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    have ht0 : 0 < t := ht
    beta_reduce
    rw [fmodif_eq' ht0, smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul]
    ring
  rw [← this]
  ring

/-- Riemann's integral, entire form: `Λ₀(s) = ∫_1^∞ (x^{s/2-1} + x^{-s/2-1/2}) ω(x) dx` for every `s`,
where `Λ(s) = Λ₀(s) - 1/s - 1/(1-s)` (Mathlib's `completedRiemannZeta₀`). -/
theorem completedRiemannZeta₀_eq_integral (s : ℂ) :
    completedRiemannZeta₀ s =
      ∫ x in Set.Ioi (1 : ℝ), ((x : ℂ) ^ (s / 2 - 1) + (x : ℂ) ^ (-s / 2 - 1 / 2)) *
        (riemannOmega x : ℂ) := by
  show mellin (hurwitzEvenFEPair 0).f_modif (s / 2) / 2 = _
  rw [mellin_fmodif, mellin_omegaInd, mellin_omegaInd, ← integral_add (integrableOn_omega _)
    (integrableOn_omega _), ← integral_div]
  refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
  have e : (1 / 2 - s / 2 - 1 : ℂ) = -s / 2 - 1 / 2 := by ring
  rw [e]
  push_cast
  ring

/-- **Davenport, Ch. 8, (8)** (Riemann): `π^{-s/2} Γ(s/2) ζ(s) = 1/(s(s-1)) + ∫_1^∞ (x^{s/2-1} + x^{-s/2-1/2}) ω(x) dx`;
the right side is defined for all `s ≠ 0, 1`; here `Λ(s) = completedRiemannZeta s`. -/
@[kb "davenport1980" "Ch 8, p. 62"]
theorem completedRiemannZeta_eq_integral {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    completedRiemannZeta s = 1 / (s * (s - 1)) +
      ∫ x in Set.Ioi (1 : ℝ), ((x : ℂ) ^ (s / 2 - 1) + (x : ℂ) ^ (-s / 2 - 1 / 2)) *
        (riemannOmega x : ℂ) := by
  rw [completedRiemannZeta_eq, completedRiemannZeta₀_eq_integral]
  have h1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have h2 : 1 - s ≠ 0 := sub_ne_zero.mpr hs1.symm
  field_simp
  ring

/-- The same with `π^{-s/2} Γ(s/2) ζ(s)` (`Gammaℝ s * riemannZeta s`), where `Γ(s/2)` has no pole. -/
@[kb "davenport1980" "Ch 8, p. 62"]
theorem gammaR_mul_riemannZeta_eq_integral {s : ℂ} (hs1 : s ≠ 1) (hs : ∀ n : ℕ, s ≠ -(2 * n)) :
    Complex.Gammaℝ s * riemannZeta s = 1 / (s * (s - 1)) +
      ∫ x in Set.Ioi (1 : ℝ), ((x : ℂ) ^ (s / 2 - 1) + (x : ℂ) ^ (-s / 2 - 1 / 2)) *
        (riemannOmega x : ℂ) := by
  have hs0 : s ≠ 0 := by simpa using hs 0
  have hG : Complex.Gammaℝ s ≠ 0 := by
    intro h
    obtain ⟨n, hn⟩ := Complex.Gammaℝ_eq_zero_iff.mp h
    exact hs n hn
  rw [riemannZeta_def_of_ne_zero hs0, mul_div_cancel₀ _ hG]
  exact completedRiemannZeta_eq_integral hs0 hs1

end NTKB.Davenport
