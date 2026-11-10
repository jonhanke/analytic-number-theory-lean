/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import NTKB.Analytic.Apostol.Zeta.HurwitzIntegral

/-!
# The contour integral representation of `ζ(s, a)` (Apostol, Theorem 12.3)

Apostol (§12.4) takes the loop `C` around the negative real axis made of the lower edge `C₁`
(`z = r e^{-πi}`, `r` from `+∞` to `c`), the circle `C₂` (`z = c e^{iθ}`, `-π ≤ θ ≤ π`, `0 < c < 2π`)
and the upper edge `C₃` (`z = r e^{πi}`, `r` from `c` to `+∞`), and
`I(s, a) = (1/2πi) ∫_C z^{s-1} e^{az}/(1 - e^z) dz`. With his parametrization (`z^s = r^s e^{∓πis}` on
`C₁`, `C₃`) this is
`2πi I(s, a) = 2i sin(πs) ∫_c^∞ r^{s-1} g(-r) dr + i c^s ∫_{-π}^{π} e^{isθ} g(c e^{iθ}) dθ`,
`g(z) = e^{az}/(1 - e^z)`; we take this as the definition (`hankelI a c s`).

Theorem 12.3: for `0 < a ≤ 1`, `I(s, a)` is entire, and `ζ(s, a) = Γ(1 - s) I(s, a)` for `σ > 1`.

Apostol lets `c → 0`, which uses the independence of `I` from `c` (Cauchy's theorem). We apply
Cauchy's theorem for rectangles (`Complex.integral_boundary_rect_eq_zero_of_differentiableOn`) to
`Ψ(L) = e^{sL} g(e^L)` on `[log ε, log c] × [-π, π]`: the image of this rectangle under `exp` is the
keyhole between the circles of radii `ε` and `c`. This gives
`C(c) - C(ε) = 2 sin(πs) ∫_ε^c r^{s-1} g(-r) dr` for the circle integrals `C` (`hankelCircle_sub`).
-/

open Complex Set Filter MeasureTheory intervalIntegral HurwitzZeta
open scoped Real Topology Interval

namespace NTKB.Apostol

/-- `g(z) = e^{az}/(1 - e^z)`. -/
noncomputable def hankelG (a : ℝ) (z : ℂ) : ℂ := cexp (a * z) / (1 - cexp z)

/-- The edge integral `∫_c^∞ r^{s-1} g(-r) dr = ∫_c^∞ r^{s-1} e^{-ar}/(1 - e^{-r}) dr`. -/
noncomputable def hankelEdge (a c : ℝ) (s : ℂ) : ℂ :=
  ∫ r in Ioi c, (r : ℂ) ^ (s - 1) * hankelG a (-r)

/-- The circle integral `c^s ∫_{-π}^{π} e^{isθ} g(c e^{iθ}) dθ`. -/
noncomputable def hankelCircle (a c : ℝ) (s : ℂ) : ℂ :=
  ∫ θ in (-π)..π, (c : ℂ) ^ s * cexp (s * θ * I) * hankelG a (c * cexp (θ * I))

/-- Apostol's contour integral `I(s, a) = (1/2πi) ∫_C z^{s-1} e^{az}/(1 - e^z) dz` over the loop `C`
of radius `c`, written through its parametrization:
`I(s, a) = (sin(πs) ∫_c^∞ r^{s-1} g(-r) dr + (c^s/2) ∫_{-π}^{π} e^{isθ} g(c e^{iθ}) dθ) / π`. -/
noncomputable def hankelI (a c : ℝ) (s : ℂ) : ℂ :=
  (Complex.sin (π * s) * hankelEdge a c s + hankelCircle a c s / 2) / π

/-- `1 - e^z ≠ 0` for `0 < |z| < 2π`. -/
theorem one_sub_exp_ne_zero {z : ℂ} (hz0 : z ≠ 0) (hz : ‖z‖ < 2 * π) : 1 - cexp z ≠ 0 := by
  intro h
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 (sub_eq_zero.1 h).symm
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn; exact hz0 hn
  have : ‖z‖ = |(n : ℝ)| * (2 * π) := by
    rw [hn, norm_mul, norm_intCast, norm_mul, norm_mul, norm_ofNat, Complex.norm_real, norm_I,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    ring
  have h1 : (1 : ℝ) ≤ |(n : ℝ)| := by
    rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hn0
  nlinarith [Real.pi_pos]

/-- `Ψ(L) = e^{sL} g(e^L)`: the integrand `z^{s-1} g(z) dz` in the variable `L = log z`. -/
noncomputable def hankelPsi (a : ℝ) (s L : ℂ) : ℂ := cexp (s * L) * hankelG a (cexp L)

theorem differentiableAt_hankelPsi (a : ℝ) (s : ℂ) {L : ℂ} (hL : 1 - cexp (cexp L) ≠ 0) :
    DifferentiableAt ℂ (hankelPsi a s) L := by
  unfold hankelPsi hankelG
  fun_prop (disch := exact hL)

theorem norm_cexp_ofReal_mul_I (y : ℝ) : ‖cexp (y * I)‖ = 1 := Complex.norm_exp_ofReal_mul_I y

/-- On the circle of radius `c`, the integrand of `hankelCircle` is `Ψ(log c + iθ)`. -/
theorem hankelCircle_eq {a c : ℝ} (hc : 0 < c) (s : ℂ) :
    hankelCircle a c s = ∫ θ in (-π)..π, hankelPsi a s (Real.log c + θ * I) := by
  unfold hankelCircle hankelPsi
  refine integral_congr fun θ _ ↦ ?_
  have hc0 : (c : ℂ) ≠ 0 := ofReal_ne_zero.2 hc.ne'
  have e1 : (c : ℂ) ^ s = cexp (Real.log c * s) := by rw [cpow_def_of_ne_zero hc0, ofReal_log hc.le]
  have e2 : cexp (Real.log c) = c := by rw [← ofReal_exp, Real.exp_log hc]
  rw [e1, Complex.exp_add (Real.log c : ℂ), e2, ← Complex.exp_add]
  congr 2
  ring

theorem one_sub_exp_neg_ne_zero {r : ℝ} (hr : 0 < r) : 1 - cexp (-(r : ℂ)) ≠ 0 := by
  rw [← ofReal_neg, ← ofReal_exp, ← ofReal_one, ← ofReal_sub, ofReal_ne_zero, sub_ne_zero]
  have := Real.exp_lt_exp.2 (neg_neg_of_pos hr)
  rw [Real.exp_zero] at this
  exact this.ne'

/-- The edge integrand `r^{s-1} g(-r)` is continuous at every `r > 0`. -/
theorem continuousAt_edge (a : ℝ) (s : ℂ) {r : ℝ} (hr : 0 < r) :
    ContinuousAt (fun r : ℝ ↦ (r : ℂ) ^ (s - 1) * hankelG a (-r)) r := by
  have h1 : ContinuousAt (fun r : ℝ ↦ (r : ℂ) ^ (s - 1)) r :=
    (continuousAt_cpow_const (ofReal_mem_slitPlane.2 hr)).comp continuous_ofReal.continuousAt
  have h2 : ContinuousAt (fun r : ℝ ↦ hankelG a (-r)) r := by
    unfold hankelG
    have := one_sub_exp_neg_ne_zero hr
    fun_prop (disch := exact this)
  exact h1.mul h2

/-- **Cauchy's theorem on the keyhole**, in the variable `L = log z`:
`C(c) - C(ε) = 2 sin(πs) ∫_ε^c r^{s-1} g(-r) dr` for `0 < ε ≤ c < 2π`. -/
theorem hankelCircle_sub {a ε c : ℝ} (hε : 0 < ε) (hεc : ε ≤ c) (hc : c < 2 * π) (s : ℂ) :
    hankelCircle a c s - hankelCircle a ε s =
      2 * Complex.sin (π * s) * ∫ r in ε..c, (r : ℂ) ^ (s - 1) * hankelG a (-r) := by
  have hc0 : 0 < c := hε.trans_le hεc
  have hlog : Real.log ε ≤ Real.log c := Real.log_le_log hε hεc
  have H : DifferentiableOn ℂ (hankelPsi a s)
      ([[((Real.log ε : ℂ) - π * I).re, ((Real.log c : ℂ) + π * I).re]] ×ℂ
        [[((Real.log ε : ℂ) - π * I).im, ((Real.log c : ℂ) + π * I).im]]) := by
    intro L hL
    refine (differentiableAt_hankelPsi a s ?_).differentiableWithinAt
    rw [mem_reProdIm] at hL
    have hre : L.re ≤ Real.log c := by
      have := hL.1.2
      simp only [sub_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_zero,
        add_re, add_zero] at this
      exact this.trans (max_le hlog le_rfl)
    refine one_sub_exp_ne_zero (Complex.exp_ne_zero L) ?_
    rw [Complex.norm_exp]
    calc Real.exp L.re ≤ Real.exp (Real.log c) := Real.exp_le_exp.2 hre
      _ = c := Real.exp_log hc0
      _ < 2 * π := hc
  have hR := integral_boundary_rect_eq_zero_of_differentiableOn (hankelPsi a s) _ _ H
  simp only [sub_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_zero, add_re,
    add_zero, sub_im, mul_im, zero_add, add_im, zero_sub] at hR
  rw [← hankelCircle_eq hc0, ← hankelCircle_eq hε] at hR
  set F : ℝ → ℂ := fun x ↦ cexp (s * x) * hankelG a (-(Real.exp x : ℂ)) with hF
  have hbot : ∀ x : ℝ, hankelPsi a s (x + ((-π : ℝ) : ℂ) * I) = cexp (-(π * s * I)) * F x := by
    intro x
    simp only [hankelPsi, hF, ofReal_neg]
    rw [Complex.exp_add (x : ℂ), show -π * I = -(π * I) by ring, Complex.exp_neg, exp_pi_mul_I,
      ofReal_exp, show s * (x + -(π * I)) = s * x + -(π * s * I) by ring, Complex.exp_add]
    ring_nf
  have htop : ∀ x : ℝ, hankelPsi a s (x + π * I) = cexp (π * s * I) * F x := by
    intro x
    simp only [hankelPsi, hF]
    rw [Complex.exp_add (x : ℂ), exp_pi_mul_I, ofReal_exp,
      show s * (x + π * I) = s * x + π * s * I by ring, Complex.exp_add]
    ring_nf
  simp only [hbot, htop, intervalIntegral.integral_const_mul] at hR
  -- `F` integrates to the edge integral, by `r = e^x`.
  have hK : ∫ x in Real.log ε..Real.log c, F x = ∫ r in ε..c, (r : ℂ) ^ (s - 1) * hankelG a (-r) := by
    have := integral_deriv_smul_comp' (a := Real.log ε) (b := Real.log c) (f := Real.exp)
      (f' := Real.exp) (g := fun r : ℝ ↦ (r : ℂ) ^ (s - 1) * hankelG a (-r))
      (fun x _ ↦ Real.hasDerivAt_exp x) Real.continuous_exp.continuousOn
      (fun r hr ↦ by
        obtain ⟨x, _, rfl⟩ := hr
        exact (continuousAt_edge a s (Real.exp_pos x)).continuousWithinAt)
    rw [Real.exp_log hε, Real.exp_log hc0] at this
    rw [← this]
    refine integral_congr fun x _ ↦ ?_
    simp only [hF, Function.comp_apply, real_smul, ofReal_exp]
    rw [cpow_def_of_ne_zero (Complex.exp_ne_zero _), Complex.log_exp (by simp [Real.pi_pos])
      (by simp [Real.pi_pos.le]), ← mul_assoc, ← Complex.exp_add]
    congr 2
    ring
  rw [hK] at hR
  rw [Complex.sin, show -(π * s) * I = -(π * s * I) by ring, show π * s * I = π * s * I from rfl]
  linear_combination (-I) * hR + (hankelCircle a c s - hankelCircle a ε s) * I_sq

/-- `|g(z)| ≤ 2e^{|a|}/|z|` for `0 < |z| ≤ 1/2`. -/
theorem norm_hankelG_le {a : ℝ} {z : ℂ} (hz0 : z ≠ 0) (hz : ‖z‖ ≤ 1 / 2) :
    ‖hankelG a z‖ ≤ 2 * Real.exp |a| / ‖z‖ := by
  have hz1 : ‖z‖ ≤ 1 := hz.trans (by norm_num)
  have hpos : 0 < ‖z‖ := norm_pos_iff.2 hz0
  have hlow : ‖z‖ / 2 ≤ ‖1 - cexp z‖ := by
    have h1 := norm_exp_sub_one_sub_id_le hz1
    have h2 : ‖z‖ - ‖cexp z - 1 - z‖ ≤ ‖cexp z - 1‖ := by
      have := norm_sub_norm_le z (-(cexp z - 1 - z))
      rw [show z - -(cexp z - 1 - z) = cexp z - 1 by ring, norm_neg] at this
      linarith
    rw [norm_sub_rev]
    nlinarith
  have hnum : ‖cexp (a * z)‖ ≤ Real.exp |a| := by
    rw [Complex.norm_exp]
    refine Real.exp_le_exp.2 ?_
    calc (a * z).re ≤ ‖(a : ℂ) * z‖ := Complex.re_le_norm _
      _ = |a| * ‖z‖ := by rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ |a| * 1 := mul_le_mul_of_nonneg_left hz1 (abs_nonneg a)
      _ = |a| := mul_one _
  rw [hankelG, norm_div]
  calc ‖cexp (a * z)‖ / ‖1 - cexp z‖ ≤ Real.exp |a| / (‖z‖ / 2) :=
        div_le_div₀ (Real.exp_pos _).le hnum (by positivity) hlow
    _ = 2 * Real.exp |a| / ‖z‖ := by field_simp

/-- For `σ > 1` the circle integral tends to `0` with the radius. -/
theorem tendsto_hankelCircle_zero (a : ℝ) {s : ℂ} (hs : 1 < s.re) :
    Tendsto (fun ε ↦ hankelCircle a ε s) (𝓝[>] 0) (𝓝 0) := by
  set K : ℝ := 2 * π * (2 * Real.exp |a| * Real.exp (π * |s.im|))
  have hbound : ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 → ‖hankelCircle a ε s‖ ≤ K * ε ^ (s.re - 1) := by
    intro ε hε hε2
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := -π) (b := π)
      (C := 2 * Real.exp |a| * Real.exp (π * |s.im|) * ε ^ (s.re - 1))
      (f := fun θ : ℝ ↦ (ε : ℂ) ^ s * cexp (s * θ * I) * hankelG a (ε * cexp (θ * I)))
      (fun θ hθ ↦ by
        have hθ' : |θ| ≤ π := by
          rw [uIoc_of_le (by linarith [Real.pi_pos])] at hθ
          exact abs_le.2 ⟨hθ.1.le, hθ.2⟩
        have hnz : (ε : ℂ) * cexp (θ * I) ≠ 0 :=
          mul_ne_zero (ofReal_ne_zero.2 hε.ne') (Complex.exp_ne_zero _)
        have hn : ‖(ε : ℂ) * cexp (θ * I)‖ = ε := by
          rw [norm_mul, norm_cexp_ofReal_mul_I, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos hε, mul_one]
        have hg := norm_hankelG_le (a := a) hnz (by rw [hn]; exact hε2)
        rw [hn] at hg
        have he : ‖cexp (s * θ * I)‖ ≤ Real.exp (π * |s.im|) := by
          rw [Complex.norm_exp]
          refine Real.exp_le_exp.2 ?_
          have : (s * θ * I).re = -(s.im * θ) := by simp
          rw [this]
          calc -(s.im * θ) ≤ |s.im * θ| := neg_le_abs _
            _ = |s.im| * |θ| := abs_mul _ _
            _ ≤ |s.im| * π := mul_le_mul_of_nonneg_left hθ' (abs_nonneg _)
            _ = π * |s.im| := mul_comm _ _
        rw [norm_mul, norm_mul, norm_cpow_eq_rpow_re_of_pos hε]
        calc ε ^ s.re * ‖cexp (s * θ * I)‖ * ‖hankelG a (ε * cexp (θ * I))‖
            ≤ ε ^ s.re * Real.exp (π * |s.im|) * (2 * Real.exp |a| / ε) := by
              gcongr
          _ = 2 * Real.exp |a| * Real.exp (π * |s.im|) * ε ^ (s.re - 1) := by
              rw [Real.rpow_sub hε, Real.rpow_one]; field_simp)
    rw [hankelCircle]
    refine h.trans (le_of_eq ?_)
    rw [show π - -π = 2 * π by ring, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
    ring
  have hlim : Tendsto (fun ε : ℝ ↦ K * ε ^ (s.re - 1)) (𝓝[>] 0) (𝓝 0) := by
    have hc := (Real.continuousAt_rpow_const 0 (s.re - 1) (Or.inr (by linarith))).tendsto
    rw [Real.zero_rpow (by linarith)] at hc
    simpa using (hc.mono_left nhdsWithin_le_nhds).const_mul K
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_ hlim
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num)] with ε hε
  exact hbound ε hε.1 hε.2.le

/-- `1/(1 - e^{-r}) ≤ 1 + 1/r` for `r > 0`. -/
theorem inv_one_sub_exp_neg_le {r : ℝ} (hr : 0 < r) : 1 / (1 - Real.exp (-r)) ≤ 1 + 1 / r := by
  have h1 : Real.exp (-r) < 1 := by
    have := Real.exp_lt_exp.2 (neg_neg_of_pos hr); rwa [Real.exp_zero] at this
  have h2 : 1 + r ≤ Real.exp r := by linarith [Real.add_one_le_exp r]
  have h3 : Real.exp (-r) * Real.exp r = 1 := by rw [← Real.exp_add]; simp
  rw [div_le_iff₀ (by linarith)]
  have : 0 < Real.exp (-r) := Real.exp_pos _
  field_simp
  nlinarith

/-- For `σ > 1`, `a > 0`, the edge integrand `r^{s-1} g(-r)` is integrable on `(0, ∞)`. -/
theorem integrableOn_edge {a : ℝ} (ha : 0 < a) {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun r : ℝ ↦ (r : ℂ) ^ (s - 1) * hankelG a (-r)) (Ioi 0) := by
  have h1 := integrableOn_cpow_mul_exp_neg (s := s) (by linarith) ha
  have h2 := integrableOn_cpow_mul_exp_neg (s := s - 1) (by simp; linarith) ha
  refine (h1.norm.add h2.norm).mono' ?_ ?_
  · exact ContinuousOn.aestronglyMeasurable
      (fun r hr ↦ (continuousAt_edge a s hr).continuousWithinAt) measurableSet_Ioi
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun r hr ↦ ?_)
    have hr : (0 : ℝ) < r := hr
    have hexp : ‖cexp (-((a : ℂ) * r))‖ = Real.exp (-(a * r)) := by
      rw [show -((a : ℂ) * r) = ((-(a * r) : ℝ) : ℂ) by push_cast; ring, norm_exp_ofReal]
    have hg : ‖hankelG a (-r)‖ = Real.exp (-(a * r)) / (1 - Real.exp (-r)) := by
      rw [hankelG, norm_div, show (a : ℂ) * -(r : ℂ) = -((a : ℂ) * r) by ring, hexp,
        ← ofReal_neg, ← ofReal_exp, ← ofReal_one, ← ofReal_sub, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos]
      have := Real.exp_lt_exp.2 (neg_neg_of_pos hr); rw [Real.exp_zero] at this; linarith
    simp only [Pi.add_apply, norm_mul, norm_cpow_eq_rpow_re_of_pos hr, hexp, hg, sub_re, one_re]
    have hb := inv_one_sub_exp_neg_le hr
    have hpos : 0 < 1 - Real.exp (-r) := by
      have := Real.exp_lt_exp.2 (neg_neg_of_pos hr); rw [Real.exp_zero] at this; linarith
    have hrp : r ^ (s.re - 1 - 1) = r ^ (s.re - 1) / r := by
      rw [Real.rpow_sub hr, Real.rpow_one]
    rw [hrp]
    have e1 : 0 ≤ r ^ (s.re - 1) * Real.exp (-(a * r)) := by positivity
    calc r ^ (s.re - 1) * (Real.exp (-(a * r)) / (1 - Real.exp (-r)))
        = r ^ (s.re - 1) * Real.exp (-(a * r)) * (1 / (1 - Real.exp (-r))) := by ring
      _ ≤ r ^ (s.re - 1) * Real.exp (-(a * r)) * (1 + 1 / r) := mul_le_mul_of_nonneg_left hb e1
      _ = r ^ (s.re - 1) * Real.exp (-(a * r)) + r ^ (s.re - 1) / r * Real.exp (-(a * r)) := by
        field_simp

/-- For `σ > 1` (letting the small circle shrink): `C(c) = 2 sin(πs) ∫_0^c r^{s-1} g(-r) dr`. -/
theorem hankelCircle_eq_of_one_lt {a c : ℝ} (ha : 0 < a) {s : ℂ} (hs : 1 < s.re) (hc0 : 0 < c)
    (hc : c < 2 * π) :
    hankelCircle a c s = 2 * Complex.sin (π * s) * ∫ r in (0 : ℝ)..c, (r : ℂ) ^ (s - 1) * hankelG a (-r) := by
  set f : ℝ → ℂ := fun r ↦ (r : ℂ) ^ (s - 1) * hankelG a (-r) with hf
  have hint := integrableOn_edge ha hs
  have hintc : IntegrableOn f (uIcc 0 c) := by
    rw [uIcc_of_le hc0.le, integrableOn_Icc_iff_integrableOn_Ioc]
    exact hint.mono_set Ioc_subset_Ioi_self
  have hcont := continuousOn_primitive_interval_left hintc
  have ht1 : Tendsto (fun ε ↦ ∫ r in ε..c, f r) (𝓝[>] 0) (𝓝 (∫ r in (0 : ℝ)..c, f r)) := by
    have := (hcont 0 left_mem_uIcc).tendsto
    rw [← nhdsWithin_Ioo_eq_nhdsGT hc0]
    exact this.mono_left (nhdsWithin_mono _ (fun x hx ↦ by
      rw [uIcc_of_le hc0.le]; exact Ioo_subset_Icc_self hx))
  have hlim := (tendsto_hankelCircle_zero a hs).add (ht1.const_mul (2 * Complex.sin (π * s)))
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), hankelCircle a c s =
      hankelCircle a ε s + 2 * Complex.sin (π * s) * ∫ r in ε..c, f r := by
    filter_upwards [Ioo_mem_nhdsGT hc0] with ε hε
    rw [← hankelCircle_sub hε.1 hε.2.le hc s]
    ring
  have := tendsto_nhds_unique (tendsto_const_nhds.congr' hev) hlim
  rw [this, zero_add]

/-- **Theorem 12.3**, the identity, in the form valid for every `σ > 1`:
`π I(s, a) = sin(πs) Γ(s) ζ(s, a)`. -/
theorem pi_mul_hankelI {a c : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1) (hc0 : 0 < c) (hc : c < 2 * π)
    {s : ℂ} (hs : 1 < s.re) :
    π * hankelI a c s = Complex.sin (π * s) * (Gamma s * hurwitzZeta a s) := by
  set f : ℝ → ℂ := fun r ↦ (r : ℂ) ^ (s - 1) * hankelG a (-r) with hf
  have hint := integrableOn_edge ha0 hs
  have h12 := apostol_thm_12_2 ha0 ha1 hs
  have hcongr : ∫ x : ℝ in Ioi 0, (x : ℂ) ^ (s - 1) *
      ((Real.exp (-(a * x)) / (1 - Real.exp (-x)) : ℝ) : ℂ) = ∫ x in Ioi 0, f x := by
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ ↦ ?_
    simp only [hf, hankelG]
    push_cast
    ring_nf
  rw [h12, hcongr, ← Ioc_union_Ioi_eq_Ioi hc0.le,
    setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (hint.mono_set Ioc_subset_Ioi_self) (hint.mono_set (Ioi_subset_Ioi hc0.le)),
    ← intervalIntegral.integral_of_le hc0.le]
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  rw [hankelI, mul_div_cancel₀ _ hπ, hankelCircle_eq_of_one_lt ha0 hs hc0 hc, hankelEdge]
  ring

/-! ### `I(s, a)` is entire -/

theorem norm_hankelG_neg {a r : ℝ} (hr : 0 < r) :
    ‖hankelG a (-r)‖ = Real.exp (-(a * r)) / (1 - Real.exp (-r)) := by
  have hexp : ‖cexp (-((a : ℂ) * r))‖ = Real.exp (-(a * r)) := by
    rw [show -((a : ℂ) * r) = ((-(a * r) : ℝ) : ℂ) by push_cast; ring, norm_exp_ofReal]
  rw [hankelG, norm_div, show (a : ℂ) * -(r : ℂ) = -((a : ℂ) * r) by ring, hexp,
    ← ofReal_neg, ← ofReal_exp, ← ofReal_one, ← ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos]
  have := Real.exp_lt_exp.2 (neg_neg_of_pos hr); rw [Real.exp_zero] at this; linarith

/-- The edge integral is a Mellin transform. -/
theorem hankelEdge_eq_mellin {a c : ℝ} (hc0 : 0 < c) :
    hankelEdge a c = mellin ((Ioi c).indicator fun r : ℝ ↦ hankelG a (-r)) := by
  funext s
  rw [mellin, hankelEdge]
  have : (fun t : ℝ ↦ (t : ℂ) ^ (s - 1) • (Ioi c).indicator (fun r : ℝ ↦ hankelG a (-r)) t) =
      (Ioi c).indicator (fun t : ℝ ↦ (t : ℂ) ^ (s - 1) * hankelG a (-t)) := by
    funext t
    by_cases ht : t ∈ Ioi c <;> simp [ht]
  rw [this, setIntegral_indicator measurableSet_Ioi, inter_eq_right.2 (Ioi_subset_Ioi hc0.le)]

theorem differentiable_hankelEdge {a c : ℝ} (ha : 0 < a) (hc0 : 0 < c) :
    Differentiable ℂ (hankelEdge a c) := by
  set G : ℝ → ℂ := fun r ↦ hankelG a (-r) with hG
  have hc1 : 0 < 1 - Real.exp (-c) := by
    have := Real.exp_lt_exp.2 (neg_neg_of_pos hc0); rw [Real.exp_zero] at this; linarith
  have hbd : ∀ r, c < r → ‖G r‖ ≤ (1 - Real.exp (-c))⁻¹ * Real.exp (-a * r) := by
    intro r hr
    have hr0 : 0 < r := hc0.trans hr
    rw [hG, norm_hankelG_neg hr0, div_eq_inv_mul, neg_mul]
    refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
    refine inv_anti₀ hc1 ?_
    have := Real.exp_le_exp.2 (neg_le_neg hr.le); linarith
  have hGint : IntegrableOn G (Ioi c) := by
    refine ((integrableOn_exp_mul_Ioi (neg_neg_of_pos ha) c).const_mul
      (1 - Real.exp (-c))⁻¹).mono' ?_ ?_
    · refine ContinuousOn.aestronglyMeasurable (fun r hr ↦ ?_) measurableSet_Ioi
      have hz := one_sub_exp_neg_ne_zero (hc0.trans hr)
      have : ContinuousAt G r := by
        simp only [hG, hankelG]
        fun_prop (disch := exact hz)
      exact this.continuousWithinAt
    · exact (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun r hr ↦ hbd r hr)
  intro s
  rw [hankelEdge_eq_mellin hc0]
  refine mellin_differentiableAt_of_isBigO_rpow (a := s.re + 1) (b := s.re - 1) ?_ ?_
    (by linarith) ?_ (by linarith)
  · exact ((integrable_indicator_iff measurableSet_Ioi).2 hGint).integrableOn.locallyIntegrableOn
  · have h1 : Asymptotics.IsBigO atTop ((Ioi c).indicator G) fun r ↦ Real.exp (-a * r) := by
      refine Asymptotics.IsBigO.of_bound (1 - Real.exp (-c))⁻¹ ?_
      filter_upwards [eventually_gt_atTop c] with r hr
      rw [indicator_of_mem hr, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact hbd r hr
    exact h1.trans (isLittleO_exp_neg_mul_rpow_atTop ha _).isBigO
  · have h0 : Filter.EventuallyEq (𝓝[>] 0) ((Ioi c).indicator G) fun _ ↦ (0 : ℂ) := by
      filter_upwards [Ioo_mem_nhdsGT hc0] with r hr
      exact indicator_of_notMem (fun h ↦ (lt_irrefl _ (hr.2.trans h))) _
    exact h0.trans_isBigO (Asymptotics.isBigO_zero _ _)

/-- The circle integral is entire in `s`. -/
theorem differentiable_hankelCircle {a c : ℝ} (hc0 : 0 < c) (hc : c < 2 * π) :
    Differentiable ℂ (hankelCircle a c) := by
  set L : ℝ → ℂ := fun θ ↦ Real.log c + θ * I with hL
  set h : ℝ → ℂ := fun θ ↦ hankelG a (cexp (L θ)) with hh
  have hnorm : ∀ θ, ‖cexp (L θ)‖ = c := fun θ ↦ by
    rw [hL, Complex.exp_add, norm_mul, norm_cexp_ofReal_mul_I, mul_one, ← ofReal_exp,
      Real.exp_log hc0, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc0]
  have hhc : Continuous h := by
    refine continuous_iff_continuousAt.2 fun θ ↦ ?_
    have hz : 1 - cexp (cexp (L θ)) ≠ 0 :=
      one_sub_exp_ne_zero (Complex.exp_ne_zero _) (by rw [hnorm]; exact hc)
    simp only [hh, hankelG, hL]
    fun_prop (disch := exact hz)
  have hLc : Continuous L := by simp only [hL]; fun_prop
  obtain ⟨Hb, hHb⟩ := (isCompact_Icc (a := -π) (b := π)).exists_bound_of_continuousOn
    hhc.continuousOn
  set Λ : ℝ := |Real.log c| + π
  have hLb : ∀ θ ∈ Ι (-π) π, ‖L θ‖ ≤ Λ := by
    intro θ hθ
    rw [uIoc_of_le (by linarith [Real.pi_pos])] at hθ
    have : |θ| ≤ π := abs_le.2 ⟨hθ.1.le, hθ.2⟩
    calc ‖L θ‖ ≤ ‖(Real.log c : ℂ)‖ + ‖(θ : ℂ) * I‖ := norm_add_le _ _
      _ = |Real.log c| + |θ| := by
        rw [norm_mul, norm_I, mul_one, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
          Real.norm_eq_abs]
      _ ≤ Λ := by linarith
  intro s₀
  have hfun : hankelCircle a c = fun s ↦ ∫ θ in (-π)..π, cexp (s * L θ) * h θ :=
    funext fun s ↦ hankelCircle_eq hc0 s
  rw [hfun]
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := -π) (b := π) (x₀ := s₀) (s := Metric.ball s₀ 1)
    (F := fun s θ ↦ cexp (s * L θ) * h θ) (F' := fun s θ ↦ L θ * cexp (s * L θ) * h θ)
    (bound := fun _ ↦ Λ * Real.exp ((‖s₀‖ + 1) * Λ) * Hb) (Metric.ball_mem_nhds s₀ one_pos)
    (Eventually.of_forall fun s ↦ (by fun_prop : Continuous fun θ ↦ cexp (s * L θ) * h θ)
      |>.aestronglyMeasurable)
    ((by fun_prop : Continuous fun θ ↦ cexp (s₀ * L θ) * h θ).intervalIntegrable _ _)
    ((by fun_prop : Continuous fun θ ↦ L θ * cexp (s₀ * L θ) * h θ).aestronglyMeasurable)
    (Eventually.of_forall fun θ hθ s hs ↦ by
      have hsn : ‖s‖ ≤ ‖s₀‖ + 1 := by
        have := norm_le_norm_add_norm_sub' s s₀
        rw [Metric.mem_ball, dist_eq_norm] at hs
        linarith
      have hθ' : θ ∈ Icc (-π) π := by
        rw [uIoc_of_le (by linarith [Real.pi_pos])] at hθ; exact Ioc_subset_Icc_self hθ
      have he : ‖cexp (s * L θ)‖ ≤ Real.exp ((‖s₀‖ + 1) * Λ) := by
        rw [Complex.norm_exp]
        refine Real.exp_le_exp.2 ((Complex.re_le_norm _).trans ?_)
        rw [norm_mul]
        exact mul_le_mul hsn (hLb θ hθ) (norm_nonneg _) (by positivity)
      rw [norm_mul, norm_mul]
      exact mul_le_mul (mul_le_mul (hLb θ hθ) he (norm_nonneg _) (by positivity)) (hHb θ hθ')
        (norm_nonneg _) (by positivity))
    intervalIntegrable_const
    (Eventually.of_forall fun θ _ s _ ↦ by
      have := (((hasDerivAt_id s).mul_const (L θ)).cexp).mul_const (h θ)
      exact this.congr_deriv (by simp only [id]; ring))
  exact key.2.differentiableAt

/-- **Theorem 12.3** (Apostol). For `0 < a ≤ 1` and a loop of radius `0 < c < 2π`, the contour
integral `I(s, a) = (1/2πi) ∫_C z^{s-1} e^{az}/(1 - e^z) dz` is an entire function of `s`, and
`ζ(s, a) = Γ(1 - s) I(s, a)` for `σ > 1`. The identity is stated for `s` not an integer: at
`s = 2, 3, …` both `I(s, a)` and Mathlib's `Γ(1 - s)` (`Γ` at a pole is `0` in Mathlib) vanish,
and there the identity holds as `π I(s, a) = sin(πs) Γ(s) ζ(s, a)` (`pi_mul_hankelI`, all `σ > 1`). -/
@[kb "apostol1976" "Thm 12.3, p. 253"]
theorem apostol_thm_12_3 {a c : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1) (hc0 : 0 < c) (hc : c < 2 * π) :
    Differentiable ℂ (hankelI a c) ∧
      ∀ s : ℂ, 1 < s.re → (∀ n : ℤ, s ≠ n) → hurwitzZeta a s = Gamma (1 - s) * hankelI a c s := by
  refine ⟨?_, fun s hs hint ↦ ?_⟩
  · unfold hankelI
    have h1 : Differentiable ℂ fun s : ℂ ↦ Complex.sin (π * s) :=
      Complex.differentiable_sin.comp (differentiable_id.const_mul _)
    exact ((h1.mul (differentiable_hankelEdge ha0 hc0)).add
      ((differentiable_hankelCircle hc0 hc).div_const 2)).div_const _
  · have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
    have hsin : Complex.sin (π * s) ≠ 0 := by
      rw [Ne, Complex.sin_eq_zero_iff]
      rintro ⟨k, hk⟩
      exact hint k (by
        have : (π : ℂ) * s = π * k := by rw [hk]; ring
        exact mul_left_cancel₀ hπ this)
    have h := pi_mul_hankelI ha0 ha1 hc0 hc hs
    have hG := Complex.Gamma_mul_Gamma_one_sub s
    have hI : hankelI a c s = Complex.sin (π * s) * (Gamma s * hurwitzZeta a s) / π := by
      rw [← h]; field_simp
    rw [hI]
    symm
    calc Gamma (1 - s) * (Complex.sin (π * s) * (Gamma s * hurwitzZeta a s) / π)
        = Gamma s * Gamma (1 - s) * Complex.sin (π * s) * hurwitzZeta a s / π := by ring
      _ = π / Complex.sin (π * s) * Complex.sin (π * s) * hurwitzZeta a s / π := by rw [hG]
      _ = hurwitzZeta a s := by field_simp

end NTKB.Apostol
