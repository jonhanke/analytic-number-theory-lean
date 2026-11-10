/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Analysis.Real.Pi.Bounds
import NTKB.Analytic.Apostol.Zeta.HurwitzBounds
import NTKB.Analytic.Davenport.Hadamard.Gamma
import NTKB.Analytic.Davenport.Hadamard.LogDeriv

/-!
# Riemann's `ξ` function and its order (Davenport, Chapter 12, p. 79–80)

**Davenport, Ch. 12, (1).** `ξ(s) = ½ s(s - 1) π^{-s/2} Γ(s/2) ζ(s)` is entire, `ξ(s) = ξ(1 - s)`.
**(2)** `|ξ(s)| < exp(C|s| log|s|)` as `|s| → ∞`, so `ξ` has order at most `1`.
**(3)** `ζ(s) = O(|s|)` for `σ ≥ 1/2`, `|s|` large.
The zeros of `ξ` are the nontrivial zeros of `ζ`, in `0 < σ < 1`.

## Main definitions

* `NTKB.riemannXi s = (s (s - 1) Λ₀(s) + 1) / 2`, with Mathlib's entire `completedRiemannZeta₀`
  (`Λ₀(s) = Λ(s) + 1/s + 1/(1 - s)`); `NTKB.riemannXi_eq` is Davenport's formula (1).

Mathlib has `Λ₀` but not `ξ` (the coverage audit). The bound for `ζ` reuses Apostol's Theorem
12.23 (`NTKB.Apostol.apostol_thm_12_23_a`, `apostol_thm_12_23_b`) instead of Davenport's integral
representation; the bound for `Γ` is `NTKB.Gamma_le_rpow` instead of Stirling's formula.
-/

open Complex Filter Topology Asymptotics Bornology HurwitzZeta
open scoped ENNReal NNReal Real

namespace NTKB

/-- **Riemann's `ξ` function** (Davenport, Ch. 12, (1)):
`ξ(s) = ½ s(s - 1) π^{-s/2} Γ(s/2) ζ(s)`, written through Mathlib's entire `Λ₀` as
`(s (s - 1) Λ₀(s) + 1) / 2` (see `riemannXi_eq`). -/
noncomputable def riemannXi (s : ℂ) : ℂ := (s * (s - 1) * completedRiemannZeta₀ s + 1) / 2

lemma differentiable_riemannXi : Differentiable ℂ riemannXi :=
  (((differentiable_id.mul (differentiable_id.sub_const 1)).mul
    differentiable_completedZeta₀).add_const 1).div_const 2

/-- `ξ(1 - s) = ξ(s)` (Davenport, Ch. 12, p. 79). -/
@[kb "davenport1980" "Ch 12, p. 79"]
theorem riemannXi_one_sub (s : ℂ) : riemannXi (1 - s) = riemannXi s := by
  simp only [riemannXi, completedRiemannZeta₀_one_sub]; ring

@[simp] lemma riemannXi_zero : riemannXi 0 = 1 / 2 := by simp [riemannXi]

@[simp] lemma riemannXi_one : riemannXi 1 = 1 / 2 := by simp [riemannXi]

lemma riemannXi_eq_completed {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    riemannXi s = s * (s - 1) / 2 * completedRiemannZeta s := by
  rw [completedRiemannZeta_eq, riemannXi]
  have : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  have : s - 1 ≠ 0 := sub_ne_zero.mpr h1
  field_simp
  ring

lemma riemannXi_eq_mul_Gammaℝ {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) (hG : Gammaℝ s ≠ 0) :
    riemannXi s = s * (s - 1) / 2 * Gammaℝ s * riemannZeta s := by
  rw [riemannXi_eq_completed h0 h1, riemannZeta_def_of_ne_zero h0]
  field_simp

/-- **Davenport, Ch. 12, (1)**: `ξ(s) = ½ s(s - 1) π^{-s/2} Γ(s/2) ζ(s)` (away from `s = 1` and the
poles `0, -2, -4, …` of `Γ(s/2)`). -/
@[kb "davenport1980" "Ch 12, p. 79"]
theorem riemannXi_eq {s : ℂ} (h1 : s ≠ 1) (h2 : ∀ n : ℕ, s ≠ -(2 * n)) :
    riemannXi s = 1 / 2 * s * (s - 1) * (π : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2) *
      riemannZeta s := by
  have h0 : s ≠ 0 := by simpa using h2 0
  have hG : Gammaℝ s ≠ 0 := by
    rw [Ne, Gammaℝ_eq_zero_iff, not_exists]; exact h2
  rw [riemannXi_eq_mul_Gammaℝ h0 h1 hG, Gammaℝ_def]
  ring

/-- `ξ` does not vanish on `σ ≥ 1`. -/
lemma riemannXi_ne_zero_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) : riemannXi s ≠ 0 := by
  rcases eq_or_ne s 1 with rfl | h1
  · simp
  have h0 : s ≠ 0 := by rintro rfl; simp at hs; linarith
  rw [riemannXi_eq_mul_Gammaℝ h0 h1 (Gammaℝ_ne_zero_of_re_pos (by linarith))]
  exact mul_ne_zero (mul_ne_zero (div_ne_zero (mul_ne_zero h0 (sub_ne_zero.mpr h1)) two_ne_zero)
    (Gammaℝ_ne_zero_of_re_pos (by linarith))) (riemannZeta_ne_zero_of_one_le_re hs)

/-- **Davenport, Ch. 12, p. 80**: the zeros of `ξ` are exactly the nontrivial zeros of `ζ`, those
in the critical strip `0 < σ < 1`. -/
@[kb "davenport1980" "Ch 12, p. 80"]
theorem riemannXi_eq_zero_iff {s : ℂ} :
    riemannXi s = 0 ↔ riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 := by
  constructor
  · intro h
    have hlt : s.re < 1 := by
      by_contra hle; exact riemannXi_ne_zero_of_one_le_re (not_lt.mp hle) h
    have hgt : 0 < s.re := by
      by_contra hle
      have : 1 ≤ (1 - s).re := by simp; linarith [not_lt.mp hle]
      exact riemannXi_ne_zero_of_one_le_re this (by rw [riemannXi_one_sub]; exact h)
    have h0 : s ≠ 0 := by rintro rfl; simp at hgt
    have h1 : s ≠ 1 := by rintro rfl; simp at hlt
    rw [riemannXi_eq_mul_Gammaℝ h0 h1 (Gammaℝ_ne_zero_of_re_pos hgt)] at h
    refine ⟨?_, hgt, hlt⟩
    rcases mul_eq_zero.mp h with h | h
    · exfalso
      rcases mul_eq_zero.mp h with h | h
      · exact mul_ne_zero h0 (sub_ne_zero.mpr h1) (by simpa using h)
      · exact Gammaℝ_ne_zero_of_re_pos hgt h
    · exact h
  · rintro ⟨hz, hgt, hlt⟩
    have h0 : s ≠ 0 := by rintro rfl; simp at hgt
    have h1 : s ≠ 1 := by rintro rfl; simp at hlt
    rw [riemannXi_eq_mul_Gammaℝ h0 h1 (Gammaℝ_ne_zero_of_re_pos hgt), hz, mul_zero]

/-! ### Growth -/

/-- `a^c ≤ b^d` for `1 ≤ a ≤ b` and `0 ≤ c ≤ d`. -/
lemma rpow_le_rpow_of_le_of_le {a b c d : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) (hc : 0 ≤ c)
    (hcd : c ≤ d) : a ^ c ≤ b ^ d :=
  (Real.rpow_le_rpow (by linarith) hab hc).trans
    (Real.rpow_le_rpow_of_exponent_le (by linarith) hcd)

lemma hurwitzZeta_one_eq : hurwitzZeta ((1 : ℝ) : UnitAddCircle) = riemannZeta := by
  have h : ((1 : ℝ) : UnitAddCircle) = 0 := AddCircle.coe_period 1
  rw [h, hurwitzZeta_zero]

/-- **Davenport, Ch. 12, (3)**: `ζ(s) = O(|s|)` for `σ ≥ 1/2` and `|s|` large (here `|s| ≥ 3`).
Proof via Apostol's Theorem 12.23 instead of Davenport's integral representation. -/
@[kb "davenport1980" "Ch 12, p. 79"]
theorem Davenport.norm_riemannZeta_le_mul_norm :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, 1 / 2 ≤ s.re → 3 ≤ ‖s‖ → ‖riemannZeta s‖ ≤ C * ‖s‖ := by
  obtain ⟨A, hA, hAb⟩ := NTKB.Apostol.apostol_thm_12_23_b (δ := 1 / 2) (by norm_num) (by norm_num)
  refine ⟨A + 3, by linarith, fun s hσ hs ↦ ?_⟩
  have hs1 : 1 ≤ ‖s‖ := by linarith
  have hone : ((1 : ℝ) : ℂ) ^ (-s) = 1 := by simp
  rcases le_or_gt s.re 2 with h2 | h2
  · -- the strip `1/2 ≤ σ ≤ 2`, where `|t| ≥ 1`
    have ht : 1 ≤ |s.im| := by
      have hn : ‖s‖ ^ 2 = s.re ^ 2 + s.im ^ 2 := by
        rw [← Complex.normSq_add_mul_I s.re s.im, Complex.re_add_im, Complex.sq_norm,
          Complex.normSq_apply]
      have : 9 ≤ s.re ^ 2 + s.im ^ 2 := by rw [← hn]; nlinarith
      have : s.re ^ 2 ≤ 4 := by nlinarith
      have : 1 ≤ s.im ^ 2 := by linarith
      rw [← abs_one, ← sq_le_sq]; simpa using this
    have h := hAb 1 one_pos le_rfl s (by linarith) h2 ht
    rw [hone, congrFun hurwitzZeta_one_eq s] at h
    have htle : |s.im| ^ (1 / 2 : ℝ) ≤ ‖s‖ :=
      (Real.rpow_le_self_of_one_le ht (by norm_num)).trans (Complex.abs_im_le_norm s)
    calc ‖riemannZeta s‖ ≤ ‖riemannZeta s - 1‖ + 1 := by
          simpa using norm_le_norm_sub_add (riemannZeta s) 1
      _ ≤ A * ‖s‖ + 1 := by nlinarith
      _ ≤ (A + 3) * ‖s‖ := by nlinarith
  · -- `σ > 2`: `|ζ(s) - 1| ≤ ζ(2) = π²/6`
    have h := NTKB.Apostol.apostol_thm_12_23_a (a := 1) one_pos le_rfl (δ := 1) one_pos
      (s := s) (by linarith)
    rw [hone, congrFun hurwitzZeta_one_eq s] at h
    have hz2 : (riemannZeta ((1 + 1 : ℝ) : ℂ)).re ≤ 2 := by
      rw [show ((1 + 1 : ℝ) : ℂ) = 2 by norm_num, riemannZeta_two]
      have : (((π : ℂ) ^ 2 / 6).re) = π ^ 2 / 6 := by
        rw [show ((π : ℂ) ^ 2 / 6) = ((π ^ 2 / 6 : ℝ) : ℂ) by push_cast; ring, Complex.ofReal_re]
      rw [this]
      nlinarith [Real.pi_lt_d2, Real.pi_pos]
    calc ‖riemannZeta s‖ ≤ ‖riemannZeta s - 1‖ + 1 := by
          simpa using norm_le_norm_sub_add (riemannZeta s) 1
      _ ≤ 3 := by linarith
      _ ≤ (A + 3) * ‖s‖ := by nlinarith

/-- Growth on `σ ≥ 1/2`: `|ξ(s)| ≤ K (|s| + 1)^{|s| + 4}` for `|s| ≥ 3`. -/
lemma norm_riemannXi_le_of_half_le_re :
    ∃ K : ℝ, 0 < K ∧ ∀ s : ℂ, 1 / 2 ≤ s.re → 3 ≤ ‖s‖ →
      ‖riemannXi s‖ ≤ K * (‖s‖ + 1) ^ (‖s‖ + 4) := by
  obtain ⟨C, hC, hCb⟩ := Davenport.norm_riemannZeta_le_mul_norm
  refine ⟨10 * C, by positivity, fun s hσ hs ↦ ?_⟩
  have h1 : s ≠ 1 := by rintro rfl; norm_num at hs
  have h2 : ∀ n : ℕ, s ≠ -(2 * n) := by
    intro n h
    have : s.re = -(2 * n) := by rw [h]; simp
    have : (0 : ℝ) ≤ n := n.cast_nonneg
    linarith
  rw [riemannXi_eq h1 h2]
  set x := ‖s‖
  have hx1 : 1 ≤ x + 1 := by linarith [norm_nonneg s]
  -- the factors
  have hpi : ‖(π : ℂ) ^ (-s / 2)‖ ≤ 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    refine Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.pi_gt_three]) ?_
    simp; linarith
  have hG : ‖Complex.Gamma (s / 2)‖ ≤ 20 * (x + 1) ^ (x + 1) := by
    have hre : (s / 2).re = s.re / 2 := by simp
    refine (norm_Gamma_le_Gamma_re (by rw [hre]; linarith)).trans ?_
    rw [hre]
    refine (Gamma_le_rpow (by linarith)).trans ?_
    have hσx : s.re ≤ x := Complex.re_le_norm s
    gcongr
    exact rpow_le_rpow_of_le_of_le (by linarith) (by linarith) (by linarith) (by linarith)
  have hsx : ‖s - 1‖ ≤ x + 1 := by
    simpa using norm_sub_le s 1
  have hz := hCb s hσ hs
  have hpow : (x + 1) ^ (x + 4) = (x + 1) ^ (3 : ℝ) * (x + 1) ^ (x + 1) := by
    rw [← Real.rpow_add (by linarith)]; ring_nf
  have hx3 : (x + 1) ^ (3 : ℝ) = (x + 1) ^ 3 := by norm_cast
  rw [hpow, hx3]
  have hGpos : 0 ≤ (x + 1) ^ (x + 1) := by positivity
  calc ‖1 / 2 * s * (s - 1) * (π : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2) * riemannZeta s‖
      = 1 / 2 * x * ‖s - 1‖ * ‖(π : ℂ) ^ (-s / 2)‖ * ‖Complex.Gamma (s / 2)‖ *
          ‖riemannZeta s‖ := by
        simp only [norm_mul, norm_div, norm_one, Complex.norm_ofNat, x]
    _ ≤ 1 / 2 * x * (x + 1) * 1 * (20 * (x + 1) ^ (x + 1)) * (C * x) := by
        gcongr
    _ ≤ 10 * C * ((x + 1) ^ 3 * (x + 1) ^ (x + 1)) := by
        have hx0 : 0 ≤ x := norm_nonneg s
        have : x * (x + 1) * x ≤ (x + 1) ^ 3 := by nlinarith
        nlinarith [mul_le_mul_of_nonneg_right this (mul_nonneg hC.le hGpos)]

/-- **Davenport, Ch. 12, (2)**: `|ξ(s)| < exp(C |s| log |s|)` for `|s|` large (here `|s| ≥ 4`). -/
@[kb "davenport1980" "Ch 12, p. 79"]
theorem Davenport.norm_riemannXi_le_exp :
    ∃ C : ℝ, ∀ s : ℂ, 4 ≤ ‖s‖ → ‖riemannXi s‖ ≤ Real.exp (C * ‖s‖ * Real.log ‖s‖) := by
  obtain ⟨K, hK, hKb⟩ := norm_riemannXi_le_of_half_le_re
  -- both half planes: `|ξ(s)| ≤ K (|s| + 2)^{|s| + 5}`
  have hall : ∀ s : ℂ, 4 ≤ ‖s‖ → ‖riemannXi s‖ ≤ K * (‖s‖ + 2) ^ (‖s‖ + 5) := by
    intro s hs
    rcases le_or_gt (1 / 2) s.re with hσ | hσ
    · refine (hKb s hσ (by linarith)).trans ?_
      gcongr
      exact rpow_le_rpow_of_le_of_le (by linarith [norm_nonneg s]) (by linarith) (by linarith)
        (by linarith)
    · rw [← riemannXi_one_sub]
      have h1 : 1 / 2 ≤ (1 - s).re := by simp; linarith
      have hn1 : ‖1 - s‖ ≤ ‖s‖ + 1 := by simpa [add_comm] using norm_sub_le (1 : ℂ) s
      have hn2 : ‖s‖ - 1 ≤ ‖1 - s‖ := by
        have := norm_sub_norm_le s 1
        rw [norm_sub_rev] at this; simpa using this
      refine (hKb (1 - s) h1 (by linarith)).trans ?_
      gcongr
      exact rpow_le_rpow_of_le_of_le (by linarith [norm_nonneg (1 - s)]) (by linarith)
        (by linarith [norm_nonneg (1 - s)]) (by linarith)
  refine ⟨|Real.log K| + 5, fun s hs ↦ ?_⟩
  set x := ‖s‖
  have hx0 : 0 < x := by linarith
  have hlogx : 1 ≤ Real.log x := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
  have hlog2 : Real.log (x + 2) ≤ 2 * Real.log x := by
    rw [← Real.log_rpow hx0]
    refine Real.log_le_log (by linarith) ?_
    norm_num
    nlinarith
  refine (hall s hs).trans ?_
  have hexp : K * (x + 2) ^ (x + 5) = Real.exp (Real.log K + Real.log (x + 2) * (x + 5)) := by
    rw [Real.exp_add, Real.exp_log hK, Real.rpow_def_of_pos (by linarith)]
  rw [hexp]
  refine Real.exp_le_exp.mpr ?_
  have hxl : 1 ≤ x * Real.log x := by nlinarith
  have hlogK : Real.log K ≤ |Real.log K| := le_abs_self _
  have : Real.log (x + 2) * (x + 5) ≤ 2 * Real.log x * (9 / 4 * x) := by
    have hlx2 : 0 ≤ Real.log (x + 2) := Real.log_nonneg (by linarith)
    have : x + 5 ≤ 9 / 4 * x := by linarith
    calc Real.log (x + 2) * (x + 5) ≤ Real.log (x + 2) * (9 / 4 * x) := by gcongr
      _ ≤ 2 * Real.log x * (9 / 4 * x) := by gcongr
  have habs : |Real.log K| ≤ |Real.log K| * (x * Real.log x) :=
    le_mul_of_one_le_right (abs_nonneg _) hxl
  nlinarith

/-- **Davenport, Ch. 12, p. 79**: `ξ` is an entire function of order at most `1`. -/
@[kb "davenport1980" "Ch 12, p. 79"]
theorem Davenport.entireOrder_riemannXi_le_one : entireOrder riemannXi ≤ 1 := by
  obtain ⟨C, hC⟩ := Davenport.norm_riemannXi_le_exp
  have : entireOrder riemannXi ≤ ((1 : ℝ≥0) : ℝ≥0∞) := by
    refine entireOrder_le_of_eventually fun a ha ↦ ?_
    simp only [NNReal.coe_one] at ha
    set ε := (a - 1) / 2
    have hε : 0 < ε := by simp only [ε]; linarith
    have hev : ∀ᶠ r : ℝ in atTop, (|C| / ε) * r ^ (1 + ε) + 0 ≤ r ^ a :=
      eventually_mul_rpow_add_le_rpow (by linarith) (by simp only [ε]; linarith) _ _
    have hev' := (tendsto_norm_cobounded_atTop (E := ℂ)).eventually
      (hev.and (eventually_ge_atTop 4))
    filter_upwards [hev'] with s hs
    obtain ⟨hs1, hs4⟩ := hs
    refine (hC s hs4).trans (Real.exp_le_exp.mpr ?_)
    have hlog : Real.log ‖s‖ ≤ ‖s‖ ^ ε / ε := Real.log_le_rpow_div (norm_nonneg _) hε
    have hlog0 : 0 ≤ Real.log ‖s‖ := Real.log_nonneg (by linarith)
    have hpow : ‖s‖ * ‖s‖ ^ ε = ‖s‖ ^ (1 + ε) := by
      rw [Real.rpow_add (by linarith), Real.rpow_one]
    have hxl : 0 ≤ ‖s‖ * Real.log ‖s‖ := mul_nonneg (norm_nonneg _) hlog0
    calc C * ‖s‖ * Real.log ‖s‖ ≤ |C| * ‖s‖ * Real.log ‖s‖ := by
          rw [mul_assoc, mul_assoc]; exact mul_le_mul_of_nonneg_right (le_abs_self C) hxl
      _ ≤ |C| * ‖s‖ * (‖s‖ ^ ε / ε) := by gcongr
      _ = |C| / ε * ‖s‖ ^ (1 + ε) := by rw [← hpow]; field_simp
      _ ≤ ‖s‖ ^ a := by linarith
  simpa using this

/-- **Davenport, Ch. 12, (6) (row 12-6)**: `ξ(s) = e^{A + Bs} ∏_ρ (1 - s/ρ) e^{s/ρ}`, the product
over the zeros `ρ` of `ξ` (the nontrivial zeros of `ζ`) with multiplicity. -/
@[kb "davenport1980" "Ch 12, p. 80"]
theorem Davenport.riemannXi_hadamard :
    ∃ A B : ℂ, ∀ s, riemannXi s = Complex.exp (A + B * s) *
      ∏' ρ : ZeroIndex riemannXi, (1 - s / ρ.val) * Complex.exp (s / ρ.val) :=
  Davenport.hadamard_factorization_order_one differentiable_riemannXi (by simp)
    Davenport.entireOrder_riemannXi_le_one

lemma summable_riemannXi_zeros :
    (Summable fun ρ : ZeroIndex riemannXi ↦ ‖ρ.val‖⁻¹ ^ 2) ∧
      (∀ ρ : ZeroIndex riemannXi, ρ.val ≠ 0) :=
  summable_of_entireOrder_le_one differentiable_riemannXi (by simp)
    Davenport.entireOrder_riemannXi_le_one

/-- **Logarithmic derivative of `ξ`** (Davenport, Ch. 12, p. 80):
`ξ'(s)/ξ(s) = B + ∑_ρ (1/(s - ρ) + 1/ρ)` for `ξ(s) ≠ 0`. -/
@[kb "davenport1980" "Ch 12, p. 80"]
theorem Davenport.logDeriv_riemannXi {A B : ℂ}
    (h : ∀ s, riemannXi s = Complex.exp (A + B * s) *
      ∏' ρ : ZeroIndex riemannXi, (1 - s / ρ.val) * Complex.exp (s / ρ.val))
    {s : ℂ} (hs : riemannXi s ≠ 0) :
    logDeriv riemannXi s = B + ∑' ρ : ZeroIndex riemannXi, (1 / (s - ρ.val) + 1 / ρ.val) := by
  obtain ⟨ha, ha0⟩ := summable_riemannXi_zeros
  have hfun : riemannXi = fun z ↦ Complex.exp (A + B * z) *
      canonicalProductOne (fun ρ : ZeroIndex riemannXi ↦ ρ.val) z := funext h
  have := logDeriv_exp_mul_canonicalProductOne ha ha0 A B fun ρ ↦
    ZeroIndex.val_ne_of_ne_zero (differentiable_riemannXi.analyticAt _) hs
  rw [← hfun] at this
  exact this

lemma hasDerivAt_riemannXi_zero :
    HasDerivAt riemannXi (-completedRiemannZeta₀ 0 / 2) 0 := by
  have hΛ := (differentiable_completedZeta₀ 0).hasDerivAt
  have := ((((hasDerivAt_id (0 : ℂ)).mul ((hasDerivAt_id (0 : ℂ)).sub_const 1)).mul hΛ).add_const
    1).div_const 2
  convert this using 1
  · rfl
  · simp

/-- **Davenport, Ch. 12, p. 80–81 (rows 12-9, 12-10)**: in `ξ(s) = e^{A+Bs} ∏ (1 - s/ρ) e^{s/ρ}`,
`e^A = ξ(0) = 1/2` and `B = -γ/2 - 1 + ½ log 4π`. -/
@[kb "davenport1980" "Ch 12, p. 80-81"]
theorem Davenport.riemannXi_hadamard_constants {A B : ℂ}
    (h : ∀ s, riemannXi s = Complex.exp (A + B * s) *
      ∏' ρ : ZeroIndex riemannXi, (1 - s / ρ.val) * Complex.exp (s / ρ.val)) :
    Complex.exp A = 1 / 2 ∧
      B = -(Real.eulerMascheroniConstant : ℂ) / 2 - 1 + Complex.log (4 * π) / 2 := by
  constructor
  · have h0 := h 0
    simp only [zero_div, sub_zero, Complex.exp_zero, mul_one, tprod_one, mul_zero, add_zero,
      riemannXi_zero] at h0
    exact h0.symm
  · have hlog := Davenport.logDeriv_riemannXi h (s := 0) (by simp)
    simp only [zero_sub, one_div, inv_neg, neg_add_cancel, tsum_zero, add_zero] at hlog
    rw [logDeriv_apply, hasDerivAt_riemannXi_zero.deriv, riemannXi_zero,
      completedRiemannZeta₀_zero] at hlog
    rw [← hlog]
    ring

/-! ### Growth on the real axis: `ξ` is not of exponential type -/

lemma one_le_norm_riemannZeta_nat {k : ℕ} (hk : 1 < k) : 1 ≤ ‖riemannZeta k‖ := by
  rw [zeta_nat_eq_tsum_of_gt_one hk]
  have hs : Summable (fun n : ℕ ↦ 1 / (n : ℝ) ^ k) := Real.summable_one_div_nat_pow.mpr hk
  have hc : ∑' n : ℕ, 1 / (n : ℂ) ^ k = ((∑' n : ℕ, 1 / (n : ℝ) ^ k : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum]; push_cast; rfl
  rw [hc, Complex.norm_real, Real.norm_of_nonneg (tsum_nonneg fun n ↦ by positivity)]
  simpa using hs.le_tsum 1 fun j _ ↦ by positivity

/-- On the real axis, `ξ(2n + 2) ≥ n! / (2 π^{n+1})`. -/
lemma norm_riemannXi_nat_ge (n : ℕ) :
    (n.factorial : ℝ) / (2 * π ^ (n + 1)) ≤ ‖riemannXi (2 * n + 2)‖ := by
  set s : ℂ := 2 * n + 2
  have hsre : s.re = 2 * n + 2 := by simp [s]
  have h1 : s ≠ 1 := fun h ↦ by
    have := congrArg Complex.re h; rw [hsre] at this; simp at this; linarith [n.cast_nonneg (α := ℝ)]
  have h2 : ∀ m : ℕ, s ≠ -(2 * m) := fun m h ↦ by
    have := congrArg Complex.re h; rw [hsre] at this; simp at this
    linarith [n.cast_nonneg (α := ℝ), m.cast_nonneg (α := ℝ)]
  rw [riemannXi_eq h1 h2]
  have hs2 : s / 2 = (n : ℂ) + 1 := by simp only [s]; ring
  have hΓ : Complex.Gamma (s / 2) = n.factorial := by rw [hs2, Complex.Gamma_nat_eq_factorial]
  have hpi : ‖(π : ℂ) ^ (-s / 2)‖ = (π ^ (n + 1))⁻¹ := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    have : (-s / 2).re = -((n : ℝ) + 1) := by simp [s]; ring
    rw [this, Real.rpow_neg Real.pi_pos.le]
    norm_cast
  have hsz : s = ((2 * n + 2 : ℕ) : ℂ) := by simp [s]
  have hz : 1 ≤ ‖riemannZeta s‖ := by
    rw [hsz]; exact one_le_norm_riemannZeta_nat (by omega)
  have hsn : 2 ≤ ‖s‖ := by
    rw [hsz, Complex.norm_natCast]; norm_cast; omega
  have hs1 : 1 ≤ ‖s - 1‖ := by
    have : s - 1 = ((2 * n + 1 : ℕ) : ℂ) := by simp [s]; ring
    rw [this, Complex.norm_natCast]; norm_cast; omega
  simp only [norm_mul, hΓ, hpi, Complex.norm_natCast]
  rw [norm_div, norm_one, Complex.norm_ofNat]
  have hfac : (0 : ℝ) ≤ n.factorial := by positivity
  have hπ : 0 < π ^ (n + 1) := by positivity
  rw [div_le_iff₀ (by positivity)]
  calc (n.factorial : ℝ) ≤ 2 * n.factorial := by linarith
    _ = 1 / 2 * 2 * 1 * (π ^ (n + 1))⁻¹ * n.factorial * 1 * (2 * π ^ (n + 1)) := by
        field_simp
    _ ≤ 1 / 2 * ‖s‖ * ‖s - 1‖ * (π ^ (n + 1))⁻¹ * n.factorial * ‖riemannZeta s‖ *
          (2 * π ^ (n + 1)) := by gcongr

/-- **Davenport, Ch. 12, p. 79 (row 12-4)**: the growth bound (2) is essentially best possible on
the real axis: `ξ` is not of exponential type, i.e. there are no `C`, `R₀` with
`|ξ(s)| ≤ e^{C|s|}` for `|s| ≥ R₀`. -/
@[kb "davenport1980" "Ch 12, p. 79"]
theorem Davenport.riemannXi_not_exponential_type :
    ¬ ∃ C R₀ : ℝ, ∀ s : ℂ, R₀ ≤ ‖s‖ → ‖riemannXi s‖ ≤ Real.exp (C * ‖s‖) := by
  rintro ⟨C, R₀, hC⟩
  set D := |C|
  set q : ℝ := π * Real.exp (2 * D)
  set c : ℝ := 2 * π * Real.exp (2 * D)
  have hc : 0 < c := by positivity
  have hlim := FloorSemiring.tendsto_pow_div_factorial_atTop q
  have hev := hlim.eventually (gt_mem_nhds (inv_pos.mpr hc))
  obtain ⟨N, hN⟩ := (hev.and (eventually_ge_atTop ⌈R₀⌉₊)).exists_forall_of_atTop
  obtain ⟨hlt, hR⟩ := hN N le_rfl
  have hsn : ‖(2 * (N : ℂ) + 2)‖ = 2 * N + 2 := by
    rw [show (2 * (N : ℂ) + 2) = ((2 * N + 2 : ℕ) : ℂ) by push_cast; ring, Complex.norm_natCast]
    push_cast; ring
  have hR₀ : R₀ ≤ ‖(2 * (N : ℂ) + 2)‖ := by
    rw [hsn]
    have := Nat.le_ceil R₀
    have : (⌈R₀⌉₊ : ℝ) ≤ N := by exact_mod_cast hR
    linarith [N.cast_nonneg (α := ℝ)]
  have hup := hC _ hR₀
  have hlow := norm_riemannXi_nat_ge N
  rw [hsn] at hup
  have hexp : Real.exp (C * (2 * N + 2)) ≤ Real.exp (2 * D) * Real.exp (2 * D) ^ N := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have : C ≤ D := le_abs_self C
    have : (0 : ℝ) ≤ 2 * N + 2 := by positivity
    nlinarith
  have hfac : (N.factorial : ℝ) ≤ c * q ^ N := by
    have h := hlow.trans (hup.trans hexp)
    rw [div_le_iff₀ (by positivity)] at h
    calc (N.factorial : ℝ) ≤ Real.exp (2 * D) * Real.exp (2 * D) ^ N * (2 * π ^ (N + 1)) := h
      _ = c * q ^ N := by simp only [c, q]; rw [mul_pow, pow_succ]; ring
  have hpos : (0 : ℝ) < N.factorial := by positivity
  have : c⁻¹ ≤ q ^ N / N.factorial := by
    rw [le_div_iff₀ hpos, inv_mul_le_iff₀ hc]; linarith
  linarith

/-- **Davenport, Ch. 12, p. 79 (row 12-4)**: `ξ` has order exactly `1`. -/
@[kb "davenport1980" "Ch 12, p. 79"]
theorem Davenport.entireOrder_riemannXi : entireOrder riemannXi = 1 := by
  refine le_antisymm Davenport.entireOrder_riemannXi_le_one (not_lt.mp fun hlt ↦ ?_)
  obtain ⟨ρ, hρ1, hρ⟩ : ∃ ρ : ℝ≥0, (ρ : ℝ≥0∞) < 1 ∧ entireOrder riemannXi ≤ ρ :=
    ⟨(entireOrder riemannXi).toNNReal, by
      rwa [ENNReal.coe_toNNReal (ne_top_of_lt hlt)], ENNReal.coe_toNNReal (ne_top_of_lt hlt) ▸ le_rfl⟩
  have hρ1' : (ρ : ℝ) < 1 := by exact_mod_cast hρ1
  have hev := eventually_norm_le_exp_of_entireOrder_le hρ (a := 1) hρ1'
  obtain ⟨R₀, hR₀⟩ := (Metric.hasBasis_cobounded_compl_closedBall (0 : ℂ)).eventually_iff.mp hev
    |>.imp fun r hr ↦ hr.2
  refine Davenport.riemannXi_not_exponential_type ⟨1, R₀ + 1, fun s hs ↦ ?_⟩
  have : s ∈ (Metric.closedBall (0 : ℂ) R₀)ᶜ := by
    simp only [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le]; linarith
  simpa using hR₀ this

/-- **Davenport, Ch. 12, p. 80, (4), (5) (row 12-5)**: `ξ` has infinitely many zeros `ρ`; they are
the nontrivial zeros of `ζ`, in the critical strip `0 < σ < 1`; `∑ |ρ|^{-1-ε}` converges for every
`ε > 0`, while `∑ |ρ|⁻¹` diverges. -/
@[kb "davenport1980" "Ch 12, p. 80"]
theorem Davenport.riemannXi_zeros :
    Infinite (ZeroIndex riemannXi) ∧
    (∀ ρ : ZeroIndex riemannXi, riemannZeta ρ.val = 0 ∧ 0 < ρ.val.re ∧ ρ.val.re < 1) ∧
    (∀ ε : ℝ, 0 < ε → Summable fun ρ : ZeroIndex riemannXi ↦ ‖ρ.val‖ ^ (-1 - ε)) ∧
    ¬ Summable fun ρ : ZeroIndex riemannXi ↦ ‖ρ.val‖⁻¹ := by
  have hsum := (Davenport.entire_order_one_summary differentiable_riemannXi (by simp)
    Davenport.entireOrder_riemannXi_le_one)
  have hdiv : ¬ Summable fun ρ : ZeroIndex riemannXi ↦ ‖ρ.val‖⁻¹ := fun h ↦ by
    obtain ⟨C, hC⟩ := hsum.2.2 h
    exact Davenport.riemannXi_not_exponential_type ⟨C, 1, hC⟩
  refine ⟨?_, fun ρ ↦ ?_, hsum.2.1, hdiv⟩
  · by_contra hfin
    rw [not_infinite_iff_finite] at hfin
    exact hdiv (Summable.of_finite)
  · exact riemannXi_eq_zero_iff.mp (ZeroIndex.apply_val_eq_zero (differentiable_riemannXi.analyticAt _))

/-! ### Partial fractions for `ζ'/ζ` (Davenport, Ch. 12, (8)) -/

/-- `ξ(w) = (w - 1) π^{-w/2} Γ(w/2 + 1) ζ(w)` (from `½ s Γ(s/2) = Γ(s/2 + 1)`). -/
lemma riemannXi_eq_mul_Gamma_add_one {w : ℂ} (hw1 : w ≠ 1) (hΓ : Complex.Gamma (w / 2 + 1) ≠ 0) :
    riemannXi w = (w - 1) * (π : ℂ) ^ (-w / 2) * Complex.Gamma (w / 2 + 1) * riemannZeta w := by
  rw [riemannXi, riemannZeta_eq_mul_completedRiemannZeta₀]
  have h1w : (1 : ℂ) - w ≠ 0 := sub_ne_zero.mpr (Ne.symm hw1)
  have hw1' : w - 1 ≠ 0 := sub_ne_zero.mpr hw1
  have hπ : (π : ℂ) ^ (-w / 2) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]; push Not; intro h
    exact absurd h (by exact_mod_cast Real.pi_ne_zero)
  generalize Complex.Gamma (w / 2 + 1) = G at *
  generalize (π : ℂ) ^ (-w / 2) = P at *
  field_simp
  ring

/-- **Davenport, Ch. 12, (8) (row 12-7)**: for `s ≠ 1` with `ζ(s) ≠ 0`,
`ζ'(s)/ζ(s) = B - 1/(s - 1) + ½ log π - ½ Γ'(s/2 + 1)/Γ(s/2 + 1) + ∑_ρ (1/(s - ρ) + 1/ρ)`,
where `B` is the constant of the Hadamard product of `ξ` and `ρ` runs over the nontrivial zeros of
`ζ` with multiplicity. -/
@[kb "davenport1980" "Ch 12, p. 80"]
theorem Davenport.logDeriv_riemannZeta {A B : ℂ}
    (h : ∀ s, riemannXi s = Complex.exp (A + B * s) *
      ∏' ρ : ZeroIndex riemannXi, (1 - s / ρ.val) * Complex.exp (s / ρ.val))
    {s : ℂ} (hs1 : s ≠ 1) (hz : riemannZeta s ≠ 0) :
    deriv riemannZeta s / riemannZeta s =
      B - 1 / (s - 1) + Complex.log π / 2 -
        deriv Complex.Gamma (s / 2 + 1) / (2 * Complex.Gamma (s / 2 + 1)) +
        ∑' ρ : ZeroIndex riemannXi, (1 / (s - ρ.val) + 1 / ρ.val) := by
  -- `s/2 + 1` is not a pole of `Γ` (those `s` are trivial zeros of `ζ`)
  have hpole : ∀ m : ℕ, s / 2 + 1 ≠ -m := by
    intro m hm
    have : s = -2 * ((m : ℂ) + 1) := by linear_combination 2 * hm
    exact hz (this ▸ riemannZeta_neg_two_mul_nat_add_one m)
  have hΓs : Complex.Gamma (s / 2 + 1) ≠ 0 := Complex.Gamma_ne_zero hpole
  have hπ0 : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hπs : (π : ℂ) ^ (-s / 2) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]; push Not; intro h; exact absurd h hπ0
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  -- derivatives of the factors
  have hdΓ : HasDerivAt (fun w ↦ Complex.Gamma (w / 2 + 1))
      (deriv Complex.Gamma (s / 2 + 1) * (1 / 2)) s := by
    have hin : HasDerivAt (fun w : ℂ ↦ w / 2 + 1) (1 / 2) s := by
      simpa using ((hasDerivAt_id s).div_const 2).add_const 1
    exact (Complex.differentiableAt_Gamma _ hpole).hasDerivAt.comp s hin
  have hdπ : HasDerivAt (fun w : ℂ ↦ (π : ℂ) ^ (-w / 2))
      ((π : ℂ) ^ (-s / 2) * Complex.log π * (-1 / 2)) s := by
    have hin : HasDerivAt (fun w : ℂ ↦ -w / 2) (-1 / 2) s := by
      simpa using ((hasDerivAt_id s).neg).div_const 2
    exact hin.const_cpow (Or.inl hπ0)
  have hdζ : HasDerivAt riemannZeta (deriv riemannZeta s) s :=
    (differentiableAt_riemannZeta hs1).hasDerivAt
  set g : ℂ → ℂ := fun w ↦ (w - 1) * (π : ℂ) ^ (-w / 2) * Complex.Gamma (w / 2 + 1) *
    riemannZeta w
  have hdg : HasDerivAt g _ s := ((((hasDerivAt_id s).sub_const 1).mul hdπ).mul hdΓ).mul hdζ
  -- `ξ = g` near `s`
  have hev : riemannXi =ᶠ[𝓝 s] g := by
    have hc : ContinuousAt (fun w ↦ Complex.Gamma (w / 2 + 1)) s := hdΓ.continuousAt
    filter_upwards [hc.eventually_ne hΓs, isOpen_ne.mem_nhds hs1] with w hw hw1
    exact riemannXi_eq_mul_Gamma_add_one hw1 hw
  have hξs : riemannXi s ≠ 0 := by
    rw [hev.eq_of_nhds]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero hs1' hπs) hΓs) hz
  have hlog := Davenport.logDeriv_riemannXi h hξs
  rw [logDeriv_apply, hev.deriv_eq, hev.eq_of_nhds, hdg.deriv] at hlog
  set T := ∑' ρ : ZeroIndex riemannXi, (1 / (s - ρ.val) + 1 / ρ.val)
  rw [show B - 1 / (s - 1) + Complex.log π / 2 -
      deriv Complex.Gamma (s / 2 + 1) / (2 * Complex.Gamma (s / 2 + 1)) + T =
      (B + T) - 1 / (s - 1) + Complex.log π / 2 -
      deriv Complex.Gamma (s / 2 + 1) / (2 * Complex.Gamma (s / 2 + 1)) by ring, ← hlog]
  simp only [g, id, Pi.mul_apply]
  generalize Complex.Gamma (s / 2 + 1) = G at *
  generalize (π : ℂ) ^ (-s / 2) = P at *
  generalize riemannZeta s = Z at *
  field_simp
  ring

end NTKB
