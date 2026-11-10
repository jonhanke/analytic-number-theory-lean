/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Davenport.Hadamard.XiSum
import NTKB.Analytic.Davenport.Zeros.Digamma

/-!
# The real part of `ζ'/ζ` from the Hadamard product

**Davenport, Ch. 13, pp. 85-86 and Ch. 15, p. 98.** From the partial fraction formula (8) of
Chapter 12 and `Re B = -∑ Re(1/ρ)` (Chapter 12, (11)):
`-Re ζ'/ζ(s) = Re 1/(s - 1) - ½ log π + ½ Re ψ(s/2 + 1) - ∑_ρ Re 1/(s - ρ)`,
and for `1 < σ ≤ 2` (Davenport's (D)):
`-Re ζ'/ζ(s) ≤ Re 1/(s - 1) + A log(|t| + 2) - ∑_ρ Re 1/(s - ρ)`, every term of the sum positive.
-/

open Filter Topology Complex Set
open scoped Real

namespace NTKB

/-- Every zero of an entire function `f` with `f 0 ≠ 0` occurs in `ZeroIndex f`. -/
lemma exists_zeroIndex_val_eq {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hf0 : f 0 ≠ 0) {z : ℂ}
    (hz : f z = 0) : ∃ i : ZeroIndex f, i.val = z := by
  have han : AnalyticOnNhd ℂ f univ := fun w _ ↦ hf.analyticAt w
  have hne : analyticOrderAt f z ≠ ⊤ := by
    have := han.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ (mem_univ 0)
      (mem_univ z) (by
        rw [(hf.analyticAt 0).analyticOrderAt_eq_zero.mpr hf0]
        exact ENat.zero_ne_top)
    exact this
  have hpos : 0 < analyticOrderNatAt f z := by
    rw [analyticOrderNatAt]
    have h0 : analyticOrderAt f z ≠ 0 := by
      rw [ne_eq, (hf.analyticAt z).analyticOrderAt_eq_zero]; exact not_not.mpr hz
    rcases ENat.ne_top_iff_exists.mp hne with ⟨n, hn⟩
    rw [← hn] at h0 ⊢
    simp only [ENat.toNat_natCast]
    exact Nat.pos_of_ne_zero (by exact_mod_cast h0)
  exact ⟨⟨z, ⟨0, hpos⟩⟩, rfl⟩

lemma riemannXi_zero_mem (ρ : ZeroIndex riemannXi) : riemannZeta ρ.val = 0 ∧ 0 < ρ.val.re ∧
    ρ.val.re < 1 :=
  riemannXi_eq_zero_iff.mp (ZeroIndex.apply_val_eq_zero (differentiable_riemannXi.analyticAt _))

/-- A nontrivial zero of `ζ` (in `0 < σ`) is a zero of `ξ`, so it occurs in `ZeroIndex riemannXi`. -/
lemma exists_zeroIndex_riemannXi {s : ℂ} (hs : riemannZeta s = 0) (h0 : 0 < s.re) :
    ∃ ρ : ZeroIndex riemannXi, ρ.val = s := by
  have h1 : s.re < 1 := by
    by_contra h
    exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp h) hs
  exact exists_zeroIndex_val_eq differentiable_riemannXi (by simp)
    (riemannXi_eq_zero_iff.mpr ⟨hs, h0, h1⟩)

lemma summable_re_inv_riemannXi_zeros :
    Summable fun ρ : ZeroIndex riemannXi ↦ (1 / ρ.val).re := by
  obtain ⟨ha, ha0⟩ := summable_riemannXi_zeros
  refine Summable.of_norm_bounded ha fun ρ ↦ ?_
  have h := riemannXi_zero_mem ρ
  have hρ : ρ.val ≠ 0 := ha0 ρ
  rw [Real.norm_eq_abs, one_div, Complex.inv_re, abs_div, abs_of_pos h.2.1,
    abs_of_pos (Complex.normSq_pos.mpr hρ), ← Complex.sq_norm, inv_pow, div_eq_mul_inv]
  exact mul_le_of_le_one_left (by positivity) h.2.2.le

lemma riemannXi_zero_ne {s : ℂ} (hz : riemannZeta s ≠ 0) (ρ : ZeroIndex riemannXi) :
    ρ.val ≠ s := fun h ↦ hz (h ▸ (riemannXi_zero_mem ρ).1)

lemma summable_re_inv_sub_riemannXi_zeros {s : ℂ} (hs : ∀ ρ : ZeroIndex riemannXi, ρ.val ≠ s) :
    Summable fun ρ : ZeroIndex riemannXi ↦ (1 / (s - ρ.val)).re := by
  obtain ⟨ha, ha0⟩ := summable_riemannXi_zeros
  have h := ((summable_inv_sub_add_inv ha ha0 hs).mapL Complex.reCLM).sub
    summable_re_inv_riemannXi_zeros
  refine h.congr fun ρ ↦ ?_
  simp

/-- For `Re s > Re ρ`: `Re 1/(s - ρ) = (σ - β)/|s - ρ|² > 0`. -/
lemma re_one_div_sub_pos {s ρ : ℂ} (h : ρ.re < s.re) : 0 < (1 / (s - ρ)).re := by
  have hne : s - ρ ≠ 0 := fun h' ↦ by
    have := congrArg Complex.re h'; simp at this; linarith
  rw [one_div, Complex.inv_re]
  exact div_pos (by simp; linarith) (Complex.normSq_pos.mpr hne)

lemma re_log_pi : (Complex.log (π : ℂ)).re = Real.log π := by
  rw [← Complex.ofReal_log Real.pi_pos.le, Complex.ofReal_re]

/-- **Real part of the partial fraction formula** (Davenport, Ch. 13, p. 85, from (8) and (11)
of Ch. 12): for `s ≠ 1` with `ζ(s) ≠ 0`,
`-Re ζ'/ζ(s) = Re 1/(s - 1) - ½ log π + ½ Re ψ(s/2 + 1) - ∑_ρ Re 1/(s - ρ)`,
the sum over the nontrivial zeros with multiplicity (absolutely convergent). -/
@[kb "davenport1980" "Ch 13, p. 85"]
theorem Davenport.neg_re_logDeriv_riemannZeta_eq {s : ℂ} (hs1 : s ≠ 1) (hz : riemannZeta s ≠ 0) :
    -(deriv riemannZeta s / riemannZeta s).re =
      (1 / (s - 1)).re - Real.log π / 2 + (Complex.digamma (s / 2 + 1)).re / 2 -
        ∑' ρ : ZeroIndex riemannXi, (1 / (s - ρ.val)).re := by
  obtain ⟨A, B, h⟩ := Davenport.riemannXi_hadamard
  have hB := Davenport.riemannXi_B_eq_neg_tsum h
  rw [Davenport.logDeriv_riemannZeta h hs1 hz]
  obtain ⟨ha, ha0⟩ := summable_riemannXi_zeros
  have hS := summable_inv_sub_add_inv ha ha0 (riemannXi_zero_ne hz)
  have hS1 := summable_re_inv_sub_riemannXi_zeros (riemannXi_zero_ne hz)
  have hS2 := summable_re_inv_riemannXi_zeros
  have hre : (∑' ρ : ZeroIndex riemannXi, (1 / (s - ρ.val) + 1 / ρ.val)).re =
      ∑' ρ : ZeroIndex riemannXi, (1 / (s - ρ.val)).re +
        ∑' ρ : ZeroIndex riemannXi, (1 / ρ.val).re := by
    rw [Complex.re_tsum hS, ← hS1.tsum_add hS2]
    exact tsum_congr fun ρ ↦ by simp
  have hd : deriv Complex.Gamma (s / 2 + 1) / (2 * Complex.Gamma (s / 2 + 1)) =
      Complex.digamma (s / 2 + 1) / 2 := by
    rw [Complex.digamma_def, logDeriv_apply]; ring
  rw [hd]
  simp only [Complex.add_re, Complex.sub_re, hre, hB, Complex.ofReal_re, Complex.div_ofNat_re,
    re_log_pi]
  ring

/-- `‖ψ(w)‖ ≤ 4 + 2 log(‖w‖ + 1)` for `Re w ≥ 0`, `‖w‖ ≥ 1`. -/
lemma norm_digamma_le {w : ℂ} (hw : 0 ≤ w.re) (hw1 : 1 ≤ ‖w‖) :
    ‖Complex.digamma w‖ ≤ 4 + 2 * Real.log (‖w‖ + 1) := by
  have hw0 : w ≠ 0 := fun h ↦ by simp [h] at hw1; linarith
  have h := norm_digamma_add_inv_le hw hw0
  have h1 : ‖1 / w‖ ≤ 1 := by
    rw [norm_div, norm_one]; exact (div_le_one (by linarith)).mpr hw1
  calc ‖Complex.digamma w‖ = ‖(Complex.digamma w + 1 / w) - 1 / w‖ := by ring_nf
    _ ≤ ‖Complex.digamma w + 1 / w‖ + ‖1 / w‖ := norm_sub_le _ _
    _ ≤ 4 + 2 * Real.log (‖w‖ + 1) := by linarith

lemma log_two_gt_two_thirds : 2 / 3 < Real.log 2 := by
  have := Real.log_two_gt_d9; linarith

/-- The Gamma term: `½ Re ψ(s/2 + 1) ≤ 5 log(|t| + 2)` for `0 ≤ σ ≤ 2`. -/
lemma re_digamma_half_le {s : ℂ} (h0 : 0 ≤ s.re) (h2 : s.re ≤ 2) :
    (Complex.digamma (s / 2 + 1)).re / 2 ≤ 5 * Real.log (|s.im| + 2) := by
  set w := s / 2 + 1
  have hwre : w.re = s.re / 2 + 1 := by simp [w]
  have hw1 : 1 ≤ ‖w‖ := by
    have := Complex.re_le_norm w; linarith
  have hwn : ‖w‖ ≤ |s.im| + 2 := by
    calc ‖w‖ ≤ ‖s / 2‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ = ‖s‖ / 2 + 1 := by simp
      _ ≤ (|s.re| + |s.im|) / 2 + 1 := by
          gcongr; exact Complex.norm_le_abs_re_add_abs_im s
      _ ≤ |s.im| + 2 := by rw [abs_of_nonneg h0]; linarith [abs_nonneg s.im]
  have hT : 0 ≤ |s.im| := abs_nonneg _
  have hlog2 : Real.log 2 ≤ Real.log (|s.im| + 2) := Real.log_le_log two_pos (by linarith)
  have hlogw : Real.log (‖w‖ + 1) ≤ 2 * Real.log (|s.im| + 2) := by
    rw [show (2 : ℝ) * Real.log (|s.im| + 2) = ((2 : ℕ) : ℝ) * Real.log (|s.im| + 2) by norm_num,
      ← Real.log_pow]
    exact Real.log_le_log (by linarith) (by nlinarith)
  have hψ := norm_digamma_le (by rw [hwre]; linarith) hw1
  have := Complex.re_le_norm (Complex.digamma w)
  have := log_two_gt_two_thirds
  linarith

/-- **Davenport, Ch. 13, p. 85, (D) (row 13-9)**, in the uniform form
`-Re ζ'/ζ(s) ≤ Re 1/(s - 1) + 5 log(|t| + 2) - ∑_ρ Re 1/(s - ρ)` for `1 < σ ≤ 2`;
each term `Re 1/(s - ρ)` of the sum is positive (`re_one_div_sub_pos`). -/
@[kb "davenport1980" "Ch 13, p. 85"]
theorem Davenport.neg_re_logDeriv_riemannZeta_le {s : ℂ} (h1 : 1 < s.re) (h2 : s.re ≤ 2) :
    -(deriv riemannZeta s / riemannZeta s).re ≤
      (1 / (s - 1)).re + 5 * Real.log (|s.im| + 2) -
        ∑' ρ : ZeroIndex riemannXi, (1 / (s - ρ.val)).re := by
  have hs1 : s ≠ 1 := fun h ↦ by rw [h] at h1; simp at h1
  have hz := riemannZeta_ne_zero_of_one_lt_re h1
  rw [Davenport.neg_re_logDeriv_riemannZeta_eq hs1 hz]
  have := re_digamma_half_le (by linarith) h2
  have hπ : 0 ≤ Real.log π := Real.log_nonneg (by linarith [Real.pi_gt_three])
  linarith

end NTKB
