/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Davenport.Zeros.Digamma
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-!
# `Re ψ(w) = log |w| + O(1/(1 + |Im w|))`

The form of Stirling's formula for the digamma function used for `N(T)` (Davenport, Ch. 15,
p. 98, where Stirling's formula gives `Im log Γ(1/4 + iT/2)`; here its derivative in `T` is
estimated instead): for `Re w ≥ 2`, `|Re ψ(w) - log |w|| ≤ 2/(1 + |Im w|)`
(`abs_re_digamma_sub_log_le`).

Proof: from the digamma series (Ch. 12, p. 80),
`Re ψ(w) - log |w| = ∑_{k ≥ 0} (log |1 + 1/(w + k)| - Re 1/(w + k))` (telescoping, with
`H_N - log N → γ`), and each term is at most `|w + k|^{-2}` in absolute value.
-/

open Filter Topology Complex Set

namespace NTKB

/-- Telescoping bound: for `c ≥ 1`, `∑_{k < n} 1/(k + c)² ≤ 1/(c - 1/2)`. -/
lemma sum_range_inv_add_sq_le {c : ℝ} (hc : 1 ≤ c) (n : ℕ) :
    ∑ k ∈ Finset.range n, 1 / ((k : ℝ) + c) ^ 2 ≤ 1 / (c - 1 / 2) := by
  have key : ∀ n : ℕ, ∑ k ∈ Finset.range n, 1 / ((k : ℝ) + c) ^ 2 ≤
      1 / (c - 1 / 2) - 1 / (n + c - 1 / 2) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ]
      set x : ℝ := (n : ℝ) + c with hx
      have hx1 : 1 ≤ x := by have := n.cast_nonneg (α := ℝ); linarith
      have e : ((n + 1 : ℕ) : ℝ) + c - 1 / 2 = x + 1 / 2 := by push_cast; ring
      have e' : (n : ℝ) + c - 1 / 2 = x - 1 / 2 := by ring
      rw [e]
      rw [e'] at ih
      have h1 : x - 1 / 2 ≠ 0 := by linarith
      have h2 : x + 1 / 2 ≠ 0 := by linarith
      have h3 : 1 / (x - 1 / 2) - 1 / (x + 1 / 2) = 1 / ((x - 1 / 2) * (x + 1 / 2)) := by
        rw [div_sub_div _ _ h1 h2]; congr 1; ring
      have h4 : 1 / x ^ 2 ≤ 1 / ((x - 1 / 2) * (x + 1 / 2)) :=
        one_div_le_one_div_of_le (by nlinarith) (by nlinarith)
      linarith
  have hn : 0 ≤ 1 / ((n : ℝ) + c - 1 / 2) := by
    have : (0 : ℝ) < n + c - 1 / 2 := by have := n.cast_nonneg (α := ℝ); linarith
    positivity
  linarith [key n]

lemma summable_inv_add_sq {c : ℝ} (hc : 1 ≤ c) : Summable fun k : ℕ ↦ 1 / ((k : ℝ) + c) ^ 2 :=
  summable_of_sum_range_le (fun k ↦ by positivity) (sum_range_inv_add_sq_le hc)

lemma tsum_inv_add_sq_le {c : ℝ} (hc : 1 ≤ c) :
    ∑' k : ℕ, 1 / ((k : ℝ) + c) ^ 2 ≤ 1 / (c - 1 / 2) :=
  Real.tsum_le_of_sum_range_le (fun k ↦ by positivity) (sum_range_inv_add_sq_le hc)

/-- `|log |1 + z| - Re z| ≤ |z|²` for `z = 1/v`, `Re v ≥ 2`. -/
lemma abs_log_norm_one_add_inv_sub_le {v : ℂ} (hv : 2 ≤ v.re) :
    |Real.log ‖1 + 1 / v‖ - (1 / v).re| ≤ 1 / ‖v‖ ^ 2 := by
  have hvn : 2 ≤ ‖v‖ := hv.trans (Complex.re_le_norm v)
  set z := 1 / v with hz
  have hzn : ‖z‖ = 1 / ‖v‖ := by rw [hz, norm_div, norm_one]
  have hz2 : ‖z‖ ≤ 1 / 2 := by
    rw [hzn]; exact one_div_le_one_div_of_le (by norm_num) hvn
  have hz0 : 0 ≤ ‖z‖ := norm_nonneg _
  have hlog := Complex.norm_log_one_add_sub_self_le (z := z) (by linarith)
  have hre : Real.log ‖1 + z‖ - z.re = (Complex.log (1 + z) - z).re := by
    rw [Complex.sub_re, Complex.log_re]
  rw [hre]
  refine (Complex.abs_re_le_norm _).trans (hlog.trans ?_)
  have hinv : (1 - ‖z‖)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
  have : ‖z‖ ^ 2 * (1 - ‖z‖)⁻¹ / 2 ≤ ‖z‖ ^ 2 := by
    have h0 : 0 ≤ ‖z‖ ^ 2 := by positivity
    nlinarith
  refine this.trans (le_of_eq ?_)
  rw [hzn, div_pow, one_pow]

/-- `1/|w + k|² ≤ 2/(k + 2 + |Im w|)²` for `Re w ≥ 2`. -/
lemma inv_norm_add_nat_sq_le {w : ℂ} (hw : 2 ≤ w.re) (k : ℕ) :
    1 / ‖w + k‖ ^ 2 ≤ 2 * (1 / ((k : ℝ) + (2 + |w.im|)) ^ 2) := by
  have hre : (w + k).re = w.re + k := by simp
  have him : (w + k).im = w.im := by simp
  have hsq : ‖w + k‖ ^ 2 = (w.re + k) ^ 2 + w.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hre, him]; ring
  have hk : (0 : ℝ) ≤ k := k.cast_nonneg
  have hpos : 0 < (k : ℝ) + (2 + |w.im|) := by positivity
  have hle : ((k : ℝ) + (2 + |w.im|)) ^ 2 ≤ 2 * ‖w + k‖ ^ 2 := by
    rw [hsq]
    have h1 : (k : ℝ) + 2 ≤ w.re + k := by linarith
    have h2 : |w.im| ^ 2 = w.im ^ 2 := sq_abs _
    have h3 : ((k : ℝ) + (2 + |w.im|)) ^ 2 ≤ (w.re + k + |w.im|) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (by linarith) 2
    have h4 : (w.re + k + |w.im|) ^ 2 ≤ 2 * ((w.re + k) ^ 2 + |w.im| ^ 2) := by
      nlinarith [sq_nonneg (w.re + k - |w.im|)]
    rw [h2] at h4
    linarith
  have hn : 0 < ‖w + k‖ ^ 2 := by nlinarith
  rw [mul_one_div, div_le_div_iff₀ hn (by positivity)]
  linarith

/-- Partial sums of the series for `Re ψ(w) - log |w|`. -/
lemma sum_range_log_norm_sub {w : ℂ} (hw : 0 < w.re) (N : ℕ) :
    ∑ k ∈ Finset.range N, (Real.log ‖1 + 1 / (w + k)‖ - (1 / (w + k)).re) =
      Real.log ‖w + N‖ - Real.log ‖w‖ - ∑ k ∈ Finset.range N, (1 / (w + k)).re := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
    have hN : w + N ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith [N.cast_nonneg (α := ℝ)]
    have hN1 : w + ((N + 1 : ℕ) : ℂ) ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this
      linarith [N.cast_nonneg (α := ℝ)]
    have e : 1 + 1 / (w + N) = (w + ((N + 1 : ℕ) : ℂ)) / (w + N) := by
      field_simp; push_cast; ring
    rw [e, norm_div, Real.log_div (norm_ne_zero_iff.mpr hN1) (norm_ne_zero_iff.mpr hN)]
    ring

/-- **The series for `Re ψ(w) - log |w|`** (for `Re w ≥ 2`). -/
lemma hasSum_re_digamma_sub_log {w : ℂ} (hw : 2 ≤ w.re) :
    HasSum (fun k : ℕ ↦ Real.log ‖1 + 1 / (w + k)‖ - (1 / (w + k)).re)
      ((Complex.digamma w).re - Real.log ‖w‖) := by
  have hw0 : 0 < w.re := by linarith
  set d : ℕ → ℝ := fun k ↦ Real.log ‖1 + 1 / (w + k)‖ - (1 / (w + k)).re with hd
  -- summability from the bound on the terms
  have hdb : ∀ k : ℕ, ‖d k‖ ≤ 2 * (1 / ((k : ℝ) + (2 + |w.im|)) ^ 2) := by
    intro k
    have h1 := abs_log_norm_one_add_inv_sub_le (v := w + k) (by simp; linarith [k.cast_nonneg (α := ℝ)])
    exact (Real.norm_eq_abs _ ▸ h1).trans (inv_norm_add_nat_sq_le hw k)
  have hds : Summable d :=
    Summable.of_norm_bounded ((summable_inv_add_sq (by linarith [abs_nonneg w.im])).mul_left 2) hdb
  -- the limit of the partial sums
  have hpole : ∀ m : ℕ, w ≠ -m := by
    intro m h; have := congrArg Complex.re h; simp at this; linarith [m.cast_nonneg (α := ℝ)]
  have hS := (summable_digamma_terms hpole).hasSum.tendsto_sum_nat
  rw [← sub_eq_iff_eq_add'.mpr (Davenport.digamma_eq_tsum hpole)] at hS
  -- `log |w + N + 1| - H_N → -γ`
  have hH := Real.tendsto_harmonic_sub_log
  have hratio : Tendsto (fun N : ℕ ↦ ‖w + ((N + 1 : ℕ) : ℂ)‖ / (N : ℝ)) atTop (𝓝 1) := by
    have h1 : Tendsto (fun N : ℕ ↦ (w + 1) / (N : ℂ)) atTop (𝓝 0) := by
      have := tendsto_const_div_atTop_nhds_zero_nat (‖w + 1‖)
      rw [tendsto_zero_iff_norm_tendsto_zero]
      refine this.congr fun N ↦ ?_
      rw [norm_div, Complex.norm_natCast]
    have h2 : Tendsto (fun N : ℕ ↦ ‖(w + 1) / (N : ℂ) + 1‖) atTop (𝓝 1) := by
      have := ((h1.add_const 1).norm)
      simpa using this
    refine h2.congr' ?_
    filter_upwards [eventually_ne_atTop 0] with N hN
    have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN
    have : (w + 1) / (N : ℂ) + 1 = (w + ((N + 1 : ℕ) : ℂ)) / (N : ℂ) := by
      field_simp; push_cast; ring
    rw [this, norm_div, Complex.norm_natCast]
  have hlog : Tendsto (fun N : ℕ ↦ Real.log ‖w + ((N + 1 : ℕ) : ℂ)‖ - Real.log N) atTop (𝓝 0) := by
    have := (Real.continuousAt_log one_ne_zero).tendsto.comp hratio
    rw [Real.log_one] at this
    refine this.congr' ?_
    filter_upwards [eventually_ne_atTop 0] with N hN
    have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN
    have hw' : ‖w + ((N + 1 : ℕ) : ℂ)‖ ≠ 0 := by
      rw [norm_ne_zero_iff]; intro h; have := congrArg Complex.re h; simp at this
      linarith [N.cast_nonneg (α := ℝ)]
    simp only [Function.comp]
    rw [Real.log_div hw' hN']
  -- assemble
  have hP : Tendsto (fun N : ℕ ↦ ∑ k ∈ Finset.range (N + 1), d k) atTop
      (𝓝 ((Complex.digamma w).re - Real.log ‖w‖)) := by
    have hre := (Complex.continuous_re.tendsto _).comp hS
    have hall := (hlog.sub hH).add hre
    have hlim : (0 - Real.eulerMascheroniConstant +
        (Complex.digamma w - (-(Real.eulerMascheroniConstant : ℂ) - 1 / w)).re) -
        Real.log ‖w‖ - (1 / w).re = (Complex.digamma w).re - Real.log ‖w‖ := by
      simp only [Complex.sub_re, Complex.neg_re, Complex.ofReal_re]
      ring
    rw [← hlim]
    refine (hall.sub_const _ |>.sub_const _).congr fun N ↦ ?_
    simp only [Function.comp, hd]
    rw [sum_range_log_norm_sub hw0, Finset.sum_range_succ']
    have hharm : (harmonic N : ℝ) = ∑ k ∈ Finset.range N, 1 / ((k : ℝ) + 1) := by
      rw [harmonic]; push_cast; simp [one_div]
    have hsum : (∑ k ∈ Finset.range N, (1 / ((k : ℂ) + 1) - 1 / (w + k + 1))).re =
        ∑ k ∈ Finset.range N, 1 / ((k : ℝ) + 1) -
          ∑ k ∈ Finset.range N, (1 / (w + ((k + 1 : ℕ) : ℂ))).re := by
      rw [Complex.re_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [Complex.sub_re]
      congr 1
      · rw [show (1 : ℂ) / ((k : ℂ) + 1) = ((1 / ((k : ℝ) + 1) : ℝ) : ℂ) by push_cast; rfl,
          Complex.ofReal_re]
      · push_cast; ring_nf
    rw [hsum, hharm]
    push_cast
    ring_nf
  have h1 := hds.hasSum.tendsto_sum_nat
  have h2 := h1.comp (tendsto_add_atTop_nat 1)
  have := tendsto_nhds_unique h2 hP
  rw [← this]
  exact hds.hasSum

/-- **Stirling's formula for `Re ψ`**: for `Re w ≥ 2`, `|Re ψ(w) - log |w|| ≤ 2/(1 + |Im w|)`. -/
theorem abs_re_digamma_sub_log_le {w : ℂ} (hw : 2 ≤ w.re) :
    |(Complex.digamma w).re - Real.log ‖w‖| ≤ 2 / (1 + |w.im|) := by
  have hH := hasSum_re_digamma_sub_log hw
  have hc : 1 ≤ 2 + |w.im| := by linarith [abs_nonneg w.im]
  have hs := summable_inv_add_sq hc
  have hb : ∀ k : ℕ, ‖Real.log ‖1 + 1 / (w + k)‖ - (1 / (w + k)).re‖ ≤
      2 * (1 / ((k : ℝ) + (2 + |w.im|)) ^ 2) := by
    intro k
    have h1 := abs_log_norm_one_add_inv_sub_le (v := w + k)
      (by simp; linarith [k.cast_nonneg (α := ℝ)])
    exact (Real.norm_eq_abs _ ▸ h1).trans (inv_norm_add_nat_sq_le hw k)
  have hds : Summable fun k : ℕ ↦ Real.log ‖1 + 1 / (w + k)‖ - (1 / (w + k)).re :=
    Summable.of_norm_bounded (hs.mul_left 2) hb
  rw [← hH.tsum_eq, ← Real.norm_eq_abs]
  refine (norm_tsum_le_tsum_norm hds.norm).trans ?_
  refine (Summable.tsum_le_tsum hb hds.norm (hs.mul_left 2)).trans ?_
  rw [tsum_mul_left]
  have := tsum_inv_add_sq_le hc
  have h3 : 1 / (2 + |w.im| - 1 / 2) ≤ 1 / (1 + |w.im|) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  calc 2 * ∑' k : ℕ, 1 / ((k : ℝ) + (2 + |w.im|)) ^ 2 ≤ 2 * (1 / (1 + |w.im|)) := by
        gcongr; exact this.trans h3
    _ = 2 / (1 + |w.im|) := by ring

end NTKB
