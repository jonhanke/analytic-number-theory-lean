/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Apostol.Averages.PowerSums
import NTKB.Analytic.Apostol.Zeta.Alternating

/-!
# `∑_{n ≤ x} n^{-s} = x^{1-s}/(1-s) + ζ(s) + O(x^{-s})` (Apostol, Theorem 3.2 (b))

For real `s > 0`, `s ≠ 1`. The constant: `u(N) = ∑_{n ≤ N} n^{-s} - N^{1-s}/(1-s)` decreases
(`u(N) - u(N+1) = ∫_N^{N+1} (t^{-s} - (N+1)^{-s}) dt ∈ [0, N^{-s} - (N+1)^{-s}]`), so it converges to
some `C` with `|u(N) - C| ≤ N^{-s}`. Apostol identifies `C` with `ζ(s)` through his definition of
`ζ(s)` for `0 < s < 1` (by this very formula); with Mathlib's `riemannZeta` (analytic
continuation) we identify it through the alternating series (Theorem 13.11, `NTKB`):
`∑_{n < 2N} (-1)^n (n+1)^{-s} = u(2N) - 2^{1-s} u(N) → (1 - 2^{1-s}) C`, while the left side tends
to `(1 - 2^{1-s}) ζ(s)`, and `2^{1-s} ≠ 1`.
-/

open Finset Real Filter Topology

namespace NTKB.Apostol

/-- `u(N) = ∑_{n ≤ N} n^{-s} - N^{1-s}/(1-s)`. -/
noncomputable def powerSumSeq (s : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Ioc 0 N, (n : ℝ) ^ (-s) - (N : ℝ) ^ (1 - s) / (1 - s)

/-- `0 ≤ ∫_a^b t^{-s} dt ≤ (b - a) a^{-s}` and `≥ (b - a) b^{-s}`, `0 < a ≤ b`, `s ≥ 0`. -/
lemma integral_rpow_neg_bounds {a b s : ℝ} (ha : 0 < a) (hab : a ≤ b) (hs : 0 ≤ s) :
    (b - a) * b ^ (-s) ≤ ∫ t in a..b, t ^ (-s) ∧ ∫ t in a..b, t ^ (-s) ≤ (b - a) * a ^ (-s) := by
  have hint : IntervalIntegrable (fun t : ℝ => t ^ (-s)) MeasureTheory.volume a b :=
    intervalIntegral.intervalIntegrable_rpow (Or.inr (by
      rw [Set.uIcc_of_le hab]; intro h; exact absurd h.1 (not_le.2 ha)))
  constructor
  · have := intervalIntegral.integral_mono_on hab intervalIntegrable_const hint
      (fun t ht => Real.rpow_le_rpow_of_nonpos (ha.trans_le ht.1) ht.2 (by linarith))
    simpa [mul_comm] using this
  · have := intervalIntegral.integral_mono_on hab hint intervalIntegrable_const
      (fun t ht => Real.rpow_le_rpow_of_nonpos ha ht.1 (by linarith))
    simpa [mul_comm] using this

lemma powerSumSeq_succ {s : ℝ} (hs : 0 < s) (hs1 : s ≠ 1) {N : ℕ} (hN : 1 ≤ N) :
    0 ≤ powerSumSeq s N - powerSumSeq s (N + 1) ∧
      powerSumSeq s N - powerSumSeq s (N + 1) ≤ (N : ℝ) ^ (-s) - ((N + 1 : ℕ) : ℝ) ^ (-s) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have e : powerSumSeq s N - powerSumSeq s (N + 1) =
      (∫ t in (N : ℝ)..((N + 1 : ℕ) : ℝ), t ^ (-s)) - ((N + 1 : ℕ) : ℝ) ^ (-s) := by
    rw [integral_rpow_neg hN0 (by push_cast; linarith) hs1, powerSumSeq, powerSumSeq,
      sum_Ioc_succ_top (Nat.zero_le _)]
    ring
  rw [e]
  obtain ⟨h1, h2⟩ := integral_rpow_neg_bounds hN0 (show (N : ℝ) ≤ ((N + 1 : ℕ) : ℝ) by
    push_cast; linarith) hs.le
  have h11 : ((N + 1 : ℕ) : ℝ) - N = 1 := by push_cast; ring
  rw [h11, one_mul] at h1 h2
  constructor <;> linarith

lemma powerSumSeq_sub {s : ℝ} (hs : 0 < s) (hs1 : s ≠ 1) {N M : ℕ} (hN : 1 ≤ N) (hNM : N ≤ M) :
    0 ≤ powerSumSeq s N - powerSumSeq s M ∧
      powerSumSeq s N - powerSumSeq s M ≤ (N : ℝ) ^ (-s) - (M : ℝ) ^ (-s) := by
  induction M, hNM using Nat.le_induction with
  | base => simp
  | succ M hNM ih =>
    have h := powerSumSeq_succ hs hs1 (le_trans hN hNM)
    constructor <;> linarith [ih.1, ih.2, h.1, h.2]

/-- The limit `C(s) = lim u(N)` with `|u(N) - C| ≤ N^{-s}`. -/
lemma exists_powerSumSeq_lim {s : ℝ} (hs : 0 < s) (hs1 : s ≠ 1) :
    ∃ C : ℝ, Tendsto (powerSumSeq s) atTop (𝓝 C) ∧
      ∀ N : ℕ, 1 ≤ N → |powerSumSeq s N - C| ≤ (N : ℝ) ^ (-s) := by
  set v : ℕ → ℝ := fun k => powerSumSeq s (k + 1)
  have hanti : Antitone v := antitone_nat_of_succ_le fun k => by
    have := (powerSumSeq_succ hs hs1 (N := k + 1) (by omega)).1; simp only [v]; linarith
  have hbdd : BddBelow (Set.range v) := ⟨powerSumSeq s 1 - 1, by
    rintro _ ⟨k, rfl⟩
    have := (powerSumSeq_sub hs hs1 (N := 1) (M := k + 1) le_rfl (by omega)).2
    have : (0 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) ^ (-s) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    simp only [v, Nat.cast_one, Real.one_rpow] at *
    linarith⟩
  have hv := tendsto_atTop_ciInf hanti hbdd
  set C := ⨅ k, v k
  have hu : Tendsto (powerSumSeq s) atTop (𝓝 C) := by
    rw [← tendsto_add_atTop_iff_nat 1]; exact hv
  refine ⟨C, hu, fun N hN => ?_⟩
  have hle : ∀ M ≥ N, |powerSumSeq s N - powerSumSeq s M| ≤ (N : ℝ) ^ (-s) := fun M hM => by
    obtain ⟨h1, h2⟩ := powerSumSeq_sub hs hs1 hN hM
    have : (0 : ℝ) ≤ (M : ℝ) ^ (-s) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    rw [abs_of_nonneg h1]; linarith
  have hlim : Tendsto (fun M => |powerSumSeq s N - powerSumSeq s M|) atTop
      (𝓝 |powerSumSeq s N - C|) := (tendsto_const_nhds.sub hu).abs
  exact le_of_tendsto hlim (eventually_atTop.mpr ⟨N, hle⟩)

/-- `∑_{n < 2N} (-1)^n (n+1)^{-s} = S(2N) - 2^{1-s} S(N)`, `S(M) = ∑_{n ≤ M} n^{-s}`. -/
lemma sum_alternating_eq {s : ℝ} (N : ℕ) :
    ∑ n ∈ range (2 * N), (-1 : ℝ) ^ n * ((n : ℝ) + 1) ^ (-s) =
      ∑ n ∈ Ioc 0 (2 * N), (n : ℝ) ^ (-s) - 2 ^ (1 - s) * ∑ n ∈ Ioc 0 N, (n : ℝ) ^ (-s) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [show 2 * (N + 1) = 2 * N + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih,
      sum_Ioc_succ_top (by omega), sum_Ioc_succ_top (by omega), sum_Ioc_succ_top (by omega)]
    have h2 : ((2 * N + 1 + 1 : ℕ) : ℝ) ^ (-s) = 2 ^ (-s) * ((N + 1 : ℕ) : ℝ) ^ (-s) := by
      rw [show ((2 * N + 1 + 1 : ℕ) : ℝ) = 2 * ((N + 1 : ℕ) : ℝ) by push_cast; ring,
        Real.mul_rpow (by norm_num) (Nat.cast_nonneg _)]
    have h3 : (2 : ℝ) ^ (1 - s) = 2 * 2 ^ (-s) := by
      rw [Real.rpow_sub (by norm_num), Real.rpow_one, Real.rpow_neg (by norm_num), div_eq_mul_inv]
    have h4 : ((2 * N + 1 : ℕ) : ℝ) + 1 = ((2 * N + 1 + 1 : ℕ) : ℝ) := by push_cast; ring
    have h5 : ((2 * N : ℕ) : ℝ) + 1 = ((2 * N + 1 : ℕ) : ℝ) := by push_cast; ring
    have h6 : (-1 : ℝ) ^ (2 * N) = 1 := by rw [pow_mul, neg_one_sq, one_pow]
    rw [h4, h5, h2, h3]
    simp only [pow_succ, h6]
    ring

lemma sum_alternating_eq_powerSumSeq {s : ℝ} (N : ℕ) :
    ∑ n ∈ range (2 * N), (-1 : ℝ) ^ n * ((n : ℝ) + 1) ^ (-s) =
      powerSumSeq s (2 * N) - 2 ^ (1 - s) * powerSumSeq s N := by
  rw [sum_alternating_eq, powerSumSeq, powerSumSeq, show ((2 * N : ℕ) : ℝ) = 2 * (N : ℝ) by
    push_cast; ring, Real.mul_rpow (by norm_num) (Nat.cast_nonneg _)]
  ring

lemma re_sum_alternating (s : ℝ) (M : ℕ) :
    (∑ n ∈ range M, (-1 : ℂ) ^ n / ((n : ℂ) + 1) ^ (s : ℂ)).re =
      ∑ n ∈ range M, (-1 : ℝ) ^ n * ((n : ℝ) + 1) ^ (-s) := by
  rw [Complex.re_sum]
  refine sum_congr rfl fun n _ => ?_
  have h1 : ((n : ℂ) + 1) ^ (s : ℂ) = ((((n : ℝ) + 1) ^ s : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow (by positivity)]; push_cast; rfl
  rw [h1, show (-1 : ℂ) ^ n = (((-1 : ℝ) ^ n : ℝ) : ℂ) by push_cast; rfl, ← Complex.ofReal_div,
    Complex.ofReal_re, Real.rpow_neg (by positivity), div_eq_mul_inv]

/-- The constant of `u(N)` is `ζ(s)` (Mathlib's `riemannZeta`, real for real `s`). -/
lemma tendsto_powerSumSeq_riemannZeta {s : ℝ} (hs : 0 < s) (hs1 : s ≠ 1) :
    Tendsto (powerSumSeq s) atTop (𝓝 (riemannZeta s).re) := by
  obtain ⟨C, hC, -⟩ := exists_powerSumSeq_lim hs hs1
  have h2N : Tendsto (fun N : ℕ => 2 * N) atTop atTop :=
    tendsto_atTop_mono (fun N => by simp only [id]; omega) tendsto_id
  have hz := (Complex.continuous_re.tendsto _).comp ((tendsto_sum_alternating_zeta
    (s := (s : ℂ)) (by simpa using hs) (by exact_mod_cast hs1)).comp h2N)
  have hre : ((1 - 2 ^ (1 - (s : ℂ))) * riemannZeta s).re = (1 - 2 ^ (1 - s)) * (riemannZeta s).re := by
    have : (2 : ℂ) ^ (1 - (s : ℂ)) = (((2 : ℝ) ^ (1 - s) : ℝ) : ℂ) := by
      rw [Complex.ofReal_cpow (by norm_num)]; push_cast; rfl
    rw [this, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.re_ofReal_mul]
  rw [hre] at hz
  have h1 : Tendsto (fun N : ℕ => ∑ n ∈ range (2 * N), (-1 : ℝ) ^ n * ((n : ℝ) + 1) ^ (-s))
      atTop (𝓝 ((1 - 2 ^ (1 - s)) * (riemannZeta s).re)) := by
    refine hz.congr fun N => ?_
    simp only [Function.comp_apply]
    exact re_sum_alternating s (2 * N)
  have h2 : Tendsto (fun N : ℕ => ∑ n ∈ range (2 * N), (-1 : ℝ) ^ n * ((n : ℝ) + 1) ^ (-s))
      atTop (𝓝 (C - 2 ^ (1 - s) * C)) := by
    simp_rw [sum_alternating_eq_powerSumSeq]
    exact (hC.comp h2N).sub (hC.const_mul _)
  have heq := tendsto_nhds_unique h2 h1
  have hne : (1 : ℝ) - 2 ^ (1 - s) ≠ 0 := by
    intro h
    have h' : (2 : ℝ) ^ (1 - s) = 1 := by linarith
    have := congrArg Real.log h'
    rw [Real.log_rpow (by norm_num), Real.log_one] at this
    rcases mul_eq_zero.mp this with h | h
    · exact hs1 (by linarith)
    · exact absurd h (Real.log_pos one_lt_two).ne'
  have : C = (riemannZeta s).re := by
    apply mul_left_cancel₀ hne
    rw [← heq]; ring
  rwa [this] at hC

/-- **Theorem 3.2 (b)**: for real `s > 0`, `s ≠ 1` and `x ≥ 1`,
`∑_{n ≤ x} n^{-s} = x^{1-s}/(1-s) + ζ(s) + O(x^{-s})`, with the explicit error `2^{s+1} x^{-s}`. -/
@[kb "apostol1976" "Thm 3.2(b), p. 55"]
theorem apostol_thm_3_2_b {s : ℝ} (hs : 0 < s) (hs1 : s ≠ 1) {x : ℝ} (hx : 1 ≤ x) :
    |∑ n ∈ Ioc 0 ⌊x⌋₊, (n : ℝ) ^ (-s) - x ^ (1 - s) / (1 - s) - (riemannZeta s).re| ≤
      2 * 2 ^ s * x ^ (-s) := by
  obtain ⟨C, hC, hCb⟩ := exists_powerSumSeq_lim hs hs1
  have hCz : C = (riemannZeta s).re :=
    tendsto_nhds_unique hC (tendsto_powerSumSeq_riemannZeta hs hs1)
  rw [← hCz]
  set N := ⌊x⌋₊
  have hN1 : 1 ≤ N := Nat.one_le_floor_iff _ |>.mpr hx
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hNx : (N : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hxN : x < N + 1 := Nat.lt_floor_add_one x
  have hint := integral_rpow_neg hN0 hNx hs1
  obtain ⟨-, hup⟩ := integral_rpow_neg_bounds hN0 hNx hs.le
  have hlow : 0 ≤ ∫ t in (N : ℝ)..x, t ^ (-s) :=
    intervalIntegral.integral_nonneg hNx fun t ht => Real.rpow_nonneg (hN0.le.trans ht.1) _
  have hNs : 0 ≤ (N : ℝ) ^ (-s) := Real.rpow_nonneg hN0.le _
  have e : ∑ n ∈ Ioc 0 N, (n : ℝ) ^ (-s) - x ^ (1 - s) / (1 - s) - C =
      (powerSumSeq s N - C) - ∫ t in (N : ℝ)..x, t ^ (-s) := by
    rw [hint, powerSumSeq]; ring
  rw [e]
  have hb1 := hCb N hN1
  have hb2 : ∫ t in (N : ℝ)..x, t ^ (-s) ≤ (N : ℝ) ^ (-s) :=
    hup.trans (by nlinarith)
  have hNx2 : (N : ℝ) ^ (-s) ≤ 2 ^ s * x ^ (-s) := by
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    have hx2 : x / 2 ≤ N := by linarith
    calc (N : ℝ) ^ (-s) ≤ (x / 2) ^ (-s) :=
          Real.rpow_le_rpow_of_nonpos (by linarith) hx2 (by linarith)
      _ = 2 ^ s * x ^ (-s) := by
          rw [Real.div_rpow (by linarith) (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
            div_inv_eq_mul, mul_comm]
  calc |(powerSumSeq s N - C) - ∫ t in (N : ℝ)..x, t ^ (-s)|
      ≤ |powerSumSeq s N - C| + |∫ t in (N : ℝ)..x, t ^ (-s)| := abs_sub _ _
    _ ≤ (N : ℝ) ^ (-s) + (N : ℝ) ^ (-s) := by
        gcongr; rw [abs_of_nonneg hlow]; exact hb2
    _ ≤ 2 * 2 ^ s * x ^ (-s) := by linarith

end NTKB.Apostol
