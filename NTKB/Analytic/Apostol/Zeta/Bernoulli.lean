/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.NumberTheory.ZetaValues
import NTKB.Attr

/-!
# Sign and size of the Bernoulli numbers (Apostol, Chapter 12, Theorem 12.18)

**Theorem 12.18.** `(-1)^{k+1} B_{2k} > 0` for `k ≥ 1`, and
`|B_{2k}| ~ 2 (2k)! / (2π)^{2k}` as `k → ∞`.

Proof (Apostol's): Euler's formula `ζ(2k) = (-1)^{k+1} (2π)^{2k} B_{2k} / (2 (2k)!)` (Mathlib's
`hasSum_zeta_nat`) with `ζ(2k) = ∑ n^{-2k} ≥ 1 > 0` and `ζ(2k) → 1`
(`1 ≤ ζ(2k) ≤ 1 + 4^{1-k} ζ(2)`).
-/

open Filter Topology
open scoped Real Nat

namespace NTKB.Apostol

/-- `ζ(2k) = ∑_{n ≥ 1} n^{-2k}` lies in `[1, 1 + 4^{1-k} π²/6]` for `k ≥ 1`. -/
theorem one_le_tsum_and_le {k : ℕ} (hk : k ≠ 0) :
    1 ≤ ∑' n : ℕ, 1 / (n : ℝ) ^ (2 * k) ∧
      ∑' n : ℕ, 1 / (n : ℝ) ^ (2 * k) ≤ 1 + (1 / 4) ^ (k - 1) * (π ^ 2 / 6) := by
  have hs := hasSum_zeta_nat hk
  have hnn : ∀ n : ℕ, 0 ≤ 1 / (n : ℝ) ^ (2 * k) := fun n ↦ by positivity
  constructor
  · have := le_hasSum hs 1 (fun j _ ↦ hnn j)
    rw [hs.tsum_eq]; simpa using this
  · set c : ℝ := (1 / 4) ^ (k - 1)
    have hg : HasSum (fun n : ℕ ↦ (if n = 1 then (1 : ℝ) else 0) + c * (1 / (n : ℝ) ^ 2))
        (1 + c * (π ^ 2 / 6)) :=
      (hasSum_ite_eq 1 (1 : ℝ)).add (hasSum_zeta_two.mul_left c)
    rw [hs.tsum_eq]
    refine hasSum_le (fun n ↦ ?_) hs hg
    have hc0 : 0 ≤ c := by positivity
    rcases Nat.lt_or_ge n 2 with h | h
    · interval_cases n
      · simp [hk]
      · simp; positivity
    · rw [if_neg (by omega), zero_add]
      have hn : (2 : ℝ) ≤ n := by exact_mod_cast h
      have hpow : (4 : ℝ) ^ (k - 1) * (n : ℝ) ^ 2 ≤ (n : ℝ) ^ (2 * k) := by
        have h1 : (4 : ℝ) ^ (k - 1) ≤ (n : ℝ) ^ (2 * (k - 1)) := by
          rw [pow_mul]
          exact pow_le_pow_left₀ (by norm_num) (by nlinarith) _
        calc (4 : ℝ) ^ (k - 1) * (n : ℝ) ^ 2 ≤ (n : ℝ) ^ (2 * (k - 1)) * (n : ℝ) ^ 2 :=
              mul_le_mul_of_nonneg_right h1 (by positivity)
          _ = (n : ℝ) ^ (2 * k) := by
              rw [← pow_add]; congr 1; omega
      have h4 : (0 : ℝ) < (4 : ℝ) ^ (k - 1) * (n : ℝ) ^ 2 := by positivity
      calc 1 / (n : ℝ) ^ (2 * k) ≤ 1 / ((4 : ℝ) ^ (k - 1) * (n : ℝ) ^ 2) :=
            one_div_le_one_div_of_le h4 hpow
        _ = c * (1 / (n : ℝ) ^ 2) := by
            simp only [c, one_div, inv_pow, mul_inv]

/-- `ζ(2k) = (-1)^{k+1} B_{2k} · (2π)^{2k} / (2 (2k)!)`. -/
theorem tsum_eq_bernoulli {k : ℕ} (hk : k ≠ 0) :
    ∑' n : ℕ, 1 / (n : ℝ) ^ (2 * k) =
      (-1) ^ (k + 1) * (bernoulli (2 * k) : ℝ) * ((2 * π) ^ (2 * k) / (2 * (2 * k)!)) := by
  rw [(hasSum_zeta_nat hk).tsum_eq, mul_pow]
  have h2 : (2 : ℝ) ^ (2 * k) = 2 * 2 ^ (2 * k - 1) := by
    rw [← pow_succ']; congr 1; omega
  rw [h2]
  field_simp

/-- **Apostol, Theorem 12.18 (a).** `(-1)^{k+1} B_{2k} > 0` for `k ≥ 1`. -/
@[kb "apostol1976" "Thm 12.18, p. 277"]
theorem neg_one_pow_mul_bernoulli_pos {k : ℕ} (hk : k ≠ 0) :
    0 < (-1) ^ (k + 1) * (bernoulli (2 * k) : ℝ) := by
  have h := tsum_eq_bernoulli hk
  have h1 := (one_le_tsum_and_le hk).1
  have hpos : 0 < (2 * π) ^ (2 * k) / (2 * (2 * k)!) := by positivity
  by_contra hneg
  push_neg at hneg
  have : (-1) ^ (k + 1) * (bernoulli (2 * k) : ℝ) * ((2 * π) ^ (2 * k) / (2 * (2 * k)!)) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hneg hpos.le
  linarith

/-- **Apostol, Theorem 12.18 (b).** `|B_{2k}| ~ 2 (2k)!/(2π)^{2k}`: the ratio tends to `1`. -/
@[kb "apostol1976" "Thm 12.18, p. 277"]
theorem tendsto_abs_bernoulli_div :
    Tendsto (fun k : ℕ ↦ |(bernoulli (2 * k) : ℝ)| / (2 * (2 * k)! / (2 * π) ^ (2 * k)))
      atTop (𝓝 1) := by
  -- the ratio is `ζ(2k)`
  have e : ∀ k : ℕ, k ≠ 0 → |(bernoulli (2 * k) : ℝ)| / (2 * (2 * k)! / (2 * π) ^ (2 * k)) =
      ∑' n : ℕ, 1 / (n : ℝ) ^ (2 * k) := by
    intro k hk
    rw [tsum_eq_bernoulli hk]
    have hpos := neg_one_pow_mul_bernoulli_pos hk
    have habs : |(bernoulli (2 * k) : ℝ)| = (-1) ^ (k + 1) * (bernoulli (2 * k) : ℝ) := by
      rw [← abs_of_pos hpos, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    rw [habs]
    field_simp
  -- squeeze `1 ≤ ζ(2k) ≤ 1 + 4^{1-k} π²/6`
  have hup : Tendsto (fun k : ℕ ↦ 1 + (1 / 4 : ℝ) ^ (k - 1) * (π ^ 2 / 6)) atTop (𝓝 1) := by
    have h0 : Tendsto (fun k : ℕ ↦ (1 / 4 : ℝ) ^ (k - 1)) atTop (𝓝 0) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).comp
        (tendsto_sub_atTop_nat 1)
    simpa using (h0.mul_const (π ^ 2 / 6)).const_add 1
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards [eventually_ne_atTop 0] with k hk
    rw [e k hk]; exact (one_le_tsum_and_le hk).1
  · filter_upwards [eventually_ne_atTop 0] with k hk
    rw [e k hk]; exact (one_le_tsum_and_le hk).2

end NTKB.Apostol
