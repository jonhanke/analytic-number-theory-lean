/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Apostol.Primes.MertensSecond
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Mertens' product `∏_{p ≤ x} (1 - 1/p) = c/log x + O(1/log² x)` (Apostol, Theorem 13.13)

Apostol's proof: `log P(x) = ∑_{p ≤ x} log(1 - 1/p) = -∑_{p ≤ x} 1/p - ∑_{p ≤ x} b(p)` with
`0 ≤ b(p) = -log(1 - 1/p) - 1/p ≤ 2/p²`; the series `B = ∑_p b(p)` converges with tail
`O(1/x)`, and Theorem 4.12 gives `log P(x) = -log log x - A - B + O(1/log x)`. Exponentiating,
`P(x) = c/log x + O(1/log² x)` with `c = e^{-A-B}`. (Apostol notes `c = e^{-γ}`, proved
elsewhere; this identification is not formalized here. Also in PrimeNumberTheoremAnd,
`Mertens.E₃.bound'''`; re-derived here by Apostol's route.)
-/

open Finset Real Filter Topology

namespace NTKB.Apostol

/-- Mertens' product `P(x) = ∏_{p ≤ x} (1 - 1/p)`. -/
noncomputable def mertensProd (x : ℝ) : ℝ := ∏ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, (1 - 1 / (p : ℝ))

lemma mertensProd_pos (x : ℝ) : 0 < mertensProd x := by
  refine prod_pos fun p hp => ?_
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (mem_filter.mp hp).2.two_le
  have : 1 / (p : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp2
  linarith

/-- `b(n) = -log(1 - 1/n) - 1/n` on primes, `0` elsewhere. -/
noncomputable def mertensB (n : ℕ) : ℝ :=
  if n.Prime then -Real.log (1 - 1 / (n : ℝ)) - 1 / n else 0

lemma mertensB_nonneg_le (n : ℕ) : 0 ≤ mertensB n ∧ mertensB n ≤ 2 * ((n : ℝ) ^ 2)⁻¹ := by
  unfold mertensB
  split_ifs with hn
  swap
  · exact ⟨le_rfl, by positivity⟩
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn.two_le
  set x : ℝ := 1 / n with hx
  have hx0 : 0 < x := by positivity
  have hx2 : x ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hn2
  have habs : |x| = x := abs_of_pos hx0
  have h1 := Real.abs_log_sub_add_sum_range_le (x := x) (by rw [habs]; linarith) 1
  simp only [range_one, sum_singleton, zero_add, pow_one, Nat.cast_zero, div_one, habs] at h1
  have hlog : Real.log (1 - x) ≤ -x := by
    have := Real.log_le_sub_one_of_pos (show 0 < 1 - x by linarith)
    linarith
  constructor
  · linarith
  · have h2 : x ^ 2 / (1 - x) ≤ 2 * x ^ 2 := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith [sq_nonneg x]
    have h3 : x ^ 2 = ((n : ℝ) ^ 2)⁻¹ := by rw [hx, div_pow, one_pow, one_div]
    have := (abs_le.mp h1).1
    rw [← h3]
    linarith

lemma summable_mertensB : Summable mertensB :=
  Summable.of_nonneg_of_le (fun n => (mertensB_nonneg_le n).1) (fun n => (mertensB_nonneg_le n).2)
    ((Real.summable_nat_pow_inv.mpr one_lt_two).mul_left 2)

/-- Tail of `∑ b(p)`: `0 ≤ B - ∑_{n ≤ N} b(n) ≤ 4/(N+1)`. -/
lemma mertensB_tail (N : ℕ) :
    0 ≤ (∑' n, mertensB n) - ∑ n ∈ range (N + 1), mertensB n ∧
      (∑' n, mertensB n) - ∑ n ∈ range (N + 1), mertensB n ≤ 4 / (N + 1) := by
  constructor
  · exact sub_nonneg.mpr (summable_mertensB.sum_le_tsum _ fun n _ => (mertensB_nonneg_le n).1)
  have hlim : Tendsto (fun M => ∑ n ∈ range (M + 1), mertensB n - ∑ n ∈ range (N + 1), mertensB n)
      atTop (𝓝 ((∑' n, mertensB n) - ∑ n ∈ range (N + 1), mertensB n)) :=
    ((summable_mertensB.hasSum.tendsto_sum_nat).comp (tendsto_add_atTop_nat 1)).sub_const _
  refine le_of_tendsto hlim ?_
  filter_upwards [eventually_ge_atTop N] with M hM
  rw [← sum_range_add_sum_Ico _ (by omega : N + 1 ≤ M + 1), add_sub_cancel_left]
  have hI : Ico (N + 1) (M + 1) = Ioo N (M + 1) := by ext; simp only [mem_Ico, mem_Ioo]; omega
  rw [hI]
  calc ∑ n ∈ Ioo N (M + 1), mertensB n ≤ ∑ n ∈ Ioo N (M + 1), 2 * ((n : ℝ) ^ 2)⁻¹ :=
        sum_le_sum fun n _ => (mertensB_nonneg_le n).2
    _ = 2 * ∑ n ∈ Ioo N (M + 1), ((n : ℝ) ^ 2)⁻¹ := by rw [mul_sum]
    _ ≤ 2 * (2 / (N + 1)) := by gcongr; exact sum_Ioo_inv_sq_le N (M + 1)
    _ = 4 / (N + 1) := by ring

lemma log_mertensProd (x : ℝ) :
    Real.log (mertensProd x) = -(∑ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, (1 : ℝ) / p) -
      ∑ n ∈ range (⌊x⌋₊ + 1), mertensB n := by
  rw [mertensProd, Real.log_prod (fun p hp => ?_), Nat.range_succ_eq_Icc_zero]
  · rw [show ∑ n ∈ Icc 0 ⌊x⌋₊, mertensB n = ∑ n ∈ Icc 0 ⌊x⌋₊,
        (if n.Prime then -Real.log (1 - 1 / (n : ℝ)) - 1 / n else 0) from rfl,
      sum_Icc_eq_sum_filter_prime, ← sum_neg_distrib, ← sum_sub_distrib]
    refine sum_congr rfl fun p _ => by ring
  · have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (mem_filter.mp hp).2.two_le
    have : 1 / (p : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp2
    linarith

/-- `|e^δ - 1| ≤ K |δ|`-type bound in the form needed below: if `|δ| ≤ D/L` with `L ≥ L₀ > 0`,
then `|e^δ - 1| ≤ (2D + (e^{D/L₀} + 1) D)/L`. -/
lemma abs_exp_sub_one_le_of_le {δ D L L₀ : ℝ} (hD : 0 ≤ D) (hL₀ : 0 < L₀) (hL : L₀ ≤ L)
    (hδ : |δ| ≤ D / L) :
    |Real.exp δ - 1| ≤ (2 * D + (Real.exp (D / L₀) + 1) * D) / L := by
  have hL0 : 0 < L := hL₀.trans_le hL
  have hK : 0 ≤ (Real.exp (D / L₀) + 1) * D := by positivity
  by_cases h1 : D / L ≤ 1
  · calc |Real.exp δ - 1| ≤ 2 * |δ| := Real.abs_exp_sub_one_le (hδ.trans h1)
      _ ≤ 2 * (D / L) := by gcongr
      _ = 2 * D / L := by ring
      _ ≤ (2 * D + (Real.exp (D / L₀) + 1) * D) / L := by gcongr; linarith
  · push Not at h1
    have hδ' : δ ≤ D / L₀ := (le_abs_self δ).trans (hδ.trans (div_le_div_of_nonneg_left hD hL₀ hL))
    have e1 : |Real.exp δ - 1| ≤ Real.exp (D / L₀) + 1 := by
      rw [abs_le]
      constructor
      · have := Real.exp_pos δ; linarith [Real.exp_pos (D / L₀)]
      · linarith [Real.exp_le_exp.mpr hδ']
    calc |Real.exp δ - 1| ≤ Real.exp (D / L₀) + 1 := e1
      _ ≤ (Real.exp (D / L₀) + 1) * (D / L) := le_mul_of_one_le_right (by positivity) h1.le
      _ = (Real.exp (D / L₀) + 1) * D / L := by ring
      _ ≤ (2 * D + (Real.exp (D / L₀) + 1) * D) / L := by gcongr; linarith

/-- **Theorem 13.13** (Mertens): there is a constant `c > 0` with
`∏_{p ≤ x} (1 - 1/p) = c/log x + O(1/log² x)` for `x ≥ 2`. -/
@[kb "apostol1976" "Thm 13.13, p. 297"]
theorem apostol_thm_13_13 : ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x →
    |mertensProd x - c / Real.log x| ≤ C / Real.log x ^ 2 := by
  obtain ⟨A, C₁, hA⟩ := apostol_thm_4_12
  set B := ∑' n, mertensB n
  have hC₁ : 0 ≤ C₁ := by
    have h := hA 2 le_rfl
    have : 0 < Real.log 2 := Real.log_pos one_lt_two
    have := (abs_nonneg _).trans h
    exact (div_nonneg_iff.mp this).elim (fun h => h.1) fun h => absurd h.2 (not_le.mpr ‹_›)
  set D := C₁ + 4
  have hD : 0 ≤ D := by positivity
  set K := 2 * D + (Real.exp (D / Real.log 2) + 1) * D
  refine ⟨Real.exp (-A - B), Real.exp_pos _, Real.exp (-A - B) * K, fun x hx => ?_⟩
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlog2x : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  set δ := Real.log (mertensProd x) + Real.log (Real.log x) + A + B with hδdef
  have hδ : |δ| ≤ D / Real.log x := by
    have h1 := hA x hx
    obtain ⟨h2, h3⟩ := mertensB_tail ⌊x⌋₊
    have hfl : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
    have h4 : 4 / ((⌊x⌋₊ : ℝ) + 1) ≤ 4 / Real.log x := by
      have : Real.log x < x := (Real.log_le_sub_one_of_pos (by linarith)).trans_lt (by linarith)
      gcongr; linarith
    have e : δ = -(∑ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, (1 : ℝ) / p - Real.log (Real.log x) - A) +
        (B - ∑ n ∈ range (⌊x⌋₊ + 1), mertensB n) := by
      rw [hδdef, log_mertensProd]; ring
    rw [e]
    calc _ ≤ |∑ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, (1 : ℝ) / p - Real.log (Real.log x) - A| +
          |B - ∑ n ∈ range (⌊x⌋₊ + 1), mertensB n| := by
          refine (abs_add_le _ _).trans ?_; rw [abs_neg]
      _ ≤ C₁ / Real.log x + 4 / Real.log x := by
          gcongr
          rw [abs_of_nonneg h2]; exact h3.trans h4
      _ = D / Real.log x := by ring
  have hP : mertensProd x = Real.exp (-A - B) / Real.log x * Real.exp δ := by
    rw [hδdef, Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_log (mertensProd_pos x),
      Real.exp_log hlogx]
    have := Real.exp_pos A
    have := Real.exp_pos B
    rw [show -A - B = -A + -B by ring, Real.exp_add, Real.exp_neg, Real.exp_neg]
    field_simp
  rw [hP, show Real.exp (-A - B) / Real.log x * Real.exp δ - Real.exp (-A - B) / Real.log x =
    Real.exp (-A - B) / Real.log x * (Real.exp δ - 1) by ring, abs_mul,
    abs_of_pos (by positivity)]
  calc Real.exp (-A - B) / Real.log x * |Real.exp δ - 1|
      ≤ Real.exp (-A - B) / Real.log x * (K / Real.log x) := by
        gcongr; exact abs_exp_sub_one_le_of_le hD hlog2 hlog2x hδ
    _ = Real.exp (-A - B) * K / Real.log x ^ 2 := by ring

end NTKB.Apostol
