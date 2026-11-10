/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.NumberTheory.Chebyshev
import NTKB.Attr

/-!
# `ψ`, `θ` and `π`: equivalent forms of the prime number theorem (Apostol, Theorems 4.1, 4.4)

* **Theorem 4.1**: for `x > 0`, `0 ≤ ψ(x)/x - θ(x)/x ≤ (log x)²/(2 √x log 2)`; hence
  `ψ(x)/x - θ(x)/x → 0`. Apostol's proof: `ψ(x) - θ(x) = ∑_{2 ≤ m ≤ log₂ x} θ(x^{1/m})`
  (Mathlib's `Chebyshev.psi_eq_theta_add_sum_theta`) and `θ(y) ≤ y log y`.
* **Theorem 4.4**: `π(x) log x / x → 1` iff `θ(x)/x → 1` iff `ψ(x)/x → 1`. The first equivalence
  uses `π(x) - θ(x)/log x = O(x/log² x)` (Abel summation, Mathlib's
  `Chebyshev.primeCounting_sub_theta_div_log_isBigO`; Apostol's Theorem 4.3 identities).
-/

open Real Filter Topology Finset Chebyshev Asymptotics

namespace NTKB.Apostol

lemma theta_le_mul_log {y : ℝ} (hy : 1 ≤ y) : θ y ≤ y * Real.log y := by
  rw [theta]
  calc ∑ p ∈ Ioc 0 ⌊y⌋₊ with p.Prime, Real.log p
      ≤ ∑ _p ∈ Ioc 0 ⌊y⌋₊, Real.log y := by
        refine (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun p _ _ => ?_).trans
          (sum_le_sum fun p hp => ?_)
        · exact Real.log_natCast_nonneg p
        · have h1 := (mem_Ioc.mp hp)
          exact Real.log_le_log (by exact_mod_cast h1.1) (Nat.le_floor_iff (by linarith) |>.mp h1.2)
    _ = ⌊y⌋₊ * Real.log y := by rw [sum_const, Nat.card_Ioc, nsmul_eq_mul]; simp
    _ ≤ y * Real.log y := by
        gcongr
        · exact Real.log_nonneg hy
        · exact Nat.floor_le (by linarith)

/-- **Theorem 4.1**. -/
@[kb "apostol1976" "Thm 4.1, p. 76"]
theorem apostol_thm_4_1 {x : ℝ} (hx : 0 < x) :
    0 ≤ ψ x / x - θ x / x ∧ ψ x / x - θ x / x ≤ Real.log x ^ 2 / (2 * √x * Real.log 2) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hsx : 0 < √x := Real.sqrt_pos.mpr hx
  constructor
  · rw [← sub_div]; exact div_nonneg (sub_nonneg.mpr (theta_le_psi x)) hx.le
  by_cases h2 : x < 2
  · rw [psi_eq_zero_of_lt_two h2, theta_eq_zero_of_lt_two h2, zero_div, sub_zero]
    positivity
  push Not at h2
  have hx1 : 1 ≤ x := by linarith
  have hlx : 0 < Real.log x := Real.log_pos (by linarith)
  set N := ⌊Real.log x / Real.log 2⌋₊
  have hterm : ∀ n ∈ Icc 2 N, θ (x ^ ((1 : ℝ) / n)) ≤ √x * (Real.log x / 2) := by
    intro n hn
    have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast (mem_Icc.mp hn).1
    have hy1 : 1 ≤ x ^ ((1 : ℝ) / n) := Real.one_le_rpow hx1 (by positivity)
    refine (theta_le_mul_log hy1).trans ?_
    have h1 : x ^ ((1 : ℝ) / n) ≤ √x := by
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow_of_exponent_le hx1 (by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith)
    have h2' : Real.log (x ^ ((1 : ℝ) / n)) ≤ Real.log x / 2 := by
      rw [Real.log_rpow hx]
      rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    exact mul_le_mul h1 h2' (Real.log_nonneg hy1) hsx.le
  have hsum : ψ x - θ x ≤ (Real.log x / Real.log 2) * (√x * (Real.log x / 2)) := by
    rw [psi_eq_theta_add_sum_theta h2, add_sub_cancel_left]
    calc ∑ n ∈ Icc 2 N, θ (x ^ ((1 : ℝ) / n)) ≤ ∑ _n ∈ Icc 2 N, √x * (Real.log x / 2) :=
          sum_le_sum hterm
      _ = ((Icc 2 N).card : ℝ) * (√x * (Real.log x / 2)) := by rw [sum_const, nsmul_eq_mul]
      _ ≤ (Real.log x / Real.log 2) * (√x * (Real.log x / 2)) := by
          gcongr
          rw [Nat.card_Icc]
          calc ((N + 1 - 2 : ℕ) : ℝ) ≤ N := by exact_mod_cast (by omega : N + 1 - 2 ≤ N)
            _ ≤ Real.log x / Real.log 2 := Nat.floor_le (by positivity)
  rw [← sub_div, div_le_div_iff₀ hx (by positivity)]
  have hxx : √x * √x = x := Real.mul_self_sqrt hx.le
  calc (ψ x - θ x) * (2 * √x * Real.log 2)
      ≤ (Real.log x / Real.log 2) * (√x * (Real.log x / 2)) * (2 * √x * Real.log 2) := by
        gcongr
    _ = Real.log x ^ 2 * (√x * √x) := by field_simp
    _ = Real.log x ^ 2 * x := by rw [hxx]

lemma tendsto_psi_div_sub_theta_div :
    Tendsto (fun x => ψ x / x - θ x / x) atTop (𝓝 0) := by
  have hb : Tendsto (fun x : ℝ => Real.log x ^ 2 / (2 * √x * Real.log 2)) atTop (𝓝 0) := by
    have h := (isLittleO_log_rpow_atTop (r := (1 / 4 : ℝ)) (by norm_num))
    have h1 : Tendsto (fun x : ℝ => Real.log x / x ^ (1 / 4 : ℝ)) atTop (𝓝 0) :=
      h.tendsto_div_nhds_zero
    have h2 := (h1.mul h1).div_const (2 * Real.log 2)
    rw [zero_mul, zero_div] at h2
    refine h2.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with x hx
    have hq : x ^ (1 / 4 : ℝ) * x ^ (1 / 4 : ℝ) = √x := by
      rw [← Real.rpow_add hx, Real.sqrt_eq_rpow]; norm_num
    rw [div_mul_div_comm, ← sq, hq, div_div]; ring
  refine squeeze_zero' (Eventually.of_forall fun x => ?_) ?_ hb
  · by_cases hx : 0 < x
    · exact (apostol_thm_4_1 hx).1
    · push Not at hx
      rw [psi_eq_zero_of_lt_two (by linarith), theta_eq_zero_of_lt_two (by linarith)]; simp
  · filter_upwards [eventually_gt_atTop 0] with x hx using (apostol_thm_4_1 hx).2

/-- **Theorem 4.4**: the three forms of the prime number theorem are equivalent:
`π(x) log x / x → 1` iff `θ(x)/x → 1` iff `ψ(x)/x → 1`. -/
@[kb "apostol1976" "Thm 4.4, p. 79"]
theorem apostol_thm_4_4 :
    (Tendsto (fun x => (Nat.primeCounting ⌊x⌋₊ : ℝ) * Real.log x / x) atTop (𝓝 1) ↔
        Tendsto (fun x => θ x / x) atTop (𝓝 1)) ∧
      (Tendsto (fun x => θ x / x) atTop (𝓝 1) ↔ Tendsto (fun x => ψ x / x) atTop (𝓝 1)) := by
  have hdiff : Tendsto (fun x => (Nat.primeCounting ⌊x⌋₊ : ℝ) * Real.log x / x - θ x / x) atTop
      (𝓝 0) := by
    have hO := primeCounting_sub_theta_div_log_isBigO.mul
      (isBigO_refl (fun x : ℝ => Real.log x / x) atTop)
    have hg : Tendsto (fun x : ℝ => x / Real.log x ^ 2 * (Real.log x / x)) atTop (𝓝 0) := by
      refine (tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop).congr' ?_
      filter_upwards [eventually_gt_atTop 1] with x hx
      have hl : Real.log x ≠ 0 := (Real.log_pos hx).ne'
      have hx0 : x ≠ 0 := by linarith
      simp only [Function.comp_apply]
      field_simp
    refine (hO.trans_tendsto hg).congr' ?_
    filter_upwards [eventually_gt_atTop 1] with x hx
    have hl : Real.log x ≠ 0 := (Real.log_pos hx).ne'
    have hx0 : x ≠ 0 := by linarith
    field_simp
  have hpt := tendsto_psi_div_sub_theta_div
  constructor
  · constructor
    · intro h; simpa using h.sub hdiff
    · intro h; simpa using h.add hdiff
  · constructor
    · intro h; simpa using h.add hpt
    · intro h; simpa using h.sub hpt

end NTKB.Apostol
