/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable
import NTKB.Attr

/-!
# Jacobi's triple product identity (Apostol, Theorem 14.6)

For complex `x, z` with `|x| < 1`, `z ≠ 0`:
`∏_{n ≥ 1} (1 - x^{2n})(1 + x^{2n-1} z²)(1 + x^{2n-1} z^{-2}) = ∑_{m ∈ ℤ} x^{m²} z^{2m}`.

Apostol's proof uses the Laurent expansion of the product in `z` (on `ℂ \ {0}`), which is not in
Mathlib. We use instead the classical finite form (Cauchy's identity) and a limit:

* the Gaussian binomial coefficients `qBinom q N j = (q;q)_N / ((q;q)_j (q;q)_{N-j})` (`|q| < 1`) and the
  `q`-binomial theorem `∏_{k<N} (1 + q^k t) = ∑_{j ≤ N} q^{j(j-1)/2} [N, j]_q t^j` (`qbinomial_theorem`),
  by induction from the `q`-Pascal rule;
* with `q = x²`, `N = 2n`, `t = w x^{1-2n}` this gives the finite triple product
  `∏_{k<n} (1 + x^{2k+1} w)(1 + x^{2k+1} w⁻¹) = ∑_{|m| ≤ n} [2n, n+m]_{x²} x^{m²} w^m` (`finite_jacobi`);
* as `n → ∞`, `[2n, n+m]_{x²} → 1/(x²;x²)_∞`, dominated by a constant, so Tannery's theorem
  (`tendsto_tsum_of_dominated_convergence`) gives the identity (`apostol_thm_14_6`).
-/

open Complex Finset Filter
open scoped Topology Real

namespace NTKB.Apostol

/-- The `q`-Pochhammer symbol `(q; q)_n = ∏_{k=1}^n (1 - q^k)`. -/
noncomputable def qPoch (q : ℂ) (n : ℕ) : ℂ := ∏ k ∈ range n, (1 - q ^ (k + 1))

/-- The Gaussian binomial coefficient `[N, j]_q = (q;q)_N / ((q;q)_j (q;q)_{N-j})` (`0` for `j > N`). -/
noncomputable def qBinom (q : ℂ) (N j : ℕ) : ℂ :=
  if j ≤ N then qPoch q N / (qPoch q j * qPoch q (N - j)) else 0

theorem qPoch_zero (q : ℂ) : qPoch q 0 = 1 := by simp [qPoch]

theorem qPoch_succ (q : ℂ) (n : ℕ) : qPoch q (n + 1) = qPoch q n * (1 - q ^ (n + 1)) := by
  simp [qPoch, prod_range_succ]

theorem one_sub_pow_ne_zero {q : ℂ} (hq : ‖q‖ < 1) (k : ℕ) : 1 - q ^ (k + 1) ≠ 0 := by
  intro h
  have h1 : q ^ (k + 1) = 1 := (sub_eq_zero.1 h).symm
  have h2 := congrArg norm h1
  rw [norm_pow, norm_one] at h2
  have : ‖q‖ ^ (k + 1) < 1 := pow_lt_one₀ (norm_nonneg _) hq (Nat.succ_ne_zero k)
  linarith

theorem qPoch_ne_zero {q : ℂ} (hq : ‖q‖ < 1) (n : ℕ) : qPoch q n ≠ 0 :=
  prod_ne_zero_iff.2 fun k _ ↦ one_sub_pow_ne_zero hq k

theorem qBinom_zero_right {q : ℂ} (hq : ‖q‖ < 1) (N : ℕ) : qBinom q N 0 = 1 := by
  simp [qBinom, qPoch_zero, div_self (qPoch_ne_zero hq N)]

theorem qBinom_self {q : ℂ} (hq : ‖q‖ < 1) (N : ℕ) : qBinom q N N = 1 := by
  simp [qBinom, qPoch_zero, div_self (qPoch_ne_zero hq N)]

theorem qBinom_of_lt {q : ℂ} {N j : ℕ} (h : N < j) : qBinom q N j = 0 := by
  simp [qBinom, not_le.2 h]

/-- The `q`-Pascal rule `[N+1, j+1] = [N, j+1] + q^{N-j} [N, j]`. -/
theorem qBinom_succ_succ {q : ℂ} (hq : ‖q‖ < 1) {N j : ℕ} (hj : j ≤ N) :
    qBinom q (N + 1) (j + 1) = qBinom q N (j + 1) + q ^ (N - j) * qBinom q N j := by
  rcases hj.eq_or_lt with rfl | hlt
  · rw [qBinom_self hq, qBinom_of_lt (Nat.lt_succ_self j), qBinom_self hq, Nat.sub_self]
    ring
  obtain ⟨d, rfl⟩ : ∃ d, N = j + 1 + d := ⟨N - (j + 1), by omega⟩
  have h0 := qPoch_ne_zero hq
  simp only [qBinom, show j + 1 ≤ j + 1 + d + 1 by omega, show j + 1 ≤ j + 1 + d by omega,
    show j ≤ j + 1 + d by omega, ite_true,
    show j + 1 + d + 1 - (j + 1) = d + 1 by omega, show j + 1 + d - (j + 1) = d by omega,
    show j + 1 + d - j = d + 1 by omega]
  rw [qPoch_succ q (j + 1 + d), qPoch_succ q j, qPoch_succ q d]
  have e1 := one_sub_pow_ne_zero hq j
  have e2 := one_sub_pow_ne_zero hq d
  have e3 := h0 j
  have e4 := h0 d
  have e5 := h0 (j + 1 + d)
  field_simp
  ring

theorem choose_two_succ (j : ℕ) : (j + 1).choose 2 = j.choose 2 + j := by
  rw [Nat.choose_succ_succ, Nat.choose_one_right, add_comm]

/-- The `q`-binomial theorem: `∏_{k<N} (1 + q^k t) = ∑_{j=0}^{N} q^{j(j-1)/2} [N, j]_q t^j`. -/
theorem qbinomial_theorem {q : ℂ} (hq : ‖q‖ < 1) (t : ℂ) (N : ℕ) :
    ∏ k ∈ range N, (1 + q ^ k * t) =
      ∑ j ∈ range (N + 1), q ^ (j.choose 2) * qBinom q N j * t ^ j := by
  induction N with
  | zero => simp [qBinom_zero_right hq]
  | succ N ih =>
    rw [prod_range_succ, ih, sum_range_succ' (fun j ↦ q ^ (j.choose 2) * qBinom q (N + 1) j * t ^ j)]
    have h1 : ∀ j ∈ range (N + 1),
        q ^ ((j + 1).choose 2) * qBinom q (N + 1) (j + 1) * t ^ (j + 1) =
          q ^ ((j + 1).choose 2) * qBinom q N (j + 1) * t ^ (j + 1) +
            q ^ N * t * (q ^ (j.choose 2) * qBinom q N j * t ^ j) := by
      intro j hj
      have hjN : j ≤ N := Nat.lt_succ_iff.1 (mem_range.1 hj)
      rw [qBinom_succ_succ hq hjN, choose_two_succ]
      have : q ^ N = q ^ j * q ^ (N - j) := by rw [← pow_add, Nat.add_sub_cancel' hjN]
      rw [this]
      ring
    rw [sum_congr rfl h1, sum_add_distrib, ← mul_sum]
    have h2 := sum_range_succ' (fun j ↦ q ^ (j.choose 2) * qBinom q N j * t ^ j) (N + 1)
    rw [sum_range_succ, qBinom_of_lt (Nat.lt_succ_self N)] at h2
    simp only [pow_zero, Nat.choose, qBinom_zero_right hq, one_mul, mul_one, mul_zero, zero_mul,
      add_zero] at h2 ⊢
    linear_combination h2

theorem two_mul_choose_two (j : ℕ) : 2 * ((j.choose 2 : ℕ) : ℤ) = (j : ℤ) ^ 2 - j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [choose_two_succ]
    push_cast
    linear_combination ih

theorem prod_zpow_neg_odd {x : ℂ} (hx0 : x ≠ 0) (n : ℕ) :
    ∏ k ∈ range n, x ^ (-(2 * (k : ℤ) + 1)) = x ^ (-((n : ℤ) ^ 2)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [prod_range_succ, ih, ← zpow_add₀ hx0]
    congr 1; push_cast; ring

/-- The finite form of the triple product identity (Cauchy):
`∏_{k<n} (1 + x^{2k+1} w)(1 + x^{2k+1} w⁻¹) = ∑_{j=0}^{2n} [2n, j]_{x²} x^{(j-n)²} w^{j-n}`. -/
theorem finite_jacobi {x w : ℂ} (hx0 : x ≠ 0) (hx : ‖x‖ < 1) (hw : w ≠ 0) (n : ℕ) :
    ∏ k ∈ range n, ((1 + x ^ (2 * k + 1) * w) * (1 + x ^ (2 * k + 1) * w⁻¹)) =
      ∑ j ∈ range (2 * n + 1),
        qBinom (x ^ 2) (2 * n) j * x ^ (((j : ℤ) - n) ^ 2) * w ^ ((j : ℤ) - n) := by
  have hq : ‖x ^ 2‖ < 1 := by
    rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hx two_ne_zero
  have QB := qbinomial_theorem hq (w * x ^ (1 - 2 * (n : ℤ))) (2 * n)
  have pw : ∀ i : ℕ, (x ^ 2) ^ i * x ^ (1 - 2 * (n : ℤ)) = x ^ (2 * (i : ℤ) + 1 - 2 * n) := by
    intro i
    rw [← pow_mul, ← zpow_natCast, ← zpow_add₀ hx0]
    congr 1; push_cast; ring
  set c : ℂ := w ^ n * x ^ (-((n : ℤ) ^ 2)) with hc
  have hc0 : c ≠ 0 := mul_ne_zero (pow_ne_zero _ hw) (zpow_ne_zero _ hx0)
  -- The left side of the `q`-binomial theorem.
  have hL : ∏ k ∈ range (2 * n), (1 + (x ^ 2) ^ k * (w * x ^ (1 - 2 * (n : ℤ)))) =
      c * ∏ k ∈ range n, ((1 + x ^ (2 * k + 1) * w) * (1 + x ^ (2 * k + 1) * w⁻¹)) := by
    rw [two_mul, prod_range_add, ← prod_range_reflect _ n, prod_mul_distrib]
    have h1 : ∀ k ∈ range n, 1 + (x ^ 2) ^ (n - 1 - k) * (w * x ^ (1 - 2 * (n : ℤ))) =
        (w * x ^ (-(2 * (k : ℤ) + 1))) * (1 + x ^ (2 * k + 1) * w⁻¹) := by
      intro k hk
      have hkn : k < n := mem_range.1 hk
      rw [mul_left_comm, pw, show 2 * ((n - 1 - k : ℕ) : ℤ) + 1 - 2 * n = -(2 * (k : ℤ) + 1) by
        omega]
      have : x ^ (-(2 * (k : ℤ) + 1)) * x ^ (2 * k + 1) = 1 := by
        rw [← zpow_natCast, ← zpow_add₀ hx0]; push_cast; simp
      have h5 : w * x ^ (-(2 * (k : ℤ) + 1)) * (x ^ (2 * k + 1) * w⁻¹) = 1 := by
        rw [show w * x ^ (-(2 * (k : ℤ) + 1)) * (x ^ (2 * k + 1) * w⁻¹) =
          (x ^ (-(2 * (k : ℤ) + 1)) * x ^ (2 * k + 1)) * (w * w⁻¹) by ring, this,
          mul_inv_cancel₀ hw, one_mul]
      rw [mul_add, mul_one, h5, add_comm]
    have h2 : ∀ k ∈ range n, 1 + (x ^ 2) ^ (n + k) * (w * x ^ (1 - 2 * (n : ℤ))) =
        1 + x ^ (2 * k + 1) * w := by
      intro k _
      rw [mul_left_comm, pw, show 2 * ((n + k : ℕ) : ℤ) + 1 - 2 * n = ((2 * k + 1 : ℕ) : ℤ) by
        push_cast; ring, zpow_natCast, mul_comm]
    rw [prod_congr rfl h1, prod_congr rfl h2, prod_mul_distrib, prod_mul_distrib, prod_const,
      card_range]
    rw [prod_zpow_neg_odd hx0 n, hc]
    ring
  -- The right side.
  have hR : ∀ j ∈ range (2 * n + 1),
      (x ^ 2) ^ (j.choose 2) * qBinom (x ^ 2) (2 * n) j * (w * x ^ (1 - 2 * (n : ℤ))) ^ j =
        c * (qBinom (x ^ 2) (2 * n) j * x ^ (((j : ℤ) - n) ^ 2) * w ^ ((j : ℤ) - n)) := by
    intro j _
    have e1 : (x ^ 2) ^ (j.choose 2) * (x ^ (1 - 2 * (n : ℤ))) ^ j =
        x ^ (-((n : ℤ) ^ 2)) * x ^ (((j : ℤ) - n) ^ 2) := by
      rw [← pow_mul, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_add₀ hx0,
        ← zpow_add₀ hx0]
      congr 1
      push_cast
      linear_combination two_mul_choose_two j
    have e2 : w ^ j = w ^ n * w ^ ((j : ℤ) - n) := by
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ hw]; congr 1; ring
    rw [hc, mul_pow, e2]
    linear_combination (qBinom (x ^ 2) (2 * n) j * w ^ n * w ^ ((j : ℤ) - n)) * e1
  rw [hL, sum_congr rfl hR, ← mul_sum] at QB
  exact mul_left_cancel₀ hc0 QB

/-! ### Bounds for `(q;q)_n` and the limit `(q;q)_∞` -/

section Bounds

variable {q : ℂ} (hq : ‖q‖ < 1)
include hq

theorem summable_norm_pow_succ : Summable fun k : ℕ ↦ ‖q ^ (k + 1)‖ := by
  simp_rw [norm_pow]
  exact (summable_geometric_of_lt_one (norm_nonneg _) hq).comp_injective (add_left_injective 1)

/-- `(q;q)_∞ = ∏_{k ≥ 1} (1 - q^k)`. -/
noncomputable def qPochInf (q : ℂ) : ℂ := ∏' k : ℕ, (1 - q ^ (k + 1))

theorem multipliable_one_sub_pow_succ : Multipliable fun k : ℕ ↦ (1 - q ^ (k + 1)) :=
  multipliable_one_sub_of_summable (summable_norm_pow_succ hq)

theorem tendsto_qPoch : Tendsto (qPoch q) atTop (𝓝 (qPochInf q)) :=
  (multipliable_one_sub_pow_succ hq).hasProd.tendsto_prod_nat

theorem qPochInf_ne_zero : qPochInf q ≠ 0 := by
  have h := tprod_one_add_ne_zero_of_summable (f := fun k : ℕ ↦ -q ^ (k + 1))
    (fun k ↦ by rw [← sub_eq_add_neg]; exact one_sub_pow_ne_zero hq k)
    (by simpa using summable_norm_pow_succ hq)
  simpa [qPochInf, ← sub_eq_add_neg] using h

/-- A uniform lower bound `δ ≤ |(q;q)_n|`, `δ > 0`. -/
theorem exists_le_norm_qPoch : ∃ δ > 0, ∀ n, δ ≤ ‖qPoch q n‖ := by
  set r := ‖q‖ with hr
  have hr0 : 0 ≤ r := norm_nonneg _
  have hsum : Summable fun k : ℕ ↦ ‖r ^ (k + 1)‖ := by
    simpa [hr, norm_pow] using summable_norm_pow_succ hq
  have hmul : Multipliable fun k : ℕ ↦ (1 - r ^ (k + 1)) := multipliable_one_sub_of_summable hsum
  have hfac : ∀ k : ℕ, 0 < 1 - r ^ (k + 1) := fun k ↦
    sub_pos.2 (pow_lt_one₀ hr0 hq (Nat.succ_ne_zero k))
  set pr : ℕ → ℝ := fun n ↦ ∏ k ∈ range n, (1 - r ^ (k + 1)) with hpr
  have hanti : Antitone pr := by
    refine antitone_nat_of_succ_le fun n ↦ ?_
    simp only [hpr, prod_range_succ]
    have h0 : 0 ≤ ∏ k ∈ range n, (1 - r ^ (k + 1)) := prod_nonneg fun k _ ↦ (hfac k).le
    have h1 : 1 - r ^ (n + 1) ≤ 1 := by have := pow_nonneg hr0 (n + 1); linarith
    nlinarith
  have htend : Tendsto pr atTop (𝓝 (∏' k : ℕ, (1 - r ^ (k + 1)))) := hmul.hasProd.tendsto_prod_nat
  have hne : ∏' k : ℕ, (1 - r ^ (k + 1)) ≠ 0 := by
    have h := tprod_one_add_ne_zero_of_summable (R := ℝ) (f := fun k : ℕ ↦ -r ^ (k + 1))
      (fun k ↦ by rw [← sub_eq_add_neg]; exact (hfac k).ne') (by simpa using hsum)
    simpa [← sub_eq_add_neg] using h
  have hnonneg : 0 ≤ ∏' k : ℕ, (1 - r ^ (k + 1)) :=
    ge_of_tendsto' htend fun n ↦ prod_nonneg fun k _ ↦ (hfac k).le
  refine ⟨_, lt_of_le_of_ne hnonneg (Ne.symm hne), fun n ↦ ?_⟩
  refine (hanti.le_of_tendsto htend n).trans ?_
  rw [qPoch, _root_.norm_prod]
  refine prod_le_prod₀ (fun k _ ↦ (hfac k).le) fun k _ ↦ ?_
  have := norm_sub_norm_le (1 : ℂ) (q ^ (k + 1))
  rwa [norm_one, norm_pow] at this

/-- A uniform upper bound for `|(q;q)_n|`. -/
theorem norm_qPoch_le (n : ℕ) : ‖qPoch q n‖ ≤ Real.exp (∑' k : ℕ, ‖q‖ ^ (k + 1)) := by
  have hs : Summable fun k : ℕ ↦ ‖q‖ ^ (k + 1) := by simpa [norm_pow] using summable_norm_pow_succ hq
  rw [qPoch, _root_.norm_prod]
  calc ∏ k ∈ range n, ‖1 - q ^ (k + 1)‖ ≤ ∏ k ∈ range n, Real.exp (‖q‖ ^ (k + 1)) := by
        refine prod_le_prod₀ (fun k _ ↦ norm_nonneg _) fun k _ ↦ ?_
        refine (norm_sub_le _ _).trans ?_
        rw [norm_one, norm_pow, add_comm]
        exact Real.add_one_le_exp _
    _ = Real.exp (∑ k ∈ range n, ‖q‖ ^ (k + 1)) := (Real.exp_sum _ _).symm
    _ ≤ Real.exp (∑' k : ℕ, ‖q‖ ^ (k + 1)) :=
        Real.exp_le_exp.2 (hs.sum_le_tsum _ fun k _ ↦ pow_nonneg (norm_nonneg _) _)

/-- A uniform bound for the Gaussian binomial coefficients. -/
theorem exists_norm_qBinom_le : ∃ B, ∀ N j, ‖qBinom q N j‖ ≤ B := by
  obtain ⟨δ, hδ, hle⟩ := exists_le_norm_qPoch hq
  set U := Real.exp (∑' k : ℕ, ‖q‖ ^ (k + 1))
  refine ⟨U / (δ * δ), fun N j ↦ ?_⟩
  have hU : 0 ≤ U := (Real.exp_pos _).le
  unfold qBinom
  split_ifs
  · rw [norm_div, norm_mul]
    exact div_le_div₀ hU (norm_qPoch_le hq N) (mul_pos hδ hδ) (mul_le_mul (hle j) (hle _) hδ.le
      (norm_nonneg _))
  · rw [norm_zero]; positivity

end Bounds

/-! ### The limit `n → ∞` -/

/-- For `0 < |x| < 1` and `w ≠ 0` the terms `x^{m²} w^m` are the terms of a Jacobi theta series. -/
theorem exists_jacobiTheta₂_term_eq {x w : ℂ} (hx0 : x ≠ 0) (hx : ‖x‖ < 1) (hw : w ≠ 0) :
    ∃ z τ : ℂ, 0 < τ.im ∧ ∀ m : ℤ, jacobiTheta₂_term m z τ = x ^ (m ^ 2) * w ^ m := by
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  refine ⟨log w / (2 * π * I), log x / (π * I), ?_, fun m ↦ ?_⟩
  · have e : log x / (π * I) = (-I * log x) / (π : ℝ) := by
      field_simp
      ring_nf
      rw [I_sq]
      ring
    rw [e, div_ofReal_im]
    have : (-I * log x).im = -Real.log ‖x‖ := by simp [log_re]
    rw [this]
    exact div_pos (neg_pos.2 (Real.log_neg (norm_pos_iff.2 hx0) hx)) Real.pi_pos
  · rw [jacobiTheta₂_term, show 2 * π * I * m * (log w / (2 * π * I)) + π * I * m ^ 2 *
        (log x / (π * I)) = (m : ℂ) * log w + ((m ^ 2 : ℤ) : ℂ) * log x by
        field_simp; push_cast; ring,
      Complex.exp_add, Complex.exp_int_mul, Complex.exp_int_mul, exp_log hw, exp_log hx0, mul_comm]

/-- The finite sum of `finite_jacobi` as a sum over `ℤ`. -/
theorem sum_range_eq_tsum_ite {x w : ℂ} (n : ℕ) :
    ∑ j ∈ range (2 * n + 1), qBinom (x ^ 2) (2 * n) j * x ^ (((j : ℤ) - n) ^ 2) * w ^ ((j : ℤ) - n) =
      ∑' m : ℤ, if m ∈ Icc (-(n : ℤ)) n then
        qBinom (x ^ 2) (2 * n) (m + n).toNat * (x ^ (m ^ 2) * w ^ m) else 0 := by
  rw [tsum_eq_sum (s := Icc (-(n : ℤ)) n) (fun m hm ↦ if_neg hm)]
  rw [sum_congr rfl fun m hm ↦ if_pos hm]
  refine sum_nbij' (fun j : ℕ ↦ (j : ℤ) - n) (fun m : ℤ ↦ (m + n).toNat) ?_ ?_ ?_ ?_ ?_
  · intro j hj; simp only [mem_range] at hj; simp only [mem_Icc]; omega
  · intro m hm; simp only [mem_Icc] at hm; simp only [mem_range]; omega
  · intro j _; simp
  · intro m hm; simp only [mem_Icc] at hm; omega
  · intro j _
    simp only [sub_add_cancel, Int.toNat_natCast]
    ring

/-- Jacobi's triple product identity with `w` in place of `z²`. -/
theorem jacobi_triple_product {x w : ℂ} (hx : ‖x‖ < 1) (hw : w ≠ 0) :
    Summable (fun m : ℤ ↦ x ^ (m ^ 2) * w ^ m) ∧
    HasProd (fun n : ℕ ↦ (1 - x ^ (2 * (n + 1))) * (1 + x ^ (2 * n + 1) * w) *
      (1 + x ^ (2 * n + 1) * w⁻¹)) (∑' m : ℤ, x ^ (m ^ 2) * w ^ m) := by
  rcases eq_or_ne x 0 with rfl | hx0
  · have hz : ∀ m : ℤ, m ≠ 0 → (0 : ℂ) ^ (m ^ 2) * w ^ m = 0 := fun m hm ↦ by
      rw [zero_zpow _ (pow_ne_zero 2 hm), zero_mul]
    refine ⟨summable_of_ne_finset_zero (s := {0}) fun m hm ↦ hz m (by simpa using hm), ?_⟩
    rw [tsum_eq_single 0 hz]
    simp
  obtain ⟨z, τ, hτ, hT⟩ := exists_jacobiTheta₂_term_eq hx0 hx hw
  set T : ℤ → ℂ := fun m ↦ x ^ (m ^ 2) * w ^ m with hTdef
  have hTsum : Summable T := by
    have := (summable_jacobiTheta₂_term_iff z τ).2 hτ
    simpa [hT] using this
  refine ⟨hTsum, ?_⟩
  set q : ℂ := x ^ 2 with hqdef
  have hq : ‖q‖ < 1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hx two_ne_zero
  set P := qPochInf q with hP
  have hP0 : P ≠ 0 := qPochInf_ne_zero hq
  -- Multipliability of the three factors.
  have hgeom (c : ℂ) : Summable fun n : ℕ ↦ ‖x ^ (2 * n + 1) * c‖ := by
    have h := (summable_geometric_of_lt_one (norm_nonneg q) hq).mul_left (‖x‖ * ‖c‖)
    refine h.congr fun n ↦ ?_
    simp only [norm_mul, norm_pow, hqdef]
    ring
  have ha : Multipliable fun n : ℕ ↦ (1 - x ^ (2 * (n + 1))) := by
    simpa [pow_mul, hqdef] using multipliable_one_sub_pow_succ hq
  have hb := multipliable_one_add_of_summable (hgeom w)
  have hc := multipliable_one_add_of_summable (hgeom w⁻¹)
  have hmul := (ha.hasProd.mul hb.hasProd).mul hc.hasProd
  have hA := hmul.multipliable.hasProd.tendsto_prod_nat
  -- The partial products.
  set G : ℕ → ℤ → ℂ := fun n m ↦ if m ∈ Icc (-(n : ℤ)) n then
    qBinom q (2 * n) (m + n).toNat * T m else 0 with hG
  have hpart : ∀ n : ℕ, ∏ k ∈ range n, ((1 - x ^ (2 * (k + 1))) * (1 + x ^ (2 * k + 1) * w) *
      (1 + x ^ (2 * k + 1) * w⁻¹)) = qPoch q n * ∑' m, G n m := by
    intro n
    have e1 : ∏ k ∈ range n, (1 - x ^ (2 * (k + 1))) = qPoch q n := by
      simp [qPoch, hqdef, pow_mul]
    rw [hG, ← sum_range_eq_tsum_ite n, ← finite_jacobi hx0 hx hw n, ← e1, ← prod_mul_distrib]
    exact prod_congr rfl fun k _ ↦ by ring
  -- Tannery's theorem for `∑' m, G n m`.
  obtain ⟨B, hB⟩ := exists_norm_qBinom_le hq
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 0)
  have hup (m : ℤ) : Tendsto (fun n : ℕ ↦ (m + n).toNat) atTop atTop :=
    tendsto_atTop_atTop.2 fun b ↦ ⟨b + m.natAbs, fun n hn ↦ by omega⟩
  have hup' (m : ℤ) : Tendsto (fun n : ℕ ↦ 2 * n - (m + n).toNat) atTop atTop :=
    tendsto_atTop_atTop.2 fun b ↦ ⟨b + m.natAbs, fun n hn ↦ by omega⟩
  have hup2 : Tendsto (fun n : ℕ ↦ 2 * n) atTop atTop :=
    tendsto_atTop_atTop.2 fun b ↦ ⟨b, fun n hn ↦ by omega⟩
  have hpt (m : ℤ) : Tendsto (fun n ↦ G n m) atTop (𝓝 (T m / P)) := by
    have hlim : Tendsto (fun n : ℕ ↦ qPoch q (2 * n) / (qPoch q (m + n).toNat *
        qPoch q (2 * n - (m + n).toNat)) * T m) atTop (𝓝 (P / (P * P) * T m)) :=
      (((tendsto_qPoch hq).comp hup2).div (((tendsto_qPoch hq).comp (hup m)).mul
        ((tendsto_qPoch hq).comp (hup' m))) (mul_ne_zero hP0 hP0)).mul_const _
    rw [show T m / P = P / (P * P) * T m by field_simp]
    refine hlim.congr' (eventually_atTop.2 ⟨m.natAbs, fun n hn ↦ ?_⟩)
    have hmem : m ∈ Icc (-(n : ℤ)) n := by simp only [mem_Icc]; omega
    simp only [hG, if_pos hmem, qBinom, if_pos (show (m + n).toNat ≤ 2 * n by omega)]
  have hbd : ∀ᶠ n in atTop, ∀ m, ‖G n m‖ ≤ B * ‖T m‖ := Eventually.of_forall fun n m ↦ by
    simp only [hG]
    split_ifs
    · rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hB _ _) (norm_nonneg _)
    · rw [norm_zero]; positivity
  have htann := tendsto_tsum_of_dominated_convergence (hTsum.norm.mul_left B) hpt hbd
  have hlim := (tendsto_qPoch hq).mul htann
  rw [tsum_div_const, mul_div_cancel₀ _ hP0] at hlim
  have heq := tendsto_nhds_unique (hA.congr hpart) hlim
  rw [← heq]
  exact hmul.multipliable.hasProd

/-- **Theorem 14.6** (Jacobi's triple product identity, Apostol). For complex `x, z` with `|x| < 1`
and `z ≠ 0`, `∏_{n=1}^∞ (1 - x^{2n})(1 + x^{2n-1} z²)(1 + x^{2n-1} z^{-2}) = ∑_{m=-∞}^{∞} x^{m²} z^{2m}`,
the series converging absolutely. -/
@[kb "apostol1976" "Thm 14.6, p. 319"]
theorem apostol_thm_14_6 {x z : ℂ} (hx : ‖x‖ < 1) (hz : z ≠ 0) :
    Summable (fun m : ℤ ↦ x ^ (m ^ 2) * z ^ (2 * m)) ∧
    HasProd (fun n : ℕ ↦ (1 - x ^ (2 * (n + 1))) * (1 + x ^ (2 * n + 1) * z ^ 2) *
      (1 + x ^ (2 * n + 1) * z ^ (-2 : ℤ))) (∑' m : ℤ, x ^ (m ^ 2) * z ^ (2 * m)) := by
  have h := jacobi_triple_product hx (pow_ne_zero 2 hz)
  have e1 : ∀ m : ℤ, (z ^ 2) ^ m = z ^ (2 * m) := fun m ↦ by
    rw [← zpow_natCast, ← zpow_mul]; rfl
  have e2 : (z ^ 2)⁻¹ = z ^ (-2 : ℤ) := by rw [zpow_neg]; rfl
  simp only [e1, e2] at h
  exact h

end NTKB.Apostol
