/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Apostol.Primes.MertensPNT
import NTKB.Analytic.Apostol.ArithmeticFunctions.Derivative

/-!
# The prime number theorem implies `M(x) = o(x)` (Apostol, Theorems 3.12, 3.13 and 4.14)

* Theorem 3.12, first identity: `∑_{n ≤ x} μ(n) ⌊x/n⌋ = 1` for `x ≥ 1`;
* Theorem 3.13: `|∑_{n ≤ x} μ(n)/n| ≤ 1` for `x ≥ 1`;
* the identity `-H(x) = ∑_{n ≤ x} μ(n) ψ(x/n)` (Apostol (34), from `-μ(n) log n = (μ * Λ)(n)`,
  here via the derivative rule 2.26(c));
* **Theorem 4.14**: `ψ(x)/x → 1` implies `H(x)/(x log x) → 0`, hence (Theorem 4.13)
  `M(x)/x → 0`.
-/

open Finset ArithmeticFunction Filter Topology Real Chebyshev
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

namespace NTKB.Apostol

/-- **Apostol, Theorem 3.12**, first identity: `∑_{n ≤ x} μ(n) ⌊x/n⌋ = 1` for `x ≥ 1`. -/
@[kb "apostol1976" "Thm 3.12, p. 66"]
theorem sum_moebius_mul_floor {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ Ioc 0 ⌊x⌋₊, (μ n : ℝ) * (⌊x / n⌋₊ : ℝ) = 1 := by
  have hN1 : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
  have h := sum_Ioc_mul_zeta_eq_sum (μ : ArithmeticFunction ℝ) ⌊x⌋₊
  rw [coe_moebius_mul_coe_zeta] at h
  rw [sum_eq_single 1 (fun b _ hb ↦ ArithmeticFunction.one_apply_ne hb)
    (fun h1 ↦ absurd (mem_Ioc.2 ⟨one_pos, hN1⟩) h1), ArithmeticFunction.one_one] at h
  refine Eq.trans ?_ h.symm
  refine sum_congr rfl fun n _ ↦ ?_
  rw [intCoe_apply, Nat.floor_div_natCast]

/-- **Apostol, Theorem 3.13.** `|∑_{n ≤ x} μ(n)/n| ≤ 1` for `x ≥ 1`. -/
@[kb "apostol1976" "Thm 3.13, p. 66"]
theorem abs_sum_moebius_div_le {x : ℝ} (hx : 1 ≤ x) :
    |∑ n ∈ Ioc 0 ⌊x⌋₊, (μ n : ℝ) / n| ≤ 1 := by
  have hx0 : 0 < x := by linarith
  set N := ⌊x⌋₊
  have hN1 : 1 ≤ N := Nat.le_floor (by exact_mod_cast hx)
  -- `x ∑ μ(n)/n = 1 + ∑ μ(n) {x/n}`
  have e : x * ∑ n ∈ Ioc 0 N, (μ n : ℝ) / n =
      1 + ∑ n ∈ Ioc 0 N, (μ n : ℝ) * (x / n - ⌊x / n⌋₊) := by
    rw [← sum_moebius_mul_floor hx, mul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun n _ ↦ by ring
  have hR : |∑ n ∈ Ioc 0 N, (μ n : ℝ) * (x / n - ⌊x / n⌋₊)| ≤ x - 1 := by
    have hfr : ∀ n : ℕ, 0 ≤ x / n - ⌊x / n⌋₊ ∧ x / n - ⌊x / n⌋₊ < 1 := fun n ↦
      ⟨sub_nonneg.2 (Nat.floor_le (div_nonneg hx0.le (Nat.cast_nonneg _))),
        by have := Nat.lt_floor_add_one (x / n); linarith⟩
    calc |∑ n ∈ Ioc 0 N, (μ n : ℝ) * (x / n - ⌊x / n⌋₊)|
        ≤ ∑ n ∈ Ioc 0 N, (x / n - ⌊x / n⌋₊) := by
          refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun n _ ↦ ?_)
          rw [abs_mul, abs_of_nonneg (hfr n).1]
          have : |(μ n : ℝ)| ≤ 1 := by exact_mod_cast abs_moebius_le_one
          nlinarith [(hfr n).1]
      _ = (x - N) + ∑ n ∈ Ioc 1 N, (x / n - ⌊x / n⌋₊) := by
          rw [← add_sum_Ioc_eq_sum_Ioc_aux hN1]
          simp [N]
      _ ≤ (x - N) + ∑ n ∈ Ioc 1 N, (1 : ℝ) := by
          gcongr with n hn; exact (hfr n).2.le
      _ = x - 1 := by
          rw [sum_const, Nat.card_Ioc, nsmul_eq_mul, mul_one, Nat.cast_sub hN1]; ring
  have h1 : |x * ∑ n ∈ Ioc 0 N, (μ n : ℝ) / n| ≤ x := by
    rw [e]
    calc |1 + ∑ n ∈ Ioc 0 N, (μ n : ℝ) * (x / n - ⌊x / n⌋₊)| ≤ 1 + (x - 1) :=
          (abs_add_le _ _).trans (by rw [abs_one]; linarith)
      _ = x := by ring
  rw [abs_mul, abs_of_pos hx0] at h1
  exact le_of_mul_le_mul_left (by linarith) hx0
where
  add_sum_Ioc_eq_sum_Ioc_aux {N : ℕ} (hN1 : 1 ≤ N) {f : ℕ → ℝ} :
      f 1 + ∑ n ∈ Ioc 1 N, f n = ∑ n ∈ Ioc 0 N, f n := by
    rw [← sum_Ioc_consecutive f (Nat.zero_le 1) hN1]
    simp

/-- `-H(x) = ∑_{n ≤ x} μ(n) ψ(x/n)` (Apostol (34)). -/
theorem sum_moebius_mul_psi_div (x : ℝ) :
    ∑ n ∈ Ioc 0 ⌊x⌋₊, (μ n : ℝ) * ψ (x / n) = -mertensLog x := by
  -- `μ * Λ = -μ log`: from 2.26(c) for `μ = u⁻¹`
  have hinv := arithDeriv_inv (f := (ζ : ArithmeticFunction ℝ)) (g := (μ : ArithmeticFunction ℝ))
    coe_zeta_mul_coe_moebius
  have hzeta : arithDeriv (ζ : ArithmeticFunction ℝ) = ArithmeticFunction.log := by
    ext n
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · simp [natCoe_apply, zeta_apply, hn, log_apply]
  rw [hzeta] at hinv
  have hμΛ : (μ : ArithmeticFunction ℝ) * Λ = -arithDeriv (μ : ArithmeticFunction ℝ) := by
    rw [hinv, neg_neg, ← log_mul_moebius_eq_vonMangoldt]
    ring
  have h := sum_Ioc_mul_eq_sum_sum (μ : ArithmeticFunction ℝ) Λ ⌊x⌋₊
  calc ∑ n ∈ Ioc 0 ⌊x⌋₊, (μ n : ℝ) * ψ (x / n)
      = ∑ n ∈ Ioc 0 ⌊x⌋₊, (μ : ArithmeticFunction ℝ) n * ∑ m ∈ Ioc 0 (⌊x⌋₊ / n), Λ m :=
        sum_congr rfl fun n _ ↦ by rw [Chebyshev.psi, Nat.floor_div_natCast, intCoe_apply]
    _ = ∑ n ∈ Ioc 0 ⌊x⌋₊, ((μ : ArithmeticFunction ℝ) * Λ) n := h.symm
    _ = -mertensLog x := by
        rw [hμΛ, mertensLog, ← sum_neg_distrib]
        refine sum_congr rfl fun n _ ↦ ?_
        rw [neg_apply, arithDeriv_apply, smul_eq_mul, intCoe_apply, mul_comm]

/-- **Apostol, Theorem 4.14.** The prime number theorem `ψ(x)/x → 1` implies
`H(x)/(x log x) → 0`. -/
@[kb "apostol1976" "Thm 4.14, p. 92"]
theorem tendsto_mertensLog_div_of_psi (hpnt : Tendsto (fun x ↦ ψ x / x) atTop (𝓝 1)) :
    Tendsto (fun x ↦ mertensLog x / (x * Real.log x)) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε₀ hε₀
  set ε := min (ε₀ / 3) (1 / 2) with hε
  have hε0 : 0 < ε := by positivity
  have hε1 : ε ≤ ε₀ / 3 := min_le_left _ _
  -- `|ψ(y) - y| ≤ ε y` for `y ≥ A`
  obtain ⟨A₀, hA₀⟩ := Metric.tendsto_atTop.1 hpnt ε hε0
  set A := max A₀ 1
  have hA1 : 1 ≤ A := le_max_right _ _
  have hA0 : A ≠ 0 := by linarith
  have hψ : ∀ y, A ≤ y → |ψ y - y| ≤ ε * y := by
    intro y hy
    have hy0 : 0 < y := by linarith
    have := hA₀ y (le_trans (le_max_left _ _) hy)
    rw [Real.dist_eq] at this
    have e : ψ y / y - 1 = (ψ y - y) / y := by field_simp
    rw [e, abs_div, abs_of_pos hy0, div_lt_iff₀ hy0] at this
    exact this.le
  set K := 1 + ε + ψ A
  have hK0 : 0 < K := by have := psi_nonneg A; positivity
  -- for large `x`, `K / log x ≤ ε`
  obtain ⟨B₀, hB₀⟩ := (Real.tendsto_log_atTop.eventually_ge_atTop (K / ε)).exists_forall_of_atTop
  refine ⟨max (max B₀ A) (Real.exp 1), fun x hx ↦ ?_⟩
  have hxA : A ≤ x := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hx)
  have hxB : B₀ ≤ x := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hx)
  have hxe : Real.exp 1 ≤ x := le_trans (le_max_right _ _) hx
  have hx1 : 1 ≤ x := le_trans hA1 hxA
  have hx0 : 0 < x := by linarith
  have hlog1 : 1 ≤ Real.log x := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hxe
  have hlogK : K / ε ≤ Real.log x := hB₀ x hxB
  -- split `∑_{n ≤ x} μ(n) ψ(x/n)` at `y = x/A`
  set y := x / A
  have hy1 : 1 ≤ y := by rw [le_div_iff₀ (by linarith)]; linarith
  have hyx : y ≤ x := div_le_self hx0.le hA1
  have hfl : ⌊y⌋₊ ≤ ⌊x⌋₊ := Nat.floor_le_floor hyx
  have hH : |mertensLog x| = |∑ n ∈ Ioc 0 ⌊x⌋₊, (μ n : ℝ) * ψ (x / n)| := by
    rw [sum_moebius_mul_psi_div, abs_neg]
  rw [← sum_Ioc_consecutive _ (Nat.zero_le _) hfl] at hH
  -- first part: `n ≤ y`, so `x/n ≥ A`
  have hP1 : |∑ n ∈ Ioc 0 ⌊y⌋₊, (μ n : ℝ) * ψ (x / n)| ≤ x + ε * x * (1 + Real.log x) := by
    have e : ∑ n ∈ Ioc 0 ⌊y⌋₊, (μ n : ℝ) * ψ (x / n) =
        x * ∑ n ∈ Ioc 0 ⌊y⌋₊, (μ n : ℝ) / n +
          ∑ n ∈ Ioc 0 ⌊y⌋₊, (μ n : ℝ) * (ψ (x / n) - x / n) := by
      rw [mul_sum, ← sum_add_distrib]
      exact sum_congr rfl fun n _ ↦ by ring
    rw [e]
    have h1 : |x * ∑ n ∈ Ioc 0 ⌊y⌋₊, (μ n : ℝ) / n| ≤ x := by
      rw [abs_mul, abs_of_pos hx0]
      calc x * |∑ n ∈ Ioc 0 ⌊y⌋₊, (μ n : ℝ) / n| ≤ x * 1 :=
            mul_le_mul_of_nonneg_left (abs_sum_moebius_div_le hy1) hx0.le
        _ = x := mul_one x
    have h2 : |∑ n ∈ Ioc 0 ⌊y⌋₊, (μ n : ℝ) * (ψ (x / n) - x / n)| ≤
        ε * x * (1 + Real.log x) := by
      refine (abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ n ∈ Ioc 0 ⌊y⌋₊, |(μ n : ℝ) * (ψ (x / n) - x / n)|
          ≤ ∑ n ∈ Ioc 0 ⌊y⌋₊, ε * x * (1 / n) := by
            refine sum_le_sum fun n hn ↦ ?_
            have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Ioc.1 hn).1
            have hny : (n : ℝ) ≤ y := by
              have : (n : ℝ) ≤ ⌊y⌋₊ := by exact_mod_cast (mem_Ioc.1 hn).2
              linarith [Nat.floor_le (by linarith : (0 : ℝ) ≤ y)]
            have hAxn : A ≤ x / n := by
              rw [le_div_iff₀ hn0]
              have : n * A ≤ y * A := mul_le_mul_of_nonneg_right hny (by linarith)
              rw [show y * A = x by simp only [y]; field_simp] at this
              linarith
            rw [abs_mul]
            have hμ : |(μ n : ℝ)| ≤ 1 := by exact_mod_cast abs_moebius_le_one
            calc |(μ n : ℝ)| * |ψ (x / n) - x / n| ≤ 1 * (ε * (x / n)) :=
                  mul_le_mul hμ (hψ _ hAxn) (abs_nonneg _) zero_le_one
              _ = ε * x * (1 / n) := by ring
        _ = ε * x * ∑ n ∈ Ioc 0 ⌊y⌋₊, (1 / n : ℝ) := by rw [mul_sum]
        _ ≤ ε * x * (1 + Real.log x) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            refine (sum_Ioc_inv_le_one_add_log hy1).trans ?_
            have := Real.log_le_log (by linarith) hyx
            linarith
    exact (abs_add_le _ _).trans (add_le_add h1 h2)
  -- second part: `y < n ≤ x`, so `x/n < A` and `ψ(x/n) ≤ ψ(A)`
  have hP2 : |∑ n ∈ Ioc ⌊y⌋₊ ⌊x⌋₊, (μ n : ℝ) * ψ (x / n)| ≤ x * ψ A := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ n ∈ Ioc ⌊y⌋₊ ⌊x⌋₊, |(μ n : ℝ) * ψ (x / n)| ≤ ∑ n ∈ Ioc ⌊y⌋₊ ⌊x⌋₊, ψ A := by
          refine sum_le_sum fun n hn ↦ ?_
          have hn1 : ⌊y⌋₊ + 1 ≤ n := (mem_Ioc.1 hn).1
          have hn0 : (0 : ℝ) < n := by
            have : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
            linarith
          have hyn : y < n := by
            have := Nat.lt_floor_add_one y
            have : ((⌊y⌋₊ + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn1
            push_cast at this; linarith
          have hxn : x / n ≤ A := by
            rw [div_le_iff₀ hn0]
            have : y * A < n * A := mul_lt_mul_of_pos_right hyn (by linarith)
            rw [show y * A = x by simp only [y]; field_simp] at this
            linarith
          rw [abs_mul, abs_of_nonneg (psi_nonneg _)]
          have hμ : |(μ n : ℝ)| ≤ 1 := by exact_mod_cast abs_moebius_le_one
          calc |(μ n : ℝ)| * ψ (x / n) ≤ 1 * ψ A :=
                mul_le_mul hμ (psi_mono hxn) (psi_nonneg _) zero_le_one
            _ = ψ A := one_mul _
      _ = (⌊x⌋₊ - ⌊y⌋₊ : ℕ) * ψ A := by rw [sum_const, Nat.card_Ioc, nsmul_eq_mul]
      _ ≤ x * ψ A := by
          refine mul_le_mul_of_nonneg_right ?_ (psi_nonneg _)
          have : ((⌊x⌋₊ - ⌊y⌋₊ : ℕ) : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast Nat.sub_le _ _
          linarith [Nat.floor_le hx0.le]
  have hHb : |mertensLog x| ≤ K * x + ε * (x * Real.log x) := by
    rw [hH]
    refine (abs_add_le _ _).trans ?_
    have := add_le_add hP1 hP2
    simp only [K]
    nlinarith
  -- conclude
  have hxl : 0 < x * Real.log x := by positivity
  rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos hxl, div_lt_iff₀ hxl]
  have hKx : K * x ≤ ε * (x * Real.log x) := by
    rw [div_le_iff₀ hε0] at hlogK
    nlinarith
  nlinarith

/-- **Apostol, Theorem 4.14 with 4.13:** the prime number theorem implies `M(x) = o(x)`. -/
@[kb "apostol1976" "Thm 4.14, p. 92"]
theorem tendsto_mertens_div_of_psi (hpnt : Tendsto (fun x ↦ ψ x / x) atTop (𝓝 1)) :
    Tendsto (fun x ↦ mertens x / x) atTop (𝓝 0) :=
  tendsto_mertens_div_iff.2 (tendsto_mertensLog_div_of_psi hpnt)

end NTKB.Apostol
