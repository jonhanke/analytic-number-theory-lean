/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Apostol.Partitions.JacobiTriple
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# Jacobi's identity for the cube of Euler's product (Apostol, Theorem 14.7)

For `|x| < 1`: `∏_{n ≥ 1} (1 - xⁿ)³ = ∑_{m ≥ 0} (-1)^m (2m + 1) x^{m(m+1)/2}`.

Apostol replaces `z²` by `-xz` in the triple product identity, cancels the factor `1 - z⁻¹` and puts
`z = 1`. We do the same at the level of the finite identity `finite_jacobi` (with `w = -xu`), where
"cancel `1 - u⁻¹` and put `u = 1`" is differentiation at `u = 1` (`finite_jacobi_cube`):
`(q;q)_{n+1} (q;q)_n = ∑_{|m| ≤ n+1} [2n+2, n+1+m]_q (-1)^m m x^{m²+m}`, `q = x²`; then `n → ∞` by
Tannery's theorem as in Theorem 14.6, and `x` is replaced by a square root of `x`.
-/

open Complex Finset Filter
open scoped Topology Real

namespace NTKB.Apostol

/-- The reindexing `j ↦ j - n` from `range (2n + 1)` to `[-n, n]`. -/
theorem sum_range_eq_sum_Icc (n : ℕ) (F : ℕ → ℤ → ℂ) :
    ∑ j ∈ range (2 * n + 1), F j ((j : ℤ) - n) =
      ∑ m ∈ Icc (-(n : ℤ)) n, F (m + n).toNat m := by
  refine sum_nbij' (fun j : ℕ ↦ (j : ℤ) - n) (fun m : ℤ ↦ (m + n).toNat) ?_ ?_ ?_ ?_ ?_
  · intro j hj; simp only [mem_range] at hj; simp only [mem_Icc]; omega
  · intro m hm; simp only [mem_Icc] at hm; simp only [mem_range]; omega
  · intro j _; simp
  · intro m hm; simp only [mem_Icc] at hm; omega
  · intro j _
    simp only [sub_add_cancel, Int.toNat_natCast]

/-- The coefficients of the finite identity at `w = -xu`. -/
noncomputable def cubeCoeff (x : ℂ) (N : ℕ) (m : ℤ) : ℂ :=
  qBinom (x ^ 2) (2 * N) (m + N).toNat * ((-1) ^ m * x ^ (m ^ 2 + m))

/-- The cofactor of `1 - u⁻¹`. -/
noncomputable def cubeCofactor (x : ℂ) (n : ℕ) (u : ℂ) : ℂ :=
  (∏ k ∈ range (n + 1), (1 - x ^ (2 * k + 2) * u)) * ∏ k ∈ range n, (1 - x ^ (2 * k + 2) * u⁻¹)

/-- The finite triple product at `w = -xu`, with the factor `1 - u⁻¹` split off. -/
theorem one_sub_inv_mul_cubeCofactor {x : ℂ} (hx0 : x ≠ 0) (hx : ‖x‖ < 1) (n : ℕ) {u : ℂ}
    (hu : u ≠ 0) :
    (1 - u⁻¹) * cubeCofactor x n u = ∑ m ∈ Icc (-((n + 1 : ℕ) : ℤ)) (n + 1 : ℕ),
      cubeCoeff x (n + 1) m * u ^ m := by
  have hw : -x * u ≠ 0 := mul_ne_zero (neg_ne_zero.2 hx0) hu
  have h := finite_jacobi hx0 hx hw (n + 1)
  rw [sum_range_eq_sum_Icc (n + 1) (fun j m ↦ qBinom (x ^ 2) (2 * (n + 1)) j * x ^ (m ^ 2) *
    (-x * u) ^ m)] at h
  have e1 : ∀ k : ℕ, (1 + x ^ (2 * k + 1) * (-x * u)) = 1 - x ^ (2 * k + 2) * u := fun k ↦ by ring
  have e2 : ∀ k : ℕ, (1 + x ^ (2 * k + 1) * (-x * u)⁻¹) = 1 - x ^ (2 * k) * u⁻¹ := fun k ↦ by
    rw [mul_inv, pow_succ]; field_simp; ring
  simp only [e1, e2, prod_mul_distrib] at h
  rw [prod_range_succ' (fun k ↦ 1 - x ^ (2 * k) * u⁻¹)] at h
  simp only [mul_zero, pow_zero, one_mul, show ∀ k : ℕ, 2 * (k + 1) = 2 * k + 2 from
    fun k ↦ by ring] at h
  have hsum : ∑ m ∈ Icc (-((n + 1 : ℕ) : ℤ)) (n + 1 : ℕ), cubeCoeff x (n + 1) m * u ^ m =
      ∑ m ∈ Icc (-((n + 1 : ℕ) : ℤ)) (n + 1 : ℕ),
        qBinom (x ^ 2) (2 * (n + 1)) (m + ↑(n + 1)).toNat * x ^ (m ^ 2) * (-x * u) ^ m := by
    refine sum_congr rfl fun m _ ↦ ?_
    rw [cubeCoeff, mul_zpow, show (-x) ^ m = (-1) ^ m * x ^ m by
      rw [neg_eq_neg_one_mul, mul_zpow], zpow_add₀ hx0]
    ring
  rw [cubeCofactor, hsum]
  linear_combination h

/-- Differentiating at `u = 1`: `(q;q)_{n+1} (q;q)_n = ∑_{|m| ≤ n+1} [2n+2, n+1+m]_q (-1)^m m x^{m²+m}`. -/
theorem finite_jacobi_cube {x : ℂ} (hx0 : x ≠ 0) (hx : ‖x‖ < 1) (n : ℕ) :
    qPoch (x ^ 2) (n + 1) * qPoch (x ^ 2) n =
      ∑ m ∈ Icc (-((n + 1 : ℕ) : ℤ)) (n + 1 : ℕ), cubeCoeff x (n + 1) m * m := by
  set H := cubeCofactor x n
  have hH1 : H 1 = qPoch (x ^ 2) (n + 1) * qPoch (x ^ 2) n := by
    simp only [H, cubeCofactor, qPoch, inv_one, mul_one, ← pow_mul]
    rfl
  have hHd : DifferentiableAt ℂ H 1 := by
    show DifferentiableAt ℂ (fun u ↦ (∏ k ∈ range (n + 1), (1 - x ^ (2 * k + 2) * u)) *
      ∏ k ∈ range n, (1 - x ^ (2 * k + 2) * u⁻¹)) 1
    refine DifferentiableAt.mul (DifferentiableAt.fun_finsetProd fun k _ ↦ by fun_prop)
      (DifferentiableAt.fun_finsetProd fun k _ ↦ ?_)
    exact (differentiableAt_const _).sub ((differentiableAt_const _).mul
      (differentiableAt_inv one_ne_zero))
  have h1 : HasDerivAt (fun u : ℂ ↦ 1 - u⁻¹) 1 1 := by
    simpa using (hasDerivAt_inv (one_ne_zero (α := ℂ))).const_sub 1
  have hL : HasDerivAt (fun u ↦ (1 - u⁻¹) * H u) (H 1) 1 := by
    simpa using h1.fun_mul hHd.hasDerivAt
  have hR : HasDerivAt (fun u ↦ ∑ m ∈ Icc (-((n + 1 : ℕ) : ℤ)) (n + 1 : ℕ),
      cubeCoeff x (n + 1) m * u ^ m)
      (∑ m ∈ Icc (-((n + 1 : ℕ) : ℤ)) (n + 1 : ℕ), cubeCoeff x (n + 1) m * m) 1 := by
    have := HasDerivAt.fun_sum (u := Icc (-((n + 1 : ℕ) : ℤ)) (n + 1 : ℕ))
      (A := fun m u ↦ cubeCoeff x (n + 1) m * u ^ m)
      (A' := fun m ↦ cubeCoeff x (n + 1) m * ((m : ℂ) * 1 ^ (m - 1)))
      (fun m _ ↦ (hasDerivAt_zpow m 1 (Or.inl one_ne_zero)).const_mul _)
    simpa using this
  have hev : (fun u ↦ (1 - u⁻¹) * H u) =ᶠ[𝓝 1] fun u ↦ ∑ m ∈ Icc (-((n + 1 : ℕ) : ℤ)) (n + 1 : ℕ),
      cubeCoeff x (n + 1) m * u ^ m := by
    filter_upwards [isOpen_ne.mem_nhds (one_ne_zero (α := ℂ))] with u hu
    exact one_sub_inv_mul_cubeCofactor hx0 hx n hu
  rw [← hH1]
  exact (hL.congr_of_eventuallyEq hev.symm).unique hR

/-- `∏_{n ≥ 1} (1 - x^{2n})³ = ∑_{m ∈ ℤ} (-1)^m m x^{m² + m}` for `|x| < 1`. -/
theorem jacobi_cube {x : ℂ} (hx : ‖x‖ < 1) :
    Summable (fun m : ℤ ↦ (-1) ^ m * m * x ^ (m ^ 2 + m)) ∧
    HasProd (fun n : ℕ ↦ (1 - (x ^ 2) ^ (n + 1)) ^ 3) (∑' m : ℤ, (-1) ^ m * m * x ^ (m ^ 2 + m)) := by
  set T : ℤ → ℂ := fun m ↦ (-1) ^ m * m * x ^ (m ^ 2 + m) with hTdef
  rcases eq_or_ne x 0 with rfl | hx0
  · have hz : ∀ m : ℤ, m ≠ -1 → T m = 0 := by
      intro m hm
      rcases eq_or_ne m 0 with rfl | hm0
      · simp [hTdef]
      · have : m ^ 2 + m ≠ 0 := by
          rw [show m ^ 2 + m = m * (m + 1) by ring]
          exact mul_ne_zero hm0 (by omega)
        simp [hTdef, zero_zpow _ this]
    refine ⟨summable_of_ne_finset_zero (s := {-1}) fun m hm ↦ hz m (by simpa using hm), ?_⟩
    rw [tsum_eq_single (-1) hz]
    simp [hTdef]
  obtain ⟨z, τ, hτ, hθ⟩ := exists_jacobiTheta₂_term_eq hx0 hx hx0
  have hπ : (0 : ℝ) < 2 * π := by positivity
  have hTsum : Summable T := by
    refine Summable.of_norm_bounded
      (((summable_jacobiTheta₂'_term_iff z τ).2 hτ).norm.div_const (2 * π)) fun m ↦ le_of_eq ?_
    rw [jacobiTheta₂'_term, hθ, hTdef]
    simp only [norm_mul, norm_zpow, norm_neg, norm_one, one_zpow, one_mul, norm_ofNat,
      Complex.norm_real, norm_I, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    rw [zpow_add₀ (norm_ne_zero_iff.2 hx0)]
    field_simp
  refine ⟨hTsum, ?_⟩
  set q : ℂ := x ^ 2 with hqdef
  have hq : ‖q‖ < 1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hx two_ne_zero
  set P := qPochInf q with hP
  have hP0 : P ≠ 0 := qPochInf_ne_zero hq
  have ha : HasProd (fun k : ℕ ↦ 1 - q ^ (k + 1)) P := (multipliable_one_sub_pow_succ hq).hasProd
  have hprod : HasProd (fun n : ℕ ↦ (1 - q ^ (n + 1)) ^ 3) (P * P * P) := by
    have := (ha.mul ha).mul ha
    convert this using 2 with n
    ring
  set G : ℕ → ℤ → ℂ := fun n m ↦ if m ∈ Icc (-((n + 1 : ℕ) : ℤ)) (n + 1 : ℕ) then
    qBinom q (2 * (n + 1)) (m + (n + 1 : ℕ)).toNat * T m else 0 with hG
  have hfin : ∀ n : ℕ, qPoch q (n + 1) * qPoch q n = ∑' m, G n m := by
    intro n
    rw [finite_jacobi_cube hx0 hx n, tsum_eq_sum (s := Icc (-((n + 1 : ℕ) : ℤ)) (n + 1 : ℕ))
      (fun m hm ↦ by simp only [hG, if_neg hm])]
    refine sum_congr rfl fun m hm ↦ ?_
    simp only [hG, if_pos hm, cubeCoeff, hTdef]
    ring
  obtain ⟨B, hB⟩ := exists_norm_qBinom_le hq
  have hup (m : ℤ) : Tendsto (fun n : ℕ ↦ (m + (n + 1 : ℕ)).toNat) atTop atTop :=
    tendsto_atTop_atTop.2 fun b ↦ ⟨b + m.natAbs, fun n hn ↦ by omega⟩
  have hup' (m : ℤ) : Tendsto (fun n : ℕ ↦ 2 * (n + 1) - (m + (n + 1 : ℕ)).toNat) atTop atTop :=
    tendsto_atTop_atTop.2 fun b ↦ ⟨b + m.natAbs, fun n hn ↦ by omega⟩
  have hup2 : Tendsto (fun n : ℕ ↦ 2 * (n + 1)) atTop atTop :=
    tendsto_atTop_atTop.2 fun b ↦ ⟨b, fun n hn ↦ by omega⟩
  have hpt (m : ℤ) : Tendsto (fun n ↦ G n m) atTop (𝓝 (T m / P)) := by
    have hlim : Tendsto (fun n : ℕ ↦ qPoch q (2 * (n + 1)) / (qPoch q (m + (n + 1 : ℕ)).toNat *
        qPoch q (2 * (n + 1) - (m + (n + 1 : ℕ)).toNat)) * T m) atTop (𝓝 (P / (P * P) * T m)) :=
      (((tendsto_qPoch hq).comp hup2).div (((tendsto_qPoch hq).comp (hup m)).mul
        ((tendsto_qPoch hq).comp (hup' m))) (mul_ne_zero hP0 hP0)).mul_const _
    rw [show T m / P = P / (P * P) * T m by field_simp]
    refine hlim.congr' (eventually_atTop.2 ⟨m.natAbs, fun n hn ↦ ?_⟩)
    have hmem : m ∈ Icc (-((n + 1 : ℕ) : ℤ)) (n + 1 : ℕ) := by simp only [mem_Icc]; omega
    simp only [hG, if_pos hmem, qBinom, if_pos (show (m + (n + 1 : ℕ)).toNat ≤ 2 * (n + 1) by omega)]
  have hbd : ∀ᶠ n in atTop, ∀ m, ‖G n m‖ ≤ B * ‖T m‖ := Eventually.of_forall fun n m ↦ by
    simp only [hG]
    split_ifs
    · rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hB _ _) (norm_nonneg _)
    · rw [norm_zero]; exact mul_nonneg ((norm_nonneg _).trans (hB 0 0)) (norm_nonneg _)
  have htann := tendsto_tsum_of_dominated_convergence (hTsum.norm.mul_left B) hpt hbd
  have hlim1 := ((tendsto_qPoch hq).comp (tendsto_add_atTop_nat 1)).mul htann
  rw [tsum_div_const, mul_div_cancel₀ _ hP0] at hlim1
  have hlim2 : Tendsto (fun n : ℕ ↦ qPoch q (n + 1) * (qPoch q (n + 1) * qPoch q n)) atTop
      (𝓝 (P * (P * P))) :=
    ((tendsto_qPoch hq).comp (tendsto_add_atTop_nat 1)).mul
      (((tendsto_qPoch hq).comp (tendsto_add_atTop_nat 1)).mul (tendsto_qPoch hq))
  have heq := tendsto_nhds_unique hlim2 (hlim1.congr fun n ↦ by
    simp only [Function.comp_apply, hfin n])
  rw [← heq, show P * (P * P) = P * P * P by ring]
  exact hprod

/-- **Theorem 14.7** (Jacobi, Apostol). For `|x| < 1`,
`∏_{n=1}^∞ (1 - xⁿ)³ = ∑_{m=0}^∞ (-1)^m (2m + 1) x^{m(m+1)/2}`. -/
@[kb "apostol1976" "Thm 14.7, p. 321"]
theorem apostol_thm_14_7 {y : ℂ} (hy : ‖y‖ < 1) :
    HasProd (fun n : ℕ ↦ (1 - y ^ (n + 1)) ^ 3)
      (∑' m : ℕ, (-1) ^ m * (2 * m + 1) * y ^ (m * (m + 1) / 2)) := by
  set x : ℂ := y ^ (2⁻¹ : ℂ) with hxdef
  have hx2 : x ^ 2 = y := cpow_ofNat_inv_pow y 2
  have hx : ‖x‖ < 1 := by
    have h : ‖x‖ ^ 2 = ‖y‖ := by rw [← norm_pow, hx2]
    nlinarith [norm_nonneg x]
  obtain ⟨hsum, hprod⟩ := jacobi_cube hx
  rw [hx2] at hprod
  rw [← tsum_nat_add_neg_add_one hsum] at hprod
  convert hprod using 1
  refine tsum_congr fun m ↦ ?_
  have hev : 2 * (m * (m + 1) / 2) = m * (m + 1) := Nat.two_mul_div_two_of_even (Nat.even_mul_succ_self m)
  have e1 : x ^ (((m : ℤ)) ^ 2 + m) = y ^ (m * (m + 1) / 2) := by
    rw [← hx2, ← pow_mul, hev, ← zpow_natCast]
    congr 1; push_cast; ring
  have e2 : x ^ ((-((m : ℤ) + 1)) ^ 2 + -((m : ℤ) + 1)) = y ^ (m * (m + 1) / 2) := by
    rw [← e1]; congr 1; ring
  have e3 : ((-1 : ℂ)) ^ (-((m : ℤ) + 1)) = -(-1) ^ m := by
    rw [zpow_neg, show ((m : ℤ) + 1) = ((m + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast,
      pow_succ]
    rcases neg_one_pow_eq_or ℂ m with h | h <;> rw [h] <;> norm_num
  rw [e1, e2, e3, zpow_natCast]
  push_cast
  ring

end NTKB.Apostol
