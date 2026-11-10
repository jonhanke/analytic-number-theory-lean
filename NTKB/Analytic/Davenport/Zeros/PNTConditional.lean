/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Davenport.Zeros.PNT

/-!
# `ψ(x)` when the zeros satisfy `β ≤ Θ` (von Koch)

**Davenport, Ch. 18, p. 113 (rows 18-8, 18-10).** If every nontrivial zero of `ζ` has real part
at most `Θ` (`1/2 ≤ Θ < 1`), then `ψ(x) = x + O(x^Θ log² x)`; in particular, under the Riemann
hypothesis, `ψ(x) = x + O(x^{1/2} log² x)`. The proof takes `T = x^{1-Θ}` in (17-13) and uses
`∑_{|γ|<T} 1/|ρ| ≪ log² T`.
-/

open Filter Topology Complex Set
open scoped Real ArithmeticFunction.vonMangoldt

namespace NTKB

/-- The integer case of 18-10. -/
lemma psi_natCast_sub_le_of_re_le {Θ : ℝ} (hΘ : 1 / 2 ≤ Θ) (hΘ1 : Θ < 1)
    (hzeros : ∀ ρ : ZeroIndex riemannXi, ρ.val.re ≤ Θ) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 3 ≤ N →
      |Chebyshev.psi N - N| ≤ C * (N : ℝ) ^ Θ * Real.log N ^ 2 := by
  obtain ⟨A, hA, hexp⟩ := Davenport.explicit_formula_psi0
  obtain ⟨C₀, hC₀, hsum⟩ := Davenport.sum_zeros_inv_norm_le
  set Z := ‖deriv riemannZeta 0 / riemannZeta 0‖ with hZdef
  have hZ0 : 0 ≤ Z := norm_nonneg _
  clear_value Z
  refine ⟨4 * A + C₀ + Z + 2 + 14, by positivity, fun N hN ↦ ?_⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
  set L := Real.log N with hL
  have hL1 : 1 < L := by
    rw [hL, Real.lt_log_iff_exp_lt hN0]; have := Real.exp_one_lt_d9; linarith
  have hNΘ1 : 1 ≤ (N : ℝ) ^ Θ := Real.one_le_rpow (by linarith) (by linarith)
  have hL2 : 1 ≤ L ^ 2 := by nlinarith
  have hW : 1 ≤ (N : ℝ) ^ Θ * L ^ 2 := by nlinarith
  have hW0 : 0 ≤ (N : ℝ) ^ Θ * L ^ 2 := by linarith
  have hsplitN : (N : ℝ) = (N : ℝ) ^ Θ * (N : ℝ) ^ (1 - Θ) := by
    rw [← Real.rpow_add hN0]; simp
  rcases lt_or_ge ((N : ℝ) ^ (1 - Θ)) 2 with hT | hT
  · -- small `N`: the trivial bound
    have h1 : Chebyshev.psi N ≤ (Real.log 4 + 4) * N := Chebyshev.psi_le_const_mul_self hN0.le
    have hl4 : Real.log 4 < 2 := by
      rw [Real.log_lt_iff_lt_exp (by norm_num)]
      have := Real.exp_one_gt_d9
      calc (4 : ℝ) < 2.7 * 2.7 := by norm_num
        _ ≤ Real.exp 1 * Real.exp 1 := by gcongr <;> linarith
        _ = Real.exp 2 := by rw [← Real.exp_add]; norm_num
    have h4x : Real.log 4 * N ≤ 2 * N := mul_le_mul_of_nonneg_right hl4.le hN0.le
    have hψ0 := Chebyshev.psi_nonneg (N : ℝ)
    have hN2 : (N : ℝ) ≤ 2 * (N : ℝ) ^ Θ := by
      calc (N : ℝ) = (N : ℝ) ^ Θ * (N : ℝ) ^ (1 - Θ) := hsplitN
        _ ≤ (N : ℝ) ^ Θ * 2 := by gcongr
        _ = 2 * (N : ℝ) ^ Θ := by ring
    have hNW : (N : ℝ) ≤ 2 * ((N : ℝ) ^ Θ * L ^ 2) := by nlinarith
    have hrest : 0 ≤ (4 * A + C₀ + Z + 2) * ((N : ℝ) ^ Θ * L ^ 2) := by positivity
    have e : (4 * A + C₀ + Z + 2 + 14) * (N : ℝ) ^ Θ * L ^ 2 =
        (4 * A + C₀ + Z + 2) * ((N : ℝ) ^ Θ * L ^ 2) + 14 * ((N : ℝ) ^ Θ * L ^ 2) := by ring
    rw [e, abs_le]; constructor <;> linarith
  · -- `T = N^{1-Θ} ≥ 2`
    set T := (N : ℝ) ^ (1 - Θ) with hTdef
    have hT0 : 0 < T := by linarith
    have hTN : T ≤ N := by
      rw [hTdef]
      calc (N : ℝ) ^ (1 - Θ) ≤ (N : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
        _ = N := Real.rpow_one _
    have hlT : Real.log T ≤ L := Real.log_le_log hT0 hTN
    have hlT0 : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
    have hNT : N / T = (N : ℝ) ^ Θ := by
      rw [div_eq_iff hT0.ne']; exact hsplitN
    clear_value T
    have e1 := hexp N hN T hT
    have hsplit : (psi0 N : ℂ) - ((N : ℝ) : ℂ) = ((psi0 N : ℂ) - explicitMain N T) -
        ∑ ρ ∈ zerosBelow T, perronKernel N ρ.val - deriv riemannZeta 0 / riemannZeta 0 -
        ((1 / 2 * Real.log (1 - (N : ℝ) ^ (-2 : ℝ)) : ℝ) : ℂ) := by
      simp only [explicitMain]; ring
    have hlNT : Real.log (N * T) ≤ 2 * L := by
      rw [Real.log_mul hN0.ne' hT0.ne']; linarith
    have hlNT0 : 0 ≤ Real.log (N * T) :=
      Real.log_nonneg (one_le_mul_of_one_le_of_one_le (by linarith) (by linarith))
    have b1 : ‖(psi0 N : ℂ) - explicitMain N T‖ ≤ 4 * A * ((N : ℝ) ^ Θ * L ^ 2) := by
      refine e1.trans ?_
      have h1 : Real.log (N * T) ^ 2 ≤ 4 * L ^ 2 := by nlinarith
      calc A * N * Real.log (N * T) ^ 2 / T = A * (N / T) * Real.log (N * T) ^ 2 := by ring
        _ ≤ A * (N / T) * (4 * L ^ 2) := by gcongr
        _ = 4 * A * ((N : ℝ) ^ Θ * L ^ 2) := by rw [hNT]; ring
    have b2 : ‖∑ ρ ∈ zerosBelow T, perronKernel N ρ.val‖ ≤ C₀ * ((N : ℝ) ^ Θ * L ^ 2) := by
      calc ‖∑ ρ ∈ zerosBelow T, perronKernel N ρ.val‖
          ≤ ∑ ρ ∈ zerosBelow T, (N : ℝ) ^ Θ * (1 / ‖ρ.val‖) := by
            refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun ρ _ ↦ ?_)
            rw [norm_perronKernel hN0, div_eq_mul_one_div]
            gcongr
            all_goals first | exact hzeros ρ | linarith
        _ = (N : ℝ) ^ Θ * ∑ ρ ∈ zerosBelow T, 1 / ‖ρ.val‖ := by rw [Finset.mul_sum]
        _ ≤ (N : ℝ) ^ Θ * (C₀ * Real.log T ^ 2) := by gcongr; exact hsum T hT
        _ ≤ (N : ℝ) ^ Θ * (C₀ * L ^ 2) := by gcongr
        _ = C₀ * ((N : ℝ) ^ Θ * L ^ 2) := by ring
    have b3 : |1 / 2 * Real.log (1 - (N : ℝ) ^ (-2 : ℝ))| ≤ 1 := by
      have hy : (N : ℝ) ^ (-2 : ℝ) ≤ 1 / 2 := by
        rw [Real.rpow_neg hN0.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
        rw [inv_le_comm₀ (by positivity) (by norm_num)]; nlinarith
      have hy0 : 0 < (N : ℝ) ^ (-2 : ℝ) := by positivity
      have hl : Real.log (1 - (N : ℝ) ^ (-2 : ℝ)) ≤ 0 := Real.log_nonpos (by linarith) (by linarith)
      have hl' : -1 ≤ Real.log (1 - (N : ℝ) ^ (-2 : ℝ)) := by
        have := Real.one_sub_inv_le_log_of_pos (show 0 < 1 - (N : ℝ) ^ (-2 : ℝ) by linarith)
        have h2 : (1 - (N : ℝ) ^ (-2 : ℝ))⁻¹ ≤ 2 := by
          rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
        linarith
      rw [abs_le]; constructor <;> linarith
    have hψ0 : |psi0 N - N| ≤ 4 * A * ((N : ℝ) ^ Θ * L ^ 2) + C₀ * ((N : ℝ) ^ Θ * L ^ 2) + Z + 1 := by
      have : |psi0 N - N| = ‖(psi0 N : ℂ) - ((N : ℝ) : ℂ)‖ := by
        rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      rw [this, hsplit]
      have h4 : ‖(((1 / 2 * Real.log (1 - (N : ℝ) ^ (-2 : ℝ)) : ℝ) : ℂ))‖ ≤ 1 := by
        rw [Complex.norm_real, Real.norm_eq_abs]; exact b3
      calc _ ≤ ‖(psi0 N : ℂ) - explicitMain N T‖ + ‖∑ ρ ∈ zerosBelow T, perronKernel N ρ.val‖ +
            ‖deriv riemannZeta 0 / riemannZeta 0‖ +
              ‖(((1 / 2 * Real.log (1 - (N : ℝ) ^ (-2 : ℝ)) : ℝ) : ℂ))‖ :=
            (norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans
              (add_le_add (norm_sub_le _ _) le_rfl)) le_rfl)
        _ ≤ _ := add_le_add (add_le_add (add_le_add b1 b2) hZdef.ge) h4
    have hΛ : Λ N / 2 ≤ (N : ℝ) ^ Θ * L ^ 2 := by
      have h1 : Λ N ≤ L := hL ▸ ArithmeticFunction.vonMangoldt_le_log
      have h2 : L ≤ L ^ 2 := by nlinarith
      have h3 : L ^ 2 ≤ (N : ℝ) ^ Θ * L ^ 2 := by nlinarith
      have := ArithmeticFunction.vonMangoldt_nonneg (n := N)
      linarith
    have hΛ0 := ArithmeticFunction.vonMangoldt_nonneg (n := N)
    rw [psi_natCast_eq_psi0, show psi0 N + Λ N / 2 - N = (psi0 N - N) + Λ N / 2 by ring]
    refine (abs_add_le _ _).trans ?_
    rw [abs_of_nonneg (by positivity : 0 ≤ Λ N / 2)]
    have hZW : Z + 1 ≤ (Z + 1) * ((N : ℝ) ^ Θ * L ^ 2) := by
      have := mul_le_mul_of_nonneg_left hW (add_nonneg hZ0 zero_le_one)
      linarith only [this]
    have h14 : 0 ≤ 14 * ((N : ℝ) ^ Θ * L ^ 2) := by positivity
    have e : (4 * A + C₀ + Z + 2 + 14) * (N : ℝ) ^ Θ * L ^ 2 =
        4 * A * ((N : ℝ) ^ Θ * L ^ 2) + C₀ * ((N : ℝ) ^ Θ * L ^ 2) +
          (Z + 1) * ((N : ℝ) ^ Θ * L ^ 2) + (N : ℝ) ^ Θ * L ^ 2 + 14 * ((N : ℝ) ^ Θ * L ^ 2) := by
      ring
    rw [e]
    linarith only [hψ0, hΛ, hZW, h14]

/-- **Davenport, Ch. 18, p. 113 (row 18-10)**: if every nontrivial zero `ρ` of `ζ` has
`Re ρ ≤ Θ` with `1/2 ≤ Θ < 1`, then `|ψ(x) - x| ≤ C x^Θ log² x` for `x ≥ 2`. -/
@[kb "davenport1980" "Ch 18, p. 113"]
theorem Davenport.psi_sub_self_le_of_re_le {Θ : ℝ} (hΘ : 1 / 2 ≤ Θ) (hΘ1 : Θ < 1)
    (hzeros : ∀ s : ℂ, riemannZeta s = 0 → 0 < s.re → s.re ≤ Θ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 2 ≤ x →
      |Chebyshev.psi x - x| ≤ C * x ^ Θ * Real.log x ^ 2 := by
  obtain ⟨C, hC, h⟩ := psi_natCast_sub_le_of_re_le hΘ hΘ1 fun ρ ↦
    hzeros _ (riemannXi_zero_mem ρ).1 (riemannXi_zero_mem ρ).2.1
  refine ⟨C + 1 + 40, by positivity, fun x hx ↦ ?_⟩
  have hx0 : 0 < x := by linarith
  have hψ0 := Chebyshev.psi_nonneg x
  have hl2 := log_two_gt_two_thirds
  have hlx : Real.log 2 ≤ Real.log x := Real.log_le_log two_pos hx
  have hxΘ : 1 ≤ x ^ Θ := Real.one_le_rpow (by linarith) (by linarith)
  rcases lt_or_ge x 3 with hx3 | hx3
  · have h1 : Chebyshev.psi x ≤ (Real.log 4 + 4) * x := Chebyshev.psi_le_const_mul_self hx0.le
    have hl4 : Real.log 4 < 2 := by
      rw [Real.log_lt_iff_lt_exp (by norm_num)]
      have := Real.exp_one_gt_d9
      calc (4 : ℝ) < 2.7 * 2.7 := by norm_num
        _ ≤ Real.exp 1 * Real.exp 1 := by gcongr <;> linarith
        _ = Real.exp 2 := by rw [← Real.exp_add]; norm_num
    have h4x : Real.log 4 * x ≤ 2 * x := mul_le_mul_of_nonneg_right hl4.le hx0.le
    have hW : 4 / 9 ≤ x ^ Θ * Real.log x ^ 2 := by
      have : 4 / 9 ≤ Real.log x ^ 2 := by nlinarith
      nlinarith
    have hrest : 0 ≤ (C + 1) * x ^ Θ * Real.log x ^ 2 := by positivity
    have e : (C + 1 + 40) * x ^ Θ * Real.log x ^ 2 =
        (C + 1) * x ^ Θ * Real.log x ^ 2 + 40 * (x ^ Θ * Real.log x ^ 2) := by ring
    rw [e, abs_le]; constructor <;> linarith
  · set N := ⌊x⌋₊ with hN
    have hN3 : 3 ≤ N := Nat.le_floor (by exact_mod_cast hx3)
    have hNx : (N : ℝ) ≤ x := Nat.floor_le hx0.le
    have hxN : x < N + 1 := Nat.lt_floor_add_one x
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    have hψ : Chebyshev.psi x = Chebyshev.psi N := Chebyshev.psi_eq_psi_coe_floor x
    have hb := h N hN3
    have hmono : C * (N : ℝ) ^ Θ * Real.log N ^ 2 ≤ C * x ^ Θ * Real.log x ^ 2 := by
      have h1 : (N : ℝ) ^ Θ ≤ x ^ Θ := Real.rpow_le_rpow hN0.le hNx (by linarith)
      have h2 : Real.log N ≤ Real.log x := Real.log_le_log hN0 hNx
      have h3 : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
      gcongr
    have hlx1 : 1 ≤ Real.log x := by
      rw [Real.le_log_iff_exp_le hx0]; have := Real.exp_one_lt_d9; linarith
    have hW : 1 ≤ x ^ Θ * Real.log x ^ 2 := by nlinarith
    have h1 : |Chebyshev.psi N - x| ≤ |Chebyshev.psi N - N| + (x - N) := by
      have := abs_sub_le (Chebyshev.psi N) N x
      rw [abs_sub_comm (N : ℝ) x, abs_of_nonneg (by linarith : (0 : ℝ) ≤ x - N)] at this
      exact this
    rw [hψ]
    have h30 : 0 ≤ 40 * (x ^ Θ * Real.log x ^ 2) := by positivity
    have e : (C + 1 + 40) * x ^ Θ * Real.log x ^ 2 =
        C * x ^ Θ * Real.log x ^ 2 + x ^ Θ * Real.log x ^ 2 + 40 * (x ^ Θ * Real.log x ^ 2) := by
      ring
    rw [e]
    linarith

/-- **Davenport, Ch. 18, p. 113 (row 18-8)**, von Koch: under the Riemann hypothesis,
`|ψ(x) - x| ≤ C x^{1/2} log² x` for `x ≥ 2`. -/
@[kb "davenport1980" "Ch 18, p. 113"]
theorem Davenport.psi_sub_self_le_of_riemannHypothesis (hRH : RiemannHypothesis) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 2 ≤ x →
      |Chebyshev.psi x - x| ≤ C * x ^ (1 / 2 : ℝ) * Real.log x ^ 2 := by
  refine Davenport.psi_sub_self_le_of_re_le le_rfl (by norm_num) fun s hs hre ↦ ?_
  have htriv : ¬∃ n : ℕ, s = -2 * (n + 1) := by
    rintro ⟨n, rfl⟩
    simp at hre
    linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
  have h1 : s ≠ 1 := by rintro rfl; exact riemannZeta_one_ne_zero hs
  exact (hRH s hs htriv h1).le

end NTKB
