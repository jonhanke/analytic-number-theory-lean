/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Davenport.Zeros.LExceptional

/-!
# `ψ(x, χ) = -x^{β₁}/β₁ + R`

**Davenport, Ch. 19, (11)-(12) (rows 19-12, 19-14) and Ch. 20, (E)-(F) (p. 122).** For primitive
`χ` mod `q > 1`, integers `N ≥ 3`, `T ≥ 2`, with `ℓ = log q + log N + log T`:
`ψ₀(N, χ) = -∑_{exceptional ρ} N^ρ/ρ + O(N ℓ²/T + T ℓ N^{-1/2} + ℓ² + ℓ N^{1/2} log N
  + N ℓ² exp(-c log N/log(qT)))`,
where the exceptional zeros are those of 14-11 (`β > 1 - c/log q`, `c = 1/16200`; at most the
real simple zero `β₁` of a real `χ`). The zeros with `|γ| < 1` are paired with `∑_{|γ|<1} 1/ρ`
of 19-10: `|ρ|⁻¹ ≪ log q` except for `1 - β₁`, for which `(N^{1-β₁} - 1)/(1 - β₁) ≤ N^{1/2} log N`.
(Compared with Davenport's (12) we count the possible zeros `1 - β₁` with multiplicity bounded
by the number of zeros with `|γ| < 1`, which costs a factor `ℓ` in front of `N^{1/2} log N`.)
-/

open Filter Topology Complex Set DirichletCharacter
open scoped Real ComplexConjugate

namespace NTKB

variable {q : ℕ} [NeZero q]

/-- The number of zeros with `|γ| < 1` is `≤ A (log q + 1)`. -/
lemma card_zerosBelowL_one_le :
    ∃ A : ℝ, 0 < A ∧ ∀ {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
      (hq : q ≠ 1), ((zerosBelowL hχ hq 1).card : ℝ) ≤ A * (Real.log q + 1) := by
  obtain ⟨A, hA, h⟩ := Davenport.card_L_zeros_near_le
  refine ⟨A, hA, ?_⟩
  intro q _ χ hχ hq
  obtain ⟨hfin, hcard⟩ := h hχ hq 0
  have hZ : zerosBelowL hχ hq 1 = hfin.toFinset := by
    ext ρ; simp [mem_zerosBelowL]
  rw [hZ, ← Set.ncard_eq_toFinset_card _ hfin]
  refine hcard.trans ?_
  have : Real.log (|0| + 2) ≤ 1 := by
    simp; have := Real.log_two_lt_d9; linarith
  gcongr

/-- Exceptional zeros: `|1/ρ| ≤ 2`. -/
lemma norm_inv_le_of_exc {χ : DirichletCharacter ℂ q} (hχ1 : χ ≠ 1) {s : ℂ}
    (h : IsExcPoint q s) : ‖1 / s‖ ≤ 2 := by
  have h2 := h.re_gt_half hχ1
  have : 1 / 2 ≤ ‖s‖ := by linarith [Complex.re_le_norm s]
  rw [norm_div, norm_one, div_le_iff₀ (by linarith)]; linarith

/-- Zeros with `|γ| < 1` whose mirror is not exceptional: `|1/ρ| ≤ 16200 log q`. -/
lemma norm_inv_le_of_not_mirror {χ : DirichletCharacter ℂ q} (hχ1 : χ ≠ 1) {s : ℂ}
    (hs : |s.im| < 1) (hre : 0 < s.re) (h : ¬ IsExcPoint q (1 - conj s)) :
    ‖1 / s‖ ≤ 16200 * Real.log q := by
  have hq := two_le_of_ne_one hχ1
  have h1 := re_ge_of_mirror_not_exc h
  rw [logQT_of_lt_one (by linarith) hs] at h1
  have hlq : 0 < Real.log q := Real.log_pos (by linarith)
  have h2 : 1 / 16200 / Real.log q ≤ ‖s‖ := h1.trans (Complex.re_le_norm s)
  rw [norm_div, norm_one, div_le_iff₀ (by linarith [Complex.re_le_norm s])]
  rw [div_div, div_le_iff₀ (by positivity)] at h2
  nlinarith

/-- Zeros whose mirror is exceptional: `|1/ρ - N^ρ/ρ| ≤ N^{1/2} log N`. -/
lemma norm_inv_sub_kernel_le_of_mirror {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
    (hq : q ≠ 1) (ρ : ZeroIndex (dirichletXi χ)) (h : IsExcPoint q (1 - conj ρ.val))
    {N : ℝ} (hN : 1 ≤ N) :
    ‖1 / ρ.val - perronKernel N ρ.val‖ ≤ N ^ (1 / 2 : ℝ) * Real.log N := by
  obtain ⟨him, hre⟩ := mirror_exc_real hχ hq ρ h
  have hβ0 := (dirichletXi_zero_mem hχ hq ρ).2.1
  set β := ρ.val.re
  have hρ : ρ.val = (β : ℂ) := by
    apply Complex.ext <;> simp [β, him]
  have hN0 : 0 < N := by linarith
  have hk : perronKernel N ρ.val = ((N ^ β / β : ℝ) : ℂ) := by
    rw [perronKernel, hρ, ← Complex.ofReal_cpow hN0.le]; push_cast; ring
  rw [hk, hρ, show (1 : ℂ) / (β : ℂ) - ((N ^ β / β : ℝ) : ℂ) = (((1 - N ^ β) / β : ℝ) : ℂ) by
    push_cast; ring, Complex.norm_real, Real.norm_eq_abs]
  have h1 : 1 ≤ N ^ β := Real.one_le_rpow hN hβ0.le
  rw [abs_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hβ0.le), ← neg_div, neg_sub]
  refine (rpow_sub_one_div_le hN hβ0).trans ?_
  have hl := Real.log_nonneg hN
  have : N ^ β ≤ N ^ (1 / 2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hN (by linarith)
  exact mul_le_mul_of_nonneg_right this hl

/-- Non-exceptional zeros with `|γ| < T`: `|N^ρ| ≤ N exp(-c log N/log(qT))`. -/
lemma norm_cpow_le_of_not_exc {χ : DirichletCharacter ℂ q} (hχ1 : χ ≠ 1) {s : ℂ} {N T : ℝ}
    (hN : 1 ≤ N) (hT : 1 ≤ T) (hs : |s.im| < T) (h : ¬ IsExcPoint q s) :
    N ^ s.re ≤ N * Real.exp (-(1 / 16200 * Real.log N / logQT q T)) := by
  have hq := two_le_of_ne_one hχ1
  have hN0 : 0 < N := by linarith
  have h1 : s.re ≤ 1 - 1 / 16200 / logQT q s.im := not_lt.mp h
  have hp1 := logQT_pos hχ1 s.im
  have hle := logQT_le (N := q) (by linarith) hT hs
  have h2 : 1 / 16200 / logQT q T ≤ 1 / 16200 / logQT q s.im :=
    div_le_div_of_nonneg_left (by norm_num) hp1 hle
  calc N ^ s.re ≤ N ^ (1 - 1 / 16200 / logQT q T) :=
        Real.rpow_le_rpow_of_exponent_le hN (by linarith)
    _ = N * Real.exp (-(1 / 16200 * Real.log N / logQT q T)) := by
        rw [Real.rpow_sub hN0, Real.rpow_one, Real.rpow_def_of_pos hN0, div_eq_mul_inv N,
          ← Real.exp_neg]
        congr 2; ring

end NTKB
