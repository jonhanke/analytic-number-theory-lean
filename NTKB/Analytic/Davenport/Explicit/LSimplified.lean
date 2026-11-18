/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Davenport.Zeros.LExceptionalReal

/-!
# The explicit formula for `ψ(x, χ)` in the simplified form (G) (Davenport, Chapter 19)

**Davenport, Ch. 19, p. 117, (G) (row 19-8).** For `χ` primitive mod `q > 1` and `2 ≤ T ≤ x`,
`ψ(x, χ) = -∑_{|γ|<T} x^ρ/ρ - b(χ) + R₁(x, T)` with `R₁ ≪ x T^{-1} log²(qx)`.
This is the formula (D), (E) of row 19-6 (`NTKB.Davenport.explicit_formula_psi0L_real`) with the minor
terms absorbed: `ψ(x, χ) - ψ₀(x, χ)`, `(1 - a) log x`, the sum over the trivial zeros
`∑_{m ≥ 1} x^{a-2m}/(2m - a)` and `log x · min(1, x/(T ⟨x⟩))` are all `≪ log x ≤ x T^{-1} log²(qx)`
since `T ≤ x`, and `log(qxT) ≤ 2 log(qx)`.
-/

open Filter Topology Complex
open scoped Real ArithmeticFunction.vonMangoldt

namespace NTKB

lemma norm_psiL_sub_psi0LR_le {q : ℕ} (χ : DirichletCharacter ℂ q) {x : ℝ} (hx : 1 ≤ x) :
    ‖psiL χ x - psi0LR χ x‖ ≤ Real.log x := by
  by_cases hN : ∃ N : ℕ, (N : ℝ) = x
  · obtain ⟨N, rfl⟩ := hN
    rw [psiL_natCast_eq, psi0LR_natCast]
    have h1 : psi0L χ N + χ N * Λ N / 2 - psi0L χ N = χ N * Λ N / 2 := by ring
    rw [h1, norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg
      ArithmeticFunction.vonMangoldt_nonneg]
    have h2 := DirichletCharacter.norm_le_one χ N
    have h3 : Λ N ≤ Real.log N := ArithmeticFunction.vonMangoldt_le_log
    have h4 := ArithmeticFunction.vonMangoldt_nonneg (n := N)
    have : ‖(2 : ℂ)‖ = 2 := by simp
    rw [this]
    nlinarith
  · push_neg at hN
    have : psiL χ x = psi0LR χ x := by
      rw [psiL, psi0LR]
      have : Finset.Icc 0 ⌊x⌋₊ = Finset.range (⌊x⌋₊ + 1) := by
        ext n; simp [Finset.mem_Icc, Finset.mem_range]
      rw [this]
      refine Finset.sum_congr rfl fun n hn ↦ ?_
      have hn' : n ≤ ⌊x⌋₊ := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
      have hle : (n : ℝ) ≤ x := (Nat.cast_le.mpr hn').trans (Nat.floor_le (by linarith))
      have hlt : (n : ℝ) < x := lt_of_le_of_ne hle (hN n)
      simp [perronStepR, hlt]
    rw [this, sub_self, norm_zero]
    exact Real.log_nonneg hx

/-- **Davenport, Ch. 19, p. 117, (G) (row 19-8)**: there is an absolute `A` such that for every
primitive character `χ` mod `q > 1`, real `x ≥ 2` and `2 ≤ T ≤ x`,
`|ψ(x, χ) - (-∑_{|γ|<T} x^ρ/ρ - b(χ))| ≤ A x log²(qx) / T`, where `ψ(x, χ) = ∑_{n ≤ x} χ(n) Λ(n)`, the
sum runs over the nontrivial zeros `ρ = β + iγ` of `L(s, χ)` with multiplicity, and `b(χ)` is the
constant of `L'/L(s, χ)` at `s = 0` (`NTKB.bChar`). -/
@[kb "davenport1980" "Ch 19, p. 117"]
theorem Davenport.explicit_formula_psiL_simplified :
    ∃ A : ℝ, 0 < A ∧ ∀ {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
      (hq : q ≠ 1), ∀ x : ℝ, 2 ≤ x → ∀ T : ℝ, 2 ≤ T → T ≤ x →
      ‖psiL χ x - (-∑ ρ ∈ zerosBelowL hχ hq T, (x : ℂ) ^ ρ.val / ρ.val - bChar χ)‖ ≤
        A * x * Real.log (q * x) ^ 2 / T := by
  obtain ⟨A, hA, h⟩ := Davenport.explicit_formula_psi0L_real
  refine ⟨4 + 5 * A, by positivity, ?_⟩
  intro q _ χ hχ hq x hx T hT hTx
  have hq2 : 2 ≤ q := by
    have := NeZero.ne q
    omega
  have hq2' : (2 : ℝ) ≤ q := by exact_mod_cast hq2
  have hl2 := Real.log_two_gt_d9
  have hlq : Real.log 2 ≤ Real.log q := Real.log_le_log two_pos hq2'
  have hlx : Real.log 2 ≤ Real.log x := Real.log_le_log two_pos hx
  have hx0 : 0 < x := by linarith
  have hT0 : 0 < T := by linarith
  have hM : Real.log (q * x) = Real.log q + Real.log x :=
    Real.log_mul (by positivity) hx0.ne'
  set M := Real.log (q * x) with hMdef
  set L := Real.log x with hLdef
  have hM1 : 1 ≤ M := by rw [hM]; linarith
  have hLM : L ≤ M := by rw [hM]; linarith
  have hlT : Real.log T ≤ Real.log x := Real.log_le_log hT0 hTx
  have hℓ : Real.log q + Real.log x + Real.log T ≤ 2 * M := by rw [hM]; linarith
  have hℓ0 : 0 ≤ Real.log q + Real.log x + Real.log T := by
    have : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
    linarith
  have hℓ2 : (Real.log q + Real.log x + Real.log T) ^ 2 ≤ 4 * M ^ 2 := by nlinarith
  have hK : M ^ 2 ≤ x * M ^ 2 / T := by
    rw [le_div_iff₀ hT0]
    have : 0 ≤ M ^ 2 := sq_nonneg _
    nlinarith
  have hK1 : 1 ≤ x * M ^ 2 / T := by nlinarith
  have hLK : L ≤ x * M ^ 2 / T := by nlinarith
  have hE := h hχ hq x hx T hT
  have hmin : Real.log x * min 1 (x / (T * distPrimePow x)) ≤ L := by
    have : min 1 (x / (T * distPrimePow x)) ≤ 1 := min_le_left _ _
    have h0 : 0 ≤ L := by linarith
    nlinarith
  have hE2 : A * (x * (Real.log q + Real.log x + Real.log T) ^ 2 / T +
      Real.log x * min 1 (x / (T * distPrimePow x))) ≤ A * (4 * (x * M ^ 2 / T) + L) := by
    refine mul_le_mul_of_nonneg_left (add_le_add ?_ hmin) hA.le
    rw [mul_div_assoc, mul_div_assoc]
    have : x * ((Real.log q + Real.log x + Real.log T) ^ 2 / T) ≤ x * (4 * M ^ 2 / T) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hℓ2 hT0.le) hx0.le
    calc _ ≤ x * (4 * M ^ 2 / T) := this
      _ = 4 * (x * (M ^ 2 / T)) := by ring
  have hpsi := norm_psiL_sub_psi0LR_le χ (x := x) (by linarith)
  have htriv := norm_trivialSumL_le χ hx
  have hres : ‖residueZeroL χ x + bChar χ‖ ≤ L := by
    rw [residueZeroL_eq]
    have : -(if dirichletParity χ = 1 then (0 : ℂ) else (Real.log x : ℂ)) - bChar χ + bChar χ =
        -(if dirichletParity χ = 1 then (0 : ℂ) else (Real.log x : ℂ)) := by ring
    rw [this, norm_neg]
    split_ifs
    · simp; linarith
    · rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  have hsplit : psiL χ x - (-∑ ρ ∈ zerosBelowL hχ hq T, (x : ℂ) ^ ρ.val / ρ.val - bChar χ) =
      (psiL χ x - psi0LR χ x) + (psi0LR χ x - (residueZeroL χ x -
        ∑ ρ ∈ zerosBelowL hχ hq T, perronKernel x ρ.val + trivialSumL χ x)) +
      (residueZeroL χ x + bChar χ) + trivialSumL χ x := by
    simp only [perronKernel]; ring
  rw [hsplit]
  calc _ ≤ ‖psiL χ x - psi0LR χ x‖ + ‖psi0LR χ x - (residueZeroL χ x -
        ∑ ρ ∈ zerosBelowL hχ hq T, perronKernel x ρ.val + trivialSumL χ x)‖ +
      ‖residueZeroL χ x + bChar χ‖ + ‖trivialSumL χ x‖ := by
        refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
          (add_le_add_left (norm_add_le _ _) _)) le_rfl)
    _ ≤ L + A * (4 * (x * M ^ 2 / T) + L) + L + 4 / 3 := by
        gcongr
        exact hE.trans hE2
    _ ≤ (4 + 5 * A) * x * M ^ 2 / T := by
        have : (4 + 5 * A) * x * M ^ 2 / T = (4 + 5 * A) * (x * M ^ 2 / T) := by ring
        rw [this]
        nlinarith

end NTKB
