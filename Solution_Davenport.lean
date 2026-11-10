/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import NTKB.Analytic.Davenport.Hadamard.XiChar
import NTKB.Analytic.Davenport.Zeros.LZeroFreeTheorem
import NTKB.Analytic.Davenport.Zeros.Landau
import NTKB.Analytic.Davenport.Zeros.RiemannVonMangoldt
import NTKB.Analytic.Davenport.Zeros.LZeroCount
import NTKB.Analytic.Davenport.Zeros.LExplicitExact
import NTKB.Analytic.Davenport.Zeros.PNTAPPage
import NTKB.Analytic.Davenport.Sieve.PolyaVinogradov
import NTKB.Analytic.Davenport.Sieve.LargeSieve
import NTKB.Analytic.Davenport.Sieve.Characters
import NTKB.Analytic.Davenport.Sieve.Vinogradov

/-!
# Proofs of the Davenport headline statements

The statements of `Challenge_Davenport.lean`, proved by the library theorems. `lake comparator` checks that each
statement here is exactly the one in `Challenge_Davenport.lean`.
-/

namespace NTKB.Headlines.Davenport

open Complex DirichletCharacter Finset
open scoped Real ArithmeticFunction.vonMangoldt

theorem dirichletXi_hadamard {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive)
    (hN : N ≠ 1) :
    ∃ A B : ℂ, ∀ s, NTKB.dirichletXi χ s = Complex.exp (A + B * s) *
      ∏' ρ : NTKB.ZeroIndex (NTKB.dirichletXi χ), (1 - s / ρ.val) * Complex.exp (s / ρ.val) :=
  NTKB.Davenport.dirichletXi_hadamard hχ hN

theorem LFunction_zero_free_complex {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ2 : χ ^ 2 ≠ 1) {s : ℂ}
    (hs : LFunction χ s = 0) :
    s.re ≤ 1 - 1 / 16200 / NTKB.logQT N s.im :=
  NTKB.Davenport.LFunction_zero_free_theorem_complex hχ2 hs

theorem LFunction_zero_free_real {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ1 : χ ≠ 1)
    (hreal : χ ^ 2 = 1) {s : ℂ} (hs : LFunction χ s = 0)
    (hreg : 1 - 1 / 16200 / NTKB.logQT N s.im < s.re) :
    s.im = 0 ∧ ∀ s' : ℂ, LFunction χ s' = 0 → 1 - 1 / 16200 / NTKB.logQT N s'.im < s'.re → s' = s :=
  NTKB.Davenport.LFunction_zero_free_theorem_real hχ1 hreal hs hreg

theorem LFunction_zero_free_real_simple {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1) (hreal : χ ^ 2 = 1) (ρ : NTKB.ZeroIndex (NTKB.dirichletXi χ))
    (hreg : 1 - 1 / 16200 / NTKB.logQT N ρ.val.im < ρ.val.re) :
    analyticOrderNatAt (NTKB.dirichletXi χ) ρ.val = 1 :=
  NTKB.Davenport.LFunction_zero_free_theorem_real_simple hχ hχ1 hreal ρ hreg

theorem landau_real_zeros {q₁ q₂ : ℕ} [NeZero q₁] [NeZero q₂]
    {χ₁ : DirichletCharacter ℂ q₁} {χ₂ : DirichletCharacter ℂ q₂} (hp₁ : χ₁.IsPrimitive)
    (hp₂ : χ₂.IsPrimitive) (h₁ : χ₁ ≠ 1) (h₂ : χ₂ ≠ 1) (hr₁ : χ₁ ^ 2 = 1) (hr₂ : χ₂ ^ 2 = 1)
    (hne : changeLevel (dvd_mul_right q₁ q₂) χ₁ ≠ changeLevel (dvd_mul_left q₂ q₁) χ₂)
    {β₁ β₂ : ℝ} (hz₁ : LFunction χ₁ β₁ = 0) (hz₂ : LFunction χ₂ β₂ = 0) :
    min β₁ β₂ ≤ 1 - 1 / 400 / Real.log (q₁ * q₂) :=
  NTKB.Davenport.landau_real_zeros hp₁ hp₂ h₁ h₂ hr₁ hr₂ hne hz₁ hz₂

theorem page_exceptional_character {z : ℝ} (hz3 : 3 ≤ z) {q₁ q₂ : ℕ} [NeZero q₁]
    [NeZero q₂] {χ₁ : DirichletCharacter ℂ q₁} {χ₂ : DirichletCharacter ℂ q₂}
    (hp₁ : χ₁.IsPrimitive) (hp₂ : χ₂.IsPrimitive) (h₁ : χ₁ ≠ 1) (h₂ : χ₂ ≠ 1)
    (hr₁ : χ₁ ^ 2 = 1) (hr₂ : χ₂ ^ 2 = 1) (hq₁ : (q₁ : ℝ) ≤ z) (hq₂ : (q₂ : ℝ) ≤ z)
    {β₁ β₂ : ℝ} (hz₁ : LFunction χ₁ β₁ = 0) (hz₂ : LFunction χ₂ β₂ = 0)
    (hb₁ : 1 - 1 / 800 / Real.log z < β₁) (hb₂ : 1 - 1 / 800 / Real.log z < β₂) :
    q₁ = q₂ ∧ HEq χ₁ χ₂ :=
  NTKB.Davenport.page_exceptional_character hz3 hp₁ hp₂ h₁ h₂ hr₁ hr₂ hq₁ hq₂ hz₁ hz₂ hb₁ hb₂

theorem zetaZeroCount_sub_le :
    ∃ A : ℝ, 0 < A ∧ ∀ T : ℝ, 3 ≤ T →
      |(NTKB.zetaZeroCount T : ℝ) - (T / (2 * π) * Real.log (T / (2 * π)) - T / (2 * π))| ≤
        A * Real.log T :=
  NTKB.Davenport.zetaZeroCount_sub_le

theorem LZeroCount_sub_le :
    ∃ A : ℝ, 0 < A ∧ ∀ {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}, χ.IsPrimitive → N ≠ 1 →
      ∀ T : ℝ, 3 ≤ T →
      |(NTKB.LZeroCount χ T : ℝ) - (T / π * Real.log (N * T / (2 * π)) - T / π)| ≤
        A * Real.log (N * T) :=
  NTKB.Davenport.LZeroCount_sub_le

theorem explicit_formula_psi0L_odd {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
    (hq : q ≠ 1) (ha : NTKB.dirichletParity χ = 1) (N : ℕ) (hN : 3 ≤ N) :
    Filter.Tendsto (fun T : ℝ ↦ ∑ ρ ∈ NTKB.zerosBelowL hχ hq T, (N : ℂ) ^ ρ.val / ρ.val) Filter.atTop
      (nhds (-(deriv (LFunction χ) 0 / LFunction χ 0) +
        ∑' m : ℕ, (N : ℂ) ^ (-(2 * (m : ℂ) + 1)) / (2 * (m : ℂ) + 1) - NTKB.psi0L χ N)) :=
  NTKB.Davenport.explicit_formula_psi0L_odd hχ hq ha N hN

theorem explicit_formula_psi0L_even {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
    (hq : q ≠ 1) (ha : NTKB.dirichletParity χ = 0) (N : ℕ) (hN : 3 ≤ N) :
    Filter.Tendsto (fun T : ℝ ↦ ∑ ρ ∈ NTKB.zerosBelowL hχ hq T, (N : ℂ) ^ ρ.val / ρ.val) Filter.atTop
      (nhds (-((Real.log N : ℂ) + NTKB.bEven χ) +
        ∑' m : ℕ, (N : ℂ) ^ (-(2 * ((m : ℂ) + 1))) / (2 * ((m : ℂ) + 1)) - NTKB.psi0L χ N)) :=
  NTKB.Davenport.explicit_formula_psi0L_even hχ hq ha N hN

open scoped Classical in
theorem psiAP_sub_le_page (C : ℝ) (hC : 0 < C) :
    ∃ c A : ℝ, 0 < c ∧ 0 < A ∧ ∀ N : ℕ, 3 ≤ N → ∃ q₁ : ℕ,
      (q₁ = 0 ∨ NTKB.IsPageModulus (max 3 (Real.exp (C * √(Real.log N)))) q₁) ∧
      ∀ {q : ℕ} [NeZero q] {a : ZMod q}, IsUnit a → Real.log q ≤ C * √(Real.log N) → ¬ q₁ ∣ q →
        ‖(NTKB.psiAP a N : ℂ) - N / q.totient‖ ≤ A * N * Real.exp (-(c * √(Real.log N))) :=
  NTKB.Davenport.psiAP_sub_le_page C hC

theorem polya_vinogradov {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) (M : ℤ) (N : ℕ) :
    ‖∑ n ∈ Ioc M (M + N), χ n‖ ≤ 2 * √q * Real.log q :=
  NTKB.Davenport.norm_sum_Ioc_le hχ M N

theorem large_sieve {ι : Type*} (s : Finset ι) (α : ι → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ r ∈ s, ∀ t ∈ s, r ≠ t → ∀ m : ℤ, δ ≤ |α r - α t - m|) (M : ℤ) (N : ℕ)
    (a : ℤ → ℂ) :
    ∑ r ∈ s, ‖∑ n ∈ Ioc M (M + N), a n * Complex.exp (2 * π * Complex.I * (n * α r))‖ ^ 2 ≤
      (N + 3 / δ) * ∑ n ∈ Ioc M (M + N), ‖a n‖ ^ 2 :=
  NTKB.Davenport.large_sieve s α hδ hsep M N a

open scoped Classical in
theorem large_sieve_characters {Q : ℝ} (hQ : 1 ≤ Q) (M : ℤ) (N : ℕ) (c : ℤ → ℂ) :
    ∑ q ∈ Icc 1 ⌊Q⌋₊, ((q : ℝ) / q.totient) *
        ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ ↦ χ.IsPrimitive),
          ‖∑ n ∈ Ioc M (M + N), c n * χ n‖ ^ 2 ≤
      (N + 3 * Q ^ 2) * ∑ n ∈ Ioc M (M + N), ‖c n‖ ^ 2 :=
  NTKB.Davenport.large_sieve_characters hQ M N c

theorem vinogradov_prime_exponential_sum : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (a : ℤ) (q : ℕ), 1 ≤ q →
    IsCoprime a q → |α - a / q| ≤ 1 / (q : ℝ) ^ 2 → ∀ N : ℕ, 2 ≤ N →
    ‖∑ n ∈ Icc 1 N, (Λ n : ℂ) * Complex.exp (2 * π * Complex.I * (n * α))‖ ≤
      C * (N / √q + (N : ℝ) ^ ((4 : ℝ) / 5) + √N * √q) * Real.log N ^ 4 :=
  NTKB.Davenport.norm_sum_vonMangoldt_exp_le

end NTKB.Headlines.Davenport
