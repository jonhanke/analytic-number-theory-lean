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
import NTKB.Analytic.Davenport.Siegel.Siegel
import NTKB.Analytic.Davenport.Siegel.SiegelWalfisz
import NTKB.Analytic.Davenport.Siegel.PrimeCountingAP
import NTKB.Analytic.Davenport.ClassNumber.Finite
import NTKB.Analytic.Davenport.ClassNumber.Bounds
import NTKB.Analytic.Davenport.ThreePrimes.ThreePrimes

/-!
# Proofs of the Davenport headline statements

The statements of `Challenge_Davenport.lean`, proved by the library theorems. `lake comparator` checks that each
statement here is exactly the one in `Challenge_Davenport.lean`.
-/

namespace NTKB.Headlines.Davenport

open Complex _root_.DirichletCharacter Finset
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

/-! ## New in 0.2.0: Siegel's theorem and what rests on it (Chapters 21, 22, 28, 29) -/

theorem siegel {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}, χ.IsPrimitive →
      χ.IsQuadratic → χ ≠ 1 → C * (q : ℝ) ^ (-ε) < (χ.LFunction 1).re :=
  NTKB.Davenport.siegel hε

theorem siegel_second_form {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q},
      χ.IsQuadratic → χ ≠ 1 → ∀ σ : ℝ, 1 - C * (q : ℝ) ^ (-ε) < σ → χ.LFunction σ ≠ 0 :=
  NTKB.Davenport.siegel_second_form hε

theorem siegel_walfisz (B : ℝ) (hB : 0 < B) :
    ∃ c > 0, ∃ C > 0, ∀ x : ℝ, 2 ≤ x → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.log x ^ B →
      ∀ a : ℤ, IsCoprime a q →
        |NTKB.Davenport.psiAP x q a - x / q.totient| ≤ C * x * Real.exp (-c * √(Real.log x)) :=
  NTKB.Davenport.siegel_walfisz B hB

theorem siegel_walfisz_primeCounting (B : ℝ) (hB : 0 < B) :
    ∃ c > 0, ∃ C > 0, ∀ x : ℝ, 2 ≤ x → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.log x ^ B →
      ∀ a : ℤ, IsCoprime a q →
        |(NTKB.Davenport.primeCountingAP x q a : ℝ) - NTKB.logIntegral x / q.totient| ≤
          C * x * Real.exp (-c * √(Real.log x)) :=
  NTKB.Davenport.siegel_walfisz_primeCounting B hB

theorem bombieri_vinogradov {A : ℝ} (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 3 ≤ x → ∀ Q : ℝ, √x * Real.log x ^ (-A) ≤ Q → Q ≤ √x →
      ∀ (y : ℕ → ℝ) (a : ℕ → ℤ), (∀ q, 0 ≤ y q ∧ y q ≤ x) → (∀ q, IsCoprime (a q) q) →
        ∑ q ∈ Icc 1 ⌊Q⌋₊, |NTKB.Davenport.psiAP (y q) q (a q) - y q / q.totient| ≤
          C * √x * Q * Real.log x ^ 5 :=
  NTKB.Davenport.bombieri_unconditional hA

theorem barban_davenport_halberstam {A : ℝ} (hA : 0 < A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 3 ≤ x → ∀ Q : ℝ, x * Real.log x ^ (-A) < Q → Q ≤ x →
      ∑ q ∈ Icc 1 ⌊Q⌋₊, ∑ a ∈ (Icc 1 q).filter (fun a ↦ Nat.Coprime a q),
        (NTKB.Davenport.psiAP x q a - x / q.totient) ^ 2 ≤ C * x * Q * Real.log x :=
  NTKB.Davenport.barban_davenport_halberstam_unconditional hA

/-! ## New in 0.3.0: class number formulas (Chapters 6 and 21) and the three primes theorem (Chapter 26)

The class number statements are *conditional*: each takes the two named inputs
`NTKB.Davenport.QuadraticFieldDiscriminants` and `NTKB.Davenport.QuadraticIdealCount` as hypotheses (see "Definitions
used" above). The class number and the regulator are those of the field (`h` counts ideal classes, the regulator is
`log ε` for a fundamental unit `ε`, whatever its norm); Davenport's `h(d)` for `d > 0` counts classes of forms. -/

section ClassNumber

open scoped NumberField

theorem classNumber_eq_sum_of_discr_neg {K : Type} [Field K] [NumberField K]
    (hF : NTKB.Davenport.QuadraticFieldDiscriminants) (hI : NTKB.Davenport.QuadraticIdealCount)
    (hK : Module.finrank ℚ K = 2) (hD : NumberField.discr K < 0) :
    (NumberField.classNumber K : ℂ) =
      -((NumberField.Units.torsionOrder K : ℂ) / (2 * (NumberField.discr K).natAbs)) *
        ∑ m ∈ Icc 1 (NumberField.discr K).natAbs, (m : ℂ) * NTKB.kroneckerChar (NumberField.discr K) m :=
  NTKB.Davenport.classNumber_eq_sum_of_discr_neg hF hI hK hD

theorem classNumber_mul_log_eq_sum_of_discr_pos {K : Type} [Field K] [NumberField K]
    (hF : NTKB.Davenport.QuadraticFieldDiscriminants) (hI : NTKB.Davenport.QuadraticIdealCount)
    (hK : Module.finrank ℚ K = 2) (hD : 0 < NumberField.discr K) (ε : (𝓞 K)ˣ)
    (hε : Subgroup.closure {ε} ⊔ NumberField.Units.torsion K = ⊤) (w : NumberField.InfinitePlace K) :
    ((NumberField.classNumber K * |Real.log (w (ε : K))| : ℝ) : ℂ) = -(1 / 2) *
      ∑ m ∈ Ico 1 (NumberField.discr K).natAbs,
        NTKB.kroneckerChar (NumberField.discr K) m *
          (Real.log (Real.sin (π * m / NumberField.discr K)) : ℂ) :=
  NTKB.Davenport.classNumber_mul_log_eq_sum_of_discr_pos hF hI hK hD ε hε w

theorem classNumber_eq_jacobi {K : Type} [Field K] [NumberField K]
    (hF : NTKB.Davenport.QuadraticFieldDiscriminants) (hI : NTKB.Davenport.QuadraticIdealCount)
    {q : ℕ} [Fact q.Prime] (hq : q % 4 = 3) (hq3 : 3 < q) (hK : Module.finrank ℚ K = 2)
    (hDq : NumberField.discr K = -q) :
    (q : ℤ) * NumberField.classNumber K = -∑ m ∈ Ico 1 q, (m : ℤ) * legendreSym q m :=
  NTKB.Davenport.classNumber_eq_jacobi hF hI hq hq3 hK hDq

theorem classNumber_gt_of_discr_neg (hF : NTKB.Davenport.QuadraticFieldDiscriminants)
    (hI : NTKB.Davenport.QuadraticIdealCount) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 →
      NumberField.discr K < 0 →
        C * |(NumberField.discr K : ℝ)| ^ ((1 : ℝ) / 2 - ε) < NumberField.classNumber K :=
  NTKB.Davenport.classNumber_gt_of_discr_neg hF hI hε

theorem classNumber_mul_log_gt_of_discr_pos (hF : NTKB.Davenport.QuadraticFieldDiscriminants)
    (hI : NTKB.Davenport.QuadraticIdealCount) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 →
      0 < NumberField.discr K →
      ∀ (η : (𝓞 K)ˣ), Subgroup.closure {η} ⊔ NumberField.Units.torsion K = ⊤ →
        ∀ w : NumberField.InfinitePlace K,
          C * (NumberField.discr K : ℝ) ^ ((1 : ℝ) / 2 - ε) <
            NumberField.classNumber K * |Real.log (w (η : K))| :=
  NTKB.Davenport.classNumber_mul_log_gt_of_discr_pos hF hI hε

end ClassNumber

theorem vinogradov_three_primes (A : ℝ) (hA : 0 < A) :
    ∃ C > 0, ∀ N : ℕ, 2 ≤ N →
      |NTKB.Davenport.threePrimeRep N - NTKB.Davenport.singularSeries N * N ^ 2 / 2| ≤
        C * N ^ 2 * Real.log N ^ (-A) :=
  NTKB.Davenport.vinogradov_three_primes A hA

theorem exists_three_primes_of_odd :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Odd N →
      ∃ p₁ p₂ p₃ : ℕ, p₁.Prime ∧ p₂.Prime ∧ p₃.Prime ∧ p₁ + p₂ + p₃ = N :=
  NTKB.Davenport.exists_three_primes_of_odd

end NTKB.Headlines.Davenport
