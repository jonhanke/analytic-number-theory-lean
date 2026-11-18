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
import NTKB.Analytic.Davenport.ClassNumber.Unconditional
import NTKB.Analytic.Davenport.Forms.Invariance
import NTKB.Analytic.Davenport.Forms.Units
import NTKB.Analytic.Davenport.Zeros.RiemannVonMangoldtExact
import NTKB.Analytic.Davenport.Zeros.ExplicitReal
import NTKB.Analytic.Davenport.Zeros.ExplicitSmall
import NTKB.Analytic.Davenport.Explicit.RiemannMemoir
import NTKB.Analytic.Davenport.Explicit.LSimplified
import NTKB.Analytic.Davenport.ClassNumber.EvenZero
import NTKB.Analytic.Davenport.Zeros.PNTAPExceptional
import NTKB.Analytic.Davenport.Siegel.Hecke
import NTKB.Analytic.Davenport.Sieve.Montgomery
import NTKB.Analytic.Davenport.Zeros.ZeroCountArgBook
import NTKB.Analytic.Davenport.Zeros.LZeroCountArgBook
import NTKB.Analytic.Davenport.Poisson.Summation
import NTKB.Analytic.Davenport.Ch1to6.CubicRoots

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

The class number statements are *conditional* (since 0.4.0 the inputs are proved: see the unconditional copies in the
section *New in 0.4.0* below): each takes the two named inputs
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

/-! ## New in 0.4.0: class numbers with no assumed input, binary quadratic forms (Chapter 6), the Riemann–von
Mangoldt formula (Chapter 15) and von Mangoldt's explicit formula (Chapter 17)

The five class number statements of 0.3.0 without their two named inputs, which are now theorems of the library (the
ring of integers, discriminant and decomposition law of a quadratic field, proved from Mathlib's `QuadraticAlgebra`). -/

section ClassNumberUnconditional

open scoped NumberField

theorem classNumber_eq_sum_of_discr_neg_unconditional {K : Type} [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) (hD : NumberField.discr K < 0) :
    (NumberField.classNumber K : ℂ) =
      -((NumberField.Units.torsionOrder K : ℂ) / (2 * (NumberField.discr K).natAbs)) *
        ∑ m ∈ Icc 1 (NumberField.discr K).natAbs, (m : ℂ) * NTKB.kroneckerChar (NumberField.discr K) m :=
  NTKB.Davenport.classNumber_eq_sum_of_discr_neg_unconditional hK hD

theorem classNumber_mul_log_eq_sum_of_discr_pos_unconditional {K : Type} [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) (hD : 0 < NumberField.discr K) (ε : (𝓞 K)ˣ)
    (hε : Subgroup.closure {ε} ⊔ NumberField.Units.torsion K = ⊤) (w : NumberField.InfinitePlace K) :
    ((NumberField.classNumber K * |Real.log (w (ε : K))| : ℝ) : ℂ) = -(1 / 2) *
      ∑ m ∈ Ico 1 (NumberField.discr K).natAbs,
        NTKB.kroneckerChar (NumberField.discr K) m *
          (Real.log (Real.sin (π * m / NumberField.discr K)) : ℂ) :=
  NTKB.Davenport.classNumber_mul_log_eq_sum_of_discr_pos_unconditional hK hD ε hε w

theorem classNumber_eq_jacobi_unconditional {K : Type} [Field K] [NumberField K]
    {q : ℕ} [Fact q.Prime] (hq : q % 4 = 3) (hq3 : 3 < q) (hK : Module.finrank ℚ K = 2)
    (hDq : NumberField.discr K = -q) :
    (q : ℤ) * NumberField.classNumber K = -∑ m ∈ Ico 1 q, (m : ℤ) * legendreSym q m :=
  NTKB.Davenport.classNumber_eq_jacobi_unconditional hq hq3 hK hDq

theorem classNumber_gt_of_discr_neg_unconditional {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 →
      NumberField.discr K < 0 →
        C * |(NumberField.discr K : ℝ)| ^ ((1 : ℝ) / 2 - ε) < NumberField.classNumber K :=
  NTKB.Davenport.classNumber_gt_of_discr_neg_unconditional hε

theorem classNumber_mul_log_gt_of_discr_pos_unconditional {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 →
      0 < NumberField.discr K →
      ∀ (η : (𝓞 K)ˣ), Subgroup.closure {η} ⊔ NumberField.Units.torsion K = ⊤ →
        ∀ w : NumberField.InfinitePlace K,
          C * (NumberField.discr K : ℝ) ^ ((1 : ℝ) / 2 - ε) <
            NumberField.classNumber K * |Real.log (w (η : K))| :=
  NTKB.Davenport.classNumber_mul_log_gt_of_discr_pos_unconditional hε

end ClassNumberUnconditional

theorem basic_theorem_binary_forms {D : ℤ} (hD : NTKB.IsFundamentalDiscriminant D) (h1 : D ≠ 1)
    {S : Finset (ℤ × ℤ × ℤ)} (hS : NTKB.Davenport.IsDavFormSystem D S) {n : ℕ} (hn : 0 < n) :
    ((∑ f ∈ S, NTKB.Davenport.repClassCount f n : ℕ) : ℂ) = ∑ m ∈ n.divisors, NTKB.kroneckerChar D m :=
  NTKB.Davenport.sum_repClassCount_eq_of_isDavFormSystem hD h1 hS hn

theorem total_representations_of_discr_neg {D : ℤ} (hD : NTKB.IsFundamentalDiscriminant D) (hneg : D < 0)
    {S : Finset (ℤ × ℤ × ℤ)} (hS : NTKB.Davenport.IsFormSystem D S) {n : ℕ} (hn : 0 < n) :
    ((∑ f ∈ S, Nat.card (NTKB.Davenport.Reps f n) : ℕ) : ℂ) =
      ((if D = -3 then 6 else if D = -4 then 4 else 2 : ℕ) : ℂ) * ∑ m ∈ n.divisors, NTKB.kroneckerChar D m :=
  NTKB.Davenport.sum_card_reps_eq_of_neg hD hneg hS hn

theorem riemann_von_mangoldt {T : ℝ} (hT : 0 < T) (hTz : ∀ ρ : NTKB.ZeroIndex NTKB.riemannXi, |ρ.val.im| ≠ T) :
    |(NTKB.zetaZeroCount T : ℝ) -
      (T / (2 * π) * Real.log (T / (2 * π)) - T / (2 * π) + 7 / 8 + NTKB.zetaArgS T)| ≤ 3 / T :=
  NTKB.Davenport.riemann_von_mangoldt hT hTz

theorem explicit_formula_vonMangoldt {x : ℝ} (hx : 2 ≤ x) :
    Filter.Tendsto (fun T : ℝ ↦ ∑ ρ ∈ NTKB.zerosBelow T, (x : ℂ) ^ ρ.val / ρ.val) Filter.atTop
      (nhds ((x : ℂ) - NTKB.psi0R x - Real.log (2 * π) -
        ((1 / 2 * Real.log (1 - x ^ (-2 : ℝ)) : ℝ) : ℂ))) :=
  NTKB.Davenport.explicit_formula_vonMangoldt_of_two_le hx

/-! ## New in 0.4.1: von Mangoldt's explicit formula for every real `x > 1` (Chapter 17) -/

theorem explicit_formula_vonMangoldt_of_one_lt {x : ℝ} (hx : 1 < x) :
    Filter.Tendsto (fun T : ℝ ↦ ∑ ρ ∈ NTKB.zerosBelow T, (x : ℂ) ^ ρ.val / ρ.val) Filter.atTop
      (nhds ((x : ℂ) - NTKB.psi0R x - Real.log (2 * π) -
        ((1 / 2 * Real.log (1 - x ^ (-2 : ℝ)) : ℝ) : ℂ))) :=
  NTKB.Davenport.explicit_formula_vonMangoldt hx

/-! ## New in 0.5.0: explicit formulas (Chapters 8 and 19), the exceptional zero (Chapters 14 and 20), Hecke's class
number bound (Chapter 21) and Montgomery's large sieve (Chapter 27)

The Brun–Titchmarsh inequality, which the library proves from Montgomery's large sieve
(`NTKB.Davenport.brun_titchmarsh`, `NTKB.Davenport.brun_titchmarsh_asymptotic`), is not a headline:
PrimeNumberTheoremAnd proves it by the Selberg sieve (`BrunTitchmarsh.primesBetween_le`). -/

theorem explicit_formula_memoir {x : ℝ} (hx : 1 < x) (hpp : ∀ n : ℕ, IsPrimePow n → (n : ℝ) ≠ x) :
    Filter.Tendsto (fun T : ℝ ↦ -∑ ρ ∈ NTKB.zerosBelow T, (x : ℂ) ^ ρ.val / ρ.val -
        deriv riemannZeta 0 / riemannZeta 0 - ((1 / 2 * Real.log (1 - x ^ (-2 : ℝ)) : ℝ) : ℂ))
      Filter.atTop (nhds ((Chebyshev.psi x - x : ℝ) : ℂ)) :=
  NTKB.Davenport.explicit_formula_memoir hx hpp

theorem explicit_formula_psiL :
    ∃ A : ℝ, 0 < A ∧ ∀ {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
      (hq : q ≠ 1), ∀ x : ℝ, 2 ≤ x → ∀ T : ℝ, 2 ≤ T → T ≤ x →
      ‖NTKB.psiL χ x - (-∑ ρ ∈ NTKB.zerosBelowL hχ hq T, (x : ℂ) ^ ρ.val / ρ.val - NTKB.bChar χ)‖ ≤
        A * x * Real.log (q * x) ^ 2 / T :=
  NTKB.Davenport.explicit_formula_psiL_simplified

theorem real_zero_lt :
    ∃ c : ℝ, 0 < c ∧ ∀ {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q},
      χ.IsQuadratic → χ ≠ 1 → ∀ β : ℝ, χ.LFunction β = 0 →
        β < 1 - c / (√(q : ℝ) * Real.log q ^ 2) ∧
          (χ.Even → β < 1 - c / (√(q : ℝ) * Real.log q)) :=
  NTKB.Davenport.real_zero_lt_book

theorem psiAP_exceptional (C : ℝ) (hC : 0 < C) :
    ∃ c A : ℝ, 0 < c ∧ 0 < A ∧ ∀ {q : ℕ} [NeZero q] {a : ZMod q}, IsUnit a →
      ∀ x : ℝ, 3 ≤ x → Real.log q ≤ C * √(Real.log x) →
      ((∀ (χ : DirichletCharacter ℂ q) (β : ℝ), ¬ NTKB.IsExceptional χ β) →
        |NTKB.psiAP a x - x / q.totient| ≤ A * x * Real.exp (-(c * √(Real.log x)))) ∧
      (∀ (χ₁ : DirichletCharacter ℂ q) (β₁ : ℝ), NTKB.IsExceptional χ₁ β₁ →
        ‖(NTKB.psiAP a x : ℂ) - x / q.totient + χ₁ a * (x : ℂ) ^ (β₁ : ℂ) / (q.totient * β₁)‖ ≤
          A * x * Real.exp (-(c * √(Real.log x)))) :=
  NTKB.Davenport.psiAP_exceptional_real C hC

theorem classNumber_gt_of_no_real_zero {c₂ : ℝ} (hc₂ : 0 < c₂) :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 →
      NumberField.discr K < 0 →
      (∀ σ : ℝ, 1 - c₂ / Real.log |(NumberField.discr K : ℝ)| < σ → σ < 1 →
        (NTKB.kroneckerChar (NumberField.discr K)).LFunction σ ≠ 0) →
      C * √|(NumberField.discr K : ℝ)| / Real.log |(NumberField.discr K : ℝ)| < NumberField.classNumber K :=
  NTKB.Davenport.classNumber_gt_of_no_real_zero hc₂

theorem classNumber_mul_regulator_gt_of_no_real_zero {c₂ : ℝ} (hc₂ : 0 < c₂) :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 →
      0 < NumberField.discr K →
      (∀ σ : ℝ, 1 - c₂ / Real.log (NumberField.discr K : ℝ) < σ → σ < 1 →
        (NTKB.kroneckerChar (NumberField.discr K)).LFunction σ ≠ 0) →
      C * √(NumberField.discr K : ℝ) / Real.log (NumberField.discr K : ℝ) <
        NumberField.classNumber K * NumberField.Units.regulator K :=
  NTKB.Davenport.classNumber_mul_regulator_gt_of_no_real_zero hc₂

theorem card_le_montgomery {Q : ℝ} (hQ : 1 ≤ Q) (M : ℤ) (N : ℕ) (Z : Finset ℤ) (hZ : Z ⊆ Ioc M (M + N)) :
    (Z.card : ℝ) ≤ (N + 3 * Q ^ 2) / NTKB.Davenport.montgomeryL Z Q :=
  NTKB.Davenport.card_le_montgomery hQ M N Z hZ

/-! ## New in 0.6.0: the zeros in the book's form (Chapters 8, 15, 16), Poisson summation (Chapter 2) and Kummer's
cubic periods (Chapter 3)

The change of argument by continuous variation is `NTKB.argChange φ a b`: the value `θ(b) - θ(a)` for any
continuous `θ` on `[a, b]` with `φ = |φ| e^{iθ}` (it does not depend on the choice of `θ`,
`NTKB.IsArgChange.unique`; it is `0` by convention if no such `θ` exists, which does not happen below, where `φ`
has no zero on the path). -/

theorem riemann_von_mangoldt_argChange :
    ∃ A : ℝ, 0 < A ∧ ∀ T : ℝ, 3 ≤ T →
      |(NTKB.zetaZeroCount T : ℝ) - (T / (2 * π) * Real.log (T / (2 * π)) - T / (2 * π))| ≤
          A * Real.log T ∧
      |(NTKB.zetaZeroCountLE T : ℝ) - (T / (2 * π) * Real.log (T / (2 * π)) - T / (2 * π))| ≤
          A * Real.log T ∧
      ((∀ ρ : NTKB.ZeroIndex NTKB.riemannXi, |ρ.val.im| ≠ T) →
        2 * π * NTKB.zetaZeroCount T =
          NTKB.argChange (fun y : ℝ ↦ NTKB.riemannXi (2 + y * I)) 0 T +
          NTKB.argChange (fun x : ℝ ↦ NTKB.riemannXi (x + T * I)) 2 (-1) +
          NTKB.argChange (fun y : ℝ ↦ NTKB.riemannXi (-1 + y * I)) T 0 +
          NTKB.argChange (fun x : ℝ ↦ NTKB.riemannXi x) (-1) 2) :=
  NTKB.Davenport.riemann_von_mangoldt_argChange

theorem abs_argChange_LFunction_le :
    ∃ A : ℝ, 0 < A ∧ ∀ {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}, χ.IsPrimitive → N ≠ 1 →
      ∀ T : ℝ, 2 ≤ T → (∀ ρ : NTKB.ZeroIndex (NTKB.dirichletXi χ), |ρ.val.im| ≠ T) →
      ∀ h : ℝ, |h| = T →
      |NTKB.argChange (fun x : ℝ ↦ χ.LFunction (x + h * I)) (3 / 2) (1 / 2)| ≤
          A * (Real.log N + Real.log (T + 2)) ∧
      |NTKB.argChange (fun y : ℝ ↦ χ.LFunction (3 / 2 + y * I)) 0 h +
          NTKB.argChange (fun x : ℝ ↦ χ.LFunction (x + h * I)) (3 / 2) (1 / 2)| ≤
          A * (Real.log N + Real.log (T + 2)) :=
  NTKB.Davenport.abs_argChange_LFunction_le

theorem poisson_summation_piecewise_monotone {f : ℝ → ℝ} {A B : ℝ} (hAB : A < B)
    (hf : ContinuousOn f (Set.Icc A B)) (hpm : NTKB.Davenport.Poisson.PiecewiseMonotoneOn f A B) :
    Filter.Tendsto (fun N : ℕ ↦ ∑ ν ∈ Finset.Icc (-(N : ℤ)) N,
        ∫ x in A..B, (f x : ℂ) * Complex.exp (2 * π * Complex.I * ν * x)) Filter.atTop
      (nhds (NTKB.Davenport.Poisson.halvedSum f A B : ℂ)) :=
  NTKB.Davenport.Poisson.poisson_summation_piecewise_monotone hAB hf hpm

theorem kummer_cubic_periods {q : ℕ} [Fact q.Prime] (hq : q % 3 = 1) {g : (ZMod q)ˣ}
    (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    ∃ a b : ℤ, 4 * (q : ℤ) = a ^ 2 + 27 * b ^ 2 ∧ a ≡ 1 [ZMOD 3] ∧ ∀ z : ℂ,
      z ^ 3 - 3 * q * z - q * a =
        (z - NTKB.Davenport.kummerPeriod g 0) * (z - NTKB.Davenport.kummerPeriod g 1) *
          (z - NTKB.Davenport.kummerPeriod g 2) :=
  NTKB.Davenport.exists_cubic_eq_prod_kummerPeriod hq hg

end NTKB.Headlines.Davenport
