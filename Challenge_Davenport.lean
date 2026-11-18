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

/-!
# Headline statements of analytic-number-theory-lean: Davenport

H. Davenport, *Multiplicative Number Theory* (2nd edition, revised by H. L. Montgomery, 1980). The main results of
the library for this book, one theorem each, with every proof a deliberate `sorry`: to check what is claimed, read
this file. `Solution_Davenport.lean` proves the same statements from the library, and `lake comparator`
(configured by `comparator/Davenport.json`) checks that each proved statement is exactly the one here and uses only
the standard axioms `propext`, `Classical.choice` and `Quot.sound`.

Each statement is the library's statement, copied. The statements were not yet reviewed by a human (see the README).
Constants are explicit where the library has them (Davenport's absolute constants `c` are not computed in the book).

`L(s, χ)` is Mathlib's `DirichletCharacter.LFunction χ s`; `ζ` is Mathlib's `riemannZeta`; `Λ` is Mathlib's von
Mangoldt function.

## Definitions used

Besides Mathlib, the statements use these definitions of the library; a reader checking a statement should check
these too:

* `NTKB.dirichletXi` (Davenport's `ξ(s, χ) = (q/π)^{(s+a)/2} Γ((s+a)/2) L(s, χ)`, defined as `q^{(s+a)/2}` times
  Mathlib's completed `L`-function `DirichletCharacter.completedLFunction`) and `NTKB.dirichletParity` (`a = 0` for
  even `χ`, `1` for odd `χ`)
* `NTKB.ZeroIndex f` (the zeros of an entire function `f`, each repeated according to its multiplicity, Mathlib's
  `analyticOrderNatAt`)
* `NTKB.logQT N t = log(N max(1, |t|))`
* `NTKB.zetaZeroCount T` (Davenport's `N(T)`: zeros `β + iγ` of `ζ` with `0 < β < 1` and `0 < γ < T`, with
  multiplicity) and `NTKB.LZeroCount χ T` (Davenport's `N(T, χ)`: zeros of `L(s, χ)` with `0 < β < 1` and
  `|γ| < T`, with multiplicity)
* `NTKB.zerosBelowL hχ hq T` (the zeros of `ξ(s, χ)` with multiplicity and `|γ| < T`), `NTKB.psi0L χ N`
  (`ψ₀(N, χ) = ∑_{n < N} χ(n) Λ(n) + χ(N) Λ(N)/2`) and `NTKB.bEven χ` (Davenport's `b(χ)` for even `χ`: the constant
  term of `L'/L(s, χ)` at `s = 0`)
* `NTKB.psiAP a x` (`ψ(x; q, a) = ∑_{n ≤ x, n ≡ a mod q} Λ(n)`) and `NTKB.IsPageModulus z q'` (a modulus
  `q' ≤ z` of a real primitive character `χ' ≠ 1` with a real zero `β > 1 - 1/(800 log z)` of `L(s, χ')`)
* (since 0.2.0) `NTKB.Davenport.psiAP x q a` (the same `ψ(x; q, a)` with `x : ℝ`, `q : ℕ`, `a : ℤ`, as in the
  sieve chapters: `∑ Λ(n)` over `1 ≤ n ≤ x` with `n ≡ a (mod q)`), `NTKB.Davenport.primeCountingAP x q a`
  (`π(x; q, a)`, the number of primes `p ≤ x` with `p ≡ a (mod q)`) and `NTKB.logIntegral x`
  (`li x = ∫_2^x dt/log t`)
* (since 0.3.0) `NTKB.kroneckerChar D` (the Kronecker symbol `(D/·)` as a Dirichlet character modulo `|D|`),
  `NTKB.IsFundamentalDiscriminant D`, `NTKB.Davenport.threePrimeRep N`
  (`r(N) = ∑_{k₁ + k₂ + k₃ = N} Λ(k₁) Λ(k₂) Λ(k₃)`) and `NTKB.Davenport.singularSeries N` (the singular series
  `G(N) = ∏_{p ∣ N} (1 - (p - 1)⁻²) ∏_{p ∤ N} (1 + (p - 1)⁻³)`); the class number, discriminant, regulator, number
  of roots of unity and infinite places of a number field are Mathlib's (`NumberField.classNumber`,
  `NumberField.discr`, `NumberField.Units.regulator`, `NumberField.Units.torsionOrder`,
  `NumberField.InfinitePlace`)
* (since 0.3.0) the two **named inputs** of the class number statements, structures assumed as hypotheses, not
  proved in this library: `NTKB.Davenport.QuadraticFieldDiscriminants` (the discriminant of a quadratic number field
  is a fundamental discriminant, and every fundamental discriminant `d ≠ 1` is the discriminant of a quadratic
  number field) and `NTKB.Davenport.QuadraticIdealCount` (in a quadratic number field of discriminant `d` the number
  of ideals of norm `n ≥ 1` is `∑_{m ∣ n} (d/m)`). Both are classical (Dedekind); the statements that take them are
  marked *conditional*. Since 0.4.0 both are theorems of the library (`NTKB.Davenport.quadraticFieldDiscriminants`,
  `NTKB.Davenport.quadraticIdealCount`), and each conditional statement has an unconditional copy below
  (`..._unconditional`); the conditional statements are kept unchanged.
* (since 0.4.0) binary quadratic forms `(a, b, c) : ℤ × ℤ × ℤ` (`a x² + b x y + c y²`) with
  `NTKB.Davenport.formDisc f = b² - 4ac`, `NTKB.Davenport.formEval`, proper equivalence `NTKB.Davenport.FormEquiv`
  (by a matrix of `SL₂(ℤ)`, `NTKB.Davenport.formSubst`), `NTKB.Davenport.IsDavFormSystem D S` and
  `NTKB.Davenport.IsFormSystem D S` (`S` is a complete system of representatives of the proper classes of forms of
  discriminant `D`, positive definite if `D < 0`, resp. with `a > 0`), `NTKB.Davenport.Reps f n` (the solutions of
  `f(x, y) = n`) and `NTKB.Davenport.repClassCount f n` (Davenport's `R_f(n)`: their number up to automorphs of `f`)
* (since 0.4.0) `NTKB.riemannXi` (Riemann's `ξ`, from Mathlib's `completedRiemannZeta₀`), `NTKB.zerosBelow T` (the
  zeros of `ξ` with multiplicity and `|γ| < T`), `NTKB.zetaArgS T` (Davenport's `S(T)`, `π⁻¹` times the argument of
  `ζ(1/2 + iT)` by continuous variation from `2` along `2 → 2 + iT → 1/2 + iT`, written as the integral of `ζ'/ζ`),
  `NTKB.psi0R x` (`ψ₀(x) = ∑_{n ≤ x} Λ(n)`, with the term `n = x` halved)
* (since 0.5.0) `NTKB.psiL χ x` (`ψ(x, χ) = ∑_{n ≤ x} χ(n) Λ(n)`), `NTKB.bChar χ` (Davenport's `b(χ)`: the constant
  term of `L'/L(s, χ)` at `s = 0`, for every `χ`), `NTKB.IsExceptional χ β` (`β` is an exceptional zero: `χ ≠ 1`,
  `χ² = 1`, `L(β, χ) = 0` and `β > 1 - 1/(16200 log q)`), `NTKB.Davenport.sieveOmega Z p` (the number of residue
  classes modulo `p` containing no element of `Z`) and `NTKB.Davenport.montgomeryL Z Q`
  (`L = ∑_{q ≤ Q} μ(q)² ∏_{p ∣ q} ω(p)/(p - ω(p))`)

A real character is one with `χ ^ 2 = 1`, or in the statements since 0.2.0, Mathlib's `χ.IsQuadratic` (every value
is `0`, `1` or `-1`); these are equivalent.
-/

namespace NTKB.Headlines.Davenport

open Complex _root_.DirichletCharacter Finset
open scoped Real ArithmeticFunction.vonMangoldt

/-- **The Hadamard product for `ξ(s, χ)`** (Chapter 12, (17)): for a primitive character `χ` modulo `N > 1`,
`ξ(s, χ) = e^{A + Bs} ∏_ρ (1 - s/ρ) e^{s/ρ}` over the zeros `ρ` of `ξ(s, χ)` with multiplicity. The library proves
Hadamard's factorization theorem for entire functions of order at most one (`Davenport.hadamard_factorization_order_one`,
Chapter 11), shows that `ξ(s, χ)` has order one and applies it; the product converges locally uniformly
(`hasProdLocallyUniformlyOn_canonicalProductOne`). PrimeNumberTheoremAnd has Hadamard's theorem for every finite order
and the product for `ξ(s)` (`riemannXi_hadamard_factorization`), not the product for `ξ(s, χ)`; Mathlib has
neither. -/
theorem dirichletXi_hadamard {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive)
    (hN : N ≠ 1) :
    ∃ A B : ℂ, ∀ s, NTKB.dirichletXi χ s = Complex.exp (A + B * s) *
      ∏' ρ : NTKB.ZeroIndex (NTKB.dirichletXi χ), (1 - s / ρ.val) * Complex.exp (s / ρ.val) := by
  sorry

/-- **The zero-free region for `L(s, χ)`, complex characters** (Chapter 14, Theorem, p. 93): if `χ² ≠ 1`, then
`L(s, χ)` has no zero with `σ > 1 - c/log(N max(1, |t|))`, `c = 1/16200`. Mathlib has `L(s, χ) ≠ 0` on `σ ≥ 1`
(`DirichletCharacter.LFunction_ne_zero_of_one_le_re`); PrimeNumberTheoremAnd has a zero-free region for `ζ`, not
for `L(s, χ)`. -/
theorem LFunction_zero_free_complex {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ2 : χ ^ 2 ≠ 1) {s : ℂ}
    (hs : LFunction χ s = 0) :
    s.re ≤ 1 - 1 / 16200 / NTKB.logQT N s.im := by
  sorry

/-- **The zero-free region for `L(s, χ)`, real characters** (Chapter 14, Theorem, p. 93): for a real character
`χ ≠ 1`, a zero of `L(s, χ)` in the same region is real, and there is at most one. -/
theorem LFunction_zero_free_real {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ1 : χ ≠ 1)
    (hreal : χ ^ 2 = 1) {s : ℂ} (hs : LFunction χ s = 0)
    (hreg : 1 - 1 / 16200 / NTKB.logQT N s.im < s.re) :
    s.im = 0 ∧ ∀ s' : ℂ, LFunction χ s' = 0 → 1 - 1 / 16200 / NTKB.logQT N s'.im < s'.re → s' = s := by
  sorry

/-- **The exceptional zero is simple** (Chapter 14, Theorem, p. 93): for a real primitive character `χ ≠ 1`, a zero
of `ξ(s, χ)` in the region has multiplicity one. -/
theorem LFunction_zero_free_real_simple {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1) (hreal : χ ^ 2 = 1) (ρ : NTKB.ZeroIndex (NTKB.dirichletXi χ))
    (hreg : 1 - 1 / 16200 / NTKB.logQT N ρ.val.im < ρ.val.re) :
    analyticOrderNatAt (NTKB.dirichletXi χ) ρ.val = 1 := by
  sorry

/-- **Landau's theorem on real zeros** (Chapter 14, p. 93): for distinct real primitive characters `χ₁ ≠ 1`,
`χ₂ ≠ 1` modulo `q₁`, `q₂` with real zeros `β₁`, `β₂` of their `L`-functions, `min(β₁, β₂) ≤ 1 - c/log(q₁ q₂)`,
`c = 1/400`. Not in Mathlib, Tau Ceti or PrimeNumberTheoremAnd. -/
theorem landau_real_zeros {q₁ q₂ : ℕ} [NeZero q₁] [NeZero q₂]
    {χ₁ : DirichletCharacter ℂ q₁} {χ₂ : DirichletCharacter ℂ q₂} (hp₁ : χ₁.IsPrimitive)
    (hp₂ : χ₂.IsPrimitive) (h₁ : χ₁ ≠ 1) (h₂ : χ₂ ≠ 1) (hr₁ : χ₁ ^ 2 = 1) (hr₂ : χ₂ ^ 2 = 1)
    (hne : changeLevel (dvd_mul_right q₁ q₂) χ₁ ≠ changeLevel (dvd_mul_left q₂ q₁) χ₂)
    {β₁ β₂ : ℝ} (hz₁ : LFunction χ₁ β₁ = 0) (hz₂ : LFunction χ₂ β₂ = 0) :
    min β₁ β₂ ≤ 1 - 1 / 400 / Real.log (q₁ * q₂) := by
  sorry

/-- **Page's theorem** (Chapter 14, p. 95): for `z ≥ 3` there is at most one real primitive character `χ ≠ 1` to a
modulus `q ≤ z` whose `L`-function has a real zero `β > 1 - c/log z`, `c = 1/800`. Not in Mathlib, Tau Ceti or
PrimeNumberTheoremAnd. -/
theorem page_exceptional_character {z : ℝ} (hz3 : 3 ≤ z) {q₁ q₂ : ℕ} [NeZero q₁]
    [NeZero q₂] {χ₁ : DirichletCharacter ℂ q₁} {χ₂ : DirichletCharacter ℂ q₂}
    (hp₁ : χ₁.IsPrimitive) (hp₂ : χ₂.IsPrimitive) (h₁ : χ₁ ≠ 1) (h₂ : χ₂ ≠ 1)
    (hr₁ : χ₁ ^ 2 = 1) (hr₂ : χ₂ ^ 2 = 1) (hq₁ : (q₁ : ℝ) ≤ z) (hq₂ : (q₂ : ℝ) ≤ z)
    {β₁ β₂ : ℝ} (hz₁ : LFunction χ₁ β₁ = 0) (hz₂ : LFunction χ₂ β₂ = 0)
    (hb₁ : 1 - 1 / 800 / Real.log z < β₁) (hb₂ : 1 - 1 / 800 / Real.log z < β₂) :
    q₁ = q₂ ∧ HEq χ₁ χ₂ := by
  sorry

/-- **The Riemann–von Mangoldt formula** (Chapter 15, p. 98, and Chapter 8, (1)):
`N(T) = (T/2π) log(T/2π) - T/2π + O(log T)` for `T ≥ 3`. PrimeNumberTheoremAnd has the bound `N(T) ≪ T^{3/2}` and
assumes the formula as a hypothesis elsewhere; Mathlib and Tau Ceti count no zeros of `ζ`. -/
theorem zetaZeroCount_sub_le :
    ∃ A : ℝ, 0 < A ∧ ∀ T : ℝ, 3 ≤ T →
      |(NTKB.zetaZeroCount T : ℝ) - (T / (2 * π) * Real.log (T / (2 * π)) - T / (2 * π))| ≤
        A * Real.log T := by
  sorry

/-- **The number of zeros of `L(s, χ)`** (Chapter 16, p. 101): for a primitive character `χ` modulo `N > 1` and
`T ≥ 3`, `N(T, χ) = (T/π) log(NT/2π) - T/π + O(log NT)` with an absolute constant (`N(T, χ)` counts `|γ| < T`, so it
is twice Davenport's `N(T)`-type count). Not in Mathlib, Tau Ceti or PrimeNumberTheoremAnd. -/
theorem LZeroCount_sub_le :
    ∃ A : ℝ, 0 < A ∧ ∀ {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}, χ.IsPrimitive → N ≠ 1 →
      ∀ T : ℝ, 3 ≤ T →
      |(NTKB.LZeroCount χ T : ℝ) - (T / π * Real.log (N * T / (2 * π)) - T / π)| ≤
        A * Real.log (N * T) := by
  sorry

/-- **The explicit formula for `ψ(x, χ)`, odd characters** (Chapter 19, (2)): for a primitive odd character `χ`
modulo `q > 1` and an integer `N ≥ 3`, `ψ₀(N, χ) = -∑_ρ N^ρ/ρ - L'/L(0, χ) + ∑_{m ≥ 1} N^{1-2m}/(2m - 1)`, the sum
over the nontrivial zeros `ρ` taken as `lim_{T → ∞} ∑_{|γ| < T}`. Not in Mathlib, Tau Ceti or
PrimeNumberTheoremAnd (which have no explicit formula). -/
theorem explicit_formula_psi0L_odd {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
    (hq : q ≠ 1) (ha : NTKB.dirichletParity χ = 1) (N : ℕ) (hN : 3 ≤ N) :
    Filter.Tendsto (fun T : ℝ ↦ ∑ ρ ∈ NTKB.zerosBelowL hχ hq T, (N : ℂ) ^ ρ.val / ρ.val) Filter.atTop
      (nhds (-(deriv (LFunction χ) 0 / LFunction χ 0) +
        ∑' m : ℕ, (N : ℂ) ^ (-(2 * (m : ℂ) + 1)) / (2 * (m : ℂ) + 1) - NTKB.psi0L χ N)) := by
  sorry

/-- **The explicit formula for `ψ(x, χ)`, even characters** (Chapter 19, (3)): for a primitive even character `χ`
modulo `q > 1` and an integer `N ≥ 3`, `ψ₀(N, χ) = -∑_ρ N^ρ/ρ - log N - b(χ) + ∑_{m ≥ 1} N^{-2m}/(2m)`, the sum
over the nontrivial zeros taken as `lim_{T → ∞} ∑_{|γ| < T}`. -/
theorem explicit_formula_psi0L_even {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
    (hq : q ≠ 1) (ha : NTKB.dirichletParity χ = 0) (N : ℕ) (hN : 3 ≤ N) :
    Filter.Tendsto (fun T : ℝ ↦ ∑ ρ ∈ NTKB.zerosBelowL hχ hq T, (N : ℂ) ^ ρ.val / ρ.val) Filter.atTop
      (nhds (-((Real.log N : ℂ) + NTKB.bEven χ) +
        ∑' m : ℕ, (N : ℂ) ^ (-(2 * ((m : ℂ) + 1))) / (2 * ((m : ℂ) + 1)) - NTKB.psi0L χ N)) := by
  sorry

open scoped Classical in
/-- **The prime number theorem for arithmetic progressions with the classical error term** (Chapter 20, (13), after
Page): for every `C > 0` there are `c, A > 0` such that for every integer `N ≥ 3` there is at most one exceptional
modulus `q₁` (a Page modulus, or none: `q₁ = 0`), and for every `q` with `log q ≤ C √(log N)` that is not a multiple of
`q₁` and every `a` prime to `q`, `|ψ(N; q, a) - N/φ(q)| ≤ A N exp(-c √(log N))`. PrimeNumberTheoremAnd has
`ψ(x; q, a) ~ x/φ(q)` for fixed `q` without an error term (`WeakPNT_AP`) and the classical error term for `ψ(x)`
(`StrongPNT`); Mathlib has Dirichlet's theorem. -/
theorem psiAP_sub_le_page (C : ℝ) (hC : 0 < C) :
    ∃ c A : ℝ, 0 < c ∧ 0 < A ∧ ∀ N : ℕ, 3 ≤ N → ∃ q₁ : ℕ,
      (q₁ = 0 ∨ NTKB.IsPageModulus (max 3 (Real.exp (C * √(Real.log N)))) q₁) ∧
      ∀ {q : ℕ} [NeZero q] {a : ZMod q}, IsUnit a → Real.log q ≤ C * √(Real.log N) → ¬ q₁ ∣ q →
        ‖(NTKB.psiAP a N : ℂ) - N / q.totient‖ ≤ A * N * Real.exp (-(c * √(Real.log N))) := by
  sorry

/-- **The Pólya–Vinogradov inequality** (Chapter 23, (1)): for a nonprincipal character `χ` modulo `q`, every sum
of `χ(n)` over an interval `M < n ≤ M + N` has absolute value at most `2 √q log q`. Tau Ceti bounds such sums by
the modulus (`DirichletCharacter.norm_sum_Icc_le_level`); none of Mathlib, Tau Ceti and PrimeNumberTheoremAnd has
the `√q log q` bound. -/
theorem polya_vinogradov {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) (M : ℤ) (N : ℕ) :
    ‖∑ n ∈ Ioc M (M + N), χ n‖ ≤ 2 * √q * Real.log q := by
  sorry

/-- **The large sieve** (Chapter 27, Theorem 2): for points `α_r` that are `δ`-separated modulo `1` and complex
numbers `a_n`, `∑_r |∑_{M < n ≤ M + N} a_n e(n α_r)|² ≤ (N + 3/δ) ∑_n |a_n|²`. Not in Mathlib, Tau Ceti or
PrimeNumberTheoremAnd. -/
theorem large_sieve {ι : Type*} (s : Finset ι) (α : ι → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ r ∈ s, ∀ t ∈ s, r ≠ t → ∀ m : ℤ, δ ≤ |α r - α t - m|) (M : ℤ) (N : ℕ)
    (a : ℤ → ℂ) :
    ∑ r ∈ s, ‖∑ n ∈ Ioc M (M + N), a n * Complex.exp (2 * π * Complex.I * (n * α r))‖ ^ 2 ≤
      (N + 3 / δ) * ∑ n ∈ Ioc M (M + N), ‖a n‖ ^ 2 := by
  sorry

open scoped Classical in
/-- **The large sieve for characters** (Chapter 27, Theorem 4, Gallagher's form): for `Q ≥ 1`,
`∑_{q ≤ Q} (q/φ(q)) ∑*_χ |∑_{M < n ≤ M + N} c_n χ(n)|² ≤ (N + 3Q²) ∑_n |c_n|²`, the inner sum over the primitive
characters modulo `q`. -/
theorem large_sieve_characters {Q : ℝ} (hQ : 1 ≤ Q) (M : ℤ) (N : ℕ) (c : ℤ → ℂ) :
    ∑ q ∈ Icc 1 ⌊Q⌋₊, ((q : ℝ) / q.totient) *
        ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ ↦ χ.IsPrimitive),
          ‖∑ n ∈ Ioc M (M + N), c n * χ n‖ ^ 2 ≤
      (N + 3 * Q ^ 2) * ∑ n ∈ Ioc M (M + N), ‖c n‖ ^ 2 := by
  sorry

/-- **Vinogradov's estimate for exponential sums over primes** (Chapter 25, (2), by Vaughan's identity, Chapter 24):
if `|α - a/q| ≤ q⁻²` with `a` prime to `q`, then
`∑_{n ≤ N} Λ(n) e(nα) ≪ (N q^{-1/2} + N^{4/5} + N^{1/2} q^{1/2}) (log N)⁴`. Not in Mathlib, Tau Ceti or
PrimeNumberTheoremAnd. -/
theorem vinogradov_prime_exponential_sum : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (a : ℤ) (q : ℕ), 1 ≤ q →
    IsCoprime a q → |α - a / q| ≤ 1 / (q : ℝ) ^ 2 → ∀ N : ℕ, 2 ≤ N →
    ‖∑ n ∈ Icc 1 N, (Λ n : ℂ) * Complex.exp (2 * π * Complex.I * (n * α))‖ ≤
      C * (N / √q + (N : ℝ) ^ ((4 : ℝ) / 5) + √N * √q) * Real.log N ^ 4 := by
  sorry

/-! ## New in 0.2.0: Siegel's theorem and what rests on it (Chapters 21, 22, 28, 29) -/

/-- **Siegel's theorem** (Chapter 21, (1)): for every `ε > 0` there is `C(ε) > 0` such that
`L(1, χ) > C(ε) q^{-ε}` for every real primitive character `χ ≠ 1` modulo `q`. (`L(1, χ)` is real for a real
character; the statement is about its real part.) The constant is not effective. Proof: Estermann's, as in the
book. Tau Ceti has parts of a proof (the nonnegative coefficients of `ζ(s) L(s, χ) L(s, ψ) L(s, χψ)`, ported here
with credit, and `|L(1, χ)| ≪ log q`) but not the theorem; Mathlib and PrimeNumberTheoremAnd have neither. -/
theorem siegel {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}, χ.IsPrimitive →
      χ.IsQuadratic → χ ≠ 1 → C * (q : ℝ) ^ (-ε) < (χ.LFunction 1).re := by
  sorry

/-- **Siegel's theorem, second form** (Chapter 21, (D)): for every `ε > 0` there is `C(ε) > 0` such that
`L(σ, χ) ≠ 0` for real `σ > 1 - C(ε) q^{-ε}`, for every real character `χ ≠ 1` modulo `q` (primitive or not). Not in
Mathlib, Tau Ceti or PrimeNumberTheoremAnd. -/
theorem siegel_second_form {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q},
      χ.IsQuadratic → χ ≠ 1 → ∀ σ : ℝ, 1 - C * (q : ℝ) ^ (-ε) < σ → χ.LFunction σ ≠ 0 := by
  sorry

/-- **The Siegel–Walfisz theorem** (Chapter 22, (D)): for every `B > 0` there are `c, C > 0` such that
`|ψ(x; q, a) - x/φ(q)| ≤ C x exp(-c √(log x))` for all `x ≥ 2`, `q ≤ (log x)^B` and `a` prime to `q` (`c` is not
effective). PrimeNumberTheoremAnd has `ψ(x; q, a) ~ x/φ(q)` for fixed `q` without an error term (`WeakPNT_AP`);
Mathlib has Dirichlet's theorem; Tau Ceti has neither error term. -/
theorem siegel_walfisz (B : ℝ) (hB : 0 < B) :
    ∃ c > 0, ∃ C > 0, ∀ x : ℝ, 2 ≤ x → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.log x ^ B →
      ∀ a : ℤ, IsCoprime a q →
        |NTKB.Davenport.psiAP x q a - x / q.totient| ≤ C * x * Real.exp (-c * √(Real.log x)) := by
  sorry

/-- **The Siegel–Walfisz theorem for `π(x; q, a)`** (Chapter 22, p. 133): for every `B > 0` there are `c, C > 0`
such that `|π(x; q, a) - li(x)/φ(q)| ≤ C x exp(-c √(log x))` for all `x ≥ 2`, `q ≤ (log x)^B` and `a` prime to `q`.
(The book's saving of a factor `log x` in the error is absorbed by a change of `c`.) Not in Mathlib, Tau Ceti or
PrimeNumberTheoremAnd. -/
theorem siegel_walfisz_primeCounting (B : ℝ) (hB : 0 < B) :
    ∃ c > 0, ∃ C > 0, ∀ x : ℝ, 2 ≤ x → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.log x ^ B →
      ∀ a : ℤ, IsCoprime a q →
        |(NTKB.Davenport.primeCountingAP x q a : ℝ) - NTKB.logIntegral x / q.totient| ≤
          C * x * Real.exp (-c * √(Real.log x)) := by
  sorry

/-- **The Bombieri–Vinogradov theorem** (Chapter 28, Bombieri's theorem, p. 161): for every `A > 0`,
`∑_{q ≤ Q} max_{y ≤ x} max_{(a, q) = 1} |ψ(y; q, a) - y/φ(q)| ≪ x^{1/2} Q (log x)^5` for
`x^{1/2} (log x)^{-A} ≤ Q ≤ x^{1/2}`. The maxima are expressed by arbitrary choices `y(q) ∈ [0, x]` and `a(q)`
prime to `q`, uniformly. Unconditional (it uses the Siegel–Walfisz theorem above). Not in Mathlib, Tau Ceti or
PrimeNumberTheoremAnd. -/
theorem bombieri_vinogradov {A : ℝ} (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 3 ≤ x → ∀ Q : ℝ, √x * Real.log x ^ (-A) ≤ Q → Q ≤ √x →
      ∀ (y : ℕ → ℝ) (a : ℕ → ℤ), (∀ q, 0 ≤ y q ∧ y q ≤ x) → (∀ q, IsCoprime (a q) q) →
        ∑ q ∈ Icc 1 ⌊Q⌋₊, |NTKB.Davenport.psiAP (y q) q (a q) - y q / q.totient| ≤
          C * √x * Q * Real.log x ^ 5 := by
  sorry

/-- **The Barban–Davenport–Halberstam theorem** (Chapter 29, (1), Gallagher's form): for every `A > 0`,
`∑_{q ≤ Q} ∑_{a mod q, (a, q) = 1} (ψ(x; q, a) - x/φ(q))² ≪ x Q log x` for `x (log x)^{-A} < Q ≤ x`.
Unconditional (it uses the Siegel–Walfisz theorem above). Not in Mathlib, Tau Ceti or PrimeNumberTheoremAnd. -/
theorem barban_davenport_halberstam {A : ℝ} (hA : 0 < A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 3 ≤ x → ∀ Q : ℝ, x * Real.log x ^ (-A) < Q → Q ≤ x →
      ∑ q ∈ Icc 1 ⌊Q⌋₊, ∑ a ∈ (Icc 1 q).filter (fun a ↦ Nat.Coprime a q),
        (NTKB.Davenport.psiAP x q a - x / q.totient) ^ 2 ≤ C * x * Q * Real.log x := by
  sorry

/-! ## New in 0.3.0: class number formulas (Chapters 6 and 21) and the three primes theorem (Chapter 26)

The class number statements are *conditional* (since 0.4.0 the inputs are proved: see the unconditional copies in the
section *New in 0.4.0* below): each takes the two named inputs
`NTKB.Davenport.QuadraticFieldDiscriminants` and `NTKB.Davenport.QuadraticIdealCount` as hypotheses (see "Definitions
used" above). The class number and the regulator are those of the field (`h` counts ideal classes, the regulator is
`log ε` for a fundamental unit `ε`, whatever its norm); Davenport's `h(d)` for `d > 0` counts classes of forms. -/

section ClassNumber

open scoped NumberField

/-- **The finite class number formula, `d < 0`** (Chapter 6, p. 51), *conditional*: for an imaginary quadratic field
of discriminant `d` with `w` roots of unity, `h(d) = -(w/(2|d|)) ∑_{m=1}^{|d|} m (d/m)`. Tau Ceti has
`h(d) = w √|d| L(1, χ)/(2π)` (`classNumber_eq_card_units_mul_LFunction_one`), not the finite formula; Mathlib and
PrimeNumberTheoremAnd have neither. -/
theorem classNumber_eq_sum_of_discr_neg {K : Type} [Field K] [NumberField K]
    (hF : NTKB.Davenport.QuadraticFieldDiscriminants) (hI : NTKB.Davenport.QuadraticIdealCount)
    (hK : Module.finrank ℚ K = 2) (hD : NumberField.discr K < 0) :
    (NumberField.classNumber K : ℂ) =
      -((NumberField.Units.torsionOrder K : ℂ) / (2 * (NumberField.discr K).natAbs)) *
        ∑ m ∈ Icc 1 (NumberField.discr K).natAbs, (m : ℂ) * NTKB.kroneckerChar (NumberField.discr K) m := by
  sorry

/-- **The finite class number formula, `d > 0`** (Chapter 6, p. 51), *conditional*: for a real quadratic field of
discriminant `d`, a fundamental unit `ε` (a unit generating the units modulo `±1`) and an infinite place `w`,
`h(d) log ε = -(1/2) ∑_{m=1}^{d-1} (d/m) log sin(π m/d)`, with `log ε = |log w(ε)|`. Not in Mathlib, Tau Ceti or
PrimeNumberTheoremAnd. -/
theorem classNumber_mul_log_eq_sum_of_discr_pos {K : Type} [Field K] [NumberField K]
    (hF : NTKB.Davenport.QuadraticFieldDiscriminants) (hI : NTKB.Davenport.QuadraticIdealCount)
    (hK : Module.finrank ℚ K = 2) (hD : 0 < NumberField.discr K) (ε : (𝓞 K)ˣ)
    (hε : Subgroup.closure {ε} ⊔ NumberField.Units.torsion K = ⊤) (w : NumberField.InfinitePlace K) :
    ((NumberField.classNumber K * |Real.log (w (ε : K))| : ℝ) : ℂ) = -(1 / 2) *
      ∑ m ∈ Ico 1 (NumberField.discr K).natAbs,
        NTKB.kroneckerChar (NumberField.discr K) m *
          (Real.log (Real.sin (π * m / NumberField.discr K)) : ℂ) := by
  sorry

/-- **Jacobi's class number formula** (Chapter 6, p. 51, (19)), *conditional*: for a prime `q ≡ 3 (mod 4)`,
`q > 3`, the quadratic field of discriminant `-q` has `q h(-q) = -∑_{m=1}^{q-1} m (m/q)`. Not in Mathlib, Tau Ceti
or PrimeNumberTheoremAnd. -/
theorem classNumber_eq_jacobi {K : Type} [Field K] [NumberField K]
    (hF : NTKB.Davenport.QuadraticFieldDiscriminants) (hI : NTKB.Davenport.QuadraticIdealCount)
    {q : ℕ} [Fact q.Prime] (hq : q % 4 = 3) (hq3 : 3 < q) (hK : Module.finrank ℚ K = 2)
    (hDq : NumberField.discr K = -q) :
    (q : ℤ) * NumberField.classNumber K = -∑ m ∈ Ico 1 q, (m : ℤ) * legendreSym q m := by
  sorry

/-- **Siegel's lower bound for the class number, `d < 0`** (Chapter 21, (2)), *conditional*: for every `ε > 0`
there is `C(ε) > 0` with `h(d) > C(ε) |d|^{1/2 - ε}` for every imaginary quadratic field of discriminant `d` (`C(ε)`
is not effective). From Siegel's theorem above. Tau Ceti has the upper bound `h(d) ≪ √|d| log |d|`
(`classNumber_le_card_units_mul_sqrt_mul_one_add_log`), not a lower bound; Mathlib and PrimeNumberTheoremAnd have
neither. -/
theorem classNumber_gt_of_discr_neg (hF : NTKB.Davenport.QuadraticFieldDiscriminants)
    (hI : NTKB.Davenport.QuadraticIdealCount) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 →
      NumberField.discr K < 0 →
        C * |(NumberField.discr K : ℝ)| ^ ((1 : ℝ) / 2 - ε) < NumberField.classNumber K := by
  sorry

/-- **Siegel's lower bound, `d > 0`** (Chapter 21, (3)), *conditional*: for every `ε > 0` there is `C(ε) > 0` with
`h(d) log η > C(ε) d^{1/2 - ε}` for every real quadratic field of discriminant `d`, `η` a fundamental unit and
`log η = |log w(η)|` at any infinite place `w`. Not in Mathlib, Tau Ceti or PrimeNumberTheoremAnd. -/
theorem classNumber_mul_log_gt_of_discr_pos (hF : NTKB.Davenport.QuadraticFieldDiscriminants)
    (hI : NTKB.Davenport.QuadraticIdealCount) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 →
      0 < NumberField.discr K →
      ∀ (η : (𝓞 K)ˣ), Subgroup.closure {η} ⊔ NumberField.Units.torsion K = ⊤ →
        ∀ w : NumberField.InfinitePlace K,
          C * (NumberField.discr K : ℝ) ^ ((1 : ℝ) / 2 - ε) <
            NumberField.classNumber K * |Real.log (w (η : K))| := by
  sorry

end ClassNumber

/-- **Vinogradov's asymptotic formula** (Chapter 26, p. 146): for every `A > 0`,
`r(N) = (1/2) G(N) N² + O(N² (log N)^{-A})`, where `r(N) = ∑_{k₁ + k₂ + k₃ = N} Λ(k₁) Λ(k₂) Λ(k₃)` and `G(N)` is the
singular series. Unconditional (major arcs by the Siegel–Walfisz theorem above, minor arcs by Vinogradov's estimate
above). Not in Mathlib, Tau Ceti or PrimeNumberTheoremAnd. -/
theorem vinogradov_three_primes (A : ℝ) (hA : 0 < A) :
    ∃ C > 0, ∀ N : ℕ, 2 ≤ N →
      |NTKB.Davenport.threePrimeRep N - NTKB.Davenport.singularSeries N * N ^ 2 / 2| ≤
        C * N ^ 2 * Real.log N ^ (-A) := by
  sorry

/-- **Every sufficiently large odd integer is a sum of three primes** (Vinogradov; Chapter 26, p. 146).
Unconditional. PrimeNumberTheoremAnd states the odd Goldbach conjecture up to a given height (`odd_conjecture`) and
checks it up to 33, not for all large odd integers; Mathlib and Tau Ceti have neither. -/
theorem exists_three_primes_of_odd :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Odd N →
      ∃ p₁ p₂ p₃ : ℕ, p₁.Prime ∧ p₂.Prime ∧ p₃.Prime ∧ p₁ + p₂ + p₃ = N := by
  sorry

/-! ## New in 0.4.0: class numbers with no assumed input, binary quadratic forms (Chapter 6), the Riemann–von
Mangoldt formula (Chapter 15) and von Mangoldt's explicit formula (Chapter 17)

The five class number statements of 0.3.0 without their two named inputs, which are now theorems of the library (the
ring of integers, discriminant and decomposition law of a quadratic field, proved from Mathlib's `QuadraticAlgebra`). -/

section ClassNumberUnconditional

open scoped NumberField

/-- **The finite class number formula, `d < 0`** (Chapter 6, p. 51), unconditional. For an imaginary quadratic field
of discriminant `d` with `w` roots of unity, `h(d) = -(w/(2|d|)) ∑_{m=1}^{|d|} m (d/m)`. Tau Ceti has
`h(d) = w √|d| L(1, χ)/(2π)` (`classNumber_eq_card_units_mul_LFunction_one`), not the finite formula; Mathlib and
PrimeNumberTheoremAnd have neither. -/
theorem classNumber_eq_sum_of_discr_neg_unconditional {K : Type} [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) (hD : NumberField.discr K < 0) :
    (NumberField.classNumber K : ℂ) =
      -((NumberField.Units.torsionOrder K : ℂ) / (2 * (NumberField.discr K).natAbs)) *
        ∑ m ∈ Icc 1 (NumberField.discr K).natAbs, (m : ℂ) * NTKB.kroneckerChar (NumberField.discr K) m := by
  sorry

/-- **The finite class number formula, `d > 0`** (Chapter 6, p. 51), unconditional: for a real quadratic field of
discriminant `d`, a fundamental unit `ε` and an infinite place `w`,
`h(d) log ε = -(1/2) ∑_{m=1}^{d-1} (d/m) log sin(π m/d)`, with `log ε = |log w(ε)|`. Not in Mathlib, Tau Ceti or
PrimeNumberTheoremAnd. -/
theorem classNumber_mul_log_eq_sum_of_discr_pos_unconditional {K : Type} [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) (hD : 0 < NumberField.discr K) (ε : (𝓞 K)ˣ)
    (hε : Subgroup.closure {ε} ⊔ NumberField.Units.torsion K = ⊤) (w : NumberField.InfinitePlace K) :
    ((NumberField.classNumber K * |Real.log (w (ε : K))| : ℝ) : ℂ) = -(1 / 2) *
      ∑ m ∈ Ico 1 (NumberField.discr K).natAbs,
        NTKB.kroneckerChar (NumberField.discr K) m *
          (Real.log (Real.sin (π * m / NumberField.discr K)) : ℂ) := by
  sorry

/-- **Jacobi's class number formula** (Chapter 6, p. 51, (19)), unconditional: for a prime `q ≡ 3 (mod 4)`, `q > 3`,
the quadratic field of discriminant `-q` has `q h(-q) = -∑_{m=1}^{q-1} m (m/q)`. Not in Mathlib, Tau Ceti or
PrimeNumberTheoremAnd. -/
theorem classNumber_eq_jacobi_unconditional {K : Type} [Field K] [NumberField K]
    {q : ℕ} [Fact q.Prime] (hq : q % 4 = 3) (hq3 : 3 < q) (hK : Module.finrank ℚ K = 2)
    (hDq : NumberField.discr K = -q) :
    (q : ℤ) * NumberField.classNumber K = -∑ m ∈ Ico 1 q, (m : ℤ) * legendreSym q m := by
  sorry

/-- **Siegel's lower bound for the class number, `d < 0`** (Chapter 21, (2)), unconditional: for every `ε > 0` there
is `C(ε) > 0` with `h(d) > C(ε) |d|^{1/2 - ε}` for every imaginary quadratic field of discriminant `d` (`C(ε)` is not
effective). Tau Ceti has the upper bound `h(d) ≪ √|d| log |d|` and ingredients of a lower bound, not a lower bound;
Mathlib and PrimeNumberTheoremAnd have neither. -/
theorem classNumber_gt_of_discr_neg_unconditional {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 →
      NumberField.discr K < 0 →
        C * |(NumberField.discr K : ℝ)| ^ ((1 : ℝ) / 2 - ε) < NumberField.classNumber K := by
  sorry

/-- **Siegel's lower bound, `d > 0`** (Chapter 21, (3)), unconditional: for every `ε > 0` there is `C(ε) > 0` with
`h(d) log η > C(ε) d^{1/2 - ε}` for every real quadratic field of discriminant `d`, `η` a fundamental unit and
`log η = |log w(η)|` at any infinite place `w`. Not in Mathlib, Tau Ceti or PrimeNumberTheoremAnd. -/
theorem classNumber_mul_log_gt_of_discr_pos_unconditional {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 →
      0 < NumberField.discr K →
      ∀ (η : (𝓞 K)ˣ), Subgroup.closure {η} ⊔ NumberField.Units.torsion K = ⊤ →
        ∀ w : NumberField.InfinitePlace K,
          C * (NumberField.discr K : ℝ) ^ ((1 : ℝ) / 2 - ε) <
            NumberField.classNumber K * |Real.log (w (η : K))| := by
  sorry

end ClassNumberUnconditional

/-- **The basic theorem on binary quadratic forms** (Chapter 6, p. 57). Let `d ≠ 1` be a fundamental discriminant
and `S` a complete system of representatives of the proper classes of binary quadratic forms of discriminant `d`
(positive definite if `d < 0`). For every `n ≥ 1`, `∑_{f ∈ S} R_f(n) = ∑_{m ∣ n} (d/m)`, where `R_f(n)` is the number
of representations of `n` by `f` up to automorphs of `f`. No condition `(n, d) = 1` (Davenport has it; the library's
proof goes through ideals of the quadratic field). Tau Ceti has the correspondence between forms and (narrow) ideal
classes (`properClassEquivNarrowPic`, `posDefProperClassEquivPic`), not this count; Mathlib and
PrimeNumberTheoremAnd have neither. -/
theorem basic_theorem_binary_forms {D : ℤ} (hD : NTKB.IsFundamentalDiscriminant D) (h1 : D ≠ 1)
    {S : Finset (ℤ × ℤ × ℤ)} (hS : NTKB.Davenport.IsDavFormSystem D S) {n : ℕ} (hn : 0 < n) :
    ((∑ f ∈ S, NTKB.Davenport.repClassCount f n : ℕ) : ℂ) = ∑ m ∈ n.divisors, NTKB.kroneckerChar D m := by
  sorry

/-- **The total number of representations by the forms of a negative fundamental discriminant** (Chapter 6, p. 57):
for `d < 0` fundamental, `S` a complete system of representatives of the proper classes of positive definite forms
of discriminant `d`, and `n ≥ 1`, the number of solutions of `f(x, y) = n` summed over `f ∈ S` is
`w ∑_{m ∣ n} (d/m)`, with `w = 6, 4, 2` for `d = -3`, `d = -4`, `d < -4`. Not in Mathlib, Tau Ceti or
PrimeNumberTheoremAnd. -/
theorem total_representations_of_discr_neg {D : ℤ} (hD : NTKB.IsFundamentalDiscriminant D) (hneg : D < 0)
    {S : Finset (ℤ × ℤ × ℤ)} (hS : NTKB.Davenport.IsFormSystem D S) {n : ℕ} (hn : 0 < n) :
    ((∑ f ∈ S, Nat.card (NTKB.Davenport.Reps f n) : ℕ) : ℂ) =
      ((if D = -3 then 6 else if D = -4 then 4 else 2 : ℕ) : ℂ) * ∑ m ∈ n.divisors, NTKB.kroneckerChar D m := by
  sorry

/-- **The Riemann–von Mangoldt formula** (Chapter 15, p. 98, (1)): for `T > 0` not the ordinate of a zero of `ζ`,
`N(T) = (T/2π) log(T/2π) - T/2π + 7/8 + S(T) + O(1/T)`, with the explicit error bound `3/T`; `S(T)` is `π⁻¹` times
the argument of `ζ(1/2 + iT)` (see "Definitions used"). PrimeNumberTheoremAnd states a Riemann–von Mangoldt bound
with `sorry` (`riemannZeta.Riemann_vonMangoldt_bound`) and proves `N(T) ≤ A T^{3/2}`; Mathlib and Tau Ceti have
neither. -/
theorem riemann_von_mangoldt {T : ℝ} (hT : 0 < T) (hTz : ∀ ρ : NTKB.ZeroIndex NTKB.riemannXi, |ρ.val.im| ≠ T) :
    |(NTKB.zetaZeroCount T : ℝ) -
      (T / (2 * π) * Real.log (T / (2 * π)) - T / (2 * π) + 7 / 8 + NTKB.zetaArgS T)| ≤ 3 / T := by
  sorry

/-- **Von Mangoldt's explicit formula** (Chapter 17, p. 104, (1)), for every real `x ≥ 2`:
`ψ₀(x) = x - ∑_ρ x^ρ/ρ - log 2π - (1/2) log(1 - x⁻²)`, the sum over the nontrivial zeros `ρ` of `ζ` (with
multiplicity) taken symmetrically, `|γ| < T`, `T → ∞`. (Davenport states it for `x > 1`: that is the headline `explicit_formula_vonMangoldt_of_one_lt`,
new in 0.4.1.)
PrimeNumberTheoremAnd has smoothed explicit formulas that depend on statements with `sorry`; Mathlib and Tau Ceti have
none. -/
theorem explicit_formula_vonMangoldt {x : ℝ} (hx : 2 ≤ x) :
    Filter.Tendsto (fun T : ℝ ↦ ∑ ρ ∈ NTKB.zerosBelow T, (x : ℂ) ^ ρ.val / ρ.val) Filter.atTop
      (nhds ((x : ℂ) - NTKB.psi0R x - Real.log (2 * π) -
        ((1 / 2 * Real.log (1 - x ^ (-2 : ℝ)) : ℝ) : ℂ))) := by
  sorry

/-! ## New in 0.4.1: von Mangoldt's explicit formula for every real `x > 1` (Chapter 17) -/

/-- **Von Mangoldt's explicit formula** (Chapter 17, p. 104, (1)), for every real `x > 1`, as Davenport states it:
`ψ₀(x) = x - ∑_ρ x^ρ/ρ - log 2π - (1/2) log(1 - x⁻²)`, the sum over the nontrivial zeros `ρ` of `ζ` (with
multiplicity) taken symmetrically, `|γ| < T`, `T → ∞`. The headline `explicit_formula_vonMangoldt` of 0.4.0 is the
case `x ≥ 2`; for `1 < x < 2` (where `ψ₀(x) = 0`) the library repeats its proof with the constants depending on `x`
(`log 2` replaced by `log x` or `log(2/x)`). PrimeNumberTheoremAnd has smoothed explicit formulas that depend on statements with `sorry`; Mathlib
and Tau Ceti have none. -/
theorem explicit_formula_vonMangoldt_of_one_lt {x : ℝ} (hx : 1 < x) :
    Filter.Tendsto (fun T : ℝ ↦ ∑ ρ ∈ NTKB.zerosBelow T, (x : ℂ) ^ ρ.val / ρ.val) Filter.atTop
      (nhds ((x : ℂ) - NTKB.psi0R x - Real.log (2 * π) -
        ((1 / 2 * Real.log (1 - x ^ (-2 : ℝ)) : ℝ) : ℂ))) := by
  sorry

/-! ## New in 0.5.0: explicit formulas (Chapters 8 and 19), the exceptional zero (Chapters 14 and 20), Hecke's class
number bound (Chapter 21) and Montgomery's large sieve (Chapter 27)

The Brun–Titchmarsh inequality, which the library proves from Montgomery's large sieve
(`NTKB.Davenport.brun_titchmarsh`, `NTKB.Davenport.brun_titchmarsh_asymptotic`), is not a headline:
PrimeNumberTheoremAnd proves it by the Selberg sieve (`BrunTitchmarsh.primesBetween_le`). -/

/-- **Von Mangoldt's formula in Riemann's form** (Chapter 8, p. 60, (d')): for real `x > 1` not a prime power,
`ψ(x) - x = -∑_ρ x^ρ/ρ - ζ'(0)/ζ(0) - (1/2) log(1 - x⁻²)`, with `ψ(x) = ∑_{n ≤ x} Λ(n)` (Mathlib's `Chebyshev.psi`)
and the sum over the nontrivial zeros `ρ` of `ζ` (with multiplicity) taken symmetrically, `|γ| < T`, `T → ∞`. The
library proves Riemann's product for `ξ` (Chapter 8, (c'), from Hadamard's factorization of Chapter 12) and deduces
the formula from Chapter 17's (the headline `explicit_formula_vonMangoldt_of_one_lt`, where the constant appears as
`log 2π`). Neither Mathlib nor Tau Ceti has an explicit formula over the zeros of `ζ`. -/
theorem explicit_formula_memoir {x : ℝ} (hx : 1 < x) (hpp : ∀ n : ℕ, IsPrimePow n → (n : ℝ) ≠ x) :
    Filter.Tendsto (fun T : ℝ ↦ -∑ ρ ∈ NTKB.zerosBelow T, (x : ℂ) ^ ρ.val / ρ.val -
        deriv riemannZeta 0 / riemannZeta 0 - ((1 / 2 * Real.log (1 - x ^ (-2 : ℝ)) : ℝ) : ℂ))
      Filter.atTop (nhds ((Chebyshev.psi x - x : ℝ) : ℂ)) := by
  sorry

/-- **The truncated explicit formula for `ψ(x, χ)`** (Chapter 19, p. 117, (G)): there is an absolute `A` such that
for every primitive character `χ` modulo `q > 1`, real `x ≥ 2` and `2 ≤ T ≤ x`,
`|ψ(x, χ) + ∑_{|γ| < T} x^ρ/ρ + b(χ)| ≤ A x log²(qx)/T`, with `ψ(x, χ) = ∑_{n ≤ x} χ(n) Λ(n)`, the sum over the zeros
`ρ = β + iγ` of `ξ(s, χ)` with multiplicity, and `b(χ)` the constant term of `L'/L(s, χ)` at `s = 0`. Neither
Mathlib nor Tau Ceti has an explicit formula over the zeros of `L(s, χ)`. -/
theorem explicit_formula_psiL :
    ∃ A : ℝ, 0 < A ∧ ∀ {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
      (hq : q ≠ 1), ∀ x : ℝ, 2 ≤ x → ∀ T : ℝ, 2 ≤ T → T ≤ x →
      ‖NTKB.psiL χ x - (-∑ ρ ∈ NTKB.zerosBelowL hχ hq T, (x : ℂ) ^ ρ.val / ρ.val - NTKB.bChar χ)‖ ≤
        A * x * Real.log (q * x) ^ 2 / T := by
  sorry

/-- **The effective bound for a real zero** (Chapter 14, p. 96, (18)): there is an absolute `c > 0` such that for
every real character `χ ≠ 1` modulo `q` and every real zero `β` of `L(s, χ)`, `β < 1 - c/(q^{1/2} log² q)`, and
`β < 1 - c/(q^{1/2} log q)` if `χ` is even. Tau Ceti has the sign of `L(σ, χ)` up to its first real zero, not this
bound; Mathlib has neither. -/
theorem real_zero_lt :
    ∃ c : ℝ, 0 < c ∧ ∀ {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q},
      χ.IsQuadratic → χ ≠ 1 → ∀ β : ℝ, χ.LFunction β = 0 →
        β < 1 - c / (√(q : ℝ) * Real.log q ^ 2) ∧
          (χ.Even → β < 1 - c / (√(q : ℝ) * Real.log q)) := by
  sorry

/-- **The prime number theorem for arithmetic progressions with the exceptional zero** (Chapter 20, p. 123, (9)):
for every `C > 0` there are `c, A > 0` such that for every modulus `q`, every `a` prime to `q` and every real `x ≥ 3`
with `log q ≤ C (log x)^{1/2}`: if no character modulo `q` has an exceptional zero, then
`|ψ(x; q, a) - x/φ(q)| ≤ A x exp(-c (log x)^{1/2})`; and if `β₁` is an exceptional zero of `L(s, χ₁)`, then
`|ψ(x; q, a) - x/φ(q) + χ₁(a) x^{β₁}/(φ(q) β₁)| ≤ A x exp(-c (log x)^{1/2})`. An exceptional zero (`NTKB.IsExceptional`)
is a real zero `β > 1 - c₀/log q` of `L(s, χ)` for a real character `χ ≠ 1`, `c₀ = 1/16200` the constant of the
zero-free region; there is at most one. Neither Mathlib nor Tau Ceti has a prime number theorem for arithmetic
progressions with an error term. -/
theorem psiAP_exceptional (C : ℝ) (hC : 0 < C) :
    ∃ c A : ℝ, 0 < c ∧ 0 < A ∧ ∀ {q : ℕ} [NeZero q] {a : ZMod q}, IsUnit a →
      ∀ x : ℝ, 3 ≤ x → Real.log q ≤ C * √(Real.log x) →
      ((∀ (χ : DirichletCharacter ℂ q) (β : ℝ), ¬ NTKB.IsExceptional χ β) →
        |NTKB.psiAP a x - x / q.totient| ≤ A * x * Real.exp (-(c * √(Real.log x)))) ∧
      (∀ (χ₁ : DirichletCharacter ℂ q) (β₁ : ℝ), NTKB.IsExceptional χ₁ β₁ →
        ‖(NTKB.psiAP a x : ℂ) - x / q.totient + χ₁ a * (x : ℂ) ^ (β₁ : ℂ) / (q.totient * β₁)‖ ≤
          A * x * Real.exp (-(c * √(Real.log x)))) := by
  sorry

/-- **Hecke's class number bound, `d < 0`** (Chapter 21, p. 127): for every `c₂ > 0` there is `C > 0` such that for
every imaginary quadratic field of discriminant `d` whose Kronecker character `χ_d` has no real zero `σ` with
`1 - c₂/log |d| < σ < 1`, `h(d) > C |d|^{1/2}/log |d|`. The hypothesis is the zero-free interval of the theorem, not
known in general (it is not a named input). Davenport cites the result without proof; the library proves it by
Estermann's inequality for `ζ(s) L(s, χ_d)`. Neither Mathlib nor Tau Ceti has it. -/
theorem classNumber_gt_of_no_real_zero {c₂ : ℝ} (hc₂ : 0 < c₂) :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 →
      NumberField.discr K < 0 →
      (∀ σ : ℝ, 1 - c₂ / Real.log |(NumberField.discr K : ℝ)| < σ → σ < 1 →
        (NTKB.kroneckerChar (NumberField.discr K)).LFunction σ ≠ 0) →
      C * √|(NumberField.discr K : ℝ)| / Real.log |(NumberField.discr K : ℝ)| < NumberField.classNumber K := by
  sorry

/-- **Hecke's class number bound, `d > 0`** (Chapter 21, p. 127): under the same hypothesis on `χ_d`,
`h(d) R > C d^{1/2}/log d` for every real quadratic field of discriminant `d`, `R` its regulator (Mathlib's
`NumberField.Units.regulator`). Neither Mathlib nor Tau Ceti has it. -/
theorem classNumber_mul_regulator_gt_of_no_real_zero {c₂ : ℝ} (hc₂ : 0 < c₂) :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 →
      0 < NumberField.discr K →
      (∀ σ : ℝ, 1 - c₂ / Real.log (NumberField.discr K : ℝ) < σ → σ < 1 →
        (NTKB.kroneckerChar (NumberField.discr K)).LFunction σ ≠ 0) →
      C * √(NumberField.discr K : ℝ) / Real.log (NumberField.discr K : ℝ) <
        NumberField.classNumber K * NumberField.Units.regulator K := by
  sorry

/-- **Montgomery's large sieve** (Chapter 27, p. 159): for a set `Z` of integers in `(M, M + N]` and real `Q ≥ 1`,
`|Z| ≤ (N + 3Q²)/L` with `L = ∑_{q ≤ Q} μ(q)² ∏_{p ∣ q} ω(p)/(p - ω(p))`, `ω(p)` the number of residue classes modulo
`p` that contain no element of `Z` (`NTKB.Davenport.montgomeryL`, `NTKB.Davenport.sieveOmega`). Davenport states it
without proof; the library proves it by Montgomery's argument from the large sieve inequality. Tau Ceti has
ingredients of the Selberg sieve, not this inequality; Mathlib has neither. -/
theorem card_le_montgomery {Q : ℝ} (hQ : 1 ≤ Q) (M : ℤ) (N : ℕ) (Z : Finset ℤ) (hZ : Z ⊆ Ioc M (M + N)) :
    (Z.card : ℝ) ≤ (N + 3 * Q ^ 2) / NTKB.Davenport.montgomeryL Z Q := by
  sorry

end NTKB.Headlines.Davenport
