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

end NTKB.Headlines.Davenport
