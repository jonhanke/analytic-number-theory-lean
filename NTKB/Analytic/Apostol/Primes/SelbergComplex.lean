/- Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license. -/
import NTKB.Analytic.Apostol.Primes.Selberg

/-!
# Theorem 4.17 for complex-valued `F` (Apostol, Chapter 4, §4.11)

Apostol states the Tatuzawa–Iseki identity for complex-valued `F` on `(0, ∞)`;
`NTKB.Apostol.tatuzawa_iseki` is the real case. The complex case follows by applying it to the
real and imaginary parts (`tatuzawa_iseki_complex`).
-/

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius

namespace NTKB.Apostol

/-- **Apostol, Theorem 4.17** (complex-valued `F`): for `F : ℝ → ℂ` and
`G(x) = log x ∑_{n ≤ x} F(x/n)`, for `x ≥ 1`,
`F(x) log x + ∑_{n ≤ x} F(x/n) Λ(n) = ∑_{d ≤ x} μ(d) G(x/d)`. -/
@[kb "apostol1976" "Thm 4.17, p. 99"]
theorem tatuzawa_iseki_complex (F : ℝ → ℂ) {x : ℝ} (hx : 1 ≤ x) :
    F x * Real.log x + ∑ n ∈ Ioc 0 ⌊x⌋₊, F (x / n) * Λ n =
      ∑ d ∈ Ioc 0 ⌊x⌋₊, (μ d : ℂ) *
        (Real.log (x / d) * ∑ q ∈ Ioc 0 ⌊x / d⌋₊, F (x / d / q)) := by
  have h1 := tatuzawa_iseki (fun y => (F y).re) hx
  have h2 := tatuzawa_iseki (fun y => (F y).im) hx
  apply Complex.ext
  · simpa [Complex.re_sum, Complex.mul_re] using h1
  · simpa [Complex.im_sum, Complex.mul_im] using h2

end NTKB.Apostol
