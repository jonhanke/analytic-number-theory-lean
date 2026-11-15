/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Elementary.SpecialValues.KroneckerSymbol
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.LSeries.DirichletContinuation

/-!
# Davenport, Chapter 5: the Euler product of `L(s, (d/·))`

Davenport, *Multiplicative Number Theory*, §5, p. 42. For a fundamental discriminant `d` and
`Re s > 1`, `L(s, χ) = ∏_p (1 - (d/p) p^{-s})^{-1} = ∑_n (d/n) n^{-s}`, `χ = (d/·)` the Kronecker
symbol (`NTKB.kroneckerChar d`; at odd `n` it is the Jacobi symbol, `kroneckerChar_apply_odd`).
An instance of Mathlib's Euler product for Dirichlet `L`-series.
-/

noncomputable section

open Complex DirichletCharacter Nat
open scoped LSeries.notation

namespace NTKB.Davenport

/-- **Davenport §5, p. 42.** For a fundamental discriminant `d` and `Re s > 1`, the `L`-function
of the Kronecker symbol `(d/·)` is the Euler product `∏_p (1 - (d/p) p^{-s})^{-1}` and the
Dirichlet series `∑_n (d/n) n^{-s}`. -/
@[kb "davenport1980" "Ch 5, p. 42"]
theorem LFunction_kroneckerChar_eulerProduct {D : ℤ} [NeZero D.natAbs] {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun p : Primes ↦ (1 - kroneckerChar D p * (p : ℂ) ^ (-s))⁻¹)
        (LFunction (kroneckerChar D) s) ∧
      LSeriesHasSum (fun n ↦ kroneckerChar D n) s (LFunction (kroneckerChar D) s) := by
  rw [LFunction_eq_LSeries _ hs]
  exact ⟨LSeries_eulerProduct_hasProd _ hs,
    (ZMod.LSeriesSummable_of_one_lt_re (kroneckerChar D) hs).LSeriesHasSum⟩

end NTKB.Davenport
