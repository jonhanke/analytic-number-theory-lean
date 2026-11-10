/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import NTKB.Analytic.Apostol.GaussSums.Polya
import NTKB.Analytic.Apostol.Partitions.UpperBound
import NTKB.Analytic.Apostol.DirichletSeries.MeanValues

/-!
# Headline statements of analytic-number-theory-lean 0.1.0: Apostol

T. M. Apostol, *Introduction to Analytic Number Theory* (Springer, 1976). The main results of the library for this
book that Mathlib, Tau Ceti and PrimeNumberTheoremAnd do not have, one theorem each, with every proof a deliberate
`sorry`: to check what is claimed, read this file. `Solution_Apostol.lean` proves the same statements from the
library, and `lake comparator` (configured by `comparator/Apostol.json`) checks that each proved statement is exactly
the one here and uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`.

Most of Apostol's book is in Mathlib (the book map says which results); the library proves the rest, and only
three results of the book are in none of the three libraries above and not already a headline of
elementary-number-theory-lean. Each statement is the library's statement, copied. The statements were not yet
reviewed by a human (see the README).

## Definitions used

Only Mathlib's: `DirichletCharacter`, `Nat.Partition`, `LSeries`, `LSeries.term`, `LSeriesSummable`.
-/

namespace NTKB.Headlines.Apostol

open Complex Filter Topology Finset
open scoped Real

/-- **Pólya's inequality** (Theorem 8.21): for a primitive character `χ` modulo `N > 1` and every real `x`,
`|∑_{1 ≤ m ≤ x} χ(m)| < √N log N`. Tau Ceti bounds such sums by the modulus
(`DirichletCharacter.norm_sum_Icc_le_level`); none of Mathlib, Tau Ceti and PrimeNumberTheoremAnd has the
`√N log N` bound. -/
theorem polya {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (hN : 1 < N) (x : ℝ) :
    ‖∑ m ∈ Icc 1 ⌊x⌋₊, χ m‖ < √N * Real.log N := by
  sorry

/-- **An upper bound for the partition function** (Theorem 14.5): `p(n) < e^{K√n}` for `n ≥ 1`, with
`K = π √(2/3)`. No library of the three has a bound on the number of partitions. -/
theorem card_partition_lt_exp {n : ℕ} (hn : 1 ≤ n) :
    (Fintype.card n.Partition : ℝ) < Real.exp (π * √(2 / 3) * √n) := by
  sorry

/-- **The mean square of a Dirichlet series** (Theorem 11.16): if `∑ f(n) n^{-σ}` converges absolutely, then
`(1/2T) ∫_{-T}^{T} |F(σ + it)|² dt → ∑_n |f(n)|² n^{-2σ}` as `T → ∞`, where `F = LSeries f`. Not in Mathlib, Tau
Ceti or PrimeNumberTheoremAnd. -/
theorem mean_square_LSeries {f : ℕ → ℂ} {σ : ℝ} (hf : LSeriesSummable f σ) :
    Tendsto (fun T : ℝ => 1 / (2 * T) * ∫ t in (-T)..T, ‖LSeries f (σ + t * I)‖ ^ 2)
      atTop (𝓝 (∑' n : ℕ, ‖LSeries.term f σ n‖ ^ 2)) := by
  sorry

end NTKB.Headlines.Apostol
