/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import NTKB.Analytic.Apostol.GaussSums.Polya
import NTKB.Analytic.Apostol.Partitions.UpperBound
import NTKB.Analytic.Apostol.DirichletSeries.MeanValues

/-!
# Proofs of the Apostol headline statements

The statements of `Challenge_Apostol.lean`, proved by the library theorems. `lake comparator` checks that each
statement here is exactly the one in `Challenge_Apostol.lean`.
-/

namespace NTKB.Headlines.Apostol

open Complex Filter Topology Finset
open scoped Real

theorem polya {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (hN : 1 < N) (x : ℝ) :
    ‖∑ m ∈ Icc 1 ⌊x⌋₊, χ m‖ < √N * Real.log N :=
  NTKB.Apostol.polya hχ hN x

theorem card_partition_lt_exp {n : ℕ} (hn : 1 ≤ n) :
    (Fintype.card n.Partition : ℝ) < Real.exp (π * √(2 / 3) * √n) :=
  NTKB.Apostol.card_partition_lt_exp hn

theorem mean_square_LSeries {f : ℕ → ℂ} {σ : ℝ} (hf : LSeriesSummable f σ) :
    Tendsto (fun T : ℝ => 1 / (2 * T) * ∫ t in (-T)..T, ‖LSeries f (σ + t * I)‖ ^ 2)
      atTop (𝓝 (∑' n : ℕ, ‖LSeries.term f σ n‖ ^ 2)) :=
  NTKB.Apostol.apostol_thm_11_16 hf

end NTKB.Headlines.Apostol
