/-
Copyright (c) 2026 The Tau Ceti contributors. Released under Apache 2.0 license.
Copied into NTKB with credit from Tau Ceti (`TauCeti/NumberTheory/DirichletCharacter/PartialSum.lean`,
master `686d0d7f`, staged 2026-11-07); NTKB does not depend on Tau Ceti. Changes: namespace
`NTKB.DirichletCharacter`, a direct bijection `range N ≃ ZMod N` in place of Tau Ceti's `ZMod.finEquiv`, `Ioc 0 n` form added.
-/
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.Data.Nat.Periodic

/-!
# Partial sums of nonprincipal Dirichlet characters (port from Tau Ceti)

The sum of a nonprincipal character over a full period vanishes, so its partial sums depend only
on the endpoint modulo the level, and their norms are bounded by the level (Apostol, proof of
Theorem 6.17: `A(x) = O(1)`).
-/

open Finset

namespace NTKB.DirichletCharacter

variable {N : ℕ} [NeZero N]

/-- The sum of a nonprincipal character over a full period vanishes. -/
theorem sum_range_level_eq_zero {R : Type*} [CommRing R] [IsDomain R]
    (χ : DirichletCharacter R N) (hχ : χ ≠ 1) : ∑ k ∈ range N, χ k = 0 := by
  rw [← MulChar.sum_eq_zero_of_ne_one hχ]
  refine sum_nbij (fun k : ℕ ↦ (k : ZMod N)) (fun _ _ ↦ mem_univ _) ?_ ?_ (fun _ _ ↦ rfl)
  · intro a ha b hb hab
    simp only [coe_range, Set.mem_Iio] at ha hb
    have := (ZMod.natCast_eq_natCast_iff' a b N).1 hab
    rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this
  · intro a _
    exact ⟨a.val, by simpa using ZMod.val_lt a, ZMod.natCast_zmod_val a⟩

/-- The partial sum of a nonprincipal character depends only on the endpoint modulo its level. -/
theorem sum_range_eq_sum_range_mod {R : Type*} [CommRing R] [IsDomain R]
    (χ : DirichletCharacter R N) (hχ : χ ≠ 1) (n : ℕ) :
    ∑ k ∈ range n, χ k = ∑ k ∈ range (n % N), χ k := by
  have hperiod : Function.Periodic (fun n : ℕ ↦ ∑ k ∈ range n, χ k) N := by
    intro n
    dsimp only
    rw [add_comm n N, sum_range_add, sum_range_level_eq_zero χ hχ, zero_add]
    simp
  exact (hperiod.map_mod_nat n).symm

/-- Partial sums of a nonprincipal character valued in a normed field are bounded by its level. -/
theorem norm_sum_Icc_le_level {F : Type*} [NormedField F]
    (χ : DirichletCharacter F N) (hχ : χ ≠ 1) (n : ℕ) :
    ‖∑ k ∈ Icc 1 n, χ k‖ ≤ (N : ℝ) := by
  have hsum : ∑ k ∈ Icc 1 n, χ k = ∑ k ∈ range (n + 1), χ k := by
    rw [Nat.range_succ_eq_Icc_zero, ← insert_Icc_add_one_left_eq_Icc n.zero_le]
    simp [χ.map_zero' (by rintro rfl; exact hχ (Subsingleton.elim _ _))]
  rw [hsum, sum_range_eq_sum_range_mod χ hχ]
  calc
    _ ≤ ∑ k ∈ range ((n + 1) % N), (1 : ℝ) :=
      (norm_sum_le _ _).trans (sum_le_sum fun k _ ↦ χ.norm_le_one k)
    _ ≤ (N : ℝ) := by simpa using (Nat.cast_le.mpr (Nat.mod_lt (n + 1) (NeZero.pos N)).le :
      (((n + 1) % N : ℕ) : ℝ) ≤ N)

/-- The same bound for sums over `Ioc 0 n` (NTKB addition). -/
theorem norm_sum_Ioc_le_level {F : Type*} [NormedField F]
    (χ : DirichletCharacter F N) (hχ : χ ≠ 1) (n : ℕ) :
    ‖∑ k ∈ Ioc 0 n, χ k‖ ≤ (N : ℝ) := by
  have : Ioc 0 n = Icc 1 n := by ext m; simp [Nat.one_le_iff_ne_zero, Nat.pos_iff_ne_zero]
  rw [this]
  exact norm_sum_Icc_le_level χ hχ n

end NTKB.DirichletCharacter
