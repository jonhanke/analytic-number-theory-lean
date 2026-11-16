/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.Data.Int.Interval
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic

/-!
# Solutions of `t² - d u² = 4` for `d < 0` (Davenport, Chapter 6, row 6-3)

For `d < 0`, `d ≡ 0, 1 (mod 4)`, the equation `t² - d u² = 4` has `6` solutions if `d = -3`,
`4` if `d = -4` and `2` otherwise.
-/

namespace NTKB.Davenport

theorem card_eq_of_mem_iff {P : ℤ × ℤ → Prop} (S : Finset (ℤ × ℤ)) (hS : ∀ p, p ∈ S ↔ P p) :
    Nat.card {p // P p} = S.card := by
  rw [← Nat.card_eq_finsetCard]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun p ↦ (hS p).symm)

theorem bounds_of_sol {D t u : ℤ} (hD : D < 0) (h : t ^ 2 - D * u ^ 2 = 4) :
    -2 ≤ t ∧ t ≤ 2 ∧ -D * u ^ 2 ≤ 4 := by
  have ht : t ^ 2 ≤ 2 ^ 2 := by nlinarith [sq_nonneg u]
  obtain ⟨h1, h2⟩ := abs_le.mp (abs_le_of_sq_le_sq ht (by norm_num))
  exact ⟨h1, h2, by nlinarith [sq_nonneg t]⟩

theorem u_bounds {D u : ℤ} (hD : D < 0) (h : -D * u ^ 2 ≤ 4) (hD3 : D ≤ -3) : -1 ≤ u ∧ u ≤ 1 := by
  have : u ^ 2 ≤ 1 := by nlinarith [sq_nonneg u]
  exact abs_le.mp (sq_le_one_iff_abs_le_one u |>.mp this)

theorem card_sol_four_of_neg {D : ℤ} (hD : D < 0) (h4 : D % 4 = 0 ∨ D % 4 = 1) :
    Nat.card {p : ℤ × ℤ // p.1 ^ 2 - D * p.2 ^ 2 = 4} =
      if D = -3 then 6 else if D = -4 then 4 else 2 := by
  have hD3 : D ≤ -3 := by omega
  by_cases h3 : D = -3
  · subst h3
    rw [if_pos rfl, card_eq_of_mem_iff {(2, 0), (-2, 0), (1, 1), (1, -1), (-1, 1), (-1, -1)}]
    · rfl
    rintro ⟨t, u⟩
    simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
    constructor
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> norm_num
    · intro h
      obtain ⟨ht1, ht2, hu⟩ := bounds_of_sol (by norm_num) h
      obtain ⟨hu1, hu2⟩ := u_bounds (by norm_num) hu le_rfl
      interval_cases t <;> interval_cases u <;> simp_all
  by_cases h4' : D = -4
  · subst h4'
    rw [if_neg (by norm_num), if_pos rfl, card_eq_of_mem_iff {(2, 0), (-2, 0), (0, 1), (0, -1)}]
    · rfl
    rintro ⟨t, u⟩
    simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
    constructor
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> norm_num
    · intro h
      obtain ⟨ht1, ht2, hu⟩ := bounds_of_sol (by norm_num) h
      obtain ⟨hu1, hu2⟩ := u_bounds (by norm_num) hu (by norm_num)
      interval_cases t <;> interval_cases u <;> simp_all
  · rw [if_neg h3, if_neg h4', card_eq_of_mem_iff {(2, 0), (-2, 0)}]
    · rfl
    have hD5 : D ≤ -5 := by omega
    rintro ⟨t, u⟩
    simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
    constructor
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> norm_num
    · intro h
      obtain ⟨ht1, ht2, hu⟩ := bounds_of_sol hD h
      have hu0 : u = 0 := by
        have : u ^ 2 < 1 := by nlinarith [sq_nonneg u]
        have : u ^ 2 = 0 := by nlinarith [sq_nonneg u]
        exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
      subst hu0
      interval_cases t <;> simp_all

end NTKB.Davenport
