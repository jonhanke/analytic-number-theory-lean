/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Group
import NTKB.Attr

/-!
# Extending a subgroup by one element (Apostol, Chapter 6, §6.4, Theorem 6.6)

Let `G'` be a subgroup of a finite abelian group `G` and `a ∉ G'`, and let the *indicator* `h` of
`a` in `G'` be the least positive `n` with `aⁿ ∈ G'`. **Theorem 6.6:** the set
`G'' = {x a^k : x ∈ G', 0 ≤ k < h}` is a subgroup of `G` containing `G'`, and `|G''| = h |G'|`.

(Apostol uses it to build characters inductively, Theorem 6.8; Mathlib counts characters by the
structure theorem instead.) The proof follows Apostol: closure via `k + j = qh + r`, inverses via
`x⁻¹ a^{-k} = (x⁻¹ a^{-h}) a^{h-k}`, and distinctness of the products `x a^k` by minimality of `h`.
-/

namespace NTKB.Apostol

variable {G : Type*} [CommGroup G] [Finite G]

/-- The indicator of `a` in `H` exists: some positive power of `a` lies in `H`. -/
theorem exists_pos_pow_mem (H : Subgroup G) (a : G) : ∃ n, 0 < n ∧ a ^ n ∈ H :=
  ⟨orderOf a, orderOf_pos a, by rw [pow_orderOf_eq_one]; exact H.one_mem⟩

open Classical in
/-- The indicator of `a` in `H`: the least `n > 0` with `aⁿ ∈ H` (Apostol, §6.4). -/
noncomputable def indicator (H : Subgroup G) (a : G) : ℕ := Nat.find (exists_pos_pow_mem H a)

theorem indicator_spec (H : Subgroup G) (a : G) :
    0 < indicator H a ∧ a ^ indicator H a ∈ H := by
  classical
  exact Nat.find_spec (exists_pos_pow_mem H a)

theorem indicator_min (H : Subgroup G) (a : G) {m : ℕ} (hm : 0 < m) (hmH : a ^ m ∈ H) :
    indicator H a ≤ m := by
  classical
  exact Nat.find_min' (exists_pos_pow_mem H a) ⟨hm, hmH⟩

/-- The subgroup `G'' = {x a^k : x ∈ G', 0 ≤ k < h}` of Theorem 6.6. -/
def extendSubgroup (H : Subgroup G) (a : G) : Subgroup G where
  carrier := {g | ∃ x ∈ H, ∃ k < indicator H a, g = x * a ^ k}
  mul_mem' := by
    rintro _ _ ⟨x, hx, k, hk, rfl⟩ ⟨y, hy, j, hj, rfl⟩
    set h := indicator H a
    have hh := indicator_spec H a
    refine ⟨x * y * (a ^ h) ^ ((k + j) / h), H.mul_mem (H.mul_mem hx hy) (H.pow_mem hh.2 _),
      (k + j) % h, Nat.mod_lt _ hh.1, ?_⟩
    have : a ^ k * a ^ j = (a ^ h) ^ ((k + j) / h) * a ^ ((k + j) % h) := by
      rw [← pow_add, ← pow_mul, ← pow_add, Nat.div_add_mod]
    calc x * a ^ k * (y * a ^ j) = x * y * (a ^ k * a ^ j) := by rw [mul_mul_mul_comm]
      _ = x * y * (a ^ h) ^ ((k + j) / h) * a ^ ((k + j) % h) := by
          rw [this]; simp only [mul_assoc]
  one_mem' := ⟨1, H.one_mem, 0, (indicator_spec H a).1, by simp⟩
  inv_mem' := by
    rintro _ ⟨x, hx, k, hk, rfl⟩
    set h := indicator H a
    have hh := indicator_spec H a
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · exact ⟨x⁻¹, H.inv_mem hx, 0, hh.1, by simp⟩
    · refine ⟨x⁻¹ * (a ^ h)⁻¹, H.mul_mem (H.inv_mem hx) (H.inv_mem hh.2), h - k, by omega, ?_⟩
      have e : a ^ h = a ^ (h - k) * a ^ k := by rw [← pow_add, Nat.sub_add_cancel hk.le]
      have : (a ^ k)⁻¹ = (a ^ h)⁻¹ * a ^ (h - k) := by rw [e]; group
      rw [mul_inv, this, mul_assoc]

/-- **Apostol, Theorem 6.6.** `G''` contains `G'`, and `|G''| = h |G'|` where `h` is the
indicator of `a` in `G'`. -/
@[kb "apostol1976" "Thm 6.6, p. 132"]
theorem le_extendSubgroup_and_card (H : Subgroup G) (a : G) :
    H ≤ extendSubgroup H a ∧ Nat.card (extendSubgroup H a) = indicator H a * Nat.card H := by
  have hh := indicator_spec H a
  refine ⟨fun x hx ↦ ⟨x, hx, 0, hh.1, by simp⟩, ?_⟩
  -- the products `x a^k`, `x ∈ H`, `k < h`, are distinct and exhaust `G''`
  let f : Fin (indicator H a) × H → extendSubgroup H a := fun p ↦
    ⟨(p.2 : G) * a ^ (p.1 : ℕ), p.2, p.2.2, p.1, p.1.2, rfl⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨k, x⟩ ⟨j, y⟩ hkj
      have hkj' : (x : G) * a ^ (k : ℕ) = y * a ^ (j : ℕ) := congrArg Subtype.val hkj
      -- `a^{k-j} ∈ H` forces `k = j`
      have key : ∀ (x y : H) (k j : ℕ), j ≤ k → k < indicator H a →
          (x : G) * a ^ k = y * a ^ j → k = j := by
        intro x y k j hjk hk hxy
        by_contra hne
        have hpos : 0 < k - j := by omega
        have hmem : a ^ (k - j) ∈ H := by
          have : a ^ (k - j) = (x : G)⁻¹ * y := by
            have e : a ^ k = a ^ (k - j) * a ^ j := by rw [← pow_add, Nat.sub_add_cancel hjk]
            rw [e] at hxy
            rw [eq_inv_mul_iff_mul_eq]
            calc (x : G) * a ^ (k - j) = x * (a ^ (k - j) * a ^ j) * (a ^ j)⁻¹ := by group
              _ = y * a ^ j * (a ^ j)⁻¹ := by rw [hxy]
              _ = y := by group
          rw [this]; exact H.mul_mem (H.inv_mem x.2) y.2
        have := indicator_min H a hpos hmem
        omega
      have hk : (k : ℕ) = j := by
        rcases le_total (j : ℕ) k with h1 | h1
        · exact key x y k j h1 k.2 hkj'
        · exact (key y x j k h1 j.2 hkj'.symm).symm
      have hk' : k = j := Fin.ext hk
      subst hk'
      have : (x : G) = y := mul_right_cancel hkj'
      rw [Subtype.ext this]
    · rintro ⟨g, x, hx, k, hk, rfl⟩
      exact ⟨(⟨k, hk⟩, ⟨x, hx⟩), rfl⟩
  rw [← Nat.card_eq_of_bijective f hf, Nat.card_prod, Nat.card_eq_fintype_card, Fintype.card_fin]

end NTKB.Apostol
