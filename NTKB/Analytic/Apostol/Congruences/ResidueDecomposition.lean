/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Apostol.Congruences.ReducedResidues

/-!
# Decomposition of a reduced residue system (Apostol, Chapter 5, Theorem 5.33 (a))

**Theorem 5.33 (a).** For `d ∣ k`, a reduced residue system mod `k` (here: `(ZMod k)ˣ`) is the
union of `φ(k)/φ(d)` disjoint sets, each of which is a reduced residue system mod `d` (each maps
bijectively onto `(ZMod d)ˣ` under reduction mod `d`).

Apostol derives (a) from (b) (`card_fiber_unitsMap`) by arranging the `φ(k)` elements in a
`φ(k)/φ(d) × φ(d)` matrix whose columns are the classes mod `d`; the rows are the required sets.
-/

open Finset

namespace NTKB.Apostol

variable {d k : ℕ}

/-- **Apostol, Theorem 5.33 (a).** -/
@[kb "apostol1976" "Thm 5.33, p. 125"]
theorem exists_partition_units [NeZero k] (hdk : d ∣ k) :
    ∃ A : Fin (k.totient / d.totient) → Finset (ZMod k)ˣ,
      (∀ i j, i ≠ j → Disjoint (A i) (A j)) ∧ (∀ v, ∃ j, v ∈ A j) ∧
        ∀ j, Set.BijOn (ZMod.unitsMap hdk) (A j : Set (ZMod k)ˣ) Set.univ := by
  classical
  have : NeZero d := ⟨fun h ↦ NeZero.ne k (Nat.eq_zero_of_zero_dvd (h ▸ hdk))⟩
  set c := k.totient / d.totient
  -- each column (fibre over `u`) has `c` elements; enumerate it
  have hcard : ∀ u : (ZMod d)ˣ, Fintype.card {v : (ZMod k)ˣ // ZMod.unitsMap hdk v = u} = c := by
    intro u
    rw [Fintype.card_subtype]
    exact card_fiber_unitsMap hdk u
  let e : ∀ u : (ZMod d)ˣ, {v : (ZMod k)ˣ // ZMod.unitsMap hdk v = u} ≃ Fin c :=
    fun u ↦ Fintype.equivFinOfCardEq (hcard u)
  refine ⟨fun j ↦ univ.image fun u ↦ ((e u).symm j : (ZMod k)ˣ), ?_, ?_, ?_⟩
  · intro i j hij
    rw [disjoint_left]
    intro x hxi hxj
    obtain ⟨u, -, rfl⟩ := mem_image.1 hxi
    obtain ⟨w, -, hw⟩ := mem_image.1 hxj
    have huw : w = u := by
      have h1 := ((e w).symm j).2
      have h2 := ((e u).symm i).2
      rw [← h1, ← h2, hw]
    subst huw
    exact hij ((e w).symm.injective (Subtype.ext hw)).symm
  · intro v
    refine ⟨e (ZMod.unitsMap hdk v) ⟨v, rfl⟩, mem_image.2 ⟨ZMod.unitsMap hdk v, mem_univ _, ?_⟩⟩
    simp
  · intro j
    refine ⟨fun _ _ ↦ Set.mem_univ _, ?_, ?_⟩
    · intro x hx y hy hxy
      simp only [coe_image, coe_univ, Set.image_univ, Set.mem_range] at hx hy
      obtain ⟨u, rfl⟩ := hx
      obtain ⟨w, rfl⟩ := hy
      have h1 := ((e u).symm j).2
      have h2 := ((e w).symm j).2
      have huw : u = w := by rw [← h1, ← h2]; exact hxy
      subst huw; rfl
    · intro u _
      exact ⟨((e u).symm j : (ZMod k)ˣ), by simp, ((e u).symm j).2⟩

end NTKB.Apostol
