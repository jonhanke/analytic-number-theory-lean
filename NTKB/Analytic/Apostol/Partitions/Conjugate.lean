/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.Combinatorics.Enumerative.Partition.YoungDiagram
import NTKB.Attr

/-!
# Conjugate partitions (Apostol, Theorem 14.1)

**Theorem 14.1**: the number of partitions of `n` into exactly `m` parts equals the number of
partitions of `n` whose largest part is `m`. Apostol's proof: reflect the Ferrers graph
(Young diagram) about the diagonal; Mathlib's `Nat.Partition.conjugate` is this reflection, and
the number of parts of the conjugate is the largest part (`card_parts_conjugate`).
-/

open YoungDiagram

namespace NTKB.Apostol

/-- The first row of the Young diagram of `p` is its largest part. -/
lemma rowLen_zero_ofPartition {n : ℕ} (p : Nat.Partition n) :
    (ofPartition p).rowLen 0 = p.parts.sup := by
  set μ := ofPartition p
  have hparts : p.parts = (μ.rowLens : Multiset ℕ) := by
    rw [rowLens_ofPartition_eq_sort_parts, Multiset.sort_eq]
  have hmem : ∀ x, x ∈ μ.rowLens ↔ ∃ i < μ.colLen 0, μ.rowLen i = x := by
    intro x
    simp [YoungDiagram.rowLens, List.mem_map, List.mem_range]
  apply le_antisymm
  · by_cases h0 : μ.colLen 0 = 0
    · have : (0, 0) ∉ μ := by rw [mem_iff_lt_colLen, h0]; exact lt_irrefl 0
      rw [mem_iff_lt_rowLen, not_lt, Nat.le_zero] at this
      rw [this]; exact Nat.zero_le _
    · apply Multiset.le_sup
      rw [hparts, Multiset.mem_coe, hmem]
      exact ⟨0, Nat.pos_of_ne_zero h0, rfl⟩
  · apply Multiset.sup_le.mpr
    intro x hx
    rw [hparts, Multiset.mem_coe, hmem] at hx
    obtain ⟨i, -, rfl⟩ := hx
    exact μ.rowLen_anti 0 i (Nat.zero_le i)

/-- The number of parts of the conjugate partition is the largest part. -/
lemma card_parts_conjugate {n : ℕ} (p : Nat.Partition n) :
    p.conjugate.parts.card = p.parts.sup := by
  rw [← rowLen_zero_ofPartition, ← colLen_transpose, ← length_rowLens]
  rfl

/-- **Theorem 14.1**: the number of partitions of `n` into exactly `m` parts equals the number of
partitions of `n` with largest part `m`. -/
@[kb "apostol1976" "Thm 14.1, p. 307"]
theorem card_partition_card_parts_eq (n m : ℕ) :
    (Finset.univ.filter fun p : n.Partition => p.parts.card = m).card =
      (Finset.univ.filter fun p : n.Partition => p.parts.sup = m).card := by
  refine Finset.card_bij' (fun p _ => p.conjugate) (fun p _ => p.conjugate) ?_ ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    rw [← card_parts_conjugate, Nat.Partition.conjugate_conjugate, hp]
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    rw [card_parts_conjugate, hp]
  · intro p _; exact Nat.Partition.conjugate_conjugate p
  · intro p _; exact Nat.Partition.conjugate_conjugate p

end NTKB.Apostol
