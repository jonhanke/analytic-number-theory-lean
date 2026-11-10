/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.Combinatorics.Enumerative.Partition.GenFun
import Mathlib.Combinatorics.Enumerative.Pentagonal.PowerSeries
import Mathlib.Data.Int.Interval
import NTKB.Attr

/-!
# Euler's generating function for `p(n)` and the pentagonal recurrence (Apostol, Chapter 14)

As formal power series (Mathlib's `PowerSeries.WithPiTopology`):

* **Theorem 14.2** (Euler): `∏_{m ≥ 1} (1 - x^m)⁻¹ = ∑_{n ≥ 0} p(n) xⁿ`, in the forms
  `HasProd (fun m ↦ 1 + ∑_{j ≥ 1} x^{mj}) P` (each factor is `(1 - x^m)⁻¹`) and
  `P · ∏_{m ≥ 1} (1 - x^m) = 1`, with `P = ∑ p(n) xⁿ` (`NTKB.Apostol.partitionSeries`).
  Mathlib's `Nat.Partition.genFun` docstring lists this case as a TODO.
* **Theorem 14.4**: `p(n) = ∑_{k ≥ 1} (-1)^{k+1} (p(n - ω(k)) + p(n - ω(-k)))` for `n ≥ 1`, in
  the form `∑_{k ∈ ℤ, ω(k) ≤ n} (-1)^k p(n - ω(k)) = 0`, `ω(k) = k(3k-1)/2` (Mathlib's
  `pentagonal`), from Mathlib's pentagonal number theorem (`hasProd_one_sub_X_pow`).

Apostol works with convergent power series for `|x| < 1`; the formal identities are equivalent
(the coefficients are the same).
-/

open Finset PowerSeries
open scoped PowerSeries.WithPiTopology

namespace NTKB.Apostol

/-- `∑_{n ≥ 0} p(n) xⁿ`, `p(n)` the number of partitions of `n`. -/
noncomputable def partitionSeries (R : Type*) [CommRing R] : R⟦X⟧ :=
  PowerSeries.mk fun n ↦ (Fintype.card n.Partition : R)

variable (R : Type*) [CommRing R]

theorem genFun_one_eq_partitionSeries :
    Nat.Partition.genFun (fun _ _ ↦ (1 : R)) = partitionSeries R := by
  ext n
  simp [partitionSeries, Nat.Partition.coeff_genFun, Finsupp.prod]

section Topology

variable [TopologicalSpace R] [IsTopologicalRing R] [T2Space R]

/-- **Apostol, Theorem 14.2** (Euler), product form:
`∏_{m ≥ 1} (1 + x^m + x^{2m} + ⋯) = ∑ p(n) xⁿ`. -/
@[kb "apostol1976" "Thm 14.2, p. 318"]
theorem hasProd_partitionSeries :
    HasProd (fun i : ℕ ↦ 1 + ∑' j : ℕ, X ^ ((i + 1) * (j + 1)))
      (partitionSeries R) := by
  have := Nat.Partition.hasProd_genFun (fun _ _ ↦ (1 : R))
  rw [genFun_one_eq_partitionSeries] at this
  simpa using this

/-- Each factor is `(1 - x^m)⁻¹`: `(1 + ∑_{j ≥ 1} x^{mj}) (1 - x^m) = 1` for `m ≥ 1`. -/
theorem one_add_tsum_mul_one_sub (m : ℕ) (hm : m ≠ 0) :
    (1 + ∑' j : ℕ, (X : R⟦X⟧) ^ (m * (j + 1))) * (1 - X ^ m) = 1 := by
  have hs : Summable fun j : ℕ ↦ (X : R⟦X⟧) ^ (m * (j + 1)) := by
    have := Nat.Partition.summable_genFun_term' (fun _ _ ↦ (1 : R)) hm
    simpa using this
  have h1 : ∑' j : ℕ, (X : R⟦X⟧) ^ (m * (j + 1)) =
      X ^ m + ∑' j : ℕ, (X : R⟦X⟧) ^ (m * (j + 1 + 1)) := by
    rw [hs.tsum_eq_zero_add]; simp
  have h2 : (∑' j : ℕ, (X : R⟦X⟧) ^ (m * (j + 1))) * X ^ m =
      ∑' j : ℕ, (X : R⟦X⟧) ^ (m * (j + 1 + 1)) := by
    rw [← hs.tsum_mul_right]
    congr 1; ext1 j; rw [← pow_add]; ring_nf
  rw [mul_sub, mul_one, add_mul, one_mul, h2, h1]
  ring

/-- **Apostol, Theorem 14.2** (Euler), inverse form: `(∑ p(n) xⁿ) · ∏_{m ≥ 1} (1 - x^m) = 1`. -/
@[kb "apostol1976" "Thm 14.2, p. 318"]
theorem partitionSeries_mul_tprod_one_sub_X_pow :
    partitionSeries R * ∏' n : ℕ, (1 - X ^ (n + 1) : R⟦X⟧) = 1 := by
  have h := (hasProd_partitionSeries R).mul (WithPiTopology.hasProd_one_sub_X_pow R)
  have h1 : (fun i : ℕ ↦ (1 + ∑' j : ℕ, (X : R⟦X⟧) ^ ((i + 1) * (j + 1))) *
      (1 - X ^ (i + 1))) = fun _ ↦ 1 := by
    ext1 i; exact one_add_tsum_mul_one_sub R (i + 1) (Nat.succ_ne_zero i)
  rw [h1] at h
  rw [WithPiTopology.tprod_one_sub_X_pow]
  exact h.unique hasProd_one

end Topology

/-- `P · (pentagonal series) = 1` over any commutative ring (no topology needed). -/
theorem partitionSeries_mul_pentagonalSeries :
    partitionSeries R * pentagonalSeries R = 1 := by
  let _ : TopologicalSpace R := ⊥
  have : DiscreteTopology R := ⟨rfl⟩
  have := partitionSeries_mul_tprod_one_sub_X_pow R
  rwa [WithPiTopology.tprod_one_sub_X_pow] at this

theorem pentagonal_le_iff_mem {n : ℕ} {k : ℤ} (h : pentagonal k ≤ n) : k ∈ Icc (-(n : ℤ)) n := by
  have h2 := two_mul_natCast_pentagonal k
  have : (pentagonal k : ℤ) ≤ n := by exact_mod_cast h
  simp only [mem_Icc]
  constructor <;> nlinarith

/-- **Apostol, Theorem 14.4.** For `n ≥ 1`, `∑_{k ∈ ℤ, ω(k) ≤ n} (-1)^k p(n - ω(k)) = 0`, i.e.
`p(n) = ∑_{k ≥ 1} (-1)^{k+1} (p(n - ω(k)) + p(n - ω(-k)))` with `ω(k) = k(3k-1)/2`. -/
@[kb "apostol1976" "Thm 14.4, p. 325"]
theorem sum_negOnePow_card_partition_sub_pentagonal {n : ℕ} (hn : n ≠ 0) :
    ∑ k ∈ (Icc (-(n : ℤ)) n).filter (fun k ↦ pentagonal k ≤ n),
      (k.negOnePow : ℤ) * (Fintype.card (n - pentagonal k).Partition : ℤ) = 0 := by
  classical
  have h := congrArg (coeff n) (partitionSeries_mul_pentagonalSeries ℤ)
  rw [coeff_mul, coeff_one, if_neg hn, Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j ↦ coeff i (partitionSeries ℤ) * coeff j (pentagonalSeries ℤ))] at h
  -- reindex by `j = n - i`
  rw [← sum_range_reflect] at h
  have h' : ∑ j ∈ range (n + 1), (pentagonalSeries ℤ).coeff j *
      (Fintype.card (n - j).Partition : ℤ) = 0 := by
    rw [← h]
    refine sum_congr rfl fun j hj ↦ ?_
    have hj' : j ≤ n := Nat.lt_succ_iff.1 (mem_range.1 hj)
    simp only [partitionSeries, coeff_mk]
    rw [show n + 1 - 1 - j = n - j by omega, show n - (n - j) = j by omega, mul_comm]
  -- only pentagonal `j` contribute
  rw [← sum_filter_of_ne (p := fun j ↦ j ∈ Set.range pentagonal)] at h'
  · rw [← h']
    symm
    have himg : (range (n + 1)).filter (fun j ↦ j ∈ Set.range pentagonal) =
        ((Icc (-(n : ℤ)) n).filter (fun k ↦ pentagonal k ≤ n)).image pentagonal := by
      ext j
      simp only [mem_filter, mem_range, Set.mem_range, mem_image]
      constructor
      · rintro ⟨hj, k, rfl⟩
        exact ⟨k, ⟨pentagonal_le_iff_mem (by omega), by omega⟩, rfl⟩
      · rintro ⟨k, ⟨-, hk⟩, rfl⟩
        exact ⟨by omega, k, rfl⟩
    rw [himg, sum_image (fun a _ b _ hab ↦ pentagonal_injective hab)]
    refine sum_congr rfl fun k _ ↦ ?_
    rw [coeff_pentagonalSeries_pentagonal, Int.cast_id]
  · intro j _ hne
    by_contra hmem
    exact hne (by rw [coeff_pentagonalSeries_eq_zero ℤ hmem, zero_mul])

end NTKB.Apostol
