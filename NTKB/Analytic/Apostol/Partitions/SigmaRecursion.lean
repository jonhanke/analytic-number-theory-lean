/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import NTKB.Analytic.Apostol.ArithmeticFunctions.GeneralizedConvolution

/-!
# `n p(n) = ∑_{k=1}^n σ(k) p(n - k)` (Apostol, Theorem 14.8, Example 1)

Apostol obtains this from Theorem 14.8 (logarithmic differentiation of `∏ (1 - x^m)⁻¹`,
`x F'(x) = F(x) ∑ σ(k) x^k`). We give the equivalent counting proof of the coefficient identity:
`n p(n) = ∑_{λ ⊢ n} ∑_d d c_d(λ) = ∑_d d ∑_{j ≥ 1} #{λ ⊢ n : c_d(λ) ≥ j}` and
`#{λ ⊢ n : c_d(λ) ≥ j} = p(n - jd)` (remove `j` parts equal to `d`); collecting the terms with
`jd = k` gives `σ(k) p(n - k)`.
-/

open Finset
open scoped ArithmeticFunction.sigma

namespace NTKB.Apostol

/-- Partitions of `n` with at least `j` parts equal to `d` correspond to partitions of
`n - j d` (remove, resp. add, `j` copies of `d`). -/
def partitionReplicateEquiv {n d j : ℕ} (hd : 1 ≤ d) (hjd : j * d ≤ n) :
    {p : n.Partition // Multiset.replicate j d ≤ p.parts} ≃ (n - j * d).Partition where
  toFun p := by
    refine ⟨p.1.parts - Multiset.replicate j d, fun hi ↦ ?_, ?_⟩
    · exact p.1.parts_pos (Multiset.mem_of_le (Multiset.sub_le_self _ _) hi)
    · have h := congrArg Multiset.sum (Multiset.sub_add_cancel p.2)
      rw [Multiset.sum_add, p.1.parts_sum, Multiset.sum_replicate, smul_eq_mul] at h
      omega
  invFun q := ⟨⟨q.parts + Multiset.replicate j d, fun hi ↦ by
      rcases Multiset.mem_add.1 hi with h | h
      · exact q.parts_pos h
      · rw [Multiset.eq_of_mem_replicate h]; omega, by
      rw [Multiset.sum_add, q.parts_sum, Multiset.sum_replicate, smul_eq_mul]; omega⟩,
    Multiset.le_add_left _ _⟩
  left_inv p := Subtype.ext <| Nat.Partition.ext <| Multiset.sub_add_cancel p.2
  right_inv q := Nat.Partition.ext <| Multiset.add_sub_cancel_right

theorem card_filter_le_count {n d j : ℕ} (hd : 1 ≤ d) (hjd : j * d ≤ n) :
    #{p : n.Partition | j ≤ p.parts.count d} = Fintype.card (n - j * d).Partition := by
  rw [← Fintype.card_congr (partitionReplicateEquiv hd hjd), Fintype.card_subtype]
  congr 1
  ext p
  simp [Multiset.le_count_iff_replicate_le]

theorem count_mul_le {n : ℕ} (p : n.Partition) (d : ℕ) : p.parts.count d * d ≤ n := by
  have h := Multiset.le_count_iff_replicate_le.1 (le_refl (p.parts.count d))
  obtain ⟨t, ht⟩ := Multiset.le_iff_exists_add.1 h
  have := congrArg Multiset.sum ht
  rw [Multiset.sum_add, Multiset.sum_replicate, smul_eq_mul, p.parts_sum] at this
  omega

theorem sum_parts_eq_sum_count {n : ℕ} (p : n.Partition) :
    ∑ d ∈ Ioc 0 n, d * p.parts.count d = n := by
  have h := p.toFinsuppAntidiag_mem_finsuppAntidiag
  rw [mem_finsuppAntidiag] at h
  refine Eq.trans ?_ h.1
  rw [← Finset.Icc_add_one_left_eq_Ioc]
  exact sum_congr rfl fun d _ ↦ mul_comm _ _

/-- **Apostol, Theorem 14.8, Example 1**: `n p(n) = ∑_{k=1}^n σ(k) p(n - k)`. -/
@[kb "apostol1976" "Thm 14.8 Example 1, p. 323"]
theorem mul_card_partition_eq_sum_sigma (n : ℕ) :
    n * Fintype.card n.Partition =
      ∑ k ∈ Ioc 0 n, σ 1 k * Fintype.card (n - k).Partition := by
  -- right side as a double sum over `(d, j)` with `dj ≤ n`
  have hR : ∑ k ∈ Ioc 0 n, σ 1 k * Fintype.card (n - k).Partition =
      ∑ d ∈ Ioc 0 n, ∑ j ∈ Ioc 0 (n / d), d * Fintype.card (n - j * d).Partition := by
    rw [← sum_Ioc_sum_divisorsAntidiagonal (fun d j ↦ d * Fintype.card (n - j * d).Partition)]
    refine sum_congr rfl fun k hk ↦ ?_
    rw [ArithmeticFunction.sigma_one_apply, sum_mul,
      ← Nat.sum_divisorsAntidiagonal (fun d _ ↦ d * Fintype.card (n - k).Partition)]
    refine sum_congr rfl fun x hx ↦ ?_
    rw [Nat.mem_divisorsAntidiagonal] at hx
    rw [mul_comm x.2, hx.1]
  rw [hR]
  -- left side
  have hL : n * Fintype.card n.Partition =
      ∑ d ∈ Ioc 0 n, d * ∑ p : n.Partition, p.parts.count d := by
    calc n * Fintype.card n.Partition = ∑ _p : n.Partition, n := by
          rw [sum_const, card_univ, smul_eq_mul, mul_comm]
      _ = ∑ p : n.Partition, ∑ d ∈ Ioc 0 n, d * p.parts.count d :=
          sum_congr rfl fun p _ ↦ (sum_parts_eq_sum_count p).symm
      _ = ∑ d ∈ Ioc 0 n, d * ∑ p : n.Partition, p.parts.count d := by
          rw [sum_comm]; simp_rw [mul_sum]
  rw [hL]
  refine sum_congr rfl fun d hd ↦ ?_
  have hd1 : 1 ≤ d := (mem_Ioc.1 hd).1
  rw [← mul_sum]
  congr 1
  have hc : ∀ p : n.Partition,
      p.parts.count d = ∑ j ∈ Ioc 0 (n / d), if j ≤ p.parts.count d then 1 else 0 := by
    intro p
    have hle : p.parts.count d ≤ n / d := (Nat.le_div_iff_mul_le hd1).2 (count_mul_le p d)
    rw [← card_filter]
    have : {j ∈ Ioc 0 (n / d) | j ≤ p.parts.count d} = Ioc 0 (p.parts.count d) := by
      ext j; simp only [mem_filter, mem_Ioc]; omega
    rw [this, Nat.card_Ioc, Nat.sub_zero]
  calc ∑ p : n.Partition, p.parts.count d
      = ∑ p : n.Partition, ∑ j ∈ Ioc 0 (n / d), if j ≤ p.parts.count d then 1 else 0 :=
        sum_congr rfl fun p _ ↦ hc p
    _ = ∑ j ∈ Ioc 0 (n / d), ∑ p : n.Partition, if j ≤ p.parts.count d then 1 else 0 := sum_comm
    _ = ∑ j ∈ Ioc 0 (n / d), #{p : n.Partition | j ≤ p.parts.count d} := by
        simp only [card_filter]
    _ = ∑ j ∈ Ioc 0 (n / d), Fintype.card (n - j * d).Partition :=
        sum_congr rfl fun j hj ↦
          card_filter_le_count hd1 ((Nat.le_div_iff_mul_le hd1).1 (mem_Ioc.1 hj).2)

end NTKB.Apostol
