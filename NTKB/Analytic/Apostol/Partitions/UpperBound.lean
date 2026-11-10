/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.NumberTheory.ZetaValues
import NTKB.Attr

/-!
# An upper bound for `p(n)` (Apostol, Theorem 14.5)

**Theorem 14.5**: `p(n) < e^{K√n}` for `n ≥ 1`, `K = π √(2/3)`.

Apostol's proof: for `0 < x < 1`, `p(n) xⁿ < F(x) = ∏_{m ≥ 1} (1 - x^m)⁻¹`, and
`log F(x) = ∑_m ∑_k x^{mk}/k = ∑_k (1/k) x^k/(1 - x^k) ≤ ∑_k (1/k²) x/(1 - x) = (π²/6)/t` with
`t = (1 - x)/x` (using `k x^{k-1} ≤ (1 - x^k)/(1 - x)`); also `n log(1/x) < n t`; take
`t = π/√(6n)`. Here only the factors `m ≤ n` of `F(x)` are used (the others are `≥ 1`), which
avoids the infinite product: `p(n) xⁿ < ∏_{m=1}^n (1 - x^m)⁻¹` is proved by sending a partition
to its multiplicity vector `(c_1, …, c_n)`, an injection into `{0, …, n}ⁿ`.
-/

open Finset Real

namespace NTKB.Apostol

/-- The multiplicities `c_m` (`1 ≤ m ≤ n`) of a partition of `n`, indexed by `i = m - 1`. -/
def partitionMult {n : ℕ} (p : n.Partition) (i : Fin n) : ℕ :=
  p.parts.count ((i : ℕ) + 1)

theorem partitionMult_injective (n : ℕ) : Function.Injective (partitionMult (n := n)) := by
  intro p q h
  apply Nat.Partition.toFinsuppAntidiag_injective
  ext m
  change p.parts.count m * m = q.parts.count m * m
  rcases Nat.eq_zero_or_pos m with rfl | hm0
  · simp
  by_cases hmn : m ≤ n
  · have := congrFun h ⟨m - 1, by omega⟩
    simp only [partitionMult, Nat.sub_add_cancel hm0] at this
    rw [this]
  · have hp : p.parts.count m = 0 := Multiset.count_eq_zero.2
      fun hm ↦ hmn (Nat.Partition.le_of_mem_parts hm)
    have hq : q.parts.count m = 0 := Multiset.count_eq_zero.2
      fun hm ↦ hmn (Nat.Partition.le_of_mem_parts hm)
    rw [hp, hq]

theorem sum_mul_partitionMult {n : ℕ} (p : n.Partition) :
    ∑ i : Fin n, ((i : ℕ) + 1) * partitionMult p i = n := by
  have h := p.toFinsuppAntidiag_mem_finsuppAntidiag
  rw [mem_finsuppAntidiag] at h
  refine Eq.trans ?_ h.1
  rw [← Finset.Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range, Nat.add_sub_cancel,
    ← Fin.sum_univ_eq_sum_range]
  refine sum_congr rfl fun i _ ↦ ?_
  change _ = p.parts.count (1 + (i : ℕ)) * (1 + (i : ℕ))
  rw [partitionMult, add_comm 1, mul_comm]

theorem partitionMult_le {n : ℕ} (p : n.Partition) (i : Fin n) : partitionMult p i ≤ n := by
  refine (Multiset.count_le_card _ _).trans ?_
  have := Multiset.card_nsmul_le_sum (s := p.parts) (a := 1) fun x hx ↦ p.parts_pos hx
  simpa [p.parts_sum] using this

/-- `p(n) xⁿ < ∏_{m=1}^n (1 - x^m)⁻¹` for `n ≥ 1`, `0 < x < 1`. -/
theorem card_partition_mul_pow_lt {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    (Fintype.card n.Partition : ℝ) * x ^ n < ∏ i : Fin n, 1 / (1 - x ^ ((i : ℕ) + 1)) := by
  set F : (Fin n → ℕ) → ℝ := fun g ↦ ∏ i : Fin n, (x ^ ((i : ℕ) + 1)) ^ g i
  have hF : ∀ p : n.Partition, F (partitionMult p) = x ^ n := by
    intro p
    simp only [F, ← pow_mul, prod_pow_eq_pow_sum, sum_mul_partitionMult]
  have h1 : (Fintype.card n.Partition : ℝ) * x ^ n = ∑ g ∈ univ.image partitionMult, F g := by
    rw [sum_image fun p _ q _ h ↦ partitionMult_injective n h]
    simp [hF, Finset.card_univ]
  have h2 : ∑ g ∈ univ.image partitionMult, F g ≤
      ∑ g ∈ Fintype.piFinset fun _ : Fin n ↦ range (n + 1), F g := by
    apply sum_le_sum_of_subset_of_nonneg
    · intro g hg
      obtain ⟨p, -, rfl⟩ := mem_image.1 hg
      simp only [Fintype.mem_piFinset, mem_range]
      exact fun i ↦ Nat.lt_succ_of_le (partitionMult_le p i)
    · intro g _ _
      exact prod_nonneg fun i _ ↦ by positivity
  have h3 : ∑ g ∈ Fintype.piFinset (fun _ : Fin n ↦ range (n + 1)), F g =
      ∏ i : Fin n, ∑ j ∈ range (n + 1), (x ^ ((i : ℕ) + 1)) ^ j :=
    (prod_univ_sum (fun _ : Fin n ↦ range (n + 1)) fun i j ↦ (x ^ ((i : ℕ) + 1)) ^ j).symm
  rw [h1]
  refine h2.trans_lt (h3 ▸ ?_)
  have hne : (univ : Finset (Fin n)).Nonempty := ⟨⟨0, hn⟩, mem_univ _⟩
  apply prod_lt_prod_of_nonempty₀ _ _ hne
  · intro i _
    exact sum_pos (fun j _ ↦ by positivity) ⟨0, by simp⟩
  · intro i _
    set r := x ^ ((i : ℕ) + 1)
    have hr0 : 0 < r := by positivity
    have hr1 : r < 1 := pow_lt_one₀ hx0.le hx1 (by omega)
    have hg : (∑ j ∈ range (n + 1), r ^ j) * (1 - r) = 1 - r ^ (n + 1) := geom_sum_mul_neg r _
    rw [lt_div_iff₀ (by linarith), hg]
    linarith [pow_pos hr0 (n + 1)]

/-- `y/(1 - y) ≤ x/(k(1 - x))` for `y = x^k`, `0 < x < 1`, `k ≥ 1`
(Apostol: `k x^{k-1} ≤ 1 + x + ⋯ + x^{k-1} = (1 - x^k)/(1 - x)`). -/
theorem pow_div_one_sub_pow_le {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) (k : ℕ) :
    x ^ (k + 1) / (1 - x ^ (k + 1)) ≤ x / ((k + 1) * (1 - x)) := by
  have hgeom : 1 - x ^ (k + 1) = (1 - x) * ∑ j ∈ range (k + 1), x ^ j := by
    rw [mul_comm, geom_sum_mul_neg]
  have hsum : ((k : ℝ) + 1) * x ^ k ≤ ∑ j ∈ range (k + 1), x ^ j := by
    have := card_nsmul_le_sum (range (k + 1)) (fun j ↦ x ^ j) (x ^ k)
      fun j hj ↦ pow_le_pow_of_le_one hx0.le hx1.le (by simpa [Nat.lt_succ_iff] using hj)
    simpa using this
  have hxk : 0 < 1 - x ^ (k + 1) := by
    have := pow_lt_one₀ hx0.le hx1 (show k + 1 ≠ 0 by omega); linarith
  have h1x : 0 < 1 - x := by linarith
  rw [div_le_div_iff₀ hxk (by positivity), hgeom]
  have := mul_le_mul_of_nonneg_left hsum (show 0 ≤ x * (1 - x) by positivity)
  calc x ^ (k + 1) * ((k + 1) * (1 - x)) = x * (1 - x) * ((k + 1) * x ^ k) := by ring
    _ ≤ x * (1 - x) * ∑ j ∈ range (k + 1), x ^ j := this
    _ = x * ((1 - x) * ∑ j ∈ range (k + 1), x ^ j) := by ring

theorem hasSum_one_div_succ_sq : HasSum (fun k : ℕ ↦ 1 / ((k : ℝ) + 1) ^ 2) (π ^ 2 / 6) := by
  have := (hasSum_nat_add_iff' 1).2 hasSum_zeta_two
  simpa using this

/-- Apostol's estimate of `log F(x)`, for the factors `m ≤ n`:
`∑_{m=1}^n -log(1 - x^m) ≤ (π²/6) · x/(1 - x)`. -/
theorem sum_neg_log_one_sub_pow_le (n : ℕ) {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    ∑ i : Fin n, -log (1 - x ^ ((i : ℕ) + 1)) ≤ π ^ 2 / 6 * (x / (1 - x)) := by
  have hy : ∀ i : Fin n, |x ^ ((i : ℕ) + 1)| < 1 := fun i ↦ by
    rw [abs_of_pos (by positivity)]; exact pow_lt_one₀ hx0.le hx1 (by omega)
  set f : Fin n → ℕ → ℝ := fun i k ↦ (x ^ ((i : ℕ) + 1)) ^ (k + 1) / (k + 1)
  have hs : ∀ i, HasSum (f i) (-log (1 - x ^ ((i : ℕ) + 1))) := fun i ↦
    hasSum_pow_div_log_of_abs_lt_one (hy i)
  have hsum : HasSum (fun k ↦ ∑ i : Fin n, f i k) (∑ i : Fin n, -log (1 - x ^ ((i : ℕ) + 1))) :=
    hasSum_sum fun i _ ↦ hs i
  set C := x / (1 - x)
  have hbound : ∀ k : ℕ, ∑ i : Fin n, f i k ≤ 1 / ((k : ℝ) + 1) ^ 2 * C := by
    intro k
    set y := x ^ (k + 1)
    have hy0 : 0 < y := by positivity
    have hy1 : y < 1 := pow_lt_one₀ hx0.le hx1 (show k + 1 ≠ 0 by omega)
    have e : ∑ i : Fin n, f i k = (1 / ((k : ℝ) + 1)) * ∑ i ∈ range n, y ^ (i + 1) := by
      rw [mul_sum, ← Fin.sum_univ_eq_sum_range (fun i ↦ 1 / ((k : ℝ) + 1) * y ^ (i + 1))]
      refine sum_congr rfl fun i _ ↦ ?_
      simp only [f, y, ← pow_mul]
      rw [mul_comm ((i : ℕ) + 1)]
      ring
    have hgeo : ∑ i ∈ range n, y ^ (i + 1) ≤ y / (1 - y) := by
      have : ∑ i ∈ range n, y ^ (i + 1) = y * ∑ i ∈ range n, y ^ i := by
        rw [mul_sum]; exact sum_congr rfl fun i _ ↦ by ring
      rw [this, geom_sum_eq hy1.ne, le_div_iff₀ (by linarith)]
      have : (y ^ n - 1) / (y - 1) * (1 - y) = 1 - y ^ n := by
        field_simp [show y - 1 ≠ 0 by linarith]; ring
      rw [mul_assoc, this]
      nlinarith [pow_pos hy0 n]
    rw [e]
    calc 1 / ((k : ℝ) + 1) * ∑ i ∈ range n, y ^ (i + 1)
        ≤ 1 / ((k : ℝ) + 1) * (y / (1 - y)) := by gcongr
      _ ≤ 1 / ((k : ℝ) + 1) * (x / ((k + 1) * (1 - x))) := by
          exact mul_le_mul_of_nonneg_left (pow_div_one_sub_pow_le hx0 hx1 k) (by positivity)
      _ = 1 / ((k : ℝ) + 1) ^ 2 * C := by
          simp only [C]; field_simp
  exact hasSum_le hbound hsum (hasSum_one_div_succ_sq.mul_right C)

/-- **Apostol, Theorem 14.5**: `p(n) < e^{K√n}` for `n ≥ 1`, with `K = π √(2/3)`. -/
@[kb "apostol1976" "Thm 14.5, p. 316"]
theorem card_partition_lt_exp {n : ℕ} (hn : 1 ≤ n) :
    (Fintype.card n.Partition : ℝ) < exp (π * √(2 / 3) * √n) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  set s := √(n : ℝ)
  have hs : 0 < s := sqrt_pos.2 hn0
  have hs2 : s ^ 2 = n := sq_sqrt hn0.le
  have h6 : (0 : ℝ) < √6 := by positivity
  have h66 : √6 ^ 2 = 6 := sq_sqrt (by norm_num)
  set t := π / (√6 * s)
  have ht : 0 < t := by positivity
  set x := 1 / (1 + t)
  have hx0 : 0 < x := by positivity
  have hx1 : x < 1 := by rw [div_lt_one (by linarith)]; linarith
  have hC : x / (1 - x) = 1 / t := by
    simp only [x]; field_simp [ht.ne']; ring
  have hp : 0 < (Fintype.card n.Partition : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have key := card_partition_mul_pow_lt hn hx0 hx1
  have hprod : 0 < (Fintype.card n.Partition : ℝ) * x ^ n := by positivity
  have hlog := log_lt_log hprod key
  rw [log_mul hp.ne' (by positivity), log_pow, log_prod (fun i _ ↦ by
    have : x ^ ((i : ℕ) + 1) < 1 := pow_lt_one₀ hx0.le hx1 (by omega)
    exact (one_div_pos.2 (by linarith)).ne')] at hlog
  simp only [one_div, log_inv] at hlog
  have hS := sum_neg_log_one_sub_pow_le n hx0 hx1
  rw [hC] at hS
  have hlogx : -t ≤ log x := by
    simp only [x, one_div, log_inv, neg_le_neg_iff]
    have := log_le_sub_one_of_pos (show 0 < 1 + t by linarith); linarith
  rw [← log_lt_iff_lt_exp hp]
  have h23 : √(2 / 3) = √6 / 3 := by
    rw [show (2 : ℝ) / 3 = 6 / 9 by norm_num, sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 9),
      show (9 : ℝ) = 3 ^ 2 by norm_num, sqrt_sq (by norm_num)]
  have hval : π ^ 2 / 6 * (1 / t) + n * t = π * √(2 / 3) * s := by
    rw [h23, ← hs2]; simp only [t]; field_simp; rw [h66]; ring
  have : (n : ℝ) * (-t) ≤ n * log x := mul_le_mul_of_nonneg_left hlogx hn0.le
  nlinarith

end NTKB.Apostol
