/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Apostol.Averages.DivisorSums
import NTKB.Analytic.Apostol.Averages.Visible
import Mathlib.Data.Int.Interval
import Mathlib.Order.Filter.AtTopBot.Floor

/-!
# The density of lattice points visible from the origin (Apostol, Theorem 3.9)

Let `N(r)` be the number of lattice points in the square `|x| ≤ r, |y| ≤ r` and `N'(r)` the number
of those visible from the origin. **Theorem 3.9:** `N'(r)/N(r) → 6/π²`.

Apostol's proof: by symmetry `N'(r) = 8 ∑_{n ≤ r} φ(n)` (here: by Theorem 3.8 the visible points
are those with `gcd(x, y) = 1`; folding the signs gives `4 + 4 C(R)` with
`C(R) = #{(a, b) ∈ [1, R]² : (a, b) = 1} = 2 ∑_{n ≤ R} φ(n) - 1`), then Theorem 3.7 gives
`N'(r) = (24/π²) r² + O(r log r)` while `N(r) = (2⌊r⌋ + 1)² = 4r² + O(r)`.
-/

open Finset Filter Topology Real

namespace NTKB.Apostol

/-- The lattice points of the square `|x|, |y| ≤ R`. -/
noncomputable def latticeSquare (R : ℕ) : Finset (ℤ × ℤ) := Icc (-(R : ℤ)) R ×ˢ Icc (-(R : ℤ)) R

/-- `N'(r)`: the lattice points in `|x|, |y| ≤ r` visible from the origin. -/
noncomputable def visibleCount (r : ℝ) : ℕ := by
  classical
  exact ((latticeSquare ⌊r⌋₊).filter fun P ↦ MutuallyVisible (0, 0) P).card

/-- `N(r)`: the lattice points in `|x|, |y| ≤ r`. -/
noncomputable def latticeCount (r : ℝ) : ℕ := (latticeSquare ⌊r⌋₊).card

theorem latticeCount_eq (r : ℝ) : (latticeCount r : ℝ) = (2 * ⌊r⌋₊ + 1) ^ 2 := by
  rw [latticeCount, latticeSquare, card_product, Int.card_Icc]
  push_cast
  have : ((⌊r⌋₊ : ℤ) + 1 - -(⌊r⌋₊ : ℤ)).toNat = 2 * ⌊r⌋₊ + 1 := by omega
  rw [this]; push_cast; ring

/-- `C(R) + 1 = 2 ∑_{n ≤ R} φ(n) + [R = 0]`, where `C(R)` counts the coprime pairs in `[1, R]²`. -/
theorem card_coprime_pairs (R : ℕ) :
    ∑ a ∈ Icc 1 R, ∑ b ∈ Icc 1 R, (if a.Coprime b then 1 else 0) + 1 =
      2 * ∑ n ∈ Ioc 0 R, n.totient + (if R = 0 then 1 else 0) := by
  -- `#{b ∈ [1, R] : (R+1, b) = 1} + [R = 0] = φ(R + 1)`
  have hrow : ∀ R : ℕ, ∑ b ∈ Icc 1 R, (if (R + 1).Coprime b then 1 else 0) +
      (if R = 0 then 1 else 0) = (R + 1).totient := by
    intro R
    rw [Nat.totient_eq_card_coprime, card_filter, range_eq_Ico,
      sum_eq_sum_Ico_succ_bot (by omega)]
    rw [show Ico (0 + 1) (R + 1) = Icc 1 R by ext; simp only [mem_Ico, mem_Icc]; omega]
    simp only [Nat.coprime_zero_right, Nat.add_eq_right]
    rw [add_comm]
  induction R with
  | zero => simp
  | succ R ih =>
    rw [sum_Icc_succ_top (by omega)]
    simp_rw [sum_Icc_succ_top (show 1 ≤ R + 1 by omega)]
    rw [sum_add_distrib, sum_Ioc_succ_top (by omega)]
    have hr1 := hrow R
    have hr2 : ∑ a ∈ Icc 1 R, (if a.Coprime (R + 1) then 1 else 0) + (if R = 0 then 1 else 0) =
        (R + 1).totient := by
      rw [← hrow R]; congr 1
      exact sum_congr rfl fun a _ ↦ by simp only [Nat.coprime_comm]
    have hd : (if (R + 1).Coprime (R + 1) then 1 else 0) = (if R = 0 then 1 else 0) := by
      simp [Nat.coprime_self]
    rw [hd]
    simp only [show R + 1 ≠ 0 from by omega, if_false, add_zero]
    have := ih
    omega

/-- `∑_{|x| ≤ R} f(x) = f(0) + ∑_{a=1}^{R} (f(a) + f(-a))`. -/
theorem sum_Icc_neg_eq {M : Type*} [AddCommMonoid M] (f : ℤ → M) (R : ℕ) :
    ∑ x ∈ Icc (-(R : ℤ)) R, f x = f 0 + ∑ a ∈ Icc 1 R, (f a + f (-(a : ℤ))) := by
  induction R with
  | zero => simp
  | succ R ih =>
    have hset : Icc (-((R + 1 : ℕ) : ℤ)) ((R + 1 : ℕ) : ℤ) =
        insert ((R + 1 : ℕ) : ℤ) (insert (-((R + 1 : ℕ) : ℤ)) (Icc (-(R : ℤ)) R)) := by
      ext x; simp only [mem_Icc, mem_insert]; push_cast; omega
    rw [hset, sum_insert (by simp only [mem_insert, mem_Icc]; push_cast; omega),
      sum_insert (by simp only [mem_Icc]; push_cast; omega), ih, sum_Icc_succ_top (by omega)]
    abel

/-- `N'(r)` counts the points with `gcd(x, y) = 1` (Theorem 3.8). -/
theorem visibleCount_eq (r : ℝ) : visibleCount r =
    ((latticeSquare ⌊r⌋₊).filter fun P : ℤ × ℤ ↦ Int.gcd P.1 P.2 = 1).card := by
  classical
  rw [visibleCount]
  congr 1
  ext P
  simp only [mem_filter]
  rw [mutuallyVisible_iff_gcd_eq_one]
  simp [Int.gcd_neg]

/-- `N'(R) = 8 ∑_{n ≤ R} φ(n)` for `R ≥ 1` (Apostol, proof of Theorem 3.9). -/
theorem card_gcd_eq_one_latticeSquare {R : ℕ} (hR : 1 ≤ R) :
    ((latticeSquare R).filter fun P : ℤ × ℤ ↦ Int.gcd P.1 P.2 = 1).card =
      8 * ∑ n ∈ Ioc 0 R, n.totient := by
  rw [card_filter, latticeSquare, sum_product, sum_Icc_neg_eq]
  simp_rw [sum_Icc_neg_eq (fun y ↦ if Int.gcd _ y = 1 then 1 else 0) R]
  simp
  have hD := card_coprime_pairs R
  rw [if_neg (by omega), add_zero] at hD
  simp only [Nat.coprime_iff_gcd_eq_one] at hD
  have h1 : ∑ a ∈ Icc 1 R, (if a = 1 then 1 else 0) = 1 := by
    rw [sum_ite_eq']; simp [hR]
  simp only [sum_add_distrib, h1]
  omega

/-- **Apostol, Theorem 3.9.** The lattice points visible from the origin have density `6/π²`:
`N'(r)/N(r) → 6/π²` as `r → ∞`. -/
@[kb "apostol1976" "Thm 3.9, p. 63"]
theorem tendsto_visibleCount_div_latticeCount :
    Tendsto (fun r : ℝ ↦ (visibleCount r : ℝ) / latticeCount r) atTop (𝓝 (6 / π ^ 2)) := by
  -- `N'(r)/r² → 24/π²`
  have hN' : Tendsto (fun r : ℝ ↦ (visibleCount r : ℝ) / r ^ 2) atTop (𝓝 (24 / π ^ 2)) := by
    have hlog : Tendsto (fun r : ℝ ↦ 40 * (Real.log r / r)) atTop (𝓝 0) := by
      have := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).const_mul 40
      simpa using this
    refine tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero_norm' ?_ hlog)
    filter_upwards [eventually_ge_atTop 2] with r hr
    have hr0 : 0 < r := by linarith
    have hN1 : 1 ≤ ⌊r⌋₊ := Nat.le_floor (by push_cast; linarith)
    rw [visibleCount_eq, card_gcd_eq_one_latticeSquare hN1]
    have h37 := abs_sum_totient_sub_le hr
    rw [norm_norm, Real.norm_eq_abs]
    push_cast
    have e : (8 * ∑ n ∈ Ioc 0 ⌊r⌋₊, (n.totient : ℝ)) / r ^ 2 - 24 / π ^ 2 =
        8 * (∑ n ∈ Ioc 0 ⌊r⌋₊, (n.totient : ℝ) - 3 / π ^ 2 * r ^ 2) / r ^ 2 := by
      field_simp; ring
    rw [e, abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 8),
      abs_of_pos (by positivity : (0 : ℝ) < r ^ 2), div_le_iff₀ (by positivity)]
    calc 8 * |∑ n ∈ Ioc 0 ⌊r⌋₊, (n.totient : ℝ) - 3 / π ^ 2 * r ^ 2| ≤
        8 * (5 * (r * Real.log r)) := by gcongr
      _ = 40 * (Real.log r / r) * r ^ 2 := by field_simp; ring
  -- `N(r)/r² → 4`
  have hN : Tendsto (fun r : ℝ ↦ (latticeCount r : ℝ) / r ^ 2) atTop (𝓝 4) := by
    have hfl : Tendsto (fun r : ℝ ↦ (⌊r⌋₊ : ℝ) / r) atTop (𝓝 1) := tendsto_nat_floor_div_atTop
    have hinv : Tendsto (fun r : ℝ ↦ 1 / r) atTop (𝓝 0) := by
      simpa using tendsto_inv_atTop_zero
    have h2 := ((hfl.const_mul 2).add hinv).pow 2
    norm_num at h2
    refine h2.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with r hr
    rw [latticeCount_eq]
    field_simp
  have := hN'.div hN (by norm_num)
  refine (this.congr' ?_).trans (by rw [show (24 / π ^ 2) / 4 = 6 / π ^ 2 by ring])
  filter_upwards [eventually_gt_atTop 0] with r hr
  have : (r ^ 2 : ℝ) ≠ 0 := by positivity
  simp only [Pi.div_apply]
  rw [div_div_div_cancel_right₀ this]

end NTKB.Apostol
