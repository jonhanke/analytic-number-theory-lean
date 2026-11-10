/- Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license. -/
import NTKB.Attr
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Algebra.Order.Round
import Mathlib.RingTheory.Coprime.Basic

/-!
# The sum `∑ min(N/t, 1/‖tα‖)` (Davenport, Chapter 25, p. 154, (3))

If `|α - a/q| ≤ q⁻²` with `(a, q) = 1`, then
`∑_{t ≤ T} min(N/t, 1/‖tα‖) ≪ (N/q + T + q) log (2qT)`.
-/

open Finset Real

namespace NTKB.Davenport

/-- Distance to the nearest integer, `‖x‖`. -/
noncomputable def distInt (x : ℝ) : ℝ := |x - round x|

/-- `min(A, 1/‖x‖)`, with the value `A` when `‖x‖ = 0` (i.e. `1/0 = ∞`). -/
noncomputable def minInv (A x : ℝ) : ℝ := if distInt x = 0 then A else min A (1 / distInt x)

lemma minSum_minInv_le_A (A x : ℝ) : minInv A x ≤ A := by
  unfold minInv
  split_ifs
  · exact le_rfl
  · exact min_le_left _ _

lemma minSum_minInv_le_of_ge (A x c : ℝ) (hc : 0 < c) (h : c ≤ distInt x) :
    minInv A x ≤ 1 / c := by
  have hne : distInt x ≠ 0 := ne_of_gt (lt_of_lt_of_le hc h)
  unfold minInv
  simp only [hne, ↓reduceIte]
  exact (min_le_right _ _).trans (one_div_le_one_div_of_le hc h)

lemma minSum_distInt_ge_fract (x : ℝ) : min (Int.fract x) (1 - Int.fract x) ≤ distInt x := by
  unfold distInt
  have hx : (⌊x⌋ : ℝ) + Int.fract x = x := Int.floor_add_fract x
  rcases le_or_gt (round x) ⌊x⌋ with h | h
  · have h1 : ((round x : ℤ) : ℝ) ≤ ⌊x⌋ := by exact_mod_cast h
    calc min (Int.fract x) (1 - Int.fract x) ≤ Int.fract x := min_le_left _ _
      _ ≤ x - round x := by linarith
      _ ≤ _ := le_abs_self _
  · have h' : ⌊x⌋ + 1 ≤ round x := Int.add_one_le_iff.mpr h
    have h1 : (⌊x⌋ : ℝ) + 1 ≤ ((round x : ℤ) : ℝ) := by exact_mod_cast h'
    calc min (Int.fract x) (1 - Int.fract x) ≤ 1 - Int.fract x := min_le_right _ _
      _ ≤ -(x - round x) := by linarith
      _ ≤ _ := neg_le_abs _

lemma minSum_harm_range (n : ℕ) :
    ∑ i ∈ range n, (1 : ℝ) / ((i : ℝ) + 1) ≤ 1 + Real.log n := by
  have h := harmonic_le_one_add_log n
  have e : ((harmonic n : ℚ) : ℝ) = ∑ i ∈ range n, (1 : ℝ) / ((i : ℝ) + 1) := by
    simp [harmonic]
  rw [← e]
  exact h

lemma minSum_Icc_eq_range (n : ℕ) (g : ℕ → ℝ) :
    ∑ k ∈ Icc 1 n, g k = ∑ i ∈ range n, g (i + 1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]

lemma minSum_harm_Icc (n : ℕ) :
    ∑ k ∈ Icc 1 n, (1 : ℝ) / (k : ℝ) ≤ 1 + Real.log n := by
  rw [minSum_Icc_eq_range]
  simpa using minSum_harm_range n

/-- Bin sum bound. -/
lemma minSum_bins_sum (q : ℕ) (hq : 1 ≤ q) :
    ∑ k ∈ Icc 1 (q - 2), ((q : ℝ) / k + (q : ℝ) / ((q : ℝ) - 1 - k)) ≤
      2 * q * (1 + Real.log q) := by
  rw [Finset.sum_add_distrib]
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have h1 : ∑ k ∈ Icc 1 (q - 2), (q : ℝ) / k ≤ q * (1 + Real.log q) := by
    have : ∑ k ∈ Icc 1 (q - 2), (q : ℝ) / k ≤ ∑ k ∈ Icc 1 q, (q : ℝ) / k := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro k hk
        simp only [mem_Icc] at hk ⊢
        omega
      · intro k _ _
        positivity
    refine this.trans ?_
    have e : ∑ k ∈ Icc 1 q, (q : ℝ) / k = q * ∑ k ∈ Icc 1 q, (1 : ℝ) / k := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      ring
    rw [e]
    exact mul_le_mul_of_nonneg_left (minSum_harm_Icc q) hq'.le
  have h2 : ∑ k ∈ Icc 1 (q - 2), (q : ℝ) / ((q : ℝ) - 1 - k) =
      ∑ k ∈ Icc 1 (q - 2), (q : ℝ) / k := by
    refine Finset.sum_nbij' (fun k => q - 1 - k) (fun k => q - 1 - k) ?_ ?_ ?_ ?_ ?_
    · intro k hk
      simp only [mem_Icc] at hk ⊢
      omega
    · intro k hk
      simp only [mem_Icc] at hk ⊢
      omega
    · intro k hk
      simp only [mem_Icc] at hk
      omega
    · intro k hk
      simp only [mem_Icc] at hk
      omega
    · intro k hk
      simp only [mem_Icc] at hk
      have : ((q - 1 - k : ℕ) : ℝ) = (q : ℝ) - 1 - k := by
        rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
        simp
      rw [this]
  rw [h2]
  linarith

lemma minSum_good (A x : ℝ) (q k : ℕ) (hk1 : 1 ≤ k) (hk2 : k + 2 ≤ q)
    (hb : ⌊(q : ℝ) * Int.fract x⌋₊ = k) :
    minInv A x ≤ (q : ℝ) / k + (q : ℝ) / ((q : ℝ) - 1 - k) := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hkq : (k : ℝ) + 2 ≤ q := by exact_mod_cast hk2
  have hfr0 : 0 ≤ (q : ℝ) * Int.fract x := mul_nonneg hq'.le (Int.fract_nonneg x)
  have l1 : (k : ℝ) ≤ q * Int.fract x := by
    rw [← hb]; exact Nat.floor_le hfr0
  have l2 : (q : ℝ) * Int.fract x < k + 1 := by
    rw [← hb]; exact Nat.lt_floor_add_one _
  have hm : (1 : ℝ) ≤ (q : ℝ) - 1 - k := by linarith
  have hqk : 0 ≤ (q : ℝ) / k := by positivity
  have hqm : 0 ≤ (q : ℝ) / ((q : ℝ) - 1 - k) := div_nonneg hq'.le (by linarith)
  have hd := minSum_distInt_ge_fract x
  rcases le_total (Int.fract x) (1 - Int.fract x) with h | h
  · rw [min_eq_left h] at hd
    have hc : (k : ℝ) / q ≤ Int.fract x := by
      rw [div_le_iff₀ hq']; linarith
    have := minSum_minInv_le_of_ge A x ((k : ℝ) / q) (by positivity) (hc.trans hd)
    rw [one_div_div] at this
    linarith
  · rw [min_eq_right h] at hd
    have hc : ((q : ℝ) - 1 - k) / q ≤ 1 - Int.fract x := by
      rw [div_le_iff₀ hq']; linarith
    have := minSum_minInv_le_of_ge A x (((q : ℝ) - 1 - k) / q) (by positivity) (hc.trans hd)
    rw [one_div_div] at this
    linarith

lemma minSum_bin_lt (q : ℕ) (hq : 1 ≤ q) (x : ℝ) : ⌊(q : ℝ) * Int.fract x⌋₊ < q := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hfr0 : 0 ≤ (q : ℝ) * Int.fract x := mul_nonneg hq'.le (Int.fract_nonneg x)
  rw [Nat.floor_lt hfr0]
  have := Int.fract_lt_one x
  nlinarith

/-- For small `t`, `‖tα‖ ≥ 1/(2q)`. -/
lemma minSum_small (α : ℝ) (a : ℤ) (q : ℕ) (hq : 1 ≤ q) (hcop : IsCoprime a q)
    (hα : |α - a / q| ≤ 1 / (q : ℝ) ^ 2) (t : ℕ) (ht1 : 1 ≤ t) (ht2 : 2 * t ≤ q) :
    1 / (2 * (q : ℝ)) ≤ distInt (t * α) := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  unfold distInt
  set n : ℤ := round ((t : ℝ) * α) with hn
  set z : ℤ := (t : ℤ) * a - n * q with hz
  have hz0 : z ≠ 0 := by
    intro h0
    have hd : (q : ℤ) ∣ (t : ℤ) * a := ⟨n, by linarith⟩
    have hd2 : (q : ℤ) ∣ (t : ℤ) := hcop.symm.dvd_of_dvd_mul_right hd
    have := Int.eq_zero_of_abs_lt_dvd hd2 (by rw [abs_of_nonneg (by positivity)]; omega)
    omega
  have hz1 : (1 : ℝ) ≤ |(z : ℝ)| := by
    have : (1 : ℤ) ≤ |z| := Int.one_le_abs hz0
    exact_mod_cast this
  have e : (t : ℝ) * α - n = (z : ℝ) / q + t * (α - a / q) := by
    simp only [hz]
    push_cast
    field_simp
    ring
  have h1 : (1 : ℝ) / q ≤ |(z : ℝ) / q| := by
    rw [abs_div, abs_of_pos hq']
    exact div_le_div_of_nonneg_right hz1 hq'.le
  have h2 : |(t : ℝ) * (α - a / q)| ≤ 1 / (2 * (q : ℝ)) := by
    rw [abs_mul, Nat.abs_cast]
    calc (t : ℝ) * |α - a / q| ≤ t * (1 / (q : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left hα (by positivity)
      _ ≤ 1 / (2 * (q : ℝ)) := by
          have ht : (2 : ℝ) * t ≤ q := by exact_mod_cast ht2
          rw [← mul_div_assoc, mul_one, div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith
  have h3 : |(z : ℝ) / q| ≤ |(t : ℝ) * α - n| + |(t : ℝ) * (α - a / q)| := by
    have : (z : ℝ) / q = ((t : ℝ) * α - n) - t * (α - a / q) := by rw [e]; ring
    rw [this]
    exact abs_sub _ _
  have h4 : 1 / (2 * (q : ℝ)) = 1 / q - 1 / (2 * q) := by
    field_simp
    ring
  linarith

lemma minSum_inj (a : ℤ) (q : ℕ) (hcop : IsCoprime a q) (h : ℕ) (t1 t2 : ℕ)
    (h1 : h * q + 1 ≤ t1 ∧ t1 ≤ h * q + q) (h2 : h * q + 1 ≤ t2 ∧ t2 ≤ h * q + q)
    (hd : (q : ℤ) ∣ ((t1 : ℤ) - t2) * a) : t1 = t2 := by
  have hd2 : (q : ℤ) ∣ ((t1 : ℤ) - t2) := hcop.symm.dvd_of_dvd_mul_right hd
  have := Int.eq_zero_of_abs_lt_dvd hd2 (by rw [abs_lt]; constructor <;> omega)
  omega

lemma minSum_same_bin (α : ℝ) (a : ℤ) (q : ℕ) (hq : 1 ≤ q)
    (hα : |α - a / q| ≤ 1 / (q : ℝ) ^ 2) (h : ℕ) (t1 t2 : ℕ)
    (h1 : h * q + 1 ≤ t1 ∧ t1 ≤ h * q + q) (h2 : h * q + 1 ≤ t2 ∧ t2 ≤ h * q + q)
    (hb : ⌊(q : ℝ) * Int.fract (t1 * α)⌋₊ = ⌊(q : ℝ) * Int.fract (t2 * α)⌋₊) :
    ∃ m : ℤ, |((t1 : ℤ) - t2) * a - m * q| ≤ 1 := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  obtain ⟨k, hk1⟩ : ∃ k, ⌊(q : ℝ) * Int.fract (t1 * α)⌋₊ = k := ⟨_, rfl⟩
  have hk2 : ⌊(q : ℝ) * Int.fract (t2 * α)⌋₊ = k := hb.symm.trans hk1
  have hf1 : 0 ≤ (q : ℝ) * Int.fract (t1 * α) := mul_nonneg hq'.le (Int.fract_nonneg _)
  have hf2 : 0 ≤ (q : ℝ) * Int.fract (t2 * α) := mul_nonneg hq'.le (Int.fract_nonneg _)
  have a1 : (k : ℝ) ≤ q * Int.fract (t1 * α) := by rw [← hk1]; exact Nat.floor_le hf1
  have a2 : (q : ℝ) * Int.fract (t1 * α) < k + 1 := by rw [← hk1]; exact Nat.lt_floor_add_one _
  have b1 : (k : ℝ) ≤ q * Int.fract (t2 * α) := by rw [← hk2]; exact Nat.floor_le hf2
  have b2 : (q : ℝ) * Int.fract (t2 * α) < k + 1 := by rw [← hk2]; exact Nat.lt_floor_add_one _
  refine ⟨⌊(t1 : ℝ) * α⌋ - ⌊(t2 : ℝ) * α⌋, ?_⟩
  set β := α - a / q with hβ
  have hd : |((t1 : ℝ) - t2)| ≤ (q : ℝ) - 1 := by
    rw [abs_le]
    have e1 : ((h * q + 1 : ℕ) : ℝ) ≤ t1 := by exact_mod_cast h1.1
    have e2 : (t1 : ℝ) ≤ ((h * q + q : ℕ) : ℝ) := by exact_mod_cast h1.2
    have e3 : ((h * q + 1 : ℕ) : ℝ) ≤ t2 := by exact_mod_cast h2.1
    have e4 : (t2 : ℝ) ≤ ((h * q + q : ℕ) : ℝ) := by exact_mod_cast h2.2
    push_cast at e1 e2 e3 e4
    constructor <;> linarith
  have hqb : |(q : ℝ) * ((t1 : ℝ) - t2) * β| < 1 := by
    have : |(q : ℝ) * ((t1 : ℝ) - t2) * β| ≤ q * ((q : ℝ) - 1) * (1 / (q : ℝ) ^ 2) := by
      rw [abs_mul, abs_mul, abs_of_pos hq']
      have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
      gcongr
    refine this.trans_lt ?_
    have e : (q : ℝ) * ((q : ℝ) - 1) * (1 / (q : ℝ) ^ 2) = ((q : ℝ) - 1) / q := by
      field_simp
    rw [e, div_lt_one hq']
    linarith
  have hE : ((((t1 : ℤ) - t2) * a - (⌊(t1 : ℝ) * α⌋ - ⌊(t2 : ℝ) * α⌋) * q : ℤ) : ℝ) =
      (q * Int.fract (t1 * α) - q * Int.fract (t2 * α)) - q * ((t1 : ℝ) - t2) * β := by
    simp only [Int.fract, hβ]
    push_cast
    field_simp
    ring
  have hlt : |((((t1 : ℤ) - t2) * a - (⌊(t1 : ℝ) * α⌋ - ⌊(t2 : ℝ) * α⌋) * q : ℤ) : ℝ)| < 2 := by
    rw [hE]
    rw [abs_lt] at hqb ⊢
    constructor <;> linarith
  have hlt' : |((t1 : ℤ) - t2) * a - (⌊(t1 : ℝ) * α⌋ - ⌊(t2 : ℝ) * α⌋) * q| < 2 := by
    exact_mod_cast hlt
  rw [abs_lt] at hlt'
  rw [abs_le]
  constructor <;> omega

lemma minSum_card_bin (α : ℝ) (a : ℤ) (q : ℕ) (hq : 1 ≤ q) (hcop : IsCoprime a q)
    (hα : |α - a / q| ≤ 1 / (q : ℝ) ^ 2) (h : ℕ) (S : Finset ℕ)
    (hS : ∀ t ∈ S, h * q + 1 ≤ t ∧ t ≤ h * q + q) (k : ℕ) :
    (S.filter (fun t : ℕ => ⌊(q : ℝ) * Int.fract (t * α)⌋₊ = k)).card ≤ 3 := by
  classical
  set F := S.filter (fun t : ℕ => ⌊(q : ℝ) * Int.fract (t * α)⌋₊ = k) with hF
  rcases F.eq_empty_or_nonempty with he | ⟨t0, ht0⟩
  · rw [he]; simp
  have ht0' := (Finset.mem_filter.mp ht0)
  set A := F.filter (fun t : ℕ => ∃ m : ℤ, ((t : ℤ) - t0) * a - m * q = 1) with hA
  set B := F.filter (fun t : ℕ => ∃ m : ℤ, ((t : ℤ) - t0) * a - m * q = -1) with hB
  have hsub : F ⊆ insert t0 (A ∪ B) := by
    intro t ht
    have ht' := Finset.mem_filter.mp ht
    by_cases htt : t = t0
    · simp [htt]
    · obtain ⟨m, hm⟩ := minSum_same_bin α a q hq hα h t t0 (hS t ht'.1) (hS t0 ht0'.1)
        (ht'.2.trans ht0'.2.symm)
      rw [abs_le] at hm
      have hne : ((t : ℤ) - t0) * a - m * q ≠ 0 := by
        intro h0
        apply htt
        exact minSum_inj a q hcop h t t0 (hS t ht'.1) (hS t0 ht0'.1) ⟨m, by linarith⟩
      have : ((t : ℤ) - t0) * a - m * q = 1 ∨ ((t : ℤ) - t0) * a - m * q = -1 := by omega
      simp only [mem_insert, mem_union, hA, hB, mem_filter]
      rcases this with h1 | h1
      · exact Or.inr (Or.inl ⟨ht, m, h1⟩)
      · exact Or.inr (Or.inr ⟨ht, m, h1⟩)
  have cA : A.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro x hx y hy
    obtain ⟨hxF, m1, hm1⟩ := Finset.mem_filter.mp hx
    obtain ⟨hyF, m2, hm2⟩ := Finset.mem_filter.mp hy
    exact minSum_inj a q hcop h x y (hS x (Finset.mem_filter.mp hxF).1)
      (hS y (Finset.mem_filter.mp hyF).1) ⟨m1 - m2, by linear_combination hm1 - hm2⟩
  have cB : B.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro x hx y hy
    obtain ⟨hxF, m1, hm1⟩ := Finset.mem_filter.mp hx
    obtain ⟨hyF, m2, hm2⟩ := Finset.mem_filter.mp hy
    exact minSum_inj a q hcop h x y (hS x (Finset.mem_filter.mp hxF).1)
      (hS y (Finset.mem_filter.mp hyF).1) ⟨m1 - m2, by linear_combination hm1 - hm2⟩
  calc F.card ≤ (insert t0 (A ∪ B)).card := Finset.card_le_card hsub
    _ ≤ (A ∪ B).card + 1 := Finset.card_insert_le _ _
    _ ≤ A.card + B.card + 1 := by
        have := Finset.card_union_le A B
        omega
    _ ≤ 3 := by omega

lemma minSum_block (α : ℝ) (a : ℤ) (q : ℕ) (hq : 1 ≤ q) (hcop : IsCoprime a q)
    (hα : |α - a / q| ≤ 1 / (q : ℝ) ^ 2) (N : ℝ) (h : ℕ) (S : Finset ℕ)
    (hS : ∀ t ∈ S, h * q + 1 ≤ t ∧ t ≤ h * q + q) (M : ℝ) (hM0 : 0 ≤ M)
    (hM : ∀ t ∈ S, minInv (N / t) (t * α) ≤ M) :
    ∑ t ∈ S, minInv (N / t) (t * α) ≤ 6 * M + 6 * q * (1 + Real.log q) := by
  classical
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  set bin : ℕ → ℕ := fun t => ⌊(q : ℝ) * Int.fract (t * α)⌋₊ with hbin
  set G := S.filter (fun t => 1 ≤ bin t ∧ bin t + 2 ≤ q) with hG
  rw [← Finset.sum_filter_add_sum_filter_not S (fun t => 1 ≤ bin t ∧ bin t + 2 ≤ q)]
  have hbad : ∑ t ∈ S.filter (fun t => ¬ (1 ≤ bin t ∧ bin t + 2 ≤ q)), minInv (N / t) (t * α)
      ≤ 6 * M := by
    set Bd := S.filter (fun t => ¬ (1 ≤ bin t ∧ bin t + 2 ≤ q)) with hBd
    have hsub : Bd ⊆ S.filter (fun t => bin t = 0) ∪ S.filter (fun t => bin t = q - 1) := by
      intro t ht
      obtain ⟨htS, htn⟩ := Finset.mem_filter.mp ht
      have := minSum_bin_lt q hq ((t : ℝ) * α)
      simp only [mem_union, mem_filter]
      have h2 : bin t < q := this
      by_cases h0 : bin t = 0
      · exact Or.inl ⟨htS, h0⟩
      · right
        refine ⟨htS, ?_⟩
        omega
    have c1 := minSum_card_bin α a q hq hcop hα h S hS 0
    have c2 := minSum_card_bin α a q hq hcop hα h S hS (q - 1)
    have hc : Bd.card ≤ 6 := by
      have := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
      simp only [hbin] at this ⊢
      omega
    calc ∑ t ∈ Bd, minInv (N / t) (t * α) ≤ ∑ t ∈ Bd, M :=
          Finset.sum_le_sum (fun t ht => hM t (Finset.mem_filter.mp ht).1)
      _ = Bd.card * M := by simp
      _ ≤ 6 * M := by
          apply mul_le_mul_of_nonneg_right _ hM0
          exact_mod_cast hc
  have hgood : ∑ t ∈ G, minInv (N / t) (t * α) ≤ 6 * q * (1 + Real.log q) := by
    set F : ℕ → ℝ := fun k => (q : ℝ) / k + (q : ℝ) / ((q : ℝ) - 1 - k) with hFdef
    have step1 : ∑ t ∈ G, minInv (N / t) (t * α) ≤ ∑ t ∈ G, F (bin t) := by
      apply Finset.sum_le_sum
      intro t ht
      obtain ⟨_, h1, h2⟩ := (Finset.mem_filter.mp ht)
      exact minSum_good (N / t) ((t : ℝ) * α) q (bin t) h1 h2 rfl
    refine step1.trans ?_
    rw [Finset.sum_comp]
    have hFnn : ∀ k ∈ Icc 1 (q - 2), 0 ≤ F k := by
      intro k hk
      simp only [mem_Icc] at hk
      have hkq : (k : ℝ) + 2 ≤ q := by exact_mod_cast (by omega : k + 2 ≤ q)
      simp only [hFdef]
      have : (0 : ℝ) ≤ (q : ℝ) / k := by positivity
      have : (0 : ℝ) ≤ (q : ℝ) / ((q : ℝ) - 1 - k) := div_nonneg hq'.le (by linarith)
      linarith
    calc ∑ b ∈ G.image bin, #{a ∈ G | bin a = b} • F b
        ≤ ∑ b ∈ G.image bin, (3 : ℝ) * F b := by
          apply Finset.sum_le_sum
          intro k hk
          have hkI : k ∈ Icc 1 (q - 2) := by
            obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hk
            obtain ⟨_, h1, h2⟩ := (Finset.mem_filter.mp ht)
            simp only [mem_Icc]
            omega
          have hc : (G.filter (fun a => bin a = k)).card ≤ 3 := by
            refine le_trans (Finset.card_le_card ?_) (minSum_card_bin α a q hq hcop hα h S hS k)
            intro t ht
            simp only [mem_filter, hG] at ht ⊢
            exact ⟨ht.1.1, ht.2⟩
          rw [nsmul_eq_mul]
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (hFnn k hkI)
      _ ≤ ∑ b ∈ Icc 1 (q - 2), (3 : ℝ) * F b := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro k hk
            obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hk
            obtain ⟨_, h1, h2⟩ := (Finset.mem_filter.mp ht)
            simp only [mem_Icc]
            omega
          · intro k hk _
            exact mul_nonneg (by norm_num) (hFnn k hk)
      _ = 3 * ∑ b ∈ Icc 1 (q - 2), F b := by rw [Finset.mul_sum]
      _ ≤ 6 * q * (1 + Real.log q) := by
          have := minSum_bins_sum q hq
          simp only [hFdef]
          linarith
  linarith

lemma minSum_blockM (α : ℝ) (a : ℤ) (q : ℕ) (hq : 1 ≤ q) (hcop : IsCoprime a q)
    (hα : |α - a / q| ≤ 1 / (q : ℝ) ^ 2) (N : ℝ) (hN : 0 ≤ N) (h : ℕ) (S : Finset ℕ)
    (hS : ∀ t ∈ S, h * q + 1 ≤ t ∧ t ≤ h * q + q) :
    ∑ t ∈ S, minInv (N / t) (t * α) ≤
      6 * (if h = 0 then 2 * (q : ℝ) + 2 * N / q else N / (h * q)) +
        6 * q * (1 + Real.log q) := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hNq : 0 ≤ N / q := div_nonneg hN hq'.le
  by_cases h0 : h = 0
  · subst h0
    simp only [ite_true]
    apply minSum_block α a q hq hcop hα N 0 S hS
    · positivity
    · intro t ht
      obtain ⟨ht1, ht2⟩ := hS t ht
      simp only [zero_mul, zero_add] at ht1 ht2
      have htpos : (0 : ℝ) < t := by exact_mod_cast ht1
      by_cases hsm : 2 * t ≤ q
      · have := minSum_minInv_le_of_ge (N / t) ((t : ℝ) * α) (1 / (2 * (q : ℝ)))
          (by positivity) (minSum_small α a q hq hcop hα t ht1 hsm)
        rw [one_div_one_div] at this
        have : 0 ≤ 2 * N / (q : ℝ) := by positivity
        linarith
      · have hq2 : (q : ℝ) ≤ 2 * t := by exact_mod_cast (by omega : q ≤ 2 * t)
        have h1 := minSum_minInv_le_A (N / t) ((t : ℝ) * α)
        have h2 : N / t ≤ 2 * N / q := by
          rw [div_le_div_iff₀ htpos hq']
          nlinarith
        have : 0 ≤ 2 * (q : ℝ) := by positivity
        linarith
  · simp only [h0, ite_false]
    have hh : (1 : ℝ) ≤ h := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr h0
    have hhq : (0 : ℝ) < h * q := by positivity
    apply minSum_block α a q hq hcop hα N h S hS
    · positivity
    · intro t ht
      obtain ⟨ht1, _⟩ := hS t ht
      have : ((h : ℝ) * q) ≤ t := by exact_mod_cast (by omega : h * q ≤ t)
      exact (minSum_minInv_le_A _ _).trans (div_le_div_of_nonneg_left hN hhq this)

/-- **Davenport, Chapter 25, p. 154, (3)**: if `|α - a/q| ≤ q⁻²` with `(a, q) = 1` then
`∑_{t ≤ T} min(N/t, 1/‖tα‖) ≪ (N/q + T + q) log (2qT)`. -/
@[kb "davenport1980" "Ch 25, p. 154, (3)"]
theorem sum_minInv_le : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (a : ℤ) (q : ℕ), 1 ≤ q → IsCoprime a q →
    |α - a / q| ≤ 1 / (q : ℝ) ^ 2 → ∀ (N : ℝ) (T : ℕ), 1 ≤ N → 1 ≤ T →
    ∑ t ∈ Icc 1 T, minInv (N / t) (t * α) ≤
      C * (N / q + T + q) * Real.log (2 * q * T) := by
  classical
  refine ⟨50, by norm_num, ?_⟩
  intro α a q hq hcop hα N T hN1 hT
  have hN : 0 ≤ N := by linarith
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hT' : (1 : ℝ) ≤ T := by exact_mod_cast hT
  set K : ℝ := 6 * q * (1 + Real.log q) with hK
  set Mh : ℕ → ℝ := fun h => if h = 0 then 2 * (q : ℝ) + 2 * N / q else N / (h * q) with hMh
  set H := T / q with hH
  have hmaps : ∀ t ∈ Icc 1 T, (fun t : ℕ => (t - 1) / q) t ∈ range (H + 1) := by
    intro t ht
    simp only [mem_Icc] at ht
    simp only [mem_range]
    exact Nat.lt_succ_of_le (Nat.div_le_div_right (by omega))
  have hfib := Finset.sum_fiberwise_of_maps_to hmaps (fun t => minInv (N / t) (t * α))
  rw [← hfib]
  have hbl : ∑ h ∈ range (H + 1), ∑ t ∈ (Icc 1 T).filter (fun t => (t - 1) / q = h),
      minInv (N / t) (t * α) ≤ ∑ h ∈ range (H + 1), (6 * Mh h + K) := by
    apply Finset.sum_le_sum
    intro h _
    apply minSum_blockM α a q hq hcop hα N hN h
    intro t ht
    obtain ⟨ht1, hth⟩ := Finset.mem_filter.mp ht
    simp only [mem_Icc] at ht1
    have e1 := Nat.div_add_mod (t - 1) q
    have e2 := Nat.mod_lt (t - 1) hq
    rw [hth] at e1
    rw [Nat.mul_comm h q]
    constructor
    · generalize q * h = P at *
      omega
    · generalize q * h = P at *
      omega
  refine hbl.trans ?_
  have e1 : ∀ i : ℕ, 6 * Mh (i + 1) + K = 6 * ((N / q) * (1 / ((i : ℝ) + 1))) + K := by
    intro i
    simp only [hMh, Nat.succ_ne_zero, ite_false]
    push_cast
    field_simp
  rw [Finset.sum_range_succ', Finset.sum_congr rfl (fun i _ => e1 i), Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum]
  simp only [hMh, ite_true]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  -- the harmonic sum
  have hharm : ∑ i ∈ range H, (1 : ℝ) / ((i : ℝ) + 1) ≤ 1 + Real.log T := by
    refine (minSum_harm_range H).trans ?_
    rcases Nat.eq_zero_or_pos H with h0 | h0
    · rw [h0]; simp only [Nat.cast_zero, Real.log_zero]
      have := Real.log_nonneg hT'
      linarith
    · have : Real.log (H : ℝ) ≤ Real.log T := by
        apply Real.log_le_log (by exact_mod_cast h0)
        exact_mod_cast Nat.div_le_self T q
      linarith
  have hHle : (H : ℝ) ≤ T / q := by
    rw [hH]; exact Nat.cast_div_le
  have hlogq : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq)
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg hT'
  have hL : Real.log (2 * q * T) = Real.log 2 + Real.log q + Real.log T := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by norm_num) (by positivity)]
  have hlog2 : (1 : ℝ) / 2 ≤ Real.log 2 := by
    have := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at this ⊢
    linarith
  set L := Real.log (2 * q * T) with hLdef
  have hL1 : 1 ≤ 2 * L := by rw [hL]; linarith
  have hX : 0 ≤ N / (q : ℝ) := div_nonneg hN hq'.le
  have hL0 : 0 ≤ L := by linarith
  have hK1 : (H + 1 : ℝ) * K ≤ 6 * (T + q) * (1 + Real.log q) := by
    have : (H + 1 : ℝ) ≤ T / q + 1 := by linarith
    have hKn : 0 ≤ K := by rw [hK]; positivity
    calc (H + 1 : ℝ) * K ≤ (T / q + 1) * K := mul_le_mul_of_nonneg_right this hKn
      _ = 6 * (T + q) * (1 + Real.log q) := by rw [hK]; field_simp
  have f1 : 6 * (N / (q : ℝ)) * (1 + Real.log T) ≤ 6 * (N / (q : ℝ)) * (3 * L) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [hL]; linarith
  have f2 : 6 * (N / (q : ℝ)) * ∑ i ∈ range H, (1 : ℝ) / ((i : ℝ) + 1) ≤
      6 * (N / (q : ℝ)) * (1 + Real.log T) :=
    mul_le_mul_of_nonneg_left hharm (by positivity)
  have f3 : 6 * (T + q : ℝ) * (1 + Real.log q) ≤ 6 * (T + q : ℝ) * (3 * L) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [hL]; linarith
  have f4 : 12 * (q : ℝ) ≤ 12 * q * (2 * L) :=
    le_mul_of_one_le_right (by positivity) hL1
  have f5 : 12 * (N / (q : ℝ)) ≤ 12 * (N / q) * (2 * L) :=
    le_mul_of_one_le_right (by positivity) hL1
  have g1 : 0 ≤ N / (q : ℝ) * L := mul_nonneg hX hL0
  have g2 : 0 ≤ (T : ℝ) * L := mul_nonneg (by positivity) hL0
  have g3 : 0 ≤ (q : ℝ) * L := mul_nonneg hq'.le hL0
  have e3 : 6 * (2 * (q : ℝ) + 2 * N / q) = 12 * q + 12 * (N / q) := by ring
  nlinarith [f1, f2, f3, f4, f5, g1, g2, g3, hK1, e3]

end NTKB.Davenport
