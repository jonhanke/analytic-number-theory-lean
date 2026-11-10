/- Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license. -/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Log
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Dyadic decomposition (Davenport, Multiplicative Number Theory, ch. 29, p. 171)

If the partial sums of nonnegative `a_d` satisfy `∑_{d ≤ y} a_d ≤ (X + 3y²) K` for all real
`y ≥ 1`, then for integers `1 ≤ Q₁ ≤ Q`,
`∑_{Q₁ < d ≤ Q} (1 + log(Q/d)) a_d / d ≪ K (X (1 + log(Q/Q₁)) / Q₁ + Q)`.

The proof splits `(Q₁, Q]` into the blocks `2^j d ≤ Q < 2^(j+1) d`, `j ≤ p`, where
`p = ⌊log₂ ⌊Q/Q₁⌋⌋`.  The absolute constant obtained is `40`.
-/

namespace NTKB.Davenport

open Finset Real

lemma sum_succ_two_mul_pow_le (n : ℕ) :
    ∑ j ∈ range n, ((j : ℝ) + 2) * 2 ^ (j + 1) ≤ ((n : ℝ) + 1) * 2 ^ (n + 1) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [sum_range_succ]
    have h : (0 : ℝ) < 2 ^ (n + 1) := by positivity
    have h2 : (2 : ℝ) ^ (n + 1 + 1) = 2 * 2 ^ (n + 1) := by ring
    push_cast
    rw [h2]
    nlinarith

lemma sum_two_div_pow_le (n : ℕ) :
    ∑ j ∈ range n, ((j : ℝ) + 2) / 2 ^ j ≤ 6 := by
  have key : ∀ n : ℕ, ∑ j ∈ range n, ((j : ℝ) + 2) / 2 ^ j + 2 * ((n : ℝ) + 3) / 2 ^ n = 6 := by
    intro n
    induction n with
    | zero => norm_num
    | succ n ih =>
      rw [sum_range_succ]
      push_cast
      have e : ((n : ℝ) + 2) / 2 ^ n + 2 * ((n : ℝ) + 1 + 3) / 2 ^ (n + 1)
          = 2 * ((n : ℝ) + 3) / 2 ^ n := by
        rw [pow_succ]; field_simp; ring
      linarith
  have := key n
  have h : 0 ≤ 2 * ((n : ℝ) + 3) / 2 ^ n := by positivity
  linarith

lemma cover_le (f : ℕ → ℝ) (Q₁ Q p : ℕ) (hf : ∀ d ∈ Ioc Q₁ Q, 0 ≤ f d)
    (hQJ : Q ≤ 2 ^ (p + 1) * Q₁) :
    ∑ d ∈ Ioc Q₁ Q, f d ≤ ∑ j ∈ range (p + 1),
      ∑ d ∈ (Ioc Q₁ Q).filter (fun d => 2 ^ j * d ≤ Q ∧ Q < 2 ^ (j + 1) * d), f d := by
  simp_rw [sum_filter]
  rw [sum_comm]
  apply sum_le_sum
  intro d hd
  have hd' := mem_Ioc.1 hd
  have hd0 : 0 < d := lt_of_le_of_lt (Nat.zero_le _) hd'.1
  have hne : Q / d ≠ 0 := (Nat.div_pos hd'.2 hd0).ne'
  have h1 : 2 ^ Nat.log 2 (Q / d) ≤ Q / d := Nat.pow_log_le_self 2 hne
  have h2 : Q / d < 2 ^ (Nat.log 2 (Q / d) + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  have c1 : 2 ^ Nat.log 2 (Q / d) * d ≤ Q :=
    (Nat.mul_le_mul_right d h1).trans (Nat.div_mul_le_self Q d)
  have c2 : Q < 2 ^ (Nat.log 2 (Q / d) + 1) * d := (Nat.div_lt_iff_lt_mul hd0).1 h2
  have hj0 : Nat.log 2 (Q / d) < p + 1 := by
    by_contra hcon
    have hge : p + 1 ≤ Nat.log 2 (Q / d) := not_lt.1 hcon
    have h3 : 2 ^ (p + 1) ≤ 2 ^ Nat.log 2 (Q / d) := Nat.pow_le_pow_right (by norm_num) hge
    have h4 : 2 ^ (p + 1) * d ≤ Q := (Nat.mul_le_mul_right d h3).trans c1
    have h5 : 2 ^ (p + 1) * Q₁ < 2 ^ (p + 1) * d :=
      Nat.mul_lt_mul_of_pos_left hd'.1 (by positivity)
    omega
  calc f d = (if 2 ^ Nat.log 2 (Q / d) * d ≤ Q ∧ Q < 2 ^ (Nat.log 2 (Q / d) + 1) * d
        then f d else 0) := (if_pos ⟨c1, c2⟩).symm
    _ ≤ _ := by
      refine single_le_sum (f := fun j => if 2 ^ j * d ≤ Q ∧ Q < 2 ^ (j + 1) * d
        then f d else 0) ?_ (mem_range.2 hj0)
      intro j _
      split_ifs
      · exact hf d hd
      · exact le_rfl

lemma block_le (a : ℕ → ℝ) (ha : ∀ d, 0 ≤ a d) (Q₁ Q j : ℕ) (hQ : 0 < Q) :
    ∑ d ∈ (Ioc Q₁ Q).filter (fun d => 2 ^ j * d ≤ Q ∧ Q < 2 ^ (j + 1) * d),
      (1 + Real.log ((Q : ℝ) / d)) / d * a d ≤
    ((j : ℝ) + 2) * 2 ^ (j + 1) / Q * ∑ d ∈ Icc 1 ⌊(Q : ℝ) / 2 ^ j⌋₊, a d := by
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
  calc _ ≤ ∑ d ∈ (Ioc Q₁ Q).filter (fun d => 2 ^ j * d ≤ Q ∧ Q < 2 ^ (j + 1) * d),
        ((j : ℝ) + 2) * 2 ^ (j + 1) / Q * a d := by
        apply sum_le_sum
        intro d hd
        rw [mem_filter, mem_Ioc] at hd
        obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hd
        have hd0 : 0 < d := lt_of_le_of_lt (Nat.zero_le _) h1
        have hdr : (0 : ℝ) < d := by exact_mod_cast hd0
        have h4r : (Q : ℝ) < 2 ^ (j + 1) * d := by exact_mod_cast h4
        apply mul_le_mul_of_nonneg_right _ (ha d)
        have hj1 : (0 : ℝ) ≤ (j : ℝ) + 1 := by positivity
        have hlog : Real.log ((Q : ℝ) / d) ≤ j + 1 := by
          have h6 : Real.log ((Q : ℝ) / d) ≤ Real.log ((2 : ℝ) ^ (j + 1)) := by
            apply Real.log_le_log (div_pos hQr hdr)
            rw [div_le_iff₀ hdr]; exact h4r.le
          rw [Real.log_pow] at h6
          have h7 := Real.log_two_lt_d9
          push_cast at h6
          nlinarith [mul_le_mul_of_nonneg_left h7.le hj1]
        calc (1 + Real.log ((Q : ℝ) / d)) / d ≤ ((j : ℝ) + 2) / d := by
              exact div_le_div_of_nonneg_right (by linarith) hdr.le
          _ ≤ _ := by
              rw [div_le_div_iff₀ hdr hQr]
              have h8 : (0 : ℝ) ≤ (j : ℝ) + 2 := by positivity
              nlinarith [mul_le_mul_of_nonneg_left h4r.le h8]
    _ = _ := by rw [← mul_sum]
    _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply sum_le_sum_of_subset_of_nonneg
        · intro d hd
          rw [mem_filter, mem_Ioc] at hd
          obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hd
          rw [mem_Icc]
          refine ⟨by omega, Nat.le_floor ?_⟩
          rw [le_div_iff₀ (by positivity)]
          have h5 : ((2 ^ j * d : ℕ) : ℝ) ≤ Q := by exact_mod_cast h3
          push_cast at h5; linarith
        · intros; exact ha _

/-- Dyadic decomposition: if the partial sums of the nonnegative `a_d` satisfy
`∑_{d ≤ y} a_d ≤ (X + 3y²) K` for all real `y ≥ 1`, then for integers `1 ≤ Q₁ ≤ Q`,
`∑_{Q₁ < d ≤ Q} (1 + log(Q/d)) a_d / d ≪ K (X (1 + log(Q/Q₁)) / Q₁ + Q)`. -/
theorem sum_dyadic_le : ∃ C : ℝ, 0 < C ∧ ∀ (a : ℕ → ℝ), (∀ d, 0 ≤ a d) → ∀ (X K : ℝ), 0 ≤ X → 0 ≤ K →
    (∀ y : ℝ, 1 ≤ y → ∑ d ∈ Icc 1 ⌊y⌋₊, a d ≤ (X + 3 * y ^ 2) * K) →
    ∀ Q₁ Q : ℕ, 1 ≤ Q₁ → Q₁ ≤ Q →
    ∑ d ∈ Ioc Q₁ Q, (1 + Real.log ((Q : ℝ) / d)) / d * a d ≤
      C * K * (X * (1 + Real.log ((Q : ℝ) / Q₁)) / Q₁ + Q) := by
  refine ⟨40, by norm_num, ?_⟩
  intro a ha X K hX hK hS Q₁ Q hQ₁ hQQ₁
  have hQ0 : 0 < Q := lt_of_lt_of_le hQ₁ hQQ₁
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ0
  have hQ₁r : (0 : ℝ) < Q₁ := by exact_mod_cast hQ₁
  have hm1 : Q / Q₁ ≠ 0 := (Nat.div_pos hQQ₁ hQ₁).ne'
  obtain ⟨p, hp⟩ : ∃ p, p = Nat.log 2 (Q / Q₁) := ⟨_, rfl⟩
  have hpm : 2 ^ p ≤ Q / Q₁ := hp ▸ Nat.pow_log_le_self 2 hm1
  have hmp : Q / Q₁ < 2 ^ (p + 1) := hp ▸ Nat.lt_pow_succ_log_self (by norm_num) (Q / Q₁)
  have hQJ : Q ≤ 2 ^ (p + 1) * Q₁ := by
    have h1 : Q < Q₁ * (Q / Q₁ + 1) := Nat.lt_mul_div_succ Q hQ₁
    have h2 : Q / Q₁ + 1 ≤ 2 ^ (p + 1) := hmp
    nlinarith
  have hpQ : 2 ^ p * Q₁ ≤ Q :=
    (Nat.mul_le_mul_right _ hpm).trans (Nat.div_mul_le_self Q Q₁)
  have hpQr : (2 : ℝ) ^ p * Q₁ ≤ Q := by exact_mod_cast hpQ
  have hL0 : 0 ≤ Real.log ((Q : ℝ) / Q₁) :=
    Real.log_nonneg ((one_le_div hQ₁r).2 (by exact_mod_cast hQQ₁))
  have hpL : (p : ℝ) ≤ 2 * Real.log ((Q : ℝ) / Q₁) := by
    have h2 : (2 : ℝ) ^ p ≤ Q / Q₁ := by rw [le_div_iff₀ hQ₁r]; exact hpQr
    have h3 := Real.log_le_log (by positivity) h2
    rw [Real.log_pow] at h3
    have hl2 := Real.log_two_gt_d9
    nlinarith [Nat.cast_nonneg (α := ℝ) p]
  have hf0 : ∀ d ∈ Ioc Q₁ Q, 0 ≤ (1 + Real.log ((Q : ℝ) / d)) / d * a d := by
    intro d hd
    rw [mem_Ioc] at hd
    have hdr : (0 : ℝ) < d := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le _) hd.1)
    have : 0 ≤ Real.log ((Q : ℝ) / d) :=
      Real.log_nonneg ((one_le_div hdr).2 (by exact_mod_cast hd.2))
    exact mul_nonneg (div_nonneg (by linarith) hdr.le) (ha d)
  calc ∑ d ∈ Ioc Q₁ Q, (1 + Real.log ((Q : ℝ) / d)) / d * a d
      ≤ _ := cover_le (fun d => (1 + Real.log ((Q : ℝ) / d)) / d * a d) Q₁ Q p hf0 hQJ
    _ ≤ ∑ j ∈ range (p + 1), (K * X / Q * (((j : ℝ) + 2) * 2 ^ (j + 1))
          + 6 * Q * K * (((j : ℝ) + 2) / 2 ^ j)) := by
      apply sum_le_sum
      intro j hj
      have hj' : j ≤ p := Nat.lt_succ_iff.1 (mem_range.1 hj)
      refine (block_le a ha Q₁ Q j hQ0).trans ?_
      have h2j : (2 : ℝ) ^ j ≤ Q := by
        calc (2 : ℝ) ^ j ≤ 2 ^ p := pow_le_pow_right₀ (by norm_num) hj'
          _ ≤ 2 ^ p * Q₁ := le_mul_of_one_le_right (by positivity) (by exact_mod_cast hQ₁)
          _ ≤ Q := hpQr
      have h1y : 1 ≤ (Q : ℝ) / 2 ^ j := (one_le_div (by positivity)).2 h2j
      have hc : 0 ≤ ((j : ℝ) + 2) * 2 ^ (j + 1) / Q := by positivity
      calc _ ≤ ((j : ℝ) + 2) * 2 ^ (j + 1) / Q * ((X + 3 * ((Q : ℝ) / 2 ^ j) ^ 2) * K) :=
            mul_le_mul_of_nonneg_left (hS _ h1y) hc
        _ = _ := by rw [div_pow, pow_succ]; field_simp; ring
    _ = K * X / Q * ∑ j ∈ range (p + 1), (((j : ℝ) + 2) * 2 ^ (j + 1))
          + 6 * Q * K * ∑ j ∈ range (p + 1), (((j : ℝ) + 2) / 2 ^ j) := by
      rw [sum_add_distrib, ← mul_sum, ← mul_sum]
    _ ≤ K * X / Q * ((((p + 1 : ℕ) : ℝ) + 1) * 2 ^ (p + 1 + 1)) + 6 * Q * K * 6 :=
      add_le_add (mul_le_mul_of_nonneg_left (sum_succ_two_mul_pow_le _) (by positivity))
        (mul_le_mul_of_nonneg_left (sum_two_div_pow_le _) (by positivity))
    _ ≤ _ := by
      have c1 : (((p + 1 : ℕ) : ℝ) + 1) = p + 2 := by push_cast; ring
      have c2 : (2 : ℝ) ^ (p + 1 + 1) = 4 * 2 ^ p := by ring
      rw [c1, c2]
      set L := Real.log ((Q : ℝ) / Q₁) with hL
      have hKX : 0 ≤ K * X := mul_nonneg hK hX
      have part1 : K * X / Q * (((p : ℝ) + 2) * (4 * 2 ^ p)) ≤ 8 * K * (X * (1 + L) / Q₁) := by
        have e1 : K * X / Q * (((p : ℝ) + 2) * (4 * 2 ^ p))
            = (K * X * (((p : ℝ) + 2) * (4 * 2 ^ p))) / Q := by ring
        have e2 : 8 * K * (X * (1 + L) / Q₁) = (8 * K * X * (1 + L)) / Q₁ := by ring
        rw [e1, e2, div_le_div_iff₀ hQr hQ₁r]
        have h5 : K * X * (((p : ℝ) + 2) * (4 * 2 ^ p)) * Q₁
            = (K * X * (4 * ((p : ℝ) + 2))) * (2 ^ p * Q₁) := by ring
        have h6 : 8 * K * X * (1 + L) * Q = (K * X * (8 * (1 + L))) * Q := by ring
        rw [h5, h6]
        have h7 : K * X * (4 * ((p : ℝ) + 2)) ≤ K * X * (8 * (1 + L)) :=
          mul_le_mul_of_nonneg_left (by linarith) hKX
        exact mul_le_mul h7 hpQr (by positivity) (mul_nonneg hKX (by linarith))
      have h8 : 0 ≤ K * (X * (1 + L) / Q₁) :=
        mul_nonneg hK (div_nonneg (mul_nonneg hX (by linarith)) hQ₁r.le)
      have h9 : 0 ≤ K * Q := mul_nonneg hK hQr.le
      nlinarith

end NTKB.Davenport
