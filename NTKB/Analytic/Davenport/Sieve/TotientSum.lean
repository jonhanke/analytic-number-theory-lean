import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.Data.Finset.NatDivisors
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.Harmonic.Bounds

/- Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license. -/

/-!
# Sums of reciprocals of the totient

Three elementary facts used in the large sieve chapter:

* `φ(a) φ(b) ≤ φ(ab)`;
* `∑_{k ≤ K} 1/φ(kd) ≤ (1/φ(d)) ∑_{k ≤ K} 1/φ(k)`;
* `∑_{k ≤ K} 1/φ(k) ≪ 1 + log K`.

The last one uses `k/φ(k) ≤ ∑_{d ∣ k} 1/φ(d)` (proved multiplicatively), a divisor-sum
interchange lemma, and the bound `∑_{d ≤ K} 1/(d φ(d)) ≤ 4`.
-/

namespace NTKB.Davenport

open Finset Real

/-- `φ(a) φ(b) ≤ φ(ab)`. -/
theorem totient_mul_totient_le (a b : ℕ) : a.totient * b.totient ≤ (a * b).totient :=
  Nat.totient_super_multiplicative a b

/-- `∑_{k ≤ z} 1/φ(kd) ≤ (1/φ(d)) ∑_{k ≤ z} 1/φ(k)` for `d ≥ 1`. -/
theorem sum_inv_totient_mul_le {d : ℕ} (hd : 0 < d) (K : ℕ) :
    ∑ k ∈ Icc 1 K, (1 : ℝ) / (k * d).totient ≤ 1 / d.totient * ∑ k ∈ Icc 1 K, (1 : ℝ) / k.totient := by
  rw [mul_sum]
  apply sum_le_sum
  intro k hk
  have hk1 : 0 < k := (mem_Icc.1 hk).1
  have h1 : 0 < k.totient := Nat.totient_pos.2 hk1
  have h2 : 0 < d.totient := Nat.totient_pos.2 hd
  have h3 : ((k.totient * d.totient : ℕ) : ℝ) ≤ ((k * d).totient : ℕ) := by
    exact_mod_cast totient_mul_totient_le k d
  have h4 : (0 : ℝ) < ((k.totient * d.totient : ℕ) : ℝ) := by exact_mod_cast Nat.mul_pos h1 h2
  calc (1 : ℝ) / ((k * d).totient : ℕ) ≤ 1 / ((k.totient * d.totient : ℕ) : ℝ) :=
        one_div_le_one_div_of_le h4 h3
    _ = 1 / d.totient * (1 / k.totient) := by push_cast; field_simp

/-- Multiplicativity of `∑_{x ∣ n} 1/φ(x)`. -/
lemma sum_divisors_inv_totient_mul {a b : ℕ} (h : a.Coprime b) :
    ∑ x ∈ (a * b).divisors, (1 : ℝ) / x.totient
      = (∑ x ∈ a.divisors, (1 : ℝ) / x.totient) * ∑ x ∈ b.divisors, (1 : ℝ) / x.totient := by
  rw [Nat.divisors_mul, ← Finset.image_mul_product,
    sum_image (fun p hp q hq hpq => h.mul_injOn_divisors hp hq hpq), sum_mul_sum, sum_product]
  apply sum_congr rfl
  intro d hd
  apply sum_congr rfl
  intro e he
  have hc : d.Coprime e :=
    (h.coprime_dvd_left (Nat.dvd_of_mem_divisors hd)).coprime_dvd_right
      (Nat.dvd_of_mem_divisors he)
  simp only [Nat.totient_mul hc]
  push_cast
  rw [one_div_mul_one_div]

/-- `k/φ(k) ≤ ∑_{d ∣ k} 1/φ(d)`. -/
lemma div_totient_le_sum (k : ℕ) :
    (k : ℝ) / k.totient ≤ ∑ d ∈ k.divisors, (1 : ℝ) / d.totient := by
  induction k using Nat.recOnPosPrimePosCoprime with
  | zero => simp
  | one => simp
  | prime_pow p n hp hn =>
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    have hpm : (0 : ℝ) < p - 1 := by linarith
    have ht : ((p ^ (m + 1)).totient : ℝ) = p ^ m * (p - 1) := by
      rw [Nat.totient_prime_pow hp (by omega)]
      simp only [Nat.add_sub_cancel]
      rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_sub hp.one_lt.le]; simp
    rw [Nat.sum_divisors_prime_pow hp, ht, Finset.sum_range_succ']
    have h0 : (1 : ℝ) / ((p ^ (0 + 1)).totient : ℕ) ≤
        ∑ i ∈ range (m + 1), (1 : ℝ) / ((p ^ (i + 1)).totient : ℕ) :=
      Finset.single_le_sum (f := fun i => (1 : ℝ) / ((p ^ (i + 1)).totient : ℕ))
        (fun i _ => by positivity) (by simp)
    have h1 : (1 : ℝ) / ((p ^ (0 + 1)).totient : ℕ) = 1 / (p - 1) := by
      simp [Nat.totient_prime hp, Nat.cast_sub hp.one_lt.le]
    have h2 : ((p ^ (m + 1) : ℕ) : ℝ) / (p ^ m * (p - 1)) = 1 + 1 / (p - 1) := by
      push_cast
      field_simp
      ring
    rw [h2]
    simp only [pow_zero, Nat.totient_one, Nat.cast_one, div_one]
    linarith
  | coprime a b ha hb hab iha ihb =>
    rw [sum_divisors_inv_totient_mul hab, Nat.totient_mul hab]
    push_cast
    rw [mul_div_mul_comm]
    exact mul_le_mul iha ihb (by positivity) (le_trans (by positivity) iha)

/-- Interchange of summation for divisor sums. -/
lemma sum_mul_divisors_le (c w : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n) (hw : ∀ n, 0 ≤ w n)
    (hcm : ∀ d m, 0 < d → 0 < m → c (d * m) ≤ c d * c m) (K : ℕ) :
    ∑ k ∈ Icc 1 K, c k * ∑ d ∈ k.divisors, w d
      ≤ (∑ d ∈ Icc 1 K, w d * c d) * ∑ m ∈ Icc 1 K, c m := by
  have step1 : ∑ k ∈ Icc 1 K, c k * ∑ d ∈ k.divisors, w d
      = ∑ d ∈ Icc 1 K, ∑ k ∈ (Icc 1 K).filter (d ∣ ·), c k * w d := by
    simp_rw [mul_sum]
    apply Finset.sum_comm'
    intro k d
    simp only [mem_Icc, Nat.mem_divisors, mem_filter]
    constructor
    · rintro ⟨⟨hk1, hk2⟩, hdk, hk0⟩
      have := Nat.le_of_dvd (by omega) hdk
      have := Nat.pos_of_dvd_of_pos hdk (by omega)
      exact ⟨⟨⟨hk1, hk2⟩, hdk⟩, by omega, by omega⟩
    · rintro ⟨⟨⟨hk1, hk2⟩, hdk⟩, _, _⟩
      exact ⟨⟨hk1, hk2⟩, hdk, by omega⟩
  rw [step1, sum_mul]
  apply sum_le_sum
  intro d hd
  have hd1 : 0 < d := (mem_Icc.1 hd).1
  have inner : ∑ k ∈ (Icc 1 K).filter (d ∣ ·), c k ≤ c d * ∑ m ∈ Icc 1 K, c m := by
    calc ∑ k ∈ (Icc 1 K).filter (d ∣ ·), c k
        ≤ ∑ k ∈ (Icc 1 K).filter (d ∣ ·), c d * c (k / d) := by
          apply sum_le_sum
          intro k hk
          obtain ⟨hk1, hdk⟩ := mem_filter.1 hk
          have hk0 : 0 < k := (mem_Icc.1 hk1).1
          have hq : 0 < k / d := Nat.div_pos (Nat.le_of_dvd hk0 hdk) hd1
          have := hcm d (k / d) hd1 hq
          rwa [Nat.mul_div_cancel' hdk] at this
      _ = c d * ∑ k ∈ (Icc 1 K).filter (d ∣ ·), c (k / d) := by rw [mul_sum]
      _ = c d * ∑ m ∈ ((Icc 1 K).filter (d ∣ ·)).image (· / d), c m := by
          rw [sum_image]
          intro x hx y hy hxy
          exact (Nat.div_left_inj (mem_filter.1 hx).2 (mem_filter.1 hy).2).1 hxy
      _ ≤ c d * ∑ m ∈ Icc 1 K, c m := by
          apply mul_le_mul_of_nonneg_left _ (hc d)
          apply sum_le_sum_of_subset_of_nonneg
          · intro m hm
            obtain ⟨k, hk, rfl⟩ := mem_image.1 hm
            obtain ⟨hk1, hdk⟩ := mem_filter.1 hk
            obtain ⟨hk2, hk3⟩ := mem_Icc.1 hk1
            have hq : 0 < k / d := Nat.div_pos (Nat.le_of_dvd (by omega) hdk) hd1
            exact mem_Icc.2 ⟨hq, (Nat.div_le_self k d).trans hk3⟩
          · intro i _ _; exact hc i
  have : ∑ k ∈ (Icc 1 K).filter (d ∣ ·), c k * w d
      = w d * ∑ k ∈ (Icc 1 K).filter (d ∣ ·), c k := by
    rw [← sum_mul, mul_comm]
  rw [this, mul_assoc]
  exact mul_le_mul_of_nonneg_left inner (hw d)

lemma sum_inv_sq_le (K : ℕ) : ∑ m ∈ Icc 1 K, (1 : ℝ) / (m : ℝ) ^ 2 ≤ 2 := by
  rcases Nat.eq_zero_or_pos K with rfl | hK
  · simp
  have : ∀ K : ℕ, 1 ≤ K → ∑ m ∈ Icc 1 K, (1 : ℝ) / (m : ℝ) ^ 2 ≤ 2 - 1 / K := by
    intro K hK
    induction K, hK using Nat.le_induction with
    | base => norm_num
    | succ n hn ih =>
      rw [Finset.sum_Icc_succ_top (by omega)]
      have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have h : (1 : ℝ) / ((n : ℝ) + 1) ^ 2 ≤ 1 / n - 1 / ((n : ℝ) + 1) := by
        rw [div_sub_div _ _ (by positivity) (by positivity),
          div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      push_cast
      linarith
  have h2 := this K hK
  have : (0 : ℝ) ≤ 1 / K := by positivity
  linarith

/-- `∑_{d ≤ K} 1/(φ(d) d) ≤ 4`. -/
lemma sum_inv_totient_mul_inv_le (K : ℕ) :
    ∑ d ∈ Icc 1 K, (1 : ℝ) / d.totient * (1 / (d : ℝ)) ≤ 4 := by
  have h1 : ∑ d ∈ Icc 1 K, (1 : ℝ) / d.totient * (1 / (d : ℝ))
      ≤ ∑ k ∈ Icc 1 K, (1 / (k : ℝ) ^ 2) * ∑ d ∈ k.divisors, (1 : ℝ) / d.totient := by
    apply sum_le_sum
    intro k hk
    have hk1 : (0 : ℝ) < k := by exact_mod_cast (mem_Icc.1 hk).1
    have h := div_totient_le_sum k
    have ht : (0 : ℝ) < k.totient := by exact_mod_cast Nat.totient_pos.2 (mem_Icc.1 hk).1
    calc (1 : ℝ) / k.totient * (1 / (k : ℝ)) = (1 / (k : ℝ) ^ 2) * ((k : ℝ) / k.totient) := by
          field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left h (by positivity)
  have h2 := sum_mul_divisors_le (fun k => 1 / (k : ℝ) ^ 2) (fun d => 1 / (d.totient : ℝ))
    (fun n => by positivity) (fun n => by positivity)
    (fun d m _ _ => by push_cast; rw [mul_pow, one_div_mul_one_div]) K
  have h3 : ∑ d ∈ Icc 1 K, 1 / (d.totient : ℝ) * (1 / (d : ℝ) ^ 2) ≤ 2 := by
    calc _ ≤ ∑ d ∈ Icc 1 K, 1 / (d : ℝ) ^ 2 := by
          apply sum_le_sum
          intro d hd
          have : (1 : ℝ) ≤ d.totient := by exact_mod_cast Nat.totient_pos.2 (mem_Icc.1 hd).1
          have h0 : (0 : ℝ) ≤ 1 / (d : ℝ) ^ 2 := by positivity
          have : 1 / (d.totient : ℝ) ≤ 1 := by
            rw [div_le_one (by linarith)]; exact this
          nlinarith
      _ ≤ 2 := sum_inv_sq_le K
  have h4 := sum_inv_sq_le K
  have h5 : 0 ≤ ∑ d ∈ Icc 1 K, 1 / (d.totient : ℝ) * (1 / (d : ℝ) ^ 2) :=
    sum_nonneg fun _ _ => by positivity
  calc _ ≤ _ := h1
    _ ≤ _ := h2
    _ ≤ 2 * 2 := mul_le_mul h3 h4 (sum_nonneg fun _ _ => by positivity) (by norm_num)
    _ = 4 := by norm_num

/-- `∑_{k ≤ K} 1/φ(k) ≪ 1 + log K`. -/
theorem sum_inv_totient_le : ∃ C : ℝ, 0 < C ∧ ∀ K : ℕ, 1 ≤ K →
    ∑ k ∈ Icc 1 K, (1 : ℝ) / k.totient ≤ C * (1 + Real.log K) := by
  refine ⟨4, by norm_num, fun K hK => ?_⟩
  have h1 : ∑ k ∈ Icc 1 K, (1 : ℝ) / k.totient
      ≤ ∑ k ∈ Icc 1 K, (1 / (k : ℝ)) * ∑ d ∈ k.divisors, (1 : ℝ) / d.totient := by
    apply sum_le_sum
    intro k hk
    have hk1 : (0 : ℝ) < k := by exact_mod_cast (mem_Icc.1 hk).1
    have h := div_totient_le_sum k
    calc (1 : ℝ) / k.totient = (1 / (k : ℝ)) * ((k : ℝ) / k.totient) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left h (by positivity)
  have h2 := sum_mul_divisors_le (fun k => 1 / (k : ℝ)) (fun d => 1 / (d.totient : ℝ))
    (fun n => by positivity) (fun n => by positivity)
    (fun d m _ _ => by push_cast; rw [one_div_mul_one_div]) K
  have hH : ∑ m ∈ Icc 1 K, (1 : ℝ) / (m : ℝ) = (harmonic K : ℝ) := by
    rw [harmonic_eq_sum_Icc]; push_cast; simp
  have hH2 : (harmonic K : ℝ) ≤ 1 + Real.log K := harmonic_le_one_add_log K
  have hH0 : 0 ≤ (harmonic K : ℝ) := by rw [← hH]; exact sum_nonneg fun _ _ => by positivity
  have h3 := sum_inv_totient_mul_inv_le K
  rw [hH] at h2
  calc _ ≤ _ := h1
    _ ≤ _ := h2
    _ ≤ 4 * (harmonic K : ℝ) := mul_le_mul_of_nonneg_right h3 hH0
    _ ≤ 4 * (1 + Real.log K) := by linarith

end NTKB.Davenport
