/- Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license. -/
import NTKB.Attr
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Mean square of the divisor function (Davenport, Chapter 24)

`∑_{k ≤ K} d(k)² ≤ K (1 + log K)³`.

For `a, b ∣ k` write `g = gcd(a,b)`, `a = g a'`, `b = g b'`; then `g a' b' = lcm(a,b) ∣ k`,
and `(a,b) ↦ (g,a',b')` is injective.  Hence `d(k)²` is at most the number of triples
`(g,a',b') ∈ [1,K]³` with `g a' b' ∣ k`, and summing over `k ≤ K` gives at most
`K (∑_{n ≤ K} 1/n)³`.
-/

namespace NTKB.Davenport

open Finset Real

/-- The cube `[1,K]³`. -/
def divSq_box (K : ℕ) : Finset (ℕ × ℕ × ℕ) := Icc 1 K ×ˢ Icc 1 K ×ˢ Icc 1 K

lemma divSq_card_le (K k : ℕ) (hk : 1 ≤ k) (hkK : k ≤ K) :
    k.divisors.card ^ 2 ≤
      ((divSq_box K).filter (fun t => t.1 * t.2.1 * t.2.2 ∣ k)).card := by
  rw [sq, ← Finset.card_product]
  apply Finset.card_le_card_of_injOn (fun p : ℕ × ℕ => (Nat.gcd p.1 p.2, p.1 / Nat.gcd p.1 p.2,
    p.2 / Nat.gcd p.1 p.2))
  · rintro ⟨a, b⟩ hab
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Nat.mem_divisors] at hab
    obtain ⟨⟨hak, -⟩, ⟨hbk, -⟩⟩ := hab
    have ha : 0 < a := Nat.pos_of_dvd_of_pos hak (by omega)
    have hb : 0 < b := Nat.pos_of_dvd_of_pos hbk (by omega)
    have hg : 0 < Nat.gcd a b := Nat.gcd_pos_of_pos_left _ ha
    have hal : a ≤ k := Nat.le_of_dvd (by omega) hak
    have hbl : b ≤ k := Nat.le_of_dvd (by omega) hbk
    have hga : Nat.gcd a b ≤ a := Nat.le_of_dvd ha (Nat.gcd_dvd_left a b)
    have h1 : 0 < a / Nat.gcd a b := Nat.div_pos hga hg
    have h2 : 0 < b / Nat.gcd a b := Nat.div_pos (Nat.le_of_dvd hb (Nat.gcd_dvd_right a b)) hg
    have hlcm : Nat.gcd a b * (Nat.gcd a b * (a / Nat.gcd a b) * (b / Nat.gcd a b))
        = Nat.gcd a b * Nat.lcm a b := by
      rw [Nat.gcd_mul_lcm]
      have e1 := Nat.mul_div_cancel' (Nat.gcd_dvd_left a b)
      have e2 := Nat.mul_div_cancel' (Nat.gcd_dvd_right a b)
      calc _ = (Nat.gcd a b * (a / Nat.gcd a b)) * (Nat.gcd a b * (b / Nat.gcd a b)) := by ring
        _ = _ := by rw [e1, e2]
    have hlcm' := Nat.eq_of_mul_eq_mul_left hg hlcm
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, divSq_box, Finset.mem_product, Finset.mem_Icc]
    refine ⟨⟨⟨hg, by omega⟩, ⟨h1, ?_⟩, ⟨h2, ?_⟩⟩, ?_⟩
    · exact le_trans (Nat.div_le_self _ _) (by omega)
    · exact le_trans (Nat.div_le_self _ _) (by omega)
    · rw [hlcm']; exact Nat.lcm_dvd hak hbk
  · rintro ⟨a, b⟩ _ ⟨a', b'⟩ _ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2, h3⟩ := h
    have e1 := Nat.mul_div_cancel' (Nat.gcd_dvd_left a b)
    have e2 := Nat.mul_div_cancel' (Nat.gcd_dvd_right a b)
    have e3 := Nat.mul_div_cancel' (Nat.gcd_dvd_left a' b')
    have e4 := Nat.mul_div_cancel' (Nat.gcd_dvd_right a' b')
    rw [← h1] at h2 h3 e3 e4
    simp only [Prod.mk.injEq]
    constructor
    · rw [← e1, ← e3, h2]
    · rw [← e2, ← e4, h3]

lemma divSq_card_multiples (K n : ℕ) (hn : 0 < n) :
    (((Icc 1 K).filter (n ∣ ·)).card : ℝ) ≤ (K : ℝ) / n := by
  have h : ((Icc 1 K).filter (n ∣ ·)).card ≤ K / n := by
    have := Finset.card_le_card_of_injOn (s := (Icc 1 K).filter (n ∣ ·)) (t := Icc 1 (K / n))
      (fun k => k / n) ?_ ?_
    · simpa using this
    · intro k hk
      simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_Icc] at hk
      obtain ⟨⟨h1, h2⟩, ⟨c, rfl⟩⟩ := hk
      simp only [Finset.coe_Icc, Set.mem_Icc]
      have hc : 0 < c := by
        rcases Nat.eq_zero_or_pos c with h | h
        · subst h; simp at h1
        · exact h
      rw [Nat.mul_div_cancel_left _ hn]
      exact ⟨hc, Nat.le_div_iff_mul_le hn |>.2 (by rw [mul_comm]; exact h2)⟩
    · intro k hk l hl h
      simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hk hl
      have := Nat.div_mul_cancel hk.2
      have := Nat.div_mul_cancel hl.2
      simp only at h
      rw [h] at *
      omega
  calc _ ≤ ((K / n : ℕ) : ℝ) := by exact_mod_cast h
    _ ≤ _ := Nat.cast_div_le

/-- `∑_{k ≤ z} d(k)² ≪ z (1 + log z)³`. -/
@[kb "davenport1980" "Ch 24, p. 140"]
theorem sum_card_divisors_sq_le : ∃ C : ℝ, 0 < C ∧ ∀ K : ℕ, 1 ≤ K →
    ∑ k ∈ Icc 1 K, ((k.divisors.card : ℝ)) ^ 2 ≤ C * K * (1 + Real.log K) ^ 3 := by
  refine ⟨1, one_pos, fun K hK => ?_⟩
  have hH : ∑ m ∈ Icc 1 K, (1 : ℝ) / (m : ℝ) = (harmonic K : ℝ) := by
    rw [harmonic_eq_sum_Icc]; push_cast; simp
  have hH2 : (harmonic K : ℝ) ≤ 1 + Real.log K := harmonic_le_one_add_log K
  have hH0 : 0 ≤ (harmonic K : ℝ) := by rw [← hH]; exact sum_nonneg fun _ _ => by positivity
  calc ∑ k ∈ Icc 1 K, ((k.divisors.card : ℝ)) ^ 2
      ≤ ∑ k ∈ Icc 1 K, (((divSq_box K).filter
          (fun t => t.1 * t.2.1 * t.2.2 ∣ k)).card : ℝ) := by
        apply sum_le_sum
        intro k hk
        rw [mem_Icc] at hk
        exact_mod_cast divSq_card_le K k hk.1 hk.2
    _ = ∑ k ∈ Icc 1 K, ∑ t ∈ divSq_box K, (if t.1 * t.2.1 * t.2.2 ∣ k then (1 : ℝ) else 0) := by
        apply sum_congr rfl
        intro k _
        rw [Finset.sum_boole]
    _ = ∑ t ∈ divSq_box K, ∑ k ∈ Icc 1 K, (if t.1 * t.2.1 * t.2.2 ∣ k then (1 : ℝ) else 0) :=
        Finset.sum_comm
    _ = ∑ t ∈ divSq_box K, (((Icc 1 K).filter (t.1 * t.2.1 * t.2.2 ∣ ·)).card : ℝ) := by
        apply sum_congr rfl
        intro t _
        rw [Finset.sum_boole]
    _ ≤ ∑ t ∈ divSq_box K, (K : ℝ) / ((t.1 * t.2.1 * t.2.2 : ℕ) : ℝ) := by
        apply sum_le_sum
        intro t ht
        simp only [divSq_box, Finset.mem_product, Finset.mem_Icc] at ht
        exact divSq_card_multiples K _ (by have := ht.1.1; have := ht.2.1.1; have := ht.2.2.1; positivity)
    _ = K * ((∑ a ∈ Icc 1 K, (1 : ℝ) / a) * (∑ b ∈ Icc 1 K, (1 : ℝ) / b) *
          (∑ c ∈ Icc 1 K, (1 : ℝ) / c)) := by
        simp only [divSq_box, Finset.sum_product, Finset.sum_mul, Finset.mul_sum]
        apply sum_congr rfl; intro a _
        apply sum_congr rfl; intro b _
        apply sum_congr rfl; intro c _
        push_cast
        field_simp
    _ ≤ 1 * K * (1 + Real.log K) ^ 3 := by
        rw [hH, one_mul]
        have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
        have h3 := pow_le_pow_left₀ hH0 hH2 3
        have : (harmonic K : ℝ) * (harmonic K) * (harmonic K) = (harmonic K : ℝ) ^ 3 := by ring
        rw [this]
        exact mul_le_mul_of_nonneg_left h3 hK0

end NTKB.Davenport
