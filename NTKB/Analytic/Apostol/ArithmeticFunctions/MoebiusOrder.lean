/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Data.Nat.Squarefree
import NTKB.Attr

/-!
# The Möbius function of order `k` (Apostol, Exercises of Chapter 2, p. 50)

For `k ≥ 1`, `μ_k(1) = 1`, `μ_k(n) = 0` if `p^{k+1} ∣ n` for some prime `p`, and otherwise
`μ_k(n) = (-1)^r` where `r` is the number of primes `p` whose exact power in `n` is `p^k`
(`μ_k(n) = 1` if there is none). Note `μ_1 = μ` (`moebiusOrder_one`).
-/

open ArithmeticFunction

namespace NTKB.Apostol

open Classical in
/-- Apostol's Möbius function of order `k`. -/
noncomputable def moebiusOrder (k : ℕ) : ArithmeticFunction ℤ :=
  ⟨fun n => if n = 0 then 0 else if ∃ p, p.Prime ∧ p ^ (k + 1) ∣ n then 0 else
    (-1) ^ (n.primeFactors.filter fun p => n.factorization p = k).card, by simp⟩

open Classical in
lemma moebiusOrder_apply (k : ℕ) {n : ℕ} (hn : n ≠ 0) :
    moebiusOrder k n = if ∃ p, p.Prime ∧ p ^ (k + 1) ∣ n then 0 else
      (-1) ^ (n.primeFactors.filter fun p => n.factorization p = k).card := by
  simp [moebiusOrder, hn]

/-- `μ_1 = μ`. -/
@[kb "apostol1976" "Ch. 2, Exercises (Möbius function of order k), p. 50"]
theorem moebiusOrder_one : moebiusOrder 1 = ArithmeticFunction.moebius := by
  ext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [moebiusOrder_apply 1 hn]
  by_cases hsq : Squarefree n
  · have hno : ¬ ∃ p, p.Prime ∧ p ^ (1 + 1) ∣ n := by
      rintro ⟨p, hp, hpn⟩
      rw [Nat.squarefree_iff_prime_squarefree] at hsq
      exact hsq p hp (by rwa [← sq])
    rw [ite_eq_right hno, moebius_apply_of_squarefree hsq,
      ← (cardDistinctFactors_eq_cardFactors_iff_squarefree hn).mpr hsq,
      cardDistinctFactors_eq_card_primeFactors]
    congr 1
    rw [Finset.filter_true_of_mem]
    intro p hp
    have h1 := (Nat.squarefree_iff_factorization_le_one hn).mp hsq p
    have h2 : 0 < n.factorization p :=
      Nat.Prime.factorization_pos_of_dvd (Nat.prime_of_mem_primeFactors hp) hn
        (Nat.dvd_of_mem_primeFactors hp)
    omega
  · rw [moebius_eq_zero_of_not_squarefree hsq, ite_eq_left ?_]
    rw [Nat.squarefree_iff_prime_squarefree] at hsq
    push Not at hsq
    obtain ⟨p, hp, hpn⟩ := hsq
    exact ⟨p, hp, by rwa [sq]⟩

end NTKB.Apostol
