/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Primorial
import NTKB.Attr

/-!
# Vinogradov's sieve identity (Davenport, Chapter 24, p. 138)

Let `P = ∏_{p ≤ √N} p`. For `1 ≤ n ≤ N`, the sieve of Eratosthenes says `(n, P) = 1` if and only if
`n = 1` or `n` is a prime in `(√N, N]` (`coprime_primorial_iff`). Hence for every function `f`
(Davenport's starting point for Vinogradov's method, p. 138)
`f(1) + ∑_{√N < p ≤ N} f(p) = ∑_{n ≤ N, (n, P) = 1} f(n) = ∑_{t ∣ P} μ(t) ∑_{r ≤ N/t} f(rt)`
(`vinogradov_sieve_identity`, `sum_coprime_primorial_eq`). `√N < p` is written `N < p²`, and
`P = primorial ⌊√N⌋` (Mathlib's `primorial n` is the product of the primes `≤ n`).
-/

open Finset
open scoped ArithmeticFunction.Moebius

namespace NTKB.Davenport

/-- **The sieve of Eratosthenes**: for `1 ≤ n ≤ N`, `n` is coprime to `∏_{p ≤ √N} p` if and only if
`n = 1` or `n` is a prime with `N < n²`. -/
theorem coprime_primorial_iff {N n : ℕ} (hn : 1 ≤ n) (hnN : n ≤ N) :
    Nat.Coprime n (primorial (Nat.sqrt N)) ↔ n = 1 ∨ (n.Prime ∧ N < n ^ 2) := by
  have hP : Nat.sqrt N ≤ Nat.sqrt N := le_rfl
  constructor
  · intro h
    by_contra hcon
    push Not at hcon
    have hn1 : n ≠ 1 := fun h1 ↦ (hcon.1 h1).elim
    by_cases hp : n.Prime
    · have h2 : n ^ 2 ≤ N := by
        have := hcon.2 hp
        omega
      have : n ≤ Nat.sqrt N := Nat.le_sqrt'.2 h2
      have hd : n ∣ primorial (Nat.sqrt N) := (Nat.Prime.dvd_primorial_iff hp).2 this
      have := Nat.Coprime.eq_one_of_dvd h hd
      exact hp.one_lt.ne' this
    · have hq := Nat.minFac_sq_le_self (by omega) hp
      have hmp : (Nat.minFac n).Prime := Nat.minFac_prime hn1
      have : Nat.minFac n ≤ Nat.sqrt N := Nat.le_sqrt'.2 (hq.trans hnN)
      have hd : Nat.minFac n ∣ primorial (Nat.sqrt N) := (Nat.Prime.dvd_primorial_iff hmp).2 this
      have := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left (Nat.minFac_dvd n) h) hd
      exact hmp.one_lt.ne' this
  · rintro (rfl | ⟨hp, hlt⟩)
    · exact Nat.coprime_one_left _
    · refine (Nat.Prime.coprime_iff_not_dvd hp).2 fun hd ↦ ?_
      have := (Nat.Prime.dvd_primorial_iff hp).1 hd
      have h2 : n ^ 2 ≤ N := by
        have := Nat.sqrt_le' N
        calc n ^ 2 ≤ (Nat.sqrt N) ^ 2 := Nat.pow_le_pow_left (by assumption) 2
          _ ≤ N := this
      omega

/-- **Davenport, Ch. 24, p. 138**, second equality (Möbius inversion over `t ∣ P`):
`∑_{n ≤ N, (n, P) = 1} f(n) = ∑_{t ∣ P} μ(t) ∑_{r ≤ N/t} f(rt)`. -/
@[kb "davenport1980" "Ch 24, p. 138"]
theorem sum_coprime_primorial_eq {R : Type*} [CommRing R] (N : ℕ) (f : ℕ → R) :
    ∑ n ∈ (Icc 1 N).filter (fun n ↦ Nat.Coprime n (primorial (Nat.sqrt N))), f n =
      ∑ t ∈ (primorial (Nat.sqrt N)).divisors, (μ t : R) * ∑ r ∈ Icc 1 (N / t), f (r * t) := by
  classical
  set P := primorial (Nat.sqrt N) with hPdef
  have hP0 : P ≠ 0 := (primorial_pos _).ne'
  have key : ∀ n : ℕ, 0 < n → (if Nat.Coprime n P then (1 : R) else 0) =
      ∑ t ∈ P.divisors, if t ∣ n then (μ t : R) else 0 := by
    intro n hn
    have h1 : ∑ d ∈ (Nat.gcd n P).divisors, (μ d : ℤ) = if Nat.gcd n P = 1 then 1 else 0 := by
      rw [← ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.moebius_mul_coe_zeta]
      simp [ArithmeticFunction.one_apply]
    have h2 : ∑ d ∈ (Nat.gcd n P).divisors, (μ d : R) = if Nat.Coprime n P then 1 else 0 := by
      have h1' := congrArg (Int.cast (R := R)) h1
      push_cast at h1'
      by_cases hc : Nat.Coprime n P
      · have hc' : Nat.gcd n P = 1 := hc
        rw [if_pos hc'] at h1'; rw [if_pos hc]; exact h1'
      · have hc' : ¬ Nat.gcd n P = 1 := hc
        rw [if_neg hc'] at h1'; rw [if_neg hc]; exact h1'.trans (by simp)
    rw [← h2]
    have h3 : (Nat.gcd n P).divisors = P.divisors.filter (· ∣ n) := by
      ext t
      simp only [Nat.mem_divisors, Finset.mem_filter, Nat.dvd_gcd_iff]
      constructor
      · rintro ⟨⟨h1, h2⟩, _⟩; exact ⟨⟨h2, hP0⟩, h1⟩
      · rintro ⟨⟨h2, _⟩, h1⟩; exact ⟨⟨h1, h2⟩, Nat.gcd_ne_zero_right hP0⟩
    rw [h3, Finset.sum_filter]
  rw [Finset.sum_filter]
  calc ∑ n ∈ Icc 1 N, (if Nat.Coprime n P then f n else 0)
      = ∑ n ∈ Icc 1 N, (∑ t ∈ P.divisors, if t ∣ n then (μ t : R) else 0) * f n := by
        refine sum_congr rfl fun n hn ↦ ?_
        rw [← key n (by simp at hn; omega)]
        split_ifs <;> simp
    _ = ∑ t ∈ P.divisors, ∑ n ∈ Icc 1 N, (if t ∣ n then (μ t : R) else 0) * f n := by
        simp_rw [Finset.sum_mul]; exact Finset.sum_comm
    _ = _ := by
        refine sum_congr rfl fun t ht ↦ ?_
        have ht0 : 0 < t := Nat.pos_of_mem_divisors ht
        rw [Finset.mul_sum]
        simp_rw [ite_mul, zero_mul]
        rw [← Finset.sum_filter]
        refine Finset.sum_nbij' (fun n ↦ n / t) (fun r ↦ r * t) ?_ ?_ ?_ ?_ ?_
        · intro n hn
          simp only [Finset.mem_filter, Finset.mem_Icc] at hn ⊢
          obtain ⟨⟨h1, h2⟩, k, rfl⟩ := hn
          rw [Nat.mul_div_cancel_left _ ht0]
          refine ⟨Nat.pos_of_ne_zero (by rintro rfl; simp at h1), ?_⟩
          exact (Nat.le_div_iff_mul_le ht0).2 (by rw [mul_comm]; exact h2)
        · intro r hr
          simp only [Finset.mem_filter, Finset.mem_Icc] at hr ⊢
          refine ⟨⟨Nat.one_le_iff_ne_zero.2 (Nat.mul_pos hr.1 ht0).ne', ?_⟩, dvd_mul_left _ _⟩
          exact (Nat.le_div_iff_mul_le ht0).1 hr.2
        · intro n hn
          simp only [Finset.mem_filter] at hn
          exact Nat.div_mul_cancel hn.2
        · intro r _
          exact Nat.mul_div_cancel _ ht0
        · intro n hn
          simp only [Finset.mem_filter] at hn
          rw [Nat.div_mul_cancel hn.2]

/-- **Vinogradov's sieve identity (Davenport, Ch. 24, p. 138)**: for `N ≥ 1`, `P = ∏_{p ≤ √N} p`
and any `f`, `f(1) + ∑_{√N < p ≤ N} f(p) = ∑_{t ∣ P} μ(t) ∑_{r ≤ N/t} f(rt)`. -/
@[kb "davenport1980" "Ch 24, p. 138"]
theorem vinogradov_sieve_identity {R : Type*} [CommRing R] {N : ℕ} (hN : 1 ≤ N) (f : ℕ → R) :
    f 1 + ∑ p ∈ (Icc 1 N).filter (fun p ↦ p.Prime ∧ N < p ^ 2), f p =
      ∑ t ∈ (primorial (Nat.sqrt N)).divisors, (μ t : R) * ∑ r ∈ Icc 1 (N / t), f (r * t) := by
  have h := sum_coprime_primorial_eq N f
  rw [← h]
  have hfilt : (Icc 1 N).filter (fun n ↦ Nat.Coprime n (primorial (Nat.sqrt N))) =
      insert 1 ((Icc 1 N).filter (fun p ↦ p.Prime ∧ N < p ^ 2)) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      rcases (coprime_primorial_iff h1 h2).1 h3 with h | h
      · exact Or.inl h
      · exact Or.inr ⟨⟨h1, h2⟩, h⟩
    · rintro (rfl | ⟨⟨h1, h2⟩, h⟩)
      · exact ⟨⟨le_rfl, hN⟩, Nat.coprime_one_left _⟩
      · exact ⟨⟨h1, h2⟩, (coprime_primorial_iff h1 h2).2 (Or.inr h)⟩
  rw [hfilt, Finset.sum_insert]
  simp [Nat.not_prime_one]

end NTKB.Davenport
