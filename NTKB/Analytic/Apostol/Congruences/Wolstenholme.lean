/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Apostol.Congruences.Basic
import Mathlib.Algebra.Polynomial.Derivative

/-!
# Wolstenholme's theorem (Apostol, Chapter 5, §5.6, Theorem 5.25)

**Theorem 5.25.** For a prime `p ≥ 5`, `∑_{k=1}^{p-1} (p-1)!/k ≡ 0 (mod p²)`.

Apostol's proof: the sum is `S_{p-2}`, the coefficient of `-x` in
`g(x) = (x - 1)(x - 2)⋯(x - p + 1) = x^{p-1} - S₁ x^{p-2} + ⋯ - S_{p-2} x + (p-1)!`;
the coefficients `S₁, …, S_{p-2}` are divisible by `p` (Theorem 5.23), and `g(p) = (p-1)!` gives
`p S_{p-2} ≡ 0 (mod p³)`.
-/

open Finset Polynomial

namespace NTKB.Apostol

/-- `g(x) = (x - 1)(x - 2)⋯(x - (p - 1))` over `ℤ`. -/
noncomputable def wilsonPoly (p : ℕ) : ℤ[X] := ∏ k ∈ Icc 1 (p - 1), (X - C (k : ℤ))

theorem wilsonPoly_monic (p : ℕ) : (wilsonPoly p).Monic :=
  monic_prod_of_monic _ _ fun _ _ ↦ monic_X_sub_C _

theorem wilsonPoly_natDegree (p : ℕ) : (wilsonPoly p).natDegree = p - 1 := by
  rw [wilsonPoly, natDegree_prod_of_monic _ _ fun _ _ ↦ monic_X_sub_C _]
  simp only [natDegree_X_sub_C, sum_const, Nat.card_Icc, smul_eq_mul, mul_one]
  omega

theorem prod_Icc_one_eq_factorial (n : ℕ) : ∏ x ∈ Icc 1 n, x = n.factorial := by
  induction n with
  | zero => simp
  | succ n ih => rw [prod_Icc_succ_top (by omega), ih, Nat.factorial_succ, mul_comm]

/-- `g(p) = (p - 1)!`. -/
theorem wilsonPoly_eval_self (p : ℕ) : (wilsonPoly p).eval (p : ℤ) = ((p - 1).factorial : ℤ) := by
  rw [wilsonPoly, eval_prod]
  simp only [eval_sub, eval_X, eval_C]
  rw [← prod_Icc_one_eq_factorial, Nat.cast_prod]
  refine prod_nbij' (fun k ↦ p - k) (fun k ↦ p - k) ?_ ?_ ?_ ?_ ?_
  · intro k hk; simp only [mem_Icc] at hk ⊢; omega
  · intro k hk; simp only [mem_Icc] at hk ⊢; omega
  · intro k hk; simp only [mem_Icc] at hk; omega
  · intro k hk; simp only [mem_Icc] at hk; omega
  · intro k hk
    simp only [mem_Icc] at hk
    rw [Nat.cast_sub (by omega)]

/-- The coefficient of `x` in `g` is `-∑_{k=1}^{p-1} (p-1)!/k` for odd `p`. -/
theorem wilsonPoly_coeff_one {p : ℕ} (hp : Odd p) :
    (wilsonPoly p).coeff 1 = -∑ k ∈ Icc 1 (p - 1), (((p - 1).factorial / k : ℕ) : ℤ) := by
  classical
  have h1 : (wilsonPoly p).coeff 1 = (derivative (wilsonPoly p)).eval 0 := by
    rw [← coeff_zero_eq_eval_zero, coeff_derivative]; simp
  rw [h1, wilsonPoly, derivative_prod_finset, eval_finsetSum, ← sum_neg_distrib]
  refine sum_congr rfl fun k hk ↦ ?_
  simp only [derivative_sub, derivative_X, derivative_C, sub_zero, mul_one, eval_prod, eval_sub,
    eval_X, eval_C, zero_sub]
  rw [prod_neg, card_erase_of_mem hk, Nat.card_Icc]
  have hodd : Odd (p - 1 + 1 - 1 - 1) := by
    obtain ⟨m, rfl⟩ := hp
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · exact absurd hk (by simp)
    · exact ⟨m - 1, by omega⟩
  rw [hodd.neg_one_pow, neg_one_mul, neg_inj]
  -- `∏_{j ≠ k} j = (p-1)!/k`
  have hk0 : k ≠ 0 := by simp only [mem_Icc] at hk; omega
  have hprod := prod_erase_mul (Icc 1 (p - 1)) (fun j ↦ j) hk
  rw [prod_Icc_one_eq_factorial] at hprod
  have : ∏ j ∈ (Icc 1 (p - 1)).erase k, j = (p - 1).factorial / k := by
    rw [← hprod, Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hk0)]
  rw [← this, Nat.cast_prod]

/-- **Apostol, Theorem 5.25** (Wolstenholme). For a prime `p ≥ 5`,
`∑_{k=1}^{p-1} (p-1)!/k ≡ 0 (mod p²)`. -/
@[kb "apostol1976" "Thm 5.25, p. 116"]
theorem wolstenholme (p : ℕ) [hp : Fact p.Prime] (hp5 : 5 ≤ p) :
    (p : ℤ) ^ 2 ∣ ∑ k ∈ Icc 1 (p - 1), (((p - 1).factorial / k : ℕ) : ℤ) := by
  set g := wilsonPoly p
  set c : ℕ → ℤ := fun j ↦ g.coeff j
  have hodd : Odd p := hp.out.odd_of_ne_two (by omega)
  -- Theorem 5.23: `p ∣ c_j` for `1 ≤ j ≤ p - 2`
  have h523 : ∀ j, 1 ≤ j → j ≤ p - 2 → (p : ℤ) ∣ c j := by
    intro j hj1 hj2
    have := dvd_coeff_prod_X_sub_sub p j
    rw [coeff_add, coeff_sub, coeff_X_pow, coeff_one, if_neg (by omega), if_neg (by omega),
      sub_zero, add_zero] at this
    exact this
  -- `c_0 = (p-1)!`, `c_{p-1} = 1`
  have hc0 : c 0 = ((p - 1).factorial : ℤ) := by
    simp only [c, g, coeff_zero_eq_eval_zero, wilsonPoly, eval_prod, eval_sub, eval_X, eval_C,
      zero_sub]
    rw [prod_neg, Nat.card_Icc, show p - 1 + 1 - 1 = p - 1 by omega]
    have he : Even (p - 1) := by obtain ⟨m, rfl⟩ := hodd; exact ⟨m, by omega⟩
    rw [he.neg_one_pow, one_mul, ← prod_Icc_one_eq_factorial, Nat.cast_prod]
  have hcp : c (p - 1) = 1 := by
    have := (wilsonPoly_monic p).leadingCoeff
    rwa [Polynomial.leadingCoeff, wilsonPoly_natDegree] at this
  -- `g(p) = ∑_{j < p} c_j p^j`
  have hev := wilsonPoly_eval_self p
  rw [eval_eq_sum_range, wilsonPoly_natDegree, show p - 1 + 1 = p by omega] at hev
  obtain ⟨n, hn⟩ : ∃ n, p = n + 3 := ⟨p - 3, by omega⟩
  have hsplit : ∑ i ∈ range p, (wilsonPoly p).coeff i * (p : ℤ) ^ i =
      ∑ i ∈ range n, c (i + 2) * (p : ℤ) ^ (i + 2) + c 1 * p + c 0 + c (n + 2) * (p : ℤ) ^ (n + 2) := by
    rw [show range p = range (n + 3) by rw [hn], sum_range_succ, sum_range_succ',
      sum_range_succ']
    simp only [c, g]
    ring
  rw [hsplit, hc0, show n + 2 = p - 1 by omega, hcp, one_mul] at hev
  -- `p c_1 = -(∑ c_{i+2} p^{i+2} + p^{p-1})`, divisible by `p³`
  have hdiv : (p : ℤ) ^ 3 ∣ c 1 * p := by
    have e : c 1 * p = -(∑ i ∈ range n, c (i + 2) * (p : ℤ) ^ (i + 2) + (p : ℤ) ^ (p - 1)) := by
      linarith
    rw [e, dvd_neg]
    refine dvd_add (dvd_sum fun i hi ↦ ?_) (pow_dvd_pow _ (by omega))
    have hi' := mem_range.1 hi
    obtain ⟨u, hu⟩ := h523 (i + 2) (by omega) (by omega)
    rw [hu, show (p : ℤ) ^ (i + 2) = p ^ 2 * p ^ i by ring]
    exact ⟨u * p ^ i, by ring⟩
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have h2 : (p : ℤ) ^ 2 ∣ c 1 := by
    rw [show (p : ℤ) ^ 3 = p ^ 2 * p by ring] at hdiv
    exact (mul_dvd_mul_iff_right hp0).1 hdiv
  have hc1 := wilsonPoly_coeff_one hodd
  rw [show c 1 = (wilsonPoly p).coeff 1 from rfl, hc1, dvd_neg] at h2
  exact h2

end NTKB.Apostol
