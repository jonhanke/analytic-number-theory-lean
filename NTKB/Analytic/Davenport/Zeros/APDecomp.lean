/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Davenport.Zeros.PNTCharacter
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality

/-!
# `ψ(x; q, a)` through the characters

**Davenport, Ch. 20, p. 121, (A)-(B) (rows 20-1, 20-2, 20-3) and Ch. 19, p. 119 (row 19-13).**
`ψ(x; q, a) = (1/φ(q)) ∑_χ χ̄(a) ψ(x, χ)` (Mathlib's `vonMangoldt.residueClass_eq`);
`|ψ(x, χ₀) - ψ(x)| ≤ (log x/log 2) log q`; and for `χ` induced by the primitive `χ*`,
`|ψ(x, χ) - ψ(x, χ*)| ≤ (log x/log 2) log q` (only the prime powers `p^k ≤ x` with `p ∣ q` differ).
-/

open Filter Topology Complex Set DirichletCharacter
open scoped Real ArithmeticFunction.vonMangoldt

namespace NTKB

/-- **Davenport, Ch. 20, p. 121, (A) (row 20-1)**: `ψ(x; q, a) = ∑_{n ≤ x, n ≡ a (q)} Λ(n)`. -/
noncomputable def psiAP {q : ℕ} (a : ZMod q) (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, ArithmeticFunction.vonMangoldt.residueClass a n

/-- **Davenport, Ch. 20, p. 121, (B) (row 20-2)**: for `a` a unit mod `q`,
`ψ(x; q, a) = (1/φ(q)) ∑_χ χ(a)⁻¹ ψ(x, χ)`. -/
@[kb "davenport1980" "Ch 20, p. 121"]
theorem Davenport.psiAP_eq {q : ℕ} [NeZero q] {a : ZMod q} (ha : IsUnit a) (x : ℝ) :
    (psiAP a x : ℂ) = (q.totient : ℂ)⁻¹ *
      ∑ χ : DirichletCharacter ℂ q, χ a⁻¹ * psiL χ x := by
  have h := ArithmeticFunction.vonMangoldt.residueClass_eq ha
  unfold psiAP psiL
  push_cast
  rw [Finset.mul_sum]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun n _ ↦ ?_
  have := congrFun h n
  simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul] at this
  rw [this, Finset.mul_sum]

/-- `∑_{n ≤ x, (n, q) > 1} Λ(n) ≤ (log x / log 2) log q`. -/
lemma sum_vonMangoldt_not_coprime_le (q : ℕ) (hq : q ≠ 0) {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, (if n.Coprime q then 0 else Λ n) ≤
      Real.log x / Real.log 2 * Real.log q := by
  classical
  have hx0 : 0 ≤ x := by linarith
  generalize hg : (fun n : ℕ ↦ (if n.Coprime q then 0 else Λ n : ℝ)) = g
  have hgn : ∀ n, g n = if n.Coprime q then 0 else Λ n := fun n ↦ by rw [← hg]
  have hg0 : g 0 = 0 := by rw [hgn]; simp
  rw [← Finset.add_sum_Ioc_eq_sum_Icc (Nat.zero_le _), hg0, zero_add]
  have hfilt : ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊ with IsPrimePow n, g n = ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, g n := by
    refine Finset.sum_filter_of_ne fun n _ hn ↦ ?_
    rw [hgn] at hn
    split_ifs at hn
    · exact absurd rfl hn
    · exact ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hn
  rw [← hfilt, Chebyshev.sum_PrimePow_eq_sum_sum g hx0]
  -- the inner sums
  have hB : ∑ p ∈ q.primeFactors, Real.log p ≤ Real.log q := by
    rw [← Real.log_prod (fun p hp ↦ by
      have := (Nat.prime_of_mem_primeFactors hp).pos; positivity)]
    apply Real.log_le_log (by
      apply Finset.prod_pos; intro p hp; exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos)
    have := Nat.le_of_dvd (Nat.pos_of_ne_zero hq) (Nat.prod_primeFactors_dvd q)
    rw [← Nat.cast_prod]; exact_mod_cast this
  have hinner : ∀ k ∈ Finset.Icc 1 ⌊Real.log x / Real.log 2⌋₊,
      ∑ p ∈ Finset.Ioc 0 ⌊x ^ ((1 : ℝ) / k)⌋₊ with p.Prime, g (p ^ k) ≤ Real.log q := by
    intro k hk
    have hk1 : k ≠ 0 := by have := (Finset.mem_Icc.mp hk).1; omega
    refine le_trans ?_ hB
    have hval : ∀ p ∈ (Finset.Ioc 0 ⌊x ^ ((1 : ℝ) / k)⌋₊).filter Nat.Prime,
        g (p ^ k) = if p ∈ q.primeFactors then Real.log p else 0 := by
      intro p hp
      have hpp := (Finset.mem_filter.mp hp).2
      rw [hgn]
      simp only [Nat.mem_primeFactors, hpp, true_and, ne_eq, hq, not_false_eq_true, and_true]
      rw [ArithmeticFunction.vonMangoldt_apply_pow hk1, ArithmeticFunction.vonMangoldt_apply_prime hpp]
      by_cases hd : p ∣ q
      · have : ¬ (p ^ k).Coprime q := by
          rw [Nat.coprime_pow_left_iff (Nat.pos_of_ne_zero hk1)]
          exact (Nat.Prime.coprime_iff_not_dvd hpp).not.mpr (not_not.mpr hd)
        simp [this, hd]
      · have : (p ^ k).Coprime q := by
          rw [Nat.coprime_pow_left_iff (Nat.pos_of_ne_zero hk1)]
          exact (Nat.Prime.coprime_iff_not_dvd hpp).mpr hd
        simp [this, hd]
    rw [Finset.sum_congr rfl hval, ← Finset.sum_filter]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro p hp; exact (Finset.mem_filter.mp hp).2
    · intro p _ _; exact Real.log_natCast_nonneg p
  calc ∑ k ∈ Finset.Icc 1 ⌊Real.log x / Real.log 2⌋₊,
        ∑ p ∈ Finset.Ioc 0 ⌊x ^ ((1 : ℝ) / k)⌋₊ with p.Prime, g (p ^ k)
      ≤ ∑ k ∈ Finset.Icc 1 ⌊Real.log x / Real.log 2⌋₊, Real.log q := Finset.sum_le_sum hinner
    _ = ⌊Real.log x / Real.log 2⌋₊ * Real.log q := by
        rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]; simp
    _ ≤ Real.log x / Real.log 2 * Real.log q := by
        have := Real.log_natCast_nonneg q
        gcongr
        exact Nat.floor_le (div_nonneg (Real.log_nonneg hx) (Real.log_nonneg one_le_two))

/-- If `χ` and `χ'` agree on the integers prime to `q` and `|χ'(n)| ≤ 1`, then
`|ψ(x, χ) - ψ(x, χ')| ≤ (log x / log 2) log q`. -/
lemma norm_psiL_sub_le {q q' : ℕ} (hq : q ≠ 0) (χ : DirichletCharacter ℂ q)
    (χ' : DirichletCharacter ℂ q') (h : ∀ n : ℕ, n.Coprime q → χ n = χ' n) {x : ℝ} (hx : 1 ≤ x) :
    ‖psiL χ x - psiL χ' x‖ ≤ Real.log x / Real.log 2 * Real.log q := by
  classical
  unfold psiL
  rw [← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun n _ ↦ ?_).trans
    (sum_vonMangoldt_not_coprime_le q hq hx))
  by_cases hc : n.Coprime q
  · rw [if_pos hc, h n hc, sub_self, norm_zero]
  · have h0 : χ n = 0 := by
      rw [MulChar.map_nonunit]
      intro hu
      exact hc ((ZMod.isUnit_iff_coprime n q).mp hu)
    simp only [hc, if_false, h0, zero_mul, zero_sub, norm_neg, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    have := DirichletCharacter.norm_le_one χ' n
    nlinarith [ArithmeticFunction.vonMangoldt_nonneg (n := n)]

/-- **Davenport, Ch. 20, p. 121 (row 20-3)**: `|ψ(x, χ₀) - ψ(x)| ≤ (log x / log 2) log q`. -/
@[kb "davenport1980" "Ch 20, p. 121"]
theorem Davenport.norm_psiL_one_sub_psi_le {q : ℕ} [NeZero q] {x : ℝ} (hx : 1 ≤ x) :
    ‖psiL (1 : DirichletCharacter ℂ q) x - Chebyshev.psi x‖ ≤
      Real.log x / Real.log 2 * Real.log q := by
  have h1 : (Chebyshev.psi x : ℂ) = psiL (1 : DirichletCharacter ℂ 1) x := by
    unfold psiL
    rw [Chebyshev.psi_eq_sum_Icc]
    push_cast
    refine Finset.sum_congr rfl fun n _ ↦ ?_
    simp [MulChar.one_apply (isUnit_of_subsingleton _)]
  rw [h1]
  refine norm_psiL_sub_le (NeZero.ne q) _ _ (fun n hn ↦ ?_) hx
  rw [MulChar.one_apply ((ZMod.isUnit_iff_coprime n q).mpr hn),
    MulChar.one_apply (isUnit_of_subsingleton _)]

/-- **Davenport, Ch. 19, p. 119 (row 19-13)**: for `χ` mod `q` and its primitive character `χ*`,
`|ψ(x, χ) - ψ(x, χ*)| ≤ (log x / log 2) log q`. -/
@[kb "davenport1980" "Ch 19, p. 119"]
theorem Davenport.norm_psiL_sub_primitive_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {x : ℝ} (hx : 1 ≤ x) :
    ‖psiL χ x - psiL χ.primitiveCharacter x‖ ≤ Real.log x / Real.log 2 * Real.log q := by
  refine norm_psiL_sub_le (NeZero.ne q) _ _ (fun n hn ↦ ?_) hx
  conv_lhs => rw [← χ.changeLevel_primitiveCharacter]
  have := changeLevel_eq_cast_of_dvd' χ.primitiveCharacter χ.conductor_dvd_level (a := (n : ℤ))
    (by rw [Int.isCoprime_iff_gcd_eq_one]; exact_mod_cast hn)
  simpa using this

end NTKB
