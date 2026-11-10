/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import NTKB.Elementary.SpecialValues.GeneralizedBernoulli

/-!
# Values of Dirichlet L-functions at non-positive integers, `k ≥ 2`

For every Dirichlet character `χ` modulo `N ≥ 1` (primitive or not, principal or not) and every
`k ≥ 2`,
$$L(1-k,\chi) = -\frac{B_{k,\chi}}{k}$$
(Washington, Theorem 4.2; Miyake, Theorem 3.3.4), where `L` is Mathlib's
`DirichletCharacter.LFunction` (the analytic continuation of `∑ χ(n) n^{-s}` at level `N`).
The case `k = 1` is in `NTKB.Elementary.SpecialValues.ValueAtZero`.

The proof is the one of modular-forms-lean (`ModularFormsKB/Miyake/GeneralizedBernoulli.lean`,
`LFunction_one_sub_nat`), which evaluates Mathlib's Hurwitz zeta functions at negative integers
(`HurwitzZeta.hurwitzZeta_neg_nat`).
-/

open Complex

namespace NTKB

/-- **`L(1-k, χ) = -B_{k,χ}/k` for `k ≥ 2`**, for every Dirichlet character. -/
theorem LFunction_one_sub_nat_of_two_le {m : ℕ} [NeZero m] (χ : DirichletCharacter ℂ m) {k : ℕ}
    (hk : 2 ≤ k) :
    DirichletCharacter.LFunction χ (1 - k) = -generalizedBernoulli χ k / k := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  have hn : n ≠ 0 := by omega
  have hs : (1 : ℂ) - ((n + 1 : ℕ) : ℂ) = -(n : ℂ) := by push_cast; ring
  have hterm : ∀ a ∈ Finset.Icc 1 m, χ (a : ZMod m) *
      HurwitzZeta.hurwitzZeta (ZMod.toAddCircle (a : ZMod m)) (-(n : ℂ)) =
      χ a * (-1 / ((n : ℂ) + 1) *
        ((Polynomial.bernoulli (n + 1)).map (algebraMap ℚ ℂ)).eval ((a : ℂ) / m)) := by
    intro a ha
    rw [Finset.mem_Icc] at ha
    rw [ZMod.toAddCircle_natCast]
    have hx : ((a : ℝ) / m) ∈ Set.Icc (0 : ℝ) 1 := by
      refine ⟨by positivity, ?_⟩
      rw [div_le_one (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m))]
      exact_mod_cast ha.2
    have := HurwitzZeta.hurwitzZeta_neg_nat (k := n) hn hx
    push_cast at this
    rw [this]
  have hbij : ∑ j : ZMod m, χ j * HurwitzZeta.hurwitzZeta (ZMod.toAddCircle j) (-(n : ℂ)) =
      ∑ a ∈ Finset.Icc 1 m, χ (a : ZMod m) *
        HurwitzZeta.hurwitzZeta (ZMod.toAddCircle (a : ZMod m)) (-(n : ℂ)) := by
    symm
    refine Finset.sum_bij (fun a _ ↦ (a : ZMod m)) (fun _ _ ↦ Finset.mem_univ _) ?_ ?_
      fun _ _ ↦ rfl
    · intro a ha b hb hab
      rw [Finset.mem_Icc] at ha hb
      rw [ZMod.natCast_eq_natCast_iff'] at hab
      rcases Nat.lt_or_ge a m with h1 | h1 <;> rcases Nat.lt_or_ge b m with h2 | h2
      · rwa [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at hab
      · have : b = m := by omega
        subst this
        rw [Nat.mod_eq_of_lt h1, Nat.mod_self] at hab
        omega
      · have : a = m := by omega
        subst this
        rw [Nat.mod_eq_of_lt h2, Nat.mod_self] at hab
        omega
      · omega
    · intro j _
      by_cases h0 : j.val = 0
      · refine ⟨m, Finset.mem_Icc.mpr ⟨Nat.pos_of_ne_zero (NeZero.ne m), le_rfl⟩, ?_⟩
        rw [ZMod.val_eq_zero] at h0
        simp [h0]
      · refine ⟨j.val, Finset.mem_Icc.mpr ⟨Nat.pos_of_ne_zero h0, (ZMod.val_lt j).le⟩, ?_⟩
        simp
  rw [generalizedBernoulli_eq_sum_Icc]
  unfold DirichletCharacter.LFunction ZMod.LFunction
  rw [hs, hbij, Finset.sum_congr rfl hterm]
  have : (m : ℂ) ^ (-(-(n : ℂ))) = (m : ℂ) ^ (((n + 1 : ℕ) : ℤ) - 1) := by
    rw [neg_neg, Complex.cpow_natCast]
    push_cast
    simp
  rw [this]
  simp only [← mul_assoc, Finset.mul_sum]
  push_cast
  have hn1 : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  rw [eq_div_iff hn1, ← Finset.sum_neg_distrib, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  field_simp

end NTKB
