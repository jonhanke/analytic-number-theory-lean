/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import NTKB.Analytic.Apostol.Zeta.HurwitzEuler
import NTKB.Analytic.Apostol.GaussSums.Quadratic

/-!
# `L(0, χ)` (Apostol, Theorem 12.20)

For a Dirichlet character `χ` mod `k > 1`: `L(0, χ₁) = 0` for the principal character, and
`L(0, χ) = -(1/k) ∑_{r=1}^{k} r χ(r)` for `χ ≠ χ₁`.
Proof as in Apostol: `L(0, χ) = ∑_{r=1}^{k} χ(r) ζ(0, r/k)` and `ζ(0, a) = 1/2 - a`
(Theorem 12.13 for `n = 0`, `hurwitzZeta_zero_eq`).
-/

open Complex Finset HurwitzZeta

namespace NTKB.Apostol

variable {N : ℕ} [NeZero N]

/-- `L(0, χ) = ∑_{j mod k} χ(j) (1/2 - j/k)` for `k > 1`. -/
lemma LFunction_zero_eq_sum (χ : DirichletCharacter ℂ N) (hN : 1 < N) :
    χ.LFunction 0 = ∑ j : ZMod N, χ j * (1 / 2 - (j.val : ℂ) / N) := by
  have : Fact (1 < N) := ⟨hN⟩
  rw [DirichletCharacter.LFunction, ZMod.LFunction, neg_zero, cpow_zero, one_mul]
  refine sum_congr rfl fun j _ ↦ ?_
  rcases eq_or_ne j 0 with rfl | hj
  · simp [MulChar.map_nonunit χ not_isUnit_zero]
  · have hN0 : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
    have hv : 0 < j.val := Nat.pos_of_ne_zero ((ZMod.val_ne_zero j).mpr hj)
    rw [ZMod.toAddCircle_apply, hurwitzZeta_zero_eq (by positivity)
      ((div_le_one hN0).mpr (by exact_mod_cast (ZMod.val_lt j).le))]
    push_cast
    ring

/-- `∑_{j mod k} j χ(j) = ∑_{r=1}^{k} r χ(r)`. -/
lemma sum_zmod_val_mul_eq_sum_Icc (χ : DirichletCharacter ℂ N) (hN : 1 < N) :
    ∑ j : ZMod N, (j.val : ℂ) * χ j = ∑ r ∈ Icc 1 N, (r : ℂ) * χ r := by
  have : Fact (1 < N) := ⟨hN⟩
  rw [sum_Icc_one_eq_sum_range (fun r : ℕ ↦ (r : ℂ) * χ r) N
    (by simp [MulChar.map_nonunit χ not_isUnit_zero])]
  symm
  refine sum_nbij' (fun r ↦ (r : ZMod N)) (fun x ↦ x.val) (by simp) (fun x _ ↦ by
    simpa using ZMod.val_lt x) (fun r hr ↦ ?_) (fun x _ ↦ by simp) (fun r hr ↦ ?_)
  · rw [ZMod.val_natCast, Nat.mod_eq_of_lt (mem_range.mp hr)]
  · rw [ZMod.val_natCast, Nat.mod_eq_of_lt (mem_range.mp hr)]

/-- **Apostol, Theorem 12.20** (a): `L(0, χ₁) = 0` for the principal character mod `k > 1`. -/
@[kb "apostol1976" "Thm 12.20, p. 268"]
theorem LFunction_one_zero (hN : 1 < N) : (1 : DirichletCharacter ℂ N).LFunction 0 = 0 := by
  have : Fact (1 < N) := ⟨hN⟩
  rw [DirichletCharacter.LFunction, ZMod.LFunction_apply_zero_of_even
    (DirichletCharacter.even_one).to_fun]
  simp [MulChar.map_nonunit (1 : DirichletCharacter ℂ N) (not_isUnit_zero (M₀ := ZMod N))]

/-- **Apostol, Theorem 12.20** (b): `L(0, χ) = -(1/k) ∑_{r=1}^{k} r χ(r)` for `χ ≠ χ₁` mod `k`. -/
@[kb "apostol1976" "Thm 12.20, p. 268"]
theorem LFunction_zero_of_ne_one {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) :
    χ.LFunction 0 = -(1 / N) * ∑ r ∈ Icc 1 N, (r : ℂ) * χ r := by
  have hN : 1 < N := by
    by_contra h
    have h1 : N = 1 := by have := NeZero.pos N; omega
    subst h1
    exact hχ (Subsingleton.elim _ _)
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  rw [LFunction_zero_eq_sum χ hN, ← sum_zmod_val_mul_eq_sum_Icc χ hN]
  have hs := MulChar.sum_eq_zero_of_ne_one hχ
  have : ∑ j : ZMod N, χ j * (1 / 2 - (j.val : ℂ) / N) =
      1 / 2 * ∑ j : ZMod N, χ j - 1 / N * ∑ j : ZMod N, (j.val : ℂ) * χ j := by
    rw [mul_sum, mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun j _ ↦ ?_
    field_simp
  rw [this, hs]
  ring

/-- **Apostol, Theorem 12.20** (b), last part: `L(0, χ) = 0` if `χ(-1) = 1` (`k > 1`). -/
@[kb "apostol1976" "Thm 12.20, p. 268"]
theorem LFunction_zero_of_even {χ : DirichletCharacter ℂ N} (hN : 1 < N) (hχ : χ.Even) :
    χ.LFunction 0 = 0 := by
  have : Fact (1 < N) := ⟨hN⟩
  rw [DirichletCharacter.LFunction, ZMod.LFunction_apply_zero_of_even hχ.to_fun]
  simp [MulChar.map_nonunit χ (not_isUnit_zero (M₀ := ZMod N))]

/-- **Apostol, Theorem 12.13**: `ζ(-n, a) = -B_{n+1}(a)/(n+1)` for all integers `n ≥ 0`,
`0 < a ≤ 1` (Mathlib's `hurwitzZeta_neg_nat` for `n ≥ 1`, `hurwitzZeta_zero_eq` for `n = 0`). -/
@[kb "apostol1976" "Thm 12.13, p. 264"]
theorem apostol_thm_12_13 (n : ℕ) {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1) :
    hurwitzZeta a (-n) =
      -1 / (n + 1) * ((Polynomial.bernoulli (n + 1)).map (algebraMap ℚ ℂ)).eval (a : ℂ) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [CharP.cast_eq_zero, neg_zero, hurwitzZeta_zero_eq ha0 ha1, zero_add,
      Polynomial.bernoulli_one]
    simp
  · exact hurwitzZeta_neg_nat hn ⟨ha0.le, ha1⟩

end NTKB.Apostol
