/-
Ireland–Rosen, Chapter 11, §1: the zeta function `Z(u) = exp(∑_{s ≥ 1} N_s u^s / s)` as a formal
power series, and Proposition 11.1.1 (with its converse, Exercise 11.2): `Z` is the rational
function `∏ (1 - α_i u) / ∏ (1 - β_j u)` iff `N_s = ∑ β_j^s - ∑ α_i^s` for all `s ≥ 1`.

The book's proof compares logarithmic derivatives; we do the same with Mathlib's formal derivative
`d⁄dX` and composition `PowerSeries.subst`.
-/
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Analysis.Complex.Basic
import NTKB.Attr

open PowerSeries

namespace NTKB.IrelandRosen

/-- `∑_{s ≥ 1} N_s u^s / s`. -/
noncomputable def logSeries (N : ℕ → ℂ) : ℂ⟦X⟧ := mk fun s => if s = 0 then 0 else N s / s

lemma constantCoeff_logSeries (N : ℕ → ℂ) : constantCoeff (logSeries N) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply]; simp [logSeries]

/-- **The zeta function** attached to the numbers `N_s` (Ireland–Rosen, Chapter 11, §1):
`Z(u) = exp(∑_{s ≥ 1} N_s u^s / s)`, as a formal power series. -/
noncomputable def zetaOfCounts (N : ℕ → ℂ) : ℂ⟦X⟧ := (exp ℂ).subst (logSeries N)

lemma hasSubst_logSeries (N : ℕ → ℂ) : HasSubst (logSeries N) :=
  HasSubst.of_constantCoeff_zero' (constantCoeff_logSeries N)

lemma constantCoeff_zetaOfCounts (N : ℕ → ℂ) : constantCoeff (zetaOfCounts N) = 1 := by
  have := constantCoeff_subst_of_constantCoeff_zero (S := ℂ) (constantCoeff_logSeries N) (exp ℂ)
  rw [zetaOfCounts]
  exact this.trans (by simp)

lemma derivative_logSeries (N : ℕ → ℂ) : d⁄dX (logSeries N) = mk fun k => N (k + 1) := by
  ext k
  rw [coeff_derivative, coeff_mk, logSeries, coeff_mk, if_neg (Nat.succ_ne_zero k)]
  have : ((k + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  push_cast at this ⊢
  field_simp

lemma derivative_zetaOfCounts (N : ℕ → ℂ) :
    d⁄dX (zetaOfCounts N) = zetaOfCounts N * mk fun k => N (k + 1) := by
  rw [zetaOfCounts, derivative_subst (hasSubst_logSeries N), derivative_exp,
    derivative_logSeries]

/-- Uniqueness for the equation `A' = A M`: the solution is determined by its constant term. -/
lemma eq_of_derivative_eq_mul {A B M : ℂ⟦X⟧} (h0 : constantCoeff A = constantCoeff B)
    (hA : d⁄dX A = A * M) (hB : d⁄dX B = B * M) : A = B := by
  ext n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | n
    · simpa using h0
    · have eA := congrArg (coeff n) hA
      have eB := congrArg (coeff n) hB
      rw [coeff_derivative, coeff_mul] at eA eB
      have hsum : ∑ p ∈ Finset.antidiagonal n, coeff p.1 A * coeff p.2 M =
          ∑ p ∈ Finset.antidiagonal n, coeff p.1 B * coeff p.2 M := by
        refine Finset.sum_congr rfl fun p hp => ?_
        rw [ih p.1 (by have := Finset.mem_antidiagonal.mp hp; omega)]
      have hn : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
      have := eA.trans (hsum.trans eB.symm)
      exact mul_right_cancel₀ hn this

/-- `M_β = -∑_{k ≥ 0} β^{k+1} u^k`, the logarithmic derivative of `1 - βu`. -/
noncomputable def geomLogDeriv (β : ℂ) : ℂ⟦X⟧ := mk fun k => -β ^ (k + 1)

lemma derivative_one_sub (β : ℂ) :
    d⁄dX (1 - C β * X : ℂ⟦X⟧) = (1 - C β * X) * geomLogDeriv β := by
  ext k
  rw [coeff_derivative, sub_mul, one_mul, map_sub, map_sub, mul_assoc, coeff_C_mul, coeff_C_mul]
  rcases k with _ | k
  · simp [geomLogDeriv, coeff_one]
  · simp [geomLogDeriv, coeff_one, coeff_succ_X_mul, coeff_X, pow_succ]
    ring

lemma derivative_prod_one_sub (s : Multiset ℂ) :
    d⁄dX (s.map fun b => (1 - C b * X : ℂ⟦X⟧)).prod =
      (s.map fun b => (1 - C b * X : ℂ⟦X⟧)).prod * (s.map geomLogDeriv).sum := by
  induction s using Multiset.induction_on with
  | empty => simp [derivative_one]
  | cons b s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, Derivation.leibniz, ih, derivative_one_sub,
      Multiset.map_cons, Multiset.sum_cons, smul_eq_mul, smul_eq_mul]
    ring

lemma coeff_sum_geomLogDeriv (s : Multiset ℂ) (k : ℕ) :
    coeff k (s.map geomLogDeriv).sum = -(s.map fun b => b ^ (k + 1)).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons b s ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, map_add, ih, geomLogDeriv, coeff_mk]
    ring

lemma constantCoeff_prod_one_sub (s : Multiset ℂ) :
    constantCoeff (s.map fun b => (1 - C b * X : ℂ⟦X⟧)).prod = 1 := by
  rw [map_multiset_prod, Multiset.map_map]
  have : ∀ b ∈ s, (constantCoeff ∘ fun b => (1 - C b * X : ℂ⟦X⟧)) b = 1 := by
    intro b _; simp
  rw [Multiset.map_congr rfl this, Multiset.map_const', Multiset.prod_replicate, one_pow]

/-- **Proposition 11.1.1 and its converse (Exercise 11.2).** For finitely many complex numbers
`α_i, β_j`: `Z(u) ∏ (1 - β_j u) = ∏ (1 - α_i u)` iff `N_s = ∑ β_j^s - ∑ α_i^s` for all `s ≥ 1`. -/
@[kb "irelandrosen1990" "Prop 11.1.1, p. 166"]
theorem zetaOfCounts_mul_eq_iff (N : ℕ → ℂ) (α β : Multiset ℂ) :
    zetaOfCounts N * (β.map fun b => (1 - C b * X : ℂ⟦X⟧)).prod =
        (α.map fun a => (1 - C a * X : ℂ⟦X⟧)).prod ↔
      ∀ s, 1 ≤ s → N s = (β.map fun b => b ^ s).sum - (α.map fun a => a ^ s).sum := by
  set Bβ := (β.map fun b => (1 - C b * X : ℂ⟦X⟧)).prod
  set Aα := (α.map fun a => (1 - C a * X : ℂ⟦X⟧)).prod
  have hW : d⁄dX (zetaOfCounts N * Bβ) =
      (zetaOfCounts N * Bβ) * ((mk fun k => N (k + 1)) + (β.map geomLogDeriv).sum) := by
    rw [Derivation.leibniz, derivative_zetaOfCounts, derivative_prod_one_sub, smul_eq_mul,
      smul_eq_mul]
    ring
  have hA : d⁄dX Aα = Aα * (α.map geomLogDeriv).sum := derivative_prod_one_sub α
  constructor
  · intro h
    rw [h] at hW
    rw [hA] at hW
    have hA0 : Aα ≠ 0 := by
      intro h0; have := constantCoeff_prod_one_sub α
      change constantCoeff Aα = 1 at this
      rw [h0, map_zero] at this
      exact zero_ne_one this
    have hM := mul_left_cancel₀ hA0 hW
    intro s hs
    obtain ⟨k, rfl⟩ : ∃ k, s = k + 1 := ⟨s - 1, by omega⟩
    have := congrArg (coeff k) hM
    rw [map_add, coeff_mk, coeff_sum_geomLogDeriv, coeff_sum_geomLogDeriv] at this
    linear_combination -this
  · intro h
    have hM : (mk fun k => N (k + 1)) + (β.map geomLogDeriv).sum = (α.map geomLogDeriv).sum := by
      ext k
      rw [map_add, coeff_mk, coeff_sum_geomLogDeriv, coeff_sum_geomLogDeriv, h (k + 1) (by omega)]
      ring
    rw [hM] at hW
    refine eq_of_derivative_eq_mul ?_ hW hA
    rw [map_mul, constantCoeff_zetaOfCounts, constantCoeff_prod_one_sub,
      constantCoeff_prod_one_sub, one_mul]

end NTKB.IrelandRosen
