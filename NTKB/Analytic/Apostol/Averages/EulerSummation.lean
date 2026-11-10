/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.NumberTheory.AbelSummation
import NTKB.Attr

/-!
# Euler's summation formula (Apostol, Theorem 3.1)

If `f` has a continuous derivative on `[y, x]`, `0 ≤ y ≤ x`, then
`∑_{y<n≤x} f(n) = ∫_y^x f + ∫_y^x (t - ⌊t⌋) f'(t) dt + f(x)(⌊x⌋ - x) - f(y)(⌊y⌋ - y)`.

Apostol proves it by splitting `∫_y^x ⌊t⌋ f'(t) dt` at the integers; we take it from Mathlib's Abel
summation formula (`sum_mul_eq_sub_sub_integral_mul`, with all coefficients `1`), which is the same
computation, and integrate `∫ (t + 1) f'(t) dt` by parts.
-/

open Finset MeasureTheory intervalIntegral

namespace NTKB.Apostol

/-- **Theorem 3.1** (Euler's summation formula, Apostol). -/
@[kb "apostol1976" "Thm 3.1, p. 54"]
theorem euler_summation {f f' : ℝ → ℝ} {x y : ℝ} (hy : 0 ≤ y) (hyx : y ≤ x)
    (hf : ∀ t ∈ Set.Icc y x, HasDerivAt f (f' t) t) (hf' : ContinuousOn f' (Set.Icc y x)) :
    ∑ n ∈ Ioc ⌊y⌋₊ ⌊x⌋₊, f n = (∫ t in y..x, f t) + (∫ t in y..x, (t - ⌊t⌋) * f' t) +
      f x * (⌊x⌋ - x) - f y * (⌊y⌋ - y) := by
  have hderiv : Set.EqOn (deriv f) f' (Set.Icc y x) := fun t ht ↦ (hf t ht).deriv
  have hint' : IntegrableOn f' (Set.Icc y x) := hf'.integrableOn_Icc
  have hint : IntegrableOn (deriv f) (Set.Icc y x) := hint'.congr_fun hderiv.symm measurableSet_Icc
  have habel := sum_mul_eq_sub_sub_integral_mul (c := fun _ ↦ (1 : ℝ)) (f := f) hy hyx
    (fun t ht ↦ (hf t ht).differentiableAt) hint
  simp only [mul_one, sum_const, Nat.card_Icc, tsub_zero, nsmul_eq_mul, Nat.cast_add,
    Nat.cast_one] at habel
  -- `⌊t⌋ = ⌊t⌋₊` on `[y, x]`.
  have hfl : ∀ t : ℝ, 0 ≤ t → ((⌊t⌋ : ℤ) : ℝ) = (⌊t⌋₊ : ℝ) := fun t ht ↦ by
    rw [← Int.natCast_floor_eq_floor ht]; rfl
  -- The integral in Abel's formula, with `f'`.
  have hI : ∫ t in Set.Ioc y x, deriv f t * (⌊t⌋₊ + 1) = ∫ t in y..x, f' t * (⌊t⌋₊ + 1) := by
    rw [integral_of_le hyx]
    refine setIntegral_congr_fun measurableSet_Ioc fun t ht ↦ ?_
    simp only [hderiv (Set.Ioc_subset_Icc_self ht)]
  have hA : IntervalIntegrable (fun t ↦ f' t * (⌊t⌋₊ + 1)) volume y x := by
    have h := integrableOn_mul_sum_Icc (c := fun _ ↦ (1 : ℝ)) (m := 0) hy hint'
    simp only [mul_one, sum_const, Nat.card_Icc, tsub_zero, nsmul_eq_mul, Nat.cast_add,
      Nat.cast_one] at h
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le hyx).2 h
  have hB : IntervalIntegrable (fun t ↦ f' t * (t + 1)) volume y x :=
    (hf'.mul (by fun_prop)).intervalIntegrable_of_Icc hyx
  -- Integration by parts: `∫ (t + 1) f'(t) = [(t + 1) f(t)] - ∫ f`.
  have hparts : ∫ t in y..x, f' t * (t + 1) = f x * (x + 1) - f y * (y + 1) - ∫ t in y..x, f t := by
    have h := integral_deriv_mul_eq_sub (a := y) (b := x) (u := f) (u' := f')
      (v := fun t ↦ t + 1) (v' := fun _ ↦ 1)
      (fun t ht ↦ hf t (by rwa [Set.uIcc_of_le hyx] at ht))
      (fun t _ ↦ (hasDerivAt_id t).add_const 1)
      (hf'.intervalIntegrable_of_Icc hyx)
      intervalIntegrable_const
    have hfc : ContinuousOn f (Set.uIcc y x) := fun t ht ↦
      (hf t (by rwa [Set.uIcc_of_le hyx] at ht)).continuousAt.continuousWithinAt
    have h2 : ∫ t in y..x, (f' t * (t + 1) + f t * 1) =
        (∫ t in y..x, f' t * (t + 1)) + ∫ t in y..x, f t := by
      rw [integral_add hB (by simpa using hfc.intervalIntegrable)]
      simp
    rw [h2] at h
    linarith
  have hsaw : ∫ t in y..x, (t - ⌊t⌋) * f' t =
      (∫ t in y..x, f' t * (t + 1)) - ∫ t in y..x, f' t * (⌊t⌋₊ + 1) := by
    rw [← integral_sub hB hA, integral_of_le hyx, integral_of_le hyx]
    refine setIntegral_congr_fun measurableSet_Ioc fun t ht ↦ ?_
    rw [hfl t (hy.trans ht.1.le)]
    ring
  rw [habel, hI, hsaw, hparts, hfl x (hy.trans hyx), hfl y hy]
  ring

end NTKB.Apostol
