/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import NTKB.Attr

/-!
# The contour integral of `u^{-z}/(z(z+1)⋯(z+k))` (Apostol, Chapter 13, Lemma 3)

**Lemma 3.** For `c > 0`, `u > 0` and integers `k ≥ 1`,
`(1/2πi) ∫_{c-i∞}^{c+i∞} u^{-z}/(z(z+1)⋯(z+k)) dz = (1-u)^k/k!` if `0 < u ≤ 1`, `0` if `u > 1`,
the integral being absolutely convergent. With `z = c + iy`, `(1/2πi) ∫ … dz = (1/2π) ∫ … dy`.

Apostol proves this by residues. Here: `1/(z(z+1)⋯(z+k))` is the Mellin transform of
`φ_k(u) = (1-u)^k/k!` on `(0, 1]` (`0` for `u > 1`), a Beta integral; Mathlib's Mellin inversion
theorem (`mellinInv_mellin_eq`) then gives the lemma.
-/

open Complex Filter Topology Finset MeasureTheory Set
open scoped Real

namespace NTKB.Apostol

/-- `φ_k(u) = (1-u)^k/k!` for `u ≤ 1`, `0` for `u > 1`. -/
noncomputable def perronKernelFun (k : ℕ) (u : ℝ) : ℂ :=
  if u ≤ 1 then (((1 - u) ^ k / k.factorial : ℝ) : ℂ) else 0

/-- `z(z+1)⋯(z+k)`. -/
noncomputable def perronDen (k : ℕ) (z : ℂ) : ℂ := ∏ j ∈ range (k + 1), (z + j)

lemma Gamma_add_nat_eq (k : ℕ) {z : ℂ} (hz : 0 < z.re) :
    Gamma (z + (k + 1 : ℕ)) = perronDen k z * Gamma z := by
  induction k with
  | zero =>
    simp only [perronDen, zero_add, Nat.cast_one]
    rw [Finset.prod_range_one, Nat.cast_zero, add_zero]
    exact Gamma_add_one z (fun h ↦ by simp [h] at hz)
  | succ k ih =>
    have hne : z + ((k + 1 : ℕ) : ℂ) ≠ 0 := fun h ↦ by
      have := congrArg re h; simp at this; linarith [k.cast_nonneg (α := ℝ)]
    have hp : perronDen (k + 1) z = perronDen k z * (z + ((k + 1 : ℕ) : ℂ)) := by
      simp only [perronDen]; rw [prod_range_succ _ (k + 1)]
    rw [show z + ((k + 1 + 1 : ℕ) : ℂ) = (z + ((k + 1 : ℕ) : ℂ)) + 1 by push_cast; ring,
      Gamma_add_one _ hne, ih, hp]
    ring

lemma perronDen_ne_zero (k : ℕ) {z : ℂ} (hz : 0 < z.re) : perronDen k z ≠ 0 := by
  rw [perronDen, prod_ne_zero_iff]
  intro j _ h
  have := congrArg re h
  simp at this
  linarith [j.cast_nonneg (α := ℝ)]

/-- `‖z(z+1)⋯(z+k)‖ ≥ ‖z‖²` for `σ > 0`, `k ≥ 1`. -/
lemma norm_perronDen_ge (k : ℕ) (hk : 1 ≤ k) {z : ℂ} (hz : 0 < z.re) :
    ‖z‖ ^ 2 ≤ ‖perronDen k z‖ := by
  obtain ⟨k, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  rw [perronDen, prod_range_succ', prod_range_succ', norm_mul, norm_mul]
  simp only [Nat.cast_zero, add_zero, Nat.cast_one]
  have h1 : ‖z‖ ≤ ‖z + 1‖ := by
    rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), ← normSq_eq_norm_sq, ← normSq_eq_norm_sq]
    simp only [normSq_apply, add_re, add_im, one_re, one_im, add_zero]
    nlinarith
  have h2 : 1 ≤ ‖∏ j ∈ range k, (z + ((j + 1 + 1 : ℕ) : ℂ))‖ := by
    rw [norm_prod]
    refine one_le_prod₀ fun j _ ↦ ?_
    calc (1 : ℝ) ≤ (z + ((j + 1 + 1 : ℕ) : ℂ)).re := by
          simp; linarith [j.cast_nonneg (α := ℝ)]
      _ ≤ ‖z + ((j + 1 + 1 : ℕ) : ℂ)‖ := re_le_norm _
  calc ‖z‖ ^ 2 = 1 * ‖z + 1‖ * ‖z‖ * (‖z‖ / ‖z + 1‖) := by
        have : ‖z + 1‖ ≠ 0 := by
          intro h; rw [norm_eq_zero] at h; have := congrArg re h; simp at this; linarith
        field_simp
    _ ≤ ‖∏ j ∈ range k, (z + ((j + 1 + 1 : ℕ) : ℂ))‖ * ‖z + 1‖ * ‖z‖ := by
        have : ‖z‖ / ‖z + 1‖ ≤ 1 := div_le_one_of_le₀ h1 (norm_nonneg _)
        have : 0 ≤ ‖z + 1‖ * ‖z‖ := by positivity
        nlinarith [norm_nonneg z]
    _ = _ := by push_cast; ring_nf

/-- The Mellin transform of `φ_k` is `1/(z(z+1)⋯(z+k))` for `σ > 0`. -/
lemma mellin_perronKernelFun (k : ℕ) {z : ℂ} (hz : 0 < z.re) :
    mellin (perronKernelFun k) z = 1 / perronDen k z := by
  have hk : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have h1 : mellin (perronKernelFun k) z =
      ∫ t in (0 : ℝ)..1, (t : ℂ) ^ (z - 1) * (1 - (t : ℂ)) ^ ((k + 1 : ℂ) - 1) / k.factorial := by
    rw [mellin, setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
      Ioc_subset_Ioi_self (fun t ht ↦ by
        have : 1 < t := by
          rcases ht with ⟨h0, h1⟩
          simp only [Set.mem_Ioc, not_and, not_le] at h1
          exact h1 h0
        simp [perronKernelFun, not_le.mpr this]),
      ← intervalIntegral.integral_of_le zero_le_one]
    refine intervalIntegral.integral_congr fun t ht ↦ ?_
    rw [Set.uIcc_of_le zero_le_one] at ht
    simp only [perronKernelFun, ht.2, ↓reduceIte, smul_eq_mul]
    rw [show (k + 1 : ℂ) - 1 = (k : ℕ) by ring, cpow_natCast]
    push_cast
    ring
  rw [h1, intervalIntegral.integral_div]
  have hB := Gamma_mul_Gamma_eq_betaIntegral hz (t := (k + 1 : ℂ)) (by simp; positivity)
  rw [show (k + 1 : ℂ) = ((k : ℕ) : ℂ) + 1 by push_cast; ring, Gamma_nat_eq_factorial,
    show z + ((k : ℕ) + 1 : ℂ) = z + ((k + 1 : ℕ) : ℂ) by push_cast; ring,
    Gamma_add_nat_eq k hz] at hB
  have hG := Gamma_ne_zero_of_re_pos hz
  have hP := perronDen_ne_zero k hz
  show betaIntegral z ((k : ℂ) + 1) / k.factorial = 1 / perronDen k z
  have hBP : betaIntegral z ((k : ℂ) + 1) * perronDen k z = k.factorial :=
    mul_left_cancel₀ hG (by linear_combination -hB)
  rw [div_eq_div_iff hk hP]
  linear_combination hBP

lemma mellinConvergent_perronKernelFun (k : ℕ) {c : ℝ} (hc : 0 < c) :
    MellinConvergent (perronKernelFun k) c := by
  have hB := betaIntegral_convergent (u := (c : ℂ)) (v := (k : ℂ) + 1) (by simpa using hc)
    (by simp; positivity)
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at hB
  have h1 : IntegrableOn (fun t : ℝ ↦ (t : ℂ) ^ ((c : ℂ) - 1) • perronKernelFun k t) (Ioc 0 1) := by
    refine IntegrableOn.congr_fun (hB.div_const (k.factorial : ℂ)) (fun t ht ↦ ?_) measurableSet_Ioc
    simp only [perronKernelFun, ht.2, ↓reduceIte, smul_eq_mul]
    rw [show (k : ℂ) + 1 - 1 = (k : ℕ) by ring, cpow_natCast]
    push_cast
    ring
  refine h1.of_forall_sdiff_eq_zero measurableSet_Ioi fun t ht ↦ ?_
  have : 1 < t := by
    rcases ht with ⟨h0, h1⟩
    simp only [Set.mem_Ioc, not_and, not_le] at h1
    exact h1 h0
  simp [perronKernelFun, not_le.mpr this]

lemma perronKernelFun_eq (k : ℕ) (hk : 1 ≤ k) :
    perronKernelFun k = fun u : ℝ ↦ (((max (1 - u) 0) ^ k / k.factorial : ℝ) : ℂ) := by
  funext u
  simp only [perronKernelFun]
  split_ifs with h
  · rw [max_eq_left (by linarith)]
  · rw [max_eq_right (by linarith), zero_pow (by omega), zero_div, ofReal_zero]

lemma verticalIntegrable_perronDen (k : ℕ) (hk : 1 ≤ k) {c : ℝ} (hc : 0 < c) :
    Integrable (fun y : ℝ ↦ 1 / perronDen k (c + y * I)) := by
  refine ((integrable_inv_one_add_sq).const_mul (1 + 1 / c ^ 2)).mono' ?_
    (Eventually.of_forall fun y ↦ ?_)
  · refine Continuous.aestronglyMeasurable ?_
    refine continuous_const.div (by unfold perronDen; fun_prop) fun y ↦ perronDen_ne_zero k ?_
    simpa using hc
  · have hre : 0 < (c + y * I).re := by simpa using hc
    have hP := norm_perronDen_ge k hk hre
    have hn : ‖(c : ℂ) + y * I‖ ^ 2 = c ^ 2 + y ^ 2 := by
      rw [← normSq_eq_norm_sq, normSq_apply]; simp; ring
    rw [hn] at hP
    rw [norm_div, norm_one]
    have hpos : 0 < c ^ 2 + y ^ 2 := by positivity
    calc 1 / ‖perronDen k (c + y * I)‖ ≤ 1 / (c ^ 2 + y ^ 2) :=
          one_div_le_one_div_of_le hpos hP
      _ ≤ (1 + 1 / c ^ 2) * (1 + y ^ 2)⁻¹ := by
          rw [div_le_iff₀ hpos]
          field_simp
          nlinarith [sq_nonneg y, sq_nonneg c, sq_nonneg (y * y)]

/-- **Apostol, Chapter 13, Lemma 3**: for `c > 0`, `u > 0`, `k ≥ 1`,
`(1/2πi) ∫_{c-i∞}^{c+i∞} u^{-z}/(z(z+1)⋯(z+k)) dz = (1-u)^k/k!` for `u ≤ 1`, `0` for `u > 1`
(written with `z = c + iy`, `dz = i dy`); the integral converges absolutely. -/
@[kb "apostol1976" "Lemma 3 (Ch. 13), p. 281"]
theorem ch13_lemma_3 {c : ℝ} (hc : 0 < c) {u : ℝ} (hu : 0 < u) {k : ℕ} (hk : 1 ≤ k) :
    Integrable (fun y : ℝ ↦ (u : ℂ) ^ (-((c : ℂ) + y * I)) / perronDen k (c + y * I)) ∧
    (1 / (2 * π)) * ∫ y : ℝ, (u : ℂ) ^ (-((c : ℂ) + y * I)) / perronDen k (c + y * I) =
      perronKernelFun k u := by
  have hmel : ∀ y : ℝ, mellin (perronKernelFun k) (c + y * I) = 1 / perronDen k (c + y * I) :=
    fun y ↦ mellin_perronKernelFun k (by simpa using hc)
  constructor
  · refine ((verticalIntegrable_perronDen k hk hc).bdd_mul
      (f := fun y : ℝ ↦ (u : ℂ) ^ (-((c : ℂ) + y * I))) (c := u ^ (-c)) ?_ ?_).congr ?_
    · exact (Continuous.aestronglyMeasurable (by
        refine Continuous.const_cpow (by fun_prop) (Or.inl (by exact_mod_cast hu.ne'))))
    · refine Eventually.of_forall fun y ↦ ?_
      rw [norm_cpow_eq_rpow_re_of_pos hu]; simp
    · exact Eventually.of_forall fun y ↦ by simp [div_eq_mul_inv]
  · have h := mellinInv_mellin_eq (c : ℝ) (perronKernelFun k) hu
      (mellinConvergent_perronKernelFun k hc)
      (by
        change Integrable (fun y : ℝ ↦ mellin (perronKernelFun k) (c + y * I))
        simp_rw [hmel]
        exact verticalIntegrable_perronDen k hk hc)
      (by rw [perronKernelFun_eq k hk]; fun_prop)
    rw [mellinInv] at h
    simp_rw [hmel, smul_eq_mul] at h
    rw [← h]
    simp [div_eq_mul_inv]

end NTKB.Apostol
