/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Analysis.MeanInequalities
import NTKB.Attr

/-!
# Bessel's inequality for almost orthogonal vectors (Davenport, Chapter 27, Theorem 1)

For vectors `φ_1, …, φ_R` of a complex inner product space and a constant `A`:

* **Boas**: the inequality (A) `∑_r |(ξ, φ_r)|² ≤ A ‖ξ‖²` holds for all `ξ` if and only if the
  bilinear form inequality (B) `|∑_{r,s} u_r ū_s (φ_r, φ_s)| ≤ A ∑_r |u_r|²` holds for all complex
  `u_r` (`boas_iff`);
* **Theorem 1**: (A) holds with `A = max_r ∑_s |(φ_r, φ_s)|` (`sum_norm_inner_sq_le`), by
  `|u_r ū_s| ≤ (|u_r|² + |u_s|²)/2` in (B). For orthonormal `φ_r` this is Bessel's inequality.

Davenport's inner product `(ξ, φ)` is linear in `ξ`; Mathlib's `⟪φ, ξ⟫_ℂ` is linear in `ξ` and
conjugate linear in `φ`, so Davenport's `(ξ, φ_r)` is `conj ⟪φ_r, ξ⟫_ℂ` and his `(φ_r, φ_s)` is
`⟪φ_s, φ_r⟫_ℂ`; absolute values are unchanged.
-/

open Finset ComplexConjugate
open scoped InnerProductSpace

namespace NTKB.Davenport

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {ι : Type*}

/-- `‖∑ u_r φ_r‖² = ∑_{r,s} u_r ū_s (φ_r, φ_s)`. -/
lemma norm_sum_smul_sq (s : Finset ι) (φ : ι → E) (u : ι → ℂ) :
    ((‖∑ r ∈ s, u r • φ r‖ ^ 2 : ℝ) : ℂ) =
      ∑ r ∈ s, ∑ t ∈ s, u r * conj (u t) * ⟪φ t, φ r⟫_ℂ := by
  have h := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (∑ r ∈ s, u r • φ r)
  rw [show ((‖∑ r ∈ s, u r • φ r‖ ^ 2 : ℝ) : ℂ) = ⟪∑ r ∈ s, u r • φ r, ∑ r ∈ s, u r • φ r⟫_ℂ by
    rw [h]; norm_cast]
  rw [sum_inner, sum_comm]
  refine sum_congr rfl fun r _ ↦ ?_
  rw [inner_sum]
  refine sum_congr rfl fun t _ ↦ ?_
  rw [inner_smul_left, inner_smul_right]
  ring

/-- **Boas**, (B) ⟹ (A). -/
theorem sum_norm_inner_sq_le_of_bilinear (s : Finset ι) (φ : ι → E) {A : ℝ} (hA : 0 ≤ A)
    (hB : ∀ u : ι → ℂ, ‖∑ r ∈ s, ∑ t ∈ s, u r * conj (u t) * ⟪φ t, φ r⟫_ℂ‖ ≤
      A * ∑ r ∈ s, ‖u r‖ ^ 2) (ξ : E) :
    ∑ r ∈ s, ‖⟪φ r, ξ⟫_ℂ‖ ^ 2 ≤ A * ‖ξ‖ ^ 2 := by
  classical
  rcases hA.eq_or_lt with rfl | hA
  · -- `A = 0`: every `φ_r` vanishes
    have hφ : ∀ r ∈ s, φ r = 0 := by
      intro r hr
      have h := hB (Pi.single r 1)
      rw [← norm_sum_smul_sq] at h
      simp only [zero_mul, Complex.norm_real, norm_pow, norm_norm] at h
      have h' : ‖∑ t ∈ s, (Pi.single r (1 : ℂ) : ι → ℂ) t • φ t‖ ^ 2 ≤ 0 := by
        simpa using h
      rw [sum_eq_single_of_mem r hr (fun t _ ht ↦ by simp [ht])] at h'
      simpa using h'
    rw [zero_mul]
    exact (sum_eq_zero fun r hr ↦ by rw [hφ r hr]; simp).le
  -- `A > 0`: Davenport's choice `u_r = (ξ, φ_r)/A`
  set c : ι → ℂ := fun r ↦ ⟪φ r, ξ⟫_ℂ
  set S : ℝ := ∑ r ∈ s, ‖c r‖ ^ 2
  set u : ι → ℂ := fun r ↦ c r / A
  have h0 : 0 ≤ ‖ξ - ∑ r ∈ s, u r • φ r‖ ^ 2 := by positivity
  have hexp : ‖ξ - ∑ r ∈ s, u r • φ r‖ ^ 2 =
      ‖ξ‖ ^ 2 - 2 * (∑ r ∈ s, (conj (u r) * c r)).re + ‖∑ r ∈ s, u r • φ r‖ ^ 2 := by
    rw [@norm_sub_sq ℂ, inner_sum, RCLike.re_to_complex]
    congr 2
    rw [Complex.re_sum, Complex.re_sum]
    congr 1
    refine sum_congr rfl fun r _ ↦ ?_
    rw [inner_smul_right, ← inner_conj_symm]
    have : u r * (starRingEnd ℂ) ⟪φ r, ξ⟫_ℂ = (starRingEnd ℂ) ((starRingEnd ℂ) (u r) * c r) := by
      simp [c]
    rw [this, Complex.conj_re]
  have hcross : (∑ r ∈ s, (conj (u r) * c r)).re = S / A := by
    simp only [S]
    rw [Complex.re_sum, sum_div]
    refine sum_congr rfl fun r _ ↦ ?_
    simp only [u, map_div₀, Complex.conj_ofReal]
    rw [div_mul_eq_mul_div, Complex.div_ofReal_re, mul_comm, Complex.mul_conj,
      Complex.normSq_eq_norm_sq, Complex.ofReal_re]
  have hquad : ‖∑ r ∈ s, u r • φ r‖ ^ 2 ≤ S / A := by
    have h := hB u
    rw [← norm_sum_smul_sq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      at h
    refine h.trans (le_of_eq ?_)
    simp only [u, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hA, div_pow, ← sum_div]
    field_simp
    rfl
  rw [hexp, hcross] at h0
  have : S / A ≤ ‖ξ‖ ^ 2 := by linarith
  rwa [div_le_iff₀ hA, mul_comm] at this

/-- **Boas**, (A) ⟹ (B). -/
theorem bilinear_le_of_sum_norm_inner_sq_le (s : Finset ι) (φ : ι → E) {A : ℝ} (hA0 : 0 ≤ A)
    (hA : ∀ ξ : E, ∑ r ∈ s, ‖⟪φ r, ξ⟫_ℂ‖ ^ 2 ≤ A * ‖ξ‖ ^ 2) (u : ι → ℂ) :
    ‖∑ r ∈ s, ∑ t ∈ s, u r * conj (u t) * ⟪φ t, φ r⟫_ℂ‖ ≤ A * ∑ r ∈ s, ‖u r‖ ^ 2 := by
  rw [← norm_sum_smul_sq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  obtain ⟨ξ, hξdef⟩ : ∃ ξ, ξ = ∑ r ∈ s, u r • φ r := ⟨_, rfl⟩
  rw [← hξdef]
  -- `‖ξ‖² = ∑_t ū_t (ξ, φ_t)` and Cauchy's inequality
  have hξ : ‖ξ‖ ^ 2 = (∑ t ∈ s, conj (u t) * ⟪φ t, ξ⟫_ℂ).re := by
    rw [← @inner_self_eq_norm_sq ℂ]
    nth_rewrite 1 [hξdef]
    rw [sum_inner, RCLike.re_to_complex, Complex.re_sum, Complex.re_sum]
    refine sum_congr rfl fun t _ ↦ ?_
    rw [inner_smul_left]
  set U := ∑ t ∈ s, ‖u t‖ ^ 2
  have hcs : ‖ξ‖ ^ 2 ≤ √U * √(∑ t ∈ s, ‖⟪φ t, ξ⟫_ℂ‖ ^ 2) := by
    rw [hξ]
    refine (Complex.re_le_norm _).trans ((norm_sum_le _ _).trans ?_)
    simp only [norm_mul, Complex.norm_conj]
    exact Real.sum_mul_le_sqrt_mul_sqrt _ _ _
  have h2 : √(∑ t ∈ s, ‖⟪φ t, ξ⟫_ℂ‖ ^ 2) ≤ √A * ‖ξ‖ := by
    rw [← Real.sqrt_sq (norm_nonneg ξ), ← Real.sqrt_mul hA0]
    exact Real.sqrt_le_sqrt (hA ξ)
  have hU : 0 ≤ U := sum_nonneg fun _ _ ↦ by positivity
  rcases (norm_nonneg ξ).eq_or_lt with h | hpos
  · rw [← h, sq, zero_mul]; exact mul_nonneg hA0 hU
  have h3 : ‖ξ‖ ^ 2 ≤ (√U * √A) * ‖ξ‖ := by
    calc ‖ξ‖ ^ 2 ≤ √U * (√A * ‖ξ‖) := hcs.trans (mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg _))
      _ = _ := by ring
  have h4 : ‖ξ‖ ≤ √U * √A := by
    rw [sq] at h3; exact le_of_mul_le_mul_right h3 hpos
  calc ‖ξ‖ ^ 2 ≤ (√U * √A) ^ 2 := by gcongr
    _ = A * U := by rw [mul_pow, Real.sq_sqrt hU, Real.sq_sqrt hA0]; ring

/-- **Davenport, Ch. 27 (Boas)**: for `A ≥ 0`, inequality (A) holds for all `ξ` if and only if the
bilinear form inequality (B) holds for all complex `u_r`. -/
@[kb "davenport1980" "Ch 27, p. 151"]
theorem boas_iff (s : Finset ι) (φ : ι → E) {A : ℝ} (hA : 0 ≤ A) :
    (∀ ξ : E, ∑ r ∈ s, ‖⟪φ r, ξ⟫_ℂ‖ ^ 2 ≤ A * ‖ξ‖ ^ 2) ↔
      ∀ u : ι → ℂ, ‖∑ r ∈ s, ∑ t ∈ s, u r * conj (u t) * ⟪φ t, φ r⟫_ℂ‖ ≤
        A * ∑ r ∈ s, ‖u r‖ ^ 2 :=
  ⟨bilinear_le_of_sum_norm_inner_sq_le s φ hA, sum_norm_inner_sq_le_of_bilinear s φ hA⟩

/-- **Davenport, Ch. 27, Theorem 1**: for arbitrary vectors `φ_r` and `ξ` of a complex inner
product space, `∑_r |(ξ, φ_r)|² ≤ A ‖ξ‖²` with `A = max_r ∑_s |(φ_r, φ_s)|` (here: any `A` bounding
every row sum; `A ≥ 0` is automatic when there is at least one vector). -/
@[kb "davenport1980" "Ch 27, p. 153, Theorem 1"]
theorem sum_norm_inner_sq_le (s : Finset ι) (φ : ι → E) {A : ℝ} (hA0 : 0 ≤ A)
    (hA : ∀ r ∈ s, ∑ t ∈ s, ‖⟪φ r, φ t⟫_ℂ‖ ≤ A) (ξ : E) :
    ∑ r ∈ s, ‖⟪φ r, ξ⟫_ℂ‖ ^ 2 ≤ A * ‖ξ‖ ^ 2 := by
  refine sum_norm_inner_sq_le_of_bilinear s φ hA0 (fun u ↦ ?_) ξ
  -- `|u_r ū_t| ≤ (|u_r|² + |u_t|²)/2` and the symmetry `|(φ_r, φ_t)| = |(φ_t, φ_r)|`
  have hsym : ∀ r t, ‖⟪φ t, φ r⟫_ℂ‖ = ‖⟪φ r, φ t⟫_ℂ‖ := fun r t ↦ by
    rw [← inner_conj_symm, Complex.norm_conj]
  calc ‖∑ r ∈ s, ∑ t ∈ s, u r * conj (u t) * ⟪φ t, φ r⟫_ℂ‖
      ≤ ∑ r ∈ s, ∑ t ∈ s, ‖u r‖ * ‖u t‖ * ‖⟪φ r, φ t⟫_ℂ‖ := by
        refine (norm_sum_le _ _).trans (sum_le_sum fun r _ ↦ (norm_sum_le _ _).trans
          (sum_le_sum fun t _ ↦ ?_))
        rw [norm_mul, norm_mul, Complex.norm_conj, hsym]
    _ ≤ ∑ r ∈ s, ∑ t ∈ s, (‖u r‖ ^ 2 / 2 + ‖u t‖ ^ 2 / 2) * ‖⟪φ r, φ t⟫_ℂ‖ := by
        gcongr with r _ t _
        nlinarith [sq_nonneg (‖u r‖ - ‖u t‖)]
    _ = ∑ r ∈ s, ‖u r‖ ^ 2 * ∑ t ∈ s, ‖⟪φ r, φ t⟫_ℂ‖ := by
        simp only [add_mul, sum_add_distrib]
        have h2 : ∑ r ∈ s, ∑ t ∈ s, ‖u t‖ ^ 2 / 2 * ‖⟪φ r, φ t⟫_ℂ‖ =
            ∑ r ∈ s, ∑ t ∈ s, ‖u r‖ ^ 2 / 2 * ‖⟪φ r, φ t⟫_ℂ‖ := by
          rw [sum_comm]
          refine sum_congr rfl fun r _ ↦ sum_congr rfl fun t _ ↦ ?_
          rw [hsym]
        rw [h2, ← two_mul, mul_sum]
        refine sum_congr rfl fun r _ ↦ ?_
        rw [mul_sum, mul_sum]
        refine sum_congr rfl fun t _ ↦ ?_
        ring
    _ ≤ ∑ r ∈ s, ‖u r‖ ^ 2 * A := by
        gcongr with r hr
        exact hA r hr
    _ = A * ∑ r ∈ s, ‖u r‖ ^ 2 := by rw [← sum_mul, mul_comm]

/-- Bessel's inequality as the case `A = 1` of Theorem 1 (orthonormal `φ_r`). -/
@[kb "davenport1980" "Ch 27, p. 151"]
theorem sum_norm_inner_sq_le_of_orthonormal (s : Finset ι) {φ : ι → E} (hφ : Orthonormal ℂ φ)
    (ξ : E) : ∑ r ∈ s, ‖⟪φ r, ξ⟫_ℂ‖ ^ 2 ≤ ‖ξ‖ ^ 2 := by
  classical
  have := sum_norm_inner_sq_le s φ (A := 1) zero_le_one (fun r hr ↦ by
    rw [sum_eq_single_of_mem r hr (fun t _ ht ↦ by rw [orthonormal_iff_ite.1 hφ, if_neg ht.symm,
      norm_zero])]
    rw [orthonormal_iff_ite.1 hφ, if_pos rfl, norm_one]) ξ
  rwa [one_mul] at this

end NTKB.Davenport
