/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.NumberTheory.DirichletCharacter.GaussSum
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.NumberTheory.LSeries.HurwitzZeta
import Mathlib.NumberTheory.LSeries.RiemannZeta
import NTKB.Attr

/-!
# The Fourier expansion of a primitive character and the Hurwitz zeta function at `1/2`
(Davenport, Chapter 9, rows 9-6 and 9-15)

* **9-6**: for a primitive character `χ` modulo `N`,
  `χ(n) = τ(χ̄)⁻¹ ∑_m χ̄(m) e(mn/N)` (`IsPrimitive.eq_inv_gaussSum_mul_sum`); `χ̄ = χ⁻¹` is the
  complex conjugate character (`inv_apply_eq_conj`). Mathlib has the Gauss sum identity
  `gaussSum_mulShift_of_isPrimitive` (`τ(χ̄, e(n·/N)) = χ(n) τ(χ̄)`), from which this is the
  inversion.
* **9-15**: the Hurwitz zeta function `ζ(s, a) = ∑_{n ≥ 0} (n + a)^{-s}` is Mathlib's
  `hurwitzZeta` (series for `Re s > 1` and `0 ≤ a ≤ 1`: `HurwitzZeta.hasSum_hurwitzZeta_of_one_lt_re`);
  here `ζ(s, 1) = ζ(s)` (`hurwitzZeta_one`) and `ζ(s, 1/2) = (2^s - 1) ζ(s)` for every `s ≠ 1`
  (`hurwitzZeta_one_half`: the series identity for `Re s > 1`, then analytic continuation).

Source text unavailable; written from the map rows 9-6 and 9-15.
-/

open Complex HurwitzZeta

namespace NTKB.Davenport

/-- `χ⁻¹(m) = conj χ(m)` for a Dirichlet character with complex values. -/
theorem inv_apply_eq_conj {N : ℕ} (χ : DirichletCharacter ℂ N) (m : ZMod N) :
    χ⁻¹ m = (starRingEnd ℂ) (χ m) := by
  have := MulChar.star_apply' χ m
  simpa using this.symm

/-- **Davenport, Ch. 9, p. 68 (row 9-6)**: for primitive `χ` modulo `N`,
`χ(n) = τ(χ̄)⁻¹ ∑_m χ̄(m) e(mn/N)`. -/
@[kb "davenport1980" "Ch 9, p. 68"]
theorem IsPrimitive.eq_inv_gaussSum_mul_sum {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ.IsPrimitive) (n : ZMod N) :
    χ n = (gaussSum χ⁻¹ (ZMod.stdAddChar : AddChar (ZMod N) ℂ))⁻¹ *
      ∑ m : ZMod N, χ⁻¹ m * ZMod.stdAddChar (m * n) := by
  have hne : gaussSum χ⁻¹ (ZMod.stdAddChar : AddChar (ZMod N) ℂ) ≠ 0 := by
    intro h0
    have hp := hχ.inv
    have h1 : ZMod.dft (χ⁻¹ : DirichletCharacter ℂ N) = 0 := by
      funext k
      rw [DirichletCharacter.IsPrimitive.fourierTransform_eq_inv_mul_gaussSum hp, h0]
      simp
    have h2 := congrFun (ZMod.dft_dft (χ⁻¹ : DirichletCharacter ℂ N)) (-1)
    rw [h1] at h2
    simp at h2
    exact (NeZero.ne (N : ℂ)) h2.symm
  have h := gaussSum_mulShift_of_isPrimitive (e := (ZMod.stdAddChar : AddChar (ZMod N) ℂ))
    hχ.inv n
  rw [inv_inv] at h
  rw [eq_inv_mul_iff_mul_eq₀ hne, mul_comm, ← h]
  unfold gaussSum
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [AddChar.mulShift_apply, mul_comm n m]

/-- `ζ(s, 1) = ζ(s)`. -/
theorem hurwitzZeta_one (s : ℂ) : hurwitzZeta ((1 : ℝ) : UnitAddCircle) s = riemannZeta s := by
  rw [show ((1 : ℝ) : UnitAddCircle) = 0 from by
    rw [← QuotientAddGroup.mk_zero]; exact (QuotientAddGroup.eq_zero_iff _).2 ⟨1, by simp⟩,
    hurwitzZeta_zero]

/-- The series identity `ζ(s, 1/2) = (2^s - 1) ζ(s)` for `Re s > 1`. -/
theorem hurwitzZeta_one_half_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    hurwitzZeta ((1 / 2 : ℝ) : UnitAddCircle) s = (2 ^ s - 1) * riemannZeta s := by
  have hH := hasSum_hurwitzZeta_of_one_lt_re (a := 1 / 2) ⟨by norm_num, by norm_num⟩ hs
  have hζ : HasSum (fun n : ℕ ↦ 1 / ((n : ℂ) + 1) ^ s) (riemannZeta s) := by
    have := hasSum_hurwitzZeta_of_one_lt_re (a := 1) ⟨zero_le_one, le_rfl⟩ hs
    rw [show ((1 : ℝ) : UnitAddCircle) = 0 from by
      rw [← QuotientAddGroup.mk_zero]; exact (QuotientAddGroup.eq_zero_iff _).2 ⟨1, by simp⟩,
      hurwitzZeta_zero] at this
    simpa using this
  have h2s : (2 : ℂ) ^ s ≠ 0 := by simp
  -- even-indexed terms
  have hev : HasSum (fun k : ℕ ↦ 1 / (((2 * k : ℕ) : ℂ) + 1) ^ s)
      (∑' k : ℕ, 1 / (((2 * k : ℕ) : ℂ) + 1) ^ s) :=
    (hζ.summable.comp_injective (mul_right_injective₀ (two_ne_zero' ℕ))).hasSum
  have hodd : HasSum (fun k : ℕ ↦ 1 / (((2 * k + 1 : ℕ) : ℂ) + 1) ^ s)
      ((2 : ℂ) ^ (-s) * riemannZeta s) := by
    have := hζ.mul_left ((2 : ℂ) ^ (-s))
    convert this using 2 with k
    have h : (((2 * k + 1 : ℕ) : ℂ) + 1) = ((2 : ℝ) : ℂ) * (((k : ℝ) + 1 : ℝ) : ℂ) := by
      push_cast; ring
    rw [h, Complex.mul_cpow_ofReal_nonneg (by norm_num) (by positivity), cpow_neg]
    push_cast
    field_simp
  have htot := HasSum.even_add_odd (f := fun n : ℕ ↦ 1 / ((n : ℂ) + 1) ^ s) hev hodd
  have hO : ∑' k : ℕ, 1 / (((2 * k : ℕ) : ℂ) + 1) ^ s =
      (1 - (2 : ℂ) ^ (-s)) * riemannZeta s := by
    have := htot.unique hζ
    linear_combination this
  have hH2 : HasSum (fun n : ℕ ↦ 1 / ((n : ℂ) + ((1 / 2 : ℝ) : ℂ)) ^ s)
      ((2 : ℂ) ^ s * ∑' k : ℕ, 1 / (((2 * k : ℕ) : ℂ) + 1) ^ s) := by
    have := hev.mul_left ((2 : ℂ) ^ s)
    convert this using 2 with k
    have h : (((2 * k : ℕ) : ℂ) + 1) = ((2 : ℝ) : ℂ) * (((k : ℝ) + 1 / 2 : ℝ) : ℂ) := by
      push_cast; ring
    rw [h, Complex.mul_cpow_ofReal_nonneg (by norm_num) (by positivity)]
    push_cast
    field_simp
  rw [hH.unique hH2, hO, cpow_neg]
  field_simp

/-- **Davenport, Ch. 9, p. 71 (row 9-15)**: `ζ(s, 1/2) = (2^s - 1) ζ(s)` for `s ≠ 1`. -/
@[kb "davenport1980" "Ch 9, p. 71"]
theorem hurwitzZeta_one_half {s : ℂ} (hs : s ≠ 1) :
    hurwitzZeta ((1 / 2 : ℝ) : UnitAddCircle) s = (2 ^ s - 1) * riemannZeta s := by
  have hconn := (isConnected_compl_singleton_of_one_lt_rank
    (by simp : 1 < Module.rank ℝ ℂ) (1 : ℂ)).isPreconnected
  have hf : AnalyticOnNhd ℂ (fun s ↦ hurwitzZeta ((1 / 2 : ℝ) : UnitAddCircle) s) {1}ᶜ := by
    refine DifferentiableOn.analyticOnNhd ?_ isOpen_compl_singleton
    intro z hz
    exact (differentiableAt_hurwitzZeta _ (by simpa using hz)).differentiableWithinAt
  have hg : AnalyticOnNhd ℂ (fun s : ℂ ↦ (2 ^ s - 1) * riemannZeta s) {1}ᶜ := by
    refine DifferentiableOn.analyticOnNhd ?_ isOpen_compl_singleton
    intro z hz
    refine DifferentiableAt.differentiableWithinAt ?_
    have hz' : z ≠ 1 := by simpa using hz
    have h2 : DifferentiableAt ℂ (fun s : ℂ ↦ (2 : ℂ) ^ s) z :=
      DifferentiableAt.const_cpow (c := (2 : ℂ)) (f := fun s : ℂ ↦ s) differentiableAt_fun_id
        (Or.inl two_ne_zero)
    exact (h2.sub (differentiableAt_const _)).mul (differentiableAt_riemannZeta hz')
  exact hf.eqOn_of_preconnected_of_eventuallyEq hg hconn (by simp : (2 : ℂ) ∈ _)
    (Filter.eventuallyEq_of_mem
      (((isOpen_lt continuous_const continuous_re : IsOpen {z : ℂ | (1 : ℝ) < z.re})).mem_nhds
        (by simp))
      fun z (hz : (1 : ℝ) < z.re) ↦ hurwitzZeta_one_half_of_one_lt_re hz) hs

end NTKB.Davenport
