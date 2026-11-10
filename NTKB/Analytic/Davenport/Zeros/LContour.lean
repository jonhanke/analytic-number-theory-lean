/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Davenport.Zeros.LResidues

/-!
# The contour integral of `-L'/L(s, χ) x^s/s`

**Davenport, Ch. 19, pp. 115-116.** For primitive `χ` mod `q > 1`, `x > 0`, `c > 1` and `T > 0`
not the ordinate of a zero, the integral of `F(s, χ) = -L'/L(s, χ) x^s/s` around the rectangle
with corners `-1/2 - iT`, `c + iT` is `2πi (r₀ - ∑_{|γ|<T} x^ρ/ρ)`, where the residue at `0` is
`r₀ = -L'/L(0, χ)` (odd `χ`) or `r₀ = -(log x + b(χ))` (even `χ`). (We stop the contour at
`σ = -1/2` instead of letting it go to `-∞`; the left side is estimated in `LExplicitFormula`.)
-/

open Filter Topology Complex Set DirichletCharacter MeasureTheory
open scoped Real Interval

namespace NTKB

/-- The integral of a derivative around a rectangle vanishes. -/
lemma rectIntegral_deriv_eq_zero {f f' : ℂ → ℂ} {z w : ℂ}
    (hf : ∀ s, OnRectBoundary z w s → HasDerivAt f (f' s) s)
    (hc : ∀ s, OnRectBoundary z w s → ContinuousAt f' s) : rectIntegral f' z w = 0 := by
  have hI := rectIntegrable_of_continuousAt hc
  have hb1 : ∀ x ∈ [[z.re, w.re]], OnRectBoundary z w (x + z.im * I) := fun x hx ↦
    ⟨by simp [mem_reProdIm, hx, left_mem_uIcc], fun h' ↦ by
      have := (mem_reProdIm.mp h').2; simp at this; linarith [this.1, this.2]⟩
  have hb2 : ∀ x ∈ [[z.re, w.re]], OnRectBoundary z w (x + w.im * I) := fun x hx ↦
    ⟨by simp [mem_reProdIm, hx, right_mem_uIcc], fun h' ↦ by
      have := (mem_reProdIm.mp h').2; simp at this; linarith [this.1, this.2]⟩
  have hb3 : ∀ y ∈ [[z.im, w.im]], OnRectBoundary z w (w.re + y * I) := fun y hy ↦
    ⟨by simp [mem_reProdIm, hy, right_mem_uIcc], fun h' ↦ by
      have := (mem_reProdIm.mp h').1; simp at this; linarith [this.1, this.2]⟩
  have hb4 : ∀ y ∈ [[z.im, w.im]], OnRectBoundary z w (z.re + y * I) := fun y hy ↦
    ⟨by simp [mem_reProdIm, hy, left_mem_uIcc], fun h' ↦ by
      have := (mem_reProdIm.mp h').1; simp at this; linarith [this.1, this.2]⟩
  -- horizontal sides
  have hh : ∀ (c : ℝ), (∀ x ∈ [[z.re, w.re]], OnRectBoundary z w (x + c * I)) →
      IntervalIntegrable (fun x : ℝ ↦ f' (x + c * I)) volume z.re w.re →
      ∫ x : ℝ in z.re..w.re, f' (x + c * I) = f (w.re + c * I) - f (z.re + c * I) := by
    intro c hbc hint
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun x : ℝ ↦ f (x + c * I))
      (fun x hx ↦ ?_) hint
    have h1 := (hf _ (hbc x hx)).comp_add_const (x : ℂ) (c * I)
    exact (HasDerivAt.comp_ofReal (e := fun u : ℂ ↦ f (u + c * I)) (by simpa using h1))
  -- vertical sides
  have hv : ∀ (c : ℝ), (∀ y ∈ [[z.im, w.im]], OnRectBoundary z w (c + y * I)) →
      IntervalIntegrable (fun y : ℝ ↦ f' (c + y * I)) volume z.im w.im →
      I * ∫ y : ℝ in z.im..w.im, f' (c + y * I) = f (c + w.im * I) - f (c + z.im * I) := by
    intro c hbc hint
    have hd : ∀ y ∈ [[z.im, w.im]], HasDerivAt (fun y : ℝ ↦ f (c + y * I)) (f' (c + y * I) * I) y := by
      intro y hy
      have h1 : HasDerivAt (fun u : ℂ ↦ (c : ℂ) + u * I) I (y : ℂ) := by
        simpa using ((hasDerivAt_id (y : ℂ)).mul_const I).const_add (c : ℂ)
      have h2 := (hf _ (hbc y hy)).comp (y : ℂ) h1
      exact HasDerivAt.comp_ofReal (e := fun u : ℂ ↦ f (c + u * I)) h2
    rw [← intervalIntegral.integral_const_mul]
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun y : ℝ ↦ f (c + y * I))
      (fun y hy ↦ ?_) (hint.const_mul I)]
    · have := hd y hy
      convert this using 1; ring
  unfold rectIntegral
  rw [hh _ hb1 hI.1, hh _ hb2 hI.2.1, hv _ hb3 hI.2.2.1, hv _ hb4 hI.2.2.2]
  ring

/-- `∮ 1/s² = 0` around a rectangle whose boundary avoids `0`. -/
lemma rectIntegral_inv_sq {z w : ℂ} (h : ∀ s, OnRectBoundary z w s → s ≠ 0) :
    rectIntegral (fun s ↦ 1 / (s - 0) ^ 2) z w = 0 := by
  refine rectIntegral_deriv_eq_zero (f := fun s ↦ -s⁻¹) (fun s hs ↦ ?_) (fun s hs ↦ ?_)
  · have := (hasDerivAt_inv (h s hs)).neg
    convert this using 1
    simp
  · have hs0 := h s hs
    simp only [sub_zero, one_div]
    exact (continuousAt_id.pow 2).inv₀ (pow_ne_zero 2 hs0)

variable {N : ℕ} [NeZero N]

/-- The zeros of `ξ(s, χ)` with `|γ| < T` are finitely many. -/
lemma finite_L_zeros_im_lt {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (hN : N ≠ 1)
    (T : ℝ) : {ρ : ZeroIndex (dirichletXi χ) | |ρ.val.im| < T}.Finite := by
  have hF := finite_zeroIndex_closedBall
    (differentiable_dirichletXi (ne_one_of_isPrimitive hχ hN)) (|T| + 1)
  refine (Set.finite_coe_iff.mp ?_).subset
    (s := {ρ : ZeroIndex (dirichletXi χ) | ‖ρ.val‖ ≤ |T| + 1}) fun ρ hρ ↦ ?_
  · exact hF
  · simp only [Set.mem_ofPred_eq] at hρ ⊢
    have := norm_dirichletXi_zero_le hχ hN ρ
    linarith [le_abs_self T]

/-- The zeros `ρ` of `L(s, χ)` (with multiplicity) with `|γ| < T`. -/
noncomputable def zerosBelowL {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (hN : N ≠ 1)
    (T : ℝ) : Finset (ZeroIndex (dirichletXi χ)) :=
  (finite_L_zeros_im_lt hχ hN T).toFinset

lemma mem_zerosBelowL {χ : DirichletCharacter ℂ N} {hχ : χ.IsPrimitive} {hN : N ≠ 1} {T : ℝ}
    {ρ : ZeroIndex (dirichletXi χ)} : ρ ∈ zerosBelowL hχ hN T ↔ |ρ.val.im| < T := by
  simp [zerosBelowL]

lemma card_fiber_zerosBelowL {χ : DirichletCharacter ℂ N} {hχ : χ.IsPrimitive} {hN : N ≠ 1}
    {T : ℝ} {p : ℂ} (hp : |p.im| < T) :
    (Finset.filter (fun ρ : ZeroIndex (dirichletXi χ) ↦ ρ.val = p) (zerosBelowL hχ hN T)).card =
      analyticOrderNatAt (dirichletXi χ) p := by
  classical
  have : Finset.filter (fun ρ : ZeroIndex (dirichletXi χ) ↦ ρ.val = p) (zerosBelowL hχ hN T) =
      Finset.univ.map ⟨fun i : Fin (analyticOrderNatAt (dirichletXi χ) p) ↦
        (⟨p, i⟩ : ZeroIndex (dirichletXi χ)), fun i j h ↦ by simpa using h⟩ := by
    ext ρ
    simp only [Finset.mem_filter, mem_zerosBelowL, Finset.mem_map, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨-, hρ⟩
      obtain ⟨z, i⟩ := ρ
      simp only [ZeroIndex.val] at hρ
      subst hρ
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨hp, rfl⟩
  rw [this, Finset.card_map, Finset.card_univ, Fintype.card_fin]

end NTKB
