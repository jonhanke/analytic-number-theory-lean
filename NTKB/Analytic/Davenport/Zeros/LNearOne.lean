/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Apostol.Zeta.LBounds
import NTKB.Analytic.Apostol.Zeta.HurwitzEuler
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# `L(σ, χ)` and `L'(σ, χ)` near `σ = 1`

**Davenport, Ch. 14, p. 105 (rows 14-17, 14-19).** For `χ` nonprincipal mod `q ≥ 3` and
`1 - 1/log q ≤ σ < 1`: `|L(σ, χ)| ≤ c log q` and `|L'(σ, χ)| ≤ c log² q`
(`Davenport.norm_LFunction_near_one_le`, `Davenport.norm_deriv_LFunction_near_one_le`).

Davenport uses partial summation with `|∑_{n ≤ N} χ(n)| ≤ q`. Here the same cancellation is used
in Euler's summation formula for the Hurwitz zeta function (Apostol, Theorem 12.21, proved in
the Apostol part of the library): with `L(s, χ) = q^{-s} ∑_{r=1}^q χ(r) ζ(s, r/q)` and
`ζ(s, a) = a^{-s} + (1 + a)^{-s} + (1 + a)^{1-s}/(s - 1) - s J(a)`, the polar terms combine to
`q^{-s}/(s - 1) ∑ χ(r) ((1 + r/q)^{1-s} - 1)` because `∑ χ(r) = 0`, which is `O(q^{1-σ})`
(`norm_LFunction_le_euler`). The bound for `L'` then follows from Cauchy's estimate on a circle
of radius `1/(20 log q)`.
-/

open Complex Finset HurwitzZeta ZMod Metric

namespace NTKB

open Apostol

/-- `‖(1 + a)^{1-s} - 1‖ ≤ ‖1 - s‖ a` for `a ≥ 0`, `Re s ≥ 0`. -/
lemma norm_one_add_cpow_sub_one_le {a : ℝ} (ha : 0 ≤ a) {s : ℂ} (hs : 0 ≤ s.re) :
    ‖((1 + a : ℝ) : ℂ) ^ (1 - s) - 1‖ ≤ ‖1 - s‖ * a := by
  have hle : (1 : ℝ) ≤ 1 + a := by linarith
  have hd : ∀ u ∈ Set.uIcc (1 : ℝ) (1 + a), HasDerivAt (fun y : ℝ ↦ (y : ℂ) ^ (1 - s))
      ((1 - s) * (u : ℂ) ^ (1 - s - 1)) u := fun u hu ↦ by
    rw [Set.uIcc_of_le hle] at hu
    exact hasDerivAt_ofReal_cpow_any (by linarith [hu.1]) _
  have hc : ContinuousOn (fun u : ℝ ↦ (1 - s) * (u : ℂ) ^ (1 - s - 1)) (Set.uIcc 1 (1 + a)) := by
    intro u hu
    rw [Set.uIcc_of_le hle] at hu
    exact (continuousAt_const.mul (hasDerivAt_ofReal_cpow_any (by linarith [hu.1])
      (1 - s - 1)).continuousAt).continuousWithinAt
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable
  simp only [Complex.ofReal_one, Complex.one_cpow] at hint
  rw [← hint]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := 1) (b := 1 + a)
    (C := ‖1 - s‖) (f := fun u : ℝ ↦ (1 - s) * (u : ℂ) ^ (1 - s - 1)) (fun u hu ↦ by
      rw [Set.uIoc_of_le hle] at hu
      have hu0 : 0 < u := by linarith [hu.1]
      rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hu0]
      have : u ^ (1 - s - 1).re ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (by linarith [hu.1]) (by simp; linarith)
      calc ‖1 - s‖ * u ^ (1 - s - 1).re ≤ ‖1 - s‖ * 1 := by gcongr
        _ = ‖1 - s‖ := mul_one _)
  refine hb.trans (le_of_eq ?_)
  rw [show (1 + a) - 1 = a by ring, abs_of_nonneg ha]

/-- `‖∫_0^1 u (m + u)^{-s-1} du‖ ≤ m^{-σ-1}`. -/
lemma norm_integral_euler_le {m : ℝ} (hm : 0 < m) {s : ℂ} (hs : 0 ≤ s.re) :
    ‖∫ u in (0 : ℝ)..1, (u : ℂ) * ((m + u : ℝ) : ℂ) ^ (-s - 1)‖ ≤ m ^ (-s.re - 1) := by
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1)
    (C := m ^ (-s.re - 1)) (f := fun u : ℝ ↦ (u : ℂ) * ((m + u : ℝ) : ℂ) ^ (-s - 1))
    (fun u hu ↦ by
      rw [Set.uIoc_of_le zero_le_one] at hu
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hu.1.le,
        norm_cpow_eq_rpow_re_of_pos (by linarith [hu.1])]
      have h1 : (m + u) ^ (-s - 1).re ≤ m ^ (-s - 1).re :=
        Real.rpow_le_rpow_of_nonpos hm (by linarith [hu.1]) (by simp; linarith)
      have h2 : (-s - 1).re = -s.re - 1 := by simp
      rw [h2] at h1
      calc u * (m + u) ^ (-s.re - 1) ≤ 1 * m ^ (-s.re - 1) :=
            mul_le_mul hu.2 h1 (Real.rpow_nonneg (by linarith [hu.1]) _) zero_le_one
          _ = m ^ (-s.re - 1) := one_mul _)
  refine hb.trans (le_of_eq ?_)
  simp

variable {k : ℕ} [NeZero k]

/-- The pieces of `k^{-s} χ(j) ζ(s, j/k)` from Euler summation with `N = 1`. -/
lemma cpow_mul_hurwitz_eq (j : ZMod k) {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    (k : ℂ) ^ (-s) * hurwitzZeta (toAddCircle j) s =
      ((((zmodRep j : ℕ) : ℝ) : ℂ) ^ (-s) + (((k + zmodRep j : ℕ) : ℝ) : ℂ) ^ (-s)) +
      (k : ℂ) ^ (-s) / (s - 1) * ((1 + (zmodRep j : ℝ) / k : ℝ) : ℂ) ^ (1 - s) -
      s * (k : ℂ) ^ (-s) * ∑' n : ℕ, ∫ u in (0 : ℝ)..1,
        (u : ℂ) * (((1 : ℕ) + n + (zmodRep j : ℝ) / k + u : ℝ) : ℂ) ^ (-s - 1) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast NeZero.pos k
  set a : ℝ := (zmodRep j : ℝ) / k with ha
  have ha0 : 0 < a := div_pos (by exact_mod_cast zmodRep_pos j) hk0
  have ha1 : a ≤ 1 := by
    rw [ha, div_le_one hk0]; exact_mod_cast zmodRep_le j
  rw [toAddCircle_eq_zmodRep, apostol_thm_12_21 ha0 ha1 1 hs hs1]
  have hka : (k : ℝ) * a = (zmodRep j : ℝ) := by rw [ha]; field_simp
  have e0 : (k : ℂ) ^ (-s) * (((0 : ℕ) + a : ℝ) : ℂ) ^ (-s) = (((zmodRep j : ℕ) : ℝ) : ℂ) ^ (-s) := by
    have := mul_cpow_ofReal_nonneg hk0.le (by positivity : (0 : ℝ) ≤ (0 : ℕ) + a) (-s)
    rw [← ofReal_mul, show (k : ℝ) * ((0 : ℕ) + a) = (zmodRep j : ℝ) by push_cast; linarith]
      at this
    rw [show ((k : ℂ)) = ((k : ℝ) : ℂ) by simp]
    exact this.symm
  have e1 : (k : ℂ) ^ (-s) * (((1 : ℕ) + a : ℝ) : ℂ) ^ (-s) =
      (((k + zmodRep j : ℕ) : ℝ) : ℂ) ^ (-s) := by
    have := mul_cpow_ofReal_nonneg hk0.le (by positivity : (0 : ℝ) ≤ (1 : ℕ) + a) (-s)
    rw [← ofReal_mul, show (k : ℝ) * ((1 : ℕ) + a) = ((k + zmodRep j : ℕ) : ℝ) by
      push_cast; linarith] at this
    rw [show ((k : ℂ)) = ((k : ℝ) : ℂ) by simp]
    exact this.symm
  rw [Finset.sum_range_succ, Finset.sum_range_one]
  rw [show (((1 : ℕ) + a : ℝ) : ℂ) ^ (1 - s) = ((1 + a : ℝ) : ℂ) ^ (1 - s) by push_cast; ring_nf]
  rw [← e0, ← e1]
  ring

/-- **The Euler-summation bound**: for `χ ≠ 1` mod `k`, `σ > 0`, `s ≠ 1`,
`‖L(s, χ)‖ ≤ 2 ∑_{n < k} (n + 1)^{-σ} + k^{1-σ} + ‖s‖ k^{1-σ} ∑_n (n + 1)^{-1-σ}`. -/
lemma norm_LFunction_le_euler {χ : DirichletCharacter ℂ k} (hχ : χ ≠ 1) {s : ℂ}
    (hs : 0 < s.re) (hs1 : s ≠ 1) :
    ‖χ.LFunction s‖ ≤ 2 * ∑ n ∈ range k, ((n : ℝ) + 1) ^ (-s.re) + (k : ℝ) ^ (1 - s.re) +
      ‖s‖ * (k : ℝ) ^ (1 - s.re) * ∑' n : ℕ, ((n : ℝ) + 1) ^ (-(1 + s.re)) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast NeZero.pos k
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  set σ := s.re with hσ
  set a : ZMod k → ℝ := fun j ↦ (zmodRep j : ℝ) / k with ha
  have ha0 : ∀ j, 0 < a j := fun j ↦ div_pos (by exact_mod_cast zmodRep_pos j) hk0
  have ha1 : ∀ j, a j ≤ 1 := fun j ↦ by
    simp only [ha]; rw [div_le_one hk0]; exact_mod_cast zmodRep_le j
  set J : ZMod k → ℂ := fun j ↦ ∑' n : ℕ, ∫ u in (0 : ℝ)..1,
    (u : ℂ) * (((1 : ℕ) + n + a j + u : ℝ) : ℂ) ^ (-s - 1) with hJ
  -- the identity
  have hsum0 : ∑ j : ZMod k, χ j = 0 := MulChar.sum_eq_zero_of_ne_one hχ
  have hL : χ.LFunction s =
      (∑ j : ZMod k, χ j * ((((zmodRep j : ℕ) : ℝ) : ℂ) ^ (-s) +
        (((k + zmodRep j : ℕ) : ℝ) : ℂ) ^ (-s))) +
      (k : ℂ) ^ (-s) / (s - 1) * ∑ j : ZMod k, χ j * (((1 + a j : ℝ) : ℂ) ^ (1 - s) - 1) -
      s * (k : ℂ) ^ (-s) * ∑ j : ZMod k, χ j * J j := by
    rw [DirichletCharacter.LFunction, ZMod.LFunction, mul_sum]
    have h1 : ∀ j : ZMod k, (k : ℂ) ^ (-s) * (χ j * hurwitzZeta (toAddCircle j) s) =
        χ j * ((((zmodRep j : ℕ) : ℝ) : ℂ) ^ (-s) + (((k + zmodRep j : ℕ) : ℝ) : ℂ) ^ (-s)) +
        (k : ℂ) ^ (-s) / (s - 1) * (χ j * (((1 + a j : ℝ) : ℂ) ^ (1 - s) - 1)) +
        (k : ℂ) ^ (-s) / (s - 1) * χ j - s * (k : ℂ) ^ (-s) * (χ j * J j) := by
      intro j
      rw [mul_left_comm, cpow_mul_hurwitz_eq j hs hs1]
      simp only [ha, hJ]
      ring
    rw [Finset.sum_congr rfl fun j _ ↦ h1 j, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, hsum0]
    ring
  rw [hL]
  -- the bounds
  have hkσ : (k : ℝ) ^ (1 - σ) = k * (k : ℝ) ^ (-σ) := by
    rw [sub_eq_add_neg, Real.rpow_add hk0, Real.rpow_one]
  have hkn : ‖(k : ℂ) ^ (-s)‖ = (k : ℝ) ^ (-σ) := by
    rw [show (k : ℂ) = ((k : ℝ) : ℂ) by simp, norm_cpow_eq_rpow_re_of_pos hk0, neg_re]
  have bA : ‖∑ j : ZMod k, χ j * ((((zmodRep j : ℕ) : ℝ) : ℂ) ^ (-s) +
      (((k + zmodRep j : ℕ) : ℝ) : ℂ) ^ (-s))‖ ≤ 2 * ∑ n ∈ range k, ((n : ℝ) + 1) ^ (-σ) := by
    refine (norm_sum_le _ _).trans ?_
    have hj : ∀ j : ZMod k, ‖χ j * ((((zmodRep j : ℕ) : ℝ) : ℂ) ^ (-s) +
        (((k + zmodRep j : ℕ) : ℝ) : ℂ) ^ (-s))‖ ≤ 2 * ((zmodRep j : ℕ) : ℝ) ^ (-σ) := by
      intro j
      have hr : (0 : ℝ) < ((zmodRep j : ℕ) : ℝ) := by exact_mod_cast zmodRep_pos j
      rw [norm_mul]
      have h1 := DirichletCharacter.norm_le_one χ j
      have h2 : ‖(((k + zmodRep j : ℕ) : ℝ) : ℂ) ^ (-s)‖ ≤ ((zmodRep j : ℕ) : ℝ) ^ (-σ) := by
        rw [norm_cpow_eq_rpow_re_of_pos (by push_cast; linarith [(k.cast_nonneg : (0 : ℝ) ≤ k)]),
          neg_re]
        exact Real.rpow_le_rpow_of_nonpos hr (by push_cast; linarith) (by linarith)
      have h3 : ‖(((zmodRep j : ℕ) : ℝ) : ℂ) ^ (-s)‖ = ((zmodRep j : ℕ) : ℝ) ^ (-σ) := by
        rw [norm_cpow_eq_rpow_re_of_pos hr, neg_re]
      have h4 := norm_add_le ((((zmodRep j : ℕ) : ℝ) : ℂ) ^ (-s))
        ((((k + zmodRep j : ℕ) : ℝ) : ℂ) ^ (-s))
      calc ‖χ j‖ * ‖(((zmodRep j : ℕ) : ℝ) : ℂ) ^ (-s) + (((k + zmodRep j : ℕ) : ℝ) : ℂ) ^ (-s)‖
          ≤ 1 * (2 * ((zmodRep j : ℕ) : ℝ) ^ (-σ)) := by
            gcongr
            linarith
        _ = _ := one_mul _
    refine (Finset.sum_le_sum fun j _ ↦ hj j).trans (le_of_eq ?_)
    rw [← Finset.mul_sum, sum_zmodRep_rpow]
  have bB : ‖(k : ℂ) ^ (-s) / (s - 1) * ∑ j : ZMod k, χ j * (((1 + a j : ℝ) : ℂ) ^ (1 - s) - 1)‖ ≤
      (k : ℝ) ^ (1 - σ) := by
    rw [norm_mul, norm_div, hkn]
    have hj : ∀ j : ZMod k, ‖χ j * (((1 + a j : ℝ) : ℂ) ^ (1 - s) - 1)‖ ≤ ‖s - 1‖ := by
      intro j
      rw [norm_mul]
      have h1 := DirichletCharacter.norm_le_one χ j
      have h2 := norm_one_add_cpow_sub_one_le (ha0 j).le (s := s) hs.le
      rw [show ‖(1 : ℂ) - s‖ = ‖s - 1‖ from norm_sub_rev _ _] at h2
      have h3 : ‖s - 1‖ * a j ≤ ‖s - 1‖ := by
        have := ha1 j; have := norm_nonneg (s - 1); nlinarith
      calc ‖χ j‖ * ‖((1 + a j : ℝ) : ℂ) ^ (1 - s) - 1‖ ≤ 1 * ‖s - 1‖ := by
            gcongr; linarith
        _ = ‖s - 1‖ := one_mul _
    have hS := (norm_sum_le _ _).trans (Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) ↦ hj j)
    rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul] at hS
    have hn : 0 < ‖s - 1‖ := norm_pos_iff.mpr hs1'
    calc (k : ℝ) ^ (-σ) / ‖s - 1‖ * ‖∑ j : ZMod k, χ j * (((1 + a j : ℝ) : ℂ) ^ (1 - s) - 1)‖
        ≤ (k : ℝ) ^ (-σ) / ‖s - 1‖ * (k * ‖s - 1‖) := by gcongr
      _ = (k : ℝ) ^ (1 - σ) := by rw [hkσ]; field_simp
  have hZ := hasSum_rpow_riemannZeta hs
  have bJ : ∀ j : ZMod k, ‖J j‖ ≤ ∑' n : ℕ, ((n : ℝ) + 1) ^ (-(1 + σ)) := by
    intro j
    refine tsum_of_norm_bounded hZ.summable.hasSum fun n ↦ ?_
    have hm : 0 < ((1 : ℕ) : ℝ) + n + a j := by
      push_cast; linarith [ha0 j, (n.cast_nonneg : (0 : ℝ) ≤ n)]
    refine (norm_integral_euler_le hm hs.le).trans ?_
    rw [show -σ - 1 = -(1 + σ) by ring]
    exact Real.rpow_le_rpow_of_nonpos (by positivity) (by push_cast; linarith [ha0 j])
      (by linarith)
  have bC : ‖s * (k : ℂ) ^ (-s) * ∑ j : ZMod k, χ j * J j‖ ≤
      ‖s‖ * (k : ℝ) ^ (1 - σ) * ∑' n : ℕ, ((n : ℝ) + 1) ^ (-(1 + σ)) := by
    rw [norm_mul, norm_mul, hkn]
    have hj : ∀ j : ZMod k, ‖χ j * J j‖ ≤ ∑' n : ℕ, ((n : ℝ) + 1) ^ (-(1 + σ)) := by
      intro j
      rw [norm_mul]
      have h1 := DirichletCharacter.norm_le_one χ j
      calc ‖χ j‖ * ‖J j‖ ≤ 1 * ∑' n : ℕ, ((n : ℝ) + 1) ^ (-(1 + σ)) :=
            mul_le_mul h1 (bJ j) (norm_nonneg _) zero_le_one
        _ = _ := one_mul _
    have hS := (norm_sum_le _ _).trans (Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) ↦ hj j)
    rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul] at hS
    calc ‖s‖ * (k : ℝ) ^ (-σ) * ‖∑ j : ZMod k, χ j * J j‖
        ≤ ‖s‖ * (k : ℝ) ^ (-σ) * (k * ∑' n : ℕ, ((n : ℝ) + 1) ^ (-(1 + σ))) := by gcongr
      _ = _ := by rw [hkσ]; ring
  calc _ ≤ ‖∑ j : ZMod k, χ j * ((((zmodRep j : ℕ) : ℝ) : ℂ) ^ (-s) +
        (((k + zmodRep j : ℕ) : ℝ) : ℂ) ^ (-s))‖ +
        ‖(k : ℂ) ^ (-s) / (s - 1) * ∑ j : ZMod k, χ j * (((1 + a j : ℝ) : ℂ) ^ (1 - s) - 1)‖ +
        ‖s * (k : ℂ) ^ (-s) * ∑ j : ZMod k, χ j * J j‖ := by
        have k1 := norm_sub_le (∑ j : ZMod k, χ j * ((((zmodRep j : ℕ) : ℝ) : ℂ) ^ (-s) +
          (((k + zmodRep j : ℕ) : ℝ) : ℂ) ^ (-s)) +
          (k : ℂ) ^ (-s) / (s - 1) * ∑ j : ZMod k, χ j * (((1 + a j : ℝ) : ℂ) ^ (1 - s) - 1))
          (s * (k : ℂ) ^ (-s) * ∑ j : ZMod k, χ j * J j)
        have k2 := norm_add_le (∑ j : ZMod k, χ j * ((((zmodRep j : ℕ) : ℝ) : ℂ) ^ (-s) +
          (((k + zmodRep j : ℕ) : ℝ) : ℂ) ^ (-s)))
          ((k : ℂ) ^ (-s) / (s - 1) * ∑ j : ZMod k, χ j * (((1 + a j : ℝ) : ℂ) ^ (1 - s) - 1))
        linarith
    _ ≤ _ := by linarith

omit [NeZero k] in
/-- `∑_{n < k} (n + 1)^{-σ} ≤ B (1 + log k)` when `(n + 1)^{1-σ} ≤ B` for `n < k`. -/
lemma sum_range_rpow_neg_le {σ B : ℝ} (hB : 1 ≤ B) (h : ∀ n < k, ((n : ℝ) + 1) ^ (1 - σ) ≤ B) :
    ∑ n ∈ range k, ((n : ℝ) + 1) ^ (-σ) ≤ B * (1 + Real.log k) := by
  have hH := harmonic_le_one_add_log k
  have hHr : ((harmonic k : ℚ) : ℝ) = ∑ n ∈ range k, 1 / ((n : ℝ) + 1) := by
    rw [harmonic]; push_cast; simp [one_div]
  calc ∑ n ∈ range k, ((n : ℝ) + 1) ^ (-σ) ≤ ∑ n ∈ range k, B * (1 / ((n : ℝ) + 1)) := by
        refine Finset.sum_le_sum fun n hn ↦ ?_
        have hn0 : (0 : ℝ) < n + 1 := by positivity
        have e : ((n : ℝ) + 1) ^ (-σ) = ((n : ℝ) + 1) ^ (1 - σ) * (1 / ((n : ℝ) + 1)) := by
          rw [one_div, ← Real.rpow_neg_one, ← Real.rpow_add hn0]; ring_nf
        rw [e]
        exact mul_le_mul_of_nonneg_right (h n (Finset.mem_range.mp hn)) (by positivity)
    _ = B * ((harmonic k : ℚ) : ℝ) := by rw [← Finset.mul_sum, hHr]
    _ ≤ B * (1 + Real.log k) := by gcongr

/-- `|L(s, χ)| ≤ C log k` for `χ ≠ 1` mod `k ≥ 3`, `σ ≥ 1 - 21/(20 log k)`, `|s| ≤ 3`. -/
lemma exists_norm_LFunction_region_le :
    ∃ C : ℝ, 0 < C ∧ ∀ {k : ℕ} [NeZero k] {χ : DirichletCharacter ℂ k}, χ ≠ 1 → 3 ≤ k →
      ∀ s : ℂ, 1 - 21 / (20 * Real.log k) ≤ s.re → ‖s‖ ≤ 3 →
      ‖χ.LFunction s‖ ≤ C * Real.log k := by
  have hZs := (hasSum_rpow_riemannZeta (δ := 1 / 25) (by norm_num)).summable
  set Z₀ := ∑' n : ℕ, ((n : ℝ) + 1) ^ (-(1 + 1 / 25 : ℝ)) with hZ₀
  have hZ₀0 : 0 ≤ Z₀ := tsum_nonneg fun n ↦ by positivity
  refine ⟨40 + 24 * Z₀, by positivity, fun {k} _ {χ} hχ hk s hσ hs3 ↦ ?_⟩
  have hk0 : (0 : ℝ) < k := by exact_mod_cast NeZero.pos k
  have hk3 : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hL3 : 1.0986122885 < Real.log k :=
    Real.log_three_gt_d9.trans_le (Real.log_le_log (by norm_num) hk3)
  have hL0 : 0 < Real.log k := by linarith
  have hL1 : 1 ≤ Real.log k := by linarith
  -- `σ ≥ 1/25` and `(1 - σ) log k ≤ 21/20`
  have hσL : (1 - s.re) * Real.log k ≤ 21 / 20 := by
    have : 1 - s.re ≤ 21 / (20 * Real.log k) := by linarith
    calc (1 - s.re) * Real.log k ≤ 21 / (20 * Real.log k) * Real.log k := by gcongr
      _ = 21 / 20 := by field_simp
  have hσ25 : 1 / 25 ≤ s.re := by
    have h1 : 21 / (20 * Real.log k) ≤ 24 / 25 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    linarith
  have hexp : Real.exp (21 / 20) ≤ 8 := by
    have h := Real.exp_one_lt_d9
    have e2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    have : Real.exp (21 / 20) ≤ Real.exp 2 := Real.exp_le_exp.mpr (by norm_num)
    nlinarith [Real.exp_pos 1]
  have hkσ : (k : ℝ) ^ (1 - s.re) ≤ 8 := by
    rw [Real.rpow_def_of_pos hk0]
    calc Real.exp (Real.log k * (1 - s.re)) ≤ Real.exp (21 / 20) :=
          Real.exp_le_exp.mpr (by linarith)
      _ ≤ 8 := hexp
  have hn : ∀ n < k, ((n : ℝ) + 1) ^ (1 - s.re) ≤ 8 := by
    intro n hn
    have hn1 : (1 : ℝ) ≤ n + 1 := by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
    rcases le_or_gt (1 - s.re) 0 with h | h
    · exact (Real.rpow_le_one_of_one_le_of_nonpos hn1 h).trans (by norm_num)
    · refine le_trans ?_ hkσ
      exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast hn) h.le
  have hsum := sum_range_rpow_neg_le (k := k) (σ := s.re) (by norm_num) hn
  have hZ : ∑' n : ℕ, ((n : ℝ) + 1) ^ (-(1 + s.re)) ≤ Z₀ := by
    refine Summable.tsum_le_tsum (fun n ↦ ?_) ?_ hZs
    · exact Real.rpow_le_rpow_of_exponent_le (by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)])
        (by linarith)
    · exact (hasSum_rpow_riemannZeta (δ := s.re) (by linarith)).summable
  rcases eq_or_ne s 1 with rfl | hs1
  · -- `s = 1`: by continuity from the right
    have hcont : ContinuousAt (fun x : ℝ ↦ ‖χ.LFunction (x : ℂ)‖) 1 :=
      ((DirichletCharacter.differentiable_LFunction hχ).continuous.continuousAt.comp
        Complex.continuous_ofReal.continuousAt).norm
    have hlim : Filter.Tendsto (fun x : ℝ ↦ ‖χ.LFunction (x : ℂ)‖) (nhdsWithin 1 (Set.Ioi 1))
        (nhds ‖χ.LFunction ((1 : ℝ) : ℂ)‖) := hcont.tendsto.mono_left nhdsWithin_le_nhds
    push_cast at hlim
    refine le_of_tendsto hlim ?_
    filter_upwards [Ioo_mem_nhdsGT (show (1 : ℝ) < 2 by norm_num)] with x hx
    have hx1 : (x : ℂ) ≠ 1 := fun h ↦ by
      have := congrArg Complex.re h; simp at this; linarith [hx.1]
    have hb := norm_LFunction_le_euler hχ (s := (x : ℂ)) (by simp; linarith [hx.1]) hx1
    simp only [Complex.ofReal_re] at hb
    have hn' : ∀ n < k, ((n : ℝ) + 1) ^ (1 - x) ≤ 8 := fun n _ ↦
      (Real.rpow_le_one_of_one_le_of_nonpos (by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)])
        (by linarith [hx.1])).trans (by norm_num)
    have hsum' := sum_range_rpow_neg_le (k := k) (σ := x) (by norm_num) hn'
    have hkx : (k : ℝ) ^ (1 - x) ≤ 8 :=
      (Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith [hx.1])).trans
        (by norm_num)
    have hZx : ∑' n : ℕ, ((n : ℝ) + 1) ^ (-(1 + x)) ≤ Z₀ := by
      refine Summable.tsum_le_tsum (fun n ↦ ?_) ?_ hZs
      · exact Real.rpow_le_rpow_of_exponent_le
          (by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]) (by linarith [hx.1])
      · exact (hasSum_rpow_riemannZeta (δ := x) (by linarith [hx.1])).summable
    have hxn : ‖(x : ℂ)‖ ≤ 3 := by
      rw [Complex.norm_real, Real.norm_of_nonneg (by linarith [hx.1])]; linarith [hx.2]
    have e1 : ‖(x : ℂ)‖ * (k : ℝ) ^ (1 - x) * ∑' n : ℕ, ((n : ℝ) + 1) ^ (-(1 + x)) ≤
        3 * 8 * Z₀ := by
      gcongr
    nlinarith
  · have hb := norm_LFunction_le_euler hχ (s := s) (by linarith) hs1
    have e1 : ‖s‖ * (k : ℝ) ^ (1 - s.re) * ∑' n : ℕ, ((n : ℝ) + 1) ^ (-(1 + s.re)) ≤
        3 * 8 * Z₀ := by
      gcongr
    nlinarith

/-- **Davenport, Ch. 14, p. 105 (row 14-19)**: there is an absolute `c` such that for `χ`
nonprincipal mod `q ≥ 3` and `1 - 1/log q ≤ σ < 1`, `|L(σ, χ)| ≤ c log q`. -/
@[kb "davenport1980" "Ch 14, p. 105"]
theorem Davenport.norm_LFunction_near_one_le :
    ∃ c : ℝ, 0 < c ∧ ∀ {k : ℕ} [NeZero k] {χ : DirichletCharacter ℂ k}, χ ≠ 1 → 3 ≤ k →
      ∀ σ : ℝ, 1 - 1 / Real.log k ≤ σ → σ < 1 → ‖χ.LFunction σ‖ ≤ c * Real.log k := by
  obtain ⟨C, hC, h⟩ := exists_norm_LFunction_region_le
  refine ⟨C, hC, fun {k} _ {χ} hχ hk σ hσ hσ1 ↦ h hχ hk σ ?_ ?_⟩
  · have hL0 : 0 < Real.log k := Real.log_pos (by exact_mod_cast (show 1 < k by omega))
    simp only [Complex.ofReal_re]
    have : 21 / (20 * Real.log k) ≥ 1 / Real.log k := by
      rw [ge_iff_le, div_le_div_iff₀ hL0 (by positivity)]; nlinarith
    linarith
  · have hL0 : 0 < Real.log k := Real.log_pos (by exact_mod_cast (show 1 < k by omega))
    have hk3 : (3 : ℝ) ≤ k := by exact_mod_cast hk
    have hL1 : 1 < Real.log k :=
      (by norm_num : (1 : ℝ) < 1.0986122885).trans
        (Real.log_three_gt_d9.trans_le (Real.log_le_log (by norm_num) hk3))
    have : 0 < σ := by
      have : 1 / Real.log k < 1 := by rw [div_lt_one hL0]; exact hL1
      linarith
    rw [Complex.norm_real, Real.norm_of_nonneg this.le]; linarith

/-- **Davenport, Ch. 14, p. 105 (row 14-17)**: there is an absolute `c` such that for `χ`
nonprincipal mod `q ≥ 3` and `1 - 1/log q ≤ σ < 1`, `|L'(σ, χ)| ≤ c log² q`. -/
@[kb "davenport1980" "Ch 14, p. 105"]
theorem Davenport.norm_deriv_LFunction_near_one_le :
    ∃ c : ℝ, 0 < c ∧ ∀ {k : ℕ} [NeZero k] {χ : DirichletCharacter ℂ k}, χ ≠ 1 → 3 ≤ k →
      ∀ σ : ℝ, 1 - 1 / Real.log k ≤ σ → σ < 1 →
      ‖deriv χ.LFunction σ‖ ≤ c * Real.log k ^ 2 := by
  obtain ⟨C, hC, h⟩ := exists_norm_LFunction_region_le
  refine ⟨20 * C, by positivity, fun {k} _ {χ} hχ hk σ hσ hσ1 ↦ ?_⟩
  have hk3 : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hL1 : 1 < Real.log k :=
    (by norm_num : (1 : ℝ) < 1.0986122885).trans
      (Real.log_three_gt_d9.trans_le (Real.log_le_log (by norm_num) hk3))
  have hL0 : 0 < Real.log k := by linarith
  set R : ℝ := 1 / (20 * Real.log k) with hR
  have hR0 : 0 < R := by positivity
  have hR1 : R ≤ 1 / 20 := by
    rw [hR]; exact one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hσ0 : 0 < σ := by
    have : 1 / Real.log k < 1 := by rw [div_lt_one hL0]; exact hL1
    linarith
  have hbound : ∀ z ∈ sphere (σ : ℂ) R, ‖χ.LFunction z‖ ≤ C * Real.log k := by
    intro z hz
    rw [mem_sphere, dist_eq_norm] at hz
    refine h hχ hk z ?_ ?_
    · have h1 := Complex.abs_re_le_norm (z - σ)
      rw [hz, Complex.sub_re, Complex.ofReal_re, abs_le] at h1
      have : 1 / Real.log k + R = 21 / (20 * Real.log k) := by rw [hR]; field_simp; ring
      linarith [h1.1]
    · have h1 := norm_add_le (z - σ) (σ : ℂ)
      rw [sub_add_cancel, hz, Complex.norm_real, Real.norm_of_nonneg hσ0.le] at h1
      linarith
  have hd := norm_deriv_le_of_forall_mem_sphere_norm_le hR0
    (DirichletCharacter.differentiable_LFunction hχ).diffContOnCl hbound
  refine hd.trans (le_of_eq ?_)
  rw [hR]; field_simp

end NTKB
