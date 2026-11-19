/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Attr
import Mathlib.NumberTheory.LSeries.HurwitzZetaEven
import Mathlib.NumberTheory.LSeries.HurwitzZetaOdd
import Mathlib.NumberTheory.DirichletCharacter.GaussSum
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

/-!
# Theta functions attached to Dirichlet characters

**Davenport, Multiplicative Number Theory, Ch. 9, (2), (7), (9), (10), pp. 68-70.**

For a character `χ` modulo `q = N` we put
`ψ(x, χ) = ∑_{n ∈ ℤ} χ(n) e^{-π n² x / q}` and `ψ₁(x, χ) = ∑_{n ∈ ℤ} n χ(n) e^{-π n² x / q}`,
and prove, for `χ` primitive,
`τ(χ) ψ(1/x, χ̄) = (q x)^{1/2} ψ(x, χ)` and
`τ(χ) ψ₁(1/x, χ̄) = i q^{1/2} x^{3/2} ψ₁(x, χ)`.

Route (Davenport uses Poisson summation; Mathlib already packages it in the functional equations
of the Hurwitz kernels):

* split `n = j + q k` with `j` ranging over `ZMod N` (`hasSum_split`), so that
  `ψ(x, χ) = ∑_j χ(j) · evenKernel (j/q) (q x)` and
  `ψ₁(x, χ) = q ∑_j χ(j) · oddKernel (j/q) (q x)`;
* apply `evenKernel_functional_equation` / `oddKernel_functional_equation` and expand the resulting
  `cosKernel` / `sinKernel` as sums over `ℤ` of `e(j n / q) e^{-π n² / (q x)}`;
* evaluate `∑_j χ(j) e(j n / q) = χ̄(n) τ(χ)` by `gaussSum_mulShift_of_isPrimitive`.

Davenport states the first identity for `χ` even and the second for `χ` odd; no parity hypothesis
is needed, since for the other parity both sides vanish (`ψ(x, χ) = 0` for `χ` odd and
`ψ₁(x, χ) = 0` for `χ` even), and the proof never uses it.

(The parity hypotheses are not needed by this argument: for the wrong parity both sides vanish.)
-/

open Complex HurwitzZeta
open scoped Real

noncomputable section

namespace NTKB.Davenport

variable {N : ℕ} [NeZero N]

/-- Davenport's `ψ(x, χ) = ∑_{n ∈ ℤ} χ(n) e^{-π n² x / q}` (Ch. 9, (2)), `q = N`.
**Restriction:** the series converges only for `x > 0`; for `x ≤ 0` it diverges and the value is 0 by Lean's `∑'`
convention, not the intended value. -/
def thetaChar (χ : DirichletCharacter ℂ N) (x : ℝ) : ℂ :=
  ∑' n : ℤ, χ n * (Real.exp (-Real.pi * (n : ℝ) ^ 2 * x / N) : ℂ)

/-- Davenport's `ψ₁(x, χ) = ∑_{n ∈ ℤ} n χ(n) e^{-π n² x / q}` (Ch. 9, (9)). -/
def thetaCharOdd (χ : DirichletCharacter ℂ N) (x : ℝ) : ℂ :=
  ∑' n : ℤ, (n : ℂ) * χ n * (Real.exp (-Real.pi * (n : ℝ) ^ 2 * x / N) : ℂ)

/-- Summing over residue classes: if each progression `j + N k` sums to `s j`, then `f` sums to
`∑ s j`. -/
lemma hasSum_split (f : ℤ → ℂ) (s : ZMod N → ℂ)
    (hs : ∀ j : ZMod N, HasSum (fun k : ℤ => f ((j.val : ℤ) + N * k)) (s j)) :
    HasSum f (∑ j, s j) := by
  have h : ∀ j : ZMod N,
      HasSum (fun n : ℤ => if (n : ZMod N) = j then f n else 0) (s j) := by
    intro j
    have hN : (N : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne N
    have hinj : Function.Injective (fun k : ℤ => (j.val : ℤ) + N * k) := by
      intro a b hab
      exact mul_left_cancel₀ hN (add_left_cancel hab)
    rw [← hinj.hasSum_iff (f := fun n : ℤ => if (n : ZMod N) = j then f n else 0)]
    · convert hs j using 1
      funext k
      have : (((j.val : ℤ) + N * k : ℤ) : ZMod N) = j :=
        (ZMod.intCast_eq_iff N _ j).mpr ⟨k, rfl⟩
      simp only [Function.comp_apply, this, ite_true]
    · intro n hn
      by_cases h' : (n : ZMod N) = j
      · exfalso
        apply hn
        obtain ⟨k, hk⟩ := (ZMod.intCast_eq_iff N n j).mp h'
        exact ⟨k, hk.symm⟩
      · simp [h']
  have := hasSum_sum (s := Finset.univ) (fun j _ => h j)
  convert this using 1
  funext n
  simp [Finset.sum_ite_eq]

lemma thetaChar_eq (χ : DirichletCharacter ℂ N) {x : ℝ} (hx : 0 < x) :
    thetaChar χ x = ∑ j : ZMod N,
      χ j * (evenKernel ((((j.val : ℝ) / N : ℝ)) : UnitAddCircle) (N * x) : ℂ) := by
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  have hNx : 0 < (N : ℝ) * x := mul_pos hN hx
  refine HasSum.tsum_eq (hasSum_split _ _ (fun j => ?_))
  have h1 := hasSum_int_evenKernel ((j.val : ℝ) / N) hNx
  have h2 := (Complex.hasSum_ofReal.mpr h1).mul_left (χ j)
  convert h2 using 1
  funext k
  have hc : (((j.val : ℤ) + N * k : ℤ) : ZMod N) = j :=
    (ZMod.intCast_eq_iff N _ j).mpr ⟨k, rfl⟩
  rw [hc]
  congr 3
  push_cast
  field_simp
  ring

lemma thetaCharOdd_eq (χ : DirichletCharacter ℂ N) {x : ℝ} (hx : 0 < x) :
    thetaCharOdd χ x = N * ∑ j : ZMod N,
      χ j * (oddKernel ((((j.val : ℝ) / N : ℝ)) : UnitAddCircle) (N * x) : ℂ) := by
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  have hNx : 0 < (N : ℝ) * x := mul_pos hN hx
  rw [Finset.mul_sum]
  refine HasSum.tsum_eq (hasSum_split _ _ (fun j => ?_))
  have h1 := hasSum_int_oddKernel ((j.val : ℝ) / N) hNx
  have h2 := (Complex.hasSum_ofReal.mpr h1).mul_left ((N : ℂ) * χ j)
  convert h2 using 1
  · funext k
    have hc : (((j.val : ℤ) + N * k : ℤ) : ZMod N) = j :=
      (ZMod.intCast_eq_iff N _ j).mpr ⟨k, rfl⟩
    rw [hc]
    have hNc : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
    have e : Real.exp (-Real.pi * (((j.val : ℤ) + N * k : ℤ) : ℝ) ^ 2 * x / N) =
        Real.exp (-Real.pi * ((k : ℝ) + (j.val : ℝ) / N) ^ 2 * (N * x)) := by
      congr 1
      push_cast
      field_simp
      ring
    rw [e]
    push_cast
    field_simp
    ring
  · ring

/-- `∑_j χ(j) e(j n / N) = χ̄(n) τ(χ)` for primitive `χ`. -/
lemma sum_char_exp {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (n : ℤ) :
    ∑ j : ZMod N, χ j * Complex.exp (2 * π * I * (((j.val : ℝ) / N : ℝ) : ℂ) * (n : ℂ)) =
      χ⁻¹ (n : ZMod N) * gaussSum χ ZMod.stdAddChar := by
  rw [← gaussSum_mulShift_of_isPrimitive ZMod.stdAddChar hχ (n : ZMod N), gaussSum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [AddChar.mulShift_apply]
  have : (n : ZMod N) * j = ((n * j.val : ℤ) : ZMod N) := by
    push_cast
    rw [ZMod.natCast_zmod_val]
  rw [this, ZMod.stdAddChar_coe]
  congr 2
  push_cast
  ring

lemma sum_cosKernel {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) {y : ℝ} (hy : 0 < y) :
    ∑ j : ZMod N, χ j * (cosKernel ((((j.val : ℝ) / N : ℝ)) : UnitAddCircle) y : ℂ) =
      gaussSum χ ZMod.stdAddChar *
        ∑' n : ℤ, χ⁻¹ n * (Real.exp (-Real.pi * (n : ℝ) ^ 2 * y) : ℂ) := by
  have h : HasSum (fun n : ℤ => gaussSum χ ZMod.stdAddChar *
      (χ⁻¹ n * (Real.exp (-Real.pi * (n : ℝ) ^ 2 * y) : ℂ)))
      (∑ j : ZMod N, χ j * (cosKernel ((((j.val : ℝ) / N : ℝ)) : UnitAddCircle) y : ℂ)) := by
    have := hasSum_sum (s := Finset.univ)
      (fun (j : ZMod N) _ => (hasSum_int_cosKernel ((j.val : ℝ) / N) hy).mul_left (χ j))
    convert this using 1
    funext n
    simp_rw [← mul_assoc, ← Finset.sum_mul, sum_char_exp hχ n]
    ring
  rw [← tsum_mul_left]
  exact h.tsum_eq.symm

lemma sum_sinKernel {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) {y : ℝ} (hy : 0 < y) :
    ∑ j : ZMod N, χ j * (sinKernel ((((j.val : ℝ) / N : ℝ)) : UnitAddCircle) y : ℂ) =
      -I * gaussSum χ ZMod.stdAddChar *
        ∑' n : ℤ, (n : ℂ) * χ⁻¹ n * (Real.exp (-Real.pi * (n : ℝ) ^ 2 * y) : ℂ) := by
  have h : HasSum (fun n : ℤ => -I * gaussSum χ ZMod.stdAddChar *
      ((n : ℂ) * χ⁻¹ n * (Real.exp (-Real.pi * (n : ℝ) ^ 2 * y) : ℂ)))
      (∑ j : ZMod N, χ j * (sinKernel ((((j.val : ℝ) / N : ℝ)) : UnitAddCircle) y : ℂ)) := by
    have := hasSum_sum (s := Finset.univ)
      (fun (j : ZMod N) _ => (hasSum_int_sinKernel ((j.val : ℝ) / N) hy).mul_left (χ j))
    convert this using 1
    funext n
    have e := sum_char_exp hχ n
    calc _ = -I * (n : ℂ) * (Real.exp (-Real.pi * (n : ℝ) ^ 2 * y) : ℂ) *
          (χ⁻¹ (n : ZMod N) * gaussSum χ ZMod.stdAddChar) := by ring
      _ = _ := by
        rw [← e, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring
  rw [← tsum_mul_left]
  exact h.tsum_eq.symm

/-- **Davenport, Ch. 9, (7)**: for `χ` primitive, `τ(χ) ψ(1/x, χ̄) = (q x)^{1/2} ψ(x, χ)`
(Davenport: `χ` even; for `χ` odd both sides are `0`). -/
@[kb "davenport1980" "Ch 9, p. 68"]
theorem gaussSum_mul_thetaChar_inv {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive)
    {x : ℝ} (hx : 0 < x) :
    gaussSum χ ZMod.stdAddChar * thetaChar χ⁻¹ (1 / x) = (Real.sqrt (N * x) : ℂ) * thetaChar χ x := by
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  have hNx : 0 < (N : ℝ) * x := mul_pos hN hx
  have hy : 0 < 1 / ((N : ℝ) * x) := one_div_pos.mpr hNx
  have hs : 0 < Real.sqrt ((N : ℝ) * x) := Real.sqrt_pos.mpr hNx
  have h3 : thetaChar χ x = ((1 / Real.sqrt ((N : ℝ) * x) : ℝ) : ℂ) *
      (gaussSum χ ZMod.stdAddChar *
        ∑' n : ℤ, χ⁻¹ n * (Real.exp (-Real.pi * (n : ℝ) ^ 2 * (1 / ((N : ℝ) * x))) : ℂ)) := by
    rw [thetaChar_eq χ hx, ← sum_cosKernel hχ hy, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [evenKernel_functional_equation, ← Real.sqrt_eq_rpow]
    push_cast
    ring
  have h4 : thetaChar χ⁻¹ (1 / x) =
      ∑' n : ℤ, χ⁻¹ n * (Real.exp (-Real.pi * (n : ℝ) ^ 2 * (1 / ((N : ℝ) * x))) : ℂ) := by
    unfold thetaChar
    refine tsum_congr fun n => ?_
    congr 3
    field_simp
  rw [h3, h4, ← mul_assoc, ← Complex.ofReal_mul, mul_one_div_cancel hs.ne', Complex.ofReal_one,
    one_mul]

/-- **Davenport, Ch. 9, (10)**: for `χ` primitive, `τ(χ) ψ₁(1/x, χ̄) = i q^{1/2} x^{3/2} ψ₁(x, χ)`
(Davenport: `χ` odd; for `χ` even both sides are `0`). -/
@[kb "davenport1980" "Ch 9, p. 70"]
theorem gaussSum_mul_thetaCharOdd_inv {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive)
    {x : ℝ} (hx : 0 < x) :
    gaussSum χ ZMod.stdAddChar * thetaCharOdd χ⁻¹ (1 / x) =
      Complex.I * (Real.sqrt N : ℂ) * ((x ^ ((3 : ℝ) / 2) : ℝ) : ℂ) * thetaCharOdd χ x := by
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  have hNx : 0 < (N : ℝ) * x := mul_pos hN hx
  have hy : 0 < 1 / ((N : ℝ) * x) := one_div_pos.mpr hNx
  set T : ℂ := ∑' n : ℤ, (n : ℂ) * χ⁻¹ n *
    (Real.exp (-Real.pi * (n : ℝ) ^ 2 * (1 / ((N : ℝ) * x))) : ℂ) with hT
  set τ : ℂ := gaussSum χ ZMod.stdAddChar with hτ
  set c : ℝ := 1 / ((N : ℝ) * x) ^ ((3 : ℝ) / 2) with hc
  have h3 : thetaCharOdd χ x = (N : ℂ) * (c : ℂ) * (-I * τ * T) := by
    rw [thetaCharOdd_eq χ hx, ← sum_sinKernel hχ hy, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [oddKernel_functional_equation, hc]
    push_cast
    ring
  have h4 : thetaCharOdd χ⁻¹ (1 / x) = T := by
    unfold thetaCharOdd
    refine tsum_congr fun n => ?_
    congr 3
    field_simp
  have hN3 : (N : ℝ) ^ ((3 : ℝ) / 2) = N * Real.sqrt N := by
    rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add hN, Real.rpow_one,
      ← Real.sqrt_eq_rpow]
  have hpos : 0 < ((N : ℝ) * x) ^ ((3 : ℝ) / 2) := Real.rpow_pos_of_pos hNx _
  have key : Real.sqrt N * x ^ ((3 : ℝ) / 2) * N * c = 1 := by
    rw [hc, Real.mul_rpow hN.le hx.le, hN3]
    have : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN
    have : 0 < x ^ ((3 : ℝ) / 2) := Real.rpow_pos_of_pos hx _
    field_simp
  have keyC : (Real.sqrt N : ℂ) * ((x ^ ((3 : ℝ) / 2) : ℝ) : ℂ) * (N : ℂ) * (c : ℂ) = 1 := by
    exact_mod_cast congrArg (fun r : ℝ => (r : ℂ)) key
  rw [h3, h4]
  linear_combination (-(τ * T)) * keyC + (τ * T * ((Real.sqrt N : ℂ) *
    ((x ^ ((3 : ℝ) / 2) : ℝ) : ℂ) * (N : ℂ) * (c : ℂ))) * Complex.I_sq

end NTKB.Davenport
