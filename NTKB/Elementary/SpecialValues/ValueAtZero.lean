/-
Copyright (c) 2026 The Tau Ceti contributors (`pi_mul_cot_pi_mul_val_div_eq_sum`,
`sum_val_eq_sum_range`); the NTKB authors (the rest). Released under Apache 2.0 license.
-/
import Mathlib.NumberTheory.LSeries.ZMod
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import NTKB.Elementary.SpecialValues.NegativeValues
import NTKB.Elementary.SpecialValues.HurwitzOddOne

/-!
# `L(1 - k, χ) = -B_{k,χ}/k` for every `k ≥ 1`

The case `k = 1`, `L(0, χ) = -B_{1,χ}`, for every Dirichlet character `χ` modulo `N ≥ 1`:
* `χ` even: Mathlib's `ZMod.LFunction_apply_zero_of_even` gives `L(0, χ) = -χ(0)/2`, which is
  `-1/2 = -B_{1,χ}` at modulus one and `0 = -B_{1,χ}` otherwise (parity vanishing);
* `χ` odd: Mathlib's functional equation `ZMod.LFunction_one_sub` at `s = 1` gives
  `L(0, χ) = (i/π) L(1, 𝓕χ)` with `𝓕` the discrete Fourier transform; `L(1, 𝓕χ)` is a finite sum of
  odd Hurwitz zeta values at `1`, that is of cotangents (`NTKB.hurwitzZetaOdd_one`); the finite
  Fourier expansion of the cotangent and Fourier inversion turn it into `π i B_{1,χ}`.

With `NTKB.LFunction_one_sub_nat_of_two_le` this gives `L(1 - k, χ) = -B_{k,χ}/k` for all `k ≥ 1`
(Washington, Theorem 4.2; Miyake, Theorem 3.3.4), with no primitivity or nontriviality hypothesis
and the convention `B_1 = +1/2` (`B_{1,χ} = 1/2` for the character modulo one: `L(0) = ζ(0) = -1/2`).

## Provenance

`pi_mul_cot_pi_mul_val_div_eq_sum` (the finite Fourier expansion of the cotangent) and
`sum_val_eq_sum_range` are copied (Apache 2.0, with credit) from Tau Ceti,
`TauCeti/Analysis/SpecialFunctions/Trigonometric/Cotangent.lean` and `TauCeti/Data/ZMod/Count.lean`,
main `d7b4780` (2026-11-07), namespace moved to `NTKB`, proofs unchanged.
-/

noncomputable section

open Complex HurwitzZeta ZMod
open scoped Real

namespace NTKB

/-- Summing a function of the least nonnegative representative over `ZMod n`. (Tau Ceti.) -/
theorem sum_val_eq_sum_range {n : ℕ} {M : Type*} [AddCommMonoid M] [NeZero n] (f : ℕ → M) :
    ∑ x : ZMod n, f x.val = ∑ i ∈ Finset.range n, f i := by
  rw [← Finset.sum_image (f := f) (s := Finset.univ) (g := ZMod.val)
    (fun x _ y _ h ↦ ZMod.val_injective n h)]
  congr 1
  ext i
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_range]
  constructor
  · rintro ⟨x, rfl⟩
    exact x.val_lt
  · intro hi
    exact ⟨(i : ZMod n), ZMod.val_cast_of_lt hi⟩

/-- **The finite Fourier expansion of the cotangent at the division points.** For a nonzero
residue `j` modulo `M`, `π cot (π j / M) = π i + (2π i / M) ∑_{m mod M} m e(m j / M)`. (Tau Ceti.) -/
theorem pi_mul_cot_pi_mul_val_div_eq_sum (M : ℕ) [NeZero M] {j : ZMod M} (hj : j ≠ 0) :
    π * cot (π * (j.val / M)) =
      π * I + 2 * π * I / M * ∑ m : ZMod M, (m.val : ℂ) * ZMod.stdAddChar (m * j) := by
  set ζ : ℂ := ZMod.stdAddChar j with hζdef
  have hζ : ζ = cexp (2 * π * I * (j.val / M)) := by
    have : ζ = ZMod.stdAddChar ((j.val : ℤ) : ZMod M) := by simp [hζdef]
    rw [this, ZMod.stdAddChar_coe]
    push_cast
    ring_nf
  have hζ1 : ζ - 1 ≠ 0 := by
    refine sub_ne_zero.mpr fun h ↦ hj ?_
    rw [← AddChar.map_zero_eq_one (ZMod.stdAddChar (N := M))] at h
    exact ZMod.injective_stdAddChar (by exact_mod_cast h)
  have hζM : ζ ^ M = 1 := by
    rw [hζdef, ← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, ZMod.natCast_self, zero_mul,
      AddChar.map_zero_eq_one]
  have hterm (m : ZMod M) : (ZMod.stdAddChar (m * j) : ℂ) = ζ ^ m.val := by
    rw [hζdef, ← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, ZMod.natCast_zmod_val]
  have hgeom : ∑ i ∈ Finset.range M, ζ ^ i = 0 := by
    have h := geom_sum_mul ζ M
    rw [hζM, sub_self] at h
    exact (mul_eq_zero.mp h).resolve_right hζ1
  have hind (K : ℕ) : (ζ - 1) * ∑ i ∈ Finset.range K, (i : ℂ) * ζ ^ i =
      K * ζ ^ K - ζ * ∑ i ∈ Finset.range K, ζ ^ i := by
    induction K with
    | zero => simp
    | succ K ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, mul_add, ih]
      push_cast
      ring
  have hS : ∑ m : ZMod M, (m.val : ℂ) * ZMod.stdAddChar (m * j) = M / (ζ - 1) := by
    simp_rw [hterm]
    rw [sum_val_eq_sum_range (fun i ↦ (i : ℂ) * ζ ^ i), eq_div_iff hζ1, mul_comm, hind,
      hζM, hgeom]
    ring
  rw [hS, cot_pi_eq_exp_ratio, ← hζ]
  have hM : (M : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne M)
  have h1ζ : 1 - ζ ≠ 0 := by rwa [← neg_sub, neg_ne_zero]
  field_simp
  ring_nf
  rw [I_sq]
  ring

variable {N : ℕ} [NeZero N]

/-- The L-function of `ZMod N → ℂ` is additive in the coefficient function: `L(-Φ) = -L(Φ)`. -/
theorem ZMod_LFunction_neg (Φ : ZMod N → ℂ) (s : ℂ) :
    ZMod.LFunction (-Φ) s = -ZMod.LFunction Φ s := by
  simp only [ZMod.LFunction, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib, mul_neg]

/-- **`L(0, χ) = -B_{1,χ}` for an odd character.** -/
theorem LFunction_zero_of_odd {χ : DirichletCharacter ℂ N} (hχ : χ.Odd) :
    DirichletCharacter.LFunction χ 0 = -generalizedBernoulli χ 1 := by
  have hχ1 : χ ≠ 1 := by
    rintro rfl
    exact DirichletCharacter.Odd.not_even _ hχ (DirichletCharacter.even_one)
  have hN1 : N ≠ 1 := fun h ↦ hχ1 (χ.level_one' h)
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  set Φ : ZMod N → ℂ := fun j ↦ χ j with hΦdef
  have hΦodd : Φ.Odd := fun x ↦ by
    simp only [hΦdef]
    rw [neg_eq_neg_one_mul x, map_mul, hχ, neg_one_mul]
  have hΦ0 : Φ 0 = 0 := χ.map_zero' hN1
  have hΦneg : (fun x ↦ Φ (-x)) = -Φ := funext fun x ↦ hΦodd x
  have hsum0 : ∑ j, Φ j = 0 := MulChar.sum_eq_zero_of_ne_one hχ1
  -- Step 1: the functional equation at `s = 1`
  have hFE := ZMod.LFunction_one_sub Φ (s := 1)
    (fun n h ↦ by
      have := congrArg re h
      simp at this
      linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
    (Or.inl hΦ0)
  rw [hΦneg, map_neg, ZMod_LFunction_neg, sub_self, cpow_zero, Complex.Gamma_one,
    cpow_neg_one] at hFE
  have he1 : cexp (π * I * 1 / 2) = I := by
    rw [show (π : ℂ) * I * 1 / 2 = π / 2 * I by ring, exp_pi_div_two_mul_I]
  have he2 : cexp (-π * I * 1 / 2) = -I := by
    rw [show -(π : ℂ) * I * 1 / 2 = -π / 2 * I by ring, exp_neg_pi_div_two_mul_I]
  rw [he1, he2] at hFE
  -- Step 2: `L(1, 𝓕Φ)` as a sum of cotangents
  set Ψ := 𝓕 Φ with hΨdef
  have hΨodd : Ψ.Odd := dft_odd_iff.mpr hΦodd
  have hΨ0 : Ψ 0 = 0 := by rw [hΨdef, dft_apply_zero, hsum0]
  have hL1 : ZMod.LFunction Ψ 1 =
      (N : ℂ)⁻¹ * ∑ k : ZMod N, Ψ k * (π / 2 * cot (π * (k.val / N))) := by
    rw [ZMod.LFunction_def_odd hΨodd, cpow_neg_one]
    congr 1
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rcases eq_or_ne k 0 with rfl | hk
    · simp [hΨ0]
    · congr 1
      rw [toAddCircle_apply]
      have hkpos : 0 < k.val := Nat.pos_of_ne_zero ((ZMod.val_ne_zero k).mpr hk)
      have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
      have ha : (k.val / N : ℝ) ∈ Set.Ioo (0 : ℝ) 1 :=
        ⟨div_pos (by exact_mod_cast hkpos) hNpos,
          (div_lt_one hNpos).mpr (by exact_mod_cast k.val_lt)⟩
      rw [hurwitzZetaOdd_one ha]
      push_cast
      ring_nf
  -- Step 3: the finite Fourier expansion of the cotangent and Fourier inversion
  have hcot (k : ZMod N) : Ψ k * (π * cot (π * (k.val / N))) =
      Ψ k * (π * I + 2 * π * I / N * ∑ m : ZMod N, (m.val : ℂ) * stdAddChar (m * k)) := by
    rcases eq_or_ne k 0 with rfl | hk
    · simp [hΨ0]
    · rw [pi_mul_cot_pi_mul_val_div_eq_sum N hk]
  have hinv (m : ZMod N) : ∑ k : ZMod N, Ψ k * stdAddChar (m * k) = N * Φ m := by
    have h := congrFun (dft_dft Φ) (-m)
    rw [dft_apply, neg_neg] at h
    rw [← smul_eq_mul (a := (N : ℂ)), ← h]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [smul_eq_mul, mul_comm, mul_neg, neg_neg, mul_comm k m]
  have hinv0 : ∑ k : ZMod N, Ψ k = 0 := by
    have h := hinv 0
    simp only [zero_mul, AddChar.map_zero_eq_one, mul_one] at h
    rw [h, hΦ0, mul_zero]
  have hB := natCast_mul_generalizedBernoulli_one_of_ne_one hχ1
  have hmain : ∑ k : ZMod N, Ψ k * (π * cot (π * (k.val / N))) =
      2 * π * I * (N * generalizedBernoulli χ 1) := by
    simp_rw [hcot, mul_add]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, hinv0, zero_mul, zero_add]
    have : ∑ k : ZMod N, Ψ k * (2 * π * I / N *
        ∑ m : ZMod N, (m.val : ℂ) * stdAddChar (m * k)) =
        2 * π * I / N * ∑ m : ZMod N, (m.val : ℂ) * ∑ k : ZMod N, Ψ k * stdAddChar (m * k) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun m _ ↦ Finset.sum_congr rfl fun k _ ↦ ?_
      ring
    rw [this, hB]
    simp_rw [hinv]
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ ↦ ?_
    simp only [hΦdef]
    field_simp
  have hL1': ZMod.LFunction Ψ 1 = π * I * generalizedBernoulli χ 1 := by
    rw [hL1]
    have : ∑ k : ZMod N, Ψ k * (π / 2 * cot (π * (k.val / N))) =
        (1 / 2) * ∑ k : ZMod N, Ψ k * (π * cot (π * (k.val / N))) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      ring
    rw [this, hmain]
    field_simp
  -- conclusion
  have hpi : (2 * (π : ℂ)) ≠ 0 := mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero)
  unfold DirichletCharacter.LFunction
  rw [hFE, hL1']
  field_simp
  ring_nf
  rw [I_sq]
  ring

/-- **`L(0, χ) = -B_{1,χ}`** for every Dirichlet character (`B_1 = +1/2` convention). -/
theorem LFunction_zero (χ : DirichletCharacter ℂ N) :
    DirichletCharacter.LFunction χ 0 = -generalizedBernoulli χ 1 := by
  rcases χ.even_or_odd with hχ | hχ
  · -- even: both sides are `-χ(0)/2`
    have hΦ : (fun j ↦ χ j : ZMod N → ℂ).Even := fun x ↦ by
      show χ (-x) = χ x
      rw [neg_eq_neg_one_mul x, map_mul, hχ, one_mul]
    unfold DirichletCharacter.LFunction
    rw [ZMod.LFunction_apply_zero_of_even hΦ]
    rcases eq_or_ne N 1 with rfl | hN1
    · rw [generalizedBernoulli_modOne, χ.level_one]
      simp [bernoulli'_one]
      norm_num
    · rw [χ.map_zero' hN1, generalizedBernoulli_eq_zero_of_apply_neg_one_eq_neg (Or.inr hN1)
        (by rw [hχ]; norm_num)]
      simp
  · exact LFunction_zero_of_odd hχ

/-- **`L(1 - k, χ) = -B_{k,χ}/k` for every Dirichlet character and every `k ≥ 1`**
(Washington, Theorem 4.2; Miyake, Theorem 3.3.4 (1)). -/
@[kb "washington1997" "Theorem 4.2"]
theorem LFunction_one_sub_nat (χ : DirichletCharacter ℂ N) {k : ℕ} (hk : 1 ≤ k) :
    DirichletCharacter.LFunction χ (1 - k) = -generalizedBernoulli χ k / k := by
  rcases eq_or_lt_of_le hk with rfl | hk2
  · simpa using LFunction_zero χ
  · exact LFunction_one_sub_nat_of_two_le χ hk2

end NTKB
