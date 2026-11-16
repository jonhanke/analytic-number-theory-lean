/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Elementary.SpecialValues.FundamentalGaussSum
import Mathlib.Algebra.QuadraticAlgebra.Int
import Mathlib.Algebra.QuadraticAlgebra.Rat
import Mathlib.Algebra.QuadraticAlgebra.IsQuadraticExtension
import Mathlib.NumberTheory.NumberField.Discriminant.Defs

/-!
# The quadratic field of a fundamental discriminant and its ring of integers

For an integer `D` with `D ≡ 0, 1 (mod 4)`, Mathlib's `QuadraticAlgebra ℤ (D / 4) (D % 4)` is
`ℤ[ω]` with `ω² = D / 4 + (D % 4) ω`, of discriminant `(D % 4)² + 4 (D / 4) = D`: so `ω = √D / 2`
if `4 ∣ D` and `ω = (1 + √D) / 2` if `D ≡ 1 (mod 4)`. Its fraction field is
`QuadraticAlgebra ℚ (D / 4) (D % 4)`, which is `ℚ(√D)`.

* `NTKB.QuadraticField.not_isSquare`: a fundamental discriminant `D ≠ 1` is not a square, so
  `Model D = QuadraticAlgebra ℚ (D / 4) (D % 4)` is a quadratic number field;
* `NTKB.QuadraticField.isIntegral_iff_mem_range` (Ireland–Rosen, Proposition 13.1.1; Davenport §5,
  p. 41): for `D` fundamental the integral elements of `Model D` are exactly `ℤ[ω]`;
* `NTKB.QuadraticField.ringOfIntegersEquiv`: the ring isomorphism `𝓞 (Model D) ≃+* ℤ[ω]`;
* `NTKB.QuadraticField.discr_model` (Ireland–Rosen, Proposition 13.1.2): the discriminant of
  `Model D` is `D`.
-/

noncomputable section

open QuadraticAlgebra NumberField Module

namespace NTKB.QuadraticField

/-- The order `ℤ[ω]`, `ω² = D / 4 + (D % 4) ω`. -/
abbrev Order (D : ℤ) := QuadraticAlgebra ℤ (D / 4) (D % 4)

/-- The quadratic algebra `ℚ(ω) = ℚ(√D)`. -/
abbrev Model (D : ℤ) := QuadraticAlgebra ℚ ((D / 4 : ℤ) : ℚ) ((D % 4 : ℤ) : ℚ)

theorem emod_four_of_isFundamental {D : ℤ} (hD : IsFundamentalDiscriminant D) :
    D % 4 = 0 ∨ D % 4 = 1 := by
  rcases hD with ⟨h, -⟩ | ⟨h, -⟩ <;> omega

theorem discr_order {D : ℤ} (hD : IsFundamentalDiscriminant D) :
    discr (D / 4) (D % 4) = D :=
  discr_ediv_emod (emod_four_of_isFundamental hD)

/-- `x² % 4` is `0` or `1`. -/
theorem sq_emod_four (x : ℤ) : x * x % 4 = 0 ∨ x * x % 4 = 1 := by
  rcases Int.even_or_odd' x with ⟨k, rfl | rfl⟩
  · left; rw [show 2 * k * (2 * k) = 4 * (k * k) by ring]; simp
  · right
    rw [show (2 * k + 1) * (2 * k + 1) = 4 * (k * k + k) + 1 by ring]
    omega

/-- A fundamental discriminant `D ≠ 1` is not a square. -/
theorem not_isSquare {D : ℤ} (hD : IsFundamentalDiscriminant D) (h1 : D ≠ 1) : ¬ IsSquare D := by
  rintro ⟨r, rfl⟩
  rcases hD with ⟨-, hsq⟩ | ⟨h0, h23, -⟩
  · have hu := hsq r dvd_rfl
    rcases Int.isUnit_iff.mp hu with rfl | rfl <;> simp at h1
  · rcases Int.even_or_odd' r with ⟨k, rfl | rfl⟩
    · rw [show 2 * k * (2 * k) = 4 * (k * k) by ring,
        Int.mul_ediv_cancel_left _ (by norm_num)] at h23
      rcases sq_emod_four k with h | h <;> omega
    · have : (2 * k + 1) * (2 * k + 1) % 4 = 1 := by
        rw [show (2 * k + 1) * (2 * k + 1) = 4 * (k * k + k) + 1 by ring]; omega
      omega

theorem not_isSquare_discr {D : ℤ} (hD : IsFundamentalDiscriminant D) (h1 : D ≠ 1) :
    ¬ IsSquare (discr ((D / 4 : ℤ) : ℚ) ((D % 4 : ℤ) : ℚ)) := by
  rw [discr_intCast, discr_order hD, Rat.isSquare_intCast_iff]
  exact not_isSquare hD h1

section instances

variable (D : ℤ) [Fact (IsFundamentalDiscriminant D)] [Fact (D ≠ 1)]

instance factNotIsSquare : Fact (¬ IsSquare (discr ((D / 4 : ℤ) : ℚ) ((D % 4 : ℤ) : ℚ))) :=
  ⟨not_isSquare_discr Fact.out Fact.out⟩

instance factNotIsSquareInt : Fact (¬ IsSquare (discr (D / 4) (D % 4))) :=
  ⟨by rw [discr_order Fact.out]; exact not_isSquare Fact.out Fact.out⟩

example : Field (Model D) := inferInstance

instance : NumberField (Model D) where
  to_charZero := inferInstance
  to_finiteDimensional := inferInstance

omit [Fact (IsFundamentalDiscriminant D)] [Fact (D ≠ 1)] in
theorem finrank_model : finrank ℚ (Model D) = 2 := finrank_eq_two _ _

end instances

/-! ### The ring of integers -/

/-- If `D` is fundamental, the denominator of the imaginary part of an integral element is `1`. -/
theorem den_eq_one {D : ℤ} (hD : IsFundamentalDiscriminant D) {n e : ℤ} (hn : 0 < n)
    (he : D = n ^ 2 * e) (he4 : e % 4 = 0 ∨ e % 4 = 1) : n = 1 := by
  rcases hD with ⟨-, hsq⟩ | ⟨h0, h23, hsq⟩
  · have hu := hsq n ⟨e, by rw [he]; ring⟩
    rcases Int.isUnit_iff.mp hu with h | h <;> omega
  · rcases Int.even_or_odd' n with ⟨m, rfl | rfl⟩
    · have hk : D / 4 = m * m * e := by
        rw [he, show (2 * m) ^ 2 * e = 4 * (m * m * e) by ring,
          Int.mul_ediv_cancel_left _ (by norm_num)]
      have hu := hsq m ⟨e, by rw [hk]⟩
      rcases Int.isUnit_iff.mp hu with rfl | rfl <;> · simp at hk; omega
    · have hk : D = 4 * (D / 4) := by omega
      have hdvd : (2 * m + 1) * (2 * m + 1) ∣ 4 * (D / 4) := ⟨e, by rw [← hk, he]; ring⟩
      have hcop : IsCoprime ((2 * m + 1) * (2 * m + 1)) 4 := by
        have h2 : IsCoprime (2 * m + 1) 2 := (Int.isCoprime_two_left.mpr ⟨m, rfl⟩).symm
        have := (h2.mul_left h2).pow_right (n := 2)
        simpa [sq, show (2 : ℤ) * 2 = 4 by norm_num] using this
      have hu := hsq _ (hcop.dvd_of_dvd_mul_left hdvd)
      rcases Int.isUnit_iff.mp hu with h | h <;> omega

/-- For `ℤ[ω] ⊂ ℚ(ω)`, `ω² = a + b ω`, of fundamental discriminant `b² + 4a`, the integral
elements of `ℚ(ω)` are exactly `ℤ[ω]`. -/
theorem isIntegral_iff_mem_range_of_discr {a b D : ℤ} (hab : discr a b = D)
    (hD : IsFundamentalDiscriminant D) (z : QuadraticAlgebra ℚ a b) :
    IsIntegral ℤ z ↔
      z ∈ Set.range (algebraMap (QuadraticAlgebra ℤ a b) (QuadraticAlgebra ℚ a b)) := by
  constructor
  · intro hz
    obtain ⟨e, he, he4⟩ := Int.exists_im_den_sq_mul hz
    rw [hab] at he
    have h1 := den_eq_one hD (by exact_mod_cast z.im.den_pos) he he4
    refine (Int.mem_range_iff_im_mem_range hz).mpr ⟨z.im.num, ?_⟩
    have : z.im.den = 1 := by exact_mod_cast h1
    simpa using (Rat.intCast_num_of_den_eq_one this)
  · rintro ⟨x, rfl⟩
    exact (Algebra.IsIntegral.isIntegral x).algebraMap

/-- **Ireland–Rosen, Proposition 13.1.1** (in the form of Davenport §5, p. 41): for a fundamental
discriminant `D ≠ 1`, an element of `ℚ(√D)` is an algebraic integer iff it lies in `ℤ[ω]`. -/
theorem isIntegral_iff_mem_range {D : ℤ} [Fact (IsFundamentalDiscriminant D)] [Fact (D ≠ 1)]
    (z : Model D) :
    IsIntegral ℤ z ↔ z ∈ Set.range (algebraMap (Order D) (Model D)) := by
  constructor
  · intro hz
    obtain ⟨e, he, he4⟩ := Int.exists_im_den_sq_mul hz
    rw [discr_order Fact.out] at he
    have h1 := den_eq_one Fact.out (by exact_mod_cast z.im.den_pos) he he4
    refine (Int.mem_range_iff_im_mem_range hz).mpr ⟨z.im.num, ?_⟩
    have : z.im.den = 1 := by exact_mod_cast h1
    simpa using (Rat.intCast_num_of_den_eq_one this)
  · rintro ⟨x, rfl⟩
    exact (Algebra.IsIntegral.isIntegral x).algebraMap

instance isIntegralClosure_order (D : ℤ) [Fact (IsFundamentalDiscriminant D)] [Fact (D ≠ 1)] :
    IsIntegralClosure (Order D) ℤ (Model D) where
  algebraMap_injective := FaithfulSMul.algebraMap_injective _ _
  isIntegral_iff {z} := by
    rw [isIntegral_iff_mem_range]; rfl

/-- The ring of integers of `ℚ(√D)` is `ℤ[ω]`. -/
def ringOfIntegersEquiv (D : ℤ) [Fact (IsFundamentalDiscriminant D)] [Fact (D ≠ 1)] :
    𝓞 (Model D) ≃+* Order D :=
  RingOfIntegers.equiv (Order D)

/-! ### The discriminant -/

/-- The trace form of `QuadraticAlgebra ℤ a b`: `Tr(z) = 2 re z + b im z`. -/
theorem algebra_trace_eq (a b : ℤ) (z : QuadraticAlgebra ℤ a b) :
    Algebra.trace ℤ (QuadraticAlgebra ℤ a b) z = QuadraticAlgebra.trace z := by
  rw [Algebra.trace_eq_matrix_trace (QuadraticAlgebra.basis a b), Matrix.trace_fin_two,
    Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul]
  simp [QuadraticAlgebra.trace_def, basis_apply_one]
  ring

/-- The discriminant of the basis `1, ω` of `QuadraticAlgebra ℤ a b` is `b² + 4a`. -/
theorem algebra_discr_basis (a b : ℤ) :
    Algebra.discr ℤ (QuadraticAlgebra.basis a b) = discr a b := by
  rw [Algebra.discr_def, Matrix.det_fin_two]
  simp only [Algebra.traceMatrix_apply, Algebra.traceForm_apply, algebra_trace_eq,
    basis_apply_zero, basis_apply_one, one_mul, mul_one, trace_one, trace_omega]
  rw [omega_mul_omega_eq_mk, QuadraticAlgebra.trace_def, discr_def]
  ring

/-- **Ireland–Rosen, Proposition 13.1.2** (Davenport §5, p. 41): the discriminant of `ℚ(√D)`,
`D` fundamental, is `D`. -/
theorem discr_model (D : ℤ) [Fact (IsFundamentalDiscriminant D)] [Fact (D ≠ 1)] :
    NumberField.discr (Model D) = D := by
  classical
  let e : 𝓞 (Model D) ≃ₗ[ℤ] Order D := (ringOfIntegersEquiv D).toIntAlgEquiv.toLinearEquiv
  let bK : Basis (Fin 2) ℤ (𝓞 (Model D)) := (QuadraticAlgebra.basis _ _).map e.symm
  rw [← NumberField.discr_eq_discr (Model D) bK,
    Algebra.discr_eq_discr_of_algEquiv bK (ringOfIntegersEquiv D).toIntAlgEquiv]
  have : (ringOfIntegersEquiv D).toIntAlgEquiv ∘ bK = QuadraticAlgebra.basis _ _ := by
    ext i : 1
    simp [bK, e]
  rw [this, algebra_discr_basis, discr_order Fact.out]

end NTKB.QuadraticField
