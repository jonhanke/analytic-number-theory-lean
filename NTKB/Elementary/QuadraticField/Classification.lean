/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Elementary.QuadraticField.Model

/-!
# Every quadratic number field is `ℚ(√D)` for a fundamental discriminant `D`

* `NTKB.QuadraticField.exists_algEquiv_model`: a number field `K` of degree `2` is isomorphic to
  `Model D = ℚ(√D)` for a fundamental discriminant `D ≠ 1` (from Mathlib's
  `Algebra.IsQuadraticExtension.exists_algEquiv_quadraticAlgebra` and
  `QuadraticAlgebra.Rat.exists_squarefree_algEquiv`: `K ≅ ℚ(√d)`, `d` squarefree; then `D = d` if
  `d ≡ 1 (mod 4)` and `D = 4d` otherwise);
* `NTKB.QuadraticField.isFundamental_discr` (Davenport §5, p. 41, row 5-15, first half): the
  discriminant of a quadratic number field is a fundamental discriminant `≠ 1`, and `K ≅ ℚ(√d_K)`;
* `NTKB.QuadraticField.nonempty_ringEquiv_order`: `𝓞 K ≅ ℤ[ω]`, `ω² = d_K / 4 + (d_K % 4) ω`.
-/

noncomputable section

open QuadraticAlgebra NumberField Module

namespace NTKB.QuadraticField

/-- `d ≡ 1 (mod 4)` squarefree gives `D = d`; otherwise `D = 4d`. -/
def fundamentalOfSquarefree (d : ℤ) : ℤ := if d % 4 = 1 then d else 4 * d

theorem isFundamental_fundamentalOfSquarefree {d : ℤ} (hd : Squarefree d) :
    IsFundamentalDiscriminant (fundamentalOfSquarefree d) := by
  unfold fundamentalOfSquarefree
  split_ifs with h
  · exact Or.inl ⟨h, hd⟩
  · have h4 : d % 4 ≠ 0 := by
      intro h0
      have := hd 2 ⟨d / 4, by omega⟩
      simp [Int.isUnit_iff] at this
    refine Or.inr ⟨by omega, ?_, ?_⟩
    · rw [Int.mul_ediv_cancel_left _ (by norm_num)]; omega
    · rwa [Int.mul_ediv_cancel_left _ (by norm_num)]

/-- `ℚ(√d) ≅ ℚ(√D)` for `D = d` or `4d`. -/
theorem nonempty_algEquiv_fundamentalOfSquarefree {d : ℤ} (hd : Squarefree d) :
    Nonempty (QuadraticAlgebra ℚ (d : ℚ) 0 ≃ₐ[ℚ] Model (fundamentalOfSquarefree d)) := by
  have hD := isFundamental_fundamentalOfSquarefree hd
  rw [nonempty_algEquiv_iff_of_invertible_two, discr_intCast, discr_order hD]
  have hd0 : discr (d : ℚ) 0 = 4 * d := by rw [discr_def]; ring
  rw [hd0]
  unfold fundamentalOfSquarefree
  split_ifs
  · exact ⟨Units.mk0 2 (by norm_num), by simp; norm_num⟩
  · exact ⟨1, by simp⟩

theorem fundamentalOfSquarefree_ne_one {d : ℤ} (h1 : d ≠ 1) : fundamentalOfSquarefree d ≠ 1 := by
  unfold fundamentalOfSquarefree
  split_ifs <;> omega

variable (K : Type*) [Field K] [NumberField K]

/-- **Every quadratic number field is `ℚ(√D)`, `D ≠ 1` a fundamental discriminant.** -/
theorem exists_algEquiv_model (hK : finrank ℚ K = 2) :
    ∃ D : ℤ, IsFundamentalDiscriminant D ∧ D ≠ 1 ∧ Nonempty (K ≃ₐ[ℚ] Model D) := by
  have : Algebra.IsQuadraticExtension ℚ K := ⟨hK⟩
  obtain ⟨a, b, ⟨e₁⟩⟩ := Algebra.IsQuadraticExtension.exists_algEquiv_quadraticAlgebra
    (R := ℚ) (A := K)
  have hfield : IsField (QuadraticAlgebra ℚ a b) :=
    e₁.symm.toMulEquiv.isField (Field.toIsField K)
  have hdisc : discr a b ≠ 0 := by
    intro h
    exact not_isField_of_isSquare_discr ⟨0, by rw [h, mul_zero]⟩ hfield
  obtain ⟨d, hd, ⟨e₂⟩⟩ := Rat.exists_squarefree_algEquiv hdisc
  have hfield' : IsField (QuadraticAlgebra ℚ (d : ℚ) 0) :=
    e₂.symm.toMulEquiv.isField hfield
  have h1 : d ≠ 1 := by
    rintro rfl
    exact not_isSquare_discr_one hfield'
  obtain ⟨e₃⟩ := nonempty_algEquiv_fundamentalOfSquarefree hd
  exact ⟨_, isFundamental_fundamentalOfSquarefree hd, fundamentalOfSquarefree_ne_one h1,
    ⟨e₁.trans (e₂.trans e₃)⟩⟩
where
  not_isSquare_discr_one (h : IsField (QuadraticAlgebra ℚ ((1 : ℤ) : ℚ) 0)) : False :=
    not_isField_of_isSquare_discr ⟨2, by rw [discr_def]; norm_num⟩ h

/-- The discriminant of `K ≅ ℚ(√D)` is `D`. -/
theorem discr_eq_of_algEquiv {D : ℤ} (hD : IsFundamentalDiscriminant D) (h1 : D ≠ 1)
    (e : K ≃ₐ[ℚ] Model D) : discr K = D := by
  have : Fact (IsFundamentalDiscriminant D) := ⟨hD⟩
  have : Fact (D ≠ 1) := ⟨h1⟩
  rw [discr_eq_discr_of_algEquiv K e, discr_model]

/-- **Davenport §5, p. 41 (row 5-15, first half)**: the discriminant of a quadratic number field
is a fundamental discriminant `≠ 1`, and `K ≅ ℚ(√d_K)`. -/
theorem isFundamental_discr (hK : finrank ℚ K = 2) :
    IsFundamentalDiscriminant (discr K) ∧ discr K ≠ 1 ∧
      Nonempty (K ≃ₐ[ℚ] Model (discr K)) := by
  obtain ⟨D, hD, h1, ⟨e⟩⟩ := exists_algEquiv_model K hK
  rw [discr_eq_of_algEquiv K hD h1 e]
  exact ⟨hD, h1, ⟨e⟩⟩

/-- **The ring of integers of a quadratic number field** `K` is `ℤ[ω]`,
`ω² = d_K / 4 + (d_K % 4) ω`: `ω = √d_K / 2` or `(1 + √d_K) / 2`. -/
theorem nonempty_ringEquiv_order (hK : finrank ℚ K = 2) :
    Nonempty (Order (discr K) ≃+* 𝓞 K) := by
  obtain ⟨hD, h1, ⟨e⟩⟩ := isFundamental_discr K hK
  have : Fact (IsFundamentalDiscriminant (discr K)) := ⟨hD⟩
  have : Fact (discr K ≠ 1) := ⟨h1⟩
  exact ⟨(ringOfIntegersEquiv (discr K)).symm.trans (RingOfIntegers.mapRingEquiv e.symm.toRingEquiv)⟩

/-- **Davenport §5, p. 41 (row 5-15, second half)**: every fundamental discriminant `D ≠ 1` is the
discriminant of a quadratic number field, namely `ℚ(√D)`. -/
theorem exists_field_discr_eq {D : ℤ} (hD : IsFundamentalDiscriminant D) (h1 : D ≠ 1) :
    ∃ (K : Type) (_ : Field K) (_ : NumberField K), finrank ℚ K = 2 ∧ discr K = D := by
  have : Fact (IsFundamentalDiscriminant D) := ⟨hD⟩
  have : Fact (D ≠ 1) := ⟨h1⟩
  exact ⟨Model D, inferInstance, inferInstance, finrank_model D, discr_model D⟩

end NTKB.QuadraticField
