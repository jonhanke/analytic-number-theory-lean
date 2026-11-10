/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.RingTheory.IntegralDomain
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Data.Matrix.Mul
import NTKB.Attr

/-!
# The character matrix of a finite abelian group (Apostol, Theorem 6.11)

Let `G` be a finite abelian group of order `n` and `A = (f_i(a_j))` the matrix of the values of its
characters (`f : G →* ℂˣ`) at its elements. **Theorem 6.11**: `A A* = n I`.

The `(f, g)` entry of `A A*` is `∑_a f(a) \overline{g(a)} = ∑_a (f g⁻¹)(a)` (character values are
roots of unity, so `\overline{g(a)} = g(a)⁻¹`), which is `n` if `f = g` and `0` otherwise
(Mathlib's `sum_hom_units`). The rows are indexed by all characters; that there are exactly `n`
of them (so that `A` is square and also `A* A = n I`) is Apostol's Theorem 6.8, not needed here.
-/

open Matrix ComplexConjugate

namespace NTKB.Apostol

variable {G : Type*} [CommGroup G] [Fintype G]

/-- The character matrix `A_{f,a} = f(a)` (rows: characters, columns: group elements). -/
def charMatrix (G : Type*) [CommGroup G] : Matrix (G →* ℂˣ) G ℂ := fun f a => (f a : ℂ)

lemma conj_char_apply (f : G →* ℂˣ) (a : G) : conj (f a : ℂ) = ((f a)⁻¹ : ℂˣ) := by
  have h : ((f a : ℂ)) ^ orderOf a = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_orderOf_eq_one, map_one, Units.val_one]
  rw [Units.val_inv_eq_inv_val, Complex.inv_eq_conj
    (Complex.norm_eq_one_of_pow_eq_one h (orderOf_pos a).ne')]

/-- **Theorem 6.11**: `A A* = n I` for the character matrix `A` of a group of order `n`. -/
@[kb "apostol1976" "Thm 6.11, p. 136"]
theorem charMatrix_mul_conjTranspose [DecidableEq (G →* ℂˣ)] :
    charMatrix G * (charMatrix G)ᴴ = (Fintype.card G : ℂ) • (1 : Matrix (G →* ℂˣ) (G →* ℂˣ) ℂ) := by
  classical
  ext f g
  rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply]
  simp only [charMatrix, conjTranspose_apply, RCLike.star_def, conj_char_apply]
  have h := sum_hom_units ((Units.coeHom ℂ).comp (f * g⁻¹))
  have e : ∀ a : G, (f a : ℂ) * ((g a)⁻¹ : ℂˣ) = (Units.coeHom ℂ).comp (f * g⁻¹) a := by
    intro a
    simp [MonoidHom.mul_apply, MonoidHom.inv_apply]
  simp_rw [e, h]
  by_cases hfg : f = g
  · subst hfg
    simp only [ite_true, smul_eq_mul, mul_one]
    rw [if_pos]
    ext a
    simp
  · rw [if_neg hfg, smul_zero, if_neg ?_]
    · simp
    intro h1
    apply hfg
    ext a
    have := congrArg (fun φ => φ a) h1
    simp only [MonoidHom.comp_apply, MonoidHom.mul_apply, MonoidHom.inv_apply,
      MonoidHom.one_apply, Units.coeHom_apply] at this
    have hu : f a * (g a)⁻¹ = 1 := Units.ext (by rw [this, Units.val_one])
    simp [mul_inv_eq_one.mp hu]

end NTKB.Apostol
