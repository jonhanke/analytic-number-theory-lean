/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Davenport.Forms.BasicTheorem

/-!
# Primes represented by forms of discriminant `d` (Davenport, Chapter 5, p. 41)

Davenport (§5, p. 41, row 5-18): for a fundamental discriminant `d`, a prime `p` is not
represented by any form of discriminant `d` if `(d/p) = -1`, and is represented by at least one
form if `(d/p) = 1`. (The splitting of `p` in the quadratic field by `(d/p)`, the other half of
the row, is the decomposition law of quadratic fields, `NTKB.QuadraticField.kroneckerChar_prime_cases`.)

Both follow from the correspondence between representations and ideals
(`NTKB.Davenport.repToIdeal`, rows 6-20 to 6-22) and the ideal count `∑_{m ∣ p} (d/m) = 1 + (d/p)`
(`NTKB.Davenport.card_absNorm_eq_sum_order`): a representation `f(x, y) = p` by a form with
`a > 0` gives an ideal of norm `p` (none exists if `(d/p) = -1`), and an ideal of norm `p` (one
exists if `(d/p) ≠ -1`) comes from a representation of `p` by a form with `a > 0`. The forms are
those with `a > 0` (for `d < 0` the positive definite ones, which are the forms that can represent
a positive integer).
-/

noncomputable section

open QuadraticAlgebra NTKB.QuadraticField

namespace NTKB.Davenport

variable {D : ℤ}

/-- The ideals of norm `p` of `ℤ[ω]` number `1 + (D/p)`. -/
theorem card_absNorm_eq_prime [Fact (IsFundamentalDiscriminant D)] [Fact (D ≠ 1)] {p : ℕ}
    (hp : p.Prime) :
    (Nat.card {J : Ideal (Order D) // Ideal.absNorm J = p} : ℂ) =
      1 + kroneckerChar D (p : ZMod D.natAbs) := by
  rw [card_absNorm_eq_sum_order hp.ne_zero, Nat.Prime.sum_divisors hp, Nat.cast_one, map_one,
    add_comm]

/-- **Davenport, Ch. 5, p. 41 (row 5-18)**: if `(d/p) = -1`, no form of discriminant `d` with
`a > 0` represents the prime `p`. -/
@[kb "davenport1980" "Ch 5, p. 41"]
theorem formEval_ne_prime_of_kroneckerChar_eq_neg_one (hD : IsFundamentalDiscriminant D)
    (h1 : D ≠ 1) {p : ℕ} (hp : p.Prime) (hχ : kroneckerChar D (p : ZMod D.natAbs) = -1)
    {f : ℤ × ℤ × ℤ} (hf : formDisc f = D) (ha : 0 < f.1) (x y : ℤ) :
    formEval f x y ≠ p := by
  have : Fact (IsFundamentalDiscriminant D) := ⟨hD⟩
  have : Fact (D ≠ 1) := ⟨h1⟩
  intro hxy
  have hfin : Finite {J : Ideal (Order D) // Ideal.absNorm J = p} :=
    (finite_absNorm_eq_order (D := D) p).to_subtype
  have h0 : Nat.card {J : Ideal (Order D) // Ideal.absNorm J = p} = 0 := by
    have := card_absNorm_eq_prime (D := D) hp
    rw [hχ, add_neg_cancel] at this
    exact_mod_cast this
  have hJ := (repIdeal_mem (D := D) hf ha hp.pos ⟨(x, y), hxy⟩).1
  have hne : Nonempty {J : Ideal (Order D) // Ideal.absNorm J = p} := ⟨⟨_, hJ⟩⟩
  have := Nat.card_pos (α := {J : Ideal (Order D) // Ideal.absNorm J = p})
  omega

/-- **Davenport, Ch. 5, p. 41 (row 5-18)**: if `(d/p) ≠ -1` (in particular if `(d/p) = 1`), the
prime `p` is represented by some form of discriminant `d` with `a > 0`. -/
@[kb "davenport1980" "Ch 5, p. 41"]
theorem exists_formEval_eq_prime_of_kroneckerChar_ne_neg_one (hD : IsFundamentalDiscriminant D)
    (h1 : D ≠ 1) {p : ℕ} (hp : p.Prime) (hχ : kroneckerChar D (p : ZMod D.natAbs) ≠ -1) :
    ∃ f : ℤ × ℤ × ℤ, formDisc f = D ∧ 0 < f.1 ∧ ∃ x y : ℤ, formEval f x y = p := by
  have : Fact (IsFundamentalDiscriminant D) := ⟨hD⟩
  have : Fact (D ≠ 1) := ⟨h1⟩
  have hfin : Finite {J : Ideal (Order D) // Ideal.absNorm J = p} :=
    (finite_absNorm_eq_order (D := D) p).to_subtype
  have hpos : 0 < Nat.card {J : Ideal (Order D) // Ideal.absNorm J = p} := by
    rcases Nat.eq_zero_or_pos (Nat.card {J : Ideal (Order D) // Ideal.absNorm J = p}) with h | h
    · exfalso
      have := card_absNorm_eq_prime (D := D) hp
      rw [h, Nat.cast_zero] at this
      exact hχ (by linear_combination -this)
    · exact h
  obtain ⟨⟨J, hJ⟩⟩ := (Nat.card_pos_iff.mp hpos).1
  have hJ0 : J ≠ ⊥ := by
    rintro rfl
    rw [Ideal.absNorm_bot] at hJ
    exact hp.ne_zero hJ.symm
  obtain ⟨g, hg, hga, e, he, hJe⟩ := exists_eq_span_mul_formIdeal hJ0
  have hgJ : NarrowRel (formIdeal D g) J :=
    ⟨e, 1, by rw [norm_intCast, map_one, mul_one]; positivity,
      by rw [Ideal.span_singleton_one, Ideal.top_mul, hJe]⟩
  have hf : formDisc (formNeg g) = D := by rw [formDisc_formNeg, hg]
  have hfa : 0 < (formNeg g).1 := hga
  have hJ' : Ideal.absNorm J = p ∧ NarrowRel (formIdeal D (formNeg (formNeg g))) J := by
    rw [formNeg_formNeg]; exact ⟨hJ, hgJ⟩
  obtain ⟨P, -⟩ := repToIdeal_surjective hf hfa hp.pos ⟨J, hJ'⟩
  induction P using Quot.ind
  rename_i r
  exact ⟨formNeg g, hf, hfa, r.1.1, r.1.2, r.2⟩

end NTKB.Davenport
