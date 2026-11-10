/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Apostol.ArithmeticFunctions.Multiplicative
import Mathlib.NumberTheory.LSeries.Convolution
import Mathlib.NumberTheory.LSeries.Dirichlet

/-!
# The Dirichlet series of Liouville's function (Apostol, Chapter 11, Example 6 of §11.4)

`∑ λ(n) n^{-s} = ζ(2s)/ζ(s)` for `σ > 1`. Apostol's proof: `λ * 1` is the indicator of the
squares (Theorem 2.19, `sum_divisors_liouville`), whose Dirichlet series is `∑ m^{-2s} = ζ(2s)`,
and Theorem 11.5 (`LSeries_convolution'`).
-/

open Complex LSeries ArithmeticFunction
open scoped LSeries.notation

namespace NTKB.Apostol

/-- The indicator of the nonzero squares. -/
noncomputable def squareIndicator (n : ℕ) : ℂ := if n ≠ 0 ∧ IsSquare n then 1 else 0

lemma LSeries_squareIndicator {s : ℂ} (hs : 1 < s.re) :
    LSeries squareIndicator s = riemannZeta (2 * s) := by
  rw [← LSeries_one_eq_riemannZeta (by simp; linarith), LSeries, LSeries]
  have hinj : Function.Injective fun m : ℕ => m ^ 2 := fun a b h => by
    simpa using (Nat.pow_left_injective (by norm_num : 2 ≠ 0)) h
  rw [← hinj.tsum_eq (f := term squareIndicator s)]
  · refine tsum_congr fun m => ?_
    rcases eq_or_ne m 0 with rfl | hm
    · simp
    have hm2 : m ^ 2 ≠ 0 := pow_ne_zero 2 hm
    rw [term_of_ne_zero hm2, term_of_ne_zero hm, squareIndicator, ite_eq_left_of_eq_true _ _ (eq_true ⟨hm2, m, sq m⟩),
      Pi.one_apply, Nat.cast_pow, sq, natCast_mul_natCast_cpow,
      show (2 : ℂ) * s = ((2 : ℕ) : ℂ) * s by norm_num, cpow_nat_mul, sq]
  · intro n hn
    rw [Function.mem_support] at hn
    rcases eq_or_ne n 0 with rfl | hn0
    · simp at hn
    have : squareIndicator n ≠ 0 := by
      intro h; apply hn; rw [term_of_ne_zero hn0, h, zero_div]
    simp only [squareIndicator, ne_eq, ite_eq_right_iff, Classical.not_imp] at this
    obtain ⟨⟨-, m, rfl⟩, -⟩ := this
    exact ⟨m, by simp [sq]⟩

/-- **Apostol, §11.4 Example 6**: `∑ λ(n) n^{-s} = ζ(2s)/ζ(s)` for `σ > 1`. -/
@[kb "apostol1976" "Ch. 11, §11.4 Example 6, p. 229"]
theorem LSeries_liouville {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => (liouville n : ℂ)) s = riemannZeta (2 * s) / riemannZeta s := by
  have hlam : LSeriesSummable (fun n => (liouville n : ℂ)) s := by
    refine LSeriesSummable_of_le_const_mul_rpow (x := 1) hs ⟨1, fun n hn => ?_⟩
    rw [liouville_apply hn]
    simp
  have h1 : LSeriesSummable 1 s := LSeriesSummable_one_iff.mpr hs
  have hconv : LSeries ((fun n => (liouville n : ℂ)) ⍟ 1) s = LSeries squareIndicator s := by
    refine LSeries_congr (fun {n} hn => ?_) s
    rw [convolution_def]
    simp only [Pi.one_apply, mul_one]
    have := sum_divisors_liouville hn
    rw [squareIndicator, if_congr (and_iff_right hn) rfl rfl]
    have e : ∑ p ∈ n.divisorsAntidiagonal, (liouville p.1 : ℂ) = ∑ d ∈ n.divisors, (liouville d : ℂ) :=
      Nat.sum_divisorsAntidiagonal (fun a _ => (liouville a : ℂ))
    rw [e]
    exact_mod_cast this
  rw [LSeries_convolution' hlam h1, LSeries_squareIndicator hs,
    LSeries_one_eq_riemannZeta hs] at hconv
  rw [← hconv, mul_div_cancel_right₀ _ (riemannZeta_ne_zero_of_one_lt_re hs)]

end NTKB.Apostol
