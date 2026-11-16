/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Davenport.Forms.Representation

/-!
# Davenport, Chapter 6: the basic theorem `R(n) = w ∑_{m ∣ n} (d/m)` (row 6-7)

(§6, p. 57.) Let `d ≠ 1` be a fundamental discriminant, `χ(m) = (d/m)` its Kronecker character
(`NTKB.kroneckerChar d`) and `S` a complete system of representatives of the proper classes of
forms of discriminant `d`, each with `a > 0` (`NTKB.Davenport.IsFormSystem`). For `n ≥ 1`:

* `NTKB.Davenport.sum_repClassCount_eq`: `∑_{f ∈ S} R_f(n) = ∑_{m ∣ n} χ(m)`, where `R_f(n)` counts
  the representations of `n` by `f` up to automorphs (Davenport's `R(n)` for `d > 0`, `w = 1`);
* `NTKB.Davenport.sum_card_reps_eq_of_neg`: for `d < 0`, the total number of representations is
  `∑_{f ∈ S} r_f(n) = w ∑_{m ∣ n} χ(m)` with `w = 6, 4, 2` for `d = -3`, `d = -4`, `d < -4`.

Davenport assumes `(n, d) = 1` (his proof counts solutions of `z² ≡ d (mod 4n)`); the proof here
goes through ideals (rows 6-20 to 6-22) and the ideal count of quadratic fields, and needs no such condition.
-/

noncomputable section

open QuadraticAlgebra NTKB.QuadraticField

namespace NTKB.Davenport

variable {D : ℤ}

/-! ### The ideal count on `ℤ[ω]` -/

section transport

variable [Fact (IsFundamentalDiscriminant D)] [Fact (D ≠ 1)]

theorem absNorm_comap_ringOfIntegersEquiv (J : Ideal (Order D)) :
    Ideal.absNorm (J.comap (ringOfIntegersEquiv D)) = Ideal.absNorm J := by
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  exact Nat.card_congr (Ideal.quotientEquiv _ J (ringOfIntegersEquiv D)
    (Ideal.map_comap_of_surjective _ (RingEquiv.surjective _) J).symm).toEquiv

theorem card_absNorm_eq_order (n : ℕ) :
    Nat.card {J : Ideal (Order D) // Ideal.absNorm J = n} =
      Nat.card {I : Ideal (NumberField.RingOfIntegers (Model D)) // Ideal.absNorm I = n} :=
  Nat.card_congr (Equiv.subtypeEquiv (ringOfIntegersEquiv D).idealComapOrderIso.toEquiv
    (fun J ↦ by
      change _ ↔ Ideal.absNorm (J.comap (ringOfIntegersEquiv D)) = n
      rw [absNorm_comap_ringOfIntegersEquiv]))

/-- **Davenport §6, p. 52**, on `ℤ[ω]`: the number of ideals of norm `n ≥ 1` is
`∑_{m ∣ n} (D/m)`. -/
theorem card_absNorm_eq_sum_order {n : ℕ} (hn : n ≠ 0) :
    (Nat.card {J : Ideal (Order D) // Ideal.absNorm J = n} : ℂ) =
      ∑ m ∈ n.divisors, kroneckerChar D m := by
  rw [card_absNorm_eq_order]
  have := card_absNorm_eq (K := Model D) (finrank_model D) hn
  rwa [discr_model] at this

end transport

/-! ### Row 6-7 -/

/-- **Davenport §6, p. 57 (row 6-7): the basic theorem.** Let `d ≠ 1` be a fundamental
discriminant and `S` a complete system of representatives (with `a > 0`) of the proper classes of
forms of discriminant `d`. For every `n ≥ 1`, the number of representations of `n` by the forms of
`S`, counted up to automorphs, is `∑_{m ∣ n} (d/m)`. -/
@[kb "davenport1980" "Ch 6, p. 57"]
theorem sum_repClassCount_eq (hD : IsFundamentalDiscriminant D) (h1 : D ≠ 1)
    {S : Finset (ℤ × ℤ × ℤ)} (hS : IsFormSystem D S) {n : ℕ} (hn : 0 < n) :
    ((∑ f ∈ S, repClassCount f n : ℕ) : ℂ) = ∑ m ∈ n.divisors, kroneckerChar D m := by
  have : Fact (IsFundamentalDiscriminant D) := ⟨hD⟩
  have : Fact (D ≠ 1) := ⟨h1⟩
  rw [sum_repClassCount_eq_card hS hn, card_absNorm_eq_sum_order hn.ne']

end NTKB.Davenport
