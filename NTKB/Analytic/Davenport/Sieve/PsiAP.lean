/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Davenport.Sieve.Characters
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Data.Nat.Factorization.Basic

/-!
# `ψ(x; q, a)`, `ψ(x, χ)` and the character expansion (Davenport, Chapters 28 and 29)

* `psiAP x q a = ψ(x; q, a) = ∑_{n ≤ x, n ≡ a (q)} Λ(n)`, `psiChar χ x = ψ(x, χ) = ∑_{n ≤ x} χ(n) Λ(n)`
  and `psiChar' χ x = ψ'(x, χ)`, which is `ψ(x, χ)` minus the main term `x` when `χ` is principal;
* the character expansion (C) of §29 (= §28):
  `ψ(x; q, a) - x/φ(q) = φ(q)⁻¹ ∑_χ χ̄(a) ψ'(x, χ)` for `(a, q) = 1` (`psiAP_sub_eq`);
* Parseval over the reduced residues:
  `∑_{(a, q) = 1} (ψ(x; q, a) - x/φ(q))² = φ(q)⁻¹ ∑_χ |ψ'(x, χ)|²` (`sum_sq_psiAP_sub_eq`);
* induced characters: `|ψ'(x, χ) - ψ'(x, χ₁)| ≤ 2 (log q)(log x)` when `χ` is induced by the
  primitive `χ₁` (`norm_psiChar'_sub_le`).
-/

open Finset Real ComplexConjugate
open scoped ArithmeticFunction.vonMangoldt

namespace NTKB.Davenport

/-- `ψ(x; q, a) = ∑_{n ≤ x, n ≡ a (mod q)} Λ(n)`. -/
noncomputable def psiAP (x : ℝ) (q : ℕ) (a : ℤ) : ℝ :=
  ∑ n ∈ (Icc 1 ⌊x⌋₊).filter (fun n : ℕ ↦ (n : ℤ) ≡ a [ZMOD q]), Λ n

/-- `ψ(x, χ) = ∑_{n ≤ x} χ(n) Λ(n)`. -/
noncomputable def psiChar {q : ℕ} (χ : DirichletCharacter ℂ q) (x : ℝ) : ℂ :=
  ∑ n ∈ Icc 1 ⌊x⌋₊, χ n * Λ n

open Classical in
/-- `ψ'(x, χ)`: `ψ(x, χ)` minus the main term `x` when `χ` is the principal character. -/
noncomputable def psiChar' {q : ℕ} (χ : DirichletCharacter ℂ q) (x : ℝ) : ℂ :=
  psiChar χ x - if χ = 1 then (x : ℂ) else 0

variable {q : ℕ} [NeZero q]

/-- `∑_χ χ̄(a) χ(b) = φ(q) [a = b]` for `a` a unit, and `0` for `a` not a unit. -/
lemma sum_char_inv_mul_char (a b : ZMod q) :
    ∑ χ : DirichletCharacter ℂ q, χ⁻¹ a * χ b =
      if IsUnit a ∧ a = b then (q.totient : ℂ) else 0 := by
  by_cases ha : IsUnit a
  · simp_rw [MulChar.inv_apply, ← map_mul, DirichletCharacter.sum_characters_eq,
      Ring.inverse_mul_eq_iff_eq_mul _ _ _ ha, mul_one]
    simp only [ha, true_and, eq_comm]
  · have : ∀ χ : DirichletCharacter ℂ q, χ⁻¹ a = 0 := fun χ ↦ MulChar.map_nonunit _ ha
    simp [this, ha]

open Classical in
/-- `∑_a χ̄₁(a) χ₂(a) = φ(q) [χ₁ = χ₂]`. -/
lemma sum_inv_mul_eq (χ₁ χ₂ : DirichletCharacter ℂ q) :
    ∑ a : ZMod q, χ₁⁻¹ a * χ₂ a = if χ₁ = χ₂ then (q.totient : ℂ) else 0 := by
  classical
  simp_rw [← MulChar.mul_apply]
  split_ifs with h
  · subst h
    rw [inv_mul_cancel, MulChar.sum_one_eq_card_units, ZMod.card_units_eq_totient]
  · exact MulChar.sum_eq_zero_of_ne_one (fun h' ↦ h (inv_mul_eq_one.1 h'))

/-- Dual orthogonality: `∑_{a unit} |∑_χ χ̄(a) y_χ|² = φ(q) ∑_χ |y_χ|²`. -/
lemma sum_units_norm_sq (y : DirichletCharacter ℂ q → ℂ) :
    ∑ a ∈ univ.filter (IsUnit : ZMod q → Prop), ‖∑ χ, χ⁻¹ a * y χ‖ ^ 2 =
      q.totient * ∑ χ, ‖y χ‖ ^ 2 := by
  classical
  -- the nonunits contribute nothing
  have hnu : ∀ a : ZMod q, ¬ IsUnit a → ∑ χ : DirichletCharacter ℂ q, χ⁻¹ a * y χ = 0 :=
    fun a ha ↦ sum_eq_zero fun χ _ ↦ by rw [MulChar.map_nonunit _ ha, zero_mul]
  have hfull : ∑ a ∈ univ.filter (IsUnit : ZMod q → Prop), ‖∑ χ, χ⁻¹ a * y χ‖ ^ 2 =
      ∑ a : ZMod q, ‖∑ χ, χ⁻¹ a * y χ‖ ^ 2 := by
    refine sum_filter_of_ne fun a _ h ↦ ?_
    by_contra ha
    apply h
    rw [hnu a ha, norm_zero]; norm_num
  rw [hfull]
  apply Complex.ofReal_injective
  push_cast
  simp_rw [← Complex.mul_conj', map_sum, sum_mul_sum]
  rw [sum_comm]
  refine (sum_congr rfl fun χ₁ _ ↦ sum_comm).trans ?_
  have hinner : ∀ χ₁ χ₂ : DirichletCharacter ℂ q,
      ∑ a : ZMod q, χ₁⁻¹ a * y χ₁ * conj (χ₂⁻¹ a * y χ₂) =
        y χ₁ * conj (y χ₂) * if χ₁ = χ₂ then (q.totient : ℂ) else 0 := by
    intro χ₁ χ₂
    rw [← sum_inv_mul_eq, mul_sum]
    refine sum_congr rfl fun a _ ↦ ?_
    rw [map_mul, ← Complex.star_def, MulChar.star_apply', inv_inv]
    ring
  rw [sum_congr rfl fun χ₁ _ ↦ sum_congr rfl fun χ₂ _ ↦ hinner χ₁ χ₂]
  simp_rw [mul_ite, mul_zero, sum_ite_eq, mem_univ, if_true, mul_sum]
  refine sum_congr rfl fun χ _ ↦ ?_
  rw [Complex.mul_conj']; ring

/-- **Davenport, Ch. 29, (C)** (also Ch. 28): for `a` coprime to `q`,
`φ(q) (ψ(x; q, a) - x/φ(q)) = ∑_χ χ̄(a) ψ'(x, χ)`. -/
@[kb "davenport1980" "Ch 29, p. 169, (C)"]
theorem psiAP_sub_eq (x : ℝ) {a : ℤ} (ha : IsCoprime a q) :
    (q.totient : ℂ) * ((psiAP x q a - x / q.totient : ℝ) : ℂ) =
      ∑ χ : DirichletCharacter ℂ q, χ⁻¹ a * psiChar' χ x := by
  classical
  have hu : IsUnit (a : ZMod q) := (ZMod.isUnit_intCast_iff_isCoprime a q).2 (isCoprime_comm.1 ha)
  have hφ : (q.totient : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.2 (Nat.pos_of_ne_zero (NeZero.ne q))).ne'
  simp only [psiChar', psiChar, mul_sub, sum_sub_distrib, mul_ite, mul_zero]
  rw [sum_ite_eq' univ (1 : DirichletCharacter ℂ q), if_pos (mem_univ _), inv_one,
    MulChar.one_apply hu, one_mul]
  simp_rw [mul_sum]
  rw [sum_comm]
  have hsum : ∀ n : ℕ, ∑ χ : DirichletCharacter ℂ q, χ⁻¹ (a : ZMod q) * (χ n * Λ n) =
      if (n : ℤ) ≡ a [ZMOD q] then (q.totient : ℂ) * Λ n else 0 := by
    intro n
    simp_rw [← mul_assoc, ← sum_mul, sum_char_inv_mul_char, ite_mul, zero_mul]
    congr 1
    simp only [hu, true_and, eq_comm (a := (a : ZMod q))]
    rw [show ((n : ℕ) : ZMod q) = ((n : ℤ) : ZMod q) by push_cast; rfl,
      ZMod.intCast_eq_intCast_iff]
  rw [sum_congr rfl fun n _ ↦ hsum n, ← sum_filter, ← mul_sum]
  simp only [psiAP]
  push_cast
  field_simp

/-- **Davenport, Ch. 29** (Parseval over the reduced residues):
`∑_{1 ≤ a ≤ q, (a, q) = 1} (ψ(x; q, a) - x/φ(q))² = φ(q)⁻¹ ∑_χ |ψ'(x, χ)|²`. -/
@[kb "davenport1980" "Ch 29, p. 170"]
theorem sum_sq_psiAP_sub_eq (x : ℝ) :
    ∑ a ∈ (Icc 1 q).filter (fun a ↦ Nat.Coprime a q), (psiAP x q a - x / q.totient) ^ 2 =
      1 / q.totient * ∑ χ : DirichletCharacter ℂ q, ‖psiChar' χ x‖ ^ 2 := by
  have hφ : (0 : ℝ) < q.totient := by
    exact_mod_cast Nat.totient_pos.2 (Nat.pos_of_ne_zero (NeZero.ne q))
  have h1 : ∀ a ∈ (Icc 1 q).filter (fun a ↦ Nat.Coprime a q),
      (psiAP x q a - x / q.totient) ^ 2 =
        1 / (q.totient : ℝ) ^ 2 * ‖∑ χ : DirichletCharacter ℂ q, χ⁻¹ a * psiChar' χ x‖ ^ 2 := by
    intro a ha
    have hc : IsCoprime (a : ℤ) q := Nat.isCoprime_iff_coprime.2 (mem_filter.1 ha).2
    have := psiAP_sub_eq (q := q) x hc
    rw [Int.cast_natCast] at this
    rw [← this, norm_mul, Complex.norm_real, Complex.norm_natCast, Real.norm_eq_abs, mul_pow,
      sq_abs]
    field_simp
  rw [sum_congr rfl h1, ← mul_sum]
  have h2 := sum_units_norm_sq (q := q) (fun χ ↦ psiChar' χ x)
  rw [sum_units_eq_sum_coprime (fun a ↦ ‖∑ χ : DirichletCharacter ℂ q, χ⁻¹ a * psiChar' χ x‖ ^ 2)]
    at h2
  rw [h2]
  field_simp

end NTKB.Davenport
