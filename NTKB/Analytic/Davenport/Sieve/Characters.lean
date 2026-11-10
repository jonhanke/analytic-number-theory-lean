/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Davenport.Sieve.Farey
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.NumberTheory.MulChar.Lemmas

/-!
# Gallagher's large sieve for characters (Davenport, Chapter 27, Theorem 4)

For `T(χ) = ∑_{M < n ≤ M + N} a_n χ(n)` and real `Q ≥ 1`,
`∑_{q ≤ Q} (q/φ(q)) ∑*_{χ mod q} |T(χ)|² ≤ (N + 3Q²) ∑ |a_n|²`, the inner sum over primitive
characters (`large_sieve_characters`).

Davenport's proof: for primitive `χ`, `χ(n) τ(χ̄) = ∑_a χ̄(a) e(an/q)`, so
`τ(χ̄) T(χ) = ∑_a χ̄(a) S(a/q)` and `|τ(χ̄)|² = q`; dropping primitivity and using the
orthogonality of characters gives (10): `∑*_χ |T(χ)|² ≤ (φ(q)/q) ∑_{(a, q) = 1} |S(a/q)|²`
(`sum_primitive_norm_sq_le`), and (8) finishes the proof.
-/

open Finset Real ComplexConjugate

namespace NTKB.Davenport

variable {q : ℕ} [NeZero q]

/-- Orthogonality: `∑_χ |∑_a χ̄(a) x_a|² = φ(q) ∑_{a unit} |x_a|²`. -/
lemma sum_char_norm_sq (x : ZMod q → ℂ) :
    ∑ χ : DirichletCharacter ℂ q, ‖∑ a, χ⁻¹ a * x a‖ ^ 2 =
      q.totient * ∑ a ∈ univ.filter IsUnit, ‖x a‖ ^ 2 := by
  classical
  apply Complex.ofReal_injective
  push_cast
  simp_rw [← Complex.mul_conj', map_sum, sum_mul_sum]
  rw [sum_comm]
  refine (sum_congr rfl fun a _ ↦ sum_comm).trans ?_
  have hinner : ∀ a b : ZMod q, ∑ χ : DirichletCharacter ℂ q, χ⁻¹ a * x a * conj (χ⁻¹ b * x b) =
      x a * conj (x b) * if IsUnit a ∧ a = b then (q.totient : ℂ) else 0 := by
    intro a b
    have h1 : ∀ χ : DirichletCharacter ℂ q, χ⁻¹ a * x a * conj (χ⁻¹ b * x b) =
        x a * conj (x b) * (χ⁻¹ a * χ b) := by
      intro χ
      rw [map_mul, ← Complex.star_def, MulChar.star_apply', inv_inv]
      ring
    simp_rw [h1, ← mul_sum]
    congr 1
    by_cases ha : IsUnit a
    · simp_rw [MulChar.inv_apply, ← map_mul, DirichletCharacter.sum_characters_eq,
        Ring.inverse_mul_eq_iff_eq_mul _ _ _ ha, mul_one]
      simp only [ha, true_and, eq_comm]
    · have : ∀ χ : DirichletCharacter ℂ q, χ⁻¹ a = 0 := fun χ ↦ MulChar.map_nonunit _ ha
      simp [this, ha]
  rw [sum_congr rfl fun a _ ↦ sum_congr rfl fun b _ ↦ hinner a b]
  simp_rw [mul_ite, mul_zero]
  have hrow : ∀ a : ZMod q, (∑ b, if IsUnit a ∧ a = b then x a * conj (x b) * q.totient else 0) =
      if IsUnit a then x a * conj (x a) * q.totient else 0 := by
    intro a
    by_cases ha : IsUnit a
    · simp only [ha, true_and]; rw [sum_ite_eq]; simp
    · simp [ha]
  rw [sum_congr rfl fun a _ ↦ hrow a, ← sum_filter, mul_sum]
  refine sum_congr rfl fun a _ ↦ ?_
  rw [Complex.mul_conj']; ring

/-- Units of `ZMod q` correspond to `1 ≤ b ≤ q` with `(b, q) = 1`. -/
lemma sum_units_eq_sum_coprime {R : Type*} [AddCommMonoid R] (f : ZMod q → R) :
    ∑ a ∈ univ.filter (IsUnit : ZMod q → Prop), f a =
      ∑ b ∈ (Icc 1 q).filter (fun b ↦ Nat.Coprime b q), f b := by
  classical
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  symm
  refine sum_nbij' (fun b ↦ (b : ZMod q)) (fun a ↦ if a.val = 0 then q else a.val) ?_ ?_ ?_ ?_ ?_
  · intro b hb
    rw [mem_filter] at hb ⊢
    exact ⟨mem_univ _, (ZMod.isUnit_iff_coprime b q).2 hb.2⟩
  · intro a ha
    rw [mem_filter] at ha
    replace ha := ha.2
    rw [mem_filter, mem_Icc]
    have hv := ZMod.val_lt a
    have hcast : ((if a.val = 0 then q else a.val : ℕ) : ZMod q) = a := by
      split_ifs with h
      · rw [ZMod.natCast_self]; exact ((ZMod.val_eq_zero a).1 h).symm
      · exact ZMod.natCast_zmod_val a
    refine ⟨⟨by split_ifs <;> omega, by split_ifs <;> omega⟩, ?_⟩
    rw [← ZMod.isUnit_iff_coprime, hcast]; exact ha
  · intro b hb
    rw [mem_filter, mem_Icc] at hb
    rw [ZMod.val_natCast]
    by_cases hbq : b = q
    · subst hbq; simp
    · have : b % q = b := Nat.mod_eq_of_lt (by omega)
      rw [this, if_neg (by omega)]
  · intro a _
    split_ifs with h
    · rw [ZMod.natCast_self]; exact ((ZMod.val_eq_zero a).1 h).symm
    · exact ZMod.natCast_zmod_val a
  · intro b _; rfl

open scoped Classical in
/-- **Davenport, Ch. 27, (10)**: for `T(χ) = ∑_{M < n ≤ M + N} a_n χ(n)`,
`∑*_{χ mod q} |T(χ)|² ≤ (φ(q)/q) ∑_{a ≤ q, (a, q) = 1} |S(a/q)|²`. -/
@[kb "davenport1980" "Ch 27, p. 160, (10)"]
theorem sum_primitive_norm_sq_le (M : ℤ) (N : ℕ) (c : ℤ → ℂ) :
    ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ ↦ χ.IsPrimitive),
        ‖∑ n ∈ Ioc M (M + N), c n * χ n‖ ^ 2 ≤
      (q.totient / q : ℝ) * ∑ b ∈ (Icc 1 q).filter (fun b ↦ Nat.Coprime b q),
        ‖∑ n ∈ Ioc M (M + N), c n *
          Complex.exp (2 * π * Complex.I * (n * (((b : ℝ) / q : ℝ) : ℂ)))‖ ^ 2 := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  set I := Ioc M (M + N)
  set S' : ZMod q → ℂ := fun a ↦ ∑ n ∈ I, c n * ZMod.stdAddChar (a * (n : ZMod q))
  set U : DirichletCharacter ℂ q → ℂ := fun χ ↦ ∑ a, χ⁻¹ a * S' a
  -- primitive characters
  have hT : ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive →
      ‖∑ n ∈ I, c n * χ n‖ ^ 2 = 1 / q * ‖U χ‖ ^ 2 := by
    intro χ hχ
    have hτ : ‖gaussSum χ⁻¹ ZMod.stdAddChar‖ = √q :=
      DirichletCharacter.norm_gaussSum_stdAddChar hχ.inv
    have hmul : (∑ n ∈ I, c n * χ n) * gaussSum χ⁻¹ ZMod.stdAddChar = U χ := by
      simp only [U, S', sum_mul, mul_sum]
      rw [sum_comm]
      refine sum_congr rfl fun n _ ↦ ?_
      rw [mul_assoc, char_mul_gaussSum_inv hχ, mul_sum]
      refine sum_congr rfl fun a _ ↦ ?_
      ring
    have := congrArg (fun z : ℂ ↦ ‖z‖ ^ 2) hmul
    simp only [norm_mul, hτ, mul_pow, Real.sq_sqrt hq0.le] at this
    rw [← this]; field_simp
  have hall := sum_char_norm_sq S'
  calc _ = ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ ↦ χ.IsPrimitive),
        1 / (q : ℝ) * ‖U χ‖ ^ 2 := sum_congr rfl fun χ hχ ↦ hT χ (mem_filter.1 hχ).2
    _ ≤ ∑ χ : DirichletCharacter ℂ q, 1 / (q : ℝ) * ‖U χ‖ ^ 2 :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ ↦ by positivity
    _ = 1 / q * (q.totient * ∑ a ∈ univ.filter (IsUnit : ZMod q → Prop), ‖S' a‖ ^ 2) := by
        rw [← mul_sum]; congr 1
    _ = _ := by
        rw [sum_units_eq_sum_coprime (fun a ↦ ‖S' a‖ ^ 2)]
        have hb : ∀ b ∈ (Icc 1 q).filter (fun b ↦ Nat.Coprime b q), ‖S' b‖ ^ 2 =
            ‖∑ n ∈ I, c n *
              Complex.exp (2 * π * Complex.I * (n * (((b : ℝ) / q : ℝ) : ℂ)))‖ ^ 2 := by
          intro b _
          have : S' b = ∑ n ∈ I, c n *
              Complex.exp (2 * π * Complex.I * (n * (((b : ℝ) / q : ℝ) : ℂ))) := by
            refine sum_congr rfl fun n _ ↦ ?_
            rw [show (b : ZMod q) * (n : ZMod q) = (((b : ℤ) * n : ℤ) : ZMod q) by push_cast; ring,
              ZMod.stdAddChar_coe]
            congr 2; push_cast; ring
          rw [this]
        rw [sum_congr rfl hb]
        ring

open scoped Classical in
/-- **Davenport, Ch. 27, Theorem 4** (Gallagher): for real `Q ≥ 1`,
`∑_{q ≤ Q} (q/φ(q)) ∑*_{χ mod q} |∑_{M < n ≤ M + N} a_n χ(n)|² ≤ (N + 3Q²) ∑ |a_n|²`, the inner
sum over primitive characters modulo `q`. -/
@[kb "davenport1980" "Ch 27, p. 160, Theorem 4"]
theorem large_sieve_characters {Q : ℝ} (hQ : 1 ≤ Q) (M : ℤ) (N : ℕ) (c : ℤ → ℂ) :
    ∑ q ∈ Icc 1 ⌊Q⌋₊, ((q : ℝ) / q.totient) *
        ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ ↦ χ.IsPrimitive),
          ‖∑ n ∈ Ioc M (M + N), c n * χ n‖ ^ 2 ≤
      (N + 3 * Q ^ 2) * ∑ n ∈ Ioc M (M + N), ‖c n‖ ^ 2 := by
  refine le_trans (sum_le_sum fun q hq ↦ ?_) (large_sieve_farey hQ M N c)
  have : NeZero q := ⟨by have := (mem_Icc.1 hq).1; omega⟩
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (mem_Icc.1 hq).1
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.2 (mem_Icc.1 hq).1
  have h10 := sum_primitive_norm_sq_le (q := q) M N c
  calc (q : ℝ) / q.totient * _ ≤ (q : ℝ) / q.totient * ((q.totient / q : ℝ) * _) := by
        gcongr
    _ = _ := by field_simp

end NTKB.Davenport
