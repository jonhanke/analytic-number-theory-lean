/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Davenport.Siegel.MertensAP

/-!
# `∑_p χ(p)/p` converges for nonprincipal `χ`

**Davenport, Ch. 7, p. 67 (row 7-14).** A corollary of Mertens'
theorem for progressions (row 7-16, `sumInvPrimeAP_sub_le`): split the primes by their residue
modulo `q`; the terms `(log log x)/φ(q)` cancel since `∑_a χ(a) = 0`. With the rate
`O_q(1/log x)`.
-/

open Finset
open scoped Real

namespace NTKB.Davenport

/-- `∑_{p ≤ x} χ(p)/p`. -/
noncomputable def sumCharPrime {q : ℕ} (χ : DirichletCharacter ℂ q) (x : ℝ) : ℂ :=
  ∑ p ∈ (Icc 1 ⌊x⌋₊).filter Nat.Prime, χ p / p

/-- For `a < q`: `p % q = a ↔ p ≡ a (mod q)`. -/
lemma mod_eq_iff_modEq {q a : ℕ} (ha : a < q) (p : ℕ) :
    p % q = a ↔ (p : ℤ) ≡ a [ZMOD q] := by
  rw [Int.ModEq, ← Int.natCast_mod, ← Int.natCast_mod, Nat.mod_eq_of_lt ha]
  exact_mod_cast Iff.rfl

/-- Splitting the primes by residue class. -/
lemma sumCharPrime_eq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (x : ℝ) :
    sumCharPrime χ x = ∑ a ∈ range q, χ a * (sumInvPrimeAP x q a : ℂ) := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  unfold sumCharPrime sumInvPrimeAP
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun p ↦ p % q) (t := range q)
    (fun p _ ↦ Finset.mem_range.mpr (Nat.mod_lt p hq))]
  refine Finset.sum_congr rfl fun a ha ↦ ?_
  have ha' : a < q := Finset.mem_range.mp ha
  rw [Finset.filter_filter, Finset.filter_congr (q := fun p : ℕ ↦ p.Prime ∧ (p : ℤ) ≡ (a : ℤ) [ZMOD (q : ℤ)])
    (fun p _ ↦ by rw [mod_eq_iff_modEq ha' p])]
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun p hp ↦ ?_
  obtain ⟨-, -, h3⟩ := Finset.mem_filter.mp hp
  have h4 : (p : ZMod q) = (a : ZMod q) := by
    rw [← ZMod.natCast_mod p q, (mod_eq_iff_modEq ha' p).mpr h3]
  rw [h4, div_eq_mul_one_div]

/-- `∑_{a < q} χ(a) = 0` for `χ ≠ 1`. -/
lemma sum_range_char_eq_zero {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) :
    ∑ a ∈ range q, χ a = 0 := by
  have e : ∑ a ∈ range q, χ a = ∑ z : ZMod q, χ z := by
    refine Finset.sum_bij (fun a _ ↦ (a : ZMod q)) (by simp) (fun a ha b hb h ↦ ?_)
      (fun z _ ↦ ⟨z.val, Finset.mem_range.mpr (ZMod.val_lt z), by simp⟩) (by simp)
    have := congrArg ZMod.val h
    rwa [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt (Finset.mem_range.mp ha),
      Nat.mod_eq_of_lt (Finset.mem_range.mp hb)] at this
  rw [e]
  exact MulChar.sum_eq_zero_of_ne_one hχ

/-- **Davenport, Ch. 7, p. 67 (row 7-14)**: for a nonprincipal character `χ` modulo `q`, the sum
`∑_{p ≤ x} χ(p)/p` converges as `x → ∞`, with `|∑_{p ≤ x} χ(p)/p - S| ≤ B/log x` for `x ≥ 3`. -/
@[kb "davenport1980" "Ch 7, p. 67"]
theorem sumCharPrime_sub_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    ∃ S : ℂ, ∃ B : ℝ, ∀ x : ℝ, 3 ≤ x → ‖sumCharPrime χ x - S‖ ≤ B / Real.log x := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hcon : ∀ a : ℕ, ∃ A B : ℝ, χ a ≠ 0 → ∀ x : ℝ, 3 ≤ x →
      |sumInvPrimeAP x q a - Real.log (Real.log x) / q.totient - A| ≤ B / Real.log x := by
    intro a
    by_cases h : χ a = 0
    · exact ⟨0, 0, fun h' ↦ absurd h h'⟩
    · have hu : IsUnit (a : ZMod q) := by
        by_contra hn; exact h (MulChar.map_nonunit χ hn)
      have hcop : IsCoprime (a : ℤ) q := by
        rw [Int.isCoprime_iff_gcd_eq_one]
        have := (ZMod.isUnit_iff_coprime a q).mp hu
        exact_mod_cast this
      obtain ⟨A, B, hAB⟩ := sumInvPrimeAP_sub_le q hq a hcop
      exact ⟨A, B, fun _ ↦ hAB⟩
  choose A B hAB using hcon
  refine ⟨∑ a ∈ range q, χ a * (A a : ℂ), ∑ a ∈ range q, |B a|, fun x hx ↦ ?_⟩
  have hlx : 0 < Real.log x := Real.log_pos (by linarith)
  set L := Real.log (Real.log x) / q.totient
  rw [sumCharPrime_eq]
  have e : ∑ a ∈ range q, χ a * (sumInvPrimeAP x q a : ℂ) - ∑ a ∈ range q, χ a * (A a : ℂ) =
      ∑ a ∈ range q, (χ a * ((sumInvPrimeAP x q a - L - A a : ℝ) : ℂ) + (L : ℂ) * χ a) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    push_cast; ring
  rw [e, Finset.sum_add_distrib, ← Finset.mul_sum, sum_range_char_eq_zero hχ, mul_zero, add_zero]
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_div]
  refine Finset.sum_le_sum fun a _ ↦ ?_
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  by_cases h : χ a = 0
  · rw [h, norm_zero, zero_mul]; positivity
  · have := hAB a h x hx
    have h1 := DirichletCharacter.norm_le_one χ a
    calc ‖χ a‖ * |sumInvPrimeAP x q a - L - A a| ≤ 1 * (B a / Real.log x) :=
          mul_le_mul h1 this (abs_nonneg _) zero_le_one
      _ ≤ |B a| / Real.log x := by
          rw [one_mul]; gcongr; exact le_abs_self _

end NTKB.Davenport
