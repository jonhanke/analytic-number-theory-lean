/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import NTKB.Attr

/-!
# Powers of the quadratic Gauss sum (Apostol, Chapter 9, §9.9, Theorem 9.15)

**Theorem 9.15.** For distinct odd primes `p, q` and `χ = (·|p)`:
`G(1, χ)^{q-1} = (q|p) ∑_{r₁ + ⋯ + r_q ≡ q (mod p)} (r₁ ⋯ r_q | p)`.

Stated here for any nonprincipal quadratic character `χ` modulo a prime `p` (that is, `χ = (·|p)`),
any odd `q` with `p ∤ q`, and `G(n, χ) = gaussSum χ (ψ.mulShift n)` with `ψ = ZMod.stdAddChar`
(`ψ(x) = e^{2πi x/p}`). Apostol's proof: compute the finite Fourier coefficient
`a_q(m) = (1/p) ∑_n G(n, χ)^q e(-mn/p)` in two ways — by expanding the `q`th power
(`a_q(m) = ∑_{r₁+⋯+r_q ≡ m} χ(r₁⋯r_q)`) and by separability `G(n, χ) = χ(n) G(1, χ)`
(`a_q(m) = χ(m) G(1, χ)^{q-1}`, using `G(1,χ)² = χ(-1) p`).
-/

open Finset

namespace NTKB.Apostol

variable {p : ℕ} [Fact p.Prime] {χ : MulChar (ZMod p) ℂ}

/-- `G(n, χ) = χ(n) G(1, χ)` for every `n`, for a nonprincipal quadratic `χ` modulo `p`. -/
theorem gaussSum_mulShift_eq_mul (hχ1 : χ ≠ 1) (hχ2 : χ.IsQuadratic) (ψ : AddChar (ZMod p) ℂ)
    (n : ZMod p) : gaussSum χ (ψ.mulShift n) = χ n * gaussSum χ ψ := by
  by_cases hn : n = 0
  · subst hn
    have : gaussSum χ (ψ.mulShift 0) = ∑ x, χ x := by
      simp [gaussSum, AddChar.mulShift_apply]
    rw [this, MulChar.sum_eq_zero_of_ne_one hχ1, MulChar.map_nonunit _ not_isUnit_zero, zero_mul]
  · have hu : IsUnit n := Ne.isUnit hn
    obtain ⟨u, rfl⟩ := hu
    rw [gaussSum_mulShift_eq, hχ2.inv]

theorem addChar_map_sum {ι : Type*} (ψ : AddChar (ZMod p) ℂ) (s : Finset ι) (f : ι → ZMod p) :
    ψ (∑ i ∈ s, f i) = ∏ i ∈ s, ψ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [sum_insert ha, prod_insert ha, AddChar.map_add_eq_mul, ih]

/-- The `q`th power of `G(n, χ)` expanded over `q`-tuples. -/
theorem gaussSum_mulShift_pow (ψ : AddChar (ZMod p) ℂ) (n : ZMod p) (q : ℕ) :
    gaussSum χ (ψ.mulShift n) ^ q =
      ∑ r : Fin q → ZMod p, χ (∏ i, r i) * ψ (n * ∑ i, r i) := by
  rw [← Fin.prod_const]
  simp only [gaussSum, AddChar.mulShift_apply]
  rw [prod_univ_sum]
  refine sum_congr (by simp) fun r _ ↦ ?_
  rw [prod_mul_distrib, map_prod, mul_sum, addChar_map_sum]

/-- **Apostol, proof of Theorem 9.15**: for odd `q` and every `m`,
`∑_{r₁ + ⋯ + r_q = m} χ(r₁ ⋯ r_q) = χ(m) G(1, χ)^{q-1}`. -/
theorem sum_tuples_eq_mul_gaussSum_pow (hχ1 : χ ≠ 1) (hχ2 : χ.IsQuadratic) {q : ℕ} (hq : Odd q)
    (m : ZMod p) :
    ∑ r ∈ (univ : Finset (Fin q → ZMod p)).filter (fun r ↦ ∑ i, r i = m), χ (∏ i, r i) =
      χ m * gaussSum χ (ZMod.stdAddChar (N := p)) ^ (q - 1) := by
  set ψ : AddChar (ZMod p) ℂ := ZMod.stdAddChar
  have hψ : ψ.IsPrimitive := ZMod.isPrimitive_stdAddChar p
  set G := gaussSum χ ψ
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  -- first computation of `p a_q(m)`
  have h1 : ∑ n : ZMod p, gaussSum χ (ψ.mulShift n) ^ q * ψ (n * (-m)) =
      p * ∑ r ∈ (univ : Finset (Fin q → ZMod p)).filter (fun r ↦ ∑ i, r i = m),
        χ (∏ i, r i) := by
    simp_rw [gaussSum_mulShift_pow, sum_mul]
    rw [sum_comm, mul_sum, sum_filter]
    refine sum_congr rfl fun r _ ↦ ?_
    have : ∑ n : ZMod p, χ (∏ i, r i) * ψ (n * ∑ i, r i) * ψ (n * (-m)) =
        χ (∏ i, r i) * ∑ n : ZMod p, ψ (n * (∑ i, r i - m)) := by
      rw [mul_sum]
      refine sum_congr rfl fun n _ ↦ ?_
      rw [mul_assoc, ← AddChar.map_add_eq_mul, sub_eq_add_neg, mul_add]
    rw [this, AddChar.sum_mulShift _ hψ, ZMod.card]
    simp only [sub_eq_zero]
    split_ifs <;> simp [mul_comm]
  -- second computation, by separability
  have hpow : ∀ n : ZMod p, χ n ^ q = χ n := by
    intro n
    rcases hχ2 n with h | h | h <;> rw [h]
    · exact zero_pow (by obtain ⟨k, rfl⟩ := hq; omega)
    · exact one_pow _
    · exact hq.neg_one_pow
  have h2 : ∑ n : ZMod p, gaussSum χ (ψ.mulShift n) ^ q * ψ (n * (-m)) =
      G ^ q * (χ (-m) * G) := by
    calc ∑ n : ZMod p, gaussSum χ (ψ.mulShift n) ^ q * ψ (n * (-m))
        = ∑ n : ZMod p, G ^ q * (χ n * ψ (n * (-m))) := by
          refine sum_congr rfl fun n _ ↦ ?_
          rw [gaussSum_mulShift_eq_mul hχ1 hχ2 ψ n, mul_pow, hpow]; ring
      _ = G ^ q * gaussSum χ (ψ.mulShift (-m)) := by
          have hG : gaussSum χ (ψ.mulShift (-m)) = ∑ n : ZMod p, χ n * ψ (n * (-m)) := by
            simp only [gaussSum, AddChar.mulShift_apply]
            exact sum_congr rfl fun n _ ↦ by rw [mul_comm (-m) n]
          rw [hG, mul_sum]
      _ = G ^ q * (χ (-m) * G) := by rw [gaussSum_mulShift_eq_mul hχ1 hχ2 ψ (-m)]
  -- `G² = χ(-1) p`
  have hG2 := gaussSum_sq hχ1 hχ2 hψ
  rw [ZMod.card] at hG2
  have hq1 : 1 ≤ q := by obtain ⟨k, rfl⟩ := hq; omega
  have hGq : G ^ q = G ^ (q - 1) * G := by rw [← pow_succ, Nat.sub_add_cancel hq1]
  have hm : χ (-1) * χ (-m) = χ m := by rw [← map_mul]; ring_nf
  have key : (p : ℂ) * ∑ r ∈ (univ : Finset (Fin q → ZMod p)).filter (fun r ↦ ∑ i, r i = m),
      χ (∏ i, r i) = p * (χ m * G ^ (q - 1)) := by
    rw [← h1, h2, hGq, ← hm]
    linear_combination (G ^ (q - 1) * χ (-m)) * hG2
  exact mul_left_cancel₀ hp0 key

/-- **Apostol, Theorem 9.15.** For odd `q` with `p ∤ q`:
`G(1, χ)^{q-1} = χ(q) ∑_{r₁ + ⋯ + r_q ≡ q (mod p)} χ(r₁ ⋯ r_q)`. -/
@[kb "apostol1976" "Thm 9.15, p. 193"]
theorem gaussSum_pow_eq_sum_tuples (hχ1 : χ ≠ 1) (hχ2 : χ.IsQuadratic) {q : ℕ} (hq : Odd q)
    (hpq : (q : ZMod p) ≠ 0) :
    gaussSum χ (ZMod.stdAddChar (N := p)) ^ (q - 1) =
      χ q * ∑ r ∈ (univ : Finset (Fin q → ZMod p)).filter (fun r ↦ ∑ i, r i = (q : ZMod p)),
        χ (∏ i, r i) := by
  rw [sum_tuples_eq_mul_gaussSum_pow hχ1 hχ2 hq, ← mul_assoc]
  have : χ (q : ZMod p) * χ (q : ZMod p) = 1 := by
    obtain ⟨u, hu⟩ := Ne.isUnit hpq
    rw [← hu, ← sq]
    have := MulChar.pow_apply_coe χ 2 u
    rw [hχ2.sq_eq_one, MulChar.one_apply_coe] at this
    exact this.symm
  rw [this, one_mul]

end NTKB.Apostol
