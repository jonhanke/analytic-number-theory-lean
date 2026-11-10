/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.Algebra.Polynomial.Identities
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.FieldTheory.Finite.Basic
import NTKB.Attr

/-!
# Lifting solutions of polynomial congruences (Apostol, Theorem 5.30)

Let `f ∈ ℤ[x]`, `p` prime, `a ≥ 2`, and `r` a solution of `f(x) ≡ 0 (mod p^{a-1})`. The candidates
`t ≡ r (mod p^{a-1})` are `t = r + q p^{a-1}`, and **Theorem 5.30**:
`f(r + q p^{a-1}) ≡ 0 (mod p^a)` iff `q f'(r) ≡ -f(r)/p^{a-1} (mod p)`. Consequently
(a) if `p ∤ f'(r)` there is exactly one `q` modulo `p`;
(b) if `p ∣ f'(r)` and `f(r) ≡ 0 (mod p^a)` every `q` works;
(c) if `p ∣ f'(r)` and `f(r) ≢ 0 (mod p^a)` no `q` works.
Apostol's proof: Taylor's formula `f(r + y) = f(r) + f'(r) y + k y²` (Mathlib's
`Polynomial.binomExpansion`) with `y = q p^{a-1}`, `p^a ∣ y²`.
-/

open Polynomial

namespace NTKB.Apostol

/-- **Theorem 5.30** (the lifting criterion). -/
@[kb "apostol1976" "Thm 5.30, p. 121"]
theorem dvd_eval_add_iff (f : ℤ[X]) {p : ℕ} (hp : p.Prime) {a : ℕ} (ha : 2 ≤ a) {r c : ℤ}
    (hr : f.eval r = (p : ℤ) ^ (a - 1) * c) (q : ℤ) :
    (p : ℤ) ^ a ∣ f.eval (r + q * (p : ℤ) ^ (a - 1)) ↔ (p : ℤ) ∣ q * f.derivative.eval r + c := by
  obtain ⟨k, hk⟩ := binomExpansion f r (q * (p : ℤ) ^ (a - 1))
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hpa : (p : ℤ) ^ a = (p : ℤ) ^ (a - 1) * p := by
    rw [← pow_succ]; congr 1; omega
  have hsq : (p : ℤ) ^ a ∣ k * (q * (p : ℤ) ^ (a - 1)) ^ 2 := by
    refine Dvd.dvd.mul_left ?_ k
    rw [mul_pow, ← pow_mul]
    exact Dvd.dvd.mul_left (pow_dvd_pow _ (by omega)) _
  rw [hk, hr]
  have e : (p : ℤ) ^ (a - 1) * c + eval r (derivative f) * (q * (p : ℤ) ^ (a - 1)) +
      k * (q * (p : ℤ) ^ (a - 1)) ^ 2 =
      (p : ℤ) ^ (a - 1) * (q * eval r (derivative f) + c) + k * (q * (p : ℤ) ^ (a - 1)) ^ 2 := by
    ring
  rw [e, (Int.dvd_add_left hsq), hpa]
  exact mul_dvd_mul_iff_left (pow_ne_zero _ hp0)

/-- **Theorem 5.30 (a)**: if `p ∤ f'(r)`, exactly one lift `q` modulo `p`. -/
@[kb "apostol1976" "Thm 5.30, p. 121"]
theorem existsUnique_lift (f : ℤ[X]) {p : ℕ} (hp : p.Prime) {a : ℕ} (ha : 2 ≤ a) {r c : ℤ}
    (hr : f.eval r = (p : ℤ) ^ (a - 1) * c) (hf' : ¬ (p : ℤ) ∣ f.derivative.eval r) :
    ∃ q : ℤ, 0 ≤ q ∧ q < p ∧ (p : ℤ) ^ a ∣ f.eval (r + q * (p : ℤ) ^ (a - 1)) ∧
      ∀ q₁ : ℤ, (p : ℤ) ^ a ∣ f.eval (r + q₁ * (p : ℤ) ^ (a - 1)) → Int.ModEq p q₁ q := by
  have hpi := Nat.prime_iff_prime_int.mp hp
  have hp0 : (0 : ℤ) < p := by exact_mod_cast hp.pos
  set d := f.derivative.eval r
  -- `d` is invertible mod `p`
  have hcop : IsCoprime d p := (Prime.coprime_iff_not_dvd hpi).mpr hf' |>.symm
  obtain ⟨u, v, huv⟩ := hcop
  -- `q₀ = -u c` solves `q d + c ≡ 0`
  set q := (-u * c) % p
  have hq : (p : ℤ) ∣ q * d + c := by
    have h1 : (p : ℤ) ∣ (-u * c) * d + c := ⟨v * c, by linear_combination (-c) * huv⟩
    have h2 : Int.ModEq p q (-u * c) := Int.emod_emod_of_dvd _ (dvd_refl _)
    have h3 : Int.ModEq p (q * d + c) ((-u * c) * d + c) := (h2.mul_right _).add_right _
    have := dvd_add (Int.ModEq.dvd h3.symm) h1
    rwa [sub_add_cancel] at this
  refine ⟨q, Int.emod_nonneg _ hp0.ne', Int.emod_lt_of_pos _ hp0,
    (dvd_eval_add_iff f hp ha hr q).mpr hq, fun q₁ hq₁ => ?_⟩
  have h' := (dvd_eval_add_iff f hp ha hr q₁).mp hq₁
  have hdiff : (p : ℤ) ∣ (q₁ - q) * d := by
    have := dvd_sub h' hq
    rw [show q₁ * d + c - (q * d + c) = (q₁ - q) * d by ring] at this
    exact this
  rcases hpi.dvd_or_dvd hdiff with h | h
  · exact (Int.modEq_iff_dvd.mpr (by rw [← neg_sub, dvd_neg]; exact h))
  · exact absurd h hf'

/-- **Theorem 5.30 (b), (c)**: if `p ∣ f'(r)`, then every `q` lifts when `p^a ∣ f(r)`, and none
does otherwise. -/
@[kb "apostol1976" "Thm 5.30, p. 121"]
theorem lift_of_dvd_derivative (f : ℤ[X]) {p : ℕ} (hp : p.Prime) {a : ℕ} (ha : 2 ≤ a) {r c : ℤ}
    (hr : f.eval r = (p : ℤ) ^ (a - 1) * c) (hf' : (p : ℤ) ∣ f.derivative.eval r) (q : ℤ) :
    (p : ℤ) ^ a ∣ f.eval (r + q * (p : ℤ) ^ (a - 1)) ↔ (p : ℤ) ^ a ∣ f.eval r := by
  rw [dvd_eval_add_iff f hp ha hr q, (Int.dvd_add_right (hf'.mul_left q)), hr]
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hpa : (p : ℤ) ^ a = (p : ℤ) ^ (a - 1) * p := by
    rw [← pow_succ]; congr 1; omega
  rw [hpa, mul_dvd_mul_iff_left (pow_ne_zero _ hp0)]

end NTKB.Apostol
