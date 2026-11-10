/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.Polynomial.Roots
import NTKB.Attr

/-!
# Linear and polynomial congruences (Apostol, Theorems 5.7, 5.12, 5.13, 5.20, 5.21)

* **5.7**: if `a ≡ b (mod m)` and `|b - a| < m` then `a = b`.
* **5.12**: if `(a, m) = 1`, then `a x ≡ b (mod m)` has exactly one solution modulo `m`.
* **5.13**: with `d = (a, m)`, `a x ≡ b (mod m)` is solvable iff `d ∣ b`.
* **5.20**: if `(a, m) = 1`, then `x = b a^{φ(m) - 1}` solves `a x ≡ b (mod m)`.
* **5.21** (Lagrange): a polynomial congruence `f(x) ≡ 0 (mod p)` of degree `n` whose leading
  coefficient is prime to `p` has at most `n` solutions modulo `p`.
-/

open Polynomial

namespace NTKB.Apostol

/-- **Theorem 5.7**. -/
@[kb "apostol1976" "Thm 5.7, p. 108"]
theorem eq_of_modEq_of_abs_sub_lt {a b m : ℤ} (h : a ≡ b [ZMOD m]) (hab : |b - a| < m) :
    a = b := by
  have := Int.eq_zero_of_abs_lt_dvd (Int.ModEq.dvd h) hab
  linarith

lemma isUnit_intCast_of_isCoprime {m : ℕ} {a : ℤ} (ha : IsCoprime a m) : IsUnit (a : ZMod m) := by
  obtain ⟨u, v, huv⟩ := ha
  have : (u : ZMod m) * a = 1 := by
    have := congrArg (Int.cast : ℤ → ZMod m) huv
    push_cast at this
    rwa [ZMod.natCast_self, mul_zero, add_zero] at this
  exact IsUnit.of_mul_eq_one_right _ this

/-- **Theorem 5.12**: for `(a, m) = 1` the congruence `a x ≡ b (mod m)` has exactly one solution
modulo `m`. -/
@[kb "apostol1976" "Thm 5.12, p. 110"]
theorem existsUnique_mul_eq {m : ℕ} {a : ℤ} (ha : IsCoprime a m) (b : ℤ) :
    ∃! x : ZMod m, (a : ZMod m) * x = b := by
  obtain ⟨u, hu⟩ := isUnit_intCast_of_isCoprime ha
  rw [← hu]
  refine ⟨(u⁻¹ : (ZMod m)ˣ) * b, ?_, fun y hy => ?_⟩
  · show (u : ZMod m) * ((u⁻¹ : (ZMod m)ˣ) * (b : ZMod m)) = b
    rw [← mul_assoc, Units.mul_inv, one_mul]
  · have hy' : (u : ZMod m) * y = b := hy
    rw [← hy', ← mul_assoc, Units.inv_mul, one_mul]

/-- **Theorem 5.13**: with `d = (a, m)`, the congruence `a x ≡ b (mod m)` is solvable iff
`d ∣ b`. -/
@[kb "apostol1976" "Thm 5.13, p. 110"]
theorem exists_mul_modEq_iff (a b m : ℤ) :
    (∃ x : ℤ, a * x ≡ b [ZMOD m]) ↔ (Int.gcd a m : ℤ) ∣ b := by
  constructor
  · rintro ⟨x, hx⟩
    have h1 : (Int.gcd a m : ℤ) ∣ a * x := (Int.gcd_dvd_left a m).mul_right x
    have h2 : (Int.gcd a m : ℤ) ∣ b - a * x := (Int.gcd_dvd_right a m).trans (Int.ModEq.dvd hx)
    have := dvd_add h1 h2
    simpa using this
  · rintro ⟨c, hc⟩
    refine ⟨Int.gcdA a m * c, ?_⟩
    rw [Int.modEq_iff_dvd]
    refine ⟨Int.gcdB a m * c, ?_⟩
    rw [hc, Int.gcd_eq_gcd_ab a m]
    ring

/-- **Theorem 5.20**: for `(a, m) = 1`, `m ≥ 1`, `x = b a^{φ(m) - 1}` solves `a x ≡ b (mod m)`. -/
@[kb "apostol1976" "Thm 5.20, p. 113"]
theorem mul_pow_totient_sub_one {m : ℕ} (hm : 1 ≤ m) {a : ℤ} (ha : IsCoprime a m) (b : ℤ) :
    (a : ZMod m) * (b * (a : ZMod m) ^ (m.totient - 1)) = b := by
  obtain ⟨u, hu⟩ := isUnit_intCast_of_isCoprime ha
  have ht : 1 ≤ m.totient := Nat.totient_pos.mpr hm
  rw [← hu, mul_left_comm, ← pow_succ', Nat.sub_add_cancel ht, ← Units.val_pow_eq_pow_val,
    ZMod.pow_totient, Units.val_one, mul_one]

/-- **Theorem 5.21** (Lagrange): if `f ∈ ℤ[x]` has degree `n` and `p ∤` its leading coefficient,
the congruence `f(x) ≡ 0 (mod p)` has at most `n` solutions modulo `p`. -/
@[kb "apostol1976" "Thm 5.21, p. 115"]
theorem card_solutions_le_natDegree {p : ℕ} [Fact p.Prime] {f : ℤ[X]}
    (hf : ¬ (p : ℤ) ∣ f.leadingCoeff) :
    (Finset.univ.filter fun x : ZMod p => (f.map (Int.castRingHom (ZMod p))).eval x = 0).card ≤
      f.natDegree := by
  set g := f.map (Int.castRingHom (ZMod p))
  have hlc : (Int.castRingHom (ZMod p)) f.leadingCoeff ≠ 0 := by
    rw [eq_intCast, Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hf
  have hg0 : g ≠ 0 := by
    intro h
    apply hlc
    have := congrArg leadingCoeff h
    rwa [leadingCoeff_map_of_leadingCoeff_ne_zero _ hlc, leadingCoeff_zero] at this
  have hdeg : g.natDegree = f.natDegree := natDegree_map_of_leadingCoeff_ne_zero _ hlc
  calc (Finset.univ.filter fun x : ZMod p => g.eval x = 0).card
      ≤ g.roots.toFinset.card := Finset.card_le_card fun x hx => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
        exact Multiset.mem_toFinset.mpr ((mem_roots hg0).mpr hx)
    _ ≤ Multiset.card g.roots := Multiset.toFinset_card_le _
    _ ≤ g.natDegree := card_roots' g
    _ = f.natDegree := hdeg

end NTKB.Apostol
