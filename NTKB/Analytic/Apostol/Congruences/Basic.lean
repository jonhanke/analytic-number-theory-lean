/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.Index
import NTKB.Attr

/-!
# Congruences (Apostol, Chapter 5: Theorems 5.14, 5.23, 5.27, 5.28)

Residues modulo `m` are elements of `ZMod m`.

* Theorem 5.14: if `d = (a, m)` divides `b`, the congruence `ax ≡ b (mod m)` has exactly `d`
  solutions modulo `m`;
* Theorem 5.23: all coefficients of `(x - 1)(x - 2)⋯(x - p + 1) - x^{p-1} + 1` are divisible by
  the prime `p` (Apostol's proof: a polynomial of degree `< p - 1` with the `p - 1` roots
  `1, …, p - 1` modulo `p` vanishes modulo `p`, Theorem 5.22);
* Theorem 5.27: for pairwise coprime moduli `m_k` and `(a_k, m_k) = 1`, the system
  `a_k x ≡ b_k (mod m_k)` has exactly one solution modulo `m₁⋯m_r`;
* Theorem 5.28: for pairwise coprime `m_i`, the number of solutions of `f(x) ≡ 0 (mod m₁⋯m_r)` is
  the product of the numbers of solutions modulo the `m_i`.
-/

open Finset Polynomial
open scoped Function

namespace NTKB.Apostol

/-! ## Theorem 5.14 -/

/-- **Apostol, Theorem 5.14.** If `d = (a, m)` divides `b`, then `ax ≡ b (mod m)` has exactly
`d` solutions modulo `m`. -/
@[kb "apostol1976" "Thm 5.14, p. 112"]
theorem card_mul_eq {m : ℕ} [NeZero m] (a : ℕ) {b : ℤ} (hb : (Nat.gcd a m : ℤ) ∣ b) :
    #{x : ZMod m | (a : ZMod m) * x = b} = Nat.gcd a m := by
  classical
  set f : ZMod m →+ ZMod m := AddMonoidHom.mulLeft (a : ZMod m)
  -- `b` is in the range (Bezout)
  have hrange : ((b : ℤ) : ZMod m) ∈ Set.range f := by
    obtain ⟨c, hc⟩ := hb
    refine ⟨(Nat.gcdA a m * c : ℤ), ?_⟩
    simp only [f, AddMonoidHom.coe_mulLeft]
    have hbez : (Nat.gcd a m : ℤ) = a * Nat.gcdA a m + m * Nat.gcdB a m := Nat.gcd_eq_gcd_ab a m
    rw [hc, hbez]
    push_cast
    simp [mul_add, ZMod.natCast_self]
    ring
  -- all nonempty fibres have the size of the kernel
  have hfib : #{x : ZMod m | f x = b} = #{x : ZMod m | f x = 0} :=
    AddMonoidHom.card_fiber_eq_of_mem_range f hrange ⟨0, map_zero f⟩
  have hker : #{x : ZMod m | f x = 0} = Nat.gcd a m := by
    have hrng : f.range = AddSubgroup.zmultiples (a : ZMod m) := by
      ext y
      simp only [AddMonoidHom.mem_range, AddSubgroup.mem_zmultiples_iff, f,
        AddMonoidHom.coe_mulLeft]
      constructor
      · rintro ⟨x, rfl⟩
        refine ⟨(x.val : ℤ), ?_⟩
        rw [zsmul_eq_mul, mul_comm]
        simp
      · rintro ⟨n, rfl⟩
        exact ⟨(n : ZMod m), by rw [zsmul_eq_mul, mul_comm]⟩
    have h1 := AddSubgroup.card_mul_index f.ker
    rw [AddSubgroup.index_ker, hrng, Nat.card_zmultiples, ZMod.addOrderOf_coe a (NeZero.ne m),
      Nat.card_zmod] at h1
    have hg : Nat.gcd m a ∣ m := Nat.gcd_dvd_left m a
    have hpos : 0 < m / Nat.gcd m a :=
      Nat.div_pos (Nat.le_of_dvd (NeZero.pos m) hg) (Nat.gcd_pos_of_pos_left _ (NeZero.pos m))
    have hcard : Nat.card f.ker = Nat.gcd m a := by
      have := Nat.div_mul_cancel hg
      have h2 : Nat.card f.ker * (m / Nat.gcd m a) = Nat.gcd m a * (m / Nat.gcd m a) := by
        rw [h1, mul_comm, Nat.div_mul_cancel hg]
      exact Nat.eq_of_mul_eq_mul_right hpos h2
    rw [Nat.gcd_comm] at hcard
    rw [← hcard, Nat.card_eq_fintype_card, ← Fintype.card_subtype]
    rfl
  rw [← hker, ← hfib]
  rfl

/-! ## Theorem 5.23 -/

/-- **Apostol, Theorem 5.23.** For a prime `p`, every coefficient of
`(x - 1)(x - 2)⋯(x - p + 1) - x^{p-1} + 1` is divisible by `p`. -/
@[kb "apostol1976" "Thm 5.23, p. 116"]
theorem dvd_coeff_prod_X_sub_sub (p : ℕ) [hp : Fact p.Prime] (i : ℕ) :
    (p : ℤ) ∣ (∏ k ∈ Icc 1 (p - 1), (X - C (k : ℤ)) - X ^ (p - 1) + 1).coeff i := by
  set g : (ZMod p)[X] := ∏ k ∈ Icc 1 (p - 1), (X - C (k : ZMod p))
  set h : (ZMod p)[X] := X ^ (p - 1) - 1
  have hmap : (∏ k ∈ Icc 1 (p - 1), (X - C (k : ℤ)) - X ^ (p - 1) + 1).map
      (Int.castRingHom (ZMod p)) = g - h := by
    simp only [g, h, Polynomial.map_add, Polynomial.map_sub, Polynomial.map_prod, Polynomial.map_X,
      Polynomial.map_C, Polynomial.map_pow, Polynomial.map_one, eq_intCast, Int.cast_natCast,
      Polynomial.map_natCast, Polynomial.C_eq_natCast, ← C_eq_intCast]
    ring
  -- `g - h` has degree `< p - 1` and the `p - 1` roots `1, …, p - 1`
  have hp1 : 1 ≤ p - 1 := by have := hp.out.two_le; omega
  have hgm : g.Monic := monic_prod_of_monic _ _ fun k _ ↦ monic_X_sub_C _
  have hgd : g.natDegree = p - 1 := by
    rw [natDegree_prod_of_monic _ _ fun k _ ↦ monic_X_sub_C _]
    simp only [natDegree_X_sub_C, sum_const, Nat.card_Icc, smul_eq_mul, mul_one]
    omega
  have hhm : h.Monic := by
    simp only [h]
    rw [show (X ^ (p - 1) - 1 : (ZMod p)[X]) = X ^ (p - 1) - C 1 by rw [C_1]]
    exact monic_X_pow_sub_C 1 (by omega)
  have hhd : h.natDegree = p - 1 := by
    simp only [h]
    rw [show (X ^ (p - 1) - 1 : (ZMod p)[X]) = X ^ (p - 1) - C 1 by rw [C_1]]
    exact natDegree_X_pow_sub_C (R := ZMod p) 1
  have hzero : g - h = 0 := by
    apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero' (g - h) (univ.erase 0)
    · intro a ha
      have ha0 : a ≠ 0 := ne_of_mem_erase ha
      rw [eval_sub]
      have hg0 : g.eval a = 0 := by
        simp only [g, eval_prod, eval_sub, eval_X, eval_C]
        apply prod_eq_zero (i := a.val)
        · have h1 : a.val ≠ 0 := (ZMod.val_eq_zero a).not.2 ha0
          have h2 := ZMod.val_lt a
          simp only [mem_Icc]; omega
        · simp [ZMod.natCast_zmod_val]
      have hh0 : h.eval a = 0 := by simp [h, ZMod.pow_card_sub_one_eq_one ha0]
      rw [hg0, hh0, sub_zero]
    · rw [card_erase_of_mem (mem_univ _), card_univ, ZMod.card]
      by_cases hne : g - h = 0
      · rw [hne, natDegree_zero]; omega
      · have hdeg : (g - h).degree < g.degree := degree_sub_lt
          (by rw [degree_eq_natDegree hgm.ne_zero, degree_eq_natDegree hhm.ne_zero, hgd, hhd])
          hgm.ne_zero (by rw [hgm.leadingCoeff, hhm.leadingCoeff])
        have := natDegree_lt_natDegree hne hdeg
        omega
  have := congrArg (fun q ↦ q.coeff i) hmap
  simp only [coeff_map, hzero, coeff_zero] at this
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).1 this

/-! ## Theorems 5.27 and 5.28 -/

/-- **Apostol, Theorem 5.27.** For pairwise coprime moduli `m_k` and units `a_k` mod `m_k`, the
system `a_k x ≡ b_k (mod m_k)` has exactly one solution modulo `∏ m_k`. -/
@[kb "apostol1976" "Thm 5.27, p. 118"]
theorem existsUnique_mul_cast_eq {ι : Type*} [Fintype ι] (m : ι → ℕ)
    (hm : Pairwise (Nat.Coprime on m)) (a b : (i : ι) → ZMod (m i)) (ha : ∀ i, IsUnit (a i)) :
    ∃! x : ZMod (∏ i, m i), ∀ i, a i * ZMod.castHom (dvd_prod_of_mem m (mem_univ i)) _ x = b i := by
  set e := ZMod.prodEquivPi m hm
  set y : (i : ι) → ZMod (m i) := fun i ↦ ((ha i).unit⁻¹ : (ZMod (m i))ˣ) * b i
  have hy : ∀ i, a i * y i = b i := fun i ↦ by
    simp only [y, ← mul_assoc]
    rw [(ha i).mul_val_inv, one_mul]
  have hcomp : ∀ x i, ZMod.castHom (dvd_prod_of_mem m (mem_univ i)) _ x = e x i := fun x i ↦
    (ZMod.prodEquivPi_apply m hm x i).symm
  refine ⟨e.symm y, fun i ↦ ?_, fun x hx ↦ ?_⟩
  · rw [hcomp, RingEquiv.apply_symm_apply, hy]
  · apply e.injective
    rw [RingEquiv.apply_symm_apply]
    funext i
    have h1 := hx i
    rw [hcomp, ← hy i] at h1
    exact (ha i).mul_left_cancel h1

/-- **Apostol, Theorem 5.28.** For pairwise coprime `m_i` and `f ∈ ℤ[x]`, the number of solutions
of `f(x) ≡ 0 (mod ∏ m_i)` is the product of the numbers of solutions of `f(x) ≡ 0 (mod m_i)`. -/
@[kb "apostol1976" "Thm 5.28, p. 118"]
theorem card_roots_prod_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (m : ι → ℕ)
    (hm : Pairwise (Nat.Coprime on m)) [∀ i, NeZero (m i)] [NeZero (∏ i, m i)] (f : ℤ[X]) :
    Fintype.card {x : ZMod (∏ i, m i) // f.eval₂ (Int.castRingHom _) x = 0} =
      ∏ i, Fintype.card {x : ZMod (m i) // f.eval₂ (Int.castRingHom _) x = 0} := by
  set e := ZMod.prodEquivPi m hm
  have heval : ∀ x i, e (f.eval₂ (Int.castRingHom _) x) i =
      f.eval₂ (Int.castRingHom _) (e x i) := by
    intro x i
    have := Polynomial.hom_eval₂ f (Int.castRingHom (ZMod (∏ i, m i)))
      ((Pi.evalRingHom (fun j ↦ ZMod (m j)) i).comp e.toRingHom) x
    simp only [RingHom.coe_comp, Function.comp_apply, Pi.evalRingHom_apply,
      RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom] at this
    rw [this]
    congr 1
    exact RingHom.ext_int _ _
  rw [← Fintype.card_pi]
  refine Fintype.card_congr ((e.toEquiv.subtypeEquiv (p := fun x ↦ f.eval₂ (Int.castRingHom _) x = 0)
    (q := fun y ↦ ∀ i, f.eval₂ (Int.castRingHom _) (y i) = 0) ?_).trans
    (Equiv.subtypePiEquivPi (p := fun i (z : ZMod (m i)) ↦ f.eval₂ (Int.castRingHom _) z = 0)))
  intro x
  constructor
  · intro hx i
    rw [RingEquiv.toEquiv_eq_coe, RingEquiv.coe_toEquiv, ← heval, hx, map_zero]; rfl
  · intro hx
    apply e.injective
    rw [map_zero]
    funext i
    rw [heval]
    exact hx i

end NTKB.Apostol
