/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.NumberTheory.MulChar.Lemmas
import Mathlib.RingTheory.ZMod.UnitsCyclic
import Mathlib.NumberTheory.DirichletCharacter.Basic
import NTKB.Attr

/-!
# Real characters modulo `p^a` (Apostol, Chapter 10, §10.9, Theorem 10.12)

**Theorem 10.12.** For an odd prime `p` and `a ≥ 1` there are exactly two real Dirichlet characters
modulo `p^a` (real-valued = `MulChar.IsQuadratic`).

Proof (Apostol's): `(ZMod p^a)ˣ` is cyclic with a generator `g` (a primitive root, Theorem 10.6;
Mathlib's `ZMod.isCyclic_units_of_prime_pow`); a character is determined by `χ(g)`, and it is real
iff `χ(g) = ±1`; both values occur since `φ(p^a)` is even.
-/

namespace NTKB.Apostol

/-- **Apostol, Theorem 10.12.** For an odd prime `p` and `a ≥ 1` there are exactly two real
characters modulo `p^a`. -/
@[kb "apostol1976" "Thm 10.12, p. 230"]
theorem card_isQuadratic_prime_pow {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {a : ℕ} (ha : a ≠ 0) :
    Nat.card {χ : DirichletCharacter ℂ (p ^ a) // χ.IsQuadratic} = 2 := by
  have : NeZero (p ^ a) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hcyc := ZMod.isCyclic_units_of_prime_pow p hp hp2 a
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  -- `φ(p^a)` is even, so `-1` is a `φ(p^a)`-th root of unity
  have h2 : 2 < p ^ a := by
    have : 3 ≤ p := by have := hp.two_le; omega
    calc 2 < 3 := by norm_num
      _ ≤ p := this
      _ ≤ p ^ a := Nat.le_self_pow ha p
  have heven : Even (Fintype.card (ZMod (p ^ a))ˣ) := by
    rw [ZMod.card_units_eq_totient]; exact Nat.totient_even h2
  have hroot : (-1 : ℂˣ) ∈ rootsOfUnity (Fintype.card (ZMod (p ^ a))ˣ) ℂ := by
    rw [mem_rootsOfUnity]; exact heven.neg_one_pow
  set χm : DirichletCharacter ℂ (p ^ a) := MulChar.ofRootOfUnity hroot hg
  have hχm : χm g = -1 := by
    simp [χm, MulChar.ofRootOfUnity_spec]
  have hval : ∀ χ : DirichletCharacter ℂ (p ^ a), χ.IsQuadratic ↔ χ g = 1 ∨ χ g = -1 := by
    intro χ
    rw [MulChar.isQuadratic_iff_sq_eq_one]
    constructor
    · intro h
      have := MulChar.pow_apply_coe χ 2 g
      rw [h, MulChar.one_apply_coe] at this
      exact sq_eq_one_iff.1 this.symm
    · intro h
      rw [MulChar.eq_iff hg, MulChar.pow_apply_coe, MulChar.one_apply_coe]
      rcases h with h | h <;> rw [h] <;> norm_num
  rw [Nat.card_eq_two_iff]
  refine ⟨⟨1, (hval 1).2 (Or.inl (MulChar.one_apply_coe g))⟩, ⟨χm, (hval χm).2 (Or.inr hχm)⟩,
    ?_, ?_⟩
  · intro h
    have := congrArg (fun χ : {χ : DirichletCharacter ℂ (p ^ a) // χ.IsQuadratic} ↦ χ.1 g) h
    simp only [MulChar.one_apply_coe, hχm] at this
    norm_num at this
  · ext ⟨χ, hχ⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true, Subtype.mk.injEq]
    rcases (hval χ).1 hχ with h | h
    · left; rw [MulChar.eq_iff hg, h, MulChar.one_apply_coe]
    · right; rw [MulChar.eq_iff hg, h, hχm]

end NTKB.Apostol
