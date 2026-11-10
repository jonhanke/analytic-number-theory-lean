/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.FieldTheory.Finite.Basic
import NTKB.Attr

/-!
# Residue systems and reciprocals (Apostol, §5.2–§5.4: Theorems 5.10, 5.11, 5.16; definitions)

* A *complete residue system* modulo `m` is a set of integers containing exactly one
  representative of each residue class (`IsCompleteResidueSystem`: reduction mod `m` is a
  bijection onto `ZMod m`); a *reduced residue system* contains exactly one representative of
  each class prime to `m` (`IsReducedResidueSystem`: a bijection onto the units).
* **Theorem 5.10**: `ā = b̄` iff `a ≡ b (mod m)`; `0, 1, …, m-1` form a complete residue system.
* **Theorem 5.11**: if `(k, m) = 1` and `{a_i}` is a complete residue system, so is `{k a_i}`.
* **Theorem 5.16**: the same for reduced residue systems.
* The *reciprocal* of `a` modulo `m` (`(a, m) = 1`): the unique solution `x` of `a x ≡ 1`
  (`reciprocalMod`).
* **Theorem 1.8**: if a prime `p` does not divide `a` then `(p, a) = 1`.
-/

namespace NTKB.Apostol

/-- A complete residue system modulo `m`. -/
def IsCompleteResidueSystem (m : ℕ) (s : Set ℤ) : Prop :=
  Set.BijOn (fun a : ℤ => (a : ZMod m)) s Set.univ

/-- A reduced residue system modulo `m`. -/
def IsReducedResidueSystem (m : ℕ) (s : Set ℤ) : Prop :=
  Set.BijOn (fun a : ℤ => (a : ZMod m)) s {x | IsUnit x}

/-- **Theorem 5.10** (a): `ā = b̄` iff `a ≡ b (mod m)`. -/
@[kb "apostol1976" "Thm 5.10, p. 109"]
theorem residueClass_eq_iff (m : ℕ) (a b : ℤ) : (a : ZMod m) = b ↔ a ≡ b [ZMOD m] :=
  ZMod.intCast_eq_intCast_iff a b m

/-- **Theorem 5.10** (b): `0, 1, …, m-1` form a complete residue system modulo `m ≥ 1`. -/
@[kb "apostol1976" "Thm 5.10, p. 109"]
theorem isCompleteResidueSystem_range {m : ℕ} (hm : 0 < m) :
    IsCompleteResidueSystem m {a : ℤ | 0 ≤ a ∧ a < m} := by
  refine ⟨fun _ _ => Set.mem_univ _, fun a ha b hb hab => ?_, fun x _ => ?_⟩
  · simp only at hab
    rw [ZMod.intCast_eq_intCast_iff'] at hab
    rwa [Int.emod_eq_of_lt ha.1 ha.2, Int.emod_eq_of_lt hb.1 hb.2] at hab
  · have : NeZero m := ⟨hm.ne'⟩
    refine ⟨(x.val : ℤ), ⟨by positivity, by exact_mod_cast ZMod.val_lt x⟩, ?_⟩
    simp

lemma bijOn_mul_unit {m : ℕ} {k : ℤ} (hk : IsUnit (k : ZMod m)) {s : Set ℤ} {t : Set (ZMod m)}
    (ht : ∀ x, x ∈ t ↔ (k : ZMod m) * x ∈ t)
    (hs : Set.BijOn (fun a : ℤ => (a : ZMod m)) s t) :
    Set.BijOn (fun a : ℤ => (a : ZMod m)) ((k * ·) '' s) t := by
  obtain ⟨u, hu⟩ := hk
  refine ⟨?_, ?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩
    simp only [Int.cast_mul]
    exact (ht _).mp (hs.mapsTo ha)
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hab
    simp only [Int.cast_mul] at hab
    rw [← hu] at hab
    have := hs.injOn ha hb ((Units.mul_right_inj u).mp hab)
    simp only [this]
  · intro y hy
    have hy' : ((u⁻¹ : (ZMod m)ˣ) : ZMod m) * y ∈ t := by
      rw [ht, ← hu, ← mul_assoc, Units.mul_inv, one_mul]; exact hy
    obtain ⟨a, ha, hay⟩ := hs.surjOn hy'
    refine ⟨k * a, ⟨a, ha, rfl⟩, ?_⟩
    simp only [Int.cast_mul] at hay ⊢
    rw [hay, ← hu, ← mul_assoc, Units.mul_inv, one_mul]

lemma isUnit_intCast_of_isCoprime' {m : ℕ} {k : ℤ} (hk : IsCoprime k m) :
    IsUnit (k : ZMod m) := by
  obtain ⟨u, v, huv⟩ := hk
  have : (u : ZMod m) * k = 1 := by
    have := congrArg (Int.cast : ℤ → ZMod m) huv
    push_cast at this
    rwa [ZMod.natCast_self, mul_zero, add_zero] at this
  exact IsUnit.of_mul_eq_one_right _ this

/-- **Theorem 5.11**. -/
@[kb "apostol1976" "Thm 5.11, p. 109"]
theorem IsCompleteResidueSystem.mul {m : ℕ} {s : Set ℤ} (hs : IsCompleteResidueSystem m s)
    {k : ℤ} (hk : IsCoprime k m) : IsCompleteResidueSystem m ((k * ·) '' s) :=
  bijOn_mul_unit (isUnit_intCast_of_isCoprime' hk) (fun _ => by simp) hs

/-- **Theorem 5.16**. -/
@[kb "apostol1976" "Thm 5.16, p. 113"]
theorem IsReducedResidueSystem.mul {m : ℕ} {s : Set ℤ} (hs : IsReducedResidueSystem m s)
    {k : ℤ} (hk : IsCoprime k m) : IsReducedResidueSystem m ((k * ·) '' s) := by
  have hku := isUnit_intCast_of_isCoprime' hk
  refine bijOn_mul_unit hku (fun x => ?_) hs
  simp only [Set.mem_ofPred_eq]
  exact (IsUnit.mul_iff.trans (and_iff_right hku)).symm

/-- The reciprocal of `a` modulo `m` for `(a, m) = 1`: the class `x` with `a x ≡ 1`. -/
noncomputable def reciprocalMod {m : ℕ} {a : ℤ} (ha : IsCoprime a m) : ZMod m :=
  ((isUnit_intCast_of_isCoprime' ha).unit⁻¹ : (ZMod m)ˣ)

/-- The reciprocal is the unique solution of `a x ≡ 1 (mod m)`. -/
@[kb "apostol1976" "§5.4 Definition (reciprocal), p. 110"]
theorem mul_reciprocalMod {m : ℕ} {a : ℤ} (ha : IsCoprime a m) :
    (a : ZMod m) * reciprocalMod ha = 1 ∧ ∀ x : ZMod m, (a : ZMod m) * x = 1 → x = reciprocalMod ha := by
  set h := isUnit_intCast_of_isCoprime' ha
  refine ⟨h.mul_val_inv, fun x hx => ?_⟩
  rw [reciprocalMod, ← one_mul x, ← h.val_inv_mul, mul_assoc, hx, mul_one]

/-- **Theorem 1.8**. -/
@[kb "apostol1976" "Thm 1.8, p. 19"]
theorem coprime_of_prime_not_dvd {p a : ℕ} (hp : p.Prime) (h : ¬ p ∣ a) : Nat.Coprime p a :=
  (Nat.Prime.coprime_iff_not_dvd hp).mpr h

end NTKB.Apostol
