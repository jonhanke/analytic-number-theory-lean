/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.Data.ZMod.Units
import Mathlib.GroupTheory.Index
import Mathlib.Data.Nat.Totient
import NTKB.Attr

/-!
# Reduced residues in a residue class (Apostol, Chapter 5, Theorems 5.32 and 5.33)

**Theorem 5.32.** If `d ∣ k`, `d > 0`, `k ≥ 1` and `(r, d) = 1`, then exactly `φ(k)/φ(d)` of the
numbers `r + td`, `t = 1, …, k/d`, are prime to `k`.

**Theorem 5.33 (b)**, in counting form: the reduced residues mod `k` that are `≡ r (mod d)` are
`φ(k)/φ(d)` in number, for each of the `φ(d)` reduced classes `r` mod `d`.

Apostol proves 5.32 by inclusion–exclusion and remarks that a group-theoretic proof exists; we
use the latter: the reduction map `(ZMod k)ˣ → (ZMod d)ˣ` is surjective (Mathlib's
`ZMod.unitsMap_surjective`), so all its fibres have `φ(k)/φ(d)` elements; the numbers `r + td`,
`1 ≤ t ≤ k/d`, run through the residue class `r` mod `d` modulo `k`.
-/

open Finset

namespace NTKB.Apostol

variable {d k : ℕ}

/-- Every fibre of `(ZMod k)ˣ → (ZMod d)ˣ` has `φ(k)/φ(d)` elements: `#fibre · φ(d) = φ(k)`. -/
theorem card_fiber_unitsMap_mul [NeZero k] (hdk : d ∣ k) (u : (ZMod d)ˣ) :
    #{v : (ZMod k)ˣ | ZMod.unitsMap hdk v = u} * d.totient = k.totient := by
  classical
  have hd : NeZero d := ⟨fun h ↦ NeZero.ne k (Nat.eq_zero_of_zero_dvd (h ▸ hdk))⟩
  have hsurj := ZMod.unitsMap_surjective (n := d) (m := k) hdk
  have hcount := card_eq_sum_card_fiberwise (f := ZMod.unitsMap hdk)
    (s := (univ : Finset (ZMod k)ˣ)) (t := univ) (fun _ _ ↦ mem_univ _)
  rw [card_univ, ZMod.card_units_eq_totient] at hcount
  rw [hcount]
  have hall : ∀ w ∈ (univ : Finset (ZMod d)ˣ),
      #{v ∈ (univ : Finset (ZMod k)ˣ) | ZMod.unitsMap hdk v = w} =
        #{v : (ZMod k)ˣ | ZMod.unitsMap hdk v = u} := fun w _ ↦
    MonoidHom.card_fiber_eq_of_mem_range _ (hsurj w) (hsurj u)
  rw [sum_congr rfl hall, sum_const, card_univ, ZMod.card_units_eq_totient, smul_eq_mul, mul_comm]

/-- **Apostol, Theorem 5.33 (b)**, counting form: for `d ∣ k` and a unit `u` mod `d`, the reduced
residues `v` mod `k` with `v ≡ u (mod d)` are `φ(k)/φ(d)` in number. -/
@[kb "apostol1976" "Thm 5.33, p. 125"]
theorem card_fiber_unitsMap [NeZero k] (hdk : d ∣ k) (u : (ZMod d)ˣ) :
    #{v : (ZMod k)ˣ | ZMod.unitsMap hdk v = u} = k.totient / d.totient := by
  have hd : 0 < d := Nat.pos_of_ne_zero fun h ↦ NeZero.ne k (Nat.eq_zero_of_zero_dvd (h ▸ hdk))
  rw [← card_fiber_unitsMap_mul hdk u, Nat.mul_div_cancel _ (Nat.totient_pos.2 hd)]

/-- The residue class `r` mod `d` inside `ZMod k` has `k/d` elements. -/
theorem card_fiber_castHom [NeZero k] (hdk : d ∣ k) (r : ZMod d) :
    #{x : ZMod k | ZMod.castHom hdk (ZMod d) x = r} * d = k := by
  classical
  have hd : NeZero d := ⟨fun h ↦ NeZero.ne k (Nat.eq_zero_of_zero_dvd (h ▸ hdk))⟩
  set f : ZMod k →+ ZMod d := (ZMod.castHom hdk (ZMod d)).toAddMonoidHom
  have hsurj : Function.Surjective f := ZMod.ringHom_surjective _
  have hcount := card_eq_sum_card_fiberwise (f := f) (s := (univ : Finset (ZMod k))) (t := univ)
    (fun _ _ ↦ mem_univ _)
  rw [card_univ, ZMod.card] at hcount
  have hall : ∀ w ∈ (univ : Finset (ZMod d)),
      #{x ∈ (univ : Finset (ZMod k)) | f x = w} = #{x : ZMod k | f x = r} := fun w _ ↦
    AddMonoidHom.card_fiber_eq_of_mem_range f (hsurj w) (hsurj r)
  have h2 : #{x : ZMod k | f x = r} * d = ∑ b : ZMod d, #{x ∈ (univ : Finset (ZMod k)) | f x = b} := by
    rw [sum_congr rfl hall, sum_const, card_univ, ZMod.card, smul_eq_mul, mul_comm]
  exact h2.trans hcount.symm

/-- **Apostol, Theorem 5.32.** If `d ∣ k`, `d > 0`, `k ≥ 1` and `(r, d) = 1`, the number of
`t ∈ {1, …, k/d}` with `(r + td, k) = 1` is `φ(k)/φ(d)`. -/
@[kb "apostol1976" "Thm 5.32, p. 124"]
theorem card_coprime_add_mul (hk : 0 < k) (hdk : d ∣ k) {r : ℕ} (hrd : r.Coprime d) :
    #{t ∈ Icc 1 (k / d) | (r + t * d).Coprime k} = k.totient / d.totient := by
  classical
  have : NeZero k := ⟨hk.ne'⟩
  have hd : 0 < d := Nat.pos_of_ne_zero fun h ↦ hk.ne' (Nat.eq_zero_of_zero_dvd (h ▸ hdk))
  set q := k / d with hq
  have hkq : k = q * d := (Nat.div_mul_cancel hdk).symm
  set f : ℕ → ZMod k := fun t ↦ ((r + t * d : ℕ) : ZMod k)
  -- (A) the numbers `r + td` lie in the class `r` mod `d`
  have hA : ∀ t, ZMod.castHom hdk (ZMod d) (f t) = (r : ZMod d) := fun t ↦ by
    show ZMod.castHom hdk (ZMod d) ((r + t * d : ℕ) : ZMod k) = _
    rw [map_natCast]; push_cast; rw [ZMod.natCast_self, mul_zero, add_zero]
  -- (B) they are distinct mod `k`
  have hB : Set.InjOn f (Icc 1 q) := by
    intro t ht s hs hts
    simp only [coe_Icc, Set.mem_Icc] at ht hs
    have h1 : r + t * d ≡ r + s * d [MOD k] := (ZMod.natCast_eq_natCast_iff' _ _ _).1 hts
    have h2 : t * d ≡ s * d [MOD q * d] := hkq ▸ Nat.ModEq.add_left_cancel' r h1
    have h3 : t ≡ s [MOD q] := Nat.ModEq.mul_right_cancel' hd.ne' h2
    have h4 : t - 1 ≡ s - 1 [MOD q] := by
      have : t - 1 + 1 ≡ s - 1 + 1 [MOD q] := by rwa [Nat.sub_add_cancel ht.1, Nat.sub_add_cancel hs.1]
      exact Nat.ModEq.add_right_cancel' 1 this
    have := Nat.ModEq.eq_of_lt_of_lt h4 (by omega) (by omega)
    omega
  -- (C)–(D) they fill the class
  have hC : #{x : ZMod k | ZMod.castHom hdk (ZMod d) x = r} = q := by
    have := card_fiber_castHom hdk (r : ZMod d)
    rw [hq]; exact (Nat.div_eq_of_eq_mul_left hd this.symm).symm
  have hD : (Icc 1 q).image f =
      ({x : ZMod k | ZMod.castHom hdk (ZMod d) x = r} : Finset (ZMod k)) := by
    refine eq_of_subset_of_card_le (fun x hx ↦ ?_) ?_
    · obtain ⟨t, -, rfl⟩ := mem_image.1 hx
      rw [mem_filter]; exact ⟨mem_univ _, hA t⟩
    · rw [card_image_of_injOn hB, hC, Nat.card_Icc]; omega
  -- (E) coprime ↔ unit
  have hE : #{t ∈ Icc 1 q | (r + t * d).Coprime k} =
      #{x : ZMod k | ZMod.castHom hdk (ZMod d) x = r ∧ IsUnit x} := by
    have : ({x : ZMod k | ZMod.castHom hdk (ZMod d) x = r ∧ IsUnit x} : Finset (ZMod k)) =
        ((Icc 1 q).image f).filter IsUnit := by
      rw [hD, filter_filter]
    rw [this, filter_image, card_image_of_injOn (hB.mono (by
      intro x hx; simp only [coe_filter, Set.mem_setOf_eq] at hx; simpa using hx.1))]
    congr 1
    ext t
    simp only [mem_filter, Function.comp_apply, f, ZMod.isUnit_iff_coprime]
  -- (F) units in the class
  have hF : #{x : ZMod k | ZMod.castHom hdk (ZMod d) x = r ∧ IsUnit x} =
      #{v : (ZMod k)ˣ | ZMod.unitsMap hdk v = ZMod.unitOfCoprime r hrd} := by
    refine (card_bij (fun (v : (ZMod k)ˣ) _ ↦ (v : ZMod k)) ?_ ?_ ?_).symm
    · intro v hv
      simp only [mem_filter, mem_univ, true_and] at hv ⊢
      refine ⟨?_, v.isUnit⟩
      have := congrArg Units.val hv
      simpa [ZMod.unitsMap_def] using this
    · intro v _ w _ h; exact Units.ext h
    · intro x hx
      simp only [mem_filter, mem_univ, true_and] at hx
      refine ⟨hx.2.unit, ?_, rfl⟩
      simp only [mem_filter, mem_univ, true_and]
      ext
      simpa [ZMod.unitsMap_def] using hx.1
  rw [hE, hF, card_fiber_unitsMap hdk]

end NTKB.Apostol
