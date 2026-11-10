/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.FieldTheory.Finite.Basic
import NTKB.Attr

/-!
# Counting quadratic residues (Apostol, Theorem 9.1)

**Theorem 9.1**: for an odd prime `p`, a reduced residue system mod `p` contains exactly
`(p-1)/2` quadratic residues and `(p-1)/2` nonresidues, and the residues are the classes of
`1², 2², …, ((p-1)/2)²` (which are distinct). Apostol's proof: `x² ≡ y²` with
`1 ≤ x, y ≤ (p-1)/2` forces `x = y` since `0 < x + y < p`; and `(p - k)² ≡ k²`.
-/

open Finset

namespace NTKB.Apostol

variable {p : ℕ} [hp : Fact p.Prime]

lemma sq_injOn_half :
    Set.InjOn (fun k : ℕ => ((k : ZMod p) ^ 2)) (Icc 1 ((p - 1) / 2) : Set ℕ) := by
  intro x hx y hy hxy
  simp only [coe_Icc, Set.mem_Icc] at hx hy
  simp only at hxy
  have hpos : (p : ℤ) ∣ ((x : ℤ) - y) * ((x : ℤ) + y) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    linear_combination hxy
  have hpr := Nat.prime_iff_prime_int.mp hp.out
  rcases hpr.dvd_or_dvd hpos with h | h
  · have hlt : |(x : ℤ) - y| < p := by
      rw [abs_lt]; constructor <;> omega
    have := Int.eq_zero_of_abs_lt_dvd h hlt
    omega
  · have hle : (x : ℤ) + y < p := by omega
    have h0 : 0 < (x : ℤ) + y := by omega
    exact absurd (Int.le_of_dvd h0 h) (not_le.mpr hle)

lemma image_sq_half (hp2 : p ≠ 2) :
    (Icc 1 ((p - 1) / 2)).image (fun k : ℕ => ((k : ZMod p) ^ 2)) =
      univ.filter fun x : ZMod p => x ≠ 0 ∧ IsSquare x := by
  ext x
  simp only [mem_image, mem_Icc, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨k, ⟨hk1, hk2⟩, rfl⟩
    refine ⟨?_, ⟨(k : ZMod p), sq _⟩⟩
    have hkp : (k : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      intro h; have := Nat.le_of_dvd (by omega) h; omega
    exact pow_ne_zero 2 hkp
  · rintro ⟨hx0, y, rfl⟩
    have hy0 : y ≠ 0 := by rintro rfl; simp at hx0
    have hp1 := hp.out.two_le
    have hodd : p % 2 = 1 := by
      rcases Nat.Prime.eq_two_or_odd hp.out with h | h
      · exact absurd h hp2
      · exact h
    set v := y.val
    have hv0 : v ≠ 0 := by rwa [Ne, ZMod.val_eq_zero]
    have hvp : v < p := ZMod.val_lt y
    have hyv : (v : ZMod p) = y := ZMod.natCast_zmod_val y
    by_cases hv : v ≤ (p - 1) / 2
    · exact ⟨v, ⟨by omega, hv⟩, by rw [hyv, sq]⟩
    · refine ⟨p - v, ⟨by omega, by omega⟩, ?_⟩
      rw [Nat.cast_sub hvp.le, ZMod.natCast_self, zero_sub, neg_sq, hyv, sq]

/-- **Theorem 9.1** (count of residues): there are exactly `(p-1)/2` nonzero squares mod `p`. -/
@[kb "apostol1976" "Thm 9.1, p. 179"]
theorem card_nonzero_squares (hp2 : p ≠ 2) :
    (univ.filter fun x : ZMod p => x ≠ 0 ∧ IsSquare x).card = (p - 1) / 2 := by
  rw [← image_sq_half hp2, card_image_of_injOn (sq_injOn_half), Nat.card_Icc]
  omega

/-- **Theorem 9.1** (count of nonresidues): there are exactly `(p-1)/2` nonzero non-squares. -/
@[kb "apostol1976" "Thm 9.1, p. 179"]
theorem card_nonsquares (hp2 : p ≠ 2) :
    (univ.filter fun x : ZMod p => x ≠ 0 ∧ ¬ IsSquare x).card = (p - 1) / 2 := by
  have htot : (univ.filter fun x : ZMod p => x ≠ 0).card = p - 1 := by
    rw [filter_ne', card_erase_of_mem (mem_univ _), card_univ, ZMod.card]
  have hsplit := card_filter_add_card_filter_not (s := univ.filter fun x : ZMod p => x ≠ 0)
    (fun x => IsSquare x)
  rw [filter_filter, filter_filter, htot, card_nonzero_squares hp2] at hsplit
  have hodd : p % 2 = 1 := by
    rcases Nat.Prime.eq_two_or_odd hp.out with h | h
    · exact absurd h hp2
    · exact h
  omega

/-- **Theorem 9.1** (representatives): the quadratic residues are the classes of
`1², 2², …, ((p-1)/2)²`, and these are distinct. -/
@[kb "apostol1976" "Thm 9.1, p. 179"]
theorem squares_eq_image_sq_half (hp2 : p ≠ 2) :
    Set.InjOn (fun k : ℕ => ((k : ZMod p) ^ 2)) (Icc 1 ((p - 1) / 2) : Set ℕ) ∧
      (Icc 1 ((p - 1) / 2)).image (fun k : ℕ => ((k : ZMod p) ^ 2)) =
        univ.filter fun x : ZMod p => x ≠ 0 ∧ IsSquare x :=
  ⟨sq_injOn_half, image_sq_half hp2⟩

end NTKB.Apostol
