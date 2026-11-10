/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.Analysis.Complex.Basic
import NTKB.Attr

/-!
# Induced moduli (Apostol, Theorem 8.16)

Apostol calls `d ∣ k` an *induced modulus* for a character `χ` mod `k` if `χ(a) = 1` whenever
`(a, k) = 1` and `a ≡ 1 (mod d)`; this is Mathlib's `DirichletCharacter.FactorsThrough χ d`
(`χ` is induced from a character mod `d`; Mathlib's `factorsThrough_iff_ker_unitsMap` is the
kernel form). **Theorem 8.16**: `d` is an induced modulus iff `χ(a) = χ(b)` whenever
`(a, k) = (b, k) = 1` and `a ≡ b (mod d)`.
-/

namespace NTKB.Apostol

/-- **Theorem 8.16**. -/
@[kb "apostol1976" "Thm 8.16, p. 171"]
theorem factorsThrough_iff_apply_eq {k : ℕ} [NeZero k] (χ : DirichletCharacter ℂ k) {d : ℕ}
    (hd : d ∣ k) :
    χ.FactorsThrough d ↔ ∀ a b : ℤ, IsCoprime a k → IsCoprime b k → a ≡ b [ZMOD d] →
      χ a = χ b := by
  constructor
  · rintro ⟨-, χ₀, rfl⟩ a b ha hb hab
    rw [DirichletCharacter.changeLevel_eq_cast_of_dvd' χ₀ hd ha,
      DirichletCharacter.changeLevel_eq_cast_of_dvd' χ₀ hd hb,
      (ZMod.intCast_eq_intCast_iff a b d).mpr hab]
  · intro h
    rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap hd]
    intro u hu
    rw [MonoidHom.mem_ker] at hu ⊢
    set a : ℤ := ((u : ZMod k).val : ℤ)
    have hak : IsCoprime a k := by
      have := ZMod.val_coe_unit_coprime u
      exact Nat.isCoprime_iff_coprime.mpr this
    have hau : (a : ZMod k) = u := by
      simp only [a, Int.cast_natCast, ZMod.natCast_zmod_val]
    have had : a ≡ 1 [ZMOD d] := by
      rw [← ZMod.intCast_eq_intCast_iff, Int.cast_one]
      have e : ((a : ℤ) : ZMod d) = ((u : ZMod k).cast : ZMod d) := by
        simp only [a]; rw [Int.cast_natCast, ZMod.natCast_val]
      rw [e, ← ZMod.unitsMap_val hd u, hu, Units.val_one]
    have := h a 1 hak isCoprime_one_left had
    rw [hau, Int.cast_one, MulChar.map_one] at this
    exact Units.ext (by simpa using this)

end NTKB.Apostol
