/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.NumberTheory.LegendreSymbol.ZModChar
import Mathlib.RingTheory.ZMod.UnitsCyclic
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.Analysis.Complex.Basic
import NTKB.Attr

/-!
# Real characters modulo `2^a` (Apostol, Theorem 10.13)

**Theorem 10.13** (counting part): for `a ≥ 3` there are exactly four real Dirichlet characters
modulo `2^a` (real-valued = `MulChar.IsQuadratic`).

Apostol uses the explicit characters `χ_{α,c}(n) = f(n)^α g(n)^c` built on Theorem 10.11
(every odd `n` is `±5^b` mod `2^a`, Mathlib's `ZMod.isComplement'_zpowers_unitFive_neg_one`).
Same structure here: a character mod `2^a` is determined by `χ(-1)` and `χ(5)` (they generate
the units), which are `±1` for a real character; and all four sign patterns occur, realized by
the principal character and the characters mod 4 and mod 8 (`χ₄`, `χ₈`, `χ₈'`) lifted to `2^a`.
-/

open ZMod

namespace NTKB.Apostol

theorem isQuadratic_changeLevel {n m : ℕ} (hm : n ∣ m) {χ : DirichletCharacter ℂ n}
    (hχ : χ.IsQuadratic) : (DirichletCharacter.changeLevel hm χ).IsQuadratic := by
  intro a
  by_cases ha : IsUnit a
  · obtain ⟨u, rfl⟩ := ha
    rw [DirichletCharacter.changeLevel_eq_cast_of_dvd]
    exact hχ _
  · exact Or.inl (MulChar.map_nonunit _ ha)

/-- A character mod `2^a` is determined by its values at `-1` and `5`. -/
theorem eq_of_apply_neg_one_of_apply_five {a : ℕ} {χ ψ : DirichletCharacter ℂ (2 ^ a)}
    (h1 : χ (-1) = ψ (-1)) (h5 : χ 5 = ψ 5) : χ = ψ := by
  rw [← DirichletCharacter.toUnitHom_inj]
  have hcl : Subgroup.closure ({unitFive, -1} : Set (ZMod (2 ^ a))ˣ) = ⊤ := by
    rw [Set.insert_eq, Subgroup.closure_union, ← Subgroup.zpowers_eq_closure,
      ← Subgroup.zpowers_eq_closure]
    exact (isComplement'_zpowers_unitFive_neg_one a).sup_eq_top
  refine MonoidHom.eq_of_eqOn_dense hcl ?_
  intro u hu
  rcases hu with rfl | rfl
  · apply Units.ext
    simp only [MulChar.coe_toUnitHom, coe_unitFive]
    exact h5
  · apply Units.ext
    simp only [MulChar.coe_toUnitHom, Units.val_neg, Units.val_one]
    exact h1

theorem apply_eq_one_or_neg_one {m : ℕ} {χ : DirichletCharacter ℂ m} (hχ : χ.IsQuadratic)
    {x : ZMod m} (hx : IsUnit x) : χ x = 1 ∨ χ x = -1 := by
  rcases hχ x with h | h
  · exact absurd h (MulChar.apply_ne_zero_iff.2 hx)
  · exact h

theorem eq_of_decide_eq {x y : ℂ} (hx : x = 1 ∨ x = -1) (hy : y = 1 ∨ y = -1)
    (h : decide (x = 1) = decide (y = 1)) : x = y := by
  have h1 : (-1 : ℂ) ≠ 1 := by norm_num
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> simp_all

theorem isUnit_five_two_pow (a : ℕ) : IsUnit (5 : ZMod (2 ^ a)) := by
  rw [← coe_unitFive]; exact Units.isUnit _

/-- The values of a character mod `2^a` lifted from level `n ∣ 2^a`, at `-1` and `5`. -/
theorem changeLevel_apply_neg_one {n a : ℕ} (hn : n ∣ 2 ^ a) (χ : DirichletCharacter ℂ n) :
    DirichletCharacter.changeLevel hn χ (-1) = χ (-1) := by
  have := DirichletCharacter.changeLevel_eq_cast_of_dvd' χ hn (a := -1) isCoprime_one_left.neg_left
  simpa using this

theorem changeLevel_apply_five {n a : ℕ} (hn : n ∣ 2 ^ a) (χ : DirichletCharacter ℂ n) :
    DirichletCharacter.changeLevel hn χ 5 = χ 5 := by
  have hc : IsCoprime (5 : ℤ) ((2 ^ a : ℕ) : ℤ) := by
    have := Nat.isCoprime_iff_coprime.2 (Nat.Coprime.pow_right a (by norm_num : Nat.Coprime 5 2))
    simpa using this
  have := DirichletCharacter.changeLevel_eq_cast_of_dvd' χ hn hc
  simpa using this

/-- **Apostol, Theorem 10.13** (counting part): for `a ≥ 3` there are exactly four real
characters modulo `2^a`. -/
@[kb "apostol1976" "Thm 10.13, p. 220"]
theorem card_isQuadratic_two_pow {a : ℕ} (ha : 3 ≤ a) :
    Nat.card {χ : DirichletCharacter ℂ (2 ^ a) // χ.IsQuadratic} = 4 := by
  set Φ : {χ : DirichletCharacter ℂ (2 ^ a) // χ.IsQuadratic} → Bool × Bool :=
    fun χ ↦ (decide (χ.1 (-1) = 1), decide (χ.1 5 = 1))
  have hinj : Function.Injective Φ := by
    rintro ⟨χ, hχ⟩ ⟨ψ, hψ⟩ h
    simp only [Φ, Prod.mk.injEq] at h
    apply Subtype.ext
    exact eq_of_apply_neg_one_of_apply_five
      (eq_of_decide_eq (apply_eq_one_or_neg_one hχ isUnit_one.neg)
        (apply_eq_one_or_neg_one hψ isUnit_one.neg) h.1)
      (eq_of_decide_eq (apply_eq_one_or_neg_one hχ (isUnit_five_two_pow a))
        (apply_eq_one_or_neg_one hψ (isUnit_five_two_pow a)) h.2)
  have h4 : 4 ∣ 2 ^ a := by
    have := Nat.pow_dvd_pow 2 (by omega : 2 ≤ a); norm_num at this; exact this
  have h8 : 8 ∣ 2 ^ a := by
    have := Nat.pow_dvd_pow 2 (by omega : 3 ≤ a); norm_num at this; exact this
  set c4 : DirichletCharacter ℂ 4 := ZMod.χ₄.ringHomComp (Int.castRingHom ℂ)
  set c8 : DirichletCharacter ℂ 8 := ZMod.χ₈.ringHomComp (Int.castRingHom ℂ)
  set c8' : DirichletCharacter ℂ 8 := ZMod.χ₈'.ringHomComp (Int.castRingHom ℂ)
  have hm1 : (-1 : ℂ) ≠ 1 := by norm_num
  have hsurj : Function.Surjective Φ := by
    rintro ⟨b1, b2⟩
    cases b1 <;> cases b2
    · refine ⟨⟨DirichletCharacter.changeLevel h8 c8',
        isQuadratic_changeLevel h8 (ZMod.isQuadratic_χ₈'.comp _)⟩, ?_⟩
      simp only [Φ, changeLevel_apply_neg_one, changeLevel_apply_five, c8',
        MulChar.ringHomComp_apply]
      have e1 : ZMod.χ₈' (-1) = -1 := by decide
      have e5 : ZMod.χ₈' 5 = -1 := by decide
      simp [e1, e5, hm1]
    · refine ⟨⟨DirichletCharacter.changeLevel h4 c4,
        isQuadratic_changeLevel h4 (ZMod.isQuadratic_χ₄.comp _)⟩, ?_⟩
      simp only [Φ, changeLevel_apply_neg_one, changeLevel_apply_five, c4,
        MulChar.ringHomComp_apply]
      have e1 : ZMod.χ₄ (-1) = -1 := by decide
      have e5 : ZMod.χ₄ 5 = 1 := by decide
      simp [e1, e5, hm1]
    · refine ⟨⟨DirichletCharacter.changeLevel h8 c8,
        isQuadratic_changeLevel h8 (ZMod.isQuadratic_χ₈.comp _)⟩, ?_⟩
      simp only [Φ, changeLevel_apply_neg_one, changeLevel_apply_five, c8,
        MulChar.ringHomComp_apply]
      have e1 : ZMod.χ₈ (-1) = 1 := by decide
      have e5 : ZMod.χ₈ 5 = -1 := by decide
      simp [e1, e5, hm1]
    · refine ⟨⟨1, fun x ↦ ?_⟩, ?_⟩
      · by_cases hx : IsUnit x
        · exact Or.inr (Or.inl (MulChar.one_apply hx))
        · exact Or.inl (MulChar.map_nonunit _ hx)
      · simp [Φ, MulChar.one_apply isUnit_one.neg, MulChar.one_apply (isUnit_five_two_pow a)]
  rw [Nat.card_eq_of_bijective Φ ⟨hinj, hsurj⟩]
  simp

end NTKB.Apostol
