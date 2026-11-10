/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Apostol.PrimitiveRoots.RealCharactersTwoPow
import NTKB.Analytic.Apostol.PrimitiveRoots.PrimitiveCharacters
import NTKB.Analytic.Davenport.Ch1to6.Periods
import NTKB.Elementary.SpecialValues.FundamentalGaussSum

/-!
# Davenport, Chapter 5: real primitive characters to prime-power moduli

(§5, pp. 37–38.) The only prime powers to which there is a real primitive character are
* `p` (odd prime), with the character `(n/p)`;
* `4`, with `χ_4`;
* `8`, with `χ_8` and `χ_4 χ_8`.

For an odd prime `p` and `a ≥ 2`, a real character modulo `p^a` is trivial on the units
`≡ 1 (mod p)` (they form a group of odd order `p^{a-1}`), so it is induced modulo `p`; modulo `p`
the only real nonprincipal character is Legendre's symbol. For `2^a` a real character is determined
by its values at `-1` and `5`, so it is one of the four characters `1, χ_4, χ_8, χ_4 χ_8` lifted
from modulus `8` (Apostol's results in `NTKB.Apostol`), which are imprimitive modulo `2^a` for
`a ≥ 4`.
-/

noncomputable section

open DirichletCharacter

namespace NTKB.Davenport

/-! ### Odd prime powers -/

/-- For an odd prime `p` and `a ≥ 2`, a real character modulo `p^a` factors through `p`. -/
theorem factorsThrough_prime_of_isQuadratic {p a : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (ha : 1 ≤ a)
    {χ : DirichletCharacter ℂ (p ^ a)} (hχ : χ.IsQuadratic) : χ.FactorsThrough p := by
  have : NeZero (p ^ a) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have hd : p ∣ p ^ a := dvd_pow_self p (by omega)
  rw [factorsThrough_iff_ker_unitsMap hd]
  set K := (ZMod.unitsMap hd).ker
  -- `|K| = p^(a-1)`
  have hcardK : Nat.card K = p ^ (a - 1) := by
    have h1 := K.card_mul_index
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr (ZMod.unitsMap_surjective hd),
      Subgroup.card_top] at h1
    simp only [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient] at h1
    rw [Nat.totient_prime_pow hp (by omega), Nat.totient_prime hp] at h1
    rw [Nat.card_eq_fintype_card]
    have hp1 : 0 < p - 1 := by have := hp.two_le; omega
    exact Nat.eq_of_mul_eq_mul_right hp1 h1
  have hodd : Odd (p ^ (a - 1)) := (hp.odd_of_ne_two hp2).pow
  intro u hu
  have hpow : u ^ p ^ (a - 1) = 1 := by
    have := pow_card_eq_one' (x := (⟨u, hu⟩ : K))
    rw [hcardK] at this
    exact congrArg Subtype.val this
  rw [MonoidHom.mem_ker]
  apply Units.ext
  simp only [MulChar.coe_toUnitHom, Units.val_one]
  have hval := NTKB.Apostol.apply_eq_one_or_neg_one hχ u.isUnit
  have h1 : χ u ^ p ^ (a - 1) = 1 := by
    rw [← map_pow, ← Units.val_pow_eq_pow_val, hpow, Units.val_one, map_one]
  rcases hval with h | h
  · exact h
  · rw [h, hodd.neg_one_pow] at h1; norm_num at h1

/-- **Davenport §5, p. 37.** For an odd prime `p`, a real primitive character modulo `p^a`
(`a ≥ 1`) has `a = 1`. -/
@[kb "davenport1980" "Ch 5, p. 37"]
theorem eq_one_of_isPrimitive_of_isQuadratic_odd {p a : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (ha : 1 ≤ a) {χ : DirichletCharacter ℂ (p ^ a)} (hχ : χ.IsQuadratic) (hprim : χ.IsPrimitive) :
    a = 1 := by
  have : NeZero (p ^ a) := ⟨pow_ne_zero _ hp.ne_zero⟩
  by_contra h
  have hf := factorsThrough_prime_of_isQuadratic hp hp2 ha hχ
  rw [NTKB.Apostol.isPrimitive_iff_not_factorsThrough hp ha] at hprim
  exact hprim (FactorsThrough.mono χ hf (dvd_pow_self p (show a - 1 ≠ 0 by omega))
    (pow_dvd_pow p (by omega)))

/-- **Davenport §5, p. 38.** For an odd prime `p`, the only real nonprincipal character modulo `p`
is Legendre's symbol. -/
@[kb "davenport1980" "Ch 5, p. 38"]
theorem eq_legendreChar_of_isQuadratic {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {χ : DirichletCharacter ℂ p} (hχ : χ.IsQuadratic) (h1 : χ ≠ 1) : χ = legendreChar p := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  have hval := NTKB.Apostol.apply_eq_one_or_neg_one hχ g.isUnit
  have hg1 : χ g = -1 := by
    rcases hval with h | h
    · exfalso; apply h1
      refine MulChar.ext fun u ↦ ?_
      rw [MulChar.one_apply u.isUnit, ← pow_index hg u, Units.val_pow_eq_pow_val, map_pow, h,
        one_pow]
    · exact h
  refine MulChar.ext fun u ↦ ?_
  rw [legendreChar_apply, quadraticChar_eq_neg_one_pow_index hg hp2 u]
  conv_lhs => rw [← pow_index hg u]
  rw [Units.val_pow_eq_pow_val, map_pow, hg1]
  push_cast
  rfl

/-! ### Powers of `2` -/

theorem chi4_neg_one : chi4 (-1) = -1 := by
  have : ZMod.χ₄ (-1 : ZMod 4) = -1 := by decide
  simp [chi4, MulChar.ringHomComp_apply, this]

theorem chi4_five : chi4 (5 : ZMod 4) = 1 := by
  have : (5 : ZMod 4) = 1 := by decide
  rw [this, map_one]

theorem chi8_neg_one : chi8 (-1) = 1 := by
  have : ZMod.χ₈ (-1 : ZMod 8) = 1 := by decide
  simp [chi8, MulChar.ringHomComp_apply, this]

theorem chi8_five : chi8 (5 : ZMod 8) = -1 := by
  have : ZMod.χ₈ (5 : ZMod 8) = -1 := by decide
  simp [chi8, MulChar.ringHomComp_apply, this]

theorem chi8'_neg_one : chi8' (-1) = -1 := by
  have : ZMod.χ₈' (-1 : ZMod 8) = -1 := by decide
  simp [chi8', MulChar.ringHomComp_apply, this]

theorem chi8'_five : chi8' (5 : ZMod 8) = -1 := by
  have : ZMod.χ₈' (5 : ZMod 8) = -1 := by decide
  simp [chi8', MulChar.ringHomComp_apply, this]

/-- A real character modulo `2^a` (`a ≥ 3`) is induced from one of `1, χ_4, χ_8, χ_8'` modulo `8`;
in particular it factors through `8`. -/
theorem factorsThrough_eight_of_isQuadratic {a : ℕ} (ha : 3 ≤ a)
    {χ : DirichletCharacter ℂ (2 ^ a)} (hχ : χ.IsQuadratic) : χ.FactorsThrough 8 := by
  have h8 : 8 ∣ 2 ^ a := by
    rw [show 8 = 2 ^ 3 by norm_num]; exact pow_dvd_pow 2 ha
  have h4 : 4 ∣ 2 ^ a := (show 4 ∣ 8 by norm_num).trans h8
  have hm1 := NTKB.Apostol.apply_eq_one_or_neg_one hχ isUnit_one.neg
  have hm5 := NTKB.Apostol.apply_eq_one_or_neg_one hχ (NTKB.Apostol.isUnit_five_two_pow a)
  have key : ∀ ψ : DirichletCharacter ℂ 8, χ (-1) = ψ (-1) → χ 5 = ψ 5 → χ.FactorsThrough 8 := by
    intro ψ h1 h5
    have : χ = changeLevel h8 ψ := NTKB.Apostol.eq_of_apply_neg_one_of_apply_five
      (by rw [NTKB.Apostol.changeLevel_apply_neg_one]; exact h1)
      (by rw [NTKB.Apostol.changeLevel_apply_five]; exact h5)
    rw [this]; exact changeLevel_factorsThrough _ _
  have h48 : (4 : ℕ) ∣ 8 := by norm_num
  rcases hm1 with h1 | h1 <;> rcases hm5 with h5 | h5
  · exact key 1 (by rw [h1, MulChar.one_apply isUnit_one.neg])
      (by rw [h5, MulChar.one_apply (by decide)])
  · exact key chi8 (by rw [h1, chi8_neg_one]) (by rw [h5, chi8_five])
  · refine key (changeLevel h48 chi4) ?_ ?_
    · rw [h1, NTKB.Apostol.changeLevel_apply_neg_one (a := 3) h48, chi4_neg_one]
    · rw [h5, NTKB.Apostol.changeLevel_apply_five (a := 3) h48, chi4_five]
  · exact key chi8' (by rw [h1, chi8'_neg_one]) (by rw [h5, chi8'_five])

/-- **Davenport §5, p. 38.** A real primitive character modulo `2^a` (`a ≥ 1`) exists only for
`a = 2` and `a = 3`. -/
@[kb "davenport1980" "Ch 5, p. 38"]
theorem two_or_three_of_isPrimitive_of_isQuadratic_two_pow {a : ℕ} (ha : 1 ≤ a)
    {χ : DirichletCharacter ℂ (2 ^ a)} (hχ : χ.IsQuadratic) (hprim : χ.IsPrimitive) :
    a = 2 ∨ a = 3 := by
  have : NeZero (2 ^ a) := ⟨pow_ne_zero _ two_ne_zero⟩
  by_contra h
  rcases (show a = 1 ∨ 4 ≤ a by omega) with rfl | ha4
  · -- modulus 2: only the principal character
    have h1 : χ = 1 := NTKB.Apostol.eq_of_apply_neg_one_of_apply_five
      (by rw [MulChar.one_apply isUnit_one.neg]
          have : (-1 : ZMod (2 ^ 1)) = 1 := by decide
          rw [this, map_one])
      (by rw [MulChar.one_apply (NTKB.Apostol.isUnit_five_two_pow 1)]
          have : (5 : ZMod (2 ^ 1)) = 1 := by decide
          rw [this, map_one])
    rw [isPrimitive_def, h1, conductor_one] at hprim
    norm_num at hprim
  · have hf := factorsThrough_eight_of_isQuadratic (by omega) hχ
    rw [NTKB.Apostol.isPrimitive_iff_not_factorsThrough Nat.prime_two ha] at hprim
    exact hprim (FactorsThrough.mono χ hf (by
      rw [show 8 = 2 ^ 3 by norm_num]; exact pow_dvd_pow 2 (by omega))
      (pow_dvd_pow 2 (by omega)))

/-- **Davenport §5, p. 38.** The only real primitive character modulo `4` is `χ_4`. -/
@[kb "davenport1980" "Ch 5, p. 38"]
theorem eq_chi4_of_isPrimitive {χ : DirichletCharacter ℂ 4} (hχ : χ.IsQuadratic)
    (hprim : χ.IsPrimitive) : χ = chi4 := by
  have hm1 := NTKB.Apostol.apply_eq_one_or_neg_one hχ isUnit_one.neg
  refine NTKB.Apostol.eq_of_apply_neg_one_of_apply_five (a := 2) ?_ ?_
  · rcases hm1 with h | h
    · exfalso
      have h1 : χ = 1 := NTKB.Apostol.eq_of_apply_neg_one_of_apply_five (a := 2)
        (by rw [h, MulChar.one_apply isUnit_one.neg])
        (by rw [MulChar.one_apply (NTKB.Apostol.isUnit_five_two_pow 2)]
            have : (5 : ZMod (2 ^ 2)) = 1 := by decide
            rw [this, map_one])
      rw [isPrimitive_def, h1, conductor_one] at hprim
      norm_num at hprim
    · rw [h]; exact chi4_neg_one.symm
  · have : (5 : ZMod (2 ^ 2)) = 1 := by decide
    rw [this, map_one, map_one]

/-- **Davenport §5, p. 38.** The only real primitive characters modulo `8` are `χ_8` and
`χ_4 χ_8 = χ_8'`. -/
@[kb "davenport1980" "Ch 5, p. 38"]
theorem eq_chi8_or_eq_chi8'_of_isPrimitive {χ : DirichletCharacter ℂ 8} (hχ : χ.IsQuadratic)
    (hprim : χ.IsPrimitive) : χ = chi8 ∨ χ = chi8' := by
  have hm1 := NTKB.Apostol.apply_eq_one_or_neg_one hχ isUnit_one.neg
  have hm5 := NTKB.Apostol.apply_eq_one_or_neg_one hχ (NTKB.Apostol.isUnit_five_two_pow 3)
  have h48 : (4 : ℕ) ∣ 8 := by norm_num
  -- the characters `1` and `χ_4` lifted are imprimitive modulo `8`
  have himp : ∀ ψ : DirichletCharacter ℂ 4, χ = changeLevel h48 ψ → False := by
    intro ψ h
    rw [NTKB.Apostol.isPrimitive_iff_not_factorsThrough (a := 3) Nat.prime_two (by norm_num)] at hprim
    exact hprim (by rw [h]; exact changeLevel_factorsThrough _ _)
  rcases hm1 with h1 | h1 <;> rcases hm5 with h5 | h5
  · exfalso; refine himp 1 (NTKB.Apostol.eq_of_apply_neg_one_of_apply_five (a := 3) ?_ ?_)
    · rw [h1, NTKB.Apostol.changeLevel_apply_neg_one (a := 3) h48, MulChar.one_apply isUnit_one.neg]
    · rw [h5, NTKB.Apostol.changeLevel_apply_five (a := 3) h48,
        MulChar.one_apply (NTKB.Apostol.isUnit_five_two_pow 2)]
  · left; exact NTKB.Apostol.eq_of_apply_neg_one_of_apply_five (a := 3)
      (by rw [h1, chi8_neg_one]) (by rw [h5, chi8_five])
  · exfalso; refine himp chi4 (NTKB.Apostol.eq_of_apply_neg_one_of_apply_five (a := 3) ?_ ?_)
    · rw [h1, NTKB.Apostol.changeLevel_apply_neg_one (a := 3) h48, chi4_neg_one]
    · rw [h5, NTKB.Apostol.changeLevel_apply_five (a := 3) h48, chi4_five]
  · right; exact NTKB.Apostol.eq_of_apply_neg_one_of_apply_five (a := 3)
      (by rw [h1, chi8'_neg_one]) (by rw [h5, chi8'_five])

end NTKB.Davenport
