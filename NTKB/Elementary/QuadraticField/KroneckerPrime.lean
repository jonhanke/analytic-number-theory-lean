/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Elementary.QuadraticField.Model
import NTKB.Elementary.SpecialValues.KroneckerSymbol

/-!
# The Kronecker symbol `(D/p)` and roots of the minimal polynomial of `ω` modulo `p`

For `D ≡ 0, 1 (mod 4)` put `f(t) = t² - (D % 4) t - D / 4`, the minimal polynomial of `ω`
(`NTKB.QuadraticField.minpolyAt`); then `(2t - D % 4)² = 4 f(t) + D`. For a fundamental
discriminant `D` and a prime `p` (`2` included):

* `p ∣ D` iff `(D/p) = 0`, and then `f` has a double root modulo `p`;
* `p ∤ D` and `f` has a root modulo `p` iff `(D/p) = 1` (the root is then simple);
* `p ∤ D` and `f` has no root modulo `p` iff `(D/p) = -1`.

For odd `p` this is `(D/p) = ` Legendre symbol and `f` has a root iff `D` is a square modulo `p`;
for `p = 2` and `D ≡ 1 (mod 4)`, `f` has a root iff `D ≡ 1 (mod 8)`, iff `(D/2) = 1`.
-/

noncomputable section

namespace NTKB.QuadraticField

/-- `f(t) = t² - (D % 4) t - D / 4`: the minimal polynomial of `ω` evaluated at `t`. -/
def minpolyAt (D t : ℤ) : ℤ := t * t - (D % 4) * t - D / 4

theorem sq_two_mul_sub {D : ℤ} (hD : D % 4 = 0 ∨ D % 4 = 1) (t : ℤ) :
    (2 * t - D % 4) ^ 2 = 4 * minpolyAt D t + D := by
  have h := QuadraticAlgebra.discr_ediv_emod hD
  rw [QuadraticAlgebra.discr_def] at h
  unfold minpolyAt
  linear_combination h

theorem two_ne_zero_zmod {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h
  have : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp (by exact_mod_cast h)
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp this)

theorem minpolyAt_cast {D : ℤ} {p : ℕ} (t : ℤ) :
    ((minpolyAt D t : ℤ) : ZMod p) =
      (t : ZMod p) * t - ((D % 4 : ℤ) : ZMod p) * t - ((D / 4 : ℤ) : ZMod p) := by
  unfold minpolyAt; push_cast; ring

/-- An element of `ZMod p` as the residue of an integer. -/
theorem exists_intCast_eq {p : ℕ} [NeZero p] (x : ZMod p) : ∃ t : ℤ, (t : ZMod p) = x :=
  ⟨x.val, by simp⟩

/-- For odd `p`, `f` has a root modulo `p` iff `D` is a square modulo `p`. -/
theorem exists_root_iff_isSquare {D : ℤ} (hD : D % 4 = 0 ∨ D % 4 = 1) {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) :
    (∃ t : ℤ, (p : ℤ) ∣ minpolyAt D t) ↔ IsSquare (D : ZMod p) := by
  have hD' := QuadraticAlgebra.discr_ediv_emod hD
  rw [QuadraticAlgebra.discr_def] at hD'
  have hDp : (D : ZMod p) = ((D % 4 : ℤ) : ZMod p) ^ 2 + 4 * ((D / 4 : ℤ) : ZMod p) := by
    have := congrArg (Int.cast : ℤ → ZMod p) hD'
    simp only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_ofNat] at this
    exact this.symm
  constructor
  · rintro ⟨t, ht⟩
    have h0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr ht
    rw [minpolyAt_cast] at h0
    refine ⟨2 * t - ((D % 4 : ℤ) : ZMod p), ?_⟩
    rw [hDp]
    linear_combination (-4 : ZMod p) * h0
  · rintro ⟨r, hr⟩
    have h2 := two_ne_zero_zmod hp2
    obtain ⟨t, ht⟩ := exists_intCast_eq ((r + ((D % 4 : ℤ) : ZMod p)) / 2)
    refine ⟨t, (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp ?_⟩
    rw [minpolyAt_cast, ht]
    field_simp
    rw [hDp] at hr
    linear_combination (-1 : ZMod p) * hr

theorem natAbs_ne_zero_of_fundamental {D : ℤ} (hD : IsFundamentalDiscriminant D) :
    NeZero D.natAbs := ⟨Int.natAbs_ne_zero.mpr hD.ne_zero⟩

/-- `(D/p) = 0` when `p ∣ D`. -/
theorem kroneckerChar_eq_zero_of_dvd {D : ℤ} {p : ℕ} (hp : p.Prime) (h : (p : ℤ) ∣ D) :
    kroneckerChar D (p : ZMod D.natAbs) = 0 := by
  refine MulChar.map_nonunit _ ?_
  rw [ZMod.isUnit_iff_coprime]
  intro hc
  exact hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hc (Int.natCast_dvd.mp h))

/-- For odd `p`, `(D/p)` is the Legendre symbol. -/
theorem kroneckerChar_prime_odd {D : ℤ} (hD : IsFundamentalDiscriminant D) {p : ℕ}
    [hp : Fact p.Prime] (hp2 : p ≠ 2) :
    kroneckerChar D (p : ZMod D.natAbs) = (legendreSym p D : ℂ) := by
  have := natAbs_ne_zero_of_fundamental hD
  rw [kroneckerChar_apply_odd hD (hp.out.odd_of_ne_two hp2),
    jacobiSym.legendreSym.to_jacobiSym]

/-- For odd `D`, `(D/2) = 1` if `D ≡ 1 (mod 8)` and `-1` if `D ≡ 5 (mod 8)`. -/
theorem kroneckerChar_two {D : ℤ} (hD : IsFundamentalDiscriminant D) (h2 : D % 2 = 1) :
    kroneckerChar D ((2 : ℕ) : ZMod D.natAbs) = if D % 8 = 1 then 1 else -1 := by
  have := natAbs_ne_zero_of_fundamental hD
  have h41 : D % 4 = 1 := by rcases emod_four_of_isFundamental hD with h | h <;> omega
  rw [kroneckerChar, if_pos h2, show ((2 : ℕ) : ZMod D.natAbs) = ((2 : ℤ) : ZMod D.natAbs) by
    push_cast; rfl, jacobiChar_intCast, jacobiSym.at_two (Nat.odd_iff.mpr (by omega)),
    ZMod.χ₈_nat_eq_if_mod_eight]
  rcases Int.natAbs_eq D with h | h
  · have hm : (D.natAbs : ℤ) = D := by omega
    split_ifs <;> first | rfl | (exfalso; omega)
  · have hm : (D.natAbs : ℤ) = -D := by omega
    split_ifs <;> first | rfl | (exfalso; omega) | simp

/-- For `D ≡ 1 (mod 4)`, `f` has a root modulo `2` iff `D ≡ 1 (mod 8)`. -/
theorem exists_root_two_iff {D : ℤ} (h41 : D % 4 = 1) :
    (∃ t : ℤ, (2 : ℤ) ∣ minpolyAt D t) ↔ D % 8 = 1 := by
  have key : ∀ t, minpolyAt D t = t * (t - 1) - D / 4 := by
    intro t; unfold minpolyAt; rw [h41]; ring
  constructor
  · rintro ⟨t, ht⟩
    rw [key] at ht
    obtain ⟨k, hk⟩ := Int.even_mul_pred_self t
    generalize t * (t - 1) = u at ht hk
    omega
  · intro h
    exact ⟨0, by rw [key]; omega⟩

/-- If `p ∤ D` and `f(t) ≡ 0 (mod p)`, then `(D/p) = 1`. -/
theorem kroneckerChar_eq_one_of_root {D : ℤ} (hD : IsFundamentalDiscriminant D) {p : ℕ}
    (hp : p.Prime) (hpD : ¬ (p : ℤ) ∣ D) {t : ℤ} (ht : (p : ℤ) ∣ minpolyAt D t) :
    kroneckerChar D (p : ZMod D.natAbs) = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  by_cases hp2 : p = 2
  · subst hp2
    have h2 : D % 2 = 1 := by omega
    have h41 : D % 4 = 1 := by rcases emod_four_of_isFundamental hD with h | h <;> omega
    rw [kroneckerChar_two hD h2, if_pos ((exists_root_two_iff h41).mp ⟨t, ht⟩)]
  · rw [kroneckerChar_prime_odd hD hp2]
    have h0 : (D : ZMod p) ≠ 0 := fun h ↦ hpD ((ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp h)
    rw [(legendreSym.eq_one_iff p h0).mpr
      ((exists_root_iff_isSquare (emod_four_of_isFundamental hD) hp2).mp ⟨t, ht⟩)]
    simp

/-- If `p ∤ D` and `f` has no root modulo `p`, then `(D/p) = -1`. -/
theorem kroneckerChar_eq_neg_one_of_forall {D : ℤ} (hD : IsFundamentalDiscriminant D) {p : ℕ}
    (hp : p.Prime) (hpD : ¬ (p : ℤ) ∣ D) (h : ∀ t : ℤ, ¬ (p : ℤ) ∣ minpolyAt D t) :
    kroneckerChar D (p : ZMod D.natAbs) = -1 := by
  have : Fact p.Prime := ⟨hp⟩
  by_cases hp2 : p = 2
  · subst hp2
    have h2 : D % 2 = 1 := by omega
    have h41 : D % 4 = 1 := by rcases emod_four_of_isFundamental hD with h | h <;> omega
    rw [kroneckerChar_two hD h2, if_neg (fun h8 ↦ ?_)]
    obtain ⟨t, ht⟩ := (exists_root_two_iff h41).mpr h8
    exact h t ht
  · rw [kroneckerChar_prime_odd hD hp2]
    rw [(legendreSym.eq_neg_one_iff p).mpr
      (fun hsq ↦ ?_)]
    · simp
    obtain ⟨t, ht⟩ := (exists_root_iff_isSquare (emod_four_of_isFundamental hD) hp2).mpr hsq
    exact h t ht

/-- A root of `f` modulo `p ∤ D` is simple: `p ∤ 2t - D % 4`. -/
theorem not_dvd_two_mul_sub_of_root {D : ℤ} (hD : D % 4 = 0 ∨ D % 4 = 1) {p : ℕ}
    (hpD : ¬ (p : ℤ) ∣ D) {t : ℤ} (ht : (p : ℤ) ∣ minpolyAt D t) :
    ¬ (p : ℤ) ∣ 2 * t - D % 4 := by
  intro h
  apply hpD
  have h2 : (p : ℤ) ∣ (2 * t - D % 4) ^ 2 := dvd_pow h two_ne_zero
  rw [sq_two_mul_sub hD] at h2
  have := (Int.dvd_add_right (dvd_mul_of_dvd_right ht 4)).mp h2
  exact this

/-- If `p ∣ D`, then `f` has a double root modulo `p`. -/
theorem exists_double_root_of_dvd {D : ℤ} (hD : IsFundamentalDiscriminant D) {p : ℕ}
    (hp : p.Prime) (h : (p : ℤ) ∣ D) :
    ∃ t : ℤ, (p : ℤ) ∣ minpolyAt D t ∧ (p : ℤ) ∣ 2 * t - D % 4 := by
  have : Fact p.Prime := ⟨hp⟩
  have hD4 := emod_four_of_isFundamental hD
  by_cases hp2 : p = 2
  · subst hp2
    have h40 : D % 4 = 0 := by omega
    refine ⟨D / 4, ?_, ?_⟩
    · unfold minpolyAt
      rw [h40]
      obtain ⟨k, hk⟩ := Int.even_mul_pred_self (D / 4)
      have : D / 4 * (D / 4) - 0 * (D / 4) - D / 4 = D / 4 * (D / 4 - 1) := by ring
      rw [this, hk]
      exact ⟨k, by push_cast; ring⟩
    · rw [h40]; exact ⟨D / 4, by push_cast; ring⟩
  · have h2 := two_ne_zero_zmod hp2
    have hD0 : (D : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr h
    have hD' := QuadraticAlgebra.discr_ediv_emod hD4
    rw [QuadraticAlgebra.discr_def] at hD'
    have hDp : ((D % 4 : ℤ) : ZMod p) ^ 2 + 4 * ((D / 4 : ℤ) : ZMod p) = 0 := by
      have := congrArg (Int.cast : ℤ → ZMod p) hD'
      simp only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_ofNat] at this
      rw [this, hD0]
    obtain ⟨t, ht⟩ := exists_intCast_eq (((D % 4 : ℤ) : ZMod p) / 2)
    refine ⟨t, (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp ?_,
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp ?_⟩
    · rw [minpolyAt_cast, ht]
      field_simp
      linear_combination (-1 : ZMod p) * hDp
    · push_cast
      rw [ht]
      field_simp
      ring

end NTKB.QuadraticField
