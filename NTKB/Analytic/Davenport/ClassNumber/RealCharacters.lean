/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Davenport.Ch1to6.RealPrimitive
import NTKB.Analytic.Davenport.Ch1to6.Kronecker
import NTKB.Elementary.SpecialValues.KroneckerPrimitive

/-! # Davenport, Chapter 5: real primitive characters are Kronecker symbols

(§5, p. 40.) Every real primitive nonprincipal character modulo `q` is `χ_D = (D/·)` for a
fundamental discriminant `D ≠ 1` with `|D| = q`. Proof: strong induction on `q`. Split `q = p^a r`
with `p ∤ r`, decompose `χ = χ₁ χ₂` by the Chinese remainder theorem (both factors are real and
primitive), apply the prime-power classification to `χ₁` and the induction hypothesis to `χ₂`, and
multiply the discriminants (`kroneckerChar_mul_apply`).
-/

noncomputable section
open DirichletCharacter

namespace NTKB.Davenport

/-! ### Products of fundamental discriminants -/

private theorem fund_mul_odd {D₁ D₂ : ℤ} (h1 : D₁ % 4 = 1) (hs1 : Squarefree D₁)
    (h₂ : IsFundamentalDiscriminant D₂) (hc : Nat.Coprime D₁.natAbs D₂.natAbs) :
    IsFundamentalDiscriminant (D₁ * D₂) := by
  rcases h₂ with ⟨h2, hs2⟩ | ⟨h0, h23, hs2⟩
  · left
    refine ⟨by rw [Int.mul_emod, h1, h2]; rfl, ?_⟩
    rw [← Int.squarefree_natAbs, Int.natAbs_mul, Nat.squarefree_mul_iff]
    exact ⟨hc, Int.squarefree_natAbs.mpr hs1, Int.squarefree_natAbs.mpr hs2⟩
  · right
    obtain ⟨k, hk⟩ : ∃ k, D₂ = 4 * k := ⟨D₂ / 4, by omega⟩
    subst hk
    have e : 4 * k / 4 = k := by omega
    rw [e] at h23 hs2
    have e2 : D₁ * (4 * k) = 4 * (D₁ * k) := by ring
    have e3 : 4 * (D₁ * k) / 4 = D₁ * k := by omega
    have hkd : k.natAbs ∣ (4 * k).natAbs := ⟨4, by rw [Int.natAbs_mul]; simp; ring⟩
    have hck : Nat.Coprime D₁.natAbs k.natAbs := Nat.Coprime.coprime_dvd_right hkd hc
    rw [e2, e3]
    refine ⟨by omega, ?_, ?_⟩
    · rw [Int.mul_emod, h1]
      omega
    · rw [← Int.squarefree_natAbs, Int.natAbs_mul, Nat.squarefree_mul_iff]
      exact ⟨hck, Int.squarefree_natAbs.mpr hs1, Int.squarefree_natAbs.mpr hs2⟩

private theorem fund_mul {D₁ D₂ : ℤ} (h₁ : IsFundamentalDiscriminant D₁)
    (h₂ : IsFundamentalDiscriminant D₂) (hc : Nat.Coprime D₁.natAbs D₂.natAbs) :
    IsFundamentalDiscriminant (D₁ * D₂) := by
  rcases h₁ with ⟨h1, hs1⟩ | ⟨h0, h23, hs1⟩
  · exact fund_mul_odd h1 hs1 h₂ hc
  · rcases h₂ with ⟨h2, hs2⟩ | ⟨h0', h23', hs2'⟩
    · rw [mul_comm]
      exact fund_mul_odd h2 hs2 (Or.inr ⟨h0, h23, hs1⟩) hc.symm
    · exfalso
      exact Nat.not_coprime_of_dvd_of_dvd (by norm_num : 1 < 2) (by omega) (by omega) hc

/-! ### The Chinese remainder decomposition -/

private theorem exists_split {q m n : ℕ} [NeZero m] [NeZero n] (hq : q = m * n)
    (hcop : m.Coprime n) (χ : DirichletCharacter ℂ q) :
    ∃ (χ₁ : DirichletCharacter ℂ m) (χ₂ : DirichletCharacter ℂ n),
      (∀ a : ℕ, χ (a : ZMod q) = χ₁ (a : ZMod m) * χ₂ (a : ZMod n)) ∧
      (χ.IsQuadratic → χ₁.IsQuadratic ∧ χ₂.IsQuadratic) ∧
      (χ.IsPrimitive → χ₁.IsPrimitive ∧ χ₂.IsPrimitive) := by
  subst hq
  let e : ZMod (m * n) ≃+* ZMod m × ZMod n := ZMod.chineseRemainder hcop
  have hm : m ∣ m * n := Dvd.intro n rfl
  have hn : n ∣ m * n := Dvd.intro_left m rfl
  have he : ∀ a : ZMod (m * n), e a = (ZMod.cast a, ZMod.cast a) := by
    intro a
    rw [← ZMod.natCast_zmod_val a, map_natCast]
    refine Prod.ext ?_ ?_
    · rw [ZMod.cast_natCast (R := ZMod m) hm]; simp
    · rw [ZMod.cast_natCast (R := ZMod n) hn]; simp
  let χ₁ : DirichletCharacter ℂ m :=
    { toFun := fun a ↦ χ (e.symm (a, 1))
      map_one' := by
        have : ((1 : ZMod m), (1 : ZMod n)) = 1 := rfl
        show χ (e.symm ((1 : ZMod m), (1 : ZMod n))) = 1
        rw [this, map_one, map_one]
      map_mul' := fun a b ↦ by
        have : ((a * b, 1) : ZMod m × ZMod n) = (a, 1) * (b, 1) := by simp
        rw [this, map_mul, map_mul]
      map_nonunit' := fun a ha ↦ MulChar.map_nonunit χ (fun hu ↦ ha (by
        have h := hu.map e
        rw [e.apply_symm_apply] at h
        exact (Prod.isUnit_iff.mp h).1)) }
  let χ₂ : DirichletCharacter ℂ n :=
    { toFun := fun a ↦ χ (e.symm (1, a))
      map_one' := by
        have : ((1 : ZMod m), (1 : ZMod n)) = 1 := rfl
        show χ (e.symm ((1 : ZMod m), (1 : ZMod n))) = 1
        rw [this, map_one, map_one]
      map_mul' := fun a b ↦ by
        have : ((1, a * b) : ZMod m × ZMod n) = (1, a) * (1, b) := by simp
        rw [this, map_mul, map_mul]
      map_nonunit' := fun a ha ↦ MulChar.map_nonunit χ (fun hu ↦ ha (by
        have h := hu.map e
        rw [e.apply_symm_apply] at h
        exact (Prod.isUnit_iff.mp h).2)) }
  have hv : ∀ a : ZMod (m * n), χ a = χ₁ (ZMod.cast a) * χ₂ (ZMod.cast a) := by
    intro a
    have h1 : χ₁ (ZMod.cast a) = χ (e.symm (ZMod.cast a, 1)) := rfl
    have h2 : χ₂ (ZMod.cast a) = χ (e.symm (1, ZMod.cast a)) := rfl
    rw [h1, h2, ← map_mul χ, ← map_mul e.symm, Prod.mk_mul_mk, mul_one, one_mul, ← he,
      e.symm_apply_apply]
  have hχ : χ = changeLevel hm χ₁ * changeLevel hn χ₂ := by
    ext a
    rw [changeLevel_mul_changeLevel_apply rfl hcop χ₁ χ₂ hm hn, hv]
  refine ⟨χ₁, χ₂, ?_, ?_, ?_⟩
  · intro a
    rw [hv, ZMod.cast_natCast hm, ZMod.cast_natCast hn]
  · intro hquad
    refine ⟨fun a ↦ hquad _, fun a ↦ hquad _⟩
  · intro hprim
    rw [isPrimitive_def] at hprim
    have hdvd := conductor_mul_dvd_lcm_conductor (changeLevel hm χ₁) (changeLevel hn χ₂)
    rw [← hχ, hprim, conductor_changeLevel, conductor_changeLevel] at hdvd
    have h1 : χ₁.conductor ≤ m := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne m))
      χ₁.conductor_dvd_level
    have h2 : χ₂.conductor ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne n))
      χ₂.conductor_dvd_level
    have h3 : m * n ≤ χ₁.conductor * χ₂.conductor :=
      Nat.le_of_dvd (Nat.mul_pos (Nat.pos_of_ne_zero χ₁.conductor_ne_zero)
        (Nat.pos_of_ne_zero χ₂.conductor_ne_zero)) (hdvd.trans (Nat.lcm_dvd_mul _ _))
    have hm0 : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
    have hn0 : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
    refine ⟨?_, ?_⟩ <;> rw [isPrimitive_def]
    · by_contra hne
      have : χ₁.conductor < m := lt_of_le_of_ne h1 hne
      nlinarith
    · by_contra hne
      have : χ₂.conductor < n := lt_of_le_of_ne h2 hne
      nlinarith

/-! ### Prime moduli and moduli `4`, `8` -/

private theorem jacobiChar_natCast_congr {n p : ℕ} (h : n = p) (m : ℕ) :
    jacobiChar n (m : ZMod n) = jacobiChar p (m : ZMod p) := by
  subst h; rfl

private theorem odd_prime_core {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {χ : DirichletCharacter ℂ p}
    (hquad : χ.IsQuadratic) (h1 : χ ≠ 1) :
    ∃ D : ℤ, IsFundamentalDiscriminant D ∧ D ≠ 1 ∧ D.natAbs = p ∧
      ∀ m : ℕ, χ m = kroneckerChar D m := by
  have : Fact p.Prime := ⟨hp⟩
  have hχ := eq_legendreChar_of_isQuadratic hp2 hquad h1
  have hodd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two hp2)
  have hsq : Squarefree p := hp.squarefree
  have hp1 := hp.one_lt
  obtain ⟨D, hDf, hDodd, hDn, hD1⟩ : ∃ D : ℤ, IsFundamentalDiscriminant D ∧ D % 2 = 1 ∧
      D.natAbs = p ∧ D ≠ 1 := by
    by_cases h4 : p % 4 = 1
    · refine ⟨p, Or.inl ⟨by omega, ?_⟩, by omega, by simp, by omega⟩
      exact Int.squarefree_natAbs.mp (by simpa using hsq)
    · refine ⟨-p, Or.inl ⟨by omega, ?_⟩, by omega, by simp, by omega⟩
      exact Int.squarefree_natAbs.mp (by simpa using hsq)
  refine ⟨D, hDf, hD1, hDn, fun m ↦ ?_⟩
  rw [hχ, kroneckerChar_eq_jacobiChar_of_odd hDodd, jacobiChar_natCast_congr hDn,
    jacobiChar_prime]

private theorem odd_prime_aux {q p : ℕ} (hq : q = p) (hp : p.Prime) (hp2 : p ≠ 2)
    {χ : DirichletCharacter ℂ q} (hquad : χ.IsQuadratic) (h1 : χ ≠ 1) :
    ∃ D : ℤ, IsFundamentalDiscriminant D ∧ D ≠ 1 ∧ D.natAbs = q ∧
      ∀ m : ℕ, χ m = kroneckerChar D m := by
  subst hq
  exact odd_prime_core hp hp2 hquad h1

private theorem kron_neg_four : kroneckerChar (-4) = chi4 := by
  unfold kroneckerChar
  rw [if_neg (by decide), dif_pos (by decide)]
  have h : jacobiChar ((-4 : ℤ) / 4).natAbs = 1 := DirichletCharacter.level_one' _ (by decide)
  rw [h, changeLevel_one, mul_one]
  exact changeLevel_self _

private theorem kron_eight : kroneckerChar 8 = chi8 := by
  unfold kroneckerChar
  rw [if_neg (by decide), dif_neg (by decide), dif_pos (by decide), if_pos (by decide)]
  have h : jacobiChar ((8 : ℤ) / 8).natAbs = 1 := DirichletCharacter.level_one' _ (by decide)
  rw [h, changeLevel_one, mul_one]
  exact changeLevel_self _

private theorem kron_neg_eight : kroneckerChar (-8) = chi8' := by
  unfold kroneckerChar
  rw [if_neg (by decide), dif_neg (by decide), dif_pos (by decide), if_neg (by decide)]
  have h : jacobiChar ((-8 : ℤ) / 8).natAbs = 1 := DirichletCharacter.level_one' _ (by decide)
  rw [h, changeLevel_one, mul_one]
  exact changeLevel_self _

private theorem four_core {χ : DirichletCharacter ℂ 4} (hquad : χ.IsQuadratic)
    (hprim : χ.IsPrimitive) :
    ∃ D : ℤ, IsFundamentalDiscriminant D ∧ D ≠ 1 ∧ D.natAbs = 4 ∧
      ∀ m : ℕ, χ m = kroneckerChar D m := by
  refine ⟨-4, Or.inr ⟨by decide, Or.inr (by decide), ?_⟩, by decide, by decide, fun m ↦ ?_⟩
  · exact (isUnit_one.neg.squarefree : Squarefree (-1 : ℤ))
  · rw [eq_chi4_of_isPrimitive hquad hprim, kron_neg_four]

private theorem eight_core {χ : DirichletCharacter ℂ 8} (hquad : χ.IsQuadratic)
    (hprim : χ.IsPrimitive) :
    ∃ D : ℤ, IsFundamentalDiscriminant D ∧ D ≠ 1 ∧ D.natAbs = 8 ∧
      ∀ m : ℕ, χ m = kroneckerChar D m := by
  rcases eq_chi8_or_eq_chi8'_of_isPrimitive hquad hprim with h | h
  · refine ⟨8, Or.inr ⟨by decide, Or.inl (by decide), ?_⟩, by decide, by decide, fun m ↦ ?_⟩
    · rw [show (8 : ℤ) / 4 = 2 by norm_num]
      exact Int.prime_two.squarefree
    · rw [h, kron_eight]
  · refine ⟨-8, Or.inr ⟨by decide, Or.inl (by decide), ?_⟩, by decide, by decide, fun m ↦ ?_⟩
    · rw [show (-8 : ℤ) / 4 = -2 by norm_num]
      exact Int.squarefree_natAbs.mp (by simpa using Nat.prime_two.squarefree)
    · rw [h, kron_neg_eight]

private theorem four_aux {q : ℕ} (hq : q = 4) {χ : DirichletCharacter ℂ q} (hquad : χ.IsQuadratic)
    (hprim : χ.IsPrimitive) :
    ∃ D : ℤ, IsFundamentalDiscriminant D ∧ D ≠ 1 ∧ D.natAbs = q ∧
      ∀ m : ℕ, χ m = kroneckerChar D m := by
  subst hq
  exact four_core hquad hprim

private theorem eight_aux {q : ℕ} (hq : q = 8) {χ : DirichletCharacter ℂ q} (hquad : χ.IsQuadratic)
    (hprim : χ.IsPrimitive) :
    ∃ D : ℤ, IsFundamentalDiscriminant D ∧ D ≠ 1 ∧ D.natAbs = q ∧
      ∀ m : ℕ, χ m = kroneckerChar D m := by
  subst hq
  exact eight_core hquad hprim

private theorem eq_one_aux {q p a : ℕ} (hq : q = p ^ a) (hp : p.Prime) (hp2 : p ≠ 2) (ha : 1 ≤ a)
    {χ : DirichletCharacter ℂ q} (hquad : χ.IsQuadratic) (hprim : χ.IsPrimitive) : a = 1 := by
  subst hq
  exact eq_one_of_isPrimitive_of_isQuadratic_odd hp hp2 ha hquad hprim

private theorem two_three_aux {q a : ℕ} (hq : q = 2 ^ a) (ha : 1 ≤ a)
    {χ : DirichletCharacter ℂ q} (hquad : χ.IsQuadratic) (hprim : χ.IsPrimitive) :
    a = 2 ∨ a = 3 := by
  subst hq
  exact two_or_three_of_isPrimitive_of_isQuadratic_two_pow ha hquad hprim

/-- The prime-power case. -/
private theorem prime_pow_aux {q p a : ℕ} (hq : q = p ^ a) (hp : p.Prime) (ha : 1 ≤ a)
    {χ : DirichletCharacter ℂ q} (hquad : χ.IsQuadratic) (hprim : χ.IsPrimitive) (h1 : χ ≠ 1) :
    ∃ D : ℤ, IsFundamentalDiscriminant D ∧ D ≠ 1 ∧ D.natAbs = q ∧
      ∀ m : ℕ, χ m = kroneckerChar D m := by
  by_cases hp2 : p = 2
  · subst hp2
    rcases two_three_aux hq ha hquad hprim with rfl | rfl
    · exact four_aux (by rw [hq]; norm_num) hquad hprim
    · exact eight_aux (by rw [hq]; norm_num) hquad hprim
  · have := eq_one_aux hq hp hp2 ha hquad hprim
    subst this
    exact odd_prime_aux (by rw [hq, pow_one]) hp hp2 hquad h1

/-! ### The induction -/

private theorem exists_aux : ∀ q : ℕ, ∀ [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive →
    χ.IsQuadratic → χ ≠ 1 → ∃ D : ℤ, IsFundamentalDiscriminant D ∧ D ≠ 1 ∧ D.natAbs = q ∧
      ∀ m : ℕ, χ m = kroneckerChar D m := by
  intro q
  induction q using Nat.strong_induction_on with
  | _ q ih =>
  intro _ χ hprim hquad h1
  have hq1 : q ≠ 1 := fun h ↦ h1 (DirichletCharacter.level_one' χ h)
  have hq0 : q ≠ 0 := NeZero.ne q
  obtain ⟨p, hp, hpq⟩ : ∃ p, p.Prime ∧ p ∣ q := ⟨_, Nat.minFac_prime hq1, Nat.minFac_dvd q⟩
  obtain ⟨a, r, hpr, hqeq⟩ := Nat.exists_eq_pow_mul_and_not_dvd hq0 p hp.ne_one
  have ha : 1 ≤ a := by
    rcases Nat.eq_zero_or_pos a with h | h
    · exfalso
      apply hpr
      rw [h, pow_zero, one_mul] at hqeq
      rw [← hqeq]
      exact hpq
    · exact h
  have hr0 : r ≠ 0 := by
    rintro rfl
    simp at hqeq
    exact hq0 hqeq
  have : NeZero r := ⟨hr0⟩
  have : NeZero (p ^ a) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hcop : (p ^ a).Coprime r :=
    Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd hp).2 hpr)
  by_cases hr1 : r = 1
  · have hq : q = p ^ a := by rw [hqeq, hr1, mul_one]
    exact prime_pow_aux hq hp ha hquad hprim h1
  · have hpa : 1 < p ^ a := Nat.one_lt_pow (by omega) hp.one_lt
    obtain ⟨χ₁, χ₂, hval, hquad', hprim'⟩ := exists_split hqeq hcop χ
    obtain ⟨hq₁, hq₂⟩ := hquad' hquad
    obtain ⟨hp₁, hp₂⟩ := hprim' hprim
    have h₁ne : χ₁ ≠ 1 := by
      rintro rfl
      rw [isPrimitive_def, conductor_one] at hp₁
      omega
    have h₂ne : χ₂ ≠ 1 := by
      rintro rfl
      rw [isPrimitive_def, conductor_one] at hp₂
      exact hr1 hp₂.symm
    obtain ⟨D₁, hf₁, hD₁, hn₁, hv₁⟩ := prime_pow_aux rfl hp ha hq₁ hp₁ h₁ne
    have hlt : r < q := by
      rw [hqeq]
      exact lt_mul_left (Nat.pos_of_ne_zero hr0) hpa
    obtain ⟨D₂, hf₂, hD₂, hn₂, hv₂⟩ := ih r hlt χ₂ hp₂ hq₂ h₂ne
    have hc : Nat.Coprime D₁.natAbs D₂.natAbs := by rw [hn₁, hn₂]; exact hcop
    have hfm := fund_mul hf₁ hf₂ hc
    have hnm : (D₁ * D₂).natAbs = q := by rw [Int.natAbs_mul, hn₁, hn₂, hqeq]
    refine ⟨D₁ * D₂, hfm, ?_, hnm, fun m ↦ ?_⟩
    · intro h
      rw [h] at hnm
      exact hq1 hnm.symm
    · rw [hval m, hv₁ m, hv₂ m, kroneckerChar_mul_apply hf₁ hf₂ hfm m]

/-- **Davenport §5, p. 40.** Every real primitive nonprincipal character modulo `q` is the
Kronecker symbol `(D/·)` of a fundamental discriminant `D ≠ 1` with `|D| = q`. -/
@[kb "davenport1980" "Ch 5, p. 40"]
theorem exists_kroneckerChar_of_isPrimitive {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hprim : χ.IsPrimitive) (hquad : χ.IsQuadratic) (h1 : χ ≠ 1) :
    ∃ D : ℤ, IsFundamentalDiscriminant D ∧ D ≠ 1 ∧ D.natAbs = q ∧
      ∀ m : ℕ, χ m = kroneckerChar D m :=
  exists_aux q χ hprim hquad h1

end NTKB.Davenport
