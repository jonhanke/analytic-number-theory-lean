/-
Copyright (c) 2026 The Tau Ceti contributors (`conductor_mul_of_coprime`); the NTKB authors (the
rest). Released under Apache 2.0 license.
-/
import NTKB.Elementary.SpecialValues.KroneckerSymbol

/-!
# The Kronecker character of a fundamental discriminant is primitive

`NTKB.kroneckerChar_isPrimitive`: for a fundamental discriminant `D`, `χ_D` is a primitive
character modulo `|D|` (its conductor is `|D|`). Ingredients: a criterion for primitivity
(`NTKB.isPrimitive_of_forall_prime`: for each prime `p ∣ N` some unit `u ≡ 1 (mod N/p)` has
`χ(u) ≠ 1`), the multiplicativity of conductors for coprime conductors (Tau Ceti's
`conductor_mul_of_coprime`, copied with credit), and Mathlib's `conductor_changeLevel`.

## Provenance
`conductor_mul_of_coprime` is copied (Apache 2.0) from Tau Ceti,
`TauCeti/NumberTheory/DirichletCharacter/Conductor.lean`, main `d7b4780` (2026-11-07), namespace
moved to `NTKB`, proof unchanged.
-/

noncomputable section

open Complex DirichletCharacter

namespace NTKB

/-- The conductor of a product of two Dirichlet characters with coprime conductors is the product
of their conductors. (Tau Ceti.) -/
theorem conductor_mul_of_coprime {R : Type*} [CommMonoidWithZero R] {N : ℕ}
    {χ ψ : DirichletCharacter R N} (hcop : χ.conductor.Coprime ψ.conductor) :
    (χ * ψ).conductor = χ.conductor * ψ.conductor := by
  have key {χ ψ : DirichletCharacter R N} (h : χ.conductor.Coprime ψ.conductor) :
      χ.conductor ∣ (χ * ψ).conductor := by
    refine h.dvd_of_dvd_mul_right ?_
    simpa only [mul_inv_cancel_right, conductor_inv] using
      (conductor_mul_dvd_lcm_conductor (χ * ψ) ψ⁻¹).trans (Nat.lcm_dvd_mul _ _)
  refine Nat.dvd_antisymm ((conductor_mul_dvd_lcm_conductor χ ψ).trans (Nat.lcm_dvd_mul _ _)) ?_
  exact hcop.mul_dvd_of_dvd_of_dvd (key hcop) (mul_comm ψ χ ▸ key hcop.symm)

/-- **A criterion for primitivity**: if for every prime `p ∣ N` there is `u` prime to `N` with
`u ≡ 1 (mod N/p)` and `χ(u) ≠ 1`, then `χ` is primitive. -/
theorem isPrimitive_of_forall_prime {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (h : ∀ p : ℕ, p.Prime → p ∣ N → ∃ u : ℕ, u.Coprime N ∧ (u : ZMod (N / p)) = 1 ∧
      χ (u : ZMod N) ≠ 1) :
    χ.IsPrimitive := by
  rw [isPrimitive_def]
  by_contra hne
  obtain ⟨q, hq⟩ := χ.conductor_dvd_level
  have hq1 : q ≠ 1 := by
    intro h1; apply hne; rw [h1, mul_one] at hq; exact hq.symm
  obtain ⟨p, hp, hpq⟩ := Nat.exists_prime_and_dvd hq1
  have key : ∀ M d : ℕ, M = d * q → p ∣ M ∧ M / p = d * (q / p) := fun M d hM ↦
    ⟨hM ▸ Dvd.dvd.mul_left hpq _, by rw [hM, Nat.mul_div_assoc _ hpq]⟩
  have hpN : p ∣ N := (key N _ hq).1
  have hdNp : χ.conductor ∣ N / p := ⟨q / p, (key N _ hq).2⟩
  have hNp : N / p ∣ N := Nat.div_dvd_of_dvd hpN
  have hF := χ.factorsThrough_conductor.mono χ hdNp hNp
  obtain ⟨u, hcop, hu1, hu⟩ := h p hp hpN
  obtain ⟨_, χ₀, hχ₀⟩ := hF
  apply hu
  have hval := changeLevel_eq_cast_of_dvd χ₀ hNp (ZMod.unitOfCoprime u hcop)
  simp only [ZMod.coe_unitOfCoprime, ZMod.cast_natCast hNp] at hval
  rw [hχ₀, hval, hu1, map_one]

/-- A prime dividing `4` or `8` is `2`. -/
private theorem prime_dvd_two_pow {p e : ℕ} (hp : p.Prime) (h : p ∣ 2 ^ e) : p = 2 :=
  (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h)

theorem isPrimitive_chi4 : chi4.IsPrimitive := by
  refine isPrimitive_of_forall_prime _ fun p hp hpN ↦ ?_
  obtain rfl := prime_dvd_two_pow (e := 2) hp hpN
  refine ⟨3, by norm_num, by decide, ?_⟩
  rw [chi4, MulChar.ringHomComp_apply, show ZMod.χ₄ ((3 : ℕ) : ZMod 4) = -1 by decide]
  norm_num

theorem isPrimitive_chi8 : chi8.IsPrimitive := by
  refine isPrimitive_of_forall_prime _ fun p hp hpN ↦ ?_
  obtain rfl := prime_dvd_two_pow (e := 3) hp hpN
  refine ⟨5, by norm_num, by decide, ?_⟩
  rw [chi8, MulChar.ringHomComp_apply, show ZMod.χ₈ ((5 : ℕ) : ZMod 8) = -1 by decide]
  norm_num

theorem isPrimitive_chi8' : chi8'.IsPrimitive := by
  refine isPrimitive_of_forall_prime _ fun p hp hpN ↦ ?_
  obtain rfl := prime_dvd_two_pow (e := 3) hp hpN
  refine ⟨5, by norm_num, by decide, ?_⟩
  rw [chi8', MulChar.ringHomComp_apply, show ZMod.χ₈' ((5 : ℕ) : ZMod 8) = -1 by decide]
  norm_num

/-- The Jacobi character of an odd prime is primitive. -/
theorem isPrimitive_jacobiChar_prime (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    (jacobiChar p).IsPrimitive := by
  have hF : ringChar (ZMod p) ≠ 2 := by rwa [ZMod.ringChar_zmod_n]
  obtain ⟨a, ha⟩ := quadraticChar_exists_neg_one hF
  refine isPrimitive_of_forall_prime _ fun q hq hqp ↦ ?_
  have hqp' : q = p := (Nat.prime_dvd_prime_iff_eq hq Fact.out).mp hqp
  subst hqp'
  have ha0 : a ≠ 0 := by rintro rfl; simp at ha
  refine ⟨a.val, ?_, ?_, ?_⟩
  · rw [← ZMod.isUnit_iff_coprime, ZMod.natCast_zmod_val]; exact ha0.isUnit
  · rw [Nat.div_self (Fact.out : q.Prime).pos]; exact Subsingleton.elim _ _
  · rw [ZMod.natCast_zmod_val, jacobiChar_prime, legendreChar_apply, ha]; norm_num

/-- `jacobiChar N = changeLevel (jacobiChar p) * changeLevel (jacobiChar m)` for `N = p m`
coprime. -/
theorem jacobiChar_eq_mul_changeLevel {p m N : ℕ} [NeZero p] [NeZero m] [NeZero N]
    (hN : N = p * m) (hcop : p.Coprime m) :
    jacobiChar N = changeLevel ⟨m, hN⟩ (jacobiChar p) *
      changeLevel ⟨p, by rw [hN, mul_comm]⟩ (jacobiChar m) := by
  ext a
  rw [jacobiChar_mul_apply hN, changeLevel_mul_changeLevel_apply hN hcop]

/-- The Jacobi character of an odd squarefree modulus is primitive. -/
theorem isPrimitive_jacobiChar_aux : ∀ m : ℕ, Odd m → Squarefree m → ∀ [NeZero m],
    (jacobiChar m).IsPrimitive := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro hm hsq _
  rcases eq_or_ne m 1 with rfl | hm1
  · rw [isPrimitive_def]
    exact Nat.dvd_one.mp (conductor_dvd_level _)
  set p := m.minFac with hpdef
  have hp : p.Prime := Nat.minFac_prime hm1
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨m', hm'⟩ : p ∣ m := Nat.minFac_dvd m
  have hm'0 : m' ≠ 0 := by
    rintro rfl; rw [mul_zero] at hm'; exact NeZero.ne m hm'
  have : NeZero m' := ⟨hm'0⟩
  have hpodd : Odd p := hm.of_dvd_nat ⟨m', hm'⟩
  have hp2 : p ≠ 2 := by
    rintro h; rw [h] at hpodd; exact absurd hpodd (by decide)
  have hm'odd : Odd m' := hm.of_dvd_nat ⟨p, by rw [hm', mul_comm]⟩
  have hm'sq : Squarefree m' := hsq.squarefree_of_dvd ⟨p, by rw [hm', mul_comm]⟩
  have hcop : p.Coprime m' := by
    rw [Nat.Prime.coprime_iff_not_dvd hp]
    rintro ⟨c, rfl⟩
    have := hsq p ⟨c, by rw [hm']; ring⟩
    exact hp.not_isUnit (Nat.isUnit_iff.mpr (Nat.isUnit_iff.mp this))
  have hlt : m' < m := by
    rw [hm']
    exact lt_mul_left (Nat.pos_of_ne_zero hm'0) hp.one_lt
  have ihm' := @ih m' hlt hm'odd hm'sq ⟨hm'0⟩
  have hpp := isPrimitive_jacobiChar_prime p hp2
  rw [isPrimitive_def] at ihm' hpp ⊢
  rw [jacobiChar_eq_mul_changeLevel hm' hcop, conductor_mul_of_coprime, conductor_changeLevel,
    conductor_changeLevel, hpp, ihm', hm']
  rw [conductor_changeLevel, conductor_changeLevel, hpp, ihm']
  exact hcop

theorem isPrimitive_jacobiChar {m : ℕ} [NeZero m] (hm : Odd m) (hsq : Squarefree m) :
    (jacobiChar m).IsPrimitive :=
  isPrimitive_jacobiChar_aux m hm hsq

/-- **The Kronecker character of a fundamental discriminant is primitive** (conductor `|D|`). -/
theorem kroneckerChar_isPrimitive {D : ℤ} (hD : IsFundamentalDiscriminant D) [NeZero D.natAbs] :
    (kroneckerChar D).IsPrimitive := by
  rcases hD with ⟨h1, hsq⟩ | ⟨h0, h23, hsq⟩
  · rw [kroneckerChar, if_pos (by omega)]
    exact isPrimitive_jacobiChar (Nat.odd_iff.mpr (by omega)) (Int.squarefree_natAbs.mpr hsq)
  rcases h23 with h2 | h3
  · have h16 : D % 16 = 8 := by omega
    set k := D / 8 with hk
    have hD4 : D / 4 = 2 * k := by omega
    have hksq : Squarefree k := hsq.squarefree_of_dvd ⟨2, by rw [hD4]; ring⟩
    have hm : Odd k.natAbs := Nat.odd_iff.mpr (by omega)
    have : NeZero k.natAbs := ⟨by omega⟩
    have hN : D.natAbs = 8 * k.natAbs := natAbs_eq_eight_mul (by omega)
    have hcop : Nat.Coprime 8 k.natAbs := Nat.Coprime.pow_left 3 (Nat.coprime_two_left.mpr hm)
    have hJ := isPrimitive_jacobiChar hm (Int.squarefree_natAbs.mpr hksq)
    rw [isPrimitive_def] at hJ ⊢
    rw [kroneckerChar, if_neg (by omega), dif_neg (by omega), dif_pos h16]
    split_ifs
    · have h8 := isPrimitive_chi8
      rw [isPrimitive_def] at h8
      rw [conductor_mul_of_coprime, conductor_changeLevel, conductor_changeLevel, h8, hJ, hN]
      rw [conductor_changeLevel, conductor_changeLevel, h8, hJ]; exact hcop
    · have h8 := isPrimitive_chi8'
      rw [isPrimitive_def] at h8
      rw [conductor_mul_of_coprime, conductor_changeLevel, conductor_changeLevel, h8, hJ, hN]
      rw [conductor_changeLevel, conductor_changeLevel, h8, hJ]; exact hcop
  · have h8 : D % 8 = 4 := by omega
    set k := D / 4 with hk
    have hm : Odd k.natAbs := Nat.odd_iff.mpr (by omega)
    have : NeZero k.natAbs := ⟨by omega⟩
    have hN : D.natAbs = 4 * k.natAbs := natAbs_eq_four_mul (by omega)
    have hcop : Nat.Coprime 4 k.natAbs := Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr hm)
    have hJ := isPrimitive_jacobiChar hm (Int.squarefree_natAbs.mpr hsq)
    have h4 := isPrimitive_chi4
    rw [isPrimitive_def] at hJ h4 ⊢
    rw [kroneckerChar, if_neg (by omega), dif_pos h8, conductor_mul_of_coprime,
      conductor_changeLevel, conductor_changeLevel, h4, hJ, hN]
    rw [conductor_changeLevel, conductor_changeLevel, h4, hJ]; exact hcop

end NTKB
