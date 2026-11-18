/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Davenport.Ch1to6.CharacterProduct
import NTKB.Analytic.Davenport.Ch1to6.RealPrimitive
import NTKB.Elementary.SpecialValues.KroneckerPrimitive

/-!
# The moduli of real primitive characters (Davenport, Chapter 5, row 5-9)

A real primitive character modulo `q` exists if and only if `q` is a product of pairwise coprime
basic moduli: odd primes `p`, `4` and `8` (equivalently: every prime power `p^{v_p(q)}` of `q` is an
odd prime, `4` or `8`; `exists_isPrimitive_isQuadratic_iff`). Through the decomposition of row 4-4
a character `∏_p χ_p` is real and primitive exactly when every `χ_p` is
(`isPrimitive_primePowerProd_iff`, `isQuadratic_primePowerProd_iff`), so it is then the product of
the basic characters (Legendre's symbol modulo `p`, `χ_4`, and `χ_8` or `χ_8'` modulo `8`: the
local classification of `RealPrimitive.lean`), and there are two such characters if `8 ∣ q` and
one otherwise (`card_isPrimitive_isQuadratic`).

The conductor of a product with coprime conductors is the product of the conductors
(`NTKB.conductor_mul_of_coprime`, copied earlier from Tau Ceti with credit).

Source text unavailable; written from the map row 5-9.
-/

open DirichletCharacter

namespace NTKB.Davenport

/-- The basic moduli: odd primes, `4` and `8`. -/
def IsBasicModulus (m : ℕ) : Prop := (m.Prime ∧ m ≠ 2) ∨ m = 4 ∨ m = 8


theorem primePowerProd_pow (q : ℕ)
    (f : ∀ p ∈ q.primeFactors, DirichletCharacter ℂ (p ^ q.factorization p)) (k : ℕ) :
    primePowerProd q (fun p hp => f p hp ^ k) = primePowerProd q f ^ k := by
  unfold primePowerProd
  rw [← Finset.prod_pow]
  exact Finset.prod_congr rfl fun p _ => map_pow _ _ _

theorem primePowerProd_one (q : ℕ) :
    primePowerProd q (fun _ _ => 1) = 1 := by
  simp [primePowerProd]

/-- The conductor of a product of characters with pairwise coprime conductors. -/
theorem conductor_prod_of_coprime {N : ℕ} [NeZero N] {ι : Type*} (s : Finset ι)
    (g : ι → DirichletCharacter ℂ N)
    (h : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → (g i).conductor.Coprime (g j).conductor) :
    (∏ i ∈ s, g i).conductor = ∏ i ∈ s, (g i).conductor := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using conductor_one
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have ih' := ih fun i hi j hj hij =>
      h i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij
    rw [← ih']
    refine NTKB.conductor_mul_of_coprime ?_
    rw [ih']
    refine Nat.Coprime.prod_right fun i hi => ?_
    exact h a (Finset.mem_insert_self a s) i (Finset.mem_insert_of_mem hi)
      (fun hai => ha (hai ▸ hi))

theorem conductor_primePowerProd (q : ℕ) [NeZero q]
    (f : ∀ p ∈ q.primeFactors, DirichletCharacter ℂ (p ^ q.factorization p)) :
    (primePowerProd q f).conductor = ∏ p ∈ q.primeFactors.attach, (f p.1 p.2).conductor := by
  unfold primePowerProd
  have hne : ∀ p ∈ q.primeFactors, NeZero (p ^ q.factorization p) := fun p hp =>
    ⟨pow_ne_zero _ (Nat.prime_of_mem_primeFactors hp).ne_zero⟩
  rw [conductor_prod_of_coprime]
  · refine Finset.prod_congr rfl fun p _ => ?_
    have := hne p.1 p.2
    exact conductor_changeLevel _ _
  · intro i _ j _ hij
    have hi := hne i.1 i.2
    have hj := hne j.1 j.2
    rw [conductor_changeLevel, conductor_changeLevel]
    have hcop : (i.1 ^ q.factorization i.1).Coprime (j.1 ^ q.factorization j.1) :=
      Nat.Coprime.pow _ _ ((Nat.coprime_primes (Nat.prime_of_mem_primeFactors i.2)
        (Nat.prime_of_mem_primeFactors j.2)).mpr (fun h => hij (Subtype.ext h)))
    exact (hcop.coprime_dvd_left (conductor_dvd_level _)).coprime_dvd_right (conductor_dvd_level _)

/-- A product over the prime powers of `q` is primitive iff every factor is. -/
theorem isPrimitive_primePowerProd_iff (q : ℕ) [NeZero q]
    (f : ∀ p ∈ q.primeFactors, DirichletCharacter ℂ (p ^ q.factorization p)) :
    (primePowerProd q f).IsPrimitive ↔ ∀ p (hp : p ∈ q.primeFactors), (f p hp).IsPrimitive := by
  have hne : ∀ p ∈ q.primeFactors, NeZero (p ^ q.factorization p) := fun p hp =>
    ⟨pow_ne_zero _ (Nat.prime_of_mem_primeFactors hp).ne_zero⟩
  have hq : ∏ p ∈ q.primeFactors.attach, p.1 ^ q.factorization p.1 = q := by
    rw [Finset.prod_attach q.primeFactors (fun p => p ^ q.factorization p)]
    exact (Nat.prod_primeFactors_pow_factorization (NeZero.ne q)).symm
  rw [isPrimitive_def, conductor_primePowerProd]
  constructor
  · intro h p hp
    have _ := hne p hp
    rw [isPrimitive_def]
    by_contra hlt
    have hdvd : ∀ i ∈ q.primeFactors.attach,
        (f i.1 i.2).conductor ≤ i.1 ^ q.factorization i.1 := fun i _ =>
      have := hne i.1 i.2
      Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne _)) (conductor_dvd_level _)
    have := Finset.prod_lt_prod₀ (s := q.primeFactors.attach)
      (f := fun i => (f i.1 i.2).conductor) (g := fun i => i.1 ^ q.factorization i.1)
      (fun i _ => by
        have := hne i.1 i.2
        exact Nat.pos_of_ne_zero (conductor_ne_zero (f i.1 i.2))) hdvd
      ⟨⟨p, hp⟩, Finset.mem_attach _ _, lt_of_le_of_ne (hdvd ⟨p, hp⟩ (Finset.mem_attach _ _)) hlt⟩
    rw [h, hq] at this
    exact lt_irrefl _ this
  · intro h
    exact (Finset.prod_congr rfl fun i _ => (isPrimitive_def _).mp (h i.1 i.2)).trans hq


/-- The number of real primitive characters modulo a basic modulus: two for `8`, one otherwise. -/
theorem card_local (n : ℕ) (hn : IsBasicModulus n) :
    Nat.card {χ : DirichletCharacter ℂ n // χ.IsPrimitive ∧ χ.IsQuadratic} =
      if n = 8 then 2 else 1 := by
  rcases hn with ⟨hpr, h2⟩ | rfl | rfl
  · have : Fact n.Prime := ⟨hpr⟩
    have hn8 : n ≠ 8 := by rintro rfl; exact absurd hpr (by decide)
    simp only [hn8, ↓reduceIte]
    have hprim : (legendreChar n).IsPrimitive := by
      rw [← jacobiChar_prime]; exact isPrimitive_jacobiChar_prime n h2
    have : Nonempty {χ : DirichletCharacter ℂ n // χ.IsPrimitive ∧ χ.IsQuadratic} :=
      ⟨⟨legendreChar n, hprim, legendreChar_isQuadratic⟩⟩
    have : Subsingleton {χ : DirichletCharacter ℂ n // χ.IsPrimitive ∧ χ.IsQuadratic} := by
      refine ⟨fun a b => Subtype.ext ?_⟩
      have key : ∀ c : {χ : DirichletCharacter ℂ n // χ.IsPrimitive ∧ χ.IsQuadratic},
          c.1 = legendreChar n := by
        intro c
        refine eq_legendreChar_of_isQuadratic h2 c.2.2 ?_
        intro h1
        have := c.2.1
        rw [h1, isPrimitive_def, conductor_one] at this
        exact hpr.one_lt.ne this
      rw [key a, key b]
    exact Nat.card_unique
  · simp only [show (4 : ℕ) ≠ 8 by norm_num, ↓reduceIte]
    have : Nonempty {χ : DirichletCharacter ℂ 4 // χ.IsPrimitive ∧ χ.IsQuadratic} :=
      ⟨⟨chi4, isPrimitive_chi4, ZMod.isQuadratic_χ₄.comp _⟩⟩
    have : Subsingleton {χ : DirichletCharacter ℂ 4 // χ.IsPrimitive ∧ χ.IsQuadratic} :=
      ⟨fun a b => Subtype.ext ((eq_chi4_of_isPrimitive a.2.2 a.2.1).trans
        (eq_chi4_of_isPrimitive b.2.2 b.2.1).symm)⟩
    exact Nat.card_unique
  · simp only [↓reduceIte]
    rw [Nat.card_eq_two_iff]
    have hne : (chi8 : DirichletCharacter ℂ 8) ≠ chi8' := by
      intro h
      have := congrArg (fun χ : DirichletCharacter ℂ 8 => χ (-1)) h
      simp only [chi8_neg_one, chi8'_neg_one] at this
      norm_num at this
    refine ⟨⟨chi8, isPrimitive_chi8, ZMod.isQuadratic_χ₈.comp _⟩,
      ⟨chi8', isPrimitive_chi8', ZMod.isQuadratic_χ₈'.comp _⟩, ?_, ?_⟩
    · intro h; exact hne (congrArg Subtype.val h)
    · ext ⟨c, hc1, hc2⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true, Subtype.mk.injEq]
      exact eq_chi8_or_eq_chi8'_of_isPrimitive hc2 hc1

/-- A product over the prime powers of `q` is real iff every factor is. -/
theorem isQuadratic_primePowerProd_iff (q : ℕ) [NeZero q]
    (f : ∀ p ∈ q.primeFactors, DirichletCharacter ℂ (p ^ q.factorization p)) :
    (primePowerProd q f).IsQuadratic ↔ ∀ p (hp : p ∈ q.primeFactors), (f p hp).IsQuadratic := by
  simp only [MulChar.isQuadratic_iff_sq_eq_one]
  constructor
  · intro h p hp
    have h1 : primePowerProd q (fun p hp => f p hp ^ 2) = primePowerProd q (fun _ _ => 1) := by
      rw [primePowerProd_pow, primePowerProd_one]; exact h
    have := (primePowerProd_bijective q).1 h1
    exact congrFun (congrFun this p) hp
  · intro h
    rw [← primePowerProd_pow, ← primePowerProd_one]
    congr 1
    funext p hp
    exact h p hp

/-- **Davenport, Ch. 5, p. 38 (row 5-9)**: for such `q` there are two real primitive characters
if `8 ∣ q` and one otherwise. -/
@[kb "davenport1980" "Ch 5, p. 38"]
theorem card_isPrimitive_isQuadratic (q : ℕ) [NeZero q]
    (hq : ∀ p ∈ q.primeFactors, IsBasicModulus (p ^ q.factorization p)) :
    Nat.card {χ : DirichletCharacter ℂ q // χ.IsPrimitive ∧ χ.IsQuadratic} =
      if 8 ∣ q then 2 else 1 := by
  have hne : ∀ p ∈ q.primeFactors, NeZero (p ^ q.factorization p) := fun p hp =>
    ⟨pow_ne_zero _ (Nat.prime_of_mem_primeFactors hp).ne_zero⟩
  let e := Equiv.ofBijective (primePowerProd q) (primePowerProd_bijective q)
  let e0 : (∀ p ∈ q.primeFactors, DirichletCharacter ℂ (p ^ q.factorization p)) ≃
      ((p : q.primeFactors) → DirichletCharacter ℂ (p.1 ^ q.factorization p.1)) :=
    { toFun := fun f p => f p.1 p.2
      invFun := fun g p hp => g ⟨p, hp⟩
      left_inv := fun f => rfl
      right_inv := fun g => rfl }
  have e1 : {χ : DirichletCharacter ℂ q // χ.IsPrimitive ∧ χ.IsQuadratic} ≃
      {g : (p : q.primeFactors) → DirichletCharacter ℂ (p.1 ^ q.factorization p.1) //
        ∀ p, (g p).IsPrimitive ∧ (g p).IsQuadratic} :=
    (Equiv.subtypeEquiv e (p := fun f => ∀ p (hp : p ∈ q.primeFactors),
        (f p hp).IsPrimitive ∧ (f p hp).IsQuadratic)
      (q := fun χ => χ.IsPrimitive ∧ χ.IsQuadratic) (fun f => by
        show _ ↔ (primePowerProd q f).IsPrimitive ∧ (primePowerProd q f).IsQuadratic
        rw [isPrimitive_primePowerProd_iff, isQuadratic_primePowerProd_iff]
        simp only [forall_and])).symm.trans
      (Equiv.subtypeEquiv e0 (p := fun f => ∀ p (hp : p ∈ q.primeFactors),
        (f p hp).IsPrimitive ∧ (f p hp).IsQuadratic)
      (q := fun g => ∀ p, (g p).IsPrimitive ∧ (g p).IsQuadratic)
      (fun f => ⟨fun h (p : q.primeFactors) => h p.1 p.2, fun h p hp => h ⟨p, hp⟩⟩))
  rw [Nat.card_congr (e1.trans (Equiv.subtypePiEquivPi (p := fun (a : q.primeFactors)
    (b : DirichletCharacter ℂ (a.1 ^ q.factorization a.1)) => b.IsPrimitive ∧ b.IsQuadratic))), Nat.card_pi]
  have hloc : ∀ p : q.primeFactors,
      Nat.card {χ : DirichletCharacter ℂ (p.1 ^ q.factorization p.1) //
        χ.IsPrimitive ∧ χ.IsQuadratic} = if p.1 ^ q.factorization p.1 = 8 then 2 else 1 :=
    fun p => card_local _ (hq p.1 p.2)
  simp only [hloc]
  have h8of : ∀ p ∈ q.primeFactors, p ^ q.factorization p = 8 → p = 2 ∧ 8 ∣ q := by
    intro p hp h
    have hp2 : p ∣ 2 ^ 3 := by
      rw [show (2 : ℕ) ^ 3 = 8 by norm_num, ← h]
      exact dvd_pow_self p (Nat.pos_iff_ne_zero.mp
        (Nat.pos_of_mem_primeFactors hp |> fun _ => (Nat.Prime.factorization_pos_of_dvd
          (Nat.prime_of_mem_primeFactors hp) (NeZero.ne q) (Nat.dvd_of_mem_primeFactors hp))))
    have := (Nat.prime_dvd_prime_iff_eq (Nat.prime_of_mem_primeFactors hp) Nat.prime_two).mp
      ((Nat.prime_of_mem_primeFactors hp).dvd_of_dvd_pow hp2)
    exact ⟨this, h ▸ Nat.ordProj_dvd q p⟩
  by_cases h8 : 8 ∣ q
  · simp only [h8, ↓reduceIte]
    have h2mem : 2 ∈ q.primeFactors :=
      Nat.mem_primeFactors.mpr ⟨Nat.prime_two, (show 2 ∣ 8 by norm_num).trans h8, NeZero.ne q⟩
    have h2v : 2 ^ q.factorization 2 = 8 := by
      have h3 : 3 ≤ q.factorization 2 :=
        (Nat.prime_two.pow_dvd_iff_le_factorization (NeZero.ne q)).mp (by simpa using h8)
      have h8d : 8 ∣ 2 ^ q.factorization 2 := by
        rw [show (8 : ℕ) = 2 ^ 3 by norm_num]; exact pow_dvd_pow 2 h3
      rcases hq 2 h2mem with ⟨hpr, _⟩ | h4 | h8'
      · rcases (Nat.Prime.eq_one_or_self_of_dvd hpr 8 h8d) with h | h
        · omega
        · exact h.symm
      · rw [h4] at h8d; omega
      · exact h8'
    rw [Finset.prod_eq_single ⟨2, h2mem⟩]
    · simp [h2v]
    · intro b _ hb
      rw [ite_eq_right_iff]
      intro h
      exact (hb (Subtype.ext (h8of b.1 b.2 h).1)).elim
    · simp
  · simp only [h8, ↓reduceIte]
    refine Finset.prod_eq_one fun b _ => ?_
    rw [ite_eq_right_iff]
    intro h
    exact (h8 (h8of b.1 b.2 h).2).elim


/-- **Davenport, Ch. 5, p. 38 (row 5-9)**: a real primitive character modulo `q` exists iff `q`
is a product of pairwise coprime basic moduli (every `p^{v_p(q)}` is an odd prime, `4` or `8`). -/
@[kb "davenport1980" "Ch 5, p. 38"]
theorem exists_isPrimitive_isQuadratic_iff (q : ℕ) [NeZero q] :
    (∃ χ : DirichletCharacter ℂ q, χ.IsPrimitive ∧ χ.IsQuadratic) ↔
      ∀ p ∈ q.primeFactors, IsBasicModulus (p ^ q.factorization p) := by
  constructor
  · rintro ⟨χ, hprim, hquad⟩ p hp
    obtain ⟨f, rfl⟩ := (primePowerProd_bijective q).2 χ
    have h1 := (isPrimitive_primePowerProd_iff q f).mp hprim p hp
    have h2 := (isQuadratic_primePowerProd_iff q f).mp hquad p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hv : 1 ≤ q.factorization p :=
      hpp.factorization_pos_of_dvd (NeZero.ne q) (Nat.dvd_of_mem_primeFactors hp)
    by_cases hp2 : p = 2
    · subst hp2
      rcases two_or_three_of_isPrimitive_of_isQuadratic_two_pow hv h2 h1 with h | h <;>
        rw [h] <;> simp [IsBasicModulus]
    · have := eq_one_of_isPrimitive_of_isQuadratic_odd hpp hp2 hv h2 h1
      rw [this, pow_one]
      exact Or.inl ⟨hpp, hp2⟩
  · intro hq
    have hpos : 0 < Nat.card {χ : DirichletCharacter ℂ q // χ.IsPrimitive ∧ χ.IsQuadratic} := by
      rw [card_isPrimitive_isQuadratic q hq]; split_ifs <;> norm_num
    obtain ⟨⟨χ, h⟩⟩ := (Nat.card_pos_iff.mp hpos).1
    exact ⟨χ, h⟩

end NTKB.Davenport
