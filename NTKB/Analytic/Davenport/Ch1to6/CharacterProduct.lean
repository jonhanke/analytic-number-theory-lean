/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Analysis.Complex.Polynomial.Basic
import NTKB.Attr

/-!
# Characters modulo `q` as products over the prime powers of `q` (Davenport, Chapter 4, row 4-4)

For coprime `m`, `n`, every character modulo `mn` is `χ₁ χ₂` (lifted) for exactly one pair of
characters `χ₁` modulo `m` and `χ₂` modulo `n` (`existsUnique_mul_changeLevel`). For `q ≥ 1`, the
map `(χ_p)_{p ∣ q} ↦ ∏_p χ_p` from families of characters modulo the prime powers
`p^{v_p(q)}` to the characters modulo `q` is a bijection (`primePowerProd_bijective`); their number
is `φ(q)` (`natCard_dirichletCharacter`: Mathlib `DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity`).
Tau Ceti's Conrey labelling builds the characters in the same way; no code is taken from it.

Source text unavailable; written from the map row 4-4.
-/

open DirichletCharacter

namespace NTKB.Davenport


theorem crt_units {a b : ℕ} [NeZero a] [NeZero b] (h : a.Coprime b) (x : (ZMod a)ˣ) :
    ∃ u : (ZMod (a * b))ˣ, ZMod.unitsMap (dvd_mul_right a b) u = x ∧
      ZMod.unitsMap (dvd_mul_left b a) u = 1 := by
  let e := ZMod.chineseRemainder h
  have key : ∀ r, e r = (ZMod.castHom (dvd_mul_right a b) (ZMod a) r,
      ZMod.castHom (dvd_mul_left b a) (ZMod b) r) := fun r => by
    ext
    · exact congrFun (congrArg DFunLike.coe (RingHom.ext_zmod ((RingHom.fst _ _).comp e.toRingHom)
        (ZMod.castHom (dvd_mul_right a b) (ZMod a)))) r
    · exact congrFun (congrArg DFunLike.coe (RingHom.ext_zmod ((RingHom.snd _ _).comp e.toRingHom)
        (ZMod.castHom (dvd_mul_left b a) (ZMod b)))) r
  obtain ⟨u, hu⟩ := (Units.mapEquiv e.toMulEquiv).surjective (MulEquiv.prodUnits.symm (x, 1))
  have hp : ((MulEquiv.prodUnits.symm (x, 1) : (ZMod a × ZMod b)ˣ) : ZMod a × ZMod b) = ((x : ZMod a), (1 : ZMod b)) := rfl
  refine ⟨u, ?_, ?_⟩
  · ext
    have := congrArg (fun w : (ZMod a × ZMod b)ˣ => ((w : ZMod a × ZMod b)).1) hu
    simpa [key, ZMod.unitsMap_val, hp] using this
  · ext
    have := congrArg (fun w : (ZMod a × ZMod b)ˣ => ((w : ZMod a × ZMod b)).2) hu
    simpa [key, ZMod.unitsMap_val, hp] using this

lemma changeLevel_unit {n m : ℕ} (hm : n ∣ m) (χ : DirichletCharacter ℂ n) (u : (ZMod m)ˣ) :
    changeLevel hm χ (u : ZMod m) = χ ((ZMod.unitsMap hm u : (ZMod n)ˣ) : ZMod n) := by
  simp [changeLevel_def]

theorem crt_units' {a b : ℕ} [NeZero a] [NeZero b] (h : a.Coprime b) (x : (ZMod b)ˣ) :
    ∃ u : (ZMod (a * b))ˣ, ZMod.unitsMap (dvd_mul_right a b) u = 1 ∧
      ZMod.unitsMap (dvd_mul_left b a) u = x := by
  let e := ZMod.chineseRemainder h
  have key : ∀ r, e r = (ZMod.castHom (dvd_mul_right a b) (ZMod a) r,
      ZMod.castHom (dvd_mul_left b a) (ZMod b) r) := fun r => by
    ext
    · exact congrFun (congrArg DFunLike.coe (RingHom.ext_zmod ((RingHom.fst _ _).comp e.toRingHom)
        (ZMod.castHom (dvd_mul_right a b) (ZMod a)))) r
    · exact congrFun (congrArg DFunLike.coe (RingHom.ext_zmod ((RingHom.snd _ _).comp e.toRingHom)
        (ZMod.castHom (dvd_mul_left b a) (ZMod b)))) r
  obtain ⟨u, hu⟩ := (Units.mapEquiv e.toMulEquiv).surjective (MulEquiv.prodUnits.symm (1, x))
  have hp : ((MulEquiv.prodUnits.symm (1, x) : (ZMod a × ZMod b)ˣ) : ZMod a × ZMod b) = ((1 : ZMod a), (x : ZMod b)) := rfl
  refine ⟨u, ?_, ?_⟩
  · ext
    have := congrArg (fun w : (ZMod a × ZMod b)ˣ => ((w : ZMod a × ZMod b)).1) hu
    simpa [key, ZMod.unitsMap_val, hp] using this
  · ext
    have := congrArg (fun w : (ZMod a × ZMod b)ˣ => ((w : ZMod a × ZMod b)).2) hu
    simpa [key, ZMod.unitsMap_val, hp] using this

lemma crt_aux {a b q : ℕ} [NeZero a] [NeZero b] (h : a.Coprime b) (hq : a * b = q) (ha : a ∣ q)
    (x : (ZMod a)ˣ) [NeZero q] :
    ∃ u : (ZMod q)ˣ, ZMod.unitsMap ha u = x ∧
      ∀ d (hd : d ∣ q), d ∣ b → ZMod.unitsMap hd u = 1 := by
  subst hq
  obtain ⟨u, h1, h2⟩ := crt_units h x
  refine ⟨u, h1, fun d hd hdb => ?_⟩
  have := congrArg (fun w => ZMod.unitsMap hdb w) h2
  simpa [← MonoidHom.comp_apply, ZMod.unitsMap_comp] using this

lemma prod_apply_aux {n : ℕ} {ι : Type*} (s : Finset ι) (g : ι → DirichletCharacter ℂ n) (a : (ZMod n)ˣ) :
    (∏ i ∈ s, g i) (a : ZMod n) = ∏ i ∈ s, g i (a : ZMod n) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [MulChar.one_apply a.isUnit]
  | insert i s hi ih => simp [Finset.prod_insert hi, ih]

lemma card_aux (q : ℕ) [NeZero q] :
    Nat.card (DirichletCharacter ℂ q) = q.totient :=
  DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q

/-- The product of characters modulo the prime powers `p^{v_p(q)}` of `q`, as a character modulo `q`. -/
noncomputable def primePowerProd (q : ℕ)
    (f : ∀ p ∈ q.primeFactors, DirichletCharacter ℂ (p ^ q.factorization p)) :
    DirichletCharacter ℂ q :=
  ∏ p ∈ q.primeFactors.attach, changeLevel (Nat.ordProj_dvd q p.1) (f p.1 p.2)

/-- **Davenport, Ch. 4, p. 28 (row 4-4)**, two coprime moduli: every character modulo `mn` is
`χ₁ χ₂` for exactly one pair `χ₁` modulo `m`, `χ₂` modulo `n`. -/
@[kb "davenport1980" "Ch 4, p. 28"]
theorem existsUnique_mul_changeLevel {m n : ℕ} [NeZero m] [NeZero n] (h : m.Coprime n)
    (χ : DirichletCharacter ℂ (m * n)) :
    ∃! p : DirichletCharacter ℂ m × DirichletCharacter ℂ n,
      changeLevel (dvd_mul_right m n) p.1 * changeLevel (dvd_mul_left n m) p.2 = χ := by
  have : NeZero (m * n) := ⟨mul_ne_zero (NeZero.ne m) (NeZero.ne n)⟩
  let Φ : DirichletCharacter ℂ m × DirichletCharacter ℂ n → DirichletCharacter ℂ (m * n) :=
    fun p => changeLevel (dvd_mul_right m n) p.1 * changeLevel (dvd_mul_left n m) p.2
  have hev : ∀ (p : DirichletCharacter ℂ m × DirichletCharacter ℂ n) (u : (ZMod (m * n))ˣ),
      Φ p (u : ZMod (m * n)) =
        p.1 ((ZMod.unitsMap (dvd_mul_right m n) u : (ZMod m)ˣ) : ZMod m) *
        p.2 ((ZMod.unitsMap (dvd_mul_left n m) u : (ZMod n)ˣ) : ZMod n) := by
    intro p u
    simp only [Φ, MulChar.mul_apply, changeLevel_unit]
  have hinj : Function.Injective Φ := by
    intro p p' hpp
    have e1 : p.1 = p'.1 := by
      refine MulChar.ext fun x => ?_
      obtain ⟨u, h1, h2⟩ := crt_units h x
      have := congrArg (fun χ => χ (u : ZMod (m * n))) hpp
      simp only [hev, h1, h2] at this
      simpa using this
    have e2 : p.2 = p'.2 := by
      refine MulChar.ext fun x => ?_
      obtain ⟨u, h1, h2⟩ := crt_units' h x
      have := congrArg (fun χ => χ (u : ZMod (m * n))) hpp
      simp only [hev, h1, h2] at this
      simpa using this
    exact Prod.ext e1 e2
  have hcard : Nat.card (DirichletCharacter ℂ (m * n)) ≤
      Nat.card (DirichletCharacter ℂ m × DirichletCharacter ℂ n) := by
    rw [Nat.card_prod, card_aux, card_aux, card_aux, Nat.totient_mul h]
  exact (hinj.bijective_of_nat_card_le hcard).existsUnique χ

/-- **Davenport, Ch. 4, p. 28 (row 4-4)**: the characters modulo `q` are the products of
characters modulo the prime powers of `q`, each in exactly one way. -/
@[kb "davenport1980" "Ch 4, p. 28"]
theorem primePowerProd_bijective (q : ℕ) [NeZero q] : Function.Bijective (primePowerProd q) := by
  have hq0 : q ≠ 0 := NeZero.ne q
  have hne : ∀ p ∈ q.primeFactors, NeZero (p ^ q.factorization p) := fun p hp =>
    ⟨pow_ne_zero _ (Nat.prime_of_mem_primeFactors hp).ne_zero⟩
  have hev : ∀ (f : ∀ p ∈ q.primeFactors, DirichletCharacter ℂ (p ^ q.factorization p))
      (u : (ZMod q)ˣ), primePowerProd q f (u : ZMod q) =
      ∏ p ∈ q.primeFactors.attach,
        f p.1 p.2 ((ZMod.unitsMap (Nat.ordProj_dvd q p.1) u : (ZMod (p.1 ^ q.factorization p.1))ˣ) :
          ZMod (p.1 ^ q.factorization p.1)) := by
    intro f u
    unfold primePowerProd
    rw [prod_apply_aux]
    exact Finset.prod_congr rfl fun p _ => changeLevel_unit _ _ _
  have hex : ∀ p0 ∈ q.primeFactors, ∀ x : (ZMod (p0 ^ q.factorization p0))ˣ,
      ∃ u : (ZMod q)ˣ, ZMod.unitsMap (Nat.ordProj_dvd q p0) u = x ∧
        ∀ p ∈ q.primeFactors, p ≠ p0 → ZMod.unitsMap (Nat.ordProj_dvd q p) u = 1 := by
    intro p0 hp0 x
    have hp0p := Nat.prime_of_mem_primeFactors hp0
    have := hne p0 hp0
    have : NeZero (q / p0 ^ q.factorization p0) :=
      ⟨(Nat.div_pos (Nat.ordProj_le p0 hq0) (Nat.ordProj_pos q p0)).ne'⟩
    obtain ⟨u, h1, h2⟩ := crt_aux (a := p0 ^ q.factorization p0) (b := q / p0 ^ q.factorization p0)
      (Nat.Coprime.pow_left _ (Nat.coprime_ordCompl hp0p hq0)) (Nat.ordProj_mul_ordCompl_eq_self q p0)
      (Nat.ordProj_dvd q p0) x
    refine ⟨u, h1, fun p hp hpp => h2 _ _ ?_⟩
    have hpp' := Nat.prime_of_mem_primeFactors hp
    have hcop : (p ^ q.factorization p).Coprime (p0 ^ q.factorization p0) :=
      Nat.Coprime.pow _ _ ((Nat.coprime_primes hpp' hp0p).mpr hpp)
    exact hcop.dvd_of_dvd_mul_left ((Nat.ordProj_mul_ordCompl_eq_self q p0).symm ▸ Nat.ordProj_dvd q p)
  have heval : ∀ (f : ∀ p ∈ q.primeFactors, DirichletCharacter ℂ (p ^ q.factorization p))
      (p0 : ℕ) (hp0 : p0 ∈ q.primeFactors) (x : (ZMod (p0 ^ q.factorization p0))ˣ)
      (u : (ZMod q)ˣ), ZMod.unitsMap (Nat.ordProj_dvd q p0) u = x →
      (∀ p ∈ q.primeFactors, p ≠ p0 → ZMod.unitsMap (Nat.ordProj_dvd q p) u = 1) →
      primePowerProd q f (u : ZMod q) = f p0 hp0 (x : ZMod _) := by
    intro f p0 hp0 x u h1 h2
    rw [hev, Finset.prod_eq_single_of_mem ⟨p0, hp0⟩ (Finset.mem_attach _ _)]
    · simp [h1]
    · intro b _ hb
      have hb' : b.1 ≠ p0 := fun h => hb (Subtype.ext h)
      simp [h2 b.1 b.2 hb']
  have hinj : Function.Injective (primePowerProd q) := by
    intro f g hfg
    funext p0 hp0
    refine MulChar.ext fun x => ?_
    obtain ⟨u, h1, h2⟩ := hex p0 hp0 x
    have := congrArg (fun χ => χ (u : ZMod q)) hfg
    simp only [heval f p0 hp0 x u h1 h2, heval g p0 hp0 x u h1 h2] at this
    exact this
  have hcard : Nat.card (DirichletCharacter ℂ q) ≤
      Nat.card (∀ p ∈ q.primeFactors, DirichletCharacter ℂ (p ^ q.factorization p)) := by
    let e : (∀ p ∈ q.primeFactors, DirichletCharacter ℂ (p ^ q.factorization p)) ≃
        ((p : q.primeFactors) → DirichletCharacter ℂ (p.1 ^ q.factorization p.1)) :=
      { toFun := fun f p => f p.1 p.2
        invFun := fun g p hp => g ⟨p, hp⟩
        left_inv := fun f => rfl
        right_inv := fun g => rfl }
    rw [Nat.card_congr e, Nat.card_pi, card_aux, Nat.totient_eq_prod_factorization hq0]
    rw [Finsupp.prod, Nat.support_factorization, ← Finset.prod_attach]
    refine le_of_eq (Finset.prod_congr rfl fun p _ => ?_)
    have := hne p.1 p.2
    rw [card_aux, Nat.totient_prime_pow (Nat.prime_of_mem_primeFactors p.2)
      (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp (by simp)))]
  exact ⟨hinj, (hinj.bijective_of_nat_card_le hcard).2⟩

/-- **Davenport, Ch. 4, p. 28 (row 4-4)**: there are `φ(q)` characters modulo `q`. -/
theorem natCard_dirichletCharacter (q : ℕ) [NeZero q] :
    Nat.card (DirichletCharacter ℂ q) = q.totient :=
  card_aux q

end NTKB.Davenport
