/- Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license. -/
import NTKB.Attr
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.DirichletCharacter.GaussSum
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

/-!
# The Gauss sum of an imprimitive character (Davenport, Chapter 9, p. 67)

**9-5**: if `χ` mod `q` is induced by the primitive character `χ₁` mod `q₁` (here `q₁` is the
conductor of `χ` and `χ₁ = χ.primitiveCharacter`), then `τ(χ) = μ(q/q₁) χ₁(q/q₁) τ(χ₁)`
(`gaussSum_eq_moebius_mul_primitiveCharacter`), where `τ(χ) = ∑_{m mod q} χ(m) e(m/q)`.
-/

open scoped ArithmeticFunction.Moebius

namespace NTKB.Davenport

open DirichletCharacter

lemma isUnit_castHom_iff {M p : ℕ} [NeZero M] [NeZero p] (a : ZMod (M * p)) :
    IsUnit a ↔ IsUnit (ZMod.castHom (dvd_mul_right M p) (ZMod M) a) ∧
      IsUnit (ZMod.castHom (dvd_mul_left p M) (ZMod p) a) := by
  obtain ⟨n, rfl⟩ := ZMod.natCast_zmod_surjective a
  simp only [map_natCast, ZMod.isUnit_iff_coprime, Nat.coprime_mul_iff_right]

lemma isUnit_of_castHom_of_dvd {M p : ℕ} [NeZero M] [NeZero p] (hpM : p ∣ M)
    (a : ZMod (M * p)) (h : IsUnit (ZMod.castHom (dvd_mul_right M p) (ZMod M) a)) : IsUnit a := by
  obtain ⟨n, rfl⟩ := ZMod.natCast_zmod_surjective a
  rw [map_natCast, ZMod.isUnit_iff_coprime] at h
  rw [ZMod.isUnit_iff_coprime, Nat.coprime_mul_iff_right]
  exact ⟨h, h.coprime_dvd_right hpM⟩

lemma changeLevel_apply_castHom {M p : ℕ} [NeZero M] [NeZero p] (ψ : DirichletCharacter ℂ M)
    (a : ZMod (M * p)) (ha : IsUnit a) :
    changeLevel (dvd_mul_right M p) ψ a = ψ (ZMod.castHom (dvd_mul_right M p) (ZMod M) a) := by
  have := changeLevel_eq_cast_of_dvd ψ (dvd_mul_right M p) ha.unit
  simpa [ZMod.castHom_apply] using this

lemma gaussSum_changeLevel_of_dvd {M p : ℕ} [NeZero M] (hp : p.Prime) (hpM : p ∣ M)
    [NeZero (M * p)] (ψ : DirichletCharacter ℂ M) :
    gaussSum (changeLevel (dvd_mul_right M p) ψ) (ZMod.stdAddChar : AddChar (ZMod (M * p)) ℂ) =
      0 := by
  have : NeZero p := ⟨hp.ne_zero⟩
  set χ := changeLevel (dvd_mul_right M p) ψ with hχ
  have hχa : ∀ a : ZMod (M * p),
      χ a = ψ (ZMod.castHom (dvd_mul_right M p) (ZMod M) a) := by
    intro a
    by_cases ha : IsUnit a
    · exact changeLevel_apply_castHom ψ a ha
    · rw [MulChar.map_nonunit _ ha]
      symm
      apply MulChar.map_nonunit
      exact fun h => ha (isUnit_of_castHom_of_dvd hpM a h)
  have hec : (ZMod.stdAddChar : AddChar (ZMod (M * p)) ℂ) (M : ZMod (M * p)) ≠ 1 := by
    intro h
    have h2 := ZMod.injective_stdAddChar (N := M * p)
      (h.trans (AddChar.map_zero_eq_one _).symm)
    rw [ZMod.natCast_eq_zero_iff] at h2
    have h3 := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne M)) h2
    have := hp.two_le
    have := Nat.pos_of_ne_zero (NeZero.ne M)
    nlinarith
  have key : gaussSum χ (ZMod.stdAddChar : AddChar (ZMod (M * p)) ℂ) =
      (ZMod.stdAddChar : AddChar (ZMod (M * p)) ℂ) (M : ZMod (M * p)) *
        gaussSum χ (ZMod.stdAddChar : AddChar (ZMod (M * p)) ℂ) := by
    unfold gaussSum
    refine (Equiv.sum_comp (Equiv.addRight (M : ZMod (M * p)))
      (fun a => χ a * (ZMod.stdAddChar : AddChar (ZMod (M * p)) ℂ) a)).symm.trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [Equiv.coe_addRight, AddChar.map_add_eq_mul, hχa, map_add, map_natCast,
      ZMod.natCast_self, add_zero]
    ring
  have : (1 - (ZMod.stdAddChar : AddChar (ZMod (M * p)) ℂ) (M : ZMod (M * p))) *
      gaussSum χ (ZMod.stdAddChar : AddChar (ZMod (M * p)) ℂ) = 0 := by
    rw [sub_mul, one_mul, ← key, sub_self]
  rcases mul_eq_zero.1 this with h | h
  · exact absurd (sub_eq_zero.1 h).symm hec
  · exact h

lemma gaussSum_changeLevel_of_not_dvd {M p : ℕ} [NeZero M] (hp : p.Prime) (hpM : ¬ p ∣ M)
    [NeZero (M * p)] (ψ : DirichletCharacter ℂ M) :
    gaussSum (changeLevel (dvd_mul_right M p) ψ) (ZMod.stdAddChar : AddChar (ZMod (M * p)) ℂ) =
      - ψ (p : ZMod M) * gaussSum ψ (ZMod.stdAddChar : AddChar (ZMod M) ℂ) := by
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have hcop : Nat.Coprime M p := ((Nat.Prime.coprime_iff_not_dvd hp).2 hpM).symm
  obtain ⟨s, t, hst⟩ : ∃ s t : ℤ, s * M + t * p = 1 := Nat.isCoprime_iff_coprime.2 hcop
  set χ := changeLevel (dvd_mul_right M p) ψ with hχ
  set f := (ZMod.chineseRemainder hcop).toEquiv with hfdef
  set cM := ZMod.castHom (dvd_mul_right M p) (ZMod M) with hcM
  set cp := ZMod.castHom (dvd_mul_left p M) (ZMod p) with hcp
  have hf : ∀ a, f a = (cM a, cp a) := by
    intro a
    ext
    · simp [hfdef, hcM, ZMod.chineseRemainder]
    · simp [hfdef, hcp, ZMod.chineseRemainder]
  have hA : ∀ a : ZMod (M * p), (ZMod.stdAddChar a : ℂ) =
      ZMod.stdAddChar ((s : ZMod p) * cp a) * ZMod.stdAddChar ((t : ZMod M) * cM a) := by
    intro a
    obtain ⟨n, rfl⟩ := ZMod.intCast_surjective a
    simp only [hcM, hcp, map_intCast]
    rw [← Int.cast_mul, ← Int.cast_mul, ZMod.stdAddChar_coe, ZMod.stdAddChar_coe,
      ZMod.stdAddChar_coe, ← Complex.exp_add]
    congr 1
    have hM : (M : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne M
    have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have h : (s : ℂ) * M + t * p = 1 := by exact_mod_cast hst
    push_cast
    field_simp
    linear_combination (-(n : ℂ)) * h
  have hχa : ∀ a, χ a = ψ (cM a) * (1 : DirichletCharacter ℂ p) (cp a) := by
    intro a
    by_cases ha : IsUnit a
    · have hu := (isUnit_castHom_iff a).1 ha
      rw [changeLevel_apply_castHom ψ a ha, MulChar.one_apply hu.2, mul_one]
    · rw [MulChar.map_nonunit _ ha]
      by_cases hM : IsUnit (cM a)
      · have : ¬ IsUnit (cp a) := fun h => ha ((isUnit_castHom_iff a).2 ⟨hM, h⟩)
        rw [MulChar.map_nonunit _ this, mul_zero]
      · rw [MulChar.map_nonunit _ hM, zero_mul]
  have hsum : gaussSum χ (ZMod.stdAddChar : AddChar (ZMod (M * p)) ℂ) =
      gaussSum ψ ((ZMod.stdAddChar : AddChar (ZMod M) ℂ).mulShift (t : ZMod M)) *
        gaussSum (1 : DirichletCharacter ℂ p)
          ((ZMod.stdAddChar : AddChar (ZMod p) ℂ).mulShift (s : ZMod p)) := by
    unfold gaussSum
    rw [Finset.sum_mul_sum, ← Fintype.sum_prod_type']
    rw [← Equiv.sum_comp f.symm]
    refine Finset.sum_congr rfl fun z _ => ?_
    obtain ⟨x, y⟩ := z
    have h0 := f.apply_symm_apply (x, y)
    rw [hf] at h0
    have h1 : cM (f.symm (x, y)) = x := (Prod.ext_iff.1 h0).1
    have h2 : cp (f.symm (x, y)) = y := (Prod.ext_iff.1 h0).2
    rw [hχa, hA, h1, h2]
    simp only [AddChar.mulShift_apply]
    ring
  have h1 : gaussSum (1 : DirichletCharacter ℂ p)
      ((ZMod.stdAddChar : AddChar (ZMod p) ℂ).mulShift (s : ZMod p)) = -1 := by
    apply gaussSum_one_left
    have hs0 : (s : ZMod p) ≠ 0 := by
      intro h
      have := congrArg (Int.cast : ℤ → ZMod p) hst
      push_cast at this
      simp [h] at this
    exact ZMod.isPrimitive_stdAddChar p hs0
  have ht : (t : ZMod M) * (p : ZMod M) = 1 := by
    have := congrArg (Int.cast : ℤ → ZMod M) hst
    push_cast at this
    simpa using this
  have h2 : gaussSum ψ ((ZMod.stdAddChar : AddChar (ZMod M) ℂ).mulShift (t : ZMod M)) =
      ψ (p : ZMod M) * gaussSum ψ (ZMod.stdAddChar : AddChar (ZMod M) ℂ) := by
    let u : (ZMod M)ˣ := ⟨(t : ZMod M), (p : ZMod M), ht, by rw [mul_comm]; exact ht⟩
    have hu : ψ (t : ZMod M) * ψ (p : ZMod M) = 1 := by rw [← map_mul, ht, map_one]
    have := gaussSum_mulShift ψ (ZMod.stdAddChar : AddChar (ZMod M) ℂ) u
    calc _ = ψ (p : ZMod M) * (ψ (t : ZMod M) *
          gaussSum ψ ((ZMod.stdAddChar : AddChar (ZMod M) ℂ).mulShift (t : ZMod M))) := by
          rw [← mul_assoc, mul_comm (ψ (p : ZMod M)), hu, one_mul]
      _ = _ := by rw [show ψ (t : ZMod M) * gaussSum ψ
          ((ZMod.stdAddChar : AddChar (ZMod M) ℂ).mulShift (t : ZMod M)) = _ from this]
  rw [hsum, h1, h2]
  ring

lemma gaussSum_changeLevel_mul {N : ℕ} [NeZero N] (χ₁ : DirichletCharacter ℂ N) :
    ∀ (r : ℕ) (M : ℕ) [NeZero M] (_ : r ≠ 0) (_ : M = N * r) (hd : N ∣ M),
      gaussSum (changeLevel hd χ₁) (ZMod.stdAddChar : AddChar (ZMod M) ℂ) =
        (μ r : ℂ) * χ₁ (r : ZMod N) * gaussSum χ₁ (ZMod.stdAddChar : AddChar (ZMod N) ℂ) := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
  intro M _ hr hM hd
  by_cases hr1 : r = 1
  · subst hr1
    have : M = N := by simpa using hM
    subst this
    simp [changeLevel_self]
  · have hp : r.minFac.Prime := Nat.minFac_prime hr1
    obtain ⟨r', hr'⟩ : r.minFac ∣ r := Nat.minFac_dvd r
    generalize r.minFac = p at hp hr'
    have hr'0 : r' ≠ 0 := by
      rintro rfl
      simp at hr'
      exact hr hr'
    have : NeZero r' := ⟨hr'0⟩
    have : NeZero (N * r') := ⟨mul_ne_zero (NeZero.ne N) hr'0⟩
    have hlt : r' < r := by
      rw [hr']
      have := hp.two_le
      have := Nat.pos_of_ne_zero hr'0
      nlinarith
    have hMe : M = N * r' * p := by rw [hM, hr']; ring
    have hd' : N ∣ N * r' := dvd_mul_right N r'
    have ih' := ih r' hlt (N * r') hr'0 rfl hd'
    subst hMe
    have hchain : changeLevel hd χ₁ =
        changeLevel (dvd_mul_right (N * r') p) (changeLevel hd' χ₁) :=
      changeLevel_trans χ₁ hd' (dvd_mul_right _ _)
    rw [hchain]
    by_cases hpM : p ∣ N * r'
    · rw [gaussSum_changeLevel_of_dvd hp hpM]
      symm
      rcases (Nat.Prime.dvd_mul hp).1 hpM with hN | hr''
      · have : χ₁ (r : ZMod N) = 0 := by
          apply MulChar.map_nonunit
          intro hu
          rw [hr'] at hu
          push_cast at hu
          have := isUnit_of_mul_isUnit_left hu
          rw [ZMod.isUnit_iff_coprime] at this
          exact (Nat.Prime.coprime_iff_not_dvd hp).1 this hN
        rw [this]; simp
      · have : μ r = 0 := by
          apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
          intro hsq
          obtain ⟨c, hc⟩ := hr''
          have : p * p ∣ r := ⟨c, by rw [hr', hc]; ring⟩
          exact hp.not_isUnit (hsq p this)
        rw [this]; simp
    · rw [gaussSum_changeLevel_of_not_dvd hp hpM, ih']
      have hcop : Nat.Coprime p r' :=
        (Nat.Prime.coprime_iff_not_dvd hp).2 (fun h => hpM (dvd_mul_of_dvd_right h N))
      have hcz : IsCoprime (p : ℤ) ((N * r' : ℕ) : ℤ) :=
        Nat.isCoprime_iff_coprime.2 ((Nat.Prime.coprime_iff_not_dvd hp).2 hpM)
      have hψp : changeLevel hd' χ₁ (p : ZMod (N * r')) = χ₁ (p : ZMod N) := by
        simpa using changeLevel_eq_cast_of_dvd' χ₁ hd' hcz
      rw [hψp, hr', ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop,
        ArithmeticFunction.moebius_apply_prime hp]
      push_cast
      rw [map_mul]
      ring

/-- **Davenport, Ch. 9, p. 67 (row 9-5)**: `τ(χ) = μ(q/q₁) χ₁(q/q₁) τ(χ₁)` for `χ` mod `q` induced
by the primitive `χ₁` mod `q₁`. -/
@[kb "davenport1980" "Ch 9, p. 67"]
theorem gaussSum_eq_moebius_mul_primitiveCharacter {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) :
    have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
    gaussSum χ ZMod.stdAddChar =
      (μ (q / χ.conductor) : ℂ) * χ.primitiveCharacter (q / χ.conductor : ℕ) *
        gaussSum χ.primitiveCharacter ZMod.stdAddChar := by
  have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have h := gaussSum_changeLevel_mul χ.primitiveCharacter (q / χ.conductor) q
    (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) χ.conductor_dvd_level)
      (Nat.pos_of_ne_zero χ.conductor_ne_zero)).ne'
    (by rw [Nat.mul_div_cancel' χ.conductor_dvd_level]) χ.conductor_dvd_level
  rw [changeLevel_primitiveCharacter] at h
  exact h

end NTKB.Davenport
