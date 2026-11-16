/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Davenport.Forms.Narrow
import NTKB.Elementary.QuadraticField.Classification
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.RingTheory.ClassGroup.ExtendedHom
import Mathlib.RingTheory.Norm.Basic
import Mathlib.Algebra.QuadraticAlgebra.NormDeterminant

/-!
# Davenport, Chapter 6: the form class number `h(d)` and the class number of the field

(§6, pp. 54, 62; rows 6-2, 6-22, 6-23.)

* `NTKB.Davenport.formClassNumber d`: Davenport's `h(d)`, the number of classes of forms of
  discriminant `d` under proper (unimodular) equivalence, positive definite forms only if `d < 0`
  (row 6-2). It is finite and at least `1` (`NTKB.Davenport.formClassNumber_pos`).
* `NTKB.Davenport.formClassNumber_eq_card_narrowClass`: for a fundamental `D ≠ 1`, `h(D)` is the
  number of narrow ideal classes (row 6-22).
* Row 6-23 for a quadratic number field `K` of discriminant `d` (`h_1(d)` = `classNumber K`):
  `h(d) = h_1(d)` if `d < 0` (`NTKB.Davenport.formClassNumber_eq_classNumber_of_discr_neg`) or if
  `d > 0` and there is a unit of norm `-1`
  (`NTKB.Davenport.formClassNumber_eq_classNumber_of_exists_norm_eq_neg_one`), and
  `h(d) = 2 h_1(d)` otherwise (`NTKB.Davenport.formClassNumber_eq_two_mul_classNumber`).
-/

noncomputable section

open QuadraticAlgebra NTKB.QuadraticField NumberField
open scoped nonZeroDivisors

namespace NTKB.Davenport

/-! ### Davenport's `h(d)` (row 6-2) -/

/-- Davenport's forms of discriminant `d`: all of them if `d > 0`, the positive definite ones
(`a > 0`) if `d < 0`. -/
def DavForm (d : ℤ) := {f : ℤ × ℤ × ℤ // formDisc f = d ∧ (d < 0 → 0 < f.1)}

instance davFormSetoid (d : ℤ) : Setoid (DavForm d) where
  r f g := FormEquiv f.1 g.1
  iseqv := ⟨fun _ ↦ FormEquiv.refl _, FormEquiv.symm, FormEquiv.trans⟩

/-- Proper classes of forms of discriminant `d` (positive definite if `d < 0`). -/
def FormClass (d : ℤ) := Quotient (davFormSetoid d)

/-- **Davenport §6, p. 54 (row 6-2).** The form class number `h(d)`: the number of classes of
forms of discriminant `d` under proper equivalence, positive definite forms if `d < 0`. -/
def formClassNumber (d : ℤ) : ℕ := Nat.card (FormClass d)

theorem sq_pos_of_ne {x : ℤ} (hx : x ≠ 0) : 0 < x ^ 2 :=
  lt_of_le_of_ne (sq_nonneg x) (Ne.symm (pow_ne_zero 2 hx))

/-- An equivalent form of a positive definite form is positive definite. -/
theorem formEquiv_pos {f g : ℤ × ℤ × ℤ} (hd : formDisc f < 0) (ha : 0 < f.1) (h : FormEquiv f g) :
    0 < g.1 := by
  obtain ⟨α, β, γ, δ, h1, rfl⟩ := h
  simp only [formSubst]
  simp only [formDisc] at hd
  have hne : α ≠ 0 ∨ γ ≠ 0 := by
    by_contra h; push_neg at h; rw [h.1, h.2] at h1; simp at h1
  -- `4a · f(α, γ) = (2aα + bγ)² - d γ²`
  have key : 4 * f.1 * (f.1 * α ^ 2 + f.2.1 * α * γ + f.2.2 * γ ^ 2) =
      (2 * f.1 * α + f.2.1 * γ) ^ 2 - (f.2.1 ^ 2 - 4 * f.1 * f.2.2) * γ ^ 2 := by ring
  rcases hne with hα | hγ
  · by_cases hγ : γ = 0
    · subst hγ; simp only [mul_zero, add_zero, zero_pow two_ne_zero]
      exact mul_pos ha (sq_pos_of_ne hα)
    · have : 0 < 4 * f.1 * (f.1 * α ^ 2 + f.2.1 * α * γ + f.2.2 * γ ^ 2) := by
        rw [key]; nlinarith [sq_nonneg (2 * f.1 * α + f.2.1 * γ), sq_pos_of_ne hγ]
      exact pos_of_mul_pos_right this (by linarith)
  · have : 0 < 4 * f.1 * (f.1 * α ^ 2 + f.2.1 * α * γ + f.2.2 * γ ^ 2) := by
      rw [key]; nlinarith [sq_nonneg (2 * f.1 * α + f.2.1 * γ), sq_pos_of_ne hγ]
    exact pos_of_mul_pos_right this (by linarith)

/-- **Davenport §6, p. 54.** For `d > 0` not a square every form of discriminant `d` is equivalent
to one with `a > 0`: a reduced form `|b| ≤ |a| ≤ |c|` has `ac < 0`. -/
theorem exists_formEquiv_pos {f : ℤ × ℤ × ℤ} (hd : ¬ IsSquare (formDisc f)) (hpos : 0 < formDisc f) :
    ∃ g, FormEquiv f g ∧ 0 < g.1 := by
  obtain ⟨g, hfg, h1, h2⟩ := exists_formEquiv_reduced f hd
  have hgd : formDisc g = formDisc f := hfg.formDisc_eq
  have ha := fst_ne_zero_of_not_isSquare (f := g) (by rwa [hgd])
  have hc := snd_snd_ne_zero_of_not_isSquare (f := g) (by rwa [hgd])
  rcases lt_or_gt_of_ne ha with ha | ha
  · rcases lt_or_gt_of_ne hc with hc | hc
    · exfalso
      rw [abs_of_neg ha, abs_of_neg hc] at h2
      have hb2 : g.2.1 ^ 2 ≤ g.1 ^ 2 := by
        rw [abs_of_neg ha] at h1; nlinarith [abs_nonneg g.2.1, sq_abs g.2.1]
      have : formDisc g < 0 := by simp only [formDisc]; nlinarith
      linarith
    · refine ⟨formSubst g 0 (-1) 1 0, hfg.trans ⟨0, -1, 1, 0, by ring, rfl⟩, ?_⟩
      simp only [formSubst]; linarith
  · exact ⟨g, hfg, ha⟩

theorem not_isSquare_formDisc_of {d : ℤ} {f : ℤ × ℤ × ℤ} (hd : ¬ IsSquare d) (hf : formDisc f = d) :
    ¬ IsSquare (formDisc f) := by rwa [hf]

/-- The number of classes is finite (Davenport §6, pp. 53–54; `exists_finset_formEquiv`). -/
instance finite_formClass {d : ℤ} [hd : Fact (¬ IsSquare d)] : Finite (FormClass d) := by
  classical
  obtain ⟨S, hS, hall⟩ := exists_finset_formEquiv hd.out
  let T : Finset (ℤ × ℤ × ℤ) := S.filter (fun g ↦ d < 0 → 0 < g.1)
  let F : T → FormClass d := fun g ↦ ⟦⟨g.1, hS _ (Finset.mem_filter.mp g.2).1,
    (Finset.mem_filter.mp g.2).2⟩⟧
  refine Finite.of_surjective F ?_
  intro C
  induction C using Quotient.inductionOn
  rename_i f
  obtain ⟨g, hg, hfg⟩ := hall f.1 f.2.1
  have hg' : d < 0 → 0 < g.1 := fun h ↦
    formEquiv_pos (by rw [f.2.1]; exact h) (f.2.2 h) hfg
  exact ⟨⟨g, Finset.mem_filter.mpr ⟨hg, hg'⟩⟩, Quotient.sound hfg.symm⟩

/-- The principal form `(1, σ, (σ - d)/4)`, `σ = d % 4`. -/
def principalForm (d : ℤ) : ℤ × ℤ × ℤ := (1, d % 4, (d % 4 - d) / 4)

theorem formDisc_principalForm {d : ℤ} (hd : d % 4 = 0 ∨ d % 4 = 1) :
    formDisc (principalForm d) = d := by
  simp only [formDisc, principalForm]
  rcases hd with h | h <;> rw [h] <;> omega

/-- **Davenport §6, p. 54 (row 6-2).** `h(d) ≥ 1` for `d ≡ 0, 1 (mod 4)` not a square: the
principal form exists. -/
theorem formClassNumber_pos {d : ℤ} (hd : ¬ IsSquare d) (h4 : d % 4 = 0 ∨ d % 4 = 1) :
    0 < formClassNumber d := by
  have : Fact (¬ IsSquare d) := ⟨hd⟩
  have : Nonempty (FormClass d) :=
    ⟨⟦⟨principalForm d, formDisc_principalForm h4, fun _ ↦ by simp [principalForm]⟩⟧⟩
  exact Nat.card_pos

/-! ### `h(D)` is the number of narrow classes (row 6-22) -/

section narrow

variable (D : ℤ)

/-- Forms with `a > 0` as Davenport forms. -/
def posFormClassToFormClass : PosFormClass D → FormClass D :=
  Quotient.map (fun f ↦ ⟨f.1, f.2.1, fun _ ↦ f.2.2⟩) (fun _ _ h ↦ h)

theorem posFormClassToFormClass_bijective (hD : ¬ IsSquare D) :
    Function.Bijective (posFormClassToFormClass D) := by
  constructor
  · intro F G h
    induction F using Quotient.inductionOn
    induction G using Quotient.inductionOn
    rename_i f g
    change (⟦(⟨f.1, f.2.1, fun _ ↦ f.2.2⟩ : DavForm D)⟧ : FormClass D) = ⟦⟨g.1, g.2.1, fun _ ↦ g.2.2⟩⟧ at h
    have h' : FormEquiv f.1 g.1 := Quotient.exact h
    exact Quotient.sound h'
  · intro C
    induction C using Quotient.inductionOn
    rename_i f
    rcases lt_or_gt_of_ne (show D ≠ 0 by rintro rfl; exact hD ⟨0, by simp⟩) with hneg | hpos
    · exact ⟨⟦⟨f.1, f.2.1, f.2.2 hneg⟩⟧, rfl⟩
    · obtain ⟨g, hfg, hg⟩ := exists_formEquiv_pos (f := f.1) (by rw [f.2.1]; exact hD)
        (by rw [f.2.1]; exact hpos)
      exact ⟨⟦⟨g, by rw [hfg.formDisc_eq, f.2.1], hg⟩⟧, Quotient.sound hfg.symm⟩

variable [Fact (IsFundamentalDiscriminant D)] [Fact (D ≠ 1)]

/-- **Davenport §6, p. 62 (row 6-22).** For a fundamental discriminant `D ≠ 1`, the form class
number `h(D)` is the number of ideal classes of `ℚ(√D)` in the narrow sense. -/
theorem formClassNumber_eq_card_narrowClass : formClassNumber D = Nat.card (NarrowClass D) :=
  Nat.card_congr ((Equiv.ofBijective _ (posFormClassToFormClass_bijective D
    (not_isSquare Fact.out Fact.out))).symm.trans
    (Equiv.ofBijective _ (posFormClassToNarrow_bijective D)))

/-! ### Narrow and wide classes (row 6-23) -/

variable {D}

theorem mem_nonZeroDivisors_of_ne_bot {I : Ideal (Order D)} (h : I ≠ ⊥) : I ∈ (Ideal (Order D))⁰ :=
  mem_nonZeroDivisors_iff_ne_zero.mpr h

variable (D) in
/-- The narrow class of `𝔞` goes to its (wide) ideal class. -/
def narrowToClassGroup : NarrowClass D → ClassGroup (Order D) :=
  Quotient.lift (fun I ↦ ClassGroup.mk0 ⟨I.1, mem_nonZeroDivisors_of_ne_bot I.2⟩) (by
    rintro I J ⟨x, y, hxy, h⟩
    refine ClassGroup.mk0_eq_mk0_iff.mpr ⟨x, y, ?_, ?_, h⟩
    · rintro rfl; simp at hxy
    · rintro rfl; simp at hxy)

theorem narrowToClassGroup_surjective : Function.Surjective (narrowToClassGroup D) := by
  intro C
  obtain ⟨I, rfl⟩ := ClassGroup.mk0_surjective C
  exact ⟨⟦⟨I.1, mem_nonZeroDivisors_iff_ne_zero.mp I.2⟩⟧, rfl⟩

theorem exists_of_narrowToClassGroup_eq {I J : {I : Ideal (Order D) // I ≠ ⊥}}
    (h : narrowToClassGroup D ⟦I⟧ = narrowToClassGroup D ⟦J⟧) :
    ∃ x y : Order D, x ≠ 0 ∧ y ≠ 0 ∧ Ideal.span {x} * I.1 = Ideal.span {y} * J.1 := by
  obtain ⟨x, y, hx, hy, h⟩ := ClassGroup.mk0_eq_mk0_iff.mp h
  exact ⟨x, y, hx, hy, h⟩

/-- For `D < 0` the norm of a nonzero element is positive. -/
theorem norm_pos_of_neg (hD : D < 0) {z : Order D} (hz : z ≠ 0) : 0 < z.norm := by
  have hσ : D % 4 * (D % 4) = D % 4 := emod_four_mul_self_of_fact
  have hq : D % 4 + 4 * (D / 4) = D := by omega
  have h4 : 4 * z.norm = (2 * z.re + D % 4 * z.im) ^ 2 - D * z.im ^ 2 := by
    rw [norm_def]; linear_combination -z.im ^ 2 * hσ - z.im ^ 2 * hq
  have hne := norm_ne_zero_of_ne_zero hz
  have : 0 ≤ 4 * z.norm := by rw [h4]; nlinarith [sq_nonneg (2 * z.re + D % 4 * z.im), sq_nonneg z.im]
  omega

theorem narrowToClassGroup_injective_of (hinj : ∀ x y : Order D, x ≠ 0 → y ≠ 0 →
    ∃ x' : Order D, Ideal.span {x'} = Ideal.span {x} ∧ 0 < x'.norm * y.norm) :
    Function.Injective (narrowToClassGroup D) := by
  intro C C' h
  induction C using Quotient.inductionOn
  induction C' using Quotient.inductionOn
  rename_i I J
  obtain ⟨x, y, hx, hy, hIJ⟩ := exists_of_narrowToClassGroup_eq h
  obtain ⟨x', hx', hpos⟩ := hinj x y hx hy
  exact Quotient.sound ⟨x', y, hpos, by rw [hx']; exact hIJ⟩

/-- **Row 6-23, `d < 0`.** Narrow and wide classes coincide. -/
theorem narrowToClassGroup_bijective_of_neg (hD : D < 0) :
    Function.Bijective (narrowToClassGroup D) :=
  ⟨narrowToClassGroup_injective_of fun x y hx hy ↦
    ⟨x, rfl, mul_pos (norm_pos_of_neg hD hx) (norm_pos_of_neg hD hy)⟩,
    narrowToClassGroup_surjective⟩

/-- **Row 6-23, a unit of norm `-1`.** Narrow and wide classes coincide. -/
theorem narrowToClassGroup_bijective_of_unit {u : (Order D)ˣ} (hu : (u : Order D).norm = -1) :
    Function.Bijective (narrowToClassGroup D) := by
  refine ⟨narrowToClassGroup_injective_of fun x y hx hy ↦ ?_, narrowToClassGroup_surjective⟩
  have hnx := norm_ne_zero_of_ne_zero hx
  have hny := norm_ne_zero_of_ne_zero hy
  rcases lt_or_gt_of_ne (mul_ne_zero hnx hny) with h | h
  · refine ⟨u * x, Ideal.span_singleton_mul_left_unit u.isUnit x, ?_⟩
    rw [map_mul, hu]; linarith
  · exact ⟨x, rfl, h⟩

/-- Multiplication by `√D` on narrow classes. -/
def sqrtDMul (I : {I : Ideal (Order D) // I ≠ ⊥}) : {I : Ideal (Order D) // I ≠ ⊥} :=
  ⟨Ideal.span {sqrtD D} * I.1, by
    rw [Ne, Ideal.mul_eq_bot, not_or, Ideal.span_singleton_eq_bot]
    refine ⟨fun h ↦ ?_, I.2⟩
    have := congrArg QuadraticAlgebra.im h
    simp [sqrtD] at this⟩

theorem narrowRel_sqrtDMul {I J : {I : Ideal (Order D) // I ≠ ⊥}} (h : NarrowRel I.1 J.1) :
    NarrowRel (sqrtDMul I).1 (sqrtDMul J).1 := by
  obtain ⟨x, y, hxy, h⟩ := h
  refine ⟨x, y, hxy, ?_⟩
  simp only [sqrtDMul]
  rw [mul_left_comm, h, mul_left_comm]

theorem sqrtD_ne_zero : sqrtD D ≠ 0 := fun h ↦ by
  have := congrArg QuadraticAlgebra.im h; simp [sqrtD] at this

/-- **Row 6-23, no unit of norm `-1`.** `𝔞` and `√D 𝔞` are not narrowly equivalent. -/
theorem not_narrowRel_sqrtDMul (hD : 0 < D) (hu : ∀ u : (Order D)ˣ, (u : Order D).norm ≠ -1)
    (I : {I : Ideal (Order D) // I ≠ ⊥}) : ¬ NarrowRel I.1 (sqrtDMul I).1 := by
  rintro ⟨x, y, hxy, h⟩
  simp only [sqrtDMul] at h
  rw [← mul_assoc, Ideal.span_singleton_mul_span_singleton] at h
  have h' : Ideal.span {x} = Ideal.span {y * sqrtD D} := mul_right_cancel₀ I.2 h
  obtain ⟨u, hu'⟩ := Ideal.span_singleton_eq_span_singleton.mp h'
  -- `x u = y √D`
  have hn := congrArg QuadraticAlgebra.norm hu'
  rw [map_mul, map_mul, norm_sqrtD emod_four_mul_self_of_fact] at hn
  have hunit : IsUnit (u : Order D).norm := (u.isUnit).map QuadraticAlgebra.norm
  rcases Int.isUnit_iff.mp hunit with h1 | h1
  · rw [h1, mul_one] at hn
    have e : x.norm * y.norm = -(D * y.norm ^ 2) := by rw [hn]; ring
    have := mul_nonneg hD.le (sq_nonneg y.norm)
    linarith
  · exact hu u h1

/-- The class of `√D 𝔞`. -/
def narrowSqrtD : NarrowClass D → NarrowClass D :=
  Quotient.map sqrtDMul (fun _ _ h ↦ narrowRel_sqrtDMul h)

theorem narrowToClassGroup_narrowSqrtD (C : NarrowClass D) :
    narrowToClassGroup D (narrowSqrtD C) = narrowToClassGroup D C := by
  induction C using Quotient.inductionOn
  rename_i I
  refine ClassGroup.mk0_eq_mk0_iff.mpr ⟨1, sqrtD D, one_ne_zero, sqrtD_ne_zero, ?_⟩
  simp only [sqrtDMul, Ideal.span_singleton_one, Ideal.top_mul]

theorem eq_or_eq_narrowSqrtD (hD : 0 < D) {C C' : NarrowClass D}
    (h : narrowToClassGroup D C = narrowToClassGroup D C') : C' = C ∨ C' = narrowSqrtD C := by
  induction C using Quotient.inductionOn
  induction C' using Quotient.inductionOn
  rename_i I J
  obtain ⟨x, y, hx, hy, hIJ⟩ := exists_of_narrowToClassGroup_eq h
  have hnx := norm_ne_zero_of_ne_zero hx
  have hny := norm_ne_zero_of_ne_zero hy
  rcases lt_or_gt_of_ne (mul_ne_zero hnx hny) with hneg | hpos
  · right
    refine Quotient.sound ⟨y * sqrtD D, x, ?_, ?_⟩
    · rw [map_mul, norm_sqrtD emod_four_mul_self_of_fact]; nlinarith
    · simp only [sqrtDMul]
      rw [← Ideal.span_singleton_mul_span_singleton, mul_assoc, mul_left_comm, ← hIJ, mul_left_comm]
  · left; exact Quotient.sound ⟨y, x, by rwa [mul_comm], hIJ.symm⟩

theorem narrowSqrtD_ne (hD : 0 < D) (hu : ∀ u : (Order D)ˣ, (u : Order D).norm ≠ -1)
    (C : NarrowClass D) : narrowSqrtD C ≠ C := by
  induction C using Quotient.inductionOn
  rename_i I
  intro h
  exact not_narrowRel_sqrtDMul hD hu I (Quotient.exact h).symm

/-- **Row 6-23, no unit of norm `-1`.** There are twice as many narrow classes as wide classes. -/
theorem card_narrowClass_eq_two_mul (hD : 0 < D) (hu : ∀ u : (Order D)ˣ, (u : Order D).norm ≠ -1) :
    Nat.card (NarrowClass D) = 2 * Nat.card (ClassGroup (Order D)) := by
  classical
  choose s hs using narrowToClassGroup_surjective (D := D)
  let F : ClassGroup (Order D) × Bool → NarrowClass D := fun p ↦
    cond p.2 (narrowSqrtD (s p.1)) (s p.1)
  have hπF : ∀ p, narrowToClassGroup D (F p) = p.1 := by
    rintro ⟨w, b⟩
    cases b
    · exact hs w
    · exact (narrowToClassGroup_narrowSqrtD _).trans (hs w)
  have hF : Function.Bijective F := by
    constructor
    · rintro ⟨w, b⟩ ⟨w', b'⟩ h
      have hw : w = w' := by
        have := congrArg (narrowToClassGroup D) h
        rwa [hπF, hπF] at this
      subst hw
      cases b <;> cases b'
      · rfl
      · exact absurd h.symm (narrowSqrtD_ne hD hu _)
      · exact absurd h (narrowSqrtD_ne hD hu _)
      · rfl
    · intro C
      rcases eq_or_eq_narrowSqrtD hD ((hs (narrowToClassGroup D C)).trans rfl) with h | h
      · exact ⟨(narrowToClassGroup D C, false), h.symm⟩
      · exact ⟨(narrowToClassGroup D C, true), h.symm⟩
  rw [← Nat.card_congr (Equiv.ofBijective F hF), Nat.card_prod, Nat.card_eq_fintype_card (α := Bool),
    Fintype.card_bool, mul_comm]

end narrow

/-! ### Transport to a quadratic number field `K` -/

section field

variable {K : Type*} [Field K] [NumberField K]

theorem algebraNorm_order (D : ℤ) (z : Order D) : Algebra.norm ℤ z = z.norm := by
  rw [Algebra.norm_apply]
  exact det_toLinearMap_eq_norm z

theorem classNumber_eq_card_classGroup_order {D : ℤ} [Fact (IsFundamentalDiscriminant D)]
    [Fact (D ≠ 1)] (e : Order D ≃+* 𝓞 K) :
    classNumber K = Nat.card (ClassGroup (Order D)) := by
  rw [classNumber, ← Nat.card_eq_fintype_card]
  exact (Nat.card_congr (ClassGroup.mulEquiv e).toEquiv).symm

theorem exists_unit_norm_iff {D : ℤ} (e : Order D ≃+* 𝓞 K) :
    (∃ u : (𝓞 K)ˣ, Algebra.norm ℤ (u : 𝓞 K) = -1) ↔
      ∃ u : (Order D)ˣ, (u : Order D).norm = -1 := by
  constructor
  · rintro ⟨u, hu⟩
    refine ⟨Units.map e.symm.toMonoidHom u, ?_⟩
    rw [← algebraNorm_order]
    rw [← Algebra.norm_eq_of_algEquiv e.symm.toIntAlgEquiv] at hu
    simpa using hu
  · rintro ⟨u, hu⟩
    refine ⟨Units.map e.toMonoidHom u, ?_⟩
    rw [← algebraNorm_order, ← Algebra.norm_eq_of_algEquiv e.toIntAlgEquiv] at hu
    simpa using hu

variable (K)

theorem facts_discr (hK : Module.finrank ℚ K = 2) :
    Fact (IsFundamentalDiscriminant (discr K)) ∧ Fact (discr K ≠ 1) :=
  ⟨⟨(isFundamental_discr K hK).1⟩, ⟨(isFundamental_discr K hK).2.1⟩⟩

/-- **Davenport §6, p. 62 (row 6-23), `d < 0`.** For an imaginary quadratic field `K` of
discriminant `d`, Davenport's form class number `h(d)` is the class number of `K`. -/
theorem formClassNumber_eq_classNumber_of_discr_neg (hK : Module.finrank ℚ K = 2)
    (hD : discr K < 0) : formClassNumber (discr K) = classNumber K := by
  obtain ⟨_, _⟩ := facts_discr K hK
  obtain ⟨e⟩ := nonempty_ringEquiv_order K hK
  rw [formClassNumber_eq_card_narrowClass, classNumber_eq_card_classGroup_order e]
  exact Nat.card_congr (Equiv.ofBijective _ (narrowToClassGroup_bijective_of_neg hD))

/-- **Davenport §6, p. 62 (row 6-23), `d > 0` with a unit of norm `-1`.** `h(d) = h_1(d)`. -/
theorem formClassNumber_eq_classNumber_of_exists_norm_eq_neg_one (hK : Module.finrank ℚ K = 2)
    (h : ∃ u : (𝓞 K)ˣ, Algebra.norm ℤ (u : 𝓞 K) = -1) :
    formClassNumber (discr K) = classNumber K := by
  obtain ⟨_, _⟩ := facts_discr K hK
  obtain ⟨e⟩ := nonempty_ringEquiv_order K hK
  obtain ⟨u, hu⟩ := (exists_unit_norm_iff e).mp h
  rw [formClassNumber_eq_card_narrowClass, classNumber_eq_card_classGroup_order e]
  exact Nat.card_congr (Equiv.ofBijective _ (narrowToClassGroup_bijective_of_unit hu))

/-- **Davenport §6, p. 62 (row 6-23), `d > 0` with no unit of norm `-1`.** `h(d) = 2 h_1(d)`. -/
theorem formClassNumber_eq_two_mul_classNumber (hK : Module.finrank ℚ K = 2) (hD : 0 < discr K)
    (h : ¬ ∃ u : (𝓞 K)ˣ, Algebra.norm ℤ (u : 𝓞 K) = -1) :
    formClassNumber (discr K) = 2 * classNumber K := by
  obtain ⟨_, _⟩ := facts_discr K hK
  obtain ⟨e⟩ := nonempty_ringEquiv_order K hK
  rw [exists_unit_norm_iff e] at h
  push Not at h
  rw [formClassNumber_eq_card_narrowClass, classNumber_eq_card_classGroup_order e]
  exact card_narrowClass_eq_two_mul hD h

end field

end NTKB.Davenport
