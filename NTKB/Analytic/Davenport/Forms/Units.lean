/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Davenport.Forms.BasicTheorem
import NTKB.Analytic.Davenport.Forms.PellCount
import Mathlib.NumberTheory.NumberField.Units.Basic

/-!
# Davenport, Chapter 6: the number `w` of automorphs (row 6-3)

(§6, pp. 54–55.) For a form `f` of fundamental discriminant `d ≠ 1`, the automorphs of `f`
correspond to the solutions of `t² - d u² = 4` (row 6-5) and to the units of norm `1` of
`ℤ[ω]`. For `d < 0`:

* `NTKB.Davenport.automorphCount_eq_of_neg`: `f` has `w = 6, 4, 2` automorphs for `d = -3`, `-4`,
  `d < -4` (row 6-3);
* `NTKB.Davenport.automorphCount_eq_torsionOrder`: `w` is the number of roots of unity of the
  quadratic field of discriminant `d`;
* `NTKB.Davenport.sum_card_reps_eq_of_neg`: Davenport's basic theorem for `d < 0` with all
  representations counted, `∑_{f ∈ S} r_f(n) = w ∑_{m ∣ n} (d/m)` (row 6-7).
-/

noncomputable section

open QuadraticAlgebra NTKB.QuadraticField NumberField

namespace NTKB.Davenport

variable {D : ℤ}

/-- The automorphs of `f`: substitutions `(α β; γ δ)` of determinant `1` with `f ∘ (α β; γ δ) = f`. -/
def Automorphs (f : ℤ × ℤ × ℤ) :=
  {M : ℤ × ℤ × ℤ × ℤ // M.1 * M.2.2.2 - M.2.1 * M.2.2.1 = 1 ∧
    formSubst f M.1 M.2.1 M.2.2.1 M.2.2.2 = f}

/-- **Davenport §6, p. 54.** The number `w` of automorphs of `f`. -/
def automorphCount (f : ℤ × ℤ × ℤ) : ℕ := Nat.card (Automorphs f)

/-- The solutions of `t² - D u² = 4`. -/
def PellFour (D : ℤ) := {p : ℤ × ℤ // p.1 ^ 2 - D * p.2 ^ 2 = 4}

theorem two_dvd_sub_of_pellFour {f : ℤ × ℤ × ℤ} {t u : ℤ} (hf : formDisc f = D)
    (h : t ^ 2 - D * u ^ 2 = 4) : 2 ∣ t - f.2.1 * u := by
  simp only [formDisc] at hf
  have e : (t - f.2.1 * u) * ((t - f.2.1 * u) + 2 * (f.2.1 * u)) =
      2 * (2 * (1 - f.1 * f.2.2 * u ^ 2)) := by rw [← hf] at h; linear_combination h
  have hev : Even ((t - f.2.1 * u) * ((t - f.2.1 * u) + 2 * (f.2.1 * u))) := by
    rw [e]; exact even_two_mul _
  rcases Int.even_mul.mp hev with h1 | h1
  · exact even_iff_two_dvd.mp h1
  · have : Even (2 * (f.2.1 * u)) := even_two_mul _
    exact even_iff_two_dvd.mp ((Int.even_add.mp h1).mpr this)

section automorphs

variable [Fact (IsFundamentalDiscriminant D)] [Fact (D ≠ 1)] {f : ℤ × ℤ × ℤ}

/-- **Davenport §6, pp. 54–56 (rows 6-3, 6-5).** The automorphs of `f` correspond to the
solutions of `t² - D u² = 4`: `(α β; γ δ) ↦ (α + δ, γ / a)`. -/
def automorphsEquiv (hf : formDisc f = D) : Automorphs f ≃ PellFour D where
  toFun M := ⟨(M.1.1 + M.1.2.2.2, M.1.2.2.1 / f.1), by
    obtain ⟨t, u, htu, hα, hβ, hγ, hδ⟩ := (automorph_iff hf).mp M.2
    have ha : f.1 ≠ 0 :=
      fst_ne_zero_of_not_isSquare (by rw [hf]; exact not_isSquare Fact.out Fact.out)
    have h1 : M.1.1 + M.1.2.2.2 = t := by linarith
    have h2 : M.1.2.2.1 / f.1 = u := by rw [hγ, Int.mul_ediv_cancel_left _ ha]
    simp only [h1, h2]; exact htu⟩
  invFun p := ⟨((p.1.1 - f.2.1 * p.1.2) / 2, -(f.2.2 * p.1.2), f.1 * p.1.2,
      (p.1.1 + f.2.1 * p.1.2) / 2), by
    have h2 := two_dvd_sub_of_pellFour hf p.2
    have h2' : 2 ∣ p.1.1 + f.2.1 * p.1.2 := by
      have : p.1.1 + f.2.1 * p.1.2 = (p.1.1 - f.2.1 * p.1.2) + 2 * (f.2.1 * p.1.2) := by ring
      rw [this]; exact dvd_add h2 (dvd_mul_right _ _)
    exact (automorph_iff hf).mpr ⟨p.1.1, p.1.2, p.2, Int.mul_ediv_cancel' h2, rfl, rfl,
      Int.mul_ediv_cancel' h2'⟩⟩
  left_inv M := by
    obtain ⟨t, u, htu, hα, hβ, hγ, hδ⟩ := (automorph_iff hf).mp M.2
    have ha : f.1 ≠ 0 :=
      fst_ne_zero_of_not_isSquare (by rw [hf]; exact not_isSquare Fact.out Fact.out)
    have h1 : M.1.1 + M.1.2.2.2 = t := by linarith
    have h2 : M.1.2.2.1 / f.1 = u := by rw [hγ, Int.mul_ediv_cancel_left _ ha]
    apply Subtype.ext
    simp only [h1, h2]
    obtain ⟨⟨α, β, γ, δ⟩, hM⟩ := M
    simp only at hα hβ hγ hδ ⊢
    rw [hβ, hγ, ← hα, ← hδ, Int.mul_ediv_cancel_left _ two_ne_zero,
      Int.mul_ediv_cancel_left _ two_ne_zero]
  right_inv p := by
    have ha : f.1 ≠ 0 :=
      fst_ne_zero_of_not_isSquare (by rw [hf]; exact not_isSquare Fact.out Fact.out)
    have h2 := two_dvd_sub_of_pellFour hf p.2
    have h2' : 2 ∣ p.1.1 + f.2.1 * p.1.2 := by
      have : p.1.1 + f.2.1 * p.1.2 = (p.1.1 - f.2.1 * p.1.2) + 2 * (f.2.1 * p.1.2) := by ring
      rw [this]; exact dvd_add h2 (dvd_mul_right _ _)
    apply Subtype.ext
    obtain ⟨⟨t, u⟩, hp⟩ := p
    simp only at h2 h2' ⊢
    have e1 : (t - f.2.1 * u) / 2 + (t + f.2.1 * u) / 2 = t := by
      have := Int.mul_ediv_cancel' h2
      have := Int.mul_ediv_cancel' h2'
      linarith
    rw [e1, Int.mul_ediv_cancel_left _ ha]

/-- **Davenport §6, p. 54 (row 6-3).** For `d < 0`, a form of discriminant `d` has `w = 6`
automorphs if `d = -3`, `w = 4` if `d = -4` and `w = 2` otherwise. -/
theorem automorphCount_eq_of_neg (hf : formDisc f = D) (hD : D < 0) :
    automorphCount f = if D = -3 then 6 else if D = -4 then 4 else 2 := by
  rw [automorphCount, Nat.card_congr (automorphsEquiv hf)]
  exact card_sol_four_of_neg hD (emod_four_of_isFundamental Fact.out)

end automorphs

/-! ### `w` is the number of roots of unity -/

section roots

variable [Fact (IsFundamentalDiscriminant D)] [Fact (D ≠ 1)]

/-- Units of norm `1` and solutions of `t² - D u² = 4`: `η ↦ (2 re η + σ im η, im η)`. -/
def normOneEquiv : {η : Order D // η.norm = 1} ≃ PellFour D where
  toFun η := ⟨(2 * η.1.re + D % 4 * η.1.im, η.1.im), by
    have hσ : D % 4 * (D % 4) = D % 4 := emod_four_mul_self_of_fact
    have hq : D % 4 + 4 * (D / 4) = D := by omega
    have h := η.2
    rw [norm_def] at h
    simp only
    linear_combination 4 * h + η.1.im ^ 2 * hσ + η.1.im ^ 2 * hq⟩
  invFun p := ⟨⟨(p.1.1 - D % 4 * p.1.2) / 2, p.1.2⟩, by
    have hσ : D % 4 * (D % 4) = D % 4 := emod_four_mul_self_of_fact
    have hq : D % 4 + 4 * (D / 4) = D := by omega
    have h2 : 2 ∣ p.1.1 - D % 4 * p.1.2 := by
      have := two_dvd_sub_of_pellFour (f := principalForm D)
        (formDisc_principalForm (emod_four_of_isFundamental Fact.out)) p.2
      simpa [principalForm] using this
    obtain ⟨r, hr⟩ := h2
    rw [hr, Int.mul_ediv_cancel_left _ two_ne_zero, norm_def]
    simp only
    have := p.2
    have hp1 : p.1.1 = 2 * r + D % 4 * p.1.2 := by linarith
    rw [hp1] at this
    have : 4 * (r * r + D % 4 * r * p.1.2 - D / 4 * p.1.2 * p.1.2) = 4 * 1 := by
      linear_combination this - p.1.2 ^ 2 * hσ - p.1.2 ^ 2 * hq
    linarith⟩
  left_inv η := by
    apply Subtype.ext
    ext
    · simp only
      rw [show 2 * η.1.re + D % 4 * η.1.im - D % 4 * η.1.im = 2 * η.1.re by ring,
        Int.mul_ediv_cancel_left _ two_ne_zero]
    · rfl
  right_inv p := by
    have h2 : 2 ∣ p.1.1 - D % 4 * p.1.2 := by
      have := two_dvd_sub_of_pellFour (f := principalForm D)
        (formDisc_principalForm (emod_four_of_isFundamental Fact.out)) p.2
      simpa [principalForm] using this
    apply Subtype.ext
    obtain ⟨⟨t, u⟩, hp⟩ := p
    simp only at h2 ⊢
    rw [Int.mul_ediv_cancel' h2]
    ring_nf

theorem isUnit_of_norm_eq_one {η : Order D} (h : η.norm = 1) : IsUnit η :=
  isUnit_iff_norm_isUnit.mpr (by rw [h]; exact isUnit_one)

/-- For `D < 0` every unit of `ℤ[ω]` has norm `1`. -/
def unitsEquivNormOne (hD : D < 0) : (Order D)ˣ ≃ {η : Order D // η.norm = 1} where
  toFun u := ⟨u, by
    have hpos := norm_pos_of_neg hD u.ne_zero
    rcases Int.isUnit_iff.mp ((u.isUnit).map QuadraticAlgebra.norm) with h | h
    · exact h
    · rw [h] at hpos; norm_num at hpos⟩
  invFun η := (isUnit_of_norm_eq_one η.2).unit
  left_inv u := Units.ext rfl
  right_inv η := Subtype.ext rfl

variable {K : Type*} [Field K] [NumberField K]

theorem torsionOrder_eq_card_units_of_finite [Finite (𝓞 K)ˣ] :
    Units.torsionOrder K = Nat.card (𝓞 K)ˣ := by
  rw [Units.torsionOrder]
  have : Units.torsion K = ⊤ := by
    ext x
    simp only [Subgroup.mem_top, iff_true]
    exact (CommGroup.mem_torsion x).mpr (isOfFinOrder_of_finite x)
  rw [this]
  exact Nat.card_congr (Subgroup.topEquiv.toEquiv)

end roots

/-- **Davenport §6, p. 54 (row 6-3).** For a quadratic field `K` of discriminant `d < 0` and a
form `f` of discriminant `d`, the number of automorphs of `f` is the number `w` of roots of unity
of `K`. -/
theorem automorphCount_eq_torsionOrder {K : Type*} [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) (hD : discr K < 0) {f : ℤ × ℤ × ℤ}
    (hf : formDisc f = discr K) : automorphCount f = Units.torsionOrder K := by
  obtain ⟨_, _⟩ := facts_discr K hK
  obtain ⟨e⟩ := nonempty_ringEquiv_order K hK
  have hU : (Order (discr K))ˣ ≃ (𝓞 K)ˣ := (Units.mapEquiv e.toMulEquiv)
  have hcard : Nat.card (𝓞 K)ˣ = automorphCount f := by
    rw [← Nat.card_congr hU, Nat.card_congr ((unitsEquivNormOne hD).trans normOneEquiv),
      automorphCount, Nat.card_congr (automorphsEquiv hf)]
  have : Finite (𝓞 K)ˣ := by
    apply Nat.finite_of_card_ne_zero
    rw [hcard, automorphCount_eq_of_neg hf hD]
    split_ifs <;> norm_num
  rw [torsionOrder_eq_card_units_of_finite, hcard]

/-! ### Row 6-7 for `d < 0`: all representations -/

section total

variable [Fact (IsFundamentalDiscriminant D)] [Fact (D ≠ 1)] {f : ℤ × ℤ × ℤ}

theorem repRel_of_quot_eq (hf : formDisc f = D) (ha : f.1 ≠ 0) {n : ℤ} {p q : Reps f n}
    (h : Quot.mk (fun p q : Reps f n ↦ RepRel f p.1 q.1) p = Quot.mk _ q) : RepRel f p.1 q.1 := by
  have := Quot.eqvGen_exact h
  have heq : Equivalence (fun p q : Reps f n ↦ RepRel f p.1 q.1) :=
    ⟨fun p ↦ (repRel_equivalence hf ha).refl p.1, fun h ↦ (repRel_equivalence hf ha).symm h,
      fun h h' ↦ (repRel_equivalence hf ha).trans h h'⟩
  exact (Equivalence.eqvGen_iff heq).mp this

theorem formLam_ne_zero (hf : formDisc f = D) (ha : f.1 ≠ 0) {n : ℤ} (hn : n ≠ 0) (p : Reps f n) :
    formLam D f p.1.1 p.1.2 ≠ 0 := by
  intro h
  have := norm_formLam (D := D) hf p.1.1 p.1.2
  rw [h, p.2, QuadraticAlgebra.norm_zero] at this
  exact mul_ne_zero ha hn this.symm

/-- The representations of `n` are the classes up to automorphs times the units of norm `1`. -/
theorem card_reps_eq_mul (hf : formDisc f = D) (ha : f.1 ≠ 0) {n : ℤ} (hn : n ≠ 0) :
    Nat.card (Reps f n) = Nat.card (Quot (fun p q : Reps f n ↦ RepRel f p.1 q.1)) *
      Nat.card {η : Order D // η.norm = 1} := by
  classical
  set r := fun p q : Reps f n ↦ RepRel f p.1 q.1
  have hη : ∀ p : Reps f n, ∃ η : Order D, η.norm = 1 ∧
      formLam D f p.1.1 p.1.2 = η * formLam D f (Quot.mk r p).out.1.1 (Quot.mk r p).out.1.2 :=
    fun p ↦ (repRel_iff hf ha).mp (repRel_of_quot_eq hf ha (Quot.out_eq (Quot.mk r p)))
  have hpt : ∀ (Q : Quot r) (η : {η : Order D // η.norm = 1}), ∃ q : Reps f n,
      formLam D f q.1.1 q.1.2 = η.1 * formLam D f Q.out.1.1 Q.out.1.2 := by
    intro Q η
    obtain ⟨X, Y, hXY⟩ := exists_of_mem_formIdeal hf
      (Ideal.mul_mem_left _ η.1 (formLam_mem (D := D) (f := f) Q.out.1.1 Q.out.1.2))
    refine ⟨⟨(X, Y), ?_⟩, hXY.symm⟩
    have h1 := congrArg QuadraticAlgebra.norm hXY
    rw [map_mul, η.2, one_mul, norm_formLam hf, Q.out.2, norm_mul_add_formTheta hf] at h1
    exact (mul_left_cancel₀ ha h1).symm
  refine (Nat.card_congr ?_).trans (Nat.card_prod _ _)
  refine
    { toFun := fun p ↦ (Quot.mk r p, ⟨(hη p).choose, (hη p).choose_spec.1⟩)
      invFun := fun x ↦ (hpt x.1 x.2).choose
      left_inv := fun p ↦ ?_
      right_inv := fun x ↦ ?_ }
  · have h1 := (hpt (Quot.mk r p) ⟨(hη p).choose, (hη p).choose_spec.1⟩).choose_spec
    have h2 := (hη p).choose_spec.2
    simp only at h1
    obtain ⟨e1, e2⟩ := mul_add_formTheta_injective ha (h1.trans h2.symm)
    exact Subtype.ext (Prod.ext e1 e2)
  · obtain ⟨Q, η⟩ := x
    set q := (hpt Q η).choose
    have hq : formLam D f q.1.1 q.1.2 = η.1 * formLam D f Q.out.1.1 Q.out.1.2 :=
      (hpt Q η).choose_spec
    have hQ : Quot.mk r q = Q := by
      rw [← Quot.out_eq Q]
      exact (Quot.sound (r := r) (a := Q.out) (b := q)
        ((repRel_iff hf ha).mpr ⟨η.1, η.2, hq⟩)).symm
    have h2 := (hη q).choose_spec.2
    have hout : (Quot.mk r q).out = Q.out := by rw [hQ]
    have hl : formLam D f (Quot.mk r q).out.1.1 (Quot.mk r q).out.1.2 =
        formLam D f Q.out.1.1 Q.out.1.2 := by rw [hout]
    have hne := formLam_ne_zero hf ha hn Q.out
    have e3 : (hη q).choose * formLam D f Q.out.1.1 Q.out.1.2 =
        η.1 * formLam D f Q.out.1.1 Q.out.1.2 :=
      (congrArg (fun z ↦ (hη q).choose * z) hl).symm.trans (h2.symm.trans hq)
    exact Prod.ext hQ (Subtype.ext (mul_right_cancel₀ hne e3))

end total

/-- **Davenport §6, p. 57 (row 6-7) for `d < 0`.** Let `d < 0` be a fundamental discriminant and
`S` a complete system of representatives of the classes of positive definite forms of
discriminant `d`. For `n ≥ 1` the total number of representations of `n` by the forms of `S` is
`w ∑_{m ∣ n} (d/m)`, `w = 6, 4, 2` for `d = -3`, `-4`, `d < -4`. -/
@[kb "davenport1980" "Ch 6, p. 57"]
theorem sum_card_reps_eq_of_neg (hD : IsFundamentalDiscriminant D) (hneg : D < 0)
    {S : Finset (ℤ × ℤ × ℤ)} (hS : IsFormSystem D S) {n : ℕ} (hn : 0 < n) :
    ((∑ f ∈ S, Nat.card (Reps f n) : ℕ) : ℂ) =
      ((if D = -3 then 6 else if D = -4 then 4 else 2 : ℕ) : ℂ) *
        ∑ m ∈ n.divisors, kroneckerChar D m := by
  have h1 : D ≠ 1 := by omega
  have : Fact (IsFundamentalDiscriminant D) := ⟨hD⟩
  have : Fact (D ≠ 1) := ⟨h1⟩
  have hw : ∀ f ∈ S, Nat.card (Reps f n) =
      repClassCount f n * (if D = -3 then 6 else if D = -4 then 4 else 2) := by
    intro f hf
    have hfD := hS.1 f hf
    rw [card_reps_eq_mul hfD.1 hfD.2.ne' (by exact_mod_cast hn.ne'), repClassCount,
      Nat.card_congr normOneEquiv, ← Nat.card_congr (automorphsEquiv hfD.1),
      ← automorphCount, automorphCount_eq_of_neg hfD.1 hneg]
  rw [Finset.sum_congr rfl hw, ← Finset.sum_mul, Nat.cast_mul, mul_comm,
    sum_repClassCount_eq hD h1 hS hn]

end NTKB.Davenport
