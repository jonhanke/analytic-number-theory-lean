/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Davenport.Forms.RealUnits
import NTKB.Analytic.Davenport.Forms.Representation
import NTKB.Attr

/-!
# Davenport, Chapter 6: primary representations (row 6-6)

(§6, pp. 56-57.) Let `D > 0` be a fundamental discriminant, `f = (a, b, c)` a form of
discriminant `D` with `a > 0`, and `ε > 1` the generator of the units of norm `1` up to sign.
A representation `f(x, y) = n` with `λ = a x + θ_f y` is *primary* if `λ > 0` and
`1 ≤ λ' / λ < ε²` in the real embedding, where `λ'` is the conjugate of `λ`.

* `NTKB.Davenport.IsPrimaryRep`: the definition.
* `NTKB.Davenport.card_primaryReps_eq_repClassCount`: every orbit of representations under the
  automorphs of `f` contains exactly one primary representation, so the number of primary
  representations is `R_f(n)` (`NTKB.Davenport.repClassCount`).
-/

noncomputable section

open QuadraticAlgebra NTKB.QuadraticField

namespace NTKB.Davenport

variable {D : ℤ} {f : ℤ × ℤ × ℤ}

section real

/-- Scaling by a power of `e > 1` moves the ratio `y / x` into `[1, e²)`. -/
theorem exists_zpow_scale {e x y : ℝ} (he : 1 < e) (hx : 0 < x) (hy : 0 < y) :
    ∃ k : ℤ, e ^ k * x ≤ (e ^ k)⁻¹ * y ∧ (e ^ k)⁻¹ * y < e ^ 2 * (e ^ k * x) := by
  have he0 : 0 < e := by linarith
  have hd : 0 < Real.log e := Real.log_pos he
  set L := Real.log y - Real.log x with hL
  refine ⟨⌊L / (2 * Real.log e)⌋, ?_⟩
  set k := ⌊L / (2 * Real.log e)⌋ with hk
  have h1 : (k : ℝ) ≤ L / (2 * Real.log e) := Int.floor_le _
  have h2 : L / (2 * Real.log e) < k + 1 := Int.lt_floor_add_one _
  rw [le_div_iff₀ (by positivity)] at h1
  rw [div_lt_iff₀ (by positivity)] at h2
  have hA : 0 < e ^ k := zpow_pos he0 k
  have hlogA : Real.log (e ^ k) = k * Real.log e := Real.log_zpow _ _
  have c1 : e ^ k * x ≤ (e ^ k)⁻¹ * y := by
    rw [← Real.log_le_log_iff (by positivity) (by positivity), Real.log_mul hA.ne' hx.ne',
      Real.log_mul (inv_pos.mpr hA).ne' hy.ne', Real.log_inv, hlogA]
    nlinarith
  refine ⟨c1, ?_⟩
  rw [← Real.log_lt_log_iff (by positivity) (by positivity), Real.log_mul (inv_pos.mpr hA).ne' hy.ne',
    Real.log_mul (by positivity) (by positivity), Real.log_mul hA.ne' hx.ne', Real.log_inv, hlogA,
    Real.log_pow]
  push_cast
  nlinarith

theorem eq_zero_of_primary_scale {e x y : ℝ} (he : 1 < e) (hx : 0 < x) (k : ℤ)
    (h1 : x ≤ y) (h2 : y < e ^ 2 * x)
    (h3 : e ^ k * x ≤ (e ^ k)⁻¹ * y) (h4 : (e ^ k)⁻¹ * y < e ^ 2 * (e ^ k * x)) : k = 0 := by
  have he0 : 0 < e := by linarith
  have hA : 0 < e ^ k := zpow_pos he0 k
  set A := e ^ k with hAdef
  have h3' : A ^ 2 * x ≤ y := by
    have := mul_le_mul_of_nonneg_left h3 hA.le
    rwa [← mul_assoc, ← mul_assoc, mul_inv_cancel₀ hA.ne', one_mul, ← sq] at this
  have h4' : y < e ^ 2 * A ^ 2 * x := by
    have := mul_lt_mul_of_pos_left h4 hA
    rw [← mul_assoc, mul_inv_cancel₀ hA.ne', one_mul] at this
    nlinarith
  have hAe : A < e := by
    by_contra h
    push Not at h
    have : e ^ 2 * x ≤ A ^ 2 * x := by
      have : e ^ 2 ≤ A ^ 2 := by nlinarith
      exact mul_le_mul_of_nonneg_right this hx.le
    linarith
  have hAe' : 1 < e * A := by
    by_contra h
    push Not at h
    have : (e * A) ^ 2 ≤ 1 := by nlinarith [mul_pos he0 hA]
    nlinarith
  have hk1 : k < 1 := by
    have : e ^ k < e ^ (1 : ℤ) := by rwa [zpow_one]
    exact (zpow_lt_zpow_iff_right₀ he).mp this
  have hk2 : -1 < k := by
    have : e ^ (-1 : ℤ) < e ^ k := by
      rw [zpow_neg_one]
      rw [inv_lt_iff_one_lt_mul₀ he0]
      have : e ^ k * e = e * A := by rw [hAdef, mul_comm]
      linarith
    exact (zpow_lt_zpow_iff_right₀ he).mp this
  omega

end real

section primary

variable [Fact (IsFundamentalDiscriminant D)] [Fact (D ≠ 1)]

/-- **Davenport §6, p. 56 (row 6-6).** A representation with `λ = formLam D f x y` is primary if
`λ > 0` and `1 ≤ λ' / λ < ε²` in the real embedding (`λ'` the conjugate). -/
def IsPrimaryRep (hD : 0 ≤ D) (f : ℤ × ℤ × ℤ) (ε : Order D) (p : ℤ × ℤ) : Prop :=
  0 < realEmb hD (formLam D f p.1 p.2) ∧
    realEmb hD (formLam D f p.1 p.2) ≤ realEmb hD (star (formLam D f p.1 p.2)) ∧
    realEmb hD (star (formLam D f p.1 p.2)) < realEmb hD ε ^ 2 * realEmb hD (formLam D f p.1 p.2)

/-- The primary condition on an element `z` of the order. -/
def PrimaryElt (hD : 0 ≤ D) (ε z : Order D) : Prop :=
  0 < realEmb hD z ∧ realEmb hD z ≤ realEmb hD (star z) ∧
    realEmb hD (star z) < realEmb hD ε ^ 2 * realEmb hD z

theorem isPrimaryRep_iff (hD : 0 ≤ D) (ε : Order D) (p : ℤ × ℤ) :
    IsPrimaryRep hD f ε p ↔ PrimaryElt hD ε (formLam D f p.1 p.2) := Iff.rfl

theorem realEmb_star_mul_of_norm_one (hD : 0 ≤ D) {η : Order D} (hη : η.norm = 1) :
    realEmb hD η * realEmb hD (star η) = 1 := by
  rw [realEmb_mul_star, hη, Int.cast_one]

theorem realEmb_star_mul (hD : 0 ≤ D) (η z : Order D) :
    realEmb hD (star (η * z)) = realEmb hD (star η) * realEmb hD (star z) := by
  rw [star_mul', map_mul]

theorem norm_units_zpow_eq_one {ε : (Order D)ˣ} (hε : (ε : Order D).norm = 1) (k : ℤ) :
    ((ε ^ k : (Order D)ˣ) : Order D).norm = 1 := by
  rw [norm_eq_one_iff] at hε ⊢
  rw [map_zpow, hε, one_zpow]

/-- Every element of positive norm is, up to a unit of norm `1`, primary. -/
theorem exists_primaryElt_mul (hD : 0 ≤ D) {ε : (Order D)ˣ} (hε1 : (ε : Order D).norm = 1)
    (hε : 1 < realEmb hD (ε : Order D)) {z : Order D} (hz : 0 < z.norm) :
    ∃ η : Order D, η.norm = 1 ∧ PrimaryElt hD (ε : Order D) (η * z) := by
  have hprod := realEmb_mul_star hD z
  -- first make the real embedding positive
  obtain ⟨s, hs, hx, hy⟩ : ∃ s : Order D, s.norm = 1 ∧ 0 < realEmb hD (s * z) ∧
      0 < realEmb hD (star (s * z)) := by
    have hne : realEmb hD z ≠ 0 := fun h ↦ by rw [h, zero_mul] at hprod; exact hz.ne' (by exact_mod_cast hprod.symm)
    rcases lt_or_gt_of_ne hne with h | h
    · refine ⟨-1, by simp, ?_, ?_⟩
      · rw [neg_one_mul, map_neg]; linarith
      · rw [neg_one_mul, star_neg, map_neg]
        have : 0 < realEmb hD z * realEmb hD (star z) := by rw [hprod]; exact_mod_cast hz
        nlinarith
    · refine ⟨1, by simp, ?_, ?_⟩
      · rw [one_mul]; exact h
      · rw [one_mul]
        have : 0 < realEmb hD z * realEmb hD (star z) := by rw [hprod]; exact_mod_cast hz
        exact pos_of_mul_pos_right this h.le
  obtain ⟨k, hk1, hk2⟩ := exists_zpow_scale hε hx hy
  have hεk := norm_units_zpow_eq_one hε1 k
  have hrk := realEmb_units_zpow hD ε k
  have hstar : realEmb hD (star ((ε ^ k : (Order D)ˣ) : Order D)) = (realEmb hD (ε : Order D) ^ k)⁻¹ := by
    have := realEmb_star_mul_of_norm_one hD hεk
    rw [hrk] at this
    exact eq_inv_of_mul_eq_one_right this
  refine ⟨((ε ^ k : (Order D)ˣ) : Order D) * s, by rw [map_mul, hεk, hs, one_mul], ?_⟩
  rw [mul_assoc]
  refine ⟨?_, ?_, ?_⟩ <;> rw [map_mul, hrk]
  · exact mul_pos (zpow_pos (by linarith) k) hx
  · rw [realEmb_star_mul, hstar]; exact hk1
  · rw [realEmb_star_mul, hstar]; exact hk2

end primary

section main

variable [Fact (IsFundamentalDiscriminant D)] [Fact (D ≠ 1)]

/-- Every unit of norm `1` times `λ` is again `formLam` of a representation of the same number. -/
theorem exists_rep_of_norm_one (hf : formDisc f = D) (ha : f.1 ≠ 0) {n : ℤ} (p : Reps f n)
    {η : Order D} (hη : η.norm = 1) :
    ∃ q : Reps f n, formLam D f q.1.1 q.1.2 = η * formLam D f p.1.1 p.1.2 := by
  obtain ⟨α, β, γ, δ, h1, hM, e₁, e₂⟩ := exists_automorph_of_norm_eq_one hf ha hη
  have hq : formLam D f (α * p.1.1 + β * p.1.2) (γ * p.1.1 + δ * p.1.2) =
      η * formLam D f p.1.1 p.1.2 := by
    simp only [formLam]; push_cast
    linear_combination (p.1.1 : Order D) * e₁ + (p.1.2 : Order D) * e₂
  have hN := norm_formLam (D := D) hf (α * p.1.1 + β * p.1.2) (γ * p.1.1 + δ * p.1.2)
  rw [hq, map_mul, hη, one_mul, norm_formLam hf, p.2] at hN
  have : formEval f (α * p.1.1 + β * p.1.2) (γ * p.1.1 + δ * p.1.2) = n :=
    (mul_left_cancel₀ ha hN).symm
  exact ⟨⟨(_, _), this⟩, hq⟩

theorem norm_formLam_pos (hf : formDisc f = D) (ha : 0 < f.1) {n : ℕ} (hn : 0 < n)
    (p : Reps f n) : 0 < (formLam D f p.1.1 p.1.2).norm := by
  rw [norm_formLam hf, p.2]
  have : (0 : ℤ) < n := by exact_mod_cast hn
  positivity

theorem primaryRep_surjective (hD : 0 < D) (hf : formDisc f = D) (ha : 0 < f.1)
    {ε : (Order D)ˣ} (hε1 : (ε : Order D).norm = 1) (hε : 1 < realEmb hD.le (ε : Order D))
    {n : ℕ} (hn : 0 < n) (P : Quot (fun p q : Reps f n ↦ RepRel f p.1 q.1)) :
    ∃ p : {p : Reps f n // IsPrimaryRep hD.le f (ε : Order D) p.1}, Quot.mk _ p.1 = P := by
  induction P using Quot.ind with
  | _ p =>
  obtain ⟨η, hη, hprim⟩ := exists_primaryElt_mul hD.le hε1 hε (norm_formLam_pos hf ha hn p)
  obtain ⟨q, hq⟩ := exists_rep_of_norm_one hf ha.ne' p hη
  refine ⟨⟨q, ?_⟩, Quot.sound ?_⟩
  · rw [isPrimaryRep_iff, hq]; exact hprim
  · exact (repRel_equivalence hf ha.ne').symm ((repRel_iff hf ha.ne').mpr ⟨η, hη, hq⟩)

theorem primaryRep_injective (hD : 0 < D) (hf : formDisc f = D) (ha : 0 < f.1)
    {ε : (Order D)ˣ} (hε1 : (ε : Order D).norm = 1) (hε : 1 < realEmb hD.le (ε : Order D))
    (hgen : ∀ u : (Order D)ˣ, (u : Order D).norm = 1 → ∃ n : ℤ, u = ε ^ n ∨ u = -ε ^ n)
    {n : ℕ} (p q : {p : Reps f n // IsPrimaryRep hD.le f (ε : Order D) p.1})
    (h : Quot.mk (fun p q : Reps f n ↦ RepRel f p.1 q.1) p.1 = Quot.mk _ q.1) : p = q := by
  obtain ⟨η, hη, e⟩ := (repRel_iff hf ha.ne').mp (repRel_of_quot_eq hf ha.ne' h)
  obtain ⟨u, hu⟩ := (isUnit_of_norm_eq_one hη)
  have hu1 : (u : Order D).norm = 1 := by rw [hu]; exact hη
  obtain ⟨k, hk⟩ := hgen u hu1
  have hη1 := realEmb_star_mul_of_norm_one hD.le hη
  obtain ⟨hp1, hp2, hp3⟩ := p.2
  obtain ⟨hq1, hq2, hq3⟩ := q.2
  rw [e, map_mul] at hq1
  have hapos : 0 < realEmb hD.le η := pos_of_mul_pos_left hq1 hp1.le
  have hηk : η = ((ε ^ k : (Order D)ˣ) : Order D) := by
    rcases hk with hk | hk
    · rw [← hu, hk]
    · exfalso
      rw [← hu, hk, Units.val_neg, map_neg, realEmb_units_zpow] at hapos
      have := zpow_pos (show (0 : ℝ) < realEmb hD.le (ε : Order D) by linarith) k
      linarith
  have hrk := realEmb_units_zpow hD.le ε k
  have hstar : realEmb hD.le (star η) = (realEmb hD.le (ε : Order D) ^ k)⁻¹ := by
    rw [hηk] at hη1 ⊢
    rw [hrk] at hη1
    exact eq_inv_of_mul_eq_one_right hη1
  rw [e, realEmb_star_mul, map_mul, hstar, hηk, hrk] at hq2 hq3
  have hk0 := eq_zero_of_primary_scale hε hp1 k hp2 hp3 hq2 hq3
  have hη1' : η = 1 := by rw [hηk, hk0]; simp
  rw [hη1', one_mul] at e
  obtain ⟨h1', h2'⟩ := mul_add_formTheta_injective ha.ne' e
  exact Subtype.ext (Subtype.ext (Prod.ext h1'.symm h2'.symm))

/-- **Davenport §6, pp. 56-57 (row 6-6).** In each orbit of representations of `n` by `f` under
the automorphs there is exactly one primary representation, so the number of primary
representations is `R_f(n)`. -/
@[kb "davenport1980" "Ch 6, p. 57"]
theorem card_primaryReps_eq_repClassCount (hD : 0 < D) (hf : formDisc f = D) (ha : 0 < f.1)
    {ε : (Order D)ˣ} (hε1 : (ε : Order D).norm = 1) (hε : 1 < realEmb hD.le (ε : Order D))
    (hgen : ∀ u : (Order D)ˣ, (u : Order D).norm = 1 → ∃ n : ℤ, u = ε ^ n ∨ u = -ε ^ n)
    {n : ℕ} (hn : 0 < n) :
    Nat.card {p : Reps f n // IsPrimaryRep hD.le f (ε : Order D) p.1} = repClassCount f n := by
  refine Nat.card_congr (Equiv.ofBijective
    (fun p ↦ Quot.mk (fun p q : Reps f n ↦ RepRel f p.1 q.1) p.1) ⟨?_, ?_⟩)
  · intro p q h
    exact primaryRep_injective hD hf ha hε1 hε hgen p q h
  · intro P
    exact primaryRep_surjective hD hf ha hε1 hε hn P

end main

end NTKB.Davenport
