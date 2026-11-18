/-
Ireland–Rosen, Chapter 10, §1: affine space inside projective space (Lemma 1, Exercises 10.2,
10.3) and the projective closure (homogenization) of a polynomial (Lemma 2).

Projective space `P^n(F)` is Mathlib's `Projectivization F (Fin (n + 1) → F)`. The affine map
`λ : a ↦ [1, a]` is `affineToProj`; a point is "at infinity" if its first coordinate vanishes.
-/
import Mathlib.LinearAlgebra.Projectivization.Cardinality
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Data.Finsupp.Fin
import NTKB.Attr

open scoped LinearAlgebra.Projectivization

set_option linter.unusedSectionVars false

namespace NTKB.IrelandRosen

section Points

variable {F : Type*} [Field F]

lemma cons_one_ne_zero {n : ℕ} (x : Fin n → F) : (Fin.cons 1 x : Fin (n + 1) → F) ≠ 0 := by
  intro h
  simpa using congrFun h 0

/-- The map `λ : F^n → P^n(F)`, `a ↦ [1, a]`. -/
noncomputable def affineToProj {n : ℕ} (x : Fin n → F) : ℙ F (Fin (n + 1) → F) :=
  Projectivization.mk F (Fin.cons 1 x) (cons_one_ne_zero x)

/-- A point of `P^n(F)` is at infinity if its first homogeneous coordinate vanishes. -/
def IsAtInfinity {n : ℕ} (P : ℙ F (Fin (n + 1) → F)) : Prop := P.rep 0 = 0

lemma rep_mk_eq {V : Type*} [AddCommGroup V] [Module F V] (v : V) (hv : v ≠ 0) :
    ∃ a : F, a ≠ 0 ∧ (Projectivization.mk F v hv).rep = a • v := by
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep F v hv
  exact ⟨(a : F), a.ne_zero, ha.symm⟩

lemma isAtInfinity_mk {n : ℕ} (v : Fin (n + 1) → F) (hv : v ≠ 0) :
    IsAtInfinity (Projectivization.mk F v hv) ↔ v 0 = 0 := by
  obtain ⟨a, ha, h⟩ := rep_mk_eq (F := F) v hv
  simp [IsAtInfinity, h, ha]

lemma not_isAtInfinity_affineToProj {n : ℕ} (x : Fin n → F) :
    ¬ IsAtInfinity (affineToProj x) := by
  simp [affineToProj, isAtInfinity_mk]

lemma rep_affineToProj {n : ℕ} (x : Fin n → F) :
    ∃ a : F, a ≠ 0 ∧ (affineToProj x).rep = a • (Fin.cons 1 x : Fin (n + 1) → F) :=
  rep_mk_eq _ _

/-- The inverse of `affineToProj` on the points not at infinity. -/
noncomputable def projToAffine {n : ℕ} (P : ℙ F (Fin (n + 1) → F)) : Fin n → F :=
  fun i => P.rep i.succ / P.rep 0

lemma projToAffine_affineToProj {n : ℕ} (x : Fin n → F) :
    projToAffine (affineToProj x) = x := by
  obtain ⟨a, ha, h⟩ := rep_affineToProj x
  funext i
  simp [projToAffine, h, ha]

lemma affineToProj_projToAffine {n : ℕ} (P : ℙ F (Fin (n + 1) → F)) (hP : ¬ IsAtInfinity P) :
    affineToProj (projToAffine P) = P := by
  conv_rhs => rw [← Projectivization.mk_rep P]
  rw [affineToProj, Projectivization.mk_eq_mk_iff']
  refine ⟨(P.rep 0)⁻¹, ?_⟩
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [IsAtInfinity] at hP
    simp [hP]
  · simp [projToAffine, div_eq_inv_mul]

/-- **Lemma 1 (§10.1)**: `λ` is a bijection from `F^n` onto the points of `P^n(F)` not at
infinity. -/
noncomputable def affineEquiv (n : ℕ) :
    (Fin n → F) ≃ {P : ℙ F (Fin (n + 1) → F) // ¬ IsAtInfinity P} where
  toFun x := ⟨affineToProj x, not_isAtInfinity_affineToProj x⟩
  invFun P := projToAffine P.1
  left_inv := projToAffine_affineToProj
  right_inv P := Subtype.ext (affineToProj_projToAffine P.1 P.2)

@[kb "irelandrosen1990" "Lemma 1 (§10.1), p. 150"]
theorem affineEquiv_symm_apply {n : ℕ} (P : {P : ℙ F (Fin (n + 1) → F) // ¬ IsAtInfinity P}) :
    (affineEquiv n).symm P = fun i => P.1.rep i.succ / P.1.rep 0 := rfl

@[kb "irelandrosen1990" "Lemma 1 (§10.1), p. 150"]
theorem affineEquiv_apply {n : ℕ} (x : Fin n → F) : ((affineEquiv n) x).1 = affineToProj x := rfl

@[kb "irelandrosen1990" "Lemma 1 (§10.1), p. 150"]
theorem affineToProj_injective {n : ℕ} : Function.Injective (affineToProj (F := F) (n := n)) :=
  fun _ _ h => (affineEquiv n).injective (Subtype.ext h)

@[kb "irelandrosen1990" "Lemma 1 (§10.1), p. 150"]
theorem range_affineToProj {n : ℕ} :
    Set.range (affineToProj (F := F) (n := n)) = {P | ¬ IsAtInfinity P} := by
  ext P
  constructor
  · rintro ⟨x, rfl⟩
    exact not_isAtInfinity_affineToProj x
  · intro hP
    exact ⟨_, affineToProj_projToAffine P hP⟩

end Points

section Infinity

variable {F : Type*} [Field F]

lemma tail_rep_ne_zero {n : ℕ} (P : ℙ F (Fin (n + 1) → F)) (hP : IsAtInfinity P) :
    (fun i : Fin n => P.rep i.succ) ≠ 0 := by
  intro h
  refine P.rep_ne_zero (funext fun i => ?_)
  refine Fin.cases ?_ (fun j => ?_) i
  · exact hP
  · exact congrFun h j

lemma cons_zero_ne_zero {n : ℕ} {w : Fin n → F} (hw : w ≠ 0) :
    (Fin.cons 0 w : Fin (n + 1) → F) ≠ 0 := by
  intro h
  exact hw (funext fun i => by simpa using congrFun h i.succ)

/-- **Exercise 10.2**: the points at infinity of `P^n(F)` form a copy of `P^{n-1}(F)`,
`[0, x₁, …, xₙ] ↦ [x₁, …, xₙ]`. -/
noncomputable def infinityEquiv (n : ℕ) :
    {P : ℙ F (Fin (n + 1) → F) // IsAtInfinity P} ≃ ℙ F (Fin n → F) where
  toFun P := Projectivization.mk F _ (tail_rep_ne_zero P.1 P.2)
  invFun Q := ⟨Projectivization.mk F (Fin.cons 0 Q.rep) (cons_zero_ne_zero Q.rep_ne_zero),
    (isAtInfinity_mk _ _).2 (by simp)⟩
  left_inv P := by
    obtain ⟨P, hP⟩ := P
    obtain ⟨a, ha, h⟩ := rep_mk_eq (F := F) _ (tail_rep_ne_zero P hP)
    refine Subtype.ext ?_
    refine Eq.trans ?_ (Projectivization.mk_rep P)
    rw [Projectivization.mk_eq_mk_iff']
    refine ⟨a, ?_⟩
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [h]; exact Or.inr hP
    · simp [h]
  right_inv Q := by
    obtain ⟨a, ha, h⟩ := rep_mk_eq (F := F) (Fin.cons 0 Q.rep : Fin (n + 1) → F)
      (cons_zero_ne_zero Q.rep_ne_zero)
    conv_rhs => rw [← Projectivization.mk_rep Q]
    simp only
    rw [Projectivization.mk_eq_mk_iff']
    refine ⟨a, ?_⟩
    funext i
    have := congrFun h i.succ
    simp_all

@[kb "irelandrosen1990" "Exercise 10.2, p. 160"]
theorem infinityEquiv_mk {n : ℕ} (v : Fin (n + 1) → F) (hv : v ≠ 0) (h0 : v 0 = 0)
    (hw : (fun i : Fin n => v i.succ) ≠ 0) :
    infinityEquiv n ⟨Projectivization.mk F v hv, (isAtInfinity_mk v hv).2 h0⟩ =
      Projectivization.mk F (fun i : Fin n => v i.succ) hw := by
  obtain ⟨a, ha, h⟩ := rep_mk_eq (F := F) v hv
  show Projectivization.mk F _ _ = _
  rw [Projectivization.mk_eq_mk_iff']
  refine ⟨a, ?_⟩
  funext i
  have := congrFun h i.succ
  simp_all

@[kb "irelandrosen1990" "Exercise 10.2, p. 160"]
theorem infinityEquiv_bijective (n : ℕ) : Function.Bijective (infinityEquiv (F := F) n) :=
  (infinityEquiv n).bijective

end Infinity

section Card

variable {F : Type*} [Field F] [Fintype F]

lemma card_proj (m : ℕ) :
    Nat.card (ℙ F (Fin m → F)) = ∑ i ∈ Finset.range m, Fintype.card F ^ i := by
  classical
  induction m with
  | zero =>
    have : IsEmpty (ℙ F (Fin 0 → F)) := ⟨fun P => P.rep_ne_zero (Subsingleton.elim _ _)⟩
    simp
  | succ n ih =>
    rw [← Nat.card_congr (Equiv.sumCompl IsAtInfinity), Nat.card_sum,
      Nat.card_congr (affineEquiv n).symm, Nat.card_congr (infinityEquiv n), ih,
      Finset.sum_range_succ]
    simp

/-- **Exercise 10.3**: `P^n(F)` has `1 + q + ⋯ + qⁿ` points. -/
@[kb "irelandrosen1990" "Exercise 10.3, p. 160"]
theorem card_projectiveSpace (n : ℕ) :
    Nat.card (ℙ F (Fin (n + 1) → F)) = ∑ i ∈ Finset.range (n + 1), Fintype.card F ^ i :=
  card_proj (n + 1)

end Card

section Homogenize

open MvPolynomial

variable {R : Type*} [CommRing R] {n : ℕ}

/-- The projective closure (homogenization) of `f`: each monomial `y^m` is replaced by
`y₀^{deg f - |m|} y^m`. -/
noncomputable def homogenize (f : MvPolynomial (Fin n) R) : MvPolynomial (Fin (n + 1)) R :=
  ∑ m ∈ f.support, monomial (Finsupp.cons (f.totalDegree - m.degree) m) (f.coeff m)

lemma degree_cons (a : ℕ) (m : Fin n →₀ ℕ) : (Finsupp.cons a m).degree = a + m.degree := by
  simp [Finsupp.degree_eq_sum, Fin.sum_univ_succ]

lemma degree_le_totalDegree {f : MvPolynomial (Fin n) R} {m : Fin n →₀ ℕ} (hm : m ∈ f.support) :
    m.degree ≤ f.totalDegree := by
  simpa [Finsupp.degree_apply, Finsupp.sum] using le_totalDegree hm

lemma coeff_homogenize_cons (f : MvPolynomial (Fin n) R) (m : Fin n →₀ ℕ) :
    (homogenize f).coeff (Finsupp.cons (f.totalDegree - m.degree) m) = f.coeff m := by
  classical
  simp only [homogenize, coeff_sum, coeff_monomial, Finsupp.cons_injective2.eq_iff]
  rw [Finset.sum_eq_single m (fun b _ hb => by simp [hb])
    (fun hm => by simp [notMem_support_iff.mp hm])]
  simp

/-- **Lemma 2 (§10.1)**: the homogenization of `f` is homogeneous of degree `deg f`. -/
@[kb "irelandrosen1990" "Lemma 2 (§10.1), p. 151"]
theorem isHomogeneous_homogenize (f : MvPolynomial (Fin n) R) :
    (homogenize f).IsHomogeneous f.totalDegree :=
  IsHomogeneous.sum _ _ _ fun m hm => isHomogeneous_monomial _ <| by
    have := degree_le_totalDegree hm
    rw [degree_cons]
    omega

@[kb "irelandrosen1990" "Lemma 2 (§10.1), p. 151"]
theorem totalDegree_homogenize (f : MvPolynomial (Fin n) R) :
    (homogenize f).totalDegree = f.totalDegree := by
  by_cases hf : f = 0
  · simp [hf, homogenize]
  obtain ⟨m, hm⟩ := (support_nonempty.2 hf)
  refine (isHomogeneous_homogenize f).totalDegree ?_
  intro h0
  have := coeff_homogenize_cons f m
  rw [h0] at this
  exact (mem_support_iff.1 hm) (by simpa using this.symm)

@[kb "irelandrosen1990" "Lemma 2 (§10.1), p. 151"]
theorem eval_cons_one_homogenize (f : MvPolynomial (Fin n) R) (y : Fin n → R) :
    eval (Fin.cons 1 y : Fin (n + 1) → R) (homogenize f) = eval y f := by
  rw [homogenize, map_sum]
  conv_rhs => rw [eval_eq']
  refine Finset.sum_congr rfl fun m _ => ?_
  simp [eval_monomial, Finsupp.prod_fintype, Fin.prod_univ_succ]

end Homogenize

end NTKB.IrelandRosen
