/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Davenport.Forms.Units

/-!
# Davenport, Chapter 6: the basic theorem for any complete system of forms (row 6-7)

`R_f(n)`, the number of representations of `n` by `f` up to automorphs, depends only on the proper
class of `f` (`NTKB.Davenport.repClassCount_eq_of_formEquiv`): a proper equivalence `g = f ∘ M`
maps representations by `g` to representations by `f`, and `a x + θ y` changes by the fixed factor
`a / ū`. So Davenport's basic theorem holds for every complete system of representatives of the
proper classes of forms of discriminant `d` (positive definite if `d < 0`),
`NTKB.Davenport.sum_repClassCount_eq_of_isDavFormSystem`.
-/

noncomputable section

open QuadraticAlgebra NTKB.QuadraticField

namespace NTKB.Davenport

variable {D : ℤ}

section invariance

variable [Fact (IsFundamentalDiscriminant D)] [Fact (D ≠ 1)] {f : ℤ × ℤ × ℤ} {α β γ δ : ℤ}

theorem star_mul_formLam_formSubst (hf : formDisc f = D) (h1 : α * δ - β * γ = 1) (x y : ℤ) :
    star ((f.1 : Order D) * α + formTheta D f * γ) * formLam D f (α * x + β * y) (γ * x + δ * y) =
      (f.1 : Order D) * formLam D (formSubst f α β γ δ) x y := by
  obtain ⟨huu, huv⟩ := star_mul_formTheta_eq (α := α) (β := β) (γ := γ) (δ := δ) hf h1
  have e : formLam D f (α * x + β * y) (γ * x + δ * y) =
      ((f.1 : Order D) * α + formTheta D f * γ) * x + ((f.1 : Order D) * β + formTheta D f * δ) * y := by
    simp only [formLam]; push_cast; ring
  rw [e, mul_add, ← mul_assoc, ← mul_assoc, huu, huv]
  simp only [formLam]; ring

theorem formSubst_fst_ne_zero (hf : formDisc f = D) (h1 : α * δ - β * γ = 1) :
    (formSubst f α β γ δ).1 ≠ 0 :=
  fst_ne_zero_of_not_isSquare (by
    rw [formDisc_formSubst, h1, one_pow, one_mul, hf]; exact not_isSquare Fact.out Fact.out)

theorem repRel_formSubst_iff (hf : formDisc f = D) (h1 : α * δ - β * γ = 1) {p q : ℤ × ℤ} :
    RepRel (formSubst f α β γ δ) p q ↔
      RepRel f (α * p.1 + β * p.2, γ * p.1 + δ * p.2) (α * q.1 + β * q.2, γ * q.1 + δ * q.2) := by
  have ha : f.1 ≠ 0 := fst_ne_zero_of_not_isSquare (by rw [hf]; exact not_isSquare Fact.out Fact.out)
  have hg : formDisc (formSubst f α β γ δ) = D := by rw [formDisc_formSubst, h1, one_pow, one_mul, hf]
  have hga := formSubst_fst_ne_zero hf h1
  set u : Order D := (f.1 : Order D) * α + formTheta D f * γ
  have hu0 : star u ≠ 0 := by
    intro h
    have := congrArg QuadraticAlgebra.norm h
    rw [QuadraticAlgebra.norm_star, QuadraticAlgebra.norm_zero, norm_mul_add_formTheta hf] at this
    have h' : formEval f α γ = (formSubst f α β γ δ).1 := by simp only [formEval, formSubst]
    rw [h'] at this
    exact mul_ne_zero ha hga this
  have hfa : ((f.1 : ℤ) : Order D) ≠ 0 := fun h ↦ ha (intCast_injective_order (D := D) (by simpa using h))
  have cp := star_mul_formLam_formSubst (α := α) (β := β) (γ := γ) (δ := δ) hf h1 p.1 p.2
  have cq := star_mul_formLam_formSubst (α := α) (β := β) (γ := γ) (δ := δ) hf h1 q.1 q.2
  rw [repRel_iff hg hga, repRel_iff hf ha]
  constructor
  · rintro ⟨η, hη, e⟩
    refine ⟨η, hη, mul_left_cancel₀ hu0 ?_⟩
    simp only
    rw [cq, e, mul_left_comm, ← cp]; ring
  · rintro ⟨η, hη, e⟩
    refine ⟨η, hη, mul_left_cancel₀ hfa ?_⟩
    simp only at e
    rw [← cq, e, mul_left_comm, cp]; ring

/-- The substitution `p ↦ M p` from representations by `f ∘ M` to representations by `f`. -/
def repsSubstEquiv (h1 : α * δ - β * γ = 1) (n : ℤ) :
    Reps (formSubst f α β γ δ) n ≃ Reps f n where
  toFun p := ⟨(α * p.1.1 + β * p.1.2, γ * p.1.1 + δ * p.1.2), by
    rw [← formEval_formSubst]; exact p.2⟩
  invFun q := ⟨(δ * q.1.1 - β * q.1.2, -γ * q.1.1 + α * q.1.2), by
    simp only
    rw [formEval_formSubst]
    have e1 : α * (δ * q.1.1 - β * q.1.2) + β * (-γ * q.1.1 + α * q.1.2) = q.1.1 := by
      linear_combination q.1.1 * h1
    have e2 : γ * (δ * q.1.1 - β * q.1.2) + δ * (-γ * q.1.1 + α * q.1.2) = q.1.2 := by
      linear_combination q.1.2 * h1
    rw [e1, e2]; exact q.2⟩
  left_inv p := by
    apply Subtype.ext; apply Prod.ext <;> simp only
    · linear_combination p.1.1 * h1
    · linear_combination p.1.2 * h1
  right_inv q := by
    apply Subtype.ext; apply Prod.ext <;> simp only
    · linear_combination q.1.1 * h1
    · linear_combination q.1.2 * h1

/-- **`R_f(n)` is a class invariant.** -/
theorem repClassCount_formSubst (hf : formDisc f = D) (h1 : α * δ - β * γ = 1) (n : ℤ) :
    repClassCount (formSubst f α β γ δ) n = repClassCount f n := by
  unfold repClassCount
  exact Nat.card_congr (Quot.congr (repsSubstEquiv h1 n) fun p q ↦ repRel_formSubst_iff hf h1)

theorem repClassCount_eq_of_formEquiv (hf : formDisc f = D) {g : ℤ × ℤ × ℤ} (h : FormEquiv f g)
    (n : ℤ) : repClassCount g n = repClassCount f n := by
  obtain ⟨α, β, γ, δ, h1, rfl⟩ := h
  exact repClassCount_formSubst hf h1 n

end invariance

/-- A complete system of representatives of the proper classes of forms of discriminant `D`
(positive definite if `D < 0`), as in Davenport. -/
def IsDavFormSystem (D : ℤ) (S : Finset (ℤ × ℤ × ℤ)) : Prop :=
  (∀ f ∈ S, formDisc f = D ∧ (D < 0 → 0 < f.1)) ∧
    ∀ g, formDisc g = D → (D < 0 → 0 < g.1) → ∃! f, f ∈ S ∧ FormEquiv g f

/-- **Davenport §6, p. 57 (row 6-7): the basic theorem.** Let `d ≠ 1` be a fundamental
discriminant and `S` any complete system of representatives of the proper classes of forms of
discriminant `d` (positive definite if `d < 0`). For every `n ≥ 1` the number of representations of
`n` by the forms of `S`, counted up to automorphs, is `∑_{m ∣ n} (d/m)`. -/
@[kb "davenport1980" "Ch 6, p. 57"]
theorem sum_repClassCount_eq_of_isDavFormSystem (hD : IsFundamentalDiscriminant D) (h1 : D ≠ 1)
    {S : Finset (ℤ × ℤ × ℤ)} (hS : IsDavFormSystem D S) {n : ℕ} (hn : 0 < n) :
    ((∑ f ∈ S, repClassCount f n : ℕ) : ℂ) = ∑ m ∈ n.divisors, kroneckerChar D m := by
  classical
  have : Fact (IsFundamentalDiscriminant D) := ⟨hD⟩
  have : Fact (D ≠ 1) := ⟨h1⟩
  have hnsq := not_isSquare hD h1
  -- a representative with `a > 0` of each class
  have hpos : ∀ f ∈ S, ∃ g, FormEquiv f g ∧ 0 < g.1 := by
    intro f hf
    obtain ⟨hfD, hfa⟩ := hS.1 f hf
    rcases lt_or_gt_of_ne (show D ≠ 0 from hD.ne_zero) with hneg | hposD
    · exact ⟨f, FormEquiv.refl f, hfa hneg⟩
    · exact exists_formEquiv_pos (by rw [hfD]; exact hnsq) (by rw [hfD]; exact hposD)
  let r : ℤ × ℤ × ℤ → ℤ × ℤ × ℤ := fun f ↦ if h : f ∈ S then (hpos f h).choose else f
  have hr : ∀ f ∈ S, FormEquiv f (r f) ∧ 0 < (r f).1 := fun f hf ↦ by
    simp only [r, dite_eq_left hf]; exact (hpos f hf).choose_spec
  have huniq : ∀ f₁ ∈ S, ∀ f₂ ∈ S, FormEquiv f₁ f₂ → f₁ = f₂ := by
    intro f₁ h₁ f₂ h₂ h
    obtain ⟨_, -, hu⟩ := hS.2 f₁ (hS.1 f₁ h₁).1 (hS.1 f₁ h₁).2
    exact (hu f₁ ⟨h₁, FormEquiv.refl _⟩).trans (hu f₂ ⟨h₂, h⟩).symm
  have hinj : Set.InjOn r S := fun f₁ h₁ f₂ h₂ h ↦
    huniq f₁ h₁ f₂ h₂ ((hr f₁ h₁).1.trans (h ▸ (hr f₂ h₂).1.symm))
  have hS' : IsFormSystem D (S.image r) := by
    refine ⟨fun g hg ↦ ?_, fun g hgD hga ↦ ?_⟩
    · obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hg
      exact ⟨by rw [(hr f hf).1.formDisc_eq, (hS.1 f hf).1], (hr f hf).2⟩
    · obtain ⟨f, ⟨hf, hgf⟩, -⟩ := hS.2 g hgD (fun _ ↦ hga)
      refine ⟨r f, ⟨Finset.mem_image_of_mem r hf, hgf.trans (hr f hf).1⟩, ?_⟩
      rintro g' ⟨hg', hgg'⟩
      obtain ⟨f', hf', rfl⟩ := Finset.mem_image.mp hg'
      have : f = f' := huniq f hf f' hf'
        ((hgf.symm.trans hgg').trans (hr f' hf').1.symm)
      rw [this]
  have hsum : ∑ f ∈ S, repClassCount f n = ∑ g ∈ S.image r, repClassCount g n := by
    rw [Finset.sum_image hinj]
    refine Finset.sum_congr rfl fun f hf ↦ ?_
    exact (repClassCount_eq_of_formEquiv (hS.1 f hf).1 (hr f hf).1 n).symm
  rw [hsum]
  exact sum_repClassCount_eq hD h1 hS' hn

end NTKB.Davenport
