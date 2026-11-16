/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Davenport.Forms.Automorph
import NTKB.Elementary.QuadraticField.IdealCount

/-!
# Davenport, Chapter 6: the number of representations by a system of forms (row 6-7)

(§6, p. 57, the "basic theorem", with §6, pp. 61–62.) Let `D ≠ 1` be a fundamental discriminant,
`f = (a, b, c)` a form of discriminant `D` with `a > 0` and `n ≥ 1`.

* A representation `f(x, y) = n` gives `λ = a x + θ_f y ∈ A_f` with `N(λ) = a n`, and
  `(λ) = A_f · 𝔧` for an ideal `𝔧` of norm `n`, narrowly equivalent to `A_{f'}`,
  `f' = (a, -b, c)`. Two representations give the same `𝔧` exactly when they differ by an
  automorph of `f` (row 6-5), and every such `𝔧` arises
  (`NTKB.Davenport.card_repClasses_eq`).
* Summing over a complete system `S` of forms (one with `a > 0` in each proper class) counts every
  ideal of norm `n` once (row 6-22), so with the ideal count of quadratic fields:

  `∑_{f ∈ S} R_f(n) = ∑_{m ∣ n} (D/m)` (`NTKB.Davenport.sum_repClassCount_eq`),

  where `R_f(n)` is the number of representations of `n` by `f` up to automorphs (for `D > 0`
  these are Davenport's primary representations, one in each orbit of automorphs, row 6-6).
-/

noncomputable section

open QuadraticAlgebra NTKB.QuadraticField

namespace NTKB.Davenport

variable {D : ℤ}

/-- The representations `f(x, y) = n`. -/
def Reps (f : ℤ × ℤ × ℤ) (n : ℤ) := {p : ℤ × ℤ // formEval f p.1 p.2 = n}

/-- `q` is the image of `p` under an automorph of `f`. -/
def RepRel (f : ℤ × ℤ × ℤ) (p q : ℤ × ℤ) : Prop :=
  ∃ α β γ δ : ℤ, α * δ - β * γ = 1 ∧ formSubst f α β γ δ = f ∧
    q = (α * p.1 + β * p.2, γ * p.1 + δ * p.2)

/-- **Davenport §6, pp. 56–57.** `R_f(n)`: the number of representations of `n` by `f` up to
automorphs. -/
def repClassCount (f : ℤ × ℤ × ℤ) (n : ℤ) : ℕ :=
  Nat.card (Quot (fun p q : Reps f n ↦ RepRel f p.1 q.1))

variable {f : ℤ × ℤ × ℤ}

section rel

variable [Fact (IsFundamentalDiscriminant D)] [Fact (D ≠ 1)]

theorem repRel_iff (hf : formDisc f = D) (ha : f.1 ≠ 0) {p q : ℤ × ℤ} :
    RepRel f p q ↔ ∃ η : Order D, η.norm = 1 ∧
      formLam D f q.1 q.2 = η * formLam D f p.1 p.2 := by
  constructor
  · rintro ⟨α, β, γ, δ, h1, hM, rfl⟩
    obtain ⟨η, hη, e₁, e₂⟩ := exists_norm_eq_one_of_automorph hf ha h1 hM
    refine ⟨η, hη, ?_⟩
    simp only [formLam]; push_cast
    linear_combination (p.1 : Order D) * e₁ + (p.2 : Order D) * e₂
  · rintro ⟨η, hη, e⟩
    obtain ⟨α, β, γ, δ, h1, hM, e₁, e₂⟩ := exists_automorph_of_norm_eq_one hf ha hη
    refine ⟨α, β, γ, δ, h1, hM, ?_⟩
    have : formLam D f q.1 q.2 = formLam D f (α * p.1 + β * p.2) (γ * p.1 + δ * p.2) := by
      rw [e]; simp only [formLam]; push_cast
      linear_combination -(p.1 : Order D) * e₁ - (p.2 : Order D) * e₂
    obtain ⟨h1', h2'⟩ := mul_add_formTheta_injective ha this
    exact Prod.ext h1' h2'

theorem repRel_equivalence (hf : formDisc f = D) (ha : f.1 ≠ 0) :
    Equivalence (RepRel f) := by
  refine ⟨fun p ↦ (repRel_iff hf ha).mpr ⟨1, by simp, by simp⟩, fun {p q} h ↦ ?_,
    fun {p q r} h h' ↦ ?_⟩
  · obtain ⟨η, hη, e⟩ := (repRel_iff hf ha).mp h
    refine (repRel_iff hf ha).mpr ⟨star η, by rw [QuadraticAlgebra.norm_star, hη], ?_⟩
    have hηη : star η * η = 1 := by rw [mul_comm, ← intCast_norm, hη, Int.cast_one]
    rw [e, ← mul_assoc, hηη, one_mul]
  · obtain ⟨η, hη, e⟩ := (repRel_iff hf ha).mp h
    obtain ⟨η', hη', e'⟩ := (repRel_iff hf ha).mp h'
    refine (repRel_iff hf ha).mpr ⟨η' * η, by rw [map_mul, hη, hη', one_mul], ?_⟩
    rw [e', e, mul_assoc]

end rel

/-! ### Representations and ideals -/

section ideals

variable [hD : Fact (IsFundamentalDiscriminant D)] [hD1 : Fact (D ≠ 1)]

theorem absNorm_span_singleton_order (z : Order D) :
    Ideal.absNorm (Ideal.span {z}) = z.norm.natAbs := by
  rw [Ideal.absNorm_span_singleton, algebraNorm_order]

theorem formLam_mem (x y : ℤ) : formLam D f x y ∈ formIdeal D f := mul_add_formTheta_mem x y

theorem norm_formLam (hf : formDisc f = D) (x y : ℤ) :
    (formLam D f x y).norm = f.1 * formEval f x y := norm_mul_add_formTheta hf x y

variable (D) in
/-- The ideals of norm `n` in the narrow class of `A_g`. -/
def IdealsIn (g : ℤ × ℤ × ℤ) (n : ℕ) :=
  {J : Ideal (Order D) // Ideal.absNorm J = n ∧ NarrowRel (formIdeal D g) J}

include hD hD1 in
theorem exists_ideal_of_mem {z : Order D} (hz : z ∈ formIdeal D f) :
    ∃ J : Ideal (Order D), formIdeal D f * J = Ideal.span {z} := by
  have : formIdeal D f ∣ Ideal.span {z} :=
    Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hz)
  obtain ⟨J, hJ⟩ := this
  exact ⟨J, hJ.symm⟩

/-- The ideal `𝔧` with `A_f 𝔧 = (λ)`. -/
def repIdeal (f : ℤ × ℤ × ℤ) (x y : ℤ) : Ideal (Order D) :=
  (exists_ideal_of_mem (formLam_mem (D := D) (f := f) x y)).choose

theorem formIdeal_mul_repIdeal (x y : ℤ) :
    formIdeal D f * repIdeal (D := D) f x y = Ideal.span {formLam D f x y} :=
  (exists_ideal_of_mem (formLam_mem (D := D) (f := f) x y)).choose_spec

theorem formIdeal_ne_zero (ha : f.1 ≠ 0) : formIdeal D f ≠ 0 := formIdeal_ne_bot ha

theorem repIdeal_mem (hf : formDisc f = D) (ha : 0 < f.1) {n : ℕ} (hn : 0 < n) (p : Reps f n) :
    Ideal.absNorm (repIdeal (D := D) f p.1.1 p.1.2) = n ∧
      NarrowRel (formIdeal D (formNeg f)) (repIdeal (D := D) f p.1.1 p.1.2) := by
  have hJ := formIdeal_mul_repIdeal (D := D) (f := f) p.1.1 p.1.2
  have hN : (formLam D f p.1.1 p.1.2).norm = f.1 * n := by rw [norm_formLam hf, p.2]
  constructor
  · have := congrArg Ideal.absNorm hJ
    rw [map_mul, absNorm_formIdeal hf, absNorm_span_singleton_order, hN] at this
    have h' : f.1.natAbs * Ideal.absNorm (repIdeal (D := D) f p.1.1 p.1.2) = f.1.natAbs * n := by
      rw [this, Int.natAbs_mul]; simp
    exact Nat.eq_of_mul_eq_mul_left (Int.natAbs_pos.mpr ha.ne') h'
  · refine ⟨formLam D f p.1.1 p.1.2, (f.1 : Order D), ?_, ?_⟩
    · rw [hN, norm_intCast]
      have : (0 : ℤ) < n := by exact_mod_cast hn
      positivity
    · rw [← hJ, mul_right_comm, formIdeal_mul_formIdeal_formNeg Fact.out hf]

theorem repIdeal_eq_iff (ha : f.1 ≠ 0) {x y x' y' : ℤ} :
    repIdeal (D := D) f x y = repIdeal f x' y' ↔
      Ideal.span {formLam D f x y} = Ideal.span {formLam D f x' y'} := by
  constructor
  · intro h; rw [← formIdeal_mul_repIdeal, h, formIdeal_mul_repIdeal]
  · intro h
    exact mul_left_cancel₀ (formIdeal_ne_zero ha)
      (by rw [formIdeal_mul_repIdeal, formIdeal_mul_repIdeal, h])

theorem repRel_iff_span (hf : formDisc f = D) (ha : 0 < f.1) {n : ℕ} (hn : 0 < n)
    (p q : Reps f n) :
    RepRel f p.1 q.1 ↔ Ideal.span {formLam D f p.1.1 p.1.2} = Ideal.span {formLam D f q.1.1 q.1.2} := by
  have hNp : (formLam D f p.1.1 p.1.2).norm = f.1 * n := by rw [norm_formLam hf, p.2]
  have hNq : (formLam D f q.1.1 q.1.2).norm = f.1 * n := by rw [norm_formLam hf, q.2]
  have hN0 : f.1 * (n : ℤ) ≠ 0 := mul_ne_zero ha.ne' (by exact_mod_cast hn.ne')
  rw [repRel_iff hf ha.ne']
  constructor
  · rintro ⟨η, hη, e⟩
    have hu : IsUnit η := isUnit_iff_norm_isUnit.mpr (by rw [hη]; exact isUnit_one)
    rw [e]
    exact (Ideal.span_singleton_mul_left_unit hu _).symm
  · intro h
    obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.mp h
    refine ⟨u, ?_, by rw [← hu, mul_comm]⟩
    have := congrArg QuadraticAlgebra.norm hu
    rw [map_mul, hNp, hNq] at this
    have : f.1 * n * (u : Order D).norm = f.1 * n * 1 := by rw [this, mul_one]
    exact mul_left_cancel₀ hN0 this

/-- The map from representations up to automorphs to ideals. -/
def repToIdeal (hf : formDisc f = D) (ha : 0 < f.1) {n : ℕ} (hn : 0 < n) :
    Quot (fun p q : Reps f n ↦ RepRel f p.1 q.1) → IdealsIn D (formNeg f) n :=
  Quot.lift (fun p ↦ ⟨repIdeal f p.1.1 p.1.2, repIdeal_mem hf ha hn p⟩)
    (fun p q h ↦ Subtype.ext ((repIdeal_eq_iff ha.ne').mpr ((repRel_iff_span hf ha hn p q).mp h)))

theorem repToIdeal_injective (hf : formDisc f = D) (ha : 0 < f.1) {n : ℕ} (hn : 0 < n) :
    Function.Injective (repToIdeal hf ha hn) := by
  intro P Q h
  induction P using Quot.ind
  induction Q using Quot.ind
  rename_i p q
  have h' : repIdeal (D := D) f p.1.1 p.1.2 = repIdeal f q.1.1 q.1.2 := congrArg Subtype.val h
  exact Quot.sound ((repRel_iff_span hf ha hn p q).mpr ((repIdeal_eq_iff ha.ne').mp h'))

theorem repToIdeal_surjective (hf : formDisc f = D) (ha : 0 < f.1) {n : ℕ} (hn : 0 < n) :
    Function.Surjective (repToIdeal hf ha hn) := by
  rintro ⟨J, hJn, hrel⟩
  obtain ⟨x, y, hxy, hJ⟩ := hrel
  have hf' : formDisc (formNeg f) = D := by rw [formDisc_formNeg, hf]
  have hP := formIdeal_mul_formIdeal_formNeg Fact.out hf
  have hy : y ≠ 0 := by rintro rfl; simp at hxy
  -- `(x a) = (y) (A_f 𝔧)`
  have key : Ideal.span {x * (f.1 : Order D)} = Ideal.span {y} * (formIdeal D f * J) := by
    rw [← Ideal.span_singleton_mul_span_singleton, ← hP, mul_left_comm, hJ, mul_left_comm]
  have hmem : x * (f.1 : Order D) ∈ Ideal.span {y} * (formIdeal D f * J) :=
    by rw [← key]; exact Ideal.mem_span_singleton_self _
  obtain ⟨l, hl, hyl⟩ := Ideal.mem_span_singleton_mul.mp hmem
  have hL : formIdeal D f * J = Ideal.span {l} := by
    have hy0 : Ideal.span {y} ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hy
    refine mul_left_cancel₀ hy0 ?_
    rw [← key, Ideal.span_singleton_mul_span_singleton, hyl]
  have hlA : l ∈ formIdeal D f := Ideal.mul_le_left (I := formIdeal D f) (J := J) hl
  obtain ⟨X, Y, hXY⟩ := exists_of_mem_formIdeal hf hlA
  have hlam : l = formLam D f X Y := hXY
  -- the norm of `l`
  have hNl : l.norm = f.1 * n := by
    have h1 := congrArg Ideal.absNorm hL
    rw [map_mul, absNorm_formIdeal hf, hJn, absNorm_span_singleton_order] at h1
    have h2 := congrArg QuadraticAlgebra.norm hyl
    rw [map_mul, map_mul, norm_intCast] at h2
    have hpos : 0 < l.norm := by
      have : 0 < y.norm * y.norm * l.norm := by
        have e : y.norm * y.norm * l.norm = (x.norm * y.norm) * f.1 ^ 2 := by
          linear_combination y.norm * h2
        rw [e]; exact mul_pos hxy (by positivity)
      have hyy : 0 < y.norm * y.norm := by
        exact mul_self_pos.mpr (norm_ne_zero_of_ne_zero hy)
      exact pos_of_mul_pos_right this hyy.le
    have : (l.norm.natAbs : ℤ) = f.1 * n := by
      rw [← h1]; push_cast; rw [abs_of_pos ha]
    rwa [Int.natAbs_of_nonneg hpos.le] at this
  have hrep : formEval f X Y = n := by
    rw [hlam, norm_formLam hf] at hNl
    exact mul_left_cancel₀ ha.ne' hNl
  refine ⟨Quot.mk _ ⟨(X, Y), hrep⟩, Subtype.ext ?_⟩
  show repIdeal f X Y = J
  refine mul_left_cancel₀ (formIdeal_ne_zero ha.ne') ?_
  rw [formIdeal_mul_repIdeal, hL, hlam]

/-- **Davenport §6, pp. 61–62.** For `a > 0` and `n ≥ 1`, the representations of `n` by `f` up to
automorphs correspond to the ideals of norm `n` narrowly equivalent to `A_{f'}`. -/
theorem card_repClasses_eq (hf : formDisc f = D) (ha : 0 < f.1) {n : ℕ} (hn : 0 < n) :
    repClassCount f n = Nat.card (IdealsIn D (formNeg f) n) :=
  Nat.card_congr (Equiv.ofBijective _ ⟨repToIdeal_injective hf ha hn, repToIdeal_surjective hf ha hn⟩)

end ideals

/-! ### Summing over a complete system of forms -/

theorem formNeg_formNeg (f : ℤ × ℤ × ℤ) : formNeg (formNeg f) = f := by simp [formNeg]

theorem FormEquiv.neg {f g : ℤ × ℤ × ℤ} (h : FormEquiv f g) :
    FormEquiv (formNeg f) (formNeg g) := by
  obtain ⟨α, β, γ, δ, h1, rfl⟩ := h
  refine ⟨α, -β, -γ, δ, by linear_combination h1, ?_⟩
  simp only [formNeg, formSubst, Prod.mk.injEq]
  refine ⟨by ring, by ring, by ring⟩

section sum

variable [Fact (IsFundamentalDiscriminant D)] [Fact (D ≠ 1)]

/-- A complete system of representatives (with `a > 0`) of the proper classes of forms of
discriminant `D`. -/
def IsFormSystem (D : ℤ) (S : Finset (ℤ × ℤ × ℤ)) : Prop :=
  (∀ f ∈ S, formDisc f = D ∧ 0 < f.1) ∧
    ∀ g, formDisc g = D → 0 < g.1 → ∃! f, f ∈ S ∧ FormEquiv g f

theorem exists_mem_narrowRel {S : Finset (ℤ × ℤ × ℤ)} (hS : IsFormSystem D S)
    {J : Ideal (Order D)} (hJ : J ≠ ⊥) :
    ∃ f ∈ S, NarrowRel (formIdeal D (formNeg f)) J := by
  obtain ⟨g, hg, hga, e, he, hJe⟩ := exists_eq_span_mul_formIdeal hJ
  have hgJ : NarrowRel (formIdeal D g) J :=
    ⟨e, 1, by rw [norm_intCast, map_one, mul_one]; positivity,
      by rw [Ideal.span_singleton_one, Ideal.top_mul, hJe]⟩
  obtain ⟨f, ⟨hfS, hgf⟩, -⟩ := hS.2 (formNeg g) (by rw [formDisc_formNeg, hg]) hga
  have hfD := (hS.1 f hfS)
  refine ⟨f, hfS, NarrowRel.trans ?_ hgJ⟩
  have h' : FormEquiv (formNeg f) g := by
    have := hgf.symm.neg; rwa [formNeg_formNeg] at this
  exact narrowRel_of_formEquiv (by rw [formDisc_formNeg, hfD.1]) hfD.2 hga h'

theorem eq_of_narrowRel {S : Finset (ℤ × ℤ × ℤ)} (hS : IsFormSystem D S) {f f' : ℤ × ℤ × ℤ}
    (hf : f ∈ S) (hf' : f' ∈ S) {J : Ideal (Order D)}
    (h : NarrowRel (formIdeal D (formNeg f)) J) (h' : NarrowRel (formIdeal D (formNeg f')) J) :
    f = f' := by
  have h1 := hS.1 f hf
  have h2 := hS.1 f' hf'
  have hE := formEquiv_of_narrowRel (f := formNeg f) (g := formNeg f') (by rw [formDisc_formNeg, h1.1])
    (by rw [formDisc_formNeg, h2.1]) h1.2 h2.2 (h.trans h'.symm)
  have hE' : FormEquiv f f' := by have := hE.neg; rwa [formNeg_formNeg, formNeg_formNeg] at this
  obtain ⟨f₀, -, huniq⟩ := hS.2 f h1.1 h1.2
  exact (huniq f ⟨hf, FormEquiv.refl f⟩).trans (huniq f' ⟨hf', hE'⟩).symm

instance hasFiniteQuotients_order : Ring.HasFiniteQuotients (Order D) := .of_module_finite ℤ _

theorem finite_absNorm_eq_order (n : ℕ) : {J : Ideal (Order D) | Ideal.absNorm J = n}.Finite :=
  Ring.HasFiniteQuotients.finite_absNorm_eq n

/-- **Davenport §6, p. 57 (row 6-7), the ideal side.** For a complete system `S` of forms and
`n ≥ 1`, `∑_{f ∈ S} R_f(n)` is the number of ideals of norm `n`. -/
theorem sum_repClassCount_eq_card {S : Finset (ℤ × ℤ × ℤ)} (hS : IsFormSystem D S) {n : ℕ}
    (hn : 0 < n) :
    ∑ f ∈ S, repClassCount f n = Nat.card {J : Ideal (Order D) // Ideal.absNorm J = n} := by
  classical
  set T := (finite_absNorm_eq_order (D := D) n).toFinset
  have hT : ∀ J, J ∈ T ↔ Ideal.absNorm J = n := fun J ↦ by simp [T]
  have hne : ∀ J ∈ T, J ≠ ⊥ := fun J hJ h ↦ by
    rw [hT, h, Ideal.absNorm_bot] at hJ; omega
  let φ : Ideal (Order D) → ℤ × ℤ × ℤ := fun J ↦
    if h : J ≠ ⊥ then (exists_mem_narrowRel hS h).choose else 0
  have hφS : ∀ J ∈ T, φ J ∈ S := fun J hJ ↦ by
    simp only [φ, dite_eq_left (hne J hJ)]; exact (exists_mem_narrowRel hS (hne J hJ)).choose_spec.1
  have hφ : ∀ J ∈ T, ∀ f ∈ S, φ J = f ↔ NarrowRel (formIdeal D (formNeg f)) J := by
    intro J hJ f hf
    have hspec := (exists_mem_narrowRel hS (hne J hJ)).choose_spec
    have hφJ : φ J = (exists_mem_narrowRel hS (hne J hJ)).choose := by
      simp only [φ, dite_eq_left (hne J hJ)]
    constructor
    · rintro rfl; rw [hφJ]; exact hspec.2
    · intro h; rw [hφJ]; exact eq_of_narrowRel hS hspec.1 hf hspec.2 h
  have hcard : Nat.card {J : Ideal (Order D) // Ideal.absNorm J = n} = T.card :=
    Nat.card_eq_card_finite_toFinset (finite_absNorm_eq_order (D := D) n)
  rw [hcard, Finset.card_eq_sum_card_fiberwise hφS]
  refine Finset.sum_congr rfl fun f hf ↦ ?_
  have hfD := hS.1 f hf
  rw [card_repClasses_eq hfD.1 hfD.2 hn, ← Nat.card_eq_finsetCard]
  refine Nat.card_congr ⟨fun J ↦ ⟨J.1, ?_⟩, fun J ↦ ⟨J.1, ?_⟩, fun _ ↦ rfl, fun _ ↦ rfl⟩
  · have hJT : J.1 ∈ T := (hT _).mpr J.2.1
    exact Finset.mem_filter.mpr ⟨hJT, (hφ _ hJT f hf).mpr J.2.2⟩
  · obtain ⟨hJT, hJf⟩ := Finset.mem_filter.mp J.2
    exact ⟨(hT _).mp hJT, (hφ _ hJT f hf).mp hJf⟩

end sum

end NTKB.Davenport
