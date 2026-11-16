/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Davenport.Forms.Ideal

/-!
# Davenport, Chapter 6: forms and ideal classes in the narrow sense

(§6, pp. 61–62, rows 6-20, 6-21, 6-22.) For a fundamental discriminant `D ≠ 1` and
`O = ℤ[ω] = NTKB.QuadraticField.Order D`:

* two nonzero ideals `𝔞, 𝔟` are *narrowly equivalent* (`NTKB.Davenport.NarrowRel`) if
  `(x) 𝔞 = (y) 𝔟` with `N(x) N(y) > 0`; this is Davenport's `𝔞 = (λ) 𝔟`, `N(λ) > 0`, with
  `λ = y / x` (row 6-21);
* for a form `f = (a, b, c)` of discriminant `D` with `a > 0`, the class of `A_f = (a, θ_f)` depends
  only on the proper class of `f` (row 6-20, `NTKB.Davenport.span_star_mul_formIdeal`);
* `f ↦ [A_f]` is a bijection from proper classes of forms with `a > 0` onto narrow ideal classes
  (row 6-22, `NTKB.Davenport.posFormClassToNarrow_bijective`): injective by comparing two bases of
  `x A_f = y A_g` (`NTKB.Davenport.formEquiv_of_narrowRel`), surjective because every nonzero
  ideal is `e · A_f` (Hermite normal form, `NTKB.Davenport.exists_eq_span_mul_formIdeal`).

Self-contained, on the model `QuadraticAlgebra ℤ (D / 4) (D % 4)`; Tau Ceti proves the
correspondence for every order (`properClassEquivNarrowPic`), not copied here.
-/

noncomputable section

open QuadraticAlgebra NTKB.QuadraticField

namespace NTKB.Davenport

variable {D : ℤ}

/-! ### Algebra in `O` -/

/-- `√D = 2ω - σ`. -/
def sqrtD (D : ℤ) : Order D := ⟨-(D % 4), 2⟩

theorem formTheta_sub_star (f : ℤ × ℤ × ℤ) : formTheta D f - star (formTheta D f) = sqrtD D := by
  ext <;> simp [sqrtD, star_mk, formTheta] <;> ring

theorem intCast_mul_sqrtD_eq_zero {n : ℤ} (h : (n : Order D) * sqrtD D = 0) : n = 0 := by
  have := congrArg QuadraticAlgebra.im h
  simp [sqrtD] at this
  exact this

theorem norm_sqrtD (hD : D % 4 * (D % 4) = D % 4) : (sqrtD D).norm = -D := by
  rw [norm_def]; simp only [sqrtD]
  have hq : D % 4 + 4 * (D / 4) = D := by omega
  linear_combination -hD - hq

theorem intCast_norm (z : Order D) : ((z.norm : ℤ) : Order D) = z * star z := by
  rw [← algebraMap_norm_eq_mul_star]; rfl

theorem star_formTheta {f : ℤ × ℤ × ℤ} (hf : formDisc f = D) :
    star (formTheta D f) = (f.2.1 : Order D) - formTheta D f := by
  have h := algebraMap_trace_eq_add_star (formTheta D f)
  rw [trace_formTheta hf] at h
  change ((f.2.1 : ℤ) : Order D) = _ at h
  rw [h]; ring

theorem formTheta_mul_star {f : ℤ × ℤ × ℤ} (hf : formDisc f = D) :
    formTheta D f * star (formTheta D f) = ((f.1 * f.2.2 : ℤ) : Order D) := by
  rw [← intCast_norm, norm_formTheta hf]

theorem span_singleton_mul_pair (x y z : Order D) :
    Ideal.span {x} * Ideal.span {y, z} = Ideal.span {x * y, x * z} := by
  rw [Ideal.span_mul_span]
  congr 1
  ext w
  simp

/-! ### Narrow equivalence -/

/-- Davenport's narrow equivalence of ideals: `(x) 𝔞 = (y) 𝔟` with `N(x) N(y) > 0`. -/
def NarrowRel (I J : Ideal (Order D)) : Prop :=
  ∃ x y : Order D, 0 < x.norm * y.norm ∧ Ideal.span {x} * I = Ideal.span {y} * J

theorem NarrowRel.refl (I : Ideal (Order D)) : NarrowRel I I := ⟨1, 1, by simp, rfl⟩

theorem NarrowRel.symm {I J : Ideal (Order D)} (h : NarrowRel I J) : NarrowRel J I := by
  obtain ⟨x, y, hxy, h⟩ := h
  exact ⟨y, x, by rwa [mul_comm], h.symm⟩

theorem NarrowRel.trans {I J L : Ideal (Order D)} (h₁ : NarrowRel I J) (h₂ : NarrowRel J L) :
    NarrowRel I L := by
  obtain ⟨x, y, hxy, h⟩ := h₁
  obtain ⟨x', y', hxy', h'⟩ := h₂
  refine ⟨x * x', y * y', ?_, ?_⟩
  · rw [map_mul, map_mul]
    nlinarith [mul_pos hxy hxy']
  · rw [← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_mul_span_singleton,
      mul_comm (Ideal.span {x}), mul_assoc, h, ← mul_assoc, mul_comm (Ideal.span {x'}), mul_assoc,
      h', mul_assoc]

/-! ### Row 6-20: the class of `A_f` depends only on the proper class of `f` -/

section welldefined

variable {f : ℤ × ℤ × ℤ} {α β γ δ : ℤ}

theorem formShift_sub_formShift (hf : formDisc f = D) (h1 : α * δ - β * γ = 1) :
    formShift D f - formShift D (formSubst f α β γ δ) =
      f.1 * α * β + f.2.1 * β * γ + f.2.2 * γ * δ := by
  have hg : formDisc (formSubst f α β γ δ) = D := by rw [formDisc_formSubst, h1]; simpa using hf
  have h := two_mul_formShift hf
  have h' := two_mul_formShift hg
  have hb : (formSubst f α β γ δ).2.1 =
      2 * f.1 * α * β + f.2.1 * (α * δ + β * γ) + 2 * f.2.2 * γ * δ := rfl
  rw [hb] at h'
  have : 2 * (formShift D f - formShift D (formSubst f α β γ δ)) =
      2 * (f.1 * α * β + f.2.1 * β * γ + f.2.2 * γ * δ) := by
    linear_combination h - h' + f.2.1 * h1
  linarith

/-- For `u = a α + θ_f γ`, `v = a β + θ_f δ` (determinant `1`, `g = f ∘ (α β; γ δ)`):
`ū u = a a'` and `ū v = a θ_g`. -/
theorem star_mul_formTheta_eq (hf : formDisc f = D) (h1 : α * δ - β * γ = 1) :
    star ((f.1 : Order D) * α + formTheta D f * γ) * ((f.1 : Order D) * α + formTheta D f * γ) =
        (f.1 : Order D) * (formSubst f α β γ δ).1 ∧
      star ((f.1 : Order D) * α + formTheta D f * γ) * ((f.1 : Order D) * β + formTheta D f * δ) =
        (f.1 : Order D) * formTheta D (formSubst f α β γ δ) := by
  set θ := formTheta D f
  set u : Order D := (f.1 : Order D) * α + θ * γ
  set v : Order D := (f.1 : Order D) * β + θ * δ
  have h1' : ((α : Order D) * δ - β * γ) = 1 := by exact_mod_cast h1
  have hstar : star θ = (f.2.1 : Order D) - θ := star_formTheta hf
  have hθθ : θ * ((f.2.1 : Order D) - θ) = (f.1 : Order D) * f.2.2 := by
    rw [← hstar, formTheta_mul_star hf]; push_cast; ring
  have hsu : star u = (f.1 : Order D) * α + ((f.2.1 : Order D) - θ) * γ := by
    simp only [u, star_add, star_mul, star_intCast, hstar]; ring
  have huu : star u * u = (f.1 : Order D) * (formSubst f α β γ δ).1 := by
    rw [mul_comm, ← intCast_norm, norm_mul_add_formTheta hf]
    simp only [formEval, formSubst]; push_cast; ring
  have hθg : formTheta D (formSubst f α β γ δ) =
      θ + ((f.1 * α * β + f.2.1 * β * γ + f.2.2 * γ * δ : ℤ) : Order D) := by
    rw [← formShift_sub_formShift hf h1]
    ext <;> simp [θ, formTheta] <;> ring
  have huv : star u * v = (f.1 : Order D) * formTheta D (formSubst f α β γ δ) := by
    rw [hsu, hθg]; simp only [v]; push_cast
    linear_combination (γ * δ : Order D) * hθθ + (f.1 : Order D) * θ * h1'
  exact ⟨huu, huv⟩

/-- **Davenport §6, p. 61 (row 6-20).** If `g = f ∘ (α β; γ δ)` (determinant `1`) and
`u = a α + θ_f γ`, then `ū · A_f = a · A_g`. -/
theorem span_star_mul_formIdeal (hf : formDisc f = D) (h1 : α * δ - β * γ = 1) :
    Ideal.span {star ((f.1 : Order D) * α + formTheta D f * γ)} * formIdeal D f =
      Ideal.span {((f.1 : ℤ) : Order D)} * formIdeal D (formSubst f α β γ δ) := by
  set θ := formTheta D f
  set u : Order D := (f.1 : Order D) * α + θ * γ
  set v : Order D := (f.1 : Order D) * β + θ * δ
  have h1' : ((α : Order D) * δ - β * γ) = 1 := by exact_mod_cast h1
  have hspan : formIdeal D f = Ideal.span {u, v} := by
    apply le_antisymm
    · rw [formIdeal, Ideal.span_le]
      intro w hw
      rcases hw with rfl | rfl
      · have : ((f.1 : ℤ) : Order D) = δ * u - γ * v := by
          simp only [u, v]; linear_combination -(f.1 : Order D) * h1'
        rw [this]
        exact sub_mem (Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert _ _)))
          (Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert_of_mem _ rfl)))
      · have : formTheta D f = -β * u + α * v := by
          simp only [u, v]; linear_combination -θ * h1'
        rw [this]
        exact add_mem (Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert _ _)))
          (Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert_of_mem _ rfl)))
    · rw [Ideal.span_le]
      intro w hw
      rcases hw with rfl | rfl
      · exact mul_add_formTheta_mem α γ
      · exact mul_add_formTheta_mem β δ
  obtain ⟨huu, huv⟩ := star_mul_formTheta_eq (α := α) (β := β) (γ := γ) (δ := δ) hf h1
  rw [hspan, span_singleton_mul_pair, huu, huv, formIdeal, span_singleton_mul_pair]

/-- `N(ū) N(a) > 0`. -/
theorem norm_star_mul_pos (hf : formDisc f = D) (ha : 0 < f.1)
    (hga : 0 < (formSubst f α β γ δ).1) :
    0 < (star ((f.1 : Order D) * α + formTheta D f * γ)).norm * ((f.1 : ℤ) : Order D).norm := by
  rw [QuadraticAlgebra.norm_star, norm_mul_add_formTheta hf, norm_intCast]
  have : formEval f α γ = (formSubst f α β γ δ).1 := by simp only [formEval, formSubst]
  rw [this]; positivity

theorem narrowRel_of_formEquiv {f g : ℤ × ℤ × ℤ} (hf : formDisc f = D) (ha : 0 < f.1)
    (hg : 0 < g.1) (h : FormEquiv f g) : NarrowRel (formIdeal D f) (formIdeal D g) := by
  obtain ⟨α, β, γ, δ, h1, rfl⟩ := h
  exact ⟨_, _, norm_star_mul_pos hf ha hg, span_star_mul_formIdeal hf h1⟩

end welldefined

/-! ### Injectivity: two bases of `x A_f = y A_g` -/

section injective

variable {f g : ℤ × ℤ × ℤ}

/-- If `(x) A_f = (y) A_g`, there is an integral matrix `(α β; γ δ)` with
`N(y) a' = (αδ - βγ) N(x) a` and `N(y) a' g(X, Y) = N(x) a f(αX + βY, γX + δY)`. -/
theorem exists_matrix_of_span_mul_eq (hf : formDisc f = D) (hg : formDisc g = D) {x y : Order D}
    (h : Ideal.span {x} * formIdeal D f = Ideal.span {y} * formIdeal D g) :
    ∃ α β γ δ : ℤ, y.norm * g.1 = (α * δ - β * γ) * (x.norm * f.1) ∧
      ∀ X Y, y.norm * g.1 * formEval g X Y =
        x.norm * f.1 * formEval f (α * X + β * Y) (γ * X + δ * Y) := by
  have m1 : y * (g.1 : Order D) ∈ Ideal.span {x} * formIdeal D f := by
    rw [h]; exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self y) intCast_mem_formIdeal
  have m2 : y * formTheta D g ∈ Ideal.span {x} * formIdeal D f := by
    rw [h]; exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self y) formTheta_mem_formIdeal
  obtain ⟨w₁, hw₁, e₁⟩ := Ideal.mem_span_singleton_mul.mp m1
  obtain ⟨w₂, hw₂, e₂⟩ := Ideal.mem_span_singleton_mul.mp m2
  obtain ⟨α, γ, rfl⟩ := exists_of_mem_formIdeal hf hw₁
  obtain ⟨β, δ, rfl⟩ := exists_of_mem_formIdeal hf hw₂
  refine ⟨α, β, γ, δ, ?_, fun X Y ↦ ?_⟩
  · -- the conjugate determinant `p q̄ - p̄ q`
    set θ := formTheta D f
    set θ' := formTheta D g
    have hθ := formTheta_sub_star (D := D) f
    have hθ' := formTheta_sub_star (D := D) g
    have key : (y * g.1) * star (y * θ') - star (y * g.1) * (y * θ') =
        (x * (f.1 * α + θ * γ)) * star (x * (f.1 * β + θ * δ)) -
          star (x * (f.1 * α + θ * γ)) * (x * (f.1 * β + θ * δ)) := by
      rw [← e₁, ← e₂]
    have hy : y * star y = (y.norm : Order D) := (intCast_norm y).symm
    have hx : x * star x = (x.norm : Order D) := (intCast_norm x).symm
    have lhs : (y * g.1) * star (y * θ') - star (y * g.1) * (y * θ') =
        -((y.norm * g.1 : ℤ) : Order D) * sqrtD D := by
      simp only [star_mul, star_intCast]
      rw [← hθ']; push_cast; rw [← hy]; ring
    have rhs : (x * (f.1 * α + θ * γ)) * star (x * (f.1 * β + θ * δ)) -
        star (x * (f.1 * α + θ * γ)) * (x * (f.1 * β + θ * δ)) =
          -(((α * δ - β * γ) * (x.norm * f.1) : ℤ) : Order D) * sqrtD D := by
      simp only [star_mul, star_add, star_intCast]
      rw [← hθ]; push_cast; rw [← hx]; ring
    rw [lhs, rhs] at key
    have : ((y.norm * g.1 - (α * δ - β * γ) * (x.norm * f.1) : ℤ) : Order D) * sqrtD D = 0 := by
      push_cast at key ⊢; linear_combination -key
    exact sub_eq_zero.mp (intCast_mul_sqrtD_eq_zero this)
  · have e : y * ((g.1 : Order D) * X + formTheta D g * Y) =
        x * ((f.1 : Order D) * ((α * X + β * Y : ℤ) : Order D) +
          formTheta D f * ((γ * X + δ * Y : ℤ) : Order D)) := by
      have : y * ((g.1 : Order D) * X + formTheta D g * Y) =
          (y * g.1) * X + (y * formTheta D g) * Y := by ring
      rw [this, ← e₁, ← e₂]; push_cast; ring
    have hn := congrArg QuadraticAlgebra.norm e
    rw [map_mul, map_mul, norm_mul_add_formTheta hg, norm_mul_add_formTheta hf] at hn
    linear_combination hn

/-- **Davenport §6, p. 62 (row 6-22), injectivity.** If `A_f` and `A_g` are narrowly equivalent
(`a, a' > 0`), then `f` and `g` are properly equivalent. -/
theorem formEquiv_of_narrowRel (hf : formDisc f = D) (hg : formDisc g = D) (ha : 0 < f.1)
    (hb : 0 < g.1) (h : NarrowRel (formIdeal D f) (formIdeal D g)) : FormEquiv f g := by
  obtain ⟨x, y, hxy, h⟩ := h
  obtain ⟨α, β, γ, δ, hd, hv⟩ := exists_matrix_of_span_mul_eq hf hg h
  obtain ⟨α', β', γ', δ', hd', -⟩ := exists_matrix_of_span_mul_eq hg hf h.symm
  have hx : x.norm ≠ 0 := by rintro h0; simp [h0] at hxy
  have hP : x.norm * f.1 ≠ 0 := mul_ne_zero hx ha.ne'
  have hdet : (α * δ - β * γ) * (α' * δ' - β' * γ') = 1 := by
    have : (x.norm * f.1) * 1 = (x.norm * f.1) * ((α * δ - β * γ) * (α' * δ' - β' * γ')) := by
      rw [hd] at hd'; linear_combination hd'
    exact (mul_left_cancel₀ hP this).symm
  have h1 : α * δ - β * γ = 1 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one hdet with h | h
    · exact h
    · exfalso
      rw [h] at hd
      have e : x.norm * y.norm * g.1 = -(x.norm ^ 2 * f.1) := by linear_combination x.norm * hd
      have h2 : 0 < x.norm * y.norm * g.1 := mul_pos hxy hb
      have h3 : 0 < x.norm ^ 2 * f.1 :=
        mul_pos (lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hx))) ha
      linarith
  refine ⟨α, β, γ, δ, h1, eq_of_formEval_eq fun X Y ↦ ?_⟩
  rw [formEval_formSubst]
  have := hv X Y
  rw [hd, h1, one_mul] at this
  exact mul_left_cancel₀ hP this

end injective

/-! ### Surjectivity: every nonzero ideal is `e · A_f` -/

theorem Int.exists_pos_mem_iff_dvd {I : Ideal ℤ} (hI : I ≠ ⊥) :
    ∃ a : ℤ, 0 < a ∧ ∀ r, r ∈ I ↔ a ∣ r := by
  obtain ⟨g, hg⟩ : ∃ g, I = Ideal.span {g} :=
    ⟨_, (Submodule.IsPrincipal.span_singleton_generator I).symm⟩
  have hg0 : g ≠ 0 := by rintro rfl; exact hI (by rw [hg, Ideal.span_singleton_eq_bot])
  refine ⟨|g|, abs_pos.mpr hg0, fun r ↦ ?_⟩
  rw [hg, Ideal.mem_span_singleton, abs_dvd]

/-- The imaginary part, as a `ℤ`-linear map. -/
def imLinear (D : ℤ) : Order D →ₗ[ℤ] ℤ where
  toFun z := z.im
  map_add' := by simp
  map_smul' := by simp

section surjective

variable [Fact (IsFundamentalDiscriminant D)] [Fact (D ≠ 1)]

theorem emod_four_mul_self_of_fact : D % 4 * (D % 4) = D % 4 := by
  rcases emod_four_of_isFundamental (Fact.out : IsFundamentalDiscriminant D) with h | h <;>
    rw [h] <;> norm_num

theorem norm_ne_zero_of_ne_zero {z : Order D} (hz : z ≠ 0) : z.norm ≠ 0 := by
  intro h0
  have : z * star z = 0 := by rw [← intCast_norm, h0, Int.cast_zero]
  rcases mul_eq_zero.mp this with h | h
  · exact hz h
  · exact hz (star_eq_zero.mp h)

/-- **Hermite normal form.** Every nonzero ideal of `O` is `e · A_f` for an integer `e > 0` and a
form `f = (a, b, c)` of discriminant `D` with `a > 0`. -/
theorem exists_eq_span_mul_formIdeal {J : Ideal (Order D)} (hJ : J ≠ ⊥) :
    ∃ f : ℤ × ℤ × ℤ, formDisc f = D ∧ 0 < f.1 ∧ ∃ e : ℤ, 0 < e ∧
      J = Ideal.span {(e : Order D)} * formIdeal D f := by
  classical
  have hσ : D % 4 * (D % 4) = D % 4 := emod_four_mul_self_of_fact
  have hq : D % 4 + 4 * (D / 4) = D := by omega
  obtain ⟨z, hzJ, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hJ
  have hNz : (z.norm : Order D) ∈ J := by rw [intCast_norm]; exact J.mul_mem_right _ hzJ
  -- the integers of `J` are `a ℤ`
  have hI : J.comap (Int.castRingHom (Order D)) ≠ ⊥ := by
    intro h
    have : z.norm ∈ J.comap (Int.castRingHom (Order D)) := hNz
    rw [h, Ideal.mem_bot] at this
    exact norm_ne_zero_of_ne_zero hz0 this
  obtain ⟨a, ha, memI⟩ := Int.exists_pos_mem_iff_dvd hI
  have memI' : ∀ r : ℤ, (r : Order D) ∈ J ↔ a ∣ r := fun r ↦ memI r
  have haJ : (a : Order D) ∈ J := (memI' a).mpr dvd_rfl
  -- the imaginary parts of `J` are `e ℤ`
  set E : Ideal ℤ := (J.restrictScalars ℤ).map (imLinear D)
  have memE0 : ∀ r : ℤ, r ∈ E ↔ ∃ w ∈ J, w.im = r := by
    intro r; simp [E, imLinear]
  have hE : E ≠ ⊥ := by
    intro h
    have : a ∈ E := (memE0 a).mpr ⟨ω * (a : Order D), J.mul_mem_left _ haJ, by simp⟩
    rw [h, Ideal.mem_bot] at this
    exact ha.ne' this
  obtain ⟨e, he, memE⟩ := Int.exists_pos_mem_iff_dvd hE
  have memE' : ∀ r : ℤ, (∃ w ∈ J, w.im = r) ↔ e ∣ r := fun r ↦ (memE0 r).symm.trans (memE r)
  obtain ⟨z₀, hz₀J, hz₀⟩ := (memE' e).mpr dvd_rfl
  have hea : e ∣ a := (memE' a).mp ⟨ω * (a : Order D), J.mul_mem_left _ haJ, by simp⟩
  have her : e ∣ z₀.re := by
    have h := (memE' _).mp ⟨ω * z₀, J.mul_mem_left _ hz₀J, rfl⟩
    simp only [im_mul, re_omega, im_omega, hz₀] at h
    have : e ∣ D % 4 * e := dvd_mul_left _ _
    have h' := dvd_sub h this
    simpa using h'
  obtain ⟨a', rfl⟩ := hea
  obtain ⟨r, hr⟩ := her
  have ha' : 0 < a' := pos_of_mul_pos_right ha he.le
  set k := -r with hk
  set N₀ := k * k - D % 4 * k - D / 4 with hN₀
  have hz₀eq : z₀ = ⟨-(e * k), e⟩ := by ext <;> simp [hr, hz₀, hk]
  -- `a' ∣ N(ω - k)`
  have hdiv : a' ∣ N₀ := by
    have hw : ω * z₀ - ((D % 4 - k : ℤ) : Order D) * z₀ ∈ J :=
      sub_mem (J.mul_mem_left _ hz₀J) (J.mul_mem_left _ hz₀J)
    have : ω * z₀ - ((D % 4 - k : ℤ) : Order D) * z₀ = ((-(e * N₀) : ℤ) : Order D) := by
      rw [hz₀eq]; ext <;> simp [hN₀] <;> ring
    rw [this, memI'] at hw
    have : e * a' ∣ e * N₀ := by rw [← dvd_neg]; exact hw
    exact (mul_dvd_mul_iff_left he.ne').mp this
  obtain ⟨c, hc⟩ := hdiv
  set f : ℤ × ℤ × ℤ := (a', D % 4 - 2 * k, c) with hfdef
  have hfD : formDisc f = D := by
    simp only [formDisc, hfdef]
    linear_combination 4 * hc + hσ + hq
  have hshift : formShift D f = k := by simp only [formShift, hfdef]; omega
  have htheta : formTheta D f = ⟨-k, 1⟩ := by rw [← hshift]; rfl
  have hf1 : f.1 = a' := rfl
  refine ⟨f, hfD, ha', e, he, ?_⟩
  ext w
  rw [Ideal.mem_span_singleton_mul]
  constructor
  · intro hw
    obtain ⟨t, ht⟩ := (memE' w.im).mp ⟨w, hw, rfl⟩
    have hw' : w - (t : Order D) * z₀ ∈ J := sub_mem hw (J.mul_mem_left _ hz₀J)
    have : w - (t : Order D) * z₀ = ((w.re + t * e * k : ℤ) : Order D) := by
      rw [hz₀eq]; ext <;> simp [ht] <;> ring
    rw [this, memI'] at hw'
    obtain ⟨m, hm⟩ := hw'
    refine ⟨(f.1 : Order D) * m + formTheta D f * t, mul_add_formTheta_mem m t, ?_⟩
    rw [htheta, hf1]
    ext <;> simp [ht, hk] <;> linear_combination -hm
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨X, Y, rfl⟩ := exists_of_mem_formIdeal hfD hv
    have : (e : Order D) * ((f.1 : Order D) * X + formTheta D f * Y) =
        ((e * a' : ℤ) : Order D) * X + z₀ * Y := by
      rw [hz₀eq, htheta, hf1]; ext <;> simp <;> ring
    rw [this]
    exact add_mem (J.mul_mem_right _ haJ) (J.mul_mem_right _ hz₀J)

end surjective

/-! ### Classes -/

theorem formIdeal_ne_bot {f : ℤ × ℤ × ℤ} (ha : f.1 ≠ 0) : formIdeal D f ≠ ⊥ := fun h ↦ by
  have h' := intCast_mem_formIdeal (D := D) (f := f)
  rw [h, Ideal.mem_bot] at h'
  have := congrArg QuadraticAlgebra.re h'
  simp at this
  exact ha this

variable (D)

/-- Narrow equivalence on nonzero ideals. -/
instance narrowSetoid : Setoid {I : Ideal (Order D) // I ≠ ⊥} where
  r I J := NarrowRel I.1 J.1
  iseqv := ⟨fun _ ↦ NarrowRel.refl _, NarrowRel.symm, NarrowRel.trans⟩

/-- **Davenport §6, p. 62 (row 6-21).** The ideal classes of `O` in the narrow sense. -/
def NarrowClass := Quotient (narrowSetoid D)

/-- Forms of discriminant `D` with `a > 0`. -/
def PosForm := {f : ℤ × ℤ × ℤ // formDisc f = D ∧ 0 < f.1}

instance posFormSetoid : Setoid (PosForm D) where
  r f g := FormEquiv f.1 g.1
  iseqv := ⟨fun _ ↦ FormEquiv.refl _, FormEquiv.symm, FormEquiv.trans⟩

/-- Proper classes of forms of discriminant `D` with `a > 0`. -/
def PosFormClass := Quotient (posFormSetoid D)

/-- **Davenport §6, pp. 61–62 (rows 6-20, 6-22).** The class of a form `f` (with `a > 0`) goes
to the narrow class of `A_f`. -/
def posFormClassToNarrow : PosFormClass D → NarrowClass D :=
  Quotient.map (fun f ↦ ⟨formIdeal D f.1, formIdeal_ne_bot f.2.2.ne'⟩)
    (fun f g h ↦ narrowRel_of_formEquiv f.2.1 f.2.2 g.2.2 h)

variable [Fact (IsFundamentalDiscriminant D)] [Fact (D ≠ 1)]

/-- **Davenport §6, p. 62 (row 6-22).** For a fundamental discriminant `D ≠ 1`, `f ↦ [A_f]` is a
one-to-one correspondence between proper classes of forms of discriminant `D` (with `a > 0`) and
narrow ideal classes of `ℚ(√D)`. -/
theorem posFormClassToNarrow_bijective : Function.Bijective (posFormClassToNarrow D) := by
  constructor
  · intro F G hFG
    induction F using Quotient.inductionOn
    induction G using Quotient.inductionOn
    rename_i f g
    exact Quotient.sound (formEquiv_of_narrowRel f.2.1 g.2.1 f.2.2 g.2.2 (Quotient.exact hFG))
  · intro C
    induction C using Quotient.inductionOn
    rename_i J
    obtain ⟨f, hf, ha, e, he, hJ⟩ := exists_eq_span_mul_formIdeal J.2
    refine ⟨⟦⟨f, hf, ha⟩⟧, Quotient.sound ?_⟩
    refine ⟨(e : Order D), 1, ?_, ?_⟩
    · rw [norm_intCast, map_one, mul_one]; positivity
    · rw [Ideal.span_singleton_one, Ideal.top_mul]; exact hJ.symm

end NTKB.Davenport
