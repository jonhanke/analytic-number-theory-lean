/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Davenport.Forms.ClassNumber

/-!
# Davenport, Chapter 6: automorphs of binary forms

(§6, pp. 54–56, rows 6-3, 6-4, 6-5.) Let `D ≠ 1` be a fundamental discriminant and `f = (a, b, c)`
a form of discriminant `D`.

* Every form of discriminant `D` is primitive (`NTKB.Davenport.exists_bezout_of_formDisc`), and
  `A_f · A_{f'} = (a)` for `f' = (a, -b, c)` (`NTKB.Davenport.formIdeal_mul_formIdeal_formNeg`).
* An automorph of `f` (a substitution of determinant `1` fixing `f`) is multiplication by a unit
  `η` of norm `1` on `a x + θ_f y` (`NTKB.Davenport.exists_norm_eq_one_of_automorph`), and every
  such `η` gives an automorph (`NTKB.Davenport.exists_automorph_of_norm_eq_one`).
* **Row 6-5, both directions** (`NTKB.Davenport.automorph_iff`): the automorphs of `f` are exactly
  `α = (t - bu)/2`, `β = -cu`, `γ = au`, `δ = (t + bu)/2` with `t² - D u² = 4`.
-/

noncomputable section

open QuadraticAlgebra NTKB.QuadraticField

namespace NTKB.Davenport

variable {D : ℤ} {f : ℤ × ℤ × ℤ}

/-- The form `(a, -b, c)`. -/
def formNeg (f : ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ := (f.1, -f.2.1, f.2.2)

theorem formDisc_formNeg (f : ℤ × ℤ × ℤ) : formDisc (formNeg f) = formDisc f := by
  simp [formDisc, formNeg]

theorem formTheta_formNeg (hf : formDisc f = D) :
    formTheta D (formNeg f) = formTheta D f - (f.2.1 : Order D) := by
  have h1 := two_mul_formShift hf
  have h2 := two_mul_formShift (f := formNeg f) (by rw [formDisc_formNeg, hf])
  have hb : (formNeg f).2.1 = -f.2.1 := rfl
  rw [hb] at h2
  ext <;> simp [formTheta] <;> omega

/-! ### Primitivity -/

theorem isCoprime_two_of_odd {x : ℤ} (hx : Odd x) : IsCoprime x 2 := by
  obtain ⟨m, rfl⟩ := hx
  exact ⟨1, -m, by ring⟩

/-- **Every form of fundamental discriminant is primitive**: `ax + by + cz = 1` is solvable. -/
theorem exists_bezout_of_formDisc (hD : IsFundamentalDiscriminant D) (hf : formDisc f = D) :
    ∃ x y z : ℤ, f.1 * x + f.2.1 * y + f.2.2 * z = 1 := by
  set g : ℕ := Int.gcd f.1 (Int.gcd f.2.1 f.2.2)
  have hga : (g : ℤ) ∣ f.1 := Int.gcd_dvd_left _ _
  have hgbc : (g : ℤ) ∣ (Int.gcd f.2.1 f.2.2 : ℤ) := Int.gcd_dvd_right _ _
  have hgb : (g : ℤ) ∣ f.2.1 := hgbc.trans (Int.gcd_dvd_left _ _)
  have hgc : (g : ℤ) ∣ f.2.2 := hgbc.trans (Int.gcd_dvd_right _ _)
  have hg2 : (g : ℤ) * g ∣ D := by
    rw [← hf]; simp only [formDisc]
    obtain ⟨a', ha'⟩ := hga; obtain ⟨b', hb'⟩ := hgb; obtain ⟨c', hc'⟩ := hgc
    exact ⟨b' * b' - 4 * a' * c', by rw [ha', hb', hc']; ring⟩
  have hunit : IsUnit (g : ℤ) := by
    rcases hD with ⟨-, hsq⟩ | ⟨h0, h23, hsq⟩
    · exact hsq _ hg2
    · rcases Int.even_or_odd (g : ℤ) with heven | hodd
      · exfalso
        obtain ⟨a', ha'⟩ := (even_iff_two_dvd.mp heven).trans hga
        obtain ⟨b', hb'⟩ := (even_iff_two_dvd.mp heven).trans hgb
        obtain ⟨c', hc'⟩ := (even_iff_two_dvd.mp heven).trans hgc
        have hD' : D = 4 * (b' * b') - 16 * (a' * c') := by
          rw [← hf]; simp only [formDisc]; rw [ha', hb', hc']; ring
        rcases sq_emod_four b' with h | h <;> omega
      · have hcop : IsCoprime ((g : ℤ) * g) 4 := by
          have := (isCoprime_two_of_odd (hodd.mul hodd)).pow_right (n := 2)
          simpa using this
        have h4 : (g : ℤ) * g ∣ D / 4 * 4 := by
          rwa [Int.ediv_mul_cancel (Int.dvd_of_emod_eq_zero h0)]
        exact hsq _ (hcop.dvd_of_dvd_mul_right h4)
  have hg1 : g = 1 := by
    rcases Int.isUnit_iff.mp hunit with h | h
    · exact_mod_cast h
    · have : (0 : ℤ) ≤ g := Nat.cast_nonneg _
      omega
  -- Bézout
  refine ⟨Int.gcdA f.1 (Int.gcd f.2.1 f.2.2),
    Int.gcdB f.1 (Int.gcd f.2.1 f.2.2) * Int.gcdA f.2.1 f.2.2,
    Int.gcdB f.1 (Int.gcd f.2.1 f.2.2) * Int.gcdB f.2.1 f.2.2, ?_⟩
  have e1 := Int.gcd_eq_gcd_ab f.1 (Int.gcd f.2.1 f.2.2)
  have e2 := Int.gcd_eq_gcd_ab f.2.1 f.2.2
  have : ((Int.gcd f.1 (Int.gcd f.2.1 f.2.2) : ℕ) : ℤ) = 1 := by exact_mod_cast hg1
  linear_combination -e1 - Int.gcdB f.1 (Int.gcd f.2.1 f.2.2) * e2 + this

/-- **Davenport §6, p. 61.** `A_f · A_{f'} = (a)` for `f' = (a, -b, c)`. -/
theorem formIdeal_mul_formIdeal_formNeg (hD : IsFundamentalDiscriminant D) (hf : formDisc f = D) :
    formIdeal D f * formIdeal D (formNeg f) = Ideal.span {((f.1 : ℤ) : Order D)} := by
  have hf' : formDisc (formNeg f) = D := by rw [formDisc_formNeg, hf]
  have hθ' := formTheta_formNeg hf
  have hθθ : formTheta D f * ((f.2.1 : Order D) - formTheta D f) = (f.1 : Order D) * f.2.2 := by
    rw [← star_formTheta hf, formTheta_mul_star hf]; push_cast; ring
  have ha' : (formNeg f).1 = f.1 := rfl
  apply le_antisymm
  · rw [Ideal.mul_le]
    intro x hx y hy
    obtain ⟨X, Y, rfl⟩ := exists_of_mem_formIdeal hf hx
    obtain ⟨X', Y', rfl⟩ := exists_of_mem_formIdeal hf' hy
    rw [hθ', ha', Ideal.mem_span_singleton]
    refine ⟨(f.1 : Order D) * X * X' + X * (formTheta D f - f.2.1) * Y' +
      formTheta D f * Y * X' - (f.2.2 : Order D) * Y * Y', ?_⟩
    linear_combination (-(Y : Order D) * Y') * hθθ
  · rw [Ideal.span_singleton_le_iff_mem]
    obtain ⟨x, y, z, hxyz⟩ := exists_bezout_of_formDisc hD hf
    have m1 : (f.1 : Order D) * (f.1 : Order D) ∈ formIdeal D f * formIdeal D (formNeg f) :=
      Ideal.mul_mem_mul intCast_mem_formIdeal (by rw [← ha']; exact intCast_mem_formIdeal)
    have m2 : (f.1 : Order D) * (formTheta D f - f.2.1) ∈ formIdeal D f * formIdeal D (formNeg f) :=
      Ideal.mul_mem_mul intCast_mem_formIdeal (by rw [← hθ']; exact formTheta_mem_formIdeal)
    have m3 : formTheta D f * (f.1 : Order D) ∈ formIdeal D f * formIdeal D (formNeg f) :=
      Ideal.mul_mem_mul formTheta_mem_formIdeal (by rw [← ha']; exact intCast_mem_formIdeal)
    have m4 : formTheta D f * (formTheta D f - f.2.1) ∈ formIdeal D f * formIdeal D (formNeg f) :=
      Ideal.mul_mem_mul formTheta_mem_formIdeal (by rw [← hθ']; exact formTheta_mem_formIdeal)
    have hb : ((f.1 * x + f.2.1 * y + f.2.2 * z : ℤ) : Order D) = 1 := by rw [hxyz]; simp
    push_cast at hb
    have : ((f.1 : ℤ) : Order D) =
        x * ((f.1 : Order D) * f.1) + y * (formTheta D f * f.1 - f.1 * (formTheta D f - f.2.1)) -
          z * (formTheta D f * (formTheta D f - f.2.1)) := by
      linear_combination (-(f.1 : Order D)) * hb - z * hθθ
    rw [this]
    exact sub_mem (add_mem (Ideal.mul_mem_left _ _ m1)
      (Ideal.mul_mem_left _ _ (sub_mem m3 m2))) (Ideal.mul_mem_left _ _ m4)

/-! ### Automorphs and units of norm `1` -/

/-- The element `a x + θ_f y` of `A_f`. -/
def formLam (D : ℤ) (f : ℤ × ℤ × ℤ) (x y : ℤ) : Order D := (f.1 : Order D) * x + formTheta D f * y

theorem intCast_injective_order : Function.Injective (Int.cast : ℤ → Order D) := fun m n h ↦ by
  have := congrArg QuadraticAlgebra.re h; simpa using this

section automorph

variable [Fact (IsFundamentalDiscriminant D)] [Fact (D ≠ 1)] {α β γ δ : ℤ}

/-- **Davenport §6, p. 55.** An automorph of `f` multiplies `a x + θ_f y` by a unit of norm `1`. -/
theorem exists_norm_eq_one_of_automorph (hf : formDisc f = D) (ha : f.1 ≠ 0)
    (h1 : α * δ - β * γ = 1) (hM : formSubst f α β γ δ = f) :
    ∃ η : Order D, η.norm = 1 ∧ (f.1 : Order D) * α + formTheta D f * γ = f.1 * η ∧
      (f.1 : Order D) * β + formTheta D f * δ = η * formTheta D f := by
  set u : Order D := (f.1 : Order D) * α + formTheta D f * γ
  set v : Order D := (f.1 : Order D) * β + formTheta D f * δ
  have hW := span_star_mul_formIdeal (α := α) (β := β) (γ := γ) (δ := δ) hf h1
  obtain ⟨huu, huv⟩ := star_mul_formTheta_eq (α := α) (β := β) (γ := γ) (δ := δ) hf h1
  rw [hM] at hW huu huv
  have hP := formIdeal_mul_formIdeal_formNeg Fact.out hf
  have hW' : Ideal.span {star u} * Ideal.span {((f.1 : ℤ) : Order D)} =
      Ideal.span {((f.1 : ℤ) : Order D)} * Ideal.span {((f.1 : ℤ) : Order D)} := by
    calc Ideal.span {star u} * Ideal.span {((f.1 : ℤ) : Order D)}
        = Ideal.span {star u} * (formIdeal D f * formIdeal D (formNeg f)) := by rw [hP]
      _ = (Ideal.span {star u} * formIdeal D f) * formIdeal D (formNeg f) := (mul_assoc _ _ _).symm
      _ = (Ideal.span {((f.1 : ℤ) : Order D)} * formIdeal D f) * formIdeal D (formNeg f) := by
          rw [hW]
      _ = _ := by rw [mul_assoc, hP]
  have ha0 : Ideal.span {((f.1 : ℤ) : Order D)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    intro h; exact ha (intCast_injective_order (D := D) (by simpa using h))
  have hsu : Ideal.span {star u} = Ideal.span {((f.1 : ℤ) : Order D)} := mul_right_cancel₀ ha0 hW'
  obtain ⟨w, hw⟩ := Ideal.span_singleton_eq_span_singleton.mp hsu.symm
  -- `ū = a w`, so `u = a w̄`
  have hfa : ((f.1 : ℤ) : Order D) ≠ 0 := fun h ↦ ha (intCast_injective_order (D := D) (by simpa using h))
  have hu : u = (f.1 : Order D) * star (w : Order D) := by
    have := congrArg star hw
    rw [star_star, star_mul, star_intCast] at this
    rw [← this, mul_comm]
  have hww : (w : Order D) * star (w : Order D) = 1 := by
    have : (f.1 : Order D) * f.1 * ((w : Order D) * star (w : Order D)) = (f.1 : Order D) * f.1 := by
      change star u * u = _ at huu
      calc (f.1 : Order D) * f.1 * ((w : Order D) * star (w : Order D))
          = ((f.1 : Order D) * w) * ((f.1 : Order D) * star (w : Order D)) := by ring
        _ = star u * u := by rw [hw, ← hu]
        _ = _ := huu
    have h2 : (f.1 : Order D) * f.1 ≠ 0 := mul_ne_zero hfa hfa
    exact mul_left_cancel₀ h2 (this.trans (mul_one _).symm)
  refine ⟨star (w : Order D), ?_, hu, ?_⟩
  · have : ((star (w : Order D)).norm : Order D) = 1 := by
      rw [intCast_norm, star_star, mul_comm, hww]
    exact intCast_injective_order (D := D) (by simpa using this)
  · -- `ū v = a θ` gives `a w v = a θ`
    have : (f.1 : Order D) * ((w : Order D) * v) = (f.1 : Order D) * formTheta D f := by
      change star u * v = _ at huv
      rw [← huv, ← hw]; ring
    have hv := mul_left_cancel₀ hfa this
    calc v = star (w : Order D) * ((w : Order D) * v) := by
            rw [← mul_assoc, mul_comm (star _), hww, one_mul]
      _ = star (w : Order D) * formTheta D f := by rw [hv]

end automorph

section converse

variable {α β γ δ : ℤ}

/-- The conjugate determinant of `a, θ_f`: `a θ̄ - ā θ = -a √D`. -/
theorem conjDet_formTheta :
    (f.1 : Order D) * star (formTheta D f) - star (f.1 : Order D) * formTheta D f =
      -((f.1 : Order D) * sqrtD D) := by
  rw [star_intCast, ← formTheta_sub_star]; ring

/-- **Davenport §6, p. 55.** A unit of norm `1` gives an automorph. -/
theorem exists_automorph_of_norm_eq_one (hf : formDisc f = D) (ha : f.1 ≠ 0) {η : Order D}
    (hη : η.norm = 1) :
    ∃ α β γ δ : ℤ, α * δ - β * γ = 1 ∧ formSubst f α β γ δ = f ∧
      (f.1 : Order D) * α + formTheta D f * γ = f.1 * η ∧
      (f.1 : Order D) * β + formTheta D f * δ = η * formTheta D f := by
  obtain ⟨α, γ, e₁⟩ := exists_of_mem_formIdeal hf
    (Ideal.mul_mem_right η _ (intCast_mem_formIdeal (D := D) (f := f)))
  obtain ⟨β, δ, e₂⟩ := exists_of_mem_formIdeal hf
    (Ideal.mul_mem_left _ η (formTheta_mem_formIdeal (D := D) (f := f)))
  have hηη : η * star η = 1 := by rw [← intCast_norm, hη, Int.cast_one]
  have h1 : α * δ - β * γ = 1 := by
    set θ := formTheta D f
    have hθ := formTheta_sub_star (D := D) f
    have key : ((f.1 : Order D) * η) * star (η * θ) - star ((f.1 : Order D) * η) * (η * θ) =
        ((f.1 : Order D) * α + θ * γ) * star ((f.1 : Order D) * β + θ * δ) -
          star ((f.1 : Order D) * α + θ * γ) * ((f.1 : Order D) * β + θ * δ) := by
      rw [← e₁, ← e₂]
    have lhs : ((f.1 : Order D) * η) * star (η * θ) - star ((f.1 : Order D) * η) * (η * θ) =
        -((f.1 : Order D) * sqrtD D) := by
      simp only [star_mul, star_intCast]
      rw [← hθ]; linear_combination ((f.1 : Order D) * star θ - f.1 * θ) * hηη
    have rhs : ((f.1 : Order D) * α + θ * γ) * star ((f.1 : Order D) * β + θ * δ) -
        star ((f.1 : Order D) * α + θ * γ) * ((f.1 : Order D) * β + θ * δ) =
          -(((α * δ - β * γ) * f.1 : ℤ) : Order D) * sqrtD D := by
      simp only [star_add, star_mul, star_intCast]
      rw [← hθ]; push_cast; ring
    rw [lhs, rhs] at key
    have : (((α * δ - β * γ - 1) * f.1 : ℤ) : Order D) * sqrtD D = 0 := by
      push_cast at key ⊢; linear_combination key
    have h0 := intCast_mul_sqrtD_eq_zero this
    rcases mul_eq_zero.mp h0 with h | h
    · linarith
    · exact absurd h ha
  refine ⟨α, β, γ, δ, h1, eq_of_formEval_eq fun X Y ↦ ?_, e₁.symm, e₂.symm⟩
  rw [formEval_formSubst]
  have e : (f.1 : Order D) * ((α * X + β * Y : ℤ) : Order D) +
      formTheta D f * ((γ * X + δ * Y : ℤ) : Order D) =
        η * ((f.1 : Order D) * X + formTheta D f * Y) := by
    push_cast
    linear_combination -(X : Order D) * e₁ - (Y : Order D) * e₂
  have hn := congrArg QuadraticAlgebra.norm e
  rw [map_mul, hη, one_mul, norm_mul_add_formTheta hf, norm_mul_add_formTheta hf] at hn
  exact mul_left_cancel₀ ha hn

/-- **Davenport §6, p. 55, (E), the converse (row 6-5).** If `η = re + im ω` has norm `1`
and multiplies `a x + θ_f y` as the substitution `(α β; γ δ)` does, then with `t = 2 re + σ im`,
`u = im`: `t² - D u² = 4`, `α = (t - bu)/2`, `β = -cu`, `γ = au`, `δ = (t + bu)/2`. -/
theorem automorph_eq_of_unit (hf : formDisc f = D) (ha : f.1 ≠ 0) {η : Order D}
    (hη : η.norm = 1) (e₁ : (f.1 : Order D) * α + formTheta D f * γ = f.1 * η)
    (e₂ : (f.1 : Order D) * β + formTheta D f * δ = η * formTheta D f) :
    (2 * η.re + D % 4 * η.im) ^ 2 - D * η.im ^ 2 = 4 ∧
      2 * α = (2 * η.re + D % 4 * η.im) - f.2.1 * η.im ∧ β = -(f.2.2 * η.im) ∧
      γ = f.1 * η.im ∧ 2 * δ = (2 * η.re + D % 4 * η.im) + f.2.1 * η.im := by
  have hk := two_mul_formShift hf
  have hsq := formShift_sq hf
  have hσ := emod_four_mul_self hf
  have hq : D % 4 + 4 * (D / 4) = D := by omega
  have r1 := congrArg QuadraticAlgebra.re e₁
  have i1 := congrArg QuadraticAlgebra.im e₁
  have r2 := congrArg QuadraticAlgebra.re e₂
  have i2 := congrArg QuadraticAlgebra.im e₂
  simp [formTheta] at r1 i1 r2 i2
  rw [norm_def] at hη
  have hγ : γ = f.1 * η.im := by linarith
  subst hγ
  have hα : α = η.re + formShift D f * η.im := by
    have : f.1 * (α - η.re - formShift D f * η.im) = 0 := by linear_combination r1
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h ha
    · linarith
  have hδ : δ = η.re - formShift D f * η.im + D % 4 * η.im := by linear_combination i2
  have hβ : β = -(f.2.2 * η.im) := by
    have : f.1 * (β + f.2.2 * η.im) = 0 := by
      linear_combination r2 + formShift D f * i2 - η.im * hsq
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h ha
    · linarith
  refine ⟨?_, ?_, hβ, rfl, ?_⟩
  · linear_combination 4 * hη + η.im ^ 2 * hσ + η.im ^ 2 * hq
  · rw [hα]; linear_combination η.im * hk
  · rw [hδ]; linear_combination -η.im * hk

end converse

/-! ### Row 6-5: the automorphs are the explicit substitutions -/

section iff

variable [Fact (IsFundamentalDiscriminant D)] [Fact (D ≠ 1)] {α β γ δ : ℤ}

/-- **Davenport §6, pp. 55–56 (row 6-5).** For a form `f = (a, b, c)` of fundamental
discriminant `D ≠ 1`, the substitution `(α β; γ δ)` is an automorph of `f` (determinant `1`,
`f ∘ (α β; γ δ) = f`) if and only if `α = (t - bu)/2`, `β = -cu`, `γ = au`, `δ = (t + bu)/2` for a
solution of `t² - D u² = 4`. -/
theorem automorph_iff (hf : formDisc f = D) :
    (α * δ - β * γ = 1 ∧ formSubst f α β γ δ = f) ↔
      ∃ t u : ℤ, t ^ 2 - D * u ^ 2 = 4 ∧ 2 * α = t - f.2.1 * u ∧ β = -(f.2.2 * u) ∧
        γ = f.1 * u ∧ 2 * δ = t + f.2.1 * u := by
  have ha : f.1 ≠ 0 := fst_ne_zero_of_not_isSquare (by rw [hf]; exact not_isSquare Fact.out Fact.out)
  constructor
  · rintro ⟨h1, hM⟩
    obtain ⟨η, hη, e₁, e₂⟩ := exists_norm_eq_one_of_automorph hf ha h1 hM
    obtain ⟨ht, h2, h3, h4, h5⟩ := automorph_eq_of_unit hf ha hη e₁ e₂
    exact ⟨_, _, ht, h2, h3, h4, h5⟩
  · rintro ⟨t, u, htu, hα, rfl, rfl, hδ⟩
    exact formSubst_automorph f (by rw [hf]; exact htu) hα hδ

end iff

end NTKB.Davenport
