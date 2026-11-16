/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Davenport.Ch1to6.FormReduction
import NTKB.Elementary.QuadraticField.Model
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Ideal.Norm.AbsNorm

/-!
# Davenport, Chapter 6: the ideal of a binary quadratic form

(§6, pp. 61–62, rows 6-20 to 6-22.) Let `D ≡ 0, 1 (mod 4)`, `σ = D % 4` and
`O = ℤ[ω] = QuadraticAlgebra ℤ (D / 4) σ` (`NTKB.QuadraticField.Order D`), so `ω² = D / 4 + σ ω`,
`√D = 2ω - σ` and `N(x + yω) = x² + σxy - (D/4)y²`.

For a form `f = (a, b, c)` of discriminant `D` put `k = (σ - b)/2` and `θ_f = ω - k = (b + √D)/2`.
Then `T(θ_f) = b`, `N(θ_f) = ac`, and

  `N(a x + θ_f y) = a · f(x, y)`,

which is Davenport's `f(x, y) = N(αx + βy)/N(𝔞)` for the ideal `𝔞 = A_f = (a, θ_f)` with basis
`α = a`, `β = θ_f`. The ideal `A_f` is the kernel of `O → ℤ/a`, `ω ↦ k`, so `N(A_f) = |a|`.

* `NTKB.Davenport.formEval`: the value `f(x, y)`;
* `NTKB.Davenport.norm_formTheta`, `NTKB.Davenport.norm_mul_add_formTheta`;
* `NTKB.Davenport.formIdeal`, `NTKB.Davenport.mem_formIdeal_iff`,
  `NTKB.Davenport.absNorm_formIdeal`.
-/

noncomputable section

open QuadraticAlgebra NTKB.QuadraticField

namespace NTKB.Davenport

/-- The value `f(x, y) = a x² + b x y + c y²` of the form `f = (a, b, c)`. -/
def formEval (f : ℤ × ℤ × ℤ) (x y : ℤ) : ℤ := f.1 * x ^ 2 + f.2.1 * x * y + f.2.2 * y ^ 2

theorem formEval_formSubst (f : ℤ × ℤ × ℤ) (α β γ δ x y : ℤ) :
    formEval (formSubst f α β γ δ) x y = formEval f (α * x + β * y) (γ * x + δ * y) := by
  simp only [formEval, formSubst]; ring

theorem formSubst_one (f : ℤ × ℤ × ℤ) : formSubst f 1 0 0 1 = f := by
  obtain ⟨a, b, c⟩ := f; simp only [formSubst, Prod.mk.injEq]; refine ⟨by ring, by ring, by ring⟩

theorem FormEquiv.symm {f g : ℤ × ℤ × ℤ} (h : FormEquiv f g) : FormEquiv g f := by
  obtain ⟨α, β, γ, δ, h1, rfl⟩ := h
  refine ⟨δ, -β, -γ, α, by linear_combination h1, ?_⟩
  rw [formSubst_formSubst]
  have e1 : α * δ + β * -γ = 1 := by linear_combination h1
  have e2 : α * -β + β * α = 0 := by ring
  have e3 : γ * δ + δ * -γ = 0 := by ring
  have e4 : γ * -β + δ * α = 1 := by linear_combination h1
  rw [e1, e2, e3, e4, formSubst_one]

/-- A form is determined by its values. -/
theorem eq_of_formEval_eq {f g : ℤ × ℤ × ℤ} (h : ∀ x y, formEval f x y = formEval g x y) : f = g := by
  obtain ⟨a, b, c⟩ := f
  obtain ⟨a', b', c'⟩ := g
  have h1 := h 1 0
  have h2 := h 0 1
  have h3 := h 1 1
  simp only [formEval] at h1 h2 h3
  simp only [Prod.mk.injEq]
  refine ⟨by linarith, by linarith, by linarith⟩

section algebra

variable {D : ℤ} {f : ℤ × ℤ × ℤ}

theorem emod_four_of_formDisc (hf : formDisc f = D) : D % 4 = 0 ∨ D % 4 = 1 := by
  subst hf
  simp only [formDisc]
  rw [show f.2.1 ^ 2 - 4 * f.1 * f.2.2 = f.2.1 * f.2.1 + 4 * (-(f.1 * f.2.2)) by ring,
    Int.add_mul_emod_self_left]
  exact sq_emod_four _

theorem emod_four_mul_self (hf : formDisc f = D) : D % 4 * (D % 4) = D % 4 := by
  rcases emod_four_of_formDisc hf with h | h <;> rw [h] <;> norm_num

theorem two_dvd_emod_sub (hf : formDisc f = D) : 2 ∣ D % 4 - f.2.1 := by
  subst hf
  simp only [formDisc]
  rcases Int.even_or_odd' f.2.1 with ⟨k, h | h⟩ <;> rw [h] <;>
    [rw [show (2 * k) ^ 2 - 4 * f.1 * f.2.2 = 4 * (k ^ 2 - f.1 * f.2.2) by ring];
     rw [show (2 * k + 1) ^ 2 - 4 * f.1 * f.2.2 = 4 * (k ^ 2 + k - f.1 * f.2.2) + 1 by ring]] <;>
    omega

/-- `k_f = (σ - b)/2`. -/
def formShift (D : ℤ) (f : ℤ × ℤ × ℤ) : ℤ := (D % 4 - f.2.1) / 2

theorem two_mul_formShift (hf : formDisc f = D) : 2 * formShift D f = D % 4 - f.2.1 :=
  Int.mul_ediv_cancel' (two_dvd_emod_sub hf)

/-- `θ_f = ω - k_f = (b + √D)/2`. -/
def formTheta (D : ℤ) (f : ℤ × ℤ × ℤ) : Order D := ⟨-formShift D f, 1⟩

@[simp] theorem re_formTheta : (formTheta D f).re = -formShift D f := rfl
@[simp] theorem im_formTheta : (formTheta D f).im = 1 := rfl

/-- `k² - σk - D/4 = ac`. -/
theorem formShift_sq (hf : formDisc f = D) :
    formShift D f * formShift D f - D % 4 * formShift D f - D / 4 = f.1 * f.2.2 := by
  have hk := two_mul_formShift hf
  have hq : D % 4 + 4 * (D / 4) = D := by omega
  have hσ := emod_four_mul_self hf
  simp only [formDisc] at hf
  have : 4 * (formShift D f * formShift D f - D % 4 * formShift D f - D / 4) =
      4 * (f.1 * f.2.2) := by
    linear_combination (2 * formShift D f - D % 4 - f.2.1) * hk + hf - hq - hσ
  linarith

theorem norm_formTheta (hf : formDisc f = D) : (formTheta D f).norm = f.1 * f.2.2 := by
  rw [norm_def, re_formTheta, im_formTheta, ← formShift_sq hf]; ring

theorem trace_formTheta (hf : formDisc f = D) : (formTheta D f).trace = f.2.1 := by
  rw [trace_def, re_formTheta, im_formTheta]
  linarith [two_mul_formShift hf]

/-- **Davenport §6, p. 61**: `N(a x + θ_f y) = a f(x, y)`. -/
theorem norm_mul_add_formTheta (hf : formDisc f = D) (x y : ℤ) :
    ((f.1 : Order D) * x + formTheta D f * y).norm = f.1 * formEval f x y := by
  have h := formShift_sq hf
  have hk := two_mul_formShift hf
  rw [norm_def]
  simp only [re_add, im_add, re_mul, im_mul, re_intCast, im_intCast, re_formTheta, im_formTheta]
  simp only [formEval]
  linear_combination y ^ 2 * h - f.1 * x * y * hk

/-- The ideal `A_f = (a, θ_f)` of the form `f = (a, b, c)`. -/
def formIdeal (D : ℤ) (f : ℤ × ℤ × ℤ) : Ideal (Order D) :=
  Ideal.span {((f.1 : ℤ) : Order D), formTheta D f}

theorem intCast_mem_formIdeal : ((f.1 : ℤ) : Order D) ∈ formIdeal D f :=
  Ideal.subset_span (Set.mem_insert _ _)

theorem formTheta_mem_formIdeal : formTheta D f ∈ formIdeal D f :=
  Ideal.subset_span (Set.mem_insert_of_mem _ rfl)

/-- The ideal `{z : a ∣ re z + k im z}`. -/
def formIdealKer (D : ℤ) (f : ℤ × ℤ × ℤ) (hf : formDisc f = D) : Ideal (Order D) where
  carrier := {z | f.1 ∣ z.re + formShift D f * z.im}
  add_mem' {z w} hz hw := by
    simp only [Set.mem_ofPred_eq, re_add, im_add] at hz hw ⊢
    convert dvd_add hz hw using 1; ring
  zero_mem' := by simp
  smul_mem' c z hz := by
    simp only [Set.mem_ofPred_eq, smul_eq_mul, re_mul, im_mul] at hz ⊢
    obtain ⟨m, hm⟩ := hz
    have h := formShift_sq hf
    refine ⟨c.re * m + c.im * (formShift D f * m - f.2.2 * z.im), ?_⟩
    linear_combination c.re * hm + c.im * formShift D f * hm - c.im * z.im * h

theorem mem_formIdeal_iff (hf : formDisc f = D) {z : Order D} :
    z ∈ formIdeal D f ↔ f.1 ∣ z.re + formShift D f * z.im := by
  constructor
  · intro hz
    have hle : formIdeal D f ≤ formIdealKer D f hf := by
      rw [formIdeal, Ideal.span_le]
      intro w hw
      rcases hw with rfl | rfl
      · show f.1 ∣ _
        simp
      · show f.1 ∣ _
        simp
    exact hle hz
  · rintro ⟨m, hm⟩
    have hz : z = ((m : ℤ) : Order D) * ((f.1 : ℤ) : Order D) + ((z.im : ℤ) : Order D) * formTheta D f := by
      ext <;> simp <;> linear_combination hm
    rw [hz]
    exact add_mem (Ideal.mul_mem_left _ _ intCast_mem_formIdeal)
      (Ideal.mul_mem_left _ _ formTheta_mem_formIdeal)

/-- Every element of `A_f` is `a x + θ_f y`. -/
theorem exists_of_mem_formIdeal (hf : formDisc f = D) {z : Order D} (hz : z ∈ formIdeal D f) :
    ∃ x y : ℤ, z = (f.1 : Order D) * x + formTheta D f * y := by
  obtain ⟨m, hm⟩ := (mem_formIdeal_iff hf).mp hz
  exact ⟨m, z.im, by ext <;> simp <;> linear_combination hm⟩

theorem mul_add_formTheta_mem (x y : ℤ) :
    (f.1 : Order D) * x + formTheta D f * y ∈ formIdeal D f :=
  add_mem (Ideal.mul_mem_right _ _ intCast_mem_formIdeal)
    (Ideal.mul_mem_right _ _ formTheta_mem_formIdeal)

/-- The coordinates of `a x + θ_f y` determine `x` and `y` (for `a ≠ 0`). -/
theorem mul_add_formTheta_injective (ha : f.1 ≠ 0) {x y x' y' : ℤ}
    (h : (f.1 : Order D) * x + formTheta D f * y = (f.1 : Order D) * x' + formTheta D f * y') :
    x = x' ∧ y = y' := by
  have h1 := congrArg QuadraticAlgebra.re h
  have h2 := congrArg QuadraticAlgebra.im h
  simp at h1 h2
  subst h2
  refine ⟨?_, rfl⟩
  have : f.1 * (x - x') = 0 := by linear_combination h1
  rcases mul_eq_zero.mp this with h | h
  · exact absurd h ha
  · linarith

/-- The ring homomorphism `O → ℤ/|a|`, `ω ↦ k_f`. -/
def formToZMod (hf : formDisc f = D) : Order D →+* ZMod f.1.natAbs :=
  ((lift ⟨(formShift D f : ZMod f.1.natAbs), by
      have h0 : ((f.1 * f.2.2 : ℤ) : ZMod f.1.natAbs) = 0 :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr
          (by rw [Int.natCast_natAbs]; exact (abs_dvd _ _).mpr (dvd_mul_right _ _))
      rw [← formShift_sq hf] at h0
      push_cast at h0
      rw [zsmul_eq_mul, zsmul_eq_mul, mul_one]
      linear_combination h0⟩ : Order D →ₐ[ℤ] ZMod f.1.natAbs) : Order D →+* ZMod f.1.natAbs)

theorem formToZMod_apply (hf : formDisc f = D) (z : Order D) :
    formToZMod hf z = ((z.re + formShift D f * z.im : ℤ) : ZMod f.1.natAbs) := by
  simp [formToZMod, zsmul_eq_mul]
  ring

theorem ker_formToZMod (hf : formDisc f = D) : RingHom.ker (formToZMod hf) = formIdeal D f := by
  ext z
  rw [RingHom.mem_ker, formToZMod_apply, ZMod.intCast_zmod_eq_zero_iff_dvd, Int.natCast_natAbs,
    abs_dvd, mem_formIdeal_iff hf]

theorem formToZMod_surjective (hf : formDisc f = D) : Function.Surjective (formToZMod hf) := by
  intro r
  obtain ⟨m, rfl⟩ := ZMod.intCast_surjective r
  refine ⟨((m : ℤ) : Order D), ?_⟩
  rw [formToZMod_apply]
  simp

end algebra

section dedekind

variable (D : ℤ) [Fact (IsFundamentalDiscriminant D)] [Fact (D ≠ 1)]

instance isDedekindDomain_order : IsDedekindDomain (Order D) :=
  IsIntegralClosure.isDedekindDomain ℤ ℚ (Model D) (Order D)

variable {D}

/-- **Davenport §6, p. 61**: the ideal `A_f` of a form `(a, b, c)` of discriminant `D` has norm
`|a|`. -/
theorem absNorm_formIdeal {f : ℤ × ℤ × ℤ} (hf : formDisc f = D) :
    Ideal.absNorm (formIdeal D f) = f.1.natAbs := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, ← ker_formToZMod hf,
    Nat.card_congr (RingHom.quotientKerEquivOfSurjective (formToZMod_surjective hf)).toEquiv]
  rcases eq_or_ne f.1 0 with h | h
  · rw [h]; simp
  · have : NeZero f.1.natAbs := ⟨Int.natAbs_ne_zero.mpr h⟩
    exact Nat.card_zmod _

end dedekind

end NTKB.Davenport
