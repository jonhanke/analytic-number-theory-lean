/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Davenport.Siegel.Estermann
import NTKB.Analytic.Davenport.Hadamard.XiCharConj
import NTKB.Analytic.Davenport.Zeros.LZeroFreeReal
import NTKB.Analytic.Davenport.Ch1to6.RealPrimitive
import NTKB.Elementary.SpecialValues.KroneckerPrimitive
import NTKB.Analytic.Apostol.Zeta.Alternating
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality

/-!
# Siegel's theorem (Davenport, Chapter 21)

* `siegel`: **Davenport, Ch. 21, (1)**: for every `ε > 0` there is `C₁(ε) > 0` such that
  `L(1, χ) > C₁(ε) q^{-ε}` for every real primitive character `χ` mod `q` (`χ ≠ χ₀`).
  The constant is not effective: the proof follows Estermann's two cases (p. 130), which depend
  on whether some real character has a real zero close to `1`.
* `siegel_real_zero_le`: **Davenport, Ch. 21, (E)**: every real zero `β` of `L(s, χ)`, `χ` a real
  nonprincipal character mod `q`, satisfies `β ≤ 1 - C₃(ε) q^{-ε}`.
* `siegel_second_form`: **Davenport, Ch. 21, (D)**: `L(σ, χ) ≠ 0` for `σ > 1 - C₃(ε) q^{-ε}`.

Auxiliary facts: `L(σ, χ)` is real for real `σ` and real `χ` (`LFunction_ofReal_im`, via the
reflection `L(s̄, χ̄) = conj L(s, χ)`), positivity of `L(σ, χ)` on an interval `(a, 1]` free of
zeros (`LFunction_re_pos_of_no_zero`), `|L(1, χ)| ≪ log q` (Davenport, Ch. 14, (13),
`exists_norm_LFunction_one_le_log`), and `χ₁ χ₂ ≠ χ₀` for real primitive characters of distinct
moduli (`mul_ne_one_of_lt`).
-/

open Complex Filter Topology Set
open scoped ComplexOrder ComplexConjugate

namespace NTKB.Davenport

section Aux

variable {N : ℕ} [NeZero N]

/-- `L(s̄, χ⁻¹) = conj L(s, χ)` for all `s` (`χ ≠ χ₀`), by the identity theorem from `σ > 1`. -/
lemma LFunction_inv_conj {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) (s : ℂ) :
    χ⁻¹.LFunction (conj s) = conj (χ.LFunction s) := by
  have hχ' : χ⁻¹ ≠ 1 := fun h ↦ hχ (inv_eq_one.mp h)
  have hf : AnalyticOnNhd ℂ (conj ∘ χ⁻¹.LFunction ∘ conj) Set.univ := by
    intro z _
    have h := NTKB.analyticAt_conj_conj
      ((DirichletCharacter.differentiable_LFunction hχ').analyticAt (conj z))
    rw [Complex.conj_conj] at h
    exact h
  have hg : AnalyticOnNhd ℂ χ.LFunction Set.univ := fun z _ ↦
    (DirichletCharacter.differentiable_LFunction hχ).analyticAt z
  have hopen : {w : ℂ | 1 < w.re} ∈ 𝓝 (2 : ℂ) :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  have heq := AnalyticOnNhd.eq_of_eventuallyEq hf hg (z₀ := 2) (by
    filter_upwards [hopen] with w hw
    simp only [Function.comp_apply]
    rw [NTKB.LFunction_inv_conj_of_one_lt_re χ hw, Complex.conj_conj])
  have := congrFun heq s
  simp only [Function.comp_apply] at this
  rw [← this, Complex.conj_conj]

/-- For a real character `χ ≠ χ₀` and real `σ`, `L(σ, χ)` is real. -/
lemma LFunction_ofReal_im {χ : DirichletCharacter ℂ N} (hq : χ.IsQuadratic) (hχ : χ ≠ 1)
    (σ : ℝ) : (χ.LFunction σ).im = 0 := by
  have hinv : χ⁻¹ = χ :=
    inv_eq_of_mul_eq_one_left (by rw [← sq]; exact MulChar.isQuadratic_iff_sq_eq_one.mp hq)
  have h := LFunction_inv_conj hχ (σ : ℂ)
  rw [hinv, Complex.conj_ofReal] at h
  exact Complex.conj_eq_iff_im.mp h.symm

lemma eq_ofReal_re_of_im_eq_zero {z : ℂ} (h : z.im = 0) : z = (z.re : ℂ) :=
  Complex.ext (by simp) (by simp [h])

/-- If `L(s, χ)` (`χ` real, `≠ χ₀`) has no zero in `(a, 1)`, then `L(σ, χ) > 0` on `(a, 1]`. -/
lemma LFunction_re_pos_of_no_zero {χ : DirichletCharacter ℂ N} (hq : χ.IsQuadratic)
    (hχ : χ ≠ 1) {a : ℝ} (h : ∀ σ : ℝ, a < σ → σ < 1 → χ.LFunction σ ≠ 0) {σ : ℝ}
    (hσ : a < σ) (hσ1 : σ ≤ 1) : 0 < (χ.LFunction σ).re := by
  have h1 : 0 < (χ.LFunction (1 : ℝ)).re := by
    have := Davenport.LFunction_one_pos_of_isQuadratic hq hχ
    simpa using (Complex.lt_def.mp this).1
  rcases hσ1.lt_or_eq with hσ1 | rfl
  · by_contra hneg
    push_neg at hneg
    have hcont : ContinuousOn (fun x : ℝ ↦ (χ.LFunction x).re) (Icc σ 1) :=
      (Complex.continuous_re.comp ((DirichletCharacter.differentiable_LFunction hχ).continuous.comp
        Complex.continuous_ofReal)).continuousOn
    have hmem : (0 : ℝ) ∈ Icc (χ.LFunction σ).re (χ.LFunction (1 : ℝ)).re := ⟨hneg, h1.le⟩
    obtain ⟨x, hx, hx0⟩ := intermediate_value_Icc hσ1.le hcont hmem
    have hx1 : x ≠ 1 := by
      rintro rfl; simp only at hx0; linarith
    have hz : χ.LFunction x = 0 := by
      rw [eq_ofReal_re_of_im_eq_zero (LFunction_ofReal_im hq hχ x)]
      simp only at hx0
      rw [hx0, Complex.ofReal_zero]
    exact h x (by linarith [hx.1]) (lt_of_le_of_ne hx.2 hx1) hz
  · exact h1

/-- There are no nonprincipal characters modulo `1` or `2`. -/
lemma three_le_of_ne_one {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) : 3 ≤ N := by
  by_contra hN
  push_neg at hN
  apply hχ
  have hsub : Subsingleton (ZMod N)ˣ := by
    rw [← Fintype.card_le_one_iff_subsingleton, ZMod.card_units_eq_totient]
    interval_cases N
    · exact absurd rfl (NeZero.ne 0)
    · simp
    · simp
  refine MulChar.ext fun a ↦ ?_
  rw [Subsingleton.elim a 1]
  simp

/-- **Davenport, Ch. 14, (13)** (at `σ = 1`): there is an absolute `c` with `|L(1, χ)| ≤ c log q`
for `χ ≠ χ₀` mod `q`. -/
lemma exists_norm_LFunction_one_le_log :
    ∃ c : ℝ, 0 < c ∧ ∀ {k : ℕ} [NeZero k] {χ : DirichletCharacter ℂ k}, χ ≠ 1 →
      ‖χ.LFunction 1‖ ≤ c * Real.log k := by
  obtain ⟨c, hc, h⟩ := Davenport.norm_LFunction_near_one_le
  refine ⟨c, hc, fun {k} _ {χ} hχ ↦ ?_⟩
  have hk := three_le_of_ne_one hχ
  have hk3 : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hL0 : 0 < Real.log k := Real.log_pos (by linarith)
  have hlim : Tendsto (fun x : ℝ ↦ ‖χ.LFunction x‖) (𝓝[<] 1) (𝓝 ‖χ.LFunction 1‖) := by
    have hc' := (DirichletCharacter.differentiable_LFunction hχ).continuous
    have : Tendsto (fun x : ℝ ↦ χ.LFunction x) (𝓝 1) (𝓝 (χ.LFunction 1)) := by
      have := (hc'.comp Complex.continuous_ofReal).tendsto 1
      rw [Function.comp_apply, Complex.ofReal_one] at this
      exact this
    exact (this.mono_left nhdsWithin_le_nhds).norm
  refine le_of_tendsto hlim ?_
  have hlt : 1 - 1 / Real.log k < 1 := by
    have : 0 < 1 / Real.log k := by positivity
    linarith
  filter_upwards [Ioo_mem_nhdsLT hlt] with x hx
  exact h hχ hk x hx.1.le hx.2

/-- For real characters, if `χ₁ χ₂ = χ₀` (at the least common multiple of the levels) then the
conductors agree; so real primitive characters of distinct moduli have `χ₁ χ₂ ≠ χ₀`. -/
lemma mul_ne_one_of_lt {q₁ q₂ : ℕ} [NeZero q₁] [NeZero q₂] {χ₁ : DirichletCharacter ℂ q₁}
    {χ₂ : DirichletCharacter ℂ q₂} (hq₁ : χ₁.IsQuadratic) (hp₂ : χ₂.IsPrimitive)
    (hlt : q₁ < q₂) : χ₁.mul χ₂ ≠ 1 := by
  intro h
  have hinv : χ₁⁻¹ = χ₁ :=
    inv_eq_of_mul_eq_one_left (by rw [← sq]; exact MulChar.isQuadratic_iff_sq_eq_one.mp hq₁)
  have h2 : DirichletCharacter.changeLevel (Nat.dvd_lcm_right q₁ q₂) χ₂ =
      DirichletCharacter.changeLevel (Nat.dvd_lcm_left q₁ q₂) χ₁ := by
    have := eq_inv_of_mul_eq_one_right h
    rw [this, ← map_inv, hinv]
  have hc := congrArg DirichletCharacter.conductor h2
  rw [DirichletCharacter.conductor_changeLevel, DirichletCharacter.conductor_changeLevel] at hc
  have h1 : χ₁.conductor ≤ q₁ :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q₁)) χ₁.conductor_dvd_level
  rw [DirichletCharacter.isPrimitive_def] at hp₂
  omega

/-- The product of real characters (at the least common multiple of the levels) is real. -/
lemma mul_isQuadratic {q₁ q₂ : ℕ} {χ₁ : DirichletCharacter ℂ q₁}
    {χ₂ : DirichletCharacter ℂ q₂} (hq₁ : χ₁.IsQuadratic) (hq₂ : χ₂.IsQuadratic) :
    (χ₁.mul χ₂).IsQuadratic := by
  rw [MulChar.isQuadratic_iff_sq_eq_one] at hq₁ hq₂ ⊢
  rw [DirichletCharacter.mul, mul_pow, ← map_pow, ← map_pow, hq₁, hq₂, map_one, map_one, one_mul]

/-- `χ₄` is a real primitive character. -/
lemma chi4_isQuadratic : NTKB.chi4.IsQuadratic := ZMod.isQuadratic_χ₄.comp _

lemma chi4_ne_one : NTKB.chi4 ≠ 1 := by
  intro h
  have := NTKB.Davenport.chi4_neg_one
  rw [h, MulChar.one_apply (isUnit_neg_one)] at this
  norm_num at this

/-- Finitely many moduli: a positive lower bound for `L(1, χ)` over the real characters
`χ ≠ χ₀` with modulus `q ≤ Q`. -/
lemma exists_lower_bound_le (Q : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ {q : ℕ} [NeZero q], q ≤ Q → ∀ χ : DirichletCharacter ℂ q,
      χ.IsQuadratic → χ ≠ 1 → c ≤ (χ.LFunction 1).re := by
  induction Q with
  | zero => exact ⟨1, one_pos, fun {q} _ hq ↦ absurd (Nat.le_zero.mp hq) (NeZero.ne q)⟩
  | succ Q ih =>
    obtain ⟨c, hc, h⟩ := ih
    have hpos : ∀ (χ : DirichletCharacter ℂ (Q + 1)), χ.IsQuadratic → χ ≠ 1 →
        0 < (χ.LFunction 1).re := fun χ hq hχ ↦ by
      have := Davenport.LFunction_one_pos_of_isQuadratic hq hχ
      exact (Complex.lt_def.mp this).1
    classical
    set S := (Finset.univ : Finset (DirichletCharacter ℂ (Q + 1))).filter
      (fun χ ↦ χ.IsQuadratic ∧ χ ≠ 1)
    obtain ⟨c', hc', h'⟩ : ∃ c' : ℝ, 0 < c' ∧ ∀ χ ∈ S, c' ≤ (χ.LFunction 1).re := by
      rcases S.eq_empty_or_nonempty with hS | hS
      · exact ⟨1, one_pos, by simp [hS]⟩
      · obtain ⟨χ₀, hχ₀, hmin⟩ := S.exists_min_image (fun χ ↦ (χ.LFunction 1).re) hS
        have hχ₀' := (Finset.mem_filter.mp hχ₀).2
        exact ⟨_, hpos χ₀ hχ₀'.1 hχ₀'.2, hmin⟩
    refine ⟨min c c', lt_min hc hc', fun {q} _ hq χ hqχ hχ ↦ ?_⟩
    rcases Nat.lt_or_ge q (Q + 1) with hlt | hge
    · exact (min_le_left _ _).trans (h (by omega) χ hqχ hχ)
    · obtain rfl : q = Q + 1 := by omega
      exact (min_le_right _ _).trans (h' χ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hqχ, hχ⟩))

end Aux

/-- **Estermann's case distinction (Davenport, Ch. 21, p. 130)**: for `0 < η ≤ 1/4` there are a
real primitive character `χ₁ ≠ χ₀` and `1 - η < β₁ < 1` such that `F(β₁) ≤ 0` for every real
character `χ₂ ≠ χ₀` with `χ₁ χ₂ ≠ χ₀`. (If some real character has a zero in `(1 - η, 1)`, the
primitive character inducing it and that zero; otherwise `χ₄` and `β₁ = 1 - η/2`.) -/
@[kb "davenport1980" "Ch 21, p. 130"]
theorem siegel_case_distinction {η : ℝ} (hη : 0 < η) (hη4 : η ≤ 1 / 4) :
    ∃ (q₁ : ℕ) (_ : NeZero q₁) (χ₁ : DirichletCharacter ℂ q₁) (β₁ : ℝ),
      χ₁.IsPrimitive ∧ χ₁.IsQuadratic ∧ χ₁ ≠ 1 ∧ 1 - η < β₁ ∧ β₁ < 1 ∧
      ∀ {q₂ : ℕ} [NeZero q₂] (χ₂ : DirichletCharacter ℂ q₂), χ₂.IsQuadratic → χ₂ ≠ 1 →
        χ₁.mul χ₂ ≠ 1 → (siegelF χ₁ χ₂ β₁).re ≤ 0 := by
  by_cases hA : ∃ (q : ℕ) (_ : NeZero q) (χ : DirichletCharacter ℂ q) (β : ℝ),
      χ.IsQuadratic ∧ χ ≠ 1 ∧ 1 - η < β ∧ β < 1 ∧ χ.LFunction β = 0
  · obtain ⟨q, _, χ, β, hq, hχ, hβ, hβ1, hz⟩ := hA
    have : NeZero χ.conductor := ⟨DirichletCharacter.conductor_ne_zero χ⟩
    have hz' := NTKB.LFunction_primitiveCharacter_eq_zero hχ hz (by simp; linarith)
    refine ⟨χ.conductor, inferInstance, χ.primitiveCharacter, β,
      DirichletCharacter.primitiveCharacter_isPrimitive χ,
      MulChar.isQuadratic_iff_sq_eq_one.mpr
        (NTKB.primitiveCharacter_sq_eq_one (MulChar.isQuadratic_iff_sq_eq_one.mp hq)),
      NTKB.primitiveCharacter_ne_one hχ, hβ, hβ1, fun χ₂ _ _ _ ↦ ?_⟩
    simp [siegelF, siegelG, hz']
  · push_neg at hA
    refine ⟨4, inferInstance, NTKB.chi4, 1 - η / 2, NTKB.isPrimitive_chi4, chi4_isQuadratic,
      chi4_ne_one, by linarith, by linarith, fun {q₂} _ χ₂ hq₂ h₂ h₁₂ ↦ ?_⟩
    set β : ℝ := 1 - η / 2 with hβ
    have hgt : 1 - η < β := by linarith
    have hlt : β ≤ 1 := by linarith
    have hfree : ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsQuadratic → χ ≠ 1 →
        ∀ σ : ℝ, 1 - η < σ → σ < 1 → χ.LFunction σ ≠ 0 :=
      fun {q} _ χ hq hχ σ h1 h2 ↦ hA q inferInstance χ σ hq hχ h1 h2
    have hmulq : (NTKB.chi4.mul χ₂).IsQuadratic := mul_isQuadratic chi4_isQuadratic hq₂
    have p1 := LFunction_re_pos_of_no_zero chi4_isQuadratic chi4_ne_one
      (hfree _ chi4_isQuadratic chi4_ne_one) hgt hlt
    have p2 := LFunction_re_pos_of_no_zero hq₂ h₂ (hfree _ hq₂ h₂) hgt hlt
    have p3 := LFunction_re_pos_of_no_zero hmulq h₁₂ (hfree _ hmulq h₁₂) hgt hlt
    have hz := NTKB.Apostol.riemannZeta_neg_of_lt_one (σ := β) (by linarith) (by linarith)
    rw [siegelF, siegelG,
      eq_ofReal_re_of_im_eq_zero hz.1,
      eq_ofReal_re_of_im_eq_zero (LFunction_ofReal_im chi4_isQuadratic chi4_ne_one β),
      eq_ofReal_re_of_im_eq_zero (LFunction_ofReal_im hq₂ h₂ β),
      eq_ofReal_re_of_im_eq_zero (LFunction_ofReal_im hmulq h₁₂ β)]
    simp only [← Complex.ofReal_mul, Complex.ofReal_re]
    have := mul_pos (mul_pos p1 p2) p3
    nlinarith [hz.2]

lemma rpow_neg_le_of_le {a b ε : ℝ} (ha : 0 < a) (hab : a ≤ b) (hε : 0 ≤ ε) :
    b ^ (-ε) ≤ a ^ (-ε) := by
  rw [Real.rpow_neg ha.le, Real.rpow_neg (ha.le.trans hab)]
  exact inv_anti₀ (Real.rpow_pos_of_pos ha _) (Real.rpow_le_rpow ha.le hab hε)

/-- **Siegel's theorem, Davenport, Ch. 21, p. 126, (1)**: for every `ε > 0` there is
`C₁(ε) > 0` such that `L(1, χ) > C₁(ε) q^{-ε}` for every real primitive character `χ ≠ χ₀`
mod `q`. (`L(1, χ)` is real, `LFunction_ofReal_im`; the constant is not effective.) -/
@[kb "davenport1980" "Ch 21, p. 126, (1)"]
theorem siegel {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}, χ.IsPrimitive →
      χ.IsQuadratic → χ ≠ 1 → C * (q : ℝ) ^ (-ε) < (χ.LFunction 1).re := by
  obtain ⟨c, C, hc, hC, hest⟩ := estermann_inequality
  obtain ⟨cL, hcL, hL1⟩ := exists_norm_LFunction_one_le_log
  set η := min (1 / 4) (ε / (4 * c)) with hη
  have hη0 : 0 < η := lt_min (by norm_num) (by positivity)
  have hη4 : η ≤ 1 / 4 := min_le_left _ _
  have hηc : c * η ≤ ε / 4 := by
    calc c * η ≤ c * (ε / (4 * c)) := by gcongr; exact min_le_right _ _
      _ = ε / 4 := by field_simp
  obtain ⟨q₁, _, χ₁, β₁, hp₁, hq₁, h₁, hβ, hβ1, hF⟩ := siegel_case_distinction hη0 hη4
  set δ := 1 - β₁ with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  have hδη : δ < η := by rw [hδ]; linarith
  have hβ34 : 3 / 4 ≤ β₁ := by linarith
  set ℓ := ‖χ₁.LFunction 1‖ with hℓ
  have hℓ0 : 0 < ℓ := norm_pos_iff.mpr (DirichletCharacter.LFunction_apply_one_ne_zero h₁)
  set K := δ * ε / (8 * C * cL * ℓ) with hK
  have hK0 : 0 < K := by positivity
  obtain ⟨c₀, hc₀, hfin⟩ := exists_lower_bound_le q₁
  refine ⟨min (c₀ / 2) (K / 2), by positivity, fun {q} _ {χ} hp hq hχ ↦ ?_⟩
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.one_le
  have hq0 : (0 : ℝ) < q := by linarith
  have hqε : (q : ℝ) ^ (-ε) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hq1 (by linarith)
  have hqε0 : 0 < (q : ℝ) ^ (-ε) := by positivity
  rcases le_or_gt q q₁ with hle | hlt
  · have := hfin hle χ hq hχ
    calc min (c₀ / 2) (K / 2) * (q : ℝ) ^ (-ε) ≤ c₀ / 2 * 1 :=
          mul_le_mul (min_le_left _ _) hqε hqε0.le (by positivity)
      _ < c₀ := by linarith
      _ ≤ _ := this
  have h12 := mul_ne_one_of_lt hq₁ hp hlt
  have hFβ := hF χ hq hχ h12
  have h8 := hest hq₁ hq h₁ hχ h12 β₁ hβ34 hβ1
  rw [← hδ] at h8
  set Q : ℝ := (q₁ : ℝ) * q with hQ
  have hq₁1 : (1 : ℝ) ≤ q₁ := by exact_mod_cast NeZero.one_le
  have hQ1 : 1 ≤ Q := by rw [hQ]; nlinarith
  set A := ‖siegelG χ₁ χ 1‖ with hAdef
  have hA : δ ≤ 2 * C * A * Q ^ (c * δ) := by
    have : 1 / 2 ≤ C * A * Q ^ (c * δ) / δ := by linarith
    rw [le_div_iff₀ hδ0] at this; linarith
  -- `A ≤ |L(1, χ₁)| L(1, χ) c log [q₁, q]`
  have hLpos := Davenport.LFunction_one_pos_of_isQuadratic hq hχ
  have hL2 : ‖χ.LFunction 1‖ = (χ.LFunction 1).re := by
    rw [eq_ofReal_re_of_im_eq_zero (z := χ.LFunction 1) (by simpa using LFunction_ofReal_im hq hχ 1)]
    rw [Complex.norm_real, Complex.ofReal_re, Real.norm_of_nonneg (Complex.lt_def.mp hLpos).1.le]
  have hlcm := hL1 h12
  have hLre : 0 < (χ.LFunction 1).re := (Complex.lt_def.mp hLpos).1
  set P := ℓ * (χ.LFunction 1).re * cL with hP
  have hP0 : 0 ≤ P := by positivity
  have hA2 : A ≤ P * Real.log (Nat.lcm q₁ q) := by
    rw [hAdef, siegelG, norm_mul, norm_mul, hL2, hP, mul_assoc _ cL]
    exact mul_le_mul_of_nonneg_left hlcm (mul_nonneg (norm_nonneg _) hLre.le)
  -- bounds in terms of `q`
  have hQq : Q ≤ (q : ℝ) ^ 2 := by
    have : (q₁ : ℝ) ≤ q := by exact_mod_cast hlt.le
    rw [hQ, sq]; exact mul_le_mul_of_nonneg_right this hq0.le
  have hQpow : Q ^ (c * δ) ≤ (q : ℝ) ^ (ε / 2) := by
    calc Q ^ (c * δ) ≤ Q ^ (ε / 4) :=
          Real.rpow_le_rpow_of_exponent_le hQ1 (by nlinarith)
      _ ≤ ((q : ℝ) ^ 2) ^ (ε / 4) := Real.rpow_le_rpow (by linarith) hQq (by positivity)
      _ = (q : ℝ) ^ (ε / 2) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hq0.le]; norm_num; ring_nf
  have hlog : Real.log (Nat.lcm q₁ q) ≤ 4 / ε * (q : ℝ) ^ (ε / 2) := by
    have h1 : (Nat.lcm q₁ q : ℝ) ≤ (q : ℝ) ^ 2 := (lcm_le_mul (NeZero.ne _) (NeZero.ne _)).trans hQq
    have hl0 : (0 : ℝ) < Nat.lcm q₁ q := by
      exact_mod_cast Nat.pos_of_ne_zero (Nat.lcm_ne_zero (NeZero.ne _) (NeZero.ne _))
    calc Real.log (Nat.lcm q₁ q) ≤ Real.log ((q : ℝ) ^ 2) := Real.log_le_log hl0 h1
      _ = 2 * Real.log q := by rw [Real.log_pow]; push_cast; ring
      _ ≤ 2 * ((q : ℝ) ^ (ε / 2) / (ε / 2)) := by
          gcongr; exact Real.log_le_rpow_div hq0.le (by positivity)
      _ = 4 / ε * (q : ℝ) ^ (ε / 2) := by field_simp; ring
  have hqq : (q : ℝ) ^ (ε / 2) * (q : ℝ) ^ (ε / 2) = (q : ℝ) ^ ε := by
    rw [← Real.rpow_add hq0]; ring_nf
  have hmain : δ * ε ≤ 8 * C * cL * ℓ * (χ.LFunction 1).re * (q : ℝ) ^ ε := by
    have s1 : A * Q ^ (c * δ) ≤ (P * (4 / ε * (q : ℝ) ^ (ε / 2))) * (q : ℝ) ^ (ε / 2) :=
      mul_le_mul (hA2.trans (mul_le_mul_of_nonneg_left hlog hP0)) hQpow (by positivity)
        (by positivity)
    have s2 : (P * (4 / ε * (q : ℝ) ^ (ε / 2))) * (q : ℝ) ^ (ε / 2) =
        4 / ε * P * (q : ℝ) ^ ε := by rw [← hqq]; ring
    have s3 : δ ≤ 2 * C * (4 / ε * P * (q : ℝ) ^ ε) := by
      calc δ ≤ 2 * C * A * Q ^ (c * δ) := hA
        _ = 2 * C * (A * Q ^ (c * δ)) := by ring
        _ ≤ 2 * C * (4 / ε * P * (q : ℝ) ^ ε) := by
          rw [← s2]; exact mul_le_mul_of_nonneg_left s1 (by positivity)
    have s4 : 2 * C * (4 / ε * P * (q : ℝ) ^ ε) =
        8 * C * cL * ℓ * (χ.LFunction 1).re * (q : ℝ) ^ ε / ε := by
      rw [hP]; field_simp; ring
    rw [s4, le_div_iff₀ hε] at s3
    exact s3
  have hKq : K * (q : ℝ) ^ (-ε) ≤ (χ.LFunction 1).re := by
    rw [Real.rpow_neg hq0.le, ← div_eq_mul_inv, div_le_iff₀ (by positivity), hK,
      div_le_iff₀ (by positivity)]
    linarith
  calc min (c₀ / 2) (K / 2) * (q : ℝ) ^ (-ε) ≤ K / 2 * (q : ℝ) ^ (-ε) := by
        gcongr; exact min_le_right _ _
    _ < K * (q : ℝ) ^ (-ε) := by nlinarith
    _ ≤ _ := hKq

/-- The primitive case of Davenport, Ch. 21, (E). -/
lemma siegel_real_zero_le_primitive {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ C ≤ 1 ∧ ∀ {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}, χ.IsPrimitive →
      χ.IsQuadratic → χ ≠ 1 → ∀ β : ℝ, χ.LFunction β = 0 → β ≤ 1 - C * (q : ℝ) ^ (-ε) := by
  obtain ⟨C₁, hC₁, hS⟩ := siegel (ε := ε / 2) (by positivity)
  obtain ⟨cd, hcd, hD⟩ := Davenport.norm_deriv_LFunction_near_one_le
  set C₃ := min (min 1 ε) (C₁ * ε ^ 2 / (16 * cd)) with hC₃
  refine ⟨C₃, by positivity, (min_le_left _ _).trans (min_le_left _ _),
    fun {q} _ {χ} hp hq hχ β hβ ↦ ?_⟩
  have hq3 : 3 ≤ q := three_le_of_ne_one hχ
  have hq3' : (3 : ℝ) ≤ q := by exact_mod_cast hq3
  have hq0 : (0 : ℝ) < q := by linarith
  have hlog1 : 1 < Real.log q :=
    (by norm_num : (1 : ℝ) < 1.0986122885).trans
      (Real.log_three_gt_d9.trans_le (Real.log_le_log (by norm_num) hq3'))
  have hlog0 : 0 < Real.log q := by linarith
  have hβ1 : β < 1 := by
    by_contra h
    push_neg at h
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) (by simpa using h) hβ
  have hqε : 0 < (q : ℝ) ^ ε := by positivity
  have hneg : (q : ℝ) ^ (-ε) = ((q : ℝ) ^ ε)⁻¹ := Real.rpow_neg hq0.le _
  rcases le_or_gt β (1 - 1 / Real.log q) with hcase | hcase
  · -- far from `1`: `C₃ q^{-ε} ≤ ε q^{-ε} ≤ 1/log q`
    have h1 : Real.log q ≤ (q : ℝ) ^ ε / ε := Real.log_le_rpow_div hq0.le hε
    have h2 : C₃ * (q : ℝ) ^ (-ε) ≤ 1 / Real.log q := by
      rw [hneg, ← div_eq_mul_inv, div_le_div_iff₀ hqε hlog0]
      have : C₃ ≤ ε := (min_le_left _ _).trans (min_le_right _ _)
      rw [le_div_iff₀ hε] at h1
      nlinarith
    linarith
  · -- near `1`: the mean value theorem with `|L'| ≪ log² q`
    have hS' := hS hp hq hχ
    have hmvt : ‖χ.LFunction 1‖ ≤ cd * Real.log q ^ 2 * (1 - β) := by
      have hf : ∀ x ∈ Icc β 1, HasDerivWithinAt (fun x : ℝ ↦ χ.LFunction x)
          (deriv χ.LFunction x) (Icc β 1) x := fun x _ ↦
        (((DirichletCharacter.differentiable_LFunction hχ) x).hasDerivAt.comp_ofReal).hasDerivWithinAt
      have hb : ∀ x ∈ Ico β 1, ‖deriv χ.LFunction x‖ ≤ cd * Real.log q ^ 2 := fun x hx ↦
        hD hχ hq3 x (by linarith [hx.1]) hx.2
      have := norm_image_sub_le_of_norm_deriv_le_segment' hf hb 1 ⟨hβ1.le, le_rfl⟩
      simpa [hβ] using this
    have hre : (χ.LFunction 1).re ≤ ‖χ.LFunction 1‖ := Complex.re_le_norm _
    have hlq : Real.log q ≤ 4 / ε * (q : ℝ) ^ (ε / 4) := by
      have := Real.log_le_rpow_div hq0.le (by positivity : 0 < ε / 4)
      calc Real.log q ≤ (q : ℝ) ^ (ε / 4) / (ε / 4) := this
        _ = 4 / ε * (q : ℝ) ^ (ε / 4) := by field_simp
    have hlq2 : Real.log q ^ 2 ≤ 16 / ε ^ 2 * (q : ℝ) ^ (ε / 2) := by
      calc Real.log q ^ 2 ≤ (4 / ε * (q : ℝ) ^ (ε / 4)) ^ 2 := by gcongr
        _ = 16 / ε ^ 2 * (q : ℝ) ^ (ε / 2) := by
          have hpow : ((q : ℝ) ^ (ε / 4)) ^ 2 = (q : ℝ) ^ (ε / 2) := by
            rw [← Real.rpow_mul_natCast hq0.le]; ring_nf
          rw [mul_pow, hpow]; ring
    -- `C₁ q^{-ε/2} < cd (16/ε²) q^{ε/2} (1 - β)`
    have hkey : C₁ * (q : ℝ) ^ (-(ε / 2)) < cd * (16 / ε ^ 2 * (q : ℝ) ^ (ε / 2)) * (1 - β) := by
      calc C₁ * (q : ℝ) ^ (-(ε / 2)) < (χ.LFunction 1).re := hS'
        _ ≤ cd * Real.log q ^ 2 * (1 - β) := hre.trans hmvt
        _ ≤ cd * (16 / ε ^ 2 * (q : ℝ) ^ (ε / 2)) * (1 - β) := by
            gcongr
    have hsplit : (q : ℝ) ^ (-(ε / 2)) = (q : ℝ) ^ (ε / 2) * (q : ℝ) ^ (-ε) := by
      rw [← Real.rpow_add hq0]; ring_nf
    rw [hsplit] at hkey
    have hpos : 0 < (q : ℝ) ^ (ε / 2) := by positivity
    have hkey2 : C₁ * ε ^ 2 / (16 * cd) * (q : ℝ) ^ (-ε) < 1 - β := by
      have : C₁ * (q : ℝ) ^ (-ε) < cd * (16 / ε ^ 2) * (1 - β) := by
        have h' : (q : ℝ) ^ (ε / 2) * (C₁ * (q : ℝ) ^ (-ε)) <
            (q : ℝ) ^ (ε / 2) * (cd * (16 / ε ^ 2) * (1 - β)) := by linarith
        exact lt_of_mul_lt_mul_left h' hpos.le
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      have e : cd * (16 / ε ^ 2) * (1 - β) * ε ^ 2 = (1 - β) * (16 * cd) := by field_simp
      have := mul_lt_mul_of_pos_right this (by positivity : (0 : ℝ) < ε ^ 2)
      linarith
    have : C₃ * (q : ℝ) ^ (-ε) ≤ C₁ * ε ^ 2 / (16 * cd) * (q : ℝ) ^ (-ε) := by
      gcongr; exact min_le_right _ _
    linarith

/-- **Davenport, Ch. 21, p. 127, (E)**: for every `ε > 0` there is `C₃(ε) > 0` such that every
real zero `β` of `L(s, χ)`, `χ` any real nonprincipal character mod `q`, satisfies
`β ≤ 1 - C₃(ε) q^{-ε}`. -/
@[kb "davenport1980" "Ch 21, p. 127, (E)"]
theorem siegel_real_zero_le {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q},
      χ.IsQuadratic → χ ≠ 1 → ∀ β : ℝ, χ.LFunction β = 0 → β ≤ 1 - C * (q : ℝ) ^ (-ε) := by
  obtain ⟨C, hC, hC1, h⟩ := siegel_real_zero_le_primitive hε
  refine ⟨C, hC, fun {q} _ {χ} hq hχ β hβ ↦ ?_⟩
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.one_le
  have hqε : (q : ℝ) ^ (-ε) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hq1 (by linarith)
  rcases le_or_gt β 0 with h0 | h0
  · nlinarith [Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ q) (-ε)]
  have : NeZero χ.conductor := ⟨DirichletCharacter.conductor_ne_zero χ⟩
  have hz := NTKB.LFunction_primitiveCharacter_eq_zero hχ hβ (by simpa using h0)
  have hb := h (DirichletCharacter.primitiveCharacter_isPrimitive χ)
    (MulChar.isQuadratic_iff_sq_eq_one.mpr
      (NTKB.primitiveCharacter_sq_eq_one (MulChar.isQuadratic_iff_sq_eq_one.mp hq)))
    (NTKB.primitiveCharacter_ne_one hχ) β hz
  have hd0 : (0 : ℝ) < χ.conductor := by
    exact_mod_cast Nat.pos_of_ne_zero (DirichletCharacter.conductor_ne_zero χ)
  have hdq : (χ.conductor : ℝ) ≤ q := by
    exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) χ.conductor_dvd_level
  have := rpow_neg_le_of_le hd0 hdq hε.le
  nlinarith

/-- **Siegel's theorem, second form (Davenport, Ch. 21, p. 126, (D))**: for every `ε > 0` there
is `C₃(ε) > 0` such that `L(σ, χ) ≠ 0` for real `σ > 1 - C₃(ε) q^{-ε}`, `χ` any real
nonprincipal character mod `q`. -/
@[kb "davenport1980" "Ch 21, p. 126, (D)"]
theorem siegel_second_form {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q},
      χ.IsQuadratic → χ ≠ 1 → ∀ σ : ℝ, 1 - C * (q : ℝ) ^ (-ε) < σ → χ.LFunction σ ≠ 0 := by
  obtain ⟨C, hC, h⟩ := siegel_real_zero_le hε
  exact ⟨C, hC, fun hq hχ σ hσ hz ↦ absurd (h hq hχ σ hz) (not_le.mpr hσ)⟩

end NTKB.Davenport
