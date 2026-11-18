/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Davenport.Zeros.PNTAPPage
import NTKB.Analytic.Davenport.Zeros.LEulerFactorZeros
import NTKB.Analytic.Davenport.Zeros.PrimeCounting

/-!
# The prime number theorem for progressions with the exceptional zero, in Davenport's form

**Davenport, Ch. 20, p. 123, (8), (9) (rows 20-4, 20-5) and Ch. 22, p. 143, (E) (row 22-4).** The theorems `Davenport.psi0L_sub_exceptional_le` and
`Davenport.psiAP_sub_le` carry the exceptional term as a sum over the zeros of
the primitive character `χ*` inducing `χ` in the region of 14-11 relative to the conductor of `χ`.
Here it is put in Davenport's form: the term `x^{β₁}/β₁` of the single exceptional character `χ₁`
modulo `q` and its single zero `β₁`, omitted if there is none.

* `IsExceptional χ β` (Davenport p. 123): `χ` real nonprincipal modulo `q`, `L(β, χ) = 0`,
  `β > 1 - c/log q` with `c = 1/16200`, the constant of 14-11.
* `Davenport.isExceptional_unique`: for each `q` there is at most one such pair `(χ₁, β₁)` (14-13:
  Landau; 14-11: the zero is unique).
* `excZero χ x`: `x^β/β` if `IsExceptional χ β`, and `0` if there is no such `β`.
* `norm_excTerm_sub_excZero_le`: the zeros of the sum `excTerm χ N` that are not exceptional
  relative to `q` contribute `≪ (log q + 1) N exp(-log N/(16200 log q))`; the rest is `excZero`.
* `Davenport.psiL_add_excZero_le` (20-4) and `Davenport.psiAP_sub_excZero_le` (20-5, 22-4).
-/

open Filter Topology Complex Set DirichletCharacter
open scoped Real ArithmeticFunction.vonMangoldt

namespace NTKB

/-- **Davenport, Ch. 20, p. 123**: `β` is an exceptional zero of `L(s, χ)` for the modulus `q`:
`χ` is a real nonprincipal character modulo `q` and `β > 1 - c/log q` is a real zero of `L(s, χ)`,
with `c = 1/16200` (the constant of the zero-free region 14-11, `IsExcPoint`). -/
def IsExceptional {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (β : ℝ) : Prop :=
  χ ≠ 1 ∧ χ ^ 2 = 1 ∧ LFunction χ β = 0 ∧ 1 - 1 / 16200 / Real.log q < β

variable {q : ℕ} [NeZero q]

lemma IsExceptional.isExcPoint {χ : DirichletCharacter ℂ q} {β : ℝ} (h : IsExceptional χ β) :
    IsExcPoint q (β : ℂ) := by
  have hq := two_le_of_ne_one h.1
  unfold IsExcPoint
  rw [logQT_of_lt_one (by linarith) (by simp)]
  simpa using h.2.2.2

lemma IsExceptional.lt_one {χ : DirichletCharacter ℂ q} {β : ℝ} (h : IsExceptional χ β) :
    β < 1 := by
  by_contra hb
  push Not at hb
  exact LFunction_ne_zero_of_one_le_re χ (Or.inl h.1) (by simpa using hb) h.2.2.1

lemma IsExceptional.half_lt {χ : DirichletCharacter ℂ q} {β : ℝ} (h : IsExceptional χ β) :
    1 / 2 < β := by
  simpa using h.isExcPoint.re_gt_half h.1

/-- **Davenport, Ch. 14, pp. 103-104 (rows 14-11, 14-13)**: for each modulus `q` there is at most
one exceptional character `χ₁`, and `L(s, χ₁)` has at most one exceptional zero `β₁`. -/
@[kb "davenport1980" "Ch 14, p. 104"]
theorem Davenport.isExceptional_unique {χ χ' : DirichletCharacter ℂ q} {β β' : ℝ}
    (h : IsExceptional χ β) (h' : IsExceptional χ' β') : χ = χ' ∧ β = β' := by
  have hq := two_le_of_ne_one h.1
  have hl2 := log_two_gt_two_thirds
  have hlq : Real.log 2 ≤ Real.log q := Real.log_le_log two_pos hq
  have hlt : 1 / 800 / Real.log q > 1 / 16200 / Real.log q := by
    apply div_lt_div_of_pos_right (by norm_num) (by linarith)
  have hχ : χ = χ' := Davenport.at_most_one_exceptional_character h.1 h'.1 h.2.1 h'.2.1
    h.2.2.1 h'.2.2.1 (by linarith [h.2.2.2]) (by linarith [h'.2.2.2])
  subst hχ
  refine ⟨rfl, ?_⟩
  have := (Davenport.LFunction_zero_free_theorem_real h.1 h.2.1 h.2.2.1 h.isExcPoint).2 (β' : ℂ)
    h'.2.2.1 h'.isExcPoint
  exact_mod_cast this.symm

open scoped Classical in
/-- Davenport's exceptional term `x^{β}/β` of `χ` (`β` the exceptional zero), or `0` if `L(s, χ)`
has no exceptional zero. -/
noncomputable def excZero (χ : DirichletCharacter ℂ q) (x : ℝ) : ℂ :=
  if h : ∃ β : ℝ, IsExceptional χ β then perronKernel x (h.choose : ℂ) else 0

lemma excZero_eq {χ : DirichletCharacter ℂ q} {β : ℝ} (h : IsExceptional χ β) (x : ℝ) :
    excZero χ x = perronKernel x β := by
  have hex : ∃ β : ℝ, IsExceptional χ β := ⟨β, h⟩
  rw [excZero, dif_pos hex, (Davenport.isExceptional_unique hex.choose_spec h).2]

lemma excZero_eq_zero {χ : DirichletCharacter ℂ q} (h : ∀ β : ℝ, ¬ IsExceptional χ β) (x : ℝ) :
    excZero χ x = 0 := by
  rw [excZero, dif_neg (by push Not; exact h)]

/-- A zero of `L(s, χ*)` with `σ > 0` is a zero of `L(s, χ)`. -/
lemma LFunction_eq_zero_of_primitiveCharacter {χ : DirichletCharacter ℂ q} {s : ℂ}
    (hs1 : s ≠ 1) :
    haveI : NeZero χ.conductor := ⟨conductor_ne_zero χ⟩
    LFunction χ.primitiveCharacter s = 0 → LFunction χ s = 0 := by
  haveI : NeZero χ.conductor := ⟨conductor_ne_zero χ⟩
  intro h
  have := (Davenport.LFunction_changeLevel_eq_zero_iff χ.conductor_dvd_level
    χ.primitiveCharacter hs1).mpr (Or.inl h)
  rwa [changeLevel_primitiveCharacter] at this

lemma log_conductor_le_log (χ : DirichletCharacter ℂ q) :
    Real.log χ.conductor ≤ Real.log q := by
  have hcq : (χ.conductor : ℝ) ≤ q := by
    exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) χ.conductor_dvd_level
  exact Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero (conductor_ne_zero χ)) hcq

/-- A zero `ρ` of `L(s, χ*)` counted in `excTerm χ` with `β > 1 - c/log q` is real, and `β` is an
exceptional zero of `χ` for the modulus `q`. -/
lemma isExceptional_of_mem {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1)
    (hcond : χ.conductor ≠ 1) :
    haveI : NeZero χ.conductor := ⟨conductor_ne_zero χ⟩
    ∀ ρ : ZeroIndex (dirichletXi χ.primitiveCharacter),
      IsExcPoint χ.conductor ρ.val → 1 - 1 / 16200 / Real.log q < ρ.val.re →
      ρ.val = (ρ.val.re : ℂ) ∧ IsExceptional χ ρ.val.re := by
  haveI : NeZero χ.conductor := ⟨conductor_ne_zero χ⟩
  intro ρ hexc hP
  have hprim := primitiveCharacter_isPrimitive χ
  have hχ1' : χ.primitiveCharacter ≠ 1 := primitiveCharacter_ne_one hχ
  obtain ⟨hz, h0, h1⟩ := dirichletXi_zero_mem hprim hcond ρ
  have him := (Davenport.exceptional_zero_real hχ1' hz hexc).2
  have hρr : ρ.val = (ρ.val.re : ℂ) := by apply Complex.ext <;> simp [him]
  have hzq : LFunction χ ρ.val = 0 :=
    LFunction_eq_zero_of_primitiveCharacter (fun h ↦ by rw [h] at h1; simp at h1) hz
  have hq := two_le_of_ne_one hχ
  have hexcq : IsExcPoint q ρ.val := by
    unfold IsExcPoint
    rw [logQT_of_lt_one (by linarith) (by rw [him]; simp)]
    exact hP
  have hreal := (Davenport.exceptional_zero_real hχ hzq hexcq).1
  refine ⟨hρr, hχ, hreal, by rw [← hρr]; exact hzq, hP⟩

open scoped Classical in
/-- The zeros of `excTerm χ` that are not exceptional for the modulus `q` contribute at most
`A (log q + 1) N exp(-log N/(16200 log q))`; the others give `excZero χ N`. -/
lemma norm_excTerm_sub_excZero_le :
    ∃ A : ℝ, 0 < A ∧ ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ N : ℕ,
      1 ≤ N → ‖excTerm χ N - excZero χ N‖ ≤
        A * (Real.log q + 1) * (N * Real.exp (-(1 / 16200 * Real.log N / Real.log q))) := by
  obtain ⟨A₆, hA₆, h₆⟩ := card_zerosBelowL_one_le
  refine ⟨2 * A₆, by positivity, ?_⟩
  intro q _ χ hχ N hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hq := two_le_of_ne_one hχ
  have hlq : 0 < Real.log q := Real.log_pos (by linarith)
  have hcond : χ.conductor ≠ 1 := fun h ↦ hχ (eq_one_iff_conductor_eq_one.mpr h)
  haveI : NeZero χ.conductor := ⟨conductor_ne_zero χ⟩
  have hprim := primitiveCharacter_isPrimitive χ
  have hχ1' : χ.primitiveCharacter ≠ 1 := primitiveCharacter_ne_one hχ
  have hlc := log_conductor_le_log χ
  have hlc0 : 0 < Real.log χ.conductor := by
    have := two_le_of_ne_one hχ1'
    exact Real.log_pos (by linarith)
  have hc1 : (1 : ℝ) ≤ χ.conductor := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (conductor_ne_zero χ)
  set E := Real.exp (-(1 / 16200 * Real.log N / Real.log q)) with hE
  have hE0 : 0 < E := Real.exp_pos _
  set Z := (zerosBelowL hprim hcond 1).filter (fun ρ ↦ IsExcPoint χ.conductor ρ.val) with hZ
  have hexc : excTerm χ N = ∑ ρ ∈ Z, perronKernel N ρ.val := by
    simp only [excTerm, dif_pos hcond, hZ]
  set P : ZeroIndex (dirichletXi χ.primitiveCharacter) → Prop :=
    fun ρ ↦ 1 - 1 / 16200 / Real.log q < ρ.val.re with hP
  rw [hexc, ← Finset.sum_filter_add_sum_filter_not Z P]
  -- the exceptional part
  have hbig : ∑ ρ ∈ Z.filter P, perronKernel N ρ.val = excZero χ N := by
    by_cases hex : ∃ β : ℝ, IsExceptional χ β
    · obtain ⟨β, hβ⟩ := hex
      rw [excZero_eq hβ]
      have hfib : Z.filter P =
          (zerosBelowL hprim hcond 1).filter (fun ρ ↦ ρ.val = (β : ℂ)) := by
        ext ρ
        simp only [hZ, Finset.mem_filter, mem_zerosBelowL, hP]
        constructor
        · rintro ⟨⟨hlt, hx⟩, hp⟩
          obtain ⟨hr, hρ⟩ := isExceptional_of_mem hχ hcond ρ hx hp
          exact ⟨hlt, by rw [hr, (Davenport.isExceptional_unique hρ hβ).2]⟩
        · rintro ⟨-, hv⟩
          rw [hv]
          have hb := hβ.2.2.2
          have : 1 / 16200 / Real.log q ≤ 1 / 16200 / Real.log χ.conductor :=
            div_le_div_of_nonneg_left (by norm_num) hlc0 hlc
          refine ⟨⟨by simp, ?_⟩, by simpa using hb⟩
          unfold IsExcPoint
          rw [logQT_of_lt_one hc1 (by simp)]
          simp only [ofReal_re]
          linarith
      have hcongr : ∑ ρ ∈ (zerosBelowL hprim hcond 1).filter (fun ρ ↦ ρ.val = (β : ℂ)),
          perronKernel N ρ.val = ∑ ρ ∈ (zerosBelowL hprim hcond 1).filter
            (fun ρ ↦ ρ.val = (β : ℂ)), perronKernel N β :=
        Finset.sum_congr rfl fun ρ hρ ↦ by rw [(Finset.mem_filter.mp hρ).2]
      rw [hfib, hcongr, Finset.sum_const, card_fiber_zerosBelowL (by simp)]
      have hz := LFunction_primitiveCharacter_eq_zero hχ hβ.2.2.1 (by
        simp only [ofReal_re]; linarith [hβ.half_lt])
      obtain ⟨ρ, hρ⟩ := exists_zeroIndex_dirichletXi hprim hcond hz (by
        simp only [ofReal_re]; linarith [hβ.half_lt])
      have hreg : 1 - 1 / 16200 / logQT χ.conductor ρ.val.im < ρ.val.re := by
        rw [hρ, logQT_of_lt_one hc1 (by simp)]
        simp only [ofReal_re]
        have : 1 / 16200 / Real.log q ≤ 1 / 16200 / Real.log χ.conductor :=
          div_le_div_of_nonneg_left (by norm_num) hlc0 hlc
        linarith [hβ.2.2.2]
      have h1 := Davenport.LFunction_zero_free_theorem_real_simple hprim hχ1'
        (primitiveCharacter_sq_eq_one hβ.2.1) ρ hreg
      rw [hρ] at h1
      rw [h1, one_smul]
    · push Not at hex
      rw [excZero_eq_zero hex]
      refine Finset.sum_eq_zero fun ρ hρ ↦ ?_
      exfalso
      obtain ⟨hρZ, hp⟩ := Finset.mem_filter.mp hρ
      exact hex _ (isExceptional_of_mem hχ hcond ρ (Finset.mem_filter.mp hρZ).2 hp).2
  rw [hbig, add_sub_cancel_left]
  -- the rest
  refine (norm_sum_le _ _).trans ?_
  have hpt : ∀ ρ ∈ Z.filter (fun ρ ↦ ¬ P ρ), ‖perronKernel N ρ.val‖ ≤ 2 * (N * E) := by
    intro ρ hρ
    obtain ⟨hρZ, hnp⟩ := Finset.mem_filter.mp hρ
    have hx := (Finset.mem_filter.mp hρZ).2
    have hz := (dirichletXi_zero_mem hprim hcond ρ).1
    have hhalf := hx.re_gt_half hχ1'
    have hβ : ρ.val.re ≤ 1 - 1 / 16200 / Real.log q := by
      simp only [hP] at hnp; push Not at hnp; exact hnp
    rw [norm_perronKernel hN0]
    have h1 : (N : ℝ) ^ ρ.val.re ≤ N * E := by
      calc (N : ℝ) ^ ρ.val.re ≤ (N : ℝ) ^ (1 - 1 / 16200 / Real.log q) :=
            Real.rpow_le_rpow_of_exponent_le hN1 hβ
        _ = N * E := by
            rw [Real.rpow_sub hN0, Real.rpow_one, Real.rpow_def_of_pos hN0, div_eq_mul_inv (N : ℝ),
              ← Real.exp_neg, hE]
            congr 2; ring
    have h2 : 1 / 2 ≤ ‖ρ.val‖ := by linarith [Complex.re_le_norm ρ.val]
    rw [div_le_iff₀ (by linarith)]
    have hNE : 0 ≤ (N : ℝ) * E := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h2 hNE]
  calc ∑ ρ ∈ Z.filter (fun ρ ↦ ¬ P ρ), ‖perronKernel N ρ.val‖
      ≤ ∑ ρ ∈ Z.filter (fun ρ ↦ ¬ P ρ), 2 * (N * E) := Finset.sum_le_sum hpt
    _ ≤ ((zerosBelowL hprim hcond 1).card : ℝ) * (2 * (N * E)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        have hcard : ((Z.filter (fun ρ ↦ ¬ P ρ)).card : ℝ) ≤ (zerosBelowL hprim hcond 1).card :=
          Nat.cast_le.mpr ((Finset.card_filter_le _ _).trans (Finset.card_filter_le _ _))
        have : 0 ≤ 2 * ((N : ℝ) * E) := by positivity
        exact mul_le_mul_of_nonneg_right hcard this
    _ ≤ A₆ * (Real.log q + 1) * (2 * (N * E)) := by
        gcongr
        exact (h₆ hprim hcond).trans (by gcongr)
    _ = 2 * A₆ * (Real.log q + 1) * (N * E) := by ring

/-- `exp(-L/(16200 log q)) ≤ exp(-√L/(16200 C))` when `log q ≤ C √L`. -/
lemma exp_neg_div_log_le {C L lq : ℝ} (hC : 0 < C) (hlq : 0 < lq) (hL : 0 ≤ L)
    (h : lq ≤ C * √L) :
    Real.exp (-(1 / 16200 * L / lq)) ≤ Real.exp (-(1 / (16200 * C) * √L)) := by
  apply Real.exp_le_exp.mpr
  have hs := Real.sq_sqrt hL
  have hs0 := Real.sqrt_nonneg L
  have : √L / C ≤ L / lq := by
    rw [div_le_div_iff₀ hC hlq]; nlinarith
  have e1 : 1 / 16200 * L / lq = (1 / 16200) * (L / lq) := by ring
  have e2 : 1 / (16200 * C) * √L = (1 / 16200) * (√L / C) := by field_simp
  rw [e1, e2]; linarith

/-- `(log q + 1) exp(-L/(16200 log q)) ≤ K exp(-a √L / 2)` for `√L ≥ 1`, `log q ≤ C √L`,
`a = 1/(16200 C)`, `K = 2 (C + 1)/a`. -/
lemma log_add_one_mul_exp_le {C L lq : ℝ} (hC : 0 < C) (hlq : 0 < lq) (hL : 1 ≤ √L)
    (h : lq ≤ C * √L) :
    (lq + 1) * Real.exp (-(1 / 16200 * L / lq)) ≤
      2 * (C + 1) * (16200 * C) * Real.exp (-(1 / (16200 * C) / 2 * √L)) := by
  have hL0 : 0 ≤ L := by
    by_contra hneg; push Not at hneg
    rw [Real.sqrt_eq_zero_of_nonpos hneg.le] at hL; linarith
  set u := √L with hu
  set a := 1 / (16200 * C) with ha
  have ha0 : 0 < a := by positivity
  have h1 := exp_neg_div_log_le hC hlq hL0 h
  rw [← hu, ← ha] at h1
  -- `u ≤ (2/a) exp(a u/2)`
  have h2 : a * u / 2 ≤ Real.exp (a * u / 2) := by
    have := Real.add_one_le_exp (a * u / 2); linarith
  have h3 : Real.exp (-(a * u)) = Real.exp (-(a / 2 * u)) * Real.exp (-(a * u / 2)) := by
    rw [← Real.exp_add]; congr 1; ring
  have h4 : Real.exp (a * u / 2) * Real.exp (-(a * u / 2)) = 1 := by
    rw [← Real.exp_add]; simp
  have hE0 : 0 < Real.exp (-(a / 2 * u)) := Real.exp_pos _
  have hE1 : 0 < Real.exp (-(a * u / 2)) := Real.exp_pos _
  have hlq1 : lq + 1 ≤ (C + 1) * u := by nlinarith
  have hinv : 1 / a = 16200 * C := by rw [ha]; field_simp
  calc (lq + 1) * Real.exp (-(1 / 16200 * L / lq)) ≤ (C + 1) * u * Real.exp (-(a * u)) := by
        gcongr
    _ = (C + 1) * Real.exp (-(a / 2 * u)) * (u * Real.exp (-(a * u / 2))) := by rw [h3]; ring
    _ ≤ (C + 1) * Real.exp (-(a / 2 * u)) * (2 / a) := by
        gcongr
        have : a * u / 2 * Real.exp (-(a * u / 2)) ≤ 1 := by
          calc a * u / 2 * Real.exp (-(a * u / 2)) ≤
              Real.exp (a * u / 2) * Real.exp (-(a * u / 2)) := by gcongr
            _ = 1 := h4
        rw [le_div_iff₀ ha0]; nlinarith
    _ = 2 * (C + 1) * (16200 * C) * Real.exp (-(a / 2 * u)) := by
        rw [← hinv]; field_simp

open scoped Classical in
/-- `∑_χ χ̄(a) excZero(χ, x)` is `χ₁(a) x^{β₁}/β₁` for the exceptional pair, `0` if there is none. -/
lemma sum_excZero_eq {a : ZMod q} (ha : IsUnit a) (x : ℝ) :
    ((∀ (χ : DirichletCharacter ℂ q) (β : ℝ), ¬ IsExceptional χ β) →
      ∑ χ : DirichletCharacter ℂ q, χ a⁻¹ * excZero χ x = 0) ∧
    (∀ (χ₁ : DirichletCharacter ℂ q) (β₁ : ℝ), IsExceptional χ₁ β₁ →
      ∑ χ : DirichletCharacter ℂ q, χ a⁻¹ * excZero χ x = χ₁ a * perronKernel x β₁) := by
  constructor
  · intro h
    exact Finset.sum_eq_zero fun χ _ ↦ by rw [excZero_eq_zero (h χ), mul_zero]
  · intro χ₁ β₁ h₁
    rw [Finset.sum_eq_single χ₁]
    · rw [excZero_eq h₁]
      congr 1
      -- `χ₁(a⁻¹) = χ₁(a)` for a real character
      have h1 : χ₁ a⁻¹ * χ₁ a = 1 := by rw [← map_mul, ZMod.inv_mul_of_unit a ha, map_one]
      have h2 : χ₁ a * χ₁ a = 1 := by
        have := congrArg (fun ψ : DirichletCharacter ℂ q ↦ ψ a) h₁.2.1
        simpa [sq, MulChar.one_apply ha] using this
      linear_combination (χ₁ a) * h1 - (χ₁ a⁻¹) * h2
    · intro χ _ hχ
      have : ∀ β, ¬ IsExceptional χ β := fun β hβ ↦ hχ (Davenport.isExceptional_unique hβ h₁).1
      rw [excZero_eq_zero this, mul_zero]
    · simp

/-- Common bookkeeping: for `N ≥ 3`, `u = √log N` satisfies `u > 1`, `u² = log N`,
`exp(u²) = N`. -/
lemma sqrt_log_facts {N : ℕ} (hN : 3 ≤ N) :
    1 < √(Real.log N) ∧ √(Real.log N) ^ 2 = Real.log N ∧ Real.exp (√(Real.log N) ^ 2) = N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hL1 : 1 < Real.log N := by
    rw [Real.lt_log_iff_exp_lt hN0]
    have := Real.exp_one_lt_d9
    have : (3 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hu2 : √(Real.log N) ^ 2 = Real.log N := Real.sq_sqrt (by linarith)
  refine ⟨by rw [Real.lt_sqrt zero_le_one]; linarith, hu2, by rw [hu2, Real.exp_log hN0]⟩

lemma exp_neg_mono {c c' u : ℝ} (hc : c ≤ c') (hu : 0 ≤ u) :
    Real.exp (-(c' * u)) ≤ Real.exp (-(c * u)) :=
  Real.exp_le_exp.mpr (by nlinarith)

open scoped Classical in
set_option maxHeartbeats 1000000 in
/-- **Davenport, Ch. 20, p. 123, (8) (row 20-4), as stated**: for every `C > 0` there are
`c, A > 0` such that for every nonprincipal character `χ` modulo `q` and every integer `N ≥ 3` with
`log q ≤ C √log N`, `ψ(N, χ) = -N^{β₁}/β₁ + O(N exp(-c √log N))`, where the term `N^{β₁}/β₁` is
present only if `β₁` is an exceptional zero of `L(s, χ)` for the modulus `q` (`excZero`). -/
@[kb "davenport1980" "Ch 20, p. 123"]
theorem Davenport.psiL_add_excZero_le (C : ℝ) (hC : 0 < C) :
    ∃ c A : ℝ, 0 < c ∧ 0 < A ∧ ∀ {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}, χ ≠ 1 →
      ∀ N : ℕ, 3 ≤ N → Real.log q ≤ C * √(Real.log N) →
      ‖psiL χ N + excZero χ N‖ ≤ A * N * Real.exp (-(c * √(Real.log N))) := by
  obtain ⟨c₄, A₄, hc₄, hA₄, h₄⟩ := Davenport.psi0L_sub_exceptional_le C hC
  obtain ⟨A₁, hA₁, h₁⟩ := norm_excTerm_sub_excZero_le
  set a := 1 / (16200 * C) / 2 with ha
  have ha0 : 0 < a := by positivity
  set c := min (min c₄ a) (1 / 2) with hcdef
  have hc0 : 0 < c := lt_min (lt_min hc₄ ha0) one_half_pos
  have hcc₄ : c ≤ c₄ := (min_le_left _ _).trans (min_le_left _ _)
  have hca : c ≤ a := (min_le_left _ _).trans (min_le_right _ _)
  have hc2 : c ≤ 1 / 2 := min_le_right _ _
  set K := 24 * (2 / c) ^ 4 with hK
  have hK0 : 0 < K := by positivity
  set K' := 2 * (C + 1) * (16200 * C) with hK'
  have hK'0 : 0 < K' := by positivity
  refine ⟨c, A₄ + A₁ * K' + K * (2 * C + 1), hc0, by positivity, ?_⟩
  intro q _ χ hχ N hN hqN
  obtain ⟨hu1, hu2, hNexp⟩ := sqrt_log_facts hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  set L := Real.log N with hL
  set u := √L with hu
  have hu0 : 0 ≤ u := by linarith
  have hq := two_le_of_ne_one hχ
  have hlq : 0 < Real.log q := Real.log_pos (by linarith)
  have hl2 := log_two_gt_two_thirds
  set E := Real.exp (-(c * u)) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have hcond : χ.conductor ≠ 1 := fun h ↦ hχ (eq_one_iff_conductor_eq_one.mpr h)
  haveI : NeZero χ.conductor := ⟨conductor_ne_zero χ⟩
  have hprim := primitiveCharacter_isPrimitive χ
  have hlc : Real.log χ.conductor ≤ C * √(Real.log N) := (log_conductor_le_log χ).trans hqN
  have h2 := h₄ hprim hcond N hN hlc
  have hexc : excTerm χ N = ∑ ρ ∈ (zerosBelowL hprim hcond 1).filter
      (fun ρ ↦ IsExcPoint χ.conductor ρ.val), perronKernel N ρ.val := by
    simp only [excTerm, dif_pos hcond]
  have hsplit : psiL χ N + excZero χ N = (psiL χ N - psiL χ.primitiveCharacter N) +
      χ.primitiveCharacter N * Λ N / 2 +
      (psi0L χ.primitiveCharacter N + ∑ ρ ∈ (zerosBelowL hprim hcond 1).filter
        (fun ρ ↦ IsExcPoint χ.conductor ρ.val), perronKernel N ρ.val) -
      (excTerm χ N - excZero χ N) := by
    rw [hexc, psiL_natCast_eq χ.primitiveCharacter N]; ring
  rw [hsplit]
  have t1 := Davenport.norm_psiL_sub_primitive_le χ hN1
  have t2 : ‖χ.primitiveCharacter N * Λ N / 2‖ ≤ L := by
    rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg, Complex.norm_two]
    have := DirichletCharacter.norm_le_one χ.primitiveCharacter N
    have h5 : Λ N ≤ L := ArithmeticFunction.vonMangoldt_le_log
    have h6 := ArithmeticFunction.vonMangoldt_nonneg (n := N)
    have : ‖χ.primitiveCharacter N‖ * Λ N ≤ L := by
      nlinarith [norm_nonneg (χ.primitiveCharacter N)]
    linarith
  have t3 : A₄ * N * Real.exp (-(c₄ * √(Real.log N))) ≤ A₄ * N * E := by
    gcongr; exact exp_neg_mono hcc₄ hu0
  have t4 : ‖excTerm χ N - excZero χ N‖ ≤ A₁ * K' * N * E := by
    refine (h₁ χ hχ N (by omega)).trans ?_
    have := log_add_one_mul_exp_le hC hlq hu1.le hqN
    rw [← hu] at this
    have h7 : Real.exp (-(1 / (16200 * C) / 2 * u)) ≤ E := exp_neg_mono hca hu0
    calc A₁ * (Real.log q + 1) * (N * Real.exp (-(1 / 16200 * L / Real.log q)))
        = A₁ * N * ((Real.log q + 1) * Real.exp (-(1 / 16200 * L / Real.log q))) := by ring
      _ ≤ A₁ * N * (K' * Real.exp (-(1 / (16200 * C) / 2 * u))) := by gcongr
      _ ≤ A₁ * N * (K' * E) := by gcongr
      _ = A₁ * K' * N * E := by ring
  -- `u⁴ ≤ K N E`
  have hu4 := pow_four_le_mul_exp hc0 hc2 hu1.le
  rw [← hK, hNexp] at hu4
  have hLu : L ≤ u ^ 4 := by
    rw [← hu2]; exact pow_le_pow_right₀ hu1.le (by norm_num)
  have hu4' : u ^ 4 ≤ K * N * E := by rw [mul_assoc]; exact hu4
  have h1' : L / Real.log 2 * Real.log q ≤ 2 * C * u ^ 4 := by
    have h1 : L / Real.log 2 ≤ 1.5 * L := by
      rw [div_le_iff₀ (by linarith)]; nlinarith
    have hL0 : 0 ≤ L := by rw [← hu2]; positivity
    have h2 : L * (C * u) ≤ C * u ^ 4 := by
      rw [← hu2]; nlinarith
    calc L / Real.log 2 * Real.log q ≤ 1.5 * L * (C * u) := by
          gcongr
      _ ≤ 2 * C * u ^ 4 := by nlinarith
  rw [← hL] at t1
  calc _ ≤ ‖psiL χ N - psiL χ.primitiveCharacter N‖ + ‖χ.primitiveCharacter N * Λ N / 2‖ +
        ‖psi0L χ.primitiveCharacter N + ∑ ρ ∈ (zerosBelowL hprim hcond 1).filter
          (fun ρ ↦ IsExcPoint χ.conductor ρ.val), perronKernel N ρ.val‖ +
        ‖excTerm χ N - excZero χ N‖ :=
        (norm_sub_le _ _).trans (add_le_add
          ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)
    _ ≤ (2 * C + 1) * u ^ 4 + A₄ * N * E + A₁ * K' * N * E := by linarith
    _ ≤ (2 * C + 1) * (K * N * E) + A₄ * N * E + A₁ * K' * N * E := by
        have : 0 ≤ 2 * C + 1 := by positivity
        nlinarith
    _ = (A₄ + A₁ * K' + K * (2 * C + 1)) * N * E := by ring

open scoped Classical in
set_option maxHeartbeats 1000000 in
/-- **Davenport, Ch. 20, p. 123, (9) (row 20-5)** with the exceptional term of every character
(`excZero`): for every `C > 0` there are `c, A > 0` such that, uniformly for `log q ≤ C √log N`
and `a` prime to `q`, `ψ(N; q, a) = N/φ(q) - (1/φ(q)) ∑_χ χ̄(a) excZero(χ, N) + O(N exp(-c √log N))`. -/
theorem Davenport.psiAP_sub_excZero_le (C : ℝ) (hC : 0 < C) :
    ∃ c A : ℝ, 0 < c ∧ 0 < A ∧ ∀ {q : ℕ} [NeZero q] {a : ZMod q}, IsUnit a →
      ∀ N : ℕ, 3 ≤ N → Real.log q ≤ C * √(Real.log N) →
      ‖(psiAP a N : ℂ) - N / q.totient +
          (q.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q, χ a⁻¹ * excZero χ N‖ ≤
        A * N * Real.exp (-(c * √(Real.log N))) := by
  obtain ⟨c₀, A₀, hc₀, hA₀, h₀⟩ := Davenport.psiAP_sub_le C hC
  obtain ⟨A₁, hA₁, h₁⟩ := norm_excTerm_sub_excZero_le
  set a' := 1 / (16200 * C) / 2 with ha'
  have ha0 : 0 < a' := by positivity
  set c := min c₀ a' with hcdef
  have hc0 : 0 < c := lt_min hc₀ ha0
  set K' := 2 * (C + 1) * (16200 * C) with hK'
  have hK'0 : 0 < K' := by positivity
  refine ⟨c, A₀ + A₁ * K', hc0, by positivity, ?_⟩
  intro q _ a ha N hN hqN
  obtain ⟨hu1, hu2, hNexp⟩ := sqrt_log_facts hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  set L := Real.log N with hL
  set u := √L with hu
  have hu0 : 0 ≤ u := by linarith
  set E := Real.exp (-(c * u)) with hE
  have hE0 : 0 < E := Real.exp_pos _
  set B₁ := A₁ * K' * N * E with hB₁
  have hB₁0 : 0 ≤ B₁ := by positivity
  -- each character
  have hchi : ∀ χ : DirichletCharacter ℂ q, ‖excTerm χ N - excZero χ N‖ ≤ B₁ := by
    intro χ
    by_cases hχ : χ = 1
    · have he : excTerm χ N = 0 := by
        have hc1 : χ.conductor = 1 := eq_one_iff_conductor_eq_one.mp hχ
        simp [excTerm, hc1]
      have hz : excZero χ N = 0 := excZero_eq_zero (fun β hβ ↦ hβ.1 hχ) _
      rw [he, hz, sub_zero, norm_zero]; exact hB₁0
    · have hq := two_le_of_ne_one hχ
      have hlq : 0 < Real.log q := Real.log_pos (by linarith)
      refine (h₁ χ hχ N (by omega)).trans ?_
      have := log_add_one_mul_exp_le hC hlq hu1.le hqN
      rw [← hu] at this
      have h7 : Real.exp (-(1 / (16200 * C) / 2 * u)) ≤ E :=
        exp_neg_mono (min_le_right _ _) hu0
      calc A₁ * (Real.log q + 1) * (N * Real.exp (-(1 / 16200 * L / Real.log q)))
          = A₁ * N * ((Real.log q + 1) * Real.exp (-(1 / 16200 * L / Real.log q))) := by ring
        _ ≤ A₁ * N * (K' * Real.exp (-(1 / (16200 * C) / 2 * u))) := by gcongr
        _ ≤ A₁ * N * (K' * E) := by gcongr
        _ = B₁ := by ring
  have hφ : (q.totient : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))).ne'
  have hφpos : (0 : ℝ) < q.totient := lt_of_le_of_ne (Nat.cast_nonneg _) (Ne.symm hφ)
  have hcard : (Finset.univ : Finset (DirichletCharacter ℂ q)).card = q.totient := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card,
      DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity]
  have hdiff : ‖(q.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q,
      χ a⁻¹ * (excTerm χ N - excZero χ N)‖ ≤ B₁ := by
    rw [norm_mul, norm_inv, Complex.norm_natCast]
    have : ‖∑ χ : DirichletCharacter ℂ q, χ a⁻¹ * (excTerm χ N - excZero χ N)‖ ≤
        q.totient * B₁ := by
      refine (norm_sum_le _ _).trans ?_
      calc ∑ χ : DirichletCharacter ℂ q, ‖χ a⁻¹ * (excTerm χ N - excZero χ N)‖
          ≤ ∑ χ : DirichletCharacter ℂ q, B₁ := by
            refine Finset.sum_le_sum fun χ _ ↦ ?_
            rw [norm_mul]
            have := DirichletCharacter.norm_le_one χ a⁻¹
            calc ‖χ a⁻¹‖ * ‖excTerm χ N - excZero χ N‖ ≤ 1 * B₁ :=
                  mul_le_mul this (hchi χ) (norm_nonneg _) zero_le_one
              _ = B₁ := one_mul B₁
        _ = q.totient * B₁ := by rw [Finset.sum_const, hcard, nsmul_eq_mul]
    calc (q.totient : ℝ)⁻¹ * ‖∑ χ : DirichletCharacter ℂ q, χ a⁻¹ * (excTerm χ N - excZero χ N)‖
        ≤ (q.totient : ℝ)⁻¹ * (q.totient * B₁) := by gcongr
      _ = B₁ := by field_simp
  have hsplit : (psiAP a N : ℂ) - N / q.totient +
      (q.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q, χ a⁻¹ * excZero χ N =
      ((psiAP a N : ℂ) - N / q.totient +
        (q.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q, χ a⁻¹ * excTerm χ N) -
      (q.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q, χ a⁻¹ * (excTerm χ N - excZero χ N) := by
    simp only [mul_sub, Finset.sum_sub_distrib]; ring
  rw [hsplit]
  have h0 := h₀ ha N hN hqN
  have h0' : A₀ * N * Real.exp (-(c₀ * √(Real.log N))) ≤ A₀ * N * E := by
    gcongr; exact exp_neg_mono (min_le_left _ _) hu0
  calc _ ≤ _ := norm_sub_le _ _
    _ ≤ A₀ * N * E + B₁ := add_le_add (h0.trans h0') hdiff
    _ = (A₀ + A₁ * K') * N * E := by rw [hB₁]; ring

set_option maxHeartbeats 1000000 in
/-- **Davenport, Ch. 20, p. 123, (9) (row 20-5), as stated; Ch. 22, p. 143, (E) (row 22-4)**.
For every `C > 0` there are `c, A > 0` such that for every `q`, every `a` prime to `q` and every
integer `N ≥ 3` with `q ≤ exp(C √log N)`:
* if no real nonprincipal character modulo `q` has an exceptional zero (`IsExceptional`), then
  `|ψ(N; q, a) - N/φ(q)| ≤ A N exp(-c √log N)`;
* if `χ₁` has the exceptional zero `β₁` (there is at most one such pair,
  `Davenport.isExceptional_unique`), then
  `|ψ(N; q, a) - N/φ(q) + χ₁(a) N^{β₁}/(φ(q) β₁)| ≤ A N exp(-c √log N)`. -/
@[kb "davenport1980" "Ch 20, p. 123"]
theorem Davenport.psiAP_exceptional (C : ℝ) (hC : 0 < C) :
    ∃ c A : ℝ, 0 < c ∧ 0 < A ∧ ∀ {q : ℕ} [NeZero q] {a : ZMod q}, IsUnit a →
      ∀ N : ℕ, 3 ≤ N → Real.log q ≤ C * √(Real.log N) →
      ((∀ (χ : DirichletCharacter ℂ q) (β : ℝ), ¬ IsExceptional χ β) →
        |psiAP a N - N / q.totient| ≤ A * N * Real.exp (-(c * √(Real.log N)))) ∧
      (∀ (χ₁ : DirichletCharacter ℂ q) (β₁ : ℝ), IsExceptional χ₁ β₁ →
        ‖(psiAP a N : ℂ) - N / q.totient + χ₁ a * (N : ℂ) ^ (β₁ : ℂ) / (q.totient * β₁)‖ ≤
          A * N * Real.exp (-(c * √(Real.log N)))) := by
  obtain ⟨c, A, hc, hA, h⟩ := Davenport.psiAP_sub_excZero_le C hC
  refine ⟨c, A, hc, hA, fun {q} _ {a} ha N hN hqN ↦ ⟨fun hno ↦ ?_, fun χ₁ β₁ h₁ ↦ ?_⟩⟩
  · have e := h ha N hN hqN
    rw [(sum_excZero_eq ha N).1 hno, mul_zero, add_zero] at e
    have : (psiAP a N : ℂ) - N / q.totient = ((psiAP a N - N / q.totient : ℝ) : ℂ) := by
      push_cast; ring
    rwa [this, Complex.norm_real, Real.norm_eq_abs] at e
  · have e := h ha N hN hqN
    rw [(sum_excZero_eq ha N).2 χ₁ β₁ h₁, perronKernel] at e
    have : (q.totient : ℂ)⁻¹ * (χ₁ a * ((N : ℝ) : ℂ) ^ (β₁ : ℂ) / (β₁ : ℂ)) =
        χ₁ a * (N : ℂ) ^ (β₁ : ℂ) / (q.totient * β₁) := by
      push_cast; field_simp
    rwa [mul_div_assoc', this] at e

/-! ### Real `x` -/

/-- `|x^β/β - N^β/β| ≤ 2` for `N = ⌊x⌋ ≥ 1`, `1/2 < β < 1`. -/
lemma norm_excZero_sub_floor_le (χ : DirichletCharacter ℂ q) {x : ℝ} (hx : 1 ≤ x) :
    ‖excZero χ x - excZero χ (⌊x⌋₊ : ℕ)‖ ≤ 2 := by
  by_cases hex : ∃ β : ℝ, IsExceptional χ β
  · obtain ⟨β, hβ⟩ := hex
    rw [excZero_eq hβ, excZero_eq hβ, perronKernel, perronKernel, ← sub_div,
      ← Complex.ofReal_cpow (by linarith), ← Complex.ofReal_cpow (Nat.cast_nonneg _),
      ← Complex.ofReal_sub, ← Complex.ofReal_div, Complex.norm_real, Real.norm_eq_abs]
    have hb1 := hβ.lt_one
    have hb2 := hβ.half_lt
    set N := ⌊x⌋₊
    have hN : (N : ℝ) ≤ x := Nat.floor_le (by linarith)
    have hN1 : x < N + 1 := Nat.lt_floor_add_one x
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
    have h1 : (N : ℝ) ^ β ≤ x ^ β := Real.rpow_le_rpow hN0 hN (by linarith)
    have h2 : x ^ β ≤ (N : ℝ) ^ β + 1 := by
      calc x ^ β = ((N : ℝ) + (x - N)) ^ β := by ring_nf
        _ ≤ (N : ℝ) ^ β + (x - N) ^ β :=
            Real.rpow_add_le_add_rpow hN0 (by linarith) (by linarith) hb1.le
        _ ≤ (N : ℝ) ^ β + 1 := by
            gcongr
            exact Real.rpow_le_one (by linarith) (by linarith) (by linarith)
    rw [abs_div, abs_of_pos (by linarith : (0 : ℝ) < β), div_le_iff₀ (by linarith),
      abs_of_nonneg (by linarith)]
    linarith
  · push Not at hex
    rw [excZero_eq_zero hex, excZero_eq_zero hex, sub_zero, norm_zero]; norm_num

set_option maxHeartbeats 1000000 in
/-- Row 20-5 with the exceptional term of every character, for real `x ≥ 3`. -/
theorem Davenport.psiAP_sub_excZero_le_real (C : ℝ) (hC : 0 < C) :
    ∃ c A : ℝ, 0 < c ∧ 0 < A ∧ ∀ {q : ℕ} [NeZero q] {a : ZMod q}, IsUnit a →
      ∀ x : ℝ, 3 ≤ x → Real.log q ≤ C * √(Real.log x) →
      ‖(psiAP a x : ℂ) - x / q.totient +
          (q.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q, χ a⁻¹ * excZero χ x‖ ≤
        A * x * Real.exp (-(c * √(Real.log x))) := by
  obtain ⟨c₀, A₀, hc₀, hA₀, h₀⟩ := Davenport.psiAP_sub_excZero_le (2 * C) (by positivity)
  set c := min (c₀ / 2) (1 / 2) with hcdef
  have hc0 : 0 < c := lt_min (by positivity) one_half_pos
  refine ⟨c, A₀ + 3, hc0, by positivity, ?_⟩
  intro q _ a ha x hx hqx
  set N := ⌊x⌋₊ with hNdef
  have hx0 : 0 < x := by linarith
  have hN3 : 3 ≤ N := Nat.le_floor (by exact_mod_cast hx)
  have hN : (N : ℝ) ≤ x := Nat.floor_le hx0.le
  have hN1 : x < N + 1 := Nat.lt_floor_add_one x
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN3' : (3 : ℝ) ≤ N := by exact_mod_cast hN3
  -- `log N ≥ log x / 4`
  have hxN : x ≤ 2 * N := by linarith
  have hlogN : Real.log x / 4 ≤ Real.log N := by
    have h1 : Real.log x ≤ Real.log 2 + Real.log N := by
      rw [← Real.log_mul (by norm_num) hN0.ne']; exact Real.log_le_log hx0 hxN
    have h2 : Real.log 3 ≤ Real.log N := Real.log_le_log (by norm_num) hN3'
    have h3 := Real.log_two_lt_d9
    have h4 := Real.log_three_gt_d9
    linarith
  have hsN : √(Real.log x) / 2 ≤ √(Real.log N) := by
    have : √(Real.log x / 4) ≤ √(Real.log N) := Real.sqrt_le_sqrt hlogN
    rwa [Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 4), show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)] at this
  have hqN : Real.log q ≤ 2 * C * √(Real.log N) := by nlinarith
  have hpsi : psiAP a x = psiAP a N := by simp [psiAP, hNdef]
  have e := h₀ ha N hN3 hqN
  have hsx : 0 ≤ √(Real.log x) := Real.sqrt_nonneg _
  have hE : A₀ * N * Real.exp (-(c₀ * √(Real.log N))) ≤
      A₀ * x * Real.exp (-(c * √(Real.log x))) := by
    have h1 : c * √(Real.log x) ≤ c₀ / 2 * √(Real.log x) := by
      gcongr; exact min_le_left _ _
    have h2 := mul_le_mul_of_nonneg_left hsN hc₀.le
    have hexp : Real.exp (-(c₀ * √(Real.log N))) ≤ Real.exp (-(c * √(Real.log x))) :=
      Real.exp_le_exp.mpr (by linarith)
    exact mul_le_mul (mul_le_mul_of_nonneg_left hN hA₀.le) hexp (Real.exp_pos _).le
      (by positivity)
  have hone := one_le_mul_exp_neg_sqrt_log hc0 (min_le_right _ _) (by linarith : (2 : ℝ) ≤ x)
  -- the differences
  have hφ : (1 : ℝ) ≤ q.totient := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
  have hcard : (Finset.univ : Finset (DirichletCharacter ℂ q)).card = q.totient := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card,
      DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity]
  have hd1 : ‖((x : ℂ) - N) / q.totient‖ ≤ 1 := by
    rw [norm_div, Complex.norm_natCast, ← Complex.ofReal_natCast, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith), div_le_one (by linarith)]
    linarith
  have hd2 : ‖(q.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q,
      χ a⁻¹ * (excZero χ x - excZero χ N)‖ ≤ 2 := by
    rw [norm_mul, norm_inv, Complex.norm_natCast]
    have : ‖∑ χ : DirichletCharacter ℂ q, χ a⁻¹ * (excZero χ x - excZero χ N)‖ ≤
        q.totient * 2 := by
      refine (norm_sum_le _ _).trans ?_
      calc ∑ χ : DirichletCharacter ℂ q, ‖χ a⁻¹ * (excZero χ x - excZero χ N)‖
          ≤ ∑ χ : DirichletCharacter ℂ q, (2 : ℝ) := by
            refine Finset.sum_le_sum fun χ _ ↦ ?_
            rw [norm_mul]
            have := DirichletCharacter.norm_le_one χ a⁻¹
            calc ‖χ a⁻¹‖ * ‖excZero χ x - excZero χ N‖ ≤ 1 * 2 :=
                  mul_le_mul this (norm_excZero_sub_floor_le χ (by linarith))
                    (norm_nonneg _) zero_le_one
              _ = 2 := one_mul 2
        _ = q.totient * 2 := by rw [Finset.sum_const, hcard, nsmul_eq_mul]
    calc (q.totient : ℝ)⁻¹ * ‖∑ χ : DirichletCharacter ℂ q, χ a⁻¹ * (excZero χ x - excZero χ N)‖
        ≤ (q.totient : ℝ)⁻¹ * (q.totient * 2) := by gcongr
      _ = 2 := by field_simp
  have hsplit : (psiAP a x : ℂ) - x / q.totient +
      (q.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q, χ a⁻¹ * excZero χ x =
      ((psiAP a N : ℂ) - N / q.totient +
        (q.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q, χ a⁻¹ * excZero χ N) -
      ((x : ℂ) - N) / q.totient +
      (q.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q, χ a⁻¹ * (excZero χ x - excZero χ N) := by
    rw [hpsi]; simp only [mul_sub, Finset.sum_sub_distrib]; ring
  rw [hsplit]
  calc _ ≤ ‖(psiAP a N : ℂ) - N / q.totient +
          (q.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q, χ a⁻¹ * excZero χ N‖ +
        ‖((x : ℂ) - N) / q.totient‖ + ‖(q.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q,
          χ a⁻¹ * (excZero χ x - excZero χ N)‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ A₀ * x * Real.exp (-(c * √(Real.log x))) + 1 + 2 := by linarith
    _ ≤ (A₀ + 3) * x * Real.exp (-(c * √(Real.log x))) := by nlinarith

set_option maxHeartbeats 1000000 in
/-- **Davenport, Ch. 20, p. 123, (9) (row 20-5), as stated, for real `x ≥ 3`; Ch. 22, p. 143, (E)
(row 22-4).** For every `C > 0` there are `c, A > 0` such that for every `q`, every `a` prime to
`q` and every real `x ≥ 3` with `q ≤ exp(C √log x)`:
* if no real nonprincipal character modulo `q` has an exceptional zero (`IsExceptional`), then
  `|ψ(x; q, a) - x/φ(q)| ≤ A x exp(-c √log x)`;
* if `χ₁` has the exceptional zero `β₁` (at most one such pair, `Davenport.isExceptional_unique`),
  then `|ψ(x; q, a) - x/φ(q) + χ₁(a) x^{β₁}/(φ(q) β₁)| ≤ A x exp(-c √log x)`. -/
@[kb "davenport1980" "Ch 20, p. 123"]
theorem Davenport.psiAP_exceptional_real (C : ℝ) (hC : 0 < C) :
    ∃ c A : ℝ, 0 < c ∧ 0 < A ∧ ∀ {q : ℕ} [NeZero q] {a : ZMod q}, IsUnit a →
      ∀ x : ℝ, 3 ≤ x → Real.log q ≤ C * √(Real.log x) →
      ((∀ (χ : DirichletCharacter ℂ q) (β : ℝ), ¬ IsExceptional χ β) →
        |psiAP a x - x / q.totient| ≤ A * x * Real.exp (-(c * √(Real.log x)))) ∧
      (∀ (χ₁ : DirichletCharacter ℂ q) (β₁ : ℝ), IsExceptional χ₁ β₁ →
        ‖(psiAP a x : ℂ) - x / q.totient + χ₁ a * (x : ℂ) ^ (β₁ : ℂ) / (q.totient * β₁)‖ ≤
          A * x * Real.exp (-(c * √(Real.log x)))) := by
  obtain ⟨c, A, hc, hA, h⟩ := Davenport.psiAP_sub_excZero_le_real C hC
  refine ⟨c, A, hc, hA, fun {q} _ {a} ha x hx hqx ↦ ⟨fun hno ↦ ?_, fun χ₁ β₁ h₁ ↦ ?_⟩⟩
  · have e := h ha x hx hqx
    rw [(sum_excZero_eq ha x).1 hno, mul_zero, add_zero] at e
    have : (psiAP a x : ℂ) - x / q.totient = ((psiAP a x - x / q.totient : ℝ) : ℂ) := by
      push_cast; ring
    rwa [this, Complex.norm_real, Real.norm_eq_abs] at e
  · have e := h ha x hx hqx
    rw [(sum_excZero_eq ha x).2 χ₁ β₁ h₁, perronKernel] at e
    have : (q.totient : ℂ)⁻¹ * (χ₁ a * (x : ℂ) ^ (β₁ : ℂ) / (β₁ : ℂ)) =
        χ₁ a * (x : ℂ) ^ (β₁ : ℂ) / (q.totient * β₁) := by
      field_simp
    rwa [mul_div_assoc', this] at e

set_option maxHeartbeats 1000000 in
/-- **Davenport, Ch. 20, p. 123, (8) (row 20-4), as stated, for real `x ≥ 3`**: for every `C > 0`
there are `c, A > 0` such that for every nonprincipal character `χ` modulo `q` and every real
`x ≥ 3` with `log q ≤ C √log x`, `|ψ(x, χ) + x^{β₁}/β₁| ≤ A x exp(-c √log x)`, the term `x^{β₁}/β₁`
present only if `L(s, χ)` has an exceptional zero `β₁` (`excZero`). -/
@[kb "davenport1980" "Ch 20, p. 123"]
theorem Davenport.psiL_add_excZero_le_real (C : ℝ) (hC : 0 < C) :
    ∃ c A : ℝ, 0 < c ∧ 0 < A ∧ ∀ {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}, χ ≠ 1 →
      ∀ x : ℝ, 3 ≤ x → Real.log q ≤ C * √(Real.log x) →
      ‖psiL χ x + excZero χ x‖ ≤ A * x * Real.exp (-(c * √(Real.log x))) := by
  obtain ⟨c₀, A₀, hc₀, hA₀, h₀⟩ := Davenport.psiL_add_excZero_le (2 * C) (by positivity)
  set c := min (c₀ / 2) (1 / 2) with hcdef
  have hc0 : 0 < c := lt_min (by positivity) one_half_pos
  refine ⟨c, A₀ + 2, hc0, by positivity, ?_⟩
  intro q _ χ hχ x hx hqx
  set N := ⌊x⌋₊ with hNdef
  have hx0 : 0 < x := by linarith
  have hN3 : 3 ≤ N := Nat.le_floor (by exact_mod_cast hx)
  have hN : (N : ℝ) ≤ x := Nat.floor_le hx0.le
  have hN1 : x < N + 1 := Nat.lt_floor_add_one x
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN3' : (3 : ℝ) ≤ N := by exact_mod_cast hN3
  have hxN : x ≤ 2 * N := by linarith
  have hlogN : Real.log x / 4 ≤ Real.log N := by
    have h1 : Real.log x ≤ Real.log 2 + Real.log N := by
      rw [← Real.log_mul (by norm_num) hN0.ne']; exact Real.log_le_log hx0 hxN
    have h2 : Real.log 3 ≤ Real.log N := Real.log_le_log (by norm_num) hN3'
    have h3 := Real.log_two_lt_d9
    have h4 := Real.log_three_gt_d9
    linarith
  have hsN : √(Real.log x) / 2 ≤ √(Real.log N) := by
    have : √(Real.log x / 4) ≤ √(Real.log N) := Real.sqrt_le_sqrt hlogN
    rwa [Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 4), show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)] at this
  have hqN : Real.log q ≤ 2 * C * √(Real.log N) := by nlinarith
  have hpsi : psiL χ x = psiL χ N := by simp [psiL, hNdef]
  have e := h₀ hχ N hN3 hqN
  have hsx : 0 ≤ √(Real.log x) := Real.sqrt_nonneg _
  have hE : A₀ * N * Real.exp (-(c₀ * √(Real.log N))) ≤
      A₀ * x * Real.exp (-(c * √(Real.log x))) := by
    have h1 : c * √(Real.log x) ≤ c₀ / 2 * √(Real.log x) := by
      gcongr; exact min_le_left _ _
    have h2 := mul_le_mul_of_nonneg_left hsN hc₀.le
    have hexp : Real.exp (-(c₀ * √(Real.log N))) ≤ Real.exp (-(c * √(Real.log x))) :=
      Real.exp_le_exp.mpr (by linarith)
    exact mul_le_mul (mul_le_mul_of_nonneg_left hN hA₀.le) hexp (Real.exp_pos _).le
      (by positivity)
  have hone := one_le_mul_exp_neg_sqrt_log hc0 (min_le_right _ _) (by linarith : (2 : ℝ) ≤ x)
  have hd := norm_excZero_sub_floor_le χ (by linarith : (1 : ℝ) ≤ x)
  rw [← hNdef] at hd
  have hsplit : psiL χ x + excZero χ x = (psiL χ N + excZero χ N) +
      (excZero χ x - excZero χ N) := by rw [hpsi]; ring
  rw [hsplit]
  calc _ ≤ ‖psiL χ N + excZero χ N‖ + ‖excZero χ x - excZero χ N‖ := norm_add_le _ _
    _ ≤ A₀ * x * Real.exp (-(c * √(Real.log x))) + 2 := by linarith
    _ ≤ (A₀ + 2) * x * Real.exp (-(c * √(Real.log x))) := by nlinarith

end NTKB
