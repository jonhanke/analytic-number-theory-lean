/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Davenport.Zeros.LZeroFreeComplex

/-!
# Zero-free regions for `L(s, χ)`, `χ` real; the exceptional zero

**Davenport, Ch. 14, pp. 90-92.** For a real nonprincipal character `χ` mod `q`
(`χ² = χ₀`), with `𝔏 = log q + log(|γ| + 2)`:

* (row 14-9) if `0 < δ ≤ 2/245`, every zero `β + iγ` with `|γ| ≥ δ/𝔏` (in particular with
  `|γ| ≥ δ/log q`) has `β ≤ 1 - δ/(9 𝔏)`;
* (row 14-10) if `0 < δ ≤ 1/600`, there is at most one zero (counted with multiplicity) with
  `|γ| < δ/log q` and `β > 1 - δ/log q`; if it exists it is real and simple.
-/

open Filter Topology Complex Set DirichletCharacter LSeries
open scoped Real LSeries.notation ArithmeticFunction.vonMangoldt ComplexConjugate

namespace NTKB

variable {N : ℕ} [NeZero N]

/-- **Crude lower bound** (Davenport, Ch. 14, p. 92): for real `σ > 1`,
`-Re 𝔏'/𝔏(σ, χ) ≥ ζ'/ζ(σ)`, i.e. `Re 𝔏'/𝔏(σ, χ) ≤ -ζ'/ζ(σ)`. -/
lemma re_logDeriv_LFunction_le_neg_zeta (χ : DirichletCharacter ℂ N) {σ : ℝ} (hσ : 1 < σ) :
    (deriv (LFunction χ) σ / LFunction χ σ).re ≤ -(deriv riemannZeta σ / riemannZeta σ).re := by
  have h1 : 1 < (σ : ℂ).re := by simpa using hσ
  have hχ := neg_logDeriv_LFunction_eq_LSeries χ h1
  have hζ := neg_logDeriv_LFunction_eq_LSeries (1 : DirichletCharacter ℂ 1) h1
  rw [LFunction_modOne_eq] at hζ
  have sχ := (DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ h1).LSeriesHasSum
  have sζ := (DirichletCharacter.LSeriesSummable_twist_vonMangoldt
    (1 : DirichletCharacter ℂ 1) h1).LSeriesHasSum
  have hχ' := Complex.reCLM.hasSum sχ
  have hζ' := Complex.reCLM.hasSum sζ
  have hle : ∀ n, -(term (↗(1 : DirichletCharacter ℂ 1) * ↗Λ) (σ : ℂ) n).re ≤
      (term (↗χ * ↗Λ) (σ : ℂ) n).re := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    have e1 := term_twist_vonMangoldt_eq χ σ 0 hn
    have e2 := term_twist_vonMangoldt_eq (1 : DirichletCharacter ℂ 1) σ 0 hn
    simp only [Complex.ofReal_zero, zero_mul, add_zero, neg_zero, Complex.exp_zero,
      mul_one] at e1 e2
    rw [e1, e2, MulChar.one_apply (isUnit_of_subsingleton _)]
    set c : ℝ := Λ n * (n : ℝ) ^ (-σ)
    have hc : 0 ≤ c := mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
      (Real.rpow_nonneg n.cast_nonneg _)
    have hre : -1 ≤ (χ n).re := by
      have := Complex.abs_re_le_norm (χ n)
      have := χ.norm_le_one n
      linarith [neg_abs_le (χ n).re]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
      one_re]
    nlinarith
  have := hasSum_le (fun n ↦ by simpa using hle n) hζ'.neg hχ'
  simp only [Complex.reCLM_apply] at this
  rw [← hχ, ← hζ] at this
  rw [neg_div, Complex.neg_re, neg_div, Complex.neg_re] at this
  linarith

/-- `Re 1/(d + 2iγ) ≤ 1/(5d)` when `0 < d ≤ |γ|`. -/
lemma re_one_div_le_of_le_abs {d γ : ℝ} (hd : 0 < d) (hγ : d ≤ |γ|) :
    (1 / ((d : ℂ) + (2 * γ : ℝ) * I)).re ≤ 1 / (5 * d) := by
  rw [one_div, Complex.inv_re, Complex.normSq_apply]
  simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
    add_zero, add_im, mul_im, zero_add]
  have hγ2 : d ^ 2 ≤ γ ^ 2 := by
    rw [← sq_abs γ]; exact pow_le_pow_left₀ hd.le hγ 2
  rw [div_le_div_iff₀ (by nlinarith) (by positivity)]
  nlinarith

/-- **Davenport, Ch. 14, p. 91 (row 14-9)**, primitive case: for a real primitive character
`χ ≠ χ₀` mod `q` and `0 < δ ≤ 2/245`, every zero `β + iγ` of `L(s, χ)` with
`|γ| ≥ δ/𝔏`, `𝔏 = log q + log(|γ| + 2)`, satisfies `β ≤ 1 - δ/(9 𝔏)`. -/
@[kb "davenport1980" "Ch 14, p. 91"]
theorem Davenport.LFunction_zero_free_real_primitive {χ : DirichletCharacter ℂ N}
    (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1) (hreal : χ ^ 2 = 1) {κ : ℝ} (hκ : 0 < κ)
    (hκ' : κ ≤ 2 / 245) {s : ℂ} (hs : LFunction χ s = 0)
    (hγ : κ / (Real.log N + Real.log (|s.im| + 2)) ≤ |s.im|) :
    s.re ≤ 1 - κ / (9 * (Real.log N + Real.log (|s.im| + 2))) := by
  have hN : N ≠ 1 := by
    rintro rfl
    exact hχ1 (Subsingleton.elim _ _)
  have hN2 : (2 : ℝ) ≤ N := by
    have := NeZero.ne N
    exact_mod_cast (show 2 ≤ N by omega)
  have hl2 := log_two_gt_two_thirds
  obtain ⟨Lq, hLdef⟩ : ∃ Lq, Lq = Real.log N + Real.log (|s.im| + 2) := ⟨_, rfl⟩
  rw [← hLdef] at hγ ⊢
  have hlN : Real.log 2 ≤ Real.log N := Real.log_le_log two_pos hN2
  have hlT : Real.log 2 ≤ Real.log (|s.im| + 2) :=
    Real.log_le_log two_pos (by linarith [abs_nonneg s.im])
  have hL : 4 / 3 < Lq := by linarith
  have hL0 : 0 < Lq := by linarith
  rcases le_or_gt s.re 0 with h0 | h0
  · have : κ / (9 * Lq) ≤ 1 := by rw [div_le_one (by positivity)]; nlinarith
    linarith
  obtain ⟨ρ, rfl⟩ := exists_zeroIndex_dirichletXi hχ hN hs h0
  have hβ := dirichletXi_zero_mem hχ hN ρ
  obtain ⟨d, hd⟩ : ∃ d : ℝ, d = κ / Lq := ⟨_, rfl⟩
  rw [← hd] at hγ
  have hd0 : 0 < d := by rw [hd]; positivity
  have hdL : d * Lq = κ := by rw [hd]; field_simp
  have hd1 : d ≤ 1 := by rw [hd, div_le_one hL0]; linarith
  set σ : ℝ := 1 + d with hσ
  have hσ1 : 1 < σ := by linarith
  have hσ2 : σ ≤ 2 := by linarith
  -- the three estimates
  have e1 := neg_logDeriv_one_real_le (N := N) hσ1 hσ2
  have e2 := neg_re_logDeriv_LFunction_le_zero hχ hN ρ hσ1 hσ2
  have e3 := neg_re_logDeriv_one_le (N := N) (s := σ + (2 * ρ.val.im : ℝ) * I)
    (by simpa using hσ1)
  have e3' := Davenport.neg_re_logDeriv_riemannZeta_le_log (s := σ + (2 * ρ.val.im : ℝ) * I)
    (by simpa using hσ1) (by simpa using hσ2)
  have key := Davenport.three_four_one_LFunction χ hσ1 ρ.val.im
  rw [hreal] at key
  simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero, zero_add,
    add_zero] at e3'
  have hpole : (1 / ((σ : ℂ) + (2 * ρ.val.im : ℝ) * I - 1)).re ≤ 1 / (5 * d) := by
    have : (σ : ℂ) + (2 * ρ.val.im : ℝ) * I - 1 = (d : ℂ) + (2 * ρ.val.im : ℝ) * I := by
      rw [hσ]; push_cast; ring
    rw [this]; exact re_one_div_le_of_le_abs hd0 hγ
  have hlog2T : Real.log (|2 * ρ.val.im| + 2) ≤ 2 * Real.log (|ρ.val.im| + 2) := by
    rw [show (2 : ℝ) * Real.log (|ρ.val.im| + 2) = ((2 : ℕ) : ℝ) * Real.log (|ρ.val.im| + 2) by
      norm_num, ← Real.log_pow, abs_mul, abs_two]
    have := abs_nonneg ρ.val.im
    exact Real.log_le_log (by linarith) (by nlinarith)
  have hσm1 : 1 / (σ - 1) = 1 / d := by rw [hσ]; ring_nf
  have hu : 0 < σ - ρ.val.re := by linarith [hβ.2.2]
  have hneg : ∀ (ψ : DirichletCharacter ℂ N) (z : ℂ), (-deriv (LFunction ψ) z / LFunction ψ z).re =
      -(deriv (LFunction ψ) z / LFunction ψ z).re := fun ψ z ↦ by rw [neg_div, Complex.neg_re]
  rw [hneg, hneg, hneg] at key
  rw [hσm1] at e1
  -- `4/(σ - β) ≤ 3/d + 1/(5d) + 49 Lq`
  have hcomb : 4 * (1 / (σ - ρ.val.re)) ≤ 3 * (1 / d) + 1 / (5 * d) + 49 * Lq := by
    rw [← hLdef] at e2
    nlinarith
  -- multiply out by `d (σ - β)`
  have h5 : (1 / (5 * d)) * d = 1 / 5 := by field_simp
  have h3 : (1 / d) * d = 1 := by field_simp
  have h4 : (1 / (σ - ρ.val.re)) * (σ - ρ.val.re) = 1 := by field_simp
  have hmul : 4 * d ≤ (σ - ρ.val.re) * (16 / 5 + 49 * κ) := by
    have := mul_le_mul_of_nonneg_right hcomb (by positivity : 0 ≤ d * (σ - ρ.val.re))
    rw [← hdL]
    nlinarith
  have hfin : 10 * d / 9 ≤ σ - ρ.val.re := by nlinarith
  rw [show κ / (9 * Lq) = d / 9 by rw [hd]; field_simp]
  linarith

/-- `Re 1/z ≥ 4/(5 Re z)` when `Re z > 0` and `|Im z| ≤ Re z / 2`. -/
lemma re_one_div_ge {z : ℂ} (h0 : 0 < z.re) (him : |z.im| ≤ z.re / 2) :
    4 / (5 * z.re) ≤ (1 / z).re := by
  have hz : z ≠ 0 := fun h ↦ by rw [h] at h0; simp at h0
  rw [one_div, Complex.inv_re, Complex.normSq_apply,
    div_le_div_iff₀ (by positivity) (by nlinarith)]
  have : z.im * z.im ≤ z.re * z.re / 4 := by
    have h2 : |z.im| * |z.im| ≤ (z.re / 2) * (z.re / 2) :=
      mul_le_mul him him (abs_nonneg _) (by linarith)
    rw [abs_mul_abs_self] at h2
    linarith
  nlinarith

/-- Hypothesis of the exceptional-zero lemma: `|γ| < δ/log q` and `β > 1 - δ/log q`. -/
def IsNearOne (κ : ℝ) (N : ℕ) (ρ : ℂ) : Prop :=
  |ρ.im| < κ / Real.log N ∧ 1 - κ / Real.log N < ρ.re

/-- **Davenport, Ch. 14, p. 92 (row 14-10)**, uniqueness: for a real primitive character
`χ ≠ χ₀` mod `q` and `0 < δ ≤ 1/600`, there is at most one zero of `ξ(s, χ)` (counted with
multiplicity) with `|γ| < δ/log q` and `β > 1 - δ/log q`. -/
@[kb "davenport1980" "Ch 14, p. 92"]
theorem Davenport.LFunction_exceptional_zero_unique {χ : DirichletCharacter ℂ N}
    (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1) {κ : ℝ} (hκ : 0 < κ) (hκ' : κ ≤ 1 / 600)
    (ρ₁ ρ₂ : ZeroIndex (dirichletXi χ)) (h₁ : IsNearOne κ N ρ₁.val)
    (h₂ : IsNearOne κ N ρ₂.val) : ρ₁ = ρ₂ := by
  by_contra hne
  have hN : N ≠ 1 := by
    rintro rfl
    exact hχ1 (Subsingleton.elim _ _)
  have hN2 : (2 : ℝ) ≤ N := by
    have := NeZero.ne N
    exact_mod_cast (show 2 ≤ N by omega)
  have hl2 := log_two_gt_two_thirds
  obtain ⟨Lq, hLdef⟩ : ∃ Lq, Lq = Real.log N := ⟨_, rfl⟩
  have hlN : Real.log 2 ≤ Lq := hLdef ▸ Real.log_le_log two_pos hN2
  have hL0 : 0 < Lq := by linarith
  unfold IsNearOne at h₁ h₂
  rw [← hLdef] at h₁ h₂
  obtain ⟨d, hd⟩ : ∃ d : ℝ, d = κ / Lq := ⟨_, rfl⟩
  rw [← hd] at h₁ h₂
  have hd0 : 0 < d := by rw [hd]; positivity
  have hdL : d * Lq = κ := by rw [hd]; field_simp
  have hd1 : d ≤ 1 / 300 := by
    rw [hd, div_le_iff₀ hL0]; nlinarith
  set σ : ℝ := 1 + 2 * d with hσ
  have hσ1 : 1 < σ := by linarith
  have hσ2 : σ ≤ 2 := by linarith
  -- upper bound from (B), keeping the two terms
  have hb := Davenport.neg_re_logDeriv_LFunction_le hχ hN (s := σ) (by simpa using hσ1)
    (by simpa using hσ2)
  simp only [Complex.ofReal_im, abs_zero, zero_add] at hb
  have hterm : ∀ ρ : ZeroIndex (dirichletXi χ), |ρ.val.im| < d → 1 - d < ρ.val.re →
      4 / (5 * (3 * d)) ≤ (1 / ((σ : ℂ) - ρ.val)).re := by
    intro ρ hγ hβ
    have hβ1 := (dirichletXi_zero_mem hχ hN ρ).2.2
    have hre : ((σ : ℂ) - ρ.val).re = σ - ρ.val.re := by simp
    have him : |((σ : ℂ) - ρ.val).im| = |ρ.val.im| := by simp
    have h := re_one_div_ge (z := (σ : ℂ) - ρ.val) (by rw [hre]; linarith)
      (by rw [him, hre]; linarith)
    rw [hre] at h
    refine le_trans ?_ h
    exact div_le_div_of_nonneg_left (by norm_num) (by nlinarith) (by nlinarith)
  have hsum := summable_re_inv_sub_dirichletXi_zeros hχ hN (s := σ) fun ρ' h ↦ by
    have := congrArg Complex.re h
    simp at this
    linarith [(dirichletXi_zero_mem hχ hN ρ').2.2]
  have hpair : (1 / ((σ : ℂ) - ρ₁.val)).re + (1 / ((σ : ℂ) - ρ₂.val)).re ≤
      ∑' ρ : ZeroIndex (dirichletXi χ), (1 / ((σ : ℂ) - ρ.val)).re := by
    have := hsum.sum_le_tsum {ρ₁, ρ₂} fun ρ _ ↦
      (re_one_div_sub_pos (by simp; linarith [(dirichletXi_zero_mem hχ hN ρ).2.2])).le
    rwa [Finset.sum_pair hne] at this
  have t1 := hterm ρ₁ h₁.1 h₁.2
  have t2 := hterm ρ₂ h₂.1 h₂.2
  -- the crude lower bound
  have hlow := re_logDeriv_LFunction_le_neg_zeta χ hσ1
  have hz := Davenport.neg_logDeriv_riemannZeta_real_le hσ1 hσ2
  have hσm1 : 1 / (σ - 1) = 1 / (2 * d) := by rw [hσ]; ring_nf
  rw [hσm1] at hz
  rw [← hLdef] at hb
  -- `-(1/(2d) + 5 log 2) ≤ 6 (Lq + log 2) - 8/(15 d)`
  have h8 : 4 / (5 * (3 * d)) = (4 / 15) * (1 / d) := by field_simp; ring
  have h2d : 1 / (2 * d) = (1 / 2) * (1 / d) := by field_simp
  rw [h8] at t1 t2
  rw [h2d] at hz
  have hineq : (1 / 30) * (1 / d) ≤ 17 * Lq := by nlinarith
  have : (1 / 30) * (1 / d) * d = 1 / 30 := by field_simp
  have hfin : 1 / 30 ≤ 17 * κ := by
    rw [← hdL]; nlinarith
  linarith

/-- **Davenport, Ch. 14, p. 92 (row 14-10)**: the exceptional zero, if it exists, is real and
simple (as a zero of `ξ(s, χ)`, equivalently of `L(s, χ)` in the critical strip). -/
@[kb "davenport1980" "Ch 14, p. 92"]
theorem Davenport.LFunction_exceptional_zero_real_simple {χ : DirichletCharacter ℂ N}
    (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1) (hreal : χ ^ 2 = 1) {κ : ℝ} (hκ : 0 < κ)
    (hκ' : κ ≤ 1 / 600) (ρ : ZeroIndex (dirichletXi χ)) (hρ : IsNearOne κ N ρ.val) :
    ρ.val.im = 0 ∧ analyticOrderNatAt (dirichletXi χ) ρ.val = 1 := by
  have hN : N ≠ 1 := by
    rintro rfl
    exact hχ1 (Subsingleton.elim _ _)
  have hinv : χ⁻¹ = χ := inv_eq_of_mul_eq_one_left (by rw [← sq, hreal])
  have hord : ∀ z, analyticOrderNatAt (dirichletXi χ) (conj z) =
      analyticOrderNatAt (dirichletXi χ) z := by
    intro z
    have := analyticOrderNatAt_dirichletXi_conj hχ hN z
    rwa [hinv] at this
  constructor
  · -- the conjugate zero
    let ρ' : ZeroIndex (dirichletXi χ) := ⟨conj ρ.val, Fin.cast (hord ρ.val).symm ρ.2⟩
    have hρ' : IsNearOne κ N ρ'.val := by
      simp only [IsNearOne, ZeroIndex.val, ρ'] at hρ ⊢
      simpa using hρ
    have := Davenport.LFunction_exceptional_zero_unique hχ hχ1 hκ hκ' ρ ρ' hρ hρ'
    have hv : ρ.val = conj ρ.val := congrArg ZeroIndex.val this
    have := congrArg Complex.im hv
    simp at this
    linarith
  · have hpos := ZeroIndex.analyticOrderNatAt_val_pos ρ
    by_contra h1
    have h2 : 1 < analyticOrderNatAt (dirichletXi χ) ρ.val := by omega
    let a : ZeroIndex (dirichletXi χ) := ⟨ρ.val, ⟨0, hpos⟩⟩
    let b : ZeroIndex (dirichletXi χ) := ⟨ρ.val, ⟨1, h2⟩⟩
    have hab := Davenport.LFunction_exceptional_zero_unique hχ hχ1 hκ hκ' a b hρ hρ
    have : (⟨0, hpos⟩ : Fin _) = ⟨1, h2⟩ := eq_of_heq (Sigma.mk.inj hab).2
    simp at this

lemma primitiveCharacter_sq_eq_one {χ : DirichletCharacter ℂ N} (hreal : χ ^ 2 = 1) :
    have : NeZero χ.conductor := ⟨conductor_ne_zero χ⟩
    χ.primitiveCharacter ^ 2 = 1 := by
  have : NeZero χ.conductor := ⟨conductor_ne_zero χ⟩
  rw [← changeLevel_eq_one_iff (conductor_dvd_level χ), map_pow, changeLevel_primitiveCharacter,
    hreal]

lemma primitiveCharacter_ne_one {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) :
    have : NeZero χ.conductor := ⟨conductor_ne_zero χ⟩
    χ.primitiveCharacter ≠ 1 := by
  intro _ h
  apply hχ
  rw [← changeLevel_primitiveCharacter χ, h, changeLevel_one]

lemma two_le_conductor {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) : (2 : ℝ) ≤ χ.conductor := by
  have h0 := conductor_ne_zero χ
  have h1 := conductor_ne_one_of_ne_one hχ
  exact_mod_cast (show 2 ≤ χ.conductor by omega)

lemma log_conductor_le (χ : DirichletCharacter ℂ N) :
    Real.log χ.conductor ≤ Real.log N :=
  Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero (conductor_ne_zero χ))
    (by exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne N)) (conductor_dvd_level χ))

/-- **Davenport, Ch. 14, p. 91 (row 14-9)**: for a real character `χ ≠ χ₀` mod `q` (primitive or
not) and `0 < δ ≤ 2/245`, every zero `β + iγ` of `L(s, χ)` with `|γ| ≥ δ/𝔏`,
`𝔏 = log q + log(|γ| + 2)`, satisfies `β ≤ 1 - δ/(9 𝔏)`. -/
@[kb "davenport1980" "Ch 14, p. 91"]
theorem Davenport.LFunction_zero_free_real {χ : DirichletCharacter ℂ N} (hχ1 : χ ≠ 1)
    (hreal : χ ^ 2 = 1) {κ : ℝ} (hκ : 0 < κ) (hκ' : κ ≤ 2 / 245) {s : ℂ}
    (hs : LFunction χ s = 0)
    (hγ : κ / (Real.log N + Real.log (|s.im| + 2)) ≤ |s.im|) :
    s.re ≤ 1 - κ / (9 * (Real.log N + Real.log (|s.im| + 2))) := by
  have hl2 := log_two_gt_two_thirds
  have hlT : Real.log 2 ≤ Real.log (|s.im| + 2) :=
    Real.log_le_log two_pos (by linarith [abs_nonneg s.im])
  have hlN : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  have hL : 0 < Real.log N + Real.log (|s.im| + 2) := by linarith
  rcases le_or_gt s.re 0 with h0 | h0
  · have : κ / (9 * (Real.log N + Real.log (|s.im| + 2))) ≤ 1 := by
      rw [div_le_one (by positivity)]; nlinarith
    linarith
  have : NeZero χ.conductor := ⟨conductor_ne_zero χ⟩
  have hz := LFunction_primitiveCharacter_eq_zero hχ1 hs h0
  have hM2 := two_le_conductor hχ1
  have hlM : Real.log 2 ≤ Real.log χ.conductor := Real.log_le_log two_pos hM2
  have hMN := log_conductor_le χ
  set L₁ := Real.log χ.conductor + Real.log (|s.im| + 2) with hL₁
  set Lq := Real.log N + Real.log (|s.im| + 2) with hLL
  have hL₁0 : 0 < L₁ := by linarith
  have hL₁L : L₁ ≤ Lq := by linarith
  -- apply the primitive case with `κ' = κ L₁ / Lq ≤ κ`
  have hκ'0 : 0 < κ * L₁ / Lq := by positivity
  have hκ'1 : κ * L₁ / Lq ≤ 2 / 245 := by
    rw [div_le_iff₀ hL]; nlinarith
  have hγ' : κ * L₁ / Lq / L₁ ≤ |s.im| := by
    rw [show κ * L₁ / Lq / L₁ = κ / Lq by field_simp]; exact hγ
  have h := Davenport.LFunction_zero_free_real_primitive (primitiveCharacter_isPrimitive χ)
    (primitiveCharacter_ne_one hχ1) (primitiveCharacter_sq_eq_one hreal) hκ'0 hκ'1 hz hγ'
  rw [show κ * L₁ / Lq / (9 * L₁) = κ / (9 * Lq) by field_simp] at h
  exact h

/-- Davenport's form of row 14-9: the hypothesis `|γ| ≥ δ/log q`. -/
theorem Davenport.LFunction_zero_free_real' {χ : DirichletCharacter ℂ N} (hχ1 : χ ≠ 1)
    (hreal : χ ^ 2 = 1) {κ : ℝ} (hκ : 0 < κ) (hκ' : κ ≤ 2 / 245) {s : ℂ}
    (hs : LFunction χ s = 0) (hγ : κ / Real.log N ≤ |s.im|) :
    s.re ≤ 1 - κ / (9 * (Real.log N + Real.log (|s.im| + 2))) := by
  refine Davenport.LFunction_zero_free_real hχ1 hreal hκ hκ' hs (le_trans ?_ hγ)
  have hN2 : (2 : ℝ) ≤ N := by
    have h0 := NeZero.ne N
    have h1 : N ≠ 1 := by rintro rfl; exact hχ1 (Subsingleton.elim _ _)
    exact_mod_cast (show 2 ≤ N by omega)
  have hl2 := log_two_gt_two_thirds
  have hlN : Real.log 2 ≤ Real.log N := Real.log_le_log two_pos hN2
  have hlT : 0 ≤ Real.log (|s.im| + 2) := Real.log_nonneg (by linarith [abs_nonneg s.im])
  exact div_le_div_of_nonneg_left hκ.le (by linarith) (by linarith)

end NTKB
