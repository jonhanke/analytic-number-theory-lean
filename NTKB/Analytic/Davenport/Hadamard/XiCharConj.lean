/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.NumberTheory.MulChar.Lemmas
import NTKB.Analytic.Davenport.Hadamard.XiChar

/-!
# Symmetries of the zeros of `L(s, χ)` and the real part of `B(χ)` (Davenport, Ch. 12, p. 83)

**Davenport, Ch. 12, (18).** `Re B(χ) = -∑_ρ Re(1/ρ)`, the sum over the zeros of `ξ(s, χ)`;
in particular `B(χ)` is real and negative for a real character.
**p. 83.** For complex `χ` the zeros of `L(s, χ)` are still symmetric about `σ = 1/2`
(`ρ ↦ 1 - ρ̄`), but not about the real axis.

## Main results

* `NTKB.dirichletXi_inv_conj`: `ξ(s̄, χ⁻¹) = conj ξ(s, χ)` (`χ⁻¹ = χ̄`), from the Dirichlet series
  on `σ > 1` and the identity theorem (the same argument as Tau Ceti's `LFunction_inv_conj`,
  reproved here for `ξ`).
* `NTKB.analyticOrderAt_conj_conj`: `conj ∘ f ∘ conj` vanishes at `z̄₀` to the order of `f` at `z₀`.
* `NTKB.Davenport.dirichletXi_zero_symm` (row 12-19) and
  `NTKB.Davenport.re_B_eq_neg_tsum` (row 12-18).
-/

open Complex Filter Topology DirichletCharacter
open scoped ComplexConjugate Real

namespace NTKB

variable {N : ℕ} [NeZero N]

/-- Conjugating the Dirichlet series: `L(s̄, χ⁻¹) = conj L(s, χ)` for `σ > 1`. -/
lemma LFunction_inv_conj_of_one_lt_re (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    LFunction χ⁻¹ (conj s) = conj (LFunction χ s) := by
  rw [LFunction_eq_LSeries _ (by simpa using hs), LFunction_eq_LSeries _ hs, LSeries, LSeries,
    Complex.conj_tsum]
  refine tsum_congr fun n ↦ ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, map_div₀,
    ← MulChar.star_apply' χ n]
  congr 1
  have harg : (n : ℂ).arg ≠ π := by
    rw [Complex.natCast_arg]; exact Real.pi_ne_zero.symm
  rw [Complex.cpow_conj _ _ harg, Complex.conj_natCast]

/-- `conj ∘ g ∘ conj` is analytic at `z̄` if `g` is analytic at `z`. -/
lemma analyticAt_conj_conj {g : ℂ → ℂ} {z : ℂ} (hg : AnalyticAt ℂ g z) :
    AnalyticAt ℂ (conj ∘ g ∘ conj) (conj z) := by
  rw [Complex.analyticAt_iff_eventually_differentiableAt] at hg ⊢
  have hc : Tendsto conj (𝓝 (conj z)) (𝓝 z) := by
    simpa using (Complex.continuous_conj.tendsto (conj z))
  filter_upwards [hc.eventually hg] with w hw
  simpa using hw.conj_conj

/-- `conj ∘ f ∘ conj` vanishes at `z̄₀` to the same (finite) order as `f` at `z₀`. -/
lemma analyticOrderAt_conj_conj {f : ℂ → ℂ} {z₀ : ℂ} (hf : AnalyticAt ℂ f z₀)
    (hfin : analyticOrderAt f z₀ ≠ ⊤) :
    analyticOrderAt (conj ∘ f ∘ conj) (conj z₀) = analyticOrderAt f z₀ := by
  obtain ⟨g, hg, hg0, hfg⟩ := hf.analyticOrderAt_ne_top.mp hfin
  rw [← ENat.natCast_toNat hfin, (analyticAt_conj_conj hf).analyticOrderAt_eq_natCast]
  refine ⟨conj ∘ g ∘ conj, analyticAt_conj_conj hg, by simpa using hg0, ?_⟩
  have hc : Tendsto conj (𝓝 (conj z₀)) (𝓝 z₀) := by
    simpa using (Complex.continuous_conj.tendsto (conj z₀))
  filter_upwards [hc.eventually hfg] with w hw
  simp only [Function.comp_apply, hw, smul_eq_mul, map_mul, map_pow, map_sub, conj_conj]
  rfl

omit [NeZero N] in
lemma conj_dirichletParity (χ : DirichletCharacter ℂ N) :
    conj (dirichletParity χ) = dirichletParity χ :=
  Complex.conj_eq_iff_im.mpr (dirichletParity_im χ)

omit [NeZero N] in
lemma conj_natCast_cpow (w : ℂ) : conj ((N : ℂ) ^ w) = (N : ℂ) ^ (conj w) := by
  have harg : (N : ℂ).arg ≠ π := by
    rw [Complex.natCast_arg]; exact Real.pi_ne_zero.symm
  rw [Complex.cpow_conj _ _ harg, Complex.conj_natCast]

/-- **Conjugation symmetry**: `ξ(s̄, χ⁻¹) = conj ξ(s, χ)` for `χ ≠ 1` mod `q > 1` (`χ⁻¹ = χ̄`). -/
theorem dirichletXi_inv_conj {χ : DirichletCharacter ℂ N} (hχ1 : χ ≠ 1) (hN : N ≠ 1) :
    dirichletXi χ⁻¹ = conj ∘ dirichletXi χ ∘ conj := by
  have hχ1' : χ⁻¹ ≠ 1 := fun h ↦ hχ1 (inv_eq_one.mp h)
  have hf : AnalyticOnNhd ℂ (dirichletXi χ⁻¹) Set.univ := fun z _ ↦
    (differentiable_dirichletXi hχ1').analyticAt z
  have hg : AnalyticOnNhd ℂ (conj ∘ dirichletXi χ ∘ conj) Set.univ := fun z _ ↦ by
    simpa using analyticAt_conj_conj ((differentiable_dirichletXi hχ1).analyticAt (conj z))
  refine AnalyticOnNhd.eq_of_eventuallyEq hf hg (z₀ := 2) ?_
  have hopen : {w : ℂ | 1 < w.re} ∈ 𝓝 (2 : ℂ) :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  filter_upwards [hopen] with w hw
  have ha0 := dirichletParity_re_nonneg χ
  have hG1 : Gammaℝ (w + dirichletParity χ⁻¹) ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by
    simp; linarith [dirichletParity_re_nonneg χ⁻¹])
  have hG2 : Gammaℝ (conj w + dirichletParity χ) ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by
    simp; linarith)
  simp only [Function.comp_apply]
  rw [dirichletXi_eq_mul_LFunction χ⁻¹ hN hG1, dirichletXi_eq_mul_LFunction χ hN hG2,
    dirichletParity_inv, map_mul, map_mul, conj_natCast_cpow, ← Gammaℝ_conj,
    ← LFunction_inv_conj_of_one_lt_re χ (s := conj w) (by simpa using hw)]
  simp only [map_add, map_div₀, conj_conj, conj_dirichletParity, map_ofNat]

/-- Orders of vanishing under `s ↦ s̄`, `χ ↦ χ⁻¹`. -/
lemma analyticOrderNatAt_dirichletXi_conj {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive)
    (hN : N ≠ 1) (z : ℂ) :
    analyticOrderNatAt (dirichletXi χ) (conj z) = analyticOrderNatAt (dirichletXi χ⁻¹) z := by
  have hχ1 := ne_one_of_isPrimitive hχ hN
  have hd := differentiable_dirichletXi hχ1
  have hfin : analyticOrderAt (dirichletXi χ) (conj z) ≠ ⊤ :=
    AnalyticOnNhd.analyticOrderAt_ne_top_of_isPreconnected (fun w _ ↦ hd.analyticAt w)
      isPreconnected_univ (Set.mem_univ 0) (Set.mem_univ _)
      (by rw [(hd.analyticAt 0).analyticOrderAt_eq_zero.mpr (dirichletXi_zero_ne_zero hχ hN)]
          simp)
  have := analyticOrderAt_conj_conj (hd.analyticAt (conj z)) hfin
  rw [conj_conj, ← dirichletXi_inv_conj hχ1 hN] at this
  simp only [analyticOrderNatAt, this]

/-- Orders of vanishing under `s ↦ 1 - s`, `χ ↦ χ⁻¹` (functional equation). -/
lemma analyticOrderNatAt_dirichletXi_one_sub {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive)
    (hN : N ≠ 1) (z : ℂ) :
    analyticOrderNatAt (dirichletXi χ) (1 - z) = analyticOrderNatAt (dirichletXi χ⁻¹) z := by
  have hχ1 := ne_one_of_isPrimitive hχ hN
  have hχ1' : χ⁻¹ ≠ 1 := fun h ↦ hχ1 (inv_eq_one.mp h)
  have hcomp : dirichletXi χ ∘ (fun w ↦ 1 - w) = fun w ↦ rootNumber χ * dirichletXi χ⁻¹ w :=
    funext fun w ↦ dirichletXi_one_sub hχ w
  have hg : AnalyticAt ℂ (fun w : ℂ ↦ 1 - w) z := analyticAt_const.sub analyticAt_id
  have hg' : deriv (fun w : ℂ ↦ 1 - w) z ≠ 0 := by rw [deriv_const_sub]; simp
  have h1 := analyticOrderAt_comp_of_deriv_ne_zero (f := dirichletXi χ) hg hg'
  rw [hcomp] at h1
  have hε : rootNumber χ ≠ 0 := by
    rw [← norm_ne_zero_iff, norm_rootNumber hχ]; norm_num
  have h2 : analyticOrderAt (fun w ↦ rootNumber χ * dirichletXi χ⁻¹ w) z =
      analyticOrderAt (dirichletXi χ⁻¹) z := by
    have := analyticOrderAt_mul (f := fun _ ↦ rootNumber χ) (g := dirichletXi χ⁻¹)
      (z₀ := z) analyticAt_const ((differentiable_dirichletXi hχ1').analyticAt z)
    rw [show (fun w ↦ rootNumber χ * dirichletXi χ⁻¹ w) =
      (fun _ ↦ rootNumber χ) * dirichletXi χ⁻¹ from rfl, this,
      (analyticAt_const).analyticOrderAt_eq_zero.mpr hε, zero_add]
  rw [h2] at h1
  simp only [analyticOrderNatAt, ← h1]

/-- The bijection `ρ' ↦ ρ̄'` from the zeros of `ξ(s, χ⁻¹)` to those of `ξ(s, χ)`. -/
noncomputable def dirichletXiZeroConj {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive)
    (hN : N ≠ 1) : ZeroIndex (dirichletXi χ⁻¹) ≃ ZeroIndex (dirichletXi χ) :=
  Equiv.sigmaCongr ⟨conj, conj, fun z ↦ conj_conj z, fun z ↦ conj_conj z⟩ fun z ↦
    finCongr (analyticOrderNatAt_dirichletXi_conj hχ hN z).symm

@[simp] lemma dirichletXiZeroConj_val {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive)
    (hN : N ≠ 1) (ρ : ZeroIndex (dirichletXi χ⁻¹)) :
    (dirichletXiZeroConj hχ hN ρ).val = conj ρ.val := rfl

/-- The bijection `ρ' ↦ 1 - ρ'` from the zeros of `ξ(s, χ⁻¹)` to those of `ξ(s, χ)`. -/
noncomputable def dirichletXiZeroReflect {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive)
    (hN : N ≠ 1) : ZeroIndex (dirichletXi χ⁻¹) ≃ ZeroIndex (dirichletXi χ) :=
  Equiv.sigmaCongr (Equiv.subLeft (1 : ℂ)) fun z ↦
    finCongr (analyticOrderNatAt_dirichletXi_one_sub hχ hN z).symm

@[simp] lemma dirichletXiZeroReflect_val {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive)
    (hN : N ≠ 1) (ρ : ZeroIndex (dirichletXi χ⁻¹)) :
    (dirichletXiZeroReflect hχ hN ρ).val = 1 - ρ.val := rfl

/-- **Davenport, Ch. 12, p. 83 (row 12-19)**: the zeros of `L(s, χ)` in the critical strip are
symmetric about `σ = 1/2`: `ρ ↦ 1 - ρ̄` permutes them, with multiplicity. -/
@[kb "davenport1980" "Ch 12, p. 83"]
theorem Davenport.dirichletXi_zero_symm {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive)
    (hN : N ≠ 1) :
    ∃ e : ZeroIndex (dirichletXi χ) ≃ ZeroIndex (dirichletXi χ),
      ∀ ρ, (e ρ).val = 1 - conj ρ.val :=
  ⟨(dirichletXiZeroConj hχ hN).symm.trans (dirichletXiZeroReflect hχ hN), fun ρ ↦ by
    simp only [Equiv.trans_apply, dirichletXiZeroReflect_val]
    congr 1⟩

/-- `0 ≤ Re(1/ρ) ≤ |ρ|⁻²` in the critical strip. -/
lemma re_one_div_mem {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    0 ≤ (1 / ρ).re ∧ (1 / ρ).re ≤ ‖ρ‖⁻¹ ^ 2 := by
  have hρ : ρ ≠ 0 := by rintro rfl; simp at h0
  have hns : 0 < Complex.normSq ρ := Complex.normSq_pos.mpr hρ
  rw [one_div, Complex.inv_re]
  refine ⟨div_nonneg h0.le hns.le, ?_⟩
  rw [inv_pow, ← Complex.normSq_eq_norm_sq, div_le_iff₀ hns, inv_mul_cancel₀ hns.ne']
  exact h1.le

/-- `B(χ) = ξ'(0, χ)/ξ(0, χ)`. -/
lemma logDeriv_dirichletXi_zero {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (hN : N ≠ 1)
    {A B : ℂ}
    (h : ∀ s, dirichletXi χ s = Complex.exp (A + B * s) *
      ∏' ρ : ZeroIndex (dirichletXi χ), (1 - s / ρ.val) * Complex.exp (s / ρ.val)) :
    logDeriv (dirichletXi χ) 0 = B := by
  have := logDeriv_eq_of_hadamard (differentiable_dirichletXi (ne_one_of_isPrimitive hχ hN))
    (dirichletXi_zero_ne_zero hχ hN) (Davenport.entireOrder_dirichletXi_le_one hχ hN) h
    (dirichletXi_zero_ne_zero hχ hN)
  simpa using this

/-- **Davenport, Ch. 12, (18) (row 12-18)**: for primitive `χ` mod `q > 1`,
`Re B(χ) = -∑_ρ Re(1/ρ)`, the sum over the zeros of `ξ(s, χ)` (absolutely convergent). -/
@[kb "davenport1980" "Ch 12, p. 83"]
theorem Davenport.re_B_eq_neg_tsum {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive)
    (hN : N ≠ 1) {A B : ℂ}
    (h : ∀ s, dirichletXi χ s = Complex.exp (A + B * s) *
      ∏' ρ : ZeroIndex (dirichletXi χ), (1 - s / ρ.val) * Complex.exp (s / ρ.val)) :
    B.re = -∑' ρ : ZeroIndex (dirichletXi χ), (1 / ρ.val).re := by
  have hχ1 := ne_one_of_isPrimitive hχ hN
  have hχ1' : χ⁻¹ ≠ 1 := fun h1 ↦ hχ1 (inv_eq_one.mp h1)
  have hχi := hχ.inv
  obtain ⟨A', B', h'⟩ := Davenport.dirichletXi_hadamard hχi hN
  -- `B(χ⁻¹) = conj B(χ)`
  have hB0 := logDeriv_dirichletXi_zero hχ hN h
  have hB0' := logDeriv_dirichletXi_zero hχi hN h'
  have hconj : B' = conj B := by
    rw [← hB0, ← hB0', logDeriv_apply, logDeriv_apply, dirichletXi_inv_conj hχ1 hN]
    have hd := ((differentiable_dirichletXi hχ1) 0).hasDerivAt.conj_conj
    rw [map_zero] at hd
    rw [hd.deriv]
    simp [map_div₀]
  -- functional equation: `ξ'(0, χ)/ξ(0, χ) = -ξ'(1, χ⁻¹)/ξ(1, χ⁻¹)`
  have hfe : ∀ w, dirichletXi χ w = rootNumber χ * dirichletXi χ⁻¹ (1 - w) := fun w ↦ by
    have := dirichletXi_one_sub hχ (1 - w); rwa [sub_sub_cancel] at this
  have hd1 : HasDerivAt (fun w ↦ rootNumber χ * dirichletXi χ⁻¹ (1 - w))
      (rootNumber χ * (deriv (dirichletXi χ⁻¹) 1 * (-1))) 0 := by
    have hin : HasDerivAt (fun w : ℂ ↦ 1 - w) (-1) 0 := by
      simpa using (hasDerivAt_id (0 : ℂ)).const_sub 1
    have hx : HasDerivAt (dirichletXi χ⁻¹) (deriv (dirichletXi χ⁻¹) 1) ((fun w : ℂ ↦ 1 - w) 0) := by
      simpa using ((differentiable_dirichletXi hχ1') 1).hasDerivAt
    exact (hx.comp 0 hin).const_mul _
  have hfun : (fun w ↦ rootNumber χ * dirichletXi χ⁻¹ (1 - w)) = dirichletXi χ := funext fun w ↦
    (hfe w).symm
  rw [hfun] at hd1
  have hε : rootNumber χ ≠ 0 := by rw [← norm_ne_zero_iff, norm_rootNumber hχ]; norm_num
  have hξ1 : dirichletXi χ⁻¹ 1 ≠ 0 := dirichletXi_ne_zero_of_one_le_re hχ1' hN (by simp)
  have hl1 : logDeriv (dirichletXi χ) 0 = -logDeriv (dirichletXi χ⁻¹) 1 := by
    rw [logDeriv_apply, logDeriv_apply, hd1.deriv, hfe 0, sub_zero]
    field_simp
  have hsum1 := logDeriv_eq_of_hadamard (differentiable_dirichletXi hχ1')
    (dirichletXi_zero_ne_zero hχi hN) (Davenport.entireOrder_dirichletXi_le_one hχi hN) h' hξ1
  rw [hB0, hsum1, hconj] at hl1
  -- real parts
  set T := ∑' ρ : ZeroIndex (dirichletXi χ⁻¹), (1 / (1 - ρ.val) + 1 / ρ.val)
  obtain ⟨ha, ha0⟩ := summable_dirichletXi_zeros hχ hN
  obtain ⟨ha', ha0'⟩ := summable_dirichletXi_zeros hχi hN
  have hstrip := (Davenport.dirichletXi_zeros hχ hN).1
  have hstrip' := (Davenport.dirichletXi_zeros hχi hN).1
  set eC := dirichletXiZeroConj hχ hN
  set eR := dirichletXiZeroReflect hχ hN
  have hR : Summable fun ρ : ZeroIndex (dirichletXi χ) ↦ (1 / ρ.val).re :=
    ha.of_nonneg_of_le (fun ρ ↦ (re_one_div_mem (hstrip ρ).2.1 (hstrip ρ).2.2).1)
      fun ρ ↦ (re_one_div_mem (hstrip ρ).2.1 (hstrip ρ).2.2).2
  -- `∑ Re(1/(1 - ρ')) = ∑ Re(1/ρ)` (via `eR`) and `∑ Re(1/ρ') = ∑ Re(1/ρ)` (via `eC`)
  have hRR : (fun ρ' : ZeroIndex (dirichletXi χ⁻¹) ↦ (1 / (1 - ρ'.val)).re) =
      (fun ρ ↦ (1 / ρ.val).re) ∘ eR := by
    funext ρ'; simp [eR]
  have hRC : (fun ρ' : ZeroIndex (dirichletXi χ⁻¹) ↦ (1 / ρ'.val).re) =
      (fun ρ ↦ (1 / ρ.val).re) ∘ eC := by
    funext ρ'
    simp only [Function.comp_apply, eC, dirichletXiZeroConj_val]
    rw [one_div, one_div, Complex.inv_re, Complex.inv_re, Complex.conj_re, Complex.normSq_conj]
  have hS1 : Summable fun ρ' : ZeroIndex (dirichletXi χ⁻¹) ↦ (1 / (1 - ρ'.val)).re := by
    rw [hRR]; exact hR.comp_injective eR.injective
  have hS2 : Summable fun ρ' : ZeroIndex (dirichletXi χ⁻¹) ↦ (1 / ρ'.val).re := by
    rw [hRC]; exact hR.comp_injective eC.injective
  have hsumT : Summable fun ρ' : ZeroIndex (dirichletXi χ⁻¹) ↦ 1 / (1 - ρ'.val) + 1 / ρ'.val :=
    summable_inv_sub_add_inv ha' ha0' fun ρ' h1 ↦ by
      have := (hstrip' ρ').2.2; rw [h1] at this; simp at this
  have hTre : T.re = 2 * ∑' ρ : ZeroIndex (dirichletXi χ), (1 / ρ.val).re := by
    rw [Complex.re_tsum hsumT]
    simp only [Complex.add_re]
    rw [hS1.tsum_add hS2, hRR, hRC]
    simp only [Function.comp_def]
    rw [eR.tsum_eq (fun ρ ↦ (1 / ρ.val).re), eC.tsum_eq (fun ρ ↦ (1 / ρ.val).re)]
    ring
  have := congrArg Complex.re hl1
  simp only [Complex.neg_re, Complex.add_re, Complex.conj_re] at this
  rw [hTre] at this
  linarith

/-- **Davenport, Ch. 12, p. 83 (row 12-18)**: for a real primitive character (`χ⁻¹ = χ`),
`B(χ)` is real and negative. -/
@[kb "davenport1980" "Ch 12, p. 83"]
theorem Davenport.B_real_neg_of_real {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive)
    (hN : N ≠ 1) (hreal : χ⁻¹ = χ) {A B : ℂ}
    (h : ∀ s, dirichletXi χ s = Complex.exp (A + B * s) *
      ∏' ρ : ZeroIndex (dirichletXi χ), (1 - s / ρ.val) * Complex.exp (s / ρ.val)) :
    B.im = 0 ∧ B.re < 0 := by
  have hχ1 := ne_one_of_isPrimitive hχ hN
  have hB0 := logDeriv_dirichletXi_zero hχ hN h
  have hsym := dirichletXi_inv_conj hχ1 hN
  rw [hreal] at hsym
  constructor
  · have hc : B = conj B := by
      rw [← hB0, logDeriv_apply]
      conv_lhs => rw [hsym]
      have hd := ((differentiable_dirichletXi hχ1) 0).hasDerivAt.conj_conj
      rw [map_zero] at hd
      rw [hd.deriv]
      simp [map_div₀]
    exact Complex.conj_eq_iff_im.mp hc.symm
  · rw [Davenport.re_B_eq_neg_tsum hχ hN h, neg_lt_zero]
    obtain ⟨ha, -⟩ := summable_dirichletXi_zeros hχ hN
    have hstrip := (Davenport.dirichletXi_zeros hχ hN).1
    have hR : Summable fun ρ : ZeroIndex (dirichletXi χ) ↦ (1 / ρ.val).re :=
      ha.of_nonneg_of_le (fun ρ ↦ (re_one_div_mem (hstrip ρ).2.1 (hstrip ρ).2.2).1)
        fun ρ ↦ (re_one_div_mem (hstrip ρ).2.1 (hstrip ρ).2.2).2
    have hinf := (Davenport.dirichletXi_zeros_infinite hχ hN).2.1
    obtain ⟨ρ⟩ : Nonempty (ZeroIndex (dirichletXi χ)) := inferInstance
    refine hR.tsum_pos (fun ρ ↦ (re_one_div_mem (hstrip ρ).2.1 (hstrip ρ).2.2).1) ρ ?_
    have h0 := (hstrip ρ).2.1
    have hρ : ρ.val ≠ 0 := by intro h; rw [h] at h0; simp at h0
    rw [one_div, Complex.inv_re]
    exact div_pos h0 (Complex.normSq_pos.mpr hρ)

end NTKB
