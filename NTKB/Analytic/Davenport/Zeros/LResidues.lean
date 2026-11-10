/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Davenport.Zeros.LExplicitSum
import NTKB.Analytic.Davenport.Zeros.LLocalLeft
import NTKB.Analytic.Davenport.Zeros.ExplicitContour

/-!
# Residues of `-L'/L(s, χ) x^s/s`

**Davenport, Ch. 19, pp. 115-116.** For primitive `χ` mod `q > 1`: at a nontrivial zero `ρ` of
multiplicity `m` the residue of `F(s, χ) = -L'/L(s, χ) x^s/s` is `-m x^ρ/ρ`. At `s = 0`: for odd
`χ` (`a = 1`), `L(0, χ) ≠ 0` and the residue is `-L'/L(0, χ)`; for even `χ` (`a = 0`),
`L(s, χ) = s k(s)` with `k(0) = ξ(0, χ)/2 ≠ 0`, so `F` has a double pole, and
`F(s) + 1/s²` has residue `-(log x + b(χ))` where `L'/L(s, χ) = 1/s + b(χ) + O(s)`.
-/

open Filter Topology Complex Set DirichletCharacter
open scoped Real

namespace NTKB

variable {N : ℕ} [NeZero N]

omit [NeZero N] in
lemma analyticAt_Gammaℝ {s : ℂ} (hs : 0 < s.re) : AnalyticAt ℂ Gammaℝ s := by
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h0' : AnalyticAt ℂ (fun s : ℂ ↦ s / 2) s := by fun_prop
  have h1 : AnalyticAt ℂ (fun s : ℂ ↦ (π : ℂ) ^ (-s / 2)) s :=
    Differentiable.analyticAt (fun z ↦
      ((differentiableAt_id.neg).div_const (2 : ℂ)).const_cpow (Or.inl hπ)) s
  have h2 : AnalyticAt ℂ (fun s : ℂ ↦ Complex.Gamma (s / 2)) s :=
    (analyticAt_Gamma_of_re_pos' (by simp; linarith)).comp h0'
  exact (h1.mul h2).congr (Eventually.of_forall fun z ↦ by simp [Gammaℝ_def])

lemma analyticAt_LFunction {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) (s : ℂ) :
    AnalyticAt ℂ (LFunction χ) s :=
  (differentiable_LFunction hχ).analyticAt s

/-- For `Re p > 0`, `L(s, χ)` and `ξ(s, χ)` have the same order of vanishing at `p`. -/
lemma analyticOrderAt_LFunction_eq {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (hN : N ≠ 1)
    {p : ℂ} (hp : 0 < p.re) :
    analyticOrderAt (LFunction χ) p = analyticOrderAt (dirichletXi χ) p := by
  have hχ1 := ne_one_of_isPrimitive hχ hN
  set a := dirichletParity χ
  have ha0 := dirichletParity_re_nonneg χ
  set P : ℂ → ℂ := fun s ↦ (N : ℂ) ^ ((s + a) / 2) * Gammaℝ (s + a)
  have hP : AnalyticAt ℂ P p := by
    have h0' : AnalyticAt ℂ (fun s : ℂ ↦ s + a) p := by fun_prop
    have h1 : AnalyticAt ℂ (fun s : ℂ ↦ (N : ℂ) ^ ((s + a) / 2)) p :=
      Differentiable.analyticAt (fun z ↦ ((differentiableAt_id.add_const a).div_const (2 : ℂ)).const_cpow
        (Or.inl natCast_ne_zero')) p
    have h2 : AnalyticAt ℂ (fun s : ℂ ↦ Gammaℝ (s + a)) p :=
      (analyticAt_Gammaℝ (by simp; linarith)).comp h0'
    exact h1.mul h2
  have hP0 : P p ≠ 0 := by
    have h1 : (N : ℂ) ^ ((p + a) / 2) ≠ 0 := by
      rw [Ne, Complex.cpow_eq_zero_iff]; push Not; intro h; exact absurd h natCast_ne_zero'
    exact mul_ne_zero h1 (Gammaℝ_ne_zero_of_re_pos (by simp; linarith))
  have hev : dirichletXi χ =ᶠ[𝓝 p] P * LFunction χ := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show p ∈ {s : ℂ | 0 < s.re} from hp)] with s hs
    have hs' : 0 < (s + a).re := by simp; linarith [show 0 < s.re from hs]
    rw [dirichletXi_eq_mul_LFunction χ hN (Gammaℝ_ne_zero_of_re_pos hs')]
    rfl
  rw [analyticOrderAt_congr hev, analyticOrderAt_mul hP (analyticAt_LFunction hχ1 p),
    analyticOrderAt_eq_zero.mpr (Or.inr hP0), zero_add]

/-- At a nontrivial zero `ρ` of multiplicity `m`: `F(s, χ) - (-m) x^ρ/ρ / (s - ρ)` is bounded. -/
lemma bddNear_explicitIntegrandL_zero {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive)
    (hN : N ≠ 1) {x : ℝ} (hx : 0 < x) (ρ : ZeroIndex (dirichletXi χ)) :
    BddNear (fun s ↦ explicitIntegrandL χ x s -
      (-(analyticOrderNatAt (dirichletXi χ) ρ.val : ℂ)) * perronKernel x ρ.val / (s - ρ.val))
      ρ.val := by
  have hχ1 := ne_one_of_isPrimitive hχ hN
  have hρ := dirichletXi_zero_mem hχ hN ρ
  have hρ0 : ρ.val ≠ 0 := fun h ↦ by rw [h] at hρ; simp at hρ
  have hfin : analyticOrderAt (dirichletXi χ) ρ.val ≠ ⊤ := by
    intro htop
    rw [analyticOrderAt_eq_top] at htop
    have hA : AnalyticOnNhd ℂ (dirichletXi χ) univ := fun z _ ↦
      (differentiable_dirichletXi hχ1).analyticAt z
    have := hA.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
      (mem_univ ρ.val) htop (mem_univ 0)
    exact dirichletXi_zero_ne_zero hχ hN this
  have hm : analyticOrderAt (LFunction χ) ρ.val =
      (analyticOrderNatAt (dirichletXi χ) ρ.val : ℕ) := by
    rw [analyticOrderAt_LFunction_eq hχ hN hρ.2.1]
    exact (ENat.natCast_toNat hfin).symm
  have h1 := (bddNear_logDeriv_sub (analyticAt_LFunction hχ1 ρ.val) hm).neg
  have h2 : BddNear (fun s ↦ -(deriv (LFunction χ) s / LFunction χ s) -
      (-(analyticOrderNatAt (dirichletXi χ) ρ.val : ℂ)) / (s - ρ.val)) ρ.val :=
    h1.congr (Eventually.of_forall fun s ↦ by simp only [logDeriv_apply]; ring)
  exact (bddNear_mul_sub h2 (differentiableAt_perronKernel hx hρ0)).congr
    (Eventually.of_forall fun s ↦ by simp [explicitIntegrandL])

/-- `(x^s - 1)/s` is bounded near `0`. -/
lemma bddNear_perronKernel_sub {x : ℝ} (hx : 0 < x) :
    BddNear (fun s ↦ perronKernel x s - 1 / (s - 0)) 0 := by
  have hx' : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hd : DifferentiableAt ℂ (fun s : ℂ ↦ (x : ℂ) ^ s) 0 :=
    differentiableAt_id.const_cpow (Or.inl hx')
  refine (bddNear_slope hd).congr (Eventually.of_forall fun s ↦ ?_)
  simp only [perronKernel, Complex.cpow_zero, sub_zero]
  ring

/-- For odd primitive `χ`, `L(0, χ) ≠ 0`. -/
lemma LFunction_zero_ne_zero_of_odd {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (hN : N ≠ 1)
    (ha : dirichletParity χ = 1) : LFunction χ 0 ≠ 0 := by
  intro hL
  have hG : Gammaℝ (0 + dirichletParity χ) ≠ 0 := by
    rw [ha]; exact Gammaℝ_ne_zero_of_re_pos (by simp)
  have := dirichletXi_eq_mul_LFunction χ hN hG
  rw [hL, mul_zero] at this
  exact dirichletXi_zero_ne_zero hχ hN this

/-- For odd primitive `χ`: `F(s, χ) - (-L'/L(0, χ))/s` is bounded near `0`. -/
lemma bddNear_explicitIntegrandL_origin_odd {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive)
    (hN : N ≠ 1) (ha : dirichletParity χ = 1) {x : ℝ} (hx : 0 < x) :
    BddNear (fun s ↦ explicitIntegrandL χ x s -
      -(deriv (LFunction χ) 0 / LFunction χ 0) / (s - 0)) 0 := by
  have hχ1 := ne_one_of_isPrimitive hχ hN
  have hL0 := LFunction_zero_ne_zero_of_odd hχ hN ha
  have han := analyticAt_LFunction hχ1 0
  have hg : DifferentiableAt ℂ (fun s ↦ -(deriv (LFunction χ) s / LFunction χ s)) 0 :=
    ((han.deriv.differentiableAt.div han.differentiableAt hL0).neg)
  refine (bddNear_mul_sub (bddNear_perronKernel_sub hx) hg).congr
    (Eventually.of_forall fun s ↦ ?_)
  simp only [explicitIntegrandL]
  ring

/-! ### Even characters: the double pole at `0` -/

/-- For even `χ`: `k(s) = ξ(s, χ) / (2 q^{s/2} π^{-s/2} Γ(s/2 + 1))`, so that `L(s, χ) = s k(s)`
near `0` and `k(0) = ξ(0, χ)/2`. -/
noncomputable def evenFactor (χ : DirichletCharacter ℂ N) (s : ℂ) : ℂ :=
  dirichletXi χ s / (2 * (N : ℂ) ^ (s / 2) * (π : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2 + 1))

/-- Davenport's `b(χ)` for even `χ`: `L'/L(s, χ) = 1/s + b(χ) + O(|s|)` near `0`. -/
noncomputable def bEven (χ : DirichletCharacter ℂ N) : ℂ :=
  deriv (evenFactor χ) 0 / evenFactor χ 0

lemma evenFactor_denom_ne_zero {s : ℂ} (hs : ‖s‖ < 1) :
    2 * (N : ℂ) ^ (s / 2) * (π : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2 + 1) ≠ 0 := by
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h1 : (N : ℂ) ^ (s / 2) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]; push Not; intro h; exact absurd h natCast_ne_zero'
  have h2 : (π : ℂ) ^ (-s / 2) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]; push Not; intro h; exact absurd h hπ
  have h3 : Complex.Gamma (s / 2 + 1) ≠ 0 := by
    apply Complex.Gamma_ne_zero
    intro m hm
    have := congrArg Complex.re hm
    simp at this
    have h4 : |s.re| < 1 := (Complex.abs_re_le_norm s).trans_lt hs
    rw [abs_lt] at h4
    linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero h1) h2) h3

lemma analyticAt_evenFactor {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (hN : N ≠ 1)
    {s : ℂ} (hs : ‖s‖ < 1) : AnalyticAt ℂ (evenFactor χ) s := by
  have hχ1 := ne_one_of_isPrimitive hχ hN
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hξ : AnalyticAt ℂ (dirichletXi χ) s := (differentiable_dirichletXi hχ1).analyticAt s
  have h1 : AnalyticAt ℂ (fun s : ℂ ↦ (N : ℂ) ^ (s / 2)) s :=
    Differentiable.analyticAt (fun z ↦ (differentiableAt_id.div_const (2 : ℂ)).const_cpow
      (Or.inl natCast_ne_zero')) s
  have h2 : AnalyticAt ℂ (fun s : ℂ ↦ (π : ℂ) ^ (-s / 2)) s :=
    Differentiable.analyticAt (fun z ↦ ((differentiableAt_id.neg).div_const (2 : ℂ)).const_cpow
      (Or.inl hπ)) s
  have h0 : AnalyticAt ℂ (fun s : ℂ ↦ s / 2 + 1) s := by fun_prop
  have h3 : AnalyticAt ℂ (fun s : ℂ ↦ Complex.Gamma (s / 2 + 1)) s := by
    refine (analyticAt_Gamma_of_re_pos' ?_).comp h0
    have h4 : |s.re| < 1 := (Complex.abs_re_le_norm s).trans_lt hs
    rw [abs_lt] at h4
    simp; linarith
  have hd : AnalyticAt ℂ (fun s : ℂ ↦ 2 * (N : ℂ) ^ (s / 2) * (π : ℂ) ^ (-s / 2) *
      Complex.Gamma (s / 2 + 1)) s := ((analyticAt_const.mul h1).mul h2).mul h3
  exact hξ.div hd (evenFactor_denom_ne_zero hs)

lemma evenFactor_zero {χ : DirichletCharacter ℂ N} :
    evenFactor χ 0 = dirichletXi χ 0 / 2 := by
  simp [evenFactor]

/-- `L(s, χ) = s k(s)` for `0 < ‖s‖ < 1` (even `χ`). -/
lemma LFunction_eq_mul_evenFactor {χ : DirichletCharacter ℂ N} (hN : N ≠ 1)
    (ha : dirichletParity χ = 0) {s : ℂ} (hs : ‖s‖ < 1) (hs0 : s ≠ 0) :
    LFunction χ s = s * evenFactor χ s := by
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hG : Gammaℝ (s + dirichletParity χ) ≠ 0 := by
    rw [ha, add_zero, Ne, Gammaℝ_eq_zero_iff, not_exists]
    intro n hn
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · simp at hn; exact hs0 hn
    · have := congrArg norm hn
      rw [norm_neg, norm_mul, Complex.norm_natCast] at this
      have h2 : (1 : ℝ) ≤ n := by exact_mod_cast hn0
      have : ‖s‖ = 2 * n := by rw [this]; simp
      linarith
  have hξ := dirichletXi_eq_mul_LFunction χ hN hG
  rw [ha, add_zero, Gammaℝ_def] at hξ
  have hd := evenFactor_denom_ne_zero (N := N) hs
  have hΓ : Complex.Gamma (s / 2 + 1) = s / 2 * Complex.Gamma (s / 2) :=
    Complex.Gamma_add_one _ (div_ne_zero hs0 two_ne_zero)
  rw [evenFactor, hξ, eq_comm, mul_div_assoc', div_eq_iff hd, hΓ]
  ring

/-- For even primitive `χ`: `L(s, χ) = s k(s)` near `0` (including `s = 0`). -/
lemma LFunction_eventuallyEq_mul_evenFactor {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive)
    (hN : N ≠ 1) (ha : dirichletParity χ = 0) :
    ∀ᶠ s in 𝓝 (0 : ℂ), LFunction χ s = s * evenFactor χ s := by
  have hχ1 := ne_one_of_isPrimitive hχ hN
  have hball : Metric.ball (0 : ℂ) 1 ∈ 𝓝 (0 : ℂ) := Metric.ball_mem_nhds _ one_pos
  -- continuity gives the value at `0`
  have h0 : LFunction χ 0 = 0 * evenFactor χ 0 := by
    have hc1 : ContinuousAt (LFunction χ) 0 := (differentiable_LFunction hχ1).continuous.continuousAt
    have hc2 : ContinuousAt (fun s ↦ s * evenFactor χ s) 0 :=
      continuousAt_id.mul (analyticAt_evenFactor hχ hN (by simp)).continuousAt
    have hev : LFunction χ =ᶠ[𝓝[≠] (0 : ℂ)] fun s ↦ s * evenFactor χ s := by
      filter_upwards [nhdsWithin_le_nhds hball, self_mem_nhdsWithin] with s hs hs0
      exact LFunction_eq_mul_evenFactor hN ha (by simpa using hs) hs0
    exact tendsto_nhds_unique (hc1.tendsto.mono_left nhdsWithin_le_nhds)
      ((hc2.tendsto.mono_left nhdsWithin_le_nhds).congr' hev.symm)
  filter_upwards [hball] with s hs
  rcases eq_or_ne s 0 with rfl | hs0
  · exact h0
  · exact LFunction_eq_mul_evenFactor hN ha (by simpa using hs) hs0

/-- `|(x^s - 1)/s - log x| / |s| ≤ (log x)²` near `0`: `(x^s - 1 - s log x)/s²` is bounded. -/
lemma bddNear_cpow_second {x : ℝ} (hx : 0 < x) :
    BddNear (fun s : ℂ ↦ ((x : ℂ) ^ s - 1 - s * Real.log x) / (s - 0) ^ 2) 0 := by
  have hx' : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  set c := Real.log x
  refine bddNear_iff_eventually.mpr ⟨c ^ 2, ?_⟩
  have hsmall : ∀ᶠ s in 𝓝 (0 : ℂ), ‖s * (c : ℂ)‖ ≤ 1 := by
    have : ContinuousAt (fun s : ℂ ↦ ‖s * (c : ℂ)‖) 0 := by fun_prop
    have h := this.eventually (gt_mem_nhds (show ‖(0 : ℂ) * (c : ℂ)‖ < 1 by simp))
    filter_upwards [h] with s hs; exact hs.le
  filter_upwards [hsmall.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with s hs hs0
  have hs0' : s ≠ 0 := hs0
  have hcp : (x : ℂ) ^ s = Complex.exp (s * (c : ℂ)) := by
    rw [Complex.cpow_def_of_ne_zero hx', ← Complex.ofReal_log hx.le, mul_comm]
  rw [hcp, sub_zero, norm_div, norm_pow]
  have := Complex.norm_exp_sub_one_sub_id_le hs
  rw [div_le_iff₀ (by positivity)]
  calc ‖Complex.exp (s * (c : ℂ)) - 1 - s * (c : ℂ)‖ ≤ ‖s * (c : ℂ)‖ ^ 2 := this
    _ = c ^ 2 * ‖s‖ ^ 2 := by rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]; ring

/-- For even primitive `χ`: `F(s, χ) + 1/s² - (-(log x + b(χ)))/s` is bounded near `0`. -/
lemma bddNear_explicitIntegrandL_origin_even {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive)
    (hN : N ≠ 1) (ha : dirichletParity χ = 0) {x : ℝ} (hx : 0 < x) :
    BddNear (fun s ↦ (explicitIntegrandL χ x s + 1 / (s - 0) ^ 2) -
      (-((Real.log x : ℂ) + bEven χ)) / (s - 0)) 0 := by
  have hk := analyticAt_evenFactor hχ hN (s := 0) (by simp)
  have hk0 : evenFactor χ 0 ≠ 0 := by
    rw [evenFactor_zero]; exact div_ne_zero (dirichletXi_zero_ne_zero hχ hN) two_ne_zero
  set K : ℂ → ℂ := fun s ↦ deriv (evenFactor χ) s / evenFactor χ s
  have hK : DifferentiableAt ℂ (fun s ↦ -K s) 0 :=
    ((hk.deriv.differentiableAt.div hk.differentiableAt hk0).neg)
  have h1 := bddNear_mul_sub (bddNear_perronKernel_sub hx) hK
  have h2 := (bddNear_cpow_second hx).neg
  refine (h2.add h1).congr ?_
  -- the identity near `0`
  have hevL := LFunction_eventuallyEq_mul_evenFactor hχ hN ha
  have hk_ne : ∀ᶠ s in 𝓝 (0 : ℂ), evenFactor χ s ≠ 0 := hk.continuousAt.eventually_ne hk0
  have hkan : ∀ᶠ s in 𝓝 (0 : ℂ), AnalyticAt ℂ (evenFactor χ) s := hk.eventually_analyticAt
  filter_upwards [(hevL.eventually_nhds).filter_mono nhdsWithin_le_nhds,
    hk_ne.filter_mono nhdsWithin_le_nhds, hkan.filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with s hsL hsk hsan hs0
  have hs0' : s ≠ 0 := hs0
  -- `L'/L(s) = 1/s + K(s)`
  have hderiv : deriv (LFunction χ) s = evenFactor χ s + s * deriv (evenFactor χ) s := by
    have hfeq : LFunction χ =ᶠ[𝓝 s] fun z ↦ z * evenFactor χ z := hsL
    rw [hfeq.deriv_eq]
    have h := (hasDerivAt_id' s).mul hsan.differentiableAt.hasDerivAt
    have e := h.deriv
    simp only [one_mul] at e
    exact e
  have hLs : LFunction χ s = s * evenFactor χ s := hsL.self_of_nhds
  simp only [explicitIntegrandL, perronKernel, bEven, K, sub_zero]
  rw [hderiv, hLs]
  have hx' : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  field_simp
  ring

end NTKB
