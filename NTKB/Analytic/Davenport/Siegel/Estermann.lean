/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Port.ZetaMulPair
import NTKB.Analytic.Davenport.Zeros.LNearOne
import NTKB.Analytic.Davenport.Ch1to6.LOnePos
import NTKB.Analytic.Apostol.Zeta.HurwitzBounds
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Positivity
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Estermann's inequality (Davenport, Chapter 21, (6)–(10))

For real nonprincipal characters `χ₁` mod `q₁` and `χ₂` mod `q₂` with `χ₁ χ₂` nonprincipal, put
`F(s) = ζ(s) L(s, χ₁) L(s, χ₂) L(s, χ₁ χ₂)` (Davenport (6); the product character is taken at the
least common multiple of the levels) and `A = L(1, χ₁) L(1, χ₂) L(1, χ₁ χ₂)` (Davenport (7)).

* `siegelF` is `F`; `siegelG` is `G = L(s, χ₁) L(s, χ₂) L(s, χ₁ χ₂)`, so `A = G(1)`.
* `siegelH` is the entire function `F(s) - A/(s - 1)`, built from Mathlib's `riemannZeta₀`
  (the completion of `ζ(s) - 1/(s - 1)`) and the slope of `G` at `1`.
* `siegelF_eq_LSeries`: `F` is the Dirichlet series of the nonnegative coefficients
  `zetaMulPairCoeffs` (ported from Tau Ceti), with coefficient `1` at `n = 1`.
* `siegel_taylor_ge`: from the Taylor expansion (9) of `F(s) - A/(s - 1)` at `s = 2`, the signs
  of the coefficients `b_m ≥ 0`, `b₀ ≥ 1`, and Cauchy's inequality (10) on the circle
  `|s - 2| = 3/2`,
  `F(σ) ≥ 1 - |A| (2 - σ)^M/(1 - σ) - 6 K (5/6)^M` for `3/4 ≤ σ < 1`.
* `estermann_inequality`: **Davenport (8)**,
  `F(σ) ≥ 1/2 - C |A| (q₁ q₂)^{c (1 - σ)}/(1 - σ)` for `3/4 ≤ σ < 1`, with absolute `c, C`.
-/

open Complex Filter Topology Set Metric
open scoped ComplexOrder Nat

namespace NTKB.Davenport

variable {q₁ q₂ : ℕ} [NeZero q₁] [NeZero q₂]

/-- `G(s) = L(s, χ₁) L(s, χ₂) L(s, χ₁ χ₂)`. -/
noncomputable def siegelG (χ₁ : DirichletCharacter ℂ q₁) (χ₂ : DirichletCharacter ℂ q₂)
    (s : ℂ) : ℂ :=
  χ₁.LFunction s * χ₂.LFunction s * (χ₁.mul χ₂).LFunction s

/-- **Davenport, Ch. 21, (6)**: `F(s) = ζ(s) L(s, χ₁) L(s, χ₂) L(s, χ₁ χ₂)`. -/
noncomputable def siegelF (χ₁ : DirichletCharacter ℂ q₁) (χ₂ : DirichletCharacter ℂ q₂)
    (s : ℂ) : ℂ :=
  riemannZeta s * siegelG χ₁ χ₂ s

/-- The entire function `F(s) - A/(s - 1)`, `A = G(1)`. -/
noncomputable def siegelH (χ₁ : DirichletCharacter ℂ q₁) (χ₂ : DirichletCharacter ℂ q₂)
    (s : ℂ) : ℂ :=
  riemannZeta₀ s * siegelG χ₁ χ₂ s + dslope (siegelG χ₁ χ₂) 1 s

variable {χ₁ : DirichletCharacter ℂ q₁} {χ₂ : DirichletCharacter ℂ q₂}

lemma differentiable_siegelG (h₁ : χ₁ ≠ 1) (h₂ : χ₂ ≠ 1) (h₁₂ : χ₁.mul χ₂ ≠ 1) :
    Differentiable ℂ (siegelG χ₁ χ₂) := by
  unfold siegelG
  exact ((DirichletCharacter.differentiable_LFunction h₁).mul
    (DirichletCharacter.differentiable_LFunction h₂)).mul
    (DirichletCharacter.differentiable_LFunction h₁₂)

lemma differentiable_siegelH (h₁ : χ₁ ≠ 1) (h₂ : χ₂ ≠ 1) (h₁₂ : χ₁.mul χ₂ ≠ 1) :
    Differentiable ℂ (siegelH χ₁ χ₂) := by
  have hG := differentiable_siegelG h₁ h₂ h₁₂
  have hd : Differentiable ℂ (dslope (siegelG χ₁ χ₂) 1) := by
    rw [← differentiableOn_univ]
    exact (differentiableOn_dslope Filter.univ_mem).2 hG.differentiableOn
  exact (differentiable_riemannZeta₀.mul hG).add hd

/-- `H(s) = F(s) - A/(s - 1)` for `s ≠ 1`. -/
lemma siegelH_eq {s : ℂ} (hs : s ≠ 1) :
    siegelH χ₁ χ₂ s = siegelF χ₁ χ₂ s - siegelG χ₁ χ₂ 1 / (s - 1) := by
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  rw [siegelH, siegelF, dslope_of_ne _ hs, slope_def_field, riemannZeta_eq_inv_sub_add hs]
  simp only [riemannZeta₀, if_neg hs]
  field_simp
  ring

/-- **Davenport, Ch. 21, p. 129**: on `Re s > 1`, `F` is the Dirichlet series with the
coefficients `zetaMulPairCoeffs χ₁ χ₂`. -/
lemma siegelF_hasSum {s : ℂ} (hs : 1 < s.re) :
    LSeriesHasSum (NTKB.DirichletCharacter.zetaMulPairCoeffs χ₁ χ₂) s (siegelF χ₁ χ₂ s) := by
  have h := NTKB.DirichletCharacter.LSeriesHasSum_zetaMulPairCoeffs χ₁ χ₂ hs
  rw [siegelF, siegelG]
  convert h using 1
  ring

lemma siegelF_eq_LSeries {s : ℂ} (hs : 1 < s.re) :
    siegelF χ₁ χ₂ s = LSeries (NTKB.DirichletCharacter.zetaMulPairCoeffs χ₁ χ₂ ·) s :=
  (siegelF_hasSum hs).LSeries_eq.symm

lemma abscissa_zetaMulPairCoeffs_le :
    LSeries.abscissaOfAbsConv (NTKB.DirichletCharacter.zetaMulPairCoeffs χ₁ χ₂ ·) ≤ 1 := by
  refine LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy ↦ ?_
  exact (siegelF_hasSum (χ₁ := χ₁) (χ₂ := χ₂) (s := (y : ℂ)) (by simpa using hy)).LSeriesSummable

/-- **Davenport, Ch. 21, p. 129**: the Taylor coefficients of `F` at `2` have alternating signs,
`(-1)^m F^{(m)}(2) ≥ 0` (i.e. `b_m ≥ 0`), for quadratic `χ₁, χ₂`. -/
lemma iteratedDeriv_siegelF_alternating (hq₁ : χ₁.IsQuadratic) (hq₂ : χ₂.IsQuadratic) (m : ℕ) :
    0 ≤ (-1) ^ m * iteratedDeriv m (siegelF χ₁ χ₂) 2 := by
  have hU : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const continuous_re
  have heq : EqOn (siegelF χ₁ χ₂) (LSeries (NTKB.DirichletCharacter.zetaMulPairCoeffs χ₁ χ₂ ·))
      {s : ℂ | 1 < s.re} := fun s hs ↦ siegelF_eq_LSeries hs
  have h2 : (2 : ℂ) ∈ {s : ℂ | 1 < s.re} := by show (1 : ℝ) < (2 : ℂ).re; norm_num
  rw [heq.iteratedDeriv_of_isOpen hU m h2]
  have := LSeries.iteratedDeriv_alternating
    (a := (NTKB.DirichletCharacter.zetaMulPairCoeffs χ₁ χ₂ ·))
    (fun n ↦ NTKB.DirichletCharacter.zetaMulPairCoeffs_nonneg hq₁ hq₂ n)
    (x := 2) (abscissa_zetaMulPairCoeffs_le.trans_lt (by exact_mod_cast (show (1 : ℝ) < 2 by norm_num))) m
  simpa using this

/-- `F(2) ≥ 1` (the coefficient at `n = 1` is `1`, the others are nonnegative). -/
lemma one_le_siegelF_two (hq₁ : χ₁.IsQuadratic) (hq₂ : χ₂.IsQuadratic) :
    1 ≤ siegelF χ₁ χ₂ 2 := by
  have hs : 1 < (2 : ℂ).re := by simp
  have h := siegelF_hasSum (χ₁ := χ₁) (χ₂ := χ₂) hs
  have hnn : ∀ n, 0 ≤ LSeries.term (NTKB.DirichletCharacter.zetaMulPairCoeffs χ₁ χ₂ ·) 2 n :=
    fun n ↦ LSeries.term_nonneg (NTKB.DirichletCharacter.zetaMulPairCoeffs_nonneg hq₁ hq₂ n) 2
  have h1 : LSeries.term (NTKB.DirichletCharacter.zetaMulPairCoeffs χ₁ χ₂ ·) 2 1 = 1 := by
    simp [LSeries.term]
  rw [← h1]
  exact le_hasSum h 1 (fun j _ ↦ hnn j)

/-- `F^{(m)}(2) = H^{(m)}(2) + A (-1)^m m!` (the Taylor coefficients of `A/(s - 1)` at `2`). -/
lemma iteratedDeriv_siegelF_two (h₁ : χ₁ ≠ 1) (h₂ : χ₂ ≠ 1) (h₁₂ : χ₁.mul χ₂ ≠ 1) (m : ℕ) :
    iteratedDeriv m (siegelF χ₁ χ₂) 2 =
      iteratedDeriv m (siegelH χ₁ χ₂) 2 + siegelG χ₁ χ₂ 1 * ((-1) ^ m * m !) := by
  have hU : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const continuous_re
  have h2 : (2 : ℂ) ∈ {s : ℂ | 1 < s.re} := by show (1 : ℝ) < (2 : ℂ).re; norm_num
  have heq : EqOn (siegelF χ₁ χ₂)
      (fun s ↦ siegelH χ₁ χ₂ s + siegelG χ₁ χ₂ 1 * (s - 1)⁻¹) {s : ℂ | 1 < s.re} := by
    intro s hs
    have hs1 : s ≠ 1 := by
      rintro rfl; simp at hs
    simp only
    rw [siegelH_eq hs1]
    ring
  rw [heq.iteratedDeriv_of_isOpen hU m h2]
  have hH : ContDiffAt ℂ m (siegelH χ₁ χ₂) 2 :=
    (differentiable_siegelH h₁ h₂ h₁₂).contDiff.contDiffAt
  have hinv : ContDiffAt ℂ m (fun s : ℂ ↦ (s - 1)⁻¹) 2 :=
    (contDiffAt_id.sub contDiffAt_const).inv (by norm_num)
  rw [iteratedDeriv_fun_add hH (contDiffAt_const.mul hinv), iteratedDeriv_const_mul_field]
  congr 2
  rw [iteratedDeriv_eq_iterate]
  have := congrFun (iter_deriv_inv_linear_sub (𝕜 := ℂ) m 1 1) 2
  simp only [one_mul, one_pow, mul_one] at this
  rw [this]
  norm_num

/-- **Davenport, Ch. 21, (9) and (10)** (the Taylor expansion of `F(s) - A/(s - 1)` at `2`, the
signs of its coefficients and Cauchy's inequality on `|s - 2| = 3/2`): if `|H| ≤ K` on that
circle, then for `3/4 ≤ σ < 1` and `M ≥ 1`,
`F(σ) ≥ 1 - |A| (2 - σ)^M/(1 - σ) - 6 K (5/6)^M`. -/
lemma siegel_taylor_ge (hq₁ : χ₁.IsQuadratic) (hq₂ : χ₂.IsQuadratic) (h₁ : χ₁ ≠ 1)
    (h₂ : χ₂ ≠ 1) (h₁₂ : χ₁.mul χ₂ ≠ 1) {K : ℝ}
    (hK : ∀ z ∈ sphere (2 : ℂ) (3 / 2), ‖siegelH χ₁ χ₂ z‖ ≤ K) {σ : ℝ} (hσ : 3 / 4 ≤ σ)
    (hσ1 : σ < 1) {M : ℕ} (hM : 1 ≤ M) :
    1 - ‖siegelG χ₁ χ₂ 1‖ * (2 - σ) ^ M / (1 - σ) - 6 * K * (5 / 6) ^ M ≤
      (siegelF χ₁ χ₂ σ).re := by
  have hH := differentiable_siegelH h₁ h₂ h₁₂
  set G1 := siegelG χ₁ χ₂ 1 with hG1
  set t : ℝ := 2 - σ with ht
  have ht1 : 1 < t := by rw [ht]; linarith
  have ht2 : t ≤ 5 / 4 := by rw [ht]; linarith
  have hK0 : 0 ≤ K := by
    have hz : (2 + 3 / 2 : ℂ) ∈ sphere (2 : ℂ) (3 / 2) := by
      rw [mem_sphere, dist_eq_norm, add_sub_cancel_left]
      norm_num [Complex.norm_real]
    exact (norm_nonneg _).trans (hK _ hz)
  -- Taylor expansion of `H` at `2`, evaluated at `σ`
  have hmem : (σ : ℂ) ∈ ball (2 : ℂ) 2 := by
    rw [mem_ball, dist_eq_norm, show (σ : ℂ) - 2 = ((σ - 2 : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith)]
    linarith
  have hT := Complex.hasSum_taylorSeries_on_ball hH.differentiableOn hmem
  set f : ℕ → ℂ := fun n ↦ (n ! : ℂ)⁻¹ • ((σ : ℂ) - 2) ^ n • iteratedDeriv n (siegelH χ₁ χ₂) 2
    with hf
  -- the terms
  have hfn : ∀ n, f n = (t : ℂ) ^ n *
      ((n ! : ℂ)⁻¹ * ((-1) ^ n * iteratedDeriv n (siegelF χ₁ χ₂) 2) - G1) := by
    intro n
    simp only [hf, smul_eq_mul]
    rw [iteratedDeriv_siegelF_two h₁ h₂ h₁₂ n, ← hG1]
    have hσt : (σ : ℂ) - 2 = -(t : ℂ) := by rw [ht]; push_cast; ring
    rw [hσt, neg_pow]
    have hfac : (n ! : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
    have hinv : (n ! : ℂ)⁻¹ * n ! = 1 := inv_mul_cancel₀ hfac
    set u : ℂ := (-1) ^ n
    have hu : u * u = 1 := by simp only [u]; rw [← mul_pow]; norm_num
    linear_combination (-(t : ℂ) ^ n * G1 * u * u) * hinv + (-(t : ℂ) ^ n * G1) * hu
  set e : ℕ → ℝ := fun n ↦ ((-1) ^ n * iteratedDeriv n (siegelF χ₁ χ₂) 2).re with he
  have he0 : ∀ n, 0 ≤ e n := fun n ↦
    (Complex.le_def.mp (iteratedDeriv_siegelF_alternating hq₁ hq₂ n)).1
  have he_im : ∀ n, ((-1) ^ n * iteratedDeriv n (siegelF χ₁ χ₂) 2).im = 0 := fun n ↦
    ((Complex.le_def.mp (iteratedDeriv_siegelF_alternating hq₁ hq₂ n)).2).symm
  have hfre : ∀ n, (f n).re = t ^ n * ((n ! : ℝ)⁻¹ * e n - G1.re) := by
    intro n
    rw [hfn n]
    have hre : ((n ! : ℂ)⁻¹ * ((-1) ^ n * iteratedDeriv n (siegelF χ₁ χ₂) 2) - G1).re =
        (n ! : ℝ)⁻¹ * e n - G1.re := by
      rw [Complex.sub_re, show ((n ! : ℂ)⁻¹) = (((n ! : ℝ)⁻¹ : ℝ) : ℂ) by push_cast; rfl,
        Complex.re_ofReal_mul]
    rw [show (t : ℂ) ^ n = ((t ^ n : ℝ) : ℂ) by push_cast; rfl, Complex.re_ofReal_mul, hre]
  have e0 : 1 ≤ e 0 := by
    have := one_le_siegelF_two (χ₁ := χ₁) (χ₂ := χ₂) hq₁ hq₂
    simp only [he, pow_zero, one_mul, iteratedDeriv_zero]
    exact (Complex.le_def.mp this).1
  -- real parts
  have hTre : HasSum (fun n ↦ (f n).re) (siegelH χ₁ χ₂ σ).re := Complex.hasSum_re hT
  have hsplit := Summable.sum_add_tsum_nat_add M hTre.summable
  rw [hTre.tsum_eq] at hsplit
  -- lower bound for the first `M` terms
  have hfirst : 1 - G1.re * ((t ^ M - 1) / (t - 1)) ≤ ∑ i ∈ Finset.range M, (f i).re := by
    simp_rw [hfre]
    have hgeom : ∑ i ∈ Finset.range M, t ^ i = (t ^ M - 1) / (t - 1) :=
      geom_sum_eq (by linarith) M
    have hpos : ∀ i ∈ Finset.range M, 0 ≤ t ^ i * ((i ! : ℝ)⁻¹ * e i) := fun i _ ↦
      mul_nonneg (by positivity) (mul_nonneg (by positivity) (he0 i))
    have h0 : t ^ 0 * ((0 ! : ℝ)⁻¹ * e 0) ≤ ∑ i ∈ Finset.range M, t ^ i * ((i ! : ℝ)⁻¹ * e i) :=
      Finset.single_le_sum hpos (Finset.mem_range.mpr (by omega))
    simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, inv_one, one_mul] at h0
    have : ∑ i ∈ Finset.range M, t ^ i * ((i ! : ℝ)⁻¹ * e i - G1.re) =
        ∑ i ∈ Finset.range M, t ^ i * ((i ! : ℝ)⁻¹ * e i) - G1.re * ∑ i ∈ Finset.range M, t ^ i := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ ↦ by ring
    rw [this, hgeom]
    linarith
  -- the tail, by Cauchy's inequality
  have hcauchy : ∀ n, ‖iteratedDeriv n (siegelH χ₁ χ₂) 2‖ ≤ n ! * K / (3 / 2) ^ n := fun n ↦
    Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n (by norm_num)
      hH.diffContOnCl hK
  set r : ℝ := t / (3 / 2) with hr
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r ≤ 5 / 6 := by rw [hr, div_le_iff₀ (by norm_num)]; linarith
  have hfnorm : ∀ n, ‖(f (n + M)).re‖ ≤ K * r ^ M * r ^ n := by
    intro n
    refine (Complex.abs_re_le_norm _).trans ?_
    simp only [hf, norm_smul, norm_inv, norm_pow, Complex.norm_natCast]
    rw [show (σ : ℂ) - 2 = ((σ - 2 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_neg (by linarith), show -(σ - 2) = t by rw [ht]; ring]
    have hfac : (0 : ℝ) < (n + M) ! := by exact_mod_cast Nat.factorial_pos _
    calc ((n + M) ! : ℝ)⁻¹ * (t ^ (n + M) * ‖iteratedDeriv (n + M) (siegelH χ₁ χ₂) 2‖)
        ≤ ((n + M) ! : ℝ)⁻¹ * (t ^ (n + M) * ((n + M) ! * K / (3 / 2) ^ (n + M))) := by
          gcongr; exact hcauchy _
      _ = K * (t ^ (n + M) / (3 / 2) ^ (n + M)) := by field_simp
      _ = K * r ^ M * r ^ n := by rw [hr, ← div_pow, mul_assoc, ← pow_add, add_comm M n]
  have hgeo : HasSum (fun n ↦ K * r ^ M * r ^ n) (K * r ^ M * (1 - r)⁻¹) :=
    (hasSum_geometric_of_lt_one hr0 (by linarith)).mul_left _
  have htail := tsum_of_norm_bounded hgeo hfnorm
  have htail' : K * r ^ M * (1 - r)⁻¹ ≤ 6 * K * (5 / 6) ^ M := by
    have h1 : (1 - r)⁻¹ ≤ 6 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
    have h2 : r ^ M ≤ (5 / 6) ^ M := pow_le_pow_left₀ hr0 hr1 M
    calc K * r ^ M * (1 - r)⁻¹ ≤ K * (5 / 6) ^ M * 6 :=
          mul_le_mul (mul_le_mul_of_nonneg_left h2 hK0) h1 (inv_nonneg.mpr (by linarith))
            (by positivity)
      _ = 6 * K * (5 / 6) ^ M := by ring
  have htail'' : -(6 * K * (5 / 6) ^ M) ≤ ∑' n, (f (n + M)).re := by
    have := (abs_le.mp (Real.norm_eq_abs _ ▸ htail)).1
    linarith
  -- `F(σ) = H(σ) + A/(σ - 1)`
  have hσne : (σ : ℂ) ≠ 1 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hFH : (siegelF χ₁ χ₂ σ).re = (siegelH χ₁ χ₂ σ).re - G1.re / (t - 1) := by
    rw [siegelH_eq hσne, ← hG1, Complex.sub_re,
      show (σ : ℂ) - 1 = ((σ - 1 : ℝ) : ℂ) by push_cast; ring, Complex.div_ofReal_re]
    have : t - 1 = -(σ - 1) := by rw [ht]; ring
    rw [this, div_neg]
    ring
  -- combine
  have hA : G1.re * (t ^ M / (t - 1)) ≤ ‖G1‖ * (t ^ M / (t - 1)) :=
    mul_le_mul_of_nonneg_right (Complex.re_le_norm _) (by positivity)
  have hcomb : G1.re * ((t ^ M - 1) / (t - 1)) + G1.re / (t - 1) = G1.re * (t ^ M / (t - 1)) := by
    have : t - 1 ≠ 0 := by linarith
    field_simp
    ring
  have ht1' : 1 - σ = t - 1 := by rw [ht]; ring
  rw [hFH, ← hsplit, ht1', mul_div_assoc]
  linarith

omit [NeZero q₁] [NeZero q₂] in
/-- A polynomial bound for `L(s, χ)` (Davenport, Ch. 12, (14), in the weak form used in Ch. 21):
there is an absolute `C` with `|L(s, χ)| ≤ C k` for `χ ≠ χ₀` mod `k`, `σ ≥ 1/2`, `|s| ≤ 4`. -/
lemma exists_norm_LFunction_le_level :
    ∃ C : ℝ, 0 < C ∧ ∀ {k : ℕ} [NeZero k] {χ : DirichletCharacter ℂ k}, χ ≠ 1 →
      ∀ s : ℂ, 1 / 2 ≤ s.re → ‖s‖ ≤ 4 → ‖χ.LFunction s‖ ≤ C * k := by
  have hZ := NTKB.Apostol.hasSum_rpow_riemannZeta (δ := 1 / 2) (by norm_num)
  set Z := (riemannZeta (1 + 1 / 2 : ℝ)).re with hZdef
  have hZ0 : 0 ≤ Z := hZ.nonneg fun n ↦ by positivity
  -- the bound away from `s = 1`
  have hmain : ∀ {k : ℕ} [NeZero k] {χ : DirichletCharacter ℂ k}, χ ≠ 1 →
      ∀ s : ℂ, 1 / 2 ≤ s.re → ‖s‖ ≤ 4 → s ≠ 1 → ‖χ.LFunction s‖ ≤ (3 + 4 * Z) * k := by
    intro k _ χ hχ s hσ hs4 hs1
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast NeZero.one_le
    have hb := norm_LFunction_le_euler hχ (s := s) (by linarith) hs1
    have h1 : ∑ n ∈ Finset.range k, ((n : ℝ) + 1) ^ (-s.re) ≤ k := by
      calc ∑ n ∈ Finset.range k, ((n : ℝ) + 1) ^ (-s.re) ≤ ∑ _n ∈ Finset.range k, (1 : ℝ) :=
            Finset.sum_le_sum fun n _ ↦
              Real.rpow_le_one_of_one_le_of_nonpos (by linarith [n.cast_nonneg (α := ℝ)])
                (by linarith)
        _ = k := by simp
    have h2 : (k : ℝ) ^ (1 - s.re) ≤ k := by
      calc (k : ℝ) ^ (1 - s.re) ≤ (k : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hk1 (by linarith)
        _ = k := Real.rpow_one _
    have h3 : ∑' n : ℕ, ((n : ℝ) + 1) ^ (-(1 + s.re)) ≤ Z := by
      have hle : ∀ n : ℕ, ((n : ℝ) + 1) ^ (-(1 + s.re)) ≤ ((n : ℝ) + 1) ^ (-(1 + 1 / 2 : ℝ)) :=
        fun n ↦ Real.rpow_le_rpow_of_exponent_le (by linarith [n.cast_nonneg (α := ℝ)])
          (by linarith)
      have hs : Summable fun n : ℕ ↦ ((n : ℝ) + 1) ^ (-(1 + s.re)) :=
        Summable.of_nonneg_of_le (fun n ↦ by positivity) hle hZ.summable
      exact hasSum_le hle hs.hasSum hZ
    have h4 : ‖s‖ * (k : ℝ) ^ (1 - s.re) * ∑' n : ℕ, ((n : ℝ) + 1) ^ (-(1 + s.re)) ≤
        4 * k * Z := by
      gcongr
    nlinarith
  refine ⟨3 + 4 * Z, by positivity, fun {k} _ {χ} hχ s hσ hs4 ↦ ?_⟩
  by_cases hs1 : s = 1
  · subst hs1
    have hlim := (Davenport.tendsto_LFunction_one hχ).norm
    refine le_of_tendsto hlim ?_
    have hev : ∀ᶠ x : ℝ in 𝓝[>] 1, x < 2 := by
      filter_upwards [Ioo_mem_nhdsGT (show (1 : ℝ) < 2 by norm_num)] with x hx using hx.2
    filter_upwards [hev, self_mem_nhdsWithin] with x hx2 hx1
    have hx1' : (1 : ℝ) < x := hx1
    refine hmain hχ x (by simp; linarith) ?_ ?_
    · rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]; linarith
    · intro h; have := congrArg Complex.re h; simp at this; linarith
  · exact hmain hχ s hσ hs4 hs1

omit [NeZero q₁] [NeZero q₂] in
lemma lcm_le_mul (hq₁ : q₁ ≠ 0) (hq₂ : q₂ ≠ 0) : (Nat.lcm q₁ q₂ : ℝ) ≤ q₁ * q₂ := by
  have := Nat.le_of_dvd (Nat.mul_pos (Nat.pos_of_ne_zero hq₁) (Nat.pos_of_ne_zero hq₂))
    (Nat.lcm_dvd_mul q₁ q₂)
  exact_mod_cast this

omit [NeZero q₁] [NeZero q₂] in
/-- The bound for `|G(s)|` on `σ ≥ 1/2`, `|s| ≤ 4`: `|G(s)| ≤ C³ (q₁ q₂)²`. -/
lemma exists_norm_siegelG_le :
    ∃ C : ℝ, 0 < C ∧ ∀ {q₁ q₂ : ℕ} [NeZero q₁] [NeZero q₂] {χ₁ : DirichletCharacter ℂ q₁}
      {χ₂ : DirichletCharacter ℂ q₂}, χ₁ ≠ 1 → χ₂ ≠ 1 → χ₁.mul χ₂ ≠ 1 →
      ∀ s : ℂ, 1 / 2 ≤ s.re → ‖s‖ ≤ 4 → ‖siegelG χ₁ χ₂ s‖ ≤ C * ((q₁ : ℝ) * q₂) ^ 2 := by
  obtain ⟨C, hC, h⟩ := exists_norm_LFunction_le_level
  refine ⟨C ^ 3, by positivity, fun {q₁ q₂} _ _ {χ₁ χ₂} h₁ h₂ h₁₂ s hσ hs ↦ ?_⟩
  have e1 := h h₁ s hσ hs
  have e2 := h h₂ s hσ hs
  have e3 := h h₁₂ s hσ hs
  have hl := lcm_le_mul (NeZero.ne q₁) (NeZero.ne q₂)
  rw [siegelG, norm_mul, norm_mul]
  calc ‖χ₁.LFunction s‖ * ‖χ₂.LFunction s‖ * ‖(χ₁.mul χ₂).LFunction s‖
      ≤ (C * q₁) * (C * q₂) * (C * Nat.lcm q₁ q₂) := by gcongr
    _ ≤ (C * q₁) * (C * q₂) * (C * (q₁ * q₂)) := by gcongr
    _ = C ^ 3 * ((q₁ : ℝ) * q₂) ^ 2 := by ring

/-- `ζ` is bounded on the circle `|s - 2| = 3/2`. -/
lemma exists_norm_riemannZeta_sphere_le :
    ∃ Z : ℝ, 0 ≤ Z ∧ ∀ z ∈ sphere (2 : ℂ) (3 / 2), ‖riemannZeta z‖ ≤ Z := by
  have hne : ∀ z ∈ sphere (2 : ℂ) (3 / 2), z ≠ 1 := by
    intro z hz h
    rw [h, mem_sphere, dist_eq_norm] at hz
    norm_num at hz
  have hc : ContinuousOn riemannZeta (sphere (2 : ℂ) (3 / 2)) := fun z hz ↦
    (differentiableAt_riemannZeta (hne z hz)).continuousAt.continuousWithinAt
  obtain ⟨Z, hZ⟩ := (isCompact_sphere (2 : ℂ) (3 / 2)).exists_bound_of_continuousOn hc
  exact ⟨max Z 0, le_max_right _ _, fun z hz ↦ (hZ z hz).trans (le_max_left _ _)⟩

omit [NeZero q₁] [NeZero q₂] in
/-- `|H| ≤ C (q₁ q₂)²` on the circle `|s - 2| = 3/2`. -/
lemma exists_norm_siegelH_sphere_le :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {q₁ q₂ : ℕ} [NeZero q₁] [NeZero q₂] {χ₁ : DirichletCharacter ℂ q₁}
      {χ₂ : DirichletCharacter ℂ q₂}, χ₁ ≠ 1 → χ₂ ≠ 1 → χ₁.mul χ₂ ≠ 1 →
      ∀ z ∈ sphere (2 : ℂ) (3 / 2), ‖siegelH χ₁ χ₂ z‖ ≤ C * ((q₁ : ℝ) * q₂) ^ 2 := by
  obtain ⟨CG, hCG, hG⟩ := exists_norm_siegelG_le
  obtain ⟨Z, hZ0, hZ⟩ := exists_norm_riemannZeta_sphere_le
  refine ⟨(Z + 2) * CG + 1, by nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ Z + 2) hCG.le], fun {q₁ q₂} _ _ {χ₁ χ₂} h₁ h₂ h₁₂ z hz ↦ ?_⟩
  have hz' := hz
  rw [mem_sphere, dist_eq_norm] at hz'
  have hz1 : z ≠ 1 := by
    rintro rfl; norm_num at hz'
  have hre : 1 / 2 ≤ z.re := by
    have := Complex.abs_re_le_norm (z - 2)
    rw [hz', Complex.sub_re, abs_le] at this
    norm_num at this; linarith [this.1]
  have hnorm : ‖z‖ ≤ 4 := by
    have := norm_add_le (z - 2) 2
    rw [sub_add_cancel, hz'] at this
    norm_num at this; linarith
  have hd : 1 / 2 ≤ ‖z - 1‖ := by
    have := norm_sub_norm_le (z - 2) (z - 1)
    rw [hz', show z - 2 - (z - 1) = -1 by ring, norm_neg, norm_one] at this
    linarith
  have hQ : 0 ≤ ((q₁ : ℝ) * q₂) ^ 2 := by positivity
  rw [siegelH_eq hz1, siegelF]
  have e1 := hG h₁ h₂ h₁₂ z hre hnorm
  have e2 := hG h₁ h₂ h₁₂ 1 (by norm_num) (by norm_num)
  calc ‖riemannZeta z * siegelG χ₁ χ₂ z - siegelG χ₁ χ₂ 1 / (z - 1)‖
      ≤ ‖riemannZeta z‖ * ‖siegelG χ₁ χ₂ z‖ + ‖siegelG χ₁ χ₂ 1‖ / ‖z - 1‖ := by
        rw [← norm_mul, ← norm_div]; exact norm_sub_le _ _
    _ ≤ Z * (CG * ((q₁ : ℝ) * q₂) ^ 2) + (CG * ((q₁ : ℝ) * q₂) ^ 2) / (1 / 2) := by
        gcongr
        exact hZ z hz
    _ ≤ ((Z + 2) * CG + 1) * ((q₁ : ℝ) * q₂) ^ 2 := by
        rw [div_eq_mul_inv]; nlinarith

/-- **Davenport, Ch. 21, p. 128, (8)** (Estermann): there are absolute constants `c, C > 0` such
that for real nonprincipal characters `χ₁` mod `q₁`, `χ₂` mod `q₂` with `χ₁ χ₂` nonprincipal,
and `3/4 ≤ σ < 1`,
`F(σ) ≥ 1/2 - C A (q₁ q₂)^{c (1 - σ)}/(1 - σ)`, `A = L(1, χ₁) L(1, χ₂) L(1, χ₁ χ₂)`. -/
@[kb "davenport1980" "Ch 21, p. 128, (8)"]
theorem estermann_inequality :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ {q₁ q₂ : ℕ} [NeZero q₁] [NeZero q₂]
      {χ₁ : DirichletCharacter ℂ q₁} {χ₂ : DirichletCharacter ℂ q₂},
      χ₁.IsQuadratic → χ₂.IsQuadratic → χ₁ ≠ 1 → χ₂ ≠ 1 → χ₁.mul χ₂ ≠ 1 →
      ∀ σ : ℝ, 3 / 4 ≤ σ → σ < 1 →
        1 / 2 - C * ‖siegelG χ₁ χ₂ 1‖ * ((q₁ : ℝ) * q₂) ^ (c * (1 - σ)) / (1 - σ) ≤
          (siegelF χ₁ χ₂ σ).re := by
  obtain ⟨C₀, hC₀, hH⟩ := exists_norm_siegelH_sphere_le
  set L := Real.log (6 / 5) with hL
  have hL0 : 0 < L := Real.log_pos (by norm_num)
  refine ⟨2 / L, Real.exp (1 / 4 + Real.log (12 * C₀) / (4 * L)), by positivity, by positivity,
    fun {q₁ q₂} _ _ {χ₁ χ₂} hq₁ hq₂ h₁ h₂ h₁₂ σ hσ hσ1 ↦ ?_⟩
  set x := 1 - σ with hx
  have hx0 : 0 < x := by rw [hx]; linarith
  have hx4 : x ≤ 1 / 4 := by rw [hx]; linarith
  set Q : ℝ := (q₁ : ℝ) * q₂ with hQ
  have hQ1 : 1 ≤ Q := by
    have : (1 : ℝ) ≤ q₁ := by exact_mod_cast NeZero.one_le
    have : (1 : ℝ) ≤ q₂ := by exact_mod_cast NeZero.one_le
    rw [hQ]; nlinarith
  set K := C₀ * Q ^ 2 with hK
  set K₁ := 12 * K with hK₁
  have hK₁1 : 12 ≤ K₁ := by
    have : 1 ≤ Q ^ 2 := one_le_pow₀ hQ1
    rw [hK₁, hK]; nlinarith
  have hlogK₁ : 0 < Real.log K₁ := Real.log_pos (by linarith)
  set M := ⌈Real.log K₁ / L⌉₊ with hM
  have hM1 : 1 ≤ M := Nat.one_le_iff_ne_zero.mpr (by
    rw [hM]; exact (Nat.ceil_pos.mpr (by positivity)).ne')
  have hMge : Real.log K₁ / L ≤ M := Nat.le_ceil _
  have hMle : (M : ℝ) ≤ Real.log K₁ / L + 1 := (Nat.ceil_lt_add_one (by positivity)).le
  have hstep := siegel_taylor_ge hq₁ hq₂ h₁ h₂ h₁₂ (K := K) (hH h₁ h₂ h₁₂) hσ hσ1 hM1
  -- the tail term is at most `1/2`
  have htail : 6 * K * (5 / 6 : ℝ) ^ M ≤ 1 / 2 := by
    have h1 : K₁ ≤ (6 / 5 : ℝ) ^ M := by
      rw [← Real.exp_log (by linarith : (0 : ℝ) < K₁), ← Real.rpow_natCast,
        Real.rpow_def_of_pos (by norm_num), ← hL]
      refine Real.exp_le_exp.mpr ?_
      rw [div_le_iff₀ hL0] at hMge; linarith
    have h2 : (5 / 6 : ℝ) ^ M = ((6 / 5 : ℝ) ^ M)⁻¹ := by rw [← inv_pow]; norm_num
    rw [h2]
    have h3 : 0 < (6 / 5 : ℝ) ^ M := by positivity
    rw [show 6 * K * ((6 / 5 : ℝ) ^ M)⁻¹ = K₁ / 2 / (6 / 5 : ℝ) ^ M by rw [hK₁]; field_simp; ring,
      div_le_iff₀ h3]
    linarith
  -- the main term
  have hpow : (2 - σ) ^ M ≤ Real.exp (1 / 4 + Real.log (12 * C₀) / (4 * L)) * Q ^ (2 / L * x) := by
    have e1 : (2 - σ) ^ M ≤ Real.exp (x * M) := by
      rw [show 2 - σ = x + 1 by rw [hx]; ring, mul_comm, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (by linarith) (Real.add_one_le_exp x) M
    have hlogK : Real.log K₁ = Real.log (12 * C₀) + 2 * Real.log Q := by
      rw [hK₁, hK, ← mul_assoc, Real.log_mul (by positivity) (by positivity), Real.log_pow]
      push_cast; ring
    have hlog12 : 0 ≤ Real.log (12 * C₀) := Real.log_nonneg (by linarith)
    have e2 : x * M ≤ (1 / 4 + Real.log (12 * C₀) / (4 * L)) + 2 / L * x * Real.log Q := by
      have := mul_le_mul_of_nonneg_left hMle hx0.le
      rw [hlogK] at this
      have h4 : x * (Real.log (12 * C₀) / L) ≤ Real.log (12 * C₀) / (4 * L) := by
        calc x * (Real.log (12 * C₀) / L) ≤ 1 / 4 * (Real.log (12 * C₀) / L) :=
              mul_le_mul_of_nonneg_right hx4 (div_nonneg hlog12 hL0.le)
          _ = Real.log (12 * C₀) / (4 * L) := by field_simp
      have h5 : x * ((Real.log (12 * C₀) + 2 * Real.log Q) / L + 1) =
          x * (Real.log (12 * C₀) / L) + 2 / L * x * Real.log Q + x := by
        field_simp
      linarith
    calc (2 - σ) ^ M ≤ Real.exp (x * M) := e1
      _ ≤ Real.exp ((1 / 4 + Real.log (12 * C₀) / (4 * L)) + 2 / L * x * Real.log Q) :=
          Real.exp_le_exp.mpr e2
      _ = _ := by
          rw [Real.exp_add, Real.rpow_def_of_pos (by linarith)]
          ring_nf
  have hA : ‖siegelG χ₁ χ₂ 1‖ * (2 - σ) ^ M / (1 - σ) ≤
      Real.exp (1 / 4 + Real.log (12 * C₀) / (4 * L)) * ‖siegelG χ₁ χ₂ 1‖ *
        Q ^ (2 / L * (1 - σ)) / (1 - σ) := by
    rw [← hx]
    have := mul_le_mul_of_nonneg_left hpow (norm_nonneg (siegelG χ₁ χ₂ 1))
    rw [div_le_div_iff_of_pos_right hx0]
    linarith
  linarith

end NTKB.Davenport
