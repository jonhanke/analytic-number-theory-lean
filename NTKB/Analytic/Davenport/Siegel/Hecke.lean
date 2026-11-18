/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Davenport.Siegel.Siegel
import NTKB.Analytic.Davenport.ClassNumber.Unconditional

/-!
# Hecke's class number bound and Landau's deduction (Davenport, Chapter 21)

Davenport (Ch. 21, p. 127) cites without proof Hecke's theorem: if the real zeros of the
L-functions of real primitive characters satisfy `β < 1 - c/log q`, then
`h(d) > c' |d|^{1/2} / log |d|`; and (footnote, p. 127) Landau's argument, which by the same method
deduces the first form (1) of Siegel's theorem from the second form (D).

Both follow from the one-character form of Estermann's inequality (Davenport (8), p. 128, with
`F(s) = ζ(s) L(s, χ)` in place of `ζ(s) L(s, χ₁) L(s, χ₂) L(s, χ₁ χ₂)`): the coefficients of
`ζ(s) L(s, χ)` are `∑_{d ∣ n} χ(d) ≥ 0` (Mathlib `DirichletCharacter.zetaMul_nonneg`), so the
Taylor argument of `NTKB.Davenport.siegel_taylor_ge` gives
`F(σ) ≥ 1/2 - C L(1, χ) q^{c (1 - σ)}/(1 - σ)` for `3/4 ≤ σ < 1` (`hecke_inequality`). If
`L(σ, χ)` has no zero in `(1 - δ, 1)` then `F(σ) < 0` there (`ζ(σ) < 0`, `L(σ, χ) > 0`), so
`L(1, χ) ≫ δ q^{-c δ}` (`LFunction_one_ge_of_no_real_zero`). With `δ = c₂/log q` this is Hecke's
`L(1, χ) ≫ 1/log q` and, by the class number formula, `h(d) ≫ |d|^{1/2}/log |d|`
(`classNumber_gt_of_no_real_zero`); with `δ = C q^{-ε}` it is Landau's deduction
(`siegel_of_second_form`).

* `heckeF χ s = ζ(s) L(s, χ)`, `heckeH` the entire function `F(s) - L(1, χ)/(s - 1)`.
* `hecke_inequality`: the one-character inequality (8).
* `LFunction_one_ge_of_no_real_zero`: `L(1, χ) ≥ C δ q^{-c δ}` if `L(σ, χ) ≠ 0` on `(1 - δ, 1)`.
* `LFunction_one_gt_div_log_of_no_real_zero`: **Hecke**, `L(1, χ) > C/log q`.
* `classNumber_gt_of_no_real_zero`, `classNumber_mul_regulator_gt_of_no_real_zero`:
  **Hecke's class number bound (Davenport, Ch. 21, p. 127)** for `d < 0` and `d > 0`.
* `siegel_of_second_form`: **Landau's deduction (Davenport, Ch. 21, p. 127, footnote)**: the second
  form (D) of Siegel's theorem implies the first form (1).
* `LFunction_one_ge_of_real_zero_lt_unconditional`: with the real-zero bound now in the library
  (row 14-18, `β < 1 - c/(q^{1/2} log² q)`) the same lemma gives only
  `L(1, χ) ≥ C/(q^{1/2} log² q)`; Hecke's bound needs the interval `(1 - c/log q, 1)`.
-/

open Complex Filter Topology Set Metric
open scoped ComplexOrder Nat

namespace NTKB.Davenport

variable {q : ℕ} [NeZero q]

/-- `F(s) = ζ(s) L(s, χ)`. -/
noncomputable def heckeF (χ : DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  riemannZeta s * χ.LFunction s

/-- The entire function `F(s) - L(1, χ)/(s - 1)`. -/
noncomputable def heckeH (χ : DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  riemannZeta₀ s * χ.LFunction s + dslope χ.LFunction 1 s

variable {χ : DirichletCharacter ℂ q}

lemma differentiable_heckeH (h : χ ≠ 1) : Differentiable ℂ (heckeH χ) := by
  have hG := DirichletCharacter.differentiable_LFunction h
  have hd : Differentiable ℂ (dslope χ.LFunction 1) := by
    rw [← differentiableOn_univ]
    exact (differentiableOn_dslope Filter.univ_mem).2 hG.differentiableOn
  exact (differentiable_riemannZeta₀.mul hG).add hd

/-- `H(s) = F(s) - L(1, χ)/(s - 1)` for `s ≠ 1`. -/
lemma heckeH_eq {s : ℂ} (hs : s ≠ 1) :
    heckeH χ s = heckeF χ s - χ.LFunction 1 / (s - 1) := by
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  rw [heckeH, heckeF, dslope_of_ne _ hs, slope_def_field, riemannZeta_eq_inv_sub_add hs]
  simp only [riemannZeta₀, if_neg hs]
  field_simp
  ring

lemma heckeF_hasSum {s : ℂ} (hs : 1 < s.re) :
    LSeriesHasSum (χ.zetaMul ·) s (heckeF χ s) :=
  NTKB.DirichletCharacter.LSeriesHasSum_zetaMul χ hs

lemma heckeF_eq_LSeries {s : ℂ} (hs : 1 < s.re) :
    heckeF χ s = LSeries (χ.zetaMul ·) s :=
  (heckeF_hasSum hs).LSeries_eq.symm

lemma abscissa_zetaMul_le :
    LSeries.abscissaOfAbsConv (χ.zetaMul ·) ≤ 1 := by
  refine LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy ↦ ?_
  exact (heckeF_hasSum (χ := χ) (s := (y : ℂ)) (by simpa using hy)).LSeriesSummable

omit [NeZero q] in
lemma sq_eq_one_of_isQuadratic' (hq : χ.IsQuadratic) : χ ^ 2 = 1 :=
  MulChar.isQuadratic_iff_sq_eq_one.mp hq

lemma iteratedDeriv_heckeF_alternating (hq : χ.IsQuadratic) (m : ℕ) :
    0 ≤ (-1) ^ m * iteratedDeriv m (heckeF χ) 2 := by
  have hU : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const continuous_re
  have heq : EqOn (heckeF χ) (LSeries (χ.zetaMul ·)) {s : ℂ | 1 < s.re} :=
    fun s hs ↦ heckeF_eq_LSeries hs
  have h2 : (2 : ℂ) ∈ {s : ℂ | 1 < s.re} := by show (1 : ℝ) < (2 : ℂ).re; norm_num
  rw [heq.iteratedDeriv_of_isOpen hU m h2]
  have := LSeries.iteratedDeriv_alternating (a := (χ.zetaMul ·))
    (fun n ↦ DirichletCharacter.zetaMul_nonneg (sq_eq_one_of_isQuadratic' hq) n)
    (x := 2) (abscissa_zetaMul_le.trans_lt (by exact_mod_cast (show (1 : ℝ) < 2 by norm_num))) m
  simpa using this

lemma one_le_heckeF_two (hq : χ.IsQuadratic) : 1 ≤ heckeF χ 2 := by
  have hs : 1 < (2 : ℂ).re := by simp
  have h := heckeF_hasSum (χ := χ) hs
  have hnn : ∀ n, 0 ≤ LSeries.term (χ.zetaMul ·) 2 n :=
    fun n ↦ LSeries.term_nonneg
      (DirichletCharacter.zetaMul_nonneg (sq_eq_one_of_isQuadratic' hq) n) 2
  have h1 : LSeries.term (χ.zetaMul ·) 2 1 = 1 := by
    simp [LSeries.term, χ.isMultiplicative_zetaMul.map_one]
  rw [← h1]
  exact le_hasSum h 1 (fun j _ ↦ hnn j)

/-- `F^{(m)}(2) = H^{(m)}(2) + A (-1)^m m!` (the Taylor coefficients of `A/(s - 1)` at `2`). -/
lemma iteratedDeriv_heckeF_two (h : χ ≠ 1) (m : ℕ) :
    iteratedDeriv m (heckeF χ) 2 =
      iteratedDeriv m (heckeH χ) 2 + χ.LFunction 1 * ((-1) ^ m * m !) := by
  have hU : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const continuous_re
  have h2 : (2 : ℂ) ∈ {s : ℂ | 1 < s.re} := by show (1 : ℝ) < (2 : ℂ).re; norm_num
  have heq : EqOn (heckeF χ)
      (fun s ↦ heckeH χ s + χ.LFunction 1 * (s - 1)⁻¹) {s : ℂ | 1 < s.re} := by
    intro s hs
    have hs1 : s ≠ 1 := by
      rintro rfl; simp at hs
    simp only
    rw [heckeH_eq hs1]
    ring
  rw [heq.iteratedDeriv_of_isOpen hU m h2]
  have hH : ContDiffAt ℂ m (heckeH χ) 2 :=
    (differentiable_heckeH h).contDiff.contDiffAt
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
lemma hecke_taylor_ge (hq : χ.IsQuadratic) (h : χ ≠ 1) {K : ℝ}
    (hK : ∀ z ∈ sphere (2 : ℂ) (3 / 2), ‖heckeH χ z‖ ≤ K) {σ : ℝ} (hσ : 3 / 4 ≤ σ)
    (hσ1 : σ < 1) {M : ℕ} (hM : 1 ≤ M) :
    1 - ‖χ.LFunction 1‖ * (2 - σ) ^ M / (1 - σ) - 6 * K * (5 / 6) ^ M ≤
      (heckeF χ σ).re := by
  have hH := differentiable_heckeH h
  set G1 := χ.LFunction 1 with hG1
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
  set f : ℕ → ℂ := fun n ↦ (n ! : ℂ)⁻¹ • ((σ : ℂ) - 2) ^ n • iteratedDeriv n (heckeH χ) 2
    with hf
  -- the terms
  have hfn : ∀ n, f n = (t : ℂ) ^ n *
      ((n ! : ℂ)⁻¹ * ((-1) ^ n * iteratedDeriv n (heckeF χ) 2) - G1) := by
    intro n
    simp only [hf, smul_eq_mul]
    rw [iteratedDeriv_heckeF_two h n, ← hG1]
    have hσt : (σ : ℂ) - 2 = -(t : ℂ) := by rw [ht]; push_cast; ring
    rw [hσt, neg_pow]
    have hfac : (n ! : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
    have hinv : (n ! : ℂ)⁻¹ * n ! = 1 := inv_mul_cancel₀ hfac
    set u : ℂ := (-1) ^ n
    have hu : u * u = 1 := by simp only [u]; rw [← mul_pow]; norm_num
    linear_combination (-(t : ℂ) ^ n * G1 * u * u) * hinv + (-(t : ℂ) ^ n * G1) * hu
  set e : ℕ → ℝ := fun n ↦ ((-1) ^ n * iteratedDeriv n (heckeF χ) 2).re with he
  have he0 : ∀ n, 0 ≤ e n := fun n ↦
    (Complex.le_def.mp (iteratedDeriv_heckeF_alternating hq n)).1
  have he_im : ∀ n, ((-1) ^ n * iteratedDeriv n (heckeF χ) 2).im = 0 := fun n ↦
    ((Complex.le_def.mp (iteratedDeriv_heckeF_alternating hq n)).2).symm
  have hfre : ∀ n, (f n).re = t ^ n * ((n ! : ℝ)⁻¹ * e n - G1.re) := by
    intro n
    rw [hfn n]
    have hre : ((n ! : ℂ)⁻¹ * ((-1) ^ n * iteratedDeriv n (heckeF χ) 2) - G1).re =
        (n ! : ℝ)⁻¹ * e n - G1.re := by
      rw [Complex.sub_re, show ((n ! : ℂ)⁻¹) = (((n ! : ℝ)⁻¹ : ℝ) : ℂ) by push_cast; rfl,
        Complex.re_ofReal_mul]
    rw [show (t : ℂ) ^ n = ((t ^ n : ℝ) : ℂ) by push_cast; rfl, Complex.re_ofReal_mul, hre]
  have e0 : 1 ≤ e 0 := by
    have := one_le_heckeF_two hq
    simp only [he, pow_zero, one_mul, iteratedDeriv_zero]
    exact (Complex.le_def.mp this).1
  -- real parts
  have hTre : HasSum (fun n ↦ (f n).re) (heckeH χ σ).re := Complex.hasSum_re hT
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
  have hcauchy : ∀ n, ‖iteratedDeriv n (heckeH χ) 2‖ ≤ n ! * K / (3 / 2) ^ n := fun n ↦
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
    calc ((n + M) ! : ℝ)⁻¹ * (t ^ (n + M) * ‖iteratedDeriv (n + M) (heckeH χ) 2‖)
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
  have hFH : (heckeF χ σ).re = (heckeH χ σ).re - G1.re / (t - 1) := by
    rw [heckeH_eq hσne, ← hG1, Complex.sub_re,
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

omit [NeZero q] in
/-- `|L(s, χ)| ≤ C q` on `σ ≥ 1/2`, `|s| ≤ 4`, in the form `≤ C q²` used below. -/
lemma exists_norm_heckeH_sphere_le :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}, χ ≠ 1 →
      ∀ z ∈ sphere (2 : ℂ) (3 / 2), ‖heckeH χ z‖ ≤ C * (q : ℝ) ^ 2 := by
  obtain ⟨CG, hCG, hG⟩ := exists_norm_LFunction_le_level
  obtain ⟨Z, hZ0, hZ⟩ := exists_norm_riemannZeta_sphere_le
  refine ⟨(Z + 2) * CG + 1, by nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ Z + 2) hCG.le],
    fun {q} _ {χ} h z hz ↦ ?_⟩
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
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.one_le
  have hQ : (q : ℝ) ≤ (q : ℝ) ^ 2 := by nlinarith
  have hQ0 : 0 ≤ (q : ℝ) ^ 2 := by positivity
  rw [heckeH_eq hz1, heckeF]
  have e1 := hG h z hre hnorm
  have e2 := hG h 1 (by norm_num) (by norm_num)
  have e1' : ‖χ.LFunction z‖ ≤ CG * (q : ℝ) ^ 2 := e1.trans (by gcongr)
  have e2' : ‖χ.LFunction 1‖ ≤ CG * (q : ℝ) ^ 2 := e2.trans (by gcongr)
  calc ‖riemannZeta z * χ.LFunction z - χ.LFunction 1 / (z - 1)‖
      ≤ ‖riemannZeta z‖ * ‖χ.LFunction z‖ + ‖χ.LFunction 1‖ / ‖z - 1‖ := by
        rw [← norm_mul, ← norm_div]; exact norm_sub_le _ _
    _ ≤ Z * (CG * (q : ℝ) ^ 2) + (CG * (q : ℝ) ^ 2) / (1 / 2) := by
        gcongr
        exact hZ z hz
    _ ≤ ((Z + 2) * CG + 1) * (q : ℝ) ^ 2 := by
        rw [div_eq_mul_inv]; nlinarith

/-- **Davenport, Ch. 21, (8), for one character**: there are absolute constants `c, C > 0` such
that for every real nonprincipal character `χ` mod `q` and `3/4 ≤ σ < 1`,
`ζ(σ) L(σ, χ) ≥ 1/2 - C |L(1, χ)| q^{c (1 - σ)}/(1 - σ)`. -/
theorem hecke_inequality :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q},
      χ.IsQuadratic → χ ≠ 1 → ∀ σ : ℝ, 3 / 4 ≤ σ → σ < 1 →
        1 / 2 - C * ‖χ.LFunction 1‖ * (q : ℝ) ^ (c * (1 - σ)) / (1 - σ) ≤ (heckeF χ σ).re := by
  obtain ⟨C₀, hC₀, hH⟩ := exists_norm_heckeH_sphere_le
  set L := Real.log (6 / 5) with hL
  have hL0 : 0 < L := Real.log_pos (by norm_num)
  refine ⟨2 / L, Real.exp (1 / 4 + Real.log (12 * C₀) / (4 * L)), by positivity, by positivity,
    fun {q} _ {χ} hq h σ hσ hσ1 ↦ ?_⟩
  set x := 1 - σ with hx
  have hx0 : 0 < x := by rw [hx]; linarith
  have hx4 : x ≤ 1 / 4 := by rw [hx]; linarith
  set Q : ℝ := (q : ℝ) with hQ
  have hQ1 : 1 ≤ Q := by
    rw [hQ]; exact_mod_cast NeZero.one_le
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
  have hstep := hecke_taylor_ge hq h (K := K) (hH h) hσ hσ1 hM1
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
  have hA : ‖χ.LFunction 1‖ * (2 - σ) ^ M / (1 - σ) ≤
      Real.exp (1 / 4 + Real.log (12 * C₀) / (4 * L)) * ‖χ.LFunction 1‖ *
        Q ^ (2 / L * (1 - σ)) / (1 - σ) := by
    rw [← hx]
    have := mul_le_mul_of_nonneg_left hpow (norm_nonneg (χ.LFunction 1))
    rw [div_le_div_iff_of_pos_right hx0]
    linarith
  linarith

/-- **The zero-free interval gives a lower bound for `L(1, χ)`** (Hecke, Landau; Davenport, Ch. 21,
p. 127): there are absolute `c, C > 0` such that if `χ` is a real nonprincipal character mod `q`,
`0 < δ ≤ 1/4` and `L(σ, χ) ≠ 0` for `1 - δ < σ < 1`, then `L(1, χ) ≥ C δ q^{-c δ}`. -/
@[kb "davenport1980" "Ch 21, p. 127"]
theorem LFunction_one_ge_of_no_real_zero :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q},
      χ.IsQuadratic → χ ≠ 1 → ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 4 →
        (∀ σ : ℝ, 1 - δ < σ → σ < 1 → χ.LFunction σ ≠ 0) →
          C * δ * (q : ℝ) ^ (-(c * δ)) ≤ (χ.LFunction 1).re := by
  obtain ⟨c, C, hc, hC, hest⟩ := hecke_inequality
  refine ⟨c, 1 / (4 * C), hc, by positivity, fun {q} _ {χ} hq hχ δ hδ0 hδ4 hfree ↦ ?_⟩
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.one_le
  have hq0 : (0 : ℝ) < q := by linarith
  set σ : ℝ := 1 - δ / 2 with hσ
  have hσ34 : 3 / 4 ≤ σ := by rw [hσ]; linarith
  have hσ1 : σ < 1 := by rw [hσ]; linarith
  have hgt : 1 - δ < σ := by rw [hσ]; linarith
  have hfree' : ∀ τ : ℝ, 1 - δ < τ → τ < 1 → χ.LFunction τ ≠ 0 := hfree
  have hp := LFunction_re_pos_of_no_zero hq hχ hfree' hgt hσ1.le
  have hz := NTKB.Apostol.riemannZeta_neg_of_lt_one (σ := σ) (by linarith) hσ1
  have hF : (heckeF χ σ).re < 0 := by
    rw [heckeF, eq_ofReal_re_of_im_eq_zero hz.1,
      eq_ofReal_re_of_im_eq_zero (LFunction_ofReal_im hq hχ σ)]
    simp only [← Complex.ofReal_mul, Complex.ofReal_re]
    nlinarith [hz.2]
  have h8 := hest hq hχ σ hσ34 hσ1
  have hLpos := Davenport.LFunction_one_pos_of_isQuadratic hq hχ
  have hLre : 0 < (χ.LFunction 1).re := (Complex.lt_def.mp hLpos).1
  have hL2 : ‖χ.LFunction 1‖ = (χ.LFunction 1).re := by
    rw [eq_ofReal_re_of_im_eq_zero (z := χ.LFunction 1) (by simpa using LFunction_ofReal_im hq hχ 1)]
    rw [Complex.norm_real, Complex.ofReal_re, Real.norm_of_nonneg hLre.le]
  rw [hL2, show 1 - σ = δ / 2 by rw [hσ]; ring] at h8
  set R := (χ.LFunction 1).re with hR
  set P : ℝ := (q : ℝ) ^ (c * (δ / 2)) with hP
  have hP0 : 0 < P := Real.rpow_pos_of_pos hq0 _
  have h9 : 1 / 2 < C * R * P / (δ / 2) := by linarith
  rw [lt_div_iff₀ (by positivity)] at h9
  have hneg : (q : ℝ) ^ (-(c * δ)) ≤ P⁻¹ := by
    rw [Real.rpow_neg hq0.le, hP]
    refine inv_anti₀ hP0 (Real.rpow_le_rpow_of_exponent_le hq1 ?_)
    have : 0 ≤ c * δ := by positivity
    linarith
  calc 1 / (4 * C) * δ * (q : ℝ) ^ (-(c * δ)) ≤ 1 / (4 * C) * δ * P⁻¹ := by gcongr
    _ = δ / (4 * C * P) := by field_simp
    _ ≤ R := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith

/-- **Hecke (Davenport, Ch. 21, p. 127)**, the L-function form: for every `c₂ > 0` there is
`C > 0` such that if `χ` is a real nonprincipal character mod `q` and `L(σ, χ) ≠ 0` for
`1 - c₂/log q < σ < 1`, then `L(1, χ) > C/log q`. -/
@[kb "davenport1980" "Ch 21, p. 127"]
theorem LFunction_one_gt_div_log_of_no_real_zero {c₂ : ℝ} (hc₂ : 0 < c₂) :
    ∃ C : ℝ, 0 < C ∧ ∀ {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q},
      χ.IsQuadratic → χ ≠ 1 →
        (∀ σ : ℝ, 1 - c₂ / Real.log q < σ → σ < 1 → χ.LFunction σ ≠ 0) →
          C / Real.log q < (χ.LFunction 1).re := by
  obtain ⟨c, C, hc, hC, hge⟩ := LFunction_one_ge_of_no_real_zero
  set m : ℝ := min (1 / 4) c₂ with hm
  have hm0 : 0 < m := lt_min (by norm_num) hc₂
  have hm4 : m ≤ 1 / 4 := min_le_left _ _
  have hmc : m ≤ c₂ := min_le_right _ _
  refine ⟨C * m * Real.exp (-(c / 4)) / 2, by positivity, fun {q} _ {χ} hq hχ hfree ↦ ?_⟩
  have hq3 : (3 : ℝ) ≤ q := by exact_mod_cast three_le_of_ne_one hχ
  have hq0 : (0 : ℝ) < q := by linarith
  have hlog1 : 1 < Real.log q := by
    rw [Real.lt_log_iff_exp_lt hq0]
    have := Real.exp_one_lt_d9
    linarith
  have hlog0 : 0 < Real.log q := by linarith
  set δ : ℝ := m / Real.log q with hδ
  have hδ0 : 0 < δ := by positivity
  have hδm : δ ≤ m := by
    rw [hδ, div_le_iff₀ hlog0]; nlinarith
  have hδc : δ ≤ c₂ / Real.log q := by
    rw [hδ]; gcongr
  have hfree' : ∀ σ : ℝ, 1 - δ < σ → σ < 1 → χ.LFunction σ ≠ 0 := by
    intro σ h1 h2
    refine hfree σ ?_ h2
    linarith
  have hR := hge hq hχ δ hδ0 (hδm.trans hm4) hfree'
  have hexp : Real.exp (-(c / 4)) ≤ (q : ℝ) ^ (-(c * δ)) := by
    rw [Real.rpow_def_of_pos hq0, Real.exp_le_exp]
    have : Real.log q * (c * δ) = c * m := by rw [hδ]; field_simp
    have h2 : c * m ≤ c / 4 := by nlinarith
    nlinarith
  calc C * m * Real.exp (-(c / 4)) / 2 / Real.log q
      < C * m * Real.exp (-(c / 4)) / Real.log q := by
        have h0 : 0 < C * m * Real.exp (-(c / 4)) := by positivity
        rw [div_div, div_lt_div_iff_of_pos_left h0 (by positivity) hlog0]
        linarith
    _ = C * δ * Real.exp (-(c / 4)) := by rw [hδ]; ring
    _ ≤ C * δ * (q : ℝ) ^ (-(c * δ)) := by gcongr
    _ ≤ _ := hR

open Module NumberField NumberField.InfinitePlace NumberField.Units in
/-- **Hecke's class number bound (Davenport, Ch. 21, p. 127), `d < 0`**: for every `c₂ > 0` there
is `C > 0` such that for every imaginary quadratic field of discriminant `d` whose Kronecker
character `χ_d` has no real zero in `1 - c₂/log |d| < σ < 1`,
`h(d) > C |d|^{1/2} / log |d|`. -/
@[kb "davenport1980" "Ch 21, p. 127"]
theorem classNumber_gt_of_no_real_zero {c₂ : ℝ} (hc₂ : 0 < c₂) :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : Type) [Field K] [NumberField K], finrank ℚ K = 2 → discr K < 0 →
      (∀ σ : ℝ, 1 - c₂ / Real.log |(discr K : ℝ)| < σ → σ < 1 →
        (kroneckerChar (discr K)).LFunction σ ≠ 0) →
      C * √|(discr K : ℝ)| / Real.log |(discr K : ℝ)| < classNumber K := by
  obtain ⟨C₁, hC₁, hS⟩ := LFunction_one_gt_div_log_of_no_real_zero hc₂
  refine ⟨C₁ / Real.pi, by positivity, fun K _ _ hK hD hz ↦ ?_⟩
  have hfund := quadraticFieldDiscriminants.isFundamental K hK
  rw [abs_discr_eq_natAbs] at hz ⊢
  have hL := hS (kroneckerChar_isQuadratic hfund) (kroneckerChar_discr_ne_one_unconditional hK) hz
  rw [LFunction_one_re_eq_residue_unconditional hK, dedekindZeta_residue_of_discr_neg hK hD,
    ← abs_discr_eq_natAbs] at hL
  rw [← abs_discr_eq_natAbs]
  set a := |(discr K : ℝ)|
  have ha : 0 < a := abs_pos.mpr (Int.cast_ne_zero.mpr (discr_ne_zero K))
  have ha1 : 1 ≤ a := by
    have h : a = ((discr K).natAbs : ℝ) := abs_discr_eq_natAbs
    rw [h]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by simpa using discr_ne_zero K)
  have hlog : 0 ≤ Real.log a := Real.log_nonneg ha1
  have hs : 0 < √a := Real.sqrt_pos.mpr ha
  have hw2 : (2 : ℝ) ≤ torsionOrder K := by
    rcases torsionOrder_eq_two_or_four_or_six hK with h | h | h <;> rw [h] <;> norm_num
  have hw0 : (0 : ℝ) < torsionOrder K := by linarith
  have hu : 0 ≤ C₁ / Real.log a := by positivity
  rw [lt_div_iff₀ (by positivity)] at hL
  have h1 : C₁ / Real.log a * √a * 2 ≤ C₁ / Real.log a * (torsionOrder K * √a) := by
    have := mul_le_mul_of_nonneg_left hw2 (by positivity : (0 : ℝ) ≤ C₁ / Real.log a * √a)
    nlinarith
  have e : C₁ / Real.pi * √a / Real.log a = C₁ / Real.log a * √a / Real.pi := by ring
  rw [e, div_lt_iff₀ Real.pi_pos]
  nlinarith

open Module NumberField NumberField.InfinitePlace NumberField.Units in
/-- **Hecke's bound, `d > 0`**: under the same hypothesis, `h(d) R > C d^{1/2} / log d`. -/
@[kb "davenport1980" "Ch 21, p. 127"]
theorem classNumber_mul_regulator_gt_of_no_real_zero {c₂ : ℝ} (hc₂ : 0 < c₂) :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : Type) [Field K] [NumberField K], finrank ℚ K = 2 → 0 < discr K →
      (∀ σ : ℝ, 1 - c₂ / Real.log (discr K : ℝ) < σ → σ < 1 →
        (kroneckerChar (discr K)).LFunction σ ≠ 0) →
      C * √(discr K : ℝ) / Real.log (discr K : ℝ) < classNumber K * regulator K := by
  obtain ⟨C₁, hC₁, hS⟩ := LFunction_one_gt_div_log_of_no_real_zero hc₂
  refine ⟨C₁ / 2, by positivity, fun K _ _ hK hD hz ↦ ?_⟩
  have hfund := quadraticFieldDiscriminants.isFundamental K hK
  have hn : ((discr K).natAbs : ℝ) = (discr K : ℝ) := by
    rw [Nat.cast_natAbs, Int.cast_abs, abs_of_pos (by exact_mod_cast hD)]
  rw [← hn] at hz
  have hL := hS (kroneckerChar_isQuadratic hfund) (kroneckerChar_discr_ne_one_unconditional hK) hz
  rw [LFunction_one_re_eq_residue_unconditional hK, dedekindZeta_residue_of_discr_pos hK hD,
    hn] at hL
  have ha : 0 < (discr K : ℝ) := Int.cast_pos.mpr hD
  set a := (discr K : ℝ)
  have ha1 : 1 ≤ a := by have : (1 : ℤ) ≤ discr K := hD; show (1 : ℝ) ≤ (discr K : ℝ); exact_mod_cast this
  have hlog : 0 ≤ Real.log a := Real.log_nonneg ha1
  have hs : 0 < √a := Real.sqrt_pos.mpr ha
  rw [lt_div_iff₀ hs] at hL
  have hu : 0 ≤ C₁ / Real.log a := by positivity
  have e : C₁ / 2 * √a / Real.log a = C₁ / Real.log a * √a / 2 := by ring
  rw [e, div_lt_iff₀ (by norm_num)]
  nlinarith

/-- **Landau's deduction (Davenport, Ch. 21, p. 127, footnote)**: the second form (D) of Siegel's
theorem (for every `ε > 0`, `L(σ, χ) ≠ 0` for `σ > 1 - C₃(ε) q^{-ε}`, `χ` real nonprincipal
mod `q`) implies the first form (1) (`L(1, χ) > C₁(ε) q^{-ε}`). Stated as an implication between
the two statements, without using that either is proved (`siegel_second_form`, `siegel`). -/
@[kb "davenport1980" "Ch 21, p. 127"]
theorem siegel_of_second_form
    (hD : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q},
      χ.IsQuadratic → χ ≠ 1 → ∀ σ : ℝ, 1 - C * (q : ℝ) ^ (-ε) < σ → χ.LFunction σ ≠ 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q},
      χ.IsQuadratic → χ ≠ 1 → C * (q : ℝ) ^ (-ε) < (χ.LFunction 1).re := by
  obtain ⟨c, C, hc, hC, hge⟩ := LFunction_one_ge_of_no_real_zero
  obtain ⟨C₃, hC₃, hD'⟩ := hD (ε / 2) (half_pos hε)
  set m : ℝ := min (1 / 4) C₃ with hm
  have hm0 : 0 < m := lt_min (by norm_num) hC₃
  have hm4 : m ≤ 1 / 4 := min_le_left _ _
  have hmC : m ≤ C₃ := min_le_right _ _
  set E : ℝ := Real.exp (-(2 * c * C₃ / ε)) with hE
  have hE0 : 0 < E := Real.exp_pos _
  refine ⟨C * m * E / 2, by positivity, fun {q} _ {χ} hq hχ ↦ ?_⟩
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.one_le
  have hq0 : (0 : ℝ) < q := by linarith
  set x : ℝ := (q : ℝ) ^ (-(ε / 2)) with hx
  have hx0 : 0 < x := Real.rpow_pos_of_pos hq0 _
  have hx1 : x ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hq1 (by linarith)
  set δ : ℝ := min (1 / 4) (C₃ * x) with hδ
  have hδ0 : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδ4 : δ ≤ 1 / 4 := min_le_left _ _
  have hδC : δ ≤ C₃ * x := min_le_right _ _
  have hfree : ∀ σ : ℝ, 1 - δ < σ → σ < 1 → χ.LFunction σ ≠ 0 := by
    intro σ h1 _
    exact hD' hq hχ σ (by linarith)
  have hR := hge hq hχ δ hδ0 hδ4 hfree
  have hmx : m * x ≤ δ := by
    refine le_min ?_ ?_
    · nlinarith
    · exact mul_le_mul_of_nonneg_right hmC hx0.le
  have hxq : x * (q : ℝ) ^ (ε / 2) = 1 := by
    rw [hx, ← Real.rpow_add hq0]; simp
  have hlogq : x * Real.log q ≤ 2 / ε := by
    have h1 := Real.log_le_rpow_div hq0.le (half_pos hε)
    calc x * Real.log q ≤ x * ((q : ℝ) ^ (ε / 2) / (ε / 2)) := by gcongr
      _ = 2 / ε := by
        rw [← mul_div_assoc, hxq]; field_simp
  have hexp : E ≤ (q : ℝ) ^ (-(c * δ)) := by
    rw [hE, Real.rpow_def_of_pos hq0, Real.exp_le_exp]
    have h1 : δ * Real.log q ≤ C₃ * (x * Real.log q) := by
      have := mul_le_mul_of_nonneg_right hδC (Real.log_nonneg hq1)
      linarith
    have h2 : C₃ * (x * Real.log q) ≤ C₃ * (2 / ε) := by gcongr
    have h3 : c * (δ * Real.log q) ≤ c * (C₃ * (2 / ε)) := mul_le_mul_of_nonneg_left (h1.trans h2) hc.le
    have h4 : c * (C₃ * (2 / ε)) = 2 * c * C₃ / ε := by ring
    nlinarith
  have hqε : (q : ℝ) ^ (-ε) ≤ x :=
    Real.rpow_le_rpow_of_exponent_le hq1 (by linarith)
  have hqε0 : 0 < (q : ℝ) ^ (-ε) := Real.rpow_pos_of_pos hq0 _
  have h1 : C * m * E * (q : ℝ) ^ (-ε) ≤ C * δ * (q : ℝ) ^ (-(c * δ)) := by
    calc C * m * E * (q : ℝ) ^ (-ε) ≤ C * m * E * x := by gcongr
      _ = C * (m * x) * E := by ring
      _ ≤ C * δ * E := by gcongr
      _ ≤ C * δ * (q : ℝ) ^ (-(c * δ)) := by gcongr
  have hpos : 0 < C * m * E * (q : ℝ) ^ (-ε) := by positivity
  linarith

/-- **Hecke's argument with the real-zero bound now in the library** (Davenport 14-18,
`real_zero_lt_of_isQuadratic_unconditional`: `β < 1 - c/(q^{1/2} log² q)`): the zero-free interval it
gives yields only `L(1, χ) ≥ C/(q^{1/2} log² q)` (weaker than 14-16); Hecke's `1/log q` needs the
interval `(1 - c/log q, 1)`. -/
@[kb "davenport1980" "Ch 21, p. 127"]
theorem LFunction_one_ge_of_real_zero_lt_unconditional :
    ∃ C : ℝ, 0 < C ∧ ∀ {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q},
      χ.IsQuadratic → χ ≠ 1 → C / (√(q : ℝ) * Real.log q ^ 2) ≤ (χ.LFunction 1).re := by
  obtain ⟨c', C, hc', hC, hge⟩ := LFunction_one_ge_of_no_real_zero
  obtain ⟨c, hc, hz⟩ := real_zero_lt_of_isQuadratic_unconditional
  set m : ℝ := min (1 / 4) c with hm
  have hm0 : 0 < m := lt_min (by norm_num) hc
  have hm4 : m ≤ 1 / 4 := min_le_left _ _
  have hmc : m ≤ c := min_le_right _ _
  refine ⟨C * m * Real.exp (-(c' / 4)), by positivity, fun {q} _ {χ} hq hχ ↦ ?_⟩
  have hq3 : (3 : ℝ) ≤ q := by exact_mod_cast three_le_of_ne_one hχ
  have hq0 : (0 : ℝ) < q := by linarith
  have hlog1 : 1 < Real.log q := by
    rw [Real.lt_log_iff_exp_lt hq0]
    have := Real.exp_one_lt_d9
    linarith
  have hsq : 1 ≤ √(q : ℝ) := by
    rw [Real.one_le_sqrt]; linarith
  set S : ℝ := √(q : ℝ) * Real.log q ^ 2 with hS
  have hlogS : Real.log q ≤ S := by
    rw [hS]; nlinarith [mul_le_mul hsq (show Real.log q ≤ Real.log q ^ 2 by nlinarith)
      (by linarith) (by linarith)]
  have hS0 : 0 < S := by linarith
  set δ : ℝ := m / S with hδ
  have hδ0 : 0 < δ := by positivity
  have hδ4 : δ ≤ 1 / 4 := by
    have : δ ≤ m := by rw [hδ, div_le_iff₀ hS0]; nlinarith
    linarith
  have hδc : δ ≤ c / S := by rw [hδ]; gcongr
  have hfree : ∀ σ : ℝ, 1 - δ < σ → σ < 1 → χ.LFunction σ ≠ 0 := by
    intro σ h1 h2 h0
    have := hz hq hχ σ h0
    linarith
  have hR := hge hq hχ δ hδ0 hδ4 hfree
  have hexp : Real.exp (-(c' / 4)) ≤ (q : ℝ) ^ (-(c' * δ)) := by
    rw [Real.rpow_def_of_pos hq0, Real.exp_le_exp]
    have h1 : δ * Real.log q ≤ m := by
      rw [hδ, div_mul_eq_mul_div, div_le_iff₀ hS0]
      exact mul_le_mul_of_nonneg_left hlogS hm0.le
    have h2 : c' * (δ * Real.log q) ≤ c' * (1 / 4) :=
      mul_le_mul_of_nonneg_left (h1.trans hm4) hc'.le
    nlinarith
  calc C * m * Real.exp (-(c' / 4)) / S = C * δ * Real.exp (-(c' / 4)) := by rw [hδ]; ring
    _ ≤ C * δ * (q : ℝ) ^ (-(c' * δ)) := by gcongr
    _ ≤ _ := hR

end NTKB.Davenport
