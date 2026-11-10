/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import NTKB.Analytic.Apostol.PNT.Perron
import NTKB.Analytic.Apostol.PNT.Psi1

/-!
# A contour integral representation for `ψ₁(x)/x²` (Apostol, Theorems 13.2 and 13.3)

**Theorem 13.2.** For `c > 1`, `x > 1`:
`ψ₁(x)/x² = (1/2πi) ∫_{c-i∞}^{c+i∞} x^{s-1}/(s(s+1)) (-ζ'(s)/ζ(s)) ds`.

**Theorem 13.3.** For `c > 1`, `x ≥ 1`:
`ψ₁(x)/x² - (1/2)(1 - 1/x)² = (1/2πi) ∫_{c-i∞}^{c+i∞} x^{s-1} h(s) ds`,
`h(s) = (1/(s(s+1))) (-ζ'(s)/ζ(s) - 1/(s-1))`.

The integrals are written with `s = c + iy`, `ds = i dy`, so `(1/2πi) ∫ … ds = (1/2π) ∫ … dy`.
Proof as in Apostol: `-ζ'/ζ = ∑ Λ(n) n^{-s}`, Lemma 3 with `k = 1`, `u = n/x` for each `n`
(`k = 2`, `u = 1/x` for 13.3), and the interchange of sum and integral by absolute convergence.
-/

open Complex Filter Topology Finset MeasureTheory Set
open scoped Real ArithmeticFunction.vonMangoldt

namespace NTKB.Apostol

lemma ofReal_div_cpow_neg {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (z : ℂ) :
    ((a / b : ℝ) : ℂ) ^ (-z) = (b : ℂ) ^ z / (a : ℂ) ^ z := by
  rw [div_eq_mul_inv, ofReal_mul, mul_cpow_ofReal_nonneg ha.le (inv_nonneg.2 hb.le), ofReal_inv,
    inv_cpow _ _ (by rw [arg_ofReal_of_nonneg hb.le]; exact Real.pi_pos.ne), cpow_neg, cpow_neg,
    inv_inv, div_eq_mul_inv, mul_comm]

lemma perronDen_one (s : ℂ) : perronDen 1 s = s * (s + 1) := by
  simp [perronDen, prod_range_succ]

/-- The `n`-th term: `Λ(n)/x · (n/x)^{-s}/(s(s+1))`. -/
noncomputable def psi1Term (x c : ℝ) (n : ℕ) (y : ℝ) : ℂ :=
  (Λ n / x : ℝ) * ((n / x : ℝ) : ℂ) ^ (-((c : ℂ) + y * I)) / perronDen 1 (c + y * I)

lemma norm_psi1Term {x c : ℝ} (hx : 0 < x) (n : ℕ) (y : ℝ) :
    ‖psi1Term x c n y‖ = (Λ n / x) * (n / x : ℝ) ^ (-c) * ‖1 / perronDen 1 (c + y * I)‖ := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [psi1Term]
  · have hnx : (0 : ℝ) < n / x := by positivity
    simp only [psi1Term, norm_div, norm_mul, norm_real, norm_cpow_eq_rpow_re_of_pos hnx]
    simp only [Real.norm_eq_abs, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
      abs_of_pos hx, neg_re, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero,
      mul_one, sub_self, add_zero, norm_one]
    ring

lemma integral_norm_psi1Term {x c : ℝ} (hx : 0 < x) (n : ℕ) :
    ∫ y, ‖psi1Term x c n y‖ = (Λ n / x) * (n / x : ℝ) ^ (-c) *
      ∫ y : ℝ, ‖1 / perronDen 1 (c + y * I)‖ := by
  rw [← integral_const_mul]
  exact integral_congr_ae (Eventually.of_forall fun y ↦ norm_psi1Term hx n y)

lemma integrable_psi1Term {x c : ℝ} (hx : 0 < x) (hc : 0 < c) (n : ℕ) :
    Integrable (psi1Term x c n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : psi1Term x c 0 = 0 := by funext y; simp [psi1Term]
    rw [this]; exact integrable_zero _ _ _
  · have hnx : (0 : ℝ) < n / x := by positivity
    have := ((ch13_lemma_3 hc hnx le_rfl).1).const_mul ((Λ n / x : ℝ) : ℂ)
    refine this.congr (Eventually.of_forall fun y ↦ ?_)
    simp [psi1Term, mul_div_assoc]

lemma integral_psi1Term {x c : ℝ} (hx : 0 < x) (hc : 0 < c) (n : ℕ) :
    ∫ y, psi1Term x c n y = 2 * π * ((Λ n / x : ℝ) * perronKernelFun 1 (n / x)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [psi1Term]
  · have hnx : (0 : ℝ) < n / x := by positivity
    have h := (ch13_lemma_3 hc hnx le_rfl).2
    have hpi : (2 * (π : ℂ)) ≠ 0 := by exact_mod_cast (by positivity : (2 * π : ℝ) ≠ 0)
    rw [div_mul_eq_mul_div, one_mul, div_eq_iff hpi] at h
    simp only [psi1Term, mul_div_assoc]
    rw [integral_const_mul, h]
    ring

/-- `(1/x) ∑ Λ(n) φ₁(n/x) = ψ₁(x)/x²`. -/
lemma sum_psi1Term {x : ℝ} (hx : 1 ≤ x) :
    ∑' n : ℕ, (Λ n / x : ℝ) * perronKernelFun 1 (n / x) = ((psi1 x / x ^ 2 : ℝ) : ℂ) := by
  have hx0 : 0 < x := by linarith
  rw [tsum_eq_sum (s := range (⌊x⌋₊ + 1)) (fun n hn ↦ by
    have : x < n := by
      have := Nat.lt_floor_add_one x
      have h2 : ⌊x⌋₊ + 1 ≤ n := by simpa using hn
      calc x < ⌊x⌋₊ + 1 := Nat.lt_floor_add_one x
        _ ≤ n := by exact_mod_cast h2
    have : ¬ (n / x ≤ 1) := by rw [div_le_one hx0]; linarith
    simp [perronKernelFun, this])]
  rw [psi1_eq_sum hx, range_eq_Ico, show Finset.Ioc 0 ⌊x⌋₊ = Finset.Ico 1 (⌊x⌋₊ + 1) by
    ext; simp; omega]
  rw [sum_eq_sum_Ico_succ_bot (by omega)]
  simp only [ArithmeticFunction.map_zero, zero_div, ofReal_zero, zero_mul, zero_add]
  push_cast
  rw [sum_div]
  refine sum_congr rfl fun n hn ↦ ?_
  have hnx : (n : ℝ) / x ≤ 1 := by
    rw [div_le_one hx0]
    have h1 : n ≤ ⌊x⌋₊ := by simp at hn; omega
    exact (Nat.cast_le.mpr h1).trans (Nat.floor_le hx0.le)
  simp only [perronKernelFun, hnx, ↓reduceIte, pow_one, Nat.factorial_one, Nat.cast_one, div_one]
  have hx' : (x : ℂ) ≠ 0 := by exact_mod_cast hx0.ne'
  push_cast
  field_simp

/-- The integrand of Theorem 13.2 is `∑ₙ psi1Term`. -/
lemma integrand_eq_tsum_psi1Term {x c : ℝ} (hx0 : 0 < x) (hc : 1 < c) (y : ℝ) :
    (x : ℂ) ^ ((c : ℂ) + y * I - 1) / (((c : ℂ) + y * I) * ((c : ℂ) + y * I + 1)) *
      (-deriv riemannZeta (c + y * I) / riemannZeta (c + y * I)) = ∑' n, psi1Term x c n y := by
  set s : ℂ := c + y * I
  have hs : 1 < s.re := by simpa [s] using hc
  rw [← ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs, LSeries, ← tsum_mul_left]
  refine tsum_congr fun n ↦ ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [psi1Term]
  · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    rw [LSeries.term_of_ne_zero hn.ne', psi1Term, ofReal_div_cpow_neg hn' hx0, perronDen_one]
    have hxs : (x : ℂ) ^ (s - 1) = (x : ℂ) ^ s / x := by
      rw [cpow_sub _ _ (by exact_mod_cast hx0.ne'), cpow_one]
    have hns : (n : ℂ) ^ s ≠ 0 := by
      rw [Ne, cpow_eq_zero_iff]; push_cast; intro h; exact absurd h.1 (by exact_mod_cast hn.ne')
    have hx' : (x : ℂ) ≠ 0 := by exact_mod_cast hx0.ne'
    have hs0 : s * (s + 1) ≠ 0 := by
      have := perronDen_ne_zero 1 (z := s) (by simp [s]; linarith)
      rwa [perronDen_one] at this
    rw [hxs]
    simp only [s] at *
    push_cast
    field_simp

/-- **Apostol, Theorem 13.2**: for `c > 1`, `x > 1`,
`ψ₁(x)/x² = (1/2πi) ∫_{c-i∞}^{c+i∞} x^{s-1}/(s(s+1)) (-ζ'(s)/ζ(s)) ds`. -/
@[kb "apostol1976" "Thm 13.2, p. 283"]
theorem apostol_thm_13_2 {c : ℝ} (hc : 1 < c) {x : ℝ} (hx : 1 ≤ x) :
    ((psi1 x / x ^ 2 : ℝ) : ℂ) = (1 / (2 * π)) * ∫ y : ℝ,
      (x : ℂ) ^ ((c : ℂ) + y * I - 1) / (((c : ℂ) + y * I) * ((c : ℂ) + y * I + 1)) *
        (-deriv riemannZeta (c + y * I) / riemannZeta (c + y * I)) := by
  have hx0 : 0 < x := by linarith
  have hc0 : 0 < c := by linarith
  have hpt := integrand_eq_tsum_psi1Term (x := x) hx0 hc
  simp_rw [hpt]
  have hsum : Summable fun n : ℕ ↦ ∫ y, ‖psi1Term x c n y‖ := by
    simp_rw [integral_norm_psi1Term hx0]
    refine Summable.mul_right _ ?_
    have hL := (ArithmeticFunction.LSeriesSummable_vonMangoldt (s := (c : ℂ)) (by simpa using hc)).norm
    refine (hL.mul_left (x ^ (c - 1))).congr fun n ↦ ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      rw [LSeries.term_of_ne_zero hn.ne', norm_div, norm_real, Real.norm_of_nonneg
        ArithmeticFunction.vonMangoldt_nonneg, show ((n : ℂ)) = ((n : ℝ) : ℂ) by simp,
        norm_cpow_eq_rpow_re_of_pos hn', ofReal_re, Real.div_rpow hn'.le hx0.le,
        Real.rpow_neg (by positivity), Real.rpow_sub_one hx0.ne']
      field_simp
      rw [Real.rpow_neg hx0.le]
      field_simp
  rw [← integral_tsum_of_summable_integral_norm (integrable_psi1Term hx0 hc0) hsum]
  simp_rw [integral_psi1Term hx0 hc0]
  rw [tsum_mul_left, sum_psi1Term hx]
  field_simp

/-- Integrability of a series of functions dominated by `a n * g y`. -/
lemma integrable_tsum_of_bound {F : ℕ → ℝ → ℂ} (hF : ∀ n, Integrable (F n)) {a : ℕ → ℝ}
    (ha : Summable a) {g : ℝ → ℝ} (hg : Integrable g) (hb : ∀ n y, ‖F n y‖ ≤ a n * g y) :
    Integrable (fun y ↦ ∑' n, F n y) := by
  have hsum : ∀ y, Summable fun n ↦ F n y := fun y ↦
    Summable.of_norm_bounded (ha.mul_right (g y)) (fun n ↦ hb n y)
  refine Integrable.mono' (hg.const_mul (∑' n, a n)) ?_ (Eventually.of_forall fun y ↦ ?_)
  · refine aestronglyMeasurable_of_tendsto_ae atTop
      (f := fun N y ↦ ∑ n ∈ range N, F n y) (fun N ↦ ?_)
      (Eventually.of_forall fun y ↦ (hsum y).hasSum.tendsto_sum_nat)
    exact Finset.aestronglyMeasurable_fun_sum _ fun n _ ↦ (hF n).1
  · refine (norm_tsum_le_tsum_norm (Summable.of_norm_bounded (ha.mul_right (g y))
      (fun n ↦ by simpa using hb n y))).trans ?_
    rw [← tsum_mul_right]
    exact (Summable.of_norm_bounded (ha.mul_right (g y)) (fun n ↦ by simpa using hb n y)).tsum_le_tsum
      (fun n ↦ hb n y) (ha.mul_right _)

/-- **Apostol, Theorem 13.3**: for `c > 1`, `x ≥ 1`,
`ψ₁(x)/x² - (1/2)(1 - 1/x)² = (1/2πi) ∫_{c-i∞}^{c+i∞} x^{s-1} h(s) ds` with
`h(s) = (1/(s(s+1))) (-ζ'(s)/ζ(s) - 1/(s-1))`. -/
@[kb "apostol1976" "Thm 13.3, p. 284"]
theorem apostol_thm_13_3 {c : ℝ} (hc : 1 < c) {x : ℝ} (hx : 1 ≤ x) :
    ((psi1 x / x ^ 2 - (1 / 2) * (1 - 1 / x) ^ 2 : ℝ) : ℂ) = (1 / (2 * π)) * ∫ y : ℝ,
      (x : ℂ) ^ ((c : ℂ) + y * I - 1) * (1 / (((c : ℂ) + y * I) * ((c : ℂ) + y * I + 1)) *
        (-deriv riemannZeta (c + y * I) / riemannZeta (c + y * I) - 1 / ((c : ℂ) + y * I - 1))) := by
  have hx0 : 0 < x := by linarith
  have hc0 : 0 < c := by linarith
  have hc1 : 0 < c - 1 := by linarith
  have h1x : (0 : ℝ) < 1 / x := by positivity
  set I1 : ℝ → ℂ := fun y ↦ (x : ℂ) ^ ((c : ℂ) + y * I - 1) /
    (((c : ℂ) + y * I) * ((c : ℂ) + y * I + 1)) *
      (-deriv riemannZeta (c + y * I) / riemannZeta (c + y * I))
  set G : ℝ → ℂ := fun y ↦ ((1 / x : ℝ) : ℂ) ^ (-(((c - 1 : ℝ) : ℂ) + y * I)) /
    perronDen 2 ((c - 1 : ℝ) + y * I)
  have hL3 := ch13_lemma_3 hc1 h1x (k := 2) (by norm_num)
  -- the integrand is `I1 - G`
  have hsplit : ∀ y : ℝ, (x : ℂ) ^ ((c : ℂ) + y * I - 1) *
      (1 / (((c : ℂ) + y * I) * ((c : ℂ) + y * I + 1)) *
        (-deriv riemannZeta (c + y * I) / riemannZeta (c + y * I) - 1 / ((c : ℂ) + y * I - 1))) =
      I1 y - G y := by
    intro y
    simp only [I1, G]
    rw [ofReal_div_cpow_neg one_pos hx0, ofReal_one, one_cpow, div_one]
    have e : ((c - 1 : ℝ) : ℂ) + y * I = ((c : ℂ) + y * I) - 1 := by push_cast; ring
    rw [e]
    generalize (c : ℂ) + y * I = s
    simp only [perronDen, prod_range_succ, range_zero, prod_empty, Nat.cast_zero, Nat.cast_one,
      Nat.cast_ofNat, add_zero, one_mul]
    rw [show s - 1 + 1 = s by ring, show s - 1 + 2 = s + 1 by ring]
    simp only [div_eq_mul_inv, mul_inv, one_mul]
    ring
  simp_rw [hsplit]
  -- integrability of `I1`
  have hI1 : Integrable I1 := by
    have h := integrable_tsum_of_bound (F := psi1Term x c) (integrable_psi1Term hx0 hc0)
      (a := fun n ↦ (Λ n / x) * (n / x : ℝ) ^ (-c)) ?_
      (verticalIntegrable_perronDen 1 le_rfl hc0).norm (fun n y ↦ (norm_psi1Term hx0 n y).le)
    · exact h.congr (Eventually.of_forall fun y ↦ (integrand_eq_tsum_psi1Term hx0 hc y).symm)
    · have hL := (ArithmeticFunction.LSeriesSummable_vonMangoldt (s := (c : ℂ))
        (by simpa using hc)).norm
      refine (hL.mul_left (x ^ (c - 1))).congr fun n ↦ ?_
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
        rw [LSeries.term_of_ne_zero hn.ne', norm_div, norm_real, Real.norm_of_nonneg
          ArithmeticFunction.vonMangoldt_nonneg, show ((n : ℂ)) = ((n : ℝ) : ℂ) by simp,
          norm_cpow_eq_rpow_re_of_pos hn', ofReal_re, Real.div_rpow hn'.le hx0.le,
          Real.rpow_neg (by positivity), Real.rpow_sub_one hx0.ne']
        field_simp
        rw [Real.rpow_neg hx0.le]
        field_simp
  rw [integral_sub hI1 hL3.1, mul_sub]
  have h13_2 := apostol_thm_13_2 hc hx
  rw [← h13_2, hL3.2]
  have h1 : ¬ (1 / x > 1) := by rw [gt_iff_lt, lt_div_iff₀ hx0]; linarith
  simp only [perronKernelFun, not_lt.mp h1, ↓reduceIte, Nat.factorial_two]
  push_cast
  ring

end NTKB.Apostol
