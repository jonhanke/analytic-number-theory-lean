/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.NumberTheory.LSeries.HurwitzZeta
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Convex.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import NTKB.Analytic.Apostol.Zeta.Alternating

/-!
# Euler summation for the Hurwitz zeta function (Apostol, Theorems 12.21, 12.22, 12.13 at `n = 0`)

For `0 < a ≤ 1` (`ζ(s, a)` is Mathlib's `hurwitzZeta a s`), integers `N ≥ 0`:

* **Theorem 12.21**, in the series form (26) of the book: for `σ > 0`, `s ≠ 1`,
  `ζ(s,a) = ∑_{n=0}^{N} (n+a)^{-s} + (N+a)^{1-s}/(s-1) - s ∑_{n ≥ N} ∫_0^1 u (n+a+u)^{-s-1} du`.
* **Theorem 12.22**, first case (27): for `σ > -1`, `s ≠ 0, 1`,
  `ζ(s,a) - ∑_{n=0}^{N} (n+a)^{-s} = (N+a)^{1-s}/(s-1) - (s/2)(ζ(s+1,a) - ∑_{n=0}^{N} (n+a)^{-s-1})
    - (s(s+1)/2) ∑_{n ≥ N} ∫_0^1 u² (n+a+u)^{-s-2} du`.
* **Theorem 12.13** for `n = 0`: `ζ(0, a) = 1/2 - a = -B₁(a)` (Mathlib has `n ≥ 1`).

Proof as in Apostol: the integral terms are computed in closed form
(`s ∫_0^1 u (x+u)^{-s-1} du = ((x+1)^{1-s} - x^{1-s})/(1-s) - (x+1)^{-s}`), the series converge
locally uniformly (Weierstrass test), so the right sides are analytic; they agree with `ζ(s,a)` for
`σ > 1`, hence everywhere by analytic continuation (identity theorem).
-/

open Complex Filter Topology Finset MeasureTheory intervalIntegral HurwitzZeta

namespace NTKB.Apostol

/-- `y ↦ y^r` on `y > 0` (real variable), derivative `r y^{r-1}`, any complex `r`. -/
lemma hasDerivAt_ofReal_cpow_any {x : ℝ} (hx : 0 < x) (r : ℂ) :
    HasDerivAt (fun y : ℝ ↦ (y : ℂ) ^ r) (r * (x : ℂ) ^ (r - 1)) x :=
  ((Complex.hasStrictDerivAt_cpow_const (ofReal_mem_slitPlane.2 hx)).hasDerivAt).comp_ofReal

lemma ofReal_cpow_succ {y : ℝ} (hy : 0 < y) (r : ℂ) :
    (y : ℂ) ^ (r + 1) = (y : ℂ) * (y : ℂ) ^ r := by
  rw [cpow_add _ _ (by exact_mod_cast hy.ne'), cpow_one, mul_comm]

/-- The first-order term `J(x, s) = ((x+1)^{1-s} - x^{1-s})/(1-s) - (x+1)^{-s}`. -/
noncomputable def hurwitzJ (x : ℝ) (s : ℂ) : ℂ :=
  (((x + 1 : ℝ) : ℂ) ^ (1 - s) - (x : ℂ) ^ (1 - s)) / (1 - s) - ((x + 1 : ℝ) : ℂ) ^ (-s)

/-- The second-order term `L(x, s) = J(x, s) - (s/2) (x+1)^{-s-1}`. -/
noncomputable def hurwitzL (x : ℝ) (s : ℂ) : ℂ :=
  hurwitzJ x s - s / 2 * ((x + 1 : ℝ) : ℂ) ^ (-s - 1)

/-- `s ∫_0^1 u (x+u)^{-s-1} du = J(x, s)` for `x > 0`, `s ≠ 1`. -/
lemma integral_J {x : ℝ} (hx : 0 < x) {s : ℂ} (hs : s ≠ 1) :
    s * ∫ u in (0 : ℝ)..1, (u : ℂ) * ((x + u : ℝ) : ℂ) ^ (-s - 1) = hurwitzJ x s := by
  have h1s : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs)
  set G : ℝ → ℂ := fun u ↦ ((x + u : ℝ) : ℂ) ^ (1 - s) / (1 - s) - (u : ℂ) * ((x + u : ℝ) : ℂ) ^ (-s)
  have hG : ∀ u ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt G (s * ((u : ℂ) * ((x + u : ℝ) : ℂ) ^ (-s - 1))) u := by
    intro u hu
    have hu0 : 0 ≤ u := by simp at hu; exact hu.1
    have hxu : 0 < x + u := by linarith
    have d1 := ((hasDerivAt_ofReal_cpow_any hxu (1 - s)).comp_const_add x u).div_const (1 - s)
    have d2 := (hasDerivAt_id u).ofReal_comp.mul
      ((hasDerivAt_ofReal_cpow_any hxu (-s)).comp_const_add x u)
    convert d1.sub d2 using 1
    · funext v; simp [G]
    simp only [id, ofReal_one, one_mul]
    have e1 : (1 - s - 1) = -s := by ring
    rw [e1]
    have e2 : ((x + u : ℝ) : ℂ) ^ (-s) = ((x + u : ℝ) : ℂ) * ((x + u : ℝ) : ℂ) ^ (-s - 1) := by
      rw [← ofReal_cpow_succ hxu]; ring_nf
    rw [e2]
    field_simp
    push_cast
    ring
  have hcont : IntervalIntegrable (fun u : ℝ ↦ s * ((u : ℂ) * ((x + u : ℝ) : ℂ) ^ (-s - 1)))
      volume 0 1 := by
    refine ContinuousOn.intervalIntegrable ?_
    refine continuousOn_const.mul (continuous_ofReal.continuousOn.mul ?_)
    refine ContinuousOn.cpow_const (by fun_prop) fun u hu ↦ ?_
    have hu0 : 0 ≤ u := by simp at hu; exact hu.1
    exact ofReal_mem_slitPlane.2 (by linarith)
  rw [← intervalIntegral.integral_const_mul, integral_eq_sub_of_hasDerivAt hG hcont]
  simp only [G, hurwitzJ, ofReal_zero, zero_mul, sub_zero, add_zero, ofReal_one, one_mul]
  ring

/-- `(s(s+1)/2) ∫_0^1 u² (x+u)^{-s-2} du = L(x, s)` for `x > 0`, `s ≠ 1`. -/
lemma integral_L {x : ℝ} (hx : 0 < x) {s : ℂ} (hs : s ≠ 1) :
    s * (s + 1) / 2 * ∫ u in (0 : ℝ)..1, (u : ℂ) ^ 2 * ((x + u : ℝ) : ℂ) ^ (-s - 2) =
      hurwitzL x s := by
  have h1s : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs)
  set F : ℝ → ℂ := fun u ↦ ((x + u : ℝ) : ℂ) ^ (1 - s) / (1 - s) - (u : ℂ) * ((x + u : ℝ) : ℂ) ^ (-s)
    - s / 2 * ((u : ℂ) ^ 2 * ((x + u : ℝ) : ℂ) ^ (-s - 1))
  have hF : ∀ u ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt F (s * (s + 1) / 2 * ((u : ℂ) ^ 2 * ((x + u : ℝ) : ℂ) ^ (-s - 2))) u := by
    intro u hu
    have hu0 : 0 ≤ u := by simp at hu; exact hu.1
    have hxu : 0 < x + u := by linarith
    have d1 := ((hasDerivAt_ofReal_cpow_any hxu (1 - s)).comp_const_add x u).div_const (1 - s)
    have d2 := (hasDerivAt_id u).ofReal_comp.mul
      ((hasDerivAt_ofReal_cpow_any hxu (-s)).comp_const_add x u)
    have d3 := (((hasDerivAt_id u).ofReal_comp.pow 2).mul
      ((hasDerivAt_ofReal_cpow_any hxu (-s - 1)).comp_const_add x u)).const_mul (s / 2)
    convert (d1.sub d2).sub d3 using 1
    · funext v; simp [F]
    simp only [id, ofReal_one, one_mul, Pi.pow_apply]
    have e1 : (1 - s - 1) = -s := by ring
    have e3 : (-s - 1 - 1) = -s - 2 := by ring
    rw [e1, e3]
    have e2 : ((x + u : ℝ) : ℂ) ^ (-s) = ((x + u : ℝ) : ℂ) * ((x + u : ℝ) : ℂ) ^ (-s - 1) := by
      rw [← ofReal_cpow_succ hxu]; ring_nf
    have e4 : ((x + u : ℝ) : ℂ) ^ (-s - 1) = ((x + u : ℝ) : ℂ) * ((x + u : ℝ) : ℂ) ^ (-s - 2) := by
      rw [← ofReal_cpow_succ hxu]; ring_nf
    rw [e2, e4]
    field_simp
    push_cast
    ring
  have hcont : IntervalIntegrable
      (fun u : ℝ ↦ s * (s + 1) / 2 * ((u : ℂ) ^ 2 * ((x + u : ℝ) : ℂ) ^ (-s - 2))) volume 0 1 := by
    refine ContinuousOn.intervalIntegrable ?_
    refine continuousOn_const.mul ((continuous_ofReal.pow 2).continuousOn.mul ?_)
    refine ContinuousOn.cpow_const (by fun_prop) fun u hu ↦ ?_
    have hu0 : 0 ≤ u := by simp at hu; exact hu.1
    exact ofReal_mem_slitPlane.2 (by linarith)
  rw [← intervalIntegral.integral_const_mul, integral_eq_sub_of_hasDerivAt hF hcont]
  simp only [F, hurwitzL, hurwitzJ, ofReal_zero, zero_mul, sub_zero, add_zero, ofReal_one, one_mul,
    one_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
  ring

lemma norm_ofReal_add_cpow_le {x u : ℝ} (hx : 0 < x) (hu : 0 ≤ u) {r : ℂ} (hr : r.re ≤ 0) :
    ‖((x + u : ℝ) : ℂ) ^ r‖ ≤ x ^ r.re := by
  rw [norm_cpow_eq_rpow_re_of_pos (by linarith)]
  exact Real.rpow_le_rpow_of_nonpos hx (by linarith) hr

/-- `‖J(x, s)‖ ≤ ‖s‖ x^{-σ-1}` for `x > 0`, `σ ≥ -1`, `s ≠ 1`. -/
lemma norm_hurwitzJ_le {x : ℝ} (hx : 0 < x) {s : ℂ} (hs : s ≠ 1) (hσ : -1 ≤ s.re) :
    ‖hurwitzJ x s‖ ≤ ‖s‖ * x ^ (-s.re - 1) := by
  rw [← integral_J hx hs, norm_mul]
  gcongr
  have := norm_integral_le_of_norm_le_const (a := 0) (b := 1)
    (f := fun u : ℝ ↦ (u : ℂ) * ((x + u : ℝ) : ℂ) ^ (-s - 1)) (C := x ^ (-s.re - 1)) (fun u hu ↦ by
      rw [Set.uIoc_of_le zero_le_one] at hu
      rw [norm_mul, norm_real, Real.norm_of_nonneg hu.1.le]
      calc u * ‖((x + u : ℝ) : ℂ) ^ (-s - 1)‖ ≤ 1 * x ^ (-s.re - 1) := by
            gcongr
            · exact hu.2
            · simpa using norm_ofReal_add_cpow_le hx hu.1.le (r := -s - 1) (by simp; linarith)
        _ = _ := one_mul _)
  simpa using this

/-- `‖L(x, s)‖ ≤ (‖s‖ ‖s+1‖/2) x^{-σ-2}` for `x > 0`, `σ ≥ -2`, `s ≠ 1`. -/
lemma norm_hurwitzL_le {x : ℝ} (hx : 0 < x) {s : ℂ} (hs : s ≠ 1) (hσ : -2 ≤ s.re) :
    ‖hurwitzL x s‖ ≤ ‖s‖ * ‖s + 1‖ / 2 * x ^ (-s.re - 2) := by
  rw [← integral_L hx hs, norm_mul]
  have h2 : ‖s * (s + 1) / 2‖ = ‖s‖ * ‖s + 1‖ / 2 := by
    rw [norm_div, norm_mul]; simp
  rw [h2]
  gcongr
  have := norm_integral_le_of_norm_le_const (a := 0) (b := 1)
    (f := fun u : ℝ ↦ (u : ℂ) ^ 2 * ((x + u : ℝ) : ℂ) ^ (-s - 2)) (C := x ^ (-s.re - 2))
    (fun u hu ↦ by
      rw [Set.uIoc_of_le zero_le_one] at hu
      rw [norm_mul, norm_pow, norm_real, Real.norm_of_nonneg hu.1.le]
      calc u ^ 2 * ‖((x + u : ℝ) : ℂ) ^ (-s - 2)‖ ≤ 1 * x ^ (-s.re - 2) := by
            gcongr
            · exact pow_le_one₀ hu.1.le hu.2
            · simpa using norm_ofReal_add_cpow_le hx hu.1.le (r := -s - 2) (by simp; linarith)
        _ = _ := one_mul _)
  simpa using this

lemma summable_shift_rpow {a : ℝ} (ha : 0 < a) (N : ℕ) {p : ℝ} (hp : p < -1) :
    Summable fun n : ℕ ↦ ((N + n + a : ℝ)) ^ p := by
  refine (summable_nat_add_iff 1).mp ?_
  refine Summable.of_nonneg_of_le (fun n ↦ by positivity) (fun n ↦ ?_) (summable_succ_rpow hp)
  exact Real.rpow_le_rpow_of_nonpos (by positivity) (by push_cast; linarith) (by linarith)

/-- `x^p ≤ x^q + x^r` for `x > 0`, `r ≤ p ≤ q`. -/
lemma rpow_le_rpow_add_rpow {x : ℝ} (hx : 0 < x) {p q r : ℝ} (hrp : r ≤ p) (hpq : p ≤ q) :
    x ^ p ≤ x ^ q + x ^ r := by
  rcases le_or_gt 1 x with h | h
  · exact (Real.rpow_le_rpow_of_exponent_le h hpq).trans (le_add_of_nonneg_right (by positivity))
  · exact (Real.rpow_le_rpow_of_exponent_ge hx h.le hrp).trans (le_add_of_nonneg_left (by positivity))

/-- `∑_{n ≥ 0} J(N + n + a, s)`. -/
noncomputable def hurwitzJSum (a : ℝ) (N : ℕ) (s : ℂ) : ℂ := ∑' n : ℕ, hurwitzJ (N + n + a) s

/-- `∑_{n ≥ 0} L(N + n + a, s)`. -/
noncomputable def hurwitzLSum (a : ℝ) (N : ℕ) (s : ℂ) : ℂ := ∑' n : ℕ, hurwitzL (N + n + a) s

lemma differentiableAt_hurwitzJ {x : ℝ} (hx : 0 < x) {s : ℂ} (hs : s ≠ 1) :
    DifferentiableAt ℂ (hurwitzJ x) s := by
  have hx1 : ((x + 1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by linarith : x + 1 ≠ 0)
  have hx0 : ((x : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  unfold hurwitzJ
  refine ((((differentiableAt_const _).sub differentiableAt_id).const_cpow (Or.inl hx1)).sub
    (((differentiableAt_const _).sub differentiableAt_id).const_cpow (Or.inl hx0))).div
    ((differentiableAt_const _).sub differentiableAt_id) (sub_ne_zero.mpr (Ne.symm hs)) |>.sub ?_
  exact differentiableAt_id.neg.const_cpow (Or.inl hx1)

lemma differentiableAt_hurwitzL {x : ℝ} (hx : 0 < x) {s : ℂ} (hs : s ≠ 1) :
    DifferentiableAt ℂ (hurwitzL x) s := by
  have hx1 : ((x + 1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by linarith : x + 1 ≠ 0)
  unfold hurwitzL
  exact (differentiableAt_hurwitzJ hx hs).sub ((differentiableAt_id.div_const 2).mul
    ((differentiableAt_id.neg.sub (differentiableAt_const _)).const_cpow (Or.inl hx1)))

/-- `∑ J` is analytic on `σ > 0`, `s ≠ 1` (Weierstrass test). -/
lemma differentiableOn_hurwitzJSum {a : ℝ} (ha : 0 < a) (N : ℕ) :
    DifferentiableOn ℂ (hurwitzJSum a N) ({s : ℂ | 0 < s.re} \ {1}) := by
  intro s₀ hs₀
  have hs₀' : 0 < s₀.re := hs₀.1
  set δ := s₀.re / 2
  set R := ‖s₀‖ + 1
  set U : Set ℂ := {s | δ < s.re ∧ ‖s‖ < R} \ {1}
  have hU : IsOpen U :=
    ((isOpen_lt continuous_const continuous_re).inter
      (isOpen_lt continuous_norm continuous_const)).sdiff isClosed_singleton
  have hmem : s₀ ∈ U := ⟨⟨by simp only [δ]; linarith, by simp only [R]; linarith⟩, hs₀.2⟩
  have hR : 0 < R := by positivity
  have hdiff : DifferentiableOn ℂ (hurwitzJSum a N) U := by
    refine differentiableOn_tsum_of_summable_norm
      (u := fun n : ℕ ↦ R * (((N + n + a : ℝ)) ^ (-δ - 1) + ((N + n + a : ℝ)) ^ (-R - 1)))
      ?_ ?_ hU ?_
    · exact Summable.mul_left _ ((summable_shift_rpow ha N (by simp only [δ]; linarith)).add
        (summable_shift_rpow ha N (by linarith)))
    · intro n s hs
      exact (differentiableAt_hurwitzJ (by positivity) hs.2).differentiableWithinAt
    · intro n s hs
      have hσ : 0 < s.re := by linarith [hs.1.1, show 0 < δ by positivity]
      have hσR : s.re < R := (re_le_norm s).trans_lt hs.1.2
      refine (norm_hurwitzJ_le (by positivity) hs.2 (by linarith)).trans ?_
      gcongr
      · exact hs.1.2.le
      · exact rpow_le_rpow_add_rpow (by positivity) (by linarith) (by linarith [hs.1.1])
  exact (hdiff s₀ hmem).differentiableAt (hU.mem_nhds hmem) |>.differentiableWithinAt

/-- `∑ L` is analytic on `σ > -1`, `s ≠ 1` (Weierstrass test). -/
lemma differentiableOn_hurwitzLSum {a : ℝ} (ha : 0 < a) (N : ℕ) :
    DifferentiableOn ℂ (hurwitzLSum a N) ({s : ℂ | -1 < s.re} \ {1}) := by
  intro s₀ hs₀
  have hs₀' : -1 < s₀.re := hs₀.1
  set δ := (s₀.re - 1) / 2
  set R := ‖s₀‖ + 1
  set U : Set ℂ := {s | δ < s.re ∧ ‖s‖ < R} \ {1}
  have hU : IsOpen U :=
    ((isOpen_lt continuous_const continuous_re).inter
      (isOpen_lt continuous_norm continuous_const)).sdiff isClosed_singleton
  have hmem : s₀ ∈ U := ⟨⟨by simp only [δ]; linarith, by simp only [R]; linarith⟩, hs₀.2⟩
  have hR : 0 < R := by positivity
  have hdiff : DifferentiableOn ℂ (hurwitzLSum a N) U := by
    refine differentiableOn_tsum_of_summable_norm
      (u := fun n : ℕ ↦ R * (R + 1) / 2 *
        (((N + n + a : ℝ)) ^ (-δ - 2) + ((N + n + a : ℝ)) ^ (-R - 2))) ?_ ?_ hU ?_
    · exact Summable.mul_left _ ((summable_shift_rpow ha N (by simp only [δ]; linarith)).add
        (summable_shift_rpow ha N (by linarith)))
    · intro n s hs
      exact (differentiableAt_hurwitzL (by positivity) hs.2).differentiableWithinAt
    · intro n s hs
      have hσ : δ < s.re := hs.1.1
      have hσR : s.re < R := (re_le_norm s).trans_lt hs.1.2
      refine (norm_hurwitzL_le (by positivity) hs.2 (by simp only [δ] at hσ; linarith)).trans ?_
      have h1 : ‖s + 1‖ ≤ R + 1 := (norm_add_le _ _).trans (by simpa using hs.1.2.le)
      gcongr
      · exact hs.1.2.le
      · exact rpow_le_rpow_add_rpow (by positivity) (by linarith) (by linarith [hs.1.1])
  exact (hdiff s₀ hmem).differentiableAt (hU.mem_nhds hmem) |>.differentiableWithinAt

/-! ### The identities for `σ > 1` -/

lemma hasSum_hurwitz_shift {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1) (N : ℕ) {s : ℂ} (hs : 1 < s.re)
    (r : ℂ) (hr : r = s) :
    HasSum (fun n : ℕ ↦ ((N + n + a + 1 : ℝ) : ℂ) ^ (-r))
      (hurwitzZeta a r - ∑ i ∈ range (N + 1), ((i + a : ℝ) : ℂ) ^ (-r)) := by
  subst hr
  have hf := hasSum_hurwitzZeta_of_one_lt_re ⟨ha0.le, ha1⟩ hs
  rw [← hasSum_nat_add_iff' (N + 1)] at hf
  convert hf using 1
  · funext n
    rw [one_div, ← cpow_neg]
    congr 1
    push_cast; ring
  · congr 1
    refine sum_congr rfl fun i _ ↦ ?_
    rw [one_div, ← cpow_neg]
    push_cast; ring_nf

lemma tendsto_ofReal_cpow_atTop {a : ℝ} (ha : 0 < a) (N : ℕ) {r : ℂ} (hr : r.re < 0) :
    Tendsto (fun M : ℕ ↦ ((N + M + a : ℝ) : ℂ) ^ r) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h1 : Tendsto (fun M : ℕ ↦ ((N + M + a : ℝ))) atTop atTop := by
    refine tendsto_atTop_add_const_right _ a ?_
    exact tendsto_atTop_add_const_left _ _ tendsto_natCast_atTop_atTop
  have h2 := (tendsto_rpow_neg_atTop (y := -r.re) (by linarith)).comp h1
  refine h2.congr' (Eventually.of_forall fun M ↦ ?_)
  simp only [Function.comp, neg_neg]
  rw [norm_cpow_eq_rpow_re_of_pos (by positivity)]

/-- For `σ > 1`: `∑_{n ≥ 0} J(N+n+a, s) = -(N+a)^{1-s}/(1-s) - (ζ(s,a) - ∑_{n ≤ N} (n+a)^{-s})`. -/
lemma hurwitzJSum_eq_of_one_lt {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1) (N : ℕ) {s : ℂ}
    (hs : 1 < s.re) :
    hurwitzJSum a N s = -((N + a : ℝ) : ℂ) ^ (1 - s) / (1 - s) -
      (hurwitzZeta a s - ∑ i ∈ range (N + 1), ((i + a : ℝ) : ℂ) ^ (-s)) := by
  have hs1 : s ≠ 1 := fun h ↦ by simp [h] at hs
  have hsum : Summable fun n : ℕ ↦ hurwitzJ (N + n + a) s := by
    refine Summable.of_norm_bounded
      (Summable.mul_left ‖s‖ (summable_shift_rpow ha0 N (p := -s.re - 1) (by linarith)))
      (fun n ↦ norm_hurwitzJ_le (by positivity) hs1 (by linarith))
  set u : ℕ → ℂ := fun M ↦ ((N + M + a : ℝ) : ℂ) ^ (1 - s)
  have key : ∀ M : ℕ, ∑ n ∈ range M, hurwitzJ (N + n + a) s =
      (u M - u 0) / (1 - s) - ∑ n ∈ range M, ((N + n + a + 1 : ℝ) : ℂ) ^ (-s) := by
    intro M
    rw [← sum_range_sub u M, sum_div, ← sum_sub_distrib]
    refine sum_congr rfl fun n _ ↦ ?_
    simp only [hurwitzJ, u]
    have : ((N : ℝ) + ((n + 1 : ℕ) : ℝ) + a) = (N + n + a + 1) := by push_cast; ring
    rw [this]
  have hlim : Tendsto (fun M ↦ ∑ n ∈ range M, hurwitzJ (N + n + a) s) atTop
      (𝓝 ((0 - u 0) / (1 - s) -
        (hurwitzZeta a s - ∑ i ∈ range (N + 1), ((i + a : ℝ) : ℂ) ^ (-s)))) := by
    simp_rw [key]
    refine ((tendsto_ofReal_cpow_atTop ha0 N (r := 1 - s) (by simp; linarith)).sub
      tendsto_const_nhds |>.div_const _).sub ?_
    exact (hasSum_hurwitz_shift ha0 ha1 N hs s rfl).tendsto_sum_nat
  rw [hurwitzJSum, tendsto_nhds_unique hsum.hasSum.tendsto_sum_nat hlim]
  simp only [u, Nat.cast_zero, add_zero, zero_sub]

lemma summable_hurwitzJ {a : ℝ} (ha0 : 0 < a) (N : ℕ) {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    Summable fun n : ℕ ↦ hurwitzJ (N + n + a) s :=
  Summable.of_norm_bounded
    (Summable.mul_left ‖s‖ (summable_shift_rpow ha0 N (p := -s.re - 1) (by linarith)))
    (fun n ↦ norm_hurwitzJ_le (by positivity) hs1 (by linarith))

/-- For `σ > 1`: `∑ L = ∑ J - (s/2)(ζ(s+1,a) - ∑_{n ≤ N} (n+a)^{-s-1})`. -/
lemma hurwitzLSum_eq_of_one_lt {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1) (N : ℕ) {s : ℂ}
    (hs : 1 < s.re) :
    hurwitzLSum a N s = hurwitzJSum a N s -
      s / 2 * (hurwitzZeta a (s + 1) - ∑ i ∈ range (N + 1), ((i + a : ℝ) : ℂ) ^ (-s - 1)) := by
  have hs1 : s ≠ 1 := fun h ↦ by simp [h] at hs
  have hg := hasSum_hurwitz_shift ha0 ha1 N (s := s + 1) (by simp; linarith) (s + 1) rfl
  rw [show -(s + 1) = -s - 1 by ring] at hg
  rw [hurwitzLSum, hurwitzJSum, ← hg.tsum_eq, ← tsum_mul_left,
    ← (summable_hurwitzJ ha0 N (by linarith) hs1).tsum_sub (hg.summable.mul_left _)]
  refine tsum_congr fun n ↦ ?_
  simp only [hurwitzL]

/-- For `σ > 1`: the identity of Theorem 12.21 with the closed-form terms `J`. -/
lemma hurwitzZeta_eq_J_of_one_lt {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1) (N : ℕ) {s : ℂ}
    (hs : 1 < s.re) :
    hurwitzZeta a s = ∑ i ∈ range (N + 1), ((i + a : ℝ) : ℂ) ^ (-s) +
      ((N + a : ℝ) : ℂ) ^ (1 - s) / (s - 1) - hurwitzJSum a N s := by
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr fun h ↦ by simp [h] at hs
  have h1s : 1 - s ≠ 0 := by rw [← neg_sub]; exact neg_ne_zero.mpr hs1
  rw [hurwitzJSum_eq_of_one_lt ha0 ha1 N hs]
  field_simp
  ring

lemma isOpen_re_gt_diff {c : ℝ} (S : Set ℂ) (hS : IsClosed S) : IsOpen ({s : ℂ | c < s.re} \ S) :=
  (isOpen_lt continuous_const continuous_re).sdiff hS

/-- `{σ > -1} \ {0, 1}` is preconnected. -/
theorem isPreconnected_re_gt_neg_one_diff : IsPreconnected ({s : ℂ | -1 < s.re} \ {0, 1}) := by
  set W₁ : Set ℂ := {s | -1 < s.re ∧ 0 < s.im}
  set W₂ : Set ℂ := {s | -1 < s.re ∧ s.im < 0}
  set W₃ : Set ℂ := {s | -1 < s.re ∧ s.re < 0}
  set W₄ : Set ℂ := {s | 0 < s.re ∧ s.re < 1}
  set W₅ : Set ℂ := {s | 1 < s.re}
  have c₁ : Convex ℝ W₁ := (convex_halfSpace_gt reLm.isLinear (-1)).inter
    (convex_halfSpace_gt imLm.isLinear 0)
  have c₂ : Convex ℝ W₂ := (convex_halfSpace_gt reLm.isLinear (-1)).inter
    (convex_halfSpace_lt imLm.isLinear 0)
  have c₃ : Convex ℝ W₃ := (convex_halfSpace_gt reLm.isLinear (-1)).inter
    (convex_halfSpace_lt reLm.isLinear 0)
  have c₄ : Convex ℝ W₄ := (convex_halfSpace_gt reLm.isLinear 0).inter
    (convex_halfSpace_lt reLm.isLinear 1)
  have c₅ : Convex ℝ W₅ := convex_halfSpace_gt reLm.isLinear 1
  have heq : {s : ℂ | -1 < s.re} \ {0, 1} = (((W₁ ∪ W₃) ∪ W₄) ∪ W₂) ∪ W₅ := by
    ext s
    simp only [Set.mem_sdiff, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff,
      Set.mem_union, W₁, W₂, W₃, W₄, W₅, not_or]
    constructor
    · rintro ⟨h0, h1, h2⟩
      rcases lt_trichotomy s.im 0 with h | h | h
      · left; right; exact ⟨h0, h⟩
      · rcases lt_trichotomy s.re 0 with h' | h' | h'
        · left; left; left; right; exact ⟨h0, h'⟩
        · exact absurd (Complex.ext (by simpa using h') (by simpa using h)) h1
        · rcases lt_trichotomy s.re 1 with h'' | h'' | h''
          · left; left; right; exact ⟨h', h''⟩
          · exact absurd (Complex.ext (by simpa using h'') (by simpa using h)) h2
          · right; exact h''
      · left; left; left; left; exact ⟨h0, h⟩
    · rintro ((((h | h) | h) | h) | h)
      · exact ⟨h.1, fun e ↦ by subst e; norm_num at h, fun e ↦ by subst e; norm_num at h⟩
      · exact ⟨h.1, fun e ↦ by subst e; norm_num at h, fun e ↦ by subst e; norm_num at h⟩
      · exact ⟨by linarith [h.1], fun e ↦ by subst e; norm_num at h, fun e ↦ by subst e; norm_num at h⟩
      · exact ⟨h.1, fun e ↦ by subst e; norm_num at h, fun e ↦ by subst e; norm_num at h⟩
      · exact ⟨by linarith [show (1 : ℝ) < s.re from h], fun e ↦ by subst e; norm_num at h,
          fun e ↦ by subst e; norm_num at h⟩
  rw [heq]
  have p13 : IsPreconnected (W₁ ∪ W₃) :=
    IsPreconnected.union (-1 / 2 + I) ⟨by norm_num, by norm_num⟩
      ⟨by norm_num, by norm_num⟩ c₁.isPreconnected c₃.isPreconnected
  have p134 : IsPreconnected ((W₁ ∪ W₃) ∪ W₄) :=
    IsPreconnected.union (1 / 2 + I) (Or.inl ⟨by norm_num, by norm_num⟩)
      ⟨by norm_num, by norm_num⟩ p13 c₄.isPreconnected
  have p1342 : IsPreconnected (((W₁ ∪ W₃) ∪ W₄) ∪ W₂) :=
    IsPreconnected.union (1 / 2 - I) (Or.inr ⟨by norm_num, by norm_num⟩)
      ⟨by norm_num, by norm_num⟩ p134 c₂.isPreconnected
  exact IsPreconnected.union (2 + I) (Or.inl (Or.inl (Or.inl ⟨by norm_num, by norm_num⟩)))
    (show 1 < (2 + I).re by norm_num) p1342 c₅.isPreconnected

lemma differentiableAt_sum_cpow_neg (a : ℝ) (ha : 0 < a) (N : ℕ) (c : ℂ) (z : ℂ) :
    DifferentiableAt ℂ (fun s : ℂ ↦ ∑ n ∈ range (N + 1), ((n + a : ℝ) : ℂ) ^ (-s - c)) z := by
  refine DifferentiableAt.fun_sum fun n _ ↦ ?_
  exact (differentiableAt_id.neg.sub_const c).const_cpow
    (Or.inl (by exact_mod_cast (by positivity : (n + a : ℝ) ≠ 0)))

lemma differentiableAt_cpow_terms (x : ℝ) (hx : 0 < x) (c : ℂ) (s : ℂ) :
    DifferentiableAt ℂ (fun s : ℂ ↦ (x : ℂ) ^ (c - s)) s :=
  ((differentiableAt_const _).sub differentiableAt_id).const_cpow
    (Or.inl (by exact_mod_cast hx.ne'))

/-- The identity of Theorem 12.21 with the closed-form terms `J`, for `σ > 0`, `s ≠ 1`. -/
lemma hurwitzZeta_eq_J {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1) (N : ℕ) {s : ℂ} (hs : 0 < s.re)
    (hs1 : s ≠ 1) :
    hurwitzZeta a s = ∑ n ∈ range (N + 1), ((n + a : ℝ) : ℂ) ^ (-s) +
      ((N + a : ℝ) : ℂ) ^ (1 - s) / (s - 1) - hurwitzJSum a N s := by
  set U : Set ℂ := {s : ℂ | 0 < s.re} \ {1}
  have hU : IsOpen U := isOpen_re_gt_diff _ isClosed_singleton
  have hf : AnalyticOnNhd ℂ (fun s ↦ hurwitzZeta a s) U :=
    DifferentiableOn.analyticOnNhd (fun z hz ↦
      (differentiableAt_hurwitzZeta _ hz.2).differentiableWithinAt) hU
  have hg : AnalyticOnNhd ℂ (fun s ↦ ∑ n ∈ range (N + 1), ((n + a : ℝ) : ℂ) ^ (-s) +
      ((N + a : ℝ) : ℂ) ^ (1 - s) / (s - 1) - hurwitzJSum a N s) U := by
    refine DifferentiableOn.analyticOnNhd (fun z hz ↦ ?_) hU
    refine DifferentiableWithinAt.sub ?_ (differentiableOn_hurwitzJSum ha0 N z hz)
    refine DifferentiableAt.differentiableWithinAt ?_
    refine DifferentiableAt.add ?_ ?_
    · simpa using differentiableAt_sum_cpow_neg a ha0 N 0 z
    · exact (differentiableAt_cpow_terms (N + a) (by positivity) 1 z).div
        (differentiableAt_id.sub (differentiableAt_const _)) (sub_ne_zero.mpr hz.2)
  have h2 : (2 : ℂ) ∈ U := ⟨by simp, by norm_num⟩
  have hev : (fun s ↦ hurwitzZeta a s) =ᶠ[𝓝 2] fun s ↦ ∑ n ∈ range (N + 1),
      ((n + a : ℝ) : ℂ) ^ (-s) + ((N + a : ℝ) : ℂ) ^ (1 - s) / (s - 1) - hurwitzJSum a N s := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds
      (show (2 : ℂ) ∈ {b : ℂ | (1 : ℝ) < b.re} by norm_num)] with z hz
    exact hurwitzZeta_eq_J_of_one_lt ha0 ha1 N hz
  exact hf.eqOn_of_preconnected_of_eventuallyEq hg isPreconnected_re_pos_diff_one h2 hev ⟨hs, hs1⟩

/-- **Apostol, Theorem 12.21** (Euler summation for `ζ(s, a)`, in the series form (26)): for
`0 < a ≤ 1`, integers `N ≥ 0`, `σ > 0`, `s ≠ 1`,
`ζ(s,a) = ∑_{n=0}^{N} (n+a)^{-s} + (N+a)^{1-s}/(s-1) - s ∑_{n ≥ N} ∫_0^1 u (n+a+u)^{-s-1} du`. -/
@[kb "apostol1976" "Thm 12.21, p. 269"]
theorem apostol_thm_12_21 {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1) (N : ℕ) {s : ℂ} (hs : 0 < s.re)
    (hs1 : s ≠ 1) :
    hurwitzZeta a s = ∑ n ∈ range (N + 1), ((n + a : ℝ) : ℂ) ^ (-s) +
      ((N + a : ℝ) : ℂ) ^ (1 - s) / (s - 1) -
      s * ∑' n : ℕ, ∫ u in (0 : ℝ)..1, (u : ℂ) * ((N + n + a + u : ℝ) : ℂ) ^ (-s - 1) := by
  have hJ : s * ∑' n : ℕ, ∫ u in (0 : ℝ)..1, (u : ℂ) * ((N + n + a + u : ℝ) : ℂ) ^ (-s - 1) =
      hurwitzJSum a N s := by
    rw [← tsum_mul_left]
    exact tsum_congr fun n ↦ integral_J (by positivity) hs1
  rw [hJ]
  exact hurwitzZeta_eq_J ha0 ha1 N hs hs1

/-- The identity behind Theorem 12.22 (first case), with the closed-form terms `L`, on
`σ > -1`, `s ≠ 0, 1`. -/
lemma hurwitzZeta_eq_L {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1) (N : ℕ) {s : ℂ}
    (hs : s ∈ {s : ℂ | -1 < s.re} \ {0, 1}) :
    hurwitzZeta a s = ∑ n ∈ range (N + 1), ((n + a : ℝ) : ℂ) ^ (-s) +
      ((N + a : ℝ) : ℂ) ^ (1 - s) / (s - 1) -
      s / 2 * (hurwitzZeta a (s + 1) - ∑ i ∈ range (N + 1), ((i + a : ℝ) : ℂ) ^ (-s - 1)) -
      hurwitzLSum a N s := by
  set V : Set ℂ := {s : ℂ | -1 < s.re} \ {0, 1}
  have hV : IsOpen V := isOpen_re_gt_diff _ (Set.toFinite _).isClosed
  have hne1 : ∀ z ∈ V, z ≠ 1 := fun z hz h ↦ hz.2 (by simp [h])
  have hne0 : ∀ z ∈ V, z ≠ 0 := fun z hz h ↦ hz.2 (by simp [h])
  have hf : AnalyticOnNhd ℂ (fun s ↦ hurwitzZeta a s) V :=
    DifferentiableOn.analyticOnNhd (fun z hz ↦
      (differentiableAt_hurwitzZeta _ (hne1 z hz)).differentiableWithinAt) hV
  have hg : AnalyticOnNhd ℂ (fun s ↦ ∑ n ∈ range (N + 1), ((n + a : ℝ) : ℂ) ^ (-s) +
      ((N + a : ℝ) : ℂ) ^ (1 - s) / (s - 1) -
      s / 2 * (hurwitzZeta a (s + 1) - ∑ i ∈ range (N + 1), ((i + a : ℝ) : ℂ) ^ (-s - 1)) -
      hurwitzLSum a N s) V := by
    refine DifferentiableOn.analyticOnNhd (fun z hz ↦ ?_) hV
    refine DifferentiableWithinAt.sub ?_ ((differentiableOn_hurwitzLSum ha0 N z
      ⟨hz.1, hne1 z hz⟩).mono fun w hw ↦ ⟨hw.1, hne1 w hw⟩)
    refine DifferentiableAt.differentiableWithinAt ?_
    have d1 : DifferentiableAt ℂ (fun s : ℂ ↦ ∑ n ∈ range (N + 1), ((n + a : ℝ) : ℂ) ^ (-s)) z := by
      simpa using differentiableAt_sum_cpow_neg a ha0 N 0 z
    have d2 : DifferentiableAt ℂ (fun s : ℂ ↦ ((N + a : ℝ) : ℂ) ^ (1 - s) / (s - 1)) z :=
      (differentiableAt_cpow_terms (N + a) (by positivity) 1 z).div
        (differentiableAt_id.sub (differentiableAt_const _)) (sub_ne_zero.mpr (hne1 z hz))
    have d3 : DifferentiableAt ℂ (fun s : ℂ ↦ hurwitzZeta a (s + 1)) z :=
      (differentiableAt_hurwitzZeta _ (by simpa using hne0 z hz)).comp z
        (differentiableAt_id.add_const 1)
    have d4 := differentiableAt_sum_cpow_neg a ha0 N 1 z
    have d5 : DifferentiableAt ℂ (fun s : ℂ ↦ s / 2) z := differentiableAt_id.div_const 2
    exact (d1.add d2).sub (d5.mul (d3.sub d4))
  have h2 : (2 : ℂ) ∈ V := ⟨by norm_num, by norm_num⟩
  have hev : (fun s ↦ hurwitzZeta a s) =ᶠ[𝓝 2] fun s ↦ ∑ n ∈ range (N + 1),
      ((n + a : ℝ) : ℂ) ^ (-s) + ((N + a : ℝ) : ℂ) ^ (1 - s) / (s - 1) -
      s / 2 * (hurwitzZeta a (s + 1) - ∑ i ∈ range (N + 1), ((i + a : ℝ) : ℂ) ^ (-s - 1)) -
      hurwitzLSum a N s := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds
      (show (2 : ℂ) ∈ {b : ℂ | (1 : ℝ) < b.re} by norm_num)] with z hz
    rw [hurwitzLSum_eq_of_one_lt ha0 ha1 N hz]
    have := hurwitzZeta_eq_J_of_one_lt ha0 ha1 N hz
    linear_combination this
  exact hf.eqOn_of_preconnected_of_eventuallyEq hg isPreconnected_re_gt_neg_one_diff h2 hev hs

/-- **Apostol, Theorem 12.22**, first case (27): for `0 < a ≤ 1`, `N ≥ 0`, `σ > -1`, `s ≠ 0, 1`,
`ζ(s,a) - ∑_{n=0}^{N} (n+a)^{-s} = (N+a)^{1-s}/(s-1) - (s/2)(ζ(s+1,a) - ∑_{n=0}^{N} (n+a)^{-s-1})
  - (s(s+1)/2!) ∑_{n ≥ N} ∫_0^1 u² (n+a+u)^{-s-2} du`.
(`s = 0` must be excluded: there `ζ(s+1, a)` has its pole, and Lean's junk value `ζ(1, a)` makes
the right side wrong.) -/
@[kb "apostol1976" "Thm 12.22, p. 269"]
theorem apostol_thm_12_22 {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1) (N : ℕ) {s : ℂ} (hs : -1 < s.re)
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    hurwitzZeta a s - ∑ n ∈ range (N + 1), ((n + a : ℝ) : ℂ) ^ (-s) =
      ((N + a : ℝ) : ℂ) ^ (1 - s) / (s - 1) -
      s / 2 * (hurwitzZeta a (s + 1) - ∑ n ∈ range (N + 1), ((n + a : ℝ) : ℂ) ^ (-s - 1)) -
      s * (s + 1) / 2 * ∑' n : ℕ, ∫ u in (0 : ℝ)..1,
        (u : ℂ) ^ 2 * ((N + n + a + u : ℝ) : ℂ) ^ (-s - 2) := by
  have hL : s * (s + 1) / 2 * ∑' n : ℕ, ∫ u in (0 : ℝ)..1,
      (u : ℂ) ^ 2 * ((N + n + a + u : ℝ) : ℂ) ^ (-s - 2) = hurwitzLSum a N s := by
    rw [← tsum_mul_left]
    exact tsum_congr fun n ↦ integral_L (by positivity) hs1
  rw [hL, hurwitzZeta_eq_L ha0 ha1 N ⟨hs, by simp [hs0, hs1]⟩]
  ring

lemma hurwitzL_zero (x : ℝ) : hurwitzL x 0 = 0 := by
  simp [hurwitzL, hurwitzJ]

/-- **Apostol, Theorem 12.13** for `n = 0`: `ζ(0, a) = 1/2 - a` (`= -B₁(a)`) for `0 < a ≤ 1`.
(Mathlib's `hurwitzZeta_neg_nat` covers `n ≥ 1`.) Proof: let `s → 0` in Theorem 12.22. -/
@[kb "apostol1976" "Thm 12.13, p. 264"]
theorem hurwitzZeta_zero_eq {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1) :
    hurwitzZeta a 0 = 1 / 2 - a := by
  set R : ℂ → ℂ := fun s ↦ ∑ n ∈ range (0 + 1), ((n + a : ℝ) : ℂ) ^ (-s) +
      ((0 + a : ℝ) : ℂ) ^ (1 - s) / (s - 1) -
      s / 2 * (hurwitzZeta a (s + 1) - ∑ i ∈ range (0 + 1), ((i + a : ℝ) : ℂ) ^ (-s - 1)) -
      hurwitzLSum a 0 s
  have hev : (fun s ↦ hurwitzZeta a s) =ᶠ[𝓝[≠] 0] R := by
    have hV : IsOpen ({s : ℂ | -1 < s.re} \ {1}) := isOpen_re_gt_diff _ isClosed_singleton
    filter_upwards [nhdsWithin_le_nhds (hV.mem_nhds (show (0 : ℂ) ∈ _ by simp)),
      self_mem_nhdsWithin] with z hz hz0
    have hz0' : z ≠ 0 := hz0
    exact hurwitzZeta_eq_L ha0 ha1 0 ⟨hz.1, by simp [hz0', show z ≠ 1 from hz.2]⟩
  have hres : Tendsto (fun s : ℂ ↦ s * hurwitzZeta a (s + 1)) (𝓝[≠] 0) (𝓝 1) := by
    have h1 : Tendsto (fun s : ℂ ↦ s + 1) (𝓝[≠] 0) (𝓝[≠] 1) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · exact ((continuous_id.add continuous_const).tendsto' 0 1 (by simp)).mono_left
          nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with z hz
        simpa using hz
    have := (hurwitzZeta_residue_one a).comp h1
    refine this.congr fun s ↦ ?_
    simp
  have hc : ∀ (x : ℝ), 0 < x → ∀ c : ℂ,
      Tendsto (fun s : ℂ ↦ (x : ℂ) ^ (c - s)) (𝓝[≠] 0) (𝓝 ((x : ℂ) ^ c)) := by
    intro x hx c
    have := (differentiableAt_cpow_terms x hx c 0).continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds (s := {(0 : ℂ)}ᶜ))
    simpa using this
  have hLc : Tendsto (hurwitzLSum a 0) (𝓝[≠] 0) (𝓝 0) := by
    have hV : IsOpen ({s : ℂ | -1 < s.re} \ {1}) := isOpen_re_gt_diff _ isClosed_singleton
    have h0 : (0 : ℂ) ∈ {s : ℂ | -1 < s.re} \ {1} := by simp
    have hcont := ((differentiableOn_hurwitzLSum ha0 0).differentiableAt
      (hV.mem_nhds h0)).continuousAt
    have hval : hurwitzLSum a 0 0 = 0 := by simp [hurwitzLSum, hurwitzL_zero]
    have := hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := {(0 : ℂ)}ᶜ))
    rwa [hval] at this
  have hR : Tendsto R (𝓝[≠] 0) (𝓝 (1 / 2 - a)) := by
    have e1 := hc a ha0 0
    have e2 := hc a ha0 1
    have e3 := hc a ha0 (-1)
    have hid : Tendsto (fun s : ℂ ↦ s) (𝓝[≠] 0) (𝓝 0) := tendsto_nhdsWithin_of_tendsto_nhds
      (continuous_id.tendsto 0)
    have hden : Tendsto (fun s : ℂ ↦ s - 1) (𝓝[≠] 0) (𝓝 (-1)) := by
      simpa using hid.sub_const 1
    have := ((e1.add (e2.div hden (by norm_num))).sub
      ((hres.div_const 2).sub ((hid.div_const 2).mul e3))).sub hLc
    convert this using 2
    · simp only [R, Pi.div_apply, range_one, sum_singleton, zero_add,
        CharP.cast_eq_zero]
      ring_nf
    · simp
      ring
  have hcont : Tendsto (fun s ↦ hurwitzZeta a s) (𝓝[≠] 0) (𝓝 (hurwitzZeta a 0)) :=
    (differentiableAt_hurwitzZeta _ zero_ne_one).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  exact tendsto_nhds_unique hcont (hR.congr' hev.symm)

end NTKB.Apostol
