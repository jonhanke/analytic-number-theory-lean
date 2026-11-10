/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.RingTheory.Polynomial.Pochhammer
import NTKB.Analytic.Apostol.Zeta.HurwitzEuler

/-!
# Theorem 12.22 of Apostol in general (the expansion (28))

For `0 < a ≤ 1`, integers `N ≥ 0`, `m ≥ 1`, `σ > -m` and `s ∉ {1, 0, -1, …, 1-m}`:
`ζ(s,a) - ∑_{n=0}^{N} (n+a)^{-s} = (N+a)^{1-s}/(s-1)
   - ∑_{r=1}^{m} (s(s+1)⋯(s+r-1)/(r+1)!) (ζ(s+r,a) - ∑_{n=0}^{N} (n+a)^{-s-r})
   - (s(s+1)⋯(s+m)/(m+1)!) ∑_{n ≥ N} ∫_0^1 u^{m+1} (n+a+u)^{-s-m-1} du`.

Proof as in Apostol: repeated integration by parts
(`∫_0^1 u^r (x+u)^{-s-r} du = (x+1)^{-s-r}/(r+1) + ((s+r)/(r+1)) ∫_0^1 u^{r+1}(x+u)^{-s-r-1} du`),
then analytic continuation as for `m = 1` (`Zeta/HurwitzEuler.lean`).
`s(s+1)⋯(s+r-1)` is Mathlib's `(ascPochhammer ℂ r).eval s`.
-/

open Complex Filter Topology Finset MeasureTheory intervalIntegral HurwitzZeta

namespace NTKB.Apostol

/-- `s(s+1)⋯(s+r-1)`. -/
noncomputable abbrev cpoch (r : ℕ) (s : ℂ) : ℂ := (ascPochhammer ℂ r).eval s

lemma cpoch_succ (r : ℕ) (s : ℂ) : cpoch (r + 1) s = cpoch r s * (s + r) :=
  ascPochhammer_succ_eval r s

lemma norm_cpoch_le (r : ℕ) (s : ℂ) : ‖cpoch r s‖ ≤ (‖s‖ + r) ^ r := by
  induction r with
  | zero => simp [cpoch]
  | succ r ih =>
    rw [cpoch_succ, norm_mul, pow_succ]
    have h1 : ‖s + r‖ ≤ ‖s‖ + (r + 1 : ℕ) := by
      refine (norm_add_le _ _).trans ?_
      push_cast; simp
    have h2 : (‖s‖ + r) ^ r ≤ (‖s‖ + (r + 1 : ℕ)) ^ r := by
      gcongr; push_cast; linarith
    exact mul_le_mul (ih.trans h2) h1 (norm_nonneg _) (by positivity)

lemma continuousOn_pow_mul_cpow {x : ℝ} (hx : 0 < x) (k : ℕ) (r : ℂ) :
    ContinuousOn (fun u : ℝ ↦ (u : ℂ) ^ k * ((x + u : ℝ) : ℂ) ^ r) (Set.uIcc 0 1) := by
  refine (continuous_ofReal.pow k).continuousOn.mul ?_
  refine ContinuousOn.cpow_const (by fun_prop) fun u hu ↦ ?_
  have hu0 : 0 ≤ u := by simp at hu; exact hu.1
  exact ofReal_mem_slitPlane.2 (by linarith)

/-- Integration by parts: `∫_0^1 u^r (x+u)^{-s-r} du = (x+1)^{-s-r}/(r+1)
+ ((s+r)/(r+1)) ∫_0^1 u^{r+1}(x+u)^{-s-r-1} du`. -/
lemma integral_pow_cpow_byParts {x : ℝ} (hx : 0 < x) (r : ℕ) (s : ℂ) :
    ∫ u in (0 : ℝ)..1, (u : ℂ) ^ r * ((x + u : ℝ) : ℂ) ^ (-s - r) =
      ((x + 1 : ℝ) : ℂ) ^ (-s - r) / (r + 1) +
      (s + r) / (r + 1) * ∫ u in (0 : ℝ)..1, (u : ℂ) ^ (r + 1) * ((x + u : ℝ) : ℂ) ^ (-s - (r + 1)) := by
  have hr1 : (r : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero r
  set F : ℝ → ℂ := fun u ↦ (u : ℂ) ^ (r + 1) * ((x + u : ℝ) : ℂ) ^ (-s - r) / (r + 1)
  have hF : ∀ u ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt F ((u : ℂ) ^ r * ((x + u : ℝ) : ℂ) ^ (-s - r) -
      (s + r) / (r + 1) * ((u : ℂ) ^ (r + 1) * ((x + u : ℝ) : ℂ) ^ (-s - (r + 1)))) u := by
    intro u hu
    have hu0 : 0 ≤ u := by simp at hu; exact hu.1
    have hxu : 0 < x + u := by linarith
    have d := (((hasDerivAt_id u).ofReal_comp.pow (r + 1)).mul
      ((hasDerivAt_ofReal_cpow_any hxu (-s - r)).comp_const_add x u)).div_const ((r : ℂ) + 1)
    convert d using 1
    · funext v; simp [F]
    simp only [id, ofReal_one, mul_one, Nat.add_sub_cancel, Pi.pow_apply]
    have e : (-s - r - 1) = -s - (r + 1 : ℂ) := by ring
    rw [e]
    field_simp
    push_cast
    ring
  have hc1 := (continuousOn_pow_mul_cpow hx r (-s - r)).intervalIntegrable (μ := volume)
  have hc2 := (continuousOn_pow_mul_cpow hx (r + 1) (-s - (r + 1))).intervalIntegrable
    (μ := volume)
  have hint := integral_eq_sub_of_hasDerivAt hF (hc1.sub (hc2.const_mul _))
  rw [intervalIntegral.integral_sub hc1 (hc2.const_mul _), intervalIntegral.integral_const_mul]
    at hint
  have hF1 : F 1 = ((x + 1 : ℝ) : ℂ) ^ (-s - r) / (r + 1) := by simp [F]
  have hF0 : F 0 = 0 := by simp [F]
  rw [hF1, hF0, sub_zero] at hint
  linear_combination hint

/-- The coefficient `s(s+1)⋯(s+r-1)/(r+1)!`. -/
noncomputable def hurwitzCoeff (r : ℕ) (s : ℂ) : ℂ := cpoch r s / ((r + 1).factorial : ℂ)

/-- The order-`m` remainder term `J(x,s) - ∑_{r=1}^{m} c_r(s) (x+1)^{-s-r}`. -/
noncomputable def hurwitzLm (m : ℕ) (x : ℝ) (s : ℂ) : ℂ :=
  hurwitzJ x s - ∑ r ∈ Icc 1 m, hurwitzCoeff r s * ((x + 1 : ℝ) : ℂ) ^ (-s - r)

/-- `L_m(x,s) = (s(s+1)⋯(s+m)/(m+1)!) ∫_0^1 u^{m+1} (x+u)^{-s-m-1} du` for `x > 0`, `s ≠ 1`. -/
lemma integral_Lm {x : ℝ} (hx : 0 < x) {s : ℂ} (hs : s ≠ 1) (m : ℕ) :
    hurwitzLm m x s = cpoch (m + 1) s / ((m + 1).factorial : ℂ) *
      ∫ u in (0 : ℝ)..1, (u : ℂ) ^ (m + 1) * ((x + u : ℝ) : ℂ) ^ (-s - (m + 1)) := by
  induction m with
  | zero =>
    simp only [hurwitzLm, zero_add]
    rw [← integral_J hx hs]
    simp [hurwitzCoeff, cpoch]
  | succ m ih =>
    have hsplit : hurwitzLm (m + 1) x s = hurwitzLm m x s -
        hurwitzCoeff (m + 1) s * ((x + 1 : ℝ) : ℂ) ^ (-s - ((m + 1 : ℕ) : ℂ)) := by
      simp only [hurwitzLm]
      rw [show Icc 1 (m + 1) = insert (m + 1) (Icc 1 m) by
        ext i; simp; omega, sum_insert (by simp)]
      ring
    have hb := integral_pow_cpow_byParts hx (m + 1) s
    rw [hsplit, ih]
    push_cast at hb ⊢
    rw [hb]
    have hf : ((m + 1 + 1).factorial : ℂ) = ((m + 1 + 1 : ℕ) : ℂ) * ((m + 1).factorial : ℂ) := by
      rw [Nat.factorial_succ]; push_cast; ring
    have hf0 : ((m + 1).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    have hm2 : ((m : ℂ) + 1 + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (m + 1)
    simp only [hurwitzCoeff, cpoch_succ, hf]
    push_cast
    field_simp
    ring_nf

/-- `‖L_m(x,s)‖ ≤ (‖s(s+1)⋯(s+m)‖/(m+1)!) x^{-σ-m-1}` for `x > 0`, `s ≠ 1`, `σ ≥ -m-1`. -/
lemma norm_hurwitzLm_le {x : ℝ} (hx : 0 < x) {s : ℂ} (hs : s ≠ 1) (m : ℕ)
    (hσ : -(m : ℝ) - 1 ≤ s.re) :
    ‖hurwitzLm m x s‖ ≤ ‖cpoch (m + 1) s‖ / (m + 1).factorial * x ^ (-s.re - m - 1) := by
  rw [integral_Lm hx hs, norm_mul, norm_div, Complex.norm_natCast]
  gcongr
  have := norm_integral_le_of_norm_le_const (a := 0) (b := 1)
    (f := fun u : ℝ ↦ (u : ℂ) ^ (m + 1) * ((x + u : ℝ) : ℂ) ^ (-s - (m + 1)))
    (C := x ^ (-s.re - m - 1)) (fun u hu ↦ by
      rw [Set.uIoc_of_le zero_le_one] at hu
      rw [norm_mul, norm_pow, norm_real, Real.norm_of_nonneg hu.1.le]
      calc u ^ (m + 1) * ‖((x + u : ℝ) : ℂ) ^ (-s - (m + 1))‖ ≤ 1 * x ^ (-s.re - m - 1) := by
            gcongr
            · exact pow_le_one₀ hu.1.le hu.2
            · have h := norm_ofReal_add_cpow_le hx hu.1.le (r := -s - (m + 1))
                (by simp; linarith)
              refine h.trans (le_of_eq ?_)
              congr 1
              simp; ring
        _ = _ := one_mul _)
  simpa using this

lemma differentiableAt_hurwitzCoeff (r : ℕ) (s : ℂ) :
    DifferentiableAt ℂ (hurwitzCoeff r) s :=
  ((ascPochhammer ℂ r).differentiable.differentiableAt).div_const _

lemma differentiableAt_hurwitzLm {x : ℝ} (hx : 0 < x) {s : ℂ} (hs : s ≠ 1) (m : ℕ) :
    DifferentiableAt ℂ (hurwitzLm m x) s := by
  have hx1 : ((x + 1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by linarith : x + 1 ≠ 0)
  unfold hurwitzLm
  refine (differentiableAt_hurwitzJ hx hs).sub (DifferentiableAt.fun_sum fun r _ ↦ ?_)
  exact (differentiableAt_hurwitzCoeff r s).mul
    ((differentiableAt_id.neg.sub_const _).const_cpow (Or.inl hx1))

/-- `∑_{n ≥ 0} L_m(N + n + a, s)`. -/
noncomputable def hurwitzLmSum (a : ℝ) (N m : ℕ) (s : ℂ) : ℂ :=
  ∑' n : ℕ, hurwitzLm m (N + n + a) s

/-- `∑ L_m` is analytic on `σ > -m`, `s ≠ 1` (Weierstrass test). -/
lemma differentiableOn_hurwitzLmSum {a : ℝ} (ha : 0 < a) (N m : ℕ) :
    DifferentiableOn ℂ (hurwitzLmSum a N m) ({s : ℂ | -(m : ℝ) < s.re} \ {1}) := by
  intro s₀ hs₀
  have hs₀' : -(m : ℝ) < s₀.re := hs₀.1
  set δ := (s₀.re - m) / 2
  set R := ‖s₀‖ + 1
  set U : Set ℂ := {s | δ < s.re ∧ ‖s‖ < R} \ {1}
  have hU : IsOpen U :=
    ((isOpen_lt continuous_const continuous_re).inter
      (isOpen_lt continuous_norm continuous_const)).sdiff isClosed_singleton
  have hmem : s₀ ∈ U := ⟨⟨by simp only [δ]; linarith, by simp only [R]; linarith⟩, hs₀.2⟩
  have hR : 0 < R := by positivity
  set K : ℝ := (R + (m + 1 : ℕ)) ^ (m + 1) / (m + 1).factorial
  have hdiff : DifferentiableOn ℂ (hurwitzLmSum a N m) U := by
    refine differentiableOn_tsum_of_summable_norm
      (u := fun n : ℕ ↦ K * (((N + n + a : ℝ)) ^ (-δ - m - 1) + ((N + n + a : ℝ)) ^ (-R - m - 1)))
      ?_ ?_ hU ?_
    · exact Summable.mul_left _ ((summable_shift_rpow ha N (by simp only [δ]; linarith)).add
        (summable_shift_rpow ha N (by linarith)))
    · intro n s hs
      exact (differentiableAt_hurwitzLm (by positivity) hs.2 m).differentiableWithinAt
    · intro n s hs
      have hσ : δ < s.re := hs.1.1
      have hσR : s.re < R := (re_le_norm s).trans_lt hs.1.2
      refine (norm_hurwitzLm_le (by positivity) hs.2 m
        (by simp only [δ] at hσ; linarith)).trans ?_
      have hK : ‖cpoch (m + 1) s‖ / (m + 1).factorial ≤ K := by
        simp only [K]
        gcongr
        refine (norm_cpoch_le (m + 1) s).trans ?_
        gcongr
        exact hs.1.2.le
      gcongr
      · exact rpow_le_rpow_add_rpow (by positivity) (by linarith) (by linarith [hs.1.1])
  exact (hdiff s₀ hmem).differentiableAt (hU.mem_nhds hmem) |>.differentiableWithinAt

/-- For `σ > 1`: `∑ L_m = ∑ J - ∑_{r=1}^{m} c_r(s) (ζ(s+r,a) - ∑_{n ≤ N} (n+a)^{-s-r})`. -/
lemma hurwitzLmSum_eq_of_one_lt {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1) (N m : ℕ) {s : ℂ}
    (hs : 1 < s.re) :
    hurwitzLmSum a N m s = hurwitzJSum a N s - ∑ r ∈ Icc 1 m, hurwitzCoeff r s *
      (hurwitzZeta a (s + r) - ∑ i ∈ range (N + 1), ((i + a : ℝ) : ℂ) ^ (-s - r)) := by
  have hs1 : s ≠ 1 := fun h ↦ by simp [h] at hs
  have hg : ∀ r ∈ Icc 1 m, HasSum (fun n : ℕ ↦ hurwitzCoeff r s * ((N + n + a + 1 : ℝ) : ℂ) ^ (-s - r))
      (hurwitzCoeff r s * (hurwitzZeta a (s + r) -
        ∑ i ∈ range (N + 1), ((i + a : ℝ) : ℂ) ^ (-s - r))) := by
    intro r _
    have h := hasSum_hurwitz_shift ha0 ha1 N (s := s + r) (by simp; linarith) (s + r) rfl
    rw [show -(s + r) = -s - r by ring] at h
    exact h.mul_left _
  have hJ := (summable_hurwitzJ ha0 N (by linarith) hs1).hasSum
  have := hJ.sub (hasSum_sum hg)
  rw [hurwitzLmSum, hurwitzJSum, ← this.tsum_eq]
  rfl

/-- `{σ > c} \ S` is preconnected for a set `S` of real points with real parts `< 2`, `c < 2`. -/
theorem isPreconnected_re_gt_diff_real {c : ℝ} (hc : c < 2) {S : Set ℂ}
    (hS : ∀ z ∈ S, z.im = 0 ∧ z.re < 2) : IsPreconnected ({s : ℂ | c < s.re} \ S) := by
  set W₁ : Set ℂ := {s | c < s.re ∧ 0 < s.im}
  set W₂ : Set ℂ := {s | c < s.re ∧ s.im < 0}
  set W₃ : Set ℂ := {s | 2 < s.re}
  have c₁ : Convex ℝ W₁ := (convex_halfSpace_gt reLm.isLinear c).inter
    (convex_halfSpace_gt imLm.isLinear 0)
  have c₂ : Convex ℝ W₂ := (convex_halfSpace_gt reLm.isLinear c).inter
    (convex_halfSpace_lt imLm.isLinear 0)
  have c₃ : Convex ℝ W₃ := convex_halfSpace_gt reLm.isLinear 2
  have m1 : (3 + I) ∈ W₁ := show c < (3 + I).re ∧ 0 < (3 + I).im by norm_num; linarith
  have m3 : (3 + I) ∈ W₃ := show (2 : ℝ) < (3 + I).re by norm_num
  have m3' : (3 - I) ∈ W₃ := show (2 : ℝ) < (3 - I).re by norm_num
  have m2 : (3 - I) ∈ W₂ := show c < (3 - I).re ∧ (3 - I).im < 0 by norm_num; linarith
  have p13 : IsPreconnected (W₁ ∪ W₃) :=
    IsPreconnected.union (3 + I) m1 m3 c₁.isPreconnected c₃.isPreconnected
  have pA : IsPreconnected ((W₁ ∪ W₃) ∪ W₂) :=
    IsPreconnected.union (3 - I) (Or.inr m3') m2 p13 c₂.isPreconnected
  refine pA.subset_closure ?_ ?_
  · rintro z ((h | h) | h)
    · exact ⟨h.1, fun hz ↦ by have := (hS z hz).1; linarith [h.2]⟩
    · exact ⟨by simp only [Set.mem_ofPred_eq]; linarith [show (2 : ℝ) < z.re from h],
        fun hz ↦ by have := (hS z hz).2; linarith [show (2 : ℝ) < z.re from h]⟩
    · exact ⟨h.1, fun hz ↦ by have := (hS z hz).1; linarith [h.2]⟩
  · rintro z ⟨hz, -⟩
    rcases lt_trichotomy z.im 0 with h | h | h
    · exact subset_closure (Or.inr ⟨hz, h⟩)
    · rw [Metric.mem_closure_iff]
      intro ε hε
      refine ⟨z + (ε / 2 : ℝ) * I, Or.inl (Or.inl ⟨by simpa using hz, by simp [h]; positivity⟩), ?_⟩
      rw [dist_eq_norm, show z - (z + (ε / 2 : ℝ) * I) = -((ε / 2 : ℝ) * I) by ring, norm_neg,
        norm_mul, norm_I, mul_one, norm_real, Real.norm_of_nonneg (by positivity)]
      linarith
    · exact subset_closure (Or.inl (Or.inl ⟨hz, h⟩))

/-- The poles `1, 0, -1, …, 1-m` of the terms of (28). -/
noncomputable def hurwitzPoles (m : ℕ) : Set ℂ := ((range (m + 1)).image fun r : ℕ ↦ (1 : ℂ) - r : Finset ℂ)

lemma mem_hurwitzPoles {m : ℕ} {z : ℂ} : z ∈ hurwitzPoles m ↔ ∃ r ≤ m, z = 1 - r := by
  simp only [hurwitzPoles, coe_image, coe_range, Set.mem_image, Set.mem_Iio]
  constructor
  · rintro ⟨r, hr, rfl⟩; exact ⟨r, by omega, rfl⟩
  · rintro ⟨r, hr, rfl⟩; exact ⟨r, by omega, rfl⟩

/-- The identity (28) with the closed-form terms `L_m`, on `σ > -m` minus the poles. -/
lemma hurwitzZeta_eq_Lm {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1) (N m : ℕ) {s : ℂ}
    (hs : s ∈ {s : ℂ | -(m : ℝ) < s.re} \ hurwitzPoles m) :
    hurwitzZeta a s = ∑ n ∈ range (N + 1), ((n + a : ℝ) : ℂ) ^ (-s) +
      ((N + a : ℝ) : ℂ) ^ (1 - s) / (s - 1) -
      ∑ r ∈ Icc 1 m, hurwitzCoeff r s *
        (hurwitzZeta a (s + r) - ∑ i ∈ range (N + 1), ((i + a : ℝ) : ℂ) ^ (-s - r)) -
      hurwitzLmSum a N m s := by
  set V : Set ℂ := {s : ℂ | -(m : ℝ) < s.re} \ hurwitzPoles m
  have hV : IsOpen V := isOpen_re_gt_diff _ (Finset.finite_toSet _).isClosed
  have hne1 : ∀ z ∈ V, z ≠ 1 := fun z hz h ↦ hz.2 (mem_hurwitzPoles.mpr ⟨0, by omega, by simp [h]⟩)
  have hner : ∀ z ∈ V, ∀ r ∈ Icc 1 m, z + r ≠ 1 := fun z hz r hr h ↦
    hz.2 (mem_hurwitzPoles.mpr ⟨r, (mem_Icc.mp hr).2, by linear_combination h⟩)
  have hf : AnalyticOnNhd ℂ (fun s ↦ hurwitzZeta a s) V :=
    DifferentiableOn.analyticOnNhd (fun z hz ↦
      (differentiableAt_hurwitzZeta _ (hne1 z hz)).differentiableWithinAt) hV
  have hg : AnalyticOnNhd ℂ (fun s ↦ ∑ n ∈ range (N + 1), ((n + a : ℝ) : ℂ) ^ (-s) +
      ((N + a : ℝ) : ℂ) ^ (1 - s) / (s - 1) -
      ∑ r ∈ Icc 1 m, hurwitzCoeff r s *
        (hurwitzZeta a (s + r) - ∑ i ∈ range (N + 1), ((i + a : ℝ) : ℂ) ^ (-s - r)) -
      hurwitzLmSum a N m s) V := by
    refine DifferentiableOn.analyticOnNhd (fun z hz ↦ ?_) hV
    refine DifferentiableWithinAt.sub ?_ ((differentiableOn_hurwitzLmSum ha0 N m z
      ⟨hz.1, hne1 z hz⟩).mono fun w hw ↦ ⟨hw.1, hne1 w hw⟩)
    refine DifferentiableAt.differentiableWithinAt ?_
    have d1 : DifferentiableAt ℂ (fun s : ℂ ↦ ∑ n ∈ range (N + 1), ((n + a : ℝ) : ℂ) ^ (-s)) z := by
      simpa using differentiableAt_sum_cpow_neg a ha0 N 0 z
    have d2 : DifferentiableAt ℂ (fun s : ℂ ↦ ((N + a : ℝ) : ℂ) ^ (1 - s) / (s - 1)) z :=
      (differentiableAt_cpow_terms (N + a) (by positivity) 1 z).div
        (differentiableAt_id.sub (differentiableAt_const _)) (sub_ne_zero.mpr (hne1 z hz))
    have d3 : DifferentiableAt ℂ (fun s : ℂ ↦ ∑ r ∈ Icc 1 m, hurwitzCoeff r s *
        (hurwitzZeta a (s + r) - ∑ i ∈ range (N + 1), ((i + a : ℝ) : ℂ) ^ (-s - r))) z := by
      refine DifferentiableAt.fun_sum fun r hr ↦ ?_
      refine (differentiableAt_hurwitzCoeff r z).mul (DifferentiableAt.sub ?_
        (differentiableAt_sum_cpow_neg a ha0 N r z))
      exact (differentiableAt_hurwitzZeta _ (hner z hz r hr)).comp z
        (differentiableAt_id.add_const _)
    exact (d1.add d2).sub d3
  have h2 : (2 : ℂ) ∈ V := ⟨by simp; linarith [m.cast_nonneg (α := ℝ)], fun h ↦ by
    obtain ⟨r, -, hr⟩ := mem_hurwitzPoles.mp h
    have := congrArg re hr
    simp at this
    linarith [r.cast_nonneg (α := ℝ)]⟩
  have hev : (fun s ↦ hurwitzZeta a s) =ᶠ[𝓝 2] fun s ↦ ∑ n ∈ range (N + 1),
      ((n + a : ℝ) : ℂ) ^ (-s) + ((N + a : ℝ) : ℂ) ^ (1 - s) / (s - 1) -
      ∑ r ∈ Icc 1 m, hurwitzCoeff r s *
        (hurwitzZeta a (s + r) - ∑ i ∈ range (N + 1), ((i + a : ℝ) : ℂ) ^ (-s - r)) -
      hurwitzLmSum a N m s := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds
      (show (2 : ℂ) ∈ {b : ℂ | (1 : ℝ) < b.re} by norm_num)] with z hz
    rw [hurwitzLmSum_eq_of_one_lt ha0 ha1 N m hz]
    have := hurwitzZeta_eq_J_of_one_lt ha0 ha1 N hz
    linear_combination this
  have hpc : IsPreconnected V := by
    refine isPreconnected_re_gt_diff_real (by linarith [m.cast_nonneg (α := ℝ)]) fun z hz ↦ ?_
    obtain ⟨r, -, rfl⟩ := mem_hurwitzPoles.mp hz
    simp
    linarith [r.cast_nonneg (α := ℝ)]
  exact hf.eqOn_of_preconnected_of_eventuallyEq hg hpc h2 hev hs

/-- **Apostol, Theorem 12.22** (28): for `0 < a ≤ 1`, integers `N, m ≥ 0`, `σ > -m`,
`s ∉ {1, 0, -1, …, 1-m}`:
`ζ(s,a) - ∑_{n=0}^{N} (n+a)^{-s} = (N+a)^{1-s}/(s-1)
  - ∑_{r=1}^{m} (s(s+1)⋯(s+r-1)/(r+1)!) (ζ(s+r,a) - ∑_{n=0}^{N} (n+a)^{-s-r})
  - (s(s+1)⋯(s+m)/(m+1)!) ∑_{n ≥ N} ∫_0^1 u^{m+1} (n+a+u)^{-s-m-1} du`.
(The excluded points are the poles of `ζ(s,a)` and `ζ(s+r,a)`; there Lean's junk values make the
identity meaningless.) -/
@[kb "apostol1976" "Thm 12.22, p. 269"]
theorem apostol_thm_12_22_general {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1) (N m : ℕ) {s : ℂ}
    (hs : -(m : ℝ) < s.re) (hpole : ∀ r : ℕ, r ≤ m → s ≠ 1 - r) :
    hurwitzZeta a s - ∑ n ∈ range (N + 1), ((n + a : ℝ) : ℂ) ^ (-s) =
      ((N + a : ℝ) : ℂ) ^ (1 - s) / (s - 1) -
      ∑ r ∈ Icc 1 m, cpoch r s / ((r + 1).factorial : ℂ) *
        (hurwitzZeta a (s + r) - ∑ n ∈ range (N + 1), ((n + a : ℝ) : ℂ) ^ (-s - r)) -
      cpoch (m + 1) s / ((m + 1).factorial : ℂ) * ∑' n : ℕ, ∫ u in (0 : ℝ)..1,
        (u : ℂ) ^ (m + 1) * ((N + n + a + u : ℝ) : ℂ) ^ (-s - (m + 1)) := by
  have hs1 : s ≠ 1 := by simpa using hpole 0 (Nat.zero_le _)
  have hL : cpoch (m + 1) s / ((m + 1).factorial : ℂ) * ∑' n : ℕ, ∫ u in (0 : ℝ)..1,
      (u : ℂ) ^ (m + 1) * ((N + n + a + u : ℝ) : ℂ) ^ (-s - (m + 1)) = hurwitzLmSum a N m s := by
    rw [← tsum_mul_left]
    exact tsum_congr fun n ↦ (integral_Lm (by positivity) hs1 m).symm
  rw [hL, hurwitzZeta_eq_Lm ha0 ha1 N m ⟨hs, fun h ↦ by
    obtain ⟨r, hr, hr'⟩ := mem_hurwitzPoles.mp h
    exact hpole r hr hr'⟩]
  simp only [hurwitzCoeff]
  ring

end NTKB.Apostol
