/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import NTKB.Analytic.Davenport.Hadamard.Order

/-!
# Zero-free entire functions of finite order (Davenport, Chapter 11, p. 74–75)

**Davenport, p. 74.** An entire function of finite order without zeros is `e^{g(z)}` with `g` a
polynomial, of degree equal to the order. Davenport adds (p. 75): it suffices that the bound for
`f` on `|z| = R` hold for a sequence of radii `R` tending to infinity.

## Main results

* `NTKB.exists_entire_exp_eq`: a zero-free entire function is `exp ∘ g` with `g` entire.
* `NTKB.exists_polynomial_of_norm_le_on_circles`: Davenport's "future reference" form: a zero-free
  entire `f` with `‖f z‖ ≤ exp (C R^a)` on `|z| = R` for arbitrarily large `R` is `exp ∘ P` with
  `deg P ≤ a`.
* `NTKB.Davenport.zeroFree_finiteOrder_eq_exp_polynomial` (row 11-3): the theorem itself, with
  `deg P = entireOrder f`.

Proof: as in Davenport, `g = log f` is entire and `Re g ≤ C R^a` on `|z| ≤ R` (maximum modulus).
Davenport bounds the Taylor coefficients of `g` by Fourier integrals of `Re g`; we use instead the
Borel–Carathéodory theorem of Mathlib (`Complex.borelCaratheodory`), which packages exactly that
argument, followed by Cauchy's estimate.
-/

open Filter Topology Metric Complex
open scoped ENNReal NNReal Nat

namespace NTKB

/-- A zero-free entire function has an entire logarithm. -/
theorem exists_entire_exp_eq {f : ℂ → ℂ} (hf : Differentiable ℂ f) (h0 : ∀ z, f z ≠ 0) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ ∀ z, f z = Complex.exp (g z) := by
  have hdf : Differentiable ℂ (deriv f) := fun z ↦
    ((hf.analyticAt z).deriv).differentiableAt
  have hq : Differentiable ℂ (fun z ↦ deriv f z / f z) := hdf.div hf h0
  obtain ⟨G, hG⟩ := hq.isExactOn_univ
  set c := Complex.log (f 0) - G 0
  set g := fun z ↦ G z + c
  have hg : ∀ z, HasDerivAt g (deriv f z / f z) z := fun z ↦ (hG z trivial).add_const c
  have hgd : Differentiable ℂ g := fun z ↦ (hg z).differentiableAt
  refine ⟨g, hgd, ?_⟩
  -- `exp (g z) / f z` has derivative zero
  set h := fun z ↦ Complex.exp (g z) / f z
  have hderiv : ∀ z, HasDerivAt h 0 z := by
    intro z
    have h1 := ((hg z).cexp).div (hf z).hasDerivAt (h0 z)
    convert h1 using 1
    have : Complex.exp (g z) * (deriv f z / f z) * f z - Complex.exp (g z) * deriv f z = 0 := by
      rw [mul_div_assoc', div_mul_cancel₀ _ (h0 z), sub_self]
    rw [this, zero_div]
  have hconst := is_const_of_deriv_eq_zero (f := h) (fun z ↦ (hderiv z).differentiableAt)
    (fun z ↦ (hderiv z).deriv)
  intro z
  have h00 : h 0 = 1 := by
    simp only [h, g, c, add_sub_cancel, Complex.exp_log (h0 0)]
    exact div_self (h0 0)
  have : h z = 1 := (hconst z 0).trans h00
  simp only [h] at this
  rw [div_eq_one_iff_eq (h0 z)] at this
  exact this.symm

/-- Cauchy estimate turned into vanishing: if `‖h‖ ≤ B R^a` on circles `|z| = R` for arbitrarily
large `R`, then the Taylor coefficients of order `n > a` at `0` vanish. -/
lemma iteratedDeriv_eq_zero_of_norm_le_on_circles {h : ℂ → ℂ} (hh : Differentiable ℂ h)
    {a B : ℝ} (hR : ∀ T : ℝ, ∃ R ≥ T, ∀ z : ℂ, ‖z‖ = R → ‖h z‖ ≤ B * R ^ a)
    {n : ℕ} (hn : a < n) : iteratedDeriv n h 0 = 0 := by
  by_contra hne
  have hδ : 0 < ‖iteratedDeriv n h 0‖ := norm_pos_iff.mpr hne
  -- `n! * B * R^a / R^n → 0`
  have hlim : Tendsto (fun R : ℝ ↦ n ! * |B| * R ^ (a - n)) atTop (𝓝 0) := by
    have := tendsto_rpow_neg_atTop (y := (n : ℝ) - a) (by linarith)
    simpa [neg_sub] using this.const_mul ((n ! : ℝ) * |B|)
  obtain ⟨T, hT⟩ := (hlim.eventually (gt_mem_nhds hδ)).exists_forall_of_atTop
  obtain ⟨R, hRT, hRb⟩ := hR (max T 1)
  have hR1 : 1 ≤ R := le_trans (le_max_right _ _) hRT
  have hR0 : 0 < R := by linarith
  have hc := norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le (c := 0) (C := |B| * R ^ a) n hR0
    hh.diffContOnCl (fun z hz ↦ by
      have hz' : ‖z‖ = R := by simpa using hz
      exact (hRb z hz').trans (by gcongr; exact le_abs_self B))
  have hcalc : (n ! : ℝ) * (|B| * R ^ a) / R ^ n = n ! * |B| * R ^ (a - n) := by
    rw [Real.rpow_sub hR0, Real.rpow_natCast]
    field_simp
  have := hT R (le_trans (le_max_left _ _) hRT)
  rw [hcalc] at hc
  linarith

/-- An entire function whose Taylor coefficients at `0` vanish beyond `N` is a polynomial of degree
at most `N`. -/
lemma exists_polynomial_of_iteratedDeriv_eq_zero {h : ℂ → ℂ} (hh : Differentiable ℂ h) {N : ℕ}
    (hN : ∀ n, N < n → iteratedDeriv n h 0 = 0) :
    ∃ P : Polynomial ℂ, P.natDegree ≤ N ∧ ∀ z, h z = P.eval z := by
  refine ⟨∑ n ∈ Finset.range (N + 1),
    Polynomial.C ((n ! : ℂ)⁻¹ * iteratedDeriv n h 0) * Polynomial.X ^ n, ?_, fun z ↦ ?_⟩
  · refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun n hn ↦ ?_
    refine (Polynomial.natDegree_C_mul_X_pow_le _ _).trans ?_
    simpa [Nat.lt_succ_iff] using hn
  · rw [← taylorSeries_eq_of_entire' (c := 0) (z := z) hh, tsum_eq_sum (s := Finset.range (N + 1))]
    · simp [Polynomial.eval_finsetSum]
    · intro n hn
      simp only [Finset.mem_range, not_lt] at hn
      simp [hN n (by omega)]

/-- **Davenport, p. 74–75** (the form "for future reference"): a zero-free entire function with
`‖f z‖ ≤ exp (C R^a)` on the circles `|z| = R` of a sequence of radii tending to infinity is
`exp ∘ P` for a polynomial `P` of degree at most `a`. -/
@[kb "davenport1980" "Ch 11, p. 74-75"]
theorem exists_polynomial_of_norm_le_on_circles {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (h0 : ∀ z, f z ≠ 0) {a C : ℝ} (ha : 0 ≤ a)
    (hR : ∀ T : ℝ, ∃ R ≥ T, ∀ z : ℂ, ‖z‖ = R → ‖f z‖ ≤ Real.exp (C * R ^ a)) :
    ∃ P : Polynomial ℂ, (P.natDegree : ℝ) ≤ a ∧ ∀ z, f z = Complex.exp (P.eval z) := by
  obtain ⟨g, hg, hfg⟩ := exists_entire_exp_eq hf h0
  set h := fun z ↦ g z - g 0
  have hh : Differentiable ℂ h := hg.sub_const _
  have hh0 : h 0 = 0 := by simp [h]
  -- `Re g z = log ‖f z‖`
  have hre : ∀ z, (g z).re = Real.log ‖f z‖ := fun z ↦ by
    rw [hfg z, Complex.norm_exp, Real.log_exp]
  set K := |(g 0).re| + 1
  -- bound on circles of radius `R / 2`
  have hcirc : ∀ T : ℝ, ∃ R ≥ T, ∀ z : ℂ, ‖z‖ = R → ‖h z‖ ≤ (2 * 2 ^ a * |C| + 2 * K) * R ^ a := by
    intro T
    obtain ⟨R, hRT, hRb⟩ := hR (2 * max T 1)
    have hR2 : 2 ≤ R := le_trans (by linarith [le_max_right T 1]) hRT
    have hR0 : 0 < R := by linarith
    refine ⟨R / 2, by linarith [le_max_left T 1], fun z hz ↦ ?_⟩
    -- maximum modulus: `‖f‖ ≤ exp (C R^a)` on the closed ball
    have hball : ∀ w ∈ closedBall (0 : ℂ) R, ‖f w‖ ≤ Real.exp (C * R ^ a) := by
      intro w hw
      refine Complex.norm_le_of_forall_mem_frontier_norm_le (U := ball (0 : ℂ) R)
        isBounded_ball hf.diffContOnCl (fun u hu ↦ ?_) ?_
      · rw [frontier_ball _ hR0.ne'] at hu
        exact hRb u (by simpa using hu)
      · rwa [closure_ball _ hR0.ne']
    have hRa : 1 ≤ R ^ a := Real.one_le_rpow (by linarith) ha
    set M := |C| * R ^ a + K
    have hM : 0 < M := by positivity
    have hmaps : Set.MapsTo h (ball (0 : ℂ) R) {w | w.re ≤ M} := by
      intro w hw
      simp only [Set.mem_ofPred_eq, h, sub_re, hre w]
      have hfw := hball w (ball_subset_closedBall hw)
      have hpos : 0 < ‖f w‖ := norm_pos_iff.mpr (h0 w)
      have hlog : Real.log ‖f w‖ ≤ C * R ^ a := by
        rw [← Real.log_exp (C * R ^ a)]
        exact Real.log_le_log hpos hfw
      have : C * R ^ a ≤ |C| * R ^ a := by gcongr; exact le_abs_self C
      have : -(g 0).re ≤ |(g 0).re| := neg_le_abs _
      simp only [M, K]
      linarith
    have hz' : z ∈ ball (0 : ℂ) R := by simp [hz]; linarith
    have hbc := Complex.borelCaratheodory hM hh.differentiableOn hmaps hR0 hz'
    rw [hh0, norm_zero, zero_mul, zero_div, add_zero, hz] at hbc
    have hRa2' : R ^ a = 2 ^ a * (R / 2) ^ a := by
      rw [← Real.mul_rpow (by norm_num) (by linarith)]; ring_nf
    have hRa2 : 1 ≤ (R / 2) ^ a := Real.one_le_rpow (by linarith) ha
    calc ‖h z‖ ≤ 2 * M * (R / 2) / (R - R / 2) := hbc
      _ = 2 * M := by field_simp; ring
      _ = 2 * |C| * (2 ^ a * (R / 2) ^ a) + 2 * K := by rw [← hRa2']; ring
      _ ≤ (2 * 2 ^ a * |C| + 2 * K) * (R / 2) ^ a := by
          nlinarith [abs_nonneg C, show (0 : ℝ) ≤ K by positivity]
  -- hence the Taylor coefficients of `h` vanish beyond `⌊a⌋`
  set N := ⌊a⌋₊
  have hcoef : ∀ n, N < n → iteratedDeriv n h 0 = 0 := by
    intro n hn
    have han : a < n := by
      have := Nat.lt_floor_add_one a
      have : ((N + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
      push_cast at this
      linarith
    exact iteratedDeriv_eq_zero_of_norm_le_on_circles hh hcirc han
  obtain ⟨Q, hQ, hQh⟩ := exists_polynomial_of_iteratedDeriv_eq_zero hh hcoef
  refine ⟨Q + Polynomial.C (g 0), ?_, fun z ↦ ?_⟩
  · have : (Q + Polynomial.C (g 0)).natDegree ≤ N :=
      (Polynomial.natDegree_add_C).le.trans hQ
    exact (Nat.cast_le.mpr this).trans (Nat.floor_le ha)
  · rw [hfg z, Polynomial.eval_add, Polynomial.eval_C, ← hQh z]
    simp [h]

/-- If `exp ∘ P = exp ∘ Q` for polynomials `P`, `Q`, then `P - Q` is constant, so
`deg P ≤ deg Q`. -/
lemma natDegree_le_of_exp_eval_eq {P Q : Polynomial ℂ}
    (h : ∀ z, Complex.exp (P.eval z) = Complex.exp (Q.eval z)) : P.natDegree ≤ Q.natDegree := by
  have hD : (P - Q).derivative = 0 := by
    refine Polynomial.funext fun z ↦ ?_
    have h1 : HasDerivAt (fun w ↦ Complex.exp ((P - Q).eval w))
        (Complex.exp ((P - Q).eval z) * (P - Q).derivative.eval z) z :=
      ((P - Q).hasDerivAt z).cexp
    have hconst : (fun w ↦ Complex.exp ((P - Q).eval w)) = fun _ ↦ 1 := by
      funext w
      rw [Polynomial.eval_sub, Complex.exp_sub, h w, div_self (Complex.exp_ne_zero _)]
    rw [hconst] at h1
    have := h1.unique (hasDerivAt_const z 1)
    simpa [Complex.exp_ne_zero] using this
  have h0 : (P - Q).natDegree = 0 := Polynomial.derivative_eq_zero.mp hD
  calc P.natDegree = ((P - Q) + Q).natDegree := by rw [sub_add_cancel]
    _ ≤ max (P - Q).natDegree Q.natDegree := Polynomial.natDegree_add_le _ _
    _ = Q.natDegree := by rw [h0]; simp

/-- **Davenport, Ch. 11, p. 74 (row 11-3).** An entire function of finite order without zeros is
`e^{P(z)}` with `P` a polynomial whose degree is the order of the function. -/
@[kb "davenport1980" "Ch 11, p. 74"]
theorem Davenport.zeroFree_finiteOrder_eq_exp_polynomial {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (h0 : ∀ z, f z ≠ 0) (hord : entireOrder f < ⊤) :
    ∃ P : Polynomial ℂ, (∀ z, f z = Complex.exp (P.eval z)) ∧
      (P.natDegree : ℝ≥0∞) = entireOrder f := by
  set ρ : ℝ≥0 := (entireOrder f).toNNReal
  have hρ : entireOrder f = ρ := (ENNReal.coe_toNNReal hord.ne).symm
  -- for every `a > ρ`, a polynomial of degree `≤ a`
  have hpoly : ∀ a : ℝ, (ρ : ℝ) < a →
      ∃ P : Polynomial ℂ, (P.natDegree : ℝ) ≤ a ∧ ∀ z, f z = Complex.exp (P.eval z) := by
    intro a ha
    have hev := eventually_norm_le_exp_of_entireOrder_le hρ.le ha
    obtain ⟨R₀, hR₀⟩ := (Metric.hasBasis_cobounded_compl_closedBall (0 : ℂ)).eventually_iff.mp hev
      |>.imp fun r hr ↦ hr.2
    refine exists_polynomial_of_norm_le_on_circles hf h0 (le_trans ρ.2 ha.le) (C := 1)
      fun T ↦ ⟨max T (R₀ + 1), le_max_left _ _, fun z hz ↦ ?_⟩
    have : z ∈ (closedBall (0 : ℂ) R₀)ᶜ := by
      simp only [Set.mem_compl_iff, mem_closedBall, dist_zero_right, not_le, hz]
      linarith [le_max_right T (R₀ + 1)]
    simpa [hz] using hR₀ this
  obtain ⟨P, -, hP⟩ := hpoly (ρ + 1) (by linarith)
  refine ⟨P, hP, le_antisymm ?_ ?_⟩
  · -- the degree is at most every `a > ρ`
    rw [hρ]
    have hdeg : ∀ a : ℝ, (ρ : ℝ) < a → (P.natDegree : ℝ) ≤ a := by
      intro a ha
      obtain ⟨Q, hQa, hQ⟩ := hpoly a ha
      -- `exp ∘ P = exp ∘ Q`, so `P - Q` is constant
      have := natDegree_le_of_exp_eval_eq (P := P) (Q := Q) fun z ↦ (hP z).symm.trans (hQ z)
      exact (Nat.cast_le.mpr this).trans hQa
    have : (P.natDegree : ℝ) ≤ ρ := le_of_forall_gt_imp_ge_of_dense fun a ha ↦ hdeg a ha
    exact_mod_cast this
  · have := entireOrder_exp_polynomial_le P
    have hfeq : f = fun z ↦ Complex.exp (P.eval z) := funext hP
    rw [hfeq]
    exact this

end NTKB
