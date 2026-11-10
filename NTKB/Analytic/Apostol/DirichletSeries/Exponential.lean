/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.NumberTheory.LSeries.Convolution
import Mathlib.NumberTheory.LSeries.Deriv
import Mathlib.NumberTheory.LSeries.Injectivity
import Mathlib.Analysis.Complex.ExponentialBounds
import NTKB.Analytic.Apostol.ArithmeticFunctions.Derivative

/-!
# Dirichlet series as exponentials of Dirichlet series (Apostol, Theorem 11.14)

Let `F(s) = ∑ f(n) n^{-s}` with `f(1) ≠ 0`. Then `F(s) = e^{G(s)}` with
`G(s) = log f(1) + ∑_{n ≥ 2} ((f' * f⁻¹)(n)/log n) n^{-s}`, where `f⁻¹` is the Dirichlet inverse
and `f'(n) = f(n) log n` (`arithDeriv`).

Apostol states this for `σ > σ₀` where `F(s) ≠ 0`; his proof uses
`F'(s)/F(s) = -∑ f'(n) n^{-s} · ∑ f⁻¹(n) n^{-s}`, i.e. that the Dirichlet series of `f⁻¹`
converges absolutely there (it is then `1/F(s)`, so `F ≠ 0` follows). We state the theorem with
this hypothesis, which is what the proof needs.

Proof as in Apostol: `G' = F'/F`, so `F e^{-G}` has derivative `0` on the half-plane, hence is
constant; letting `σ → +∞`, `F → f(1)` and `G → log f(1)`, so the constant is `1`.
-/

open Complex Filter Topology LSeries ArithmeticFunction

namespace NTKB.Apostol

/-- The coefficients of `G(s)`: `log f(1)` at `n = 1`, `(f' * f⁻¹)(n)/log n` for `n ≥ 2`. -/
noncomputable def expDirichletCoeff (f : ArithmeticFunction ℂ) (hf1 : f 1 ≠ 0) (n : ℕ) : ℂ :=
  if n = 1 then Complex.log (f 1)
  else (arithDeriv f * dirichletInverse f (invertibleOfNonzero hf1)) n / Real.log n

lemma coe_arithDeriv_eq_logMul (f : ArithmeticFunction ℂ) : ⇑(arithDeriv f) = logMul ⇑f := by
  funext n
  simp [arithDeriv, logMul, Complex.real_smul, natCast_log]

lemma logMul_expDirichletCoeff (f : ArithmeticFunction ℂ) (hf1 : f 1 ≠ 0) :
    logMul (expDirichletCoeff f hf1) = ⇑(arithDeriv f * dirichletInverse f (invertibleOfNonzero hf1)) := by
  funext n
  simp only [logMul, expDirichletCoeff]
  rcases Nat.lt_trichotomy n 1 with h | rfl | h
  · obtain rfl : n = 0 := by omega
    simp
  · simp only [↓reduceIte, Nat.cast_one, Complex.log_one, zero_mul]
    rw [ArithmeticFunction.mul_apply]
    simp [arithDeriv]
  · simp only [show ¬ (n = 1) by omega, ↓reduceIte]
    have hlog : (Real.log n : ℂ) ≠ 0 := by
      have : 1 < (n : ℝ) := by exact_mod_cast h
      exact_mod_cast (Real.log_pos this).ne'
    rw [← natCast_log]
    field_simp

/-- **Apostol, Theorem 11.14**: if `∑ f(n) n^{-s}` and `∑ f⁻¹(n) n^{-s}` converge absolutely for
`σ > σ₀` and `f(1) ≠ 0`, then for `σ > σ₀`, `F(s) = e^{G(s)}` with
`G(s) = log f(1) + ∑_{n ≥ 2} ((f' * f⁻¹)(n)/log n) n^{-s}` (absolutely convergent). -/
@[kb "apostol1976" "Thm 11.14, p. 237"]
theorem apostol_thm_11_14 (f : ArithmeticFunction ℂ) (hf1 : f 1 ≠ 0) {σ₀ : ℝ}
    (hF : ∀ s : ℂ, σ₀ < s.re → LSeriesSummable ⇑f s)
    (hFinv : ∀ s : ℂ, σ₀ < s.re →
      LSeriesSummable ⇑(dirichletInverse f (invertibleOfNonzero hf1)) s)
    {s : ℂ} (hs : σ₀ < s.re) :
    LSeriesSummable (expDirichletCoeff f hf1) s ∧
      LSeries ⇑f s = cexp (LSeries (expDirichletCoeff f hf1) s) := by
  set finv := dirichletInverse f (invertibleOfNonzero hf1)
  set fd := arithDeriv f
  set h := fd * finv
  set g := expDirichletCoeff f hf1
  -- abscissae
  have habs : ∀ {u : ℕ → ℂ}, (∀ s : ℂ, σ₀ < s.re → LSeriesSummable u s) →
      abscissaOfAbsConv u ≤ σ₀ := fun hu ↦
    abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy ↦ hu y (by simpa using hy)
  have hlt : ∀ {u : ℕ → ℂ}, (∀ s : ℂ, σ₀ < s.re → LSeriesSummable u s) →
      ∀ z : ℂ, σ₀ < z.re → abscissaOfAbsConv u < z.re := fun hu z hz ↦
    (habs hu).trans_lt (by exact_mod_cast hz)
  have hfd : ∀ z : ℂ, σ₀ < z.re → LSeriesSummable ⇑fd z := fun z hz ↦ by
    rw [coe_arithDeriv_eq_logMul]
    exact LSeriesSummable_logMul_of_lt_re (hlt hF z hz)
  have hh : ∀ z : ℂ, σ₀ < z.re → LSeriesSummable ⇑h z := fun z hz ↦
    LSeriesSummable_mul (hfd z hz) (hFinv z hz)
  have hg : ∀ z : ℂ, σ₀ < z.re → LSeriesSummable g z := by
    intro z hz
    refine Summable.of_norm_bounded_eventually (g := fun n ↦ ‖term (⇑h) z n‖) (hh z hz).norm ?_
    have : ∀ᶠ n : ℕ in cofinite, 3 ≤ n := by
      simpa using (Filter.eventually_ge_atTop 3).filter_mono Nat.cofinite_eq_atTop.le
    filter_upwards [this] with n hn
    have hn0 : n ≠ 0 := by omega
    rw [term_of_ne_zero hn0, term_of_ne_zero hn0, norm_div, norm_div]
    gcongr
    simp only [g, expDirichletCoeff, show ¬ (n = 1) by omega, ↓reduceIte, norm_div]
    have hlog : 1 ≤ Real.log n := by
      rw [Real.le_log_iff_exp_le (by positivity)]
      have : (3 : ℝ) ≤ n := by exact_mod_cast hn
      linarith [Real.exp_one_lt_three]
    rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    exact div_le_self (norm_nonneg _) hlog
  -- `f * h = f'`
  have hfh : f * h = fd := by
    simp only [h, finv]
    rw [mul_comm fd, ← mul_assoc, self_mul_dirichletInverse, one_mul]
  -- the function `H(s) = F(s) e^{-G(s)}`
  set U : Set ℂ := {z | σ₀ < z.re}
  have hU : IsOpen U := isOpen_lt continuous_const continuous_re
  have hUc : IsPreconnected U := (convex_halfSpace_gt reLm.isLinear σ₀).isPreconnected
  set H : ℂ → ℂ := fun z ↦ LSeries ⇑f z * cexp (-LSeries g z)
  have hHd : ∀ z ∈ U, HasDerivAt H 0 z := by
    intro z hz
    have dF := LSeries_hasDerivAt (hlt hF z hz)
    have dG := LSeries_hasDerivAt (hlt hg z hz)
    have d := dF.mul (dG.neg.cexp)
    convert d using 1
    rw [logMul_expDirichletCoeff, ← coe_arithDeriv_eq_logMul]
    change (0 : ℂ) = -LSeries ⇑fd z * cexp (-LSeries g z) +
      LSeries ⇑f z * (cexp (-LSeries g z) * -(-LSeries ⇑h z))
    rw [← hfh, LSeries_mul' (hF z hz) (hh z hz)]
    ring
  have hHdiff : DifferentiableOn ℂ H U := fun z hz ↦ (hHd z hz).differentiableAt.differentiableWithinAt
  have hHderiv : U.EqOn (deriv H) 0 := fun z hz ↦ (hHd z hz).deriv
  -- `H(σ) → 1` as `σ → ∞`
  have hlimF := LSeries.tendsto_atTop (f := ⇑f) ((habs hF).trans_lt (EReal.coe_lt_top σ₀))
  have hlimG := LSeries.tendsto_atTop (f := g) ((habs hg).trans_lt (EReal.coe_lt_top σ₀))
  have hg1 : g 1 = Complex.log (f 1) := by simp [g, expDirichletCoeff]
  have hlimH : Tendsto (fun x : ℝ ↦ H x) atTop (𝓝 1) := by
    have := hlimF.mul (hlimG.neg.cexp)
    rw [hg1, Complex.exp_neg, Complex.exp_log hf1, mul_inv_cancel₀ hf1] at this
    exact this
  -- `H` is constant on `U`, equal to `1`
  have hconst : ∀ x : ℝ, σ₀ < x → H x = H s := fun x hx ↦
    hU.is_const_of_deriv_eq_zero hUc hHdiff hHderiv (by simpa [U] using hx) hs
  have hHs : H s = 1 := by
    refine tendsto_nhds_unique (tendsto_const_nhds.congr' ?_) hlimH
    filter_upwards [eventually_gt_atTop σ₀] with x hx
    exact (hconst x hx).symm
  refine ⟨hg s hs, ?_⟩
  have : LSeries ⇑f s * cexp (-LSeries g s) = 1 := hHs
  rw [Complex.exp_neg] at this
  have hne : cexp (LSeries g s) ≠ 0 := Complex.exp_ne_zero _
  field_simp at this
  exact this

end NTKB.Apostol
