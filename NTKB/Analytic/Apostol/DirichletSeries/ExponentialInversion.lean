/- Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license. -/
import NTKB.Analytic.Apostol.DirichletSeries.Exponential

/-!
# Apostol, Theorem 11.14 under the book's hypothesis, from a named inversion input

Apostol's Theorem 11.14 assumes only that `F(s) = ∑ f(n) n^{-s}` converges absolutely for
`σ > σₐ`, `f(1) ≠ 0` and `F(s) ≠ 0` for `σ > σ₀ ≥ σₐ`. His proof uses that the Dirichlet series of
the inverse `f⁻¹` converges absolutely for `σ > σ₀` (so that it is `1/F`). That step is a
theorem of Wiener type for absolutely convergent Dirichlet series (Hewitt and Williamson, 1957,
together with Bohr's theorem that `inf_t |F(σ + it)| > 0` when `F` has no zeros near the line
`Re s = σ`), which is not in Mathlib. It is the named input `DirichletInverseSummableInput`
(a structure, assumed as a hypothesis), and `apostol_thm_11_14_of_input` is the theorem under
the book's hypotheses, from that input and `apostol_thm_11_14`.
-/

open Complex LSeries ArithmeticFunction

namespace NTKB.Apostol

/-- **Named input (Hewitt–Williamson inversion for Dirichlet series).** If `∑ f(n) n^{-s}`
converges absolutely and does not vanish for `σ > σ₀`, and `f(1) ≠ 0`, then the Dirichlet series
of the Dirichlet inverse `f⁻¹` converges absolutely for `σ > σ₀`. -/
structure DirichletInverseSummableInput : Prop where
  summable_inverse : ∀ (f : ArithmeticFunction ℂ) (hf1 : f 1 ≠ 0) (σ₀ : ℝ),
    (∀ s : ℂ, σ₀ < s.re → LSeriesSummable ⇑f s) → (∀ s : ℂ, σ₀ < s.re → LSeries ⇑f s ≠ 0) →
      ∀ s : ℂ, σ₀ < s.re → LSeriesSummable ⇑(dirichletInverse f (invertibleOfNonzero hf1)) s

/-- **Apostol, Theorem 11.14** (the book's hypotheses, from `DirichletInverseSummableInput`): if
`∑ f(n) n^{-s}` converges absolutely for `σ > σₐ`, `f(1) ≠ 0` and `F(s) ≠ 0` for `σ > σ₀ ≥ σₐ`,
then for `σ > σ₀`, `F(s) = e^{G(s)}` with `G(s) = log f(1) + ∑_{n ≥ 2} ((f' * f⁻¹)(n)/log n) n^{-s}`
(absolutely convergent). -/
@[kb "apostol1976" "Thm 11.14, p. 237"]
theorem apostol_thm_11_14_of_input (H : DirichletInverseSummableInput)
    (f : ArithmeticFunction ℂ) (hf1 : f 1 ≠ 0) {σₐ σ₀ : ℝ} (hσ : σₐ ≤ σ₀)
    (hF : ∀ s : ℂ, σₐ < s.re → LSeriesSummable ⇑f s)
    (hne : ∀ s : ℂ, σ₀ < s.re → LSeries ⇑f s ≠ 0) {s : ℂ} (hs : σ₀ < s.re) :
    LSeriesSummable (expDirichletCoeff f hf1) s ∧
      LSeries ⇑f s = cexp (LSeries (expDirichletCoeff f hf1) s) := by
  have hF' : ∀ z : ℂ, σ₀ < z.re → LSeriesSummable ⇑f z := fun z hz ↦ hF z (hσ.trans_lt hz)
  exact apostol_thm_11_14 f hf1 hF' (H.summable_inverse f hf1 σ₀ hF' hne) hs

end NTKB.Apostol
