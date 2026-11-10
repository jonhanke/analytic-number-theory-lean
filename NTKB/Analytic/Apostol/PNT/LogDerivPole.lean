/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Complex.Basic
import NTKB.Attr

/-!
# The logarithmic derivative at a pole (Apostol, Chapter 13, Lemma 4 of §13.8)

**Lemma 4.** If `f` has a pole of order `k` at `α`, then `f'/f` has a first-order pole at `α`
with residue `-k`: `f'(z)/f(z) = -k/(z - α) + h(z)` near `α`, with `h` analytic at `α`.
More generally (same proof) for a meromorphic `f` of order `n ∈ ℤ` at `α`, `f'/f = n/(z-α) + h`.
Proof: write `f(z) = (z - α)^n g(z)` with `g` analytic, `g(α) ≠ 0`; then
`f'/f = n/(z-α) + g'/g`.
-/

open Filter Topology

namespace NTKB.Apostol

/-- For `f` meromorphic of order `n` at `α`: `f'/f = n/(z-α) + h(z)` on a punctured neighbourhood
of `α`, `h` analytic at `α`. -/
theorem logDeriv_eq_of_meromorphicOrderAt {f : ℂ → ℂ} {α : ℂ} (hf : MeromorphicAt f α) {n : ℤ}
    (hn : meromorphicOrderAt f α = n) :
    ∃ h : ℂ → ℂ, AnalyticAt ℂ h α ∧
      ∀ᶠ z in 𝓝[≠] α, deriv f z / f z = n / (z - α) + h z := by
  obtain ⟨g, hg, hgα, hfg⟩ := (meromorphicOrderAt_eq_int_iff hf).mp hn
  refine ⟨fun z ↦ deriv g z / g z, (hg.deriv).div hg hgα, ?_⟩
  have hgan : ∀ᶠ z in 𝓝 α, AnalyticAt ℂ g z := hg.eventually_analyticAt
  have hg0 : ∀ᶠ z in 𝓝 α, g z ≠ 0 := hg.continuousAt.eventually_ne hgα
  have h2 := eventually_eventually_nhdsWithin.mpr hfg
  filter_upwards [h2, self_mem_nhdsWithin, nhdsWithin_le_nhds hgan, nhdsWithin_le_nhds hg0]
    with z hz hzα hza hz0
  have hzα' : z ≠ α := hzα
  have hza0 : z - α ≠ 0 := sub_ne_zero.mpr hzα'
  have hz' : f =ᶠ[𝓝 z] fun y ↦ (y - α) ^ n • g y := by
    rwa [nhdsWithin_eq_nhds.mpr (isOpen_compl_singleton.mem_nhds hzα')] at hz
  have hd : HasDerivAt (fun y ↦ (y - α) ^ n • g y)
      ((n : ℂ) * (z - α) ^ (n - 1) * g z + (z - α) ^ n * deriv g z) z := by
    have h1 := (hasDerivAt_zpow n (z - α) (Or.inl hza0)).comp z ((hasDerivAt_id z).sub_const α)
    have h3 := h1.mul hza.differentiableAt.hasDerivAt
    simp only [smul_eq_mul]
    convert h3 using 1
    · funext y; simp [Function.comp]
    · simp [Function.comp]
  rw [hz'.deriv_eq, hd.deriv, hz'.eq_of_nhds]
  simp only [smul_eq_mul]
  rw [zpow_sub_one₀ hza0]
  have hpow : (z - α) ^ n ≠ 0 := zpow_ne_zero n hza0
  field_simp

/-- **Apostol, Lemma 4 of §13.8**: if `f` has a pole of order `k` at `α`, then
`f'/f = -k/(z - α) + h(z)` near `α` with `h` analytic at `α` (a simple pole with residue `-k`). -/
@[kb "apostol1976" "Lemma 4 (Ch. 13), p. 298"]
theorem logDeriv_eq_of_pole {f : ℂ → ℂ} {α : ℂ} (hf : MeromorphicAt f α) {k : ℕ}
    (hk : meromorphicOrderAt f α = -(k : ℤ)) :
    ∃ h : ℂ → ℂ, AnalyticAt ℂ h α ∧
      ∀ᶠ z in 𝓝[≠] α, deriv f z / f z = -k / (z - α) + h z := by
  obtain ⟨h, hh, hev⟩ := logDeriv_eq_of_meromorphicOrderAt hf (n := -(k : ℤ)) hk
  exact ⟨h, hh, hev.mono fun z hz ↦ by rw [hz]; push_cast; ring⟩

end NTKB.Apostol
