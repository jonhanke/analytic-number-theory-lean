/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Apostol.DirichletSeries.Uniqueness
import NTKB.Analytic.Apostol.ArithmeticFunctions.Multiplicative
import Mathlib.NumberTheory.LSeries.Convolution
import Mathlib.NumberTheory.EulerProduct.Basic

/-!
# Products of Dirichlet series and Euler products (Apostol, Theorems 11.5, 11.7)

* **Theorem 11.5**: `F(s) G(s) = ∑ (f * g)(n) n^{-s}` where both converge absolutely (Mathlib's
  `LSeries_convolution'`), and conversely (`apostol_thm_11_5_converse`): if
  `F(s) G(s) = ∑ α(n) n^{-s}` along a sequence `s_k` with `σ_k → ∞`, then `α = f * g` (on
  `n ≥ 1`), from the uniqueness theorem 11.3.
* **Theorem 11.7**: for multiplicative `f` with `∑ f(n) n^{-s}` absolutely convergent,
  `∑ f(n) n^{-s} = ∏_p (1 + f(p) p^{-s} + f(p²) p^{-2s} + ⋯)`, and
  `= ∏_p (1 - f(p) p^{-s})^{-1}` if `f` is completely multiplicative. Mathlib has the Euler
  product for summable multiplicative functions (`EulerProduct.eulerProduct_hasProd`); Apostol's
  proof (Theorem 11.6 applied to `f(n) n^{-s}`) is that instance.
-/

open Complex Filter Topology LSeries
open scoped LSeries.notation

namespace NTKB.Apostol

/-- **Theorem 11.5** (converse): if `F(s) G(s) = ∑ α(n) n^{-s}` (all three absolutely convergent
somewhere) for each `s` of a sequence `s_k` with `σ_k → ∞`, then `α(n) = (f * g)(n)` for
`n ≥ 1`. -/
@[kb "apostol1976" "Thm 11.5, p. 228"]
theorem apostol_thm_11_5_converse {f g α : ℕ → ℂ} (hf : abscissaOfAbsConv f < ⊤)
    (hg : abscissaOfAbsConv g < ⊤) (hα : abscissaOfAbsConv α < ⊤) {s : ℕ → ℂ}
    (hs : Tendsto (fun k => (s k).re) atTop atTop)
    (hfg : ∀ k, LSeries f (s k) * LSeries g (s k) = LSeries α (s k)) :
    ∀ n, n ≠ 0 → α n = (f ⍟ g) n := by
  obtain ⟨c₁, hc₁⟩ := exists_LSeriesSummable_real hf
  obtain ⟨c₂, hc₂⟩ := exists_LSeriesSummable_real hg
  -- `α` and `f ⍟ g` have the same sum function from some point on; shift the sequence
  obtain ⟨K, hK⟩ := eventually_atTop.mp (hs.eventually_ge_atTop (max c₁ c₂))
  have hs' : Tendsto (fun k => (s (k + K)).re) atTop atTop :=
    hs.comp (tendsto_add_atTop_nat K)
  have hconv : abscissaOfAbsConv (f ⍟ g) < ⊤ :=
    (LSeries.abscissaOfAbsConv_convolution_le f g).trans_lt (max_lt hf hg)
  refine apostol_thm_11_3 hα hconv hs' fun k => ?_
  have hk := hK (k + K) (by omega)
  rw [LSeries_convolution' (hc₁.of_re_le_re (by simpa using (le_max_left _ _).trans hk))
    (hc₂.of_re_le_re (by simpa using (le_max_right _ _).trans hk)), hfg]

lemma term_mul_of_coprime {f : ArithmeticFunction ℂ} (hf : f.IsMultiplicative) (s : ℂ) {m n : ℕ}
    (hmn : m.Coprime n) : term (fun n => f n) s (m * n) = term (fun n => f n) s m * term (fun n => f n) s n := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [term_of_ne_zero (mul_ne_zero hm hn), term_of_ne_zero hm, term_of_ne_zero hn, hf.map_mul_of_coprime hmn,
    Nat.cast_mul, natCast_mul_natCast_cpow, mul_div_mul_comm]

/-- **Theorem 11.7** (Euler product, multiplicative case): if `f` is multiplicative and
`∑ f(n) n^{-s}` converges absolutely, then
`∑ f(n) n^{-s} = ∏_p (1 + f(p) p^{-s} + f(p²) p^{-2s} + ⋯)` (an absolutely convergent product). -/
@[kb "apostol1976" "Thm 11.7, p. 231"]
theorem apostol_thm_11_7 {f : ArithmeticFunction ℂ} (hf : f.IsMultiplicative) {s : ℂ}
    (hs : LSeriesSummable (fun n => f n) s) :
    HasProd (fun p : Nat.Primes => ∑' e : ℕ, term (fun n => f n) s ((p : ℕ) ^ e))
      (LSeries (fun n => f n) s) :=
  EulerProduct.eulerProduct_hasProd (by simp [hf.map_one])
    (fun {_ _} h => term_mul_of_coprime hf s h) (summable_norm_iff.mpr hs) (by simp)

/-- **Theorem 11.7** (completely multiplicative case):
`∑ f(n) n^{-s} = ∏_p (1 - f(p) p^{-s})^{-1}`. -/
@[kb "apostol1976" "Thm 11.7, p. 231"]
theorem apostol_thm_11_7_completely {f : ArithmeticFunction ℂ} (hf : IsCompletelyMultiplicative f)
    {s : ℂ} (hs : LSeriesSummable (fun n => f n) s) :
    HasProd (fun p : Nat.Primes => (1 - f p * ((p : ℕ) : ℂ) ^ (-s))⁻¹)
      (LSeries (fun n => f n) s) := by
  let F : ℕ →*₀ ℂ :=
    { toFun := term (fun n => f n) s
      map_zero' := by simp
      map_one' := by simp [hf.1]
      map_mul' := fun m n => by
        rcases eq_or_ne m 0 with rfl | hm
        · simp
        rcases eq_or_ne n 0 with rfl | hn
        · simp
        rw [term_of_ne_zero (mul_ne_zero hm hn), term_of_ne_zero hm, term_of_ne_zero hn, hf.2,
          Nat.cast_mul, natCast_mul_natCast_cpow, mul_div_mul_comm] }
  have h := EulerProduct.eulerProduct_completely_multiplicative_hasProd (f := F)
    (summable_norm_iff.mpr hs)
  have e : LSeries (fun n => f n) s = ∑' n, F n := rfl
  rw [e]
  convert h using 2 with p
  show _ = (1 - term (fun n => f n) s p)⁻¹
  rw [term_of_ne_zero p.prop.ne_zero, cpow_neg, div_eq_mul_inv]

end NTKB.Apostol
