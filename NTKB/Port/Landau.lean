/-
Copyright (c) 2026 The Tau Ceti contributors. Released under Apache 2.0 license.
Copied into NTKB with credit from Tau Ceti (`TauCeti/NumberTheory/LSeries/Landau.lean`, main
`4caf68dc`); NTKB does not depend on Tau Ceti. Changes: namespace `NTKB.Port.Landau`, only the
declarations needed for `landau`.
-/
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.NumberTheory.LSeries.Positivity
import Mathlib.NumberTheory.LSeries.Deriv
import NTKB.Attr

/-!
# Landau's theorem on Dirichlet series with nonnegative coefficients (port from Tau Ceti)

Ported from Tau Ceti (https://github.com/TauCetiProject/TauCeti, main 4caf68dc),
`TauCeti/NumberTheory/LSeries/Landau.lean`, Apache 2.0, the Tau Ceti contributors (nothing from
its dependencies was needed: the pinned Mathlib has the iterated derivatives of L-series).

If `0 ≤ a` and `LSeries.abscissaOfAbsConv a = σ` (real), then `LSeries a` has no analytic
extension across `σ` (`NTKB.Port.Landau.landau`).  The proof expands the patched function in a
Taylor series about `σ + 1`, whose coefficients are nonnegative, and exchanges two nonnegative
summations.  From it, Apostol's Theorem 11.13 is derived at the end of the file.
-/

namespace NTKB.Port.Landau

open Complex Filter Metric
open scoped ComplexOrder

variable {a : ℕ → ℂ}

/-- Applying Mathlib's `logPowMul` operation multiplies the Dirichlet term by a power of
`Real.log n`. -/
lemma term_logPowMul (f : ℕ → ℂ) (s : ℂ) (k n : ℕ) :
    LSeries.term (LSeries.logMul^[k] f) s n = (Real.log n : ℂ) ^ k * LSeries.term f s n := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 : LSeries.term (LSeries.logMul (LSeries.logMul^[k] f)) s n
        = (Real.log n : ℂ) * LSeries.term (LSeries.logMul^[k] f) s n := by
      rcases eq_or_ne n 0 with rfl | hn
      · simp
      · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, LSeries.logMul,
          Complex.natCast_log, mul_div_assoc]
    rw [Function.iterate_succ_apply', h1, ih, pow_succ]
    ring

private lemma logPowMul_eq_alternating {s : ℂ}
    (hs : LSeries.abscissaOfAbsConv a < s.re) (k : ℕ) :
    LSeries (LSeries.logMul^[k] a) s = (-1 : ℂ) ^ k * iteratedDeriv k (LSeries a) s := by
  rw [LSeries_iteratedDeriv k hs, ← mul_assoc, ← pow_add, Even.neg_one_pow ⟨k, rfl⟩, one_mul]

private lemma logPowMul_nonneg (ha : 0 ≤ a) {x : ℝ}
    (hx : LSeries.abscissaOfAbsConv a < x) (k : ℕ) :
    0 ≤ LSeries (LSeries.logMul^[k] a) (x : ℂ) :=
  (logPowMul_eq_alternating (s := (x : ℂ)) (by simpa using hx) k).symm ▸
    LSeries.iteratedDeriv_alternating ha hx k

/-- The real part of a Dirichlet term at a real point. -/
lemma re_term_of_ne_zero (a : ℕ → ℂ) (x : ℝ) {n : ℕ} (hn : n ≠ 0) :
    (LSeries.term a (x : ℂ) n).re = (a n).re / (n : ℝ) ^ x := by
  have hcast : (n : ℂ) ^ (x : ℂ) = (((n : ℝ) ^ x : ℝ) : ℂ) := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_cpow (Nat.cast_nonneg n)]
  rw [LSeries.term_of_ne_zero hn, hcast, Complex.div_ofReal_re]

/-- At a real point `x` in the half-plane of absolute convergence, the real series obtained by
taking real parts of the terms of `logPowMul` converges to the real part of its L-series. -/
lemma hasSum_logPowMul_re_term {x : ℝ}
    (hx : LSeries.abscissaOfAbsConv a < x) (k : ℕ) :
    HasSum (fun n : ℕ ↦ Real.log n ^ k * (LSeries.term a (x : ℂ) n).re)
      (LSeries (LSeries.logMul^[k] a) (x : ℂ)).re := by
  have hsum : LSeriesSummable (LSeries.logMul^[k] a) (x : ℂ) :=
    LSeriesSummable_of_abscissaOfAbsConv_lt_re (by
      simpa [LSeries.abscissaOfAbsConv_logPowMul] using hx)
  have h : HasSum (LSeries.term (LSeries.logMul^[k] a) (x : ℂ))
      (LSeries (LSeries.logMul^[k] a) (x : ℂ)) := hsum.hasSum
  refine (Complex.hasSum_re h).congr_fun fun n ↦ ?_
  rw [term_logPowMul, ← Complex.ofReal_pow, Complex.re_ofReal_mul]

private lemma re_term_nonneg (ha : 0 ≤ a) (x : ℝ) (n : ℕ) :
    0 ≤ (LSeries.term a (x : ℂ) n).re := by
  simpa using (Complex.le_def.mp (LSeries.term_nonneg (ha n) x)).1

private lemma term_eq_ofReal_re (ha : 0 ≤ a) (x : ℝ) (n : ℕ) :
    LSeries.term a (x : ℂ) n = ((LSeries.term a (x : ℂ) n).re : ℂ) :=
  Complex.eq_re_of_ofReal_le (by
    rw [Complex.ofReal_zero]
    exact LSeries.term_nonneg (ha n) x)

/-- `HasAnalyticExtensionAt a σ` says that the L-series of `a` continues analytically across the
real point `σ`: some function differentiable on a disc around `σ` agrees with `LSeries a` on the
part of that disc lying in the half-plane `Re s > σ`. -/
def HasAnalyticExtensionAt (a : ℕ → ℂ) (σ : ℝ) : Prop :=
  ∃ r : ℝ, 0 < r ∧ ∃ F : ℂ → ℂ, DifferentiableOn ℂ F (ball (σ : ℂ) r) ∧
    ∀ s ∈ ball (σ : ℂ) r, σ < s.re → F s = LSeries a s

private lemma exists_differentiableOn_patch {σ : ℝ}
    (habs : LSeries.abscissaOfAbsConv a = (σ : EReal)) (h : HasAnalyticExtensionAt a σ) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ G : ℂ → ℂ,
      DifferentiableOn ℂ G (ball (((σ + 1 : ℝ) : ℂ)) (1 + δ)) ∧
        Set.EqOn G (LSeries a) {s : ℂ | σ < s.re} := by
  obtain ⟨r, hr, F, hF, hFeq⟩ := h
  set δ : ℝ := min (r ^ 2 / 4) 1
  have hδpos : 0 < δ := lt_min (by positivity) one_pos
  have hδ1 : δ ≤ 1 := min_le_right _ _
  have hδr : 3 * δ < r ^ 2 := by
    have h4 : δ ≤ r ^ 2 / 4 := min_le_left _ _
    nlinarith
  have hUopen : IsOpen {s : ℂ | σ < s.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have habs_lt : ∀ {s : ℂ}, σ < s.re → LSeries.abscissaOfAbsConv a < s.re := by
    intro s hs
    rw [habs]
    exact_mod_cast hs
  set G : ℂ → ℂ := fun s ↦ if σ < s.re then LSeries a s else F s with hGdef
  have hGU : Set.EqOn G (LSeries a) {s : ℂ | σ < s.re} := fun s hs ↦
    ite_eq_left (by simpa using hs)
  have hGF : Set.EqOn G F (ball ((σ : ℝ) : ℂ) r) := by
    intro s hs
    by_cases hsσ : σ < s.re
    · simpa [hGdef, hsσ] using (hFeq s hs hsσ).symm
    · simp [hGdef, hsσ]
  have hsub : ∀ s ∈ ball (((σ + 1 : ℝ) : ℂ)) (1 + δ),
      σ < s.re ∨ s ∈ ball ((σ : ℝ) : ℂ) r := by
    intro s hs
    by_cases hsσ : σ < s.re
    · exact Or.inl hsσ
    replace hsσ := not_lt.mp hsσ
    refine Or.inr ?_
    rw [mem_ball, Complex.dist_eq_re_im, Real.sqrt_lt' hr]
    rw [mem_ball, Complex.dist_eq_re_im, Real.sqrt_lt' (by linarith)] at hs
    simp only [Complex.ofReal_re, Complex.ofReal_im] at hs ⊢
    nlinarith [sq_nonneg (s.im - 0), sq_nonneg (s.re - σ)]
  refine ⟨δ, hδpos, G, fun s hs ↦ ?_, hGU⟩
  rcases hsub s hs with hsU | hsF
  · have hev : G =ᶠ[nhds s] LSeries a := Filter.eventuallyEq_of_mem
      (hUopen.mem_nhds (by simpa using hsU)) hGU
    exact (hev.differentiableAt_iff.mpr
      (LSeries_hasDerivAt (habs_lt hsU)).differentiableAt).differentiableWithinAt
  · have hev : G =ᶠ[nhds s] F :=
      Filter.eventuallyEq_of_mem (isOpen_ball.mem_nhds hsF) hGF
    exact (hev.differentiableAt_iff.mpr
      (hF.differentiableAt (isOpen_ball.mem_nhds hsF))).differentiableWithinAt

private lemma taylorSeries_term_eq (ha : 0 ≤ a) {σ c x y : ℝ} {G : ℂ → ℂ}
    (hGU : Set.EqOn G (LSeries a) {s : ℂ | σ < s.re}) (hc : σ < c)
    (hxc : x - c = -y) (habsc : LSeries.abscissaOfAbsConv a < c) (k : ℕ) :
    (Nat.factorial k : ℂ)⁻¹ • (((x : ℝ) : ℂ) - ((c : ℝ) : ℂ)) ^ k •
        iteratedDeriv k G ((c : ℝ) : ℂ) =
      ((y ^ k / Nat.factorial k *
        (LSeries (LSeries.logMul^[k] a) ((c : ℝ) : ℂ)).re : ℝ) : ℂ) := by
  have hUopen : IsOpen {s : ℂ | σ < s.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hcU : ((c : ℝ) : ℂ) ∈ {s : ℂ | σ < s.re} := by simpa using hc
  have hd : iteratedDeriv k G ((c : ℝ) : ℂ) =
      iteratedDeriv k (LSeries a) ((c : ℝ) : ℂ) :=
    hGU.iteratedDeriv_of_isOpen hUopen k hcU
  have hTk : LSeries (LSeries.logMul^[k] a) ((c : ℝ) : ℂ) =
      (((LSeries (LSeries.logMul^[k] a) ((c : ℝ) : ℂ)).re : ℝ) : ℂ) :=
    Complex.eq_re_of_ofReal_le (by
      rw [Complex.ofReal_zero]
      exact logPowMul_nonneg ha habsc k)
  have hzc : ((x : ℝ) : ℂ) - ((c : ℝ) : ℂ) = -((y : ℝ) : ℂ) := by
    exact_mod_cast hxc
  have e1 : (-((y : ℝ) : ℂ)) ^ k * iteratedDeriv k (LSeries a) ((c : ℝ) : ℂ) =
      ((y : ℝ) : ℂ) ^ k * ((-1 : ℂ) ^ k *
        iteratedDeriv k (LSeries a) ((c : ℝ) : ℂ)) := by
    rw [neg_pow]
    ring
  rw [hd, hzc, smul_eq_mul, smul_eq_mul, e1,
    ← logPowMul_eq_alternating (by simpa using habsc) k]
  nth_rewrite 1 [hTk]
  push_cast
  ring

private lemma hasSum_pow_mul_re_term (a : ℕ → ℂ) (c y : ℝ) (n : ℕ) :
    HasSum (fun k : ℕ ↦ y ^ k / Nat.factorial k *
      (Real.log n ^ k * (LSeries.term a ((c : ℝ) : ℂ) n).re))
      ((LSeries.term a (((c - y : ℝ) : ℂ)) n).re) := by
  have h1 : HasSum (fun k : ℕ ↦ (y * Real.log n) ^ k / Nat.factorial k)
      (Real.exp (y * Real.log n)) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp _
  have h2 := h1.mul_right ((LSeries.term a ((c : ℝ) : ℂ) n).re)
  have heq : Real.exp (y * Real.log n) * (LSeries.term a ((c : ℝ) : ℂ) n).re =
      (LSeries.term a (((c - y : ℝ) : ℂ)) n).re := by
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · have hn0 : (0 : ℝ) < n := by positivity
      have hyexp : Real.exp (y * Real.log n) = (n : ℝ) ^ y := by
        rw [Real.rpow_def_of_pos hn0, mul_comm]
      have hc : (n : ℝ) ^ c = (n : ℝ) ^ (c - y) * (n : ℝ) ^ y := by
        rw [← Real.rpow_add hn0]
        ring_nf
      rw [re_term_of_ne_zero a c hn, re_term_of_ne_zero a (c - y) hn, hyexp, hc]
      field_simp
  rw [← heq]
  refine h2.congr_fun fun k ↦ ?_
  rw [mul_pow]
  ring

private lemma summable_re_term_of_summable_logPow (ha : 0 ≤ a) {c x y : ℝ}
    (hx : x = c - y) (hy : 0 ≤ y) (habsc : LSeries.abscissaOfAbsConv a < c)
    (hsummable : Summable (fun k : ℕ ↦ y ^ k / Nat.factorial k *
      (LSeries (LSeries.logMul^[k] a) ((c : ℝ) : ℂ)).re)) :
    Summable (fun n : ℕ ↦ (LSeries.term a ((x : ℝ) : ℂ) n).re) := by
  have hexp : ∀ n : ℕ, HasSum (fun k : ℕ ↦ y ^ k / Nat.factorial k *
      (Real.log n ^ k * (LSeries.term a ((c : ℝ) : ℂ) n).re))
      ((LSeries.term a ((x : ℝ) : ℂ) n).re) := by
    intro n
    simpa only [hx] using hasSum_pow_mul_re_term a c y n
  refine summable_of_sum_le (c := ∑' k : ℕ, y ^ k / Nat.factorial k *
    (LSeries (LSeries.logMul^[k] a) ((c : ℝ) : ℂ)).re)
    (fun n ↦ re_term_nonneg ha x n) fun s ↦ ?_
  refine hasSum_le (fun k ↦ ?_) (hasSum_sum fun n _ ↦ hexp n) hsummable.hasSum
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_
    (div_nonneg (pow_nonneg hy k) (Nat.cast_nonneg _))
  exact sum_le_hasSum s
    (fun n _ ↦ mul_nonneg (pow_nonneg (Real.log_natCast_nonneg n) k)
      (re_term_nonneg ha c n))
    (hasSum_logPowMul_re_term habsc k)

/-- **Landau's theorem.** If `a` has nonnegative values and its abscissa of absolute convergence
is the real number `σ`, then `LSeries a` has no analytic continuation across `σ`. -/
theorem landau (ha : 0 ≤ a) {σ : ℝ} (habs : LSeries.abscissaOfAbsConv a = (σ : EReal)) :
    ¬ HasAnalyticExtensionAt a σ := by
  intro h
  obtain ⟨δ, hδpos, G, hGdiffOn', hGU⟩ := exists_differentiableOn_patch habs h
  set c : ℝ := σ + 1 with hcdef
  set y : ℝ := 1 + δ / 2 with hydef
  set x : ℝ := c - y with hxdef
  have hy0 : 0 < y := by rw [hydef]; linarith
  have hxσ : x < σ := by rw [hxdef, hydef, hcdef]; linarith
  have habsc : LSeries.abscissaOfAbsConv a < c := by
    rw [habs]
    exact_mod_cast (by rw [hcdef]; linarith : σ < c)
  have hxc : x - c = -y := by rw [hxdef]; ring
  have hxball : ((x : ℝ) : ℂ) ∈ ball ((c : ℝ) : ℂ) (1 + δ) := by
    rw [mem_ball, Complex.isometry_ofReal.dist_eq, Real.dist_eq, hxc, abs_neg,
      abs_of_pos hy0, hydef]
    linarith
  have hGdiffOn : DifferentiableOn ℂ G (ball ((c : ℝ) : ℂ) (1 + δ)) := by
    simpa only [hcdef] using hGdiffOn'
  have htaylor := Complex.hasSum_taylorSeries_on_ball hGdiffOn hxball
  have hterm : ∀ k : ℕ, (Nat.factorial k : ℂ)⁻¹ • (((x : ℝ) : ℂ) - ((c : ℝ) : ℂ)) ^ k •
      iteratedDeriv k G ((c : ℝ) : ℂ)
      = ((y ^ k / Nat.factorial k *
          (LSeries (LSeries.logMul^[k] a) ((c : ℝ) : ℂ)).re : ℝ) : ℂ) := by
    exact fun k ↦ taylorSeries_term_eq ha hGU (by rw [hcdef]; linarith) hxc habsc k
  have hsummable_k : Summable (fun k : ℕ ↦ y ^ k / Nat.factorial k *
      (LSeries (LSeries.logMul^[k] a) ((c : ℝ) : ℂ)).re) :=
    Complex.summable_ofReal.mp (htaylor.congr_fun fun k ↦ (hterm k).symm).summable
  have hsum_x : Summable (fun n : ℕ ↦ (LSeries.term a ((x : ℝ) : ℂ) n).re) := by
    exact summable_re_term_of_summable_logPow ha hxdef hy0.le habsc hsummable_k
  have hLS : LSeriesSummable a ((x : ℝ) : ℂ) :=
    (Complex.summable_ofReal.mpr hsum_x).congr fun n ↦
      (term_eq_ofReal_re ha x n).symm
  have hle := hLS.abscissaOfAbsConv_le
  rw [habs, Complex.ofReal_re] at hle
  have hσx : σ ≤ x := mod_cast hle
  linarith

end NTKB.Port.Landau

namespace NTKB.Apostol

open Filter
open scoped ComplexOrder

/-- A finite Dirichlet polynomial is entire in `s`. -/
private lemma differentiable_finite_term (f : ℕ → ℂ) (N : ℕ) :
    Differentiable ℂ (fun s : ℂ ↦ ∑ n ∈ Finset.range N, LSeries.term f s n) := by
  refine Differentiable.fun_sum fun n _ ↦ ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · simp only [LSeries.term_of_ne_zero hn]
    have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    exact (differentiable_const _).div
      (Differentiable.const_cpow differentiable_id (Or.inl hn'))
      (fun s ↦ by simp [Complex.cpow_eq_zero_iff, hn'])

open scoped ComplexOrder in
/-- **Apostol, Theorem 11.13 (Landau)**: let `F(s) = ∑ f(n) n^{-s}` converge absolutely for
`σ > σ_c`, with `f(n) ≥ 0` for `n ≥ n₀`. If `F` is analytic in a disc about `σ_c`, then the
series converges absolutely for `σ > σ_c - ε` for some `ε > 0`. -/
@[kb "apostol1976" "Thm 11.13, p. 237"]
theorem apostol_thm_11_13 {f : ℕ → ℂ} {n₀ : ℕ} (hf : ∀ n, n₀ ≤ n → 0 ≤ f n) {σc : ℝ}
    (hconv : ∀ s : ℂ, σc < s.re → LSeriesSummable f s) {r : ℝ} (hr : 0 < r) {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F (Metric.ball (σc : ℂ) r))
    (hFeq : ∀ s ∈ Metric.ball (σc : ℂ) r, σc < s.re → F s = LSeries f s) :
    ∃ ε > 0, ∀ s : ℂ, σc - ε < s.re → LSeriesSummable f s := by
  have hle : LSeries.abscissaOfAbsConv f ≤ σc :=
    LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable' fun y hy ↦ by
      simpa using hconv (y : ℂ) (by simpa using hy)
  rcases hle.lt_or_eq with hlt | heq
  · obtain ⟨σ', h₁, h₂⟩ := EReal.exists_between_coe_real hlt
    have h₂' : σ' < σc := mod_cast h₂
    refine ⟨σc - σ', by linarith, fun s hs ↦ ?_⟩
    exact LSeriesSummable_of_abscissaOfAbsConv_lt_re
      (h₁.trans_le (by exact_mod_cast (by linarith : σ' ≤ s.re)))
  · exfalso
    set g : ℕ → ℂ := fun n ↦ if n < n₀ then 0 else f n with hg
    have hg0 : 0 ≤ g := fun n ↦ by
      by_cases h : n < n₀
      · simp [hg, h]
      · simpa [hg, h] using hf n (not_lt.mp h)
    have hgev : g =ᶠ[atTop] f := by
      filter_upwards [eventually_ge_atTop n₀] with n hn
      simp [hg, not_lt.mpr hn]
    have habs : LSeries.abscissaOfAbsConv g = (σc : EReal) :=
      (LSeries.abscissaOfAbsConv_congr' hgev).trans heq
    refine Port.Landau.landau hg0 habs ⟨r, hr, fun s ↦ F s - ∑ n ∈ Finset.range n₀,
      LSeries.term f s n, hF.sub (differentiable_finite_term f n₀).differentiableOn, ?_⟩
    intro s hs hσ
    have hfs : LSeriesSummable f s := hconv s hσ
    have h1 : HasSum (LSeries.term f s) (LSeries f s) := hfs.hasSum
    have h2 : HasSum (fun n ↦ if n < n₀ then LSeries.term f s n else 0)
        (∑ n ∈ Finset.range n₀, LSeries.term f s n) := by
      have h : HasSum (fun n ↦ if n < n₀ then LSeries.term f s n else 0)
          (∑ n ∈ Finset.range n₀, (if n < n₀ then LSeries.term f s n else 0)) :=
        hasSum_sum_of_ne_finset_zero (fun n hn ↦ by
          have : ¬ n < n₀ := by simpa using hn
          simp [this])
      have e : ∑ n ∈ Finset.range n₀, (if n < n₀ then LSeries.term f s n else 0)
          = ∑ n ∈ Finset.range n₀, LSeries.term f s n :=
        Finset.sum_congr rfl fun n hn ↦ by simp [Finset.mem_range.mp hn]
      rwa [e] at h
    have e2 : LSeries.term g s =
        fun n ↦ LSeries.term f s n - (if n < n₀ then LSeries.term f s n else 0) := by
      funext n
      rcases eq_or_ne n 0 with rfl | h0
      · simp
      · by_cases h : n < n₀
        · simp [LSeries.term_of_ne_zero h0, hg, h]
        · simp [LSeries.term_of_ne_zero h0, hg, h]
    have h3 := h1.sub h2
    have h4 : LSeries g s = LSeries f s - ∑ n ∈ Finset.range n₀, LSeries.term f s n := by
      rw [LSeries]
      rw [e2]
      exact h3.tsum_eq
    show F s - _ = _
    rw [hFeq s hs hσ, h4]

end NTKB.Apostol
