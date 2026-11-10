/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.Deriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.NumberTheory.LSeries.Convergence
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Normed.Group.Tannery
import NTKB.Attr

/-!
# Mean value formulas for Dirichlet series (Apostol, §§11.10–11.11)

* **Theorem 11.15**: if `F(s) = ∑ f(n) n^{-s}`, `G(s) = ∑ g(n) n^{-s}` converge absolutely at
  `a` and `b`, then `(1/2T) ∫_{-T}^{T} F(a+it) G(b-it) dt → ∑ f(n) g(n) n^{-a-b}`.
* **Theorem 11.16**: `(1/2T) ∫_{-T}^{T} |F(σ+it)|² dt → ∑ |f(n)|² n^{-2σ}`; (a) for `ζ`, `σ > 1`.
* **Theorem 11.17**: `(1/2T) ∫_{-T}^{T} F(σ+it) x^{σ+it} dt → f(n)` if `x = n`, `→ 0` if `x > 0`
  is not an integer.

Apostol's proof: expand the product as an absolutely convergent double series, integrate term
by term, and pass to the limit term by term. Here both steps are the dominated convergence
theorem (for the integral, and for series), packaged in `tendsto_avg_tsum_exp`:
for an absolutely summable family `c k` and frequencies `θ k`,
`(1/2T) ∫_{-T}^{T} ∑ c_k e^{iθ_k t} dt → ∑_{θ_k = 0} c_k`.
-/

open Complex Filter Topology MeasureTheory LSeries

namespace NTKB.Apostol

/-- The average `(1/2T) ∫_{-T}^{T} e^{iθt} dt`. -/
noncomputable def avgExp (θ T : ℝ) : ℂ :=
  (1 / (2 * T) : ℂ) * ∫ t in (-T)..T, exp (θ * t * I)

lemma norm_avgExp_le (θ : ℝ) {T : ℝ} (hT : 0 < T) : ‖avgExp θ T‖ ≤ 1 := by
  unfold avgExp
  have h : ‖∫ t in (-T)..T, exp (θ * t * I)‖ ≤ 1 * |T - -T| :=
    intervalIntegral.norm_integral_le_of_norm_le_const fun t _ => by
      rw [show (θ : ℂ) * t * I = ((θ * t : ℝ) : ℂ) * I by push_cast; ring, norm_exp_ofReal_mul_I]
  rw [norm_mul, show T - -T = 2 * T by ring, abs_of_pos (by linarith), one_mul] at *
  rw [show (1 / (2 * T) : ℂ) = ((1 / (2 * T) : ℝ) : ℂ) by push_cast; ring, norm_real,
    Real.norm_eq_abs, abs_of_pos (by positivity)]
  calc 1 / (2 * T) * ‖∫ t in (-T)..T, exp (θ * t * I)‖ ≤ 1 / (2 * T) * (2 * T) := by gcongr
    _ = 1 := by field_simp

lemma avgExp_zero {T : ℝ} (hT : 0 < T) : avgExp 0 T = 1 := by
  unfold avgExp
  simp only [ofReal_zero, zero_mul, exp_zero, intervalIntegral.integral_const, sub_neg_eq_add,
    real_smul, mul_one]
  have : (T : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
  push_cast
  field_simp
  ring

lemma tendsto_avgExp {θ : ℝ} (hθ : θ ≠ 0) : Tendsto (avgExp θ) atTop (𝓝 0) := by
  have hc : (θ : ℂ) * I ≠ 0 := mul_ne_zero (ofReal_ne_zero.mpr hθ) I_ne_zero
  have key : ∀ T > 0, ‖avgExp θ T‖ ≤ 1 / |θ| * T⁻¹ := by
    intro T hT
    unfold avgExp
    have := integral_exp_mul_complex (a := -T) (b := T) hc
    simp only [show ∀ t : ℝ, (θ : ℂ) * t * I = θ * I * t from fun t => by ring]
    rw [this, show (1 / (2 * T) : ℂ) = ((1 / (2 * T) : ℝ) : ℂ) by push_cast; ring, norm_mul,
      norm_real, Real.norm_eq_abs, abs_of_pos (by positivity), norm_div]
    have h1 : ‖exp (θ * I * (T : ℂ)) - exp (θ * I * ((-T : ℝ) : ℂ))‖ ≤ 2 := by
      refine (norm_sub_le _ _).trans ?_
      rw [show (θ : ℂ) * I * (T : ℂ) = ((θ * T : ℝ) : ℂ) * I by push_cast; ring,
        show (θ : ℂ) * I * ((-T : ℝ) : ℂ) = ((θ * -T : ℝ) : ℂ) * I by push_cast; ring,
        norm_exp_ofReal_mul_I, norm_exp_ofReal_mul_I]
      norm_num
    rw [norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs]
    have hθ' : 0 < |θ| := abs_pos.mpr hθ
    calc 1 / (2 * T) * (‖exp (θ * I * (T : ℂ)) - exp (θ * I * ((-T : ℝ) : ℂ))‖ / |θ|)
        ≤ 1 / (2 * T) * (2 / |θ|) := by gcongr
      _ = 1 / |θ| * T⁻¹ := by field_simp
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hlim : Tendsto (fun T : ℝ => 1 / |θ| * T⁻¹) atTop (𝓝 0) := by
    simpa using tendsto_inv_atTop_zero.const_mul (1 / |θ|)
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim
  filter_upwards [eventually_gt_atTop 0] with T hT using key T hT

/-- The core of the proofs of Theorems 11.15 and 11.17: for an absolutely summable family `c`
and real frequencies `θ`, `(1/2T) ∫_{-T}^{T} ∑ c_k e^{iθ_k t} dt → ∑_{θ_k = 0} c_k`. -/
theorem tendsto_avg_tsum_exp {ι : Type*} [Countable ι] {c : ι → ℂ} (hc : Summable fun k => ‖c k‖)
    (θ : ι → ℝ) :
    Tendsto (fun T : ℝ => (1 / (2 * T) : ℂ) * ∫ t in (-T)..T, ∑' k, c k * exp (θ k * t * I))
      atTop (𝓝 (∑' k, if θ k = 0 then c k else 0)) := by
  have hint : ∀ T : ℝ, (1 / (2 * T) : ℂ) * ∫ t in (-T)..T, ∑' k, c k * exp (θ k * t * I) =
      ∑' k, c k * avgExp (θ k) T := by
    intro T
    have hs : HasSum (fun k => ∫ t in (-T)..T, c k * exp (θ k * t * I))
        (∫ t in (-T)..T, ∑' k, c k * exp (θ k * t * I)) := by
      refine intervalIntegral.hasSum_integral_of_dominated_convergence (fun k _ => ‖c k‖)
        (fun k => ?_) (fun k => Eventually.of_forall fun t _ => ?_)
        (Eventually.of_forall fun t _ => hc) intervalIntegrable_const
        (Eventually.of_forall fun t _ => ?_)
      · exact (Continuous.aestronglyMeasurable (by fun_prop))
      · rw [norm_mul, show (θ k : ℂ) * t * I = ((θ k * t : ℝ) : ℂ) * I by push_cast; ring,
          norm_exp_ofReal_mul_I, mul_one]
      · refine (Summable.of_norm ?_).hasSum
        refine hc.congr fun k => ?_
        rw [norm_mul, show (θ k : ℂ) * t * I = ((θ k * t : ℝ) : ℂ) * I by push_cast; ring,
          norm_exp_ofReal_mul_I, mul_one]
    rw [← hs.tsum_eq, ← tsum_mul_left]
    congr 1
    ext k
    rw [avgExp, intervalIntegral.integral_const_mul]
    ring
  simp_rw [hint]
  refine tendsto_tsum_of_dominated_convergence hc (fun k => ?_) ?_
  · by_cases hk : θ k = 0
    · simp only [hk, ite_true]
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with T hT
      rw [avgExp_zero hT, mul_one]
    · simp only [hk, ite_false]
      simpa using (tendsto_avgExp hk).const_mul (c k)
  · filter_upwards [eventually_gt_atTop 0] with T hT k
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (norm_avgExp_le _ hT)

/-! ### Rewriting the terms -/

lemma natCast_cpow_add_mul_I {n : ℕ} (hn : n ≠ 0) (a t : ℝ) :
    (n : ℂ) ^ ((a : ℂ) + t * I) = (n : ℂ) ^ (a : ℂ) * exp (Real.log n * t * I) := by
  rw [cpow_add _ _ (Nat.cast_ne_zero.mpr hn), cpow_def_of_ne_zero (Nat.cast_ne_zero.mpr hn)
    ((t : ℂ) * I), ← natCast_log]
  ring_nf

lemma term_add_mul_I (f : ℕ → ℂ) (a t : ℝ) (n : ℕ) :
    term f ((a : ℂ) + t * I) n = term f a n * exp (-(Real.log n) * t * I) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [term_of_ne_zero hn, term_of_ne_zero hn, natCast_cpow_add_mul_I hn, div_mul_eq_div_div,
    div_eq_mul_inv _ (exp _), ← exp_neg]
  push_cast
  ring_nf

lemma term_sub_mul_I (f : ℕ → ℂ) (a t : ℝ) (n : ℕ) :
    term f ((a : ℂ) - t * I) n = term f a n * exp (Real.log n * t * I) := by
  have := term_add_mul_I f a (-t) n
  push_cast at this
  rw [sub_eq_add_neg, show -((t : ℂ) * I) = -(t : ℂ) * I by ring, this]
  push_cast
  ring_nf

lemma summable_norm_term {f : ℕ → ℂ} {s : ℂ} (hf : LSeriesSummable f s) :
    Summable fun n => ‖term f s n‖ :=
  summable_norm_iff.mpr hf

lemma term_mul_term (f g : ℕ → ℂ) (a b : ℂ) (n : ℕ) :
    term f a n * term g b n = term (fun n => f n * g n) (a + b) n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  have h1 : (n : ℂ) ^ a ≠ 0 := by simp [hn]
  have h2 : (n : ℂ) ^ b ≠ 0 := by simp [hn]
  rw [term_of_ne_zero hn, term_of_ne_zero hn, term_of_ne_zero hn,
    cpow_add _ _ (Nat.cast_ne_zero.mpr hn)]
  field_simp

/-- **Theorem 11.15** (with absolute convergence at the points `a` and `b`). -/
theorem tendsto_avg_LSeries_mul_LSeries {f g : ℕ → ℂ} {a b : ℝ} (hf : LSeriesSummable f a)
    (hg : LSeriesSummable g b) :
    Tendsto (fun T : ℝ => (1 / (2 * T) : ℂ) *
        ∫ t in (-T)..T, LSeries f (a + t * I) * LSeries g (b - t * I))
      atTop (𝓝 (LSeries (fun n => f n * g n) (a + b))) := by
  set c : ℕ × ℕ → ℂ := fun p => term f a p.1 * term g b p.2
  set θ : ℕ × ℕ → ℝ := fun p => Real.log p.2 - Real.log p.1
  have hc : Summable fun p => ‖c p‖ := by
    have := (summable_norm_term hf).mul_norm (summable_norm_term hg)
    simpa [c, norm_mul] using this
  have hprod : ∀ t : ℝ, LSeries f (a + t * I) * LSeries g (b - t * I) =
      ∑' p, c p * exp (θ p * t * I) := by
    intro t
    have hf' : Summable fun n => ‖term f (a + t * I) n‖ := by
      refine summable_norm_term ((LSeriesSummable_iff_of_re_eq_re ?_).mp hf); simp
    have hg' : Summable fun n => ‖term g (b - t * I) n‖ := by
      refine summable_norm_term ((LSeriesSummable_iff_of_re_eq_re ?_).mp hg); simp
    rw [LSeries, LSeries, tsum_mul_tsum_of_summable_norm hf' hg']
    congr 1
    ext p
    rw [term_add_mul_I, term_sub_mul_I, mul_mul_mul_comm, ← exp_add]
    simp only [c, θ]
    push_cast
    ring_nf
  simp_rw [hprod]
  convert tendsto_avg_tsum_exp hc θ using 2
  -- the limit: the diagonal `m = n` of the double series
  have hdiag : ∀ p : ℕ × ℕ, (if θ p = 0 then c p else 0) = if p.1 = p.2 then c p else 0 := by
    rintro ⟨m, n⟩
    simp only [θ, c]
    rcases eq_or_ne m 0 with rfl | hm
    · simp
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    have : Real.log n - Real.log m = 0 ↔ m = n := by
      rw [sub_eq_zero]
      constructor
      · intro h
        exact_mod_cast (Real.log_injOn_pos (by simpa using Nat.pos_of_ne_zero hm)
          (by simpa using Nat.pos_of_ne_zero hn) h.symm)
      · rintro rfl; rfl
    simp only [this]
  simp_rw [hdiag]
  have hinj : Function.Injective fun n : ℕ => (n, n) := fun _ _ h => (Prod.mk.inj h).1
  rw [← hinj.tsum_eq (f := fun p : ℕ × ℕ => if p.1 = p.2 then c p else 0)]
  · rw [LSeries]
    congr 1
    ext n
    simp only [c, ite_true]
    exact (term_mul_term f g a b n).symm
  · rintro ⟨m, n⟩ h
    simp only [Function.mem_support, ne_eq, ite_eq_right_iff, Classical.not_imp] at h
    exact ⟨m, by simp [h.1]⟩

/-- **Theorem 11.15** (Apostol's form): for `a > σ₁`, `b > σ₂` (abscissae of absolute
convergence of `F` and `G`),
`lim_{T→∞} (1/2T) ∫_{-T}^{T} F(a+it) G(b-it) dt = ∑ f(n) g(n) n^{-a-b}`. -/
@[kb "apostol1976" "Thm 11.15, p. 240"]
theorem apostol_thm_11_15 {f g : ℕ → ℂ} {a b : ℝ} (ha : abscissaOfAbsConv f < a)
    (hb : abscissaOfAbsConv g < b) :
    Tendsto (fun T : ℝ => (1 / (2 * T) : ℂ) *
        ∫ t in (-T)..T, LSeries f (a + t * I) * LSeries g (b - t * I))
      atTop (𝓝 (LSeries (fun n => f n * g n) (a + b))) :=
  tendsto_avg_LSeries_mul_LSeries
    (LSeriesSummable_of_abscissaOfAbsConv_lt_re (s := (a : ℂ)) (by simpa using ha))
    (LSeriesSummable_of_abscissaOfAbsConv_lt_re (s := (b : ℂ)) (by simpa using hb))

/-! ### Theorem 11.16 -/

lemma term_conj (f : ℕ → ℂ) (σ : ℝ) (n : ℕ) :
    term (fun n => (starRingEnd ℂ) (f n)) σ n = (starRingEnd ℂ) (term f σ n) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [term_of_ne_zero hn, term_of_ne_zero hn, map_div₀, ← ofReal_natCast,
    ← ofReal_cpow (Nat.cast_nonneg n), conj_ofReal]

lemma LSeriesSummable_conj {f : ℕ → ℂ} {σ : ℝ} (hf : LSeriesSummable f σ) :
    LSeriesSummable (fun n => (starRingEnd ℂ) (f n)) σ := by
  have h : term (fun n => (starRingEnd ℂ) (f n)) σ = fun n => (starRingEnd ℂ) (term f σ n) :=
    funext (term_conj f σ)
  unfold LSeriesSummable
  rw [h]
  exact Summable.of_norm ((summable_norm_term hf).congr fun n => (RCLike.norm_conj _).symm)

lemma LSeries_conj_sub_mul_I (f : ℕ → ℂ) (σ t : ℝ) :
    LSeries (fun n => (starRingEnd ℂ) (f n)) (σ - t * I) =
      (starRingEnd ℂ) (LSeries f (σ + t * I)) := by
  rw [LSeries, LSeries, conj_tsum]
  refine tsum_congr fun n => ?_
  rw [term_sub_mul_I, term_add_mul_I, term_conj, map_mul, ← exp_conj, map_mul, map_mul, map_neg,
    conj_ofReal, conj_ofReal, conj_I]
  ring_nf

/-- **Theorem 11.16**: if `F(s) = ∑ f(n) n^{-s}` converges absolutely at `σ`, then
`(1/2T) ∫_{-T}^{T} |F(σ+it)|² dt → ∑ |f(n)|² n^{-2σ}` (written `∑ ‖f(n) n^{-σ}‖²`, with the
`n = 0` term `0` as in Mathlib's `LSeries.term`). -/
@[kb "apostol1976" "Thm 11.16, p. 241"]
theorem apostol_thm_11_16 {f : ℕ → ℂ} {σ : ℝ} (hf : LSeriesSummable f σ) :
    Tendsto (fun T : ℝ => 1 / (2 * T) * ∫ t in (-T)..T, ‖LSeries f (σ + t * I)‖ ^ 2)
      atTop (𝓝 (∑' n : ℕ, ‖term f σ n‖ ^ 2)) := by
  have h := tendsto_avg_LSeries_mul_LSeries hf (LSeriesSummable_conj hf)
  have e : (fun t : ℝ => LSeries f (σ + t * I) * LSeries (fun n => (starRingEnd ℂ) (f n)) (σ - t * I))
      = fun t : ℝ => ((‖LSeries f (σ + t * I)‖ ^ 2 : ℝ) : ℂ) := funext fun t => by
    rw [LSeries_conj_sub_mul_I, mul_conj, Complex.normSq_eq_norm_sq, ofReal_pow]
  rw [e] at h
  have hlim : LSeries (fun n => f n * (starRingEnd ℂ) (f n)) (σ + σ) =
      ((∑' n : ℕ, ‖term f σ n‖ ^ 2 : ℝ) : ℂ) := by
    rw [LSeries, ofReal_tsum]
    refine tsum_congr fun n => ?_
    rw [← term_mul_term, term_conj, mul_conj, Complex.normSq_eq_norm_sq, ofReal_pow]
  rw [hlim] at h
  have h2 := (continuous_re.tendsto _).comp h
  rw [ofReal_re] at h2
  refine h2.congr fun T => ?_
  simp only [Function.comp_apply]
  rw [intervalIntegral.integral_ofReal, show (1 / (2 * T) : ℂ) = ((1 / (2 * T) : ℝ) : ℂ) by
    push_cast; ring, ← ofReal_mul, ofReal_re]

/-- **Theorem 11.16 (a)**: for `σ > 1`, `(1/2T) ∫_{-T}^{T} |ζ(σ+it)|² dt → ζ(2σ)`. -/
@[kb "apostol1976" "Thm 11.16(a), p. 241"]
theorem apostol_thm_11_16_a {σ : ℝ} (hσ : 1 < σ) :
    Tendsto (fun T : ℝ => 1 / (2 * T) * ∫ t in (-T)..T, ‖riemannZeta (σ + t * I)‖ ^ 2)
      atTop (𝓝 (riemannZeta (2 * σ : ℝ)).re) := by
  have hf : LSeriesSummable 1 σ := LSeriesSummable_one_iff.mpr (by simpa using hσ)
  have h := apostol_thm_11_16 hf
  have e1 : ∀ t : ℝ, LSeries 1 (σ + t * I) = riemannZeta (σ + t * I) := fun t =>
    LSeries_one_eq_riemannZeta (by simpa using hσ)
  have e2 : riemannZeta (2 * σ : ℝ) = ((∑' n : ℕ, ‖term 1 σ n‖ ^ 2 : ℝ) : ℂ) := by
    rw [← LSeries_one_eq_riemannZeta (by simp; linarith), LSeries, ofReal_tsum]
    refine tsum_congr fun n => ?_
    have h1 : (fun n => (1 : ℕ → ℂ) n * (starRingEnd ℂ) ((1 : ℕ → ℂ) n)) = 1 := by
      funext n; simp
    rw [← Complex.normSq_eq_norm_sq, ← mul_conj, ← term_conj, term_mul_term, h1]
    push_cast; ring_nf
  simp_rw [e1] at h
  rwa [e2, ofReal_re]

lemma iteratedDeriv_riemannZeta_eq (k : ℕ) {s : ℂ} (hs : 1 < s.re) :
    iteratedDeriv k riemannZeta s = (-1) ^ k * LSeries (logMul^[k] 1) s := by
  have hev : riemannZeta =ᶠ[𝓝 s] LSeries 1 := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds
      (show s ∈ {b : ℂ | (1 : ℝ) < b.re} from hs)] with z hz
    exact (LSeries_one_eq_riemannZeta hz).symm
  rw [(hev.iteratedDeriv k).eq_of_nhds, LSeries_iteratedDeriv k (by
    rw [LSeries.abscissaOfAbsConv_one]; exact_mod_cast hs)]

lemma logMul_iterate_one_apply (k n : ℕ) :
    (logMul^[k] (1 : ℕ → ℂ)) n = ((Real.log n : ℝ) : ℂ) ^ k * (1 : ℕ → ℂ) n := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', logMul, ih, ← natCast_log, pow_succ]
    ring

/-- **Theorem 11.16 (b)**: for `σ > 1` and `k ≥ 0`,
`(1/2T) ∫_{-T}^{T} |ζ^{(k)}(σ+it)|² dt → ζ^{(2k)}(2σ)`. -/
@[kb "apostol1976" "Thm 11.16(b), p. 241"]
theorem apostol_thm_11_16_b {σ : ℝ} (hσ : 1 < σ) (k : ℕ) :
    Tendsto (fun T : ℝ => 1 / (2 * T) * ∫ t in (-T)..T, ‖iteratedDeriv k riemannZeta (σ + t * I)‖ ^ 2)
      atTop (𝓝 (iteratedDeriv (2 * k) riemannZeta (2 * σ : ℝ)).re) := by
  set g : ℕ → ℂ := logMul^[k] 1 with hgdef
  have hg : LSeriesSummable g σ := LSeriesSummable_of_abscissaOfAbsConv_lt_re (by
    rw [hgdef, LSeries.abscissaOfAbsConv_logPowMul, LSeries.abscissaOfAbsConv_one]
    exact_mod_cast hσ)
  have h := apostol_thm_11_16 hg
  have e1 : ∀ t : ℝ, ‖iteratedDeriv k riemannZeta (σ + t * I)‖ = ‖LSeries g (σ + t * I)‖ := by
    intro t
    rw [iteratedDeriv_riemannZeta_eq k (by simpa using hσ), norm_mul, norm_pow, norm_neg,
      norm_one, one_pow, one_mul]
  simp_rw [e1]
  convert h using 2
  have hgconj : ∀ n : ℕ, n ≠ 0 → (logMul^[2 * k] (1 : ℕ → ℂ)) n = g n * (starRingEnd ℂ) (g n) := by
    intro n hn
    rw [hgdef, logMul_iterate_one_apply, logMul_iterate_one_apply, map_mul, map_pow, conj_ofReal]
    simp only [Pi.one_apply, map_one, mul_one]
    ring
  rw [iteratedDeriv_riemannZeta_eq (2 * k) (by simp; linarith), pow_mul, neg_one_sq, one_pow,
    one_mul, LSeries_congr (g := fun n => g n * (starRingEnd ℂ) (g n)) (fun hn => hgconj _ hn),
    LSeries, ofReal_mul, ofReal_ofNat, two_mul]
  rw [show (∑' n, term (fun n => g n * (starRingEnd ℂ) (g n)) ((σ : ℂ) + σ) n) =
      ((∑' n : ℕ, ‖term g σ n‖ ^ 2 : ℝ) : ℂ) by
    rw [ofReal_tsum]
    refine tsum_congr fun n => ?_
    rw [← term_mul_term, term_conj, mul_conj, Complex.normSq_eq_norm_sq, ofReal_pow], ofReal_re]

/-! ### Theorem 11.17 -/

lemma ofReal_cpow_add_mul_I {x : ℝ} (hx : 0 < x) (a t : ℝ) :
    (x : ℂ) ^ ((a : ℂ) + t * I) = (x : ℂ) ^ (a : ℂ) * exp (Real.log x * t * I) := by
  have hx' : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  rw [cpow_add _ _ hx', cpow_def_of_ne_zero hx' ((t : ℂ) * I), ← ofReal_log hx.le]
  ring_nf

lemma tendsto_avg_LSeries_mul_cpow {f : ℕ → ℂ} {σ x : ℝ} (hf : LSeriesSummable f σ) (hx : 0 < x) :
    Tendsto (fun T : ℝ => (1 / (2 * T) : ℂ) *
        ∫ t in (-T)..T, LSeries f (σ + t * I) * (x : ℂ) ^ ((σ : ℂ) + t * I))
      atTop (𝓝 (∑' n : ℕ, if Real.log x - Real.log n = 0 then term f σ n * (x : ℂ) ^ (σ : ℂ)
        else 0)) := by
  set c : ℕ → ℂ := fun n => term f σ n * (x : ℂ) ^ (σ : ℂ)
  have hc : Summable fun n => ‖c n‖ := by
    simpa [c, norm_mul] using (summable_norm_term hf).mul_right ‖(x : ℂ) ^ (σ : ℂ)‖
  have e : ∀ t : ℝ, LSeries f (σ + t * I) * (x : ℂ) ^ ((σ : ℂ) + t * I) =
      ∑' n, c n * exp ((Real.log x - Real.log n : ℝ) * t * I) := by
    intro t
    rw [LSeries, ← tsum_mul_right]
    refine tsum_congr fun n => ?_
    rw [term_add_mul_I, ofReal_cpow_add_mul_I hx, mul_mul_mul_comm, ← exp_add]
    simp only [c]
    push_cast
    ring_nf
  simp_rw [e]
  exact tendsto_avg_tsum_exp hc _

/-- **Theorem 11.17**, case `x = n`: if `F(s) = ∑ f(n) n^{-s}` converges absolutely at `σ`, then
`(1/2T) ∫_{-T}^{T} F(σ+it) n^{σ+it} dt → f(n)` for every integer `n ≥ 1`. -/
@[kb "apostol1976" "Thm 11.17, p. 242"]
theorem apostol_thm_11_17 {f : ℕ → ℂ} {σ : ℝ} (hf : LSeriesSummable f σ) {k : ℕ} (hk : k ≠ 0) :
    Tendsto (fun T : ℝ => (1 / (2 * T) : ℂ) *
        ∫ t in (-T)..T, LSeries f (σ + t * I) * (k : ℂ) ^ ((σ : ℂ) + t * I))
      atTop (𝓝 (f k)) := by
  have h := tendsto_avg_LSeries_mul_cpow hf (x := k) (by exact_mod_cast Nat.pos_of_ne_zero hk)
  rw [ofReal_natCast] at h
  convert h using 2
  rw [tsum_eq_single k]
  · rw [sub_self, ite_eq_left_of_eq_true _ _ (eq_self 0), term_of_ne_zero hk, div_mul_cancel₀]
    simp [hk]
  · intro n hn
    rcases eq_or_ne n 0 with rfl | hn0
    · simp
    split_ifs with h'
    swap; · rfl
    rw [sub_eq_zero] at h'
    exfalso
    exact hn (by exact_mod_cast (Real.log_injOn_pos (by simpa using Nat.pos_of_ne_zero hk)
      (by simpa using Nat.pos_of_ne_zero hn0) h').symm)

/-- **Theorem 11.17**, case `x` not an integer: then
`(1/2T) ∫_{-T}^{T} F(σ+it) x^{σ+it} dt → 0` for every `x > 0` that is not an integer. -/
@[kb "apostol1976" "Thm 11.17, p. 242"]
theorem apostol_thm_11_17_of_ne {f : ℕ → ℂ} {σ x : ℝ} (hf : LSeriesSummable f σ) (hx : 0 < x)
    (hxn : ∀ n : ℕ, x ≠ n) :
    Tendsto (fun T : ℝ => (1 / (2 * T) : ℂ) *
        ∫ t in (-T)..T, LSeries f (σ + t * I) * (x : ℂ) ^ ((σ : ℂ) + t * I))
      atTop (𝓝 0) := by
  convert tendsto_avg_LSeries_mul_cpow hf hx using 2
  symm
  refine (tsum_congr fun n => ?_).trans tsum_zero
  rcases eq_or_ne n 0 with rfl | hn0
  · simp
  split_ifs with h'
  swap; · rfl
  rw [sub_eq_zero] at h'
  exfalso
  exact hxn n (Real.log_injOn_pos hx (by simpa using Nat.pos_of_ne_zero hn0) h')

end NTKB.Apostol
