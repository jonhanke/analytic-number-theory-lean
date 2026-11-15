/- Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license. -/
import NTKB.Analytic.Davenport.Zeros.Perron
import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Perron's formula (Apostol, Chapter 11, §11.12, Lemma 4 and Theorem 11.18)

With `I(a, T) = (1/2πi) ∫_{c-iT}^{c+iT} a^z/z dz = (1/2π) ∫_{-T}^{T} a^{c+it}/(c+it) dt`
(`NTKB.perronIntegral a c T`):

* **Lemma 4**: for `c > 0`, `a > 0`, `I(a, T) → 1, 1/2, 0` as `T → ∞` for `a > 1`, `a = 1`,
  `0 < a < 1`, with `|I(a, T) - 1| ≤ a^c/(πT log a)` (`a > 1`), `|I(a, T)| ≤ a^c/(πT|log a|)`
  (`a < 1`) and `|I(1, T) - 1/2| ≤ c/(πT)` (`apostol_lemma_11_4`). This is Davenport's lemma of
  Chapter 17 (`NTKB.Davenport.perron_truncated`, `NTKB.Davenport.perron_discontinuous_integral`),
  proved here by Davenport's contour argument.
* **Theorem 11.18** (Perron's formula): if `∑ f(n) n^{-s}` converges absolutely at `s + c`
  (`c > 0`), then for `x > 0`
  `(1/2πi) ∫_{c-iT}^{c+iT} F(s + z) x^z/z dz → ∑*_{n ≤ x} f(n) n^{-s}` as `T → ∞`, where `∑*`
  means the last term is halved when `x` is an integer (`apostol_thm_11_18`).

The proof of 11.18 is Apostol's: the series is integrated term by term over the finite segment
(absolute convergence on the line `Re z = c`), which gives `∑ f(n) n^{-s} I(x/n, T)`, and the
bounds of Lemma 4 give the limit, since `|log(x/n)|` is bounded below for `n ≠ x`. The
interchange follows Tau Ceti's `TauCeti.integral_LSeries_mul_perronIntegrand`
(TauCeti/NumberTheory/ArithmeticDirichletSeries/Perron/Formula.lean, Apache 2.0, credited).
-/

open Complex Filter Topology MeasureTheory
open scoped Real

namespace NTKB.Apostol


/-- **Apostol, Chapter 11, Lemma 4**: for `c > 0`, `a > 0`, `T > 0`:
`|I(a, T) - 1| ≤ a^c/(πT log a)` for `a > 1`, `|I(a, T)| ≤ a^c/(πT|log a|)` for `a < 1`,
`|I(1, T) - 1/2| ≤ c/(πT)`; hence `I(a, T) → 1, 1/2, 0` as `T → ∞`. -/
@[kb "apostol1976" "Ch 11, Lemma 4, p. 243"]
theorem apostol_lemma_11_4 {a c : ℝ} (ha : 0 < a) (hc : 0 < c) :
    (∀ T : ℝ, 0 < T → 1 < a →
      ‖perronIntegral a c T - 1‖ ≤ a ^ c / (π * T * Real.log a)) ∧
    (∀ T : ℝ, 0 < T → a < 1 →
      ‖perronIntegral a c T‖ ≤ a ^ c / (π * T * |Real.log a|)) ∧
    (∀ T : ℝ, 0 < T → a = 1 → ‖perronIntegral a c T - 1 / 2‖ ≤ c / (π * T)) ∧
    Tendsto (fun T ↦ perronIntegral a c T) atTop
      (𝓝 (if a < 1 then 0 else if a = 1 then 1 / 2 else 1)) := by
  refine ⟨fun T hT h1 ↦ ?_, fun T hT h1 ↦ ?_, fun T hT h1 ↦ ?_,
    Davenport.perron_discontinuous_integral ha hc⟩
  · have := norm_perronIntegral_gt_one_log h1 hc hT
    rwa [abs_of_pos (Real.log_pos h1)] at this
  · exact norm_perronIntegral_lt_one_log ha h1 hc hT
  · subst h1
    exact norm_perronIntegral_one_sub_half hc hT

/-! ### Interchange of the integral and the series -/

/-- The Perron integrand `y^z/z` is continuous along the vertical line for `y > 0`. -/
private lemma continuous_kernel_line {y : ℝ} (hy : 0 < y) {c : ℝ} (hc : 0 < c) :
    Continuous fun t : ℝ ↦ (y : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I) := by
  have hline : Continuous fun t : ℝ ↦ (c : ℂ) + t * I :=
    continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  refine (hline.const_cpow (Or.inl (by exact_mod_cast hy.ne'))).div hline fun t ↦ ?_
  intro h
  have := congrArg Complex.re h
  simp at this
  linarith

private lemma norm_kernel_line_le {y : ℝ} (hy : 0 < y) {c : ℝ} (hc : 0 < c) (t : ℝ) :
    ‖(y : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I)‖ ≤ y ^ c / c := by
  rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hy]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
    Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero]
  have : c ≤ ‖(c : ℂ) + t * I‖ := by
    have := Complex.abs_re_le_norm ((c : ℂ) + t * I)
    exact le_trans (le_abs_self c) (by simpa using this)
  have h0 : (0 : ℝ) ≤ y ^ c := Real.rpow_nonneg hy.le c
  exact div_le_div_of_nonneg_left h0 hc this

private lemma continuous_term_line (f : ℕ → ℂ) (c : ℝ) (n : ℕ) :
    Continuous fun t : ℝ ↦ LSeries.term f ((c : ℂ) + t * I) n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simpa using continuous_const
  · have hline : Continuous fun t : ℝ ↦ (c : ℂ) + t * I :=
      continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
    have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn
    simp only [LSeries.term_of_ne_zero hn]
    refine continuous_const.div (hline.const_cpow (Or.inl hn0)) fun t ↦ ?_
    exact fun h ↦ hn0 ((Complex.cpow_eq_zero_iff _ _).mp h).1

/-- Termwise integration of the Perron integrand against an absolutely convergent series.
(Adapted from Tau Ceti's `TauCeti.truncatedPerron_LSeries`.) -/
private lemma perron_interchange {f : ℕ → ℂ} (hf0 : f 0 = 0) {c x T : ℝ} (hc : 0 < c)
    (hx : 0 < x) (hT : 0 ≤ T) (h : LSeriesSummable f (c : ℂ)) :
    (1 / (2 * π)) * ∫ t : ℝ in -T..T,
        LSeries f ((c : ℂ) + t * I) * (x : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I) =
      ∑' n : ℕ, f n * perronIntegral (x / n) c T := by
  have hle : -T ≤ T := by linarith
  set K : ℝ → ℂ := fun t ↦ (x : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I) with hK
  have hKc : Continuous K := continuous_kernel_line hx hc
  have hsum : ∀ t : ℝ, LSeriesSummable f ((c : ℂ) + t * I) := fun t ↦
    h.of_re_le_re (by simp)
  have hhas := intervalIntegral.hasSum_integral_of_dominated_convergence
    (a := -T) (b := T) (μ := MeasureTheory.volume)
    (F := fun (n : ℕ) (t : ℝ) ↦ LSeries.term f ((c : ℂ) + t * I) n * K t)
    (f := fun t ↦ LSeries f ((c : ℂ) + t * I) * K t)
    (fun n _ ↦ ‖LSeries.term f (c : ℂ) n‖ * (x ^ c / c))
    (fun n ↦ ((continuous_term_line f c n).mul hKc).aestronglyMeasurable)
    (fun n ↦ Filter.Eventually.of_forall fun t _ ↦ by
      rw [norm_mul]
      exact mul_le_mul (LSeries.norm_term_le_of_re_le_re f (by simp) n)
        (norm_kernel_line_le hx hc t) (norm_nonneg _) (norm_nonneg _))
    (Filter.Eventually.of_forall fun t _ ↦ (summable_norm_iff.2 h).mul_right _)
    (by exact intervalIntegrable_const)
    (Filter.Eventually.of_forall fun t _ ↦ ((hsum t).hasSum).mul_right (K t))
  have h1 : (∫ t : ℝ in -T..T,
        LSeries f ((c : ℂ) + t * I) * (x : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I)) =
      ∑' n : ℕ, ∫ t : ℝ in -T..T, LSeries.term f ((c : ℂ) + t * I) n * K t := by
    rw [hhas.tsum_eq]
    refine intervalIntegral.integral_congr fun t _ ↦ ?_
    simp only [hK]; ring
  rw [h1, ← tsum_mul_left]
  refine tsum_congr fun n ↦ ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp [hf0]
  · have hn0 : 0 < (n : ℝ) := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn)
    have : ∀ t : ℝ, LSeries.term f ((c : ℂ) + t * I) n * K t =
        f n * (((x / n : ℝ) : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I)) := by
      intro t
      rw [LSeries.term_of_ne_zero hn, Complex.ofReal_div, Complex.div_cpow_ofReal_nonneg hx.le
        (Nat.cast_nonneg n), Complex.ofReal_natCast]
      simp only [hK]; ring
    simp only [this]
    rw [intervalIntegral.integral_const_mul, perronIntegral]
    ring

/-! ### Dominated convergence -/

private lemma summable_err {f : ℕ → ℂ} {c x : ℝ} (hx : 0 < x)
    (h : LSeriesSummable f (c : ℂ)) :
    Summable fun n : ℕ ↦ ‖f n‖ * ((x / n) ^ c / (π * |Real.log (x / n)|)) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos one_lt_two
  have hg : Summable fun n : ℕ ↦ x ^ c / (π * Real.log 2) * ‖LSeries.term f (c : ℂ) n‖ :=
    (summable_norm_iff.2 h).mul_left _
  refine Summable.of_norm_bounded_eventually_nat hg ?_
  filter_upwards [Filter.eventually_ge_atTop ⌈2 * x⌉₊, Filter.eventually_gt_atTop 0]
    with n hn hn0
  have hcast : (0 : ℝ) < n := Nat.cast_pos.2 hn0
  have hle : 2 * x ≤ n := Nat.ceil_le.1 hn
  have hxn : 0 < x / n := div_pos hx hcast
  have hhalf : x / n ≤ 1 / 2 := by rw [div_le_iff₀ hcast]; linarith
  have hlog : Real.log 2 ≤ |Real.log (x / n)| := by
    have hmono : Real.log (x / n) ≤ Real.log (1 / 2) := Real.log_le_log hxn hhalf
    rw [Real.log_div one_ne_zero two_ne_zero, Real.log_one, zero_sub] at hmono
    rw [abs_of_nonpos (by linarith)]
    linarith
  have hnorm : ‖LSeries.term f (c : ℂ) n‖ = ‖f n‖ / n ^ c := by
    rw [LSeries.norm_term_eq]
    simp [hn0.ne']
  rw [Real.norm_of_nonneg (by positivity), hnorm, Real.div_rpow hx.le hcast.le]
  have hbound : ‖f n‖ * (x ^ c / n ^ c / (π * |Real.log (x / n)|))
      ≤ ‖f n‖ * (x ^ c / n ^ c / (π * Real.log 2)) := by
    gcongr
  exact hbound.trans_eq (by ring)

private lemma summable_ind (x : ℝ) (hx : 0 < x) (f : ℕ → ℂ) (C : ℝ) :
    Summable fun n : ℕ ↦ (if 1 / 2 < x / n then ‖f n‖ * C else 0) :=
  summable_of_ne_finset_zero (s := Finset.range ⌈2 * x⌉₊) fun n hn ↦ by
    simp only [Finset.mem_range, not_lt] at hn
    have hcast : (0 : ℝ) < n := lt_of_lt_of_le (by positivity) (Nat.ceil_le.1 hn)
    have hle : x / n ≤ 1 / 2 := by rw [div_le_iff₀ hcast]; linarith [Nat.ceil_le.1 hn]
    exact ite_eq_right_iff.2 fun hc ↦ absurd hc (not_lt.2 hle)

private lemma norm_perronIntegral_le_bound {y c T : ℝ} (hy : 0 < y) (hc : 0 < c) (hT : 1 ≤ T) :
    ‖perronIntegral y c T‖ ≤
      y ^ c / (π * |Real.log y|) + (if 1 / 2 < y then 1 + c else 0) := by
  have hT0 : 0 < T := by linarith
  have hπ := Real.pi_pos
  have hE : 0 ≤ y ^ c / (π * |Real.log y|) := by positivity
  obtain ⟨h1, h2, h3, -⟩ := apostol_lemma_11_4 hy hc
  rcases lt_trichotomy y 1 with hy1 | hy1 | hy1
  · have hl : 0 < |Real.log y| := abs_pos.mpr (Real.log_neg hy hy1).ne
    have := h2 T hT0 hy1
    have h4 : y ^ c / (π * T * |Real.log y|) ≤ y ^ c / (π * |Real.log y|) := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      nlinarith [mul_pos hπ hl]
    split_ifs <;> linarith
  · subst hy1
    have := h3 T hT0 rfl
    have h5 : c / (π * T) ≤ c := by
      rw [div_le_iff₀ (by positivity)]
      have h1 : 1 ≤ π * T := by nlinarith [Real.pi_gt_three]
      nlinarith [mul_le_mul_of_nonneg_left h1 hc.le]
    simp only [show (1 : ℝ) / 2 < 1 by norm_num, ite_true]
    calc ‖perronIntegral 1 c T‖ ≤ ‖perronIntegral 1 c T - 1 / 2‖ + ‖(1 / 2 : ℂ)‖ := by
          have := norm_add_le (perronIntegral 1 c T - 1 / 2) (1 / 2)
          rwa [sub_add_cancel] at this
      _ ≤ _ := by
          have : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
          linarith
  · have hl : 0 < Real.log y := Real.log_pos hy1
    have := h1 T hT0 hy1
    have h4 : y ^ c / (π * T * Real.log y) ≤ y ^ c / (π * |Real.log y|) := by
      rw [abs_of_pos hl]
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      nlinarith [mul_pos hπ hl]
    have h7 : (1 / 2 : ℝ) < y := by linarith
    simp only [h7, ite_true]
    have := norm_add_le (perronIntegral y c T - 1) 1
    rw [sub_add_cancel] at this
    simp at this
    linarith

/-- **Apostol, Theorem 11.18 (Perron's formula)**: if `∑ f(n) n^{-(s + c)}` converges absolutely,
`c > 0`, `x > 0`, then
`(1/2π) ∫_{-T}^{T} F(s + c + it) x^{c+it}/(c+it) dt → ∑_{n ≤ x} f(n) n^{-s}` as `T → ∞`, with the
term `n = x` halved. -/
@[kb "apostol1976" "Thm 11.18, p. 245"]
theorem apostol_thm_11_18 (f : ℕ → ℂ) {s : ℂ} {c x : ℝ} (hc : 0 < c) (hx : 0 < x)
    (hf : LSeriesSummable f (s + c)) :
    Tendsto (fun T : ℝ ↦ (1 / (2 * π)) * ∫ t : ℝ in -T..T,
        LSeries f (s + c + t * I) * (x : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I))
      atTop (𝓝 (∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
        (if (n : ℝ) = x then (1 / 2 : ℂ) else 1) * f n / (n : ℂ) ^ s)) := by
  obtain ⟨g, hg⟩ : ∃ g : ℕ → ℂ, g = LSeries.term f s := ⟨_, rfl⟩
  have hg0 : g 0 = 0 := by rw [hg]; exact LSeries.term_zero f s
  have hterm : ∀ (z : ℂ) (n : ℕ), LSeries.term g z n = LSeries.term f (s + z) n := by
    intro z n
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn
      rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, hg, LSeries.term_of_ne_zero hn,
        Complex.cpow_add _ _ hn0, div_div]
  have hgs : LSeriesSummable g (c : ℂ) := by
    have e : LSeries.term g (c : ℂ) = LSeries.term f (s + c) := funext (hterm _)
    unfold LSeriesSummable
    rw [e]
    exact hf
  have hL : ∀ z : ℂ, LSeries g z = LSeries f (s + z) := by
    intro z
    unfold LSeries
    exact tsum_congr fun n ↦ hterm z n
  have hint : ∀ T : ℝ, 0 ≤ T → (1 / (2 * π)) * ∫ t : ℝ in -T..T,
        LSeries f (s + c + t * I) * (x : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I) =
      ∑' n : ℕ, g n * perronIntegral (x / n) c T := by
    intro T hT
    rw [← perron_interchange hg0 hc hx hT hgs]
    refine congrArg _ (intervalIntegral.integral_congr fun t _ ↦ ?_)
    show _ = _
    rw [hL, add_assoc]
  have hpt : ∀ n : ℕ, Tendsto (fun T : ℝ ↦ g n * perronIntegral (x / n) c T) atTop
      (𝓝 (g n * (if x / n < 1 then (0 : ℂ) else if x / n = 1 then 1 / 2 else 1))) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · simp [hg0]
    · exact (Davenport.perron_discontinuous_integral
        (div_pos hx (Nat.cast_pos.2 hn0)) hc).const_mul _
  have hdom : ∀ᶠ T : ℝ in atTop, ∀ n : ℕ,
      ‖g n * perronIntegral (x / n) c T‖ ≤
        ‖g n‖ * ((x / n) ^ c / (π * |Real.log (x / n)|)) +
          (if 1 / 2 < x / n then ‖g n‖ * (1 + c) else 0) := by
    filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with T hT n
    have hE : 0 ≤ ‖g n‖ * ((x / n) ^ c / (π * |Real.log (x / n)|)) := by positivity
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · rw [hg0, zero_mul, norm_zero]
      split_ifs <;> simp [hg0]
    · have hb := norm_perronIntegral_le_bound (div_pos hx (Nat.cast_pos.2 hn0)) hc hT
      rw [norm_mul]
      calc ‖g n‖ * ‖perronIntegral (x / n) c T‖
          ≤ ‖g n‖ * ((x / n) ^ c / (π * |Real.log (x / n)|) +
              (if 1 / 2 < x / n then 1 + c else 0)) :=
            mul_le_mul_of_nonneg_left hb (norm_nonneg _)
        _ = _ := by split_ifs <;> ring
  have hlim := tendsto_tsum_of_dominated_convergence
    ((summable_err hx hgs).add (summable_ind x hx g (1 + c))) hpt hdom
  have htsum : ∑' n : ℕ, g n * (if x / n < 1 then (0 : ℂ) else if x / n = 1 then 1 / 2 else 1) =
      ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (if (n : ℝ) = x then (1 / 2 : ℂ) else 1) * f n / (n : ℂ) ^ s := by
    rw [tsum_eq_sum (s := Finset.Icc 1 ⌊x⌋₊)]
    · refine Finset.sum_congr rfl fun n hn ↦ ?_
      rw [Finset.mem_Icc] at hn
      have hn0 : (0 : ℝ) < n := Nat.cast_pos.2 hn.1
      have hnx : (n : ℝ) ≤ x := (Nat.cast_le.2 hn.2).trans (Nat.floor_le hx.le)
      have hge : 1 ≤ x / n := (one_le_div hn0).2 hnx
      rw [hg, LSeries.term_of_ne_zero (by omega)]
      by_cases hxn : (n : ℝ) = x
      · have : x / n = 1 := by rw [← hxn]; exact div_self hn0.ne'
        rw [this, if_neg (lt_irrefl _), if_pos rfl, if_pos hxn]; ring
      · have : 1 < x / n := lt_of_le_of_ne hge (fun h ↦ hxn ((div_eq_one_iff_eq hn0.ne').1 h.symm).symm)
        rw [if_neg (not_lt.2 this.le), if_neg this.ne', if_neg hxn]; ring
    · intro n hn
      rw [Finset.mem_Icc, not_and_or] at hn
      rcases Nat.eq_zero_or_pos n with rfl | hn0
      · simp
      · have h1 : ⌊x⌋₊ < n := by omega
        have : x < n := (Nat.floor_lt hx.le).1 h1
        have hn0' : (0 : ℝ) < n := Nat.cast_pos.2 hn0
        simp [(div_lt_one hn0').2 this]
  rw [htsum] at hlim
  refine hlim.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with T hT
  exact (hint T hT).symm

end NTKB.Apostol
