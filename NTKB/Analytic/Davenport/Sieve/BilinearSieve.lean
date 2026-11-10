/- Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license. -/
import NTKB.Attr
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import NTKB.Analytic.Davenport.Sieve.Characters
import NTKB.Analytic.Davenport.Sieve.BarbanDavenportHalberstam
import NTKB.Analytic.Davenport.Sieve.SineIntegral

/-!
# The bilinear large sieve (Davenport, Chapter 28)

* `perron_truncated_sine` (28-12): the truncated Perron integral
  `∫_{-T}^T e^{itα} sin(tβ)/t dt = π · [|α| < β] + O(1/(T |β - |α||))`, from the Dirichlet integral
  with error term.
* `bilinear_large_sieve` (F6): Cauchy–Schwarz over the pairs `(q, χ)` plus Theorem 4 twice.
* `bilinear_sieve_sup` (E): the same with the double sum `∑_{mn ≤ u} a_m b_n χ(mn)` truncated by an
  arbitrary `u`, at the cost of a factor `log 2MN`.
-/

open Finset Real MeasureTheory

namespace NTKB.Davenport

/-! ### Preliminaries on bounded measurable functions -/

lemma bil_ii {E : Type*} [NormedAddCommGroup E] (f : ℝ → E)
    (hm : AEStronglyMeasurable f volume) (C : ℝ) (h : ∀ t, ‖f t‖ ≤ C) (a b : ℝ) :
    IntervalIntegrable f volume a b := by
  refine (intervalIntegrable_const (c := C)).mono_fun hm.restrict ?_
  exact Filter.Eventually.of_forall fun t => (h t).trans (by rw [Real.norm_eq_abs]; exact le_abs_self C)

lemma bil_g_bound (c t : ℝ) : |sin (t * c) / t| ≤ |c| := by
  by_cases ht : t = 0
  · simp [ht]
  · rw [abs_div, div_le_iff₀ (abs_pos.2 ht)]
    calc |sin (t * c)| ≤ |t * c| := abs_sin_le_abs
      _ = |c| * |t| := by rw [abs_mul, mul_comm]

lemma bil_g_ii (c a b : ℝ) : IntervalIntegrable (fun t : ℝ => sin (t * c) / t) volume a b :=
  bil_ii _ (by fun_prop : Measurable fun t : ℝ => sin (t * c) / t).aestronglyMeasurable |c|
    (fun t => by rw [Real.norm_eq_abs]; exact bil_g_bound c t) a b

/-- The sine integral `Si`. -/
noncomputable def bil_F (x : ℝ) : ℝ := ∫ u in (0 : ℝ)..x, sin u / u

lemma bil_F_neg (x : ℝ) : bil_F (-x) = - bil_F x := by
  unfold bil_F
  have h := intervalIntegral.integral_comp_neg (a := 0) (b := x) (f := fun u : ℝ => sin u / u)
  have h2 : (∫ t in (0 : ℝ)..x, sin (-t) / (-t)) = ∫ t in (0 : ℝ)..x, sin t / t := by
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [Real.sin_neg, neg_div_neg_eq]
  rw [h2, neg_zero] at h
  rw [intervalIntegral.integral_symm (-x) 0, ← h]

lemma bil_int_g (c T : ℝ) : ∫ t in (0 : ℝ)..T, sin (t * c) / t = bil_F (c * T) := by
  by_cases hc : c = 0
  · simp [hc, bil_F]
  · have h1 : ∀ t : ℝ, sin (t * c) / t = c * (sin (c * t) / (c * t)) := by
      intro t
      by_cases ht : t = 0
      · simp [ht]
      · rw [mul_comm t c]; field_simp
    simp_rw [h1]
    rw [intervalIntegral.integral_const_mul]
    have := intervalIntegral.integral_comp_mul_left (a := 0) (b := T) (fun u : ℝ => sin u / u) hc
    simp only [smul_eq_mul, mul_zero] at this
    rw [this, mul_inv_cancel_left₀ hc]
    rfl

lemma bil_sym {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (h : ℝ → E)
    (hi : ∀ a b, IntervalIntegrable h volume a b)
    (hi' : ∀ a b, IntervalIntegrable (fun t => h (-t)) volume a b) (T : ℝ) :
    ∫ t in (-T)..T, h t = ∫ t in (0 : ℝ)..T, (h t + h (-t)) := by
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi (-T) 0) (hi 0 T)]
  have := intervalIntegral.integral_comp_neg (a := 0) (b := T) (f := h)
  rw [neg_zero] at this
  rw [intervalIntegral.integral_add (hi 0 T) (hi' 0 T), this, add_comm]

/-! ### The truncated Perron lemma -/

lemma bil_core {p r : ℝ} (hp : |r| ≤ p) (hr : r ≠ 0) :
    |bil_F p + bil_F r - (if 0 < r then π else 0)| ≤ 4 / |r| := by
  have hr' : 0 < |r| := abs_pos.2 hr
  have hp0 : 0 < p := lt_of_lt_of_le hr' hp
  have h1 : |bil_F p - π / 2| ≤ 2 / p := sineInt_error_pi_div_two hp0
  have h1' : 2 / p ≤ 2 / |r| := div_le_div_of_nonneg_left (by norm_num) hr' hp
  rcases lt_or_gt_of_ne hr with h | h
  · have h2 : |bil_F (-r) - π / 2| ≤ 2 / (-r) := sineInt_error_pi_div_two (neg_pos.2 h)
    have h3 : bil_F r = - bil_F (-r) := by
      have := bil_F_neg (-r); rwa [neg_neg] at this
    rw [abs_of_neg h] at h1' ⊢
    have h0 : (if 0 < r then π else 0) = 0 := by simp [not_lt.2 h.le]
    rw [h0, h3]
    have e : (4 : ℝ) / (-r) = 2 / (-r) + 2 / (-r) := by ring
    rw [abs_le] at h1 h2 ⊢
    rw [e]
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  · have h2 : |bil_F r - π / 2| ≤ 2 / r := sineInt_error_pi_div_two h
    rw [abs_of_pos h] at h1' ⊢
    have h0 : (if 0 < r then π else 0) = π := by simp [h]
    rw [h0]
    have e : (4 : ℝ) / r = 2 / r + 2 / r := by ring
    rw [abs_le] at h1 h2 ⊢
    rw [e]
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

lemma bil_final0 {a β T : ℝ} (ha : 0 ≤ a) (hβ : 0 < β) (hT : 0 < T) (hne : a ≠ β) :
    |bil_F ((β + a) * T) + bil_F ((β - a) * T) - (if a < β then π else 0)| ≤
      4 / (T * |β - a|) := by
  have hp : |(β - a) * T| ≤ (β + a) * T := by
    rw [abs_mul, abs_of_pos hT]
    refine mul_le_mul_of_nonneg_right ?_ hT.le
    rw [abs_le]; constructor <;> linarith
  have hr : (β - a) * T ≠ 0 := mul_ne_zero (sub_ne_zero.2 hne.symm) hT.ne'
  have := bil_core hp hr
  have hc : (0 < (β - a) * T) ↔ a < β := by
    rw [mul_pos_iff_of_pos_right hT]; constructor <;> intro h <;> linarith
  have key : (if 0 < (β - a) * T then π else 0) = (if a < β then π else 0) := by
    simp only [hc]
  rw [key] at this
  have habs : |(β - a) * T| = T * |β - a| := by rw [abs_mul, abs_of_pos hT, mul_comm]
  rwa [habs] at this

lemma bil_final {α β T : ℝ} (hβ : 0 < β) (hT : 0 < T) (hne : |α| ≠ β) :
    |bil_F ((β + α) * T) + bil_F ((β - α) * T) - (if |α| < β then π else 0)| ≤
      4 / (T * abs (β - |α|)) := by
  rcases le_or_gt 0 α with h0 | h0
  · rw [abs_of_nonneg h0] at hne ⊢
    exact bil_final0 h0 hβ hT hne
  · rw [abs_of_neg h0] at hne ⊢
    have := bil_final0 (neg_nonneg.2 h0.le) hβ hT hne
    have e1 : β + -α = β - α := by ring
    have e2 : β - -α = β + α := by ring
    rw [e1, e2, add_comm] at this
    rw [sub_neg_eq_add]
    exact this

/-- The integrand of the truncated Perron integral. -/
noncomputable def bil_h (α β t : ℝ) : ℂ :=
  Complex.exp (t * α * Complex.I) * ((Real.sin (t * β) / t : ℝ) : ℂ)

lemma bil_h_meas (α β : ℝ) : Measurable (bil_h α β) := by
  unfold bil_h; fun_prop

lemma bil_h_bound (α β t : ℝ) : ‖bil_h α β t‖ ≤ |β| := by
  unfold bil_h
  have : Complex.exp (t * α * Complex.I) = Complex.exp (((t * α : ℝ) : ℂ) * Complex.I) := by
    push_cast; ring_nf
  rw [norm_mul, this, Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_real,
    Real.norm_eq_abs]
  exact bil_g_bound β t

lemma bil_h_ii (α β a b : ℝ) : IntervalIntegrable (bil_h α β) volume a b :=
  bil_ii _ (bil_h_meas α β).aestronglyMeasurable |β| (bil_h_bound α β) a b

lemma bil_h_ii' (α β a b : ℝ) : IntervalIntegrable (fun t => bil_h α β (-t)) volume a b :=
  bil_ii _ ((bil_h_meas α β).comp measurable_neg).aestronglyMeasurable |β|
    (fun t => bil_h_bound α β (-t)) a b

lemma bil_exp (x : ℝ) :
    Complex.exp ((x : ℂ) * Complex.I) = ((Real.cos x : ℝ) : ℂ) + ((Real.sin x : ℝ) : ℂ) * Complex.I := by
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

lemma bil_h_add_neg (α β t : ℝ) :
    bil_h α β t + bil_h α β (-t) =
      ((sin (t * (β + α)) / t + sin (t * (β - α)) / t : ℝ) : ℂ) := by
  have hx : (t : ℂ) * α * Complex.I = ((t * α : ℝ) : ℂ) * Complex.I := by push_cast; ring
  have hy : ((-t : ℝ) : ℂ) * α * Complex.I = ((-(t * α) : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  have hs : sin (-t * β) / (-t) = sin (t * β) / t := by
    rw [neg_mul, Real.sin_neg, neg_div_neg_eq]
  have hr : sin (t * (β + α)) / t + sin (t * (β - α)) / t = 2 * cos (t * α) * (sin (t * β) / t) := by
    have e1 : t * (β + α) = t * β + t * α := by ring
    have e2 : t * (β - α) = t * β - t * α := by ring
    rw [e1, e2, Real.sin_add, Real.sin_sub]
    ring
  unfold bil_h
  rw [hx, hy, bil_exp, bil_exp, Real.cos_neg, Real.sin_neg, hs, hr]
  push_cast
  ring

/-- **Davenport, Ch. 28, (28-12)** (truncated Perron lemma): for `T > 0`, `β > 0` and real `α`
with `|α| ≠ β`,
`∫_{-T}^T e^{itα} (sin tβ)/t dt = π · [|α| < β] + O(1/(T |β - |α||))`, with constant `4`. -/
@[kb "davenport1980" "Ch 28, p. 165"]
theorem perron_truncated_sine {T β α : ℝ} (hT : 0 < T) (hβ : 0 < β) (hne : |α| ≠ β) :
    ‖(∫ t in (-T)..T, Complex.exp (t * α * Complex.I) * ((Real.sin (t * β) / t : ℝ) : ℂ)) -
        ((if |α| < β then π else 0 : ℝ) : ℂ)‖ ≤ 4 / (T * abs (β - |α|)) := by
  have hmain : (∫ t in (-T)..T, bil_h α β t) =
      ((bil_F ((β + α) * T) + bil_F ((β - α) * T) : ℝ) : ℂ) := by
    rw [bil_sym (bil_h α β) (bil_h_ii α β) (bil_h_ii' α β) T]
    simp_rw [bil_h_add_neg]
    rw [intervalIntegral.integral_ofReal,
      intervalIntegral.integral_add (bil_g_ii _ _ _) (bil_g_ii _ _ _), bil_int_g, bil_int_g]
  show ‖(∫ t in (-T)..T, bil_h α β t) - _‖ ≤ _
  rw [hmain, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  exact bil_final hβ hT hne

/-! ### The bilinear large sieve -/

open scoped Classical in
/-- Theorem 4 for sequences indexed by `ℕ` and the range `1 ≤ n ≤ N`. -/
lemma bil_T4 {Q : ℝ} (hQ : 1 ≤ Q) (N : ℕ) (b : ℕ → ℂ) :
    ∑ q ∈ Icc 1 ⌊Q⌋₊, ((q : ℝ) / q.totient) *
        ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ ↦ χ.IsPrimitive),
          ‖∑ n ∈ Icc 1 N, b n * χ n‖ ^ 2 ≤
      (N + 3 * Q ^ 2) * ∑ n ∈ Icc 1 N, ‖b n‖ ^ 2 := by
  set c : ℤ → ℂ := fun n ↦ b n.toNat
  have h := large_sieve_characters hQ 0 N c
  have hT : ∀ (q : ℕ) (χ : DirichletCharacter ℂ q),
      ∑ n ∈ Ioc (0 : ℤ) (0 + N), c n * χ n = ∑ n ∈ Icc 1 N, b n * χ n := by
    intro q χ
    rw [sum_Ioc_zero_int_eq (fun n ↦ c n * χ n)]
    refine sum_congr rfl fun n _ ↦ ?_
    simp only [c, Int.toNat_natCast]
    push_cast; ring
  have hc : ∑ n ∈ Ioc (0 : ℤ) (0 + N), ‖c n‖ ^ 2 = ∑ n ∈ Icc 1 N, ‖b n‖ ^ 2 := by
    rw [sum_Ioc_zero_int_eq (fun n ↦ ‖c n‖ ^ 2)]
    refine sum_congr rfl fun n _ ↦ ?_
    simp only [c, Int.toNat_natCast]
  simp_rw [hT] at h
  rw [hc] at h
  exact h

open scoped Classical in
/-- **Davenport, Ch. 28, p. 165, (6)** (bilinear large sieve). -/
@[kb "davenport1980" "Ch 28, p. 165, (6)"]
theorem bilinear_large_sieve {Q : ℝ} (hQ : 1 ≤ Q) (M N : ℕ) (a b : ℕ → ℂ) :
    ∑ q ∈ Icc 1 ⌊Q⌋₊, ((q : ℝ) / q.totient) *
        ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ ↦ χ.IsPrimitive),
          ‖∑ m ∈ Icc 1 M, a m * χ m‖ * ‖∑ n ∈ Icc 1 N, b n * χ n‖ ≤
      √((M + 3 * Q ^ 2) * (N + 3 * Q ^ 2)) * √(∑ m ∈ Icc 1 M, ‖a m‖ ^ 2) *
        √(∑ n ∈ Icc 1 N, ‖b n‖ ^ 2) := by
  set A : ℕ → ℝ := fun q ↦
    ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ ↦ χ.IsPrimitive),
      ‖∑ m ∈ Icc 1 M, a m * χ m‖ ^ 2 with hA
  set B : ℕ → ℝ := fun q ↦
    ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ ↦ χ.IsPrimitive),
      ‖∑ n ∈ Icc 1 N, b n * χ n‖ ^ 2 with hB
  have hw : ∀ q : ℕ, 0 ≤ (q : ℝ) / q.totient := fun q ↦ by positivity
  have hA0 : ∀ q, 0 ≤ A q := fun q ↦ sum_nonneg fun _ _ ↦ by positivity
  have hB0 : ∀ q, 0 ≤ B q := fun q ↦ sum_nonneg fun _ _ ↦ by positivity
  have step1 : ∀ q ∈ Icc 1 ⌊Q⌋₊, ((q : ℝ) / q.totient) *
        ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ ↦ χ.IsPrimitive),
          ‖∑ m ∈ Icc 1 M, a m * χ m‖ * ‖∑ n ∈ Icc 1 N, b n * χ n‖ ≤
      √(((q : ℝ) / q.totient) * A q) * √(((q : ℝ) / q.totient) * B q) := by
    intro q _
    have h := Real.sum_sqrt_mul_sqrt_le
      ((univ : Finset (DirichletCharacter ℂ q)).filter (fun χ ↦ χ.IsPrimitive))
      (f := fun χ ↦ ‖∑ m ∈ Icc 1 M, a m * χ m‖ ^ 2) (g := fun χ ↦ ‖∑ n ∈ Icc 1 N, b n * χ n‖ ^ 2)
      (fun _ ↦ by positivity) (fun _ ↦ by positivity)
    simp only [Real.sqrt_sq (norm_nonneg _)] at h
    rw [Real.sqrt_mul (hw q), Real.sqrt_mul (hw q)]
    calc _ ≤ ((q : ℝ) / q.totient) * (√(A q) * √(B q)) := mul_le_mul_of_nonneg_left h (hw q)
      _ = (√((q : ℝ) / q.totient) * √((q : ℝ) / q.totient)) * (√(A q) * √(B q)) := by
          rw [Real.mul_self_sqrt (hw q)]
      _ = _ := by ring
  have step2 := Real.sum_sqrt_mul_sqrt_le (Icc 1 ⌊Q⌋₊)
    (f := fun q : ℕ ↦ ((q : ℝ) / q.totient) * A q) (g := fun q : ℕ ↦ ((q : ℝ) / q.totient) * B q)
    (fun q ↦ mul_nonneg (hw q) (hA0 q)) (fun q ↦ mul_nonneg (hw q) (hB0 q))
  have hT1 := bil_T4 hQ M a
  have hT2 := bil_T4 hQ N b
  have hS1 : 0 ≤ ∑ m ∈ Icc 1 M, ‖a m‖ ^ 2 := sum_nonneg fun _ _ ↦ by positivity
  have hS2 : 0 ≤ ∑ n ∈ Icc 1 N, ‖b n‖ ^ 2 := sum_nonneg fun _ _ ↦ by positivity
  have hQ0 : (0 : ℝ) ≤ M + 3 * Q ^ 2 := by positivity
  have hQ1 : (0 : ℝ) ≤ N + 3 * Q ^ 2 := by positivity
  calc _ ≤ ∑ q ∈ Icc 1 ⌊Q⌋₊, √(((q : ℝ) / q.totient) * A q) * √(((q : ℝ) / q.totient) * B q) :=
        sum_le_sum step1
    _ ≤ √(∑ q ∈ Icc 1 ⌊Q⌋₊, ((q : ℝ) / q.totient) * A q) *
          √(∑ q ∈ Icc 1 ⌊Q⌋₊, ((q : ℝ) / q.totient) * B q) := step2
    _ ≤ √((M + 3 * Q ^ 2) * ∑ m ∈ Icc 1 M, ‖a m‖ ^ 2) *
          √((N + 3 * Q ^ 2) * ∑ n ∈ Icc 1 N, ‖b n‖ ^ 2) :=
        mul_le_mul (Real.sqrt_le_sqrt hT1) (Real.sqrt_le_sqrt hT2) (Real.sqrt_nonneg _)
          (Real.sqrt_nonneg _)
    _ = _ := by
        rw [Real.sqrt_mul hQ0, Real.sqrt_mul hQ1, Real.sqrt_mul hQ0]
        ring

end NTKB.Davenport
