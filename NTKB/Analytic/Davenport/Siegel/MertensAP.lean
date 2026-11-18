/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Davenport.Siegel.PrimeCountingAP

/-!
# Mertens' theorem for arithmetic progressions

**Davenport, Ch. 7, p. 67 (row 7-16).** For `q ≥ 1` and `a`
prime to `q`, `∑_{p ≤ x, p ≡ a (q)} 1/p = (1/φ(q)) log log x + A(q, a) + O(1/log x)`, the constant
in the `O` depending on `q`. Route: partial summation `∑_{p ≤ x} 1/p = π(x;q,a)/x + ∫_2^x π(t;q,a)/t² dt`
against `π(t; q, a) = li t/φ(q) + O(t exp(-c √log t))` (`siegel_walfisz_primeCounting`, fixed `q`),
with `li x/x + ∫_2^x li t/t² dt = log log x - log log 2`.
-/

open Finset MeasureTheory
open scoped Real

namespace NTKB.Davenport

/-- `∑_{p ≤ x, p ≡ a (q)} 1/p`. -/
noncomputable def sumInvPrimeAP (x : ℝ) (q : ℕ) (a : ℤ) : ℝ :=
  ∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun p : ℕ ↦ p.Prime ∧ (p : ℤ) ≡ a [ZMOD q]), (1 / (p : ℝ))

/-- The indicator of a prime `≡ a (q)`. -/
noncomputable def apCoeff (q : ℕ) (a : ℤ) (n : ℕ) : ℝ :=
  if n.Prime ∧ (n : ℤ) ≡ a [ZMOD q] then 1 else 0

lemma primeCountingAP_eq_sum (x : ℝ) (q : ℕ) (a : ℤ) :
    (primeCountingAP x q a : ℝ) = ∑ n ∈ Icc 0 ⌊x⌋₊, apCoeff q a n := by
  unfold primeCountingAP apCoeff
  rw [← sum_Icc_one_eq _ (by simp [Nat.not_prime_zero]), Finset.sum_boole]

lemma sumInvPrimeAP_eq_sum (x : ℝ) (q : ℕ) (a : ℤ) :
    sumInvPrimeAP x q a = ∑ n ∈ Icc 0 ⌊x⌋₊, ((n : ℝ))⁻¹ * apCoeff q a n := by
  unfold sumInvPrimeAP
  rw [Finset.sum_filter, sum_Icc_one_eq _ (by simp)]
  refine Finset.sum_congr rfl fun n _ ↦ ?_
  unfold apCoeff
  split_ifs <;> simp

lemma intervalIntegrable_primeCountingAP_div {x : ℝ} (q : ℕ) (a : ℤ) (hx : 2 ≤ x) :
    IntervalIntegrable (fun t : ℝ ↦ (primeCountingAP t q a : ℝ) / t ^ 2) volume 2 x := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hx]
  have := integrableOn_mul_sum_Icc (m := 0) (apCoeff q a) (a := 2) (b := x) (by norm_num)
    (g := fun t : ℝ ↦ 1 / t ^ 2) (by
      refine ContinuousOn.integrableOn_Icc fun t ht ↦ ContinuousAt.continuousWithinAt ?_
      have h0 : t ≠ 0 := by linarith [ht.1]
      fun_prop (disch := exact pow_ne_zero 2 h0))
  refine this.congr_fun (fun t _ ↦ ?_) measurableSet_Icc
  simp only [primeCountingAP_eq_sum]
  ring

/-- Partial summation for `∑ 1/p`. -/
lemma sumInvPrimeAP_eq {x : ℝ} (q : ℕ) (a : ℤ) (hx : 2 ≤ x) :
    sumInvPrimeAP x q a = (primeCountingAP x q a : ℝ) / x +
      ∫ t in (2 : ℝ)..x, (primeCountingAP t q a : ℝ) / t ^ 2 := by
  have hc0 : apCoeff q a 0 = 0 := by simp [apCoeff, Nat.not_prime_zero]
  have hc1 : apCoeff q a 1 = 0 := by simp [apCoeff, Nat.not_prime_one]
  rw [sumInvPrimeAP_eq_sum, sum_mul_eq_sub_integral_mul₁ (apCoeff q a) (f := fun t : ℝ ↦ t⁻¹)
    hc0 hc1 x ?_ ?_, ← intervalIntegral.integral_of_le hx]
  · have int_deriv :
        ∫ u in (2 : ℝ)..x, deriv (fun x : ℝ ↦ x⁻¹) u * ∑ k ∈ Icc 0 ⌊u⌋₊, apCoeff q a k =
        ∫ u in (2 : ℝ)..x, -((primeCountingAP u q a : ℝ) / u ^ 2) :=
      intervalIntegral.integral_congr fun u hu ↦ by
        rw [Set.uIcc_of_le hx] at hu
        have h0 : u ≠ 0 := by linarith [hu.1]
        simp only [deriv_inv, ← primeCountingAP_eq_sum]
        field_simp
    rw [int_deriv, intervalIntegral.integral_neg, ← primeCountingAP_eq_sum]
    ring
  · intro z ⟨hz, _⟩
    have : z ≠ 0 := by linarith
    fun_prop
  · refine ContinuousOn.integrableOn_Icc fun z ⟨hz, _⟩ ↦ ContinuousWithinAt.congr ?_
      (fun _ _ ↦ deriv_inv) deriv_inv
    have : z ≠ 0 := by linarith
    exact ContinuousAt.continuousWithinAt <| by fun_prop (disch := exact pow_ne_zero 2 this)

lemma hasDerivAt_logIntegral {t : ℝ} (ht : 1 < t) :
    HasDerivAt NTKB.logIntegral (1 / Real.log t) t := by
  have hon : ContinuousOn (fun s : ℝ ↦ 1 / Real.log s) (Set.Ioi 1) := by
    intro s hs
    have h0 : s ≠ 0 := by have := hs.out; linarith
    have hl : Real.log s ≠ 0 := (Real.log_pos hs).ne'
    exact (continuousAt_const.div (Real.continuousAt_log h0) hl).continuousWithinAt
  have hct : ContinuousAt (fun s : ℝ ↦ 1 / Real.log s) t :=
    hon.continuousAt (Ioi_mem_nhds ht)
  have hint : IntervalIntegrable (fun s : ℝ ↦ 1 / Real.log s) volume 2 t := by
    refine (hon.mono ?_).intervalIntegrable
    intro s hs
    rcases Set.mem_uIcc.mp hs with h | h
    · exact lt_of_lt_of_le one_lt_two h.1
    · exact lt_of_lt_of_le ht h.1
  exact intervalIntegral.integral_hasDerivAt_right hint
    (hon.stronglyMeasurableAtFilter isOpen_Ioi t ht) hct

lemma intervalIntegrable_logIntegral_div {x : ℝ} (hx : 2 ≤ x) :
    IntervalIntegrable (fun t : ℝ ↦ NTKB.logIntegral t / t ^ 2) volume 2 x := by
  refine ContinuousOn.intervalIntegrable fun t ht ↦ ?_
  rw [Set.uIcc_of_le hx] at ht
  have h0 : t ≠ 0 := by linarith [ht.1]
  have hc := (hasDerivAt_logIntegral (by linarith [ht.1] : 1 < t)).continuousAt
  exact (hc.div ((continuousAt_id (x := t)).pow 2) (pow_ne_zero 2 h0)).continuousWithinAt

lemma logIntegral_div_add_integral {x : ℝ} (hx : 2 ≤ x) :
    NTKB.logIntegral x / x + ∫ t in (2 : ℝ)..x, NTKB.logIntegral t / t ^ 2 =
      Real.log (Real.log x) - Real.log (Real.log 2) := by
  have hd : ∀ t ∈ Set.uIcc (2 : ℝ) x, HasDerivAt
      (fun t : ℝ ↦ NTKB.logIntegral t / t - Real.log (Real.log t))
      (-(NTKB.logIntegral t / t ^ 2)) t := by
    intro t ht
    rw [Set.uIcc_of_le hx] at ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have hl : Real.log t ≠ 0 := (Real.log_pos (by linarith [ht.1])).ne'
    have h1 := (hasDerivAt_logIntegral (by linarith [ht.1] : 1 < t)).div (hasDerivAt_id t) ht0
    have h2 := (Real.hasDerivAt_log ht0).log hl
    have h3 : HasDerivAt (fun t : ℝ ↦ NTKB.logIntegral t / t - Real.log (Real.log t))
        ((1 / Real.log t * t - NTKB.logIntegral t * 1) / t ^ 2 - t⁻¹ / Real.log t) t :=
      h1.sub h2
    convert h3 using 1
    field_simp
    ring
  have hi : IntervalIntegrable (fun t : ℝ ↦ -(NTKB.logIntegral t / t ^ 2)) volume 2 x :=
    (intervalIntegrable_logIntegral_div hx).neg
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi
  rw [intervalIntegral.integral_neg] at this
  have h2 : NTKB.logIntegral 2 = 0 := by simp [NTKB.logIntegral]
  simp only [h2] at this
  linarith

lemma primeCountingAP_le (t : ℝ) (q : ℕ) (a : ℤ) : (primeCountingAP t q a : ℝ) ≤ max t 0 := by
  unfold primeCountingAP
  have h1 : ((Finset.Icc 1 ⌊t⌋₊).filter (fun p : ℕ ↦ p.Prime ∧ (p : ℤ) ≡ a [ZMOD q])).card ≤
      ⌊t⌋₊ := by
    refine (Finset.card_filter_le _ _).trans ?_
    simp
  have h2 : (⌊t⌋₊ : ℝ) ≤ max t 0 := by
    rcases le_total 0 t with h | h
    · exact (Nat.floor_le h).trans (le_max_left _ _)
    · simp [Nat.floor_of_nonpos h]
  exact (Nat.cast_le.mpr h1).trans h2

lemma logIntegral_bounds {t : ℝ} (ht : 2 ≤ t) : 0 ≤ NTKB.logIntegral t ∧
    NTKB.logIntegral t ≤ 2 * t := by
  have hL2 : 2 / 3 < Real.log 2 := log_two_gt_two_thirds
  constructor
  · refine intervalIntegral.integral_nonneg ht fun u hu ↦ ?_
    have : 0 < Real.log u := Real.log_pos (by linarith [hu.1])
    positivity
  · have hint : IntervalIntegrable (fun s : ℝ ↦ 1 / Real.log s) volume 2 t :=
      (NTKB.continuousOn_one_div_log (by norm_num) ht).intervalIntegrable
    have := intervalIntegral.integral_mono_on ht hint
      (intervalIntegrable_const (c := 1 / Real.log 2)) (fun u hu ↦ by
        have : 0 < Real.log u := Real.log_pos (by linarith [hu.1])
        exact one_div_le_one_div_of_le (by linarith) (Real.log_le_log two_pos hu.1))
    rw [intervalIntegral.integral_const] at this
    unfold NTKB.logIntegral
    refine this.trans ?_
    have h1 : 1 / Real.log 2 ≤ 3 / 2 := by
      rw [div_le_iff₀ (by linarith)]; linarith
    simp only [smul_eq_mul]
    nlinarith

/-- The remainder `R(t) = π(t; q, a) - li t / φ(q)`. -/
noncomputable def RAP (q : ℕ) (a : ℤ) (t : ℝ) : ℝ :=
  (primeCountingAP t q a : ℝ) - NTKB.logIntegral t / q.totient

lemma RAP_bound (q : ℕ) (hq : 0 < q) (a : ℤ) (ha : IsCoprime a q) :
    ∃ K : ℝ, 0 < K ∧ ∀ t : ℝ, 2 ≤ t → |RAP q a t| ≤ K * t / Real.log t ^ 2 := by
  obtain ⟨c, hc, C, hC, hSW⟩ := siegel_walfisz_primeCounting 1 one_pos
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  refine ⟨max (3 * (q : ℝ) ^ 2) (C * 24 / c ^ 4), lt_max_of_lt_left (by positivity),
    fun t ht ↦ ?_⟩
  have ht0 : 0 < t := by linarith
  have hlt : 0 < Real.log t := Real.log_pos (by linarith)
  have hl2 : 0 < Real.log t ^ 2 := by positivity
  have hφ : (1 : ℝ) ≤ q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
  unfold RAP
  rw [le_div_iff₀ hl2]
  by_cases hcase : (q : ℝ) ≤ Real.log t
  · have hS := hSW t ht q hq (by rwa [Real.rpow_one]) a ha
    set u := √(Real.log t) with hu
    have hu0 : 0 < u := Real.sqrt_pos.mpr hlt
    have hu2 : u ^ 2 = Real.log t := Real.sq_sqrt hlt.le
    have hexp : Real.exp (-c * u) * Real.log t ^ 2 ≤ 24 / c ^ 4 := by
      have h1 := Real.pow_div_factorial_le_exp (c * u) (by positivity) 4
      have h2 : Real.exp (-c * u) * Real.exp (c * u) = 1 := by
        rw [← Real.exp_add]; simp
      have h3 : Real.log t ^ 2 = u ^ 4 := by rw [← hu2]; ring
      rw [h3, le_div_iff₀ (by positivity)]
      have h4 : (c * u) ^ 4 ≤ 24 * Real.exp (c * u) := by
        have : ((4 : ℕ).factorial : ℝ) = 24 := by norm_num [Nat.factorial]
        rw [this, div_le_iff₀ (by norm_num)] at h1
        linarith
      have h5 : 0 ≤ Real.exp (-c * u) := (Real.exp_pos _).le
      calc Real.exp (-c * u) * u ^ 4 * c ^ 4 = Real.exp (-c * u) * (c * u) ^ 4 := by ring
        _ ≤ Real.exp (-c * u) * (24 * Real.exp (c * u)) := by gcongr
        _ = 24 * (Real.exp (-c * u) * Real.exp (c * u)) := by ring
        _ = 24 := by rw [h2]; ring
    calc |(primeCountingAP t q a : ℝ) - NTKB.logIntegral t / q.totient| * Real.log t ^ 2
        ≤ C * t * Real.exp (-c * u) * Real.log t ^ 2 := by gcongr
      _ = C * t * (Real.exp (-c * u) * Real.log t ^ 2) := by ring
      _ ≤ C * t * (24 / c ^ 4) := by gcongr
      _ = t * (C * 24 / c ^ 4) := by ring
      _ ≤ max (3 * (q : ℝ) ^ 2) (C * 24 / c ^ 4) * t := by
          rw [mul_comm t]; gcongr; exact le_max_right _ _
  · push Not at hcase
    have hπ := primeCountingAP_le t q a
    rw [max_eq_left ht0.le] at hπ
    have hπ0 : (0 : ℝ) ≤ primeCountingAP t q a := Nat.cast_nonneg _
    obtain ⟨hli0, hli2⟩ := logIntegral_bounds ht
    have hφ0 : (0 : ℝ) < q.totient := by linarith
    have hd0 : 0 ≤ NTKB.logIntegral t / q.totient := by positivity
    have hd1 : NTKB.logIntegral t / q.totient ≤ 2 * t :=
      (div_le_self hli0 hφ).trans hli2
    have h3 : |(primeCountingAP t q a : ℝ) - NTKB.logIntegral t / q.totient| ≤ 3 * t := by
      rw [abs_le]; constructor <;> linarith
    have hlq : Real.log t ^ 2 ≤ (q : ℝ) ^ 2 := by gcongr
    calc |(primeCountingAP t q a : ℝ) - NTKB.logIntegral t / q.totient| * Real.log t ^ 2
        ≤ 3 * t * (q : ℝ) ^ 2 := by gcongr
      _ = (3 * (q : ℝ) ^ 2) * t := by ring
      _ ≤ max (3 * (q : ℝ) ^ 2) (C * 24 / c ^ 4) * t := by
          gcongr; exact le_max_left _ _

lemma intervalIntegrable_RAP {x : ℝ} (q : ℕ) (a : ℤ) (hx : 2 ≤ x) :
    IntervalIntegrable (fun t : ℝ ↦ RAP q a t / t ^ 2) volume 2 x := by
  have h := (intervalIntegrable_primeCountingAP_div q a hx).sub
    ((intervalIntegrable_logIntegral_div hx).const_mul (1 / (q.totient : ℝ)))
  have e : (fun t : ℝ ↦ RAP q a t / t ^ 2) = fun t : ℝ ↦
      (primeCountingAP t q a : ℝ) / t ^ 2 - 1 / (q.totient : ℝ) * (NTKB.logIntegral t / t ^ 2) := by
    funext t
    simp only [RAP]
    ring
  rw [e]
  exact h

lemma sum_formula {x : ℝ} (q : ℕ) (a : ℤ) (hx : 2 ≤ x) :
    sumInvPrimeAP x q a - Real.log (Real.log x) / q.totient =
      RAP q a x / x + (∫ t in (2 : ℝ)..x, RAP q a t / t ^ 2) -
        Real.log (Real.log 2) / q.totient := by
  have hI : ∫ t in (2 : ℝ)..x, RAP q a t / t ^ 2 =
      (∫ t in (2 : ℝ)..x, (primeCountingAP t q a : ℝ) / t ^ 2) -
        1 / (q.totient : ℝ) * ∫ t in (2 : ℝ)..x, NTKB.logIntegral t / t ^ 2 := by
    rw [← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_sub (intervalIntegrable_primeCountingAP_div q a hx)
        ((intervalIntegrable_logIntegral_div hx).const_mul _)]
    refine intervalIntegral.integral_congr fun t _ ↦ ?_
    simp only [RAP]
    ring
  have hli := logIntegral_div_add_integral hx
  rw [sumInvPrimeAP_eq q a hx, hI]
  unfold RAP
  linear_combination (1 / (q.totient : ℝ)) * hli

lemma RAP_div_le {q : ℕ} {a : ℤ} {K : ℝ} (hK0 : 0 < K)
    (hK : ∀ t : ℝ, 2 ≤ t → |RAP q a t| ≤ K * t / Real.log t ^ 2) {t : ℝ} (ht : 3 ≤ t) :
    |RAP q a t / t| ≤ K / Real.log t := by
  have ht0 : 0 < t := by linarith
  have hl1 : 1 ≤ Real.log t := by
    have h3 : Real.log 3 ≤ Real.log t := Real.log_le_log (by norm_num) ht
    have : 1 < Real.log 3 := by
      rw [Real.lt_log_iff_exp_lt (by norm_num)]
      have := Real.exp_one_lt_d9
      linarith
    linarith
  have hlt : 0 < Real.log t := by linarith
  rw [abs_div, abs_of_pos ht0]
  calc |RAP q a t| / t ≤ (K * t / Real.log t ^ 2) / t := by
        gcongr; exact hK t (by linarith)
    _ = K / Real.log t ^ 2 := by field_simp
    _ ≤ K / Real.log t := by
        rw [div_le_div_iff₀ (by positivity) hlt]
        have : Real.log t ≤ Real.log t ^ 2 := by nlinarith
        exact mul_le_mul_of_nonneg_left this hK0.le

lemma integral_RAP_le {q : ℕ} {a : ℤ} {K : ℝ} (hK0 : 0 < K)
    (hK : ∀ t : ℝ, 2 ≤ t → |RAP q a t| ≤ K * t / Real.log t ^ 2) {x y : ℝ} (hx : 3 ≤ x)
    (hxy : x ≤ y) :
    |∫ t in x..y, RAP q a t / t ^ 2| ≤ K / Real.log x - K / Real.log y := by
  have hd : ∀ t ∈ Set.uIcc x y, HasDerivAt (fun t : ℝ ↦ -(K / Real.log t))
      (K / (t * Real.log t ^ 2)) t := by
    intro t ht
    rw [Set.uIcc_of_le hxy] at ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have hl : Real.log t ≠ 0 := (Real.log_pos (by linarith [ht.1])).ne'
    have := ((hasDerivAt_const t K).div (Real.hasDerivAt_log ht0) hl).neg
    convert this using 1
    field_simp
    ring
  have hgint : IntervalIntegrable (fun t : ℝ ↦ K / (t * Real.log t ^ 2)) volume x y := by
    refine ContinuousOn.intervalIntegrable fun t ht ↦ ?_
    rw [Set.uIcc_of_le hxy] at ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have hl : Real.log t ≠ 0 := (Real.log_pos (by linarith [ht.1])).ne'
    refine ContinuousAt.continuousWithinAt ?_
    exact continuousAt_const.div (continuousAt_id.mul
      ((Real.continuousAt_log ht0).pow 2)) (mul_ne_zero ht0 (pow_ne_zero 2 hl))
  have hF := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hgint
  have hpt : ∀ t ∈ Set.Ioc x y, ‖RAP q a t / t ^ 2‖ ≤ K / (t * Real.log t ^ 2) := by
    intro t ht
    have ht3 : 3 ≤ t := by linarith [ht.1]
    have ht0 : 0 < t := by linarith
    have hl : 0 < Real.log t := Real.log_pos (by linarith)
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : (0 : ℝ) < t ^ 2)]
    calc |RAP q a t| / t ^ 2 ≤ (K * t / Real.log t ^ 2) / t ^ 2 := by
          gcongr; exact hK t (by linarith)
      _ = K / (t * Real.log t ^ 2) := by field_simp
  have hI := intervalIntegral.norm_integral_le_of_norm_le hxy
    (Filter.Eventually.of_forall hpt) hgint
  rw [Real.norm_eq_abs] at hI
  rw [hF] at hI
  linarith

lemma S_diff_bound {q : ℕ} {a : ℤ} {K : ℝ} (hK0 : 0 < K)
    (hK : ∀ t : ℝ, 2 ≤ t → |RAP q a t| ≤ K * t / Real.log t ^ 2) {x y : ℝ} (hx : 3 ≤ x)
    (hxy : x ≤ y) :
    |(sumInvPrimeAP y q a - Real.log (Real.log y) / q.totient) -
      (sumInvPrimeAP x q a - Real.log (Real.log x) / q.totient)| ≤ 2 * K / Real.log x := by
  have hx2 : 2 ≤ x := by linarith
  have hy2 : 2 ≤ y := by linarith
  rw [sum_formula q a hx2, sum_formula q a hy2]
  have hint := intervalIntegral.integral_interval_sub_left
    (intervalIntegrable_RAP q a hy2) (intervalIntegrable_RAP q a hx2)
  have b1 := RAP_div_le hK0 hK (by linarith : 3 ≤ y)
  have b2 := RAP_div_le hK0 hK hx
  have b3 := integral_RAP_le hK0 hK hx hxy
  have e : RAP q a y / y + (∫ t in (2 : ℝ)..y, RAP q a t / t ^ 2) -
        Real.log (Real.log 2) / q.totient -
      (RAP q a x / x + (∫ t in (2 : ℝ)..x, RAP q a t / t ^ 2) -
        Real.log (Real.log 2) / q.totient) =
      RAP q a y / y - RAP q a x / x + ∫ t in x..y, RAP q a t / t ^ 2 := by
    linarith
  rw [e]
  have h1 := abs_add_le (RAP q a y / y - RAP q a x / x) (∫ t in x..y, RAP q a t / t ^ 2)
  have h2 := abs_sub (RAP q a y / y) (RAP q a x / x)
  have : 2 * K / Real.log x = K / Real.log x + K / Real.log x := by ring
  linarith

/-- **Davenport, Ch. 7, p. 67 (row 7-16): Mertens' theorem for progressions.** For `q ≥ 1` and `a`
prime to `q` there are constants `A = A(q, a)` and `B` with
`|∑_{p ≤ x, p ≡ a (q)} 1/p - (log log x)/φ(q) - A| ≤ B/log x` for every `x ≥ 3`. -/
@[kb "davenport1980" "Ch 7, p. 67"]
theorem sumInvPrimeAP_sub_le (q : ℕ) (hq : 0 < q) (a : ℤ) (ha : IsCoprime a q) :
    ∃ A B : ℝ, ∀ x : ℝ, 3 ≤ x →
      |sumInvPrimeAP x q a - Real.log (Real.log x) / q.totient - A| ≤ B / Real.log x := by
  obtain ⟨K, hK0, hK⟩ := RAP_bound q hq a ha
  set S : ℝ → ℝ := fun x ↦ sumInvPrimeAP x q a - Real.log (Real.log x) / q.totient with hS
  have hdiff : ∀ x y : ℝ, 3 ≤ x → x ≤ y → |S y - S x| ≤ 2 * K / Real.log x :=
    fun x y hx hxy ↦ S_diff_bound hK0 hK hx hxy
  have hcau : CauchySeq (fun n : ℕ ↦ S ((n : ℝ) + 3)) := by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    refine ⟨⌈Real.exp (2 * K / ε)⌉₊, fun n hn ↦ ?_⟩
    rw [Real.dist_eq]
    have hN : Real.exp (2 * K / ε) ≤ (⌈Real.exp (2 * K / ε)⌉₊ : ℝ) := Nat.le_ceil _
    have hn' : (⌈Real.exp (2 * K / ε)⌉₊ : ℝ) ≤ n := by exact_mod_cast hn
    have h3 : (3 : ℝ) ≤ (⌈Real.exp (2 * K / ε)⌉₊ : ℝ) + 3 := by
      have := Nat.cast_nonneg (α := ℝ) ⌈Real.exp (2 * K / ε)⌉₊
      linarith
    have hb := hdiff _ _ h3 (by linarith : (⌈Real.exp (2 * K / ε)⌉₊ : ℝ) + 3 ≤ (n : ℝ) + 3)
    refine hb.trans_lt ?_
    have hlog : 2 * K / ε < Real.log ((⌈Real.exp (2 * K / ε)⌉₊ : ℝ) + 3) := by
      rw [Real.lt_log_iff_exp_lt (by linarith)]
      linarith
    have hpos : 0 < 2 * K / ε := by positivity
    rw [div_lt_iff₀ (by linarith)]
    rw [div_lt_iff₀ hε] at hlog
    linarith
  obtain ⟨A, hA⟩ := cauchySeq_tendsto_of_complete hcau
  refine ⟨A, 2 * K, fun x hx ↦ ?_⟩
  have hlim : Filter.Tendsto (fun n : ℕ ↦ |S x - S ((n : ℝ) + 3)|) Filter.atTop
      (nhds |S x - A|) := (tendsto_const_nhds.sub hA).abs
  have := le_of_tendsto hlim (Filter.eventually_atTop.2 ⟨⌈x⌉₊, fun n hn ↦ by
    have hxn : x ≤ (n : ℝ) + 3 := by
      have : (⌈x⌉₊ : ℝ) ≤ n := by exact_mod_cast hn
      have := Nat.le_ceil x
      linarith
    rw [abs_sub_comm]
    exact hdiff x _ hx hxn⟩)
  simpa [hS] using this

end NTKB.Davenport
