/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Davenport.Siegel.PrimeCountingAP
import NTKB.Analytic.Davenport.Zeros.PNTAPExceptional

/-!
# `π(x; q, a)` with the exceptional zero

**Davenport, Ch. 20, p. 121, and Ch. 22, p. 133 (row 20-15).**
The analogue of 20-5 for `π(x; q, a)`: the main term `li x/φ(q)`, the exceptional term
`χ₁(a) Li_{β₁}(x)/φ(q)` with `Li_β(x) = ∫_2^x t^{β-1}/log t dt` (`= li(x^β) - li(2^β)` by `u = t^β`),
and the error `O(x exp(-c √log x))`, by partial summation
`π(x;q,a) = θ(x;q,a)/log x + ∫_2^x θ(t;q,a)/(t log² t) dt` from 20-5 for real `x`
(`Davenport.psiAP_exceptional_real`), as in `siegel_walfisz_primeCounting`.
-/

open Finset MeasureTheory
open scoped Real

namespace NTKB.Davenport

/-- `Li_β(x) = ∫_2^x t^{β-1}/log t dt`; `Li_1 = li`. -/
noncomputable def logIntegralPow (β x : ℝ) : ℝ := ∫ t in (2 : ℝ)..x, t ^ (β - 1) / Real.log t

lemma intervalIntegrable_rpow_div {β x : ℝ} (hx : 2 ≤ x) :
    IntervalIntegrable (fun t : ℝ ↦ t ^ β / β / (t * Real.log t ^ 2)) volume 2 x := by
  refine ContinuousOn.intervalIntegrable fun t ht ↦ ?_
  rw [Set.uIcc_of_le hx] at ht
  have ht0 : t ≠ 0 := by linarith [ht.1]
  have hl : Real.log t ≠ 0 := (Real.log_pos (by linarith [ht.1])).ne'
  have : t * Real.log t ^ 2 ≠ 0 := mul_ne_zero ht0 (pow_ne_zero 2 hl)
  refine ContinuousAt.continuousWithinAt ?_
  exact (((Real.continuousAt_rpow_const _ _ (Or.inl ht0)).div_const β)).div
    (continuousAt_id.mul ((Real.continuousAt_log ht0).pow 2)) this

/-- Integration by parts: `Li_β(x) = x^β/(β log x) - 2^β/(β log 2) + ∫_2^x t^β/β/(t log² t) dt`. -/
lemma logIntegralPow_eq {β x : ℝ} (hβ : β ≠ 0) (hx : 2 ≤ x) :
    logIntegralPow β x = x ^ β / (β * Real.log x) - 2 ^ β / (β * Real.log 2) +
      ∫ t in (2 : ℝ)..x, t ^ β / β / (t * Real.log t ^ 2) := by
  have hd : ∀ t ∈ Set.uIcc (2 : ℝ) x, HasDerivAt (fun t : ℝ ↦ t ^ β / (β * Real.log t))
      (t ^ (β - 1) / Real.log t - t ^ β / β / (t * Real.log t ^ 2)) t := by
    intro t ht
    rw [Set.uIcc_of_le hx] at ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have hl : Real.log t ≠ 0 := (Real.log_pos (by linarith [ht.1])).ne'
    have h1 := Real.hasDerivAt_rpow_const (x := t) (p := β) (Or.inl ht0)
    have h2 := (Real.hasDerivAt_log ht0).const_mul β
    have := h1.div h2 (mul_ne_zero hβ hl)
    convert this using 1
    rw [Real.rpow_sub_one ht0]
    field_simp
  have hi1 : IntervalIntegrable (fun t : ℝ ↦ t ^ (β - 1) / Real.log t) volume 2 x := by
    refine ContinuousOn.intervalIntegrable fun t ht ↦ ?_
    rw [Set.uIcc_of_le hx] at ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have hl : Real.log t ≠ 0 := (Real.log_pos (by linarith [ht.1])).ne'
    exact ((Real.continuousAt_rpow_const _ _ (Or.inl ht0)).div (Real.continuousAt_log ht0)
      hl).continuousWithinAt
  have hi2 := intervalIntegrable_rpow_div (β := β) hx
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hi1.sub hi2)
  rw [intervalIntegral.integral_sub hi1 hi2] at hFTC
  unfold logIntegralPow
  linarith

/-- The two definitions of `ψ(x; q, a)` agree. -/
lemma psiAP_eq_psiAP (x : ℝ) {q : ℕ} (a : ℤ) :
    psiAP x q a = NTKB.psiAP (a : ZMod q) x := by
  unfold psiAP NTKB.psiAP
  rw [Finset.sum_filter]
  rw [sum_Icc_one_eq _ (by simp)]
  refine Finset.sum_congr rfl fun n _ ↦ ?_
  have : ((n : ℤ) ≡ a [ZMOD q]) ↔ (n : ZMod q) = (a : ZMod q) := by
    rw [← ZMod.intCast_eq_intCast_iff, Int.cast_natCast]
  by_cases h : (n : ZMod q) = (a : ZMod q)
  · simp [ArithmeticFunction.vonMangoldt.residueClass, h, this.mpr h]
  · have h' : ¬ ((n : ℤ) ≡ a [ZMOD q]) := fun h2 ↦ h (this.mp h2)
    simp [ArithmeticFunction.vonMangoldt.residueClass, h, h']

/-- `θ(t; q, a) - t/φ(q) + ε t^β/(β φ(q))`. -/
noncomputable def excErr (q : ℕ) (a : ℤ) (ε β t : ℝ) : ℝ :=
  thetaAP t q a - t / q.totient + ε * (t ^ β / (β * q.totient))

lemma excErr_pt {q : ℕ} [NeZero q] {C : ℝ} (a : ℤ) {c' A' : ℝ} (hc : 0 < c')
    (hA' : 0 < A') (ε β : ℝ) (hε : |ε| ≤ 1) (hβ1 : 1 / 2 < β) (hβ2 : β < 1)
    (H : ∀ t : ℝ, 3 ≤ t → Real.log q ≤ 2 * C * √(Real.log t) →
      |psiAP t q a - t / q.totient + ε * (t ^ β / (β * q.totient))| ≤
        A' * t * Real.exp (-(c' * √(Real.log t))))
    {x : ℝ} (hx : 3 ≤ x) (hqx : Real.log q ≤ C * √(Real.log x)) (hC : 0 < C)
    {t : ℝ} (ht : 2 ≤ t) (htx : t ≤ x) :
    |excErr q a ε β t| ≤ (A' + 48) * t * (Real.exp (-(c' * √(Real.log x / 2))) + √x / t) +
      2 * √t * Real.log t := by
  set A := Real.exp (-(c' * √(Real.log x / 2))) with hA
  have hA0 : 0 < A := Real.exp_pos _
  have ht0 : 0 < t := by linarith
  have hx0 : 0 < x := by linarith
  have hφ : (1 : ℝ) ≤ q.totient := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
  have hMeq : (A' + 48) * t * (A + √x / t) = (A' + 48) * (t * A) + (A' + 48) * √x := by
    field_simp
  rw [hMeq]
  have hs1 : 1 ≤ √x := Real.one_le_sqrt.mpr (by linarith)
  have hlt : 0 < Real.log t := Real.log_pos (by linarith)
  have hψθ : 0 ≤ √t * Real.log t := by positivity
  have hE0 : 0 ≤ t * A := by positivity
  by_cases hcase : √x ≤ t ∧ 8 ≤ t
  · obtain ⟨h1, h2⟩ := hcase
    have hl : Real.log x / 2 ≤ Real.log t := by
      have h1' : Real.log (√x) ≤ Real.log t := Real.log_le_log (Real.sqrt_pos.mpr hx0) h1
      rwa [Real.log_sqrt hx0.le] at h1'
    have hlx0 : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
    have hqt : Real.log q ≤ 2 * C * √(Real.log t) := by
      have : √(Real.log x) ≤ 2 * √(Real.log t) := by
        rw [Real.sqrt_le_iff]
        refine ⟨by positivity, ?_⟩
        rw [mul_pow, Real.sq_sqrt hlt.le]; nlinarith [hl]
      calc Real.log q ≤ C * √(Real.log x) := hqx
        _ ≤ C * (2 * √(Real.log t)) := by gcongr
        _ = 2 * C * √(Real.log t) := by ring
    have hS := H t (by linarith) hqt
    have hexp : Real.exp (-(c' * √(Real.log t))) ≤ A := by
      apply Real.exp_le_exp.mpr
      have e1 : c' * √(Real.log x / 2) ≤ c' * √(Real.log t) :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hl) hc.le
      linarith
    have hS' : |psiAP t q a - t / q.totient + ε * (t ^ β / (β * q.totient))| ≤ A' * (t * A) := by
      refine hS.trans ?_
      calc A' * t * Real.exp (-(c' * √(Real.log t))) ≤ A' * t * A := by gcongr
        _ = A' * (t * A) := by ring
    have hd := psiAP_sub_thetaAP t q a
    have hψθ' : Chebyshev.psi t - Chebyshev.theta t ≤ 2 * √t * Real.log t := by
      have := Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log (x := t) (by linarith)
      exact (le_abs_self _).trans this
    have hmain : |excErr q a ε β t| ≤ A' * (t * A) + 2 * √t * Real.log t := by
      have := abs_le.mp hS'
      unfold excErr
      rw [abs_le]
      constructor <;> nlinarith [hd.1, hd.2]
    have hCM : A' * (t * A) ≤ (A' + 48) * (t * A) := by nlinarith
    have : 0 ≤ (A' + 48) * √x := by positivity
    linarith
  · have hθ3 : thetaAP t q a ≤ 3 * t := by
      refine (thetaAP_le_theta t q a).trans ?_
      refine (Chebyshev.theta_le_log4_mul_x ht0.le).trans ?_
      have : Real.log 4 ≤ 3 := by
        have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num); linarith
      nlinarith
    have hth0 := thetaAP_nonneg t q a
    have hφt : 0 ≤ t / q.totient := by positivity
    have hφt' : t / q.totient ≤ t := div_le_self ht0.le hφ
    have hrp : t ^ β ≤ t := by
      calc t ^ β ≤ t ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith) hβ2.le
        _ = t := Real.rpow_one t
    have hrp0 : 0 ≤ t ^ β := Real.rpow_nonneg ht0.le _
    have hβ0 : 0 < β := by linarith
    have hT : t ^ β / (β * q.totient) ≤ 2 * t := by
      rw [div_le_iff₀ (by positivity)]
      have hβφ : 1 / 2 ≤ β * q.totient := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hβφ ht0.le]
    have hT0 : 0 ≤ t ^ β / (β * q.totient) := by positivity
    have hεT : |ε * (t ^ β / (β * q.totient))| ≤ 2 * t := by
      rw [abs_mul, abs_of_nonneg hT0]
      nlinarith [abs_nonneg ε]
    have h3 : |excErr q a ε β t| ≤ 6 * t := by
      unfold excErr
      have := abs_le.mp hεT
      rw [abs_le]; constructor <;> linarith
    have h4 : 6 * t ≤ 48 * √x := by
      rw [not_and_or] at hcase
      rcases hcase with h | h
      · push Not at h; linarith
      · push Not at h; linarith
    have h5 : 48 * √x ≤ (A' + 48) * √x := by nlinarith [Real.sqrt_nonneg x]
    have : 0 ≤ (A' + 48) * (t * A) := by positivity
    have : 0 ≤ 2 * √t * Real.log t := by positivity
    linarith

set_option maxHeartbeats 1000000 in
/-- The partial summation step for `π(x; q, a)` with a real exceptional sign `ε` and `1/2 < β < 1`
(`ε = 0` if there is no exceptional zero). -/
lemma excCore {q : ℕ} [NeZero q] {C : ℝ} (a : ℤ) {c' A' : ℝ} (hc : 0 < c') (hc1 : c' ≤ 1 / 2)
    (hA' : 0 < A') (ε β : ℝ) (hε : |ε| ≤ 1) (hβ1 : 1 / 2 < β) (hβ2 : β < 1)
    (H : ∀ t : ℝ, 3 ≤ t → Real.log q ≤ 2 * C * √(Real.log t) →
      |psiAP t q a - t / q.totient + ε * (t ^ β / (β * q.totient))| ≤
        A' * t * Real.exp (-(c' * √(Real.log t))))
    (hC : 0 < C) {x : ℝ} (hx : 3 ≤ x) (hqx : Real.log q ≤ C * √(Real.log x)) :
    |(primeCountingAP x q a : ℝ) - NTKB.logIntegral x / q.totient +
        ε * logIntegralPow β x / q.totient| ≤
      (40 * (A' + 48) + 100) * x * Real.exp (-(c' / 2 * √(Real.log x))) := by
  have hx2 : 2 ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  have hβ0 : 0 < β := by linarith
  set M := A' + 48 with hMdef
  have hM : 0 < M := by positivity
  set L2 := Real.log 2 with hL2def
  have hL2 : 2 / 3 < L2 := log_two_gt_two_thirds
  have hL2' : L2 < 1 := by have := Real.log_two_lt_d9; linarith
  have hlx : L2 ≤ Real.log x := Real.log_le_log two_pos hx2
  have hlx0 : 0 < Real.log x := by linarith
  set E1 := Real.exp (-(c' / 2 * √(Real.log x))) with hE1
  have hE10 : 0 < E1 := Real.exp_pos _
  set A := Real.exp (-(c' * √(Real.log x / 2))) with hAdef
  have hA0 : 0 < A := Real.exp_pos _
  have hφ : (1 : ℝ) ≤ q.totient := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
  have hφ0 : (0 : ℝ) < q.totient := by linarith
  -- the identity
  have hπ := primeCountingAP_eq_thetaAP q a hx2
  have hli := NTKB.logIntegral_eq hx2
  have hLi := logIntegralPow_eq (β := β) hβ0.ne' hx2
  have hI1 := intervalIntegrable_thetaAP_div q a hx2
  have hI2 : IntervalIntegrable (fun t : ℝ ↦ 1 / Real.log t ^ 2) volume 2 x :=
    Chebyshev.intervalIntegrable_one_div_log_sq (by norm_num) (by linarith)
  have hI3 := intervalIntegrable_rpow_div (β := β) hx2
  have hdiff : (∫ t in (2 : ℝ)..x, thetaAP t q a / (t * Real.log t ^ 2)) -
      (1 / (q.totient : ℝ)) * (∫ t in (2 : ℝ)..x, 1 / Real.log t ^ 2) +
      (ε / q.totient) * (∫ t in (2 : ℝ)..x, t ^ β / β / (t * Real.log t ^ 2)) =
      ∫ t in (2 : ℝ)..x, excErr q a ε β t / (t * Real.log t ^ 2) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_sub hI1 (hI2.const_mul _),
      ← intervalIntegral.integral_add (hI1.sub (hI2.const_mul _)) (hI3.const_mul _)]
    refine intervalIntegral.integral_congr fun t ht ↦ ?_
    rw [Set.uIcc_of_le hx2] at ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have hl : Real.log t ≠ 0 := (Real.log_pos (by linarith [ht.1])).ne'
    simp only [excErr]
    field_simp
  have hid : (primeCountingAP x q a : ℝ) - NTKB.logIntegral x / q.totient +
        ε * logIntegralPow β x / q.totient =
      excErr q a ε β x / Real.log x +
        (2 / (q.totient * L2) - ε * (2 ^ β / (β * L2)) / q.totient) +
        ∫ t in (2 : ℝ)..x, excErr q a ε β t / (t * Real.log t ^ 2) := by
    rw [hπ, hli, hLi, ← hdiff]
    have : Real.log x ≠ 0 := hlx0.ne'
    have : L2 ≠ 0 := by linarith
    simp only [excErr]
    field_simp
    ring
  rw [hid]
  -- the bounds
  have haE : A ≤ E1 := by
    apply Real.exp_le_exp.mpr
    have h1 : √(Real.log x) / 2 ≤ √(Real.log x / 2) := by
      rw [Real.le_sqrt (by positivity) (by positivity), div_pow, Real.sq_sqrt hlx0.le]
      linarith
    have h2 := mul_le_mul_of_nonneg_left h1 hc.le
    linarith
  have hsl := NTKB.sqrt_mul_log_le (c := c' / 2) (by positivity) (by linarith) (x := x)
    (by linarith)
  rw [← hE1] at hsl
  have h1E := NTKB.one_le_mul_exp_neg_sqrt_log (c := c' / 2) (by positivity) (by linarith) hx2
  rw [← hE1] at h1E
  have hxE : 0 ≤ x * E1 := by positivity
  have hi1 : 1 / L2 ≤ 3 / 2 := by rw [div_le_iff₀ (by linarith)]; linarith
  have hsx : √x ≤ √x * Real.log x / L2 := by
    rw [le_div_iff₀ (by linarith)]
    exact mul_le_mul_of_nonneg_left hlx (Real.sqrt_nonneg x)
  have hE := fun t (ht : 2 ≤ t) (htx : t ≤ x) ↦
    excErr_pt (C := C) a hc hA' ε β hε hβ1 hβ2 H hx hqx hC ht htx
  -- `|excErr x|`
  have hEx := hE x hx2 le_rfl
  have hMx : M * x * (A + √x / x) = M * (x * A) + M * √x := by field_simp
  rw [hMx] at hEx
  have hsq : M * √x ≤ 9 * M * (x * E1) := by
    calc M * √x ≤ M * (√x * Real.log x / L2) := by gcongr
      _ ≤ M * (6 * (x * E1) / L2) := by gcongr
      _ = M * 6 * (1 / L2) * (x * E1) := by ring
      _ ≤ M * 6 * (3 / 2) * (x * E1) := by gcongr
      _ = 9 * M * (x * E1) := by ring
  have hxA : M * (x * A) ≤ M * (x * E1) := by gcongr
  have hEx' : |excErr q a ε β x| ≤ (10 * M + 12) * (x * E1) := by
    refine hEx.trans ?_
    linarith
  have b1 : |excErr q a ε β x / Real.log x| ≤
      (10 * M + 12) * (3 / 2) * (x * E1) := by
    rw [abs_div, abs_of_pos hlx0, div_le_iff₀ hlx0]
    have h0 : 0 ≤ (10 * M + 12) * (x * E1) := by positivity
    have h3 : 1 ≤ 3 / 2 * Real.log x := by linarith
    calc |excErr q a ε β x| ≤ (10 * M + 12) * (x * E1) := hEx'
      _ = (10 * M + 12) * (x * E1) * 1 := by ring
      _ ≤ (10 * M + 12) * (x * E1) * (3 / 2 * Real.log x) := by gcongr
      _ = (10 * M + 12) * (3 / 2) * (x * E1) * Real.log x := by ring
  -- the integral
  have b3 := norm_integral_le_of_bound (E := fun t ↦ excErr q a ε β t) hA0 hM
    (fun t ht htx ↦ hE t ht htx) hx2
  have b3' : |∫ t in (2 : ℝ)..x, excErr q a ε β t / (t * Real.log t ^ 2)| ≤
      (M * (9 / 4) * 7 + 24 * (9 / 4)) * (x * E1) := by
    refine b3.trans ?_
    have hB0 : 0 ≤ M / L2 ^ 2 := by positivity
    have h1 : A * x + √x * Real.log x ≤ 7 * (x * E1) := by
      have : A * x ≤ E1 * x := by gcongr
      linarith
    have h2 : 4 / L2 * √x ≤ 4 / L2 * 6 / L2 * (x * E1) := by
      have : 0 ≤ 4 / L2 := by positivity
      calc 4 / L2 * √x ≤ 4 / L2 * (√x * Real.log x / L2) := by gcongr
        _ ≤ 4 / L2 * (6 * (x * E1) / L2) := by gcongr
        _ = 4 / L2 * 6 / L2 * (x * E1) := by ring
    have hi2 : 1 / L2 ^ 2 ≤ 9 / 4 := by
      have h := pow_le_pow_left₀ (by positivity) hi1 2
      rw [div_pow, one_pow] at h
      linarith
    have c2 : M / L2 ^ 2 * 7 + 4 / L2 * 6 / L2 ≤ M * (9 / 4) * 7 + 24 * (9 / 4) := by
      have e : 4 / L2 * 6 / L2 = 24 * (1 / L2 ^ 2) := by field_simp; ring
      rw [e, div_eq_mul_one_div M]
      gcongr
    calc M / L2 ^ 2 * (A * x + √x * Real.log x) + 4 / L2 * √x
        ≤ M / L2 ^ 2 * (7 * (x * E1)) + 4 / L2 * 6 / L2 * (x * E1) := by gcongr
      _ = (M / L2 ^ 2 * 7 + 4 / L2 * 6 / L2) * (x * E1) := by ring
      _ ≤ (M * (9 / 4) * 7 + 24 * (9 / 4)) * (x * E1) := by gcongr
  -- the constant
  have k1 : 2 / ((q.totient : ℝ) * L2) ≤ 3 := by
    have h1 : 2 / ((q.totient : ℝ) * L2) ≤ 2 / (1 * L2) := by
      apply div_le_div_of_nonneg_left (by norm_num) (by linarith)
      exact mul_le_mul_of_nonneg_right hφ (by linarith)
    have h2 : 2 / (1 * L2) ≤ 3 := by rw [div_le_iff₀ (by linarith)]; linarith
    linarith
  have k2 : |ε * (2 ^ β / (β * L2)) / q.totient| ≤ 6 := by
    have h2β : (2 : ℝ) ^ β ≤ 2 := by
      calc (2 : ℝ) ^ β ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hβ2.le
        _ = 2 := Real.rpow_one 2
    have hβL : 1 / 3 < β * L2 := by nlinarith
    have hY : (2 : ℝ) ^ β / (β * L2) ≤ 6 := by
      rw [div_le_iff₀ (by positivity)]; linarith
    have hY0 : 0 ≤ (2 : ℝ) ^ β / (β * L2) := by positivity
    rw [abs_div, abs_mul, abs_of_nonneg hY0, abs_of_pos hφ0, div_le_iff₀ hφ0]
    nlinarith [mul_le_mul_of_nonneg_right hε hY0]
  have c3 : |2 / ((q.totient : ℝ) * L2) - ε * (2 ^ β / (β * L2)) / q.totient| ≤
      9 * (x * E1) := by
    have : |2 / ((q.totient : ℝ) * L2)| ≤ 3 :=
      by rw [abs_of_pos (by positivity)]; exact k1
    have h := abs_sub (2 / ((q.totient : ℝ) * L2)) (ε * (2 ^ β / (β * L2)) / q.totient)
    linarith
  calc |excErr q a ε β x / Real.log x +
        (2 / (q.totient * L2) - ε * (2 ^ β / (β * L2)) / q.totient) +
        ∫ t in (2 : ℝ)..x, excErr q a ε β t / (t * Real.log t ^ 2)|
      ≤ |excErr q a ε β x / Real.log x| +
          |2 / ((q.totient : ℝ) * L2) - ε * (2 ^ β / (β * L2)) / q.totient| +
          |∫ t in (2 : ℝ)..x, excErr q a ε β t / (t * Real.log t ^ 2)| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ (10 * M + 12) * (3 / 2) * (x * E1) + 9 * (x * E1) +
          (M * (9 / 4) * 7 + 24 * (9 / 4)) * (x * E1) := add_le_add (add_le_add b1 c3) b3'
    _ ≤ (40 * M + 100) * (x * E1) := by
        have : (10 * M + 12) * (3 / 2) + 9 + (M * (9 / 4) * 7 + 24 * (9 / 4)) ≤ 40 * M + 100 := by
          linarith
        have h := mul_le_mul_of_nonneg_right this hxE
        linarith
    _ = (40 * M + 100) * x * E1 := by ring

/-- **Davenport, Ch. 20, p. 121 and Ch. 22, p. 133 (row 20-15)**: for every `C > 0` there are
`c, A > 0` such that for every `q`, every `a` prime to `q` and every real `x ≥ 3` with
`log q ≤ C √log x`:
* if no real nonprincipal character modulo `q` has an exceptional zero, then
  `|π(x; q, a) - li x/φ(q)| ≤ A x exp(-c √log x)`;
* if `χ₁` has the exceptional zero `β₁`, then
  `|π(x; q, a) - li x/φ(q) + χ₁(a) Li_{β₁}(x)/φ(q)| ≤ A x exp(-c √log x)`. -/
@[kb "davenport1980" "Ch 22, p. 133"]
theorem primeCountingAP_exceptional (C : ℝ) (hC : 0 < C) :
    ∃ c A : ℝ, 0 < c ∧ 0 < A ∧ ∀ {q : ℕ} [NeZero q] (a : ℤ), IsCoprime a q →
      ∀ x : ℝ, 3 ≤ x → Real.log q ≤ C * √(Real.log x) →
      ((∀ (χ : DirichletCharacter ℂ q) (β : ℝ), ¬ NTKB.IsExceptional χ β) →
        |(primeCountingAP x q a : ℝ) - NTKB.logIntegral x / q.totient| ≤
          A * x * Real.exp (-(c * √(Real.log x)))) ∧
      (∀ (χ₁ : DirichletCharacter ℂ q) (β₁ : ℝ), NTKB.IsExceptional χ₁ β₁ →
        ‖((primeCountingAP x q a : ℝ) : ℂ) - NTKB.logIntegral x / q.totient +
            χ₁ (a : ZMod q) * logIntegralPow β₁ x / q.totient‖ ≤
          A * x * Real.exp (-(c * √(Real.log x)))) := by
  obtain ⟨c0, A0, hc0, hA0, h⟩ := NTKB.Davenport.psiAP_exceptional_real (2 * C) (by positivity)
  set c' := min c0 (1 / 2) with hc'
  have hc'0 : 0 < c' := lt_min hc0 one_half_pos
  have hc'1 : c' ≤ 1 / 2 := min_le_right _ _
  have hc'c : c' ≤ c0 := min_le_left _ _
  refine ⟨c' / 2, 40 * (A0 + 48) + 100, by positivity, by positivity, ?_⟩
  intro q _ a ha x hx hqx
  have hu : IsUnit (a : ZMod q) := by
    obtain ⟨u, v, huv⟩ := ha
    have := congrArg (Int.cast : ℤ → ZMod q) huv
    push_cast at this
    rw [ZMod.natCast_self, mul_zero, add_zero] at this
    exact IsUnit.of_mul_eq_one (u : ZMod q) (by rw [mul_comm]; exact this)
  have hmono : ∀ t : ℝ, 0 ≤ t → A0 * t * Real.exp (-(c0 * √(Real.log t))) ≤
      A0 * t * Real.exp (-(c' * √(Real.log t))) := by
    intro t ht
    have : Real.exp (-(c0 * √(Real.log t))) ≤ Real.exp (-(c' * √(Real.log t))) :=
      Real.exp_le_exp.mpr (by nlinarith [Real.sqrt_nonneg (Real.log t)])
    have : 0 ≤ A0 * t := by positivity
    gcongr
  refine ⟨fun hno ↦ ?_, fun χ₁ β₁ h₁ ↦ ?_⟩
  · have := excCore (q := q) (C := C) a hc'0 hc'1 hA0 0 (3 / 4) (by simp) (by norm_num)
      (by norm_num) (fun t ht hq ↦ ?_) hC hx hqx
    · simpa using this
    · have e := (h hu t ht hq).1 hno
      rw [← psiAP_eq_psiAP] at e
      simp only [zero_mul, add_zero]
      exact e.trans (hmono t (by linarith))
  · have hκ : χ₁ (a : ZMod q) * χ₁ (a : ZMod q) = 1 := by
      have := congrArg (fun ψ : DirichletCharacter ℂ q ↦ ψ (a : ZMod q)) h₁.2.1
      simpa [sq, MulChar.one_apply hu] using this
    obtain ⟨ε, hε1, hεκ⟩ : ∃ ε : ℝ, |ε| ≤ 1 ∧ χ₁ (a : ZMod q) = (ε : ℂ) := by
      rcases mul_self_eq_one_iff.mp hκ with hk | hk
      · exact ⟨1, by simp, by simp [hk]⟩
      · exact ⟨-1, by simp, by simp [hk]⟩
    have := excCore (q := q) (C := C) a hc'0 hc'1 hA0 ε β₁ hε1 h₁.half_lt h₁.lt_one
      (fun t ht hq ↦ ?_) hC hx hqx
    · have e2 : ((primeCountingAP x q a : ℝ) : ℂ) - NTKB.logIntegral x / q.totient +
          χ₁ (a : ZMod q) * logIntegralPow β₁ x / q.totient =
          (((primeCountingAP x q a : ℝ) - NTKB.logIntegral x / q.totient +
            ε * logIntegralPow β₁ x / q.totient : ℝ) : ℂ) := by
        rw [hεκ]; push_cast; ring
      rw [e2, Complex.norm_real, Real.norm_eq_abs]
      exact this
    · have e := (h hu t ht hq).2 χ₁ β₁ h₁
      rw [← psiAP_eq_psiAP] at e
      have key : (psiAP t q a : ℂ) - t / q.totient +
          χ₁ (a : ZMod q) * (t : ℂ) ^ (β₁ : ℂ) / (q.totient * β₁) =
          ((psiAP t q a - t / q.totient + ε * (t ^ β₁ / (β₁ * q.totient)) : ℝ) : ℂ) := by
        rw [hεκ, ← Complex.ofReal_cpow (by linarith)]
        push_cast; ring
      rw [key, Complex.norm_real, Real.norm_eq_abs] at e
      exact e.trans (hmono t (by linarith))

end NTKB.Davenport
