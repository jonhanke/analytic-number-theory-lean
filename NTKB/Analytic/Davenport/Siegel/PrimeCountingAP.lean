/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Davenport.Siegel.SiegelWalfisz
import NTKB.Analytic.Davenport.Zeros.PrimeCounting

/-!
# The Siegel-Walfisz theorem for `π(x; q, a)`

**Davenport, Ch. 22, p. 133 (row 22-3).** From `ψ(x; q, a) = x/φ(q) + O(x exp(-c √log x))`
(`siegel_walfisz`) we deduce `π(x; q, a) = li x/φ(q) + O(x exp(-c √log x))`, by partial
summation `π(x;q,a) = θ(x;q,a)/log x + ∫_2^x θ(t;q,a)/(t log² t) dt` and `θ(x;q,a) = ψ(x;q,a) + O(√x log x)`.
For `t ≤ √x` we use the trivial bound `θ(t;q,a) ≤ θ(t) ≪ t`.
-/

open Finset MeasureTheory
open scoped Real ArithmeticFunction.vonMangoldt

namespace NTKB.Davenport

/-- `π(x; q, a)`: the number of primes `p ≤ x` with `p ≡ a (mod q)`. -/
noncomputable def primeCountingAP (x : ℝ) (q : ℕ) (a : ℤ) : ℕ :=
  ((Finset.Icc 1 ⌊x⌋₊).filter (fun p : ℕ ↦ p.Prime ∧ (p : ℤ) ≡ a [ZMOD q])).card

/-- The coefficient `log n` if `n` is a prime `≡ a (mod q)`, and `0` otherwise. -/
noncomputable def thetaCoeff (q : ℕ) (a : ℤ) (n : ℕ) : ℝ :=
  if n.Prime ∧ (n : ℤ) ≡ a [ZMOD q] then Real.log n else 0

/-- `θ(x; q, a) = ∑_{p ≤ x, p ≡ a (q)} log p`. -/
noncomputable def thetaAP (x : ℝ) (q : ℕ) (a : ℤ) : ℝ :=
  ∑ n ∈ Icc 0 ⌊x⌋₊, thetaCoeff q a n

lemma primeCountingAP_eq (x : ℝ) (q : ℕ) (a : ℤ) :
    (primeCountingAP x q a : ℝ) = ∑ n ∈ Icc 0 ⌊x⌋₊, (Real.log n)⁻¹ * thetaCoeff q a n := by
  unfold primeCountingAP
  have h1 : (((Icc 1 ⌊x⌋₊).filter (fun p : ℕ ↦ p.Prime ∧ (p : ℤ) ≡ a [ZMOD q])).card : ℝ) =
      ∑ n ∈ Icc 1 ⌊x⌋₊, if n.Prime ∧ (n : ℤ) ≡ a [ZMOD q] then (1 : ℝ) else 0 := by
    rw [Finset.sum_boole]
  rw [h1]
  have h2 : ∑ n ∈ Icc 1 ⌊x⌋₊, (Real.log n)⁻¹ * thetaCoeff q a n =
      ∑ n ∈ Icc 0 ⌊x⌋₊, (Real.log n)⁻¹ * thetaCoeff q a n := by
    apply Finset.sum_subset (Icc_subset_Icc_left zero_le_one)
    intro n h0 hn
    have : n = 0 := by
      simp only [mem_Icc, not_and, not_le] at hn h0
      by_contra hne
      have := hn (Nat.one_le_iff_ne_zero.mpr hne)
      omega
    subst this
    simp [thetaCoeff]
  rw [← h2]
  refine Finset.sum_congr rfl fun n _ ↦ ?_
  unfold thetaCoeff
  split_ifs with h
  · have : Real.log n ≠ 0 :=
      Real.log_ne_zero_of_pos_of_ne_one (mod_cast h.1.pos) (mod_cast h.1.ne_one)
    field_simp
  · simp

lemma intervalIntegrable_thetaAP_div {x : ℝ} (q : ℕ) (a : ℤ) (hx : 2 ≤ x) :
    IntervalIntegrable (fun t : ℝ ↦ thetaAP t q a / (t * Real.log t ^ 2)) volume 2 x := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hx]
  have := integrableOn_mul_sum_Icc (m := 0) (thetaCoeff q a) (a := 2) (b := x) (by norm_num)
    (g := fun t : ℝ ↦ 1 / (t * Real.log t ^ 2)) (by
      refine ContinuousOn.integrableOn_Icc fun t ht ↦ ContinuousAt.continuousWithinAt ?_
      have h0 : t ≠ 0 := by linarith [ht.1]
      have : t * Real.log t ^ 2 ≠ 0 :=
        mul_ne_zero h0 (pow_ne_zero 2 (Real.log_pos (by linarith [ht.1])).ne')
      fun_prop)
  refine this.congr_fun (fun t _ ↦ ?_) measurableSet_Icc
  simp only [thetaAP]
  ring

/-- Partial summation: `π(x; q, a) = θ(x; q, a)/log x + ∫_2^x θ(t; q, a)/(t log² t) dt`. -/
lemma primeCountingAP_eq_thetaAP {x : ℝ} (q : ℕ) (a : ℤ) (hx : 2 ≤ x) :
    (primeCountingAP x q a : ℝ) =
      thetaAP x q a / Real.log x + ∫ t in (2 : ℝ)..x, thetaAP t q a / (t * Real.log t ^ 2) := by
  rw [primeCountingAP_eq]
  have hc0 : thetaCoeff q a 0 = 0 := by simp [thetaCoeff]
  have hc1 : thetaCoeff q a 1 = 0 := by simp [thetaCoeff]
  rw [sum_mul_eq_sub_integral_mul₁ (thetaCoeff q a) (f := fun n ↦ (Real.log n)⁻¹) hc0 hc1 x
    ?_ ?_, ← intervalIntegral.integral_of_le hx]
  · have int_deriv (f : ℝ → ℝ) :
        ∫ u in (2 : ℝ)..x, deriv (fun x ↦ (Real.log x)⁻¹) u * f u =
        ∫ u in (2 : ℝ)..x, -(f u / (u * Real.log u ^ 2)) :=
      intervalIntegral.integral_congr fun u hu ↦ by
        rw [Set.uIcc_of_le hx] at hu
        have h0 : u ≠ 0 := by linarith [hu.1]
        have hl : Real.log u ≠ 0 := (Real.log_pos (by linarith [hu.1])).ne'
        simp only [Real.deriv_inv_log_apply]
        field_simp
    rw [int_deriv, intervalIntegral.integral_neg]
    simp only [thetaAP]
    rw [inv_eq_one_div, div_eq_mul_one_div]
    ring
  · intro z ⟨hz, _⟩
    have : z ≠ 0 := by linarith
    have : Real.log z ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one (by linarith) (by linarith)
    fun_prop
  · refine ContinuousOn.integrableOn_Icc fun z ⟨hz, _⟩ ↦ ContinuousWithinAt.congr ?_
      (fun _ _ ↦ Real.deriv_inv_log_apply) Real.deriv_inv_log_apply
    have : z ≠ 0 := by linarith
    have : Real.log z ^ 2 ≠ 0 :=
      pow_ne_zero 2 (Real.log_ne_zero_of_pos_of_ne_one (by linarith) (by linarith))
    exact ContinuousAt.continuousWithinAt <| by fun_prop

lemma sum_Icc_one_eq (g : ℕ → ℝ) (h0 : g 0 = 0) (N : ℕ) :
    ∑ n ∈ Icc 1 N, g n = ∑ n ∈ Icc 0 N, g n := by
  apply Finset.sum_subset (Icc_subset_Icc_left zero_le_one)
  intro n h0' hn
  have : n = 0 := by
    simp only [mem_Icc, not_and, not_le] at hn h0'
    by_contra hne
    have := hn (Nat.one_le_iff_ne_zero.mpr hne)
    omega
  subst this
  exact h0

lemma thetaCoeff_nonneg (q : ℕ) (a : ℤ) (n : ℕ) : 0 ≤ thetaCoeff q a n := by
  unfold thetaCoeff
  split_ifs with h
  · exact Real.log_nonneg (by exact_mod_cast h.1.one_lt.le)
  · exact le_rfl

lemma thetaAP_nonneg (t : ℝ) (q : ℕ) (a : ℤ) : 0 ≤ thetaAP t q a :=
  Finset.sum_nonneg fun n _ ↦ thetaCoeff_nonneg q a n

lemma thetaAP_le_theta (t : ℝ) (q : ℕ) (a : ℤ) : thetaAP t q a ≤ Chebyshev.theta t := by
  rw [Chebyshev.theta_eq_sum_Icc, Finset.sum_filter]
  unfold thetaAP
  refine Finset.sum_le_sum fun n _ ↦ ?_
  unfold thetaCoeff
  by_cases hp : n.Prime
  · have : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
    split_ifs <;> first | exact le_rfl | exact this | simp_all
  · simp [hp]

lemma psiAP_sub_thetaAP (t : ℝ) (q : ℕ) (a : ℤ) :
    0 ≤ NTKB.Davenport.psiAP t q a - thetaAP t q a ∧
    NTKB.Davenport.psiAP t q a - thetaAP t q a ≤ Chebyshev.psi t - Chebyshev.theta t := by
  set N := ⌊t⌋₊
  have hψ : NTKB.Davenport.psiAP t q a =
      ∑ n ∈ Icc 0 N, if (n : ℤ) ≡ a [ZMOD q] then Λ n else 0 := by
    unfold NTKB.Davenport.psiAP
    rw [Finset.sum_filter]
    exact sum_Icc_one_eq _ (by simp) N
  have hψ' : Chebyshev.psi t = ∑ n ∈ Icc 0 N, Λ n := Chebyshev.psi_eq_sum_Icc t
  have hθ' : Chebyshev.theta t = ∑ n ∈ Icc 0 N, if n.Prime then Real.log n else 0 := by
    rw [Chebyshev.theta_eq_sum_Icc, Finset.sum_filter]
  set d : ℕ → ℝ := fun n ↦ Λ n - if n.Prime then Real.log n else 0 with hdd
  have hd : ∀ n, 0 ≤ d n := by
    intro n
    simp only [hdd]
    split_ifs with h
    · rw [ArithmeticFunction.vonMangoldt_apply_prime h]; simp
    · simpa using (ArithmeticFunction.vonMangoldt_nonneg (n := n))
  have key : NTKB.Davenport.psiAP t q a - thetaAP t q a =
      ∑ n ∈ Icc 0 N, if (n : ℤ) ≡ a [ZMOD q] then d n else 0 := by
    rw [hψ]
    unfold thetaAP
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n _ ↦ ?_
    unfold thetaCoeff
    simp only [hdd]
    by_cases hp : n.Prime <;> by_cases hm : (n : ℤ) ≡ a [ZMOD q]
    · simp [hp, hm, ArithmeticFunction.vonMangoldt_apply_prime hp]
    · simp [hp, hm]
    · simp [hp, hm]
    · simp [hp, hm]
  have key2 : Chebyshev.psi t - Chebyshev.theta t = ∑ n ∈ Icc 0 N, d n := by
    rw [hψ', hθ', ← Finset.sum_sub_distrib]
  rw [key, key2]
  constructor
  · exact Finset.sum_nonneg fun n _ ↦ by split_ifs <;> first | exact hd n | exact le_rfl
  · exact Finset.sum_le_sum fun n _ ↦ by split_ifs <;> first | exact le_rfl | exact hd n

lemma thetaAP_sub_le {B : ℝ} (hB : 0 < B) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 / 2 ∧ ∃ M : ℝ, 0 < M ∧ ∀ x : ℝ, 2 ≤ x → ∀ q : ℕ, 0 < q →
      (q : ℝ) ≤ Real.log x ^ B → ∀ a : ℤ, IsCoprime a q → ∀ t : ℝ, 2 ≤ t → t ≤ x →
        |thetaAP t q a - t / q.totient| ≤
          M * t * (Real.exp (-(c * √(Real.log x / 2))) + √x / t) + 2 * √t * Real.log t := by
  obtain ⟨c0, hc0, C, hC, hSW⟩ := siegel_walfisz (2 * B) (by positivity)
  set c := min c0 (1 / 2) with hcdef
  have hc : 0 < c := lt_min hc0 (by norm_num)
  refine ⟨c, hc, min_le_right _ _, C + 25, by positivity, fun x hx q hq hqx a ha t ht htx ↦ ?_⟩
  set A := Real.exp (-(c * √(Real.log x / 2))) with hA
  have hA0 : 0 < A := Real.exp_pos _
  have ht0 : 0 < t := by linarith
  have hx0 : 0 < x := by linarith
  have hφ : (1 : ℝ) ≤ q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
  have hMeq : (C + 25) * t * (A + √x / t) = (C + 25) * (t * A) + (C + 25) * √x := by
    field_simp
  rw [hMeq]
  have hs1 : 1 ≤ √x := Real.one_le_sqrt.mpr (by linarith)
  have hlt : 0 < Real.log t := Real.log_pos (by linarith)
  have hψθ : 0 ≤ √t * Real.log t := by positivity
  have hE0 : 0 ≤ t * A := by positivity
  have hCt : 0 ≤ C * (t * A) := by positivity
  by_cases hcase : √x ≤ t ∧ 8 ≤ t
  · obtain ⟨h1, h2⟩ := hcase
    have hl2 : 2 < Real.log t := by
      have h8 : Real.log 8 ≤ Real.log t := Real.log_le_log (by norm_num) h2
      have : Real.log 8 = 3 * Real.log 2 := by
        rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
      have := log_two_gt_two_thirds
      linarith
    have hl : Real.log x / 2 ≤ Real.log t := by
      have h1' : Real.log (√x) ≤ Real.log t := Real.log_le_log (Real.sqrt_pos.mpr hx0) h1
      rwa [Real.log_sqrt hx0.le] at h1'
    have hlx0 : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
    have hqt : (q : ℝ) ≤ Real.log t ^ (2 * B) := by
      calc (q : ℝ) ≤ Real.log x ^ B := hqx
        _ ≤ (2 * Real.log t) ^ B := Real.rpow_le_rpow hlx0 (by linarith) hB.le
        _ = 2 ^ B * Real.log t ^ B := Real.mul_rpow (by norm_num) hlt.le
        _ ≤ Real.log t ^ B * Real.log t ^ B := by
            gcongr
        _ = Real.log t ^ (2 * B) := by
            rw [← Real.rpow_add hlt, two_mul]
    have hS := hSW t ht q hq hqt a ha
    have hexp : Real.exp (-c0 * √(Real.log t)) ≤ A := by
      apply Real.exp_le_exp.mpr
      have e1 : c * √(Real.log x / 2) ≤ c * √(Real.log t) :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hl) hc.le
      have e2 : c * √(Real.log t) ≤ c0 * √(Real.log t) :=
        mul_le_mul_of_nonneg_right (min_le_left _ _) (Real.sqrt_nonneg _)
      linarith
    have hS' : |NTKB.Davenport.psiAP t q a - t / q.totient| ≤ C * (t * A) := by
      refine hS.trans ?_
      calc C * t * Real.exp (-c0 * √(Real.log t)) ≤ C * t * A := by gcongr
        _ = C * (t * A) := by ring
    have hd := psiAP_sub_thetaAP t q a
    have hψθ' : Chebyshev.psi t - Chebyshev.theta t ≤ 2 * √t * Real.log t := by
      have := Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log (x := t) (by linarith)
      exact (le_abs_self _).trans this
    have hmain : |thetaAP t q a - t / q.totient| ≤ C * (t * A) + 2 * √t * Real.log t := by
      have := abs_le.mp hS'
      rw [abs_le]
      constructor <;> nlinarith [hd.1, hd.2]
    have hCM : C * (t * A) ≤ (C + 25) * (t * A) := by nlinarith
    have : 0 ≤ (C + 25) * √x := by positivity
    linarith
  · -- trivial bound
    have hθ3 : thetaAP t q a ≤ 3 * t := by
      refine (thetaAP_le_theta t q a).trans ?_
      refine (Chebyshev.theta_le_log4_mul_x ht0.le).trans ?_
      have : Real.log 4 ≤ 3 := by
        have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num); linarith
      nlinarith
    have hth0 := thetaAP_nonneg t q a
    have hφt : 0 ≤ t / q.totient := by positivity
    have hφt' : t / q.totient ≤ t := div_le_self ht0.le hφ
    have h3 : |thetaAP t q a - t / q.totient| ≤ 3 * t := by
      rw [abs_le]; constructor <;> linarith
    have h4 : 3 * t ≤ 25 * √x := by
      rw [not_and_or] at hcase
      rcases hcase with h | h
      · push Not at h; nlinarith
      · push Not at h; nlinarith
    have h5 : 25 * √x ≤ (C + 25) * √x := by nlinarith
    have : 0 ≤ (C + 25) * (t * A) := by positivity
    have : 0 ≤ 2 * √t * Real.log t := by positivity
    linarith

/-- The integral `∫_2^x E(t)/(t log² t) dt` for `|E(t)| ≤ M t (A + √x/t) + 2 √t log t`. -/
lemma norm_integral_le_of_bound {E : ℝ → ℝ} {A M x : ℝ} (hA : 0 < A) (hM : 0 < M)
    (hE : ∀ t : ℝ, 2 ≤ t → t ≤ x → |E t| ≤ M * t * (A + √x / t) + 2 * √t * Real.log t)
    (hx : 2 ≤ x) :
    |∫ t in (2 : ℝ)..x, E t / (t * Real.log t ^ 2)| ≤
      M / Real.log 2 ^ 2 * (A * x + √x * Real.log x) + 4 / Real.log 2 * √x := by
  set L2 := Real.log 2
  have hL2 : 2 / 3 < L2 := log_two_gt_two_thirds
  set g : ℝ → ℝ := fun t ↦ M / L2 ^ 2 * (A + √x * t⁻¹) + 2 / L2 * t ^ (-(1 / 2) : ℝ)
  have hpt : ∀ t ∈ Set.Ioc (2 : ℝ) x, ‖E t / (t * Real.log t ^ 2)‖ ≤ g t := by
    intro t ht
    have ht2 : 2 ≤ t := ht.1.le
    have ht0 : 0 < t := by linarith
    have hlt : L2 ≤ Real.log t := Real.log_le_log two_pos ht2
    have hlt0 : 0 < Real.log t := by linarith
    have hden : 0 < t * Real.log t ^ 2 := by positivity
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hden, div_le_iff₀ hden]
    have h1 := hE t ht2 ht.2
    have hst : √t * √t = t := Real.mul_self_sqrt ht0.le
    have hst0 : 0 < √t := Real.sqrt_pos.mpr ht0
    have p1 : M * t * (A + √x / t) ≤
        M / L2 ^ 2 * (A + √x * t⁻¹) * (t * Real.log t ^ 2) := by
      have e1 : M / L2 ^ 2 * (A + √x * t⁻¹) * (t * Real.log t ^ 2) =
          M * t * (A + √x / t) * (Real.log t ^ 2 / L2 ^ 2) := by
        field_simp
      rw [e1]
      have hq : 1 ≤ Real.log t ^ 2 / L2 ^ 2 := by
        rw [le_div_iff₀ (by positivity)]; nlinarith
      have hBt : 0 ≤ M * t * (A + √x / t) := by positivity
      calc M * t * (A + √x / t) = M * t * (A + √x / t) * 1 := by ring
        _ ≤ M * t * (A + √x / t) * (Real.log t ^ 2 / L2 ^ 2) := by gcongr
    have p2 : 2 * √t * Real.log t ≤ 2 / L2 * t ^ (-(1 / 2) : ℝ) * (t * Real.log t ^ 2) := by
      have hrt : t ^ (-(1 / 2) : ℝ) * t = √t := by
        have := Real.rpow_add ht0 (-(1 / 2) : ℝ) 1
        rw [Real.rpow_one] at this
        rw [← this, Real.sqrt_eq_rpow]; norm_num
      have e2 : 2 / L2 * t ^ (-(1 / 2) : ℝ) * (t * Real.log t ^ 2) =
          2 * √t * Real.log t * (Real.log t / L2) := by
        calc 2 / L2 * t ^ (-(1 / 2) : ℝ) * (t * Real.log t ^ 2)
            = 2 / L2 * (t ^ (-(1 / 2) : ℝ) * t) * Real.log t ^ 2 := by ring
          _ = 2 * √t * Real.log t * (Real.log t / L2) := by rw [hrt]; ring
      rw [e2]
      have hq : 1 ≤ Real.log t / L2 := by rw [le_div_iff₀ (by positivity)]; linarith
      have : 0 ≤ 2 * √t * Real.log t := by positivity
      nlinarith
    have : g t * (t * Real.log t ^ 2) = M / L2 ^ 2 * (A + √x * t⁻¹) * (t * Real.log t ^ 2) +
        2 / L2 * t ^ (-(1 / 2) : ℝ) * (t * Real.log t ^ 2) := by simp only [g]; ring
    rw [this]
    linarith
  have hgint : IntervalIntegrable g MeasureTheory.volume 2 x := by
    refine ContinuousOn.intervalIntegrable fun t ht ↦ ?_
    rw [Set.uIcc_of_le hx] at ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    refine ContinuousAt.continuousWithinAt ?_
    simp only [g]
    exact (continuousAt_const.mul (continuousAt_const.add (continuousAt_const.mul
      (continuousAt_inv₀ ht0)))).add (continuousAt_const.mul
        (Real.continuousAt_rpow_const _ _ (Or.inl ht0)))
  have hI := intervalIntegral.norm_integral_le_of_norm_le hx
    (Filter.Eventually.of_forall hpt) hgint
  rw [Real.norm_eq_abs] at hI
  refine hI.trans ?_
  have hx0 : 0 < x := by linarith
  have i1 : IntervalIntegrable (fun t : ℝ ↦ M / L2 ^ 2 * (A + √x * t⁻¹))
      MeasureTheory.volume 2 x := by
    refine ContinuousOn.intervalIntegrable fun t ht ↦ ?_
    rw [Set.uIcc_of_le hx] at ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    exact (continuousAt_const.mul (continuousAt_const.add (continuousAt_const.mul
      (continuousAt_inv₀ ht0)))).continuousWithinAt
  have i2 : IntervalIntegrable (fun t : ℝ ↦ 2 / L2 * t ^ (-(1 / 2) : ℝ))
      MeasureTheory.volume 2 x := by
    refine ContinuousOn.intervalIntegrable fun t ht ↦ ?_
    rw [Set.uIcc_of_le hx] at ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    exact (continuousAt_const.mul
      (Real.continuousAt_rpow_const _ _ (Or.inl ht0))).continuousWithinAt
  have i3 : IntervalIntegrable (fun t : ℝ ↦ √x * t⁻¹) MeasureTheory.volume 2 x := by
    refine ContinuousOn.intervalIntegrable fun t ht ↦ ?_
    rw [Set.uIcc_of_le hx] at ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    exact (continuousAt_const.mul (continuousAt_inv₀ ht0)).continuousWithinAt
  have hg : ∫ t in (2 : ℝ)..x, g t = M / L2 ^ 2 * ((x - 2) * A + √x * Real.log (x / 2)) +
      2 / L2 * ((x ^ (1 / 2 : ℝ) - 2 ^ (1 / 2 : ℝ)) / (1 / 2)) := by
    simp only [g]
    rw [intervalIntegral.integral_add i1 i2, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_add intervalIntegrable_const i3,
      intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
      integral_inv_of_pos two_pos hx0, integral_rpow (Or.inl (by norm_num))]
    norm_num
  rw [hg]
  have hlog : Real.log (x / 2) ≤ Real.log x := Real.log_le_log (by positivity) (by linarith)
  have hsx : x ^ (1 / 2 : ℝ) = √x := (Real.sqrt_eq_rpow x).symm
  have h2 : (0 : ℝ) ≤ 2 ^ (1 / 2 : ℝ) := by positivity
  have hBL : 0 ≤ M / L2 ^ 2 := by positivity
  have hs0 : 0 ≤ √x := Real.sqrt_nonneg x
  have hlx : 0 ≤ Real.log (x / 2) := Real.log_nonneg (by rw [le_div_iff₀ two_pos]; linarith)
  have hha : (x - 2) * A + √x * Real.log (x / 2) ≤ A * x + √x * Real.log x := by
    nlinarith [mul_le_mul_of_nonneg_left hlog hs0]
  refine add_le_add (mul_le_mul_of_nonneg_left hha hBL) ?_
  · rw [hsx]
    have : (√x - 2 ^ (1 / 2 : ℝ)) / (1 / 2) ≤ 2 * √x := by
      rw [div_le_iff₀ (by norm_num)]; linarith
    calc 2 / L2 * ((√x - 2 ^ (1 / 2 : ℝ)) / (1 / 2)) ≤ 2 / L2 * (2 * √x) := by gcongr
      _ = 4 / L2 * √x := by ring

/-- **Davenport, Ch. 22, p. 133** (the analogue of (D) for `π(x; q, a)`): for every `N > 0`
(here `B`) there are `c, C > 0` with `|π(x; q, a) - li x/φ(q)| ≤ C x exp(-c √log x)` for
`x ≥ 2`, `q ≤ (log x)^N`, `(a, q) = 1`. -/
@[kb "davenport1980" "Ch 22, p. 133"]
theorem siegel_walfisz_primeCounting (B : ℝ) (hB : 0 < B) :
    ∃ c > 0, ∃ C > 0, ∀ x : ℝ, 2 ≤ x → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.log x ^ B →
      ∀ a : ℤ, IsCoprime a q →
        |(primeCountingAP x q a : ℝ) - NTKB.logIntegral x / q.totient| ≤
          C * x * Real.exp (-c * √(Real.log x)) := by
  obtain ⟨c, hc, hc1, M, hM, hE⟩ := thetaAP_sub_le hB
  refine ⟨c / 2, by positivity, 40 * M + 100, by positivity, fun x hx q hq hqx a ha ↦ ?_⟩
  have hx0 : 0 < x := by linarith
  set L2 := Real.log 2 with hL2def
  have hL2 : 2 / 3 < L2 := log_two_gt_two_thirds
  have hL2' : L2 < 1 := by have := Real.log_two_lt_d9; linarith
  have hlx : L2 ≤ Real.log x := Real.log_le_log two_pos hx
  have hlx0 : 0 < Real.log x := by linarith
  set E1 := Real.exp (-(c / 2 * √(Real.log x))) with hE1
  have hE10 : 0 < E1 := Real.exp_pos _
  have hform : Real.exp (-(c / 2) * √(Real.log x)) = E1 := by rw [hE1, neg_mul]
  rw [hform]
  set A := Real.exp (-(c * √(Real.log x / 2))) with hAdef
  have hA0 : 0 < A := Real.exp_pos _
  have hφ : (1 : ℝ) ≤ q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
  have hφ0 : (0 : ℝ) < q.totient := by linarith
  -- the identity
  have hπ := primeCountingAP_eq_thetaAP q a hx
  have hli := NTKB.logIntegral_eq hx
  have hI1 := intervalIntegrable_thetaAP_div q a hx
  have hI2 : IntervalIntegrable (fun t : ℝ ↦ 1 / Real.log t ^ 2) volume 2 x :=
    Chebyshev.intervalIntegrable_one_div_log_sq (by norm_num) (by linarith)
  have hdiff : (∫ t in (2 : ℝ)..x, thetaAP t q a / (t * Real.log t ^ 2)) -
      (1 / (q.totient : ℝ)) * ∫ t in (2 : ℝ)..x, 1 / Real.log t ^ 2 =
      ∫ t in (2 : ℝ)..x, (thetaAP t q a - t / q.totient) / (t * Real.log t ^ 2) := by
    rw [← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_sub hI1 (hI2.const_mul _)]
    refine intervalIntegral.integral_congr fun t ht ↦ ?_
    rw [Set.uIcc_of_le hx] at ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have hl : Real.log t ≠ 0 := (Real.log_pos (by linarith [ht.1])).ne'
    field_simp
  have hid : (primeCountingAP x q a : ℝ) - NTKB.logIntegral x / q.totient =
      (thetaAP x q a - x / q.totient) / Real.log x + 2 / (q.totient * L2) +
        ∫ t in (2 : ℝ)..x, (thetaAP t q a - t / q.totient) / (t * Real.log t ^ 2) := by
    rw [hπ, hli, ← hdiff]
    have : Real.log x ≠ 0 := hlx0.ne'
    have : L2 ≠ 0 := by linarith
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
  have hsl := NTKB.sqrt_mul_log_le (c := c / 2) (by positivity) (by linarith) (x := x)
    (by linarith)
  rw [← hE1] at hsl
  have h1E := NTKB.one_le_mul_exp_neg_sqrt_log (c := c / 2) (by positivity) (by linarith) hx
  rw [← hE1] at h1E
  have hxE : 0 ≤ x * E1 := by positivity
  have hi1 : 1 / L2 ≤ 3 / 2 := by rw [div_le_iff₀ (by linarith)]; linarith
  have hsx : √x ≤ √x * Real.log x / L2 := by
    rw [le_div_iff₀ (by linarith)]
    exact mul_le_mul_of_nonneg_left hlx (Real.sqrt_nonneg x)
  -- `|θ(x;q,a) - x/φ|`
  have hEx := hE x hx q hq hqx a ha x hx le_rfl
  have hMx : M * x * (A + √x / x) = M * (x * A) + M * √x := by field_simp
  rw [hMx] at hEx
  have hsq : M * √x ≤ 9 * M * (x * E1) := by
    calc M * √x ≤ M * (√x * Real.log x / L2) := by gcongr
      _ ≤ M * (6 * (x * E1) / L2) := by gcongr
      _ = M * 6 * (1 / L2) * (x * E1) := by ring
      _ ≤ M * 6 * (3 / 2) * (x * E1) := by gcongr
      _ = 9 * M * (x * E1) := by ring
  have hxA : M * (x * A) ≤ M * (x * E1) := by gcongr
  have hEx' : |thetaAP x q a - x / q.totient| ≤ (10 * M + 12) * (x * E1) := by
    refine hEx.trans ?_
    linarith
  have b1 : |(thetaAP x q a - x / q.totient) / Real.log x| ≤
      (10 * M + 12) * (3 / 2) * (x * E1) := by
    rw [abs_div, abs_of_pos hlx0, div_le_iff₀ hlx0]
    have h0 : 0 ≤ (10 * M + 12) * (x * E1) := by positivity
    have h3 : 1 ≤ 3 / 2 * Real.log x := by linarith
    calc |thetaAP x q a - x / q.totient| ≤ (10 * M + 12) * (x * E1) := hEx'
      _ = (10 * M + 12) * (x * E1) * 1 := by ring
      _ ≤ (10 * M + 12) * (x * E1) * (3 / 2 * Real.log x) := by gcongr
      _ = (10 * M + 12) * (3 / 2) * (x * E1) * Real.log x := by ring
  -- the integral
  have b3 := norm_integral_le_of_bound (E := fun t ↦ thetaAP t q a - t / q.totient) hA0 hM
    (fun t ht htx ↦ hE x hx q hq hqx a ha t ht htx) hx
  have b3' : |∫ t in (2 : ℝ)..x, (thetaAP t q a - t / q.totient) / (t * Real.log t ^ 2)| ≤
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
  have c3 : 2 / ((q.totient : ℝ) * L2) ≤ 3 * (x * E1) := by
    have h1 : 2 / ((q.totient : ℝ) * L2) ≤ 2 / (1 * L2) := by
      apply div_le_div_of_nonneg_left (by norm_num) (by linarith)
      exact mul_le_mul_of_nonneg_right hφ (by linarith)
    have h2 : 2 / (1 * L2) ≤ 3 := by rw [div_le_iff₀ (by linarith)]; linarith
    linarith
  calc |(thetaAP x q a - x / q.totient) / Real.log x + 2 / (q.totient * L2) +
        ∫ t in (2 : ℝ)..x, (thetaAP t q a - t / q.totient) / (t * Real.log t ^ 2)|
      ≤ |(thetaAP x q a - x / q.totient) / Real.log x| + |2 / ((q.totient : ℝ) * L2)| +
          |∫ t in (2 : ℝ)..x, (thetaAP t q a - t / q.totient) / (t * Real.log t ^ 2)| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ (10 * M + 12) * (3 / 2) * (x * E1) + 3 * (x * E1) +
          (M * (9 / 4) * 7 + 24 * (9 / 4)) * (x * E1) := by
        rw [abs_of_pos (by positivity : (0 : ℝ) < 2 / ((q.totient : ℝ) * L2))]
        exact add_le_add (add_le_add b1 c3) b3'
    _ ≤ (40 * M + 100) * (x * E1) := by
        have : (10 * M + 12) * (3 / 2) + 3 + (M * (9 / 4) * 7 + 24 * (9 / 4)) ≤ 40 * M + 100 := by
          linarith
        have h := mul_le_mul_of_nonneg_right this hxE
        linarith
    _ = (40 * M + 100) * x * E1 := by ring

end NTKB.Davenport
