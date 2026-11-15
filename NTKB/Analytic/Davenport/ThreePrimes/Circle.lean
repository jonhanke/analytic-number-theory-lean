/- Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license. -/
import NTKB.Attr
import NTKB.Analytic.Davenport.Sieve.Gallagher
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# The circle method set-up for three primes (Davenport, Chapter 26, pp. 145–150)

With `e(x) = exp(2πix)`:

* `primeExpSum N α = S(α) = ∑_{n ≤ N} Λ(n) e(nα)`, `linearExpSum N β = T(β) = ∑_{n ≤ N} e(nβ)`;
* `threePrimeRep N = r(N) = ∑_{k₁ + k₂ + k₃ = N} Λ(k₁) Λ(k₂) Λ(k₃)` (row 26-1).

Results:

* **26-2, 26-3** (formula (1)): `r(N) = ∫_c^{c+1} S(α)³ e(-Nα) dα` for every `c`
  (`threePrimeRep_eq_integral`);
* **26-13** (formula (E)): `∫_{-1/Q}^{1/Q} T(β)³ e(-Nβ) dβ = N²/2 + O(N + Q²)`
  (`norm_integral_linearExpSum_cube_sub_le`);
* **26-18** (Parseval): `∫_0^1 |S(α)|² dα = ∑_{n ≤ N} Λ(n)²` (`integral_norm_primeExpSum_sq`); the
  bound `∑_{n ≤ x} Λ(n)² ≤ (log 4 + 4) x log x` is `NTKB.Davenport.sum_vonMangoldt_sq_le`.
-/

open Finset Real
open scoped ArithmeticFunction.vonMangoldt

namespace NTKB.Davenport

/-- `S(α) = ∑_{n ≤ N} Λ(n) e(nα)`. -/
noncomputable def primeExpSum (N : ℕ) (α : ℝ) : ℂ :=
  ∑ n ∈ Icc 1 N, (Λ n : ℂ) * Complex.exp (2 * π * Complex.I * (n * α))

/-- `T(β) = ∑_{n ≤ N} e(nβ)`. -/
noncomputable def linearExpSum (N : ℕ) (β : ℝ) : ℂ :=
  ∑ n ∈ Icc 1 N, Complex.exp (2 * π * Complex.I * (n * β))

/-- **Davenport, Ch. 26, p. 145 (row 26-1)**:
`r(N) = ∑_{k₁ + k₂ + k₃ = N, kᵢ ≥ 1} Λ(k₁) Λ(k₂) Λ(k₃)`. -/
noncomputable def threePrimeRep (N : ℕ) : ℝ :=
  ∑ k ∈ (Icc 1 N ×ˢ Icc 1 N ×ˢ Icc 1 N).filter (fun k ↦ k.1 + k.2.1 + k.2.2 = N),
    Λ k.1 * Λ k.2.1 * Λ k.2.2


/-- Generic exponential sum. -/
noncomputable def genExpSum (N : ℕ) (a : ℕ → ℂ) (α : ℝ) : ℂ :=
  ∑ n ∈ Icc 1 N, a n * Complex.exp (2 * π * Complex.I * (n * α))

lemma integral_exp_int_shift (c : ℝ) (m : ℤ) :
    ∫ α in c..c + 1, Complex.exp (2 * π * Complex.I * (m : ℂ) * α) = if m = 0 then 1 else 0 := by
  by_cases hk : m = 0
  · simp [hk]
  · have hk' : (m : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hk
    have hc : (2 * π * Complex.I * (m : ℂ)) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero, hk']
    rw [integral_exp_mul_complex hc]
    have h1 : Complex.exp (2 * π * Complex.I * (m : ℂ)) = 1 := by
      rw [← Complex.exp_int_mul_two_pi_mul_I m]; congr 1; ring
    have h2 : Complex.exp (2 * π * Complex.I * (m : ℂ) * ((c + 1 : ℝ) : ℂ)) =
        Complex.exp (2 * π * Complex.I * (m : ℂ) * (c : ℂ)) := by
      rw [Complex.ofReal_add, Complex.ofReal_one, mul_add, mul_one, Complex.exp_add, h1, mul_one]
    rw [h2]; simp [hk]

lemma genExpSum_cube_mul (N : ℕ) (a : ℕ → ℂ) (α : ℝ) :
    genExpSum N a α ^ 3 * Complex.exp (-(2 * π * Complex.I * (N * α))) =
      ∑ k ∈ Icc 1 N ×ˢ Icc 1 N ×ˢ Icc 1 N, a k.1 * a k.2.1 * a k.2.2 *
        Complex.exp (2 * π * Complex.I * (((k.1 + k.2.1 + k.2.2 : ℕ) : ℤ) - N : ℤ) * α) := by
  have h3 : genExpSum N a α ^ 3 = ∑ k ∈ Icc 1 N ×ˢ Icc 1 N ×ˢ Icc 1 N,
      (a k.1 * Complex.exp (2 * π * Complex.I * (k.1 * α))) *
      (a k.2.1 * Complex.exp (2 * π * Complex.I * (k.2.1 * α))) *
      (a k.2.2 * Complex.exp (2 * π * Complex.I * (k.2.2 * α))) := by
    simp only [genExpSum, pow_three, Finset.sum_product]
    simp only [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun l _ => by ring)
  rw [h3, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  have : Complex.exp (2 * π * Complex.I * (((k.1 + k.2.1 + k.2.2 : ℕ) : ℤ) - N : ℤ) * α) =
      Complex.exp (2 * π * Complex.I * (k.1 * α)) * Complex.exp (2 * π * Complex.I * (k.2.1 * α)) *
      Complex.exp (2 * π * Complex.I * (k.2.2 * α)) *
      Complex.exp (-(2 * π * Complex.I * (N * α))) := by
    rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
    congr 1; push_cast; ring
  rw [this]; ring

lemma integral_genExpSum_cube (N : ℕ) (a : ℕ → ℂ) (c : ℝ) :
    ∫ α in c..c + 1, genExpSum N a α ^ 3 * Complex.exp (-(2 * π * Complex.I * (N * α))) =
      ∑ k ∈ (Icc 1 N ×ˢ Icc 1 N ×ˢ Icc 1 N).filter (fun k ↦ k.1 + k.2.1 + k.2.2 = N),
        a k.1 * a k.2.1 * a k.2.2 := by
  simp_rw [genExpSum_cube_mul]
  rw [intervalIntegral.integral_finsetSum (fun k _ => by
    apply Continuous.intervalIntegrable; fun_prop)]
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [intervalIntegral.integral_const_mul, integral_exp_int_shift]
  by_cases h : k.1 + k.2.1 + k.2.2 = N
  · simp [h]
  · have : ((k.1 + k.2.1 + k.2.2 : ℕ) : ℤ) - N ≠ 0 := by omega
    simp [h, this]
    intro h2; exact absurd (by exact_mod_cast h2) this

lemma card_triples (N : ℕ) :
    2 * ((Icc 1 N ×ˢ Icc 1 N ×ˢ Icc 1 N).filter
      (fun k : ℕ × ℕ × ℕ ↦ k.1 + k.2.1 + k.2.2 = N)).card = (N - 1) * (N - 2) := by
  have h1 : ((Icc 1 N ×ˢ Icc 1 N ×ˢ Icc 1 N).filter
      (fun k : ℕ × ℕ × ℕ ↦ k.1 + k.2.1 + k.2.2 = N)).card =
      ((Icc 1 N ×ˢ Icc 1 N).filter (fun p : ℕ × ℕ ↦ p.1 + p.2 < N)).card := by
    refine Finset.card_nbij' (fun k => (k.1, k.2.1)) (fun p => (p.1, p.2, N - p.1 - p.2))
      ?_ ?_ ?_ ?_
    · intro k hk; simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc,
        Finset.mem_coe] at hk ⊢; omega
    · intro p hp; simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc,
        Finset.mem_coe] at hp ⊢; omega
    · intro k hk; simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc,
        Finset.mem_coe] at hk; ext <;> simp <;> omega
    · intro p hp; simp
  have h2 : ((Icc 1 N ×ˢ Icc 1 N).filter (fun p : ℕ × ℕ ↦ p.1 + p.2 < N)).card =
      ∑ a ∈ Icc 1 N, (N - 1 - a) := by
    rw [Finset.card_filter, Finset.sum_product]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [← Finset.card_filter]
    have : (Icc 1 N).filter (fun b => a + b < N) = Icc 1 (N - 1 - a) := by
      ext b; simp only [Finset.mem_filter, Finset.mem_Icc]; omega
    rw [this]; simp
  have h3 : ∑ a ∈ Icc 1 N, (N - 1 - a) = ∑ j ∈ range N, (N - 1 - j - 1) := by
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    omega
  have h4 : ∑ j ∈ range N, (N - 1 - j - 1) = ∑ j ∈ range N, (j - 1) :=
    Finset.sum_range_reflect (fun j => j - 1) N
  rw [h1, h2, h3, h4]
  rcases N with _ | n
  · simp
  · rw [Finset.sum_range_succ']
    simp only [Nat.add_sub_cancel]
    have := Finset.sum_range_id_mul_two n
    rw [show (0 : ℕ) - 1 = 0 from rfl, add_zero, mul_comm 2, this]
    congr 1

lemma linearExpSum_geom (N : ℕ) (β : ℝ) :
    (Complex.exp (2 * π * Complex.I * β) - 1) * linearExpSum N β =
      Complex.exp (2 * π * Complex.I * β) ^ (N + 1) - Complex.exp (2 * π * Complex.I * β) := by
  set z := Complex.exp (2 * π * Complex.I * β) with hz
  have hpow : ∀ n : ℕ, Complex.exp (2 * π * Complex.I * (n * β)) = z ^ n := by
    intro n
    rw [hz, ← Complex.exp_nat_mul]; congr 1; ring
  induction N with
  | zero => simp [linearExpSum]
  | succ n ih =>
    have : linearExpSum (n + 1) β = linearExpSum n β + z ^ (n + 1) := by
      unfold linearExpSum
      rw [Finset.sum_Icc_succ_top (by omega)]
      rw [hpow]
    rw [this, mul_add, ih]; ring

lemma norm_linearExpSum_le_inv (N : ℕ) {β : ℝ} (h0 : β ≠ 0) (h : |β| ≤ 1 / 2) :
    ‖linearExpSum N β‖ ≤ 1 / (2 * |β|) := by
  set z := Complex.exp (2 * π * Complex.I * β) with hz
  have hzn : ‖z‖ = 1 := by rw [hz, Complex.norm_exp]; simp
  have hgeom := linearExpSum_geom N β
  have hnum : ‖(z ^ (N + 1) - z)‖ ≤ 2 := by
    have : z ^ (N + 1) - z = z * (z ^ N - 1) := by ring
    rw [this, norm_mul, hzn, one_mul]
    calc ‖z ^ N - 1‖ ≤ ‖z ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, hzn]; norm_num
  have hden : 4 * |β| ≤ ‖z - 1‖ := by
    have e : z = Complex.exp (Complex.I * ((2 * π * β : ℝ) : ℂ)) := by
      rw [hz]; congr 1; push_cast; ring
    rw [e, Complex.norm_exp_I_mul_ofReal_sub_one, norm_mul]
    have hs : 2 * |β| ≤ |Real.sin (2 * π * β / 2)| := by
      have hy : 2 * π * β / 2 = π * β := by ring
      rw [hy]
      have hb := abs_le.mp h
      rcases le_or_gt 0 β with hβ | hβ
      · rw [abs_of_nonneg hβ] at *
        have := Real.mul_le_sin (x := π * β) (by positivity) (by nlinarith [Real.pi_pos])
        rw [abs_of_nonneg (le_trans (by positivity) this)]
        have h2 : 2 / π * (π * β) = 2 * β := by field_simp
        linarith
      · rw [abs_of_neg hβ] at *
        have hnb : 0 < -β := by linarith
        have := Real.mul_le_sin (x := π * (-β)) (by positivity)
          (by nlinarith [Real.pi_pos])
        have e2 : Real.sin (π * β) = - Real.sin (π * (-β)) := by
          rw [mul_neg, Real.sin_neg, neg_neg]
        rw [e2, abs_neg, abs_of_nonneg (le_trans (by positivity) this)]
        have h2 : 2 / π * (π * (-β)) = 2 * (-β) := by field_simp
        linarith
    have : ‖(2 : ℝ)‖ = 2 := by simp
    rw [this]
    simp only [Real.norm_eq_abs]
    linarith
  have hβ : 0 < |β| := abs_pos.mpr h0
  have : ‖z - 1‖ * ‖linearExpSum N β‖ ≤ 2 := by
    rw [← norm_mul, hgeom]; exact hnum
  rw [le_div_iff₀ (by positivity)]
  nlinarith [norm_nonneg (linearExpSum N β)]

lemma norm_integral_le_tail (Q : ℝ) (hQ : 2 ≤ Q) (f : ℝ → ℂ)
    (h : ∀ β ∈ Set.Icc Q⁻¹ 2⁻¹, ‖f β‖ ≤ 1 / 8 * β ^ (-3 : ℤ)) :
    ‖∫ β in Q⁻¹..2⁻¹, f β‖ ≤ Q ^ 2 / 16 := by
  have hQ0 : 0 < Q := by linarith
  have hle : Q⁻¹ ≤ 2⁻¹ := inv_anti₀ (by norm_num) hQ
  have h0 : (0 : ℝ) ∉ Set.uIcc Q⁻¹ 2⁻¹ := by
    rw [Set.uIcc_of_le hle]; intro hm; have := hm.1; have : 0 < Q⁻¹ := by positivity
    linarith
  have hint : IntervalIntegrable (fun β : ℝ => 1 / 8 * β ^ (-3 : ℤ)) MeasureTheory.volume
      Q⁻¹ 2⁻¹ :=
    (intervalIntegral.intervalIntegrable_zpow (Or.inr h0)).const_mul _
  refine (intervalIntegral.norm_integral_le_of_norm_le hle ?_ hint).trans ?_
  · exact Filter.Eventually.of_forall (fun β hβ => h β ⟨hβ.1.le, hβ.2⟩)
  · rw [intervalIntegral.integral_const_mul, integral_zpow (Or.inr ⟨by norm_num, h0⟩)]
    have : (Q⁻¹) ^ (-3 + 1 : ℤ) = Q ^ 2 := by
      rw [show (-3 + 1 : ℤ) = -2 by norm_num]; simp [zpow_neg]
    rw [this]
    have h2 : ((2 : ℝ)⁻¹) ^ (-3 + 1 : ℤ) = 4 := by
      rw [show (-3 + 1 : ℤ) = -2 by norm_num]; norm_num [zpow_neg]
    rw [h2]
    norm_num
    nlinarith

/-- `S` has period `1`. -/
theorem primeExpSum_add_int (N : ℕ) (α : ℝ) (m : ℤ) :
    primeExpSum N (α + m) = primeExpSum N α := by
  unfold primeExpSum
  refine Finset.sum_congr rfl (fun n _ => ?_)
  congr 1
  have : (2 * π * Complex.I * (n * ((α + m : ℝ) : ℂ))) =
      2 * π * Complex.I * (n * α) + ((n * m : ℤ) : ℂ) * (2 * π * Complex.I) := by
    push_cast; ring
  rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- `|S(α)| ≤ ψ(N)`. -/
theorem norm_primeExpSum_le (N : ℕ) (α : ℝ) :
    ‖primeExpSum N α‖ ≤ ∑ n ∈ Icc 1 N, Λ n := by
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun n _ => ?_))
  rw [norm_mul, Complex.norm_exp]
  simp [abs_of_nonneg (ArithmeticFunction.vonMangoldt_nonneg (n := n))]

/-- `|T(β)| ≤ N`. -/
theorem norm_linearExpSum_le (N : ℕ) (β : ℝ) : ‖linearExpSum N β‖ ≤ N := by
  refine (norm_sum_le _ _).trans ?_
  have : ∀ n ∈ Icc 1 N, ‖Complex.exp (2 * π * Complex.I * (n * β))‖ ≤ 1 := by
    intro n _; rw [Complex.norm_exp]; simp
  refine (Finset.sum_le_sum this).trans ?_
  simp

/-- **Davenport, Ch. 26, p. 145, (1) (rows 26-2, 26-3)**:
`r(N) = ∫_c^{c+1} S(α)³ e(-Nα) dα`. -/
@[kb "davenport1980" "Ch 26, p. 145, (1)"]
theorem threePrimeRep_eq_integral (N : ℕ) (c : ℝ) :
    (threePrimeRep N : ℂ) = ∫ α in c..c + 1,
      primeExpSum N α ^ 3 * Complex.exp (-(2 * π * Complex.I * (N * α))) := by
  have := integral_genExpSum_cube N (fun n => (Λ n : ℂ)) c
  have e : primeExpSum N = genExpSum N (fun n => (Λ n : ℂ)) := rfl
  rw [e, this]
  unfold threePrimeRep
  push_cast; rfl

/-- **Davenport, Ch. 26, p. 148, (E) (row 26-13)**: for `Q ≥ 2`,
`|∫_{-1/Q}^{1/Q} T(β)³ e(-Nβ) dβ - N²/2| ≤ 2N + Q²`. -/
@[kb "davenport1980" "Ch 26, p. 148, (E)"]
theorem norm_integral_linearExpSum_cube_sub_le (N : ℕ) {Q : ℝ} (hQ : 2 ≤ Q) :
    ‖(∫ β in -Q⁻¹..Q⁻¹, linearExpSum N β ^ 3 * Complex.exp (-(2 * π * Complex.I * (N * β)))) -
      (N : ℂ) ^ 2 / 2‖ ≤ 2 * N + Q ^ 2 := by
  set F : ℝ → ℂ := fun β => linearExpSum N β ^ 3 * Complex.exp (-(2 * π * Complex.I * (N * β)))
    with hF
  have hQ0 : 0 < Q := by linarith
  have hle : Q⁻¹ ≤ 2⁻¹ := inv_anti₀ (by norm_num) hQ
  have hQi : 0 < Q⁻¹ := by positivity
  have hcont : Continuous F := by
    simp only [hF, linearExpSum]; fun_prop
  have hint : ∀ a b : ℝ, IntervalIntegrable F MeasureTheory.volume a b :=
    fun a b => hcont.intervalIntegrable a b
  -- full period
  have hfull : ∫ β in (-2⁻¹ : ℝ)..2⁻¹, F β = (((Icc 1 N ×ˢ Icc 1 N ×ˢ Icc 1 N).filter
      (fun k : ℕ × ℕ × ℕ ↦ k.1 + k.2.1 + k.2.2 = N)).card : ℂ) := by
    have h := integral_genExpSum_cube N (fun _ => (1 : ℂ)) (-2⁻¹)
    have e : genExpSum N (fun _ => (1 : ℂ)) = linearExpSum N := by
      funext β; simp [genExpSum, linearExpSum]
    rw [e, show (-2⁻¹ : ℝ) + 1 = 2⁻¹ by norm_num] at h
    simpa using h
  -- pointwise tail bound
  have hpt : ∀ β : ℝ, β ∈ Set.Icc Q⁻¹ 2⁻¹ →
      ‖F β‖ ≤ 1 / 8 * β ^ (-3 : ℤ) ∧ ‖F (-β)‖ ≤ 1 / 8 * β ^ (-3 : ℤ) := by
    intro β hβ
    have hβ0 : 0 < β := lt_of_lt_of_le hQi hβ.1
    have key : ∀ γ : ℝ, |γ| = β → ‖F γ‖ ≤ 1 / 8 * β ^ (-3 : ℤ) := by
      intro γ hγ
      have hγ0 : γ ≠ 0 := by intro h; rw [h] at hγ; simp at hγ; linarith
      have hb := norm_linearExpSum_le_inv N hγ0 (by rw [hγ]; exact hβ.2.trans (by norm_num))
      rw [hγ] at hb
      simp only [hF]
      rw [norm_mul, Complex.norm_exp, norm_pow]
      simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, Complex.mul_im]
      have hnn := norm_nonneg (linearExpSum N γ)
      have : (1 / (2 * β)) ^ 3 = 1 / 8 * β ^ (-3 : ℤ) := by
        rw [zpow_neg]; simp; field_simp; norm_num
      calc _ ≤ (1 / (2 * β)) ^ 3 := by
            simp
            simpa using pow_le_pow_left₀ hnn hb 3
        _ = _ := this
    exact ⟨key β (abs_of_pos hβ0), key (-β) (by rw [abs_neg, abs_of_pos hβ0])⟩
  have hA : ‖∫ β in Q⁻¹..2⁻¹, F β‖ ≤ Q ^ 2 / 16 :=
    norm_integral_le_tail Q hQ F (fun β hβ => (hpt β hβ).1)
  have hB : ‖∫ β in Q⁻¹..2⁻¹, F (-β)‖ ≤ Q ^ 2 / 16 :=
    norm_integral_le_tail Q hQ (fun β => F (-β)) (fun β hβ => (hpt β hβ).2)
  rw [intervalIntegral.integral_comp_neg (f := F)] at hB
  have hsplit : ∫ β in (-2⁻¹ : ℝ)..2⁻¹, F β =
      (∫ β in (-2⁻¹ : ℝ)..-Q⁻¹, F β) + (∫ β in -Q⁻¹..Q⁻¹, F β) + ∫ β in Q⁻¹..2⁻¹, F β := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hint _ _) (hint _ _),
      intervalIntegral.integral_add_adjacent_intervals (hint _ _) (hint _ _)]
  -- count
  have hcount : ‖((((Icc 1 N ×ˢ Icc 1 N ×ˢ Icc 1 N).filter
      (fun k : ℕ × ℕ × ℕ ↦ k.1 + k.2.1 + k.2.2 = N)).card : ℕ) : ℂ) - (N : ℂ) ^ 2 / 2‖ ≤
      2 * N := by
    have h2 := card_triples N
    set c := ((Icc 1 N ×ˢ Icc 1 N ×ˢ Icc 1 N).filter
      (fun k : ℕ × ℕ × ℕ ↦ k.1 + k.2.1 + k.2.2 = N)).card
    clear_value c
    have : ((c : ℂ) - (N : ℂ) ^ 2 / 2) = (((c : ℝ) - (N : ℝ) ^ 2 / 2 : ℝ) : ℂ) := by
      push_cast; ring
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_le]
    rcases N with _ | _ | N
    · simp at h2; simp [h2]
    · simp at h2; simp [h2]; norm_num
    · have h2' : (2 : ℝ) * c = ((N : ℝ) + 1) * N := by
        have : (2 * c : ℕ) = (N + 1 + 1 - 1) * (N + 1 + 1 - 2) := h2
        simp at this
        exact_mod_cast this
      push_cast
      constructor <;> nlinarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  have hmid : (∫ β in -Q⁻¹..Q⁻¹, F β) - (N : ℂ) ^ 2 / 2 =
      ((((Icc 1 N ×ˢ Icc 1 N ×ˢ Icc 1 N).filter
      (fun k : ℕ × ℕ × ℕ ↦ k.1 + k.2.1 + k.2.2 = N)).card : ℂ) - (N : ℂ) ^ 2 / 2) -
      (∫ β in (-2⁻¹ : ℝ)..-Q⁻¹, F β) - ∫ β in Q⁻¹..2⁻¹, F β := by
    rw [← hfull, hsplit]; ring
  show ‖(∫ β in -Q⁻¹..Q⁻¹, F β) - (N : ℂ) ^ 2 / 2‖ ≤ _
  rw [hmid]
  calc _ ≤ ‖((_ : ℂ) - (N : ℂ) ^ 2 / 2)‖ + ‖∫ β in (-2⁻¹ : ℝ)..-Q⁻¹, F β‖ +
        ‖∫ β in Q⁻¹..2⁻¹, F β‖ := by
        refine (norm_sub_le _ _).trans ?_
        gcongr
        exact norm_sub_le _ _
    _ ≤ 2 * N + Q ^ 2 / 16 + Q ^ 2 / 16 := by gcongr
    _ ≤ _ := by nlinarith [sq_nonneg Q]

/-- **Davenport, Ch. 26, p. 150 (row 26-18)**: `∫_0^1 |S(α)|² dα = ∑_{n ≤ N} Λ(n)²`. -/
@[kb "davenport1980" "Ch 26, p. 150"]
theorem integral_norm_primeExpSum_sq (N : ℕ) :
    ∫ α in (0 : ℝ)..1, ‖primeExpSum N α‖ ^ 2 = ∑ n ∈ Icc 1 N, Λ n ^ 2 := by
  have h := integral_norm_sum_exp_sq ((Icc 1 N).image (fun n : ℕ => (n : ℤ)))
    (fun n => (Λ n.toNat : ℂ))
  rw [Finset.sum_image (fun x _ y _ h => by exact_mod_cast h)] at h
  simp only [primeExpSum]
  convert h using 3
  · rw [Finset.sum_image (fun x _ y _ h => by exact_mod_cast h)]
    simp
  · simp [abs_of_nonneg (ArithmeticFunction.vonMangoldt_nonneg)]

end NTKB.Davenport
