/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Davenport.Zeros.ExplicitSmall

/-!
# The truncated explicit formula for `1 < x < 2`, and uniform convergence (Davenport, Chapter 17)

**Davenport, Ch. 17, p. 110 (row 17-16).** The truncated formula (9), (10) of row 17-13 also holds
for `1 < x < 2`, with a different error term. Here: there is an absolute `A` with
`|ψ₀(x) - (x - ∑_{|γ|<T} x^ρ/ρ - ζ'(0)/ζ(0) - ½ log(1 - x^{-2}))| ≤ A (1/log² x + 1/log(2/x)) log² T / T`
for `1 < x < 2`, `T ≥ 3` (here `ψ₀(x) = 0`). The proof is that of
`NTKB.norm_psi0R_sub_explicitMain_le_small` (nt-040-leftovers) with every constant made explicit in `x`:
the Perron part has only far terms, `|log(x/n)| ≥ log(2/x)`, and the horizontal sides use
`u ≤ (2/log x) x^{u/2}`; the Dirichlet series `-ζ'/ζ(c)` is bounded at `c = 1 + 1/log(3x) ≥ 1 + 1/log 6`.

**Davenport, Ch. 17, p. 109 (row 17-17).** The explicit formula converges uniformly on every closed
interval `[a, b] ⊂ (1, ∞)` free of prime powers (from 17-13 and 17-16), and not uniformly on any
right neighbourhood `[n, n + ε)` of a prime power `n`: the partial sums are continuous in `x`, the limit
`ψ₀` jumps at `n`.
-/

open Filter Topology Complex Set MeasureTheory
open scoped Real ArithmeticFunction.vonMangoldt Interval

namespace NTKB

/-- The Perron part for `1 < x < 2`, uniformly in `x`: the constant is `3xK/(π log(2/x)) + 1`. -/
lemma norm_psi0R_sub_explicitJ_le_unif :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : ℝ, 1 < x → x < 2 → ∀ T : ℝ, 0 < T →
      ‖(psi0R x : ℂ) - explicitJ x (perronAbscissa x) T‖ ≤
        (3 * x * K / (π * Real.log (2 / x)) + 1) / T := by
  have hπ := Real.pi_pos
  have hl6 : 0 < Real.log 6 := Real.log_pos (by norm_num)
  obtain ⟨σ₀, hσ₀def⟩ : ∃ σ₀ : ℝ, σ₀ = 1 + 1 / Real.log 6 := ⟨_, rfl⟩
  have hσ₀ : 1 < σ₀ := by
    have : 0 < 1 / Real.log 6 := by positivity
    linarith
  refine ⟨-(deriv riemannZeta σ₀ / riemannZeta σ₀).re,
    (hasSum_vonMangoldt_rpow hσ₀).nonneg fun n ↦ mul_nonneg
      ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg n.cast_nonneg _),
    fun x hx hx2 T hT ↦ ?_⟩
  have hx0 : 0 < x := by linarith
  have hc1 := one_lt_perronAbscissa (x := x) hx.le
  have hxc := rpow_perronAbscissa_le (x := x) hx.le
  set c := perronAbscissa x with hcdef
  have hc0 : 0 < c := by linarith
  have hℓ : 0 < Real.log (2 / x) := Real.log_pos (by rw [one_lt_div hx0]; exact hx2)
  set ℓ := Real.log (2 / x) with hℓdef
  have hS := hasSum_vonMangoldt_rpow hc1
  set S := -(deriv riemannZeta c / riemannZeta c).re with hSdef
  set K := -(deriv riemannZeta σ₀ / riemannZeta σ₀).re with hKdef
  have hS0 : 0 ≤ S := hS.nonneg fun n ↦ mul_nonneg
    ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg n.cast_nonneg _)
  have hcσ : σ₀ ≤ c := by
    rw [hcdef, hσ₀def]; unfold perronAbscissa
    have h3 : 0 < Real.log (3 * x) := Real.log_pos (by linarith)
    have : 1 / Real.log 6 ≤ 1 / Real.log (3 * x) :=
      one_div_le_one_div_of_le h3 (Real.log_le_log (by linarith) (by linarith))
    linarith
  have hSK : S ≤ K := by
    have h1 := norm_logDeriv_riemannZeta_le_of_le (s := (c : ℂ)) hσ₀ (by simpa using hcσ)
    have h2 : S ≤ ‖deriv riemannZeta (c : ℂ) / riemannZeta (c : ℂ)‖ :=
      (neg_le_abs _).trans (Complex.abs_re_le_norm _)
    exact h2.trans h1
  have hd := Davenport.hasSum_explicitJ (x := x) T hx0 hc1
  rw [psi0R_of_lt_two hx.le hx2, Complex.ofReal_zero, zero_sub, norm_neg, ← hd.tsum_eq]
  have hG := hS.mul_left (3 * x / (π * T * ℓ))
  refine (tsum_of_norm_bounded hG fun n ↦ ?_).trans ?_
  · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    by_cases hn : 2 ≤ n
    · have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
      set y : ℝ := x / n with hy
      have hy0 : 0 < y := div_pos hx0 hn0
      have hy1 : y < 1 := by rw [hy, div_lt_one hn0]; linarith
      have hb := norm_perronIntegral_lt_one_log hy0 hy1 hc0 hT
      have hlog : ℓ ≤ |Real.log y| := by
        rw [abs_of_neg (Real.log_neg hy0 hy1)]
        have e : Real.log y = -Real.log (n / x) := by
          rw [hy, ← Real.log_inv, inv_div]
        rw [e, neg_neg]
        exact Real.log_le_log (by positivity) (div_le_div_of_nonneg_right hn2 hx0.le)
      have hyc : y ^ c = x ^ c * (n : ℝ) ^ (-c) := by
        rw [hy, Real.div_rpow hx0.le hn0.le, Real.rpow_neg hn0.le, div_eq_mul_inv]
      have hΛ := ArithmeticFunction.vonMangoldt_nonneg (n := n)
      have e1 : y ^ c / (π * T * |Real.log y|) ≤ y ^ c / (π * T * ℓ) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) (by gcongr)
      have e2 : y ^ c / (π * T * ℓ) ≤ 3 * x / (π * T * ℓ) * (n : ℝ) ^ (-c) := by
        rw [hyc, div_mul_eq_mul_div]
        gcongr
      calc ArithmeticFunction.vonMangoldt n * ‖perronIntegral y c T‖ ≤
            ArithmeticFunction.vonMangoldt n * (3 * x / (π * T * ℓ) * (n : ℝ) ^ (-c)) :=
            mul_le_mul_of_nonneg_left (hb.trans (e1.trans e2)) hΛ
        _ = _ := by ring
    · have h0 : ArithmeticFunction.vonMangoldt n = 0 := by
        have : n = 0 ∨ n = 1 := by omega
        rcases this with rfl | rfl <;> simp
      rw [h0, zero_mul, zero_mul, mul_zero]
  · have e : 3 * x / (π * T * ℓ) * S ≤ 3 * x * K / (π * ℓ) / T := by
      calc 3 * x / (π * T * ℓ) * S ≤ 3 * x / (π * T * ℓ) * K :=
            mul_le_mul_of_nonneg_left hSK (by positivity)
        _ = _ := by field_simp
    exact e.trans (div_le_div_of_nonneg_right (by linarith) hT.le)

/-- The horizontal sides, uniformly in `x`. -/
lemma norm_integral_explicitIntegrand_horiz_unif :
    ∃ B : ℝ, 0 < B ∧ ∀ x : ℝ, 1 < x → ∀ c h δ U : ℝ, 1 < c → c ≤ 2 → 1 ≤ U → 2 ≤ |h| →
      0 < δ → δ ≤ 1 → (∀ ρ : ZeroIndex riemannXi, δ ≤ |ρ.val.im - h|) →
      ‖∫ σ : ℝ in -U..c, explicitIntegrand x (σ + h * I)‖ ≤
        B * (1 + 2 / Real.log x) * x ^ c * Real.log (|h| + 2) / (δ * |h| * Real.log x) := by
  obtain ⟨A₁, hA₁, h₁⟩ := norm_explicitIntegrand_horiz_near
  obtain ⟨A₂, hA₂, h₂⟩ := norm_explicitIntegrand_left
  refine ⟨A₁ + 2 * A₂, by positivity, fun x hx c h δ U hc1 hc2 hU hh hδ hδ1 hgood ↦ ?_⟩
  have hx0 : 0 < x := by linarith
  have hlx : 0 < Real.log x := Real.log_pos hx
  obtain ⟨K₂, hK₂, hK₂def⟩ : ∃ K₂ : ℝ, 0 < K₂ ∧ K₂ = 2 * A₂ * (1 + 2 / Real.log x) :=
    ⟨_, by positivity, rfl⟩
  have hAK : A₁ + K₂ ≤ (A₁ + 2 * A₂) * (1 + 2 / Real.log x) := by
    rw [hK₂def]
    have : 0 ≤ 2 / Real.log x := by positivity
    nlinarith
  have hh0 : 0 < |h| := by linarith
  have hL1 : 1 ≤ Real.log (|h| + 2) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    have := Real.exp_one_lt_d9; linarith
  have hcont := continuous_explicitIntegrand_horiz (h := h) hx0 (by linarith) fun ρ e ↦ by
    have := hgood ρ; rw [e, sub_self, abs_zero] at this; linarith
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := -1) (hcont.intervalIntegrable _ _)
    (hcont.intervalIntegrable _ _)]
  refine (norm_add_le _ _).trans ?_
  set L := Real.log (|h| + 2)
  -- the part `-U ≤ σ ≤ -1`
  have hfar : ‖∫ σ : ℝ in -U..(-1), explicitIntegrand x (σ + h * I)‖ ≤
      K₂ * L / (|h| * Real.log x) := by
    have hle : ∀ σ ∈ Ioc (-U) (-1), ‖explicitIntegrand x (σ + h * I)‖ ≤
        A₂ * (L + 2 / Real.log x) / |h| * x ^ (σ / 2) := by
      intro σ hσ
      have hσ1 : σ ≤ -1 := hσ.2
      have hre : ((σ : ℂ) + h * I).re = σ := by simp
      have him : ((σ : ℂ) + h * I).im = h := by simp
      have e := h₂ x hx0 (σ + h * I) (by rw [hre]; exact hσ1) (by rw [him]; exact abs_pos.mp hh0)
        (Or.inl (by rw [him]; linarith))
      rw [hre, him] at e
      have hk := norm_perronKernel_le_horiz hx0 σ h (abs_pos.mp hh0)
      have hlog : Real.log (|σ| + |h| + 2) ≤ L + |σ| := by
        have := log_add_le_log_add (a := |h| + 2) (b := |σ|) (by linarith) (abs_nonneg _)
        rw [show |h| + 2 + |σ| = |σ| + |h| + 2 by ring] at this
        exact this
      have h3 := abs_mul_rpow_le_small hx (by linarith : σ ≤ 0)
      have h4 : x ^ σ ≤ x ^ (σ / 2) :=
        Real.rpow_le_rpow_of_exponent_le hx.le (by linarith)
      have hxσ : 0 ≤ x ^ σ := by positivity
      have hL0 : 0 ≤ L := by linarith
      calc ‖explicitIntegrand x (σ + h * I)‖
          ≤ A₂ * Real.log (|σ| + |h| + 2) * ‖perronKernel x (σ + h * I)‖ := e
        _ ≤ A₂ * (L + |σ|) * (x ^ σ / |h|) := by gcongr
        _ = A₂ / |h| * (L * x ^ σ + |σ| * x ^ σ) := by field_simp
        _ ≤ A₂ / |h| * (L * x ^ (σ / 2) + 2 / Real.log x * x ^ (σ / 2)) := by gcongr
        _ = A₂ * (L + 2 / Real.log x) / |h| * x ^ (σ / 2) := by ring
    have hint := intervalIntegral.norm_integral_le_of_norm_le (by linarith : -U ≤ -1)
      (Eventually.of_forall fun σ hσ ↦ hle σ hσ)
      (Continuous.intervalIntegrable (μ := volume)
        (u := fun σ : ℝ ↦ A₂ * (L + 2 / Real.log x) / |h| * x ^ (σ / 2))
        (continuous_const.mul ((Real.continuous_const_rpow hx0.ne').comp
          (continuous_id.div_const 2))) _ _)
    refine hint.trans ?_
    rw [intervalIntegral.integral_const_mul]
    have hI := integral_rpow_half_le hx (-U) (-1)
    have hxh : x ^ ((-1 : ℝ) / 2) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx.le (by norm_num)
    have hI' : ∫ σ : ℝ in -U..(-1), x ^ (σ / 2) ≤ 2 / Real.log x :=
      hI.trans (div_le_div_of_nonneg_right (by linarith) hlx.le)
    have hk2 : 0 ≤ 2 / Real.log x := by positivity
    have hLk : L + 2 / Real.log x ≤ (1 + 2 / Real.log x) * L := by nlinarith
    calc A₂ * (L + 2 / Real.log x) / |h| * ∫ σ : ℝ in -U..(-1), x ^ (σ / 2)
        ≤ A₂ * (L + 2 / Real.log x) / |h| * (2 / Real.log x) := by gcongr
      _ ≤ A₂ * ((1 + 2 / Real.log x) * L) / |h| * (2 / Real.log x) := by gcongr
      _ = K₂ * L / (|h| * Real.log x) := by rw [hK₂def]; field_simp
  -- the part `-1 ≤ σ ≤ c`
  have hnear : ‖∫ σ : ℝ in (-1)..c, explicitIntegrand x (σ + h * I)‖ ≤
      A₁ * L / (δ * |h|) * (x ^ c / Real.log x) := by
    have hle : ∀ σ ∈ Ioc (-1) c, ‖explicitIntegrand x (σ + h * I)‖ ≤ A₁ * L / (δ * |h|) * x ^ σ := by
      intro σ hσ
      have := h₁ x hx0 σ h δ hσ.1.le (by linarith [hσ.2]) hh hδ hδ1 hgood
      calc _ ≤ _ := this
        _ = A₁ * L / (δ * |h|) * x ^ σ := by
          rw [show Real.log (|h| + 2) = L from rfl]; field_simp
    have hint := intervalIntegral.norm_integral_le_of_norm_le (by linarith : (-1 : ℝ) ≤ c)
      (Eventually.of_forall fun σ hσ ↦ hle σ hσ)
      (Continuous.intervalIntegrable (μ := volume) (u := fun σ : ℝ ↦ A₁ * L / (δ * |h|) * x ^ σ)
        (continuous_const.mul (Real.continuous_const_rpow hx0.ne')) _ _)
    refine hint.trans ?_
    rw [intervalIntegral.integral_const_mul, integral_rpow_const hx0 hx.ne']
    gcongr
    have : 0 ≤ x ^ (-1 : ℝ) := by positivity
    linarith
  have hxc : 1 ≤ x ^ c := Real.one_le_rpow hx.le (by linarith)
  have hL0 : 0 ≤ L := by linarith
  calc _ ≤ K₂ * L / (|h| * Real.log x) + A₁ * L / (δ * |h|) * (x ^ c / Real.log x) :=
        add_le_add hfar hnear
    _ ≤ K₂ * x ^ c * L / (δ * |h| * Real.log x) +
        A₁ * x ^ c * L / (δ * |h| * Real.log x) := by
        gcongr ?_ + ?_
        · rw [div_le_div_iff₀ (by positivity) (by positivity)]
          have h1 : K₂ * L * (δ * |h| * Real.log x) ≤ K₂ * L * (|h| * Real.log x) := by
            gcongr; nlinarith
          have h2 : K₂ * L * (|h| * Real.log x) ≤ K₂ * x ^ c * L * (|h| * Real.log x) := by
            have : 0 ≤ K₂ * L * (|h| * Real.log x) := by positivity
            nlinarith
          linarith
        · apply le_of_eq; field_simp
    _ = (A₁ + K₂) * x ^ c * L / (δ * |h| * Real.log x) := by ring
    _ ≤ (A₁ + 2 * A₂) * (1 + 2 / Real.log x) * x ^ c * L / (δ * |h| * Real.log x) := by
        gcongr

/-- The rectangle estimate, uniformly in `x`. -/
lemma norm_explicitJ_sub_main_le_unif :
    ∃ B : ℝ, 0 < B ∧ ∀ x : ℝ, 1 < x → ∀ c T δ : ℝ, 1 < c → c ≤ 2 → 2 ≤ T → 0 < δ → δ ≤ 1 →
      (∀ ρ : ZeroIndex riemannXi, δ ≤ |ρ.val.im - T| ∧ δ ≤ |ρ.val.im + T|) →
      ‖explicitJ x c T - explicitMain x T‖ ≤
        B * (1 + 2 / Real.log x) * x ^ c * Real.log (T + 2) / (δ * T * Real.log x) := by
  obtain ⟨B, hB, hH0⟩ := norm_integral_explicitIntegrand_horiz_unif
  obtain ⟨A, hA, hL⟩ := norm_integral_explicitIntegrand_left
  refine ⟨B, hB, fun x hx c T δ hc1 hc2 hT hδ hδ1 hgood ↦ ?_⟩
  have hH := hH0 x hx
  have hx0 : 0 < x := by linarith
  have hlx : 0 < Real.log x := Real.log_pos hx
  have hT0 : 0 < T := by linarith
  have hπ := Real.pi_pos
  have hTz : ∀ ρ : ZeroIndex riemannXi, |ρ.val.im| ≠ T := by
    intro ρ e
    rcases abs_eq hT0.le |>.mp e with e' | e'
    · have := (hgood ρ).1; rw [e', sub_self, abs_zero] at this; linarith
    · have := (hgood ρ).2; rw [e', neg_add_cancel, abs_zero] at this; linarith
  obtain ⟨Hb, hHb⟩ : ∃ Hb : ℝ,
      Hb = B * (1 + 2 / Real.log x) * x ^ c * Real.log (T + 2) / (δ * T * Real.log x) :=
    ⟨_, rfl⟩
  set R : ℕ → ℂ := fun K ↦ x - deriv riemannZeta 0 / riemannZeta 0 -
    ∑ ρ ∈ zerosBelow T, perronKernel x ρ.val -
    ∑ k ∈ Finset.range K, perronKernel x (-(2 * ((k : ℂ) + 1))) with hR
  obtain ⟨lb, hlb⟩ : ∃ lb : ℕ → ℝ, lb = fun K : ℕ ↦ 2 * T * (A * Real.log (2 * (K : ℝ) + 1 + T + 2) *
      (x ^ (-(2 * (K : ℝ) + 1)) / (2 * (K : ℝ) + 1))) := ⟨_, rfl⟩
  have hJ : (∫ y : ℝ in -T..T, explicitIntegrand x (c + y * I)) = 2 * π * explicitJ x c T := by
    have h2π : (2 * π : ℂ) ≠ 0 := mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
    rw [explicitJ, ← mul_assoc, mul_one_div_cancel h2π, one_mul]
  have hTa : 2 ≤ |T| := by rw [abs_of_pos hT0]; exact hT
  have hTb : 2 ≤ |-T| := by rw [abs_neg]; exact hTa
  have hgb : ∀ ρ : ZeroIndex riemannXi, δ ≤ |ρ.val.im - -T| := fun ρ ↦ by
    rw [sub_neg_eq_add]; exact (hgood ρ).2
  have hn : ‖(2 * π * I : ℂ)‖ = 2 * π := by
    rw [norm_mul, norm_mul, Complex.norm_I, Complex.norm_two, Complex.norm_real,
      Real.norm_of_nonneg hπ.le, mul_one]
  have hK : ∀ K : ℕ, ‖explicitJ x c T - R K‖ ≤ (2 * Hb + lb K) / (2 * π) := by
    intro K
    have hK0 : (0 : ℝ) ≤ K := K.cast_nonneg
    have hrect := Davenport.rectIntegral_explicitIntegrand hx0 hc1 hT0 hTz K
    unfold rectIntegral at hrect
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      add_zero, add_im, mul_im, zero_add] at hrect
    rw [hJ] at hrect
    have hbot := hH c (-T) δ (2 * K + 1) hc1 hc2 (by linarith) hTb hδ hδ1 hgb
    have htop := hH c T δ (2 * K + 1) hc1 hc2 (by linarith) hTa hδ hδ1 (fun ρ ↦ (hgood ρ).1)
    rw [abs_neg, abs_of_pos hT0, ← hHb] at hbot
    rw [abs_of_pos hT0, ← hHb] at htop
    have hlft := hL x hx0 K T hT0.le
    have hlb' : 2 * T * (A * Real.log (2 * K + 1 + T + 2) *
        (x ^ (-(2 * K + 1) : ℝ) / (2 * K + 1))) = lb K := by rw [hlb]
    rw [hlb'] at hlft
    generalize (∫ σ : ℝ in -(2 * K + 1)..c, explicitIntegrand x (σ + (-T : ℝ) * I)) = bot
      at hrect hbot
    generalize (∫ σ : ℝ in -(2 * K + 1)..c, explicitIntegrand x (σ + T * I)) = top at hrect htop
    generalize (∫ y : ℝ in -T..T, explicitIntegrand x (((-(2 * K + 1) : ℝ) : ℂ) + y * I)) = lft
      at hrect hlft
    have hrect' : bot - top + I * (2 * π * explicitJ x c T) - I * lft = 2 * π * I * R K := hrect
    have hid : (2 * π * I) * (explicitJ x c T - R K) = top - bot + I * lft := by
      linear_combination hrect'
    have h2 : ‖top - bot + I * lft‖ ≤ 2 * Hb + lb K := by
      calc ‖top - bot + I * lft‖ ≤ ‖top‖ + ‖bot‖ + ‖I * lft‖ :=
            (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
        _ ≤ Hb + Hb + lb K := by
            rw [norm_mul, Complex.norm_I, one_mul]
            exact add_le_add (add_le_add htop hbot) hlft
        _ = 2 * Hb + lb K := by ring
    have h3 : 2 * π * ‖explicitJ x c T - R K‖ ≤ 2 * Hb + lb K := by
      rw [← hn, ← norm_mul, hid]; exact h2
    rw [le_div_iff₀ (by positivity)]
    linarith
  have hRlim : Tendsto R atTop (𝓝 (explicitMain x T)) := by
    have := (tendsto_sum_trivial hx).const_sub (x - deriv riemannZeta 0 / riemannZeta 0 -
      ∑ ρ ∈ zerosBelow T, perronKernel x ρ.val)
    convert this using 1
    simp only [explicitMain]
    ring
  have hlim1 : Tendsto (fun K ↦ ‖explicitJ x c T - R K‖) atTop
      (𝓝 ‖explicitJ x c T - explicitMain x T‖) :=
    (tendsto_const_nhds.sub hRlim).norm
  have hlim2 : Tendsto (fun K ↦ (2 * Hb + lb K) / (2 * π)) atTop (𝓝 ((2 * Hb + 0) / (2 * π))) := by
    rw [hlb]
    exact (tendsto_const_nhds.add (tendsto_left_bound hx A T hA.le hT0.le)).div_const _
  have := le_of_tendsto_of_tendsto' hlim1 hlim2 hK
  refine this.trans ?_
  have hHb0 : 0 ≤ Hb := by
    have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ T + 2)
    have : 0 ≤ x ^ c := by positivity
    rw [hHb]; positivity
  rw [← hHb, add_zero, div_le_iff₀ (by positivity)]
  have := Real.pi_gt_three
  nlinarith

/-- The arithmetic of the constants: for `1 < x < 2` the constant of the explicit formula is at most
`A (1/log² x + 1/log(2/x))`. -/
lemma const_bound_small (K B A₉ A₇ : ℝ) (hK : 0 ≤ K) (hB : 0 < B) (h9 : 0 < A₉) (h7 : 0 < A₇) :
    ∃ A : ℝ, 0 < A ∧ ∀ x : ℝ, 1 < x → x < 2 →
      (3 * x * K / (π * Real.log (2 / x)) + 1) +
        9 * (B * (1 + 2 / Real.log x)) * x * (A₉ + 1) / Real.log x + 3 * A₇ * x ≤
      A * (1 / Real.log x ^ 2 + 1 / Real.log (2 / x)) := by
  have hπ := Real.pi_pos
  have hπ3 := Real.pi_gt_three
  refine ⟨6 * K + 1 + 54 * B * (A₉ + 1) + 6 * A₇, by positivity, fun x hx hx2 ↦ ?_⟩
  have hx0 : 0 < x := by linarith
  have hlx : 0 < Real.log x := Real.log_pos hx
  have hlx1 : Real.log x < 1 := by
    have := Real.log_two_lt_d9
    have h2 : Real.log x < Real.log 2 := Real.log_lt_log hx0 hx2
    linarith
  have hℓ : 0 < Real.log (2 / x) := Real.log_pos (by rw [one_lt_div hx0]; exact hx2)
  set ℓ := Real.log (2 / x) with hℓdef
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = 1 / Real.log x := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v : ℝ, v = 1 / ℓ := ⟨_, rfl⟩
  have hu1 : 1 ≤ u := by
    rw [hu, le_div_iff₀ hlx]; linarith
  have hv0 : 0 ≤ v := by rw [hv]; positivity
  have hu2 : 1 / Real.log x ^ 2 = u ^ 2 := by rw [hu, one_div_pow]
  have e2 : 2 / Real.log x = 2 * u := by rw [hu]; ring
  have e3 : ∀ w : ℝ, w / Real.log x = w * u := fun w ↦ by rw [hu]; ring
  have t1 : 3 * x * K / (π * ℓ) ≤ 6 * K * v := by
    rw [hv, show 6 * K * (1 / ℓ) = 6 * K / ℓ by ring, div_le_div_iff₀ (by positivity) hℓ]
    nlinarith [mul_nonneg (mul_nonneg hK hℓ.le) (by linarith : 0 ≤ 6 * π - 3 * x)]
  have t3 : 9 * (B * (1 + 2 / Real.log x)) * x * (A₉ + 1) / Real.log x ≤
      54 * B * (A₉ + 1) * u ^ 2 := by
    rw [e3, e2]
    have h3u : 1 + 2 * u ≤ 3 * u := by linarith
    calc 9 * (B * (1 + 2 * u)) * x * (A₉ + 1) * u
        ≤ 9 * (B * (3 * u)) * 2 * (A₉ + 1) * u := by gcongr
      _ = 54 * B * (A₉ + 1) * u ^ 2 := by ring
  have hu2' : 1 ≤ u ^ 2 := by nlinarith
  have t4 : 3 * A₇ * x ≤ 6 * A₇ * u ^ 2 := by nlinarith
  have p1 : 0 ≤ 6 * K * u ^ 2 := by positivity
  have p2 : 0 ≤ (1 + 54 * B * (A₉ + 1) + 6 * A₇) * v := by positivity
  rw [hu2, ← hv]
  nlinarith

set_option maxHeartbeats 1000000 in
/-- For `1 < x < 2` and `T ≥ 3`, `|ψ₀(x) - (x - ∑_{|γ|<T} x^ρ/ρ - ζ'(0)/ζ(0) - ½ log(1 - x^{-2}))|
≤ A (1/log² x + 1/log(2/x)) log²(xT)/T`, with `A` absolute. -/
lemma norm_psi0R_sub_explicitMain_le_unif :
    ∃ A : ℝ, 0 < A ∧ ∀ x : ℝ, 1 < x → x < 2 → ∀ T : ℝ, 3 ≤ T →
      ‖(psi0R x : ℂ) - explicitMain x T‖ ≤
        A * (1 / Real.log x ^ 2 + 1 / Real.log (2 / x)) * Real.log (x * T) ^ 2 / T := by
  obtain ⟨K, hK, h₁⟩ := norm_psi0R_sub_explicitJ_le_unif
  obtain ⟨B, hB, hJ⟩ := norm_explicitJ_sub_main_le_unif
  obtain ⟨A₉, hA₉, h₉⟩ := Davenport.exists_good_height
  obtain ⟨A₇, hA₇, h₇⟩ := norm_sum_zeros_strip_le
  obtain ⟨A, hA, hAb⟩ := const_bound_small K B A₉ A₇ hK hB hA₉ hA₇
  refine ⟨A, hA, fun x hx hx2 T hT3 ↦ ?_⟩
  have hπ := Real.pi_pos
  have hx0 : 0 < x := by linarith
  have hlx : 0 < Real.log x := Real.log_pos hx
  have hℓ : 0 < Real.log (2 / x) := Real.log_pos (by rw [one_lt_div hx0]; exact hx2)
  obtain ⟨C₁, hC₁, hC₁def⟩ : ∃ C₁ : ℝ, 0 < C₁ ∧ C₁ = 3 * x * K / (π * Real.log (2 / x)) + 1 :=
    ⟨_, add_pos_of_nonneg_of_pos (div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hx0.le) hK)
      (mul_pos hπ hℓ).le) one_pos, rfl⟩
  obtain ⟨Bx, hBx, hBxdef⟩ : ∃ Bx : ℝ, 0 < Bx ∧ Bx = B * (1 + 2 / Real.log x) :=
    ⟨_, by positivity, rfl⟩
  have hC := hAb x hx hx2
  rw [← hC₁def, ← hBxdef] at hC
  have hT : 2 ≤ T := by linarith
  have hT0 : 0 < T := by linarith
  set c := perronAbscissa x with hcdef
  have hc1 : 1 < c := one_lt_perronAbscissa hx.le
  have hc2 : c ≤ 2 := perronAbscissa_le_two hx.le
  have hxc : x ^ c ≤ 3 * x := rpow_perronAbscissa_le hx.le
  set Lm := Real.log (x * T) with hLmdef
  have hLm1 : 1 < Lm := by
    rw [hLmdef, Real.lt_log_iff_exp_lt (by positivity)]
    have := Real.exp_one_lt_d9
    nlinarith
  have hTLm : Real.log T ≤ Lm := Real.log_le_log hT0 (by nlinarith)
  have hlT : 0 < Real.log T := Real.log_pos (by linarith)
  obtain ⟨T', hT', hgood⟩ := h₉ T hT
  have hT'0 : 0 < T' := by linarith [hT'.1]
  have hT'2 : 2 ≤ T' := by linarith [hT'.1]
  set δ := min (1 / (A₉ * Real.log T)) 1 with hδdef
  have hδ0 : 0 < δ := lt_min (by positivity) one_pos
  have hδ1 : δ ≤ 1 := min_le_right _ _
  have hinvδ : 1 / δ ≤ A₉ * Real.log T + 1 := by
    rcases le_total (1 / (A₉ * Real.log T)) 1 with h | h
    · rw [hδdef, min_eq_left h, one_div_one_div]; linarith
    · rw [hδdef, min_eq_right h]; have : 0 ≤ A₉ * Real.log T := by positivity
      linarith
  have hgood' : ∀ ρ : ZeroIndex riemannXi, δ ≤ |ρ.val.im - T'| ∧ δ ≤ |ρ.val.im + T'| :=
    fun ρ ↦ ⟨(min_le_left _ _).trans (hgood ρ).1, (min_le_left _ _).trans (hgood ρ).2⟩
  have e1 := h₁ x hx hx2 T' hT'0
  rw [← hC₁def] at e1
  have e2 := hJ x hx c T' δ hc1 hc2 hT'2 hδ0 hδ1 hgood'
  rw [← hBxdef] at e2
  have e3 := h₇ x hx.le T T' hT hT'.1 hT'.2
  have hsplit : (psi0R x : ℂ) - explicitMain x T =
      ((psi0R x : ℂ) - explicitJ x c T') + (explicitJ x c T' - explicitMain x T') -
        (∑ ρ ∈ zerosBelow T', perronKernel x ρ.val - ∑ ρ ∈ zerosBelow T, perronKernel x ρ.val) := by
    simp only [explicitMain]; ring
  rw [hsplit]
  refine (norm_sub_le _ _).trans ((add_le_add (norm_add_le _ _) le_rfl).trans ?_)
  have hLm2 : 1 ≤ Lm ^ 2 := by nlinarith
  have b1 : ‖(psi0R x : ℂ) - explicitJ x c T'‖ ≤ C₁ * Lm ^ 2 / T := by
    refine e1.trans ?_
    calc C₁ / T' ≤ C₁ / T := div_le_div_of_nonneg_left hC₁.le hT0 hT'.1
      _ ≤ C₁ * Lm ^ 2 / T := div_le_div_of_nonneg_right (by nlinarith) hT0.le
  have b2 : ‖explicitJ x c T' - explicitMain x T'‖ ≤
      9 * Bx * x * (A₉ + 1) / Real.log x * Lm ^ 2 / T := by
    refine e2.trans ?_
    have hlog3 := log_add_three_le hT
    have hq : Real.log (T' + 2) ≤ 3 * Lm := by
      have : Real.log (T' + 2) ≤ Real.log (T + 3) :=
        Real.log_le_log (by linarith) (by linarith [hT'.2])
      linarith
    have hq0 : 0 ≤ Real.log (T' + 2) := Real.log_nonneg (by linarith)
    have hA : 1 ≤ δ * ((A₉ + 1) * Lm) := by
      have h1 : 1 ≤ δ * (A₉ * Real.log T + 1) := by
        have := (div_le_iff₀ hδ0).mp hinvδ; linarith
      have h2 : A₉ * Real.log T + 1 ≤ (A₉ + 1) * Lm := by nlinarith
      nlinarith
    have e : 9 * Bx * x * (A₉ + 1) / Real.log x * Lm ^ 2 / T =
        9 * Bx * x * (A₉ + 1) * Lm ^ 2 / (T * Real.log x) := by field_simp
    rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
    have hx3 : 0 ≤ Bx * (3 * x) * (3 * Lm) := by positivity
    calc Bx * x ^ c * Real.log (T' + 2) * (T * Real.log x)
        ≤ Bx * (3 * x) * (3 * Lm) * (T * Real.log x) := by gcongr
      _ ≤ Bx * (3 * x) * (3 * Lm) * ((δ * ((A₉ + 1) * Lm)) * T' * Real.log x) := by
          apply mul_le_mul_of_nonneg_left _ hx3
          have h1 : T ≤ T' := hT'.1
          have h2 : T' ≤ T' * (δ * ((A₉ + 1) * Lm)) := le_mul_of_one_le_right hT'0.le hA
          have : T ≤ (δ * ((A₉ + 1) * Lm)) * T' := by linarith
          exact mul_le_mul_of_nonneg_right this hlx.le
      _ = 9 * Bx * x * (A₉ + 1) * Lm ^ 2 * (δ * T' * Real.log x) := by ring
  have b3 : ‖∑ ρ ∈ zerosBelow T', perronKernel x ρ.val - ∑ ρ ∈ zerosBelow T, perronKernel x ρ.val‖ ≤
      3 * A₇ * x * Lm ^ 2 / T := by
    refine e3.trans ?_
    apply div_le_div_of_nonneg_right _ hT0.le
    have hlog3 := log_add_three_le hT
    have hLm2' : Lm ≤ Lm ^ 2 := by nlinarith
    have h1 : Real.log (T + 3) ≤ 3 * Lm ^ 2 := by linarith
    have h2 : 0 ≤ A₇ * x := by positivity
    have h3 := mul_le_mul_of_nonneg_left h1 h2
    linarith
  have := add_le_add (add_le_add b1 b2) b3
  refine this.trans ?_
  calc C₁ * Lm ^ 2 / T + 9 * Bx * x * (A₉ + 1) / Real.log x * Lm ^ 2 / T +
        3 * A₇ * x * Lm ^ 2 / T
      = (C₁ + 9 * Bx * x * (A₉ + 1) / Real.log x + 3 * A₇ * x) * Lm ^ 2 / T := by ring
    _ ≤ A * (1 / Real.log x ^ 2 + 1 / Real.log (2 / x)) * Lm ^ 2 / T :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hC (sq_nonneg _)) hT0.le

/-- **Davenport, Ch. 17, p. 110 (row 17-16)**: the truncated explicit formula for `1 < x < 2`, with
an absolute constant: `|ψ₀(x) - (x - ∑_{|γ|<T} x^ρ/ρ - ζ'(0)/ζ(0) - ½ log(1 - x^{-2}))| ≤
A (1/log² x + 1/log(2/x)) log² T / T` for `T ≥ 3`. -/
@[kb "davenport1980" "Ch 17, p. 110"]
theorem Davenport.explicit_formula_psi0_lt_two :
    ∃ A : ℝ, 0 < A ∧ ∀ x : ℝ, 1 < x → x < 2 → ∀ T : ℝ, 3 ≤ T →
      ‖(psi0R x : ℂ) - explicitMain x T‖ ≤
        A * (1 / Real.log x ^ 2 + 1 / Real.log (2 / x)) * Real.log T ^ 2 / T := by
  obtain ⟨A, hA, h⟩ := norm_psi0R_sub_explicitMain_le_unif
  refine ⟨4 * A, by positivity, fun x hx hx2 T hT ↦ ?_⟩
  have hx0 : 0 < x := by linarith
  have hT0 : 0 < T := by linarith
  have hlx : 0 < Real.log x := Real.log_pos hx
  have hℓ : 0 < Real.log (2 / x) := Real.log_pos (by rw [one_lt_div hx0]; exact hx2)
  have hQ : 0 ≤ A * (1 / Real.log x ^ 2 + 1 / Real.log (2 / x)) :=
    mul_nonneg hA.le (add_nonneg (by positivity) (one_div_nonneg.2 hℓ.le))
  have hlog2 : Real.log x ≤ Real.log T := by
    have h3 : Real.log 3 ≤ Real.log T := Real.log_le_log (by norm_num) hT
    have h2 : Real.log x ≤ Real.log 2 := Real.log_le_log hx0 hx2.le
    have h23 : Real.log 2 ≤ Real.log 3 := Real.log_le_log (by norm_num) (by norm_num)
    linarith
  have hΛ : Real.log (x * T) ^ 2 ≤ 4 * Real.log T ^ 2 := by
    rw [Real.log_mul hx0.ne' hT0.ne']
    have : 0 ≤ Real.log x := hlx.le
    nlinarith
  calc _ ≤ A * (1 / Real.log x ^ 2 + 1 / Real.log (2 / x)) * Real.log (x * T) ^ 2 / T :=
        h x hx hx2 T hT
    _ ≤ A * (1 / Real.log x ^ 2 + 1 / Real.log (2 / x)) * (4 * Real.log T ^ 2) / T :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hΛ hQ) hT0.le
    _ = _ := by ring

/-- A bound on the error uniform on a set `s` with a null majorant gives uniform convergence. -/
lemma tendstoUniformlyOn_of_bound (s : Set ℝ) (g : ℝ → ℝ) (hg : Tendsto g atTop (𝓝 0))
    (h : ∀ᶠ T in atTop, ∀ x ∈ s, ‖(psi0R x : ℂ) - explicitMain x T‖ ≤ g T) :
    TendstoUniformlyOn (fun T x ↦ explicitMain x T) (fun x ↦ (psi0R x : ℂ)) atTop s := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [h, hg.eventually (gt_mem_nhds hε)] with T h1 h2 x hx
  rw [dist_eq_norm]
  exact lt_of_le_of_lt (h1 x hx) h2

/-- `log² T / T → 0`. -/
lemma tendsto_log_sq_div_id :
    Tendsto (fun T : ℝ ↦ Real.log T ^ 2 / T) atTop (𝓝 0) := by
  simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero

/-- Uniform convergence on `[a, b] ⊂ (1, 2)`. -/
lemma tendstoUniformlyOn_explicitMain_lt_two {a b : ℝ} (ha : 1 < a) (hb : b < 2) :
    TendstoUniformlyOn (fun T x ↦ explicitMain x T) (fun x ↦ (psi0R x : ℂ)) atTop (Icc a b) := by
  by_cases hab : a ≤ b
  swap
  · refine tendstoUniformlyOn_of_bound _ (fun _ ↦ 0) tendsto_const_nhds
      (Eventually.of_forall fun T x hx ↦ ?_)
    exact absurd (hx.1.trans hx.2) hab
  obtain ⟨A, hA, h⟩ := Davenport.explicit_formula_psi0_lt_two
  have ha0 : 0 < a := by linarith
  have hla : 0 < Real.log a := Real.log_pos ha
  have hb0 : 0 < b := by linarith
  have hℓb : 0 < Real.log (2 / b) := Real.log_pos (by rw [one_lt_div hb0]; exact hb)
  set Q := 1 / Real.log a ^ 2 + 1 / Real.log (2 / b) with hQ
  have hQ0 : 0 ≤ Q := by positivity
  refine tendstoUniformlyOn_of_bound _ (fun T ↦ A * Q * (Real.log T ^ 2 / T))
    (by simpa using tendsto_log_sq_div_id.const_mul (A * Q)) ?_
  filter_upwards [eventually_ge_atTop (3 : ℝ)] with T hT x hx
  have hx1 : a ≤ x := hx.1
  have hx2 : x ≤ b := hx.2
  have hx0 : 0 < x := by linarith
  have hlx : Real.log a ≤ Real.log x := Real.log_le_log ha0 hx1
  have hT0 : 0 < T := by linarith
  have e := h x (by linarith) (by linarith) T hT
  refine e.trans ?_
  rw [← mul_div_assoc]
  have h1 : 1 / Real.log x ^ 2 ≤ 1 / Real.log a ^ 2 :=
    one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hla.le hlx 2)
  have h2 : 1 / Real.log (2 / x) ≤ 1 / Real.log (2 / b) := by
    apply one_div_le_one_div_of_le hℓb
    exact Real.log_le_log (by positivity) (div_le_div_of_nonneg_left (by norm_num) hx0 hx2)
  have hLT : 0 ≤ Real.log T ^ 2 := sq_nonneg _
  have : A * (1 / Real.log x ^ 2 + 1 / Real.log (2 / x)) ≤ A * Q :=
    mul_le_mul_of_nonneg_left (add_le_add h1 h2) hA.le
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right this hLT) hT0.le

/-- For finitely many positive reals there is a positive lower bound. -/
lemma exists_pos_le_finset {ι : Type*} (F : Finset ι) (m : ι → ℝ) (hm : ∀ n ∈ F, 0 < m n) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ n ∈ F, δ ≤ m n := by
  classical
  induction F using Finset.induction_on with
  | empty => exact ⟨1, one_pos, by simp⟩
  | insert a s ha ih =>
    obtain ⟨δ, hδ, h⟩ := ih fun n hn ↦ hm n (Finset.mem_insert_of_mem hn)
    refine ⟨min δ (m a), lt_min hδ (hm a (Finset.mem_insert_self _ _)), fun n hn ↦ ?_⟩
    rcases Finset.mem_insert.mp hn with rfl | hn
    · exact min_le_right _ _
    · exact (min_le_left _ _).trans (h n hn)

/-- On `[a, b]` free of prime powers (`a > 2`), `⟨x⟩` is bounded below. -/
lemma exists_distPrimePow_ge {a b : ℝ} (ha : 2 < a) (hab : a ≤ b)
    (hpp : ∀ n : ℕ, IsPrimePow n → (n : ℝ) ∉ Icc a b) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ Icc a b, δ ≤ distPrimePow x := by
  classical
  have hne : (Icc a b).Nonempty := ⟨a, left_mem_Icc.2 hab⟩
  obtain ⟨δ, hδ, hF⟩ := exists_pos_le_finset
    ((Finset.range (⌈b⌉₊ + 2)).filter IsPrimePow) (fun n ↦ Metric.infDist (n : ℝ) (Icc a b))
    (fun n hn ↦ by
      have := (Finset.mem_filter.mp hn).2
      exact (isClosed_Icc.notMem_iff_infDist_pos hne).1 (hpp n this))
  refine ⟨min δ 1, lt_min hδ one_pos, fun x hx ↦ ?_⟩
  unfold distPrimePow
  have hne2 : ((fun n : ℕ ↦ |x - n|) '' {n : ℕ | IsPrimePow n ∧ (n : ℝ) ≠ x}).Nonempty :=
    ⟨_, 2, ⟨Nat.prime_two.isPrimePow, by intro h; have := hx.1; rw [← h] at this; push_cast at this; linarith⟩, rfl⟩
  refine le_csInf hne2 ?_
  rintro _ ⟨n, ⟨hn, hnx⟩, rfl⟩
  show min δ 1 ≤ |x - (n : ℝ)|
  by_cases hlt : n < ⌈b⌉₊ + 2
  · have h1 := hF n (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hlt, hn⟩)
    have h2 : Metric.infDist (n : ℝ) (Icc a b) ≤ dist (n : ℝ) x :=
      Metric.infDist_le_dist_of_mem hx
    rw [Real.dist_eq, abs_sub_comm] at h2
    exact (min_le_left _ _).trans (h1.trans h2)
  · have h3 : (⌈b⌉₊ : ℝ) + 2 ≤ n := by exact_mod_cast not_lt.mp hlt
    have h4 : b ≤ ⌈b⌉₊ := Nat.le_ceil b
    have h5 : |x - n| = n - x := by rw [abs_sub_comm, abs_of_nonneg (by linarith [hx.2])]
    rw [h5]
    refine (min_le_right _ _).trans ?_
    linarith [hx.2]

/-- Uniform convergence on `[a, b] ⊂ (2, ∞)` free of prime powers. -/
lemma tendstoUniformlyOn_explicitMain_gt_two {a b : ℝ} (ha : 2 < a)
    (hpp : ∀ n : ℕ, IsPrimePow n → (n : ℝ) ∉ Icc a b) :
    TendstoUniformlyOn (fun T x ↦ explicitMain x T) (fun x ↦ (psi0R x : ℂ)) atTop (Icc a b) := by
  by_cases hab : a ≤ b
  swap
  · refine tendstoUniformlyOn_of_bound _ (fun _ ↦ 0) tendsto_const_nhds
      (Eventually.of_forall fun T x hx ↦ ?_)
    exact absurd (hx.1.trans hx.2) hab
  obtain ⟨A, hA, h⟩ := Davenport.explicit_formula_psi0_real
  obtain ⟨δ, hδ, hd⟩ := exists_distPrimePow_ge ha hab hpp
  have hb0 : 0 < b := by linarith
  have hlb : 0 ≤ Real.log b := Real.log_nonneg (by linarith)
  have hlim : Tendsto (fun T : ℝ ↦ A * (b * (Real.log (b * T) ^ 2 / T) +
      Real.log b * b / δ * (1 / T))) atTop (𝓝 0) := by
    have h3 : Tendsto (fun T : ℝ ↦ 1 / T) atTop (𝓝 0) := by
      simpa using tendsto_inv_atTop_zero (𝕜 := ℝ)
    have := (((tendsto_log_sq_div_small hb0).const_mul b).add
      (h3.const_mul (Real.log b * b / δ))).const_mul A
    simpa using this
  refine tendstoUniformlyOn_of_bound _ _ hlim ?_
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with T hT x hx
  have hx1 : a ≤ x := hx.1
  have hx2 : x ≤ b := hx.2
  have hx0 : 0 < x := by linarith
  have hT0 : 0 < T := by linarith
  have e := h x (by linarith) T hT
  refine e.trans ?_
  have hd' := hd x hx
  have hdpos : δ ≤ distPrimePow x := hd'
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hlxb : Real.log x ≤ Real.log b := Real.log_le_log hx0 hx2
  have hxT : 0 ≤ Real.log (x * T) := Real.log_nonneg (by nlinarith)
  have hxTb : Real.log (x * T) ≤ Real.log (b * T) :=
    Real.log_le_log (by positivity) (by nlinarith)
  have s1 : x * Real.log (x * T) ^ 2 / T ≤ b * (Real.log (b * T) ^ 2 / T) := by
    calc x * Real.log (x * T) ^ 2 / T ≤ b * Real.log (b * T) ^ 2 / T :=
          div_le_div_of_nonneg_right
            (mul_le_mul hx2 (pow_le_pow_left₀ hxT hxTb 2) (sq_nonneg _) hb0.le) hT0.le
      _ = b * (Real.log (b * T) ^ 2 / T) := by ring
  have s2 : Real.log x * min 1 (x / (T * distPrimePow x)) ≤
      Real.log b * b / δ * (1 / T) := by
    have m1 : min 1 (x / (T * distPrimePow x)) ≤ b / δ * (1 / T) := by
      refine (min_le_right _ _).trans ?_
      rw [show b / δ * (1 / T) = b / (T * δ) by field_simp]
      exact div_le_div₀ hb0.le hx2 (by positivity) (by gcongr)
    calc Real.log x * min 1 (x / (T * distPrimePow x)) ≤ Real.log b * (b / δ * (1 / T)) :=
          mul_le_mul hlxb m1 (le_min zero_le_one (div_nonneg hx0.le (mul_nonneg hT0.le (hδ.le.trans hdpos)))) hlb
      _ = _ := by ring
  have : x * Real.log (x * T) ^ 2 / T + Real.log x * min 1 (x / (T * distPrimePow x)) ≤
      b * (Real.log (b * T) ^ 2 / T) + Real.log b * b / δ * (1 / T) := add_le_add s1 s2
  exact mul_le_mul_of_nonneg_left this hA.le

/-- **Davenport, Ch. 17, p. 109 (row 17-17)**, first half: on a closed interval `[a, b]`, `a > 1`,
containing no prime power, `x - ∑_{|γ|<T} x^ρ/ρ - ζ'(0)/ζ(0) - ½ log(1 - x^{-2}) → ψ₀(x)` uniformly
as `T → ∞`. -/
@[kb "davenport1980" "Ch 17, p. 109"]
theorem Davenport.tendstoUniformlyOn_explicitMain {a b : ℝ} (ha : 1 < a)
    (hpp : ∀ n : ℕ, IsPrimePow n → (n : ℝ) ∉ Icc a b) :
    TendstoUniformlyOn (fun T x ↦ explicitMain x T) (fun x ↦ (psi0R x : ℂ)) atTop (Icc a b) := by
  by_cases hab : a ≤ b
  swap
  · refine tendstoUniformlyOn_of_bound _ (fun _ ↦ 0) tendsto_const_nhds
      (Eventually.of_forall fun T x hx ↦ ?_)
    exact absurd (hx.1.trans hx.2) hab
  have h2 := hpp 2 Nat.prime_two.isPrimePow
  push_cast at h2
  by_cases hb : b < 2
  · exact tendstoUniformlyOn_explicitMain_lt_two ha hb
  · have ha2 : 2 < a := by
      by_contra hc
      exact h2 ⟨by linarith, by linarith⟩
    exact tendstoUniformlyOn_explicitMain_gt_two ha2 hpp

/-- `ψ₀(x) = ∑_{k ≤ n} Λ(k)` for `n < x < n + 1`. -/
lemma psi0R_of_between {n : ℕ} {x : ℝ} (h1 : (n : ℝ) < x) (h2 : x < n + 1) :
    psi0R x = ∑ k ∈ Finset.range (n + 1), Λ k := by
  have hx0 : 0 ≤ x := by have : (0 : ℝ) ≤ n := n.cast_nonneg
                         linarith
  have hf : ⌊x⌋₊ = n := by
    rw [Nat.floor_eq_iff hx0]; exact ⟨h1.le, h2⟩
  unfold psi0R
  rw [hf]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  have hk' : (k : ℝ) < x := lt_of_le_of_lt (by exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)) h1
  simp [perronStepR, hk']

/-- `ψ₀(n) = ∑_{k < n} Λ(k) + Λ(n)/2`. -/
lemma psi0R_natCast' (n : ℕ) :
    psi0R (n : ℝ) = ∑ k ∈ Finset.range n, Λ k + Λ n / 2 := by
  unfold psi0R
  rw [Nat.floor_natCast, Finset.sum_range_succ]
  congr 1
  · refine Finset.sum_congr rfl fun k hk ↦ ?_
    have hk' : (k : ℝ) < n := by exact_mod_cast Finset.mem_range.mp hk
    simp [perronStepR, hk']
  · simp [perronStepR]
    ring

/-- `x ↦ explicitMain x T` is continuous at every `x > 1`. -/
lemma continuousAt_explicitMain {x₀ : ℝ} (hx : 1 < x₀) (T : ℝ) :
    ContinuousAt (fun x : ℝ ↦ explicitMain x T) x₀ := by
  have hx0 : 0 < x₀ := by linarith
  have hslit : (x₀ : ℂ) ∈ Complex.slitPlane := Complex.ofReal_mem_slitPlane.2 hx0
  unfold explicitMain
  refine ContinuousAt.sub (ContinuousAt.sub (ContinuousAt.sub
    Complex.continuous_ofReal.continuousAt ?_) continuousAt_const) ?_
  · refine (tendsto_finsetSum _ fun ρ _ ↦ ?_)
    unfold perronKernel
    have h1 : ContinuousAt (fun x : ℝ ↦ (x : ℂ) ^ ρ.val) x₀ :=
      continuousAt_ofReal_cpow_const x₀ ρ.val (Or.inr hx0.ne')
    exact h1.div_const _
  · refine Complex.continuous_ofReal.continuousAt.comp ?_
    refine ContinuousAt.mul continuousAt_const ?_
    have hpos : 0 < 1 - x₀ ^ (-2 : ℝ) := by
      have : x₀ ^ (-2 : ℝ) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hx (by norm_num)
      linarith
    refine ContinuousAt.log (ContinuousAt.sub continuousAt_const ?_) hpos.ne'
    exact (Real.continuousAt_rpow_const _ _ (Or.inl hx0.ne'))

/-- **Davenport, Ch. 17, p. 109 (row 17-17)**, second half: the convergence is not uniform on any
set `U` containing a right neighbourhood `[n, n + ε)` of a prime power `n` (in particular on no
interval containing `n`). -/
@[kb "davenport1980" "Ch 17, p. 109"]
theorem Davenport.not_tendstoUniformlyOn_explicitMain {n : ℕ} (hn : IsPrimePow n) {U : Set ℝ}
    (hU : U ∈ 𝓝[≥] (n : ℝ)) :
    ¬ TendstoUniformlyOn (fun T x ↦ explicitMain x T) (fun x ↦ (psi0R x : ℂ)) atTop U := by
  intro H
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn.two_le
  have hΛ : 0 < Λ n := ArithmeticFunction.vonMangoldt_pos_iff.mpr hn
  have hnU : (n : ℝ) ∈ U := mem_of_mem_nhdsWithin self_mem_Ici hU
  set V : Set ℝ := U ∩ Icc (n : ℝ) (n + 1 / 2) ∩ Ioi 1 with hV
  have hVmem : V ∈ 𝓝[≥] (n : ℝ) := by
    refine inter_mem (inter_mem hU (Icc_mem_nhdsGE (by linarith))) ?_
    exact mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (by linarith))
  have hVU : V ⊆ U := fun x hx ↦ hx.1.1
  have hH := H.mono hVU
  have hcont : ∀ T : ℝ, ContinuousOn (fun x ↦ explicitMain x T) V := fun T x hx ↦
    (continuousAt_explicitMain hx.2 T).continuousWithinAt
  have hf := hH.continuousOn (Eventually.of_forall hcont).frequently
  have hnV : (n : ℝ) ∈ V := mem_of_mem_nhdsWithin self_mem_Ici hVmem
  have hcw : ContinuousWithinAt (fun x : ℝ ↦ (psi0R x : ℂ)) V n := hf.continuousWithinAt hnV
  have hVgt : V ∈ 𝓝[>] (n : ℝ) := nhdsWithin_mono _ Ioi_subset_Ici_self hVmem
  have hT1 : Tendsto (fun x : ℝ ↦ (psi0R x : ℂ)) (𝓝[>] (n : ℝ)) (𝓝 (psi0R n : ℂ)) :=
    hcw.mono_of_mem_nhdsWithin hVgt
  have hT2 : Tendsto (fun x : ℝ ↦ (psi0R x : ℂ)) (𝓝[>] (n : ℝ))
      (𝓝 ((∑ k ∈ Finset.range (n + 1), Λ k : ℝ) : ℂ)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT (show (n : ℝ) < n + 1 by linarith)] with x hx
    rw [psi0R_of_between hx.1 hx.2]
  have := tendsto_nhds_unique hT1 hT2
  have h3 : psi0R (n : ℝ) = ∑ k ∈ Finset.range (n + 1), Λ k := by exact_mod_cast this
  rw [psi0R_natCast', Finset.sum_range_succ] at h3
  linarith

end NTKB
