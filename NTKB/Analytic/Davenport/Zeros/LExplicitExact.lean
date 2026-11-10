/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Davenport.Zeros.LLeftStrip
import NTKB.Analytic.Davenport.Zeros.LExplicitPsi

/-!
# The explicit formula for `ψ₀(x, χ)`, with the trivial zeros

**Davenport, Ch. 19, pp. 115-117 (rows 19-2, 19-3, 19-6).** For `χ` primitive mod `q > 1` with
parity `a`, integers `N ≥ 3` and `T ≥ 2`, with `ℓ = log q + log N + log T`:
`ψ₀(N, χ) = r₀ - ∑_{|γ|<T} N^ρ/ρ + ∑_{m ≥ 1} N^{a-2m}/(2m - a) + O(N ℓ²/T)`
(`Davenport.explicit_formula_psi0L_exact`), where `r₀ = -L'/L(0, χ)` for odd `χ` and
`r₀ = -log N - b(χ)` for even `χ`; letting `T → ∞`,
`ψ₀(N, χ) = r₀ - lim_{T → ∞} ∑_{|γ|<T} N^ρ/ρ + ∑_{m ≥ 1} N^{a-2m}/(2m - a)`
(`Davenport.tendsto_sum_L_zeros`), which is (2) for odd `χ` and (3) for even `χ`. The contour is
moved to `σ = -∞` in `LLeftStrip`.
-/

open Filter Topology Complex Set DirichletCharacter
open scoped Real

namespace NTKB

/-- **Davenport, Ch. 19, pp. 116-117**: for primitive `χ` mod `q > 1`, `x ≥ 2`, `1 < c ≤ 2`,
`T ≥ 2` at distance `≥ δ` from all `±γ`,
`|J(x, T, χ) - (r₀ - ∑_{|γ|<T} x^ρ/ρ + ∑_m x^{a-2m}/(2m-a))| ≤
B (log q + log(T + 2) + 3) (x^c/(δ T log x) + x^{-1/4}/(T log x))`. -/
@[kb "davenport1980" "Ch 19, p. 117"]
theorem Davenport.norm_explicitJL_sub_main_exact_le :
    ∃ B : ℝ, 0 < B ∧ ∀ {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive)
      (hN : N ≠ 1), ∀ x : ℝ, 2 ≤ x → ∀ c T δ : ℝ, 1 < c → c ≤ 2 → 2 ≤ T → 0 < δ → δ ≤ 1 →
      (∀ ρ : ZeroIndex (dirichletXi χ), δ ≤ |ρ.val.im - T| ∧ δ ≤ |ρ.val.im + T|) →
      ‖explicitJL χ x c T - (residueZeroL χ x - ∑ ρ ∈ zerosBelowL hχ hN T, perronKernel x ρ.val +
          trivialSumL χ x)‖ ≤
        B * (Real.log N + Real.log (T + 2) + 3) *
          (x ^ c / (δ * T * Real.log x) + x ^ (-1 / 4 : ℝ) / (T * Real.log x)) := by
  obtain ⟨A₁, hA₁, hH⟩ := norm_integral_explicitIntegrandL_horiz
  obtain ⟨A₂, hA₂, hL⟩ := Davenport.norm_left_integral_sub_trivialSumL_le
  refine ⟨A₁ + A₂, by positivity, ?_⟩
  intro N _ χ hχ hN x hx c T δ hc1 hc2 hT hδ hδ1 hgood
  have hx0 : 0 < x := by linarith
  have hlx : 0 < Real.log x := Real.log_pos (by linarith)
  have hT0 : 0 < T := by linarith
  have hπ := Real.pi_pos
  have hTz : ∀ ρ : ZeroIndex (dirichletXi χ), |ρ.val.im| ≠ T := by
    intro ρ e
    rcases abs_eq hT0.le |>.mp e with e' | e'
    · have := (hgood ρ).1; rw [e', sub_self, abs_zero] at this; linarith
    · have := (hgood ρ).2; rw [e', neg_add_cancel, abs_zero] at this; linarith
  set R := residueZeroL χ x - ∑ ρ ∈ zerosBelowL hχ hN T, perronKernel x ρ.val with hR
  set S := trivialSumL χ x with hS
  have hrect := Davenport.rectIntegral_explicitIntegrandL hχ hN hx0 hc1 hT0 hTz
  unfold rectIntegral at hrect
  simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
    add_zero, add_im, mul_im, zero_add] at hrect
  have hJ : (∫ y : ℝ in -T..T, explicitIntegrandL χ x (c + y * I)) = 2 * π * explicitJL χ x c T := by
    have h2π : (2 * π : ℂ) ≠ 0 := mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
    rw [explicitJL, ← mul_assoc, mul_one_div_cancel h2π, one_mul]
  rw [hJ] at hrect
  have hTa : 2 ≤ |T| := by rw [abs_of_pos hT0]; exact hT
  have hTb : 2 ≤ |-T| := by rw [abs_neg]; exact hTa
  have hgb : ∀ ρ : ZeroIndex (dirichletXi χ), δ ≤ |ρ.val.im - -T| := fun ρ ↦ by
    rw [sub_neg_eq_add]; exact (hgood ρ).2
  have hbot := hH hχ hN x hx c (-T) δ hc1 hc2 hTb hδ hδ1 hgb
  have htop := hH hχ hN x hx c T δ hc1 hc2 hTa hδ hδ1 (fun ρ ↦ (hgood ρ).1)
  rw [abs_neg, abs_of_pos hT0] at hbot
  rw [abs_of_pos hT0] at htop
  have hlft := hL hχ hN x hx T hT
  rw [← hS] at hlft
  generalize (∫ σ : ℝ in (-1 / 2)..c, explicitIntegrandL χ x (σ + (-T : ℝ) * I)) = bot
    at hrect hbot
  generalize (∫ σ : ℝ in (-1 / 2)..c, explicitIntegrandL χ x (σ + T * I)) = top at hrect htop
  generalize (∫ y : ℝ in -T..T, explicitIntegrandL χ x (((-1 / 2 : ℝ) : ℂ) + y * I)) = lft
    at hrect hlft
  have hid : (2 * π * I) * (explicitJL χ x c T - (R + S)) =
      top - bot + (I * lft - 2 * π * I * S) := by
    rw [hR]; linear_combination hrect
  have hn : ‖(2 * π * I : ℂ)‖ = 2 * π := by
    rw [norm_mul, norm_mul, Complex.norm_I, Complex.norm_two, Complex.norm_real,
      Real.norm_of_nonneg hπ.le, mul_one]
  set Lg := Real.log N + Real.log (T + 2)
  have hLg : 0 ≤ Lg := by
    have := Real.log_natCast_nonneg N
    have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ T + 2); linarith
  set X := x ^ c / (δ * T * Real.log x) with hX
  set Y := x ^ (-1 / 4 : ℝ) / (T * Real.log x) with hY
  have hX0 : 0 ≤ X := by positivity
  have hY0 : 0 ≤ Y := by positivity
  have htop' : ‖top‖ ≤ A₁ * Lg * X := by
    refine htop.trans (le_of_eq ?_); simp only [hX]; ring
  have hbot' : ‖bot‖ ≤ A₁ * Lg * X := by
    refine hbot.trans (le_of_eq ?_); simp only [hX]; ring
  have hlft' : ‖I * lft - 2 * π * I * S‖ ≤ 4 * A₂ * (Lg + 3) * Y := by
    refine hlft.trans (le_of_eq ?_); simp only [hY]; ring
  have hsum : ‖top - bot + (I * lft - 2 * π * I * S)‖ ≤
      2 * (A₁ * Lg * X) + 4 * A₂ * (Lg + 3) * Y := by
    calc ‖top - bot + (I * lft - 2 * π * I * S)‖ ≤ ‖top‖ + ‖bot‖ + ‖I * lft - 2 * π * I * S‖ :=
          (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
      _ ≤ A₁ * Lg * X + A₁ * Lg * X + 4 * A₂ * (Lg + 3) * Y := by linarith
      _ = _ := by ring
  have h3 : 2 * π * ‖explicitJL χ x c T - (R + S)‖ ≤
      2 * (A₁ * Lg * X) + 4 * A₂ * (Lg + 3) * Y := by
    rw [← hn, ← norm_mul, hid]; exact hsum
  have hπ3 := Real.pi_gt_three
  have h4 : 6 * ‖explicitJL χ x c T - (R + S)‖ ≤ 2 * (A₁ * Lg * X) + 4 * A₂ * (Lg + 3) * Y := by
    have := norm_nonneg (explicitJL χ x c T - (R + S)); nlinarith
  have e : R + S = residueZeroL χ x - ∑ ρ ∈ zerosBelowL hχ hN T, perronKernel x ρ.val +
      trivialSumL χ x := by rw [hR, hS]
  rw [← e]
  have k1 : A₁ * Lg * X ≤ A₁ * (Lg + 3) * X := by gcongr; linarith
  have k2 : 0 ≤ A₁ * (Lg + 3) * Y := by positivity
  have k3 : 0 ≤ A₂ * (Lg + 3) * X := by positivity
  have e2 : (A₁ + A₂) * (Lg + 3) * (X + Y) =
      A₁ * (Lg + 3) * X + A₁ * (Lg + 3) * Y + A₂ * (Lg + 3) * X + A₂ * (Lg + 3) * Y := by ring
  rw [e2]
  have k4 : 0 ≤ A₂ * (Lg + 3) * Y := by positivity
  have k5 : 0 ≤ A₁ * (Lg + 3) * X := by positivity
  linarith

variable {q : ℕ} [NeZero q]

set_option maxHeartbeats 1000000 in
/-- **Davenport, Ch. 19, p. 117, (6) (row 19-6)**, integer form with the trivial zeros: there is
an absolute `A` such that for primitive `χ` mod `q > 1`, integers `N ≥ 3` and `T ≥ 2`, with
`ℓ = log q + log N + log T`,
`|ψ₀(N, χ) - (r₀ - ∑_{|γ|<T} N^ρ/ρ + ∑_{m ≥ 1} N^{a-2m}/(2m - a))| ≤ A N ℓ²/T`. -/
@[kb "davenport1980" "Ch 19, p. 117"]
theorem Davenport.explicit_formula_psi0L_exact :
    ∃ A : ℝ, 0 < A ∧ ∀ {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
      (hq : q ≠ 1), ∀ N : ℕ, 3 ≤ N → ∀ T : ℝ, 2 ≤ T →
      ‖psi0L χ N - (residueZeroL χ N - ∑ ρ ∈ zerosBelowL hχ hq T, perronKernel N ρ.val +
          trivialSumL χ N)‖ ≤
        A * (N * (Real.log q + Real.log N + Real.log T) ^ 2 / T) := by
  obtain ⟨B, hB, hJ⟩ := Davenport.norm_explicitJL_sub_main_exact_le
  obtain ⟨A₉, hA₉, h₉⟩ := Davenport.exists_good_height_L
  obtain ⟨A₇, hA₇, h₇⟩ := norm_sum_L_zeros_strip_le
  have he := Real.exp_one_lt_d9
  refine ⟨100 + 6 * B * (3 * A₉ + 4) + 3 * A₇, by positivity, ?_⟩
  intro q _ χ hχ hq N hN T hT
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hT0 : 0 < T := by linarith
  set L := Real.log N with hLdef
  have hL : 1 < L := by
    rw [hLdef, Real.lt_log_iff_exp_lt hN0]; linarith
  set c := 1 + 1 / L with hcdef
  have hc1 : 1 < c := by rw [hcdef]; have : 0 < 1 / L := by positivity
                         linarith
  have hc2 : c ≤ 2 := by
    rw [hcdef]; have : 1 / L ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    linarith
  have hNc : (N : ℝ) ^ c = N * Real.exp 1 := by
    rw [hcdef, Real.rpow_add hN0, Real.rpow_one, Real.rpow_def_of_pos hN0, ← hLdef,
      mul_one_div_cancel (by linarith)]
  have hlq : 0 ≤ Real.log q := Real.log_natCast_nonneg q
  have hlT : 0 < Real.log T := Real.log_pos (by linarith)
  -- the good height
  obtain ⟨T', hT', hgood⟩ := h₉ hχ hq T hT
  have hT'0 : 0 < T' := by linarith [hT'.1]
  set δ := min (1 / (A₉ * (Real.log q + Real.log T))) 1 with hδdef
  have hqT : 0 < Real.log q + Real.log T := by linarith
  have hδ0 : 0 < δ := lt_min (by positivity) one_pos
  have hδ1 : δ ≤ 1 := min_le_right _ _
  have hinvδ : 1 / δ ≤ A₉ * (Real.log q + Real.log T) + 1 := by
    rcases le_total (1 / (A₉ * (Real.log q + Real.log T))) 1 with h | h
    · rw [hδdef, min_eq_left h, one_div_one_div]; linarith
    · rw [hδdef, min_eq_right h]; have : 0 ≤ A₉ * (Real.log q + Real.log T) := by positivity
      linarith
  have hgood' : ∀ ρ : ZeroIndex (dirichletXi χ), δ ≤ |ρ.val.im - T'| ∧ δ ≤ |ρ.val.im + T'| :=
    fun ρ ↦ ⟨(min_le_left _ _).trans (hgood ρ).1, (min_le_left _ _).trans (hgood ρ).2⟩
  -- the three errors
  have e1 := Davenport.norm_psi0L_sub_explicitJL_le χ hN hT'0
  have e2 := hJ hχ hq N (by linarith) c T' δ hc1 hc2 (by linarith [hT'.1]) hδ0 hδ1 hgood'
  have e3 := h₇ hχ hq N (by linarith) T T' hT hT'.1 hT'.2
  have hsplit : psi0L χ N - (residueZeroL χ N - ∑ ρ ∈ zerosBelowL hχ hq T, perronKernel N ρ.val +
        trivialSumL χ N) =
      (psi0L χ N - explicitJL χ N c T') + (explicitJL χ N c T' -
        (residueZeroL χ N - ∑ ρ ∈ zerosBelowL hχ hq T', perronKernel N ρ.val +
          trivialSumL χ N)) -
      (∑ ρ ∈ zerosBelowL hχ hq T', perronKernel N ρ.val -
        ∑ ρ ∈ zerosBelowL hχ hq T, perronKernel N ρ.val) := by ring
  rw [hsplit]
  refine (norm_sub_le _ _).trans ((add_le_add (norm_add_le _ _) le_rfl).trans ?_)
  set ℓ := Real.log q + Real.log N + Real.log T with hℓ
  have hLℓ : L ≤ ℓ := by rw [hℓ, ← hLdef]; linarith
  have hℓ1 : 1 ≤ ℓ := by linarith
  have hℓ2 : ℓ ≤ ℓ ^ 2 := by nlinarith
  have hlog3 := log_add_three_le hT
  have hT2 : Real.log (T' + 2) ≤ Real.log (T + 3) :=
    Real.log_le_log (by linarith) (by linarith [hT'.2])
  have hq3 : Real.log q + Real.log (T + 3) ≤ 3 * ℓ := by rw [hℓ, ← hLdef]; linarith
  have hq3' : Real.log q + Real.log (T' + 2) ≤ 3 * ℓ := by linarith
  -- first error
  have b1 : ‖psi0L χ N - explicitJL χ N c T'‖ ≤ 100 * (N * ℓ ^ 2 / T) := by
    refine e1.trans ?_
    have h1 : 100 * N * L ^ 2 / T' ≤ 100 * N * L ^ 2 / T :=
      div_le_div_of_nonneg_left (by positivity) hT0 hT'.1
    have h2 : 100 * N * L ^ 2 / T ≤ 100 * (N * ℓ ^ 2 / T) := by
      rw [mul_div_assoc', show (100 : ℝ) * N * L ^ 2 = 100 * (N * L ^ 2) by ring]
      gcongr
    linarith
  -- second error
  have b2 : ‖explicitJL χ N c T' - (residueZeroL χ N -
        ∑ ρ ∈ zerosBelowL hχ hq T', perronKernel N ρ.val + trivialSumL χ N)‖ ≤
      6 * B * (3 * A₉ + 4) * (N * ℓ ^ 2 / T) := by
    refine e2.trans ?_
    rw [hNc]
    have hX : (N : ℝ) * Real.exp 1 / (δ * T' * L) ≤ 3 * (A₉ + 1) * N * ℓ / T := by
      rw [div_le_div_iff₀ (by positivity) hT0]
      have h1 : 1 ≤ δ * (A₉ * (Real.log q + Real.log T) + 1) := by
        have := (div_le_iff₀ hδ0).mp hinvδ; linarith
      have h2 : A₉ * (Real.log q + Real.log T) + 1 ≤ (A₉ + 1) * ℓ := by
        have : Real.log q + Real.log T ≤ ℓ := by rw [hℓ, ← hLdef]; linarith
        nlinarith
      have h3 : 1 ≤ δ * ((A₉ + 1) * ℓ) := h1.trans (by gcongr)
      have h4 : T ≤ T' * L := by nlinarith [hT'.1]
      have h5 : (N : ℝ) * Real.exp 1 * T ≤ N * 3 * (T' * L) := by
        have := mul_le_mul (by linarith : Real.exp 1 ≤ 3) h4 hT0.le (by norm_num)
        nlinarith
      have h6 : (N : ℝ) * 3 * (T' * L) ≤ N * 3 * (T' * L) * (δ * ((A₉ + 1) * ℓ)) := by
        have : 0 ≤ (N : ℝ) * 3 * (T' * L) := by positivity
        nlinarith
      nlinarith
    have hY : (N : ℝ) ^ (-1 / 4 : ℝ) / (T' * L) ≤ N * ℓ / T := by
      have h1 : (N : ℝ) ^ (-1 / 4 : ℝ) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
      rw [div_le_div_iff₀ (by positivity) hT0]
      have h2 : T ≤ T' * L := by nlinarith [hT'.1]
      have h3 : 1 ≤ (N : ℝ) * ℓ := by nlinarith
      calc (N : ℝ) ^ (-1 / 4 : ℝ) * T ≤ 1 * (T' * L) := mul_le_mul h1 h2 hT0.le zero_le_one
        _ ≤ N * ℓ * (T' * L) := by
          have : 0 ≤ T' * L := by positivity
          nlinarith
    have hLg : Real.log q + Real.log (T' + 2) + 3 ≤ 6 * ℓ := by linarith
    have hB0 : 0 ≤ B * (Real.log q + Real.log (T' + 2) + 3) := by
      have := Real.log_nonneg (by linarith [hT'.1] : (1 : ℝ) ≤ T' + 2); positivity
    calc B * (Real.log q + Real.log (T' + 2) + 3) *
          ((N : ℝ) * Real.exp 1 / (δ * T' * L) + (N : ℝ) ^ (-1 / 4 : ℝ) / (T' * L))
        ≤ B * (6 * ℓ) * (3 * (A₉ + 1) * N * ℓ / T + N * ℓ / T) := by
          gcongr
      _ = 6 * B * (3 * A₉ + 4) * (N * ℓ ^ 2 / T) := by ring
  -- third error
  have b3 : ‖∑ ρ ∈ zerosBelowL hχ hq T', perronKernel N ρ.val -
      ∑ ρ ∈ zerosBelowL hχ hq T, perronKernel N ρ.val‖ ≤ 3 * A₇ * (N * ℓ ^ 2 / T) := by
    refine e3.trans ?_
    calc A₇ * (Real.log q + Real.log (T + 3)) * N / T ≤ A₇ * (3 * ℓ ^ 2) * N / T := by
          gcongr; linarith
      _ = 3 * A₇ * (N * ℓ ^ 2 / T) := by ring
  have hP : 0 ≤ (N : ℝ) * ℓ ^ 2 / T := by positivity
  calc _ ≤ 100 * (N * ℓ ^ 2 / T) + 6 * B * (3 * A₉ + 4) * (N * ℓ ^ 2 / T) +
        3 * A₇ * (N * ℓ ^ 2 / T) := add_le_add (add_le_add b1 b2) b3
    _ = (100 + 6 * B * (3 * A₉ + 4) + 3 * A₇) * (N * ℓ ^ 2 / T) := by ring

/-- `N (a + log T)² / T → 0` as `T → ∞`. -/
lemma tendsto_mul_add_log_sq_div (N a : ℝ) :
    Tendsto (fun T : ℝ ↦ N * (a + Real.log T) ^ 2 / T) atTop (𝓝 0) := by
  have h0 := Real.tendsto_pow_log_div_mul_add_atTop 1 0 0 one_ne_zero
  have h1 := Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have h2 := Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero
  simp only [one_mul, add_zero, pow_zero, pow_one] at h0 h1 h2
  have h := ((h0.const_mul (N * a ^ 2)).add (h1.const_mul (2 * N * a))).add (h2.const_mul N)
  simp only [mul_zero, add_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
  field_simp
  ring

/-- **Davenport, Ch. 19, pp. 115-116 (rows 19-2, 19-3), uniform form**: for `χ` primitive mod
`q > 1` and integers `N ≥ 3`, `∑_{|γ|<T} N^ρ/ρ → r₀ + ∑_{m ≥ 1} N^{a-2m}/(2m - a) - ψ₀(N, χ)` as
`T → ∞`; that is, `ψ₀(N, χ) = r₀ - ∑_ρ N^ρ/ρ + ∑_{m ≥ 1} N^{a-2m}/(2m - a)` with the sum over the
nontrivial zeros taken symmetrically. -/
@[kb "davenport1980" "Ch 19, p. 115"]
theorem Davenport.tendsto_sum_L_zeros {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
    (hq : q ≠ 1) (N : ℕ) (hN : 3 ≤ N) :
    Tendsto (fun T : ℝ ↦ ∑ ρ ∈ zerosBelowL hχ hq T, perronKernel N ρ.val) atTop
      (𝓝 (residueZeroL χ N + trivialSumL χ N - psi0L χ N)) := by
  obtain ⟨A, hA, h⟩ := Davenport.explicit_formula_psi0L_exact
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hb := (tendsto_mul_add_log_sq_div N (Real.log q + Real.log N)).const_mul A
  rw [mul_zero] at hb
  refine squeeze_zero' (Eventually.of_forall fun T ↦ norm_nonneg _) ?_ hb
  filter_upwards [eventually_ge_atTop 2] with T hT
  have := h hχ hq N hN T hT
  have e : ∑ ρ ∈ zerosBelowL hχ hq T, perronKernel N ρ.val -
      (residueZeroL χ N + trivialSumL χ N - psi0L χ N) =
      psi0L χ N - (residueZeroL χ N - ∑ ρ ∈ zerosBelowL hχ hq T, perronKernel N ρ.val +
        trivialSumL χ N) := by ring
  rw [e]
  refine this.trans (le_of_eq ?_)
  ring

open scoped Classical in
/-- The trivial-zero sum for odd `χ`: `∑_{m ≥ 1} x^{1-2m}/(2m - 1)`. -/
lemma trivialSumL_odd {χ : DirichletCharacter ℂ q} (ha : dirichletParity χ = 1) (x : ℝ) :
    trivialSumL χ x = ∑' m : ℕ, (x : ℂ) ^ (-(2 * (m : ℂ) + 1)) / (2 * (m : ℂ) + 1) := by
  rw [trivialSumL]
  refine tsum_congr fun m ↦ ?_
  have hp : trivialZeroL χ m = -(2 * (m : ℂ) + 1) := by rw [trivialZeroL, ha]; ring
  have hp0 : trivialZeroL χ m ≠ 0 := by
    rw [hp]; intro h
    have := congrArg Complex.re h; simp at this; linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
  rw [if_neg hp0, perronKernel, hp, div_neg, neg_neg]

open scoped Classical in
/-- The trivial-zero sum for even `χ`: `∑_{m ≥ 1} x^{-2m}/(2m)`. -/
lemma trivialSumL_even {χ : DirichletCharacter ℂ q} (ha : dirichletParity χ = 0) {x : ℝ}
    (hx : 2 ≤ x) :
    trivialSumL χ x = ∑' m : ℕ, (x : ℂ) ^ (-(2 * ((m : ℂ) + 1))) / (2 * ((m : ℂ) + 1)) := by
  have hs := (hasSum_trivialSumL χ hx).summable
  rw [trivialSumL, hs.tsum_eq_zero_add]
  have h0 : trivialZeroL χ 0 = 0 := by simp [trivialZeroL, ha]
  rw [if_pos h0, zero_add]
  refine tsum_congr fun m ↦ ?_
  have hp : trivialZeroL χ (m + 1) = -(2 * ((m : ℂ) + 1)) := by
    rw [trivialZeroL, ha]; push_cast; ring
  have hp0 : trivialZeroL χ (m + 1) ≠ 0 := by
    rw [hp]; intro h
    have := congrArg Complex.re h; simp at this; linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
  rw [if_neg hp0, perronKernel, hp, div_neg, neg_neg]

/-- **Davenport, Ch. 19, p. 115, (2) (row 19-2)**: for `χ` primitive and odd mod `q > 1` and
integers `N ≥ 3`, `ψ₀(N, χ) = -∑_ρ N^ρ/ρ - L'/L(0, χ) + ∑_{m ≥ 1} N^{1-2m}/(2m - 1)`, the sum over
the nontrivial zeros `ρ` being `lim_{T → ∞} ∑_{|γ|<T}`. -/
@[kb "davenport1980" "Ch 19, p. 115"]
theorem Davenport.explicit_formula_psi0L_odd {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
    (hq : q ≠ 1) (ha : dirichletParity χ = 1) (N : ℕ) (hN : 3 ≤ N) :
    Tendsto (fun T : ℝ ↦ ∑ ρ ∈ zerosBelowL hχ hq T, (N : ℂ) ^ ρ.val / ρ.val) atTop
      (𝓝 (-(deriv (LFunction χ) 0 / LFunction χ 0) +
        ∑' m : ℕ, (N : ℂ) ^ (-(2 * (m : ℂ) + 1)) / (2 * (m : ℂ) + 1) - psi0L χ N)) := by
  have h := Davenport.tendsto_sum_L_zeros hχ hq N hN
  rw [trivialSumL_odd ha] at h
  have hr : residueZeroL χ N = -(deriv (LFunction χ) 0 / LFunction χ 0) := by
    simp [residueZeroL, ha]
  rw [hr] at h
  simpa [perronKernel] using h

/-- **Davenport, Ch. 19, p. 116, (3) (row 19-3)**: for `χ` primitive and even mod `q > 1` and
integers `N ≥ 3`, `ψ₀(N, χ) = -∑_ρ N^ρ/ρ - log N - b(χ) + ∑_{m ≥ 1} N^{-2m}/(2m)`, where
`L'/L(s, χ) = 1/s + b(χ) + O(|s|)` near `0` (`bEven`, `bChar`). -/
@[kb "davenport1980" "Ch 19, p. 116"]
theorem Davenport.explicit_formula_psi0L_even {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
    (hq : q ≠ 1) (ha : dirichletParity χ = 0) (N : ℕ) (hN : 3 ≤ N) :
    Tendsto (fun T : ℝ ↦ ∑ ρ ∈ zerosBelowL hχ hq T, (N : ℂ) ^ ρ.val / ρ.val) atTop
      (𝓝 (-((Real.log N : ℂ) + bEven χ) +
        ∑' m : ℕ, (N : ℂ) ^ (-(2 * ((m : ℂ) + 1))) / (2 * ((m : ℂ) + 1)) - psi0L χ N)) := by
  have h := Davenport.tendsto_sum_L_zeros hχ hq N hN
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast (by omega : 2 ≤ N)
  rw [trivialSumL_even ha hN2] at h
  have hr : residueZeroL χ N = -((Real.log N : ℂ) + bEven χ) := by
    simp [residueZeroL, ha]
  rw [hr] at h
  simpa [perronKernel] using h

end NTKB
