/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Davenport.Zeros.LTrivialResidues
import NTKB.Analytic.Davenport.Zeros.LExplicitFormula
import NTKB.Analytic.Davenport.Zeros.ExplicitBounds

/-!
# The strip `σ ≤ -1/2` in the explicit formula for `ψ(x, χ)`

**Davenport, Ch. 19, pp. 116-117.** For `χ` primitive mod `q > 1`, the integral of
`F(s, χ) = -L'/L(s, χ) x^s/s` along `σ = -1/2`, `|t| ≤ T`, equals `2πi` times the sum
`∑_{m ≥ 1} x^{a-2m}/(2m - a)` of the residues at the trivial zeros, up to an error
`O((log q + log T) x^{-1/4}/(T log x))` (`Davenport.norm_left_integral_sub_trivialSumL_le`).
This is Davenport's step of moving the contour to `σ = -∞` (with 19-5 on the far left side and on
the horizontal sides).
-/

open Filter Topology Complex Set DirichletCharacter MeasureTheory
open scoped Real Interval

namespace NTKB

variable {N : ℕ} [NeZero N]

/-- `|L'/L(s, χ)| ≤ A (log q + log(|t| + 2))` for `-1 ≤ σ ≤ -1/2`, `|t| ≥ 2`. -/
lemma norm_logDeriv_LFunction_strip_left :
    ∃ A : ℝ, 0 < A ∧ ∀ {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}, χ.IsPrimitive → N ≠ 1 →
      ∀ s : ℂ, -1 ≤ s.re → s.re ≤ -1 / 2 → 2 ≤ |s.im| →
      ‖deriv (LFunction χ) s / LFunction χ s‖ ≤ A * (Real.log N + Real.log (|s.im| + 2)) := by
  classical
  obtain ⟨A₁, hA₁, h₁⟩ := Davenport.logDeriv_LFunction_local
  obtain ⟨A₂, hA₂, h₂⟩ := Davenport.card_L_zeros_near_le
  refine ⟨A₁ + 2 * A₂, by positivity, fun {N} _ {χ} hχ hN s hσ1 hσ2 ht ↦ ?_⟩
  have hpar : ∀ m : ℕ, s + dirichletParity χ ≠ -(2 * m) := by
    intro m h
    have := congrArg Complex.im h
    simp [dirichletParity_im] at this
    rw [this] at ht; simp at ht; linarith
  have hz : LFunction χ s ≠ 0 := LFunction_ne_zero_of_re_nonpos hχ hN hpar (by linarith)
  have hloc := h₁ hχ hN s hσ1 (by linarith) ht hz
  obtain ⟨hfin, hcard⟩ := h₂ hχ hN s.im
  have hsum : ∑' ρ : ZeroIndex (dirichletXi χ),
      (if |s.im - ρ.val.im| < 1 then 1 / (s - ρ.val) else 0) =
      ∑ ρ ∈ hfin.toFinset, (if |s.im - ρ.val.im| < 1 then 1 / (s - ρ.val) else 0) := by
    rw [tsum_eq_sum]
    intro ρ hρ
    rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hρ
    exact ite_eq_right_iff.mpr fun e ↦ absurd (by rw [abs_sub_comm] at e; exact e) hρ
  rw [hsum] at hloc
  have hS : ‖∑ ρ ∈ hfin.toFinset, (if |s.im - ρ.val.im| < 1 then 1 / (s - ρ.val) else 0)‖ ≤
      2 * hfin.toFinset.card := by
    refine (norm_sum_le _ _).trans ?_
    have : ∀ ρ ∈ hfin.toFinset, ‖(if |s.im - ρ.val.im| < 1 then 1 / (s - ρ.val) else 0)‖ ≤ 2 := by
      intro ρ _
      split_ifs
      · have hβ := (dirichletXi_zero_mem hχ hN ρ).2.1
        have h1 : 1 / 2 ≤ ‖s - ρ.val‖ := by
          have := Complex.abs_re_le_norm (s - ρ.val)
          rw [sub_re, abs_of_neg (by linarith)] at this; linarith
        rw [norm_div, norm_one, div_le_iff₀ (by linarith)]; linarith
      · simp
    refine (Finset.sum_le_sum this).trans (le_of_eq ?_)
    rw [Finset.sum_const, nsmul_eq_mul]; ring
  have hc : (hfin.toFinset.card : ℝ) ≤ A₂ * (Real.log N + Real.log (|s.im| + 2)) := by
    rw [← Set.ncard_eq_toFinset_card _ hfin]; exact hcard
  have k1 := norm_sub_norm_le (deriv (LFunction χ) s / LFunction χ s)
    (∑ ρ ∈ hfin.toFinset, (if |s.im - ρ.val.im| < 1 then 1 / (s - ρ.val) else 0))
  nlinarith

/-- **Bound on the horizontal lines** `|t| ≥ 2`, `σ ≤ -1/2`:
`|L'/L(s, χ)| ≤ B (log q + log(|t| + 2) + |σ|)`. -/
lemma norm_logDeriv_LFunction_horiz_left :
    ∃ B : ℝ, 0 < B ∧ ∀ {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}, χ.IsPrimitive → N ≠ 1 →
      ∀ s : ℂ, s.re ≤ -1 / 2 → 2 ≤ |s.im| →
      ‖deriv (LFunction χ) s / LFunction χ s‖ ≤
        B * (Real.log N + Real.log (|s.im| + 2) + |s.re|) := by
  obtain ⟨A₁, hA₁, h₁⟩ := norm_logDeriv_LFunction_strip_left
  obtain ⟨A₂, hA₂, h₂⟩ := Davenport.norm_logDeriv_LFunction_left_le
  refine ⟨A₁ + A₂, by positivity, fun {N} _ {χ} hχ hN s hσ ht ↦ ?_⟩
  have hlN : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  have hlT : 0 ≤ Real.log (|s.im| + 2) := Real.log_nonneg (by linarith [abs_nonneg s.im])
  rcases le_or_gt (-1) s.re with h1 | h1
  · have := h₁ hχ hN s h1 hσ ht
    have : 0 ≤ A₂ * (Real.log N + Real.log (|s.im| + 2)) + (A₁ + A₂) * |s.re| := by positivity
    nlinarith
  · have := h₂ hχ hN s h1.le (Or.inl (by linarith))
    have hn : ‖s‖ + 2 ≤ (|s.im| + 2) + |s.re| := by
      have := Complex.norm_le_abs_re_add_abs_im s; linarith
    have hl : Real.log (‖s‖ + 2) ≤ Real.log (|s.im| + 2) + |s.re| :=
      (Real.log_le_log (by positivity) hn).trans
        (log_add_le_log_add (by linarith [abs_nonneg s.im]) (abs_nonneg _))
    have : 0 ≤ A₁ * (Real.log N + Real.log (|s.im| + 2) + |s.re|) := by positivity
    nlinarith

/-- The real part `U_K = 2K + 1 + a` of the far left side (midway between two trivial zeros). -/
noncomputable def leftU (χ : DirichletCharacter ℂ N) (K : ℕ) : ℝ :=
  2 * K + 1 + (dirichletParity χ).re

omit [NeZero N] in
lemma one_le_leftU (χ : DirichletCharacter ℂ N) (K : ℕ) : 1 ≤ leftU χ K := by
  have := dirichletParity_re_nonneg χ
  rw [leftU]; linarith [(K.cast_nonneg : (0 : ℝ) ≤ K)]

/-- The indices `n ≤ K` of the trivial zeros `p_n ≠ 0`. -/
noncomputable def trivialIdx (χ : DirichletCharacter ℂ N) (K : ℕ) : Finset ℕ :=
  (Finset.range (K + 1)).filter fun n ↦ trivialZeroL χ n ≠ 0

omit [NeZero N] in
lemma trivialZeroL_injective (χ : DirichletCharacter ℂ N) : Function.Injective (trivialZeroL χ) := by
  intro m n h
  have := congrArg Complex.re h
  simp only [trivialZeroL_re] at this
  exact_mod_cast (show (m : ℝ) = n by linarith)

omit [NeZero N] in
lemma trivialZeroL_re_lt {χ : DirichletCharacter ℂ N} {n : ℕ} (hn : trivialZeroL χ n ≠ 0) :
    (trivialZeroL χ n).re ≤ -1 := by
  rw [trivialZeroL_re]
  rcases dirichletParity_eq_zero_or_one χ with ha | ha
  · rw [ha]; simp
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · exact absurd (by simp [trivialZeroL, ha]) hn
    · have : (1 : ℝ) ≤ n := by exact_mod_cast hn0
      linarith
  · rw [ha]; simp

/-- **The residue theorem on the left strip** `[-U_K, -1/2] × [-T, T]`. -/
theorem rectIntegral_explicitIntegrandL_left {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive)
    (hN : N ≠ 1) {x : ℝ} (hx : 0 < x) {T : ℝ} (hT : 0 < T) (K : ℕ) :
    rectIntegral (explicitIntegrandL χ x) (((-leftU χ K : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * I)
        (((-1 / 2 : ℝ) : ℂ) + (T : ℂ) * I) =
      2 * π * I * ∑ n ∈ trivialIdx χ K, (-1) * perronKernel x (trivialZeroL χ n) := by
  classical
  have hχ1 := ne_one_of_isPrimitive hχ hN
  set U := leftU χ K with hU
  have hU1 := one_le_leftU χ K
  set a := dirichletParity χ with ha
  have ha0 : 0 ≤ a.re := dirichletParity_re_nonneg χ
  set z₀ : ℂ := ((-U : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * I with hz₀
  set w₀ : ℂ := ((-1 / 2 : ℝ) : ℂ) + (T : ℂ) * I with hw₀
  have hz₀re : z₀.re = -U := by simp [z₀]
  have hz₀im : z₀.im = -T := by simp [z₀]
  have hw₀re : w₀.re = -1 / 2 := by simp [w₀]
  have hw₀im : w₀.im = T := by simp [w₀]
  set P : Finset ℂ := (trivialIdx χ K).image (trivialZeroL χ) with hP
  have hPre : ∀ p ∈ P, -U < p.re ∧ p.re ≤ -1 ∧ p.im = 0 := by
    intro p hp
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hp
    rw [trivialIdx, Finset.mem_filter, Finset.mem_range] at hn
    refine ⟨?_, trivialZeroL_re_lt hn.2, trivialZeroL_im χ n⟩
    rw [trivialZeroL_re, hU, leftU]
    have : (n : ℝ) ≤ K := by exact_mod_cast Nat.lt_succ_iff.mp hn.1
    linarith
  set B : Set ℂ := {s : ℂ | -U - 1 / 2 < s.re} ∩ {s : ℂ | s.re < -1 / 4} ∩
    {s : ℂ | |s.im| < T + 1} with hB
  have hBopen : IsOpen B :=
    ((isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)).inter
        (isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const)
  have hRU : [[z₀.re, w₀.re]] ×ℂ [[z₀.im, w₀.im]] ⊆ B := by
    intro s hs
    rw [mem_reProdIm, hz₀re, hw₀re, hz₀im, hw₀im, uIcc_of_le (by linarith),
      uIcc_of_le (by linarith)] at hs
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · show -U - 1 / 2 < s.re; linarith [hs.1.1]
    · show s.re < -1 / 4; linarith [hs.1.2]
    · show |s.im| < T + 1; rw [abs_lt]; constructor <;> linarith [hs.2.1, hs.2.2]
  have hPin : ∀ p ∈ P, p ∈ Ioo z₀.re w₀.re ×ℂ Ioo z₀.im w₀.im := by
    intro p hp
    rw [mem_reProdIm, hz₀re, hw₀re, hz₀im, hw₀im]
    obtain ⟨h1, h2, h3⟩ := hPre p hp
    rw [h3]
    exact ⟨⟨h1, by linarith⟩, ⟨by linarith, hT⟩⟩
  have hdiff : DifferentiableOn ℂ (explicitIntegrandL χ x) (B \ ↑P) := by
    intro s ⟨hsB, hsP⟩
    have hre1 : -U - 1 / 2 < s.re := hsB.1.1
    have hre2 : s.re < -1 / 4 := hsB.1.2
    have hs0 : s ≠ 0 := fun h ↦ by rw [h] at hre2; simp at hre2; linarith
    have hpar : ∀ m : ℕ, s + a ≠ -(2 * m) := by
      intro m h
      have hs' : s = trivialZeroL χ m := by rw [trivialZeroL, ← ha]; linear_combination h
      apply hsP
      rw [Finset.mem_coe, hP, Finset.mem_image]
      refine ⟨m, ?_, hs'.symm⟩
      rw [trivialIdx, Finset.mem_filter, Finset.mem_range]
      refine ⟨?_, fun h0 ↦ hs0 (hs'.trans h0)⟩
      have := congrArg Complex.re hs'
      rw [trivialZeroL_re, ← ha] at this
      rw [this, hU, leftU, ← ha] at hre1
      have : (m : ℝ) < K + 1 := by linarith
      exact_mod_cast this
    have hL := LFunction_ne_zero_of_re_nonpos hχ hN hpar (by linarith)
    exact (differentiableAt_explicitIntegrandL hχ1 hx hs0 hL).differentiableWithinAt
  set r : ℂ → ℂ := fun p ↦ (-1) * perronKernel x p with hr
  have hres : ∀ p ∈ P, ∃ V ∈ 𝓝 p, BddAbove (norm ∘ (fun s ↦ explicitIntegrandL χ x s -
      r p / (s - p)) '' (V \ {p})) := by
    intro p hp
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hp
    rw [trivialIdx, Finset.mem_filter] at hn
    exact bddNear_explicitIntegrandL_trivial hχ hN hx n hn.2
  have hrect := rectIntegral_eq_sum_residues (z := z₀) (w := w₀) (by rw [hz₀re, hw₀re]; linarith)
    (by rw [hz₀im, hw₀im]; linarith) hBopen hRU r P hPin (explicitIntegrandL χ x) hdiff hres
  rw [hrect, hP, Finset.sum_image fun m _ n _ h ↦ trivialZeroL_injective χ h]

/-- The horizontal sides of the left strip: for `x ≥ 2`, `|h| ≥ 2`, `U ≥ 1/2`,
`|∫_{-U}^{-1/2} F(σ + ih, χ) dσ| ≤ 2B (log q + log(|h| + 2) + 3) x^{-1/4}/(|h| log x)`. -/
lemma norm_integral_explicitIntegrandL_horiz_left :
    ∃ B : ℝ, 0 < B ∧ ∀ {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}, χ.IsPrimitive → N ≠ 1 →
      ∀ x : ℝ, 2 ≤ x → ∀ h : ℝ, 2 ≤ |h| → ∀ U : ℝ, 1 / 2 ≤ U →
      ‖∫ σ : ℝ in (-U)..(-1 / 2), explicitIntegrandL χ x (σ + h * I)‖ ≤
        2 * B * (Real.log N + Real.log (|h| + 2) + 3) * x ^ (-1 / 4 : ℝ) /
          (|h| * Real.log x) := by
  obtain ⟨B, hB, hb⟩ := norm_logDeriv_LFunction_horiz_left
  refine ⟨B, hB, fun {N} _ {χ} hχ hN x hx h hh U hU ↦ ?_⟩
  have hx0 : 0 < x := by linarith
  have hx1 : 1 < x := by linarith
  have hlx : 0 < Real.log x := Real.log_pos hx1
  have hh0 : 0 < |h| := by linarith
  set Lg := Real.log N + Real.log (|h| + 2) with hLg
  have hLg0 : 0 ≤ Lg := by
    have := Real.log_natCast_nonneg N
    have := Real.log_nonneg (by linarith [abs_nonneg h] : (1 : ℝ) ≤ |h| + 2); linarith
  set g : ℝ → ℝ := fun σ ↦ B * (Lg + 3) * x ^ (σ / 2) / |h| with hg
  have hgc : Continuous g := by
    simp only [hg]
    exact ((continuous_const.mul (continuous_const.rpow (continuous_id.div_const 2)
      fun _ ↦ Or.inl hx0.ne')).div_const _)
  have hpt : ∀ σ ∈ Set.Ioc (-U) (-1 / 2),
      ‖explicitIntegrandL χ x (σ + h * I)‖ ≤ g σ := by
    intro σ hσ
    set s : ℂ := σ + h * I with hs
    have hsre : s.re = σ := by simp [s]
    have hsim : s.im = h := by simp [s]
    have h1 := hb hχ hN s (by rw [hsre]; exact hσ.2) (by rw [hsim]; exact hh)
    rw [hsre, hsim] at h1
    have hk : ‖perronKernel x s‖ ≤ x ^ σ / |h| := by
      rw [norm_perronKernel hx0, hsre]
      apply div_le_div_of_nonneg_left (by positivity) hh0
      have := Complex.abs_im_le_norm s; rwa [hsim] at this
    have hσ0 : σ ≤ 0 := by linarith [hσ.2]
    have e1 := rpow_le_rpow_half hx hσ0
    have e2 := abs_mul_rpow_le hx hσ0
    rw [explicitIntegrandL, norm_mul, norm_neg]
    calc ‖deriv (LFunction χ) s / LFunction χ s‖ * ‖perronKernel x s‖
        ≤ B * (Lg + |σ|) * (x ^ σ / |h|) :=
          mul_le_mul h1 hk (norm_nonneg _) (by positivity)
      _ = (B * Lg * x ^ σ + B * (|σ| * x ^ σ)) / |h| := by ring
      _ ≤ (B * Lg * x ^ (σ / 2) + B * (3 * x ^ (σ / 2))) / |h| := by
          gcongr
      _ = g σ := by simp only [hg]; ring
  have hle := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) (by linarith)
    (Eventually.of_forall hpt) (hgc.intervalIntegrable (-U) (-1 / 2))
  refine hle.trans ?_
  have hint : ∫ σ in (-U)..(-1 / 2), g σ =
      B * (Lg + 3) / |h| * ∫ σ in (-U)..(-1 / 2), x ^ (σ / 2) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun σ _ ↦ ?_
    simp only [hg]; ring
  rw [hint]
  have hI := integral_rpow_half_le hx1 (-U) (-1 / 2)
  rw [show (-1 / 2 : ℝ) / 2 = -1 / 4 by norm_num] at hI
  calc B * (Lg + 3) / |h| * ∫ σ in (-U)..(-1 / 2), x ^ (σ / 2)
      ≤ B * (Lg + 3) / |h| * (2 * x ^ (-1 / 4 : ℝ) / Real.log x) := by gcongr
    _ = 2 * B * (Lg + 3) * x ^ (-1 / 4 : ℝ) / (|h| * Real.log x) := by
        field_simp

/-- The far left side `σ = -U_K`:
`|∫_{-T}^{T} F(-U_K + iy, χ) dy| ≤ 2T A (log q + log(T + 2) + U_K) x^{-U_K}/U_K`. -/
lemma norm_integral_explicitIntegrandL_far_left :
    ∃ A : ℝ, 0 < A ∧ ∀ {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}, χ.IsPrimitive → N ≠ 1 →
      ∀ x : ℝ, 0 < x → ∀ T : ℝ, 0 ≤ T → ∀ K : ℕ,
      ‖∫ y : ℝ in -T..T, explicitIntegrandL χ x (((-leftU χ K : ℝ) : ℂ) + y * I)‖ ≤
        2 * T * (A * (Real.log N + Real.log (T + 2) + leftU χ K) * x ^ (-leftU χ K) /
          leftU χ K) := by
  obtain ⟨A, hA, hb⟩ := Davenport.norm_logDeriv_LFunction_left_le
  refine ⟨A, hA, fun {N} _ {χ} hχ hN x hx T hT K ↦ ?_⟩
  set U := leftU χ K with hU
  have hU1 : 1 ≤ U := one_le_leftU χ K
  have hlN := Real.log_natCast_nonneg N
  have hpt : ∀ y ∈ Ι (-T) T, ‖explicitIntegrandL χ x (((-U : ℝ) : ℂ) + y * I)‖ ≤
      A * (Real.log N + Real.log (T + 2) + U) * x ^ (-U) / U := by
    intro y hy
    rw [uIoc_of_le (by linarith)] at hy
    set s : ℂ := ((-U : ℝ) : ℂ) + y * I with hs
    have hsre : s.re = -U := by simp [s]
    have hsim : s.im = y := by simp [s]
    have h1 := hb hχ hN s (by rw [hsre]; linarith) (Or.inr ⟨K, by rw [hsre, hU, leftU]; ring⟩)
    have hyT : |y| ≤ T := abs_le.mpr ⟨by linarith [hy.1], hy.2⟩
    have hn : ‖s‖ ≤ U + T := by
      have := Complex.norm_le_abs_re_add_abs_im s
      rw [hsre, hsim, abs_neg, abs_of_pos (by linarith)] at this; linarith
    have hnU : U ≤ ‖s‖ := by
      have := Complex.abs_re_le_norm s
      rw [hsre, abs_neg, abs_of_pos (by linarith)] at this; exact this
    have hlog : Real.log (‖s‖ + 2) ≤ Real.log (T + 2) + U := by
      calc Real.log (‖s‖ + 2) ≤ Real.log ((T + 2) + U) :=
            Real.log_le_log (by positivity) (by linarith)
        _ ≤ Real.log (T + 2) + U := log_add_le_log_add (by linarith) (by linarith)
    have hk : ‖perronKernel x s‖ ≤ x ^ (-U) / U := by
      rw [norm_perronKernel hx, hsre]
      exact div_le_div_of_nonneg_left (by positivity) (by linarith) hnU
    rw [explicitIntegrandL, norm_mul, norm_neg]
    calc ‖deriv (LFunction χ) s / LFunction χ s‖ * ‖perronKernel x s‖
        ≤ A * (Real.log N + Real.log (T + 2) + U) * (x ^ (-U) / U) := by
          refine mul_le_mul (h1.trans ?_) hk (norm_nonneg _) ?_
          · have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ T + 2)
            nlinarith
          · have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ T + 2)
            have : 0 ≤ Real.log N + Real.log (T + 2) + U := by linarith
            positivity
      _ = A * (Real.log N + Real.log (T + 2) + U) * x ^ (-U) / U := by ring
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := -T) (b := T) hpt
  rw [show T - -T = 2 * T by ring, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 * T)] at this
  calc _ ≤ A * (Real.log N + Real.log (T + 2) + U) * x ^ (-U) / U * (2 * T) := this
    _ = _ := by ring

open scoped Classical in
/-- The sum of the residues of `F(s, χ)` at the trivial zeros `p_n ≠ 0`:
`∑_n -x^{p_n}/p_n = ∑_{m ≥ 1} x^{a-2m}/(2m - a)` (Davenport's last sums in (2), (3) of Ch. 19). -/
noncomputable def trivialSumL (χ : DirichletCharacter ℂ N) (x : ℝ) : ℂ :=
  ∑' n : ℕ, if trivialZeroL χ n = 0 then 0 else -perronKernel x (trivialZeroL χ n)

omit [NeZero N] in
open scoped Classical in
lemma hasSum_trivialSumL (χ : DirichletCharacter ℂ N) {x : ℝ} (hx : 2 ≤ x) :
    HasSum (fun n : ℕ ↦ if trivialZeroL χ n = 0 then 0 else -perronKernel x (trivialZeroL χ n))
      (trivialSumL χ x) := by
  have hx0 : 0 < x := by linarith
  have hb : ∀ n : ℕ, ‖(if trivialZeroL χ n = 0 then 0 else -perronKernel x (trivialZeroL χ n))‖ ≤
      (1 / 4 : ℝ) ^ n := by
    intro n
    split_ifs with h
    · simp
    · rw [norm_neg, norm_perronKernel hx0]
      have hre := trivialZeroL_re_lt h
      have hn1 : 1 ≤ ‖trivialZeroL χ n‖ := by
        have := Complex.abs_re_le_norm (trivialZeroL χ n)
        rw [abs_of_neg (by linarith)] at this; linarith
      have ha0 := dirichletParity_re_nonneg χ
      have h1 : x ^ (trivialZeroL χ n).re ≤ x ^ (-(2 * n : ℝ)) := by
        apply Real.rpow_le_rpow_of_exponent_le (by linarith)
        rw [trivialZeroL_re]; linarith
      have h2 : x ^ (-(2 * n : ℝ)) ≤ (1 / 4 : ℝ) ^ n := by
        rw [Real.rpow_neg hx0.le, show (2 * n : ℝ) = ((2 * n : ℕ) : ℝ) by push_cast; ring,
          Real.rpow_natCast, pow_mul, ← inv_pow, one_div]
        apply pow_le_pow_left₀ (by positivity)
        rw [inv_le_inv₀ (by positivity) (by norm_num)]
        nlinarith
      calc x ^ (trivialZeroL χ n).re / ‖trivialZeroL χ n‖ ≤ x ^ (trivialZeroL χ n).re / 1 :=
            div_le_div_of_nonneg_left (by positivity) one_pos hn1
        _ ≤ (1 / 4 : ℝ) ^ n := by rw [div_one]; exact h1.trans h2
  exact (Summable.of_norm_bounded (summable_geometric_of_lt_one (by norm_num) (by norm_num))
    hb).hasSum

omit [NeZero N] in
lemma tendsto_rpow_neg_leftU (χ : DirichletCharacter ℂ N) {x : ℝ} (hx : 2 ≤ x) :
    Tendsto (fun K : ℕ ↦ x ^ (-leftU χ K)) atTop (𝓝 0) := by
  have hx0 : 0 < x := by linarith
  refine squeeze_zero (fun K ↦ by positivity) (fun K ↦ ?_)
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num))
  have ha0 := dirichletParity_re_nonneg χ
  calc x ^ (-leftU χ K) ≤ x ^ (-(K : ℝ)) := by
        apply Real.rpow_le_rpow_of_exponent_le (by linarith)
        rw [leftU]; linarith [(K.cast_nonneg : (0 : ℝ) ≤ K)]
    _ = (x⁻¹) ^ K := by rw [Real.rpow_neg hx0.le, Real.rpow_natCast, inv_pow]
    _ ≤ (1 / 2) ^ K := by
        apply pow_le_pow_left₀ (by positivity)
        rw [one_div]; exact inv_anti₀ (by norm_num) hx

/-- **Davenport, Ch. 19, pp. 116-117 (the contour moved to `σ = -∞`)**: there is an absolute `B`
such that for `χ` primitive mod `q > 1`, `x ≥ 2`, `T ≥ 2`,
`|i ∫_{-T}^{T} F(-1/2 + iy, χ) dy - 2πi ∑_{m ≥ 1} x^{a-2m}/(2m - a)| ≤
4B (log q + log(T + 2) + 3) x^{-1/4}/(T log x)`. -/
@[kb "davenport1980" "Ch 19, p. 116"]
theorem Davenport.norm_left_integral_sub_trivialSumL_le :
    ∃ B : ℝ, 0 < B ∧ ∀ {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}, χ.IsPrimitive → N ≠ 1 →
      ∀ x : ℝ, 2 ≤ x → ∀ T : ℝ, 2 ≤ T →
      ‖I * (∫ y : ℝ in -T..T, explicitIntegrandL χ x (((-1 / 2 : ℝ) : ℂ) + y * I)) -
        2 * π * I * trivialSumL χ x‖ ≤
        4 * B * (Real.log N + Real.log (T + 2) + 3) * x ^ (-1 / 4 : ℝ) / (T * Real.log x) := by
  classical
  obtain ⟨B, hB, hH⟩ := norm_integral_explicitIntegrandL_horiz_left
  obtain ⟨A, hA, hF⟩ := norm_integral_explicitIntegrandL_far_left
  refine ⟨B, hB, fun {N} _ {χ} hχ hN x hx T hT ↦ ?_⟩
  have hx0 : 0 < x := by linarith
  have hT0 : 0 < T := by linarith
  set lft := ∫ y : ℝ in -T..T, explicitIntegrandL χ x (((-1 / 2 : ℝ) : ℂ) + y * I) with hlft
  set H := 2 * B * (Real.log N + Real.log (T + 2) + 3) * x ^ (-1 / 4 : ℝ) / (T * Real.log x)
    with hHdef
  set S : ℕ → ℂ := fun K ↦ ∑ n ∈ trivialIdx χ K, (-1) * perronKernel x (trivialZeroL χ n) with hS
  set E : ℕ → ℝ := fun K ↦ 2 * T * (A * (Real.log N + Real.log (T + 2) + leftU χ K) *
    x ^ (-leftU χ K) / leftU χ K) with hE
  -- for each `K`
  have hK : ∀ K : ℕ, ‖I * lft - 2 * π * I * S K‖ ≤ 2 * H + E K := by
    intro K
    have hrect := rectIntegral_explicitIntegrandL_left hχ hN hx0 hT0 K
    unfold rectIntegral at hrect
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      add_zero, add_im, mul_im, zero_add] at hrect
    have hU := one_le_leftU χ K
    have hTa : 2 ≤ |T| := by rw [abs_of_pos hT0]; exact hT
    have hTb : 2 ≤ |-T| := by rw [abs_neg]; exact hTa
    have hbot := hH hχ hN x hx (-T) hTb (leftU χ K) (by linarith)
    have htop := hH hχ hN x hx T hTa (leftU χ K) (by linarith)
    rw [abs_neg, abs_of_pos hT0] at hbot
    rw [abs_of_pos hT0] at htop
    have hfl := hF hχ hN x hx0 T hT0.le K
    generalize (∫ σ : ℝ in (-leftU χ K)..(-1 / 2), explicitIntegrandL χ x (σ + (-T : ℝ) * I)) =
      bot at hrect hbot
    generalize (∫ σ : ℝ in (-leftU χ K)..(-1 / 2), explicitIntegrandL χ x (σ + T * I)) =
      top at hrect htop
    generalize (∫ y : ℝ in -T..T, explicitIntegrandL χ x (((-leftU χ K : ℝ) : ℂ) + y * I)) =
      far at hrect hfl
    have hid : I * lft - 2 * π * I * S K = top - bot + I * far := by
      rw [hlft]; simp only [hS]; linear_combination hrect
    rw [hid]
    calc ‖top - bot + I * far‖ ≤ ‖top‖ + ‖bot‖ + ‖I * far‖ :=
          (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
      _ ≤ H + H + E K := by
          rw [norm_mul, Complex.norm_I, one_mul]
          exact add_le_add (add_le_add htop hbot) hfl
      _ = 2 * H + E K := by ring
  -- the limit `K → ∞`
  have hSlim : Tendsto S atTop (𝓝 (trivialSumL χ x)) := by
    have h := ((hasSum_trivialSumL χ hx).tendsto_sum_nat).comp (tendsto_add_atTop_nat 1)
    refine h.congr fun K ↦ ?_
    simp only [Function.comp, hS, trivialIdx, Finset.sum_filter]
    refine Finset.sum_congr rfl fun n _ ↦ ?_
    split_ifs <;> simp_all
  have hElim : Tendsto E atTop (𝓝 0) := by
    have hc : 0 ≤ Real.log N + Real.log (T + 2) := by
      have := Real.log_natCast_nonneg N
      have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ T + 2); linarith
    have hb := (tendsto_rpow_neg_leftU χ hx).const_mul (2 * T * A * (Real.log N + Real.log (T + 2) + 1))
    rw [mul_zero] at hb
    refine squeeze_zero (fun K ↦ ?_) (fun K ↦ ?_) hb
    · have := one_le_leftU χ K
      simp only [hE]; positivity
    · have hU := one_le_leftU χ K
      simp only [hE]
      have hxU : 0 ≤ x ^ (-leftU χ K) := by positivity
      have e : (Real.log N + Real.log (T + 2) + leftU χ K) / leftU χ K ≤
          Real.log N + Real.log (T + 2) + 1 := by
        rw [div_le_iff₀ (by linarith)]; nlinarith
      calc 2 * T * (A * (Real.log N + Real.log (T + 2) + leftU χ K) * x ^ (-leftU χ K) /
            leftU χ K)
          = 2 * T * A * ((Real.log N + Real.log (T + 2) + leftU χ K) / leftU χ K) *
              x ^ (-leftU χ K) := by ring
        _ ≤ 2 * T * A * (Real.log N + Real.log (T + 2) + 1) * x ^ (-leftU χ K) := by gcongr
  have hl1 : Tendsto (fun K ↦ ‖I * lft - 2 * π * I * S K‖) atTop
      (𝓝 ‖I * lft - 2 * π * I * trivialSumL χ x‖) :=
    ((tendsto_const_nhds.sub (tendsto_const_nhds.mul hSlim))).norm
  have hl2 : Tendsto (fun K ↦ 2 * H + E K) atTop (𝓝 (2 * H)) := by
    simpa using tendsto_const_nhds.add hElim
  have := le_of_tendsto_of_tendsto' hl1 hl2 hK
  refine this.trans (le_of_eq ?_)
  rw [hHdef]; ring

end NTKB
