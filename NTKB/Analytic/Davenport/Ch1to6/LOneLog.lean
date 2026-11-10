/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.Analysis.Complex.AbelLimit
import Mathlib.Analysis.Complex.Convex
import Mathlib.NumberTheory.DirichletCharacter.GaussSum
import Mathlib.NumberTheory.LSeries.Nonvanishing
import NTKB.Analytic.Apostol.DirichletSeries.UniformConvergence
import NTKB.Analytic.Apostol.Characters.PartialSums
import NTKB.Elementary.SpecialValues.ValueAtZero

/-!
# Davenport, Chapters 1 and 6: `L(1, χ)` through the logarithmic series

* (§1, pp. 4–5) For a nonprincipal character the series `∑ χ(n) n^{-s}` converges for
  `Re s > 1/2` (in fact for `Re s > 0`) to `L(s, χ)`, Mathlib's analytic continuation; in
  particular `L(1, χ) = ∑_{n ≥ 1} χ(n)/n` (`NTKB.Davenport.tendsto_sum_char_div_LFunction`).
* (§1, p. 8) For `|z| = 1`, `z ≠ 1`: `∑_{n ≥ 1} z^n/n = -log(1 - z)` (principal logarithm), and for
  `z = e^{iθ}`, `0 < θ < 2π`: `-log(1 - z) = -log(2 sin(θ/2)) + i(π - θ)/2`.
* (§1, p. 8, (6); §6, p. 50) For a primitive character `χ` modulo `N > 1`,
  `L(1, χ) = -(1/τ(χ̄)) ∑_{m=1}^{N-1} χ̄(m) log(1 - e(m/N))` (Davenport's substitution of
  `χ(n) = τ(χ̄)^{-1} ∑_m χ̄(m) e(mn/N)` into the series).
-/

noncomputable section

open Complex Filter Topology Finset DirichletCharacter
open scoped Real

namespace NTKB.Davenport

open NTKB.Apostol

variable {N : ℕ} [NeZero N]

/-! ### The series `∑ χ(n) n^{-s}` for `Re s > 1/2` -/

/-- For `χ ≠ 1` the series `∑ χ(n) n^{-1/2}` converges (Dirichlet's test). -/
theorem exists_tendsto_dirichletPartialSum_half {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) :
    ∃ L, Tendsto (dirichletPartialSum (fun n ↦ χ n) (1 / 2)) atTop (𝓝 L) := by
  have h := (tendsto_sum_char_mul_and_norm_sub_le hχ antitoneOn_one_div_sqrt
    (fun t ht ↦ by positivity)
    ((tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop).congr fun t ↦ by
      simp [one_div])).1
  refine ⟨_, (tendsto_add_atTop_iff_nat 1).mp (h.congr fun M ↦ ?_)⟩
  rw [dirichletPartialSum, sum_range_succ', LSeries.term_zero, add_zero]
  induction M with
  | zero => simp
  | succ M ih =>
  rw [Finset.sum_Ioc_succ_top (Nat.zero_le _), sum_range_succ, ih]
  congr 1
  rw [LSeries.term_of_ne_zero (Nat.succ_ne_zero M), div_eq_mul_inv]
  congr 1
  have hk : (0 : ℝ) ≤ ((M + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have e : ((1 / √((M + 1 : ℕ) : ℝ) : ℝ) : ℂ) = (((M + 1 : ℕ) : ℂ) ^ (1 / 2 : ℂ))⁻¹ := by
    rw [one_div, ofReal_inv, Real.sqrt_eq_rpow, ofReal_cpow hk]
    push_cast
    rfl
  exact e

/-- **Davenport §1, pp. 4–5 (and §4).** For `χ ≠ 1` and `Re s > 1/2`, the partial sums
`∑_{n < M} χ(n) n^{-s}` converge to `L(s, χ)`. -/
@[kb "davenport1980" "Ch 1, pp. 4-5"]
theorem tendsto_dirichletPartialSum_LFunction {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1)
    {s : ℂ} (hs : 1 / 2 < s.re) :
    Tendsto (dirichletPartialSum (fun n ↦ χ n) s) atTop (𝓝 (LFunction χ s)) := by
  obtain ⟨L, hL⟩ := exists_tendsto_dirichletPartialSum_half hχ
  set f : ℕ → ℂ := fun n ↦ χ n
  set U : Set ℂ := {z | 1 / 2 < z.re}
  have hUsub : U ⊆ halfPlaneOfConv f := fun z hz ↦ ⟨1 / 2, by
    have : (1 / 2 : ℝ) < z.re := hz
    simpa using this, L, hL⟩
  have hUo : IsOpen U := isOpen_lt continuous_const continuous_re
  have hUc : IsPreconnected U := (convex_halfSpace_re_gt (1 / 2)).isPreconnected
  have hd : DifferentiableOn ℂ (dirichletSum f) U := (apostol_thm_11_12 f).1.mono hUsub
  have hconv : ∀ z ∈ halfPlaneOfConv f,
      Tendsto (dirichletPartialSum f z) atTop (𝓝 (dirichletSum f z)) := by
    rintro z ⟨z₀, hz₀, L₀, hL₀⟩
    obtain ⟨L', hL'⟩ := apostol_thm_11_8 hL₀ hz₀
    exact tendsto_nhds_limUnder ⟨L', hL'⟩
  -- on `Re z > 1` the sum is Mathlib's `L`-series
  have hgt : ∀ z : ℂ, 1 < z.re → dirichletSum f z = LFunction χ z := by
    intro z hz
    have h1 := (LSeriesSummable_of_one_lt_re χ hz).hasSum.tendsto_sum_nat
    rw [LFunction_eq_LSeries χ hz]
    exact (tendsto_nhds_unique (hconv z (hUsub (by simp only [U, Set.mem_setOf_eq]; linarith)))
      h1)
  have heq : Set.EqOn (dirichletSum f) (LFunction χ) U := by
    refine (hd.analyticOnNhd hUo).eqOn_of_preconnected_of_eventuallyEq
      ((differentiable_LFunction hχ).differentiableOn.analyticOnNhd hUo) hUc
      (z₀ := 2) (by simp [U]; norm_num) ?_
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds
      (show (2 : ℂ) ∈ {b : ℂ | (1 : ℝ) < b.re} by simp)] with z hz
    exact hgt z hz
  rw [← heq hs]
  exact hconv s (hUsub hs)

/-- **Davenport §1, p. 5.** For `χ ≠ 1`, `L(1, χ) = ∑_{n ≥ 1} χ(n)/n` (the partial sums
`∑_{n < M} χ(n)/n` converge to `L(1, χ)`). -/
@[kb "davenport1980" "Ch 1, p. 5"]
theorem tendsto_sum_char_div_LFunction {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) :
    Tendsto (fun M ↦ ∑ n ∈ range M, χ n / n) atTop (𝓝 (LFunction χ 1)) := by
  refine (tendsto_dirichletPartialSum_LFunction hχ (by norm_num)).congr fun M ↦ ?_
  refine sum_congr rfl fun n _ ↦ ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [LSeries.term_of_ne_zero hn, cpow_one]

/-! ### The logarithmic series on the unit circle -/

/-- `Re z < 1` for `|z| = 1`, `z ≠ 1`. -/
theorem re_lt_one_of_norm_eq_one {z : ℂ} (hz : ‖z‖ = 1) (hz1 : z ≠ 1) : z.re < 1 := by
  have hle : z.re ≤ 1 := (re_le_norm z).trans hz.le
  refine lt_of_le_of_ne hle fun h ↦ hz1 ?_
  have h2 : z.re ^ 2 + z.im ^ 2 = 1 := by
    have := Complex.sq_norm z
    rw [hz, normSq_apply] at this
    nlinarith
  have him : z.im = 0 := by rw [h] at h2; nlinarith
  exact Complex.ext h him

/-- **Davenport §1, p. 8.** For `|z| = 1`, `z ≠ 1`, the series `∑_{n ≥ 1} z^n/n` converges to
`-log(1 - z)` (principal value): Dirichlet's test, and Abel's limit theorem. -/
@[kb "davenport1980" "Ch 1, p. 8"]
theorem tendsto_sum_range_pow_div {z : ℂ} (hz : ‖z‖ = 1) (hz1 : z ≠ 1) :
    Tendsto (fun M ↦ ∑ n ∈ range M, z ^ n / n) atTop (𝓝 (-log (1 - z))) := by
  have hz1' : z - 1 ≠ 0 := sub_ne_zero.mpr hz1
  -- convergence (Dirichlet's test)
  have hbound : ∀ n, ‖∑ i ∈ range n, z ^ (i + 1)‖ ≤ 2 / ‖z - 1‖ := by
    intro n
    have : ∑ i ∈ range n, z ^ (i + 1) = z * ((z ^ n - 1) / (z - 1)) := by
      rw [← geom_sum_eq hz1, mul_sum]; exact sum_congr rfl fun i _ ↦ by ring
    rw [this, norm_mul, hz, one_mul, norm_div]
    gcongr
    calc ‖z ^ n - 1‖ ≤ ‖z ^ n‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, hz, one_pow, norm_one]; norm_num
  have hanti : Antitone (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) := by
    intro a b hab
    exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hab 1)
  have hlim0 : Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨l, hl⟩ := cauchySeq_tendsto_of_complete
    (hanti.cauchySeq_series_mul_of_tendsto_zero_of_bounded hlim0 hbound)
  have hl' : Tendsto (fun M ↦ ∑ n ∈ range M, z ^ n / n) atTop (𝓝 l) := by
    refine (tendsto_add_atTop_iff_nat 1).mp (hl.congr fun M ↦ ?_)
    rw [sum_range_succ', pow_zero, Nat.cast_zero, div_zero, add_zero]
    refine sum_congr rfl fun i _ ↦ ?_
    rw [Complex.real_smul]
    push_cast
    ring
  -- Abel's limit theorem identifies the sum
  have habel := tendsto_tsum_powerSeries_nhdsWithin_lt (f := fun n ↦ z ^ n / n) hl'
  rw [tendsto_map'_iff] at habel
  have hslit : 1 - z ∈ slitPlane := by
    rw [mem_slitPlane_iff]; left
    simp only [sub_re, one_re]
    linarith [re_lt_one_of_norm_eq_one hz hz1]
  have hcont : Tendsto (fun x : ℝ ↦ -log (1 - (x : ℂ) * z)) (𝓝[<] 1) (𝓝 (-log (1 - z))) := by
    have hc : ContinuousAt (fun x : ℝ ↦ -log (1 - (x : ℂ) * z)) 1 := by
      have h1 : ContinuousAt (fun x : ℝ ↦ 1 - (x : ℂ) * z) 1 := by fun_prop
      have h2 : ContinuousAt log ((fun x : ℝ ↦ 1 - (x : ℂ) * z) 1) := by
        simp only [ofReal_one, one_mul]; exact continuousAt_clog hslit
      exact (ContinuousAt.comp (f := fun x : ℝ ↦ 1 - (x : ℂ) * z) h2 h1).neg
    have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Iio 1))
    simpa using this
  have hev : (fun x : ℝ ↦ ∑' n : ℕ, z ^ n / n * (x : ℂ) ^ n) =ᶠ[𝓝[<] 1]
      fun x ↦ -log (1 - (x : ℂ) * z) := by
    filter_upwards [Ioo_mem_nhdsLT (show (-1 : ℝ) < 1 by norm_num)] with x hx
    have hxz : ‖(x : ℂ) * z‖ < 1 := by
      rw [norm_mul, hz, mul_one, norm_real, Real.norm_eq_abs, abs_lt]; exact ⟨hx.1, hx.2⟩
    rw [← (hasSum_taylorSeries_neg_log hxz).tsum_eq]
    exact tsum_congr fun n ↦ by rw [mul_pow]; ring
  simp only [Function.comp_def] at habel
  have := habel.congr' hev
  rw [tendsto_nhds_unique this hcont] at hl'
  exact hl'

/-- **Davenport §1, p. 8.** For `0 < θ < 2π`:
`-log(1 - e^{iθ}) = -log(2 sin(θ/2)) + i(π - θ)/2`. -/
@[kb "davenport1980" "Ch 1, p. 8"]
theorem neg_log_one_sub_exp {θ : ℝ} (h0 : 0 < θ) (h2 : θ < 2 * π) :
    -log (1 - cexp (θ * I)) = -(Real.log (2 * Real.sin (θ / 2)) : ℂ) + ((π - θ) / 2 : ℝ) * I := by
  have hs : 0 < Real.sin (θ / 2) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  set w : ℂ := (Real.log (2 * Real.sin (θ / 2)) : ℂ) + ((θ - π) / 2 : ℝ) * I
  have hw : cexp w = 1 - cexp (θ * I) := by
    simp only [w]
    rw [Complex.exp_add, ← ofReal_exp, Real.exp_log (by positivity), Complex.exp_mul_I]
    rw [← ofReal_cos, ← ofReal_sin]
    have hc : Real.cos ((θ - π) / 2) = Real.sin (θ / 2) := by
      rw [show (θ - π) / 2 = θ / 2 - π / 2 by ring, Real.cos_sub_pi_div_two]
    have hsn : Real.sin ((θ - π) / 2) = -Real.cos (θ / 2) := by
      rw [show (θ - π) / 2 = θ / 2 - π / 2 by ring, Real.sin_sub_pi_div_two]
    rw [hc, hsn, Complex.exp_mul_I, ← ofReal_cos, ← ofReal_sin]
    have hcos : Real.cos θ = 1 - 2 * Real.sin (θ / 2) ^ 2 := by
      have h := Real.cos_two_mul (θ / 2)
      rw [show 2 * (θ / 2) = θ by ring] at h
      nlinarith [Real.sin_sq_add_cos_sq (θ / 2)]
    have hsin : Real.sin θ = 2 * Real.sin (θ / 2) * Real.cos (θ / 2) := by
      have h := Real.sin_two_mul (θ / 2)
      rw [show 2 * (θ / 2) = θ by ring] at h
      exact h
    rw [hcos, hsin]
    push_cast
    ring
  have him : w.im = (θ - π) / 2 := by simp [w]
  rw [← hw, log_exp (by rw [him]; linarith [Real.pi_pos]) (by rw [him]; linarith [Real.pi_pos])]
  simp only [w]
  push_cast
  ring

/-! ### `L(1, χ)` for a primitive character -/

theorem norm_stdAddChar (b : ZMod N) : ‖(ZMod.stdAddChar b : ℂ)‖ = 1 := by
  rw [ZMod.stdAddChar_apply, Circle.norm_coe]

/-- **Davenport §1, p. 8, (6); §6, p. 50.** For a primitive character `χ` modulo `N > 1`,
`L(1, χ) = -(1/τ(χ̄)) ∑_{m=1}^{N-1} χ̄(m) log(1 - e(m/N))`. -/
@[kb "davenport1980" "Ch 1, p. 8, (6); Ch 6, p. 50"]
theorem LFunction_one_eq_neg_sum_log {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive)
    (hN : N ≠ 1) :
    LFunction χ 1 = -(gaussSum χ⁻¹ ZMod.stdAddChar)⁻¹ *
      ∑ m ∈ Ico 1 N, χ⁻¹ m * log (1 - ZMod.stdAddChar (m : ZMod N)) := by
  set ψ : AddChar (ZMod N) ℂ := ZMod.stdAddChar
  set τ := gaussSum χ⁻¹ ψ
  have hχ1 : χ ≠ 1 := by
    rintro rfl
    have h := hχ
    rw [IsPrimitive, DirichletCharacter.conductor_one] at h
    exact hN h.symm
  have hτ : τ ≠ 0 := by
    intro h
    have := norm_gaussSum_stdAddChar hχ.inv
    rw [show gaussSum χ⁻¹ ZMod.stdAddChar = τ from rfl, h, norm_zero] at this
    exact (Real.sqrt_pos.mpr (by exact_mod_cast NeZero.pos N)).ne' this.symm
  -- `χ(n) τ = ∑_b χ̄(b) ψ(b)^n`
  have hexp : ∀ n : ℕ, χ n * τ = ∑ b : ZMod N, χ⁻¹ b * ψ b ^ n := by
    intro n
    have := gaussSum_mulShift_of_isPrimitive hχ.inv (n : ZMod N) (e := ψ)
    rw [inv_inv] at this
    rw [← this, gaussSum]
    refine sum_congr rfl fun b _ ↦ ?_
    rw [AddChar.mulShift_apply, ← nsmul_eq_mul, AddChar.map_nsmul_eq_pow]
  -- the partial sums
  have hpart : ∀ M, ∑ n ∈ range M, χ n / n =
      τ⁻¹ * ∑ b : ZMod N, χ⁻¹ b * ∑ n ∈ range M, ψ b ^ n / n := by
    intro M
    rw [mul_sum]
    simp_rw [mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun n _ ↦ ?_
    have h' : ∑ i : ZMod N, χ⁻¹ i * (ψ i ^ n / n) = (χ n * τ) / n := by
      rw [hexp n, sum_div]; exact sum_congr rfl fun _ _ ↦ by ring
    rw [← mul_sum, h']
    field_simp
  have hlim : Tendsto (fun M ↦ τ⁻¹ * ∑ b : ZMod N, χ⁻¹ b * ∑ n ∈ range M, ψ b ^ n / n) atTop
      (𝓝 (τ⁻¹ * ∑ b : ZMod N, χ⁻¹ b * -log (1 - ψ b))) := by
    refine (tendsto_finsetSum _ fun b _ ↦ ?_).const_mul _
    by_cases hb : b = 0
    · rw [hb, (χ⁻¹).map_zero' hN]; simp
    · refine (tendsto_sum_range_pow_div (norm_stdAddChar b) ?_).const_mul _
      intro h
      exact hb (ZMod.injective_stdAddChar (by rw [h, AddChar.map_zero_eq_one]))
  have := tendsto_nhds_unique ((tendsto_sum_char_div_LFunction hχ1).congr hpart) hlim
  rw [this]
  have hs : ∑ b : ZMod N, χ⁻¹ b * -log (1 - ψ b) =
      ∑ m ∈ range N, χ⁻¹ (m : ZMod N) * -log (1 - ψ (m : ZMod N)) := by
    rw [← NTKB.sum_val_eq_sum_range
      (fun m : ℕ ↦ χ⁻¹ (m : ZMod N) * -log (1 - ψ (m : ZMod N)))]
    simp only [ZMod.natCast_zmod_val]
  rw [hs, range_eq_Ico, sum_eq_sum_Ico_succ_bot (NeZero.pos N)]
  simp only [Nat.cast_zero, (χ⁻¹).map_zero' hN, zero_mul, zero_add, mul_neg, sum_neg_distrib]
  ring

end NTKB.Davenport
