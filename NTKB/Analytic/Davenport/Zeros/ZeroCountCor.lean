/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Davenport.Zeros.LZeroCount

/-!
# Corollaries of the zero counts

* **Davenport, Ch. 15, p. 98 (row 15-10, in the equivalent form for `N(T)`)**:
  `N(T) ~ (T/2π) log T` (`Davenport.tendsto_zetaZeroCount_div`); Davenport's `γ_n ~ 2πn/log n` for
  the `n`-th ordinate is the inverse form of this.
* **Davenport, Ch. 16, p. 102 (row 16-8)**: there are `T₀`, `c > 0` and `q₀` such that for every
  primitive `χ` mod `q ≥ q₀`, `N(T₀, χ) ≥ c log q` (`Davenport.LZeroCount_ge_log`), so the bound
  `O(log q)` of 16-5 and 16-6 at `t = 0` is best possible.
-/

open Filter Topology
open scoped Real

namespace NTKB

/-- **Davenport, Ch. 15, p. 98 (row 15-10, `N(T)` form)**: `N(T)/((T/2π) log T) → 1`. -/
@[kb "davenport1980" "Ch 15, p. 98"]
theorem Davenport.tendsto_zetaZeroCount_div :
    Tendsto (fun T : ℝ ↦ (zetaZeroCount T : ℝ) / (T / (2 * π) * Real.log T)) atTop (𝓝 1) := by
  obtain ⟨A, hA, h⟩ := Davenport.zetaZeroCount_sub_le
  have hπ : 0 < π := Real.pi_pos
  -- `N/D = 1 - (log 2π + 1)/log T + (N - M)/D`
  have hlog : Tendsto (fun T : ℝ ↦ (Real.log (2 * π) + 1) / Real.log T) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
  have herr : Tendsto (fun T : ℝ ↦ ((zetaZeroCount T : ℝ) -
      (T / (2 * π) * Real.log (T / (2 * π)) - T / (2 * π))) / (T / (2 * π) * Real.log T))
      atTop (𝓝 0) := by
    have hb : Tendsto (fun T : ℝ ↦ 2 * π * A / T) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    rw [tendsto_zero_iff_abs_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun T ↦ abs_nonneg _) ?_ hb
    filter_upwards [eventually_ge_atTop 3] with T hT
    have hT0 : 0 < T := by linarith
    have hlogT : 0 < Real.log T := Real.log_pos (by linarith)
    show |_| ≤ _
    rw [abs_div, abs_of_pos (by positivity : 0 < T / (2 * π) * Real.log T),
      div_le_div_iff₀ (by positivity) hT0]
    have := h T hT
    have e : 2 * π * A * (T / (2 * π) * Real.log T) = A * Real.log T * T := by field_simp
    rw [e]
    nlinarith
  have hsum := (tendsto_const_nhds (x := (1 : ℝ))).sub hlog |>.add herr
  rw [sub_zero, add_zero] at hsum
  refine hsum.congr' ?_
  filter_upwards [eventually_ge_atTop 3] with T hT
  have hT0 : 0 < T := by linarith
  have hlogT : 0 < Real.log T := Real.log_pos (by linarith)
  have hl : Real.log (T / (2 * π)) = Real.log T - Real.log (2 * π) :=
    Real.log_div hT0.ne' (by positivity)
  rw [hl]
  field_simp
  ring

/-- **Davenport, Ch. 16, p. 102 (row 16-8)**: there are `T₀ ≥ 3`, `c > 0` and `q₀` such that for
every primitive `χ` mod `q ≥ q₀`, at least `c log q` zeros of `L(s, χ)` have `|γ| < T₀`. -/
@[kb "davenport1980" "Ch 16, p. 102"]
theorem Davenport.LZeroCount_ge_log :
    ∃ T₀ c q₀ : ℝ, 3 ≤ T₀ ∧ 0 < c ∧ ∀ {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N},
      χ.IsPrimitive → N ≠ 1 → q₀ ≤ N → c * Real.log N ≤ LZeroCount χ T₀ := by
  obtain ⟨A, hA, h⟩ := Davenport.LZeroCount_sub_le
  have hπ : 0 < π := Real.pi_pos
  set T₀ : ℝ := 2 * π * A + 3 with hT₀
  have hT₀3 : 3 ≤ T₀ := by rw [hT₀]; nlinarith
  have hT₀0 : 0 < T₀ := by linarith
  set K : ℝ := T₀ / π * Real.log (T₀ / (2 * π)) - T₀ / π - A * Real.log T₀ with hK
  refine ⟨T₀, A / 2, Real.exp (2 * |K| / A), hT₀3, by positivity, fun {N} _ {χ} hχ hN hq ↦ ?_⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hlogN : 2 * |K| / A ≤ Real.log N := by
    rw [← Real.log_exp (2 * |K| / A)]; exact Real.log_le_log (Real.exp_pos _) hq
  have hb := h hχ hN T₀ hT₀3
  rw [abs_le] at hb
  have e1 : Real.log (N * T₀ / (2 * π)) = Real.log N + Real.log (T₀ / (2 * π)) := by
    rw [mul_div_assoc, Real.log_mul hN0.ne' (by positivity)]
  have e2 : Real.log (N * T₀) = Real.log N + Real.log T₀ := Real.log_mul hN0.ne' hT₀0.ne'
  rw [e1, e2] at hb
  have hcoef : 2 * A ≤ T₀ / π := by rw [hT₀, le_div_iff₀ hπ]; nlinarith
  have hKabs : -|K| ≤ K := neg_abs_le K
  have hlN : 0 ≤ Real.log N := le_trans (by positivity) hlogN
  have h3 : |K| ≤ A * Real.log N / 2 := by
    rw [div_le_iff₀ hA] at hlogN; linarith
  have hmain : 0 ≤ (T₀ / π - 2 * A) * Real.log N := mul_nonneg (by linarith) hlN
  nlinarith [hb.1]

end NTKB
