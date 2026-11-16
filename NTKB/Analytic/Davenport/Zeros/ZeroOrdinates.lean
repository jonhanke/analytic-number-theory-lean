/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Davenport.Zeros.ZeroCountCor

/-!
# The ordinates of the zeros: `γ_n ~ 2πn / log n`

**Davenport, Ch. 15, p. 98 (row 15-10).** Arrange the ordinates `0 < γ_1 ≤ γ_2 ≤ ...` of the zeros of
`ζ(s)` in the upper half of the critical strip, with multiplicity. Then `γ_n ~ 2πn / log n`. Here
`γ_n = inf {T : N(T) ≥ n}` (`zetaOrdinate`), the `n`-th ordinate, and the statement follows from
`N(T) ~ (T/2π) log T` (`Davenport.tendsto_zetaZeroCount_div`) by inversion.
-/

open Filter Topology
open scoped Real

namespace NTKB

/-- The `n`-th ordinate `γ_n` of the zeros of `ζ` in the upper half of the critical strip,
counted with multiplicity: `γ_n = inf {T : N(T) ≥ n}`. -/
noncomputable def zetaOrdinate (n : ℕ) : ℝ := sInf {T : ℝ | n ≤ zetaZeroCount T}

lemma zetaZeroCount_of_nonpos {T : ℝ} (hT : T ≤ 0) : zetaZeroCount T = 0 := by
  unfold zetaZeroCount
  have : IsEmpty {ρ : ZeroIndex riemannXi // 0 < ρ.val.im ∧ ρ.val.im < T} :=
    ⟨fun ρ ↦ by linarith [ρ.2.1, ρ.2.2]⟩
  exact Nat.card_of_isEmpty

lemma tendsto_zetaZeroCount_atTop :
    Tendsto (fun T : ℝ ↦ (zetaZeroCount T : ℝ)) atTop atTop := by
  have hD : Tendsto (fun T : ℝ ↦ T / (2 * π) * Real.log T) atTop atTop := by
    have h1 : Tendsto (fun T : ℝ ↦ T / (2 * π)) atTop atTop :=
      tendsto_id.atTop_div_const (by positivity)
    exact h1.atTop_mul_atTop₀ Real.tendsto_log_atTop
  have h := (Davenport.tendsto_zetaZeroCount_div).pos_mul_atTop one_pos hD
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 1] with T hT
  have hT0 : 0 < T := by linarith
  have hlogT : 0 < Real.log T := Real.log_pos hT
  have : T / (2 * π) * Real.log T ≠ 0 := by positivity
  field_simp

/-- Openness: if `n ≤ N(T)` with `n ≥ 1` then `n ≤ N(T')` for some `T' < T`. -/
lemma exists_lt_le_zetaZeroCount {n : ℕ} (hn : 1 ≤ n) {T : ℝ} (h : n ≤ zetaZeroCount T) :
    ∃ T' < T, n ≤ zetaZeroCount T' := by
  classical
  have hne : ((zerosBelow T).filter fun ρ ↦ 0 < ρ.val.im).Nonempty := by
    rw [← Finset.card_pos, ← zetaZeroCount_eq_card]; omega
  obtain ⟨ρ0, hρ0, hmax⟩ := Finset.exists_max_image _ (fun ρ : ZeroIndex riemannXi ↦ ρ.val.im) hne
  have hρ0' := Finset.mem_filter.mp hρ0
  have hlt : ρ0.val.im < T := by
    have := mem_zerosBelow.mp hρ0'.1
    rw [abs_of_pos hρ0'.2] at this
    exact this
  refine ⟨(ρ0.val.im + T) / 2, by linarith, ?_⟩
  refine h.trans ?_
  rw [zetaZeroCount_eq_card, zetaZeroCount_eq_card]
  refine Finset.card_le_card fun ρ hρ ↦ ?_
  have hρ' := Finset.mem_filter.mp hρ
  have h1 := hmax ρ hρ
  rw [Finset.mem_filter, mem_zerosBelow]
  refine ⟨?_, hρ'.2⟩
  rw [abs_of_pos hρ'.2]
  linarith

lemma tendsto_h_atTop : Tendsto (fun n : ℕ ↦ 2 * π * n / Real.log n) atTop atTop := by
  have h1 : Tendsto (fun x : ℝ ↦ Real.log x / x) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have h1' : Tendsto (fun x : ℝ ↦ Real.log x / x) atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨h1, ?_⟩
    filter_upwards [eventually_gt_atTop 1] with x hx
    exact div_pos (Real.log_pos hx) (by linarith)
  have h2 : Tendsto (fun x : ℝ ↦ x / Real.log x) atTop atTop := by
    refine (tendsto_inv_nhdsGT_zero.comp h1').congr' ?_
    filter_upwards with x
    simp
  have h3 := (h2.comp tendsto_natCast_atTop_atTop).const_mul_atTop (show 0 < 2 * π by positivity)
  refine h3.congr fun n ↦ ?_
  simp only [Function.comp]
  ring

lemma tendsto_log_ratio {c : ℝ} (hc : 0 < c) :
    Tendsto (fun n : ℕ ↦ Real.log (c * (2 * π * n / Real.log n)) / Real.log n) atTop (𝓝 1) := by
  have hl : Tendsto (fun n : ℕ ↦ Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have h1 : Tendsto (fun x : ℝ ↦ Real.log x / x) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have h2 : Tendsto (fun n : ℕ ↦ Real.log (Real.log n) / Real.log n) atTop (𝓝 0) :=
    h1.comp hl
  have h3 : Tendsto (fun n : ℕ ↦ Real.log (c * (2 * π)) / Real.log n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hl
  have h4 := (tendsto_const_nhds (x := (1 : ℝ))).add (h3.sub h2)
  rw [sub_zero, add_zero] at h4
  refine h4.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hn1 : (1 : ℝ) < n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hL : 0 < Real.log n := Real.log_pos hn1
  have e : Real.log (c * (2 * π * n / Real.log n)) =
      Real.log (c * (2 * π)) + Real.log n - Real.log (Real.log n) := by
    rw [show c * (2 * π * n / Real.log n) = (c * (2 * π)) * n / Real.log n by ring,
      Real.log_div (by positivity) hL.ne', Real.log_mul (by positivity) hn0.ne']
  rw [e]
  field_simp
  ring

lemma zetaZeroCount_ratio {c : ℝ} (hc : 0 < c) :
    Tendsto (fun n : ℕ ↦ (zetaZeroCount (c * (2 * π * n / Real.log n)) : ℝ) / n) atTop (𝓝 c) := by
  have hT : Tendsto (fun n : ℕ ↦ c * (2 * π * n / Real.log n)) atTop atTop :=
    tendsto_h_atTop.const_mul_atTop hc
  have h1 := (Davenport.tendsto_zetaZeroCount_div).comp hT
  have h2 := (tendsto_const_nhds (x := c)).mul (tendsto_log_ratio hc)
  have h3 := h1.mul h2
  rw [one_mul, mul_one] at h3
  refine h3.congr' ?_
  filter_upwards [eventually_ge_atTop 2, hT.eventually_gt_atTop 1] with n hn hTn
  have hn1 : (1 : ℝ) < n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hL : 0 < Real.log n := Real.log_pos hn1
  have hLT : 0 < Real.log (c * (2 * π * n / Real.log n)) := Real.log_pos hTn
  have hπ := Real.pi_pos
  simp only [Function.comp]
  field_simp
  rw [mul_div_cancel_right₀]
  rw [show c * 2 * π * (n : ℝ) / Real.log n = c * (2 * π * n / Real.log n) by ring]
  exact hLT.ne'

/-- `N(T) ≥ n` exactly when `T > γ_n` (for `n ≥ 1`). -/
lemma le_zetaZeroCount_iff {n : ℕ} (hn : 1 ≤ n) (T : ℝ) :
    n ≤ zetaZeroCount T ↔ zetaOrdinate n < T := by
  classical
  set S : Set ℝ := {T : ℝ | n ≤ zetaZeroCount T} with hS
  have hbdd : BddBelow S := ⟨0, fun T hT ↦ by
    by_contra hlt
    push Not at hlt
    have := zetaZeroCount_of_nonpos hlt.le
    simp only [hS, Set.mem_ofPred_eq] at hT
    omega⟩
  have hne : S.Nonempty := by
    obtain ⟨T, hT⟩ := (tendsto_zetaZeroCount_atTop.eventually_ge_atTop (n : ℝ)).exists
    exact ⟨T, by simp only [hS, Set.mem_ofPred_eq]; exact_mod_cast hT⟩
  constructor
  · intro h
    obtain ⟨T', hT', h'⟩ := exists_lt_le_zetaZeroCount hn h
    exact lt_of_le_of_lt (csInf_le hbdd h') hT'
  · intro h
    obtain ⟨T', hT'S, hT'⟩ := exists_lt_of_csInf_lt hne h
    exact hT'S.trans (zetaZeroCount_mono hT'.le)

/-- **Davenport, Ch. 15, p. 98 (row 15-10)**: `γ_n ~ 2πn / log n`, i.e.
`γ_n / (2πn / log n) → 1` as `n → ∞`. -/
@[kb "davenport1980" "Ch 15, p. 98"]
theorem Davenport.tendsto_zetaOrdinate_div :
    Tendsto (fun n : ℕ ↦ zetaOrdinate n / (2 * π * n / Real.log n)) atTop (𝓝 1) := by
  have hπ := Real.pi_pos
  rw [tendsto_order]
  have hev : ∀ᶠ n : ℕ in atTop, 2 ≤ n := eventually_ge_atTop 2
  constructor
  · intro a ha
    set c : ℝ := max ((a + 1) / 2) (1 / 2) with hcdef
    have hc0 : 0 < c := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
    have hc1 : c < 1 := max_lt (by linarith) (by norm_num)
    have hac : a < c := lt_of_lt_of_le (by linarith) (le_max_left _ _)
    have hr := (zetaZeroCount_ratio hc0).eventually (gt_mem_nhds hc1)
    filter_upwards [hr, hev] with n hn hn2
    have hn1 : (1 : ℝ) < n := by exact_mod_cast hn2
    have hn0 : (0 : ℝ) < n := by linarith
    have hL : 0 < Real.log n := Real.log_pos hn1
    have hh : 0 < 2 * π * n / Real.log n := by positivity
    rw [lt_div_iff₀ hh]
    by_contra hcon
    have hlt : zetaOrdinate n < c * (2 * π * n / Real.log n) := by nlinarith
    have h1 := (le_zetaZeroCount_iff (by omega : 1 ≤ n) _).mpr hlt
    have h2 : (n : ℝ) ≤ zetaZeroCount (c * (2 * π * n / Real.log n)) := by exact_mod_cast h1
    rw [div_lt_one hn0] at hn
    linarith
  · intro a ha
    set c : ℝ := (1 + a) / 2 with hcdef
    have hc1 : 1 < c := by linarith
    have hc0 : 0 < c := by linarith
    have hr := (zetaZeroCount_ratio hc0).eventually (lt_mem_nhds hc1)
    filter_upwards [hr, hev] with n hn hn2
    have hn1 : (1 : ℝ) < n := by exact_mod_cast hn2
    have hn0 : (0 : ℝ) < n := by linarith
    have hL : 0 < Real.log n := Real.log_pos hn1
    have hh : 0 < 2 * π * n / Real.log n := by positivity
    rw [div_lt_iff₀ hh]
    rw [lt_div_iff₀ hn0] at hn
    have h2 : n ≤ zetaZeroCount (c * (2 * π * n / Real.log n)) := by
      have : (n : ℝ) ≤ zetaZeroCount (c * (2 * π * n / Real.log n)) := by linarith
      exact_mod_cast this
    have := (le_zetaZeroCount_iff (by omega : 1 ≤ n) _).mp h2
    nlinarith

end NTKB
