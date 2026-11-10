/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Davenport.Zeros.ExplicitSum
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# `ψ₀(x) - J(x, T)` for integral `x`

**Davenport, Ch. 17, pp. 106-107 and (11), p. 110.** With `ψ₀(N) = ∑_{n < N} Λ(n) + Λ(N)/2` and
`c = 1 + 1/log N`, `|ψ₀(N) - J(N, T)| ≪ N log² N / T` for integers `N ≥ 3`.
-/

open Filter Topology Complex Set
open scoped Real ArithmeticFunction.vonMangoldt

namespace NTKB

/-- **Davenport, Ch. 17, p. 104 (row 17-1)**: `ψ₀(N) = ψ(N) - Λ(N)/2 = ∑_{n < N} Λ(n) + Λ(N)/2`
at an integer `N` (the mean of the left and right limits of `ψ`). -/
noncomputable def psi0 (N : ℕ) : ℝ := (∑ n ∈ Finset.range N, Λ n) + Λ N / 2

/-- The step function `δ(N/n)` of the discontinuous integral. -/
noncomputable def perronStep (N n : ℕ) : ℝ := if n < N then 1 else if n = N then 1 / 2 else 0

lemma hasSum_psi0 (N : ℕ) : HasSum (fun n ↦ (Λ n : ℂ) * perronStep N n) (psi0 N) := by
  have : ∀ n ∉ Finset.range (N + 1), (Λ n : ℂ) * perronStep N n = 0 := by
    intro n hn
    rw [Finset.mem_range, not_lt] at hn
    have h1 : ¬ n < N := by omega
    rcases eq_or_ne n N with rfl | hnN
    · omega
    · simp [perronStep, h1, hnN]
  have h : HasSum (fun n ↦ (Λ n : ℂ) * perronStep N n)
      (∑ n ∈ Finset.range (N + 1), (Λ n : ℂ) * perronStep N n) :=
    hasSum_sum_of_ne_finset_zero this
  convert h using 1
  rw [Finset.sum_range_succ, psi0]
  push_cast
  congr 1
  · refine Finset.sum_congr rfl fun n hn ↦ ?_
    simp [perronStep, Finset.mem_range.mp hn]
  · simp [perronStep]; ring

/-- `1/|log(N/n)| ≤ 2N/|N - n|` for `N/2 < n < 2N`, `n ≠ N`. -/
lemma inv_abs_log_le {N n : ℝ} (hN : 0 < N) (hn : 0 < n) (hne : n ≠ N) :
    1 / |Real.log (N / n)| ≤ max N n / |N - n| := by
  have hlog : |N - n| / max N n ≤ |Real.log (N / n)| := by
    rcases lt_or_gt_of_ne hne with h | h
    · -- `n < N`
      rw [max_eq_left h.le, abs_of_pos (sub_pos.mpr h),
        abs_of_pos (Real.log_pos ((one_lt_div hn).mpr h))]
      have := Real.add_one_le_exp (-(N - n) / N)
      have h2 : Real.log (n / N) ≤ -(N - n) / N := by
        have h3 := Real.log_le_sub_one_of_pos (div_pos hn hN)
        have : n / N - 1 = -(N - n) / N := by field_simp; ring
        linarith
      rw [Real.log_div hN.ne' hn.ne'] at *
      rw [Real.log_div hn.ne' hN.ne'] at h2
      have : (N - n) / N = -(-(N - n) / N) := by ring
      linarith
    · -- `N < n`
      rw [max_eq_right h.le, abs_of_neg (sub_neg.mpr h),
        abs_of_neg (Real.log_neg (div_pos hN hn) ((div_lt_one hn).mpr h))]
      have h3 := Real.log_le_sub_one_of_pos (div_pos hN hn)
      have : N / n - 1 = -(n - N) / n := by field_simp; ring
      have e2 : -(N - n) / n = -(-(n - N) / n) := by ring
      linarith
  have hpos : 0 < |N - n| := abs_pos.mpr (sub_ne_zero.mpr hne.symm)
  have hmax : 0 < max N n := lt_max_of_lt_left hN
  rw [div_le_div_iff₀ (by
    have := div_pos hpos hmax; linarith) hpos, one_mul]
  rw [div_le_iff₀ hmax] at hlog
  linarith

lemma harmonic_eq_sum (n : ℕ) : (harmonic n : ℝ) = ∑ k ∈ Finset.range n, 1 / ((k : ℝ) + 1) := by
  simp only [harmonic, one_div]
  push_cast
  rfl

/-- `∑_{n < 2N, n ≠ N} 1/|N - n| ≤ 2 (1 + log N)`. -/
lemma sum_inv_abs_sub_le (N : ℕ) :
    ∑ n ∈ (Finset.range (2 * N)).filter (· ≠ N), 1 / |(N : ℝ) - n| ≤ 2 * (1 + Real.log N) := by
  have hsplit : (Finset.range (2 * N)).filter (· ≠ N) = Finset.range N ∪ Finset.Ico (N + 1) (2 * N) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_union, Finset.mem_Ico]
    omega
  have hdisj : Disjoint (Finset.range N) (Finset.Ico (N + 1) (2 * N)) := by
    rw [Finset.disjoint_left]
    intro n h1 h2
    simp only [Finset.mem_range, Finset.mem_Ico] at h1 h2
    omega
  rw [hsplit, Finset.sum_union hdisj]
  have h1 : ∑ n ∈ Finset.range N, 1 / |(N : ℝ) - n| = harmonic N := by
    rw [harmonic_eq_sum, ← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    have hk' := Finset.mem_range.mp hk
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    push_cast
    rw [abs_of_pos (by linarith)]
    ring_nf
  have h2 : ∑ n ∈ Finset.Ico (N + 1) (2 * N), 1 / |(N : ℝ) - n| = harmonic (N - 1) := by
    rw [harmonic_eq_sum, Finset.sum_Ico_eq_sum_range,
      show 2 * N - (N + 1) = N - 1 by omega]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    push_cast
    rw [abs_of_neg (by linarith), neg_sub]
    ring_nf
  rw [h1, h2]
  have hH1 := harmonic_le_one_add_log N
  have hH2 := harmonic_le_one_add_log (N - 1)
  have hmono : Real.log (N - 1 : ℕ) ≤ Real.log N := by
    rcases Nat.eq_zero_or_pos (N - 1) with h | h
    · rw [h]; simp; exact Real.log_natCast_nonneg N
    · exact Real.log_le_log (by exact_mod_cast h) (by exact_mod_cast Nat.sub_le N 1)
  linarith

/-- The pointwise bound for `Λ(n) |I(N/n, T) - δ(N/n)|`. -/
lemma vonMangoldt_mul_perron_sub_le {N : ℕ} (hN : 3 ≤ N) {T : ℝ} (hT : 0 < T) (n : ℕ) :
    Λ n * ‖perronIntegral (N / n) (1 + 1 / Real.log N) T - perronStep N n‖ ≤
      (N : ℝ) ^ (1 + 1 / Real.log N) / (π * T * Real.log 2) *
          (Λ n * (n : ℝ) ^ (-(1 + 1 / Real.log N))) +
        (if n < 2 * N ∧ n ≠ N then 8 * N * Real.log (2 * N) / (π * T) / |(N : ℝ) - n| else 0) +
        (if n = N then Λ N * (1 + 1 / Real.log N) / (π * T) else 0) := by
  set c := 1 + 1 / Real.log N with hcdef
  have hπ := Real.pi_pos
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hL : 1 < Real.log N := by
    rw [Real.lt_log_iff_exp_lt hN0]
    have := Real.exp_one_lt_d9
    have : (3 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hc1 : 1 < c := by rw [hcdef]; have : 0 < 1 / Real.log N := by positivity
                         linarith
  have hc2 : c ≤ 2 := by
    rw [hcdef]; have : 1 / Real.log N ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    linarith
  have hc0 : 0 < c := by linarith
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hΛ := ArithmeticFunction.vonMangoldt_nonneg (n := n)
  have hK1 : 0 ≤ (N : ℝ) ^ c / (π * T * Real.log 2) * (Λ n * (n : ℝ) ^ (-c)) := by positivity
  have hK2 : 0 ≤ (if n < 2 * N ∧ n ≠ N then 8 * N * Real.log (2 * N) / (π * T) / |(N : ℝ) - n|
      else 0) := by
    split_ifs
    · have : 0 ≤ Real.log (2 * N) := Real.log_nonneg (by linarith)
      positivity
    · exact le_rfl
  have hK3 : 0 ≤ (if n = N then Λ N * c / (π * T) else 0) := by
    split_ifs
    · have := ArithmeticFunction.vonMangoldt_nonneg (n := N); positivity
    · exact le_rfl
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [ArithmeticFunction.map_zero, zero_mul]; linarith
  rcases eq_or_ne n N with rfl | hnN
  · -- `n = N`
    have hstep : perronStep n n = 1 / 2 := by simp [perronStep]
    rw [hstep, div_self hN0.ne', if_pos rfl]
    have := norm_perronIntegral_one_sub_half hc0 hT
    push_cast at this ⊢
    have h3 : Λ n * ‖perronIntegral 1 c T - 1 / 2‖ ≤ Λ n * c / (π * T) := by
      rw [mul_div_assoc]; exact mul_le_mul_of_nonneg_left this hΛ
    have hfalse : ¬ (n < 2 * n ∧ n ≠ n) := fun h ↦ h.2 rfl
    rw [if_neg hfalse] at hK2 ⊢
    linarith
  -- `n ≠ N`
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  set y : ℝ := N / n with hy
  have hy0 : 0 < y := div_pos hN0 hn0
  have hy1 : y ≠ 1 := by
    rw [hy, Ne, div_eq_one_iff_eq hn0.ne']
    exact fun h ↦ hnN (by exact_mod_cast h.symm)
  have hlogy : 0 < |Real.log y| := abs_pos.mpr (fun h ↦ hy1 (by
    rcases Real.log_eq_zero.mp h with h | h | h <;> [linarith; exact h; linarith]))
  have hB : ‖perronIntegral y c T - perronStep N n‖ ≤ y ^ c / (π * T * |Real.log y|) := by
    rcases lt_or_gt_of_ne hnN with h | h
    · have hy1' : 1 < y := by rw [hy, one_lt_div hn0]; exact_mod_cast h
      have : perronStep N n = 1 := by simp [perronStep, h]
      rw [this]; push_cast
      exact norm_perronIntegral_gt_one_log hy1' hc0 hT
    · have hy1' : y < 1 := by rw [hy, div_lt_one hn0]; exact_mod_cast h
      have : perronStep N n = 0 := by simp [perronStep, not_lt.mpr h.le, h.ne']
      rw [this]; push_cast; rw [sub_zero]
      exact norm_perronIntegral_lt_one_log hy0 hy1' hc0 hT
  have hLHS : Λ n * ‖perronIntegral y c T - perronStep N n‖ ≤
      Λ n * (y ^ c / (π * T * |Real.log y|)) := mul_le_mul_of_nonneg_left hB hΛ
  have hyc : y ^ c = (N : ℝ) ^ c * (n : ℝ) ^ (-c) := by
    rw [hy, Real.div_rpow hN0.le hn0.le, Real.rpow_neg hn0.le, div_eq_mul_inv]
  rw [if_neg (Ne.symm hnN ∘ Eq.symm)] at hK3 ⊢
  by_cases hnear : (N : ℝ) / 2 < n ∧ (n : ℝ) < 2 * N
  · -- near `N`
    have hn2N : n < 2 * N := by exact_mod_cast hnear.2
    rw [if_pos ⟨hn2N, hnN⟩]
    have hlog : 1 / |Real.log y| ≤ max (N : ℝ) (n : ℝ) / |(N : ℝ) - n| :=
      inv_abs_log_le hN0 hn0 (fun h ↦ hnN (by exact_mod_cast h))
    have hmax : max (N : ℝ) n ≤ 2 * N := max_le (by linarith) hnear.2.le
    have hdiff : 0 < |(N : ℝ) - n| := abs_pos.mpr (sub_ne_zero.mpr (fun h ↦ hnN (by
      exact_mod_cast h.symm)))
    have hyc4 : y ^ c ≤ 4 := by
      have hy2 : y ≤ 2 := by rw [hy, div_le_iff₀ hn0]; linarith [hnear.1]
      calc y ^ c ≤ (max 1 y) ^ c := Real.rpow_le_rpow hy0.le (le_max_right _ _) hc0.le
        _ ≤ (max 1 y) ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (le_max_left _ _) hc2
        _ ≤ 2 ^ (2 : ℝ) := Real.rpow_le_rpow (by positivity) (max_le (by norm_num) hy2)
            (by norm_num)
        _ = 4 := by norm_num
    have hΛlog : Λ n ≤ Real.log (2 * N) := by
      refine ArithmeticFunction.vonMangoldt_le_log.trans (Real.log_le_log hn0 hnear.2.le)
    have h1 : Λ n * (y ^ c / (π * T * |Real.log y|)) =
        Λ n * y ^ c * (1 / |Real.log y|) / (π * T) := by
      field_simp
    rw [h1] at hLHS
    have h2 : Λ n * y ^ c * (1 / |Real.log y|) ≤ Real.log (2 * N) * 4 * (2 * N / |(N : ℝ) - n|) := by
      have hlogN : 0 ≤ Real.log (2 * N) := Real.log_nonneg (by linarith)
      have h3 : 1 / |Real.log y| ≤ 2 * N / |(N : ℝ) - n| :=
        hlog.trans (div_le_div_of_nonneg_right hmax hdiff.le)
      have hyc0 : 0 ≤ y ^ c := Real.rpow_nonneg hy0.le _
      calc Λ n * y ^ c * (1 / |Real.log y|) ≤ Real.log (2 * N) * 4 * (1 / |Real.log y|) := by
            gcongr
        _ ≤ Real.log (2 * N) * 4 * (2 * N / |(N : ℝ) - n|) := by gcongr
    have h4 : Λ n * y ^ c * (1 / |Real.log y|) / (π * T) ≤
        8 * N * Real.log (2 * N) / (π * T) / |(N : ℝ) - n| := by
      calc Λ n * y ^ c * (1 / |Real.log y|) / (π * T)
          ≤ Real.log (2 * N) * 4 * (2 * N / |(N : ℝ) - n|) / (π * T) := by gcongr
        _ = 8 * N * Real.log (2 * N) / (π * T) / |(N : ℝ) - n| := by ring
    linarith
  · -- far from `N`
    have hfar : Real.log 2 ≤ |Real.log y| := by
      push Not at hnear
      by_cases hle : (n : ℝ) ≤ N / 2
      · have : 2 ≤ y := by rw [hy, le_div_iff₀ hn0]; linarith
        rw [abs_of_pos (Real.log_pos (by linarith))]
        exact Real.log_le_log two_pos this
      · have h2N : 2 * N ≤ (n : ℝ) := hnear (by linarith)
        have : y ≤ 1 / 2 := by rw [hy, div_le_iff₀ hn0]; linarith
        rw [abs_of_neg (Real.log_neg hy0 (by linarith)), ← Real.log_inv]
        exact Real.log_le_log two_pos (by rw [le_inv_comm₀ two_pos hy0]; linarith)
    have h1 : Λ n * (y ^ c / (π * T * |Real.log y|)) ≤
        (N : ℝ) ^ c / (π * T * Real.log 2) * (Λ n * (n : ℝ) ^ (-c)) := by
      rw [hyc]
      have : (N : ℝ) ^ c * (n : ℝ) ^ (-c) / (π * T * |Real.log y|) ≤
          (N : ℝ) ^ c * (n : ℝ) ^ (-c) / (π * T * Real.log 2) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) (by gcongr)
      calc Λ n * ((N : ℝ) ^ c * (n : ℝ) ^ (-c) / (π * T * |Real.log y|))
          ≤ Λ n * ((N : ℝ) ^ c * (n : ℝ) ^ (-c) / (π * T * Real.log 2)) := by gcongr
        _ = _ := by ring
    have h2 : (0 : ℝ) ≤ if n < 2 * N ∧ n ≠ N then 8 * N * Real.log (2 * N) / (π * T) /
        |(N : ℝ) - n| else 0 := hK2
    linarith

/-- The Dirichlet series `∑ Λ(n) n^{-σ} = -ζ'/ζ(σ)` for real `σ > 1`. -/
lemma hasSum_vonMangoldt_rpow {σ : ℝ} (hσ : 1 < σ) :
    HasSum (fun n : ℕ ↦ Λ n * (n : ℝ) ^ (-σ)) (-(deriv riemannZeta σ / riemannZeta σ).re) := by
  have h1 : 1 < ((σ : ℝ) : ℂ).re := by simpa using hσ
  have e0 := neg_logDeriv_LFunction_eq_LSeries (1 : DirichletCharacter ℂ 1) h1
  rw [DirichletCharacter.LFunction_modOne_eq] at e0
  have s0 := Complex.reCLM.hasSum (DirichletCharacter.LSeriesSummable_twist_vonMangoldt
    (1 : DirichletCharacter ℂ 1) h1).LSeriesHasSum
  rw [← e0, Complex.reCLM_apply, neg_div, Complex.neg_re] at s0
  refine s0.congr_fun fun n ↦ ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  have t0 := term_twist_vonMangoldt_eq (1 : DirichletCharacter ℂ 1) σ 0 hn
  simp only [Complex.ofReal_zero, zero_mul, add_zero, neg_zero, Complex.exp_zero,
    mul_one] at t0
  rw [Complex.reCLM_apply, t0, MulChar.one_apply (isUnit_of_subsingleton _), one_mul,
    Complex.ofReal_re]

/-- The majorant for `Λ(n) |I(N/n, T) - δ(N/n)|` (with `c = 1 + 1/log N`): a summable `G` with
`∑ G ≤ 100 N log² N / T`. -/
lemma exists_perron_majorant {N : ℕ} (hN : 3 ≤ N) {T : ℝ} (hT : 0 < T) :
    ∃ G : ℕ → ℝ, ∃ S : ℝ, HasSum G S ∧ S ≤ 100 * N * Real.log N ^ 2 / T ∧
      ∀ n, Λ n * ‖perronIntegral (N / n) (1 + 1 / Real.log N) T - perronStep N n‖ ≤ G n := by
  set c := 1 + 1 / Real.log N with hcdef
  set L := Real.log N with hLdef
  have hπ := Real.pi_gt_three
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hL : 1 < L := by
    rw [hLdef, Real.lt_log_iff_exp_lt hN0]
    have := Real.exp_one_lt_d9
    linarith
  have hc1 : 1 < c := by rw [hcdef]; have : 0 < 1 / L := by positivity
                         linarith
  have hc2 : c ≤ 2 := by
    rw [hcdef]; have : 1 / L ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    linarith
  have hl2 := log_two_gt_two_thirds
  set K₁ : ℝ := (N : ℝ) ^ c / (π * T * Real.log 2)
  set K₂ : ℝ := 8 * N * Real.log (2 * N) / (π * T)
  have hS := hasSum_vonMangoldt_rpow hc1
  set S := -(deriv riemannZeta c / riemannZeta c).re
  have hp1 := hS.mul_left K₁
  have hp2 : HasSum (fun n : ℕ ↦ if n < 2 * N ∧ n ≠ N then K₂ / |(N : ℝ) - n| else 0)
      (∑ n ∈ (Finset.range (2 * N)).filter (· ≠ N), K₂ / |(N : ℝ) - n|) := by
    rw [Finset.sum_filter]
    have h : HasSum (fun n : ℕ ↦ if n < 2 * N ∧ n ≠ N then K₂ / |(N : ℝ) - n| else 0)
        (∑ n ∈ Finset.range (2 * N), if n < 2 * N ∧ n ≠ N then K₂ / |(N : ℝ) - n| else 0) :=
      hasSum_sum_of_ne_finset_zero fun n hn ↦ by
        rw [Finset.mem_range] at hn; simp [hn]
    convert h using 1
    refine Finset.sum_congr rfl fun n hn ↦ ?_
    simp [Finset.mem_range.mp hn]
  have hp3 : HasSum (fun n : ℕ ↦ if n = N then Λ N * c / (π * T) else 0) (Λ N * c / (π * T)) :=
    hasSum_ite_eq N _
  have hg := (hp1.add hp2).add hp3
  refine ⟨_, _, hg, ?_, fun n ↦ vonMangoldt_mul_perron_sub_le hN hT n⟩
  -- estimate the three parts
  have hNc : (N : ℝ) ^ c = N * Real.exp 1 := by
    rw [hcdef, Real.rpow_add hN0, Real.rpow_one, Real.rpow_def_of_pos hN0, ← hLdef,
      mul_one_div_cancel (by linarith)]
  have hSle : S ≤ L + 5 * Real.log 2 := by
    have := Davenport.neg_logDeriv_riemannZeta_real_le hc1 hc2
    have hc' : 1 / (c - 1) = L := by rw [hcdef]; field_simp; ring
    rw [hc'] at this
    exact this
  have hlog2 : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9; linarith
  have hS0 : 0 ≤ S := by
    have := hS.nonneg fun n ↦ mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
      (Real.rpow_nonneg n.cast_nonneg _)
    exact this
  have he := Real.exp_one_lt_d9
  have hK₁ : K₁ * S ≤ 10 * N * L ^ 2 / T := by
    have hπl : 2 ≤ π * Real.log 2 := by nlinarith
    have h5 : S ≤ 5 * L := by have := Real.log_two_lt_d9; linarith
    have hK : K₁ ≤ 3 * N / (2 * T) := by
      simp only [K₁]
      rw [hNc, div_le_div_iff₀ (by positivity) (by positivity)]
      have h1 : (N : ℝ) * Real.exp 1 * (2 * T) ≤ N * 3 * (2 * T) := by gcongr; linarith
      have hNT : 0 ≤ (N : ℝ) * T := by positivity
      have h2 : (N : ℝ) * T * 2 ≤ N * T * (π * Real.log 2) := mul_le_mul_of_nonneg_left hπl hNT
      nlinarith
    calc K₁ * S ≤ 3 * N / (2 * T) * (5 * L) := mul_le_mul hK h5 hS0 (by positivity)
      _ ≤ 10 * N * L ^ 2 / T := by
        rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) hT]
        have hX : 0 ≤ (N : ℝ) * T * L := by positivity
        have : (N : ℝ) * T * L * 1 ≤ N * T * L * L := mul_le_mul_of_nonneg_left hL.le hX
        nlinarith
  have hH := sum_inv_abs_sub_le N
  have hlog2N : Real.log (2 * N) ≤ 2 * L := by
    rw [hLdef, show (2 : ℝ) * Real.log N = ((2 : ℕ) : ℝ) * Real.log N by norm_num,
      ← Real.log_pow]
    exact Real.log_le_log (by positivity) (by push_cast; nlinarith)
  have hK₂ : ∑ n ∈ (Finset.range (2 * N)).filter (· ≠ N), K₂ / |(N : ℝ) - n| ≤
      30 * N * L ^ 2 / T := by
    simp_rw [div_eq_mul_one_div K₂]
    rw [← Finset.mul_sum]
    have hK₂0 : 0 ≤ K₂ := by
      have : 0 ≤ Real.log (2 * N) := Real.log_nonneg (by linarith)
      positivity
    calc K₂ * ∑ n ∈ (Finset.range (2 * N)).filter (· ≠ N), 1 / |(N : ℝ) - n|
        ≤ K₂ * (2 * (1 + L)) := mul_le_mul_of_nonneg_left hH hK₂0
      _ ≤ 30 * N * L ^ 2 / T := by
          simp only [K₂]
          rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) hT]
          have hA : 0 ≤ Real.log (2 * N) := Real.log_nonneg (by linarith)
          have hB : 2 * (1 + L) ≤ 4 * L := by linarith
          have h0 := mul_le_mul hlog2N hB (by positivity) (by positivity)
          have h8 : (0 : ℝ) ≤ 8 * N := by positivity
          have h1 : 8 * N * Real.log (2 * N) * (2 * (1 + L)) ≤ 8 * N * (2 * L) * (4 * L) := by
            calc 8 * N * Real.log (2 * N) * (2 * (1 + L))
                = 8 * N * (Real.log (2 * N) * (2 * (1 + L))) := by ring
              _ ≤ 8 * N * (2 * L * (4 * L)) := mul_le_mul_of_nonneg_left h0 h8
              _ = 8 * N * (2 * L) * (4 * L) := by ring
          have h2 := mul_le_mul_of_nonneg_right h1 hT.le
          have hX : 0 ≤ (N : ℝ) * L ^ 2 * T := by positivity
          have h3 : (N : ℝ) * L ^ 2 * T * 3 ≤ N * L ^ 2 * T * π :=
            mul_le_mul_of_nonneg_left hπ.le hX
          nlinarith
  have hK₃ : Λ N * c / (π * T) ≤ N * L ^ 2 / T := by
    have hΛ : Λ N ≤ L := ArithmeticFunction.vonMangoldt_le_log
    have hΛ0 := ArithmeticFunction.vonMangoldt_nonneg (n := N)
    rw [div_le_div_iff₀ (by positivity) hT]
    have h1 : Λ N * c ≤ L * 2 := mul_le_mul hΛ hc2 (by linarith) (by linarith)
    have h1' := mul_le_mul_of_nonneg_right h1 hT.le
    have hX : 0 ≤ L * T := by positivity
    have h2 : L * T * 1 ≤ L * T * L := mul_le_mul_of_nonneg_left hL.le hX
    have hY : 0 ≤ L ^ 2 * T := by positivity
    have h3 : L ^ 2 * T * (3 * 3) ≤ L ^ 2 * T * (N * π) :=
      mul_le_mul_of_nonneg_left (mul_le_mul hN3 hπ.le (by norm_num) hN0.le) hY
    nlinarith
  have : K₁ * S + ∑ n ∈ (Finset.range (2 * N)).filter (· ≠ N), K₂ / |(N : ℝ) - n| +
      Λ N * c / (π * T) ≤ 41 * N * L ^ 2 / T := by
    have e : (41 : ℝ) * N * L ^ 2 / T = 10 * N * L ^ 2 / T + 30 * N * L ^ 2 / T + N * L ^ 2 / T := by
      ring
    linarith
  refine this.trans ?_
  apply div_le_div_of_nonneg_right _ hT.le
  have : 0 ≤ (N : ℝ) * L ^ 2 := by positivity
  nlinarith

/-- **Davenport, Ch. 17, p. 110, (11) (rows 17-8, 17-15)** for the first part of the error:
for integers `N ≥ 3`, `c = 1 + 1/log N` and `T > 0`,
`|ψ₀(N) - J(N, T)| ≤ A N log² N / T` with an absolute constant `A`. -/
@[kb "davenport1980" "Ch 17, p. 110"]
theorem Davenport.norm_psi0_sub_explicitJ_le :
    ∃ A : ℝ, 0 < A ∧ ∀ N : ℕ, 3 ≤ N → ∀ T : ℝ, 0 < T →
      ‖(psi0 N : ℂ) - explicitJ N (1 + 1 / Real.log N) T‖ ≤ A * N * Real.log N ^ 2 / T := by
  refine ⟨100, by norm_num, fun N hN T hT ↦ ?_⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hL : 0 < Real.log N := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hc1 : 1 < 1 + 1 / Real.log N := by have : 0 < 1 / Real.log N := by positivity
                                          linarith
  have hJ := Davenport.hasSum_explicitJ (x := N) T hN0 hc1
  have hψ := hasSum_psi0 N
  have hd := hJ.sub hψ
  obtain ⟨G, S, hG, hS, hGb⟩ := exists_perron_majorant hN hT
  have hbound := tsum_of_norm_bounded (f := fun n : ℕ ↦ (Λ n : ℂ) *
      perronIntegral (N / n) (1 + 1 / Real.log N) T - (Λ n : ℂ) * (perronStep N n : ℂ)) hG
    fun n ↦ by
      have := hGb n
      rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_of_nonneg
        ArithmeticFunction.vonMangoldt_nonneg]
      exact this
  rw [hd.tsum_eq, norm_sub_rev] at hbound
  exact hbound.trans hS

end NTKB
