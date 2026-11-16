/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Davenport.Zeros.ExplicitPrime

/-!
# The truncated Perron formula summed over prime powers, for real `x`

**Davenport, Ch. 17, pp. 106-107 and (11), (12), p. 110 (rows 17-6, 17-8).** For real `x ≥ 2`,
`c = 1 + 1/log(3x)` and `T ≥ 2`,
`∑_n Λ(n) |I(x/n, T) - δ(x/n)| ≪ x log² x / T + log x · min(1, x/(T ⟨x⟩))`,
where `⟨x⟩` is the distance from `x` to the nearest prime power other than `x` itself. This removes the
restriction to integers of `Davenport.norm_psi0_sub_explicitJ_le`.

The abscissa `1 + 1/log(3x)` (rather than Davenport's `1 + 1/log x`) keeps `c ≤ 2` down to `x = 2`.
-/

open Filter Topology Complex Set
open scoped Real ArithmeticFunction.vonMangoldt

namespace NTKB

/-- The step function `δ(x/n)`: `1` for `n < x`, `1/2` for `n = x`, `0` for `n > x`. -/
noncomputable def perronStepR (x : ℝ) (n : ℕ) : ℝ :=
  if (n : ℝ) < x then 1 else if (n : ℝ) = x then 1 / 2 else 0

/-- **Davenport, Ch. 17, p. 104 (row 17-1)** for real `x`: `ψ₀(x) = ∑_{n < x} Λ(n) + Λ(x)/2`, the last
term only when `x` is an integer (the mean of the left and right limits of `ψ` at `x`). -/
noncomputable def psi0R (x : ℝ) : ℝ := ∑ n ∈ Finset.range (⌊x⌋₊ + 1), Λ n * perronStepR x n

/-- The abscissa of the Perron integral for real `x`. -/
noncomputable def perronAbscissa (x : ℝ) : ℝ := 1 + 1 / Real.log (3 * x)

/-- **Davenport, Ch. 17, p. 110**: `⟨x⟩`, the distance from `x` to the nearest prime power other than
`x` itself. -/
noncomputable def distPrimePow (x : ℝ) : ℝ :=
  sInf ((fun n : ℕ ↦ |x - n|) '' {n : ℕ | IsPrimePow n ∧ (n : ℝ) ≠ x})

lemma hasSum_psi0R (x : ℝ) : HasSum (fun n : ℕ ↦ (Λ n : ℂ) * perronStepR x n) (psi0R x) := by
  have this : ∀ n ∉ Finset.range (⌊x⌋₊ + 1), (Λ n : ℂ) * perronStepR x n = 0 := by
    intro n hn
    rw [Finset.mem_range, not_lt] at hn
    have h1 : x < n := by
      have h2 := Nat.lt_floor_add_one x
      have h3 : ((⌊x⌋₊ : ℝ) + 1) ≤ n := by exact_mod_cast hn
      linarith
    simp [perronStepR, not_lt.mpr h1.le, h1.ne']
  have h : HasSum (fun n : ℕ ↦ (Λ n : ℂ) * perronStepR x n)
      (∑ n ∈ Finset.range (⌊x⌋₊ + 1), (Λ n : ℂ) * perronStepR x n) :=
    hasSum_sum_of_ne_finset_zero this
  convert h using 1
  rw [psi0R]; push_cast; rfl

lemma psi0R_natCast (N : ℕ) : psi0R N = psi0 N := by
  unfold psi0R psi0
  rw [Nat.floor_natCast, Finset.sum_range_succ]
  congr 1
  · refine Finset.sum_congr rfl fun n hn ↦ ?_
    have : (n : ℝ) < N := by exact_mod_cast Finset.mem_range.mp hn
    simp [perronStepR, this]
  · simp [perronStepR]; ring

/-- Away from the integers, `ψ₀(x) = ψ(x)`. -/
lemma psi0R_eq_psi {x : ℝ} (hx : ∀ n : ℕ, (n : ℝ) ≠ x) : psi0R x = Chebyshev.psi x := by
  rw [Chebyshev.psi_eq_sum_Icc]
  have hI : Finset.Icc 0 ⌊x⌋₊ = Finset.range (⌊x⌋₊ + 1) := by
    ext n; simp [Nat.lt_succ_iff]
  rw [hI, psi0R]
  refine Finset.sum_congr rfl fun n hn ↦ ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn1
  · simp
  have : (n : ℝ) < x := by
    rcases lt_or_gt_of_ne (hx n) with h | h
    · exact h
    · exfalso
      have hle : n ≤ ⌊x⌋₊ := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
      have h0 : 0 ≤ x := by
        by_contra hneg
        push Not at hneg
        rw [Nat.floor_of_nonpos hneg.le] at hle
        omega
      have h1 := Nat.floor_le h0
      have h2 : (n : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast hle
      linarith
  simp [perronStepR, this]

lemma distPrimePow_le {x : ℝ} {n : ℕ} (hn : IsPrimePow n) (hnx : (n : ℝ) ≠ x) :
    distPrimePow x ≤ |x - n| :=
  csInf_le ⟨0, by rintro _ ⟨m, _, rfl⟩; exact abs_nonneg _⟩ ⟨n, ⟨hn, hnx⟩, rfl⟩

lemma exists_pos_le_of_finset (f : ℕ → ℝ) (F : Finset ℕ) (h : ∀ n ∈ F, 0 < f n) :
    ∃ δ > 0, ∀ n ∈ F, δ ≤ f n := by
  induction F using Finset.induction_on with
  | empty => exact ⟨1, one_pos, by simp⟩
  | insert a s ha ih =>
    obtain ⟨δ, hδ, h'⟩ := ih (fun n hn ↦ h n (Finset.mem_insert_of_mem hn))
    refine ⟨min δ (f a), lt_min hδ (h a (Finset.mem_insert_self _ _)), fun n hn ↦ ?_⟩
    rcases Finset.mem_insert.mp hn with rfl | hn
    · exact min_le_right _ _
    · exact (min_le_left _ _).trans (h' n hn)

lemma distPrimePow_pos (x : ℝ) : 0 < distPrimePow x := by
  classical
  obtain ⟨δ, hδ, hF⟩ := exists_pos_le_of_finset (fun n : ℕ ↦ |x - n|)
    ((Finset.range (⌈|x|⌉₊ + 2)).filter (fun n ↦ IsPrimePow n ∧ (n : ℝ) ≠ x))
    (fun n hn ↦ by
      have := (Finset.mem_filter.mp hn).2.2
      exact abs_pos.mpr (sub_ne_zero.mpr this.symm))
  have key : ∀ n : ℕ, IsPrimePow n → (n : ℝ) ≠ x → min δ 1 ≤ |x - n| := by
    intro n hn hnx
    by_cases hm : n < ⌈|x|⌉₊ + 2
    · exact (min_le_left _ _).trans
        (hF n (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hm, hn, hnx⟩))
    · refine (min_le_right _ _).trans ?_
      push Not at hm
      have h1 : |x| ≤ ⌈|x|⌉₊ := Nat.le_ceil _
      have h2 : ((⌈|x|⌉₊ + 2 : ℕ) : ℝ) ≤ n := by exact_mod_cast hm
      push_cast at h2
      have h3 := le_abs_self x
      rw [abs_sub_comm]
      exact le_trans (by linarith) (le_abs_self ((n : ℝ) - x))
  have hne : ((fun n : ℕ ↦ |x - n|) '' {n : ℕ | IsPrimePow n ∧ (n : ℝ) ≠ x}).Nonempty := by
    by_cases h : ((2 : ℕ) : ℝ) = x
    · refine ⟨|x - ((3 : ℕ) : ℝ)|, 3, ⟨Nat.prime_three.isPrimePow, ?_⟩, rfl⟩
      rw [← h]; norm_num
    · exact ⟨|x - ((2 : ℕ) : ℝ)|, 2, ⟨Nat.prime_two.isPrimePow, h⟩, rfl⟩
  exact lt_of_lt_of_le (lt_min hδ one_pos)
    (le_csInf hne (by rintro _ ⟨n, ⟨hn, hnx⟩, rfl⟩; exact key n hn hnx))

lemma one_lt_perronAbscissa {x : ℝ} (hx : 1 ≤ x) : 1 < perronAbscissa x := by
  have hl : 0 < Real.log (3 * x) := Real.log_pos (by linarith)
  unfold perronAbscissa
  have : 0 < 1 / Real.log (3 * x) := by positivity
  linarith

lemma perronAbscissa_le_two {x : ℝ} (hx : 1 ≤ x) : perronAbscissa x ≤ 2 := by
  have hl : 1 ≤ Real.log (3 * x) := by
    have h3 : (1 : ℝ) < Real.log 3 := by
      rw [Real.lt_log_iff_exp_lt (by norm_num)]
      have := Real.exp_one_lt_d9
      linarith
    have : Real.log 3 ≤ Real.log (3 * x) := Real.log_le_log (by norm_num) (by linarith)
    linarith
  unfold perronAbscissa
  have : 1 / Real.log (3 * x) ≤ 1 := by rw [div_le_one (by linarith)]; exact hl
  linarith

/-- `x^c ≤ 3 x` for `c = 1 + 1/log(3x)` (indeed `x^c ≤ e x`). -/
lemma rpow_perronAbscissa_le {x : ℝ} (hx : 1 ≤ x) : x ^ perronAbscissa x ≤ 3 * x := by
  have hx0 : 0 < x := by linarith
  have hl : 0 < Real.log (3 * x) := Real.log_pos (by linarith)
  unfold perronAbscissa
  rw [Real.rpow_add hx0, Real.rpow_one, Real.rpow_def_of_pos hx0]
  have h1 : Real.log x * (1 / Real.log (3 * x)) ≤ 1 := by
    rw [mul_one_div, div_le_one hl]; exact Real.log_le_log hx0 (by linarith)
  have h2 : Real.exp (Real.log x * (1 / Real.log (3 * x))) ≤ Real.exp 1 := Real.exp_le_exp.mpr h1
  have h3 := Real.exp_one_lt_d9
  nlinarith

/-- The pointwise bound for `Λ(n) |I(x/n, T) - δ(x/n)|`. -/
lemma vonMangoldt_mul_perron_sub_le_real {x : ℝ} (hx : 2 ≤ x) {T : ℝ} (hT : 2 ≤ T) {d : ℝ}
    (hd : 0 < d) (hdd : ∀ n : ℕ, IsPrimePow n → (n : ℝ) ≠ x → d ≤ |x - n|) (n : ℕ) :
    Λ n * ‖perronIntegral (x / n) (perronAbscissa x) T - perronStepR x n‖ ≤
      3 * x / (π * T * Real.log 2) * (Λ n * (n : ℝ) ^ (-perronAbscissa x)) +
      (if (n : ℝ) < 2 * x ∧ 1 ≤ |x - n| then 16 * x * Real.log x / (π * T) / |x - n| else 0) +
      (if |x - n| < 1 ∧ (n : ℝ) ≠ x ∧ IsPrimePow n then 8 * Real.log x * min 1 (x / (T * d))
        else 0) +
      (if (n : ℝ) = x then 2 * Real.log x / (π * T) else 0) := by
  have hπ := Real.pi_pos
  have hπ3 := Real.pi_gt_three
  have hx0 : 0 < x := by linarith
  have hT0 : 0 < T := by linarith
  have hL2 : Real.log 2 ≤ Real.log x := Real.log_le_log two_pos hx
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hL0 : 0 < Real.log x := by linarith
  have hc1 := one_lt_perronAbscissa (x := x) (by linarith)
  have hc2 := perronAbscissa_le_two (x := x) (by linarith)
  have hxc := rpow_perronAbscissa_le (x := x) (by linarith)
  set c := perronAbscissa x with hcdef
  have hc0 : 0 < c := by linarith
  have hΛ := ArithmeticFunction.vonMangoldt_nonneg (n := n)
  have hπ' : π ≠ 0 := hπ.ne'
  have hT' : T ≠ 0 := hT0.ne'
  have hmin : 0 ≤ min 1 (x / (T * d)) := le_min zero_le_one (by positivity)
  have hK1 : 0 ≤ 3 * x / (π * T * Real.log 2) * (Λ n * (n : ℝ) ^ (-c)) := by positivity
  have hK2 : 0 ≤ (if (n : ℝ) < 2 * x ∧ 1 ≤ |x - n| then
      16 * x * Real.log x / (π * T) / |x - n| else 0) := by
    split_ifs
    · positivity
    · exact le_rfl
  have hK3 : 0 ≤ (if |x - n| < 1 ∧ (n : ℝ) ≠ x ∧ IsPrimePow n then
      8 * Real.log x * min 1 (x / (T * d)) else 0) := by
    split_ifs
    · exact mul_nonneg (by linarith) hmin
    · exact le_rfl
  have hK4 : 0 ≤ (if (n : ℝ) = x then 2 * Real.log x / (π * T) else 0) := by
    split_ifs
    · positivity
    · exact le_rfl
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h0 : Λ 0 = 0 := by simp
    simp only [h0, zero_mul, mul_zero]
    linarith [hK2, hK3, hK4]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  by_cases hnx : (n : ℝ) = x
  · rw [if_pos hnx]
    have hy : x / (n : ℝ) = 1 := by rw [← hnx]; exact div_self hn0.ne'
    have hstep : perronStepR x n = 1 / 2 := by simp [perronStepR, hnx]
    rw [hy, hstep]
    have h1 := norm_perronIntegral_one_sub_half hc0 hT0
    push_cast at h1 ⊢
    have hΛ' : Λ n ≤ Real.log x := by
      have := ArithmeticFunction.vonMangoldt_le_log (n := n)
      rwa [hnx] at this
    have h3 : Λ n * ‖perronIntegral 1 c T - 1 / 2‖ ≤ Real.log x * (c / (π * T)) :=
      mul_le_mul hΛ' h1 (norm_nonneg _) hL0.le
    have h4 : Real.log x * (c / (π * T)) ≤ 2 * Real.log x / (π * T) := by
      rw [← mul_div_assoc]
      exact div_le_div_of_nonneg_right (by nlinarith) (by positivity)
    linarith
  set y : ℝ := x / n with hy
  have hy0 : 0 < y := div_pos hx0 hn0
  have hy1 : y ≠ 1 := by
    rw [hy, Ne, div_eq_one_iff_eq hn0.ne']
    exact fun h ↦ hnx h.symm
  have hlogy : 0 < |Real.log y| := abs_pos.mpr (fun h ↦ hy1 (by
    rcases Real.log_eq_zero.mp h with h | h | h <;> [linarith; exact h; linarith]))
  have hB : ‖perronIntegral y c T - perronStepR x n‖ ≤ y ^ c / (π * T * |Real.log y|) ∧
      ‖perronIntegral y c T - perronStepR x n‖ ≤ y ^ c := by
    rcases lt_or_gt_of_ne hnx with h | h
    · have hy1' : 1 < y := by rw [hy, one_lt_div hn0]; exact h
      have : perronStepR x n = 1 := by simp [perronStepR, h]
      rw [this]; push_cast
      exact ⟨norm_perronIntegral_gt_one_log hy1' hc0 hT0,
        norm_perronIntegral_gt_one_le hy1' hc0 (hc2.trans hT)⟩
    · have hy1' : y < 1 := by rw [hy, div_lt_one hn0]; exact h
      have : perronStepR x n = 0 := by simp [perronStepR, not_lt.mpr h.le, h.ne']
      rw [this]; push_cast; rw [sub_zero]
      exact ⟨norm_perronIntegral_lt_one_log hy0 hy1' hc0 hT0,
        norm_perronIntegral_lt_one_le hy0 hy1' hc0 hT0⟩
  have hyc : y ^ c = x ^ c * (n : ℝ) ^ (-c) := by
    rw [hy, Real.div_rpow hx0.le hn0.le, Real.rpow_neg hn0.le, div_eq_mul_inv]
  have hLHS : Λ n * ‖perronIntegral y c T - perronStepR x n‖ ≤
      Λ n * (y ^ c / (π * T * |Real.log y|)) := mul_le_mul_of_nonneg_left hB.1 hΛ
  by_cases hnear : x / 2 < n ∧ (n : ℝ) < 2 * x
  · have hlog : 1 / |Real.log y| ≤ max x (n : ℝ) / |x - n| :=
      inv_abs_log_le hx0 hn0 (fun h ↦ hnx h)
    have hdiff : 0 < |x - n| := abs_pos.mpr (sub_ne_zero.mpr (fun h ↦ hnx h.symm))
    have hdiff' : |x - n| ≠ 0 := hdiff.ne'
    have hmax : max x (n : ℝ) ≤ 2 * x := max_le (by linarith) hnear.2.le
    have h3 : 1 / |Real.log y| ≤ 2 * x / |x - n| :=
      hlog.trans (div_le_div_of_nonneg_right hmax hdiff.le)
    have hyc4 : y ^ c ≤ 4 := by
      have hy2 : y ≤ 2 := by rw [hy, div_le_iff₀ hn0]; linarith [hnear.1]
      calc y ^ c ≤ (max 1 y) ^ c := Real.rpow_le_rpow hy0.le (le_max_right _ _) hc0.le
        _ ≤ (max 1 y) ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (le_max_left _ _) hc2
        _ ≤ 2 ^ (2 : ℝ) := Real.rpow_le_rpow (by positivity) (max_le (by norm_num) hy2)
            (by norm_num)
        _ = 4 := by norm_num
    have hΛ2 : Λ n ≤ 2 * Real.log x := by
      have h1 : Λ n ≤ Real.log (2 * x) :=
        ArithmeticFunction.vonMangoldt_le_log.trans (Real.log_le_log hn0 hnear.2.le)
      have h2 : Real.log (2 * x) = Real.log 2 + Real.log x := Real.log_mul two_ne_zero hx0.ne'
      linarith
    have hN : ‖perronIntegral y c T - perronStepR x n‖ ≤ 4 * (2 * x / |x - n|) / (π * T) := by
      have h1 : y ^ c / (π * T * |Real.log y|) = y ^ c * (1 / |Real.log y|) / (π * T) := by
        field_simp
      calc _ ≤ y ^ c / (π * T * |Real.log y|) := hB.1
        _ = y ^ c * (1 / |Real.log y|) / (π * T) := h1
        _ ≤ 4 * (2 * x / |x - n|) / (π * T) :=
          div_le_div_of_nonneg_right (mul_le_mul hyc4 h3 (by positivity) (by norm_num))
            (by positivity)
    by_cases h1 : 1 ≤ |x - n|
    · rw [if_pos ⟨hnear.2, h1⟩]
      have h5 : Λ n * ‖perronIntegral y c T - perronStepR x n‖ ≤
          2 * Real.log x * (4 * (2 * x / |x - n|) / (π * T)) :=
        mul_le_mul hΛ2 hN (norm_nonneg _) (by linarith)
      have e : 2 * Real.log x * (4 * (2 * x / |x - n|) / (π * T)) =
          16 * x * Real.log x / (π * T) / |x - n| := by field_simp; ring
      linarith
    · push Not at h1
      by_cases hp : IsPrimePow n
      · have hdn : d ≤ |x - n| := hdd n hp hnx
        rw [if_pos (show |x - n| < 1 ∧ (n : ℝ) ≠ x ∧ IsPrimePow n from ⟨h1, hnx, hp⟩)]
        have hq : 4 * (2 * x / |x - n|) / (π * T) ≤ 4 * (x / (T * d)) := by
          have e1 : 2 * x / |x - n| ≤ 2 * x / d :=
            div_le_div_of_nonneg_left (by positivity) hd hdn
          have e2 : 4 * (2 * x / |x - n|) / (π * T) ≤ 4 * (2 * x / d) / (π * T) := by
            gcongr
          have e3 : 4 * (2 * x / d) / (π * T) = (8 / π) * (x / (T * d)) := by
            field_simp; ring
          have e4 : 8 / π ≤ 4 := by rw [div_le_iff₀ hπ]; linarith
          have e5 : 0 ≤ x / (T * d) := by positivity
          have := mul_le_mul_of_nonneg_right e4 e5
          linarith
        have hN1 : ‖perronIntegral y c T - perronStepR x n‖ ≤ 4 := hB.2.trans hyc4
        have hN2 : ‖perronIntegral y c T - perronStepR x n‖ ≤ 4 * min 1 (x / (T * d)) := by
          have h6 : ‖perronIntegral y c T - perronStepR x n‖ / 4 ≤ min 1 (x / (T * d)) :=
            le_min (by linarith) (by linarith [hN.trans hq])
          linarith
        have h5 : Λ n * ‖perronIntegral y c T - perronStepR x n‖ ≤
            2 * Real.log x * (4 * min 1 (x / (T * d))) :=
          mul_le_mul hΛ2 hN2 (norm_nonneg _) (by linarith)
        linarith
      · have h0 : Λ n = 0 := ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hp
        have h5 : Λ n * ‖perronIntegral y c T - perronStepR x n‖ = 0 := by rw [h0, zero_mul]
        linarith
  · have hfar : Real.log 2 ≤ |Real.log y| := by
      push Not at hnear
      by_cases hle : (n : ℝ) ≤ x / 2
      · have : 2 ≤ y := by rw [hy, le_div_iff₀ hn0]; linarith
        rw [abs_of_pos (Real.log_pos (by linarith))]
        exact Real.log_le_log two_pos this
      · have h2N : 2 * x ≤ (n : ℝ) := hnear (by linarith)
        have : y ≤ 1 / 2 := by rw [hy, div_le_iff₀ hn0]; linarith
        rw [abs_of_neg (Real.log_neg hy0 (by linarith)), ← Real.log_inv]
        exact Real.log_le_log two_pos (by rw [le_inv_comm₀ two_pos hy0]; linarith)
    have h1 : Λ n * (y ^ c / (π * T * |Real.log y|)) ≤
        3 * x / (π * T * Real.log 2) * (Λ n * (n : ℝ) ^ (-c)) := by
      rw [hyc]
      have e1 : x ^ c * (n : ℝ) ^ (-c) / (π * T * |Real.log y|) ≤
          x ^ c * (n : ℝ) ^ (-c) / (π * T * Real.log 2) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) (by gcongr)
      have e2 : x ^ c * (n : ℝ) ^ (-c) / (π * T * Real.log 2) ≤
          3 * x * (n : ℝ) ^ (-c) / (π * T * Real.log 2) := by gcongr
      calc Λ n * (x ^ c * (n : ℝ) ^ (-c) / (π * T * |Real.log y|))
          ≤ Λ n * (3 * x * (n : ℝ) ^ (-c) / (π * T * Real.log 2)) :=
            mul_le_mul_of_nonneg_left (e1.trans e2) hΛ
        _ = _ := by ring
    linarith

/-- `∑_{n < 2⌈x⌉, 1 ≤ |x - n|, n < 2x} K/|x - n| ≤ 4 K (1 + log ⌈x⌉)`. -/
lemma sum_near_le {x : ℝ} (hx : 2 ≤ x) (K : ℝ) (hK : 0 ≤ K) :
    ∑ n ∈ Finset.range (2 * ⌈x⌉₊),
      (if (n : ℝ) < 2 * x ∧ 1 ≤ |x - n| then K / |x - n| else 0) ≤
      4 * K * (1 + Real.log ⌈x⌉₊) := by
  set N := ⌈x⌉₊ with hN
  have hxN : x ≤ N := Nat.le_ceil x
  have hNx : (N : ℝ) < x + 1 := Nat.ceil_lt_add_one (by linarith)
  have h1 : ∀ n ∈ Finset.range (2 * N),
      (if (n : ℝ) < 2 * x ∧ 1 ≤ |x - n| then K / |x - n| else 0) ≤
        if n ≠ N then 2 * K * (1 / |(N : ℝ) - n|) else 0 := by
    intro n _
    by_cases h : (n : ℝ) < 2 * x ∧ 1 ≤ |x - n|
    · rw [if_pos h]
      by_cases h' : n ≠ N
      · rw [if_pos h']
        have hb : |(N : ℝ) - n| ≤ 2 * |x - n| := by
          have h2 : |(N : ℝ) - n| ≤ |(N : ℝ) - x| + |x - n| := abs_sub_le _ _ _
          have h3 : |(N : ℝ) - x| ≤ 1 := by rw [abs_le]; constructor <;> linarith
          linarith [h.2]
        have hpos : 0 < |(N : ℝ) - n| := abs_pos.mpr (sub_ne_zero.mpr (fun e ↦ h' (by
          exact_mod_cast e.symm)))
        have hpos2 : 0 < |x - n| := lt_of_lt_of_le one_pos h.2
        rw [div_le_iff₀ hpos2]
        have h4 : 1 ≤ 2 * |x - n| / |(N : ℝ) - n| := by rw [le_div_iff₀ hpos]; linarith
        calc K = K * 1 := (mul_one K).symm
          _ ≤ K * (2 * |x - n| / |(N : ℝ) - n|) := mul_le_mul_of_nonneg_left h4 hK
          _ = 2 * K * (1 / |(N : ℝ) - n|) * |x - n| := by ring
      · exfalso
        have : n = N := not_not.mp h'
        subst this
        have h2 := h.2
        rw [abs_of_nonpos (by linarith)] at h2
        linarith
    · rw [if_neg h]
      split_ifs
      · positivity
      · exact le_rfl
  calc _ ≤ ∑ n ∈ Finset.range (2 * N), (if n ≠ N then 2 * K * (1 / |(N : ℝ) - n|) else 0) :=
        Finset.sum_le_sum h1
    _ = ∑ n ∈ (Finset.range (2 * N)).filter (· ≠ N), 2 * K * (1 / |(N : ℝ) - n|) :=
        (Finset.sum_filter _ _).symm
    _ = 2 * K * ∑ n ∈ (Finset.range (2 * N)).filter (· ≠ N), 1 / |(N : ℝ) - n| := by
        rw [← Finset.mul_sum]
    _ ≤ 2 * K * (2 * (1 + Real.log N)) :=
        mul_le_mul_of_nonneg_left (sum_inv_abs_sub_le N) (by positivity)
    _ = 4 * K * (1 + Real.log N) := by ring

/-- **Davenport, Ch. 17, (11), (12), p. 110**: a summable majorant of `Λ(n) |I(x/n, T) - δ(x/n)|`
for real `x ≥ 2`, `T ≥ 2` and any `d > 0` at most the distance from `x` to every prime power
`n ≠ x`. -/
theorem Davenport.exists_perron_majorant_real :
    ∃ A : ℝ, 0 < A ∧ ∀ x : ℝ, 2 ≤ x → ∀ T : ℝ, 2 ≤ T → ∀ d : ℝ, 0 < d →
      (∀ n : ℕ, IsPrimePow n → (n : ℝ) ≠ x → d ≤ |x - n|) →
      ∃ G : ℕ → ℝ, ∃ S : ℝ, HasSum G S ∧
        S ≤ A * (x * Real.log x ^ 2 / T + Real.log x * min 1 (x / (T * d))) ∧
        ∀ n, Λ n * ‖perronIntegral (x / n) (perronAbscissa x) T - perronStepR x n‖ ≤ G n := by
  refine ⟨1000, by norm_num, fun x hx T hT d hd hdd ↦ ?_⟩
  have hπ := Real.pi_gt_three
  have hπpos : 0 < π := Real.pi_pos
  have hπ' : π ≠ 0 := hπpos.ne'
  have hx0 : 0 < x := by linarith
  have hT0 : 0 < T := by linarith
  have hT' : T ≠ 0 := hT0.ne'
  have hl23 := log_two_gt_two_thirds
  have hL2 : Real.log 2 ≤ Real.log x := Real.log_le_log two_pos hx
  have hL0 : 0 < Real.log x := by linarith
  have hl2' : Real.log 2 ≠ 0 := by linarith
  have hc1 := one_lt_perronAbscissa (x := x) (by linarith)
  have hc2 := perronAbscissa_le_two (x := x) (by linarith)
  have hpt := fun n ↦ vonMangoldt_mul_perron_sub_le_real hx hT hd hdd n
  have h3x : Real.log (3 * x) ≤ 3 * Real.log x := by
    have h1 : Real.log 3 ≤ Real.log 4 := Real.log_le_log (by norm_num) (by norm_num)
    have h2 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    rw [Real.log_mul (by norm_num) hx0.ne']
    linarith
  have hw0 : 0 ≤ x / T := by positivity
  -- piece 1
  obtain ⟨S1, p1, b1⟩ : ∃ S1, HasSum (fun n : ℕ ↦ 3 * x / (π * T * Real.log 2) *
      (Λ n * (n : ℝ) ^ (-perronAbscissa x))) S1 ∧ S1 ≤ 12 * (x / T * Real.log x) := by
    have hS := (hasSum_vonMangoldt_rpow hc1).mul_left (3 * x / (π * T * Real.log 2))
    refine ⟨_, hS, ?_⟩
    have hSle : -(deriv riemannZeta (perronAbscissa x) / riemannZeta (perronAbscissa x)).re ≤
        8 * Real.log x := by
      have := Davenport.neg_logDeriv_riemannZeta_real_le hc1 hc2
      have hc' : 1 / (perronAbscissa x - 1) = Real.log (3 * x) := by
        rw [show perronAbscissa x - 1 = 1 / Real.log (3 * x) by unfold perronAbscissa; ring,
          one_div_one_div]
      rw [hc'] at this
      linarith
    have hS0 : 0 ≤ -(deriv riemannZeta (perronAbscissa x) /
        riemannZeta (perronAbscissa x)).re :=
      (hasSum_vonMangoldt_rpow hc1).nonneg fun n ↦ mul_nonneg
        ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg n.cast_nonneg _)
    have hK1 : 3 * x / (π * T * Real.log 2) ≤ 3 / 2 * (x / T) := by
      have hπl : 2 ≤ π * Real.log 2 := by nlinarith
      have e : 3 * x / (π * T * Real.log 2) = 3 / (π * Real.log 2) * (x / T) := by
        field_simp
      rw [e]
      have : 3 / (π * Real.log 2) ≤ 3 / 2 :=
        div_le_div_of_nonneg_left (by norm_num) (by norm_num) hπl
      exact mul_le_mul_of_nonneg_right this hw0
    calc _ ≤ (3 / 2 * (x / T)) * (8 * Real.log x) := mul_le_mul hK1 hSle hS0 (by positivity)
      _ = 12 * (x / T * Real.log x) := by ring
  -- piece 2
  obtain ⟨S2, p2, b2⟩ : ∃ S2, HasSum (fun n : ℕ ↦
      if (n : ℝ) < 2 * x ∧ 1 ≤ |x - n| then 16 * x * Real.log x / (π * T) / |x - n| else 0) S2 ∧
      S2 ≤ 108 * (x / T * Real.log x ^ 2) := by
    have hK2 : 16 * x * Real.log x / (π * T) ≤ 6 * (x / T * Real.log x) := by
      have e : 16 * x * Real.log x / (π * T) = 16 / π * (x / T * Real.log x) := by
        field_simp
      rw [e]
      have : 16 / π ≤ 6 := by rw [div_le_iff₀ hπpos]; linarith
      exact mul_le_mul_of_nonneg_right this (by positivity)
    have hK20 : 0 ≤ 16 * x * Real.log x / (π * T) := by positivity
    refine ⟨_, hasSum_sum_of_ne_finset_zero (s := Finset.range (2 * ⌈x⌉₊)) fun n hn ↦ ?_, ?_⟩
    · rw [Finset.mem_range, not_lt] at hn
      have h1 : 2 * x ≤ (n : ℝ) := by
        have h2 : ((2 * ⌈x⌉₊ : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
        push_cast at h2
        have := Nat.le_ceil x
        linarith
      rw [if_neg (fun h ↦ absurd h.1 (not_lt.mpr h1))]
    · have hN : (⌈x⌉₊ : ℝ) ≤ 3 * x := by
        have := Nat.ceil_lt_add_one (by linarith : 0 ≤ x); linarith
      have hNpos : 0 < (⌈x⌉₊ : ℝ) := Nat.cast_pos.mpr (Nat.ceil_pos.mpr hx0)
      have hlogN : Real.log ⌈x⌉₊ ≤ 3 * Real.log x :=
        (Real.log_le_log hNpos hN).trans h3x
      calc _ ≤ 4 * (16 * x * Real.log x / (π * T)) * (1 + Real.log ⌈x⌉₊) :=
            sum_near_le hx _ hK20
        _ ≤ 4 * (16 * x * Real.log x / (π * T)) * (9 / 2 * Real.log x) :=
            mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        _ ≤ 4 * (6 * (x / T * Real.log x)) * (9 / 2 * Real.log x) := by gcongr
        _ = 108 * (x / T * Real.log x ^ 2) := by ring
  -- piece 3
  obtain ⟨S3, p3, b3⟩ : ∃ S3, HasSum (fun n : ℕ ↦
      if |x - n| < 1 ∧ (n : ℝ) ≠ x ∧ IsPrimePow n then 8 * Real.log x * min 1 (x / (T * d))
        else 0) S3 ∧ S3 ≤ 16 * Real.log x * min 1 (x / (T * d)) := by
    have hm : 0 ≤ 8 * Real.log x * min 1 (x / (T * d)) :=
      mul_nonneg (by linarith) (le_min zero_le_one (by positivity))
    refine ⟨_, hasSum_sum_of_ne_finset_zero (s := ({⌊x⌋₊, ⌊x⌋₊ + 1} : Finset ℕ)) fun n hn ↦ ?_, ?_⟩
    · rw [if_neg]
      rintro ⟨h1, -, -⟩
      apply hn
      rw [abs_lt] at h1
      have f1 := Nat.floor_le hx0.le
      have f2 := Nat.lt_floor_add_one x
      simp only [Finset.mem_insert, Finset.mem_singleton]
      by_contra hcon
      push Not at hcon
      have : n < ⌊x⌋₊ ∨ ⌊x⌋₊ + 1 < n := by omega
      rcases this with h | h
      · have : (n : ℝ) + 1 ≤ ⌊x⌋₊ := by exact_mod_cast (by omega : n + 1 ≤ ⌊x⌋₊)
        linarith [h1.1, h1.2]
      · have : (⌊x⌋₊ : ℝ) + 2 ≤ n := by exact_mod_cast (by omega : ⌊x⌋₊ + 2 ≤ n)
        linarith [h1.1, h1.2]
    · rw [Finset.sum_pair (by omega)]
      have e1 : ∀ m : ℕ, (if |x - m| < 1 ∧ (m : ℝ) ≠ x ∧ IsPrimePow m then
          8 * Real.log x * min 1 (x / (T * d)) else 0) ≤
          8 * Real.log x * min 1 (x / (T * d)) := fun m ↦ by split_ifs <;> linarith
      linarith [e1 ⌊x⌋₊, e1 (⌊x⌋₊ + 1)]
  -- piece 4
  obtain ⟨S4, p4, b4⟩ : ∃ S4, HasSum (fun n : ℕ ↦
      if (n : ℝ) = x then 2 * Real.log x / (π * T) else 0) S4 ∧
      S4 ≤ x / T * Real.log x ^ 2 := by
    have hxL : 1 ≤ x * Real.log x := by nlinarith
    have hLxL : Real.log x ≤ x * Real.log x ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_right hxL hL0.le]
    have hK4 : 2 * Real.log x / (π * T) ≤ x / T * Real.log x ^ 2 := by
      have e : 2 * Real.log x / (π * T) = 2 / π * (Real.log x / T) := by field_simp
      have h1 : 2 / π ≤ 1 := by rw [div_le_one hπpos]; linarith
      have h2 : Real.log x / T ≤ x / T * Real.log x ^ 2 := by
        rw [div_mul_eq_mul_div]; exact div_le_div_of_nonneg_right hLxL hT0.le
      calc 2 * Real.log x / (π * T) = 2 / π * (Real.log x / T) := e
        _ ≤ 1 * (Real.log x / T) := mul_le_mul_of_nonneg_right h1 (by positivity)
        _ = Real.log x / T := one_mul _
        _ ≤ _ := h2
    refine ⟨_, hasSum_sum_of_ne_finset_zero (s := ({⌊x⌋₊} : Finset ℕ)) fun n hn ↦ ?_, ?_⟩
    · rw [if_neg]
      intro h
      apply hn
      rw [Finset.mem_singleton, ← h]
      exact (Nat.floor_natCast n).symm
    · rw [Finset.sum_singleton]
      split_ifs
      · exact hK4
      · positivity
  refine ⟨_, _, (((p1.add p2).add p3).add p4), ?_, hpt⟩
  have hLL : Real.log x ≤ 3 / 2 * Real.log x ^ 2 := by nlinarith
  have hRQ : x / T * Real.log x ≤ 3 / 2 * (x / T * Real.log x ^ 2) :=
    calc x / T * Real.log x ≤ x / T * (3 / 2 * Real.log x ^ 2) :=
          mul_le_mul_of_nonneg_left hLL hw0
      _ = _ := by ring
  have hQ0 : 0 ≤ x / T * Real.log x ^ 2 := by positivity
  have hLm : 0 ≤ Real.log x * min 1 (x / (T * d)) :=
    mul_nonneg hL0.le (le_min zero_le_one (by positivity))
  have e : x * Real.log x ^ 2 / T = x / T * Real.log x ^ 2 := by ring
  rw [e]
  nlinarith

end NTKB
