/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Apostol.Averages.PowerSums
import NTKB.Analytic.Apostol.ArithmeticFunctions.GeneralizedConvolution

/-!
# The average order of `σ_α(n)` (Apostol, Chapter 3, §3.6, Theorem 3.5)

**Theorem 3.5.** For `x ≥ 1` and `α > 0`, `α ≠ 1`,
`∑_{n ≤ x} σ_α(n) = ζ(α+1)/(α+1) · x^{α+1} + O(x^β)`, `β = max(1, α)`,
where `σ_α(n) = ∑_{d ∣ n} d^α` and `ζ(α+1) = ∑_{n ≥ 1} n^{-(α+1)}`.

Proof (Apostol's): `∑_{n ≤ x} σ_α(n) = ∑_{d ≤ x} ∑_{q ≤ x/d} q^α`, then Theorem 3.2 (d) for the
inner sum and 3.2 (b)/(c) (here: (c) for `s = α + 1 > 1` and the partial sums of `d^{-α}`).
-/

open Finset Real

namespace NTKB.Apostol

/-- `∑_{n ≤ N} σ_α(n) = ∑_{d ≤ N} ∑_{q ≤ N/d} q^α`. -/
theorem sum_sigma_rpow_eq (α : ℝ) (N : ℕ) :
    ∑ n ∈ Ioc 0 N, ∑ d ∈ n.divisors, (d : ℝ) ^ α =
      ∑ d ∈ Ioc 0 N, ∑ q ∈ Ioc 0 (N / d), (q : ℝ) ^ α := by
  rw [← sum_Ioc_sum_divisorsAntidiagonal (fun _ q ↦ (q : ℝ) ^ α) N]
  refine sum_congr rfl fun n _ ↦ ?_
  rw [Nat.sum_divisorsAntidiagonal' (fun _ q ↦ (q : ℝ) ^ α)]

/-- The partial sums `∑_{n ≤ N} n^{-α}` are `≤ N^{1-α}/(1-α) + 1` for `0 < α < 1` and
`≤ 1 + 1/(α-1)` for `α > 1`. -/
theorem sum_Ioc_rpow_neg_le_of_lt_one {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {N : ℕ} (hN : 1 ≤ N) :
    ∑ n ∈ Ioc 0 N, (n : ℝ) ^ (-α) ≤ 1 + (N : ℝ) ^ (1 - α) / (1 - α) := by
  have h := sum_Ioc_one_rpow_neg_le hα0.le hα1.ne hN
  rw [← sum_Ioc_consecutive _ (Nat.zero_le 1) hN]
  have h1 : ∑ n ∈ Ioc (0 : ℕ) 1, ((n : ℕ) : ℝ) ^ (-α) = 1 := by simp
  rw [h1]
  have : ((N : ℝ) ^ (1 - α) - 1) / (1 - α) ≤ (N : ℝ) ^ (1 - α) / (1 - α) :=
    div_le_div_of_nonneg_right (by linarith) (by linarith)
  linarith

theorem sum_Ioc_rpow_neg_le_of_one_lt {α : ℝ} (hα1 : 1 < α) {N : ℕ} (hN : 1 ≤ N) :
    ∑ n ∈ Ioc 0 N, (n : ℝ) ^ (-α) ≤ 1 + 1 / (α - 1) := by
  have h := sum_Ioc_one_rpow_neg_le (by linarith) hα1.ne' hN
  rw [← sum_Ioc_consecutive _ (Nat.zero_le 1) hN]
  have h1 : ∑ n ∈ Ioc (0 : ℕ) 1, ((n : ℕ) : ℝ) ^ (-α) = 1 := by simp
  rw [h1]
  have hN0 : 0 ≤ (N : ℝ) ^ (1 - α) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have : ((N : ℝ) ^ (1 - α) - 1) / (1 - α) ≤ 1 / (α - 1) := by
    rw [show ((N : ℝ) ^ (1 - α) - 1) / (1 - α) = (1 - (N : ℝ) ^ (1 - α)) / (α - 1) by
      have : (1 : ℝ) - α ≠ 0 := by linarith
      field_simp; ring]
    exact div_le_div_of_nonneg_right (by linarith) (by linarith)
  linarith

/-- **Apostol, Theorem 3.5.** For `α > 0`, `α ≠ 1`:
`∑_{n ≤ x} σ_α(n) = ζ(α+1)/(α+1) x^{α+1} + O(x^β)` for `x ≥ 1`, `β = max(1, α)`. -/
@[kb "apostol1976" "Thm 3.5, p. 60"]
theorem exists_abs_sum_sigma_rpow_sub_le {α : ℝ} (hα : 0 < α) (hα1 : α ≠ 1) :
    ∃ C, ∀ x : ℝ, 1 ≤ x →
      |∑ n ∈ Ioc 0 ⌊x⌋₊, ∑ d ∈ n.divisors, (d : ℝ) ^ α -
        (∑' n : ℕ, (n : ℝ) ^ (-(α + 1))) / (α + 1) * x ^ (α + 1)| ≤ C * x ^ max 1 α := by
  set Cs : ℝ := if α < 1 then 1 + 1 / (1 - α) else 1 + 1 / (α - 1)
  refine ⟨2 ^ α / (α * (α + 1)) + Cs, fun x hx ↦ ?_⟩
  have hx0 : 0 < x := by linarith
  set N := ⌊x⌋₊
  have hN1 : 1 ≤ N := Nat.le_floor (by exact_mod_cast hx)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hNx : (N : ℝ) ≤ x := Nat.floor_le hx0.le
  have hxN : x < N + 1 := Nat.lt_floor_add_one x
  have hpos : 0 < α + 1 := by linarith
  set Z := ∑' n : ℕ, (n : ℝ) ^ (-(α + 1))
  set S := ∑ d ∈ Ioc 0 N, (d : ℝ) ^ (-(α + 1))
  -- decomposition
  rw [sum_sigma_rpow_eq]
  have hsplit : ∑ d ∈ Ioc 0 N, ∑ q ∈ Ioc 0 (N / d), (q : ℝ) ^ α - Z / (α + 1) * x ^ (α + 1) =
      ∑ d ∈ Ioc 0 N, (∑ q ∈ Ioc 0 ⌊x / d⌋₊, (q : ℝ) ^ α - (x / d) ^ (α + 1) / (α + 1)) -
        x ^ (α + 1) / (α + 1) * (Z - S) := by
    have e : ∀ d ∈ Ioc 0 N, (x / d) ^ (α + 1) / (α + 1) =
        x ^ (α + 1) / (α + 1) * (d : ℝ) ^ (-(α + 1)) := by
      intro d hd
      have hd0 : (0 : ℝ) < d := by exact_mod_cast (mem_Ioc.1 hd).1
      rw [Real.div_rpow hx0.le hd0.le, Real.rpow_neg hd0.le]
      ring
    rw [sum_sub_distrib, sum_congr rfl e, ← mul_sum]
    simp_rw [Nat.floor_div_natCast]
    ring
  rw [hsplit]
  -- the two error terms
  have hE1 : |∑ d ∈ Ioc 0 N, (∑ q ∈ Ioc 0 ⌊x / d⌋₊, (q : ℝ) ^ α -
      (x / d) ^ (α + 1) / (α + 1))| ≤ x ^ α * ∑ d ∈ Ioc 0 N, (d : ℝ) ^ (-α) := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    rw [mul_sum]
    refine sum_le_sum fun d hd ↦ ?_
    have hd0 : (0 : ℝ) < d := by exact_mod_cast (mem_Ioc.1 hd).1
    refine (abs_sum_rpow_sub_le hα (div_nonneg hx0.le hd0.le)).trans (le_of_eq ?_)
    rw [Real.div_rpow hx0.le hd0.le, Real.rpow_neg hd0.le]; ring
  have hE2 : |x ^ (α + 1) / (α + 1) * (Z - S)| ≤ 2 ^ α / (α * (α + 1)) * x := by
    have ht := abs_tsum_rpow_neg_sub_le (s := α + 1) (by linarith) hN1
    rw [show (1 : ℝ) - (α + 1) = -α by ring, show α + 1 - 1 = α by ring] at ht
    rw [abs_mul, abs_of_pos (by positivity)]
    -- `N^{-α} ≤ 2^α x^{-α}` since `x ≤ 2N`
    have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    have h2N : x ≤ 2 * N := by linarith
    have hNpow : (N : ℝ) ^ (-α) ≤ 2 ^ α * x ^ (-α) := by
      rw [Real.rpow_neg hN0.le, Real.rpow_neg hx0.le, ← div_eq_mul_inv]
      rw [le_div_iff₀ (Real.rpow_pos_of_pos hx0 _), inv_mul_eq_div,
        div_le_iff₀ (Real.rpow_pos_of_pos hN0 _)]
      rw [← Real.mul_rpow (by norm_num) hN0.le]
      exact Real.rpow_le_rpow hx0.le h2N hα.le
    calc x ^ (α + 1) / (α + 1) * |Z - S| ≤ x ^ (α + 1) / (α + 1) * ((N : ℝ) ^ (-α) / α) :=
          mul_le_mul_of_nonneg_left ht (by positivity)
      _ ≤ x ^ (α + 1) / (α + 1) * (2 ^ α * x ^ (-α) / α) := by
          gcongr
      _ = 2 ^ α / (α * (α + 1)) * x := by
          rw [Real.rpow_add hx0, Real.rpow_one, Real.rpow_neg hx0.le]
          field_simp
  -- `x^α ∑ d^{-α} ≤ Cs x^β`
  have hE1' : x ^ α * ∑ d ∈ Ioc 0 N, (d : ℝ) ^ (-α) ≤ Cs * x ^ max 1 α := by
    rcases lt_or_gt_of_ne hα1 with h | h
    · have hb := sum_Ioc_rpow_neg_le_of_lt_one hα h hN1
      have hmax : max 1 α = 1 := max_eq_left h.le
      rw [hmax, Real.rpow_one]
      simp only [Cs, if_pos h]
      have hNp : (N : ℝ) ^ (1 - α) ≤ x ^ (1 - α) := Real.rpow_le_rpow hN0.le hNx (by linarith)
      have hxa : x ^ α ≤ x := by
        calc x ^ α ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx h.le
          _ = x := Real.rpow_one x
      have hxx : x ^ α * x ^ (1 - α) = x := by
        rw [← Real.rpow_add hx0]; norm_num
      calc x ^ α * ∑ d ∈ Ioc 0 N, (d : ℝ) ^ (-α) ≤ x ^ α * (1 + x ^ (1 - α) / (1 - α)) := by
            refine mul_le_mul_of_nonneg_left (hb.trans ?_) (by positivity)
            gcongr
        _ = x ^ α + x / (1 - α) := by rw [mul_add, mul_one, mul_div_assoc', hxx]
        _ ≤ x + x / (1 - α) := by linarith
        _ = (1 + 1 / (1 - α)) * x := by ring
    · have hb := sum_Ioc_rpow_neg_le_of_one_lt h hN1
      have hmax : max 1 α = α := max_eq_right h.le
      rw [hmax]
      simp only [Cs, if_neg (not_lt.2 h.le)]
      calc x ^ α * ∑ d ∈ Ioc 0 N, (d : ℝ) ^ (-α) ≤ x ^ α * (1 + 1 / (α - 1)) :=
            mul_le_mul_of_nonneg_left hb (by positivity)
        _ = (1 + 1 / (α - 1)) * x ^ α := by ring
  have hxβ : x ≤ x ^ max 1 α := by
    calc x = x ^ (1 : ℝ) := (Real.rpow_one x).symm
      _ ≤ x ^ max 1 α := Real.rpow_le_rpow_of_exponent_le hx (le_max_left _ _)
  have hC0 : 0 ≤ 2 ^ α / (α * (α + 1)) := by positivity
  calc |∑ d ∈ Ioc 0 N, (∑ q ∈ Ioc 0 ⌊x / d⌋₊, (q : ℝ) ^ α - (x / d) ^ (α + 1) / (α + 1)) -
        x ^ (α + 1) / (α + 1) * (Z - S)|
      ≤ |∑ d ∈ Ioc 0 N, (∑ q ∈ Ioc 0 ⌊x / d⌋₊, (q : ℝ) ^ α - (x / d) ^ (α + 1) / (α + 1))| +
        |x ^ (α + 1) / (α + 1) * (Z - S)| := abs_sub _ _
    _ ≤ Cs * x ^ max 1 α + 2 ^ α / (α * (α + 1)) * x := add_le_add (hE1.trans hE1') hE2
    _ ≤ Cs * x ^ max 1 α + 2 ^ α / (α * (α + 1)) * x ^ max 1 α := by gcongr
    _ = (2 ^ α / (α * (α + 1)) + Cs) * x ^ max 1 α := by ring

/-! ## Theorem 3.6 -/

theorem sum_sigma_rpow_neg_eq' (β : ℝ) (N : ℕ) :
    ∑ d ∈ Ioc 0 N, ∑ q ∈ Ioc 0 (N / d), (d : ℝ) ^ (-β) =
      ∑ d ∈ Ioc 0 N, (d : ℝ) ^ (-β) * ((N / d : ℕ) : ℝ) := by
  refine sum_congr rfl fun d _ ↦ ?_
  rw [sum_const, Nat.card_Ioc, Nat.sub_zero, nsmul_eq_mul, mul_comm]

/-- `∑_{n ≤ N} σ_{-β}(n) = ∑_{d ≤ N} d^{-β} ⌊N/d⌋`. -/
theorem sum_sigma_rpow_neg_eq (β : ℝ) (N : ℕ) :
    ∑ n ∈ Ioc 0 N, ∑ d ∈ n.divisors, (d : ℝ) ^ (-β) =
      ∑ d ∈ Ioc 0 N, (d : ℝ) ^ (-β) * ((N / d : ℕ) : ℝ) := by
  rw [← sum_sigma_rpow_neg_eq' β N,
    ← sum_Ioc_sum_divisorsAntidiagonal (fun d _ ↦ (d : ℝ) ^ (-β)) N]
  refine sum_congr rfl fun n _ ↦ ?_
  rw [Nat.sum_divisorsAntidiagonal (fun d _ ↦ (d : ℝ) ^ (-β))]

/-- The common step of Theorem 3.6: for `β > 0`, `x ≥ 1`,
`|∑_{n ≤ x} σ_{-β}(n) - ζ(β+1) x| ≤ 2^β x^{1-β}/β + ∑_{d ≤ x} d^{-β}`. -/
theorem abs_sum_sigma_rpow_neg_sub_le {β : ℝ} (hβ : 0 < β) {x : ℝ} (hx : 1 ≤ x) :
    |∑ n ∈ Ioc 0 ⌊x⌋₊, ∑ d ∈ n.divisors, (d : ℝ) ^ (-β) -
      (∑' n : ℕ, (n : ℝ) ^ (-(β + 1))) * x| ≤
        2 ^ β * x ^ (1 - β) / β + ∑ d ∈ Ioc 0 ⌊x⌋₊, (d : ℝ) ^ (-β) := by
  have hx0 : 0 < x := by linarith
  set N := ⌊x⌋₊
  have hN1 : 1 ≤ N := Nat.le_floor (by exact_mod_cast hx)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hNx : (N : ℝ) ≤ x := Nat.floor_le hx0.le
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have h2N : x ≤ 2 * N := by have := Nat.lt_floor_add_one x; linarith
  set Z := ∑' n : ℕ, (n : ℝ) ^ (-(β + 1))
  set S := ∑ d ∈ Ioc 0 N, (d : ℝ) ^ (-(β + 1))
  rw [sum_sigma_rpow_neg_eq]
  -- `⌊N/d⌋ = x/d - {x/d}`
  have e : ∑ d ∈ Ioc 0 N, (d : ℝ) ^ (-β) * ((N / d : ℕ) : ℝ) - Z * x =
      -(x * (Z - S)) - ∑ d ∈ Ioc 0 N, (d : ℝ) ^ (-β) * (x / d - ((N / d : ℕ) : ℝ)) := by
    have e1 : ∀ d ∈ Ioc 0 N, (d : ℝ) ^ (-β) * (x / d) = x * (d : ℝ) ^ (-(β + 1)) := by
      intro d hd
      have hd0 : (0 : ℝ) < d := by exact_mod_cast (mem_Ioc.1 hd).1
      rw [show -(β + 1) = -β + -1 by ring, Real.rpow_add hd0, Real.rpow_neg_one]
      field_simp
    have : ∑ d ∈ Ioc 0 N, (d : ℝ) ^ (-β) * (x / d - ((N / d : ℕ) : ℝ)) =
        x * S - ∑ d ∈ Ioc 0 N, (d : ℝ) ^ (-β) * ((N / d : ℕ) : ℝ) := by
      simp_rw [mul_sub]
      rw [sum_sub_distrib, sum_congr rfl e1, ← mul_sum]
    rw [this]; ring
  rw [e]
  have hfr : ∀ d ∈ Ioc 0 N, 0 ≤ x / d - ((N / d : ℕ) : ℝ) ∧ x / d - ((N / d : ℕ) : ℝ) ≤ 1 := by
    intro d hd
    have hd0 : (0 : ℝ) < d := by exact_mod_cast (mem_Ioc.1 hd).1
    rw [← Nat.floor_div_natCast]
    exact ⟨sub_nonneg.2 (Nat.floor_le (by positivity)),
      by have := Nat.lt_floor_add_one (x / d); linarith⟩
  have h1 : |∑ d ∈ Ioc 0 N, (d : ℝ) ^ (-β) * (x / d - ((N / d : ℕ) : ℝ))| ≤
      ∑ d ∈ Ioc 0 N, (d : ℝ) ^ (-β) := by
    rw [abs_of_nonneg (sum_nonneg fun d hd ↦ mul_nonneg (by positivity) (hfr d hd).1)]
    refine sum_le_sum fun d hd ↦ ?_
    calc (d : ℝ) ^ (-β) * (x / d - ((N / d : ℕ) : ℝ)) ≤ (d : ℝ) ^ (-β) * 1 :=
          mul_le_mul_of_nonneg_left (hfr d hd).2 (by positivity)
      _ = (d : ℝ) ^ (-β) := mul_one _
  have h2 : |x * (Z - S)| ≤ 2 ^ β * x ^ (1 - β) / β := by
    have ht := abs_tsum_rpow_neg_sub_le (s := β + 1) (by linarith) hN1
    rw [show (1 : ℝ) - (β + 1) = -β by ring, show β + 1 - 1 = β by ring] at ht
    have hNpow : (N : ℝ) ^ (-β) ≤ 2 ^ β * x ^ (-β) := by
      rw [Real.rpow_neg hN0.le, Real.rpow_neg hx0.le, ← div_eq_mul_inv]
      rw [le_div_iff₀ (Real.rpow_pos_of_pos hx0 _), inv_mul_eq_div,
        div_le_iff₀ (Real.rpow_pos_of_pos hN0 _)]
      rw [← Real.mul_rpow (by norm_num) hN0.le]
      exact Real.rpow_le_rpow hx0.le h2N hβ.le
    rw [abs_mul, abs_of_pos hx0]
    calc x * |Z - S| ≤ x * ((N : ℝ) ^ (-β) / β) := mul_le_mul_of_nonneg_left ht hx0.le
      _ ≤ x * (2 ^ β * x ^ (-β) / β) := by gcongr
      _ = 2 ^ β * x ^ (1 - β) / β := by
          rw [show (1 : ℝ) - β = 1 + -β by ring, Real.rpow_add hx0, Real.rpow_one]; ring
  calc _ ≤ |x * (Z - S)| + |∑ d ∈ Ioc 0 N, (d : ℝ) ^ (-β) * (x / d - ((N / d : ℕ) : ℝ))| := by
        refine (abs_sub _ _).trans ?_; rw [abs_neg]
    _ ≤ _ := add_le_add h2 h1

/-- **Apostol, Theorem 3.6**, `β ≠ 1`: for `β > 0`, `β ≠ 1`, `x ≥ 1`,
`∑_{n ≤ x} σ_{-β}(n) = ζ(β+1) x + O(x^δ)`, `δ = max(0, 1 - β)`. -/
@[kb "apostol1976" "Thm 3.6, p. 61"]
theorem exists_abs_sum_sigma_rpow_neg_sub_le {β : ℝ} (hβ : 0 < β) (hβ1 : β ≠ 1) :
    ∃ C, ∀ x : ℝ, 1 ≤ x →
      |∑ n ∈ Ioc 0 ⌊x⌋₊, ∑ d ∈ n.divisors, (d : ℝ) ^ (-β) -
        (∑' n : ℕ, (n : ℝ) ^ (-(β + 1))) * x| ≤ C * x ^ max 0 (1 - β) := by
  set Cs : ℝ := if β < 1 then 1 + 1 / (1 - β) else 1 + 1 / (β - 1)
  refine ⟨2 ^ β / β + Cs, fun x hx ↦ ?_⟩
  have hx0 : 0 < x := by linarith
  have hN1 : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
  have hNx : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx0.le
  have hN0 : (0 : ℝ) < ⌊x⌋₊ := by exact_mod_cast hN1
  refine (abs_sum_sigma_rpow_neg_sub_le hβ hx).trans ?_
  have hxd : x ^ (1 - β) ≤ x ^ max 0 (1 - β) :=
    Real.rpow_le_rpow_of_exponent_le hx (le_max_right _ _)
  have h1 : (1 : ℝ) ≤ x ^ max 0 (1 - β) := Real.one_le_rpow hx (le_max_left _ _)
  have hS : ∑ d ∈ Ioc 0 ⌊x⌋₊, (d : ℝ) ^ (-β) ≤ Cs * x ^ max 0 (1 - β) := by
    rcases lt_or_gt_of_ne hβ1 with h | h
    · simp only [Cs, if_pos h]
      have hb := sum_Ioc_rpow_neg_le_of_lt_one hβ h hN1
      have hNp : (⌊x⌋₊ : ℝ) ^ (1 - β) ≤ x ^ (1 - β) :=
        Real.rpow_le_rpow hN0.le hNx (by linarith)
      have : (⌊x⌋₊ : ℝ) ^ (1 - β) / (1 - β) ≤ x ^ max 0 (1 - β) / (1 - β) :=
        div_le_div_of_nonneg_right (hNp.trans hxd) (by linarith)
      calc ∑ d ∈ Ioc 0 ⌊x⌋₊, (d : ℝ) ^ (-β) ≤ 1 + x ^ max 0 (1 - β) / (1 - β) := by linarith
        _ ≤ x ^ max 0 (1 - β) + x ^ max 0 (1 - β) / (1 - β) := by linarith
        _ = (1 + 1 / (1 - β)) * x ^ max 0 (1 - β) := by ring
    · simp only [Cs, if_neg (not_lt.2 h.le)]
      have hb := sum_Ioc_rpow_neg_le_of_one_lt h hN1
      have hc : 0 ≤ 1 + 1 / (β - 1) := by
        have : 0 < β - 1 := by linarith
        positivity
      calc ∑ d ∈ Ioc 0 ⌊x⌋₊, (d : ℝ) ^ (-β) ≤ (1 + 1 / (β - 1)) * 1 := by linarith
        _ ≤ (1 + 1 / (β - 1)) * x ^ max 0 (1 - β) := mul_le_mul_of_nonneg_left h1 hc
  have hT : 2 ^ β * x ^ (1 - β) / β ≤ 2 ^ β / β * x ^ max 0 (1 - β) := by
    rw [mul_div_right_comm]
    exact mul_le_mul_of_nonneg_left hxd (by positivity)
  linarith

/-- **Apostol, Theorem 3.6**, `β = 1`: `∑_{n ≤ x} σ_{-1}(n) = ζ(2) x + O(log x)`; explicitly the
error is at most `6 log x` for `x ≥ 2` (the book's range `x ≥ 1` cannot hold at `x = 1`). -/
@[kb "apostol1976" "Thm 3.6, p. 61"]
theorem abs_sum_sigma_neg_one_sub_le {x : ℝ} (hx : 2 ≤ x) :
    |∑ n ∈ Ioc 0 ⌊x⌋₊, ∑ d ∈ n.divisors, (d : ℝ) ^ (-(1 : ℝ)) -
      (∑' n : ℕ, (n : ℝ) ^ (-((1 : ℝ) + 1))) * x| ≤ 6 * Real.log x := by
  have hx1 : 1 ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  refine (abs_sum_sigma_rpow_neg_sub_le one_pos hx1).trans ?_
  have hS : ∑ d ∈ Ioc 0 ⌊x⌋₊, (d : ℝ) ^ (-(1 : ℝ)) ≤ 1 + Real.log x := by
    have := sum_Ioc_inv_le_one_add_log hx1
    convert this using 2 with d
    rw [Real.rpow_neg_one, one_div]
  have hl2 : (0.69 : ℝ) < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hlx : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  have hT : (2 : ℝ) ^ (1 : ℝ) * x ^ ((1 : ℝ) - 1) / 1 = 2 := by simp
  rw [hT]
  linarith

end NTKB.Apostol
