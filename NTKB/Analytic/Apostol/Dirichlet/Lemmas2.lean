/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Apostol.Dirichlet.Lemmas

/-!
# Lemmas 7.5, 7.6 and 7.8 of Apostol's proof of Dirichlet's theorem

For `χ ≠ χ₁` mod `k`, with `M_χ(x) = ∑_{n ≤ x} μ(n)χ(n)/n` (`moebiusCharSum`):
* Lemma 7.5: `∑_{p ≤ x} χ(p) log p/p = -L'(1, χ) M_χ(x) + O(1)`;
* Lemma 7.6: `L(1, χ) M_χ(x) = O(1)` (in fact `1 + O(1)`);
* Lemma 7.8: if `L(1, χ) = 0` then `L'(1, χ) M_χ(x) = log x + O(1)`.
-/

open Finset ArithmeticFunction Filter Topology Real Chebyshev
open scoped ArithmeticFunction.Moebius

namespace NTKB.Apostol

variable {k : ℕ} [NeZero k]

/-- `∑_{d ≤ N} u(d) ∑_{c ≤ N/d} v(c) = ∑_{n ≤ N} ∑_{dc = n} u(d) v(c)`. -/
theorem sum_Ioc_mul_sum_Ioc_div (u v : ℕ → ℂ) (N : ℕ) :
    ∑ d ∈ Ioc 0 N, u d * ∑ c ∈ Ioc 0 (N / d), v c =
      ∑ n ∈ Ioc 0 N, ∑ p ∈ n.divisorsAntidiagonal, u p.1 * v p.2 := by
  rw [sum_Ioc_sum_divisorsAntidiagonal (fun a b ↦ u a * v b)]
  simp [mul_sum]

theorem char_mul_of_mem_divisorsAntidiagonal (χ : DirichletCharacter ℂ k) {n : ℕ} {p : ℕ × ℕ}
    (hp : p ∈ n.divisorsAntidiagonal) : χ p.1 * χ p.2 = χ n := by
  rw [← map_mul, ← Nat.cast_mul, (Nat.mem_divisorsAntidiagonal.1 hp).1]

theorem one_div_mul_of_mem_divisorsAntidiagonal {n : ℕ} {p : ℕ × ℕ}
    (hp : p ∈ n.divisorsAntidiagonal) : (1 / p.1 : ℝ) * (1 / p.2) = 1 / n := by
  rw [one_div_mul_one_div, ← Nat.cast_mul, (Nat.mem_divisorsAntidiagonal.1 hp).1]

theorem sum_divisorsAntidiagonal_moebius (n : ℕ) :
    ∑ p ∈ n.divisorsAntidiagonal, (μ p.1 : ℂ) = if n = 1 then 1 else 0 := by
  rw [Nat.sum_divisorsAntidiagonal (fun a _ ↦ (μ a : ℂ)), sum_divisors_moebius,
    ArithmeticFunction.one_apply]

/-- The bound `‖∑_{c ≤ y} χ(c) log c/c + L'(1, χ)‖ ≤ C (1 + log y)/y` for all `y ≥ 1`
(Theorem 6.18 (10) for `y ≥ 3`, trivial for `1 ≤ y < 3`). -/
theorem exists_norm_sum_char_log_div_add_le {χ : DirichletCharacter ℂ k} (hχ : χ ≠ 1) :
    ∃ C, 0 ≤ C ∧ ∀ y : ℝ, 1 ≤ y →
      ‖∑ c ∈ Ioc 0 ⌊y⌋₊, χ c * ((Real.log c / c : ℝ) : ℂ) + LOneDeriv χ‖ ≤
        C * ((1 + Real.log y) / y) := by
  refine ⟨max (2 * (k : ℝ)) (3 * (2 + ‖LOneDeriv χ‖)), by positivity, fun y hy ↦ ?_⟩
  have hy0 : 0 < y := by linarith
  have hl0 : 0 ≤ Real.log y := Real.log_nonneg hy
  rcases le_or_gt 3 y with h3 | h3
  · refine (norm_sum_char_log_div_add_LOneDeriv_le hχ h3).trans ?_
    calc 2 * k * (Real.log y / y) ≤ 2 * k * ((1 + Real.log y) / y) := by
          gcongr; linarith
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  · have hN : ⌊y⌋₊ ≤ 2 := by
      have := Nat.floor_le hy0.le
      have : (⌊y⌋₊ : ℝ) < 3 := by linarith
      exact_mod_cast Nat.lt_succ_iff.1 (by exact_mod_cast this)
    have hsum : ‖∑ c ∈ Ioc 0 ⌊y⌋₊, χ c * ((Real.log c / c : ℝ) : ℂ)‖ ≤ 2 := by
      refine (norm_sum_le _ _).trans ?_
      calc ∑ c ∈ Ioc 0 ⌊y⌋₊, ‖χ c * ((Real.log c / c : ℝ) : ℂ)‖ ≤ ∑ c ∈ Ioc 0 ⌊y⌋₊, (1 : ℝ) := by
            refine sum_le_sum fun c hc ↦ ?_
            have hc1 : (1 : ℝ) ≤ c := by exact_mod_cast (mem_Ioc.1 hc).1
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
            have hlc : 0 ≤ Real.log c / c := div_nonneg (Real.log_nonneg hc1) (by linarith)
            rw [abs_of_nonneg hlc]
            have : Real.log c / c ≤ 1 := by
              rw [div_le_one (by linarith)]
              have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < c by linarith); linarith
            calc ‖χ c‖ * (Real.log c / c) ≤ 1 * 1 :=
                  mul_le_mul (DirichletCharacter.norm_le_one χ _) this hlc zero_le_one
              _ = 1 := one_mul _
        _ = ⌊y⌋₊ := by simp
        _ ≤ 2 := by exact_mod_cast hN
    have hfrac : 1 / 3 ≤ (1 + Real.log y) / y := by
      rw [div_le_div_iff₀ (by norm_num) hy0]; linarith
    calc ‖∑ c ∈ Ioc 0 ⌊y⌋₊, χ c * ((Real.log c / c : ℝ) : ℂ) + LOneDeriv χ‖
        ≤ 2 + ‖LOneDeriv χ‖ := (norm_add_le _ _).trans (by linarith)
      _ = 3 * (2 + ‖LOneDeriv χ‖) * (1 / 3) := by ring
      _ ≤ max (2 * (k : ℝ)) (3 * (2 + ‖LOneDeriv χ‖)) * ((1 + Real.log y) / y) :=
          mul_le_mul (le_max_right _ _) hfrac (by norm_num) (by positivity)

/-! ## Lemma 7.6 -/

/-- `∑_{d ≤ x} μ(d)χ(d)/d ∑_{c ≤ x/d} χ(c)/c = 1` for `x ≥ 1`. -/
theorem sum_moebius_char_mul_sum_char_div (χ : DirichletCharacter ℂ k) {x : ℝ} (hx : 1 ≤ x) :
    ∑ d ∈ Ioc 0 ⌊x⌋₊, (μ d : ℂ) * χ d * ((1 / d : ℝ) : ℂ) *
      ∑ c ∈ Ioc 0 ⌊x / d⌋₊, χ c * ((1 / c : ℝ) : ℂ) = 1 := by
  have hN1 : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
  simp_rw [Nat.floor_div_natCast]
  rw [sum_Ioc_mul_sum_Ioc_div (fun d ↦ (μ d : ℂ) * χ d * ((1 / d : ℝ) : ℂ))
    (fun c ↦ χ c * ((1 / c : ℝ) : ℂ))]
  have hn : ∀ n ∈ Ioc 0 ⌊x⌋₊, ∑ p ∈ n.divisorsAntidiagonal,
      (μ p.1 : ℂ) * χ p.1 * ((1 / p.1 : ℝ) : ℂ) * (χ p.2 * ((1 / p.2 : ℝ) : ℂ)) =
      χ n * ((1 / n : ℝ) : ℂ) * (if n = 1 then 1 else 0) := by
    intro n _
    rw [← sum_divisorsAntidiagonal_moebius, mul_sum]
    refine sum_congr rfl fun p hp ↦ ?_
    rw [← char_mul_of_mem_divisorsAntidiagonal χ hp, ← one_div_mul_of_mem_divisorsAntidiagonal hp]
    push_cast; ring
  rw [sum_congr rfl hn, sum_eq_single 1]
  · simp
  · intro b _ hb; simp [hb]
  · intro h; simp [hN1] at h

/-- **Apostol, Lemma 7.6.** For `χ ≠ χ₁`, `‖L(1, χ) M_χ(x) - 1‖ ≤ 2k` for `x ≥ 1`; in particular
`L(1, χ) ∑_{n ≤ x} μ(n)χ(n)/n = O(1)`. -/
@[kb "apostol1976" "Lemma 7.6, p. 149"]
theorem lemma_7_6 {χ : DirichletCharacter ℂ k} (hχ : χ ≠ 1) {x : ℝ} (hx : 1 ≤ x) :
    ‖LOne χ * moebiusCharSum χ x - 1‖ ≤ 2 * k := by
  have hx0 : 0 < x := by linarith
  have hid := sum_moebius_char_mul_sum_char_div χ hx
  -- `1 = L M + ∑ μχ/d · E(x/d)`
  have e : LOne χ * moebiusCharSum χ x - 1 = -∑ d ∈ Ioc 0 ⌊x⌋₊, (μ d : ℂ) * χ d *
      ((1 / d : ℝ) : ℂ) * (∑ c ∈ Ioc 0 ⌊x / d⌋₊, χ c * ((1 / c : ℝ) : ℂ) - LOne χ) := by
    conv_lhs => rw [← hid]
    rw [moebiusCharSum, mul_sum, ← sum_sub_distrib, ← sum_neg_distrib]
    exact sum_congr rfl fun d _ ↦ by ring
  rw [e, norm_neg]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ d ∈ Ioc 0 ⌊x⌋₊, ‖(μ d : ℂ) * χ d * ((1 / d : ℝ) : ℂ) *
        (∑ c ∈ Ioc 0 ⌊x / d⌋₊, χ c * ((1 / c : ℝ) : ℂ) - LOne χ)‖
      ≤ ∑ d ∈ Ioc 0 ⌊x⌋₊, (2 * k) / x := by
        refine sum_le_sum fun d hd ↦ ?_
        have hd' : (0 : ℝ) < d := by exact_mod_cast (mem_Ioc.1 hd).1
        have hdx : (d : ℝ) ≤ x := by
          have : (d : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast (mem_Ioc.1 hd).2
          linarith [Nat.floor_le hx0.le]
        have hxd : 1 ≤ x / d := by rw [le_div_iff₀ hd']; linarith
        have hb := norm_sum_char_div_sub_LOne_le hχ hxd
        have hμ : ‖(μ d : ℂ)‖ ≤ 1 := by
          rw [Complex.norm_intCast]; exact_mod_cast abs_moebius_le_one
        rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (by positivity : (0 : ℝ) < 1 / d)]
        calc ‖(μ d : ℂ)‖ * ‖χ d‖ * (1 / d) *
              ‖∑ c ∈ Ioc 0 ⌊x / d⌋₊, χ c * ((1 / c : ℝ) : ℂ) - LOne χ‖
            ≤ 1 * 1 * (1 / d) * (2 * k * (1 / (x / d))) := by
              gcongr
              exact DirichletCharacter.norm_le_one χ _
          _ = (2 * k) / x := by field_simp
    _ ≤ 2 * k := sum_Ioc_floor_const_div_le hx0 (by positivity)

/-! ## Lemma 7.5 -/

/-- `∑_{n ≤ x} χ(n)Λ(n)/n = ∑_{d ≤ x} μ(d)χ(d)/d ∑_{c ≤ x/d} χ(c) log c/c`. -/
theorem sum_char_vonMangoldt_div_eq (χ : DirichletCharacter ℂ k) (x : ℝ) :
    ∑ n ∈ Ioc 0 ⌊x⌋₊, χ n * ((Λ n / n : ℝ) : ℂ) =
      ∑ d ∈ Ioc 0 ⌊x⌋₊, (μ d : ℂ) * χ d * ((1 / d : ℝ) : ℂ) *
        ∑ c ∈ Ioc 0 ⌊x / d⌋₊, χ c * ((Real.log c / c : ℝ) : ℂ) := by
  simp_rw [Nat.floor_div_natCast]
  rw [sum_Ioc_mul_sum_Ioc_div (fun d ↦ (μ d : ℂ) * χ d * ((1 / d : ℝ) : ℂ))
    (fun c ↦ χ c * ((Real.log c / c : ℝ) : ℂ))]
  refine sum_congr rfl fun n _ ↦ ?_
  have hΛ : Λ n = ∑ p ∈ n.divisorsAntidiagonal, (μ p.1 : ℝ) * Real.log p.2 := by
    rw [← moebius_mul_log_eq_vonMangoldt, ArithmeticFunction.mul_apply]
    simp [intCoe_apply, log_apply]
  rw [hΛ, Complex.ofReal_div, Complex.ofReal_sum, sum_div, mul_sum]
  refine sum_congr rfl fun p hp ↦ ?_
  rw [← char_mul_of_mem_divisorsAntidiagonal χ hp]
  have h1 := one_div_mul_of_mem_divisorsAntidiagonal hp
  have hn : (n : ℝ) = p.1 * p.2 := by
    rw [← Nat.cast_mul, (Nat.mem_divisorsAntidiagonal.1 hp).1]
  have hp1 : (p.1 : ℝ) ≠ 0 := by
    exact_mod_cast Nat.left_ne_zero_of_mem_divisorsAntidiagonal hp
  have hp2 : (p.2 : ℝ) ≠ 0 := by
    exact_mod_cast Nat.right_ne_zero_of_mem_divisorsAntidiagonal hp
  rw [hn]
  push_cast
  field_simp

/-- **Apostol, Lemma 7.5.** For `χ ≠ χ₁` and `x ≥ 1`,
`∑_{p ≤ x} χ(p) log p/p = -L'(1, χ) ∑_{n ≤ x} μ(n)χ(n)/n + O(1)`. -/
@[kb "apostol1976" "Lemma 7.5, p. 149"]
theorem lemma_7_5 {χ : DirichletCharacter ℂ k} (hχ : χ ≠ 1) :
    ∃ C, ∀ x : ℝ, 1 ≤ x → ‖primeCharSum χ x + LOneDeriv χ * moebiusCharSum χ x‖ ≤ C := by
  obtain ⟨CA, hCA⟩ := exists_sum_nonprime_vonMangoldt_div_le
  obtain ⟨C2, hC20, hC2⟩ := exists_norm_sum_char_log_div_add_le hχ
  refine ⟨CA + 3 * C2, fun x hx ↦ ?_⟩
  have hx0 : 0 < x := by linarith
  -- (i) primes versus prime powers
  have hsplit : ∑ n ∈ Ioc 0 ⌊x⌋₊, χ n * ((Λ n / n : ℝ) : ℂ) = primeCharSum χ x +
      ∑ n ∈ Ioc 0 ⌊x⌋₊ with ¬ n.Prime, χ n * ((Λ n / n : ℝ) : ℂ) := by
    rw [primeCharSum, ← sum_filter_add_sum_filter_not (Ioc 0 ⌊x⌋₊) Nat.Prime]
    congr 1
    refine sum_congr rfl fun p hp ↦ ?_
    rw [vonMangoldt_apply_prime (mem_filter.1 hp).2]
  have hnp : ‖∑ n ∈ Ioc 0 ⌊x⌋₊ with ¬ n.Prime, χ n * ((Λ n / n : ℝ) : ℂ)‖ ≤ CA := by
    refine (norm_sum_le _ _).trans ((sum_le_sum fun n _ ↦ ?_).trans (hCA ⌊x⌋₊))
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg _))]
    calc ‖χ n‖ * (Λ n / n) ≤ 1 * (Λ n / n) := mul_le_mul_of_nonneg_right
          (DirichletCharacter.norm_le_one χ _) (div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg _))
      _ = Λ n / n := one_mul _
  -- (ii)–(iv)
  have hmain : ‖∑ n ∈ Ioc 0 ⌊x⌋₊, χ n * ((Λ n / n : ℝ) : ℂ) + LOneDeriv χ * moebiusCharSum χ x‖
      ≤ 3 * C2 := by
    rw [sum_char_vonMangoldt_div_eq, moebiusCharSum, mul_sum, ← sum_add_distrib]
    have e : ∀ d ∈ Ioc 0 ⌊x⌋₊, (μ d : ℂ) * χ d * ((1 / d : ℝ) : ℂ) *
        ∑ c ∈ Ioc 0 ⌊x / d⌋₊, χ c * ((Real.log c / c : ℝ) : ℂ) +
        LOneDeriv χ * ((μ d : ℂ) * χ d * ((1 / d : ℝ) : ℂ)) =
        (μ d : ℂ) * χ d * ((1 / d : ℝ) : ℂ) *
          (∑ c ∈ Ioc 0 ⌊x / d⌋₊, χ c * ((Real.log c / c : ℝ) : ℂ) + LOneDeriv χ) :=
      fun d _ ↦ by ring
    rw [sum_congr rfl e]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ d ∈ Ioc 0 ⌊x⌋₊, ‖(μ d : ℂ) * χ d * ((1 / d : ℝ) : ℂ) *
          (∑ c ∈ Ioc 0 ⌊x / d⌋₊, χ c * ((Real.log c / c : ℝ) : ℂ) + LOneDeriv χ)‖
        ≤ ∑ d ∈ Ioc 0 ⌊x⌋₊, C2 / x * (1 + Real.log (x / d)) := by
          refine sum_le_sum fun d hd ↦ ?_
          have hd' : (0 : ℝ) < d := by exact_mod_cast (mem_Ioc.1 hd).1
          have hdx : (d : ℝ) ≤ x := by
            have : (d : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast (mem_Ioc.1 hd).2
            linarith [Nat.floor_le hx0.le]
          have hxd : 1 ≤ x / d := by rw [le_div_iff₀ hd']; linarith
          have hb := hC2 (x / d) hxd
          have hμ : ‖(μ d : ℂ)‖ ≤ 1 := by
            rw [Complex.norm_intCast]; exact_mod_cast abs_moebius_le_one
          rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos (by positivity : (0 : ℝ) < 1 / d)]
          calc ‖(μ d : ℂ)‖ * ‖χ d‖ * (1 / d) *
                ‖∑ c ∈ Ioc 0 ⌊x / d⌋₊, χ c * ((Real.log c / c : ℝ) : ℂ) + LOneDeriv χ‖
              ≤ 1 * 1 * (1 / d) * (C2 * ((1 + Real.log (x / d)) / (x / d))) := by
                gcongr
                exact DirichletCharacter.norm_le_one χ _
            _ = C2 / x * (1 + Real.log (x / d)) := by field_simp
      _ = C2 / x * ∑ d ∈ Ioc 0 ⌊x⌋₊, (1 + Real.log (x / d)) := by rw [mul_sum]
      _ ≤ C2 / x * (3 * x) :=
          mul_le_mul_of_nonneg_left (sum_Ioc_floor_one_add_log_div_le hx) (by positivity)
      _ = 3 * C2 := by field_simp
  rw [hsplit] at hmain
  calc ‖primeCharSum χ x + LOneDeriv χ * moebiusCharSum χ x‖
      = ‖(primeCharSum χ x + ∑ n ∈ Ioc 0 ⌊x⌋₊ with ¬ n.Prime, χ n * ((Λ n / n : ℝ) : ℂ) +
          LOneDeriv χ * moebiusCharSum χ x) -
          ∑ n ∈ Ioc 0 ⌊x⌋₊ with ¬ n.Prime, χ n * ((Λ n / n : ℝ) : ℂ)‖ := by ring_nf
    _ ≤ 3 * C2 + CA := (norm_sub_le _ _).trans (add_le_add hmain hnp)
    _ = CA + 3 * C2 := add_comm _ _

end NTKB.Apostol
