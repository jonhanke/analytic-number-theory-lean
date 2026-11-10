/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Apostol.Dirichlet.Lemmas2

/-!
# Dirichlet's theorem by Apostol's elementary route (Chapter 7, Theorems 7.3 and 7.9)

* Lemma 7.8: if `χ ≠ χ₁` and `L(1, χ) = 0` then `L'(1, χ) ∑_{n ≤ x} μ(n)χ(n)/n = log x + O(1)`;
* Lemma 7.7: `∑_{p ≤ x, p ≡ 1} log p/p = ((1 - N(k))/φ(k)) log x + O(1)`, `N(k)` the number of
  nonprincipal `χ` mod `k` with `L(1, χ) = 0`;
* `N(k) = 0`, i.e. `L(1, χ) ≠ 0` for every `χ ≠ χ₁` (Apostol, §7.3): by Lemma 7.7 `N(k) ≤ 1`; the
  characters with `L(1, χ) = 0` are closed under `χ ↦ χ̄` (`L(1, χ̄)` is the conjugate of
  `L(1, χ)`), so a single one would be real, contradicting Theorem 6.20;
* **Theorem 7.3**: for `(h, k) = 1`, `∑_{p ≤ x, p ≡ h (mod k)} log p/p = (1/φ(k)) log x + O(1)`;
* **Theorem 7.9** (Dirichlet): there are infinitely many primes `p ≡ h (mod k)`.

Mathlib proves Dirichlet's theorem (`Nat.setOf_prime_and_eq_mod_infinite`) and `L(1, χ) ≠ 0` by
the analytic route; this file follows Apostol's elementary proof, where `L(1, χ)` is the sum of the
conditionally convergent series `∑ χ(n)/n`.
-/

open Finset ArithmeticFunction Filter Topology Real Chebyshev
open scoped ArithmeticFunction.Moebius

namespace NTKB.Apostol

variable {k : ℕ} [NeZero k]

/-! ## Lemma 7.8 -/

/-- `∑_{d ≤ x} μ(d)χ(d) ∑_{c ≤ x/d} χ(c) (x/(dc)) log(x/(dc)) = x log x` for `x ≥ 1`. -/
theorem sum_moebius_char_mul_sum_xlogx (χ : DirichletCharacter ℂ k) {x : ℝ} (hx : 1 ≤ x) :
    ∑ d ∈ Ioc 0 ⌊x⌋₊, (μ d : ℂ) * χ d *
      ∑ c ∈ Ioc 0 ⌊x / d⌋₊, χ c * (((x / d / c) * Real.log (x / d / c) : ℝ) : ℂ) =
        ((x * Real.log x : ℝ) : ℂ) := by
  have hN1 : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
  simp_rw [Nat.floor_div_natCast, mul_sum]
  set w : ℕ → ℂ := fun n ↦ (((x / n) * Real.log (x / n) : ℝ) : ℂ)
  have hw : ∀ a b : ℕ, (((x / a / b) * Real.log (x / a / b) : ℝ) : ℂ) = w (a * b) := by
    intro a b; simp only [w, div_div, Nat.cast_mul]
  simp_rw [hw]
  rw [← sum_Ioc_sum_divisorsAntidiagonal (fun a b ↦ (μ a : ℂ) * χ a * (χ b * w (a * b)))]
  have hn : ∀ n ∈ Ioc 0 ⌊x⌋₊, ∑ p ∈ n.divisorsAntidiagonal,
      (μ p.1 : ℂ) * χ p.1 * (χ p.2 * w (p.1 * p.2)) = χ n * w n * (if n = 1 then 1 else 0) := by
    intro n _
    rw [← sum_divisorsAntidiagonal_moebius, mul_sum]
    refine sum_congr rfl fun p hp ↦ ?_
    rw [← char_mul_of_mem_divisorsAntidiagonal χ hp, (Nat.mem_divisorsAntidiagonal.1 hp).1]
    ring
  rw [sum_congr rfl hn, sum_eq_single 1]
  · simp [w]
  · intro b _ hb; simp [hb]
  · intro h; simp [hN1] at h

/-- **Apostol, Lemma 7.8.** If `χ ≠ χ₁` and `L(1, χ) = 0` then
`L'(1, χ) ∑_{n ≤ x} μ(n)χ(n)/n = log x + O(1)` for `x ≥ 1`. -/
@[kb "apostol1976" "Lemma 7.8, p. 150"]
theorem lemma_7_8 {χ : DirichletCharacter ℂ k} (hχ : χ ≠ 1) (hL : LOne χ = 0) :
    ∃ C, ∀ x : ℝ, 1 ≤ x → ‖LOneDeriv χ * moebiusCharSum χ x - Real.log x‖ ≤ C := by
  obtain ⟨C2, hC20, hC2⟩ := exists_norm_sum_char_log_div_add_le hχ
  set K := 2 * (k : ℝ) + C2
  refine ⟨3 * K, fun x hx ↦ ?_⟩
  have hx0 : 0 < x := by linarith
  -- `G(y) - y L'(1, χ)` is `O(1 + log y)`
  have hG : ∀ y : ℝ, 1 ≤ y →
      ‖∑ c ∈ Ioc 0 ⌊y⌋₊, χ c * (((y / c) * Real.log (y / c) : ℝ) : ℂ) - y * LOneDeriv χ‖ ≤
        K * (1 + Real.log y) := by
    intro y hy
    have hy0 : 0 < y := by linarith
    have hl0 : 0 ≤ Real.log y := Real.log_nonneg hy
    have e : ∑ c ∈ Ioc 0 ⌊y⌋₊, χ c * (((y / c) * Real.log (y / c) : ℝ) : ℂ) - y * LOneDeriv χ =
        ((y * Real.log y : ℝ) : ℂ) * (∑ c ∈ Ioc 0 ⌊y⌋₊, χ c * ((1 / c : ℝ) : ℂ) - LOne χ) -
          (y : ℂ) * (∑ c ∈ Ioc 0 ⌊y⌋₊, χ c * ((Real.log c / c : ℝ) : ℂ) + LOneDeriv χ) := by
      rw [hL, sub_zero, mul_sum, mul_add, mul_sum, sub_add_eq_sub_sub, ← sum_sub_distrib]
      congr 1
      refine sum_congr rfl fun c hc ↦ ?_
      have hc0 : (0 : ℝ) < c := by exact_mod_cast (mem_Ioc.1 hc).1
      rw [Real.log_div hy0.ne' hc0.ne']
      push_cast
      field_simp
    rw [e]
    have h1 := norm_sum_char_div_sub_LOne_le hχ hy
    have h2 := hC2 y hy
    calc _ ≤ ‖((y * Real.log y : ℝ) : ℂ) * (∑ c ∈ Ioc 0 ⌊y⌋₊, χ c * ((1 / c : ℝ) : ℂ) - LOne χ)‖
          + ‖(y : ℂ) * (∑ c ∈ Ioc 0 ⌊y⌋₊, χ c * ((Real.log c / c : ℝ) : ℂ) + LOneDeriv χ)‖ :=
          norm_sub_le _ _
      _ ≤ (y * Real.log y) * (2 * k * (1 / y)) + y * (C2 * ((1 + Real.log y) / y)) := by
          rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (by positivity), Complex.norm_real, Real.norm_eq_abs, abs_of_pos hy0]
          gcongr
      _ = 2 * k * Real.log y + C2 * (1 + Real.log y) := by field_simp
      _ ≤ K * (1 + Real.log y) := by
          simp only [K]; nlinarith [Nat.cast_nonneg (α := ℝ) k]
  have hid := sum_moebius_char_mul_sum_xlogx χ hx
  -- `x log x - x L' M(x) = ∑ μ(d)χ(d) (G(x/d) - (x/d) L')`
  have e : ((x * Real.log x : ℝ) : ℂ) - (x : ℂ) * (LOneDeriv χ * moebiusCharSum χ x) =
      ∑ d ∈ Ioc 0 ⌊x⌋₊, (μ d : ℂ) * χ d *
        (∑ c ∈ Ioc 0 ⌊x / d⌋₊, χ c * (((x / d / c) * Real.log (x / d / c) : ℝ) : ℂ) -
          ((x / d : ℝ) : ℂ) * LOneDeriv χ) := by
    rw [← hid, moebiusCharSum, mul_sum, mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun d hd ↦ ?_
    push_cast
    ring
  have hbound : ‖((x * Real.log x : ℝ) : ℂ) - (x : ℂ) * (LOneDeriv χ * moebiusCharSum χ x)‖ ≤
      K * (3 * x) := by
    rw [e]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ d ∈ Ioc 0 ⌊x⌋₊, ‖(μ d : ℂ) * χ d *
          (∑ c ∈ Ioc 0 ⌊x / d⌋₊, χ c * (((x / d / c) * Real.log (x / d / c) : ℝ) : ℂ) -
            ((x / d : ℝ) : ℂ) * LOneDeriv χ)‖
        ≤ ∑ d ∈ Ioc 0 ⌊x⌋₊, K * (1 + Real.log (x / d)) := by
          refine sum_le_sum fun d hd ↦ ?_
          have hd' : (0 : ℝ) < d := by exact_mod_cast (mem_Ioc.1 hd).1
          have hdx : (d : ℝ) ≤ x := by
            have : (d : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast (mem_Ioc.1 hd).2
            linarith [Nat.floor_le hx0.le]
          have hxd : 1 ≤ x / d := by rw [le_div_iff₀ hd']; linarith
          have hμ : ‖(μ d : ℂ)‖ ≤ 1 := by
            rw [Complex.norm_intCast]; exact_mod_cast abs_moebius_le_one
          rw [norm_mul, norm_mul]
          calc ‖(μ d : ℂ)‖ * ‖χ d‖ *
                ‖∑ c ∈ Ioc 0 ⌊x / d⌋₊, χ c * (((x / d / c) * Real.log (x / d / c) : ℝ) : ℂ) -
                  ((x / d : ℝ) : ℂ) * LOneDeriv χ‖ ≤ 1 * 1 * (K * (1 + Real.log (x / d))) := by
                gcongr
                · exact DirichletCharacter.norm_le_one χ _
                · exact hG (x / d) hxd
            _ = K * (1 + Real.log (x / d)) := by ring
      _ = K * ∑ d ∈ Ioc 0 ⌊x⌋₊, (1 + Real.log (x / d)) := by rw [mul_sum]
      _ ≤ K * (3 * x) := mul_le_mul_of_nonneg_left (sum_Ioc_floor_one_add_log_div_le hx)
          (by positivity)
  have e2 : LOneDeriv χ * moebiusCharSum χ x - Real.log x =
      -((1 / x : ℝ) : ℂ) * (((x * Real.log x : ℝ) : ℂ) -
        (x : ℂ) * (LOneDeriv χ * moebiusCharSum χ x)) := by
    have : (x : ℂ) ≠ 0 := by exact_mod_cast hx0.ne'
    push_cast; field_simp; ring
  rw [e2, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  calc 1 / x * ‖((x * Real.log x : ℝ) : ℂ) - (x : ℂ) * (LOneDeriv χ * moebiusCharSum χ x)‖
      ≤ 1 / x * (K * (3 * x)) := mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = 3 * K := by field_simp

/-! ## `L(1, χ̄) = conj L(1, χ)` -/

theorem LOne_inv {χ : DirichletCharacter ℂ k} (hχ : χ ≠ 1) :
    LOne χ⁻¹ = starRingEnd ℂ (LOne χ) := by
  have h1 := tendsto_LOne (χ := χ⁻¹) (inv_ne_one.2 hχ)
  have h2 := ((Complex.continuous_conj.tendsto _).comp (tendsto_LOne hχ))
  refine tendsto_nhds_unique h1 (h2.congr fun N ↦ ?_)
  simp only [Function.comp_apply, map_sum, map_mul, Complex.conj_ofReal]
  refine sum_congr rfl fun n _ ↦ ?_
  rw [← MulChar.star_apply', RCLike.star_def]

/-! ## Lemma 7.7 and `N(k) = 0` -/

theorem sum_ite_eq_zero_eq_sub {α : Type*} [Fintype α] [DecidableEq α] (a : α) (g : α → ℂ) :
    ∑ x, (if x = a then 0 else g x) = ∑ x, g x - g a := by
  rw [eq_sub_iff_add_eq]
  have : g a = ∑ x, (if a = x then g x else 0) := by rw [sum_ite_eq]; simp
  rw [this, ← sum_add_distrib]
  refine sum_congr rfl fun x _ ↦ ?_
  by_cases h : x = a
  · subst h; simp
  · simp [h, Ne.symm h]

/-- `N(k)`: the number of nonprincipal characters mod `k` with `L(1, χ) = 0` (Apostol, §7.3). -/
noncomputable def numLOneZero (k : ℕ) [NeZero k] : ℕ :=
  Nat.card {χ : DirichletCharacter ℂ k // χ ≠ 1 ∧ LOne χ = 0}

/-- For each `χ ≠ χ₁`, `∑_{p ≤ x} χ(p) log p/p = -[L(1,χ) = 0] log x + O(1)` (Lemmas 7.5, 7.6,
7.8). -/
theorem exists_norm_primeCharSum_add_le {χ : DirichletCharacter ℂ k} (hχ : χ ≠ 1) :
    ∃ C, ∀ x : ℝ, 1 ≤ x →
      ‖primeCharSum χ x + (if LOne χ = 0 then (Real.log x : ℂ) else 0)‖ ≤ C := by
  obtain ⟨C5, hC5⟩ := lemma_7_5 hχ
  by_cases hL : LOne χ = 0
  · obtain ⟨C8, hC8⟩ := lemma_7_8 hχ hL
    refine ⟨C5 + C8, fun x hx ↦ ?_⟩
    rw [if_pos hL]
    calc ‖primeCharSum χ x + (Real.log x : ℂ)‖ =
        ‖(primeCharSum χ x + LOneDeriv χ * moebiusCharSum χ x) -
          (LOneDeriv χ * moebiusCharSum χ x - Real.log x)‖ := by ring_nf
      _ ≤ C5 + C8 := (norm_sub_le _ _).trans (add_le_add (hC5 x hx) (hC8 x hx))
  · refine ⟨C5 + ‖LOneDeriv χ‖ * ((2 * k + 1) / ‖LOne χ‖), fun x hx ↦ ?_⟩
    rw [if_neg hL, add_zero]
    have hM : ‖moebiusCharSum χ x‖ ≤ (2 * k + 1) / ‖LOne χ‖ := by
      have h6 := lemma_7_6 hχ hx
      have hLpos : 0 < ‖LOne χ‖ := norm_pos_iff.2 hL
      rw [le_div_iff₀ hLpos, mul_comm, ← norm_mul]
      calc ‖LOne χ * moebiusCharSum χ x‖ = ‖(LOne χ * moebiusCharSum χ x - 1) + 1‖ := by ring_nf
        _ ≤ 2 * k + 1 := (norm_add_le _ _).trans (by rw [norm_one]; linarith)
    calc ‖primeCharSum χ x‖ = ‖(primeCharSum χ x + LOneDeriv χ * moebiusCharSum χ x) -
          LOneDeriv χ * moebiusCharSum χ x‖ := by ring_nf
      _ ≤ C5 + ‖LOneDeriv χ‖ * ((2 * k + 1) / ‖LOne χ‖) := by
          refine (norm_sub_le _ _).trans (add_le_add (hC5 x hx) ?_)
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left hM (norm_nonneg _)

open Classical in
/-- The sum over `χ ≠ χ₁` of `∑_{p ≤ x} χ(p) log p/p` is `-N(k) log x + O(1)`. -/
theorem exists_norm_sum_primeCharSum_add_le :
    ∃ C, ∀ x : ℝ, 1 ≤ x →
      ‖(∑ χ : DirichletCharacter ℂ k, primeCharSum χ x -
        primeCharSum (1 : DirichletCharacter ℂ k) x) +
        (numLOneZero k : ℂ) * Real.log x‖ ≤ C := by
  have hC : ∀ χ : DirichletCharacter ℂ k, ∃ C, ∀ x : ℝ, 1 ≤ x →
      ‖(if χ = 1 then 0 else primeCharSum χ x + (if LOne χ = 0 then (Real.log x : ℂ) else 0))‖
        ≤ C := by
    intro χ
    by_cases h : χ = 1
    · exact ⟨0, fun x _ ↦ by simp [h]⟩
    · obtain ⟨C, hC⟩ := exists_norm_primeCharSum_add_le h
      exact ⟨C, fun x hx ↦ by simpa [h] using hC x hx⟩
  choose C hC using hC
  refine ⟨∑ χ, C χ, fun x hx ↦ ?_⟩
  have hN : (numLOneZero k : ℂ) =
      ∑ χ : DirichletCharacter ℂ k, (if χ ≠ 1 ∧ LOne χ = 0 then 1 else 0) := by
    rw [numLOneZero, Nat.card_eq_fintype_card, Fintype.card_subtype, sum_boole]
  have e : (∑ χ : DirichletCharacter ℂ k, primeCharSum χ x -
      primeCharSum (1 : DirichletCharacter ℂ k) x) +
      (numLOneZero k : ℂ) * Real.log x = ∑ χ : DirichletCharacter ℂ k,
        (if χ = 1 then 0 else primeCharSum χ x + (if LOne χ = 0 then (Real.log x : ℂ) else 0)) := by
    rw [hN, sum_mul, ← sum_ite_eq_zero_eq_sub, ← sum_add_distrib]
    refine sum_congr rfl fun χ _ ↦ ?_
    by_cases h1 : χ = 1 <;> by_cases hL : LOne χ = 0 <;> simp [h1, hL]
  rw [e]
  exact (norm_sum_le _ _).trans (sum_le_sum fun χ _ ↦ hC χ x hx)

/-- **Apostol, Lemma 7.7.** `∑_{p ≤ x, p ≡ 1} log p/p = ((1 - N(k))/φ(k)) log x + O(1)`. -/
@[kb "apostol1976" "Lemma 7.7, p. 150"]
theorem lemma_7_7 :
    ∃ C, ∀ x : ℝ, 1 ≤ x →
      |∑ p ∈ Ioc 0 ⌊x⌋₊ with (p.Prime ∧ ((p : ℕ) : ZMod k) = 1), Real.log p / p -
        (1 - numLOneZero k) / k.totient * Real.log x| ≤ C := by
  obtain ⟨C4, hC4⟩ := lemma_7_4 (h := (1 : ZMod k)) isUnit_one
  obtain ⟨CN, hCN⟩ := exists_norm_sum_primeCharSum_add_le (k := k)
  have hφ : (0 : ℝ) < k.totient := by exact_mod_cast Nat.totient_pos.2 (NeZero.pos k)
  refine ⟨C4 + CN / k.totient, fun x hx ↦ ?_⟩
  have h4 := hC4 x hx
  simp only [ZMod.inv_one, MulChar.map_one, one_mul] at h4
  set S := ∑ p ∈ Ioc 0 ⌊x⌋₊ with (p.Prime ∧ ((p : ℕ) : ZMod k) = 1), Real.log p / p
  set T := ∑ χ : DirichletCharacter ℂ k, primeCharSum χ x -
    primeCharSum (1 : DirichletCharacter ℂ k) x
  have e : ((S - (1 - numLOneZero k) / k.totient * Real.log x : ℝ) : ℂ) =
      ((S : ℂ) - (1 / k.totient : ℂ) * Real.log x - (1 / k.totient : ℂ) * T) +
        (1 / k.totient : ℂ) * (T + (numLOneZero k : ℂ) * Real.log x) := by
    have : (k.totient : ℂ) ≠ 0 := by exact_mod_cast hφ.ne'
    push_cast; field_simp; ring
  rw [← Real.norm_eq_abs, ← Complex.norm_real, e]
  refine (norm_add_le _ _).trans (add_le_add h4 ?_)
  rw [norm_mul, norm_div, norm_one, Complex.norm_natCast, div_mul_eq_mul_div, one_mul]
  exact div_le_div_of_nonneg_right (hCN x hx) hφ.le

/-- **Apostol, §7.3: `N(k) = 0`.** `L(1, χ) ≠ 0` for every nonprincipal `χ` mod `k`. -/
@[kb "apostol1976" "§7.3, N(k) = 0, p. 149"]
theorem numLOneZero_eq_zero : numLOneZero k = 0 := by
  obtain ⟨C, hC⟩ := lemma_7_7 (k := k)
  have hφ : (0 : ℝ) < k.totient := by exact_mod_cast Nat.totient_pos.2 (NeZero.pos k)
  -- `N(k) ≤ 1`: otherwise the right side of Lemma 7.7 tends to `-∞`
  have hle : numLOneZero k ≤ 1 := by
    by_contra hN
    push_neg at hN
    have hN' : (2 : ℝ) ≤ numLOneZero k := by exact_mod_cast hN
    set x := Real.exp (k.totient * (C + 1))
    have hx1 : 1 ≤ x := Real.one_le_exp (by
      have := (abs_nonneg _).trans (hC 1 le_rfl); positivity)
    have h := abs_le.1 (hC x hx1)
    have hlog : Real.log x = k.totient * (C + 1) := Real.log_exp _
    have hS : 0 ≤ ∑ p ∈ Ioc 0 ⌊x⌋₊ with (p.Prime ∧ ((p : ℕ) : ZMod k) = 1), Real.log p / p :=
      sum_nonneg fun p hp ↦ div_nonneg (Real.log_nonneg (by
        exact_mod_cast (mem_filter.1 hp).2.1.one_lt.le)) (Nat.cast_nonneg _)
    have hcoef : (1 - numLOneZero k) / k.totient * Real.log x ≤ -(C + 1) := by
      have e : (1 - numLOneZero k) / k.totient * Real.log x = (1 - numLOneZero k) * (C + 1) := by
        rw [hlog]; field_simp
      rw [e]
      have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 1 le_rfl)
      nlinarith
    linarith [h.2]
  -- `N(k) = 1` is impossible: the unique zero would be a real character
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hle with h0 | h1
  · exact h0
  · exfalso
    obtain ⟨⟨χ₀, hχ₀1, hχ₀L⟩, huniq⟩ := Nat.card_eq_one_iff_exists.1 h1
    have hinv : χ₀⁻¹ ≠ 1 ∧ LOne χ₀⁻¹ = 0 :=
      ⟨inv_ne_one.2 hχ₀1, by rw [LOne_inv hχ₀1, hχ₀L, _root_.map_zero]⟩
    have heq : χ₀⁻¹ = χ₀ := congrArg Subtype.val (huniq ⟨χ₀⁻¹, hinv⟩)
    have hquad : χ₀.IsQuadratic := by
      rw [MulChar.isQuadratic_iff_sq_eq_one, sq]
      nth_rw 2 [← heq]
      exact mul_inv_cancel χ₀
    exact LOne_ne_zero_of_isQuadratic hχ₀1 hquad hχ₀L

/-- `L(1, χ) ≠ 0` for every nonprincipal character mod `k` (Apostol's elementary proof). -/
@[kb "apostol1976" "§7.3, p. 149"]
theorem LOne_ne_zero {χ : DirichletCharacter ℂ k} (hχ : χ ≠ 1) : LOne χ ≠ 0 := by
  intro hL
  have h := numLOneZero_eq_zero (k := k)
  rw [numLOneZero, Nat.card_eq_zero] at h
  rcases h with h | h
  · exact h.false ⟨χ, hχ, hL⟩
  · exact absurd (inferInstance : Finite {χ : DirichletCharacter ℂ k // χ ≠ 1 ∧ LOne χ = 0})
      (not_finite_iff_infinite.2 h)

/-! ## Theorems 7.3 and 7.9 -/

/-- **Apostol, Theorem 7.3.** For `k ≥ 1` and a unit `h` mod `k` (i.e. `(h, k) = 1`),
`∑_{p ≤ x, p ≡ h (mod k)} log p/p = (1/φ(k)) log x + O(1)` for `x ≥ 1`. -/
@[kb "apostol1976" "Thm 7.3, p. 148"]
theorem dirichlet_sum_log_div_prime {h : ZMod k} (hh : IsUnit h) :
    ∃ C, ∀ x : ℝ, 1 ≤ x →
      |∑ p ∈ Ioc 0 ⌊x⌋₊ with (p.Prime ∧ ((p : ℕ) : ZMod k) = h), Real.log p / p -
        1 / k.totient * Real.log x| ≤ C := by
  classical
  obtain ⟨C4, hC4⟩ := lemma_7_4 hh
  have hC : ∀ χ : DirichletCharacter ℂ k, ∃ C, ∀ x : ℝ, 1 ≤ x →
      ‖(if χ = 1 then 0 else χ h⁻¹ * primeCharSum χ x)‖ ≤ C := by
    intro χ
    by_cases h1 : χ = 1
    · exact ⟨0, fun x _ ↦ by simp [h1]⟩
    · obtain ⟨C, hC⟩ := exists_norm_primeCharSum_add_le h1
      refine ⟨C, fun x hx ↦ ?_⟩
      have := hC x hx
      rw [if_neg (LOne_ne_zero h1), add_zero] at this
      rw [if_neg h1, norm_mul]
      calc ‖χ h⁻¹‖ * ‖primeCharSum χ x‖ ≤ 1 * C :=
            mul_le_mul (DirichletCharacter.norm_le_one χ _) this (norm_nonneg _) zero_le_one
        _ = C := one_mul _
  choose C hC using hC
  have hφ : (0 : ℝ) < k.totient := by exact_mod_cast Nat.totient_pos.2 (NeZero.pos k)
  refine ⟨C4 + (∑ χ, C χ) / k.totient, fun x hx ↦ ?_⟩
  set S := ∑ p ∈ Ioc 0 ⌊x⌋₊ with (p.Prime ∧ ((p : ℕ) : ZMod k) = h), Real.log p / p
  set T := ∑ χ : DirichletCharacter ℂ k, χ h⁻¹ * primeCharSum χ x -
    primeCharSum (1 : DirichletCharacter ℂ k) x
  have hT : T = ∑ χ : DirichletCharacter ℂ k, (if χ = 1 then 0 else χ h⁻¹ * primeCharSum χ x) := by
    have hu : IsUnit h⁻¹ := ⟨⟨h⁻¹, h, ZMod.inv_mul_of_unit h hh, ZMod.mul_inv_of_unit h hh⟩, rfl⟩
    rw [sum_ite_eq_zero_eq_sub (1 : DirichletCharacter ℂ k)
      (fun χ ↦ χ h⁻¹ * primeCharSum χ x), MulChar.one_apply hu, one_mul]
  have e : ((S - 1 / k.totient * Real.log x : ℝ) : ℂ) =
      ((S : ℂ) - (1 / k.totient : ℂ) * Real.log x - (1 / k.totient : ℂ) * T) +
        (1 / k.totient : ℂ) * T := by push_cast; ring
  rw [← Real.norm_eq_abs, ← Complex.norm_real, e]
  refine (norm_add_le _ _).trans (add_le_add (hC4 x hx) ?_)
  rw [norm_mul, norm_div, norm_one, Complex.norm_natCast, div_mul_eq_mul_div, one_mul, hT]
  exact div_le_div_of_nonneg_right ((norm_sum_le _ _).trans (sum_le_sum fun χ _ ↦ hC χ x hx))
    hφ.le

/-- **Apostol, Theorem 7.9** (Dirichlet's theorem). If `k > 0` and `(h, k) = 1` there are
infinitely many primes `p ≡ h (mod k)`; deduced from Theorem 7.3. -/
@[kb "apostol1976" "Thm 7.9, p. 154"]
theorem exists_prime_gt_eq {h : ZMod k} (hh : IsUnit h) (M : ℕ) :
    ∃ p, M < p ∧ p.Prime ∧ ((p : ℕ) : ZMod k) = h := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨C, hC⟩ := dirichlet_sum_log_div_prime hh
  have hφ : (0 : ℝ) < k.totient := by exact_mod_cast Nat.totient_pos.2 (NeZero.pos k)
  -- the sum is constant for `x ≥ M`
  set S₀ := ∑ p ∈ Ioc 0 M with (p.Prime ∧ ((p : ℕ) : ZMod k) = h), Real.log p / p
  have hconst : ∀ x : ℝ, (M : ℝ) ≤ x →
      ∑ p ∈ Ioc 0 ⌊x⌋₊ with (p.Prime ∧ ((p : ℕ) : ZMod k) = h), Real.log p / p = S₀ := by
    intro x hx
    have hM : M ≤ ⌊x⌋₊ := Nat.le_floor hx
    refine (sum_subset (filter_subset_filter _ (Ioc_subset_Ioc_right hM)) ?_).symm
    intro p hp hp'
    simp only [mem_filter, mem_Ioc] at hp hp'
    by_cases hpM : p ≤ M
    · exact absurd ⟨⟨hp.1.1, hpM⟩, hp.2⟩ hp'
    · exact absurd hp.2.2 (hcon p (not_le.1 hpM) hp.2.1)
  set x := max (M : ℝ) (Real.exp (k.totient * (C + |S₀| + 1)))
  have hx1 : 1 ≤ x := le_trans (Real.one_le_exp (by
    have := (abs_nonneg _).trans (hC 1 le_rfl); positivity)) (le_max_right _ _)
  have h := abs_le.1 (hC x hx1)
  rw [hconst x (le_max_left _ _)] at h
  have hlog : k.totient * (C + |S₀| + 1) ≤ Real.log x := by
    rw [← Real.log_exp (k.totient * (C + |S₀| + 1))]
    exact Real.log_le_log (Real.exp_pos _) (le_max_right _ _)
  have : C + |S₀| + 1 ≤ 1 / k.totient * Real.log x := by
    rw [one_div_mul_eq_div, le_div_iff₀ hφ]; linarith
  linarith [le_abs_self S₀]

end NTKB.Apostol
