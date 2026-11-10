/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Apostol.Averages.PrimeFloorSum

/-!
# Shapiro's Tauberian theorem and its applications (Apostol, Chapter 4, §§4.6–4.7)

**Theorem 4.8** (Shapiro, 1950). Let `a(n) ≥ 0` with `∑_{n ≤ x} a(n) ⌊x/n⌋ = x log x + O(x)` for
`x ≥ 1`. Then
(a) `∑_{n ≤ x} a(n)/n = log x + O(1)`;
(b) `∑_{n ≤ x} a(n) ≤ B x` for some `B > 0` and all `x ≥ 1`;
(c) `∑_{n ≤ x} a(n) ≥ A x` for some `A > 0` and all `x ≥ x₀`.

Applications: Theorem 4.9 (`a = Λ`: `∑ Λ(n)/n = log x + O(1)`, `c₂ x ≤ ψ(x) ≤ c₁ x`) and
Theorem 4.10 (`a = Λ₁`, the prime part of `Λ`: `∑_{p ≤ x} log p/p = log x + O(1)`,
`c₂ x ≤ ϑ(x) ≤ c₁ x`), both obtained here by Apostol's route (Shapiro's theorem fed with
Theorem 3.12/3.15 and Theorem 3.16 respectively). Mathlib and PrimeNumberTheoremAnd have these
bounds by other routes.

Proofs follow Apostol: (b) from `S(x) - S(x/2) ≤ T(x) - 2T(x/2)` and halving; (a) from
`⌊x/n⌋ = x/n + O(1)` and (b); (c) from (a) applied at `x` and `αx`, `α = e^{-2M-1}`.
-/

open Finset ArithmeticFunction Real Chebyshev

namespace NTKB.Apostol

/-- The key inequality of Shapiro's proof, in integer form:
`S(N) - S(N/2) ≤ T(N) - 2 T(N/2)` where `S(N) = ∑_{n ≤ N} a(n)`, `T(N) = ∑_{n ≤ N} a(n) ⌊N/n⌋`. -/
theorem shapiro_key {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (N : ℕ) :
    ∑ n ∈ Ioc 0 N, a n - ∑ n ∈ Ioc 0 (N / 2), a n ≤
      ∑ n ∈ Ioc 0 N, a n * ((N / n : ℕ) : ℝ) -
        2 * ∑ n ∈ Ioc 0 (N / 2), a n * ((N / 2 / n : ℕ) : ℝ) := by
  have hsub : Ioc 0 (N / 2) ⊆ Ioc 0 N := Ioc_subset_Ioc_right (Nat.div_le_self _ _)
  -- extend the second `T` sum to `n ≤ N` (the extra terms vanish)
  have hT2 : ∑ n ∈ Ioc 0 (N / 2), a n * ((N / 2 / n : ℕ) : ℝ) =
      ∑ n ∈ Ioc 0 N, a n * ((N / 2 / n : ℕ) : ℝ) := by
    refine sum_subset hsub fun n hn hn' ↦ ?_
    simp only [mem_Ioc, not_and, not_le] at hn hn'
    rw [Nat.div_eq_of_lt (hn' hn.1), Nat.cast_zero, mul_zero]
  have hS : ∑ n ∈ Ioc 0 N, a n - ∑ n ∈ Ioc 0 (N / 2), a n = ∑ n ∈ Ioc (N / 2) N, a n := by
    rw [← sum_Ioc_consecutive _ (Nat.zero_le _) (Nat.div_le_self N 2)]; ring
  have hT : ∑ n ∈ Ioc 0 N, a n * ((N / n : ℕ) : ℝ) -
      2 * ∑ n ∈ Ioc 0 N, a n * ((N / 2 / n : ℕ) : ℝ) =
      ∑ n ∈ Ioc 0 N, a n * (((N / n : ℕ) : ℝ) - 2 * ((N / 2 / n : ℕ) : ℝ)) := by
    rw [mul_sum, ← sum_sub_distrib]; exact sum_congr rfl fun n _ ↦ by ring
  rw [hT2, hS, hT, ← sum_Ioc_consecutive _ (Nat.zero_le _) (Nat.div_le_self N 2)]
  have hfac : ∀ n, (0 : ℝ) ≤ ((N / n : ℕ) : ℝ) - 2 * ((N / 2 / n : ℕ) : ℝ) := fun n ↦ by
    have h1 : N / 2 / n = N / n / 2 := by rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, mul_comm]
    have h2 := Nat.mul_div_le (N / n) 2
    rw [h1, sub_nonneg]
    exact_mod_cast h2
  have h0 : 0 ≤ ∑ n ∈ Ioc 0 (N / 2), a n * (((N / n : ℕ) : ℝ) - 2 * ((N / 2 / n : ℕ) : ℝ)) :=
    sum_nonneg fun n _ ↦ mul_nonneg (ha n) (hfac n)
  have h1 : ∑ n ∈ Ioc (N / 2) N, a n ≤
      ∑ n ∈ Ioc (N / 2) N, a n * (((N / n : ℕ) : ℝ) - 2 * ((N / 2 / n : ℕ) : ℝ)) := by
    refine sum_le_sum fun n hn ↦ ?_
    simp only [mem_Ioc] at hn
    have hn0 : 0 < n := by omega
    rw [Nat.div_eq_of_lt hn.1, Nat.cast_zero, mul_zero, sub_zero]
    have : 1 ≤ N / n := (Nat.one_le_div_iff hn0).2 hn.2
    calc a n = a n * 1 := (mul_one _).symm
      _ ≤ a n * ((N / n : ℕ) : ℝ) := mul_le_mul_of_nonneg_left (by exact_mod_cast this) (ha n)
  linarith

/-- `T(x) = ∑_{n ≤ x} a(n) ⌊x/n⌋` in terms of `N = ⌊x⌋` (`⌊x/n⌋ = ⌊N/n⌋`). -/
theorem sum_mul_floor_div_eq (a : ℕ → ℝ) (x : ℝ) :
    ∑ n ∈ Ioc 0 ⌊x⌋₊, a n * (⌊x / n⌋₊ : ℝ) = ∑ n ∈ Ioc 0 ⌊x⌋₊, a n * ((⌊x⌋₊ / n : ℕ) : ℝ) := by
  refine sum_congr rfl fun n _ ↦ ?_
  rw [Nat.floor_div_natCast]

theorem floor_div_two_eq (x : ℝ) : ⌊x / 2⌋₊ = ⌊x⌋₊ / 2 := by
  have := Nat.floor_div_natCast x 2
  simpa using this

/-- **Apostol, Theorem 4.8** (Shapiro's Tauberian theorem). -/
@[kb "apostol1976" "Thm 4.8, p. 85"]
theorem shapiro {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n)
    (hT : ∃ K, ∀ x : ℝ, 1 ≤ x →
      |∑ n ∈ Ioc 0 ⌊x⌋₊, a n * (⌊x / n⌋₊ : ℝ) - x * Real.log x| ≤ K * x) :
    (∃ C, ∀ x : ℝ, 1 ≤ x → |∑ n ∈ Ioc 0 ⌊x⌋₊, a n / n - Real.log x| ≤ C) ∧
    (∃ B > 0, ∀ x : ℝ, 1 ≤ x → ∑ n ∈ Ioc 0 ⌊x⌋₊, a n ≤ B * x) ∧
    (∃ A > 0, ∃ x₀ > 0, ∀ x : ℝ, x₀ ≤ x → A * x ≤ ∑ n ∈ Ioc 0 ⌊x⌋₊, a n) := by
  obtain ⟨K, hK⟩ := hT
  set S : ℝ → ℝ := fun x ↦ ∑ n ∈ Ioc 0 ⌊x⌋₊, a n with hSdef
  set T : ℝ → ℝ := fun x ↦ ∑ n ∈ Ioc 0 ⌊x⌋₊, a n * (⌊x / n⌋₊ : ℝ) with hTdef
  set K' := Real.log 2 + 2 * |K| with hK'
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hK'0 : 0 < K' := by positivity
  -- Step 1: `S(x) - S(x/2) ≤ K' x` for `x ≥ 1`
  have hstep : ∀ x : ℝ, 1 ≤ x → S x - S (x / 2) ≤ K' * x := by
    intro x hx
    have hkey := shapiro_key ha ⌊x⌋₊
    have hTx : T x = ∑ n ∈ Ioc 0 ⌊x⌋₊, a n * ((⌊x⌋₊ / n : ℕ) : ℝ) := sum_mul_floor_div_eq a x
    have hTx2 : T (x / 2) = ∑ n ∈ Ioc 0 (⌊x⌋₊ / 2), a n * ((⌊x⌋₊ / 2 / n : ℕ) : ℝ) := by
      rw [hTdef]; dsimp only; rw [sum_mul_floor_div_eq, floor_div_two_eq]
    have hSx2 : S (x / 2) = ∑ n ∈ Ioc 0 (⌊x⌋₊ / 2), a n := by
      rw [hSdef]; dsimp only; rw [floor_div_two_eq]
    have hle : S x - S (x / 2) ≤ T x - 2 * T (x / 2) := by
      rw [hTx, hTx2, hSx2]; exact hkey
    have h1 := (abs_le.1 (hK x hx)).2
    have hT2nonneg : 0 ≤ T (x / 2) :=
      sum_nonneg fun n _ ↦ mul_nonneg (ha n) (Nat.cast_nonneg _)
    rcases lt_or_ge x 2 with hx2 | hx2
    · -- `T(x/2) ≥ 0` and `log x ≤ log 2`
      have hl : Real.log x ≤ Real.log 2 := Real.log_le_log (by linarith) hx2.le
      have : T x ≤ x * Real.log 2 + |K| * x := by
        have := le_abs_self K
        nlinarith
      nlinarith [abs_nonneg K]
    · have h2 := (abs_le.1 (hK (x / 2) (by linarith))).1
      have hl : Real.log (x / 2) = Real.log x - Real.log 2 :=
        Real.log_div (by linarith) two_ne_zero
      rw [hl] at h2
      have := le_abs_self K
      have := neg_abs_le K
      nlinarith
  -- Step 2: `S(x) ≤ 2 K' x` for all `x ≥ 0`
  have hSbound : ∀ x : ℝ, 0 ≤ x → S x ≤ 2 * K' * x := by
    suffices H : ∀ N : ℕ, ∀ x : ℝ, 0 ≤ x → ⌊x⌋₊ ≤ N → S x ≤ 2 * K' * x from
      fun x hx ↦ H _ x hx le_rfl
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
    intro x hx hxN
    rcases lt_or_ge x 1 with hx1 | hx1
    · have : S x = 0 := by
        rw [hSdef]; dsimp only; rw [Nat.floor_eq_zero.2 hx1]; simp
      rw [this]; positivity
    · have hlt : ⌊x / 2⌋₊ < ⌊x⌋₊ := by
        rw [floor_div_two_eq]
        have : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx1)
        omega
      have := ih ⌊x / 2⌋₊ (lt_of_lt_of_le hlt hxN) (x / 2) (by linarith) le_rfl
      have := hstep x hx1
      linarith
  -- (b)
  have hb : ∃ B > 0, ∀ x : ℝ, 1 ≤ x → S x ≤ B * x :=
    ⟨2 * K', by positivity, fun x hx ↦ hSbound x (by linarith)⟩
  -- (a)
  set C := 2 * K' + |K| with hC
  have ha' : ∀ x : ℝ, 1 ≤ x → |∑ n ∈ Ioc 0 ⌊x⌋₊, a n / n - Real.log x| ≤ C := by
    intro x hx
    have hx0 : 0 < x := by linarith
    -- `x ∑ a(n)/n - T(x) ∈ [0, S(x)]`
    have hdiff : x * ∑ n ∈ Ioc 0 ⌊x⌋₊, a n / n - T x =
        ∑ n ∈ Ioc 0 ⌊x⌋₊, a n * (x / n - ⌊x / n⌋₊) := by
      rw [mul_sum, hTdef]; dsimp only; rw [← sum_sub_distrib]
      exact sum_congr rfl fun n _ ↦ by ring
    have hd0 : 0 ≤ x * ∑ n ∈ Ioc 0 ⌊x⌋₊, a n / n - T x := by
      rw [hdiff]
      refine sum_nonneg fun n hn ↦ mul_nonneg (ha n) ?_
      have := Nat.floor_le (div_nonneg hx0.le (Nat.cast_nonneg (α := ℝ) n))
      linarith
    have hd1 : x * ∑ n ∈ Ioc 0 ⌊x⌋₊, a n / n - T x ≤ S x := by
      rw [hdiff, hSdef]
      refine sum_le_sum fun n hn ↦ ?_
      have := Nat.lt_floor_add_one (x / n)
      calc a n * (x / n - ⌊x / n⌋₊) ≤ a n * 1 :=
            mul_le_mul_of_nonneg_left (by linarith) (ha n)
        _ = a n := mul_one _
    have hS := hSbound x hx0.le
    have hTK := abs_le.1 (hK x hx)
    have habsK := le_abs_self K
    have habsK' := neg_abs_le K
    rw [abs_le]
    constructor
    · -- lower bound
      have : x * (∑ n ∈ Ioc 0 ⌊x⌋₊, a n / n - Real.log x) ≥ x * (-C) := by nlinarith
      exact le_of_mul_le_mul_left (by linarith) hx0
    · have : x * (∑ n ∈ Ioc 0 ⌊x⌋₊, a n / n - Real.log x) ≤ x * C := by nlinarith
      exact le_of_mul_le_mul_left this hx0
  -- (c)
  have hc : ∃ A > 0, ∃ x₀ > 0, ∀ x : ℝ, x₀ ≤ x → A * x ≤ S x := by
    set α := Real.exp (-2 * C - 1) with hα
    have hα0 : 0 < α := Real.exp_pos _
    have hC0 : 0 ≤ C := by positivity
    have hα1 : α ≤ 1 := by rw [hα, Real.exp_le_one_iff]; linarith
    refine ⟨α, hα0, 1 / α, by positivity, fun x hx ↦ ?_⟩
    have hαx : 1 ≤ α * x := by
      rw [div_le_iff₀ hα0] at hx; linarith
    have hx1 : 1 ≤ x := le_trans hαx (by nlinarith)
    have hx0 : 0 < x := by linarith
    have hA1 := abs_le.1 (ha' x hx1)
    have hA2 := abs_le.1 (ha' (α * x) hαx)
    have hlogα : Real.log (α * x) = (-2 * C - 1) + Real.log x := by
      rw [Real.log_mul hα0.ne' hx0.ne', hα, Real.log_exp]
    rw [hlogα] at hA2
    -- `A(x) - A(αx) ≥ 1`
    have hdiffA : 1 ≤ ∑ n ∈ Ioc 0 ⌊x⌋₊, a n / n - ∑ n ∈ Ioc 0 ⌊α * x⌋₊, a n / n := by linarith
    have hfl : ⌊α * x⌋₊ ≤ ⌊x⌋₊ := Nat.floor_le_floor (by nlinarith)
    rw [← sum_Ioc_consecutive _ (Nat.zero_le _) hfl, add_sub_cancel_left] at hdiffA
    -- each term `a(n)/n ≤ a(n)/(αx)`
    have hterm : ∑ n ∈ Ioc ⌊α * x⌋₊ ⌊x⌋₊, a n / n ≤ (∑ n ∈ Ioc 0 ⌊x⌋₊, a n) / (α * x) := by
      rw [sum_div]
      calc ∑ n ∈ Ioc ⌊α * x⌋₊ ⌊x⌋₊, a n / n ≤ ∑ n ∈ Ioc ⌊α * x⌋₊ ⌊x⌋₊, a n / (α * x) := by
            refine sum_le_sum fun n hn ↦ ?_
            have hn := (mem_Ioc.1 hn).1
            have h1 := Nat.lt_floor_add_one (α * x)
            have h2 : (⌊α * x⌋₊ : ℝ) + 1 ≤ n := by exact_mod_cast hn
            exact div_le_div_of_nonneg_left (ha n) (by linarith) (by linarith)
        _ ≤ ∑ n ∈ Ioc 0 ⌊x⌋₊, a n / (α * x) :=
            sum_le_sum_of_subset_of_nonneg (Ioc_subset_Ioc_left (Nat.zero_le _))
              fun n _ _ ↦ div_nonneg (ha n) (by positivity)
    have : 1 ≤ S x / (α * x) := le_trans hdiffA hterm
    rw [le_div_iff₀ (by positivity)] at this
    linarith
  exact ⟨⟨C, ha'⟩, hb, hc⟩

/-! ## Theorem 4.9: `a = Λ` -/

/-- Hypothesis of Shapiro's theorem for `a = Λ` (Theorems 3.12 and 3.15):
`|∑_{n ≤ x} Λ(n) ⌊x/n⌋ - x log x| ≤ 2x`. -/
theorem abs_sum_vonMangoldt_mul_floor_sub_le {x : ℝ} (hx : 1 ≤ x) :
    |∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n * (⌊x / n⌋₊ : ℝ) - x * Real.log x| ≤ 2 * x := by
  rw [sum_vonMangoldt_mul_floor, abs_le]
  have h1 := Real.sum_log_le' hx
  have h2 := Real.le_sum_log' hx
  constructor <;> linarith

/-- **Apostol, Theorem 4.9.** `∑_{n ≤ x} Λ(n)/n = log x + O(1)` for `x ≥ 1`, and there are
`c₁, c₂ > 0` with `ψ(x) ≤ c₁ x` for `x ≥ 1` and `ψ(x) ≥ c₂ x` for all large `x`. -/
@[kb "apostol1976" "Thm 4.9, p. 88"]
theorem apostol_thm_4_9 :
    (∃ C, ∀ x : ℝ, 1 ≤ x → |∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / n - Real.log x| ≤ C) ∧
    (∃ c₁ > 0, ∀ x : ℝ, 1 ≤ x → ψ x ≤ c₁ * x) ∧
    (∃ c₂ > 0, ∃ x₀ > 0, ∀ x : ℝ, x₀ ≤ x → c₂ * x ≤ ψ x) :=
  shapiro (fun _ ↦ vonMangoldt_nonneg) ⟨2, fun _ hx ↦ abs_sum_vonMangoldt_mul_floor_sub_le hx⟩

/-! ## Theorem 4.10: `a = Λ₁` -/

/-- **Apostol, Theorem 4.10.** `∑_{p ≤ x} log p/p = log x + O(1)` for `x ≥ 1`, and there are
`c₁, c₂ > 0` with `ϑ(x) ≤ c₁ x` for `x ≥ 1` and `ϑ(x) ≥ c₂ x` for all large `x`. -/
@[kb "apostol1976" "Thm 4.10, p. 89"]
theorem apostol_thm_4_10 :
    (∃ C, ∀ x : ℝ, 1 ≤ x → |∑ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, Real.log p / p - Real.log x| ≤ C) ∧
    (∃ c₁ > 0, ∀ x : ℝ, 1 ≤ x → θ x ≤ c₁ * x) ∧
    (∃ c₂ > 0, ∃ x₀ > 0, ∀ x : ℝ, x₀ ≤ x → c₂ * x ≤ θ x) := by
  set a : ℕ → ℝ := fun n ↦ if n.Prime then Real.log n else 0 with ha
  have ha0 : ∀ n, 0 ≤ a n := fun n ↦ by
    rw [ha]; dsimp only; split_ifs with h
    · exact Real.log_nonneg (by exact_mod_cast h.one_lt.le)
    · exact le_rfl
  have hfilt : ∀ (g : ℕ → ℝ) (N : ℕ), ∑ n ∈ Ioc 0 N, a n * g n =
      ∑ p ∈ Ioc 0 N with p.Prime, Real.log p * g p := by
    intro g N
    rw [sum_filter]
    exact sum_congr rfl fun n _ ↦ by rw [ha]; dsimp only; split_ifs <;> simp
  obtain ⟨C₀, hC₀⟩ := exists_abs_sum_prime_floor_mul_log_sub_le
  have hT : ∃ K, ∀ x : ℝ, 1 ≤ x →
      |∑ n ∈ Ioc 0 ⌊x⌋₊, a n * (⌊x / n⌋₊ : ℝ) - x * Real.log x| ≤ K * x := by
    refine ⟨max C₀ 1, fun x hx ↦ ?_⟩
    rw [hfilt (fun n ↦ (⌊x / n⌋₊ : ℝ))]
    rcases lt_or_ge x 2 with hx2 | hx2
    · have hN : ⌊x⌋₊ = 1 := by
        rw [Nat.floor_eq_iff (by linarith)]; constructor <;> push_cast <;> linarith
      rw [hN]
      have : (Ioc 0 1).filter Nat.Prime = ∅ := by decide
      rw [this, sum_empty, zero_sub, abs_neg, abs_of_nonneg (mul_nonneg (by linarith)
        (Real.log_nonneg hx))]
      have hl : Real.log x ≤ x - 1 := Real.log_le_sub_one_of_pos (by linarith)
      have : x * Real.log x ≤ x * 1 := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      nlinarith [le_max_right C₀ 1]
    · have := hC₀ x hx2
      have hsw : ∑ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, Real.log p * (⌊x / p⌋₊ : ℝ) =
          ∑ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, (⌊x / p⌋₊ : ℝ) * Real.log p :=
        sum_congr rfl fun _ _ ↦ mul_comm _ _
      rw [hsw]
      exact this.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith))
  obtain ⟨⟨C, hCa⟩, ⟨c₁, hc₁, hb⟩, ⟨c₂, hc₂, x₀, hx₀, hc⟩⟩ := shapiro ha0 hT
  have hθ : ∀ x : ℝ, θ x = ∑ n ∈ Ioc 0 ⌊x⌋₊, a n := fun x ↦ by
    have := hfilt (fun _ ↦ 1) ⌊x⌋₊
    simp only [mul_one] at this
    rw [this]; rfl
  refine ⟨⟨C, fun x hx ↦ ?_⟩, ⟨c₁, hc₁, fun x hx ↦ ?_⟩, ⟨c₂, hc₂, x₀, hx₀, fun x hx ↦ ?_⟩⟩
  · have := hCa x hx
    have e := hfilt (fun n ↦ 1 / (n : ℝ)) ⌊x⌋₊
    simp only [mul_one_div] at e
    rwa [e] at this
  · rw [hθ]; exact hb x hx
  · rw [hθ]; exact hc x hx

/-! ## Theorem 4.11 -/

/-- **Apostol, Theorem 4.11**, first formula: `∑_{n ≤ x} ψ(x/n) = x log x - x + O(log x)`;
explicitly the error is at most `log x + 1` for `x ≥ 1` (at `x = 1` an `O(log x)` bound would force
`0 = -1`, so the book's range needs the `+ 1`). -/
@[kb "apostol1976" "Thm 4.11, p. 89"]
theorem abs_sum_psi_div_sub_le {x : ℝ} (hx : 1 ≤ x) :
    |∑ n ∈ Ioc 0 ⌊x⌋₊, ψ (x / n) - (x * Real.log x - x)| ≤ Real.log x + 1 := by
  have e : ∑ n ∈ Ioc 0 ⌊x⌋₊, ψ (x / n) = ∑ n ∈ Ioc 0 ⌊x⌋₊, Real.log n := by
    rw [← sum_vonMangoldt_mul_floor, sum_mul_floor_div_eq, sum_mul_div_eq_sum_sum]
    refine sum_congr rfl fun n _ ↦ ?_
    rw [Chebyshev.psi, Nat.floor_div_natCast]
  rw [e, abs_le]
  have h1 := Real.sum_log_le hx
  have h2 := Real.le_sum_log hx
  constructor <;> linarith

/-- **Apostol, Theorem 4.11**, second formula: `∑_{n ≤ x} ϑ(x/n) = x log x + O(x)`. -/
@[kb "apostol1976" "Thm 4.11, p. 89"]
theorem exists_abs_sum_theta_div_sub_le :
    ∃ C, ∀ x : ℝ, 2 ≤ x → |∑ n ∈ Ioc 0 ⌊x⌋₊, θ (x / n) - x * Real.log x| ≤ C * x := by
  obtain ⟨C, hC⟩ := exists_abs_sum_prime_floor_mul_log_sub_le
  refine ⟨C, fun x hx ↦ ?_⟩
  convert hC x hx using 3
  set a : ArithmeticFunction ℝ := ⟨fun n ↦ if n.Prime then Real.log n else 0, by simp⟩
  have h := sum_mul_div_eq_sum_sum a ⌊x⌋₊
  have e1 : ∑ n ∈ Ioc 0 ⌊x⌋₊, θ (x / n) = ∑ m ∈ Ioc 0 ⌊x⌋₊, ∑ n ∈ Ioc 0 (⌊x⌋₊ / m), a n := by
    refine sum_congr rfl fun m _ ↦ ?_
    rw [Chebyshev.theta, Nat.floor_div_natCast, sum_filter]
    rfl
  have e2 : ∑ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, (⌊x / p⌋₊ : ℝ) * Real.log p =
      ∑ n ∈ Ioc 0 ⌊x⌋₊, a n * ((⌊x⌋₊ / n : ℕ) : ℝ) := by
    rw [sum_filter]
    refine sum_congr rfl fun n _ ↦ ?_
    rw [← Nat.floor_div_natCast]
    by_cases hp : n.Prime <;> simp [a, hp, mul_comm]
  rw [e1, e2, h]

end NTKB.Apostol
