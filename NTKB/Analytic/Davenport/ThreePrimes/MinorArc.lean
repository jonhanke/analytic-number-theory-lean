/- Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license. -/
import NTKB.Analytic.Davenport.ThreePrimes.Circle
import NTKB.Analytic.Davenport.Sieve.Vinogradov
import Mathlib.NumberTheory.DiophantineApproximation.Basic

/-!
# `S(α)` on the minor arcs (Davenport, Chapter 26, p. 150)

**26-19, 26-20**: with `P = (log N)^B` and `Q = N (log N)^{-B}`, if `|α - a/q| > 1/Q` for every
`q ≤ P` and every integer `a`, then Dirichlet's theorem (`Real.exists_rat_abs_sub_le_and_den_le`)
gives `a/q` with `P < q ≤ Q` and `|α - a/q| ≤ 1/(qQ) ≤ q⁻²`, and Vinogradov's estimate of
Chapter 25 (`norm_sum_vonMangoldt_exp_le`) gives `S(α) ≪ N (log N)^{4 - B/2}`
(`norm_primeExpSum_minor_le`).
-/

open Finset Real
open scoped ArithmeticFunction.vonMangoldt

namespace NTKB.Davenport

/-- Growth of `(log N)^(B/2)` against `N^(1/5)`. -/
lemma log_rpow_le_const_mul (B : ℝ) (hB : 0 < B) :
    ∃ K : ℝ, 0 < K ∧ ∀ N : ℕ, 2 ≤ N →
      Real.log N ^ (B / 2) ≤ K * (N : ℝ) ^ ((1 : ℝ) / 5) := by
  set ε : ℝ := 2 / (5 * B) with hε
  have hε0 : 0 < ε := by positivity
  refine ⟨(ε ^ (B / 2))⁻¹, by positivity, fun N hN => ?_⟩
  have hN0 : (0 : ℝ) ≤ N := by positivity
  have h1 : Real.log N ≤ (N : ℝ) ^ ε / ε := Real.log_le_rpow_div hN0 hε0
  have hL : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))
  calc Real.log N ^ (B / 2) ≤ ((N : ℝ) ^ ε / ε) ^ (B / 2) :=
        Real.rpow_le_rpow hL h1 (by positivity)
    _ = (ε ^ (B / 2))⁻¹ * (N : ℝ) ^ ((1 : ℝ) / 5) := by
        rw [Real.div_rpow (by positivity) hε0.le, ← Real.rpow_mul hN0, div_eq_inv_mul]
        congr 2
        rw [hε]; field_simp

/-- **Davenport, Ch. 26, p. 150 (row 26-20)**: for every `B > 0` there is `C` such that for
`N ≥ 2`, if `|α - a/q| > (log N)^B / N` for all `1 ≤ q ≤ (log N)^B` and all integers `a`, then
`|S(α)| ≤ C N (log N)^{4 - B/2}`. -/
@[kb "davenport1980" "Ch 26, p. 150"]
theorem norm_primeExpSum_minor_le (B : ℝ) (hB : 0 < B) :
    ∃ C > 0, ∀ N : ℕ, 2 ≤ N → ∀ α : ℝ,
      (∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.log N ^ B → ∀ a : ℤ,
        Real.log N ^ B / N < |α - a / q|) →
      ‖primeExpSum N α‖ ≤ C * N * Real.log N ^ (4 - B / 2) := by
  obtain ⟨C, hC, hV⟩ := norm_sum_vonMangoldt_exp_le
  obtain ⟨K, hK, hKN⟩ := log_rpow_le_const_mul B hB
  refine ⟨C * (2 + K), by positivity, fun N hN α hα => ?_⟩
  have hN1 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hL : 0 < Real.log N := Real.log_pos (by linarith)
  set L := Real.log N with hLdef
  set s := L ^ (B / 2) with hsdef
  have hs : 0 < s := Real.rpow_pos_of_pos hL _
  have hss : s * s = L ^ B := by
    rw [hsdef, ← Real.rpow_add hL]; congr 1; ring
  have hLB : 0 < L ^ B := Real.rpow_pos_of_pos hL _
  have hKs := hKN N hN
  -- Dirichlet
  have hQ : 1 ≤ (N : ℝ) / L ^ B := by
    by_contra hlt
    push Not at hlt
    have hlt' : (N : ℝ) < L ^ B := by
      rwa [div_lt_one hLB] at hlt
    have := hα 1 le_rfl (by simp; linarith) (round α)
    have h2 : |α - (round α : ℤ) / ((1 : ℕ) : ℝ)| ≤ 1 / 2 := by
      simpa using abs_sub_round α
    have h3 : 1 < L ^ B / N := by rw [lt_div_iff₀ hN0]; linarith
    linarith
  set Q := (N : ℝ) / L ^ B with hQdef
  have hn : 1 ≤ ⌊Q⌋₊ := Nat.le_floor (by simpa using hQ)
  obtain ⟨r, hr1, hr2⟩ := Real.exists_rat_abs_sub_le_and_den_le α (n := ⌊Q⌋₊) hn
  set q := r.den with hqdef
  set a := r.num with hadef
  have hq1 : 1 ≤ q := r.den_pos
  have hqQ : (q : ℝ) ≤ Q := le_trans (by exact_mod_cast hr2) (Nat.floor_le (by linarith))
  have hq1' : (1 : ℝ) ≤ q := by exact_mod_cast hq1
  have hrq : (r : ℝ) = a / q := by rw [Rat.cast_def]
  have hfl : Q < (⌊Q⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one Q
  have hQpos : 0 < Q := by linarith
  have hαq : |α - a / q| < L ^ B / N := by
    rw [← hrq]
    refine lt_of_le_of_lt hr1 ?_
    have : L ^ B / N = 1 / Q := by rw [hQdef]; field_simp
    rw [this]
    have hqpos : (0 : ℝ) < q := by linarith
    calc 1 / ((((⌊Q⌋₊ : ℕ) : ℝ) + 1) * q) ≤ 1 / (((⌊Q⌋₊ : ℕ) : ℝ) + 1) :=
          one_div_le_one_div_of_le (by positivity) (le_mul_of_one_le_right (by positivity) hq1')
      _ < 1 / Q := one_div_lt_one_div_of_lt hQpos hfl
  have hα2 : |α - a / q| ≤ 1 / (q : ℝ) ^ 2 := by
    rw [← hrq]
    refine hr1.trans ?_
    have hqn : (q : ℝ) ≤ ⌊Q⌋₊ := by exact_mod_cast hr2
    have hqpos : (0 : ℝ) < q := by linarith
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith
  have hqP : L ^ B < q := by
    by_contra hle
    push Not at hle
    have := hα q hq1 hle a
    linarith
  have hcop : IsCoprime a (q : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    exact r.reduced
  have hVN := hV α a q hq1 hcop hα2 N hN
  have hsq : s < √q := by
    rw [← Real.sqrt_mul_self hs.le]; exact Real.sqrt_lt_sqrt (by positivity) (by linarith)
  have hsqpos : 0 < √q := by linarith
  have e1 : (N : ℝ) / √q ≤ N / s := div_le_div_of_nonneg_left hN0.le hs hsq.le
  have e2 : √N * √q ≤ N / s := by
    rw [le_div_iff₀ hs]
    have h1 : q * (s * s) ≤ N := by
      have : (q : ℝ) * L ^ B ≤ Q * L ^ B := mul_le_mul_of_nonneg_right hqQ hLB.le
      rw [hss]
      calc (q : ℝ) * L ^ B ≤ Q * L ^ B := this
        _ = N := by rw [hQdef]; field_simp
    have h2 : √q * s ≤ √N := by
      rw [← Real.sqrt_mul_self hs.le, ← Real.sqrt_mul (by positivity)]
      exact Real.sqrt_le_sqrt (by linarith)
    calc √N * √q * s = √N * (√q * s) := by ring
      _ ≤ √N * √N := mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg _)
      _ = N := Real.mul_self_sqrt hN0.le
  have e3 : (N : ℝ) ^ ((4 : ℝ) / 5) ≤ K * N / s := by
    rw [le_div_iff₀ hs]
    have hp : (N : ℝ) ^ ((4 : ℝ) / 5) * (N : ℝ) ^ ((1 : ℝ) / 5) = N := by
      rw [← Real.rpow_add hN0]; norm_num
    have hp0 : 0 ≤ (N : ℝ) ^ ((4 : ℝ) / 5) := by positivity
    calc (N : ℝ) ^ ((4 : ℝ) / 5) * s ≤ (N : ℝ) ^ ((4 : ℝ) / 5) * (K * (N : ℝ) ^ ((1 : ℝ) / 5)) :=
          mul_le_mul_of_nonneg_left hKs hp0
      _ = K * ((N : ℝ) ^ ((4 : ℝ) / 5) * (N : ℝ) ^ ((1 : ℝ) / 5)) := by ring
      _ = K * N := by rw [hp]
  have hL4 : L ^ (4 - B / 2) = L ^ 4 / s := by
    rw [Real.rpow_sub hL]
    have : L ^ (4 : ℝ) = L ^ 4 := by exact_mod_cast Real.rpow_natCast L 4
    rw [this]
  have hL4pos : 0 ≤ L ^ 4 := by positivity
  have hprim : ‖primeExpSum N α‖ ≤ C * ((N : ℝ) / √q + (N : ℝ) ^ ((4 : ℝ) / 5) + √N * √q) * L ^ 4 :=
    hVN
  refine hprim.trans ?_
  rw [hL4]
  have : C * ((N : ℝ) / √q + (N : ℝ) ^ ((4 : ℝ) / 5) + √N * √q) * L ^ 4 ≤
      C * (N / s + K * N / s + N / s) * L ^ 4 := by
    gcongr
  refine this.trans (le_of_eq ?_)
  field_simp
  ring

end NTKB.Davenport
