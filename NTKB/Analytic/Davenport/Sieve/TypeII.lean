/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Davenport.Sieve.Vaughan
import NTKB.Analytic.Davenport.Sieve.DivisorSquare
import NTKB.Analytic.Davenport.Sieve.BarbanDavenportHalberstam
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Complex.Basic

/-!
# Type II sums (Davenport, Chapter 24)

The reduction of the bilinear constant `A` of (D) by Cauchy's inequality (Davenport p. 141):
`|∑_{M < m ≤ 2M} b_m ∑_{V < k ≤ N/m} c_k f(mk)|² ≤ Δ (∑ |b_m|²)(∑ |c_k|²)` whenever every row sum
`∑_k |∑_{M < m ≤ 2M, m ≤ N/j, m ≤ N/k} f(mj) f̄(mk)|` is at most `Δ` (`norm_bilinear_sq_le`).
-/

open Finset ComplexConjugate

namespace NTKB.Davenport

/-- **Davenport, Ch. 24** (Cauchy's inequality for the type II sums): if for every `j`,
`∑_k |∑_{M < m ≤ 2M, mj ≤ N, mk ≤ N} f(mj) conj f(mk)| ≤ Δ` (`j, k` in `(V, N/M]`), then
`|∑_{M < m ≤ 2M} b_m ∑_{V < k, mk ≤ N} c_k f(mk)|² ≤ Δ (∑_m |b_m|²) (∑_k |c_k|²)`. -/
@[kb "davenport1980" "Ch 24, p. 141"]
theorem norm_bilinear_sq_le (f : ℕ → ℂ) (N M V : ℕ) (b c : ℕ → ℂ) {Δ : ℝ}
    (hΔ : ∀ j ∈ Ioc V (N / M), ∑ k ∈ Ioc V (N / M),
      ‖∑ m ∈ (Ioc M (2 * M)).filter (fun m ↦ m * j ≤ N ∧ m * k ≤ N),
        f (m * j) * conj (f (m * k))‖ ≤ Δ) :
    ‖∑ m ∈ Ioc M (2 * M), b m * ∑ k ∈ (Ioc V (N / M)).filter (fun k ↦ m * k ≤ N),
        c k * f (m * k)‖ ^ 2 ≤
      Δ * (∑ m ∈ Ioc M (2 * M), ‖b m‖ ^ 2) * ∑ k ∈ Ioc V (N / M), ‖c k‖ ^ 2 := by
  set I := Ioc M (2 * M)
  set K := Ioc V (N / M)
  set X : ℕ → ℂ := fun m ↦ ∑ k ∈ K.filter (fun k ↦ m * k ≤ N), c k * f (m * k)
  set T : ℕ → ℕ → ℂ := fun j k ↦
    ∑ m ∈ I.filter (fun m ↦ m * j ≤ N ∧ m * k ≤ N), f (m * j) * conj (f (m * k))
  -- Cauchy's inequality over `m`
  have h1 : ‖∑ m ∈ I, b m * X m‖ ^ 2 ≤ (∑ m ∈ I, ‖b m‖ ^ 2) * ∑ m ∈ I, ‖X m‖ ^ 2 := by
    have hcs : (∑ m ∈ I, ‖b m‖ * ‖X m‖) ^ 2 ≤ (∑ m ∈ I, ‖b m‖ ^ 2) * ∑ m ∈ I, ‖X m‖ ^ 2 :=
      sum_mul_sq_le_sq_mul_sq I (fun m ↦ ‖b m‖) fun m ↦ ‖X m‖
    calc ‖∑ m ∈ I, b m * X m‖ ^ 2 ≤ (∑ m ∈ I, ‖b m‖ * ‖X m‖) ^ 2 := by
          gcongr
          exact (norm_sum_le _ _).trans (le_of_eq (sum_congr rfl fun m _ ↦ norm_mul _ _))
      _ ≤ _ := hcs
  -- expanding `∑_m |X_m|²`
  have hX : ∀ m, X m = ∑ k ∈ K, if m * k ≤ N then c k * f (m * k) else 0 := fun m ↦ by
    simp only [X, sum_filter]
  have h2 : ((∑ m ∈ I, ‖X m‖ ^ 2 : ℝ) : ℂ) = ∑ j ∈ K, ∑ k ∈ K, c j * conj (c k) * T j k := by
    push_cast
    simp_rw [← Complex.mul_conj', hX, map_sum, sum_mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun j _ ↦ ?_
    rw [sum_comm]
    refine sum_congr rfl fun k _ ↦ ?_
    simp only [T, mul_sum, sum_filter]
    refine sum_congr rfl fun m _ ↦ ?_
    by_cases hj : m * j ≤ N <;> by_cases hk : m * k ≤ N <;> simp [hj, hk] <;> ring
  have hT : ∀ j k, ‖T k j‖ = ‖T j k‖ := by
    intro j k
    have : T k j = conj (T j k) := by
      simp only [T, map_sum, map_mul, Complex.conj_conj]
      refine sum_congr (filter_congr fun m _ ↦ and_comm) fun m _ ↦ mul_comm _ _
    rw [this, Complex.norm_conj]
  have h3 : ∑ m ∈ I, ‖X m‖ ^ 2 ≤ Δ * ∑ k ∈ K, ‖c k‖ ^ 2 := by
    have hreal : ∑ m ∈ I, ‖X m‖ ^ 2 = ‖∑ j ∈ K, ∑ k ∈ K, c j * conj (c k) * T j k‖ := by
      rw [← h2, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [hreal]
    calc ‖∑ j ∈ K, ∑ k ∈ K, c j * conj (c k) * T j k‖
        ≤ ∑ j ∈ K, ∑ k ∈ K, ‖c j‖ * ‖c k‖ * ‖T j k‖ := by
          refine (norm_sum_le _ _).trans (sum_le_sum fun j _ ↦ (norm_sum_le _ _).trans
            (sum_le_sum fun k _ ↦ ?_))
          rw [norm_mul, norm_mul, Complex.norm_conj]
      _ ≤ ∑ j ∈ K, ∑ k ∈ K, (‖c j‖ ^ 2 / 2 + ‖c k‖ ^ 2 / 2) * ‖T j k‖ := by
          gcongr with j _ k _
          nlinarith [sq_nonneg (‖c j‖ - ‖c k‖)]
      _ = ∑ j ∈ K, ‖c j‖ ^ 2 * ∑ k ∈ K, ‖T j k‖ := by
          simp only [add_mul, sum_add_distrib]
          have : ∑ j ∈ K, ∑ k ∈ K, ‖c k‖ ^ 2 / 2 * ‖T j k‖ =
              ∑ j ∈ K, ∑ k ∈ K, ‖c j‖ ^ 2 / 2 * ‖T j k‖ := by
            rw [sum_comm]
            exact sum_congr rfl fun j _ ↦ sum_congr rfl fun k _ ↦ by rw [hT]
          rw [this, ← two_mul, mul_sum]
          refine sum_congr rfl fun j _ ↦ ?_
          rw [mul_sum, mul_sum]
          exact sum_congr rfl fun k _ ↦ by ring
      _ ≤ ∑ j ∈ K, ‖c j‖ ^ 2 * Δ := by
          gcongr with j hj
          exact hΔ j hj
      _ = Δ * ∑ k ∈ K, ‖c k‖ ^ 2 := by rw [← sum_mul, mul_comm]
  calc ‖∑ m ∈ I, b m * X m‖ ^ 2 ≤ (∑ m ∈ I, ‖b m‖ ^ 2) * ∑ m ∈ I, ‖X m‖ ^ 2 := h1
    _ ≤ (∑ m ∈ I, ‖b m‖ ^ 2) * (Δ * ∑ k ∈ K, ‖c k‖ ^ 2) := by gcongr
    _ = _ := by ring

open ArithmeticFunction in
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta in
/-- `|∑_{d ∣ k, d ≤ V} μ(d)| ≤ d(k)`. -/
lemma abs_sum_moebius_le_card_divisors (k V : ℕ) :
    |∑ d ∈ k.divisors.filter (· ≤ V), (μ d : ℝ)| ≤ k.divisors.card := by
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ d ∈ k.divisors.filter (· ≤ V), |(μ d : ℝ)| ≤ ∑ d ∈ k.divisors.filter (· ≤ V), (1 : ℝ) :=
        sum_le_sum fun d _ ↦ by exact_mod_cast abs_moebius_le_one
    _ ≤ ∑ d ∈ k.divisors, (1 : ℝ) :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ ↦ zero_le_one
    _ = k.divisors.card := by simp

open ArithmeticFunction in
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta in
/-- **Davenport, Ch. 24, (E)**: if the bilinear inequality (D) holds with constant `A` for every
`U ≤ M ≤ N/V`, then `|S₄| ≪ A N^{1/2} (log N)³`. -/
@[kb "davenport1980" "Ch 24, p. 141, (E)"]
theorem norm_S₄_le : ∃ C : ℝ, 0 < C ∧ ∀ (f : ℕ → ℂ) (N U V : ℕ) (A : ℝ), 2 ≤ N → 1 ≤ U →
    1 ≤ V → 0 ≤ A →
    (∀ M : ℕ, U ≤ M → M ≤ N / V → ∀ b c : ℕ → ℂ,
      ‖∑ m ∈ Ioc M (2 * M), b m * ∑ k ∈ (Ioc V (N / M)).filter (fun k ↦ m * k ≤ N),
          c k * f (m * k)‖ ≤
        A * √(∑ m ∈ Ioc M (2 * M), ‖b m‖ ^ 2) * √(∑ k ∈ Ioc V (N / M), ‖c k‖ ^ 2)) →
    ‖∑ n ∈ Icc 1 N, f n * (((Λ - truncate Λ U) *
        (1 - (ζ : ArithmeticFunction ℝ) * truncate (μ : ArithmeticFunction ℝ) V)) n : ℂ)‖ ≤
      C * A * √N * Real.log N ^ 3 := by
  obtain ⟨Cd, hCd, hdiv⟩ := sum_card_divisors_sq_le
  set Cl : ℝ := Real.log 4 + 4
  set C₁ : ℝ := √(2 * Cl * 2 * Cd * 27) with hC₁
  refine ⟨4 * C₁ + 1, by positivity, ?_⟩
  intro f N U V A hN hU hV hA hD
  set L := Real.log N with hLdef
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hL : (1 : ℝ) / 2 ≤ L := by
    have h2 : Real.log 2 ≤ L := Real.log_le_log (by norm_num) (by exact_mod_cast hN)
    have := Real.log_two_gt_d9; linarith
  set c : ℕ → ℂ := fun k ↦ ((∑ d ∈ k.divisors.filter (· ≤ V), (μ d : ℝ) : ℝ) : ℂ) with hcdef
  rw [S₄_eq f N U V hV, norm_neg]
  set jf : ℕ → ℕ := fun m ↦ Nat.log 2 ((m - 1) / U) with hjf
  have hmaps : ∀ m ∈ Ioc U N, jf m ∈ range (Nat.log 2 N + 1) := by
    intro m hm
    simp only [mem_range, hjf, Nat.lt_succ_iff]
    exact Nat.log_mono_right ((Nat.div_le_self _ _).trans (by simp only [mem_Ioc] at hm; omega))
  rw [← sum_fiberwise_of_maps_to hmaps]
  refine (norm_sum_le _ _).trans ?_
  -- one dyadic block
  have hblock : ∀ j ∈ range (Nat.log 2 N + 1),
      ‖∑ m ∈ (Ioc U N).filter (fun m ↦ jf m = j), (Λ m : ℂ) *
        ∑ k ∈ Ioc V (N / m), c k * f (m * k)‖ ≤ C₁ * A * √N * L ^ 2 := by
    intro j _
    set M := U * 2 ^ j with hM
    have hUM : U ≤ M := Nat.le_mul_of_pos_right U (by positivity)
    have hM0 : 0 < M := by omega
    -- membership in the block
    have e1 : 2 ^ j * U = M := by rw [hM, mul_comm]
    have e2 : 2 ^ (j + 1) * U = 2 * M := by rw [hM, pow_succ]; ring
    have hmem : ∀ m, m ∈ (Ioc U N).filter (fun m ↦ jf m = j) ↔ m ∈ Ioc M (2 * M) ∧ m ≤ N := by
      intro m
      simp only [mem_filter, mem_Ioc, hjf]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        have hpos : (m - 1) / U ≠ 0 := by
          have : 1 ≤ (m - 1) / U := (Nat.one_le_div_iff (by omega)).2 (by omega)
          omega
        have := (Nat.log_eq_iff (Or.inr ⟨by norm_num, hpos⟩)).1 h3
        rw [Nat.le_div_iff_mul_le (by omega), Nat.div_lt_iff_lt_mul (by omega), e1, e2] at this
        refine ⟨⟨by omega, by omega⟩, h2⟩
      · rintro ⟨⟨h1, h2⟩, h3⟩
        refine ⟨⟨by omega, h3⟩, ?_⟩
        have hpos : (m - 1) / U ≠ 0 := by
          have : 1 ≤ (m - 1) / U := (Nat.one_le_div_iff (by omega)).2 (by omega)
          omega
        rw [Nat.log_eq_iff (Or.inr ⟨by norm_num, hpos⟩), Nat.le_div_iff_mul_le (by omega),
          Nat.div_lt_iff_lt_mul (by omega), e1, e2]
        omega
    set X' : ℕ → ℂ := fun m ↦ ∑ k ∈ (Ioc V (N / M)).filter (fun k ↦ m * k ≤ N), c k * f (m * k)
    have hX : ∀ m, M < m → m ≤ N → ∑ k ∈ Ioc V (N / m), c k * f (m * k) = X' m := by
      intro m hm hmN
      refine sum_congr ?_ fun _ _ ↦ rfl
      ext k
      simp only [mem_filter, mem_Ioc]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨⟨h1, h2.trans (Nat.div_le_div_left hm.le hM0)⟩, ?_⟩
        calc m * k ≤ m * (N / m) := Nat.mul_le_mul_left m h2
          _ ≤ N := Nat.mul_div_le N m
      · rintro ⟨⟨h1, -⟩, h3⟩
        exact ⟨h1, (Nat.le_div_iff_mul_le (by omega)).2 (by rw [mul_comm]; exact h3)⟩
    have hX0 : ∀ m, N < m → X' m = 0 := by
      intro m hm
      refine sum_eq_zero fun k hk ↦ ?_
      simp only [mem_filter, mem_Ioc] at hk
      nlinarith [hk.1.1]
    have hblk : ∑ m ∈ (Ioc U N).filter (fun m ↦ jf m = j), (Λ m : ℂ) *
        ∑ k ∈ Ioc V (N / m), c k * f (m * k) = ∑ m ∈ Ioc M (2 * M), (Λ m : ℂ) * X' m := by
      have hsub : (Ioc U N).filter (fun m ↦ jf m = j) ⊆ Ioc M (2 * M) := fun m hm ↦
        ((hmem m).1 hm).1
      rw [← sum_subset hsub (fun m hm hm' ↦ by
        have : N < m := by
          by_contra h; exact hm' ((hmem m).2 ⟨hm, by omega⟩)
        rw [hX0 m this, mul_zero])]
      refine sum_congr rfl fun m hm ↦ ?_
      have := (hmem m).1 hm
      rw [hX m (mem_Ioc.1 this.1).1 this.2]
    rw [hblk]
    rcases le_or_gt M (N / V) with hMV | hMV
    swap
    · -- the block is empty
      have : ∀ m ∈ Ioc M (2 * M), X' m = 0 := by
        intro m hm
        refine sum_eq_zero fun k hk ↦ ?_
        simp only [mem_filter, mem_Ioc] at hk hm
        exfalso
        have h1 : N < m * V := by
          have := (Nat.div_lt_iff_lt_mul (by omega)).1 (lt_of_lt_of_le hMV hm.1.le)
          linarith
        nlinarith [hk.1.1]
      rw [sum_eq_zero fun m hm ↦ by rw [this m hm, mul_zero], norm_zero]
      positivity
    have hDM := hD M hUM hMV (fun m ↦ (Λ m : ℂ)) c
    refine hDM.trans ?_
    -- the two mean squares
    have hNM : 1 ≤ N / M := (Nat.one_le_div_iff hM0).2 ((hMV.trans (Nat.div_le_self N V)))
    have hb : ∑ m ∈ Ioc M (2 * M), ‖(Λ m : ℂ)‖ ^ 2 ≤ Cl * (2 * M) * (2 * L) := by
      have h1 : ∑ m ∈ Ioc M (2 * M), ‖(Λ m : ℂ)‖ ^ 2 ≤ ∑ m ∈ Icc 1 ⌊((2 * M : ℕ) : ℝ)⌋₊, Λ m ^ 2 := by
        rw [Nat.floor_natCast]
        refine sum_le_sum_of_subset_of_nonneg (fun m hm ↦ ?_) (fun _ _ _ ↦ sq_nonneg _) |>.trans'
          (le_of_eq (sum_congr rfl fun m _ ↦ by rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]))
        simp only [mem_Ioc, mem_Icc] at hm ⊢; omega
      refine h1.trans ((sum_vonMangoldt_sq_le (by exact_mod_cast (by omega : 1 ≤ 2 * M))).trans ?_)
      push_cast
      have h2M : (2 * (M : ℝ)) ≤ (N : ℝ) ^ 2 := by
        have h1 : (M : ℝ) ≤ N := by exact_mod_cast hMV.trans (Nat.div_le_self N V)
        have h2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
        calc 2 * (M : ℝ) ≤ 2 * N := by linarith
          _ ≤ N * N := by nlinarith
          _ = _ := by ring
      have hlog : Real.log (2 * M) ≤ 2 * L := by
        have e : Real.log ((N : ℝ) ^ 2) = 2 * L := by rw [Real.log_pow]; push_cast; ring
        rw [← e]
        exact Real.log_le_log (by positivity) h2M
      gcongr
    have hc : ∑ k ∈ Ioc V (N / M), ‖c k‖ ^ 2 ≤ Cd * (N / M : ℕ) * (3 * L) ^ 3 := by
      have h1 : ∑ k ∈ Ioc V (N / M), ‖c k‖ ^ 2 ≤ ∑ k ∈ Icc 1 (N / M), (k.divisors.card : ℝ) ^ 2 := by
        refine (sum_le_sum fun k _ ↦ ?_).trans (sum_le_sum_of_subset_of_nonneg (fun k hk ↦ ?_)
          (fun _ _ _ ↦ sq_nonneg _))
        · rw [hcdef, Complex.norm_real, Real.norm_eq_abs, sq_abs]
          have := abs_sum_moebius_le_card_divisors k V
          have h0 := abs_nonneg (∑ d ∈ k.divisors.filter (· ≤ V), (μ d : ℝ))
          nlinarith [sq_abs (∑ d ∈ k.divisors.filter (· ≤ V), (μ d : ℝ))]
        · simp only [mem_Ioc, mem_Icc] at hk ⊢; omega
      refine h1.trans ((hdiv _ hNM).trans ?_)
      have hlog : 1 + Real.log (N / M : ℕ) ≤ 3 * L := by
        have : Real.log (N / M : ℕ) ≤ L :=
          Real.log_le_log (by exact_mod_cast (by omega : 0 < N / M))
            (by exact_mod_cast Nat.div_le_self N M)
        linarith
      gcongr
    have hMN : (M : ℝ) * (N / M : ℕ) ≤ N := by exact_mod_cast Nat.mul_div_le N M
    have hprod : (∑ m ∈ Ioc M (2 * M), ‖(Λ m : ℂ)‖ ^ 2) * ∑ k ∈ Ioc V (N / M), ‖c k‖ ^ 2 ≤
        C₁ ^ 2 * N * L ^ 4 := by
      rw [hC₁, Real.sq_sqrt (by positivity)]
      calc _ ≤ (Cl * (2 * M) * (2 * L)) * (Cd * (N / M : ℕ) * (3 * L) ^ 3) := by
            gcongr
        _ = 2 * Cl * 2 * Cd * 27 * ((M : ℝ) * (N / M : ℕ)) * (2 * L ^ 4) / 2 := by ring
        _ ≤ 2 * Cl * 2 * Cd * 27 * N * (2 * L ^ 4) / 2 := by gcongr
        _ = _ := by ring
    rw [mul_assoc A, ← Real.sqrt_mul (by positivity)]
    calc A * √((∑ m ∈ Ioc M (2 * M), ‖(Λ m : ℂ)‖ ^ 2) * ∑ k ∈ Ioc V (N / M), ‖c k‖ ^ 2)
        ≤ A * √(C₁ ^ 2 * N * L ^ 4) := by gcongr
      _ = C₁ * A * √N * L ^ 2 := by
        rw [show C₁ ^ 2 * N * L ^ 4 = (C₁ * L ^ 2) ^ 2 * N by ring, Real.sqrt_mul (by positivity),
          Real.sqrt_sq (by positivity)]
        ring
  refine (sum_le_sum hblock).trans ?_
  rw [sum_const, card_range, nsmul_eq_mul]
  have hlog2 : ((Nat.log 2 N : ℕ) : ℝ) ≤ 2 * L := by
    have h1 : (2 : ℝ) ^ (Nat.log 2 N) ≤ N := by exact_mod_cast Nat.pow_log_le_self 2 (by omega)
    have h2 : (Nat.log 2 N : ℝ) * Real.log 2 ≤ L := by
      rw [← Real.log_pow]; exact Real.log_le_log (by positivity) h1
    have := Real.log_two_gt_d9
    nlinarith
  have hcnt : ((Nat.log 2 N + 1 : ℕ) : ℝ) ≤ 4 * L := by push_cast; linarith
  calc ((Nat.log 2 N + 1 : ℕ) : ℝ) * (C₁ * A * √N * L ^ 2) ≤ 4 * L * (C₁ * A * √N * L ^ 2) := by
        gcongr
    _ = 4 * C₁ * A * √N * L ^ 3 := by ring
    _ ≤ (4 * C₁ + 1) * A * √N * L ^ 3 := by
        have : 0 ≤ A * √N * L ^ 3 := by have : 0 ≤ L := by linarith
                                        positivity
        nlinarith

open ArithmeticFunction in
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta Chebyshev in
/-- **Davenport, Ch. 24, (F)** (the Vinogradov–Vaughan estimate): let `|f(n)| ≤ 1`, `U, V ≥ 1`,
`UV ≤ N`, `N ≥ 2`. Suppose `B_t` bounds every tail `|∑_{w ≤ r ≤ N/t} f(rt)|` (`t ≤ UV`) and `Δ`
bounds every row sum `∑_{V < k ≤ N/M} |∑_{M < m ≤ 2M, mj ≤ N, mk ≤ N} f(mj) f̄(mk)|`
(`U ≤ M ≤ N/V`, `V < j ≤ N/M`). Then
`|∑_{n ≤ N} f(n) Λ(n)| ≪ U + (log N) ∑_{t ≤ UV} B_t + N^{1/2} (log N)³ Δ^{1/2}`. -/
@[kb "davenport1980" "Ch 24, p. 142, (F)"]
theorem norm_sum_mul_vonMangoldt_le : ∃ C : ℝ, 0 < C ∧ ∀ (f : ℕ → ℂ) (N U V : ℕ)
    (B : ℕ → ℝ) (Δ : ℝ), (∀ n, ‖f n‖ ≤ 1) → 2 ≤ N → 1 ≤ U → 1 ≤ V → U * V ≤ N →
    (∀ t, 0 ≤ B t) → 0 ≤ Δ →
    (∀ t ∈ Icc 1 (U * V), ∀ w ∈ Icc 1 (N / t), ‖∑ h ∈ Icc w (N / t), f (t * h)‖ ≤ B t) →
    (∀ M : ℕ, U ≤ M → M ≤ N / V → ∀ j ∈ Ioc V (N / M), ∑ k ∈ Ioc V (N / M),
      ‖∑ m ∈ (Ioc M (2 * M)).filter (fun m ↦ m * j ≤ N ∧ m * k ≤ N),
        f (m * j) * conj (f (m * k))‖ ≤ Δ) →
    ‖∑ n ∈ Icc 1 N, f n * (Λ n : ℂ)‖ ≤
      C * (U + Real.log N * ∑ t ∈ Icc 1 (U * V), B t + √N * Real.log N ^ 3 * √Δ) := by
  obtain ⟨C₄, hC₄, h4⟩ := norm_S₄_le
  refine ⟨C₄ + Real.log 4 + 6, by positivity, ?_⟩
  intro f N U V B Δ hf hN hU hV hUV hB0 hΔ0 hB hΔ
  have hL : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  have hsumB : 0 ≤ ∑ t ∈ Icc 1 (U * V), B t := sum_nonneg fun t _ ↦ hB0 t
  rw [sum_mul_vonMangoldt_eq f N U V]
  -- S₁
  have h1 : ‖∑ n ∈ Icc 1 N, f n * (truncate Λ U n : ℂ)‖ ≤ (Real.log 4 + 4) * U := by
    refine (norm_sum_le _ _).trans ?_
    have : ∀ n ∈ Icc 1 N, ‖f n * (truncate Λ U n : ℂ)‖ ≤ if n ≤ U then Λ n else 0 := by
      intro n _
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, truncate_apply]
      split_ifs
      · rw [abs_of_nonneg vonMangoldt_nonneg]
        exact mul_le_of_le_one_left vonMangoldt_nonneg (hf n)
      · simp
    refine (sum_le_sum this).trans ?_
    rw [← sum_filter]
    have hsub : (Icc 1 N).filter (· ≤ U) ⊆ Ioc 0 ⌊(U : ℝ)⌋₊ := by
      intro n hn; rw [Nat.floor_natCast]; simp only [mem_filter, mem_Icc, mem_Ioc] at hn ⊢; omega
    refine (sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ ↦ vonMangoldt_nonneg).trans ?_
    exact Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg U)
  -- S₂
  have h2 := norm_S₂_le f N U V
  have h2' : Real.log (U * V) * ∑ t ∈ Icc 1 (U * V), ‖∑ r ∈ Icc 1 (N / t), f (t * r)‖ ≤
      Real.log N * ∑ t ∈ Icc 1 (U * V), B t := by
    have hlog : Real.log (U * V) ≤ Real.log N := by
      apply Real.log_le_log (by positivity); exact_mod_cast hUV
    have hlog0 : 0 ≤ Real.log (U * V) := by
      have : (1 : ℝ) ≤ U * V := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (by positivity)
      exact Real.log_nonneg this
    calc _ ≤ Real.log (U * V) * ∑ t ∈ Icc 1 (U * V), B t := by
          gcongr with t ht
          rcases Nat.eq_zero_or_pos (N / t) with h0 | h0
          · rw [h0]; simpa using hB0 t
          · exact hB t ht 1 (by simp only [mem_Icc]; omega)
      _ ≤ _ := by gcongr
  -- S₃
  have h3 := norm_S₃_le f N V B hB0 (fun d hd w hw ↦ hB d (by
    simp only [mem_Icc] at hd ⊢; constructor
    · exact hd.1
    · exact hd.2.trans (Nat.le_mul_of_pos_left V hU)) w hw)
  have h3' : Real.log N * ∑ d ∈ Icc 1 V, B d ≤ Real.log N * ∑ t ∈ Icc 1 (U * V), B t := by
    gcongr
    all_goals first
      | exact fun t _ _ ↦ hB0 t
      | exact Nat.le_mul_of_pos_left V hU
  -- S₄
  have hD : ∀ M : ℕ, U ≤ M → M ≤ N / V → ∀ b c : ℕ → ℂ,
      ‖∑ m ∈ Ioc M (2 * M), b m * ∑ k ∈ (Ioc V (N / M)).filter (fun k ↦ m * k ≤ N),
          c k * f (m * k)‖ ≤
        √Δ * √(∑ m ∈ Ioc M (2 * M), ‖b m‖ ^ 2) * √(∑ k ∈ Ioc V (N / M), ‖c k‖ ^ 2) := by
    intro M hM1 hM2 b c
    have := norm_bilinear_sq_le f N M V b c (hΔ M hM1 hM2)
    rw [← Real.sqrt_mul hΔ0, ← Real.sqrt_mul (by positivity)]
    exact Real.le_sqrt_of_sq_le this
  have h4' := h4 f N U V √Δ hN hU hV (Real.sqrt_nonneg _) hD
  -- assembly
  refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add h1 (h2.trans h2'))) (h3.trans h3'))) h4') |>.trans ?_
  have hU0 : (0 : ℝ) ≤ U := Nat.cast_nonneg U
  have hX : 0 ≤ Real.log N * ∑ t ∈ Icc 1 (U * V), B t := mul_nonneg hL hsumB
  have hY : 0 ≤ √N * Real.log N ^ 3 * √Δ := by positivity
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  nlinarith

end NTKB.Davenport
