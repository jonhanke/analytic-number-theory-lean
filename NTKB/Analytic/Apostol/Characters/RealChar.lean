/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Apostol.Characters.PartialSums
import NTKB.Analytic.Apostol.Averages.PrimeFloorSum
import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# Divisor sums of real characters; `∑_{n ≤ x} 1/√n` (Apostol, Theorems 6.19 and 3.2(b))

* Theorem 6.19: for a real-valued character `χ` mod `k` (`χ.IsQuadratic`: values in `{0, ±1}`),
  `A(n) = ∑_{d ∣ n} χ(d)` satisfies `A(n) ≥ 0`, and `A(n) ≥ 1` if `n` is a square.
* Theorem 3.2(b) for `s = 1/2`: `∑_{n ≤ x} 1/√n = 2√x + A + O(1/√x)` for a constant `A`
  (Apostol identifies `A = ζ(1/2)`; only the existence of the constant is used in Theorem 6.20).
-/

open Finset ArithmeticFunction Filter Topology
open scoped ArithmeticFunction.zeta

namespace NTKB.Apostol

variable {k : ℕ} [NeZero k]

/-- For a quadratic (real-valued) character, the values are real. -/
theorem IsQuadratic.apply_eq_re {χ : DirichletCharacter ℂ k} (hχ : χ.IsQuadratic) (a : ZMod k) :
    χ a = ((χ a).re : ℂ) := by
  rcases hχ a with h | h | h <;> simp [h]

/-- The real part of a real character on `ℕ`, as an arithmetic function (`0` at `0`). -/
noncomputable def charRe (χ : DirichletCharacter ℂ k) : ArithmeticFunction ℝ :=
  ⟨fun n ↦ if n = 0 then 0 else (χ n).re, by simp⟩

theorem charRe_apply {χ : DirichletCharacter ℂ k} {n : ℕ} (hn : n ≠ 0) :
    charRe χ n = (χ n).re := by simp [charRe, hn]

theorem charRe_mul {χ : DirichletCharacter ℂ k} (hχ : χ.IsQuadratic) (m n : ℕ) :
    charRe χ (m * n) = charRe χ m * charRe χ n := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp [charRe]
  rcases eq_or_ne n 0 with rfl | hn
  · simp [charRe]
  rw [charRe_apply (mul_ne_zero hm hn), charRe_apply hm, charRe_apply hn, Nat.cast_mul, map_mul,
    IsQuadratic.apply_eq_re hχ (m : ZMod k), IsQuadratic.apply_eq_re hχ (n : ZMod k)]
  simp

theorem isMultiplicative_charRe {χ : DirichletCharacter ℂ k} (hχ : χ.IsQuadratic) :
    (charRe χ).IsMultiplicative :=
  ⟨by simp [charRe], fun {m n} _ ↦ charRe_mul hχ m n⟩

theorem charRe_pow {χ : DirichletCharacter ℂ k} (hχ : χ.IsQuadratic) (p j : ℕ) :
    charRe χ (p ^ j) = charRe χ p ^ j := by
  induction j with
  | zero => simp [charRe]
  | succ j ih => rw [pow_succ, charRe_mul hχ, ih, pow_succ]

theorem charRe_mem {χ : DirichletCharacter ℂ k} (hχ : χ.IsQuadratic) (n : ℕ) :
    charRe χ n = 0 ∨ charRe χ n = 1 ∨ charRe χ n = -1 := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [charRe]
  rw [charRe_apply hn]
  rcases hχ (n : ZMod k) with h | h | h <;> simp [h]

/-- `∑_{j ≤ a} c^j` for `c ∈ {0, 1, -1}` is `≥ 0`, and `≥ 1` for even `a`. -/
theorem sum_range_pow_nonneg_of_mem {c : ℝ} (hc : c = 0 ∨ c = 1 ∨ c = -1) (a : ℕ) :
    0 ≤ ∑ j ∈ range (a + 1), c ^ j ∧ (Even a → 1 ≤ ∑ j ∈ range (a + 1), c ^ j) := by
  rcases hc with rfl | rfl | rfl
  · rw [sum_range_succ']; simp
  · simp only [one_pow, sum_const, card_range, nsmul_eq_mul, mul_one]
    constructor
    · positivity
    · intro _; push_cast; linarith [Nat.cast_nonneg (α := ℝ) a]
  · have key : ∀ a : ℕ, ∑ j ∈ range (a + 1), (-1 : ℝ) ^ j = if Even a then 1 else 0 := by
      intro a
      induction a with
      | zero => simp
      | succ a ih =>
        rw [sum_range_succ, ih]
        rcases Nat.even_or_odd a with h | h
        · have h' : ¬ Even (a + 1) := by rw [Nat.even_add_one]; exact not_not.2 h
          simp [h, h', pow_succ, h.neg_one_pow]
        · have h' : Even (a + 1) := h.add_one
          simp [Nat.not_even_iff_odd.2 h, h', h'.neg_one_pow]
    rw [key]
    constructor
    · split_ifs <;> norm_num
    · intro h; simp [h]

/-- **Apostol, Theorem 6.19.** For a real-valued character `χ` mod `k` and
`A(n) = ∑_{d ∣ n} χ(d)`: `A(n) ≥ 0` for all `n`, and `A(n) ≥ 1` if `n ≥ 1` is a square. -/
@[kb "apostol1976" "Thm 6.19, p. 142"]
theorem sum_divisors_char_nonneg {χ : DirichletCharacter ℂ k} (hχ : χ.IsQuadratic) (n : ℕ) :
    0 ≤ ∑ d ∈ n.divisors, (χ d).re ∧ (n ≠ 0 → IsSquare n → 1 ≤ ∑ d ∈ n.divisors, (χ d).re) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  have hA : ∑ d ∈ n.divisors, (χ d).re = (charRe χ * ζ) n := by
    rw [coe_mul_zeta_apply]
    exact sum_congr rfl fun d hd ↦ (charRe_apply (Nat.ne_of_gt (Nat.pos_of_mem_divisors hd))).symm
  have hmult := (isMultiplicative_charRe hχ).mul (isMultiplicative_zeta.natCast (R := ℝ))
  have hpp : ∀ p a : ℕ, p.Prime → (charRe χ * ζ) (p ^ a) =
      ∑ j ∈ range (a + 1), charRe χ p ^ j := by
    intro p a hp
    rw [coe_mul_zeta_apply, Nat.sum_divisors_prime_pow hp]
    exact sum_congr rfl fun j _ ↦ charRe_pow hχ p j
  rw [hA, hmult.multiplicative_factorization _ hn, Finsupp.prod, Nat.support_factorization]
  have hfac : ∀ p ∈ n.primeFactors, 0 ≤ (charRe χ * ζ) (p ^ n.factorization p) ∧
      (Even (n.factorization p) → 1 ≤ (charRe χ * ζ) (p ^ n.factorization p)) := by
    intro p hp
    rw [hpp p _ (Nat.prime_of_mem_primeFactors hp)]
    exact sum_range_pow_nonneg_of_mem (charRe_mem hχ p) _
  refine ⟨prod_nonneg fun p hp ↦ (hfac p hp).1, fun _ hsq ↦ ?_⟩
  rw [Nat.isSquare_iff_even_factorization] at hsq
  calc (1 : ℝ) = ∏ p ∈ n.primeFactors, (1 : ℝ) := by simp
    _ ≤ ∏ p ∈ n.primeFactors, (charRe χ * ζ) (p ^ n.factorization p) :=
        prod_le_prod₀ (fun _ _ ↦ zero_le_one)
          (fun p hp ↦ (hfac p hp).2 (hsq p (Nat.prime_of_mem_primeFactors hp)))

/-- The divisor sum of a real character is real. -/
theorem sum_divisors_char_eq_re {χ : DirichletCharacter ℂ k} (hχ : χ.IsQuadratic) (n : ℕ) :
    ∑ d ∈ n.divisors, χ d = ((∑ d ∈ n.divisors, (χ d).re : ℝ) : ℂ) := by
  push_cast
  exact sum_congr rfl fun d _ ↦ IsQuadratic.apply_eq_re hχ _

/-! ## `∑_{n ≤ x} 1/√n = 2√x + A + O(1/√x)` -/

/-- `u(N) = ∑_{n ≤ N} 1/√n - 2√N`. -/
noncomputable def sqrtSumSeq (N : ℕ) : ℝ := ∑ n ∈ Ioc 0 N, 1 / √(n : ℝ) - 2 * √(N : ℝ)

theorem sqrtSumSeq_succ_le (N : ℕ) (hN : 1 ≤ N) :
    0 ≤ sqrtSumSeq N - sqrtSumSeq (N + 1) ∧
      sqrtSumSeq N - sqrtSumSeq (N + 1) ≤ 1 / √(N : ℝ) - 1 / √((N + 1 : ℕ) : ℝ) := by
  have e : sqrtSumSeq N - sqrtSumSeq (N + 1) =
      2 * √((N + 1 : ℕ) : ℝ) - 2 * √(N : ℝ) - 1 / √((N + 1 : ℕ) : ℝ) := by
    rw [sqrtSumSeq, sqrtSumSeq, sum_Ioc_succ_top (Nat.zero_le _)]; ring
  rw [e]
  set a := √(N : ℝ)
  set b := √((N + 1 : ℕ) : ℝ)
  have ha : 0 < a := Real.sqrt_pos.2 (by exact_mod_cast hN)
  have hb : 0 < b := Real.sqrt_pos.2 (by positivity)
  have ha2 : a ^ 2 = N := Real.sq_sqrt (Nat.cast_nonneg _)
  have hb2 : b ^ 2 = N + 1 := by rw [Real.sq_sqrt (Nat.cast_nonneg _)]; push_cast; ring
  have hab : a ≤ b := Real.sqrt_le_sqrt (by push_cast; linarith)
  -- `b - a = 1/(a + b)`
  have hba : (b - a) * (a + b) = 1 := by nlinarith
  constructor
  · rw [sub_nonneg, div_le_iff₀ hb]
    nlinarith
  · have : 2 * (b - a) ≤ 1 / a := by
      rw [le_div_iff₀ ha]
      nlinarith
    linarith

theorem sqrtSumSeq_sub_le (N M : ℕ) (hN : 1 ≤ N) (hNM : N ≤ M) :
    0 ≤ sqrtSumSeq N - sqrtSumSeq M ∧ sqrtSumSeq N - sqrtSumSeq M ≤ 1 / √(N : ℝ) - 1 / √(M : ℝ) := by
  induction M, hNM using Nat.le_induction with
  | base => simp
  | succ M hNM ih =>
    have h := sqrtSumSeq_succ_le M (le_trans hN hNM)
    constructor <;> linarith [ih.1, ih.2, h.1, h.2]

/-- **Apostol, Theorem 3.2(b)** for `s = 1/2`: there is a constant `A` with
`|∑_{n ≤ x} 1/√n - 2√x - A| ≤ 4/√x` for `x ≥ 1`. -/
@[kb "apostol1976" "Thm 3.2(b), p. 55"]
theorem exists_abs_sum_inv_sqrt_sub_le :
    ∃ A : ℝ, ∀ x : ℝ, 1 ≤ x → |∑ n ∈ Ioc 0 ⌊x⌋₊, 1 / √(n : ℝ) - 2 * √x - A| ≤ 4 / √x := by
  -- `u` is antitone and bounded below on `N ≥ 1`
  set u : ℕ → ℝ := fun N ↦ sqrtSumSeq (N + 1)
  have hanti : Antitone u := antitone_nat_of_succ_le fun N ↦ by
    have := (sqrtSumSeq_succ_le (N + 1) (by omega)).1; simp only [u]; linarith
  have hbdd : ∀ N, sqrtSumSeq 1 - 1 ≤ u N := fun N ↦ by
    have := (sqrtSumSeq_sub_le 1 (N + 1) le_rfl (by omega)).2
    have h0 : 0 ≤ 1 / √((N + 1 : ℕ) : ℝ) := by positivity
    have h1 : 1 / √((1 : ℕ) : ℝ) = 1 := by simp
    simp only [u]; linarith
  have hlim : Tendsto u atTop (𝓝 (⨅ N, u N)) :=
    tendsto_atTop_ciInf hanti ⟨sqrtSumSeq 1 - 1, by rintro _ ⟨N, rfl⟩; exact hbdd N⟩
  set A := ⨅ N, u N
  refine ⟨A, fun x hx ↦ ?_⟩
  have hx0 : 0 < x := by linarith
  set N := ⌊x⌋₊
  have hN1 : 1 ≤ N := Nat.le_floor (by exact_mod_cast hx)
  -- `0 ≤ u(N) - A ≤ 1/√N`
  have hA1 : A ≤ sqrtSumSeq N := by
    have := ciInf_le ⟨sqrtSumSeq 1 - 1, by rintro _ ⟨M, rfl⟩; exact hbdd M⟩ (N - 1)
    simp only [u, Nat.sub_add_cancel hN1] at this
    exact this
  have hA2 : sqrtSumSeq N - A ≤ 1 / √(N : ℝ) := by
    have : ∀ M, N ≤ M + 1 → sqrtSumSeq N - u M ≤ 1 / √(N : ℝ) := fun M hM ↦ by
      have := (sqrtSumSeq_sub_le N (M + 1) hN1 hM).2
      have h0 : 0 ≤ 1 / √((M + 1 : ℕ) : ℝ) := by positivity
      simp only [u]; linarith
    have hl : Tendsto (fun M ↦ sqrtSumSeq N - u M) atTop (𝓝 (sqrtSumSeq N - A)) :=
      hlim.const_sub _
    exact le_of_tendsto hl (eventually_atTop.2 ⟨N, fun M hM ↦ this M (by omega)⟩)
  -- compare `√N` with `√x`
  have hNx : (N : ℝ) ≤ x := Nat.floor_le hx0.le
  have hxN : x < N + 1 := Nat.lt_floor_add_one x
  have hsN : 0 < √(N : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hN1)
  have hsx : 0 < √x := Real.sqrt_pos.2 hx0
  have hsNx : √(N : ℝ) ≤ √x := Real.sqrt_le_sqrt hNx
  have hsN2 : √(N : ℝ) ^ 2 = N := Real.sq_sqrt (Nat.cast_nonneg _)
  have hsx2 : √x ^ 2 = x := Real.sq_sqrt hx0.le
  -- `1/√N ≤ 2/√x` (since `x ≤ 2N`) and `2√x - 2√N ≤ 2/√x`
  have h1 : 1 / √(N : ℝ) ≤ 2 / √x := by
    rw [div_le_div_iff₀ hsN hsx]
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    nlinarith
  have h2 : 2 * √x - 2 * √(N : ℝ) ≤ 2 / √x := by
    rw [le_div_iff₀ hsx]
    nlinarith
  have e : ∑ n ∈ Ioc 0 N, 1 / √(n : ℝ) - 2 * √x - A =
      (sqrtSumSeq N - A) - (2 * √x - 2 * √(N : ℝ)) := by rw [sqrtSumSeq]; ring
  rw [e, abs_le]
  have h3 : 0 ≤ 2 * √x - 2 * √(N : ℝ) := by linarith
  constructor
  · have : 4 / √x = 2 / √x + 2 / √x := by ring
    linarith
  · have : 4 / √x = 2 / √x + 2 / √x := by ring
    have : 0 ≤ 2 / √x := by positivity
    linarith

end NTKB.Apostol
