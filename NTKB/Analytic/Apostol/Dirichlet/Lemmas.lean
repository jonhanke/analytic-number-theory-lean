/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Apostol.Characters.RealNonvanishing
import NTKB.Analytic.Apostol.Primes.Shapiro
import NTKB.Analytic.Apostol.ArithmeticFunctions.GeneralizedConvolution
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# The lemmas of Apostol's proof of Dirichlet's theorem (Chapter 7, §§7.3–7.7)

Fixed modulus `k ≥ 1`, `χ` a Dirichlet character mod `k` (`DirichletCharacter ℂ k`),
`L(1, χ) = ∑ χ(n)/n` and `L'(1, χ) = -∑ χ(n) log n/n` (`LOne`, `LOneDeriv`, Theorem 6.18).

* Lemma 7.4 (extraction of a residue class by orthogonality);
* Lemma 7.5: `∑_{p ≤ x} χ(p) log p/p = -L'(1, χ) ∑_{n ≤ x} μ(n)χ(n)/n + O(1)` for `χ ≠ χ₁`;
* Lemma 7.6: `L(1, χ) ∑_{n ≤ x} μ(n)χ(n)/n = O(1)` for `χ ≠ χ₁`;
* Lemma 7.8: if `χ ≠ χ₁` and `L(1, χ) = 0` then `L'(1, χ) ∑_{n ≤ x} μ(n)χ(n)/n = log x + O(1)`.

Error terms are `∃ C, ∀ x ≥ 1, ‖…‖ ≤ C`. Apostol's uses of the generalized Möbius inversion
(Theorem 2.23) are replaced by the equivalent finite identities over `ab ≤ x`
(`sum_Ioc_sum_divisorsAntidiagonal`).
-/

open Finset ArithmeticFunction Filter Topology Real Chebyshev
open scoped ArithmeticFunction.Moebius

namespace NTKB.Apostol

variable {k : ℕ} [NeZero k]

/-! ## The prime powers `p^a`, `a ≥ 2`, contribute `O(1)` to `∑ Λ(n)/n` -/

theorem sum_Ioc_mul_eq_abel_real (c f : ℕ → ℝ) (N : ℕ) :
    ∑ n ∈ Ioc 0 N, c n * f n = (∑ n ∈ Ioc 0 N, c n) * f (N + 1) +
      ∑ n ∈ Ioc 0 N, (∑ m ∈ Ioc 0 n, c m) * (f n - f (n + 1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_Ioc_succ_top (Nat.zero_le N), sum_Ioc_succ_top (Nat.zero_le N)
      (fun n ↦ (∑ m ∈ Ioc 0 n, c m) * (f n - f (n + 1))), sum_Ioc_succ_top (Nat.zero_le N) c, ih]
    ring

theorem sqrt_div_mul_succ_le (n : ℕ) (hn : 1 ≤ n) :
    √(n : ℝ) * (1 / n - 1 / (n + 1)) ≤ 2 * (1 / √(n : ℝ) - 1 / √((n + 1 : ℕ) : ℝ)) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set a := √(n : ℝ)
  set b := √((n + 1 : ℕ) : ℝ)
  have ha : 0 < a := Real.sqrt_pos.2 hn'
  have hb : 0 < b := Real.sqrt_pos.2 (by positivity)
  have ha2 : a ^ 2 = n := Real.sq_sqrt hn'.le
  have hb2 : b ^ 2 = n + 1 := by rw [Real.sq_sqrt (by positivity)]; push_cast; ring
  have e1 : a * (1 / n - 1 / (n + 1)) = 1 / (a * b ^ 2) := by
    rw [hb2, ← ha2]; field_simp; ring
  have e2 : 2 * (1 / a - 1 / b) = 2 * (b - a) / (a * b) := by field_simp
  rw [e1, e2, div_le_div_iff₀ (by positivity) (by positivity)]
  have key : 1 ≤ 2 * (b - a) * b := by nlinarith [sq_nonneg (a - b)]
  calc 1 * (a * b) ≤ (2 * (b - a) * b) * (a * b) :=
        mul_le_mul_of_nonneg_right key (le_of_lt (mul_pos ha hb))
    _ = 2 * (b - a) * (a * b ^ 2) := by ring

theorem sum_sqrt_div_mul_succ_le (N : ℕ) :
    ∑ n ∈ Ioc 0 N, √(n : ℝ) * (1 / n - 1 / (n + 1)) ≤ 2 := by
  have h : ∀ N : ℕ, ∑ n ∈ Ioc 0 N, √(n : ℝ) * (1 / n - 1 / (n + 1)) ≤
      2 * (1 - 1 / √((N + 1 : ℕ) : ℝ)) := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [sum_Ioc_succ_top (Nat.zero_le _)]
      have := sqrt_div_mul_succ_le (N + 1) (by omega)
      push_cast at this ih ⊢
      linarith
  refine (h N).trans ?_
  have : 0 ≤ 1 / √((N + 1 : ℕ) : ℝ) := by positivity
  linarith

/-- `∑_{n ≤ N, n not prime} Λ(n)/n ≤ C` (Apostol, proof of Lemma 7.5: `∑_p ∑_{a ≥ 2} log p/p^a`
converges; here via partial summation and Mathlib's `ψ(x) - ϑ(x) ≤ C √x`). -/
theorem exists_sum_nonprime_vonMangoldt_div_le :
    ∃ C, ∀ N : ℕ, ∑ n ∈ Ioc 0 N with ¬ n.Prime, Λ n / n ≤ C := by
  obtain ⟨C₀, hC₀⟩ := psi_sub_theta_le_mul_sqrt
  set C := max C₀ 0
  refine ⟨3 * C, fun N ↦ ?_⟩
  set a : ℕ → ℝ := fun n ↦ if n.Prime then 0 else Λ n
  have hE : ∀ m : ℕ, ∑ n ∈ Ioc 0 m, a n = ψ m - θ m := fun m ↦ by
    rw [psi_sub_theta_eq_sum_not_prime, Nat.floor_natCast, sum_filter]
    exact sum_congr rfl fun n _ ↦ by simp only [a]; split_ifs <;> simp_all
  have hE0 : ∀ m : ℕ, 0 ≤ ∑ n ∈ Ioc 0 m, a n := fun m ↦
    sum_nonneg fun n _ ↦ by simp only [a]; split_ifs; exacts [le_rfl, vonMangoldt_nonneg]
  have hEC : ∀ m : ℕ, ∑ n ∈ Ioc 0 m, a n ≤ C * √(m : ℝ) := fun m ↦ by
    rw [hE]
    exact (hC₀ m).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _))
  have hsum : ∑ n ∈ Ioc 0 N with ¬ n.Prime, Λ n / n = ∑ n ∈ Ioc 0 N, a n * (1 / (n : ℝ)) := by
    rw [sum_filter]
    exact sum_congr rfl fun n _ ↦ by simp only [a]; split_ifs <;> simp [div_eq_mul_inv]
  rw [hsum, sum_Ioc_mul_eq_abel_real a (fun n ↦ 1 / (n : ℝ)) N]
  have hC0 : 0 ≤ C := le_max_right _ _
  have h1 : (∑ n ∈ Ioc 0 N, a n) * (1 / ((N + 1 : ℕ) : ℝ)) ≤ C := by
    calc (∑ n ∈ Ioc 0 N, a n) * (1 / ((N + 1 : ℕ) : ℝ)) ≤ C * √(N : ℝ) * (1 / ((N + 1 : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_right (hEC N) (by positivity)
      _ ≤ C * 1 := by
          rw [mul_assoc]
          refine mul_le_mul_of_nonneg_left ?_ hC0
          rw [mul_one_div, div_le_one (by positivity)]
          have : √(N : ℝ) ≤ N + 1 := by
            rcases Nat.eq_zero_or_pos N with rfl | hN
            · simp
            · have : (1 : ℝ) ≤ N := by exact_mod_cast hN
              calc √(N : ℝ) ≤ √(((N : ℝ) + 1) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
                _ = N + 1 := Real.sqrt_sq (by positivity)
          push_cast; linarith
      _ = C := mul_one _
  have h2 : ∑ n ∈ Ioc 0 N, (∑ m ∈ Ioc 0 n, a m) * (1 / (n : ℝ) - 1 / ((n + 1 : ℕ) : ℝ)) ≤
      2 * C := by
    calc _ ≤ ∑ n ∈ Ioc 0 N, C * (√(n : ℝ) * (1 / n - 1 / (n + 1))) := by
          refine sum_le_sum fun n hn ↦ ?_
          have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (mem_Ioc.1 hn).1
          have hd : 0 ≤ 1 / (n : ℝ) - 1 / ((n + 1 : ℕ) : ℝ) := by
            rw [sub_nonneg]; push_cast
            exact one_div_le_one_div_of_le (by linarith) (by linarith)
          push_cast at hd ⊢
          rw [← mul_assoc]
          exact mul_le_mul_of_nonneg_right (hEC n) hd
      _ = C * ∑ n ∈ Ioc 0 N, √(n : ℝ) * (1 / n - 1 / (n + 1)) := by rw [mul_sum]
      _ ≤ C * 2 := mul_le_mul_of_nonneg_left (sum_sqrt_div_mul_succ_le N) hC0
      _ = 2 * C := mul_comm _ _
  push_cast at h1 h2 ⊢
  linarith

/-! ## Notation: `∑_{p ≤ x} χ(p) log p / p` and `∑_{n ≤ x} μ(n) χ(n)/n` -/

/-- `∑_{p ≤ x} χ(p) log p / p`. -/
noncomputable def primeCharSum (χ : DirichletCharacter ℂ k) (x : ℝ) : ℂ :=
  ∑ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, χ p * ((Real.log p / p : ℝ) : ℂ)

/-- `∑_{n ≤ x} μ(n) χ(n) / n`. -/
noncomputable def moebiusCharSum (χ : DirichletCharacter ℂ k) (x : ℝ) : ℂ :=
  ∑ n ∈ Ioc 0 ⌊x⌋₊, (μ n : ℂ) * χ n * ((1 / n : ℝ) : ℂ)

theorem sum_Ioc_floor_one_add_log_div_le {x : ℝ} (hx : 1 ≤ x) :
    ∑ d ∈ Ioc 0 ⌊x⌋₊, (1 + Real.log (x / d)) ≤ 3 * x := by
  have hx0 : 0 < x := by linarith
  have e : ∀ d ∈ Ioc 0 ⌊x⌋₊, 1 + Real.log (x / d) = (1 + Real.log x) - Real.log d := by
    intro d hd
    have hd0 : (0 : ℝ) < d := by exact_mod_cast (mem_Ioc.1 hd).1
    rw [Real.log_div hx0.ne' hd0.ne']; ring
  rw [sum_congr rfl e, sum_sub_distrib, sum_const, Nat.card_Ioc, Nat.sub_zero, nsmul_eq_mul]
  have h1 := Real.le_sum_log' hx
  have h2 := Nat.floor_le hx0.le
  have hl : 0 ≤ 1 + Real.log x := by linarith [Real.log_nonneg hx]
  nlinarith

/-! ## Lemma 7.4 -/

/-- **Apostol, Lemma 7.4.** For a unit `h` mod `k`, `x ≥ 1`:
`∑_{p ≤ x, p ≡ h} log p/p = (1/φ(k)) log x + (1/φ(k)) ∑_{χ ≠ χ₁} χ̄(h) ∑_{p ≤ x} χ(p) log p/p + O(1)`
(`χ̄(h) = χ(h⁻¹)`; the sum over `χ ≠ χ₁` is written as the sum over all `χ` minus the `χ₁`
term). -/
@[kb "apostol1976" "Lemma 7.4, p. 149"]
theorem lemma_7_4 {h : ZMod k} (hh : IsUnit h) :
    ∃ C, ∀ x : ℝ, 1 ≤ x →
      ‖((∑ p ∈ Ioc 0 ⌊x⌋₊ with (p.Prime ∧ ((p : ℕ) : ZMod k) = h), Real.log p / p : ℝ) : ℂ) -
        (1 / k.totient : ℂ) * Real.log x -
        (1 / k.totient : ℂ) * (∑ χ : DirichletCharacter ℂ k, χ h⁻¹ * primeCharSum χ x -
          primeCharSum (1 : DirichletCharacter ℂ k) x)‖ ≤ C := by
  obtain ⟨⟨C₁, hC₁⟩, -, -⟩ := apostol_thm_4_10
  -- the primes dividing `k`
  set Ck := ∑ p ∈ k.divisors, Real.log p / p
  have hφ : (0 : ℝ) < k.totient := by exact_mod_cast Nat.totient_pos.2 (NeZero.pos k)
  refine ⟨(C₁ + Ck) / k.totient, fun x hx ↦ ?_⟩
  -- orthogonality
  have horth : ∑ χ : DirichletCharacter ℂ k, χ h⁻¹ * primeCharSum χ x =
      (k.totient : ℂ) * ((∑ p ∈ Ioc 0 ⌊x⌋₊ with (p.Prime ∧ ((p : ℕ) : ZMod k) = h),
        Real.log p / p : ℝ) : ℂ) := by
    simp only [primeCharSum, mul_sum]
    rw [sum_comm, ← filter_filter, Complex.ofReal_sum, mul_sum,
      sum_filter (p := fun p : ℕ ↦ ((p : ℕ) : ZMod k) = h)]
    refine sum_congr rfl fun p _ ↦ ?_
    have := DirichletCharacter.sum_char_inv_mul_char_eq ℂ hh (p : ZMod k)
    have e : ∑ χ : DirichletCharacter ℂ k, χ h⁻¹ * (χ p * ((Real.log p / p : ℝ) : ℂ)) =
        (∑ χ : DirichletCharacter ℂ k, χ h⁻¹ * χ p) * ((Real.log p / p : ℝ) : ℂ) := by
      rw [sum_mul]; exact sum_congr rfl fun _ _ ↦ by ring
    rw [e, this]
    split_ifs with h1 h2 h2
    · rfl
    · exact absurd h1.symm h2
    · exact absurd h2.symm h1
    · simp
  -- the principal character
  have hprin : primeCharSum (1 : DirichletCharacter ℂ k) x =
      ((∑ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, Real.log p / p : ℝ) : ℂ) -
        ((∑ p ∈ Ioc 0 ⌊x⌋₊ with (p.Prime ∧ p ∣ k), Real.log p / p : ℝ) : ℂ) := by
    simp only [primeCharSum]
    rw [← filter_filter, Complex.ofReal_sum, Complex.ofReal_sum, sum_filter (p := (· ∣ k)),
      ← sum_sub_distrib]
    refine sum_congr rfl fun p hp ↦ ?_
    have hpp := (mem_filter.1 hp).2
    by_cases hpk : p ∣ k
    · have : ¬ IsUnit (p : ZMod k) := by
        rw [ZMod.isUnit_iff_coprime]
        exact fun hc ↦ hpp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hc hpk)
      simp [MulChar.map_nonunit _ this, hpk]
    · have : IsUnit (p : ZMod k) := by
        rw [ZMod.isUnit_iff_coprime]
        exact (Nat.Prime.coprime_iff_not_dvd hpp).2 hpk
      simp [MulChar.one_apply this, hpk]
  have hdiv : 0 ≤ ∑ p ∈ Ioc 0 ⌊x⌋₊ with (p.Prime ∧ p ∣ k), Real.log p / p ∧
      ∑ p ∈ Ioc 0 ⌊x⌋₊ with (p.Prime ∧ p ∣ k), Real.log p / p ≤ Ck := by
    constructor
    · exact sum_nonneg fun p hp ↦ div_nonneg (Real.log_nonneg (by
        exact_mod_cast (mem_filter.1 hp).2.1.one_lt.le)) (Nat.cast_nonneg _)
    · have hnn : ∀ p ∈ k.divisors, 0 ≤ Real.log p / p := fun p hp ↦ by
        have : (1 : ℝ) ≤ p := by exact_mod_cast Nat.pos_of_mem_divisors hp
        exact div_nonneg (Real.log_nonneg this) (Nat.cast_nonneg _)
      refine sum_le_sum_of_subset_of_nonneg ?_ fun p hp _ ↦ hnn p hp
      intro p hp
      simp only [mem_filter] at hp
      exact Nat.mem_divisors.2 ⟨hp.2.2, NeZero.ne k⟩
  set S := ((∑ p ∈ Ioc 0 ⌊x⌋₊ with (p.Prime ∧ ((p : ℕ) : ZMod k) = h), Real.log p / p : ℝ) : ℂ)
  have hφc : (k.totient : ℂ) ≠ 0 := by exact_mod_cast hφ.ne'
  have e : S - (1 / k.totient : ℂ) * Real.log x - (1 / k.totient : ℂ) *
      (∑ χ : DirichletCharacter ℂ k, χ h⁻¹ * primeCharSum χ x -
        primeCharSum (1 : DirichletCharacter ℂ k) x) =
      (1 / k.totient : ℂ) * (((∑ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, Real.log p / p - Real.log x -
        ∑ p ∈ Ioc 0 ⌊x⌋₊ with (p.Prime ∧ p ∣ k), Real.log p / p : ℝ) : ℂ)) := by
    rw [horth, hprin]
    field_simp
    push_cast
    ring
  rw [e, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_div, norm_one, Complex.norm_natCast]
  have hb := hC₁ x hx
  rw [div_eq_mul_one_div (C₁ + Ck), mul_comm (C₁ + Ck)]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  calc |∑ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, Real.log p / p - Real.log x -
        ∑ p ∈ Ioc 0 ⌊x⌋₊ with (p.Prime ∧ p ∣ k), Real.log p / p| ≤
        |∑ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, Real.log p / p - Real.log x| +
          |∑ p ∈ Ioc 0 ⌊x⌋₊ with (p.Prime ∧ p ∣ k), Real.log p / p| := abs_sub _ _
    _ ≤ C₁ + Ck := by
        rw [abs_of_nonneg hdiv.1]; exact add_le_add hb hdiv.2

end NTKB.Apostol
