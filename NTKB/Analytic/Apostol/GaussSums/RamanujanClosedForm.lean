/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Apostol.GaussSums.Ramanujan

/-!
# Evaluation of `s_k(n)` (Apostol, Chapter 8, §8.4, Theorem 8.8)

**Theorem 8.8.** Let `f` be completely multiplicative with `f(p) ≠ 0`, `g = μ h` with `h`
multiplicative, `F = f * g`, `N = k/(n,k)`. Then `s_k(n) F(N) = F(k) g(N)`, i.e.
`s_k(n) = F(k) g(N)/F(N)` when moreover `f(p) ≠ h(p)` for all `p` (so `F(N) ≠ 0`).
Example: `c_k(n) = φ(k) μ(N)/φ(N)` (Hölder).

Apostol's proof: `F(m) = f(m) ∏_{p ∣ m} (1 - h(p)/f(p))`; with `a = (n,k)`, `k = aN`,
`s_k(n) = ∑_{e ∣ a} f(a/e) μ(Ne) h(Ne) = f(a) μ(N) h(N) ∏_{p ∣ a, p ∤ N} (1 - h(p)/f(p))`.
-/

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius

namespace NTKB.Apostol

variable {f h : ArithmeticFunction ℂ}

theorem IsCompletelyMultiplicative.apply_ne_zero (hf : IsCompletelyMultiplicative f)
    (hp : ∀ p : ℕ, p.Prime → f p ≠ 0) {m : ℕ} (hm : m ≠ 0) : f m ≠ 0 := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  by_cases h1 : m = 1
  · rw [h1, hf.1]; exact one_ne_zero
  · have hmp := Nat.minFac_prime h1
    have hdvd := Nat.minFac_dvd m
    have hlt : m / m.minFac < m := Nat.div_lt_self (Nat.pos_of_ne_zero hm) hmp.one_lt
    have hq : m / m.minFac ≠ 0 := by
      intro h0
      rw [Nat.div_eq_zero_iff_lt hmp.pos] at h0
      exact absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero hm) hdvd) (not_le.2 h0)
    rw [← Nat.mul_div_cancel' hdvd, hf.2]
    exact mul_ne_zero (hp _ hmp) (ih _ hlt hq)

/-- The multiplicative function `e ↦ [(e, N) = 1] h(e)/f(e)`. -/
noncomputable def ratioCoprime (h f : ArithmeticFunction ℂ) (N : ℕ) : ArithmeticFunction ℂ :=
  ⟨fun e ↦ if e.Coprime N then h e / f e else 0, by simp⟩

theorem isMultiplicative_ratioCoprime (hh : h.IsMultiplicative)
    (hf : IsCompletelyMultiplicative f) (N : ℕ) : (ratioCoprime h f N).IsMultiplicative := by
  refine ⟨by simp [ratioCoprime, hh.map_one, hf.1], fun {m n} hmn ↦ ?_⟩
  simp only [ratioCoprime, coe_mk, Nat.coprime_mul_iff_left]
  split_ifs <;> simp_all [hh.map_mul_of_coprime hmn, hf.2, mul_div_mul_comm]

/-- `F(m) = f(m) ∏_{p ∣ m} (1 - h(p)/f(p))` for `F = f * μh`, `m ≥ 1`. -/
theorem mul_pmul_moebius_apply (hh : h.IsMultiplicative) (hf : IsCompletelyMultiplicative f)
    (hp : ∀ p : ℕ, p.Prime → f p ≠ 0) {m : ℕ} (hm : m ≠ 0) :
    (f * (μ : ArithmeticFunction ℂ).pmul h) m = f m * ∏ p ∈ m.primeFactors, (1 - h p / f p) := by
  have hr := isMultiplicative_ratioCoprime hh hf 1
  have := hr.prodPrimeFactors_one_sub _ hm
  simp only [ratioCoprime, coe_mk, Nat.coprime_one_right_eq_true, if_true] at this
  rw [this, mul_sum, mul_comm f, mul_apply_eq_sum_divisors]
  refine sum_congr rfl fun d hd ↦ ?_
  have hd0 : d ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors hd)
  have hfd := hf.apply_ne_zero hp hd0
  have hdm := Nat.dvd_of_mem_divisors hd
  rw [pmul_apply, intCoe_apply]
  have : f m = f (m / d) * f d := by rw [← hf.2, Nat.div_mul_cancel hdm]
  rw [this]
  field_simp

end NTKB.Apostol
