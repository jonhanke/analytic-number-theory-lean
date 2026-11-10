/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Apostol.ArithmeticFunctions.Multiplicative
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

/-!
# Derivatives of arithmetical functions and the Selberg identity (Apostol, §§2.18–2.19)

Apostol's derivative of an arithmetical function is `f'(n) = f(n) log n`
(`NTKB.Apostol.arithDeriv`, for functions with values in any `ℝ`-algebra; not in Mathlib).

* Theorem 2.26: `(f + g)' = f' + g'`, `(f * g)' = f' * g + f * g'`, `(f⁻¹)' = -f' * (f * f)⁻¹`;
* Theorem 2.27 (Selberg's identity):
  `Λ(n) log n + ∑_{d ∣ n} Λ(d) Λ(n/d) = ∑_{d ∣ n} μ(d) log²(n/d)`, by Apostol's proof:
  differentiate `Λ * u = u'` and multiply by `μ`.
-/

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

namespace NTKB.Apostol

variable {R : Type*}

/-- The derivative `f'(n) = f(n) log n` of an arithmetical function (Apostol, §2.18). -/
noncomputable def arithDeriv [Ring R] [Algebra ℝ R] (f : ArithmeticFunction R) :
    ArithmeticFunction R :=
  ⟨fun n ↦ Real.log n • f n, by simp⟩

@[simp]
theorem arithDeriv_apply [Ring R] [Algebra ℝ R] (f : ArithmeticFunction R) (n : ℕ) :
    arithDeriv f n = Real.log n • f n := rfl

/-- **Apostol, Theorem 2.26 (a).** `(f + g)' = f' + g'`. -/
@[kb "apostol1976" "Thm 2.26(a), p. 45"]
theorem arithDeriv_add [Ring R] [Algebra ℝ R] (f g : ArithmeticFunction R) :
    arithDeriv (f + g) = arithDeriv f + arithDeriv g := by
  ext n
  simp [smul_add]

/-- **Apostol, Theorem 2.26 (b).** `(f * g)' = f' * g + f * g'`. -/
@[kb "apostol1976" "Thm 2.26(b), p. 45"]
theorem arithDeriv_mul [CommRing R] [Algebra ℝ R] (f g : ArithmeticFunction R) :
    arithDeriv (f * g) = arithDeriv f * g + f * arithDeriv g := by
  ext n
  simp only [arithDeriv_apply, add_apply, ArithmeticFunction.mul_apply,
    smul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun x hx ↦ ?_
  obtain ⟨rfl, hn⟩ := Nat.mem_divisorsAntidiagonal.1 hx
  have h1 : (x.1 : ℝ) ≠ 0 := by exact_mod_cast left_ne_zero_of_mul hn
  have h2 : (x.2 : ℝ) ≠ 0 := by exact_mod_cast right_ne_zero_of_mul hn
  rw [Nat.cast_mul, Real.log_mul h1 h2, add_smul, smul_mul_assoc, mul_smul_comm]

theorem arithDeriv_one [Ring R] [Algebra ℝ R] : arithDeriv (1 : ArithmeticFunction R) = 0 := by
  ext n
  by_cases h : n = 1
  · simp [h]
  · simp [ArithmeticFunction.one_apply_ne h]

/-- **Apostol, Theorem 2.26 (c).** If `f * g = I` (so `g = f⁻¹`), then
`g' = -f' * (g * g)`, i.e. `(f⁻¹)' = -f' * (f * f)⁻¹`. -/
@[kb "apostol1976" "Thm 2.26(c), p. 45"]
theorem arithDeriv_inv [CommRing R] [Algebra ℝ R] {f g : ArithmeticFunction R} (h : f * g = 1) :
    arithDeriv g = -(arithDeriv f * (g * g)) := by
  have h0 : arithDeriv f * g + f * arithDeriv g = 0 := by
    rw [← arithDeriv_mul, h, arithDeriv_one]
  have : arithDeriv g = g * (f * arithDeriv g) := by
    rw [← mul_assoc, mul_comm g f, h, one_mul]
  rw [this, eq_neg_iff_add_eq_zero]
  calc g * (f * arithDeriv g) + arithDeriv f * (g * g)
      = g * (arithDeriv f * g + f * arithDeriv g) := by ring
    _ = 0 := by rw [h0, mul_zero]

/-- `(f * g)⁻¹ = f⁻¹ * g⁻¹` in the form used in 2.26(c): `(f * f) * (g * g) = I`. -/
theorem mul_self_mul_mul_self [CommRing R] {f g : ArithmeticFunction R} (h : f * g = 1) :
    (f * f) * (g * g) = 1 := by
  calc (f * f) * (g * g) = (f * g) * (f * g) := by ring
    _ = 1 := by rw [h, one_mul]

/-- **Apostol, Theorem 2.27** (the Selberg identity), in Dirichlet-product form:
`Λ' + Λ * Λ = u'' * μ`, where `u''(n) = log² n`. -/
theorem arithDeriv_vonMangoldt_add_mul_self :
    arithDeriv Λ + Λ * Λ = arithDeriv (arithDeriv (ζ : ArithmeticFunction ℝ)) * μ := by
  -- (15): `Λ * u = u'`
  have h15 : Λ * (ζ : ArithmeticFunction ℝ) = arithDeriv (ζ : ArithmeticFunction ℝ) := by
    rw [vonMangoldt_mul_zeta]
    ext n
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · simp [natCoe_apply, zeta_apply, hn]
  -- differentiate: `Λ' * u + Λ * u' = u''`, and `u' = Λ * u`
  have hd : arithDeriv (arithDeriv (ζ : ArithmeticFunction ℝ)) =
      arithDeriv Λ * ζ + Λ * (Λ * ζ) := by
    rw [← h15, arithDeriv_mul, h15]
  -- multiply by `μ = u⁻¹`
  have hμ : (ζ : ArithmeticFunction ℝ) * μ = 1 := coe_zeta_mul_coe_moebius
  calc arithDeriv Λ + Λ * Λ
      = (arithDeriv Λ * ζ + Λ * (Λ * ζ)) * μ := by
        rw [add_mul, mul_assoc, hμ, mul_one, mul_assoc, mul_assoc, hμ, mul_one]
    _ = arithDeriv (arithDeriv (ζ : ArithmeticFunction ℝ)) * μ := by
        rw [← hd]

/-- **Apostol, Theorem 2.27** (the Selberg identity). For `n ≥ 1`,
`Λ(n) log n + ∑_{d ∣ n} Λ(d) Λ(n/d) = ∑_{d ∣ n} μ(d) log²(n/d)`. -/
@[kb "apostol1976" "Thm 2.27, p. 46"]
theorem selberg_identity (n : ℕ) :
    Λ n * Real.log n + ∑ d ∈ n.divisors, Λ d * Λ (n / d) =
      ∑ d ∈ n.divisors, (μ d : ℝ) * Real.log ((n / d : ℕ) : ℝ) ^ 2 := by
  have h := congrArg (fun F : ArithmeticFunction ℝ ↦ F n) arithDeriv_vonMangoldt_add_mul_self
  simp only [add_apply, arithDeriv_apply, smul_eq_mul] at h
  rw [mul_comm (Λ n), ← mul_apply_eq_sum_divisors, h, mul_comm, mul_apply_eq_sum_divisors]
  refine sum_congr rfl fun d hd ↦ ?_
  rw [arithDeriv_apply, arithDeriv_apply, smul_eq_mul, smul_eq_mul, intCoe_apply, natCoe_apply,
    zeta_apply_ne (Nat.div_ne_zero_iff_of_dvd (Nat.dvd_of_mem_divisors hd) |>.2
      ⟨(Nat.mem_divisors.1 hd).2, Nat.ne_of_gt (Nat.pos_of_mem_divisors hd)⟩)]
  push_cast
  ring

end NTKB.Apostol
