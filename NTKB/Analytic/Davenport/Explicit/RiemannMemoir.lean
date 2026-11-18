/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.NumberTheory.Chebyshev
import NTKB.Analytic.Davenport.Zeros.ExplicitSmall

/-!
# Riemann's memoir: the product for `ξ` and von Mangoldt's formula (Davenport, Chapter 8)

**Davenport, Ch. 8, p. 60, (c') (row 8-7).** `ξ(s) = ½ s(s - 1) π^{-s/2} Γ(s/2) ζ(s)` is entire, its
zeros are the zeros of `ζ` in `0 < σ < 1`, and `ξ(s) = e^{A + Bs} ∏_ρ (1 - s/ρ) e^{s/ρ}`. Davenport
states this in Chapter 8 and proves it in Chapter 12; here it is assembled from the Chapter 12 results
`NTKB.differentiable_riemannXi`, `NTKB.riemannXi_eq`, `NTKB.riemannXi_eq_zero_iff` and
`NTKB.Davenport.riemannXi_hadamard` (row 12-6, the factorization of an entire function of order at
most one, `NTKB/Analytic/Davenport/Hadamard/Factorization.lean`).

**Davenport, Ch. 8, p. 60, (d') (row 8-8).** von Mangoldt's formula
`ψ(x) - x = -∑_ρ x^ρ/ρ - ζ'(0)/ζ(0) - ½ log(1 - x^{-2})` for real `x > 1`, the sum over the zeros taken
symmetrically (`lim_{T → ∞} ∑_{|γ| < T}`). At a prime power `x` the left side is read with
`ψ₀(x) = ψ(x) - Λ(x)/2` (Davenport, Ch. 17, p. 104). Here `ψ` is Mathlib's `Chebyshev.psi`; the proof is
Chapter 17's (`NTKB.Davenport.explicit_formula_vonMangoldt`, row 17-2).
-/

open Filter Topology Complex
open scoped Real ArithmeticFunction.vonMangoldt

namespace NTKB

/-- **Davenport, Ch. 8, p. 60, (c') (row 8-7)**: `ξ` is entire; for `s ≠ 1` not a pole of `Γ(s/2)`,
`ξ(s) = ½ s(s - 1) π^{-s/2} Γ(s/2) ζ(s)`; the zeros of `ξ` (listed with multiplicity by `ZeroIndex`) are
zeros of `ζ` in `0 < σ < 1`; and `ξ(s) = e^{A + Bs} ∏_ρ (1 - s/ρ) e^{s/ρ}` for every `s`. -/
@[kb "davenport1980" "Ch 8, p. 60"]
theorem Davenport.riemannXi_entire_product :
    Differentiable ℂ riemannXi ∧
    (∀ s : ℂ, s ≠ 1 → (∀ n : ℕ, s ≠ -(2 * n)) →
      riemannXi s = 1 / 2 * s * (s - 1) * (π : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2) *
        riemannZeta s) ∧
    (∀ s : ℂ, riemannXi s = 0 ↔ riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1) ∧
    ∃ A B : ℂ, ∀ s, riemannXi s = Complex.exp (A + B * s) *
      ∏' ρ : ZeroIndex riemannXi, (1 - s / ρ.val) * Complex.exp (s / ρ.val) :=
  ⟨differentiable_riemannXi, fun _ h1 h2 ↦ riemannXi_eq h1 h2, fun _ ↦ riemannXi_eq_zero_iff,
    Davenport.riemannXi_hadamard⟩

/-- `ψ₀(x) = ψ(x) - Λ(x)/2`, the last term only when `x` is a natural number. -/
lemma psi0R_eq_psi_sub {x : ℝ} (hx : 0 ≤ x) :
    psi0R x = Chebyshev.psi x - if (⌊x⌋₊ : ℝ) = x then Λ ⌊x⌋₊ / 2 else 0 := by
  have hstep : ∀ n ∈ Finset.range ⌊x⌋₊, perronStepR x n = 1 := by
    intro n hn
    rw [Finset.mem_range] at hn
    have : (n : ℝ) < x := by
      have h1 : (n : ℝ) + 1 ≤ ⌊x⌋₊ := by exact_mod_cast hn
      have h2 : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx
      linarith
    simp [perronStepR, this]
  have htop : perronStepR x ⌊x⌋₊ = if (⌊x⌋₊ : ℝ) = x then 1 / 2 else 1 := by
    unfold perronStepR
    by_cases he : (⌊x⌋₊ : ℝ) = x
    · simp [he]
    · have hlt : (⌊x⌋₊ : ℝ) < x := lt_of_le_of_ne (Nat.floor_le hx) he
      simp [hlt, he]
  have hpsi : Chebyshev.psi x = ∑ n ∈ Finset.range (⌊x⌋₊ + 1), Λ n := by
    rw [Chebyshev.psi, Finset.range_eq_Ico]
    have : Finset.Ico 0 (⌊x⌋₊ + 1) = insert 0 (Finset.Ioc 0 ⌊x⌋₊) := by
      ext n; simp only [Finset.mem_Ico, Finset.mem_insert, Finset.mem_Ioc]; omega
    rw [this, Finset.sum_insert (by simp)]
    simp
  rw [psi0R, hpsi, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_congr rfl fun n hn ↦ by rw [hstep n hn, mul_one], htop]
  split_ifs <;> ring_nf

/-- `ψ₀(x) = ψ(x)` when `x` is not a prime power. -/
lemma psi0R_eq_psi_of_not_primePow {x : ℝ} (hx : 0 ≤ x) (h : ∀ n : ℕ, IsPrimePow n → (n : ℝ) ≠ x) :
    psi0R x = Chebyshev.psi x := by
  rw [psi0R_eq_psi_sub hx]
  split_ifs with he
  · have : Λ ⌊x⌋₊ = 0 := by
      rw [ArithmeticFunction.vonMangoldt_eq_zero_iff]; exact fun hp ↦ h _ hp he
    rw [this]; ring_nf
  · ring_nf

/-- **Davenport, Ch. 8, p. 60, (d') (row 8-8)**, von Mangoldt's formula at every real `x > 1`, with
`ψ₀`: `∑_{|γ|<T} x^ρ/ρ → x - ψ₀(x) - ζ'(0)/ζ(0) - ½ log(1 - x^{-2})` as `T → ∞`. -/
@[kb "davenport1980" "Ch 8, p. 60"]
theorem Davenport.explicit_formula_memoir_psi0 {x : ℝ} (hx : 1 < x) :
    Tendsto (fun T : ℝ ↦ ∑ ρ ∈ zerosBelow T, (x : ℂ) ^ ρ.val / ρ.val) atTop
      (𝓝 ((x : ℂ) - psi0R x - deriv riemannZeta 0 / riemannZeta 0 -
        ((1 / 2 * Real.log (1 - x ^ (-2 : ℝ)) : ℝ) : ℂ))) := by
  have h := (Davenport.tendsto_explicitMain_real_of_one_lt' hx).const_sub
    ((x : ℂ) - deriv riemannZeta 0 / riemannZeta 0 - ((1 / 2 * Real.log (1 - x ^ (-2 : ℝ)) : ℝ) : ℂ))
  convert h using 1
  · funext T
    simp only [explicitMain, perronKernel]
    ring_nf
  · ring_nf

/-- **Davenport, Ch. 8, p. 60, (d') (row 8-8)**, Riemann's form, von Mangoldt's theorem: for real
`x > 1` not a prime power,
`ψ(x) - x = -∑_ρ x^ρ/ρ - ζ'(0)/ζ(0) - ½ log(1 - x^{-2})`, where `ψ(x) = ∑_{n ≤ x} Λ(n)` and the sum over
the nontrivial zeros `ρ = β + iγ` of `ζ` (with multiplicity) is `lim_{T → ∞} ∑_{|γ| < T}`.
At prime powers see `Davenport.explicit_formula_memoir_psi0`. -/
@[kb "davenport1980" "Ch 8, p. 60"]
theorem Davenport.explicit_formula_memoir {x : ℝ} (hx : 1 < x)
    (hpp : ∀ n : ℕ, IsPrimePow n → (n : ℝ) ≠ x) :
    Tendsto (fun T : ℝ ↦ -∑ ρ ∈ zerosBelow T, (x : ℂ) ^ ρ.val / ρ.val -
        deriv riemannZeta 0 / riemannZeta 0 - ((1 / 2 * Real.log (1 - x ^ (-2 : ℝ)) : ℝ) : ℂ))
      atTop (𝓝 ((Chebyshev.psi x - x : ℝ) : ℂ)) := by
  have h := ((Davenport.explicit_formula_memoir_psi0 hx).neg).sub_const
    (deriv riemannZeta 0 / riemannZeta 0 + ((1 / 2 * Real.log (1 - x ^ (-2 : ℝ)) : ℝ) : ℂ))
  rw [psi0R_eq_psi_of_not_primePow (by linarith) hpp] at h
  convert h using 1
  · funext T; ring_nf
  · push_cast; ring_nf

end NTKB
