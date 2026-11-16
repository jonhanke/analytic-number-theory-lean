/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Davenport.Zeros.LZeroCount

/-!
# Zeros of `L(s, χ)` in the critical strip for every character

**Davenport, Ch. 16, p. 112 (row 16-9).** For a character `χ` mod `q` induced by `χ₁` mod `q₁`,
`L(s, χ) = L(s, χ₁) ∏_{p ∣ q} (1 - χ₁(p) p^{-s})`, and the Euler factors do not vanish for `σ > 0`.
So `L(s, χ)` and `L(s, χ₁)` have the same zeros, with the same multiplicities, in `0 < σ < 1`:
`N(T, χ) = N(T, χ₁)`, and the zero-counting formula of Chapter 16 (`Davenport.LZeroCount_sub_le`)
holds for every nonprincipal `χ` with `q` replaced by the conductor `q₁`.

Here `N(T, χ)` (`LStripZeroCount`) is defined for every `χ` directly from `L(s, χ)`: the number of
zeros in `0 < σ < 1`, `|t| < T`, with multiplicity. For primitive `χ` it agrees with the count
`LZeroCount` of the zeros of `ξ(s, χ)` used in Chapter 16 (`LStripZeroCount_eq_LZeroCount`).
-/

open Filter Topology Complex Set DirichletCharacter
open scoped Real

namespace NTKB

/-- **Davenport's `N(T, χ)` for every character** (Ch. 16, p. 101 and p. 112): the number of
zeros of `L(s, χ)` in `0 < σ < 1` with `|t| < T`, counted with multiplicity. -/
noncomputable def LStripZeroCount {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (T : ℝ) : ℕ :=
  Nat.card {ρ : ZeroIndex (LFunction χ) // 0 < ρ.val.re ∧ ρ.val.re < 1 ∧ |ρ.val.im| < T}

/-- Zero indices over a set where two functions have the same orders correspond. -/
noncomputable def zeroIndexEquivOfOrderEq {f g : ℂ → ℂ} (P : ℂ → Prop)
    (h : ∀ z, P z → analyticOrderNatAt f z = analyticOrderNatAt g z) :
    {ρ : ZeroIndex f // P ρ.val} ≃ {ρ : ZeroIndex g // P ρ.val} where
  toFun ρ := ⟨⟨ρ.1.1, Fin.cast (h _ ρ.2) ρ.1.2⟩, ρ.2⟩
  invFun ρ := ⟨⟨ρ.1.1, Fin.cast (h _ ρ.2).symm ρ.1.2⟩, ρ.2⟩
  left_inv ρ := by rfl
  right_inv ρ := by rfl

lemma analyticOrderNatAt_mul_of_ne_zero {f g : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f z)
    (hg : AnalyticAt ℂ g z) (hg0 : g z ≠ 0) :
    analyticOrderNatAt (fun s ↦ f s * g s) z = analyticOrderNatAt f z := by
  unfold analyticOrderNatAt
  rw [show (fun s ↦ f s * g s) = f * g from rfl, analyticOrderAt_mul hf hg,
    analyticOrderAt_eq_zero.mpr (Or.inr hg0), add_zero]

lemma analyticOrderNatAt_congr {f g : ℂ → ℂ} {z : ℂ} (h : f =ᶠ[𝓝 z] g) :
    analyticOrderNatAt f z = analyticOrderNatAt g z := by
  unfold analyticOrderNatAt
  rw [analyticOrderAt_congr h]

/-- The Euler factor `∏_{p ∣ N} (1 - χ(p) p^{-s})`. -/
noncomputable def eulerFactorProd {M : ℕ} (χ : DirichletCharacter ℂ M) (N : ℕ) (s : ℂ) : ℂ :=
  ∏ p ∈ N.primeFactors, (1 - χ p * (p : ℂ) ^ (-s))

lemma differentiable_eulerFactorProd {M : ℕ} (χ : DirichletCharacter ℂ M) (N : ℕ) :
    Differentiable ℂ (eulerFactorProd χ N) := by
  intro s
  unfold eulerFactorProd
  refine DifferentiableAt.fun_finsetProd fun p hp ↦ ?_
  have : NeZero p := ⟨(Nat.prime_of_mem_primeFactors hp).ne_zero⟩
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne p
  exact (differentiableAt_const _).sub ((differentiableAt_const _).mul
    ((differentiableAt_id.neg).const_cpow (Or.inl hp0)))

/-- The Euler factors do not vanish for `σ > 0`. -/
lemma eulerFactorProd_ne_zero {M : ℕ} (χ : DirichletCharacter ℂ M) (N : ℕ) {s : ℂ}
    (hs : 0 < s.re) : eulerFactorProd χ N s ≠ 0 := by
  unfold eulerFactorProd
  rw [Finset.prod_ne_zero_iff]
  intro p hp
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hpp.one_lt
  have hlt : ‖χ p * (p : ℂ) ^ (-s)‖ < 1 := by
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos hpp.pos, neg_re]
    have h1 : ‖χ p‖ ≤ 1 := DirichletCharacter.norm_le_one χ p
    have h2 : (p : ℝ) ^ (-s.re) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)
    have h3 : 0 ≤ (p : ℝ) ^ (-s.re) := by positivity
    nlinarith [norm_nonneg (χ p)]
  intro h
  have : χ p * (p : ℂ) ^ (-s) = 1 := by linear_combination -h
  rw [this, norm_one] at hlt
  exact lt_irrefl _ hlt

/-- For `χ₁` mod `M ∣ N` and `0 < σ`, `s ≠ 1`, `L(s, χ₁)` and `L(s, χ)` (`χ` induced by `χ₁`)
have the same order of vanishing. -/
lemma analyticOrderNatAt_LFunction_changeLevel {M N : ℕ} [NeZero M] [NeZero N] (hMN : M ∣ N)
    (χ : DirichletCharacter ℂ M) {z : ℂ} (hz : 0 < z.re) (hz1 : z ≠ 1) :
    analyticOrderNatAt (LFunction (changeLevel hMN χ)) z = analyticOrderNatAt (LFunction χ) z := by
  have hU : IsOpen {s : ℂ | s ≠ 1} := isOpen_ne
  have hev : LFunction (changeLevel hMN χ) =ᶠ[𝓝 z]
      fun s ↦ LFunction χ s * eulerFactorProd χ N s := by
    filter_upwards [hU.mem_nhds hz1] with s hs
    exact LFunction_changeLevel hMN χ (Or.inr hs)
  rw [analyticOrderNatAt_congr hev]
  have hL : AnalyticAt ℂ (LFunction χ) z := by
    have hd : DifferentiableOn ℂ (LFunction χ) {s : ℂ | s ≠ 1} := fun s hs ↦
      (differentiableAt_LFunction χ s (Or.inl hs)).differentiableWithinAt
    exact hd.analyticAt (hU.mem_nhds hz1)
  exact analyticOrderNatAt_mul_of_ne_zero hL
    ((differentiable_eulerFactorProd χ N).analyticAt z) (eulerFactorProd_ne_zero χ N hz)

/-- **Davenport, Ch. 16, p. 112 (row 16-9)**: if `χ` mod `N` is induced by `χ₁` mod `M`, then
`N(T, χ) = N(T, χ₁)`: the zeros of `L(s, χ)` and `L(s, χ₁)` in `0 < σ < 1` coincide, with
multiplicity. -/
@[kb "davenport1980" "Ch 16, p. 112"]
theorem Davenport.LStripZeroCount_changeLevel {M N : ℕ} [NeZero M] [NeZero N] (hMN : M ∣ N)
    (χ : DirichletCharacter ℂ M) (T : ℝ) :
    LStripZeroCount (changeLevel hMN χ) T = LStripZeroCount χ T := by
  unfold LStripZeroCount
  refine Nat.card_congr (zeroIndexEquivOfOrderEq
    (fun z : ℂ ↦ 0 < z.re ∧ z.re < 1 ∧ |z.im| < T) fun z hz ↦ ?_)
  refine analyticOrderNatAt_LFunction_changeLevel hMN χ hz.1 fun h ↦ ?_
  rw [h] at hz; simp at hz

/-- For primitive `χ` mod `q > 1`, the zeros of `ξ(s, χ)` are the zeros of `L(s, χ)` in the strip,
with multiplicity, so `LStripZeroCount χ T = LZeroCount χ T`. -/
theorem LStripZeroCount_eq_LZeroCount {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ.IsPrimitive) (hN : N ≠ 1) (T : ℝ) : LStripZeroCount χ T = LZeroCount χ T := by
  classical
  unfold LStripZeroCount LZeroCount
  have e1 : {ρ : ZeroIndex (dirichletXi χ) // |ρ.val.im| < T} ≃
      {ρ : ZeroIndex (dirichletXi χ) // 0 < ρ.val.re ∧ ρ.val.re < 1 ∧ |ρ.val.im| < T} :=
    Equiv.subtypeEquivRight fun ρ ↦ ⟨fun h ↦ ⟨(dirichletXi_zero_mem hχ hN ρ).2.1,
      (dirichletXi_zero_mem hχ hN ρ).2.2, h⟩, fun h ↦ h.2.2⟩
  rw [Nat.card_congr e1]
  refine Nat.card_congr (zeroIndexEquivOfOrderEq
    (fun z : ℂ ↦ 0 < z.re ∧ z.re < 1 ∧ |z.im| < T) fun z hz ↦ ?_)
  have hU : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  set a := dirichletParity χ with ha
  have ha0 := dirichletParity_re_nonneg χ
  have hG : ∀ s : ℂ, 0 < s.re → Gammaℝ (s + a) ≠ 0 := fun s hs ↦
    Gammaℝ_ne_zero_of_re_pos (by rw [add_re]; linarith)
  have hev : dirichletXi χ =ᶠ[𝓝 z]
      fun s ↦ LFunction χ s * ((N : ℂ) ^ ((s + a) / 2) * Gammaℝ (s + a)) := by
    filter_upwards [hU.mem_nhds hz.1] with s hs
    rw [dirichletXi_eq_mul_LFunction χ hN (hG s hs)]
    ring
  rw [analyticOrderNatAt_congr hev]
  symm
  have hχ1 := ne_one_of_isPrimitive hχ hN
  refine analyticOrderNatAt_mul_of_ne_zero ((differentiable_LFunction hχ1).analyticAt z) ?_ ?_
  · have hd : DifferentiableOn ℂ (fun s : ℂ ↦ (N : ℂ) ^ ((s + a) / 2) * Gammaℝ (s + a))
        {s | 0 < s.re} := by
      intro s hs
      have h1 : DifferentiableAt ℂ (fun s : ℂ ↦ (N : ℂ) ^ ((s + a) / 2)) s :=
        ((differentiableAt_id.add_const _).div_const 2).const_cpow (Or.inl natCast_ne_zero')
      have h2 : DifferentiableAt ℂ (fun s : ℂ ↦ Gammaℝ (s + a)) s := by
        have hne := hG s hs
        have h4 := (differentiable_Gammaℝ_inv (s + a)).inv (inv_ne_zero hne)
        have h3 : DifferentiableAt ℂ (fun w ↦ Gammaℝ w) (s + a) := by
          convert h4 using 1
          ext w
          simp
        exact h3.comp s (differentiableAt_id.add_const a)
      exact (h1.mul h2).differentiableWithinAt
    exact hd.analyticAt (hU.mem_nhds hz.1)
  · refine mul_ne_zero ?_ (hG z hz.1)
    rw [Ne, Complex.cpow_eq_zero_iff]
    exact fun h ↦ natCast_ne_zero' h.1

/-- **Davenport, Ch. 16, p. 112 (row 16-9)**: there is an absolute `A` such that for every
nonprincipal-at-the-conductor character `χ` mod `q`, i.e. with conductor `q₁ > 1`, and `T ≥ 3`,
`|N(T, χ) - ((T/π) log(q₁T/2π) - T/π)| ≤ A log(q₁T)`: the formula of 16-2 with `q` replaced by
`q₁`. -/
@[kb "davenport1980" "Ch 16, p. 112"]
theorem Davenport.LStripZeroCount_sub_le :
    ∃ A : ℝ, 0 < A ∧ ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q), χ.conductor ≠ 1 →
      ∀ T : ℝ, 3 ≤ T →
      |(LStripZeroCount χ T : ℝ) - (T / π * Real.log (χ.conductor * T / (2 * π)) - T / π)| ≤
        A * Real.log (χ.conductor * T) := by
  obtain ⟨A, hA, h⟩ := Davenport.LZeroCount_sub_le
  refine ⟨A, hA, fun {q} _ χ hc T hT ↦ ?_⟩
  have : NeZero χ.conductor := ⟨conductor_ne_zero χ⟩
  have e1 : LStripZeroCount χ T = LStripZeroCount χ.primitiveCharacter T := by
    conv_lhs => rw [← changeLevel_primitiveCharacter χ]
    exact Davenport.LStripZeroCount_changeLevel _ _ T
  rw [e1, LStripZeroCount_eq_LZeroCount (primitiveCharacter_isPrimitive χ) hc]
  exact h (primitiveCharacter_isPrimitive χ) hc T hT

end NTKB
