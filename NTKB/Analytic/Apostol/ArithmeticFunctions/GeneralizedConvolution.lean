/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Apostol.ArithmeticFunctions.Multiplicative
import Mathlib.Algebra.Order.Floor.Semifield

/-!
# Generalized convolutions (Apostol, Chapter 2, §2.14)

For an arithmetical function `α` and `F : ℝ → ℂ`, Apostol's generalized convolution is
`(α ∘ F)(x) = ∑_{n ≤ x} α(n) F(x/n)` (`NTKB.Apostol.genConv`). Mathlib has nothing of this kind.

* `sum_Ioc_sum_divisorsAntidiagonal`: the finite identity
  `∑_{k ≤ N} ∑_{ab = k} G(a, b) = ∑_{a ≤ N} ∑_{b ≤ N/a} G(a, b)` behind all of this (and behind
  the hyperbola method of Chapter 3);
* Theorem 2.21: `α ∘ (β ∘ F) = (α * β) ∘ F`;
* Theorem 2.22: the generalized inversion formula;
* Theorem 2.23: the generalized Möbius inversion formula for completely multiplicative `α`.

Apostol's functions `F` live on `(0, ∞)` and vanish on `(0, 1)`; here `F : ℝ → ℂ` and the
inversion formulas assume `F x = 0` for `0 < x < 1` and are stated for `x > 0`.
-/

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius

namespace NTKB.Apostol

/-- `∑_{k ≤ N} ∑_{ab = k} G(a, b) = ∑_{a ≤ N} ∑_{b ≤ N/a} G(a, b)`: both sides are the sum of
`G` over the lattice points `(a, b)`, `a, b ≥ 1`, under the hyperbola `ab = N`. -/
theorem sum_Ioc_sum_divisorsAntidiagonal {M : Type*} [AddCommMonoid M] (G : ℕ → ℕ → M) (N : ℕ) :
    ∑ k ∈ Ioc 0 N, ∑ x ∈ k.divisorsAntidiagonal, G x.1 x.2 =
      ∑ a ∈ Ioc 0 N, ∑ b ∈ Ioc 0 (N / a), G a b := by
  trans ∑ x ∈ Ioc 0 N ×ˢ Ioc 0 N with x.1 * x.2 ≤ N, G x.1 x.2
  · trans ∑ k ∈ Ioc 0 N, ∑ x ∈ Ioc 0 N ×ˢ Ioc 0 N with x.1 * x.2 = k, G x.1 x.2
    · refine sum_congr rfl fun k hk ↦ ?_
      simp only [mem_Ioc] at hk
      rw [Nat.divisorsAntidiagonal_eq_prod_filter_of_le hk.1.ne' hk.2]
    · simp_rw [sum_filter]
      rw [sum_comm]
      refine sum_congr rfl fun x hx ↦ ?_
      simp only [mem_product, mem_Ioc] at hx
      rw [sum_ite_eq]
      simp only [mem_Ioc]
      congr 1
      apply propext
      constructor
      · exact fun h ↦ h.2
      · exact fun h ↦ ⟨Nat.mul_pos hx.1.1 hx.2.1, h⟩
  · rw [sum_filter, sum_product]
    refine sum_congr rfl fun a ha ↦ ?_
    simp only [mem_Ioc] at ha
    rw [← sum_filter]
    congr 1
    ext b
    simp only [mem_filter, mem_Ioc]
    constructor
    · rintro ⟨⟨hb, -⟩, h⟩
      exact ⟨hb, (Nat.le_div_iff_mul_le ha.1).2 (by rwa [mul_comm])⟩
    · rintro ⟨hb, h⟩
      have h' := (Nat.le_div_iff_mul_le ha.1).1 h
      refine ⟨⟨hb, ?_⟩, by rwa [mul_comm]⟩
      exact le_trans (Nat.le_mul_of_pos_left b ha.1) (by rwa [mul_comm] at h')

/-- Apostol's generalized convolution `(α ∘ F)(x) = ∑_{n ≤ x} α(n) F(x/n)` (§2.14). -/
noncomputable def genConv (α : ArithmeticFunction ℂ) (F : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∑ n ∈ Ioc 0 ⌊x⌋₊, α n * F (x / n)

/-- **Apostol, Theorem 2.21** (associative property relating `∘` and `*`):
`α ∘ (β ∘ F) = (α * β) ∘ F`. -/
@[kb "apostol1976" "Thm 2.21, p. 39"]
theorem genConv_genConv (α β : ArithmeticFunction ℂ) (F : ℝ → ℂ) (x : ℝ) :
    genConv α (genConv β F) x = genConv (α * β) F x := by
  simp only [genConv, mul_sum]
  have hfl : ∀ n : ℕ, ⌊x / n⌋₊ = ⌊x⌋₊ / n := fun n ↦ Nat.floor_div_natCast x n
  simp_rw [hfl]
  rw [← sum_Ioc_sum_divisorsAntidiagonal (fun a b ↦ α a * (β b * F (x / a / b)))]
  refine sum_congr rfl fun k hk ↦ ?_
  rw [ArithmeticFunction.mul_apply, sum_mul]
  refine sum_congr rfl fun p hp ↦ ?_
  rw [Nat.mem_divisorsAntidiagonal] at hp
  rw [← hp.1, Nat.cast_mul, div_div, mul_assoc]

/-- `(I ∘ F)(x) = F(x)` for `x > 0` when `F` vanishes on `(0, 1)` (Apostol, §2.14). -/
theorem genConv_one {F : ℝ → ℂ} (hF : ∀ x, 0 < x → x < 1 → F x = 0) {x : ℝ} (hx : 0 < x) :
    genConv 1 F x = F x := by
  rw [genConv]
  rcases lt_or_ge x 1 with h | h
  · rw [hF x hx h, Nat.floor_eq_zero.2 h]
    simp
  · rw [sum_eq_single 1]
    · simp
    · intro b _ hb
      simp [ArithmeticFunction.one_apply_ne hb]
    · intro h1
      exact absurd (by simpa using Nat.one_le_floor_iff x |>.2 h) h1

/-- **Apostol, Theorem 2.22** (generalized inversion formula). If `α * α' = I` then
`G(x) = ∑_{n ≤ x} α(n) F(x/n)` for all `x > 0` if and only if
`F(x) = ∑_{n ≤ x} α'(n) G(x/n)` for all `x > 0`. -/
@[kb "apostol1976" "Thm 2.22, p. 40"]
theorem genConv_inversion {α α' : ArithmeticFunction ℂ} (hα : α * α' = 1) {F G : ℝ → ℂ}
    (hF : ∀ x, 0 < x → x < 1 → F x = 0) (hG : ∀ x, 0 < x → x < 1 → G x = 0) :
    (∀ x, 0 < x → G x = genConv α F x) ↔ (∀ x, 0 < x → F x = genConv α' G x) := by
  -- if `G = α ∘ F` on `(0, ∞)` then `α' ∘ G = α' ∘ (α ∘ F)` there
  have hcongr : ∀ (β : ArithmeticFunction ℂ) (H K : ℝ → ℂ), (∀ x, 0 < x → H x = K x) →
      ∀ x, 0 < x → genConv β H x = genConv β K x := by
    intro β H K hHK x hx
    refine sum_congr rfl fun n hn ↦ ?_
    rw [hHK _ (div_pos hx (by simpa using (mem_Ioc.1 hn).1))]
  constructor
  · intro h x hx
    rw [hcongr α' G (genConv α F) h x hx, genConv_genConv, mul_comm, hα, genConv_one hF hx]
  · intro h x hx
    rw [hcongr α F (genConv α' G) h x hx, genConv_genConv, hα, genConv_one hG hx]

/-- **Apostol, Theorem 2.23** (generalized Möbius inversion formula). If `α` is completely
multiplicative, then `G(x) = ∑_{n ≤ x} α(n) F(x/n)` for all `x > 0` if and only if
`F(x) = ∑_{n ≤ x} μ(n) α(n) G(x/n)` for all `x > 0`. -/
@[kb "apostol1976" "Thm 2.23, p. 40"]
theorem genConv_moebius_inversion {α : ArithmeticFunction ℂ} (hα : IsCompletelyMultiplicative α)
    {F G : ℝ → ℂ} (hF : ∀ x, 0 < x → x < 1 → F x = 0) (hG : ∀ x, 0 < x → x < 1 → G x = 0) :
    (∀ x, 0 < x → G x = ∑ n ∈ Ioc 0 ⌊x⌋₊, α n * F (x / n)) ↔
      (∀ x, 0 < x → F x = ∑ n ∈ Ioc 0 ⌊x⌋₊, (μ n : ℂ) * α n * G (x / n)) := by
  have hinv : α * (μ : ArithmeticFunction ℂ).pmul α = 1 := by
    rw [mul_comm]
    exact (isCompletelyMultiplicative_iff_pmul_moebius_mul_eq_one hα.isMultiplicative).1 hα
  have := genConv_inversion hinv hF hG
  simpa only [genConv, pmul_apply, intCoe_apply] using this

end NTKB.Apostol
