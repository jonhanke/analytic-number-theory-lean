/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import NTKB.Attr

/-!
# The integrated Chebyshev function `ψ₁` (Apostol, §13.2 Lemmas 1–2, Theorem 13.1)

For `a : ℕ → ℝ` put `A(x) = ∑_{n ≤ x} a(n)` and `A₁(x) = ∫₁ˣ A(t) dt`.

* Lemma 1: `∑_{n ≤ x} (x - n) a(n) = A₁(x)` (Apostol: Abel's identity with `f(t) = t`;
  here Mathlib's `sum_mul_eq_sub_integral_mul₀`).
* Lemma 2 (a l'Hospital rule for increasing step functions): if `a(n) ≥ 0` and
  `A₁(x) ~ L xᶜ` with `c, L > 0`, then `A(x) ~ c L x^{c-1}`. Apostol's proof: compare
  `A₁(βx) - A₁(x)` with `(β - 1) x A(x)` for `β > 1` and `A₁(x) - A₁(αx)` with
  `(1 - α) x A(x)` for `α < 1`, then let `β, α → 1`.
* Theorem 13.1: `ψ₁(x) = ∑_{n ≤ x} (x - n) Λ(n)`, and `ψ₁(x) ~ x²/2` implies `ψ(x) ~ x`.
-/

open Finset Real Filter Topology MeasureTheory
open scoped ArithmeticFunction.vonMangoldt

namespace NTKB.Apostol

/-- `A(x) = ∑_{1 ≤ n ≤ x} a(n)` (zero for `x < 1`). -/
noncomputable def partialSum (a : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑ n ∈ Ioc 0 ⌊x⌋₊, a n

/-- `A₁(x) = ∫₁ˣ A(t) dt`. -/
noncomputable def partialSumIntegral (a : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∫ t in (1 : ℝ)..x, partialSum a t

theorem partialSum_eq_sum_Icc (a : ℕ → ℝ) (x : ℝ) :
    partialSum a x = ∑ k ∈ Icc 0 ⌊x⌋₊, (fun k ↦ if k = 0 then 0 else a k) k := by
  rw [partialSum, Icc_eq_cons_Ioc (Nat.zero_le _), sum_cons]
  simp only [↓reduceIte, zero_add]
  exact sum_congr rfl fun k hk ↦ by simp [(Finset.mem_Ioc.1 hk).1.ne']

/-- **Apostol, §13.2 Lemma 1**: `∑_{n ≤ x} (x - n) a(n) = ∫₁ˣ A(t) dt` for `x ≥ 1`. -/
@[kb "apostol1976" "Ch 13 Lemma 1, p. 279"]
theorem sum_sub_mul_eq_partialSumIntegral (a : ℕ → ℝ) {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ Ioc 0 ⌊x⌋₊, (x - n) * a n = partialSumIntegral a x := by
  set c : ℕ → ℝ := fun k ↦ if k = 0 then 0 else a k
  have hab := sum_mul_eq_sub_integral_mul₀ (f := fun t : ℝ ↦ t) c (by simp [c]) x
    (fun t _ ↦ differentiableAt_id) (by simp)
  simp only [deriv_id'', one_mul] at hab
  have h1 : ∑ k ∈ Icc 0 ⌊x⌋₊, (k : ℝ) * c k = ∑ n ∈ Ioc 0 ⌊x⌋₊, (n : ℝ) * a n := by
    rw [Icc_eq_cons_Ioc (Nat.zero_le _), sum_cons, Nat.cast_zero, zero_mul, zero_add]
    exact sum_congr rfl fun k hk ↦ by simp [c, (Finset.mem_Ioc.1 hk).1.ne']
  have hA : ∀ t, ∑ k ∈ Icc 0 ⌊t⌋₊, c k = partialSum a t := fun t ↦
    (partialSum_eq_sum_Icc a t).symm
  rw [h1, hA] at hab
  simp_rw [hA] at hab
  rw [partialSumIntegral, intervalIntegral.integral_of_le hx]
  have : ∑ n ∈ Ioc 0 ⌊x⌋₊, (x - n) * a n =
      x * partialSum a x - ∑ n ∈ Ioc 0 ⌊x⌋₊, (n : ℝ) * a n := by
    rw [partialSum, mul_sum, ← sum_sub_distrib]
    exact sum_congr rfl fun n _ ↦ by ring
  rw [this, hab]
  ring

theorem partialSum_mono {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) : Monotone (partialSum a) := by
  intro x y hxy
  exact sum_le_sum_of_subset_of_nonneg (Ioc_subset_Ioc_right (Nat.floor_mono hxy))
    fun n _ _ ↦ ha n

theorem partialSum_nonneg {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (x : ℝ) : 0 ≤ partialSum a x :=
  sum_nonneg fun n _ ↦ ha n

/-- `A₁(y) - A₁(x) = ∫ₓʸ A`. -/
theorem partialSumIntegral_sub {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (x y : ℝ) :
    partialSumIntegral a y - partialSumIntegral a x = ∫ t in x..y, partialSum a t := by
  rw [partialSumIntegral, partialSumIntegral, intervalIntegral.integral_interval_sub_left]
  · exact (partialSum_mono ha).intervalIntegrable
  · exact (partialSum_mono ha).intervalIntegrable

/-- `(y - x) A(x) ≤ A₁(y) - A₁(x)` for `x ≤ y`. -/
theorem sub_mul_partialSum_le {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) {x y : ℝ} (hxy : x ≤ y) :
    (y - x) * partialSum a x ≤ partialSumIntegral a y - partialSumIntegral a x := by
  rw [partialSumIntegral_sub ha]
  have := intervalIntegral.integral_mono_on hxy (intervalIntegrable_const (μ := volume))
    (partialSum_mono ha).intervalIntegrable
    (fun t ht ↦ partialSum_mono ha ht.1)
  simpa [mul_comm] using this

/-- `A₁(y) - A₁(x) ≤ (y - x) A(y)` for `x ≤ y`. -/
theorem partialSumIntegral_sub_le {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) {x y : ℝ} (hxy : x ≤ y) :
    partialSumIntegral a y - partialSumIntegral a x ≤ (y - x) * partialSum a y := by
  rw [partialSumIntegral_sub ha]
  have := intervalIntegral.integral_mono_on hxy (partialSum_mono ha).intervalIntegrable
    (intervalIntegrable_const (μ := volume)) (fun t ht ↦ partialSum_mono ha ht.2)
  simpa [mul_comm] using this

/-- `(β^c - 1)/(β - 1) → c` as `β → 1`, `β ≠ 1`. -/
theorem tendsto_rpow_sub_one_div (c : ℝ) :
    Tendsto (fun β : ℝ ↦ (β ^ c - 1) / (β - 1)) (𝓝[≠] 1) (𝓝 c) := by
  have h := (hasDerivAt_rpow_const (x := (1 : ℝ)) (p := c) (Or.inl one_ne_zero))
  rw [hasDerivAt_iff_tendsto_slope] at h
  simp only [one_rpow, mul_one] at h
  refine h.congr' (Eventually.of_forall fun β ↦ ?_)
  simp [slope_def_field]

/-- **Apostol, §13.2 Lemma 2**: for `a(n) ≥ 0`, `A₁(x) ~ L xᶜ` (`c, L > 0`) implies
`A(x) ~ c L x^{c-1}`. -/
@[kb "apostol1976" "Ch 13 Lemma 2, p. 280"]
theorem tendsto_partialSum_div_of_partialSumIntegral {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n)
    {c L : ℝ} (_hc : 0 < c) (_hL : 0 < L)
    (h : Tendsto (fun x ↦ partialSumIntegral a x / x ^ c) atTop (𝓝 L)) :
    Tendsto (fun x ↦ partialSum a x / x ^ (c - 1)) atTop (𝓝 (c * L)) := by
  have hslope := tendsto_rpow_sub_one_div c
  -- the quotient `A₁(γx)/(γx)ᶜ · γᶜ` for fixed `γ > 0`
  have hscale : ∀ γ : ℝ, 0 < γ →
      Tendsto (fun x ↦ partialSumIntegral a (γ * x) / x ^ c) atTop (𝓝 (L * γ ^ c)) := by
    intro γ hγ
    have h1 := h.comp (tendsto_id.const_mul_atTop hγ)
    refine (h1.mul_const (γ ^ c)).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with x hx
    simp only [Function.comp, id]
    rw [mul_rpow hγ.le hx.le]
    field_simp
  -- rewrite `A(x)/x^{c-1}` as `x A(x) / xᶜ`
  have hrw : ∀ x : ℝ, 0 < x → partialSum a x / x ^ (c - 1) = x * partialSum a x / x ^ c := by
    intro x hx
    rw [rpow_sub hx, rpow_one]
    field_simp
  rw [tendsto_order]
  constructor
  · -- lower bound, with `α < 1`
    intro b hb
    have hα : Tendsto (fun α : ℝ ↦ L * ((α ^ c - 1) / (α - 1))) (𝓝[<] 1) (𝓝 (L * c)) :=
      (hslope.mono_left (nhdsWithin_mono _ fun x hx ↦ ne_of_lt hx)).const_mul L
    rw [mul_comm] at hb
    obtain ⟨α, hαb, hα0'⟩ := ((hα.eventually (lt_mem_nhds hb)).and
      (Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num))).exists
    have hα1 : α < 1 := hα0'.2
    replace hα0' : 0 < α := hα0'.1
    have hlim : Tendsto (fun x ↦ (partialSumIntegral a x / x ^ c -
        partialSumIntegral a (α * x) / x ^ c) / (1 - α)) atTop
        (𝓝 ((L - L * α ^ c) / (1 - α))) :=
      (h.sub (hscale α hα0')).div_const _
    have hval : (L - L * α ^ c) / (1 - α) = L * ((α ^ c - 1) / (α - 1)) := by
      have : (1 - α) ≠ 0 := by linarith [show α < 1 from hα1]
      have : (α - 1) ≠ 0 := by linarith [show α < 1 from hα1]
      field_simp; ring
    rw [hval] at hlim
    filter_upwards [hlim.eventually (lt_mem_nhds hαb), eventually_gt_atTop 0] with x hx hx0
    refine lt_of_lt_of_le hx ?_
    rw [hrw x hx0]
    have h1α : 0 < 1 - α := by linarith [show α < 1 from hα1]
    have key := partialSumIntegral_sub_le ha (show α * x ≤ x by nlinarith [show α < 1 from hα1])
    rw [div_le_div_iff₀ h1α (rpow_pos_of_pos hx0 c), ← sub_div,
      div_mul_eq_mul_div, div_le_iff₀ (rpow_pos_of_pos hx0 c)]
    have := mul_le_mul_of_nonneg_right key (rpow_pos_of_pos hx0 c).le
    linarith
  · -- upper bound, with `β > 1`
    intro b hb
    have hβ : Tendsto (fun β : ℝ ↦ L * ((β ^ c - 1) / (β - 1))) (𝓝[>] 1) (𝓝 (L * c)) :=
      (hslope.mono_left (nhdsWithin_mono _ fun x hx ↦ ne_of_gt hx)).const_mul L
    rw [mul_comm] at hb
    obtain ⟨β, hβb, hβ1⟩ := ((hβ.eventually (gt_mem_nhds hb)).and
      (Ioo_mem_nhdsGT (show (1 : ℝ) < 2 by norm_num))).exists
    have hβ1' : 1 < β := hβ1.1
    have hlim : Tendsto (fun x ↦ (partialSumIntegral a (β * x) / x ^ c -
        partialSumIntegral a x / x ^ c) / (β - 1)) atTop
        (𝓝 ((L * β ^ c - L) / (β - 1))) :=
      ((hscale β (by linarith)).sub h).div_const _
    have hval : (L * β ^ c - L) / (β - 1) = L * ((β ^ c - 1) / (β - 1)) := by ring
    rw [hval] at hlim
    filter_upwards [hlim.eventually (gt_mem_nhds hβb), eventually_gt_atTop 0] with x hx hx0
    refine lt_of_le_of_lt ?_ hx
    rw [hrw x hx0]
    have hβ0 : 0 < β - 1 := by linarith
    have key := sub_mul_partialSum_le ha (show x ≤ β * x by nlinarith)
    rw [div_le_div_iff₀ (rpow_pos_of_pos hx0 c) hβ0, ← sub_div,
      div_mul_eq_mul_div, le_div_iff₀ (rpow_pos_of_pos hx0 c)]
    have := mul_le_mul_of_nonneg_right key (rpow_pos_of_pos hx0 c).le
    linarith

/-- Apostol's `ψ₁(x) = ∫₁ˣ ψ(t) dt`. -/
noncomputable def psi1 (x : ℝ) : ℝ :=
  ∫ t in (1 : ℝ)..x, Chebyshev.psi t

theorem partialSum_vonMangoldt : partialSum (fun n ↦ Λ n) = Chebyshev.psi := rfl

/-- **Apostol, Theorem 13.1**, identity (10): `ψ₁(x) = ∑_{n ≤ x} (x - n) Λ(n)` for `x ≥ 1`. -/
@[kb "apostol1976" "Thm 13.1, p. 280"]
theorem psi1_eq_sum {x : ℝ} (hx : 1 ≤ x) :
    psi1 x = ∑ n ∈ Ioc 0 ⌊x⌋₊, (x - n) * Λ n :=
  (sum_sub_mul_eq_partialSumIntegral (fun n ↦ Λ n) hx).symm

/-- **Apostol, Theorem 13.1**: `ψ₁(x) ~ x²/2` implies `ψ(x) ~ x`. -/
@[kb "apostol1976" "Thm 13.1, p. 280"]
theorem tendsto_psi_div_of_psi1 (h : Tendsto (fun x ↦ psi1 x / (x ^ 2 / 2)) atTop (𝓝 1)) :
    Tendsto (fun x ↦ Chebyshev.psi x / x) atTop (𝓝 1) := by
  have h2 : Tendsto (fun x ↦ partialSumIntegral (fun n ↦ Λ n) x / x ^ (2 : ℝ)) atTop
      (𝓝 (1 / 2)) := by
    refine (h.div_const 2).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with x hx
    rw [rpow_two]
    simp only [partialSumIntegral, partialSum_vonMangoldt, psi1]
    field_simp
  have := tendsto_partialSum_div_of_partialSumIntegral
    (fun n ↦ ArithmeticFunction.vonMangoldt_nonneg) two_pos (by norm_num) h2
  rw [partialSum_vonMangoldt] at this
  norm_num at this
  exact this

end NTKB.Apostol
