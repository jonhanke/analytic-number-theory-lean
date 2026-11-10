/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.IsolatedZeros
import NTKB.Analytic.Davenport.Hadamard.ZeroCount

/-!
# Canonical products of genus one (Davenport, Chapter 11, p. 76)

**Davenport, p. 76.** If `∑ r_n^{-2}` converges (`r_n = |z_n|`), the product
`P(z) = ∏ (1 - z/z_n) e^{z/z_n}` converges absolutely for all `z`, uniformly in any bounded domain,
and represents an entire function with zeros (of the appropriate multiplicities) at the `z_n`.

## Main definitions

* `NTKB.weierstrassFactorOne w = (1 - w) e^w`, the primary factor of genus one.
* `NTKB.canonicalProductOne a z = ∏' i, weierstrassFactorOne (z / a i)` for a family `a : ι → ℂ`.

## Main results

* `NTKB.hasProdLocallyUniformlyOn_canonicalProductOne`: locally uniform convergence on `ℂ`
  when `∑ ‖a i‖⁻²` converges.
* `NTKB.differentiable_canonicalProductOne`: the product is entire.
* `NTKB.canonicalProductOne_ne_zero`: it does not vanish off the `a i`.
* `NTKB.analyticOrderAt_canonicalProductOne`: its order of vanishing at `z₀` is the number of `i`
  with `a i = z₀` (the multiplicity).
* `NTKB.Davenport.canonicalProduct_zeros` (row 11-8) for the zeros of an entire function of order
  at most one.

Mathlib has no Weierstrass products; the uniform convergence comes from Mathlib's
`Summable.hasProdUniformlyOn_one_add`, using `|E₁(w) - 1| ≤ 3|w|²` for `|w| ≤ 1`.
-/

open Filter Topology Metric Complex Set
open scoped ENNReal NNReal

namespace NTKB

/-- The Weierstrass primary factor of genus one, `E₁(w) = (1 - w) e^w`. -/
noncomputable def weierstrassFactorOne (w : ℂ) : ℂ := (1 - w) * Complex.exp w

@[simp] lemma weierstrassFactorOne_zero : weierstrassFactorOne 0 = 1 := by
  simp [weierstrassFactorOne]

lemma weierstrassFactorOne_eq_zero_iff {w : ℂ} : weierstrassFactorOne w = 0 ↔ w = 1 := by
  rw [weierstrassFactorOne, mul_eq_zero, sub_eq_zero]
  simp [Complex.exp_ne_zero, eq_comm]

lemma differentiable_weierstrassFactorOne : Differentiable ℂ weierstrassFactorOne := by
  unfold weierstrassFactorOne; fun_prop

/-- `|E₁(w) - 1| ≤ 3 |w|²` for `|w| ≤ 1`. -/
lemma norm_weierstrassFactorOne_sub_one_le {w : ℂ} (hw : ‖w‖ ≤ 1) :
    ‖weierstrassFactorOne w - 1‖ ≤ 3 * ‖w‖ ^ 2 := by
  have h : weierstrassFactorOne w - 1 = (Complex.exp w - 1 - w) - w * (Complex.exp w - 1) := by
    simp only [weierstrassFactorOne]; ring
  rw [h]
  calc ‖(Complex.exp w - 1 - w) - w * (Complex.exp w - 1)‖
      ≤ ‖Complex.exp w - 1 - w‖ + ‖w‖ * ‖Complex.exp w - 1‖ := by
        refine (norm_sub_le _ _).trans ?_
        rw [norm_mul]
    _ ≤ ‖w‖ ^ 2 + ‖w‖ * (2 * ‖w‖) := by
        gcongr
        · exact Complex.norm_exp_sub_one_sub_id_le hw
        · exact Complex.norm_exp_sub_one_le hw
    _ = 3 * ‖w‖ ^ 2 := by ring

/-- The canonical product of genus one with zeros `a i`: `∏' i, (1 - z / a i) e^{z / a i}`. -/
noncomputable def canonicalProductOne {ι : Type*} (a : ι → ℂ) (z : ℂ) : ℂ :=
  ∏' i, weierstrassFactorOne (z / a i)

variable {ι : Type*} {a : ι → ℂ}

@[simp] lemma canonicalProductOne_zero : canonicalProductOne a 0 = 1 := by
  simp [canonicalProductOne]

/-- Under `∑ ‖a i‖⁻² < ∞`, for each `R` cofinitely many `a i` satisfy `R ‖a i‖⁻¹ ≤ 1`. -/
lemma eventually_mul_inv_norm_le_one (ha : Summable fun i ↦ ‖a i‖⁻¹ ^ 2) (R : ℝ) :
    ∀ᶠ i in cofinite, R * ‖a i‖⁻¹ ≤ 1 := by
  have hR : (0 : ℝ) < (|R| + 1)⁻¹ ^ 2 := by positivity
  filter_upwards [ha.tendsto_cofinite_zero.eventually (gt_mem_nhds hR)] with i hi
  have h1 : ‖a i‖⁻¹ ≤ (|R| + 1)⁻¹ := by
    have := (pow_lt_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp hi
    exact this.le
  have h2 : R * ‖a i‖⁻¹ ≤ |R| * (|R| + 1)⁻¹ :=
    (mul_le_mul_of_nonneg_right (le_abs_self R) (by positivity)).trans
      (mul_le_mul_of_nonneg_left h1 (abs_nonneg R))
  refine h2.trans ?_
  rw [mul_inv_le_iff₀ (by positivity)]
  linarith

/-- Uniform bound for the factors on a closed disc. -/
lemma eventually_norm_weierstrassFactorOne_sub_one_le (ha : Summable fun i ↦ ‖a i‖⁻¹ ^ 2)
    (R : ℝ) :
    ∀ᶠ i in cofinite, ∀ z ∈ closedBall (0 : ℂ) R,
      ‖weierstrassFactorOne (z / a i) - 1‖ ≤ 3 * R ^ 2 * ‖a i‖⁻¹ ^ 2 := by
  filter_upwards [eventually_mul_inv_norm_le_one ha R] with i hi z hz
  have hz' : ‖z‖ ≤ R := by simpa using hz
  have hw : ‖z / a i‖ ≤ R * ‖a i‖⁻¹ := by
    rw [norm_div, div_eq_mul_inv]; gcongr
  refine (norm_weierstrassFactorOne_sub_one_le (hw.trans hi)).trans ?_
  calc 3 * ‖z / a i‖ ^ 2 ≤ 3 * (R * ‖a i‖⁻¹) ^ 2 := by gcongr
    _ = 3 * R ^ 2 * ‖a i‖⁻¹ ^ 2 := by ring

/-- Uniform convergence on closed discs. -/
theorem hasProdUniformlyOn_canonicalProductOne (ha : Summable fun i ↦ ‖a i‖⁻¹ ^ 2) (R : ℝ) :
    HasProdUniformlyOn (fun i z ↦ weierstrassFactorOne (z / a i)) (canonicalProductOne a)
      (closedBall 0 R) := by
  have h := Summable.hasProdUniformlyOn_one_add (f := fun i z ↦ weierstrassFactorOne (z / a i) - 1)
    (isCompact_closedBall 0 R) (ha.mul_left (3 * R ^ 2))
    (eventually_norm_weierstrassFactorOne_sub_one_le ha R) fun i ↦
      ((differentiable_weierstrassFactorOne.comp (differentiable_id.div_const (a i))).sub_const
        1).continuous.continuousOn
  simp only [add_sub_cancel] at h
  exact h

/-- **Davenport, p. 76**: the canonical product converges locally uniformly on `ℂ`. -/
theorem hasProdLocallyUniformlyOn_canonicalProductOne (ha : Summable fun i ↦ ‖a i‖⁻¹ ^ 2) :
    HasProdLocallyUniformlyOn (fun i z ↦ weierstrassFactorOne (z / a i))
      (canonicalProductOne a) univ := by
  refine hasProdLocallyUniformlyOn_of_forall_compact isOpen_univ fun K _ hK ↦ ?_
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  exact (hasProdUniformlyOn_canonicalProductOne ha (max R 0)).mono
    (hR.trans (closedBall_subset_closedBall (le_max_left R 0)))

lemma hasProd_canonicalProductOne (ha : Summable fun i ↦ ‖a i‖⁻¹ ^ 2) (z : ℂ) :
    HasProd (fun i ↦ weierstrassFactorOne (z / a i)) (canonicalProductOne a z) :=
  (hasProdLocallyUniformlyOn_canonicalProductOne ha).hasProd (mem_univ z)

lemma multipliable_canonicalProductOne (ha : Summable fun i ↦ ‖a i‖⁻¹ ^ 2) (z : ℂ) :
    Multipliable fun i ↦ weierstrassFactorOne (z / a i) :=
  (hasProd_canonicalProductOne ha z).multipliable

/-- **Davenport, p. 76**: the canonical product is an entire function. -/
theorem differentiable_canonicalProductOne (ha : Summable fun i ↦ ‖a i‖⁻¹ ^ 2) :
    Differentiable ℂ (canonicalProductOne a) := by
  have h := hasProdLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn.mp
    (hasProdLocallyUniformlyOn_canonicalProductOne ha)
  have hd := h.differentiableOn (Eventually.of_forall fun s ↦ by
    simp only [weierstrassFactorOne]; fun_prop) isOpen_univ
  exact fun z ↦ (hd z trivial).differentiableAt univ_mem

/-- The canonical product does not vanish off the points `a i`. -/
theorem canonicalProductOne_ne_zero (ha : Summable fun i ↦ ‖a i‖⁻¹ ^ 2) {z : ℂ}
    (hz : ∀ i, a i ≠ z) : canonicalProductOne a z ≠ 0 := by
  have hne : ∀ i, 1 + (weierstrassFactorOne (z / a i) - 1) ≠ 0 := by
    intro i
    rw [add_sub_cancel, Ne, weierstrassFactorOne_eq_zero_iff]
    intro h
    by_cases hai : a i = 0
    · simp [hai] at h
    · exact hz i ((div_eq_one_iff_eq hai).mp h).symm
  have hsum : Summable fun i ↦ ‖weierstrassFactorOne (z / a i) - 1‖ := by
    refine Summable.of_norm_bounded_eventually (ha.mul_left (3 * ‖z‖ ^ 2)) ?_
    filter_upwards [eventually_norm_weierstrassFactorOne_sub_one_le ha ‖z‖] with i hi
    simpa using hi z (by simp)
  have := tprod_one_add_ne_zero_of_summable hne hsum
  simpa [canonicalProductOne] using this

/-- Only finitely many `a i` equal a given nonzero point. -/
lemma finite_setOf_eq (ha : Summable fun i ↦ ‖a i‖⁻¹ ^ 2) {z₀ : ℂ} (hz₀ : z₀ ≠ 0) :
    {i | a i = z₀}.Finite := by
  have h := eventually_mul_inv_norm_le_one ha (2 * ‖z₀‖)
  rw [Filter.eventually_cofinite] at h
  refine h.subset fun i hi ↦ ?_
  simp only [mem_ofPred_eq] at hi ⊢
  rw [hi]
  have : 0 < ‖z₀‖ := norm_pos_iff.mpr hz₀
  rw [mul_assoc, mul_inv_cancel₀ this.ne']
  norm_num

/-- `E₁(z / z₀) = (z - z₀) · (-e^{z/z₀} / z₀)`. -/
lemma weierstrassFactorOne_div_eq {z₀ : ℂ} (hz₀ : z₀ ≠ 0) (z : ℂ) :
    weierstrassFactorOne (z / z₀) = (z - z₀) * (-Complex.exp (z / z₀) / z₀) := by
  simp only [weierstrassFactorOne]
  field_simp
  ring

/-- **Multiplicities** (Davenport, p. 76): if no `a i` is `0`, the order of vanishing of the
canonical product at `z₀` is the number of indices `i` with `a i = z₀`. -/
theorem analyticOrderAt_canonicalProductOne (ha : Summable fun i ↦ ‖a i‖⁻¹ ^ 2)
    (ha0 : ∀ i, a i ≠ 0) (z₀ : ℂ) :
    ∃ S : Finset ι, (∀ i, i ∈ S ↔ a i = z₀) ∧
      analyticOrderAt (canonicalProductOne a) z₀ = S.card := by
  classical
  have hP := differentiable_canonicalProductOne ha
  by_cases hz₀ : z₀ = 0
  · refine ⟨∅, fun i ↦ by simp [hz₀, ha0 i], ?_⟩
    rw [Finset.card_empty, Nat.cast_zero, (hP.analyticAt z₀).analyticOrderAt_eq_zero, hz₀]
    simp
  obtain ⟨S, hS⟩ : ∃ S : Finset ι, ∀ i, i ∈ S ↔ a i = z₀ :=
    ⟨(finite_setOf_eq ha hz₀).toFinset, fun i ↦ by simp⟩
  refine ⟨S, hS, ?_⟩
  set b : ↥((S : Set ι)ᶜ) → ℂ := fun j ↦ a j
  have hb : Summable fun j ↦ ‖b j‖⁻¹ ^ 2 := ha.comp_injective Subtype.val_injective
  have hQ := differentiable_canonicalProductOne hb
  have hQz₀ : canonicalProductOne b z₀ ≠ 0 :=
    canonicalProductOne_ne_zero hb fun j h ↦ j.2 (by simpa using (hS j).mpr h)
  set m := S.card
  set g : ℂ → ℂ := fun z ↦ (-Complex.exp (z / z₀) / z₀) ^ m * canonicalProductOne b z
  have hfac : ∀ z, canonicalProductOne a z = (z - z₀) ^ m • g z := by
    intro z
    have hprod : ∏ i ∈ S, weierstrassFactorOne (z / a i) = weierstrassFactorOne (z / z₀) ^ m := by
      calc ∏ i ∈ S, weierstrassFactorOne (z / a i) = ∏ _i ∈ S, weierstrassFactorOne (z / z₀) :=
            Finset.prod_congr rfl fun i hi ↦ by rw [(hS i).mp hi]
        _ = weierstrassFactorOne (z / z₀) ^ m := Finset.prod_const _
    have hsplit : (∏' x : (S : Set ι), weierstrassFactorOne (z / a x)) *
        ∏' x : ↥((S : Set ι)ᶜ), weierstrassFactorOne (z / a x) =
        ∏' i, weierstrassFactorOne (z / a i) :=
      Multipliable.tprod_mul_tprod_compl (f := fun i ↦ weierstrassFactorOne (z / a i))
        (S.multipliable (fun i ↦ weierstrassFactorOne (z / a i)))
        (multipliable_canonicalProductOne hb z)
    rw [Finset.tprod_subtype' S (fun i ↦ weierstrassFactorOne (z / a i))] at hsplit
    rw [hprod, weierstrassFactorOne_div_eq hz₀] at hsplit
    rw [canonicalProductOne, ← hsplit]
    have hb' : canonicalProductOne b z = ∏' x : ↥((S : Set ι)ᶜ), weierstrassFactorOne (z / a x) :=
      rfl
    simp only [g, smul_eq_mul, hb', mul_pow]
    ring
  rw [(hP.analyticAt z₀).analyticOrderAt_eq_natCast]
  refine ⟨g, ?_, ?_, Eventually.of_forall hfac⟩
  · exact ((by fun_prop : Differentiable ℂ fun z ↦ (-Complex.exp (z / z₀) / z₀) ^ m).mul
      hQ).analyticAt z₀
  · simp only [g]
    exact mul_ne_zero (pow_ne_zero _ (div_ne_zero (neg_ne_zero.mpr (Complex.exp_ne_zero _)) hz₀))
      hQz₀

end NTKB
