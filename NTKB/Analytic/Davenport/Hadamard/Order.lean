/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Basic.ENNReal.Inv
import NTKB.Attr

/-!
# The order of an entire function (Davenport, Chapter 11)

Davenport, *Multiplicative Number Theory*, Chapter 11, p. 74: an entire function `f` is of finite
order if `f(z) = O(e^{|z|^a})` as `|z| → ∞` for some `a`; the lower bound of such `a` is the order.

## Main definitions

* `NTKB.entireOrder f : ℝ≥0∞`: the infimum of the exponents `a ≥ 0` with
  `f =O[cobounded ℂ] (fun z ↦ exp (‖z‖ ^ a))` (`⊤` if there is none).

For a nonconstant entire function every admissible exponent is positive (Davenport's remark), so
restricting to `a ≥ 0` changes nothing; a constant function has order `0` here.

## Main results

* `NTKB.entireOrder_le_iff`: `entireOrder f ≤ ρ` iff `f = O(exp (‖z‖ ^ a))` for every `a > ρ`.
* `NTKB.entireOrder_le_iff_eventually`: equivalently, `‖f z‖ ≤ exp (‖z‖ ^ a)` for all large `‖z‖`,
  for every `a > ρ` (the form used by Davenport).
* `NTKB.entireOrder_exp_polynomial_le`: `exp ∘ P` has order at most the degree of `P`.

No such definition exists in Mathlib (the coverage audit found only order-at-most predicates in
other libraries).
-/

open Filter Asymptotics Bornology Topology
open scoped ENNReal NNReal

namespace NTKB

/-- **Order of an entire function** (Davenport, Ch. 11, p. 74): the infimum of the exponents
`a ≥ 0` with `f(z) = O(exp (|z|^a))` as `|z| → ∞`; `⊤` if `f` is not of finite order. -/
noncomputable def entireOrder (f : ℂ → ℂ) : ℝ≥0∞ :=
  ⨅ (a : ℝ≥0) (_ : f =O[cobounded ℂ] fun z ↦ Real.exp (‖z‖ ^ (a : ℝ))), (a : ℝ≥0∞)

/-- An elementary real inequality: if `b < a` and `0 ≤ b`, then `K r^b + C ≤ r^a` for large `r`. -/
lemma eventually_mul_rpow_add_le_rpow {a b : ℝ} (hb : 0 ≤ b) (hab : b < a) (K C : ℝ) :
    ∀ᶠ r : ℝ in atTop, K * r ^ b + C ≤ r ^ a := by
  have h1 : Tendsto (fun r : ℝ ↦ r ^ (a - b)) atTop atTop := tendsto_rpow_atTop (by linarith)
  filter_upwards [h1.eventually_ge_atTop (|K| + |C| + 1), eventually_ge_atTop (1 : ℝ)]
    with r hr hr1
  have hrb : 1 ≤ r ^ b := Real.one_le_rpow hr1 hb
  have hsplit : r ^ a = r ^ b * r ^ (a - b) := by
    rw [← Real.rpow_add (by linarith)]; ring_nf
  rw [hsplit]
  calc K * r ^ b + C ≤ |K| * r ^ b + |C| * r ^ b := by
        gcongr
        · exact le_abs_self K
        · exact (le_abs_self C).trans (le_mul_of_one_le_right (abs_nonneg C) hrb)
    _ ≤ r ^ b * (|K| + |C| + 1) := by nlinarith [abs_nonneg K, abs_nonneg C]
    _ ≤ r ^ b * r ^ (a - b) := by gcongr

/-- `exp (‖z‖^b) = O(exp (‖z‖^a))` for `b ≤ a`. -/
lemma isBigO_exp_rpow_of_le {a b : ℝ} (hab : b ≤ a) :
    (fun z : ℂ ↦ Real.exp (‖z‖ ^ b)) =O[cobounded ℂ] fun z ↦ Real.exp (‖z‖ ^ a) := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards [eventually_cobounded_le_norm (1 : ℝ)] with z hz
  simp only [Real.norm_eq_abs, Real.abs_exp, one_mul]
  exact Real.exp_le_exp.mpr (Real.rpow_le_rpow_of_exponent_le hz hab)

/-- If `f` has order at most `ρ` then `f = O(exp (‖z‖^a))` for every `a > ρ`. -/
lemma isBigO_of_entireOrder_le {f : ℂ → ℂ} {ρ : ℝ≥0} (hf : entireOrder f ≤ ρ) {a : ℝ}
    (ha : (ρ : ℝ) < a) : f =O[cobounded ℂ] fun z ↦ Real.exp (‖z‖ ^ a) := by
  have ha0 : 0 < a := lt_of_le_of_lt ρ.2 ha
  set a' : ℝ≥0 := ⟨a, ha0.le⟩ with ha'
  have hlt : entireOrder f < (a' : ℝ≥0∞) := by
    refine lt_of_le_of_lt hf ?_
    exact_mod_cast (show ρ < a' from ha)
  unfold entireOrder at hlt
  simp only [iInf_lt_iff] at hlt
  obtain ⟨b, hb, hba⟩ := hlt
  have hba' : (b : ℝ) ≤ a := by
    have : b < a' := by exact_mod_cast hba
    exact this.le
  exact hb.trans (isBigO_exp_rpow_of_le hba')

/-- `entireOrder f ≤ a` as soon as `f = O(exp (‖z‖^a))`. -/
lemma entireOrder_le_of_isBigO {f : ℂ → ℂ} {a : ℝ≥0}
    (h : f =O[cobounded ℂ] fun z ↦ Real.exp (‖z‖ ^ (a : ℝ))) : entireOrder f ≤ a :=
  iInf₂_le a h

/-- **Characterisation of the order**: `entireOrder f ≤ ρ` iff `f = O(exp (‖z‖^a))` for every
`a > ρ`. -/
theorem entireOrder_le_iff {f : ℂ → ℂ} {ρ : ℝ≥0} :
    entireOrder f ≤ ρ ↔ ∀ a : ℝ, (ρ : ℝ) < a → f =O[cobounded ℂ] fun z ↦ Real.exp (‖z‖ ^ a) := by
  refine ⟨fun hf a ha ↦ isBigO_of_entireOrder_le hf ha, fun h ↦ ?_⟩
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ ↦ ?_
  have := entireOrder_le_of_isBigO (a := ρ + ε) (h _ (by simp [hε]))
  simpa using this

/-- If `f` has order at most `ρ`, then for every `a > ρ`, `‖f z‖ ≤ exp (‖z‖^a)` for all
sufficiently large `‖z‖` (Davenport's form `log |f(Re^{iθ})| < R^a`). -/
theorem eventually_norm_le_exp_of_entireOrder_le {f : ℂ → ℂ} {ρ : ℝ≥0} (hf : entireOrder f ≤ ρ)
    {a : ℝ} (ha : (ρ : ℝ) < a) : ∀ᶠ z in cobounded ℂ, ‖f z‖ ≤ Real.exp (‖z‖ ^ a) := by
  set b := ((ρ : ℝ) + a) / 2
  have hρb : (ρ : ℝ) < b := by simp only [b]; linarith
  have hba : b < a := by simp only [b]; linarith
  have hb0 : 0 ≤ b := le_trans ρ.2 hρb.le
  obtain ⟨c, hc⟩ := (isBigO_of_entireOrder_le hf hρb).bound
  have hev : ∀ᶠ r : ℝ in atTop, 1 * r ^ b + Real.log (max c 1) ≤ r ^ a :=
    eventually_mul_rpow_add_le_rpow hb0 hba 1 _
  have hev' : ∀ᶠ z in cobounded ℂ, 1 * ‖z‖ ^ b + Real.log (max c 1) ≤ ‖z‖ ^ a :=
    tendsto_norm_cobounded_atTop.eventually hev
  filter_upwards [hc, hev'] with z hz hz'
  simp only [Real.norm_eq_abs, Real.abs_exp, one_mul] at hz hz'
  calc ‖f z‖ ≤ c * Real.exp (‖z‖ ^ b) := hz
    _ ≤ max c 1 * Real.exp (‖z‖ ^ b) := by gcongr; exact le_max_left _ _
    _ = Real.exp (Real.log (max c 1) + ‖z‖ ^ b) := by
        rw [Real.exp_add, Real.exp_log (by positivity)]
    _ ≤ Real.exp (‖z‖ ^ a) := Real.exp_le_exp.mpr (by linarith)

/-- Converse of `eventually_norm_le_exp_of_entireOrder_le`. -/
theorem entireOrder_le_of_eventually {f : ℂ → ℂ} {ρ : ℝ≥0}
    (h : ∀ a : ℝ, (ρ : ℝ) < a → ∀ᶠ z in cobounded ℂ, ‖f z‖ ≤ Real.exp (‖z‖ ^ a)) :
    entireOrder f ≤ ρ :=
  entireOrder_le_iff.mpr fun a ha ↦ IsBigO.of_bound 1 <| (h a ha).mono fun z hz ↦ by
    simpa [Real.abs_exp] using hz

/-- `entireOrder f ≤ ρ` iff `‖f z‖ ≤ exp (‖z‖^a)` eventually, for every `a > ρ`. -/
theorem entireOrder_le_iff_eventually {f : ℂ → ℂ} {ρ : ℝ≥0} :
    entireOrder f ≤ ρ ↔
      ∀ a : ℝ, (ρ : ℝ) < a → ∀ᶠ z in cobounded ℂ, ‖f z‖ ≤ Real.exp (‖z‖ ^ a) :=
  ⟨fun hf _ ha ↦ eventually_norm_le_exp_of_entireOrder_le hf ha, entireOrder_le_of_eventually⟩

/-- The order of `exp ∘ P` is at most the degree of the polynomial `P`. -/
theorem entireOrder_exp_polynomial_le (P : Polynomial ℂ) :
    entireOrder (fun z ↦ Complex.exp (P.eval z)) ≤ P.natDegree := by
  have key := entireOrder_le_of_eventually (f := fun z ↦ Complex.exp (P.eval z))
    (ρ := (P.natDegree : ℝ≥0)) fun a ha ↦ by
    obtain ⟨K, hK⟩ := P.isBigO_cobounded_pow_natDegree.bound
    have hev : ∀ᶠ r : ℝ in atTop, K * r ^ (P.natDegree : ℝ) + 0 ≤ r ^ a :=
      eventually_mul_rpow_add_le_rpow (Nat.cast_nonneg _) (by simpa using ha) K 0
    filter_upwards [hK, tendsto_norm_cobounded_atTop.eventually hev] with z hz hz'
    rw [Complex.norm_exp]
    refine Real.exp_le_exp.mpr ((Complex.re_le_norm _).trans ?_)
    simp only [norm_pow, Real.rpow_natCast, add_zero] at hz hz'
    linarith
  simpa using key

end NTKB
