/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Topology.Algebra.InfiniteSum.Real
import NTKB.Analytic.Davenport.Hadamard.Order

/-!
# Density of the zeros of an entire function of finite order (Davenport, Chapter 11, p. 75–76)

## Main definitions

* `NTKB.ZeroIndex f`: the zeros of `f`, repeated according to multiplicity (Davenport's sequence
  `z₁, z₂, …`): the type `Σ z : ℂ, Fin (analyticOrderNatAt f z)`, with `ZeroIndex.val i = i.1`.
* `NTKB.zeroCount f r`: the number of zeros (with multiplicity) in `|z| < r`, Davenport's `n(r)`.

## Main results

* `NTKB.card_le_of_jensen`: Jensen's inequality (Mathlib's `AnalyticOnNhd.sum_divisor_le`) counted
  over `ZeroIndex f`.
* `NTKB.Davenport.zeroCount_isBigO` (row 11-6): if `f` has order `≤ ρ` and `f(0) ≠ 0`, then
  `n(R) = O(R^a)` for every `a > ρ`.
* `NTKB.Davenport.summable_norm_zero_rpow_neg` (row 11-7): `∑ |z_n|^{-β}` converges for `β > ρ`.

Davenport derives `n(R) = O(R^a)` from Jensen's formula with the radii `R` and `2R`; this is exactly
Mathlib's Jensen inequality `AnalyticOnNhd.sum_divisor_le`. The convergence of `∑ r_n^{-β}` is
proved by grouping the zeros in dyadic shells `2^k r₀ ≤ |z| < 2^{k+1} r₀` (Davenport's displayed
partial summation is the integral form of the same estimate).
-/

open Filter Topology Metric Complex
open scoped ENNReal NNReal

namespace NTKB

/-- The zeros of `f` repeated according to multiplicity: an element is a point `z` together with an
index `< analyticOrderNatAt f z`. (Points where `f` vanishes identically contribute nothing.) -/
abbrev ZeroIndex (f : ℂ → ℂ) : Type := Σ z : ℂ, Fin (analyticOrderNatAt f z)

namespace ZeroIndex

variable {f : ℂ → ℂ}

/-- The zero of `f` attached to an index. -/
def val (i : ZeroIndex f) : ℂ := i.1

lemma analyticOrderNatAt_val_pos (i : ZeroIndex f) : 0 < analyticOrderNatAt f i.val :=
  Fin.pos i.2

/-- Each index is a zero of `f` (for `f` analytic). -/
lemma apply_val_eq_zero {i : ZeroIndex f} (hf : AnalyticAt ℂ f i.val) : f i.val = 0 := by
  have h := analyticOrderNatAt_val_pos i
  by_contra hne
  have : analyticOrderAt f i.val = 0 := hf.analyticOrderAt_eq_zero.mpr hne
  simp [analyticOrderNatAt, this] at h

/-- No index sits at a point where `f` does not vanish. -/
lemma val_ne_of_ne_zero {i : ZeroIndex f} (hf : AnalyticAt ℂ f i.val) {z : ℂ} (hz : f z ≠ 0) : i.val ≠ z := by
  rintro rfl
  exact hz (apply_val_eq_zero hf)

end ZeroIndex

/-- Davenport's `n(r)`: the number of zeros of `f` (with multiplicity) in `|z| < r`. -/
noncomputable def zeroCount (f : ℂ → ℂ) (r : ℝ) : ℕ := Nat.card {i : ZeroIndex f // ‖i.val‖ < r}

/-- On a set where `f` is analytic, the divisor of `f` is the order of vanishing. -/
lemma divisor_eq_analyticOrderNatAt {f : ℂ → ℂ} {U : Set ℂ} (hf : AnalyticOnNhd ℂ f U) {z : ℂ}
    (hz : z ∈ U) : MeromorphicOn.divisor f U z = analyticOrderNatAt f z := by
  rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hf hz, analyticOrderNatAt]
  cases h : analyticOrderAt f z with
  | top => simp
  | coe n => simp

/-- The zeros of an entire function in a closed disc are finitely many. -/
lemma finite_zeroIndex_closedBall {f : ℂ → ℂ} (hf : Differentiable ℂ f) (r : ℝ) :
    Finite {i : ZeroIndex f // ‖i.val‖ ≤ r} := by
  have han : AnalyticOnNhd ℂ f (closedBall 0 r) := fun z _ ↦ hf.analyticAt z
  have hfin := (MeromorphicOn.divisor f (closedBall (0 : ℂ) r)).finiteSupport
    (isCompact_closedBall 0 r)
  have : Finite (MeromorphicOn.divisor f (closedBall (0 : ℂ) r)).support := hfin.to_subtype
  -- inject into `Σ z ∈ support, Fin (order z)`
  let g : {i : ZeroIndex f // ‖i.val‖ ≤ r} →
      Σ z : (MeromorphicOn.divisor f (closedBall (0 : ℂ) r)).support,
        Fin (analyticOrderNatAt f z) := fun i ↦
    ⟨⟨i.1.1, by
      have hmem : i.1.1 ∈ closedBall (0 : ℂ) r := by simpa [ZeroIndex.val] using i.2
      rw [Function.mem_support, divisor_eq_analyticOrderNatAt han hmem]
      exact_mod_cast (ZeroIndex.analyticOrderNatAt_val_pos i.1).ne'⟩, i.1.2⟩
  refine Finite.of_injective g fun i j hij ↦ ?_
  simp only [g, Sigma.mk.injEq, Subtype.mk.injEq] at hij
  obtain ⟨h1, h2⟩ := hij
  apply Subtype.ext
  apply Sigma.ext h1 h2

lemma finite_zeroIndex_ball {f : ℂ → ℂ} (hf : Differentiable ℂ f) (r : ℝ) :
    Finite {i : ZeroIndex f // ‖i.val‖ < r} := by
  have := finite_zeroIndex_closedBall hf r
  exact Finite.of_injective (fun i : {i : ZeroIndex f // ‖i.val‖ < r} ↦
    (⟨i.1, i.2.le⟩ : {i : ZeroIndex f // ‖i.val‖ ≤ r})) fun i j h ↦ by
      simpa [Subtype.ext_iff] using h

/-- The zeros of an entire function form a countable family. -/
instance countable_zeroIndex {f : ℂ → ℂ} [Fact (Differentiable ℂ f)] : Countable (ZeroIndex f) := by
  have hf : Differentiable ℂ f := Fact.out
  have : (Set.univ : Set (ZeroIndex f)) = ⋃ n : ℕ, {i | ‖i.val‖ ≤ n} := by
    ext i
    simp only [Set.mem_univ, Set.mem_iUnion, Set.mem_ofPred_eq, true_iff]
    obtain ⟨n, hn⟩ := exists_nat_ge ‖i.val‖
    exact ⟨n, hn⟩
  have hc : (Set.univ : Set (ZeroIndex f)).Countable := by
    rw [this]
    refine Set.countable_iUnion fun n ↦ ?_
    have := finite_zeroIndex_closedBall hf n
    exact (Set.toFinite {i : ZeroIndex f | ‖i.val‖ ≤ n}).countable
  exact Set.countable_univ_iff.mp hc

/-- A finite set of zeros in `|z| ≤ r` has at most as many elements as the divisor of `f` on the
closed disc has mass. -/
lemma card_le_finsum_divisor {f : ℂ → ℂ} (hf : Differentiable ℂ f) {r : ℝ} (s : Finset (ZeroIndex f))
    (hs : ∀ i ∈ s, ‖i.val‖ ≤ r) :
    (s.card : ℝ) ≤ ∑ᶠ u, (MeromorphicOn.divisor f (closedBall (0 : ℂ) r) u : ℝ) := by
  classical
  have han : AnalyticOnNhd ℂ f (closedBall 0 r) := fun z _ ↦ hf.analyticAt z
  set D := MeromorphicOn.divisor f (closedBall (0 : ℂ) r)
  have hfin : D.support.Finite := D.finiteSupport (isCompact_closedBall 0 r)
  set T := s.image Sigma.fst
  -- each fibre of `Sigma.fst` on `s` has at most `order` elements
  have hfib : ∀ u ∈ T, ((s.filter (fun i ↦ i.1 = u)).card : ℝ) ≤ D u := by
    intro u hu
    obtain ⟨i, his, rfl⟩ := Finset.mem_image.mp hu
    have hmem : i.1 ∈ closedBall (0 : ℂ) r := by simpa [ZeroIndex.val] using hs i his
    rw [divisor_eq_analyticOrderNatAt han hmem]
    have : (s.filter (fun j ↦ j.1 = i.1)).card ≤ analyticOrderNatAt f i.1 := by
      have hinj : Set.InjOn (fun j : ZeroIndex f ↦ (j.2 : ℕ))
          (s.filter (fun j ↦ j.1 = i.1) : Set (ZeroIndex f)) := by
        intro j hj k hk hjk
        simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hj hk
        have h1 : j.1 = k.1 := hj.2.trans hk.2.symm
        apply Sigma.ext h1
        have : (j.2 : ℕ) = k.2 := hjk
        exact (Fin.heq_ext_iff (by rw [h1])).mpr this
      have := Finset.card_le_card_of_injOn (fun j : ZeroIndex f ↦ (j.2 : ℕ))
        (t := Finset.range (analyticOrderNatAt f i.1)) (fun j hj ↦ by
          simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hj
          have := j.2.2
          simp only [Finset.coe_range, Set.mem_Iio]
          rw [← hj.2]; exact this) hinj
      simpa using this
    exact_mod_cast this
  calc (s.card : ℝ) = ∑ u ∈ T, ((s.filter (fun i ↦ i.1 = u)).card : ℝ) := by
        rw [← Nat.cast_sum, Finset.card_eq_sum_card_image Sigma.fst s]
    _ ≤ ∑ u ∈ T, (D u : ℝ) := Finset.sum_le_sum hfib
    _ ≤ ∑ u ∈ hfin.toFinset ∪ T, (D u : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_right fun u _ _ ↦ by
          exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg han u
    _ = ∑ᶠ u, (D u : ℝ) := by
        rw [finsum_eq_sum_of_support_subset]
        intro u hu
        simp only [Function.mem_support, ne_eq, Int.cast_eq_zero] at hu
        simp [hu]

/-- **Jensen's inequality, counted over `ZeroIndex`.** If `‖f‖ ≤ M` on `|z| = R` and `0 < r < R`,
then the number of zeros in `|z| ≤ r` is at most `log (M / |f 0|) / log (R / r)`. -/
theorem card_le_of_jensen {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hf0 : f 0 ≠ 0) {r R M : ℝ}
    (hr : 0 < r) (hrR : r < R) (hM : 1 ≤ M) (hbound : ∀ z, ‖z‖ = R → ‖f z‖ ≤ M)
    (s : Finset (ZeroIndex f)) (hs : ∀ i ∈ s, ‖i.val‖ ≤ r) :
    (s.card : ℝ) ≤ Real.log (M / ‖f 0‖) / Real.log (R / r) := by
  have h1 := card_le_finsum_divisor hf s hs
  have hR : 0 < R := hr.trans hrR
  have hJ := AnalyticOnNhd.sum_divisor_le (c := 0) (r := r) (R := R) (M := M)
    (by simpa [abs_of_pos hr] using hr) (by rwa [abs_of_pos hr, abs_of_pos hR])
    hM (fun z _ ↦ hf.analyticAt z) hf0 (fun z hz ↦ hbound z (by simpa [abs_of_pos hR] using hz))
  rw [abs_of_pos hr] at hJ
  have hcast : (∑ᶠ u, (MeromorphicOn.divisor f (closedBall (0 : ℂ) r) u : ℝ)) =
      ((∑ᶠ u, MeromorphicOn.divisor f (closedBall (0 : ℂ) r) u : ℤ) : ℝ) :=
    (map_finsum (Int.castRingHom ℝ)
      ((MeromorphicOn.divisor f _).finiteSupport (isCompact_closedBall _ _))).symm
  rw [hcast] at h1
  exact h1.trans hJ

/-- **Davenport, Ch. 11, p. 75 (C) (row 11-6)**, finite-set form: if `f` has order at most `ρ`,
`f(0) ≠ 0` and `a > ρ`, then there is `C` with `#{zeros in |z| ≤ r} ≤ C r^a` for all `r ≥ 1`. -/
theorem exists_card_le_rpow {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hf0 : f 0 ≠ 0) {ρ : ℝ≥0}
    (hord : entireOrder f ≤ ρ) {a : ℝ} (ha : (ρ : ℝ) < a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 1 ≤ r → ∀ s : Finset (ZeroIndex f), (∀ i ∈ s, ‖i.val‖ ≤ r) →
      (s.card : ℝ) ≤ C * r ^ a := by
  have ha0 : 0 < a := lt_of_le_of_lt ρ.2 ha
  have hev := eventually_norm_le_exp_of_entireOrder_le hord ha
  obtain ⟨R₀, hR₀⟩ := (Metric.hasBasis_cobounded_compl_closedBall (0 : ℂ)).eventually_iff.mp hev
    |>.imp fun r hr ↦ hr.2
  set R₁ := max R₀ 1
  have hR₁ : 1 ≤ R₁ := le_max_right _ _
  set L := |Real.log ‖f 0‖|
  -- the bound at radius `r ≥ R₁`: `card ≤ ((2r)^a + L) / log 2`
  have hbig : ∀ r : ℝ, R₁ ≤ r → ∀ s : Finset (ZeroIndex f), (∀ i ∈ s, ‖i.val‖ ≤ r) →
      (s.card : ℝ) ≤ ((2 * r) ^ a + L) / Real.log 2 := by
    intro r hr s hs
    have hr1 : 1 ≤ r := hR₁.trans hr
    have hr0 : 0 < r := by linarith
    have hb : ∀ z : ℂ, ‖z‖ = 2 * r → ‖f z‖ ≤ Real.exp ((2 * r) ^ a) := by
      intro z hz
      have : z ∈ (closedBall (0 : ℂ) R₀)ᶜ := by
        simp only [Set.mem_compl_iff, mem_closedBall, dist_zero_right, not_le, hz]
        linarith [le_max_left R₀ 1]
      simpa [hz] using hR₀ this
    have hJ := card_le_of_jensen hf hf0 hr0 (by linarith) (Real.one_le_exp (by positivity)) hb s hs
    have h2 : 2 * r / r = 2 := by field_simp
    rw [h2, Real.log_div (Real.exp_pos _).ne' (norm_ne_zero_iff.mpr hf0), Real.log_exp] at hJ
    exact hJ.trans (div_le_div_of_nonneg_right (by linarith [neg_le_abs (Real.log ‖f 0‖)])
      (Real.log_pos (by norm_num)).le)
  set C := (2 ^ a + L) / Real.log 2 * R₁ ^ a
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨C, by positivity, fun r hr s hs ↦ ?_⟩
  have hr0 : 0 < r := by linarith
  have hra : 1 ≤ r ^ a := Real.one_le_rpow hr ha0.le
  have hR₁a : 1 ≤ R₁ ^ a := Real.one_le_rpow hR₁ ha0.le
  -- reduce to radius `max r R₁`
  set r' := max r R₁
  have hs' : ∀ i ∈ s, ‖i.val‖ ≤ r' := fun i hi ↦ (hs i hi).trans (le_max_left _ _)
  have h := hbig r' (le_max_right _ _) s hs'
  refine h.trans ?_
  have hr'0 : 0 < r' := lt_of_lt_of_le hr0 (le_max_left _ _)
  have hr'a : r' ^ a ≤ r ^ a * R₁ ^ a := by
    rw [← Real.mul_rpow hr0.le (by linarith)]
    refine Real.rpow_le_rpow hr'0.le ?_ ha0.le
    rcases le_total r R₁ with h | h
    · simp only [r', max_eq_right h]; nlinarith
    · simp only [r', max_eq_left h]; nlinarith
  have h2a : (2 * r') ^ a = 2 ^ a * r' ^ a := Real.mul_rpow (by norm_num) hr'0.le
  have hL : 0 ≤ L := abs_nonneg _
  have hprod : 1 ≤ R₁ ^ a * r ^ a := one_le_mul_of_one_le_of_one_le hR₁a hra
  have hnum : (2 * r') ^ a + L ≤ (2 ^ a + L) * (R₁ ^ a * r ^ a) := by
    rw [h2a]
    have h1 : 2 ^ a * r' ^ a ≤ 2 ^ a * (R₁ ^ a * r ^ a) := by
      gcongr; linarith [hr'a]
    have h2 : L ≤ L * (R₁ ^ a * r ^ a) := le_mul_of_one_le_right hL hprod
    nlinarith
  calc ((2 * r') ^ a + L) / Real.log 2 ≤ (2 ^ a + L) * (R₁ ^ a * r ^ a) / Real.log 2 := by
        gcongr
    _ = C * r ^ a := by simp only [C]; ring

/-- **Davenport, Ch. 11, p. 75 (C) (row 11-6).** If `f` has order at most `ρ` and `f(0) ≠ 0`, then
`n(R) = O(R^a)` for every `a > ρ`. -/
@[kb "davenport1980" "Ch 11, p. 75"]
theorem Davenport.zeroCount_isBigO {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hf0 : f 0 ≠ 0)
    {ρ : ℝ≥0} (hord : entireOrder f ≤ ρ) {a : ℝ} (ha : (ρ : ℝ) < a) :
    (fun R : ℝ ↦ (zeroCount f R : ℝ)) =O[atTop] fun R ↦ R ^ a := by
  obtain ⟨C, hC, hcard⟩ := exists_card_le_rpow hf hf0 hord ha
  refine Asymptotics.IsBigO.of_bound C ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
  have := finite_zeroIndex_ball hf R
  have := Fintype.ofFinite {i : ZeroIndex f // ‖i.val‖ < R}
  have hcount : (zeroCount f R : ℝ) =
      ((Finset.univ : Finset {i : ZeroIndex f // ‖i.val‖ < R}).map
        (Function.Embedding.subtype _)).card := by
    simp [zeroCount, Nat.card_eq_fintype_card]
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity), hcount]
  exact hcard R hR _ fun i hi ↦ by
    obtain ⟨j, -, rfl⟩ := Finset.mem_map.mp hi
    exact j.2.le

/-- Summability from a polynomial bound on counts: if `a i ≥ r₀ > 0` and every finite set of
indices with `a i ≤ r` has at most `A r^α` elements (`r ≥ r₀`), then `∑ (a i)^{-β}` converges for
`β > α ≥ 0`. -/
lemma summable_rpow_neg_of_card_le {ι : Type*} (a : ι → ℝ) {r₀ α β A : ℝ} (hr₀ : 0 < r₀)
    (ha : ∀ i, r₀ ≤ a i) (hα : 0 ≤ α) (hαβ : α < β) (hA : 0 ≤ A)
    (hcard : ∀ r : ℝ, r₀ ≤ r → ∀ s : Finset ι, (∀ i ∈ s, a i ≤ r) → (s.card : ℝ) ≤ A * r ^ α) :
    Summable fun i ↦ (a i) ^ (-β) := by
  classical
  have hβ : 0 < β := hα.trans_lt hαβ
  -- the dyadic shell of an index
  let k : ι → ℕ := fun i ↦ ⌊Real.logb 2 (a i / r₀)⌋₊
  have hx1 : ∀ i, 1 ≤ a i / r₀ := fun i ↦ (one_le_div hr₀).mpr (ha i)
  have hlow : ∀ i, (2 : ℝ) ^ (k i) * r₀ ≤ a i := by
    intro i
    have hlog : (k i : ℝ) ≤ Real.logb 2 (a i / r₀) :=
      Nat.floor_le (Real.logb_nonneg (by norm_num) (hx1 i))
    have : (2 : ℝ) ^ (k i : ℝ) ≤ a i / r₀ := by
      calc (2 : ℝ) ^ (k i : ℝ) ≤ 2 ^ Real.logb 2 (a i / r₀) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) hlog
        _ = a i / r₀ := Real.rpow_logb (by norm_num) (by norm_num) (by linarith [hx1 i])
    rw [Real.rpow_natCast] at this
    rwa [le_div_iff₀ hr₀] at this
  have hupp : ∀ i, a i ≤ (2 : ℝ) ^ (k i + 1) * r₀ := by
    intro i
    have hlog : Real.logb 2 (a i / r₀) < (k i : ℝ) + 1 := Nat.lt_floor_add_one _
    have : a i / r₀ < (2 : ℝ) ^ ((k i : ℝ) + 1) := by
      rw [← Real.logb_lt_iff_lt_rpow (by norm_num) (by linarith [hx1 i])]
      exact hlog
    rw [show ((k i : ℝ) + 1) = ((k i + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast] at this
    rw [div_lt_iff₀ hr₀] at this
    exact this.le
  -- the dominating geometric series
  have haux : ∀ (n : ℕ) (x : ℝ), ((2 : ℝ) ^ n * r₀) ^ x = ((2 : ℝ) ^ x) ^ n * r₀ ^ x := by
    intro n x
    rw [Real.mul_rpow (by positivity) hr₀.le]
    congr 1
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm, Real.rpow_mul (by norm_num),
      Real.rpow_natCast]
  set q : ℝ := (2 : ℝ) ^ α * (2 : ℝ) ^ (-β)
  have hq : q = (2 : ℝ) ^ (α - β) := by
    simp only [q]; rw [← Real.rpow_add (by norm_num)]; ring_nf
  have hq0 : 0 < q := by positivity
  have hq1 : q < 1 := by
    rw [hq]; exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  set c : ℕ → ℝ := fun n ↦ A * 2 ^ α * r₀ ^ α * r₀ ^ (-β) * q ^ n
  have hc : Summable c := (summable_geometric_of_lt_one hq0.le hq1).mul_left _
  have hshell : ∀ n : ℕ, ∀ s : Finset ι, (∀ i ∈ s, k i = n) →
      ∑ i ∈ s, (a i) ^ (-β) ≤ c n := by
    intro n s hs
    have hcardn : (s.card : ℝ) ≤ A * ((2 : ℝ) ^ (n + 1) * r₀) ^ α := by
      refine hcard _ ?_ s fun i hi ↦ (hupp i).trans (by rw [hs i hi])
      have : (1 : ℝ) ≤ 2 ^ (n + 1) := one_le_pow₀ (by norm_num)
      nlinarith
    have hterm : ∀ i ∈ s, (a i) ^ (-β) ≤ ((2 : ℝ) ^ n * r₀) ^ (-β) := by
      intro i hi
      refine Real.rpow_le_rpow_of_nonpos (by positivity) ?_ (by linarith)
      have := hlow i; rwa [hs i hi] at this
    calc ∑ i ∈ s, (a i) ^ (-β) ≤ ∑ i ∈ s, ((2 : ℝ) ^ n * r₀) ^ (-β) := Finset.sum_le_sum hterm
      _ = s.card * ((2 : ℝ) ^ n * r₀) ^ (-β) := by simp
      _ ≤ A * ((2 : ℝ) ^ (n + 1) * r₀) ^ α * ((2 : ℝ) ^ n * r₀) ^ (-β) := by gcongr
      _ = c n := by
          simp only [c, q]
          rw [haux, haux, mul_pow, pow_succ]
          ring
  refine summable_of_sum_le (c := ∑' n, c n) (fun i ↦ Real.rpow_nonneg (by linarith [ha i]) _)
    fun s ↦ ?_
  rw [← Finset.sum_fiberwise_of_maps_to (g := k) (t := s.image k) fun i hi ↦
    Finset.mem_image_of_mem k hi]
  calc ∑ n ∈ s.image k, ∑ i ∈ s with k i = n, (a i) ^ (-β) ≤ ∑ n ∈ s.image k, c n :=
        Finset.sum_le_sum fun n _ ↦ hshell n _ fun i hi ↦ (Finset.mem_filter.mp hi).2
    _ ≤ ∑' n, c n := hc.sum_le_tsum _ fun n _ ↦ by simp only [c]; positivity

/-- If `f(0) ≠ 0`, the zeros of `f` stay away from `0`. -/
lemma exists_pos_le_norm_val {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hf0 : f 0 ≠ 0) :
    ∃ r₀ > 0, ∀ i : ZeroIndex f, r₀ ≤ ‖i.val‖ := by
  have hc : ContinuousAt f 0 := hf.continuous.continuousAt
  obtain ⟨ε, hε, hεf⟩ := Metric.eventually_nhds_iff.mp
    (hc.eventually (isOpen_ne.mem_nhds hf0))
  refine ⟨ε, hε, fun i ↦ ?_⟩
  by_contra hlt
  push Not at hlt
  have := hεf (y := i.val) (by simpa using hlt)
  exact this (ZeroIndex.apply_val_eq_zero (hf.analyticAt _))

/-- **Davenport, Ch. 11, p. 76 (row 11-7).** If `f` has order at most `ρ` and `f(0) ≠ 0`, then
`∑ r_n^{-β}` converges for every `β > ρ`, where `r_n = |z_n|` runs over the zeros of `f`
(with multiplicity). For order `1`: `∑ r_n^{-1-ε}` converges for every `ε > 0`. -/
@[kb "davenport1980" "Ch 11, p. 76"]
theorem Davenport.summable_norm_zero_rpow_neg {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hf0 : f 0 ≠ 0) {ρ : ℝ≥0} (hord : entireOrder f ≤ ρ) {β : ℝ} (hβ : (ρ : ℝ) < β) :
    Summable fun i : ZeroIndex f ↦ ‖i.val‖ ^ (-β) := by
  set α := ((ρ : ℝ) + β) / 2
  have hα : (ρ : ℝ) < α := by simp only [α]; linarith
  have hαβ : α < β := by simp only [α]; linarith
  obtain ⟨C, hC, hcard⟩ := exists_card_le_rpow hf hf0 hord hα
  obtain ⟨r₀, hr₀, hr₀le⟩ := exists_pos_le_norm_val hf hf0
  set r₁ := min r₀ 1
  have hr₁ : 0 < r₁ := lt_min hr₀ one_pos
  have hlow : ∀ i : ZeroIndex f, r₁ ≤ ‖i.val‖ := fun i ↦ (min_le_left _ _).trans (hr₀le i)
  have hα0 : (0 : ℝ) ≤ α := ρ.2.trans hα.le
  have hA : (0 : ℝ) ≤ C * r₁⁻¹ ^ α := mul_nonneg hC (Real.rpow_nonneg (inv_nonneg.mpr hr₁.le) _)
  refine summable_rpow_neg_of_card_le (fun i : ZeroIndex f ↦ ‖i.val‖) hr₁ hlow hα0 hαβ hA
    fun r hr s hs ↦ ?_
  -- for `r ≥ r₁`, compare with the radius `r / r₁ ≥ 1`
  have hr0 : 0 < r := lt_of_lt_of_le hr₁ hr
  have hrr : 1 ≤ r / r₁ := (one_le_div hr₁).mpr hr
  have h := hcard (r / r₁) hrr s fun i hi ↦ (hs i hi).trans (by
    rw [le_div_iff₀ hr₁]
    exact mul_le_of_le_one_right hr0.le (min_le_right _ _))
  refine h.trans (le_of_eq ?_)
  rw [div_eq_mul_inv, Real.mul_rpow hr0.le (by positivity)]
  ring

end NTKB
