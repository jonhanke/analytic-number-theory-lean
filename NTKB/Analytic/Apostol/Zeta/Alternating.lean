/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Basic
import NTKB.Attr

/-!
# The alternating series for `ζ(s)` (Apostol, Theorem 13.11)

**Theorem 13.11**: for `σ > 0`, `s ≠ 1`, `(1 - 2^{1-s}) ζ(s) = ∑_{n ≥ 1} (-1)^{n-1} n^{-s}`
(the series converges, conditionally for `0 < σ ≤ 1`; we state it as the limit of the partial sums,
since Lean's `tsum` only covers unconditional sums); hence `ζ(s) < 0` for real `0 < s < 1`.

Apostol continues the series to `σ > 0` with Theorem 11.11 (uniform convergence on compact
subsets of the half-plane of convergence). Here: pairing consecutive terms,
`|(2m+1)^{-s} - (2m+2)^{-s}| ≤ |s| (2m+1)^{-σ-1}` (mean value theorem), so the paired series
converges locally uniformly on `σ > 0` and its sum `η(s)` is analytic there; for `σ > 1`,
`η(s) = ζ(s) - 2·2^{-s}ζ(s)`, and the identity theorem on the connected set `{σ > 0} \ {1}`
gives the equality for `σ > 0`. (At `s = 1` the left side is the limit `log 2`; Lean's value
`riemannZeta 1` is a junk value, so `s = 1` is excluded.)
-/

open Complex Filter Topology Finset

namespace NTKB.Apostol

/-- `(-1)^n (n+1)^{-s}`, the `(n+1)`-st term of the alternating zeta series. -/
noncomputable def etaTerm (s : ℂ) (n : ℕ) : ℂ := (-1) ^ n * ((n : ℂ) + 1) ^ (-s)

/-- The paired terms `(2m+1)^{-s} - (2m+2)^{-s}`. -/
noncomputable def etaPair (s : ℂ) (m : ℕ) : ℂ := etaTerm s (2 * m) + etaTerm s (2 * m + 1)

theorem etaPair_eq (s : ℂ) (m : ℕ) :
    etaPair s m = ((2 * m + 1 : ℝ) : ℂ) ^ (-s) - ((2 * m + 1 : ℝ) + 1 : ℝ) ^ (-s) := by
  simp only [etaPair, etaTerm, pow_succ, pow_mul, mul_neg, mul_one, neg_mul]
  push_cast
  ring_nf

theorem sum_range_two_mul_etaTerm (s : ℂ) (M : ℕ) :
    ∑ n ∈ range (2 * M), etaTerm s n = ∑ m ∈ range M, etaPair s m := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [show 2 * (M + 1) = 2 * M + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih,
      sum_range_succ, etaPair, add_assoc]

/-- `‖(a)^{-s} - (a+1)^{-s}‖ ≤ ‖s‖ a^{-σ-1}` for `a > 0`. -/
theorem norm_cpow_neg_sub_le {s : ℂ} (hs : 0 < s.re) {a : ℝ} (ha : 0 < a) :
    ‖((a : ℝ) : ℂ) ^ (-s) - ((a + 1 : ℝ) : ℂ) ^ (-s)‖ ≤ ‖s‖ * a ^ (-s.re - 1) := by
  have hs0 : -s ≠ 0 := by
    intro h; have := congrArg re h; simp at this; linarith
  set f : ℝ → ℂ := fun t ↦ (t : ℂ) ^ (-s)
  have hderiv : ∀ t ∈ Set.Icc a (a + 1),
      HasDerivWithinAt f ((-s) * (t : ℂ) ^ (-s - 1)) (Set.Icc a (a + 1)) t := by
    intro t ht
    exact (hasDerivAt_ofReal_cpow_const (by linarith [ht.1]) hs0).hasDerivWithinAt
  have hbound : ∀ t ∈ Set.Ico a (a + 1), ‖(-s) * (t : ℂ) ^ (-s - 1)‖ ≤ ‖s‖ * a ^ (-s.re - 1) := by
    intro t ht
    have ht0 : 0 < t := by linarith [ht.1]
    rw [norm_mul, norm_neg, norm_cpow_eq_rpow_re_of_pos ht0]
    gcongr
    simp only [sub_re, neg_re, one_re]
    exact Real.rpow_le_rpow_of_nonpos ha ht.1 (by linarith)
  have := norm_image_sub_le_of_norm_deriv_le_segment' hderiv hbound (a + 1) ⟨by linarith, le_rfl⟩
  rw [← norm_neg, neg_sub]
  simpa [f] using this

theorem norm_etaPair_le {s : ℂ} (hs : 0 < s.re) (m : ℕ) :
    ‖etaPair s m‖ ≤ ‖s‖ * ((m : ℝ) + 1) ^ (-s.re - 1) := by
  rw [etaPair_eq]
  refine (norm_cpow_neg_sub_le hs (by positivity)).trans ?_
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos (by positivity)
    (by linarith [m.cast_nonneg (α := ℝ)]) (by linarith)) (norm_nonneg _)

theorem summable_succ_rpow {p : ℝ} (hp : p < -1) : Summable fun n : ℕ ↦ ((n : ℝ) + 1) ^ p := by
  have h := (summable_nat_add_iff 1).2 ((Real.summable_nat_rpow (p := p)).2 hp)
  simpa [Nat.cast_add, Nat.cast_one] using h

theorem norm_natCast_add_one_cpow (s : ℂ) (k : ℕ) :
    ‖((k : ℂ) + 1) ^ (-s)‖ = ((k : ℝ) + 1) ^ (-s.re) := by
  rw [show (k : ℂ) + 1 = ((k + 1 : ℝ) : ℂ) by push_cast; rfl,
    norm_cpow_eq_rpow_re_of_pos (by positivity), neg_re]

theorem summable_etaPair {s : ℂ} (hs : 0 < s.re) : Summable (etaPair s) := by
  refine Summable.of_norm_bounded ?_ (norm_etaPair_le hs)
  exact Summable.mul_left _ (summable_succ_rpow (by linarith))

/-- `η(s) = ∑_m ((2m+1)^{-s} - (2m+2)^{-s})`. -/
noncomputable def etaSum (s : ℂ) : ℂ := ∑' m, etaPair s m

theorem differentiableOn_etaSum : DifferentiableOn ℂ etaSum {s | 0 < s.re} := by
  intro s₀ hs₀
  have hs₀' : 0 < s₀.re := hs₀
  set δ := s₀.re / 2
  set R := ‖s₀‖ + 1
  set U : Set ℂ := {s | δ < s.re ∧ ‖s‖ < R}
  have hU : IsOpen U :=
    (isOpen_lt continuous_const continuous_re).inter (isOpen_lt continuous_norm continuous_const)
  have hmem : s₀ ∈ U := ⟨by simp only [δ]; linarith, by simp only [R]; linarith⟩
  have hdiff : DifferentiableOn ℂ etaSum U := by
    refine differentiableOn_tsum_of_summable_norm
      (u := fun m : ℕ ↦ R * ((m : ℝ) + 1) ^ (-δ - 1)) ?_ ?_ hU ?_
    · exact Summable.mul_left _ (summable_succ_rpow (by simp only [δ]; linarith))
    · intro m s _
      have h1 : ∀ n : ℕ, DifferentiableAt ℂ (fun s ↦ etaTerm s n) s := fun n ↦
        (differentiableAt_id.neg.const_cpow (Or.inl (Nat.cast_add_one_ne_zero n))).const_mul _
      exact ((h1 (2 * m)).add (h1 (2 * m + 1))).differentiableWithinAt
    · intro m s hs
      have hσ : 0 < s.re := by linarith [hs.1, show 0 < δ by positivity]
      refine (norm_etaPair_le hσ m).trans ?_
      gcongr
      · exact hs.2.le
      · exact le_add_of_nonneg_left (by positivity)
      · linarith [hs.1]
  exact (hdiff s₀ hmem).differentiableAt (hU.mem_nhds hmem) |>.differentiableWithinAt

/-- The partial sums of the alternating series tend to `η(s)` for `σ > 0`. -/
theorem tendsto_sum_etaTerm {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun N ↦ ∑ n ∈ range N, etaTerm s n) atTop (𝓝 (etaSum s)) := by
  have hT : Tendsto (fun M ↦ ∑ m ∈ range M, etaPair s m) atTop (𝓝 (etaSum s)) :=
    (summable_etaPair hs).hasSum.tendsto_sum_nat
  have hlast : Tendsto (fun N : ℕ ↦ ((N : ℂ) + 1) ^ (-s)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simp_rw [norm_natCast_add_one_cpow]
    have h := (tendsto_rpow_neg_atTop hs).comp
      (tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x := (1 : ℝ))))
    exact h.congr fun N ↦ by simp [Function.comp, Real.rpow_neg (by positivity : (0:ℝ) ≤ N + 1)]
  have hdecomp : ∀ N : ℕ, ∑ n ∈ range N, etaTerm s n =
      ∑ m ∈ range (N / 2), etaPair s m +
        if N % 2 = 1 then etaTerm s (2 * (N / 2)) else 0 := by
    intro N
    rcases Nat.even_or_odd' N with ⟨k, rfl | rfl⟩
    · rw [sum_range_two_mul_etaTerm]; simp
    · rw [sum_range_succ, sum_range_two_mul_etaTerm]
      have h1 : (2 * k + 1) / 2 = k := by omega
      have h2 : (2 * k + 1) % 2 = 1 := by omega
      simp [h1, h2]
  simp_rw [hdecomp]
  rw [← add_zero (etaSum s)]
  refine (hT.comp (Nat.tendsto_div_const_atTop two_ne_zero)).add ?_
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero (fun _ ↦ norm_nonneg _) (fun N ↦ ?_)
    ((tendsto_zero_iff_norm_tendsto_zero.1 hlast).comp
      (Nat.tendsto_div_const_atTop (two_ne_zero)))
  split_ifs
  · simp only [etaTerm, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
      Function.comp, norm_natCast_add_one_cpow]
    push_cast
    exact Real.rpow_le_rpow_of_nonpos (by positivity)
      (by linarith [(N / 2 : ℕ).cast_nonneg (α := ℝ)]) (by linarith)
  · simp

theorem two_mul_cpow_neg (s : ℂ) (n : ℕ) :
    ((((2 * n + 1 : ℕ) : ℂ) + 1) ^ (-s)) = 2 ^ (-s) * ((n : ℂ) + 1) ^ (-s) := by
  have : (((2 * n + 1 : ℕ) : ℂ) + 1) = ((2 : ℕ) : ℂ) * ((n + 1 : ℕ) : ℂ) := by push_cast; ring
  rw [this, natCast_mul_natCast_cpow]
  push_cast; rfl

/-- For `σ > 1`: `η(s) = (1 - 2^{1-s}) ζ(s)`. -/
theorem etaSum_eq_of_one_lt {s : ℂ} (hs : 1 < s.re) :
    etaSum s = (1 - 2 ^ (1 - s)) * riemannZeta s := by
  have hz : HasSum (fun n : ℕ ↦ ((n : ℂ) + 1) ^ (-s)) (riemannZeta s) := by
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs]
    have hsum : Summable (fun n : ℕ ↦ 1 / ((n : ℂ) + 1) ^ s) := by
      have := (summable_nat_add_iff 1).2 (Complex.summable_one_div_nat_cpow.2 hs)
      simpa [Nat.cast_add, Nat.cast_one] using this
    convert hsum.hasSum using 1
    funext n; rw [cpow_neg, one_div]
  set f : ℕ → ℂ := fun n ↦ ((n : ℂ) + 1) ^ (-s)
  have he : Summable fun m ↦ f (2 * m) := hz.summable.comp_injective
    (fun a b h ↦ by simpa using h)
  have ho : Summable fun m ↦ f (2 * m + 1) := hz.summable.comp_injective
    (fun a b h ↦ by simpa using h)
  have hodd : ∑' m, f (2 * m + 1) = 2 ^ (-s) * riemannZeta s := by
    simp only [f, two_mul_cpow_neg]
    rw [tsum_mul_left, hz.tsum_eq]
  have hzeta : riemannZeta s = ∑' m, f (2 * m) + ∑' m, f (2 * m + 1) :=
    (HasSum.even_add_odd he.hasSum ho.hasSum).unique hz |>.symm
  have hpair : etaSum s = ∑' m, f (2 * m) - ∑' m, f (2 * m + 1) := by
    rw [etaSum, ← he.tsum_sub ho]
    congr 1; funext m
    simp [etaPair, etaTerm, f, pow_succ, pow_mul, sub_eq_add_neg]
  have h2 : (2 : ℂ) ^ (1 - s) = 2 * 2 ^ (-s) := by
    rw [sub_eq_add_neg, cpow_add _ _ two_ne_zero, cpow_one]
  rw [hpair, h2]
  linear_combination (-1 : ℂ) * hzeta + (-2 : ℂ) * hodd

theorem isPreconnected_re_pos_diff_one : IsPreconnected ({s : ℂ | 0 < s.re} \ {1}) := by
  set W₁ : Set ℂ := {s | 0 < s.re ∧ 0 < s.im}
  set W₂ : Set ℂ := {s | 0 < s.re ∧ s.im < 0}
  set W₃ : Set ℂ := {s | 0 < s.re ∧ s.re < 1}
  set W₄ : Set ℂ := {s | 1 < s.re}
  have c₁ : Convex ℝ W₁ := (convex_halfSpace_gt reLm.isLinear 0).inter
    (convex_halfSpace_gt imLm.isLinear 0)
  have c₂ : Convex ℝ W₂ := (convex_halfSpace_gt reLm.isLinear 0).inter
    (convex_halfSpace_lt imLm.isLinear 0)
  have c₃ : Convex ℝ W₃ := (convex_halfSpace_gt reLm.isLinear 0).inter
    (convex_halfSpace_lt reLm.isLinear 1)
  have c₄ : Convex ℝ W₄ := convex_halfSpace_gt reLm.isLinear 1
  have heq : {s : ℂ | 0 < s.re} \ {1} = ((W₁ ∪ W₃) ∪ W₂) ∪ W₄ := by
    ext s
    simp only [Set.mem_sdiff, Set.mem_ofPred_eq, Set.mem_singleton_iff, Set.mem_union, W₁, W₂, W₃,
      W₄]
    constructor
    · rintro ⟨h0, h1⟩
      rcases lt_trichotomy s.im 0 with h | h | h
      · left; right; exact ⟨h0, h⟩
      · rcases lt_trichotomy s.re 1 with h' | h' | h'
        · left; left; right; exact ⟨h0, h'⟩
        · exact absurd (Complex.ext (by simpa using h') (by simpa using h)) h1
        · right; exact h'
      · left; left; left; exact ⟨h0, h⟩
    · rintro (((h | h) | h) | h)
      · exact ⟨h.1, fun e ↦ by simp [e] at h⟩
      · exact ⟨h.1, fun e ↦ by simp [e] at h⟩
      · exact ⟨h.1, fun e ↦ by simp [e] at h⟩
      · exact ⟨by linarith [show (1 : ℝ) < s.re from h], fun e ↦ by simp [e] at h⟩
  rw [heq]
  have p13 : IsPreconnected (W₁ ∪ W₃) :=
    IsPreconnected.union (1 / 2 + I) ⟨by norm_num, by norm_num⟩
      ⟨by norm_num, by norm_num⟩ c₁.isPreconnected c₃.isPreconnected
  have p132 : IsPreconnected ((W₁ ∪ W₃) ∪ W₂) :=
    IsPreconnected.union (1 / 2 - I) (Or.inr ⟨by norm_num, by norm_num⟩)
      ⟨by norm_num, by norm_num⟩ p13 c₂.isPreconnected
  exact IsPreconnected.union (2 + I) (Or.inl (Or.inl ⟨by norm_num, by norm_num⟩))
    (show 1 < (2 + I).re by norm_num) p132 c₄.isPreconnected

/-- **Apostol, Theorem 13.11**: for `σ > 0`, `s ≠ 1`, the alternating series
`∑_{n ≥ 1} (-1)^{n-1} n^{-s}` converges to `(1 - 2^{1-s}) ζ(s)`. -/
@[kb "apostol1976" "Thm 13.11, p. 291"]
theorem tendsto_sum_alternating_zeta {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    Tendsto (fun N ↦ ∑ n ∈ range N, (-1) ^ n / ((n : ℂ) + 1) ^ s) atTop
      (𝓝 ((1 - 2 ^ (1 - s)) * riemannZeta s)) := by
  have hU : IsOpen ({s : ℂ | 0 < s.re} \ {1}) :=
    (isOpen_lt continuous_const continuous_re).sdiff isClosed_singleton
  have hη : AnalyticOnNhd ℂ etaSum ({s : ℂ | 0 < s.re} \ {1}) :=
    (differentiableOn_etaSum.mono Set.sdiff_subset).analyticOnNhd hU
  have hζ : AnalyticOnNhd ℂ (fun s ↦ (1 - 2 ^ (1 - s)) * riemannZeta s)
      ({s : ℂ | 0 < s.re} \ {1}) := by
    refine DifferentiableOn.analyticOnNhd (fun z hz ↦ ?_) hU
    refine DifferentiableAt.differentiableWithinAt ?_
    exact ((differentiableAt_const _).sub
      ((differentiableAt_const _).sub differentiableAt_id |>.const_cpow (Or.inl two_ne_zero))).mul
      (differentiableAt_riemannZeta hz.2)
  have h2 : (2 : ℂ) ∈ {s : ℂ | 0 < s.re} \ {1} := ⟨by simp, by norm_num⟩
  have hev : etaSum =ᶠ[𝓝 2] fun s ↦ (1 - 2 ^ (1 - s)) * riemannZeta s := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds
      (show (2 : ℂ) ∈ {b : ℂ | (1 : ℝ) < b.re} by norm_num)] with z hz
    exact etaSum_eq_of_one_lt hz
  have heq := hη.eqOn_of_preconnected_of_eventuallyEq hζ isPreconnected_re_pos_diff_one h2 hev
  have h := heq ⟨hs, hs1⟩
  simp only at h
  rw [← h]
  refine (tendsto_sum_etaTerm hs).congr fun N ↦ sum_congr rfl fun n _ ↦ ?_
  rw [etaTerm, cpow_neg, div_eq_mul_inv]

/-- **Apostol, Theorem 13.11**, consequence: `ζ(σ) < 0` for real `0 < σ < 1` (`ζ(σ)` is real). -/
@[kb "apostol1976" "Thm 13.11, p. 291"]
theorem riemannZeta_neg_of_lt_one {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) :
    (riemannZeta σ).im = 0 ∧ (riemannZeta σ).re < 0 := by
  have hs : 0 < (σ : ℂ).re := by simpa using h0
  -- the paired terms are positive reals
  set a : ℕ → ℝ := fun m ↦ (2 * m + 1 : ℝ) ^ (-σ) - ((2 * m + 1 : ℝ) + 1) ^ (-σ)
  have ha : ∀ m, etaPair σ m = (a m : ℂ) := by
    intro m
    rw [etaPair_eq]
    simp only [a, ofReal_sub]
    rw [ofReal_cpow (by positivity), ofReal_cpow (by positivity)]
    push_cast; rfl
  have hapos : ∀ m, 0 < a m := by
    intro m
    simp only [a, sub_pos]
    exact Real.rpow_lt_rpow_of_neg (by positivity) (by linarith) (by linarith)
  have hsa : Summable a := by
    exact Complex.summable_ofReal.1 ((summable_etaPair hs).congr ha)
  have hη : etaSum σ = ((∑' m, a m : ℝ) : ℂ) := by
    rw [etaSum, ofReal_tsum]; exact tsum_congr ha
  have hpos : 0 < ∑' m, a m := hsa.tsum_pos (fun m ↦ (hapos m).le) 0 (hapos 0)
  -- `1 - 2^{1-σ}` is a negative real
  have hc : (1 - (2 : ℂ) ^ (1 - (σ : ℂ))) = ((1 - (2 : ℝ) ^ (1 - σ) : ℝ) : ℂ) := by
    rw [ofReal_sub, ofReal_one, ofReal_cpow (by norm_num)]; push_cast; rfl
  have hcneg : 1 - (2 : ℝ) ^ (1 - σ) < 0 := by
    have : 1 < (2 : ℝ) ^ (1 - σ) := Real.one_lt_rpow (by norm_num) (by linarith)
    linarith
  have hlim := tendsto_sum_alternating_zeta hs (by
    intro e; have := congrArg re e; simp at this; linarith)
  have hlim' := tendsto_sum_etaTerm hs
  have huniq : etaSum σ = (1 - 2 ^ (1 - (σ : ℂ))) * riemannZeta σ := by
    refine tendsto_nhds_unique hlim' (hlim.congr fun N ↦ sum_congr rfl fun n _ ↦ ?_)
    rw [etaTerm, cpow_neg, div_eq_mul_inv]
  rw [hη, hc] at huniq
  have hζ : riemannZeta σ = (((∑' m, a m) / (1 - (2 : ℝ) ^ (1 - σ)) : ℝ) : ℂ) := by
    rw [ofReal_div, huniq, mul_div_cancel_left₀ _ (by exact_mod_cast hcneg.ne)]
  rw [hζ, ofReal_im, ofReal_re]
  exact ⟨rfl, div_neg_of_pos_of_neg hpos hcneg⟩

end NTKB.Apostol
