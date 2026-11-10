/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma

/-!
# Functions bounded near a point; simple poles

Tools for computing residues in Davenport, Ch. 17: `BddNear g p` says that `g` is bounded on a
punctured neighbourhood of `p`. Then

* `bddNear_logDeriv_sub`: at a zero of order `m` of an analytic function `f`,
  `f'/f - m/(s - p)` is bounded near `p`;
* `bddNear_mul_sub`: if `h - a/(s - p)` is bounded near `p` and `g` is differentiable at `p`, then
  `h g - a g(p)/(s - p)` is bounded near `p` (the residue of `h g` is `a g(p)`);
* `bddNear_digamma_add`: `ψ(w) + 1/(w + n)` is bounded near `w = -n`.
-/

open Filter Topology Complex Set

namespace NTKB

/-- `g` is bounded on a punctured neighbourhood of `p`. -/
def BddNear (g : ℂ → ℂ) (p : ℂ) : Prop :=
  ∃ V ∈ 𝓝 p, BddAbove (norm ∘ g '' (V \ {p}))

lemma bddNear_iff_eventually {g : ℂ → ℂ} {p : ℂ} :
    BddNear g p ↔ ∃ C, ∀ᶠ s in 𝓝[≠] p, ‖g s‖ ≤ C := by
  constructor
  · rintro ⟨V, hV, C, hC⟩
    refine ⟨C, ?_⟩
    rw [eventually_nhdsWithin_iff]
    filter_upwards [hV] with s hs hsp
    exact hC ⟨s, ⟨hs, hsp⟩, rfl⟩
  · rintro ⟨C, hC⟩
    rw [eventually_nhdsWithin_iff] at hC
    refine ⟨_, hC, C, ?_⟩
    rintro _ ⟨s, ⟨hs, hsp⟩, rfl⟩
    exact hs hsp

lemma BddNear.congr {f g : ℂ → ℂ} {p : ℂ} (hf : BddNear f p) (h : f =ᶠ[𝓝[≠] p] g) :
    BddNear g p := by
  obtain ⟨C, hC⟩ := bddNear_iff_eventually.mp hf
  exact bddNear_iff_eventually.mpr ⟨C, by filter_upwards [hC, h] with s h1 h2; rwa [← h2]⟩

lemma bddNear_of_continuousAt {g : ℂ → ℂ} {p : ℂ} (hg : ContinuousAt g p) : BddNear g p := by
  refine bddNear_iff_eventually.mpr ⟨‖g p‖ + 1, ?_⟩
  have := hg.norm.eventually (gt_mem_nhds (lt_add_one ‖g p‖))
  exact (this.filter_mono nhdsWithin_le_nhds).mono fun s hs ↦ hs.le

lemma BddNear.add {f g : ℂ → ℂ} {p : ℂ} (hf : BddNear f p) (hg : BddNear g p) :
    BddNear (fun s ↦ f s + g s) p := by
  obtain ⟨C, hC⟩ := bddNear_iff_eventually.mp hf
  obtain ⟨D, hD⟩ := bddNear_iff_eventually.mp hg
  exact bddNear_iff_eventually.mpr ⟨C + D, by
    filter_upwards [hC, hD] with s h1 h2; exact (norm_add_le _ _).trans (add_le_add h1 h2)⟩

lemma BddNear.neg {f : ℂ → ℂ} {p : ℂ} (hf : BddNear f p) : BddNear (fun s ↦ -f s) p := by
  obtain ⟨C, hC⟩ := bddNear_iff_eventually.mp hf
  exact bddNear_iff_eventually.mpr ⟨C, by filter_upwards [hC] with s h1; rwa [norm_neg]⟩

lemma BddNear.sub {f g : ℂ → ℂ} {p : ℂ} (hf : BddNear f p) (hg : BddNear g p) :
    BddNear (fun s ↦ f s - g s) p := by
  simpa [sub_eq_add_neg] using hf.add hg.neg

lemma BddNear.mul {f g : ℂ → ℂ} {p : ℂ} (hf : BddNear f p) (hg : BddNear g p) :
    BddNear (fun s ↦ f s * g s) p := by
  obtain ⟨C, hC⟩ := bddNear_iff_eventually.mp hf
  obtain ⟨D, hD⟩ := bddNear_iff_eventually.mp hg
  exact bddNear_iff_eventually.mpr ⟨C * D, by
    filter_upwards [hC, hD] with s h1 h2
    rw [norm_mul]; exact mul_le_mul h1 h2 (norm_nonneg _) ((norm_nonneg _).trans h1)⟩

lemma bddNear_const (c : ℂ) (p : ℂ) : BddNear (fun _ ↦ c) p :=
  bddNear_of_continuousAt continuousAt_const

/-- Difference quotients of a function differentiable at `p` are bounded near `p`. -/
lemma bddNear_slope {g : ℂ → ℂ} {p : ℂ} (hg : DifferentiableAt ℂ g p) :
    BddNear (fun s ↦ (g s - g p) / (s - p)) p := by
  have ht := hasDerivAt_iff_tendsto_slope_zero.mp hg.hasDerivAt
  have hev := ht.norm.eventually (gt_mem_nhds (lt_add_one ‖deriv g p‖))
  refine bddNear_iff_eventually.mpr ⟨‖deriv g p‖ + 1, ?_⟩
  rw [eventually_nhdsWithin_iff] at hev ⊢
  have hev' : ∀ᶠ s in 𝓝 p, s - p ∈ ({0}ᶜ : Set ℂ) →
      ‖(s - p)⁻¹ • (g (p + (s - p)) - g p)‖ < ‖deriv g p‖ + 1 := by
    have : Tendsto (fun s : ℂ ↦ s - p) (𝓝 p) (𝓝 0) := by
      simpa using (continuous_sub_right p).tendsto p
    exact this.eventually hev
  filter_upwards [hev'] with s hs hsp
  have hsp' : s - p ∈ ({0}ᶜ : Set ℂ) := sub_ne_zero.mpr hsp
  have := (hs hsp').le
  simp only [add_sub_cancel, smul_eq_mul] at this
  rwa [div_eq_inv_mul]

/-- **Residue of a product**: if `h - a/(s - p)` is bounded near `p` and `g` is differentiable
at `p`, then `h g - a g(p)/(s - p)` is bounded near `p`. -/
lemma bddNear_mul_sub {h g : ℂ → ℂ} {p a : ℂ} (hh : BddNear (fun s ↦ h s - a / (s - p)) p)
    (hg : DifferentiableAt ℂ g p) :
    BddNear (fun s ↦ h s * g s - a * g p / (s - p)) p := by
  have h1 := hh.mul (bddNear_of_continuousAt hg.continuousAt)
  have h2 := (bddNear_const a p).mul (bddNear_slope hg)
  refine (h1.add h2).congr ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs' : s - p ≠ 0 := sub_ne_zero.mpr hs
  field_simp
  ring

/-- **Logarithmic derivative at a zero of order `m`**: `f'/f - m/(s - p)` is bounded near `p`. -/
lemma bddNear_logDeriv_sub {f : ℂ → ℂ} {p : ℂ} {m : ℕ} (hf : AnalyticAt ℂ f p)
    (hm : analyticOrderAt f p = m) :
    BddNear (fun s ↦ logDeriv f s - m / (s - p)) p := by
  obtain ⟨g, hg, hgp, hfg⟩ := (hf.analyticOrderAt_eq_natCast).mp hm
  -- a neighbourhood where `f = (s - p)^m g`, `g` analytic and nonzero
  have hev : ∀ᶠ s in 𝓝 p, (∀ᶠ z in 𝓝 s, f z = (z - p) ^ m • g z) ∧ AnalyticAt ℂ g s ∧
      g s ≠ 0 := by
    filter_upwards [hfg.eventually_nhds, hg.eventually_analyticAt,
      hg.continuousAt.eventually_ne hgp] with s h1 h2 h3
    exact ⟨h1, h2, h3⟩
  have hcont : ContinuousAt (logDeriv g) p := by
    have hd : ContinuousAt (deriv g) p := hg.deriv.continuousAt
    exact hd.div hg.continuousAt hgp
  refine (bddNear_of_continuousAt hcont).congr ?_
  filter_upwards [hev.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with s ⟨h1, h2, h3⟩ hsp
  have hsp' : s - p ≠ 0 := sub_ne_zero.mpr hsp
  have hpow : HasDerivAt (fun z : ℂ ↦ (z - p) ^ m) (m * (s - p) ^ (m - 1)) s := by
    have := (hasDerivAt_pow m (s - p)).comp s ((hasDerivAt_id s).sub_const p)
    simpa [Function.comp_def] using this
  have hprod : HasDerivAt (fun z ↦ (z - p) ^ m * g z)
      (m * (s - p) ^ (m - 1) * g s + (s - p) ^ m * deriv g s) s :=
    hpow.mul h2.differentiableAt.hasDerivAt
  have hfeq : f =ᶠ[𝓝 s] fun z ↦ (z - p) ^ m * g z := by
    filter_upwards [h1] with z hz; rw [hz, smul_eq_mul]
  rw [eq_comm, logDeriv_apply, hfeq.deriv_eq, hprod.deriv, hfeq.eq_of_nhds, logDeriv_apply]
  rcases Nat.eq_zero_or_pos m with rfl | hm0
  · simp
  · have hpm : (s - p) ^ m = (s - p) ^ (m - 1) * (s - p) := by
      rw [← pow_succ, Nat.sub_add_cancel hm0]
    rw [hpm]
    field_simp
    ring

/-- `Γ` is analytic on `Re s > 0`. -/
lemma analyticAt_Gamma_of_re_pos' {z : ℂ} (hz : 0 < z.re) : AnalyticAt ℂ Complex.Gamma z := by
  refine DifferentiableOn.analyticAt (s := {w : ℂ | 0 < w.re}) ?_
    ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz)
  intro w hw
  refine (Complex.differentiableAt_Gamma w fun m h ↦ ?_).differentiableWithinAt
  have := congrArg Complex.re h
  simp only [Set.mem_ofPred_eq] at hw
  simp at this
  linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]

/-- `ψ` is continuous on `Re s > 0`. -/
lemma continuousAt_digamma_of_re_pos {z : ℂ} (hz : 0 < z.re) :
    ContinuousAt Complex.digamma z := by
  have hG := analyticAt_Gamma_of_re_pos' hz
  have hΓ : Complex.Gamma z ≠ 0 := Complex.Gamma_ne_zero fun m h ↦ by
    have := congrArg Complex.re h; simp at this; linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
  rw [Complex.digamma_def]
  exact hG.deriv.continuousAt.div hG.continuousAt hΓ

/-- `ψ(w) + 1/(w + n)` is bounded near the pole `w = -n` of the digamma function. -/
lemma bddNear_digamma_add (n : ℕ) :
    BddNear (fun w ↦ Complex.digamma w + 1 / (w + n)) (-n) := by
  have hcont : ContinuousAt (fun w ↦ Complex.digamma (w + (n + 1 : ℕ)) -
      ∑ k ∈ Finset.range n, (w + k)⁻¹) (-n) := by
    refine ContinuousAt.sub ?_ ?_
    · have h1 : ContinuousAt (fun w : ℂ ↦ w + ((n + 1 : ℕ) : ℂ)) (-n) :=
        continuousAt_id.add continuousAt_const
      have hz : 0 < ((-n : ℂ) + ((n + 1 : ℕ) : ℂ)).re := by
        rw [Complex.add_re, Complex.neg_re, Complex.natCast_re, Complex.natCast_re]
        push_cast; linarith
      have h2 : ContinuousAt Complex.digamma ((-n : ℂ) + ((n + 1 : ℕ) : ℂ)) :=
        continuousAt_digamma_of_re_pos hz
      exact ContinuousAt.comp (g := Complex.digamma) h2 h1
    · refine tendsto_finsetSum _ fun k hk ↦ ?_
      have hk' : (-n : ℂ) + k ≠ 0 := by
        intro h
        have := congrArg Complex.re h
        simp at this
        have hk2 := Finset.mem_range.mp hk
        have : (k : ℝ) < n := by exact_mod_cast hk2
        linarith
      exact (continuousAt_id.add continuousAt_const).inv₀ hk'
  refine (bddNear_of_continuousAt hcont).congr ?_
  -- away from the poles: `ψ(w + n + 1) = ψ(w) + ∑_{k ≤ n} 1/(w + k)`
  have hball : ∀ᶠ w in 𝓝[≠] (-(n : ℂ)), ∀ m : ℕ, w ≠ -(m : ℂ) := by
    have h1 : ∀ᶠ w in 𝓝 (-(n : ℂ)), ‖w - -(n : ℂ)‖ < 1 / 2 :=
      Filter.eventually_of_mem (Metric.ball_mem_nhds _ (by norm_num : (0 : ℝ) < 1 / 2))
        fun w hw ↦ by simpa [dist_eq_norm] using hw
    filter_upwards [h1.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with w hw hwn m hm
    rw [hm] at hw hwn
    rcases eq_or_ne m n with rfl | hmn
    · exact hwn rfl
    · have : (1 : ℝ) ≤ ‖(-m : ℂ) - (-n)‖ := by
        rw [show (-m : ℂ) - (-n) = ((n : ℤ) - m : ℤ) by push_cast; ring, Complex.norm_intCast]
        have : (n : ℤ) - m ≠ 0 := by omega
        exact_mod_cast Int.one_le_abs this
      linarith
  filter_upwards [hball] with w hw
  have h := Complex.digamma_apply_add_nat hw (n + 1)
  rw [Finset.sum_range_succ] at h
  rw [h, one_div]
  ring

end NTKB
