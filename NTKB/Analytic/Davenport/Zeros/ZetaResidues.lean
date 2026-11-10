/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Davenport.Zeros.PoleBounds
import NTKB.Analytic.Davenport.Zeros.ExplicitAux

/-!
# The poles of `-ζ'/ζ(s) x^s/s`

**Davenport, Ch. 17, p. 105.** The function `-ζ'(s)/ζ(s) · x^s/s` has simple poles at `s = 1`
(residue `x`), `s = 0` (residue `-ζ'(0)/ζ(0)`), at each nontrivial zero `ρ` of multiplicity `m`
(residue `-m x^ρ/ρ`) and at each trivial zero `-2k` (residue `x^{-2k}/(2k)`).

We use `ζ'/ζ = ξ'/ξ - 1/(s - 1) + ½ log π - ½ ψ(s/2 + 1)` (`logDeriv_riemannZeta_eq_xi`, from
`ξ(s) = (s - 1) π^{-s/2} Γ(s/2 + 1) ζ(s)`), so that the poles come from `ξ'/ξ` (nontrivial zeros),
`1/(s - 1)` and `ψ(s/2 + 1)` (trivial zeros).
-/

open Filter Topology Complex Set
open scoped Real

namespace NTKB

/-- `ζ'/ζ = ξ'/ξ - 1/(s - 1) + ½ log π - ½ ψ(s/2 + 1)`. -/
lemma logDeriv_riemannZeta_eq_xi {s : ℂ} (hs1 : s ≠ 1) (hΓ : ∀ m : ℕ, s / 2 + 1 ≠ -m)
    (hz : riemannZeta s ≠ 0) :
    deriv riemannZeta s / riemannZeta s =
      logDeriv riemannXi s - 1 / (s - 1) + Complex.log π / 2 -
        Complex.digamma (s / 2 + 1) / 2 := by
  have hΓs : Complex.Gamma (s / 2 + 1) ≠ 0 := Complex.Gamma_ne_zero hΓ
  have hπ0 : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hπs : (π : ℂ) ^ (-s / 2) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]; push Not; intro h; exact absurd h hπ0
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have hin : HasDerivAt (fun w : ℂ ↦ w / 2 + 1) (1 / 2) s := by
    simpa using ((hasDerivAt_id s).div_const 2).add_const 1
  have hdΓ : HasDerivAt (fun w ↦ Complex.Gamma (w / 2 + 1))
      (deriv Complex.Gamma (s / 2 + 1) * (1 / 2)) s :=
    (Complex.differentiableAt_Gamma _ hΓ).hasDerivAt.comp s hin
  have hdπ : HasDerivAt (fun w : ℂ ↦ (π : ℂ) ^ (-w / 2))
      ((π : ℂ) ^ (-s / 2) * Complex.log π * (-1 / 2)) s := by
    have hin' : HasDerivAt (fun w : ℂ ↦ -w / 2) (-1 / 2) s := by
      simpa using ((hasDerivAt_id s).neg).div_const 2
    exact hin'.const_cpow (Or.inl hπ0)
  have hdζ := (differentiableAt_riemannZeta hs1).hasDerivAt
  have hev : riemannXi =ᶠ[𝓝 s] fun w ↦ (w - 1) * (π : ℂ) ^ (-w / 2) *
      Complex.Gamma (w / 2 + 1) * riemannZeta w := by
    filter_upwards [hdΓ.continuousAt.eventually_ne hΓs, isOpen_ne.mem_nhds hs1] with w hw hw1
    exact riemannXi_eq_mul_Gamma_add_one hw1 hw
  rw [(logDeriv_congr_nhds hev).eq_of_nhds]
  have hprod := ((((hasDerivAt_id s).sub_const 1).mul hdπ).mul hdΓ).mul hdζ
  have e : (fun w : ℂ ↦ (w - 1) * (π : ℂ) ^ (-w / 2) * Complex.Gamma (w / 2 + 1) *
      riemannZeta w) = ((((fun x ↦ id x - 1) * fun w : ℂ ↦ (π : ℂ) ^ (-w / 2)) *
        fun w ↦ Complex.Gamma (w / 2 + 1)) * riemannZeta) := rfl
  rw [logDeriv_apply, e, hprod.deriv, Complex.digamma_def, logDeriv_apply]
  simp only [id, Pi.mul_apply]
  generalize Complex.Gamma (s / 2 + 1) = G at hΓs ⊢
  generalize (π : ℂ) ^ (-s / 2) = P at hπs ⊢
  generalize riemannZeta s = Z at hz ⊢
  field_simp
  ring

/-- `ξ` does not vanish on a punctured neighbourhood of any point. -/
lemma riemannXi_eventually_ne_zero (p : ℂ) : ∀ᶠ s : ℂ in 𝓝[≠] p, riemannXi s ≠ 0 := by
  have han : AnalyticOnNhd ℂ riemannXi univ := fun z _ ↦ differentiable_riemannXi.analyticAt z
  rcases (han p (mem_univ p)).eventually_eq_zero_or_eventually_ne_zero with h | h
  · have := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (mem_univ p) h
      (mem_univ 0)
    simp at this
  · exact h

/-- Near a point `p` (punctured), if `s ≠ 1` and `Γ(s/2 + 1)` has no pole there, the
representation of `ζ'/ζ` through `ξ'/ξ` holds. -/
lemma eventually_neg_logDeriv_riemannZeta {p : ℂ}
    (h : ∀ᶠ s : ℂ in 𝓝[≠] p, s ≠ 1 ∧ ∀ m : ℕ, s / 2 + 1 ≠ -(m : ℂ)) :
    ∀ᶠ s : ℂ in 𝓝[≠] p, -(deriv riemannZeta s / riemannZeta s) =
      -logDeriv riemannXi s + 1 / (s - 1) - Complex.log π / 2 + Complex.digamma (s / 2 + 1) / 2 := by
  filter_upwards [h, riemannXi_eventually_ne_zero p] with s ⟨hs1, hΓ⟩ hξ
  have hz : riemannZeta s ≠ 0 := by
    intro hz
    apply hξ
    rw [riemannXi_eq_mul_Gamma_add_one hs1 (Complex.Gamma_ne_zero hΓ), hz, mul_zero]
  rw [logDeriv_riemannZeta_eq_xi hs1 hΓ hz]
  ring

lemma eventually_not_pole_of_re {p : ℂ} (hp : -2 < p.re) :
    ∀ᶠ s : ℂ in 𝓝 p, ∀ m : ℕ, s / 2 + 1 ≠ -(m : ℂ) := by
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
    (show p ∈ {b : ℂ | -2 < b.re} from hp)] with s hs m h
  have := congrArg Complex.re h
  simp at this
  linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]

lemma eventually_not_pole_trivial (k : ℕ) :
    ∀ᶠ s : ℂ in 𝓝[≠] (-(2 * ((k : ℂ) + 1))), ∀ m : ℕ, s / 2 + 1 ≠ -(m : ℂ) := by
  have h1 : ∀ᶠ s : ℂ in 𝓝 (-(2 * ((k : ℂ) + 1))), ‖s - -(2 * ((k : ℂ) + 1))‖ < 1 :=
    Filter.eventually_of_mem (Metric.ball_mem_nhds _ one_pos) fun s hs ↦ by
      simpa [dist_eq_norm] using hs
  filter_upwards [h1.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with s hs hsp m hm
  have hs' : s = -(2 * ((m : ℂ) + 1)) := by linear_combination 2 * hm
  rw [hs'] at hs hsp
  rcases eq_or_ne m k with rfl | hmk
  · exact hsp rfl
  · have : (2 : ℝ) ≤ ‖-(2 * ((m : ℂ) + 1)) - -(2 * ((k : ℂ) + 1))‖ := by
      rw [show -(2 * ((m : ℂ) + 1)) - -(2 * ((k : ℂ) + 1)) = ((2 * ((k : ℤ) - m) : ℤ) : ℂ) by
        push_cast; ring, Complex.norm_intCast]
      have : (k : ℤ) - m ≠ 0 := by omega
      have h2 := Int.one_le_abs this
      push_cast
      rw [abs_mul, abs_two]
      have : (1 : ℝ) ≤ |((k : ℤ) - m : ℤ)| := by exact_mod_cast h2
      push_cast at this
      linarith
    linarith

lemma continuousAt_one_div_sub {p : ℂ} (hp : p ≠ 1) : ContinuousAt (fun s : ℂ ↦ 1 / (s - 1)) p := by
  have h : ContinuousAt (fun s : ℂ ↦ (s - 1)⁻¹) p :=
    (continuousAt_id.sub continuousAt_const).inv₀ (sub_ne_zero.mpr hp)
  exact h.congr (Eventually.of_forall fun s ↦ by simp only [one_div])

lemma continuousAt_digamma_half {p : ℂ} (hp : 0 < (p / 2 + 1).re) :
    ContinuousAt (fun s : ℂ ↦ Complex.digamma (s / 2 + 1) / 2) p := by
  have h1 : ContinuousAt (fun s : ℂ ↦ s / 2 + 1) p :=
    (continuousAt_id.div_const 2).add continuousAt_const
  exact (ContinuousAt.comp (g := Complex.digamma) (f := fun s : ℂ ↦ s / 2 + 1) (x := p)
    (continuousAt_digamma_of_re_pos hp) h1).div_const 2

lemma continuousAt_logDeriv_riemannXi {p : ℂ} (hp : riemannXi p ≠ 0) :
    ContinuousAt (logDeriv riemannXi) p := by
  have han := differentiable_riemannXi.analyticAt p
  exact han.deriv.continuousAt.div han.continuousAt hp

/-- At a nontrivial zero `ρ` of multiplicity `m`: `-ζ'/ζ(s) + m/(s - ρ)` is bounded near `ρ`. -/
lemma bddNear_neg_logDeriv_riemannZeta_zero (ρ : ZeroIndex riemannXi) :
    BddNear (fun s ↦ -(deriv riemannZeta s / riemannZeta s) -
      (-(analyticOrderNatAt riemannXi ρ.val : ℂ)) / (s - ρ.val)) ρ.val := by
  have hρ := riemannXi_zero_mem ρ
  have hρ1 : ρ.val ≠ 1 := fun h ↦ by rw [h] at hρ; simp at hρ
  have han := differentiable_riemannXi.analyticAt ρ.val
  have hfin : analyticOrderAt riemannXi ρ.val ≠ ⊤ := by
    intro htop
    rw [analyticOrderAt_eq_top] at htop
    have hA : AnalyticOnNhd ℂ riemannXi univ := fun z _ ↦ differentiable_riemannXi.analyticAt z
    have := hA.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
      (mem_univ ρ.val) htop (mem_univ 0)
    simp at this
  have hm : analyticOrderAt riemannXi ρ.val = (analyticOrderNatAt riemannXi ρ.val : ℕ) :=
    (ENat.natCast_toNat hfin).symm
  have h1 := bddNear_logDeriv_sub han hm
  have c1 : ContinuousAt (fun s : ℂ ↦ 1 / (s - 1)) ρ.val :=
    continuousAt_one_div_sub hρ1
  have c2 : ContinuousAt (fun s : ℂ ↦ Complex.digamma (s / 2 + 1) / 2) ρ.val :=
    continuousAt_digamma_half (by simp; linarith [hρ.2.1])
  have hrest : ContinuousAt (fun s ↦ 1 / (s - 1) - Complex.log π / 2 +
      Complex.digamma (s / 2 + 1) / 2) ρ.val := (c1.sub continuousAt_const).add c2
  have hev : ∀ᶠ s : ℂ in 𝓝[≠] ρ.val, s ≠ 1 ∧ ∀ m : ℕ, s / 2 + 1 ≠ -(m : ℂ) := by
    filter_upwards [(eventually_ne_nhds hρ1).filter_mono nhdsWithin_le_nhds,
      (eventually_not_pole_of_re (p := ρ.val) (by linarith [hρ.2.1])).filter_mono
        nhdsWithin_le_nhds] with s h1 h2
    exact ⟨h1, h2⟩
  refine (h1.neg.add (bddNear_of_continuousAt hrest)).congr ?_
  filter_upwards [eventually_neg_logDeriv_riemannZeta hev] with s hs
  rw [hs]
  ring

/-- At `s = 1`: `-ζ'/ζ(s) - 1/(s - 1)` is bounded near `1`. -/
lemma bddNear_neg_logDeriv_riemannZeta_one :
    BddNear (fun s ↦ -(deriv riemannZeta s / riemannZeta s) - 1 / (s - 1)) 1 := by
  have c1 : ContinuousAt (fun s ↦ -logDeriv riemannXi s) 1 :=
    (continuousAt_logDeriv_riemannXi (by simp)).neg
  have c2 : ContinuousAt (fun s : ℂ ↦ Complex.digamma (s / 2 + 1) / 2) 1 :=
    continuousAt_digamma_half (by norm_num)
  have hcont : ContinuousAt (fun s ↦ -logDeriv riemannXi s - Complex.log π / 2 +
      Complex.digamma (s / 2 + 1) / 2) 1 := (c1.sub continuousAt_const).add c2
  have hev : ∀ᶠ s : ℂ in 𝓝[≠] (1 : ℂ), s ≠ 1 ∧ ∀ m : ℕ, s / 2 + 1 ≠ -(m : ℂ) := by
    filter_upwards [self_mem_nhdsWithin, (eventually_not_pole_of_re (p := 1) (by norm_num)).filter_mono
        nhdsWithin_le_nhds] with s h1 h2
    exact ⟨h1, h2⟩
  refine (bddNear_of_continuousAt hcont).congr ?_
  filter_upwards [eventually_neg_logDeriv_riemannZeta hev] with s hs
  rw [hs]
  ring

/-- At a trivial zero `-2(k + 1)`: `-ζ'/ζ(s) + 1/(s + 2(k + 1))` is bounded near it. -/
lemma bddNear_neg_logDeriv_riemannZeta_trivial (k : ℕ) :
    BddNear (fun s ↦ -(deriv riemannZeta s / riemannZeta s) -
      (-1) / (s - -(2 * ((k : ℂ) + 1)))) (-(2 * ((k : ℂ) + 1))) := by
  set p : ℂ := -(2 * ((k : ℂ) + 1)) with hp
  have hp1 : p ≠ 1 := by
    intro h; have := congrArg Complex.re h; simp [hp] at this; linarith [(k.cast_nonneg : (0 : ℝ) ≤ k)]
  have hξ : riemannXi p ≠ 0 := by
    intro h
    have := (riemannXi_eq_zero_iff.mp h).2.1
    simp [hp] at this
    linarith [(k.cast_nonneg : (0 : ℝ) ≤ k)]
  -- the digamma pole
  have hψ := bddNear_digamma_add k
  have hψ' : BddNear (fun s ↦ Complex.digamma (s / 2 + 1) + 1 / (s / 2 + 1 + k)) p := by
    obtain ⟨C, hC⟩ := bddNear_iff_eventually.mp hψ
    refine bddNear_iff_eventually.mpr ⟨C, ?_⟩
    have ht : Tendsto (fun s : ℂ ↦ s / 2 + 1) (𝓝[≠] p) (𝓝[≠] (-(k : ℂ))) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have : (fun s : ℂ ↦ s / 2 + 1) p = -(k : ℂ) := by simp [hp]; ring
        rw [← this]
        exact (((continuous_id.div_const 2).add continuous_const).tendsto p).mono_left
          nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with s hs h
        apply hs
        simp only [Set.mem_singleton_iff] at h ⊢
        rw [hp]; linear_combination 2 * h
    exact ht.eventually hC
  have c1 : ContinuousAt (fun s ↦ -logDeriv riemannXi s) p :=
    (continuousAt_logDeriv_riemannXi hξ).neg
  have hcont : ContinuousAt (fun s ↦ -logDeriv riemannXi s + 1 / (s - 1) - Complex.log π / 2) p :=
    (c1.add (continuousAt_one_div_sub hp1)).sub continuousAt_const
  have hev : ∀ᶠ s : ℂ in 𝓝[≠] p, s ≠ 1 ∧ ∀ m : ℕ, s / 2 + 1 ≠ -(m : ℂ) := by
    filter_upwards [(eventually_ne_nhds hp1).filter_mono nhdsWithin_le_nhds,
      eventually_not_pole_trivial k] with s h1 h2
    exact ⟨h1, h2⟩
  refine ((bddNear_of_continuousAt hcont).add ((bddNear_const (1 / 2) p).mul hψ')).congr ?_
  filter_upwards [eventually_neg_logDeriv_riemannZeta hev, self_mem_nhdsWithin] with s hs hsp
  rw [hs]
  have hsp' : s - p ≠ 0 := sub_ne_zero.mpr hsp
  have h2 : s / 2 + 1 + k = (s - p) / 2 := by rw [hp]; ring
  rw [h2]
  field_simp
  ring

end NTKB
