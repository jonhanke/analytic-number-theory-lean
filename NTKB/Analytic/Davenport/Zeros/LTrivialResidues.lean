/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Davenport.Zeros.LLogDerivLeft
import NTKB.Analytic.Davenport.Zeros.LContourMain

/-!
# Residues at the trivial zeros of `L(s, χ)`

**Davenport, Ch. 19, p. 115.** For `χ` primitive mod `q > 1` with parity `a`, the trivial zeros
of `L(s, χ)` are `p_n = -(a + 2n)`; at each `p_n ≠ 0` the function `-L'/L(s, χ)` has a simple pole
with residue `-1`, so `F(s, χ) = -L'/L(s, χ) x^s/s` has residue `-x^{p_n}/p_n`
(`bddNear_explicitIntegrandL_trivial`). As in Davenport (and as for `ζ`), this is read off from
`L'/L(s, χ) = ξ'/ξ(s, χ) - ½ log(q/π) - ½ ψ((s + a)/2)` and the pole of `ψ` at `-n`.
-/

open Filter Topology Complex Set DirichletCharacter
open scoped Real

namespace NTKB

variable {N : ℕ} [NeZero N]

/-- The trivial zero `-(a + 2n)` of `L(s, χ)`. -/
noncomputable def trivialZeroL (χ : DirichletCharacter ℂ N) (n : ℕ) : ℂ :=
  -(dirichletParity χ + 2 * n)

omit [NeZero N] in
lemma trivialZeroL_re (χ : DirichletCharacter ℂ N) (n : ℕ) :
    (trivialZeroL χ n).re = -((dirichletParity χ).re + 2 * n) := by
  simp [trivialZeroL]

omit [NeZero N] in
lemma trivialZeroL_im (χ : DirichletCharacter ℂ N) (n : ℕ) : (trivialZeroL χ n).im = 0 := by
  simp [trivialZeroL, dirichletParity_im]

omit [NeZero N] in
/-- Near a trivial zero, `s + a` is not a pole of `Γ((s + a)/2)` except at the zero itself. -/
lemma eventually_not_pole_L (χ : DirichletCharacter ℂ N) (n : ℕ) :
    ∀ᶠ s : ℂ in 𝓝[≠] (trivialZeroL χ n), ∀ m : ℕ, s + dirichletParity χ ≠ -(2 * m) := by
  have h1 : ∀ᶠ s : ℂ in 𝓝 (trivialZeroL χ n), ‖s - trivialZeroL χ n‖ < 1 :=
    Filter.eventually_of_mem (Metric.ball_mem_nhds _ one_pos) fun s hs ↦ by
      simpa [dist_eq_norm] using hs
  filter_upwards [h1.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with s hs hsp m hm
  have hs' : s = -(dirichletParity χ + 2 * m) := by linear_combination hm
  rw [hs'] at hs hsp
  rcases eq_or_ne m n with rfl | hmn
  · exact hsp rfl
  · have : (2 : ℝ) ≤ ‖-(dirichletParity χ + 2 * m) - trivialZeroL χ n‖ := by
      rw [trivialZeroL, show -(dirichletParity χ + 2 * (m : ℂ)) - -(dirichletParity χ + 2 * n) =
        ((2 * ((n : ℤ) - m) : ℤ) : ℂ) by push_cast; ring, Complex.norm_intCast]
      have : (n : ℤ) - m ≠ 0 := by omega
      have h2 := Int.one_le_abs this
      push_cast
      rw [abs_mul, abs_two]
      have : (1 : ℝ) ≤ |((n : ℤ) - m : ℤ)| := by exact_mod_cast h2
      push_cast at this
      linarith
    linarith

/-- At a trivial zero `p ≠ 0`: `-L'/L(s, χ) - (-1)/(s - p)` is bounded near `p`. -/
lemma bddNear_neg_logDeriv_LFunction_trivial {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive)
    (hN : N ≠ 1) (n : ℕ) :
    BddNear (fun s ↦ -(deriv (LFunction χ) s / LFunction χ s) - (-1) / (s - trivialZeroL χ n))
      (trivialZeroL χ n) := by
  have hχ1 := ne_one_of_isPrimitive hχ hN
  set p := trivialZeroL χ n with hp
  set a := dirichletParity χ with ha
  have ha0 := dirichletParity_re_nonneg χ
  have hpre : p.re ≤ 0 := by
    rw [hp, trivialZeroL_re]; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
  have hξ : dirichletXi χ p ≠ 0 := fun h ↦ by
    have := ((dirichletXi_eq_zero_iff hχ hN).mp h).2.1; linarith
  -- the digamma pole
  have hψ := bddNear_digamma_add n
  have hψ' : BddNear (fun s ↦ Complex.digamma ((s + a) / 2) + 1 / ((s + a) / 2 + n)) p := by
    obtain ⟨C, hC⟩ := bddNear_iff_eventually.mp hψ
    refine bddNear_iff_eventually.mpr ⟨C, ?_⟩
    have ht : Tendsto (fun s : ℂ ↦ (s + a) / 2) (𝓝[≠] p) (𝓝[≠] (-(n : ℂ))) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have : (fun s : ℂ ↦ (s + a) / 2) p = -(n : ℂ) := by
          simp only [hp, trivialZeroL, ha]; ring
        rw [← this]
        exact (((continuous_id.add continuous_const).div_const 2).tendsto p).mono_left
          nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with s hs h
        apply hs
        simp only [Set.mem_singleton_iff] at h ⊢
        rw [hp, trivialZeroL]; linear_combination 2 * h
    exact ht.eventually hC
  have hcont : ContinuousAt (fun s ↦ -logDeriv (dirichletXi χ) s + Complex.log N / 2 -
      Complex.log π / 2) p :=
    ((continuousAt_logDeriv_dirichletXi hχ1 hξ).neg.add continuousAt_const).sub continuousAt_const
  have hev : ∀ᶠ s : ℂ in 𝓝[≠] p, (∀ m : ℕ, s + a ≠ -(2 * m)) ∧ dirichletXi χ s ≠ 0 := by
    have h2 : ∀ᶠ s in 𝓝 p, dirichletXi χ s ≠ 0 :=
      ((differentiable_dirichletXi hχ1).continuous.continuousAt).eventually_ne hξ
    filter_upwards [eventually_not_pole_L χ n, h2.filter_mono nhdsWithin_le_nhds] with s h1 h2
    exact ⟨h1, h2⟩
  refine ((bddNear_of_continuousAt hcont).add ((bddNear_const (1 / 2) p).mul hψ')).congr ?_
  filter_upwards [hev, self_mem_nhdsWithin] with s hs hsp
  obtain ⟨hpar, hξs⟩ := hs
  have hG : Gammaℝ (s + a) ≠ 0 := by
    rw [Ne, Gammaℝ_eq_zero_iff, not_exists]; exact hpar
  have hL : LFunction χ s ≠ 0 := by
    intro e; apply hξs
    rw [dirichletXi_eq_mul_LFunction χ hN hG, e, mul_zero]
  have hf := logDeriv_dirichletXi_eq hχ hN hpar hL hξs
  rw [← ha] at hf
  have hsp' : s - p ≠ 0 := sub_ne_zero.mpr hsp
  have h2 : (s + a) / 2 + n = (s - p) / 2 := by rw [hp, trivialZeroL, ← ha]; ring
  rw [h2, hf]
  field_simp
  ring

/-- **Residue of `F(s, χ)` at a trivial zero** `p ≠ 0`: `F(s, χ) - (-1) x^p/p/(s - p)` is bounded
near `p`. -/
lemma bddNear_explicitIntegrandL_trivial {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive)
    (hN : N ≠ 1) {x : ℝ} (hx : 0 < x) (n : ℕ) (hp0 : trivialZeroL χ n ≠ 0) :
    BddNear (fun s ↦ explicitIntegrandL χ x s -
      (-1) * perronKernel x (trivialZeroL χ n) / (s - trivialZeroL χ n)) (trivialZeroL χ n) :=
  bddNear_mul_sub (bddNear_neg_logDeriv_LFunction_trivial hχ hN n)
    (differentiableAt_perronKernel hx hp0)

end NTKB
