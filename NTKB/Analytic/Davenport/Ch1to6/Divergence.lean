/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Topology.Order.IntermediateValue
import NTKB.Analytic.Davenport.Ch1to6.LogL
import NTKB.Analytic.Davenport.Ch1to6.LOnePos

/-!
# Davenport, Chapters 1 and 4: divergence of `∑ p^{-s}` over a progression

For `(a, q) = 1`, `∑_{p ≡ a (mod q)} p^{-s} → ∞` as `s → 1⁺`, hence `∑_{p ≡ a} 1/p` diverges
(§1, p. 4; §4, p. 34). Davenport's argument: in identity (E),
`(1/φ(q)) ∑_χ χ̄(a) log L(s, χ) = ∑_{p^m ≡ a} m^{-1} p^{-ms}`, the term of the principal character
tends to `+∞` (`L(s, χ_0)` has a pole at `1`), while for `χ ≠ χ_0` the function `log L(s, χ)` stays
bounded as `s → 1⁺`, because `L(s, χ)` is continuous at `1` with `L(1, χ) ≠ 0`; the terms with
`m ≥ 2` contribute a bounded amount.

The boundedness of `log L(s, χ)` (the series value of the logarithm) is proved here from the
continuity of the series in `s > 1`: near `s = 1` it differs from the principal logarithm of
`L(s, χ)/L(1, χ)` by a constant (a continuous function with values in `2πiℤ` on an interval is
constant).
-/

noncomputable section

open Complex Filter Topology Finset DirichletCharacter

namespace NTKB.Davenport

variable {N : ℕ}

/-! ### Continuity of `log L(s, χ)` for real `s > 1` -/

/-- `∑_{p, m ≥ 1} (p^m)^{-σ}` converges for `σ > 1`. -/
theorem summable_primePow_rpow {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun pm : Nat.Primes × ℕ ↦ (((pm.1 : ℕ) ^ (pm.2 + 1) : ℕ) : ℝ) ^ (-σ)) := by
  set i : Nat.Primes × ℕ → ℕ := fun pm ↦ (pm.1 : ℕ) ^ (pm.2 + 1) with hi
  have hinj : Function.Injective i := by
    intro a b h
    obtain ⟨h1, h2⟩ := Nat.Prime.pow_inj a.1.prop b.1.prop h
    exact Prod.ext (Subtype.ext h1) h2
  have hsum : Summable (fun n : ℕ ↦ (n : ℝ) ^ (-σ)) := Real.summable_nat_rpow.mpr (by linarith)
  exact hsum.comp_injective hinj

theorem continuous_logLTerm (χ : DirichletCharacter ℂ N) (pm : Nat.Primes × ℕ) :
    Continuous (fun t : ℝ ↦ logLTerm χ t pm) := by
  have hp : ((pm.1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr pm.1.prop.ne_zero
  have h1 : Continuous (fun t : ℝ ↦ ((pm.1 : ℕ) : ℂ) ^ (-(t : ℂ))) :=
    Continuous.const_cpow (continuous_ofReal.neg) (Or.inl hp)
  have h2 : Continuous (fun t : ℝ ↦ (χ ((pm.1 : ℕ) : ZMod N) * ((pm.1 : ℕ) : ℂ) ^ (-(t : ℂ))) ^
      (pm.2 + 1) / ((pm.2 : ℂ) + 1)) :=
    ((continuous_const.mul h1).pow _).div_const _
  exact h2

theorem continuousOn_logL (χ : DirichletCharacter ℂ N) :
    ContinuousOn (fun s : ℝ ↦ logL χ s) (Set.Ioi 1) := by
  intro s hs
  have hs : 1 < s := hs
  set σ := (1 + s) / 2
  have hσ : 1 < σ := by simp only [σ]; linarith
  have hσs : σ < s := by simp only [σ]; linarith
  have hbound : ∀ (pm : Nat.Primes × ℕ) (t : ℝ), t ∈ Set.Ioi σ →
      ‖logLTerm χ t pm‖ ≤ (((pm.1 : ℕ) ^ (pm.2 + 1) : ℕ) : ℝ) ^ (-σ) := by
    intro pm t ht
    refine (norm_logLTerm_le χ pm).trans ?_
    have h1 : (1 : ℝ) ≤ (((pm.1 : ℕ) ^ (pm.2 + 1) : ℕ) : ℝ) := by
      exact_mod_cast Nat.one_le_pow _ _ pm.1.prop.pos
    refine Real.rpow_le_rpow_of_exponent_le h1 ?_
    have : σ < t := ht
    simp only [ofReal_re]
    linarith
  have hcont : ContinuousOn (fun t : ℝ ↦ ∑' pm, logLTerm χ t pm) (Set.Ioi σ) :=
    continuousOn_tsum (fun pm ↦ (continuous_logLTerm χ pm).continuousOn)
      (summable_primePow_rpow hσ) hbound
  exact ((hcont s hσs).continuousAt (Ioi_mem_nhds hσs)).continuousWithinAt

/-- A continuous real function with integer values on a preconnected set is constant. -/
theorem eq_of_continuousOn_intValued {g : ℝ → ℝ} {S : Set ℝ} (hS : IsPreconnected S)
    (hg : ContinuousOn g S) (hint : ∀ s ∈ S, ∃ n : ℤ, g s = n) {a b : ℝ} (ha : a ∈ S)
    (hb : b ∈ S) : g a = g b := by
  have hI : (g '' S).OrdConnected := isPreconnected_iff_ordConnected.mp (hS.image g hg)
  by_contra hne
  have key : ∀ x y : ℝ, x ∈ S → y ∈ S → g x < g y → False := by
    intro x y hx hy hlt
    obtain ⟨n, hn⟩ := hint x hx
    obtain ⟨m, hm⟩ := hint y hy
    have hmem : g x + 1 / 2 ∈ g '' S :=
      hI.out (Set.mem_image_of_mem g hx) (Set.mem_image_of_mem g hy)
        ⟨by linarith, by
          rw [hn, hm] at hlt ⊢
          have : n < m := by exact_mod_cast hlt
          have : (n : ℝ) + 1 ≤ m := by exact_mod_cast this
          linarith⟩
    obtain ⟨c, hc, hgc⟩ := hmem
    obtain ⟨k, hk⟩ := hint c hc
    rw [hk, hn] at hgc
    have : (2 * k : ℝ) = 2 * n + 1 := by linarith
    have : (2 * k : ℤ) = 2 * n + 1 := by exact_mod_cast this
    omega
  rcases lt_or_gt_of_ne hne with h | h
  · exact key a b ha hb h
  · exact key b a hb ha h

/-- `|log x| ≤ 1` for `1/2 ≤ x ≤ 3/2`. -/
theorem abs_log_le_one {x : ℝ} (h1 : 1 / 2 ≤ x) (h2 : x ≤ 3 / 2) : |Real.log x| ≤ 1 := by
  have hx : 0 < x := by linarith
  rw [abs_le]
  constructor
  · have := Real.one_sub_inv_le_log_of_pos hx
    have : x⁻¹ ≤ 2 := by rw [inv_le_comm₀ hx (by norm_num)]; linarith
    linarith
  · have := Real.log_le_sub_one_of_pos hx
    linarith

/-- **Davenport §1, p. 5; §4, p. 34.** For `χ ≠ χ_0`, `log L(s, χ)` is bounded as `s → 1⁺`. -/
theorem exists_bound_logL [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) :
    ∃ C δ : ℝ, 0 < δ ∧ ∀ s : ℝ, s ∈ Set.Ioo 1 (1 + δ) → ‖logL χ s‖ ≤ C := by
  set L1 := LFunction χ 1
  have hL1 : L1 ≠ 0 := LFunction_apply_one_ne_zero hχ
  have hL1n : 0 < ‖L1‖ := norm_pos_iff.mpr hL1
  -- `L(s) → L(1)`: choose `δ` with `‖L(s) - L(1)‖ < ‖L(1)‖/2` on `(1, 1 + δ)`
  have hlim := tendsto_LFunction_one hχ
  obtain ⟨δ, hδ, hball⟩ : ∃ δ > 0, ∀ s : ℝ, s ∈ Set.Ioo 1 (1 + δ) →
      ‖LFunction χ s - L1‖ < ‖L1‖ / 2 := by
    have := (Metric.tendsto_nhds.mp hlim) (‖L1‖ / 2) (by positivity)
    rw [Filter.Eventually, mem_nhdsWithin] at this
    obtain ⟨U, hU, h1U, hUsub⟩ := this
    obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU 1 h1U
    refine ⟨ε, hε, fun s hs ↦ ?_⟩
    have hsU : s ∈ U := hεU (by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith [hs.1, hs.2])
    have := hUsub ⟨hsU, hs.1⟩
    simpa [dist_eq_norm] using this
  set S : Set ℝ := Set.Ioo 1 (1 + δ)
  set w : ℝ → ℂ := fun s ↦ LFunction χ s / L1
  have hw : ∀ s ∈ S, ‖w s - 1‖ < 1 / 2 := by
    intro s hs
    simp only [w]
    rw [show LFunction χ s / L1 - 1 = (LFunction χ s - L1) / L1 by field_simp, norm_div]
    rw [div_lt_iff₀ hL1n]
    linarith [hball s hs]
  have hwslit : ∀ s ∈ S, w s ∈ slitPlane := by
    intro s hs
    rw [mem_slitPlane_iff]; left
    have := hw s hs
    have h2 : |(w s - 1).re| ≤ ‖w s - 1‖ := abs_re_le_norm _
    simp only [sub_re, one_re] at h2
    rw [abs_le] at h2
    linarith
  set h : ℝ → ℂ := fun s ↦ logL χ s - log (w s)
  have hexp : ∀ s ∈ S, cexp (h s) = L1 := by
    intro s hs
    have hs1 : 1 < (s : ℂ).re := by simpa using hs.1
    simp only [h]
    rw [Complex.exp_sub, exp_logL χ hs1, exp_log (slitPlane_ne_zero (hwslit s hs))]
    have hne : LFunction χ s ≠ 0 := by rw [← exp_logL χ hs1]; exact Complex.exp_ne_zero _
    simp only [w]
    field_simp
  have hcontw : ContinuousOn w S := by
    have : ContinuousOn (fun s : ℝ ↦ LFunction χ s) S := by
      have := (differentiable_LFunction hχ).continuous
      exact (this.comp continuous_ofReal).continuousOn
    exact this.div_const _
  have hconth : ContinuousOn h S := by
    refine ((continuousOn_logL χ).mono fun s (hs : s ∈ S) ↦ (hs.1 : s ∈ Set.Ioi 1)).sub ?_
    exact ContinuousOn.clog hcontw hwslit
  -- `h` is constant on `S`
  set s₀ : ℝ := 1 + δ / 2
  have hs₀ : s₀ ∈ S := ⟨by simp only [s₀]; linarith, by simp only [s₀]; linarith⟩
  have hconst : ∀ s ∈ S, h s = h s₀ := by
    have hk : ∀ s ∈ S, ∃ n : ℤ, h s - h s₀ = n * (2 * Real.pi * I) := by
      intro s hs
      apply Complex.exp_eq_one_iff.mp
      rw [Complex.exp_sub, hexp s hs, hexp s₀ hs₀, div_self hL1]
    set g : ℝ → ℝ := fun s ↦ (h s - h s₀).im / (2 * Real.pi)
    have hgint : ∀ s ∈ S, ∃ n : ℤ, g s = n := by
      intro s hs
      obtain ⟨n, hn⟩ := hk s hs
      refine ⟨n, ?_⟩
      simp only [g, hn]
      simp [Real.pi_pos.ne']
    have hgc : ContinuousOn g S :=
      ((continuous_im.comp_continuousOn (hconth.sub continuousOn_const))).div_const _
    intro s hs
    have := eq_of_continuousOn_intValued (isPreconnected_Ioo) hgc hgint hs hs₀
    obtain ⟨n, hn⟩ := hk s hs
    have hg0 : g s₀ = 0 := by simp [g]
    rw [hg0] at this
    have hn0 : (n : ℝ) = 0 := by
      simp only [g, hn] at this
      have : (n : ℝ) * (2 * Real.pi) / (2 * Real.pi) = 0 := by simpa using this
      rwa [mul_div_cancel_right₀ _ (by positivity)] at this
    have : h s - h s₀ = 0 := by rw [hn, show (n : ℂ) = ((n : ℝ) : ℂ) by simp, hn0]; simp
    exact sub_eq_zero.mp this
  -- the bound
  refine ⟨‖h s₀‖ + (1 + Real.pi), δ, hδ, fun s hs ↦ ?_⟩
  have hls : logL χ s = h s₀ + log (w s) := by
    rw [← hconst s hs]; simp only [h]; ring
  rw [hls]
  refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
  have hnw : 1 / 2 ≤ ‖w s‖ ∧ ‖w s‖ ≤ 3 / 2 := by
    have := hw s hs
    constructor
    · have := abs_norm_sub_norm_le (w s) 1
      rw [abs_le, norm_one] at this
      linarith
    · have := abs_norm_sub_norm_le (w s) 1
      rw [abs_le, norm_one] at this
      linarith
  calc ‖log (w s)‖ ≤ |(log (w s)).re| + |(log (w s)).im| := norm_le_abs_re_add_abs_im _
    _ ≤ 1 + Real.pi := by
      rw [log_re, log_im]
      exact add_le_add (abs_log_le_one hnw.1 hnw.2) (abs_arg_le_pi _)

/-- `log L(s, χ)` is eventually bounded as `s → 1⁺` for `χ ≠ χ_0`. -/
theorem eventually_norm_logL_le [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) :
    ∃ C : ℝ, ∀ᶠ s : ℝ in 𝓝[>] 1, ‖logL χ s‖ ≤ C := by
  obtain ⟨C, δ, hδ, h⟩ := exists_bound_logL hχ
  refine ⟨C, ?_⟩
  filter_upwards [Ioo_mem_nhdsGT (show (1 : ℝ) < 1 + δ by linarith)] with s hs
  exact h s hs

/-- **Davenport §1, p. 4; §4, p. 34.** For the principal character, `Re log L(s, χ_0) → +∞` as
`s → 1⁺` (`L(s, χ_0)` has a pole at `s = 1`). -/
theorem tendsto_re_logL_one [NeZero N] :
    Tendsto (fun s : ℝ ↦ (logL (1 : DirichletCharacter ℂ N) s).re) (𝓝[>] 1) atTop := by
  set R : ℂ := ∏ p ∈ N.primeFactors, (1 - (p : ℂ)⁻¹)
  have hR : R ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr fun p hp ↦ ?_
    have hp2 : (1 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
    intro h
    have : (p : ℂ)⁻¹ = 1 := by linear_combination -h
    have : (p : ℂ) = 1 := by simpa using congrArg (·⁻¹) this
    have : (p : ℝ) = 1 := by exact_mod_cast this
    linarith
  have hres : Tendsto (fun s : ℝ ↦ ((s : ℂ) - 1) * LFunction (1 : DirichletCharacter ℂ N) s)
      (𝓝[>] 1) (𝓝 R) := by
    have h1 := LFunctionTrivChar_residue_one (N := N)
    have h2 : Tendsto (fun s : ℝ ↦ (s : ℂ)) (𝓝[>] 1) (𝓝[≠] (1 : ℂ)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · have := (continuous_ofReal.tendsto (1 : ℝ)).mono_left
          (nhdsWithin_le_nhds (s := Set.Ioi (1 : ℝ)))
        simpa using this
      · filter_upwards [self_mem_nhdsWithin] with s hs
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        intro h
        have : s = 1 := by exact_mod_cast h
        exact (ne_of_gt (show (1 : ℝ) < s from hs)) this
    exact h1.comp h2
  -- `‖L(s)‖ ≥ (‖R‖/2)/(s - 1)` eventually
  have hev : ∀ᶠ s : ℝ in 𝓝[>] 1,
      ‖R‖ / 2 * (s - 1)⁻¹ ≤ ‖LFunction (1 : DirichletCharacter ℂ N) s‖ := by
    have hR2 : ‖R‖ / 2 < ‖R‖ := by have := norm_pos_iff.mpr hR; linarith
    filter_upwards [(hres.norm).eventually (lt_mem_nhds hR2), self_mem_nhdsWithin] with s h1 hs
    have hs1 : (0 : ℝ) < s - 1 := by have : (1 : ℝ) < s := hs; linarith
    rw [norm_mul, show (s : ℂ) - 1 = ((s - 1 : ℝ) : ℂ) by push_cast; ring, norm_real,
      Real.norm_eq_abs, abs_of_pos hs1] at h1
    rw [← div_eq_mul_inv, div_le_iff₀ hs1]
    linarith
  have hinf : Tendsto (fun s : ℝ ↦ ‖R‖ / 2 * (s - 1)⁻¹) (𝓝[>] 1) atTop := by
    refine Tendsto.const_mul_atTop (by have := norm_pos_iff.mpr hR; linarith) ?_
    refine tendsto_inv_nhdsGT_zero.comp ?_
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have := ((continuous_sub_right (1 : ℝ)).tendsto (1 : ℝ)).mono_left
        (nhdsWithin_le_nhds (s := Set.Ioi (1 : ℝ)))
      simpa using this
    · filter_upwards [self_mem_nhdsWithin] with s hs
      exact sub_pos.mpr (show (1 : ℝ) < s from hs)
  have hnorm : Tendsto (fun s : ℝ ↦ ‖LFunction (1 : DirichletCharacter ℂ N) s‖) (𝓝[>] 1) atTop :=
    tendsto_atTop_mono' _ hev hinf
  refine (Real.tendsto_log_atTop.comp hnorm).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs1 : 1 < (s : ℂ).re := by simpa using hs
  simp only [Function.comp_apply]
  rw [← exp_logL _ hs1, Complex.norm_exp, Real.log_exp]

/-- The right side of (E) as a real number: `T(s) = ∑_{p^m ≡ a} m^{-1} p^{-ms}`. -/
def primePowSum (a : ZMod N) (s : ℝ) : ℝ :=
  ∑' pm : Nat.Primes × ℕ, if (((pm.1 : ℕ) ^ (pm.2 + 1) : ℕ) : ZMod N) = a then
    (((pm.1 : ℕ) : ℝ) ^ (-s)) ^ (pm.2 + 1) / (pm.2 + 1) else 0

theorem sum_inv_mul_logL_real [NeZero N] {a : ZMod N} (ha : IsUnit a) {s : ℝ} (hs : 1 < s) :
    (1 / N.totient : ℂ) * ∑ χ : DirichletCharacter ℂ N, χ a⁻¹ * logL χ s =
      (primePowSum a s : ℂ) := by
  have hs' : 1 < (s : ℂ).re := by simpa using hs
  rw [sum_inv_mul_logL ha hs', primePowSum, ofReal_tsum]
  refine tsum_congr fun pm ↦ ?_
  split_ifs
  · rw [← ofReal_neg, ← ofReal_natCast, ← ofReal_cpow (Nat.cast_nonneg _)]
    push_cast; ring
  · simp

/-- `T(s) → +∞` as `s → 1⁺`. -/
theorem tendsto_primePowSum [NeZero N] {a : ZMod N} (ha : IsUnit a) :
    Tendsto (primePowSum a) (𝓝[>] 1) atTop := by
  classical
  have hφ : (0 : ℝ) < N.totient := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos N)
  have hbd : ∀ χ : DirichletCharacter ℂ N, ∃ C : ℝ,
      χ ≠ 1 → ∀ᶠ s : ℝ in 𝓝[>] 1, ‖logL χ s‖ ≤ C := by
    intro χ
    by_cases hχ : χ = 1
    · exact ⟨0, fun h ↦ absurd hχ h⟩
    · obtain ⟨C, hC⟩ := eventually_norm_logL_le hχ
      exact ⟨C, fun _ ↦ hC⟩
  choose C hC using hbd
  set B := ∑ χ ∈ univ.erase (1 : DirichletCharacter ℂ N), C χ
  have hev : ∀ᶠ s : ℝ in 𝓝[>] 1, ∀ χ ∈ univ.erase (1 : DirichletCharacter ℂ N),
      ‖logL χ s‖ ≤ C χ := by
    rw [Filter.eventually_all_finset]
    intro χ hχ
    exact hC χ (Finset.ne_of_mem_erase hχ)
  have hlow : ∀ᶠ s : ℝ in 𝓝[>] 1,
      ((logL (1 : DirichletCharacter ℂ N) s).re - B) / N.totient ≤ primePowSum a s := by
    filter_upwards [hev, self_mem_nhdsWithin] with s hs hs1
    have hE := sum_inv_mul_logL_real ha (show 1 < s from hs1)
    have hre := congrArg Complex.re hE
    rw [ofReal_re] at hre
    set Z := ∑ χ : DirichletCharacter ℂ N, χ a⁻¹ * logL χ s
    have hZ : ((1 / N.totient : ℂ) * Z).re = Z.re / N.totient := by
      rw [show (1 / N.totient : ℂ) = ((1 / N.totient : ℝ) : ℂ) by push_cast; ring,
        re_ofReal_mul]
      ring
    have hinvunit : IsUnit a⁻¹ :=
      ⟨⟨a⁻¹, a, ZMod.inv_mul_of_unit a ha, ZMod.mul_inv_of_unit a ha⟩, rfl⟩
    have hsplit : Z = logL (1 : DirichletCharacter ℂ N) s +
        ∑ χ ∈ univ.erase (1 : DirichletCharacter ℂ N), χ a⁻¹ * logL χ s := by
      simp only [Z]
      rw [← Finset.add_sum_erase _ _ (mem_univ (1 : DirichletCharacter ℂ N)),
        MulChar.one_apply hinvunit, one_mul]
    have hrest : -B ≤ (∑ χ ∈ univ.erase (1 : DirichletCharacter ℂ N), χ a⁻¹ * logL χ s).re := by
      have h1 : ‖∑ χ ∈ univ.erase (1 : DirichletCharacter ℂ N), χ a⁻¹ * logL χ s‖ ≤ B := by
        refine (norm_sum_le _ _).trans (sum_le_sum fun χ hχ ↦ ?_)
        rw [norm_mul]
        calc ‖χ a⁻¹‖ * ‖logL χ s‖ ≤ 1 * C χ :=
              mul_le_mul (DirichletCharacter.norm_le_one χ _) (hs χ hχ) (norm_nonneg _)
                zero_le_one
          _ = C χ := one_mul _
      have h3 := abs_re_le_norm (∑ χ ∈ univ.erase (1 : DirichletCharacter ℂ N),
        χ a⁻¹ * logL χ s)
      have h2 := neg_abs_le (∑ χ ∈ univ.erase (1 : DirichletCharacter ℂ N),
        χ a⁻¹ * logL χ s).re
      linarith
    rw [hZ] at hre
    rw [← hre, div_le_div_iff_of_pos_right hφ, hsplit, add_re]
    linarith
  have hdiv : Tendsto (fun s : ℝ ↦ ((logL (1 : DirichletCharacter ℂ N) s).re - B) / N.totient)
      (𝓝[>] 1) atTop :=
    (tendsto_atTop_add_const_right _ (-B) tendsto_re_logL_one).atTop_div_const hφ
  exact tendsto_atTop_mono' _ hlow hdiv

/-- The terms of `T(s)`. -/
def primePowTerm (a : ZMod N) (s : ℝ) (pm : Nat.Primes × ℕ) : ℝ :=
  if (((pm.1 : ℕ) ^ (pm.2 + 1) : ℕ) : ZMod N) = a then
    (((pm.1 : ℕ) : ℝ) ^ (-s)) ^ (pm.2 + 1) / (pm.2 + 1) else 0

theorem primePowTerm_nonneg (a : ZMod N) (s : ℝ) (pm : Nat.Primes × ℕ) :
    0 ≤ primePowTerm a s pm := by
  unfold primePowTerm; split_ifs
  · positivity
  · exact le_rfl

theorem primePowTerm_le_pow (a : ZMod N) (s : ℝ) (pm : Nat.Primes × ℕ) :
    primePowTerm a s pm ≤ (((pm.1 : ℕ) : ℝ) ^ (-s)) ^ (pm.2 + 1) := by
  unfold primePowTerm; split_ifs
  · have h0 : 0 ≤ (((pm.1 : ℕ) : ℝ) ^ (-s)) ^ (pm.2 + 1) := by positivity
    exact div_le_self h0 (by have : (0 : ℝ) ≤ pm.2 := Nat.cast_nonneg _; linarith)
  · positivity

theorem rpow_neg_pow_eq (pm : Nat.Primes × ℕ) (s : ℝ) :
    (((pm.1 : ℕ) : ℝ) ^ (-s)) ^ (pm.2 + 1) = (((pm.1 : ℕ) ^ (pm.2 + 1) : ℕ) : ℝ) ^ (-s) := by
  have hp : (0 : ℝ) ≤ (pm.1 : ℕ) := Nat.cast_nonneg _
  rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul hp, ← Real.rpow_natCast,
    ← Real.rpow_mul hp, mul_comm]

theorem summable_primePowTerm (a : ZMod N) {s : ℝ} (hs : 1 < s) :
    Summable (primePowTerm a s) :=
  Summable.of_nonneg_of_le (primePowTerm_nonneg a s)
    (fun pm ↦ (primePowTerm_le_pow a s pm).trans (rpow_neg_pow_eq pm s).le)
    (summable_primePow_rpow hs)

/-- The bound `2 p^{-2} 2^{-m}` for the terms with `m ≥ 1`. -/
theorem summable_tailBound :
    Summable (fun pm : Nat.Primes × ℕ ↦ (2 * (((pm.1 : ℕ) : ℝ) ^ 2)⁻¹) * ((1 : ℝ) / 2) ^ pm.2) := by
  have h0 : Summable (fun n : ℕ ↦ ((n : ℝ) ^ 2)⁻¹) := Real.summable_nat_pow_inv.mpr one_lt_two
  have h1 : Summable (fun p : Nat.Primes ↦ 2 * (((p : ℕ) : ℝ) ^ 2)⁻¹) := by
    have : Summable (fun p : Nat.Primes ↦ (((p : ℕ) : ℝ) ^ 2)⁻¹) :=
      h0.comp_injective (i := fun p : Nat.Primes ↦ (p : ℕ)) Subtype.val_injective
    exact this.mul_left 2
  have h2 : Summable (fun m : ℕ ↦ ((1 : ℝ) / 2) ^ m) := summable_geometric_two
  exact Summable.mul_of_nonneg (f := fun p : Nat.Primes ↦ 2 * (((p : ℕ) : ℝ) ^ 2)⁻¹)
    (g := fun m : ℕ ↦ ((1 : ℝ) / 2) ^ m) h1 h2 (by intro p; positivity) (by intro m; positivity)

/-- `T(s) ≤ ∑_{p ≡ a} p^{-s} + B` for `s > 1`: the terms with `m ≥ 2` are bounded. -/
theorem primePowSum_le (a : ZMod N) {s : ℝ} (hs : 1 < s) :
    primePowSum a s ≤
      (∑' p : Nat.Primes, if ((p : ℕ) : ZMod N) = a then ((p : ℕ) : ℝ) ^ (-s) else 0) +
        ∑' pm : Nat.Primes × ℕ, (2 * (((pm.1 : ℕ) : ℝ) ^ 2)⁻¹) * ((1 : ℝ) / 2) ^ pm.2 := by
  set t := primePowTerm a s
  set t1 : Nat.Primes × ℕ → ℝ := fun pm ↦ if pm.2 = 0 then t pm else 0
  set t2 : Nat.Primes × ℕ → ℝ := fun pm ↦ if pm.2 = 0 then 0 else t pm
  have ht : ∀ pm, t pm = t1 pm + t2 pm := by
    intro pm; simp only [t1, t2]; split_ifs <;> simp
  have hsum := summable_primePowTerm a hs
  have hs1 : Summable t1 := Summable.of_nonneg_of_le
    (fun pm ↦ by simp only [t1]; split_ifs; exacts [primePowTerm_nonneg _ _ _, le_rfl])
    (fun pm ↦ by
      simp only [t1]; split_ifs; exacts [le_rfl, primePowTerm_nonneg _ _ _]) hsum
  have hs2 : Summable t2 := Summable.of_nonneg_of_le
    (fun pm ↦ by simp only [t2]; split_ifs; exacts [le_rfl, primePowTerm_nonneg _ _ _])
    (fun pm ↦ by
      simp only [t2]; split_ifs; exacts [primePowTerm_nonneg _ _ _, le_rfl]) hsum
  have hT : primePowSum a s = ∑' pm, t1 pm + ∑' pm, t2 pm := by
    rw [← hs1.tsum_add hs2, primePowSum]
    exact tsum_congr fun pm ↦ ht pm
  rw [hT]
  refine add_le_add (le_of_eq ?_) ?_
  · -- the terms `m = 1`
    have hinj : Function.Injective (fun p : Nat.Primes ↦ (p, 0)) := fun a b h ↦ by
      simpa using congrArg Prod.fst h
    rw [← hinj.tsum_eq]
    · refine tsum_congr fun p ↦ ?_
      simp only [t1, t, primePowTerm, if_true, pow_one, zero_add, Nat.cast_zero]
      split_ifs <;> simp
    · intro pm hpm
      simp only [Function.mem_support, t1] at hpm
      split_ifs at hpm with h
      · exact ⟨pm.1, by rw [← h]⟩
      · exact absurd rfl hpm
  · refine hs2.tsum_le_tsum (fun pm ↦ ?_) summable_tailBound
    simp only [t2]
    split_ifs with h0
    · positivity
    · obtain ⟨m, hm⟩ : ∃ m, pm.2 = m + 1 := ⟨pm.2 - 1, by omega⟩
      have hp2 : (2 : ℝ) ≤ (pm.1 : ℕ) := by exact_mod_cast pm.1.prop.two_le
      have hp0 : (0 : ℝ) < (pm.1 : ℕ) := by linarith
      have hx : ((pm.1 : ℕ) : ℝ) ^ (-s) ≤ ((pm.1 : ℕ) : ℝ)⁻¹ := by
        rw [← Real.rpow_neg_one]
        exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      have hx0 : 0 ≤ ((pm.1 : ℕ) : ℝ) ^ (-s) := by positivity
      have hinv : ((pm.1 : ℕ) : ℝ)⁻¹ ≤ 1 / 2 := by
        rw [inv_le_comm₀ hp0 (by norm_num)]; linarith
      refine (primePowTerm_le_pow a s pm).trans ?_
      rw [hm]
      calc (((pm.1 : ℕ) : ℝ) ^ (-s)) ^ (m + 1 + 1)
          ≤ (((pm.1 : ℕ) : ℝ)⁻¹) ^ (m + 1 + 1) := pow_le_pow_left₀ hx0 hx _
        _ = (((pm.1 : ℕ) : ℝ) ^ 2)⁻¹ * (((pm.1 : ℕ) : ℝ)⁻¹) ^ m := by
          generalize ((pm.1 : ℕ) : ℝ) = x
          rw [inv_pow, inv_pow, ← mul_inv, ← pow_add, add_comm 2 m]
        _ ≤ (((pm.1 : ℕ) : ℝ) ^ 2)⁻¹ * ((1 : ℝ) / 2) ^ m := by
          gcongr
        _ = 2 * (((pm.1 : ℕ) : ℝ) ^ 2)⁻¹ * ((1 : ℝ) / 2) ^ (m + 1) := by ring

/-- **Davenport §1, p. 4; §4, p. 34.** For `(a, q) = 1`,
`∑_{p ≡ a (mod q)} p^{-s} → +∞` as `s → 1⁺`. -/
@[kb "davenport1980" "Ch 1, p. 4; Ch 4, p. 34"]
theorem tendsto_sum_prime_rpow_atTop [NeZero N] {a : ZMod N} (ha : IsUnit a) :
    Tendsto (fun s : ℝ ↦ ∑' p : Nat.Primes,
      if ((p : ℕ) : ZMod N) = a then ((p : ℕ) : ℝ) ^ (-s) else 0) (𝓝[>] 1) atTop := by
  set B := ∑' pm : Nat.Primes × ℕ, (2 * (((pm.1 : ℕ) : ℝ) ^ 2)⁻¹) * ((1 : ℝ) / 2) ^ pm.2
  refine tendsto_atTop_mono' _ ?_
    (tendsto_atTop_add_const_right _ (-B) (tendsto_primePowSum ha))
  filter_upwards [self_mem_nhdsWithin] with s hs
  have := primePowSum_le a (show 1 < s from hs)
  linarith

/-- **Davenport §1, p. 4; §4, p. 34.** For `(a, q) = 1`, the series `∑_{p ≡ a (mod q)} 1/p`
diverges. -/
@[kb "davenport1980" "Ch 1, p. 4; Ch 4, p. 34"]
theorem not_summable_one_div_prime [NeZero N] {a : ZMod N} (ha : IsUnit a) :
    ¬ Summable (fun p : Nat.Primes ↦ if ((p : ℕ) : ZMod N) = a then 1 / ((p : ℕ) : ℝ) else 0) := by
  intro hsum
  set M := ∑' p : Nat.Primes, if ((p : ℕ) : ZMod N) = a then 1 / ((p : ℕ) : ℝ) else 0
  have hle : ∀ᶠ s : ℝ in 𝓝[>] 1, (∑' p : Nat.Primes,
      if ((p : ℕ) : ZMod N) = a then ((p : ℕ) : ℝ) ^ (-s) else 0) ≤ M := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs : 1 < s := hs
    have hterm : ∀ p : Nat.Primes, (if ((p : ℕ) : ZMod N) = a then ((p : ℕ) : ℝ) ^ (-s) else 0) ≤
        if ((p : ℕ) : ZMod N) = a then 1 / ((p : ℕ) : ℝ) else 0 := by
      intro p
      split_ifs
      · have hp1 : (1 : ℝ) ≤ (p : ℕ) := by exact_mod_cast p.prop.one_lt.le
        rw [one_div, ← Real.rpow_neg_one]
        exact Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
      · exact le_rfl
    have hnn : ∀ p : Nat.Primes,
        0 ≤ (if ((p : ℕ) : ZMod N) = a then ((p : ℕ) : ℝ) ^ (-s) else 0) := by
      intro p; split_ifs
      · positivity
      · exact le_rfl
    exact (Summable.of_nonneg_of_le hnn hterm hsum).tsum_le_tsum hterm hsum
  have hgt := (tendsto_sum_prime_rpow_atTop ha).eventually (eventually_gt_atTop M)
  obtain ⟨s, h1, h2⟩ := (hle.and hgt).exists
  linarith

end NTKB.Davenport
