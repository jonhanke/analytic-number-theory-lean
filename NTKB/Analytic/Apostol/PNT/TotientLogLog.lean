/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Apostol.PNT.MertensProduct
import Mathlib.NumberTheory.Primorial

/-!
# The minimal order of `φ(n)` (Apostol, Theorem 13.14)

Let `c` be the constant of Theorem 13.13 (`∏_{p ≤ x}(1 - 1/p) log x → c`). For every `ε > 0`:
(a) `φ(n) > (1 - ε) c n / log log n` for all large `n`;
(b) `φ(n) < (1 + ε) c n / log log n` for infinitely many `n`.

Apostol's proofs. (b): `n = ∏_{p ≤ x} p`, so `φ(n)/n = P(x)` and `log n = θ(x)`; Chebyshev's
bounds `θ(x) ≍ x` (Theorem 4.10) give `log log n = log x + O(1)` (Apostol uses `θ(x) ~ x`; only
`log θ(x) ~ log x` is needed). (a): split `φ(n)/n = ∏_{p ∣ n}(1 - 1/p)` at `p = log n`; the first
part is at least `P(log n)`, and the `f(n) ≤ log n / log log n` primes `p ∣ n` with `p > log n`
contribute at least `(1 - 1/log n)^{f(n)} ≥ e^{-2/log log n} → 1`.
-/

open Finset Real Filter Topology Chebyshev

namespace NTKB.Apostol

lemma totient_eq_mul_prod_real (n : ℕ) :
    (Nat.totient n : ℝ) = n * ∏ p ∈ n.primeFactors, (1 - 1 / (p : ℝ)) := by
  have := congrArg (Rat.cast : ℚ → ℝ) (Nat.totient_eq_mul_prod_factors n)
  push_cast at this
  simpa [one_div] using this

/-- `log(1 - x) ≥ -2x` for `0 ≤ x ≤ 1/2`. -/
lemma neg_two_mul_le_log_one_sub {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    -2 * x ≤ Real.log (1 - x) := by
  rcases hx0.eq_or_lt with rfl | hx0
  · simp
  have habs : |x| = x := abs_of_pos hx0
  have h1 := Real.abs_log_sub_add_sum_range_le (x := x) (by rw [habs]; linarith) 1
  simp only [range_one, sum_singleton, zero_add, pow_one, Nat.cast_zero, div_one, habs] at h1
  have h2 : x ^ 2 / (1 - x) ≤ x := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  linarith [(abs_le.mp h1).1]

/-- The key inequality of part (a): `φ(n)/n ≥ P(log n) e^{-2/log log n}` once `log n ≥ 2`. -/
lemma totient_div_ge {n : ℕ} (hn : 2 ≤ Real.log n) :
    mertensProd (Real.log n) * Real.exp (-2 / Real.log (Real.log n)) ≤ (Nat.totient n : ℝ) / n := by
  set L := Real.log n with hL
  have hn0 : n ≠ 0 := by
    rintro rfl; norm_num [hL] at hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
  have hL0 : 0 < L := by linarith
  have hlogL : 0 < Real.log L := Real.log_pos (by linarith)
  rw [totient_eq_mul_prod_real, mul_div_cancel_left₀ _ hnpos.ne']
  have hfac : ∀ p ∈ n.primeFactors, 0 ≤ 1 - 1 / (p : ℝ) ∧ 1 - 1 / (p : ℝ) ≤ 1 := fun p hp => by
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt.le
    constructor
    · rw [sub_nonneg]; exact (div_le_one (by linarith)).mpr hp1
    · have : 0 ≤ 1 / (p : ℝ) := by positivity
      linarith
  rw [← prod_filter_mul_prod_filter_not n.primeFactors (fun p : ℕ => (p : ℝ) ≤ L)]
  set S₁ := n.primeFactors.filter (fun p : ℕ => (p : ℝ) ≤ L)
  set S₂ := n.primeFactors.filter (fun p : ℕ => ¬ (p : ℝ) ≤ L)
  -- first part
  have h1 : mertensProd L ≤ ∏ p ∈ S₁, (1 - 1 / (p : ℝ)) := by
    set T := (Ioc 0 ⌊L⌋₊).filter Nat.Prime
    have hsub : S₁ ⊆ T := fun p hp => by
      obtain ⟨hp, hpL⟩ := mem_filter.mp hp
      have hpr := Nat.prime_of_mem_primeFactors hp
      exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨hpr.pos, Nat.le_floor hpL⟩, hpr⟩
    have hT : ∀ p ∈ T, 0 ≤ 1 - 1 / (p : ℝ) ∧ 1 - 1 / (p : ℝ) ≤ 1 := fun p hp => by
      have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (mem_filter.mp hp).2.one_lt.le
      constructor
      · rw [sub_nonneg]; exact (div_le_one (by linarith)).mpr hp1
      · have : 0 ≤ 1 / (p : ℝ) := by positivity
        linarith
    rw [mertensProd, ← prod_sdiff hsub]
    refine mul_le_of_le_one_left (prod_nonneg fun p hp => (hT p (hsub hp)).1) ?_
    exact prod_le_one₀ (fun p hp => (hT p (mem_sdiff.mp hp).1).1)
      fun p hp => (hT p (mem_sdiff.mp hp).1).2
  -- second part: `(1 - 1/L)^{#S₂}` with `#S₂ log L ≤ L`
  have hcard : (S₂.card : ℝ) * Real.log L ≤ L := by
    have hdvd : ∏ p ∈ S₂, p ∣ n :=
      (prod_dvd_prod_of_subset _ _ _ (filter_subset _ _)).trans (Nat.prod_primeFactors_dvd n)
    have hle : (∏ p ∈ S₂, (p : ℝ)) ≤ n := by
      rw [← Nat.cast_prod]; exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hdvd
    have hpow : L ^ S₂.card ≤ ∏ p ∈ S₂, (p : ℝ) := by
      rw [← prod_const]
      exact prod_le_prod₀ (fun _ _ => hL0.le) fun p hp => (not_le.mp (mem_filter.mp hp).2).le
    have := Real.log_le_log (by positivity) (hpow.trans hle)
    rwa [Real.log_pow, ← hL] at this
  have h2 : Real.exp (-2 / Real.log L) ≤ ∏ p ∈ S₂, (1 - 1 / (p : ℝ)) := by
    have hq0 : 0 ≤ 1 / L := by positivity
    have hq : 1 / L ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hn
    have hbase : 0 < 1 - 1 / L := by linarith
    calc Real.exp (-2 / Real.log L) ≤ Real.exp (S₂.card * Real.log (1 - 1 / L)) := by
          rw [Real.exp_le_exp]
          have hlog1 := neg_two_mul_le_log_one_sub hq0 hq
          have hk : (S₂.card : ℝ) ≤ L / Real.log L := by rw [le_div_iff₀ hlogL]; exact hcard
          have hk0 : (0 : ℝ) ≤ S₂.card := by positivity
          calc -2 / Real.log L = (L / Real.log L) * (-2 * (1 / L)) := by field_simp
            _ ≤ (S₂.card : ℝ) * (-2 * (1 / L)) := by
                apply mul_le_mul_of_nonpos_right hk; have : 0 < 1 / L := by positivity
                linarith
            _ ≤ S₂.card * Real.log (1 - 1 / L) := mul_le_mul_of_nonneg_left hlog1 hk0
      _ = (1 - 1 / L) ^ S₂.card := by rw [Real.exp_nat_mul, Real.exp_log hbase]
      _ = ∏ _p ∈ S₂, (1 - 1 / L) := (prod_const _).symm
      _ ≤ ∏ p ∈ S₂, (1 - 1 / (p : ℝ)) := by
          refine prod_le_prod₀ (fun _ _ => hbase.le) fun p hp => ?_
          have hpL : L < p := not_le.mp (mem_filter.mp hp).2
          have : 1 / (p : ℝ) ≤ 1 / L := one_div_le_one_div_of_le hL0 hpL.le
          linarith
  exact mul_le_mul h1 h2 (Real.exp_pos _).le
    (prod_nonneg fun p hp => (hfac p (mem_filter.mp hp).1).1)

lemma filter_prime_Ioc_eq_primesLE (m : ℕ) : (Ioc 0 m).filter Nat.Prime = Nat.primesLE m := by
  ext p
  simp only [mem_filter, mem_Ioc, Nat.mem_primesLE]
  constructor
  · rintro ⟨⟨-, h⟩, hp⟩; exact ⟨h, hp⟩
  · rintro ⟨h, hp⟩; exact ⟨⟨hp.pos, h⟩, hp⟩

lemma totient_primorial_div (m : ℕ) :
    (Nat.totient (primorial m) : ℝ) = primorial m * mertensProd m := by
  rw [totient_eq_mul_prod_real, primeFactors_primorial, mertensProd, Nat.floor_natCast,
    filter_prime_Ioc_eq_primesLE]

/-- `log θ(m) / log m → 1` (from Chebyshev's bounds, Theorem 4.10). -/
lemma tendsto_log_theta_div_log :
    Tendsto (fun m : ℕ => Real.log (θ m) / Real.log m) atTop (𝓝 1) := by
  obtain ⟨-, ⟨c₁, hc₁, h₁⟩, ⟨c₂, hc₂, x₀, hx₀, h₂⟩⟩ := apostol_thm_4_10
  set K := |Real.log c₁| + |Real.log c₂|
  have hlogm : Tendsto (fun m : ℕ => Real.log m) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hbound : ∀ᶠ m : ℕ in atTop, |Real.log (θ m) - Real.log m| ≤ K := by
    filter_upwards [eventually_ge_atTop ⌈max x₀ 1⌉₊] with m hm
    have hm' : max x₀ 1 ≤ m := Nat.ceil_le.mp hm
    have hm1 : (1 : ℝ) ≤ m := (le_max_right _ _).trans hm'
    have hmx : x₀ ≤ m := (le_max_left _ _).trans hm'
    have hm0 : (0 : ℝ) < m := by linarith
    have hlow := h₂ m hmx
    have hup := h₁ m hm1
    have hθ : 0 < θ m := lt_of_lt_of_le (by positivity) hlow
    have e1 : Real.log c₂ + Real.log m ≤ Real.log (θ m) := by
      rw [← Real.log_mul hc₂.ne' hm0.ne']; exact Real.log_le_log (by positivity) hlow
    have e2 : Real.log (θ m) ≤ Real.log c₁ + Real.log m := by
      rw [← Real.log_mul hc₁.ne' hm0.ne']; exact Real.log_le_log hθ hup
    rw [abs_le]
    constructor <;> linarith [le_abs_self (Real.log c₁), neg_abs_le (Real.log c₂),
      le_abs_self (Real.log c₂), neg_abs_le (Real.log c₁)]
  have h0 : Tendsto (fun m : ℕ => (Real.log (θ m) - Real.log m) / Real.log m) atTop (𝓝 0) := by
    have hK : Tendsto (fun m : ℕ => K / Real.log m) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hlogm
    refine squeeze_zero_norm' ?_ hK
    filter_upwards [hbound, hlogm.eventually_gt_atTop 0] with m hm hl
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hl]
    exact div_le_div_of_nonneg_right hm hl.le
  have := h0.const_add 1
  rw [add_zero] at this
  refine this.congr' ?_
  filter_upwards [hlogm.eventually_gt_atTop 0] with m hl
  field_simp
  ring

/-- **Theorem 13.14**: let `c` be the constant of Theorem 13.13, i.e.
`∏_{p ≤ x}(1 - 1/p) log x → c`, and `ε > 0`. Then (a) `φ(n) > (1 - ε) c n / log log n` for all
large `n`, and (b) `φ(n) < (1 + ε) c n / log log n` for infinitely many `n`. -/
@[kb "apostol1976" "Thm 13.14, p. 298"]
theorem apostol_thm_13_14 {c : ℝ}
    (hc : Tendsto (fun x => mertensProd x * Real.log x) atTop (𝓝 c)) (hc0 : 0 < c)
    {ε : ℝ} (hε : 0 < ε) :
    (∀ᶠ n : ℕ in atTop, (1 - ε) * c * n / Real.log (Real.log n) < Nat.totient n) ∧
      (∃ᶠ n : ℕ in atTop, (Nat.totient n : ℝ) < (1 + ε) * c * n / Real.log (Real.log n)) := by
  have hlogn : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hloglog : Tendsto (fun n : ℕ => Real.log (Real.log n)) atTop atTop :=
    Real.tendsto_log_atTop.comp hlogn
  constructor
  · -- part (a)
    have hexp : Tendsto (fun n : ℕ => Real.exp (-2 / Real.log (Real.log n))) atTop (𝓝 1) := by
      have := (Real.continuous_exp.tendsto 0).comp
        ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (-2 : ℝ)) atTop (𝓝 (-2))).div_atTop hloglog)
      simpa [Function.comp_def] using this
    have hlim : Tendsto (fun n : ℕ => mertensProd (Real.log n) * Real.log (Real.log n) *
        Real.exp (-2 / Real.log (Real.log n))) atTop (𝓝 (c * 1)) :=
      (hc.comp hlogn).mul hexp
    rw [mul_one] at hlim
    have hlt : (1 - ε) * c < c := by nlinarith
    filter_upwards [(tendsto_order.mp hlim).1 _ hlt, hlogn.eventually_ge_atTop 2,
      hloglog.eventually_gt_atTop 0] with n h1 h2 h3
    have hn0 : (0 : ℝ) < n := by
      by_contra h
      have : (n : ℝ) = 0 := le_antisymm (not_lt.mp h) (Nat.cast_nonneg n)
      rw [this, Real.log_zero] at h2; linarith
    have key := totient_div_ge h2
    rw [div_lt_iff₀ h3]
    have : mertensProd (Real.log n) * Real.log (Real.log n) * Real.exp (-2 / Real.log (Real.log n))
        ≤ (Nat.totient n : ℝ) / n * Real.log (Real.log n) := by
      calc _ = mertensProd (Real.log n) * Real.exp (-2 / Real.log (Real.log n)) *
            Real.log (Real.log n) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right key h3.le
    have h4 := h1.trans_le this
    rw [div_mul_eq_mul_div, lt_div_iff₀ hn0] at h4
    linarith
  · -- part (b): `n = ∏_{p ≤ m} p`
    have hlogθ := tendsto_log_theta_div_log
    have hlogm : Tendsto (fun m : ℕ => Real.log m) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    have hlim : Tendsto (fun m : ℕ => mertensProd m * Real.log m *
        (Real.log (θ m) / Real.log m)) atTop (𝓝 (c * 1)) :=
      (hc.comp tendsto_natCast_atTop_atTop).mul hlogθ
    rw [mul_one] at hlim
    have hlt : c < (1 + ε) * c := by nlinarith
    have hθ : Tendsto (fun m : ℕ => Real.log (θ m)) atTop atTop := by
      refine Tendsto.congr' ?_ (Filter.Tendsto.pos_mul_atTop (by norm_num) hlogθ hlogm)
      filter_upwards [hlogm.eventually_gt_atTop 0] with m hm
      field_simp
    have hev : ∀ᶠ m : ℕ in atTop, (Nat.totient (primorial m) : ℝ) <
        (1 + ε) * c * (primorial m) / Real.log (Real.log (primorial m)) := by
      filter_upwards [(tendsto_order.mp hlim).2 _ hlt, hlogm.eventually_gt_atTop 0,
        hθ.eventually_gt_atTop 0] with m h1 h2 h3
      have hlp : Real.log (primorial m) = θ m := by
        rw [theta_eq_log_primorial, Nat.floor_natCast]
      rw [hlp, totient_primorial_div, lt_div_iff₀ h3]
      have hp : (0 : ℝ) < primorial m := by exact_mod_cast primorial_pos m
      have e : mertensProd m * Real.log m * (Real.log (θ m) / Real.log m) =
          mertensProd m * Real.log (θ m) := by field_simp
      rw [e] at h1
      calc (primorial m : ℝ) * mertensProd m * Real.log (θ m)
          = primorial m * (mertensProd m * Real.log (θ m)) := by ring
        _ < primorial m * ((1 + ε) * c) := mul_lt_mul_of_pos_left h1 hp
        _ = (1 + ε) * c * primorial m := by ring
    rw [frequently_atTop]
    intro a
    obtain ⟨M, hM⟩ := eventually_atTop.mp hev
    obtain ⟨m, hm, hmp⟩ := Nat.exists_infinite_primes (max a M)
    refine ⟨primorial m, ?_, hM m ((le_max_right _ _).trans hm)⟩
    have hdvd : m ∣ primorial m := by
      rw [primorial_eq_prod_primesLE]
      exact dvd_prod_of_mem _ (Nat.mem_primesLE.mpr ⟨le_rfl, hmp⟩)
    exact ((le_max_left _ _).trans hm).trans (Nat.le_of_dvd (primorial_pos m) hdvd)

/-- Theorem 13.14 with the constant of Theorem 13.13 made explicit: there is `c > 0` with
`∏_{p ≤ x}(1 - 1/p) log x → c`, and for this `c` parts (a) and (b) hold for every `ε > 0`. -/
@[kb "apostol1976" "Thm 13.14, p. 298"]
theorem apostol_thm_13_14' : ∃ c : ℝ, 0 < c ∧
    Tendsto (fun x => mertensProd x * Real.log x) atTop (𝓝 c) ∧ ∀ ε : ℝ, 0 < ε →
    (∀ᶠ n : ℕ in atTop, (1 - ε) * c * n / Real.log (Real.log n) < Nat.totient n) ∧
      (∃ᶠ n : ℕ in atTop, (Nat.totient n : ℝ) < (1 + ε) * c * n / Real.log (Real.log n)) := by
  obtain ⟨c, hc0, C, hC⟩ := apostol_thm_13_13
  have hlim : Tendsto (fun x => mertensProd x * Real.log x) atTop (𝓝 c) := by
    have hK : Tendsto (fun x : ℝ => C / Real.log x) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
    have h0 : Tendsto (fun x => mertensProd x * Real.log x - c) atTop (𝓝 0) := by
      refine squeeze_zero_norm' ?_ hK
      filter_upwards [eventually_ge_atTop 2] with x hx
      have hl : 0 < Real.log x := Real.log_pos (by linarith)
      have := hC x hx
      rw [Real.norm_eq_abs, show mertensProd x * Real.log x - c =
        (mertensProd x - c / Real.log x) * Real.log x by field_simp, abs_mul, abs_of_pos hl]
      calc |mertensProd x - c / Real.log x| * Real.log x ≤ C / Real.log x ^ 2 * Real.log x := by
            gcongr
        _ = C / Real.log x := by field_simp
    simpa using h0.add_const c
  exact ⟨c, hc0, hlim, fun ε hε => apostol_thm_13_14 hlim hc0 hε⟩

end NTKB.Apostol
