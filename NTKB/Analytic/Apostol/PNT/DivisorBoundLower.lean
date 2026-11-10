/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Apostol.PNT.TotientLogLog
import NTKB.Analytic.Apostol.Primes.ChebyshevForms

/-!
# The divisor function is infinitely often large (Apostol, Theorem 13.12 (b))

**Theorem 13.12 (b)**: for every `ε > 0`, `d(n) > 2^{(1-ε) log n / log log n}` for infinitely
many `n`. Apostol's proof uses the prime number theorem (proved analytically in his Chapter 13),
which is not in Mathlib; it enters here as the named hypothesis `PrimeNumberTheoremStatement`
(`π(x) log x / x → 1`). Take `n = ∏_{p ≤ m} p`: `d(n) = 2^{π(m)}`, `log n = θ(m)`,
`log log n = log θ(m) ~ log m`, and `θ(m) ~ m ~ π(m) log m` (Theorem 4.4).
-/

open Finset Real Filter Topology Chebyshev

namespace NTKB.Apostol

/-- The prime number theorem `π(x) log x / x → 1`, a cited input (proved in Apostol, Chapter 13,
by contour integration; not in Mathlib). -/
structure PrimeNumberTheoremStatement : Prop where
  tendsto : Tendsto (fun x : ℝ => (Nat.primeCounting ⌊x⌋₊ : ℝ) * Real.log x / x) atTop (𝓝 1)

lemma card_divisors_primorial (m : ℕ) : (primorial m).divisors.card = 2 ^ Nat.primeCounting m := by
  rw [Nat.card_divisors (primorial_ne_zero m), primeFactors_primorial,
    ← Nat.primesLE_card_eq_primeCounting, ← prod_const]
  refine prod_congr rfl fun p hp => ?_
  have hpr := (Nat.mem_primesLE.mp hp).2
  have : (primorial m).factorization p = 1 := by
    rw [primorial_eq_prod_primesLE, Nat.factorization_prod (fun q hq => (Nat.mem_primesLE.mp hq).2.ne_zero)]
    rw [Finset.sum_apply', sum_eq_single p (fun q hq hqp => by
        rw [(Nat.mem_primesLE.mp hq).2.factorization, Finsupp.single_apply, ite_eq_right hqp])
      (fun h => absurd hp h), hpr.factorization, Finsupp.single_eq_same]
  rw [this]

/-- **Theorem 13.12 (b)** (assuming the prime number theorem). -/
@[kb "apostol1976" "Thm 13.12, p. 294"]
theorem apostol_thm_13_12_b (hPNT : PrimeNumberTheoremStatement) {ε : ℝ} (hε : 0 < ε)
    (hε1 : ε < 1) :
    ∃ᶠ n : ℕ in atTop, (2 : ℝ) ^ ((1 - ε) * Real.log n / Real.log (Real.log n)) <
      (n.divisors.card : ℝ) := by
  have hpi : Tendsto (fun m : ℕ => (Nat.primeCounting m : ℝ) * Real.log m / m) atTop (𝓝 1) := by
    have := hPNT.tendsto.comp tendsto_natCast_atTop_atTop
    refine this.congr fun m => ?_
    simp [Function.comp_apply, Nat.floor_natCast]
  have hθ : Tendsto (fun m : ℕ => θ m / m) atTop (𝓝 1) :=
    ((apostol_thm_4_4.1.mp hPNT.tendsto).comp tendsto_natCast_atTop_atTop)
  have hlθ := tendsto_log_theta_div_log
  -- `(θ/log θ)/π = (θ/m) · (log m / log θ) · (m/(π log m)) → 1`
  have hratio : Tendsto (fun m : ℕ => (θ m / m) * (Real.log (θ m) / Real.log m)⁻¹ *
      ((Nat.primeCounting m : ℝ) * Real.log m / m)⁻¹) atTop (𝓝 1) := by
    have := (hθ.mul (hlθ.inv₀ one_ne_zero)).mul (hpi.inv₀ one_ne_zero)
    simpa using this
  have hlt : (1 : ℝ) < 1 / (1 - ε) := by rw [lt_div_iff₀ (by linarith)]; linarith
  have hlogm : Tendsto (fun m : ℕ => Real.log m) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hθtop : Tendsto (fun m : ℕ => θ m) atTop atTop := by
    refine (Filter.Tendsto.pos_mul_atTop one_pos hθ tendsto_natCast_atTop_atTop).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with m hm
    have : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
    field_simp
  have hev : ∀ᶠ m : ℕ in atTop, (2 : ℝ) ^ ((1 - ε) * Real.log (primorial m) /
      Real.log (Real.log (primorial m))) < ((primorial m).divisors.card : ℝ) := by
    filter_upwards [(tendsto_order.mp hratio).2 _ hlt, hθtop.eventually_gt_atTop 1,
      hlogm.eventually_gt_atTop 0, eventually_ge_atTop 2] with m h1 h2 h3 h4
    have hlp : Real.log (primorial m) = θ m := by
      rw [theta_eq_log_primorial, Nat.floor_natCast]
    have hπpos : (0 : ℝ) < Nat.primeCounting m := by
      have : 1 ≤ Nat.primeCounting m := by
        have h2le : Nat.primeCounting 2 ≤ Nat.primeCounting m := Nat.monotone_primeCounting h4
        have : Nat.primeCounting 2 = 1 := by decide
        omega
      exact_mod_cast this
    have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
    have hlθ0 : 0 < Real.log (θ m) := Real.log_pos h2
    rw [hlp, card_divisors_primorial, Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast,
      Real.rpow_lt_rpow_left_iff (by norm_num)]
    -- from `h1`: `θ/(log θ · π) < 1/(1-ε)`
    have e : θ m / m * (Real.log (θ m) / Real.log m)⁻¹ *
        ((Nat.primeCounting m : ℝ) * Real.log m / m)⁻¹ =
        θ m / (Real.log (θ m) * Nat.primeCounting m) := by
      field_simp
    rw [e, div_lt_div_iff₀ (by positivity) (by linarith), one_mul] at h1
    rw [div_lt_iff₀ hlθ0]
    nlinarith
  rw [frequently_atTop]
  intro a
  obtain ⟨M, hM⟩ := eventually_atTop.mp hev
  obtain ⟨m, hm, hmp⟩ := Nat.exists_infinite_primes (max a M)
  refine ⟨primorial m, ?_, hM m ((le_max_right _ _).trans hm)⟩
  have hdvd : m ∣ primorial m := by
    rw [primorial_eq_prod_primesLE]
    exact dvd_prod_of_mem _ (Nat.mem_primesLE.mpr ⟨le_rfl, hmp⟩)
  exact ((le_max_left _ _).trans hm).trans (Nat.le_of_dvd (primorial_pos m) hdvd)

end NTKB.Apostol
