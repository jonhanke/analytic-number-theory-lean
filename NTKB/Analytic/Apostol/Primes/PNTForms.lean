/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Apostol.Primes.PrimeBounds

/-!
# More equivalent forms of the prime number theorem (Apostol, Theorem 4.5)

**Theorem 4.5**: the following are equivalent:
(a) `π(x) log x / x → 1`; (b) `π(x) log π(x) / x → 1`; (c) `p_n / (n log n) → 1`,
where `p_n` is the `n`-th prime (`p_{n+1} = Nat.nth Nat.Prime n`, Mathlib's `nth` being
0-indexed; (c) is stated for `p_{n+1} / ((n+1) log (n+1))`).

Apostol's proof: take logarithms in (a) or (b) to get `log π(x) / log x → 1`; for (c) put
`x = p_n` (so `π(x) = n`), and conversely use `p_n ≤ x < p_{n+1}` with `n = π(x)`.
-/

open Real Filter Topology Nat

namespace NTKB.Apostol

/-- `π(x)` as a real function of a real variable. -/
noncomputable abbrev piR (x : ℝ) : ℝ := (Nat.primeCounting ⌊x⌋₊ : ℝ)

lemma tendsto_piR : Tendsto piR atTop atTop :=
  (tendsto_natCast_atTop_atTop.comp Nat.tendsto_primeCounting).comp tendsto_nat_floor_atTop

lemma tendsto_log_div_self : Tendsto (fun u : ℝ => Real.log u / u) atTop (𝓝 0) :=
  Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero

/-- If `log f - log g → 0` with `log g → ∞`, then `log f / log g → 1`. -/
lemma tendsto_log_div_log_of_sub {α : Type*} {l : Filter α} {f g : α → ℝ}
    (hg : Tendsto (fun a => Real.log (g a)) l atTop)
    (h : Tendsto (fun a => Real.log (f a) - Real.log (g a)) l (𝓝 0)) :
    Tendsto (fun a => Real.log (f a) / Real.log (g a)) l (𝓝 1) := by
  have := (h.div_atTop hg).const_add 1
  rw [add_zero] at this
  refine this.congr' ?_
  filter_upwards [hg.eventually_gt_atTop 0] with a ha
  field_simp
  ring

lemma tendsto_nth_prime : Tendsto (fun n : ℕ => (nth Nat.Prime n : ℝ)) atTop atTop :=
  tendsto_natCast_atTop_atTop.comp (Nat.nth_strictMono Nat.infinite_setOfPred_prime).tendsto_atTop

lemma tendsto_mul_log_div_succ :
    Tendsto (fun k : ℕ => ((k : ℝ) * Real.log k) / (((k : ℝ) + 1) * Real.log ((k : ℝ) + 1)))
      atTop (𝓝 1) := by
  have h1 : Tendsto (fun k : ℕ => (k : ℝ) / ((k : ℝ) + 1)) atTop (𝓝 1) :=
    tendsto_natCast_div_add_atTop 1
  have hlk : Tendsto (fun k : ℕ => Real.log (k : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  -- `log (k+1) / log k → 1`
  have h2 : Tendsto (fun k : ℕ => Real.log ((k : ℝ) + 1) / Real.log k) atTop (𝓝 1) := by
    have hsmall : Tendsto (fun k : ℕ => Real.log ((k : ℝ) + 1) - Real.log k) atTop (𝓝 0) := by
      have h3 : Tendsto (fun k : ℕ => Real.log (1 + 1 / (k : ℝ))) atTop (𝓝 0) := by
        have h3' : Tendsto (fun k : ℕ => (1 : ℝ) + 1 / (k : ℝ)) atTop (𝓝 (1 + 0)) :=
          (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).add
            ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).div_atTop
              tendsto_natCast_atTop_atTop)
        have := h3'.log (by norm_num)
        simpa using this
      refine h3.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with k hk
      have hk' : (0 : ℝ) < k := by exact_mod_cast hk
      rw [← Real.log_div (by positivity) hk'.ne']
      congr 1; field_simp
    exact tendsto_log_div_log_of_sub (f := fun k : ℕ => (k : ℝ) + 1) (g := fun k : ℕ => (k : ℝ))
      hlk hsmall
  have h4 := h1.mul (h2.inv₀ one_ne_zero)
  rw [inv_one, mul_one] at h4
  refine h4.congr' ?_
  filter_upwards [hlk.eventually_gt_atTop 0, eventually_gt_atTop 0] with k hk hk0
  have : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  field_simp

/-- **Theorem 4.5**: `π(x) log x / x → 1` iff `π(x) log π(x) / x → 1` iff `p_n / (n log n) → 1`. -/
@[kb "apostol1976" "Thm 4.5, p. 80"]
theorem apostol_thm_4_5 :
    (Tendsto (fun x => piR x * Real.log x / x) atTop (𝓝 1) ↔
        Tendsto (fun x => piR x * Real.log (piR x) / x) atTop (𝓝 1)) ∧
      (Tendsto (fun x => piR x * Real.log (piR x) / x) atTop (𝓝 1) ↔
        Tendsto (fun n : ℕ => (nth Nat.Prime n : ℝ) / (((n : ℝ) + 1) * Real.log ((n : ℝ) + 1)))
          atTop (𝓝 1)) := by
  have hP := tendsto_piR
  have hlogP : Tendsto (fun x => Real.log (piR x)) atTop atTop := Real.tendsto_log_atTop.comp hP
  have hlogx : Tendsto (fun x : ℝ => Real.log x) atTop atTop := Real.tendsto_log_atTop
  have hll : Tendsto (fun x : ℝ => Real.log (Real.log x) / Real.log x) atTop (𝓝 0) :=
    tendsto_log_div_self.comp hlogx
  have hllP : Tendsto (fun x => Real.log (Real.log (piR x)) / Real.log (piR x)) atTop (𝓝 0) :=
    tendsto_log_div_self.comp hlogP
  have hn : Tendsto (fun x : ℝ => Nat.primeCounting ⌊x⌋₊) atTop atTop :=
    Nat.tendsto_primeCounting.comp tendsto_nat_floor_atTop
  refine ⟨⟨fun hA => ?_, fun hB => ?_⟩, ⟨fun hB => ?_, fun hC => ?_⟩⟩
  · -- (a) ⇒ (b)
    have hl := hA.log one_ne_zero
    rw [Real.log_one] at hl
    have hq : Tendsto (fun x => Real.log (piR x) / Real.log x) atTop (𝓝 1) := by
      have := ((hl.div_atTop hlogx).sub hll).const_add 1
      rw [sub_zero, add_zero] at this
      refine this.congr' ?_
      filter_upwards [hP.eventually_gt_atTop 0, hlogx.eventually_gt_atTop 0,
        eventually_gt_atTop 0] with x h1 h2 h3
      rw [Real.log_div (by positivity) h3.ne', Real.log_mul h1.ne' h2.ne']
      field_simp
      ring
    have := hA.mul hq
    rw [mul_one] at this
    refine this.congr' ?_
    filter_upwards [hlogx.eventually_gt_atTop 0] with x h2
    field_simp
  · -- (b) ⇒ (a)
    have hl := hB.log one_ne_zero
    rw [Real.log_one] at hl
    have hq : Tendsto (fun x => Real.log x / Real.log (piR x)) atTop (𝓝 1) := by
      have := (hllP.sub (hl.div_atTop hlogP)).const_add 1
      rw [sub_zero, add_zero] at this
      refine this.congr' ?_
      filter_upwards [hP.eventually_gt_atTop 0, hlogP.eventually_gt_atTop 0,
        eventually_gt_atTop 0] with x h1 h2 h3
      rw [Real.log_div (by positivity) h3.ne', Real.log_mul h1.ne' h2.ne']
      field_simp
      ring
    have := hB.mul hq
    rw [mul_one] at this
    refine this.congr' ?_
    filter_upwards [hlogP.eventually_gt_atTop 0] with x h2
    field_simp
  · -- (b) ⇒ (c)
    have h := (hB.comp tendsto_nth_prime).inv₀ one_ne_zero
    rw [inv_one] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn0
    simp only [Function.comp_apply, piR, Nat.floor_natCast, primeCounting_nth]
    push_cast
    rw [inv_div]
  · -- (c) ⇒ (b)
    have hq := hC.inv₀ one_ne_zero
    rw [inv_one] at hq
    have hq' : Tendsto (fun k : ℕ => (((k : ℝ) + 1) * Real.log ((k : ℝ) + 1)) / nth Nat.Prime k)
        atTop (𝓝 1) := hq.congr fun k => by simp only [inv_div]
    have hup := hq'.comp ((tendsto_sub_atTop_nat 1).comp hn)
    have hlow := (tendsto_mul_log_div_succ.mul hq').comp hn
    rw [one_mul] at hlow
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hup ?_ ?_
    · filter_upwards [hn.eventually_ge_atTop 2, eventually_gt_atTop 0] with x hx hx0
      simp only [Function.comp_apply, piR]
      set n := Nat.primeCounting ⌊x⌋₊
      have hpx : x < nth Nat.Prime n := by
        have h1 : ⌊x⌋₊ + 1 ≤ nth Nat.Prime n :=
          (Nat.count_le_iff_le_nth Nat.infinite_setOfPred_prime).mp le_rfl
        have h2 : x < ⌊x⌋₊ + 1 := Nat.lt_floor_add_one x
        exact h2.trans_le (by exact_mod_cast h1)
      have hn0 : (0 : ℝ) ≤ (n : ℝ) * Real.log n := by
        have : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
        exact mul_nonneg (by linarith) (Real.log_nonneg this)
      have h1n : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
      have hk : (0 : ℝ) < ((n : ℝ) + 1) * Real.log ((n : ℝ) + 1) :=
        mul_pos (by linarith) (Real.log_pos (by linarith))
      rw [div_mul_div_cancel₀ hk.ne']
      exact div_le_div_of_nonneg_left hn0 hx0 hpx.le
    · filter_upwards [hn.eventually_ge_atTop 2, eventually_gt_atTop 0] with x hx hx0
      simp only [Function.comp_apply, piR]
      set n := Nat.primeCounting ⌊x⌋₊
      have hpn : (nth Nat.Prime (n - 1) : ℝ) ≤ x := by
        have h1 : nth Nat.Prime (n - 1) < ⌊x⌋₊ + 1 :=
          (Nat.lt_nth_iff_count_lt Nat.infinite_setOfPred_prime).mp (by
            show n - 1 < Nat.primeCounting ⌊x⌋₊; omega)
        have h2 : ((nth Nat.Prime (n - 1) : ℕ) : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast Nat.lt_succ_iff.mp h1
        exact h2.trans (Nat.floor_le hx0.le)
      have hp0 : (0 : ℝ) < nth Nat.Prime (n - 1) := by
        exact_mod_cast (Nat.prime_nth_prime (n - 1)).pos
      have hn0 : (0 : ℝ) ≤ (n : ℝ) * Real.log n := by
        have : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
        exact mul_nonneg (by linarith) (Real.log_nonneg this)
      have e : ((n - 1 : ℕ) : ℝ) + 1 = n := by
        rw [Nat.cast_sub (by omega)]; ring
      rw [e]
      exact div_le_div_of_nonneg_left hn0 hp0 hpn

end NTKB.Apostol
