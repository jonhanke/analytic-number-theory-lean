/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Complex.ExponentialBounds
import NTKB.Attr

/-!
# The maximal order of the divisor function (Apostol, Theorem 13.12 (a))

**Theorem 13.12 (a)**: for every `ε > 0`, `d(n) < 2^{(1+ε) log n / log log n}` for all large `n`.

Apostol's proof: with `d(n) = ∏ (a_i + 1)`, split the primes `p ∣ n` at `f(n) = log n/(log log n)²`.
The large ones contribute at most `2^{S}` with `S = ∑_{p > f} a_p ≤ log n / log f`; each small one
contributes `a_p + 1 ≤ (log n)²`, and there are at most `π(f) = O(f/log f)` of them (Chebyshev,
Mathlib's `Chebyshev.pi_le_log4_mul_div`). Hence
`log d(n) ≤ (log n/log log n) (12/log f + log 2 · log log n/log f)`, and the bracket tends to
`log 2`. (Part (b), the lower bound infinitely often, uses the prime number theorem and is not
formalized here.)
-/

open Finset Real Filter Topology

namespace NTKB.Apostol

/-- `π(x) ≤ 6 x / log x` for real `x > 1`. -/
lemma primeCounting_floor_le {x : ℝ} (hx : 1 < x) :
    (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ 6 * (x / Real.log x) := by
  have h := Chebyshev.pi_le_log4_mul_div hx
  have hlx : 0 < Real.log x := Real.log_pos hx
  have hx0 : 0 < x := by linarith
  have hsq : Real.log √x = Real.log x / 2 := by
    rw [Real.log_sqrt hx0.le]
  rw [hsq] at h
  have hsqrt : √x ≤ 2 * (x / Real.log x) := by
    have h1 : Real.log √x ≤ √x - 1 := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hx0)
    rw [hsq] at h1
    have hs0 : 0 < √x := Real.sqrt_pos.mpr hx0
    have hxx : √x * √x = x := Real.mul_self_sqrt hx0.le
    have : √x * Real.log x ≤ 2 * x := by nlinarith
    rw [mul_div_assoc', le_div_iff₀ hlx]
    linarith
  have h4 : Real.log 4 < 2 := by
    have : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    rw [this]; linarith [Real.log_two_lt_d9]
  have : Real.log 4 * x / (Real.log x / 2) = 2 * Real.log 4 * (x / Real.log x) := by
    field_simp
  rw [this] at h
  have hxl : 0 < x / Real.log x := by positivity
  nlinarith

/-- The deterministic inequality behind Theorem 13.12 (a): for `f ≥ 2` and `log n ≥ 2`,
`log d(n) ≤ π(f) · 2 log log n + log 2 · log n / log f`. -/
lemma log_card_divisors_le {n : ℕ} (hn : n ≠ 0) {f : ℝ} (hf : 2 ≤ f)
    (hL : 2 ≤ Real.log n) :
    Real.log (n.divisors.card : ℝ) ≤
      (Nat.primeCounting ⌊f⌋₊ : ℝ) * (2 * Real.log (Real.log n)) +
        Real.log 2 * (Real.log n / Real.log f) := by
  set L := Real.log n with hLdef
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hlogf : 0 < Real.log f := Real.log_pos (by linarith)
  set a : ℕ → ℕ := fun p => n.factorization p
  have hd : (n.divisors.card : ℝ) = ∏ p ∈ n.primeFactors, ((a p : ℝ) + 1) := by
    rw [Nat.card_divisors hn]; push_cast; rfl
  rw [hd, ← prod_filter_mul_prod_filter_not n.primeFactors (fun p : ℕ => (p : ℝ) ≤ f)]
  set S₁ := n.primeFactors.filter (fun p : ℕ => (p : ℝ) ≤ f)
  set S₂ := n.primeFactors.filter (fun p : ℕ => ¬ (p : ℝ) ≤ f)
  have hpow_le : ∀ p ∈ n.primeFactors, ((p : ℝ) ^ a p) ≤ n := fun p _ => by
    exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (Nat.ordProj_dvd n p)
  -- small primes: each factor is at most `L²`
  have hA : ∏ p ∈ S₁, ((a p : ℝ) + 1) ≤ (L ^ 2) ^ S₁.card := by
    rw [← prod_const]
    refine prod_le_prod₀ (fun _ _ => by positivity) fun p hp => ?_
    have hpf := (mem_filter.mp hp).1
    have hpr := Nat.prime_of_mem_primeFactors hpf
    have h2 : (2 : ℝ) ^ a p ≤ n := by
      refine le_trans ?_ (hpow_le p hpf)
      exact pow_le_pow_left₀ (by norm_num) (by exact_mod_cast hpr.two_le) _
    have h3 : (a p : ℝ) * Real.log 2 ≤ L := by
      have := Real.log_le_log (by positivity) h2
      rwa [Real.log_pow] at this
    have hl2 : (2 : ℝ) / 3 < Real.log 2 := by linarith [Real.log_two_gt_d9]
    have h4 : (a p : ℝ) ≤ 3 / 2 * L := by
      have ha0 : (0 : ℝ) ≤ a p := Nat.cast_nonneg _
      nlinarith
    nlinarith
  have hcard : (S₁.card : ℝ) ≤ Nat.primeCounting ⌊f⌋₊ := by
    rw [← Nat.primesLE_card_eq_primeCounting]
    exact_mod_cast card_le_card fun p hp => by
      obtain ⟨hpf, hpl⟩ := mem_filter.mp hp
      exact Nat.mem_primesLE.mpr ⟨Nat.le_floor hpl, Nat.prime_of_mem_primeFactors hpf⟩
  -- large primes: at most `2^S` with `S log f ≤ L`
  have hB : ∏ p ∈ S₂, ((a p : ℝ) + 1) ≤ 2 ^ (∑ p ∈ S₂, a p) := by
    rw [← prod_pow_eq_pow_sum]
    refine prod_le_prod₀ (fun _ _ => by positivity) fun p _ => ?_
    exact_mod_cast Nat.lt_two_pow_self
  have hS : ((∑ p ∈ S₂, a p : ℕ) : ℝ) * Real.log f ≤ L := by
    have hprod : f ^ (∑ p ∈ S₂, a p) ≤ n := by
      rw [← prod_pow_eq_pow_sum]
      calc ∏ p ∈ S₂, f ^ a p ≤ ∏ p ∈ S₂, (p : ℝ) ^ a p :=
            prod_le_prod₀ (fun _ _ => by positivity) fun p hp =>
              pow_le_pow_left₀ (by linarith) (not_le.mp (mem_filter.mp hp).2).le _
        _ ≤ n := by
          have hdvd : ∏ p ∈ S₂, p ^ a p ∣ n := by
            conv_rhs => rw [Nat.prod_primeFactors_pow_factorization hn]
            exact prod_dvd_prod_of_subset _ _ _ (filter_subset _ _)
          exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdvd
    have := Real.log_le_log (by positivity) hprod
    rwa [Real.log_pow] at this
  have hApos : 0 < ∏ p ∈ S₁, ((a p : ℝ) + 1) := prod_pos fun _ _ => by positivity
  have hBpos : 0 < ∏ p ∈ S₂, ((a p : ℝ) + 1) := prod_pos fun _ _ => by positivity
  rw [Real.log_mul hApos.ne' hBpos.ne']
  have hL1 : 0 < Real.log L := Real.log_pos (by linarith)
  have e1 : Real.log (∏ p ∈ S₁, ((a p : ℝ) + 1)) ≤ (Nat.primeCounting ⌊f⌋₊ : ℝ) * (2 * Real.log L) := by
    calc _ ≤ Real.log ((L ^ 2) ^ S₁.card) := Real.log_le_log hApos hA
      _ = S₁.card * (2 * Real.log L) := by rw [Real.log_pow, Real.log_pow]; push_cast; ring
      _ ≤ _ := by gcongr
  have e2 : Real.log (∏ p ∈ S₂, ((a p : ℝ) + 1)) ≤ Real.log 2 * (L / Real.log f) := by
    calc _ ≤ Real.log (2 ^ (∑ p ∈ S₂, a p)) := Real.log_le_log hBpos hB
      _ = ((∑ p ∈ S₂, a p : ℕ) : ℝ) * Real.log 2 := by rw [Real.log_pow]
      _ ≤ (L / Real.log f) * Real.log 2 := by
          gcongr; rw [le_div_iff₀ hlogf]; exact hS
      _ = _ := by ring
  linarith

/-- `12/(u - 2 log u) + log 2 · u/(u - 2 log u) → log 2` as `u → ∞`. -/
lemma tendsto_divisorBracket :
    Tendsto (fun u : ℝ => 12 / (u - 2 * Real.log u) + Real.log 2 * (u / (u - 2 * Real.log u)))
      atTop (𝓝 (Real.log 2)) := by
  have hlu : Tendsto (fun u : ℝ => Real.log u / u) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hq : Tendsto (fun u : ℝ => (u - 2 * Real.log u) / u) atTop (𝓝 1) := by
    have := (hlu.const_mul 2).const_sub 1
    rw [mul_zero, sub_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with u hu
    field_simp
  have hD : Tendsto (fun u : ℝ => u - 2 * Real.log u) atTop atTop := by
    refine (Filter.Tendsto.atTop_mul_pos one_pos tendsto_id hq).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with u hu
    simp only [id]
    field_simp
  have h1 : Tendsto (fun u : ℝ => 12 / (u - 2 * Real.log u)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hD
  have h2 : Tendsto (fun u : ℝ => u / (u - 2 * Real.log u)) atTop (𝓝 1) := by
    have := hq.inv₀ one_ne_zero
    rw [inv_one] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with u hu
    rw [inv_div]
  have := h1.add (h2.const_mul (Real.log 2))
  rwa [zero_add, mul_one] at this

/-- **Theorem 13.12 (a)**: for every `ε > 0`, `d(n) < 2^{(1+ε) log n / log log n}` for all
sufficiently large `n`. -/
@[kb "apostol1976" "Thm 13.12, p. 294"]
theorem apostol_thm_13_12_a {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      (n.divisors.card : ℝ) < 2 ^ ((1 + ε) * Real.log n / Real.log (Real.log n)) := by
  have hL : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hLL : Tendsto (fun n : ℕ => Real.log (Real.log n)) atTop atTop :=
    Real.tendsto_log_atTop.comp hL
  have hB := tendsto_divisorBracket.comp hLL
  have hf := (tendsto_exp_div_pow_atTop 2).comp hLL
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlt : Real.log 2 < (1 + ε) * Real.log 2 := by nlinarith
  filter_upwards [(tendsto_order.mp hB).2 _ hlt, hL.eventually_ge_atTop 2,
    hf.eventually_ge_atTop 2, hLL.eventually_gt_atTop 0, eventually_ge_atTop 1]
    with n hBn hL2 hf2 hu0 hn1
  simp only [Function.comp_apply] at hBn hf2
  set L := Real.log n with hLdef
  set u := Real.log L with hudef
  have hL0 : 0 < L := by linarith
  have hexp : Real.exp u = L := Real.exp_log hL0
  rw [hexp] at hf2
  set f := L / u ^ 2 with hfdef
  have hlogf : Real.log f = u - 2 * Real.log u := by
    rw [hfdef, Real.log_div hL0.ne' (by positivity), Real.log_pow]; push_cast; ring
  have hlogf0 : 0 < Real.log f := Real.log_pos (by linarith)
  have hn : n ≠ 0 := by omega
  have hmain := log_card_divisors_le hn hf2 hL2
  have hpi := primeCounting_floor_le (x := f) (by linarith)
  have hd0 : (0 : ℝ) < n.divisors.card := by
    exact_mod_cast Finset.card_pos.mpr (Nat.nonempty_divisors.mpr hn)
  rw [Real.lt_rpow_iff_log_lt hd0 two_pos]
  have key : (Nat.primeCounting ⌊f⌋₊ : ℝ) * (2 * u) + Real.log 2 * (L / Real.log f) ≤
      L / u * (12 / (u - 2 * Real.log u) + Real.log 2 * (u / (u - 2 * Real.log u))) := by
    rw [← hlogf]
    calc (Nat.primeCounting ⌊f⌋₊ : ℝ) * (2 * u) + Real.log 2 * (L / Real.log f)
        ≤ 6 * (f / Real.log f) * (2 * u) + Real.log 2 * (L / Real.log f) := by
          gcongr
      _ = L / u * (12 / Real.log f + Real.log 2 * (u / Real.log f)) := by
          rw [hfdef]; field_simp; ring
  have hLu : 0 < L / u := div_pos hL0 hu0
  calc Real.log (n.divisors.card : ℝ) ≤ _ := hmain
    _ ≤ _ := key
    _ < L / u * ((1 + ε) * Real.log 2) := mul_lt_mul_of_pos_left hBn hLu
    _ = (1 + ε) * L / u * Real.log 2 := by ring

end NTKB.Apostol
