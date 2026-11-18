/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import NTKB.Attr

/-!
# The Weierstrass product of `1/Γ` and the ratio `Γ(s/2)/Γ((1-s)/2)`
(Davenport, Chapter 10, rows 10-2 and 10-6)

* **10-2**: `1/Γ(s) = s e^{γs} ∏_{n ≥ 1} (1 + s/n) e^{-s/n}` for every complex `s`, as the limit of the
  partial products (`tendsto_weierstrassProd_one_div_Gamma`), from Mathlib's Euler limit
  `Complex.GammaSeq_tendsto_Gamma` and `H_n - log n → γ`; `Γ` has no zeros
  (Mathlib `Complex.Gamma_ne_zero`) and a simple pole at each `-n` with residue `(-1)^n/n!`
  (`tendsto_mul_Gamma_nhds_neg_nat`).
* **10-6**: `Γ(s/2)/Γ((1-s)/2) = 2^{1-s} π^{-1/2} cos(πs/2) Γ(s)` (`Gamma_half_div_Gamma_half_one_sub`),
  the identity that turns the symmetric functional equation of `ζ` into the unsymmetric one;
  a restatement of Mathlib's `Complex.Gammaℝ_div_Gammaℝ_one_sub`.

Source text unavailable; written from the map rows 10-2 and 10-6.
-/

open Complex Filter Topology
open scoped Real

namespace NTKB.Davenport

/-- The partial Weierstrass products `s e^{γs} ∏_{k=1}^{n} (1 + s/k) e^{-s/k}`. -/
noncomputable def weierstrassProd (s : ℂ) (n : ℕ) : ℂ :=
  s * cexp (Real.eulerMascheroniConstant * s) *
    ∏ k ∈ Finset.range n, (1 + s / (k + 1)) * cexp (-(s / (k + 1)))

/-- The partial Weierstrass product in terms of the Pochhammer-type product `∏_{j ≤ n} (s + j)`. -/
theorem weierstrassProd_eq (s : ℂ) (n : ℕ) :
    weierstrassProd s n = (∏ j ∈ Finset.range (n + 1), (s + j)) / (n.factorial : ℂ) *
      cexp (s * ((Real.eulerMascheroniConstant : ℂ) - ((harmonic n : ℚ) : ℂ))) := by
  unfold weierstrassProd
  have hk : ∀ k : ℕ, ((k : ℂ) + 1) ≠ 0 := fun k ↦ Nat.cast_add_one_ne_zero k
  have h1 : ∏ k ∈ Finset.range n, (1 + s / ((k : ℂ) + 1)) =
      (∏ k ∈ Finset.range n, (s + ((k + 1 : ℕ) : ℂ))) / (n.factorial : ℂ) := by
    rw [← Finset.prod_range_add_one_eq_factorial, Nat.cast_prod, ← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun k _ ↦ ?_
    push_cast
    field_simp [hk k]
    ring
  have h2 : ∏ k ∈ Finset.range n, cexp (-(s / ((k : ℂ) + 1))) =
      cexp (-(s * ((harmonic n : ℚ) : ℂ))) := by
    rw [← Complex.exp_sum, harmonic]
    congr 1
    push_cast
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [div_eq_mul_inv]
  rw [Finset.prod_mul_distrib, h1, h2, Finset.prod_range_succ' _ n]
  simp only [Nat.cast_zero, add_zero]
  rw [mul_comm s, mul_sub, sub_eq_add_neg, Complex.exp_add, neg_mul_eq_mul_neg, mul_neg]
  rw [show ((Real.eulerMascheroniConstant : ℂ) * s) = s * (Real.eulerMascheroniConstant : ℂ) by
    ring]
  ring

/-- **Davenport, Ch. 10, p. 73 (row 10-2)**: the Weierstrass product
`1/Γ(s) = s e^{γs} ∏_{n ≥ 1} (1 + s/n) e^{-s/n}`, for every complex `s`. -/
@[kb "davenport1980" "Ch 10, p. 73"]
theorem tendsto_weierstrassProd_one_div_Gamma (s : ℂ) :
    Tendsto (weierstrassProd s) atTop (𝓝 (1 / Gamma s)) := by
  by_cases hs : ∃ m : ℕ, s = -m
  · obtain ⟨m, rfl⟩ := hs
    rw [Gamma_neg_nat_eq_zero, div_zero]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop m] with n hn
    rw [weierstrassProd_eq, Finset.prod_eq_zero (i := m) (Finset.mem_range.2 (by omega))
      (by simp)]
    simp
  · push Not at hs
    have hP : ∀ n : ℕ, ∏ j ∈ Finset.range (n + 1), (s + j) ≠ 0 := by
      intro n
      rw [Finset.prod_ne_zero_iff]
      intro j _ h
      exact hs j (by linear_combination h)
    have hG := (GammaSeq_tendsto_Gamma s).inv₀ (Gamma_ne_zero hs)
    have hE : Tendsto (fun n : ℕ ↦ cexp (s * ((Real.eulerMascheroniConstant : ℂ) -
        (((harmonic n : ℚ) : ℂ) - ((Real.log n : ℝ) : ℂ))))) atTop (𝓝 1) := by
      have h'' := (Complex.continuous_ofReal.tendsto _).comp Real.tendsto_harmonic_sub_log
      have h3 := (h''.const_sub (Real.eulerMascheroniConstant : ℂ)).const_mul s
      rw [sub_self, mul_zero] at h3
      have h4 := (Complex.continuous_exp.tendsto 0).comp h3
      rw [Complex.exp_zero] at h4
      refine h4.congr fun n ↦ ?_
      simp
    have hmain := hG.mul hE
    rw [mul_one, one_div] at *
    refine hmain.congr' ?_
    filter_upwards [eventually_ne_atTop 0] with n hn
    rw [weierstrassProd_eq, GammaSeq]
    have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    have hf : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
    have hpow : (n : ℂ) ^ s = cexp (s * ((Real.log n : ℝ) : ℂ)) := by
      rw [cpow_def_of_ne_zero hn', mul_comm]
      congr 2
      rw [Complex.ofReal_log (Nat.cast_nonneg n)]
      simp
    have hpow0 : (n : ℂ) ^ s ≠ 0 := by rw [hpow]; exact Complex.exp_ne_zero _
    have hexp : cexp (s * ((Real.eulerMascheroniConstant : ℂ) -
        (((harmonic n : ℚ) : ℂ) - ((Real.log n : ℝ) : ℂ)))) =
        cexp (s * ((Real.eulerMascheroniConstant : ℂ) - ((harmonic n : ℚ) : ℂ))) *
          ((n : ℂ) ^ s) := by
      rw [hpow, ← Complex.exp_add]
      congr 1
      ring
    simp only [inv_div]
    rw [hexp]
    field_simp

/-- **Davenport, Ch. 10, p. 73 (row 10-2)**: `Γ` has a simple pole at `-n` with residue
`(-1)^n/n!`. -/
@[kb "davenport1980" "Ch 10, p. 73"]
theorem tendsto_mul_Gamma_nhds_neg_nat (n : ℕ) :
    Tendsto (fun s ↦ (s + n) * Gamma s) (𝓝[≠] (-(n : ℂ))) (𝓝 ((-1) ^ n / n.factorial)) := by
  induction n with
  | zero => simpa using tendsto_self_mul_Gamma_nhds_zero
  | succ n ih =>
    have hshift : Tendsto (fun s : ℂ ↦ s + 1) (𝓝[≠] (-((n + 1 : ℕ) : ℂ))) (𝓝[≠] (-(n : ℂ))) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have : Tendsto (fun s : ℂ ↦ s + 1) (𝓝 (-((n + 1 : ℕ) : ℂ))) (𝓝 (-((n + 1 : ℕ) : ℂ) + 1)) :=
          (continuous_id.add continuous_const).continuousAt.tendsto
        have h2 : -((n + 1 : ℕ) : ℂ) + 1 = -(n : ℂ) := by push_cast; ring
        rw [h2] at this
        exact this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with s hs h
        refine hs ?_
        simp only [Set.mem_singleton_iff] at h ⊢
        push_cast at h ⊢
        linear_combination h
    have hn0 : (-((n + 1 : ℕ) : ℂ)) ≠ 0 :=
      neg_ne_zero.mpr (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n))
    have hlim := (ih.comp hshift).div (tendsto_id.mono_left nhdsWithin_le_nhds) hn0
    have hz : ∀ᶠ s : ℂ in 𝓝[≠] (-((n + 1 : ℕ) : ℂ)), s ≠ 0 :=
      eventually_nhdsWithin_of_eventually_nhds (isOpen_ne.mem_nhds hn0)
    have e : (-1 : ℂ) ^ (n + 1) / ((n + 1).factorial : ℂ) =
        (-1) ^ n / n.factorial / -((n + 1 : ℕ) : ℂ) := by
      rw [Nat.factorial_succ]
      push_cast
      have : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
      have : (n : ℂ) + 1 ≠ 0 := Nat.cast_add_one_ne_zero n
      field_simp
      ring
    rw [e]
    refine hlim.congr' ?_
    filter_upwards [hz] with s hs
    simp only [Pi.div_apply, Function.comp_apply, id]
    rw [Gamma_add_one s hs]
    push_cast
    field_simp
    ring

/-- **Davenport, Ch. 10, p. 73 (row 10-6)**:
`Γ(s/2)/Γ((1-s)/2) = 2^{1-s} π^{-1/2} cos(πs/2) Γ(s)` (off `s = -1, -3, -5, …`). -/
@[kb "davenport1980" "Ch 10, p. 73"]
theorem Gamma_half_div_Gamma_half_one_sub {s : ℂ} (hs : ∀ n : ℕ, s ≠ -(2 * n + 1)) :
    Gamma (s / 2) / Gamma ((1 - s) / 2) =
      2 ^ (1 - s) * (π : ℂ) ^ (-(1 / 2 : ℂ)) * cos (π * s / 2) * Gamma s := by
  have h := Gammaℝ_div_Gammaℝ_one_sub hs
  have hP : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  unfold Gammaℝ Gammaℂ at h
  rw [mul_div_mul_comm, ← cpow_sub _ _ hP] at h
  have hc : (π : ℂ) ^ (-s / 2 - -(1 - s) / 2) ≠ 0 := by
    rw [Ne, cpow_eq_zero_iff]; tauto
  apply mul_left_cancel₀ hc
  rw [h, show (-s / 2 - -(1 - s) / 2 : ℂ) = 1 / 2 + -s by ring, cpow_add _ _ hP,
    show (1 - s : ℂ) = 1 + -s by ring, cpow_add _ _ two_ne_zero, cpow_one,
    show (2 * (π : ℂ) : ℂ) = ((2 : ℝ) : ℂ) * ((π : ℝ) : ℂ) by push_cast; ring,
    Complex.mul_cpow_ofReal_nonneg (by norm_num) Real.pi_pos.le]
  have : (π : ℂ) ^ (1 / 2 : ℂ) * (π : ℂ) ^ (-(1 / 2 : ℂ)) = 1 := by
    rw [← cpow_add _ _ hP]; simp
  push_cast
  linear_combination (-2 *(2 : ℂ) ^ (-s) * (π : ℂ) ^ (-s) * cos (π * s / 2) * Gamma s) * this

end NTKB.Davenport
