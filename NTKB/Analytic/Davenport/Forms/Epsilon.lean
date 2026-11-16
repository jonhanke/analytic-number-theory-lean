/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Davenport.Forms.RealUnits
import NTKB.Analytic.Davenport.ClassNumber.Unconditional

/-!
# Davenport, Chapter 6: the class number formulas for `h(d)` and `ε` (rows 6-4, 6-24)

(§6, pp. 49–51, 55, 62.) Davenport's class number formulas are stated for his form class number
`h(d)` (`NTKB.Davenport.formClassNumber`) and, for `d > 0`, for
`ε = (t₀ + u₀√d)/2`, the fundamental solution of `t² - d u² = 4`
(`NTKB.Davenport.IsPellFundamental d t₀ u₀`: `ε > 1` and every solution has
`(t + u√d)/2 = ± εⁿ`).

* Row 6-4: `NTKB.Davenport.exists_isPellFundamental` (with `t₀, u₀ > 0`),
  `NTKB.Davenport.infinite_automorphs`.
* Row 6-24: `NTKB.Davenport.formClassNumber_mul_log_eq`: `h(d) log ε = 2 h₁(d) log ε₁`.
* The formulas with `h(d)` and `ε`: (15), (16), (17), (18) in the form of row 6-25,
  Jacobi's formula 6-17 and Siegel's bounds 21-2, 21-3.
-/

noncomputable section

open QuadraticAlgebra NTKB.QuadraticField NumberField NumberField.Units Complex DirichletCharacter
open scoped Real

namespace NTKB.Davenport

/-- `(t + u√d)/2`. -/
def pellValue (d t u : ℤ) : ℝ := (t + u * √(d : ℝ)) / 2

/-- Davenport's fundamental solution of `t² - d u² = 4` (p. 55): `ε = (t₀ + u₀√d)/2 > 1` and
every solution has `(t + u√d)/2 = ± εⁿ`. -/
def IsPellFundamental (d t₀ u₀ : ℤ) : Prop :=
  t₀ ^ 2 - d * u₀ ^ 2 = 4 ∧ 1 < pellValue d t₀ u₀ ∧
    ∀ t u : ℤ, t ^ 2 - d * u ^ 2 = 4 →
      ∃ n : ℤ, pellValue d t u = pellValue d t₀ u₀ ^ n ∨ pellValue d t u = -pellValue d t₀ u₀ ^ n

section generator

variable {D : ℤ} [Fact (IsFundamentalDiscriminant D)] [Fact (D ≠ 1)]

theorem realEmb_eq_pellValue (hD : 0 ≤ D) (η : {η : Order D // η.norm = 1}) :
    realEmb hD η.1 = pellValue D (normOneEquiv η).1.1 (normOneEquiv η).1.2 := by
  have := realEmb_normOneEquiv_symm hD (normOneEquiv η)
  rw [Equiv.symm_apply_apply] at this
  rw [this, pellValue]

/-- A norm-one generator `ε > 1` gives a fundamental solution. -/
theorem isPellFundamental_of_generator (hD : 0 < D) {K : Type*} [Field K] [NumberField K]
    (ε : (Order D)ˣ) (hN : (ε : Order D).norm = 1) (h1 : 1 < realEmb hD.le (ε : Order D))
    (hgen : ∀ u : (Order D)ˣ, (u : Order D).norm = 1 → ∃ n : ℤ, u = ε ^ n ∨ u = -ε ^ n) :
    IsPellFundamental D (normOneEquiv ⟨_, hN⟩).1.1 (normOneEquiv ⟨_, hN⟩).1.2 := by
  have hval := realEmb_eq_pellValue hD.le ⟨_, hN⟩
  refine ⟨(normOneEquiv ⟨_, hN⟩).2, hval ▸ h1, fun t u htu ↦ ?_⟩
  have hu := isUnit_of_norm_eq_one (normOneEquiv.symm (⟨(t, u), htu⟩ : PellFour D)).2
  obtain ⟨n, hn⟩ := hgen hu.unit (normOneEquiv.symm (⟨(t, u), htu⟩ : PellFour D)).2
  refine ⟨n, ?_⟩
  have hηv : realEmb hD.le (normOneEquiv.symm (⟨(t, u), htu⟩ : PellFour D)).1 = pellValue D t u := by
    exact realEmb_normOneEquiv_symm hD.le (⟨(t, u), htu⟩ : PellFour D)
  rw [← hηv, ← hval]
  rcases hn with h | h
  · left
    have := congrArg (fun v : (Order D)ˣ ↦ realEmb hD.le (v : Order D)) h
    simp only [IsUnit.unit_spec] at this
    rw [this, realEmb_units_zpow]
  · right
    have := congrArg (fun v : (Order D)ˣ ↦ realEmb hD.le (v : Order D)) h
    simp only [IsUnit.unit_spec] at this
    rw [this, realEmb_neg_units, realEmb_units_zpow]

theorem pellValue_mul_conj {d t u : ℤ} (hd : 0 ≤ d) (h : t ^ 2 - d * u ^ 2 = 4) :
    pellValue d t u * ((t - u * √(d : ℝ)) / 2) = 1 := by
  have hs : √(d : ℝ) * √(d : ℝ) = d := Real.mul_self_sqrt (by exact_mod_cast hd)
  have h' : (t : ℝ) ^ 2 - d * u ^ 2 = 4 := by exact_mod_cast h
  simp only [pellValue]
  linear_combination h' / 4 - (u : ℝ) ^ 2 * hs / 4

theorem pos_of_isPellFundamental {d t₀ u₀ : ℤ} (hd : 0 < d) (h : IsPellFundamental d t₀ u₀) :
    0 < t₀ ∧ 0 < u₀ := by
  obtain ⟨h0, h1, -⟩ := h
  have hc := pellValue_mul_conj hd.le h0
  set x := pellValue d t₀ u₀
  have hx : x = (t₀ + u₀ * √(d : ℝ)) / 2 := rfl
  have hsq : 0 < √(d : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hd)
  have hy : 0 < (t₀ - u₀ * √(d : ℝ)) / 2 := by
    by_contra hneg; push Not at hneg; nlinarith
  have hy1 : (t₀ - u₀ * √(d : ℝ)) / 2 < 1 := by nlinarith
  constructor
  · have : (0 : ℝ) < t₀ := by linarith
    exact_mod_cast this
  · have : (0 : ℝ) < u₀ * √(d : ℝ) := by linarith
    have : (0 : ℝ) < u₀ := pos_of_mul_pos_left this hsq.le
    exact_mod_cast this

end generator

/-- **Davenport §6, p. 55 (row 6-4).** For a fundamental discriminant `d > 1`, the equation
`t² - d u² = 4` has a fundamental solution `(t₀, u₀)`, `t₀, u₀ > 0`: with `ε = (t₀ + u₀√d)/2 > 1`,
every solution satisfies `(t + u√d)/2 = ± εⁿ` for some `n ∈ ℤ`. -/
@[kb "davenport1980" "Ch 6, p. 55"]
theorem exists_isPellFundamental {d : ℤ} (hd : IsFundamentalDiscriminant d) (h1 : d ≠ 1) (hpos : 0 < d) :
    ∃ t₀ u₀ : ℤ, 0 < t₀ ∧ 0 < u₀ ∧ IsPellFundamental d t₀ u₀ := by
  have : Fact (IsFundamentalDiscriminant d) := ⟨hd⟩
  have : Fact (d ≠ 1) := ⟨h1⟩
  obtain ⟨ε, hN, hε1, hgen, -, -⟩ := exists_normOne_generator (finrank_model d)
    (ringOfIntegersEquiv d).symm hpos (discr_model d)
  have hF := isPellFundamental_of_generator (K := Model d) hpos ε hN hε1 hgen
  exact ⟨_, _, (pos_of_isPellFundamental hpos hF).1, (pos_of_isPellFundamental hpos hF).2, hF⟩

/-- The fundamental solution is unique. -/
theorem IsPellFundamental.pellValue_eq {d t₀ u₀ t₁ u₁ : ℤ} (h₀ : IsPellFundamental d t₀ u₀)
    (h₁ : IsPellFundamental d t₁ u₁) : pellValue d t₀ u₀ = pellValue d t₁ u₁ := by
  set x := pellValue d t₀ u₀
  set y := pellValue d t₁ u₁
  have hx := h₀.2.1
  have hy := h₁.2.1
  obtain ⟨n, hn⟩ := h₀.2.2 t₁ u₁ h₁.1
  obtain ⟨m, hm⟩ := h₁.2.2 t₀ u₀ h₀.1
  have hxpos : 0 < x := by linarith
  have hypos : 0 < y := by linarith
  have hn' : y = x ^ n := by
    rcases hn with h | h
    · exact h
    · have := zpow_pos hxpos n; linarith
  have hm' : x = y ^ m := by
    rcases hm with h | h
    · exact h
    · have := zpow_pos hypos m; linarith
  have hnm : x ^ (n * m) = x ^ (1 : ℤ) := by rw [zpow_mul, ← hn', ← hm', zpow_one]
  have hnm1 : n * m = 1 := zpow_right_injective₀ hxpos (ne_of_gt hx) hnm
  rcases Int.eq_one_or_neg_one_of_mul_eq_one hnm1 with h | h
  · rw [hn', h, zpow_one]
  · exfalso
    rw [h, zpow_neg_one] at hn'
    have : x⁻¹ < 1 := inv_lt_one_of_one_lt₀ hx
    linarith

/-- **Davenport §6, p. 55 (row 6-4).** For `d > 1` fundamental, every form of discriminant `d`
has infinitely many automorphs. -/
theorem infinite_automorphs {d : ℤ} (hd : IsFundamentalDiscriminant d) (h1 : d ≠ 1) (hpos : 0 < d)
    {f : ℤ × ℤ × ℤ} (hf : formDisc f = d) : Infinite (Automorphs f) := by
  have : Fact (IsFundamentalDiscriminant d) := ⟨hd⟩
  have : Fact (d ≠ 1) := ⟨h1⟩
  obtain ⟨ε, hN, hε1, -, -, -⟩ := exists_normOne_generator (finrank_model d)
    (ringOfIntegersEquiv d).symm hpos (discr_model d)
  have hNk : ∀ k : ℕ, ((ε ^ k : (Order d)ˣ) : Order d).norm = 1 := fun k ↦ by
    rw [Units.val_pow_eq_pow_val, map_pow, hN, one_pow]
  let F : ℕ → Automorphs f := fun k ↦ (automorphsEquiv hf).symm (normOneEquiv ⟨_, hNk k⟩)
  refine Infinite.of_injective F fun k l hkl ↦ ?_
  have h := congrArg (fun M ↦ realEmb hpos.le (normOneEquiv.symm (automorphsEquiv hf M)).1) hkl
  simp only [F, Equiv.apply_symm_apply, Equiv.symm_apply_apply] at h
  rw [← zpow_natCast, ← zpow_natCast, realEmb_units_zpow, realEmb_units_zpow] at h
  have := zpow_right_injective₀ (lt_trans one_pos hε1) (ne_of_gt hε1) h
  exact_mod_cast this

/-! ### Row 6-24 -/

section field

variable {K : Type} [Field K] [NumberField K]

/-- **Davenport §6, p. 62 (row 6-24).** For a real quadratic field `K` of discriminant `d` and the
fundamental solution `ε = (t₀ + u₀√d)/2` of `t² - d u² = 4`:
`h(d) log ε = 2 h₁(d) log ε₁`, `h₁(d)` the class number and `log ε₁` the regulator of `K`. -/
@[kb "davenport1980" "Ch 6, p. 62"]
theorem formClassNumber_mul_log_eq (hK : Module.finrank ℚ K = 2) (hD : 0 < discr K) {t₀ u₀ : ℤ}
    (hε : IsPellFundamental (discr K) t₀ u₀) :
    (formClassNumber (discr K) : ℝ) * Real.log (pellValue (discr K) t₀ u₀) =
      2 * classNumber K * regulator K := by
  obtain ⟨_, _⟩ := facts_discr K hK
  obtain ⟨e⟩ := nonempty_ringEquiv_order K hK
  obtain ⟨ε, hN, hε1, hgen, hyes, hno⟩ := exists_normOne_generator hK e hD rfl
  have hF := isPellFundamental_of_generator (K := K) hD ε hN hε1 hgen
  have hval : pellValue (discr K) t₀ u₀ = realEmb hD.le (ε : Order (discr K)) := by
    rw [hε.pellValue_eq hF, realEmb_eq_pellValue hD.le ⟨_, hN⟩]
  rw [hval]
  by_cases hu : ∃ u : (Order (discr K))ˣ, (u : Order (discr K)).norm = -1
  · rw [formClassNumber_eq_classNumber_of_exists_norm_eq_neg_one K hK
      ((exists_unit_norm_iff e).mpr hu), hyes hu]; ring
  · rw [formClassNumber_eq_two_mul_classNumber K hK hD (fun h ↦ hu ((exists_unit_norm_iff e).mp h)),
      hno hu]; push_cast; ring

/-! ### The class number formulas for `h(d)` and `ε` -/

/-- **Davenport §6, p. 49, (16)**, for Davenport's `h(d)` and `ε`: `h(d) log ε = √d L(1, χ)`. -/
@[kb "davenport1980" "Ch 6, p. 49, (16)"]
theorem formClassNumber_mul_log_eq_of_discr_pos (hK : Module.finrank ℚ K = 2) (hD : 0 < discr K)
    {t₀ u₀ : ℤ} (hε : IsPellFundamental (discr K) t₀ u₀) :
    (((formClassNumber (discr K) : ℝ) * Real.log (pellValue (discr K) t₀ u₀) : ℝ) : ℂ) =
      √(discr K : ℝ) * LFunction (kroneckerChar (discr K)) 1 := by
  rw [formClassNumber_mul_log_eq hK hD hε]
  exact two_mul_classNumber_mul_regulator_eq_of_discr_pos_unconditional hK hD

/-- **Davenport §6, p. 51 and row 6-25**, for `h(d)` and `ε`:
`h(d) log ε = -∑_{0 < m < d} (d/m) log sin(π m / d)`. -/
@[kb "davenport1980" "Ch 6, p. 51"]
theorem formClassNumber_mul_log_eq_sum_of_discr_pos (hK : Module.finrank ℚ K = 2)
    (hD : 0 < discr K) {t₀ u₀ : ℤ} (hε : IsPellFundamental (discr K) t₀ u₀) :
    (((formClassNumber (discr K) : ℝ) * Real.log (pellValue (discr K) t₀ u₀) : ℝ) : ℂ) =
      -∑ m ∈ Finset.Ico 1 (discr K).natAbs,
        kroneckerChar (discr K) m * (Real.log (Real.sin (π * m / discr K)) : ℂ) := by
  rw [formClassNumber_mul_log_eq hK hD hε]
  have := classNumber_mul_regulator_eq_sum_of_discr_pos_unconditional hK hD
  push_cast at this ⊢
  linear_combination 2 * this

/-- **Davenport §6, p. 49, (15)**, for Davenport's `h(d)`: for `d < 0`,
`h(d) = w √|d| L(1, χ) / (2π)`. -/
@[kb "davenport1980" "Ch 6, p. 49, (15)"]
theorem formClassNumber_eq_of_discr_neg (hK : Module.finrank ℚ K = 2) (hD : discr K < 0) :
    (formClassNumber (discr K) : ℂ) =
      torsionOrder K * √|(discr K : ℝ)| * LFunction (kroneckerChar (discr K)) 1 / (2 * π) := by
  rw [formClassNumber_eq_classNumber_of_discr_neg K hK hD]
  exact classNumber_eq_of_discr_neg_unconditional hK hD

/-- **Davenport §6, p. 51 and row 6-25**, for `h(d)`: for `d < 0`,
`h(d) = -(w / (2|d|)) ∑_{m=1}^{|d|} m (d/m)`. -/
@[kb "davenport1980" "Ch 6, p. 51"]
theorem formClassNumber_eq_sum_of_discr_neg (hK : Module.finrank ℚ K = 2) (hD : discr K < 0) :
    (formClassNumber (discr K) : ℂ) = -((torsionOrder K : ℂ) / (2 * (discr K).natAbs)) *
      ∑ m ∈ Finset.Icc 1 (discr K).natAbs, (m : ℂ) * kroneckerChar (discr K) m := by
  rw [formClassNumber_eq_classNumber_of_discr_neg K hK hD]
  exact classNumber_eq_sum_of_discr_neg_unconditional hK hD

/-- **Davenport §6, p. 51, (19): Jacobi's formula**, for `h(-q)`: for a prime `q ≡ 3 (mod 4)`,
`q > 3`, `q h(-q) = -∑_{m=1}^{q-1} m (m/q)`. -/
@[kb "davenport1980" "Ch 6, p. 51, (19)"]
theorem formClassNumber_eq_jacobi {q : ℕ} [Fact q.Prime] (hq : q % 4 = 3) (hq3 : 3 < q)
    (hK : Module.finrank ℚ K = 2) (hDq : discr K = -q) :
    (q : ℤ) * formClassNumber (discr K) = -∑ m ∈ Finset.Ico 1 q, (m : ℤ) * legendreSym q m := by
  have hq0 : (0 : ℤ) < q := by exact_mod_cast (Fact.out : q.Prime).pos
  have hD : discr K < 0 := by rw [hDq]; linarith
  rw [formClassNumber_eq_classNumber_of_discr_neg K hK hD]
  exact classNumber_eq_jacobi_unconditional hq hq3 hK hDq

end field

/-- **Davenport §21, (2): Siegel's theorem** for Davenport's `h(d)`, `d < 0`:
`h(d) > C(ε) |d|^{1/2 - ε}`. -/
@[kb "davenport1980" "Ch 21, (2)"]
theorem formClassNumber_gt_of_discr_neg {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 →
      discr K < 0 → C * |(discr K : ℝ)| ^ ((1 : ℝ) / 2 - ε) < formClassNumber (discr K) := by
  obtain ⟨C, hC, h⟩ := classNumber_gt_of_discr_neg_unconditional hε
  refine ⟨C, hC, fun K _ _ hK hD ↦ ?_⟩
  rw [formClassNumber_eq_classNumber_of_discr_neg K hK hD]
  exact h K hK hD

/-- **Davenport §21, (3): Siegel's theorem** for Davenport's `h(d)` and `ε`, `d > 0`:
`h(d) log ε > C(ε') d^{1/2 - ε'}`. -/
@[kb "davenport1980" "Ch 21, (3)"]
theorem formClassNumber_mul_log_gt_of_discr_pos {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 →
      0 < discr K → ∀ t₀ u₀ : ℤ, IsPellFundamental (discr K) t₀ u₀ →
        C * (discr K : ℝ) ^ ((1 : ℝ) / 2 - ε) <
          formClassNumber (discr K) * Real.log (pellValue (discr K) t₀ u₀) := by
  obtain ⟨C, hC, h⟩ := classNumber_mul_regulator_gt_of_discr_pos_unconditional hε
  refine ⟨C, hC, fun K _ _ hK hD t₀ u₀ hF ↦ ?_⟩
  rw [formClassNumber_mul_log_eq hK hD hF]
  have h1 := h K hK hD
  have h2 : 0 ≤ (classNumber K : ℝ) * regulator K :=
    mul_nonneg (Nat.cast_nonneg _) (le_of_lt (lt_of_lt_of_le (Real.log_pos (by norm_num))
      (log_three_halves_le_regulator hK hD)))
  linarith

end NTKB.Davenport
