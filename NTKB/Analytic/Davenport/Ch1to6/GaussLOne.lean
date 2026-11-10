/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Davenport.Ch1to6.GaussProduct
import NTKB.Analytic.Davenport.Ch1to6.LOneEven

/-!
# Davenport, Chapter 1: `L(1) ≠ 0` for `q ≡ 1 (mod 4)` through Gauss's cyclotomy

For a prime `q ≡ 1 (mod 4)`, formula (9) reads `L(1) = q^{-1/2} log Q` with
`Q = ∏_N 2 sin(πN/q) / ∏_R 2 sin(πR/q) = |∏_N (1 - ζ^N)| / |∏_R (1 - ζ^R)|`, and Gauss's identity
at `x = 1` gives `2∏_R (1 - ζ^R) = Y - √q Z`, `2∏_N (1 - ζ^N) = Y + √q Z` with integers `Y, Z`,
`Y² - qZ² = 4q`, `Z ≠ 0`. Hence `Q = (Y + √q Z)/(Y - √q Z) ≠ 1` and `L(1) ≠ 0`
(§1, pp. 10–11). (Davenport's `Q` has `sin` in place of `2 sin`; the two agree since there are
as many residues as nonresidues.)
-/

noncomputable section

open Complex Finset Polynomial DirichletCharacter
open scoped Real

namespace NTKB.Davenport

variable {q : ℕ} [Fact q.Prime]

/-- `∑_{m=1}^{q-1} F(m) = ∑_{u unit} F(u)`. -/
theorem sum_Ico_eq_sum_units {M : Type*} [AddCommGroup M] (F : ℕ → M) :
    ∑ m ∈ Ico 1 q, F m = ∑ u : (ZMod q)ˣ, F (u : ZMod q).val := by
  have h := NTKB.sum_val_eq_sum_range (n := q) F
  rw [sum_zmod_eq_add_sum_units (fun x : ZMod q ↦ F x.val), ZMod.val_zero, range_eq_Ico,
    sum_eq_sum_Ico_succ_bot (Fact.out : q.Prime).pos] at h
  exact (add_left_cancel h).symm

/-- `log |1 - ζ^m| = log(2 sin(πm/q))` for `0 < m < q`, `ζ = e(1/q)`. -/
theorem log_norm_one_sub_pow {m : ℕ} (hm : m ∈ Ico 1 q) :
    Real.log ‖1 - cexp (2 * π * I / q) ^ m‖ = Real.log (2 * Real.sin (π * m / q)) := by
  have h := log_one_sub_stdAddChar (N := q) hm
  rw [stdAddChar_natCast_eq_pow, stdAddChar_one_eq] at h
  have := congrArg Complex.re h
  rw [log_re] at this
  simpa using this

theorem one_sub_pow_ne_zero (u : (ZMod q)ˣ) : 1 - cexp (2 * π * I / q) ^ (u : ZMod q).val ≠ 0 := by
  intro h
  have h1 : cexp (2 * π * I / q) ^ (u : ZMod q).val = cexp (2 * π * I / q) ^ 0 := by
    rw [pow_zero]; linear_combination -h
  have := isPrimitiveRoot_cexp.pow_inj (ZMod.val_lt _) (Fact.out : q.Prime).pos h1
  exact u.ne_zero ((ZMod.val_eq_zero _).mp this)

/-- **Davenport §1, pp. 10–11.** For a prime `q ≡ 1 (mod 4)` there are integers `Y, Z` with
`Y² - q Z² = 4q`, `Z ≠ 0`, `Q = (Y + √q Z)/(Y - √q Z) > 0`, `Q ≠ 1` and `L(1) = q^{-1/2} log Q`;
hence `L(1) ≠ 0`. -/
@[kb "davenport1980" "Ch 1, pp. 10-11"]
theorem exists_LFunction_one_eq_log (hq : q % 4 = 1) :
    ∃ Y Z : ℤ, Y ^ 2 - q * Z ^ 2 = 4 * q ∧ Z ≠ 0 ∧
      0 < (Y + √(q : ℝ) * Z) / (Y - √(q : ℝ) * Z) ∧
      (Y + √(q : ℝ) * Z) / (Y - √(q : ℝ) * Z) ≠ 1 ∧
      LFunction (legendreChar q) 1 =
        (((√(q : ℝ))⁻¹ * Real.log ((Y + √(q : ℝ) * Z) / (Y - √(q : ℝ) * Z)) : ℝ) : ℂ) := by
  have hq2 : q ≠ 2 := by omega
  obtain ⟨Yp, Zp, hR, hN, hYZ⟩ := exists_gauss_product (q := q) hq2
  set ζ := cexp (2 * π * I / q)
  set y : ℤ := Yp.eval 1
  set z : ℤ := Zp.eval 1
  have hG : epsSqrt q = (√(q : ℝ) : ℂ) := by simp [epsSqrt, hq]
  -- values at `x = 1`
  have hR1 : 2 * ∏ r ∈ residues q, (1 - ζ ^ (r : ZMod q).val) = (y : ℂ) - √(q : ℝ) * z := by
    have := congrArg (Polynomial.eval 1) hR
    simpa [eval_prod, hG, y, z, eval_intCast_map] using this
  have hN1 : 2 * ∏ n ∈ nonresidues q, (1 - ζ ^ (n : ZMod q).val) = (y : ℂ) + √(q : ℝ) * z := by
    have := congrArg (Polynomial.eval 1) hN
    simpa [eval_prod, hG, y, z, eval_intCast_map] using this
  have hyz : y ^ 2 - q * z ^ 2 = 4 * q := by
    have := congrArg (Polynomial.eval 1) hYZ
    simpa [if_pos hq, eval_finsetSum, y, z] using this
  have hp : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp Fact.out
  have hz : z ≠ 0 := by
    intro hz0
    rw [hz0] at hyz
    have hy2 : y ^ 2 = 4 * q := by linarith
    have hdvd : (q : ℤ) ∣ y := hp.dvd_of_dvd_pow (n := 2) ⟨4, by rw [hy2]; ring⟩
    obtain ⟨t, ht⟩ := hdvd
    rw [ht] at hy2
    have : (q : ℤ) * t ^ 2 = 4 := by
      have := mul_left_cancel₀ hp.ne_zero (show (q : ℤ) * (q * t ^ 2) = q * 4 by linarith)
      exact this
    have : q ∣ 4 := Int.natCast_dvd_natCast.mp ⟨t ^ 2, this.symm⟩
    have := Nat.le_of_dvd (by norm_num) this
    interval_cases q <;> simp_all
  have hsq : (0 : ℝ) < √(q : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (Fact.out : q.Prime).pos)
  have hsq2 : √(q : ℝ) ^ 2 = q := Real.sq_sqrt (Nat.cast_nonneg _)
  have hprodR : ((y : ℝ) + √(q : ℝ) * z) * ((y : ℝ) - √(q : ℝ) * z) = 4 * q := by
    have : ((y ^ 2 - q * z ^ 2 : ℤ) : ℝ) = 4 * q := by rw [hyz]; push_cast; ring
    push_cast at this
    nlinarith [hsq2]
  have hminus : (y : ℝ) - √(q : ℝ) * z ≠ 0 := by
    intro h; rw [h, mul_zero] at hprodR
    have : (0 : ℝ) < q := by exact_mod_cast (Fact.out : q.Prime).pos
    linarith
  have hplus : (y : ℝ) + √(q : ℝ) * z ≠ 0 := by
    intro h; rw [h, zero_mul] at hprodR
    have : (0 : ℝ) < q := by exact_mod_cast (Fact.out : q.Prime).pos
    linarith
  have hQpos : 0 < ((y : ℝ) + √(q : ℝ) * z) / ((y : ℝ) - √(q : ℝ) * z) := by
    have h4 : 0 < ((y : ℝ) + √(q : ℝ) * z) * ((y : ℝ) - √(q : ℝ) * z) := by
      rw [hprodR]; have : (0 : ℝ) < q := by exact_mod_cast (Fact.out : q.Prime).pos
      linarith
    rcases lt_or_gt_of_ne hminus with h | h
    · exact div_pos_of_neg_of_neg (by nlinarith) h
    · exact div_pos (by nlinarith) h
  have hQ1 : ((y : ℝ) + √(q : ℝ) * z) / ((y : ℝ) - √(q : ℝ) * z) ≠ 1 := by
    intro h
    rw [div_eq_one_iff_eq hminus] at h
    have : √(q : ℝ) * z = 0 := by linarith
    rcases mul_eq_zero.mp this with h0 | h0
    · exact hsq.ne' h0
    · exact hz (by exact_mod_cast h0)
  refine ⟨y, z, hyz, hz, hQpos, hQ1, ?_⟩
  -- formula (9) as a sum over the units, split into residues and nonresidues
  rw [LFunction_one_legendreChar_of_one_mod_four hq]
  have hlog : ∀ m ∈ Ico 1 q, (Real.log (2 * Real.sin (π * m / q)) : ℂ) =
      (Real.log ‖1 - ζ ^ m‖ : ℂ) := fun m hm ↦ by rw [log_norm_one_sub_pow hm]
  rw [sum_congr rfl fun m hm ↦ by rw [hlog m hm]]
  rw [sum_Ico_eq_sum_units (fun m ↦ (legendreSym q m : ℂ) * (Real.log ‖1 - ζ ^ m‖ : ℂ))]
  have hχ : ∀ u : (ZMod q)ˣ, legendreSym q ((u : ZMod q).val : ℤ) = quadraticChar (ZMod q) u := by
    intro u; rw [legendreSym, Int.cast_natCast, ZMod.natCast_zmod_val]
  simp_rw [hχ]
  rw [← sum_filter_add_sum_filter_not univ (fun u : (ZMod q)ˣ ↦ quadraticChar (ZMod q) u = 1)]
  have hRs : ∑ u ∈ univ.filter (fun u : (ZMod q)ˣ ↦ quadraticChar (ZMod q) u = 1),
      ((quadraticChar (ZMod q) u : ℤ) : ℂ) * (Real.log ‖1 - ζ ^ (u : ZMod q).val‖ : ℂ) =
      (Real.log ‖∏ r ∈ residues q, (1 - ζ ^ (r : ZMod q).val)‖ : ℂ) := by
    rw [norm_prod, Real.log_prod (fun u _ ↦ norm_ne_zero_iff.mpr (one_sub_pow_ne_zero u))]
    push_cast
    refine sum_congr rfl fun u hu ↦ ?_
    rw [(mem_filter.mp hu).2]; simp [ζ]
  have hNs : ∑ u ∈ univ.filter (fun u : (ZMod q)ˣ ↦ ¬ quadraticChar (ZMod q) u = 1),
      ((quadraticChar (ZMod q) u : ℤ) : ℂ) * (Real.log ‖1 - ζ ^ (u : ZMod q).val‖ : ℂ) =
      -(Real.log ‖∏ n ∈ nonresidues q, (1 - ζ ^ (n : ZMod q).val)‖ : ℂ) := by
    rw [norm_prod, Real.log_prod (fun u _ ↦ norm_ne_zero_iff.mpr (one_sub_pow_ne_zero u))]
    push_cast
    rw [← sum_neg_distrib]
    refine sum_congr (filter_congr fun u _ ↦ ?_) fun u hu ↦ ?_
    · rcases quadraticChar_unit_eq u with h | h <;> rw [h] <;> norm_num
    · rw [(mem_filter.mp hu).2]; simp [ζ]
  rw [hRs, hNs]
  -- the norms of the products
  have hnR : ‖∏ r ∈ residues q, (1 - ζ ^ (r : ZMod q).val)‖ = |(y : ℝ) - √(q : ℝ) * z| / 2 := by
    have : ∏ r ∈ residues q, (1 - ζ ^ (r : ZMod q).val) = (((y : ℝ) - √(q : ℝ) * z) / 2 : ℝ) := by
      push_cast; linear_combination hR1 / 2
    rw [this, norm_real, Real.norm_eq_abs, abs_div, abs_two]
  have hnN : ‖∏ n ∈ nonresidues q, (1 - ζ ^ (n : ZMod q).val)‖ = |(y : ℝ) + √(q : ℝ) * z| / 2 := by
    have : ∏ n ∈ nonresidues q, (1 - ζ ^ (n : ZMod q).val) = (((y : ℝ) + √(q : ℝ) * z) / 2 : ℝ) := by
      push_cast; linear_combination hN1 / 2
    rw [this, norm_real, Real.norm_eq_abs, abs_div, abs_two]
  rw [hnR, hnN]
  have habs : |(y : ℝ) + √(q : ℝ) * z| / |(y : ℝ) - √(q : ℝ) * z| =
      ((y : ℝ) + √(q : ℝ) * z) / ((y : ℝ) - √(q : ℝ) * z) := by
    rw [← abs_div, abs_of_pos hQpos]
  rw [← habs, Real.log_div (abs_pos.mpr hplus).ne' (abs_pos.mpr hminus).ne',
    Real.log_div (by positivity) two_ne_zero, Real.log_div (by positivity) two_ne_zero]
  push_cast
  ring

/-- **Davenport §1, p. 11.** Dirichlet's proof (via Gauss's cyclotomy) that `L(1) ≠ 0` for a prime
`q ≡ 1 (mod 4)`. -/
@[kb "davenport1980" "Ch 1, p. 11"]
theorem LFunction_one_legendreChar_ne_zero_of_one_mod_four (hq : q % 4 = 1) :
    LFunction (legendreChar q) 1 ≠ 0 := by
  obtain ⟨Y, Z, -, -, hpos, hne, hL⟩ := exists_LFunction_one_eq_log (q := q) hq
  rw [hL, ofReal_ne_zero]
  refine mul_ne_zero (inv_ne_zero (Real.sqrt_pos.mpr ?_).ne') ?_
  · exact_mod_cast (Fact.out : q.Prime).pos
  · intro h
    rcases Real.log_eq_zero.mp h with h | h | h
    · exact hpos.ne' h
    · exact hne h
    · linarith

end NTKB.Davenport
