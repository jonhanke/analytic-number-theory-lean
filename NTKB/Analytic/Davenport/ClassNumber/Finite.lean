/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Davenport.ClassNumber.Formula
import NTKB.Analytic.Davenport.Ch1to6.Kronecker

/-!
# Davenport, Chapter 6: the finite class number formulas and Jacobi's formula

Davenport, *Multiplicative Number Theory*, §6, pp. 50–51. Combining the class number formulas
(`classNumber_eq_of_discr_neg`, `two_mul_classNumber_mul_regulator_eq_of_discr_pos`) with the
values of `L(1, χ)` of §6, (17) and (18) (`LFunction_one_kroneckerChar_of_neg`,
`LFunction_one_kroneckerChar_of_pos`):

* `classNumber_eq_sum_of_discr_neg` (§6, p. 51): for `d < 0`,
  `h(d) = -(w / (2|d|)) ∑_{m=1}^{|d|} m (d/m)`;
* `classNumber_mul_regulator_eq_sum_of_discr_pos` and `classNumber_mul_log_eq_sum_of_discr_pos`
  (§6, p. 51): for `d > 0`, `h R = h log ε = -(1/2) ∑_{m=1}^{d-1} (d/m) log sin(πm/d)`
  (Davenport's `h(d) log ε = -∑ (d/m) log sin(πm/d)` is twice this, row 6-24);
* `classNumber_eq_jacobi` (§6, p. 51, (19), **Jacobi**): for a prime `q ≡ 3 (mod 4)`, `q > 3`,
  and the field of discriminant `-q`: `q h(-q) = -∑_{m=1}^{q-1} m (m/q)`.

All are conditional on the two named statements of `NTKB.Davenport.ClassNumber.Formula`.
-/

noncomputable section

open Complex DirichletCharacter Module NumberField NumberField.InfinitePlace NumberField.Units
  Finset
open scoped Real

namespace NTKB.Davenport

variable {K : Type} [Field K] [NumberField K]

/-- `|d|` as a real number. -/
theorem abs_discr_eq_natAbs : |(discr K : ℝ)| = ((discr K).natAbs : ℝ) := by
  rw [Nat.cast_natAbs, Int.cast_abs]

/-- **Davenport §6, p. 51: the finite class number formula for `d < 0`.**
`h(d) = -(w / (2|d|)) ∑_{m=1}^{|d|} m (d/m)`. -/
@[kb "davenport1980" "Ch 6, p. 51"]
theorem classNumber_eq_sum_of_discr_neg (hF : QuadraticFieldDiscriminants)
    (hI : QuadraticIdealCount) (hK : finrank ℚ K = 2) (hD : discr K < 0) :
    (classNumber K : ℂ) = -((torsionOrder K : ℂ) / (2 * (discr K).natAbs)) *
      ∑ m ∈ Icc 1 (discr K).natAbs, (m : ℂ) * kroneckerChar (discr K) m := by
  rw [classNumber_eq_of_discr_neg hF hI hK hD,
    LFunction_one_kroneckerChar_of_neg (hF.isFundamental K hK) hD, abs_discr_eq_natAbs]
  set n : ℝ := ((discr K).natAbs : ℝ)
  have hn : 0 < n := by
    simp only [n]; exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne _)
  have hpow : n ^ ((3 : ℝ) / 2) = n * √n := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_one_add' hn.le (by norm_num)]
    norm_num
  have hsq : (√n : ℂ) * √n = n := by rw [← ofReal_mul, Real.mul_self_sqrt hn.le]
  have hs0 : (√n : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hn).ne'
  have hn0 : (n : ℂ) ≠ 0 := ofReal_ne_zero.mpr hn.ne'
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_pos.ne'
  have hnat : (((discr K).natAbs : ℕ) : ℂ) = (n : ℂ) := by simp only [n, ofReal_natCast]
  rw [hpow, hnat, ofReal_div, ofReal_mul]
  field_simp

/-- `1 < d` for a real quadratic field. -/
theorem one_lt_discr_of_pos (hK : finrank ℚ K = 2) (hD : 0 < discr K) : 1 < discr K := by
  have h2 := abs_discr_gt_two (K := K) (by omega)
  rw [abs_of_pos hD] at h2
  omega

/-- **Davenport §6, p. 51: the finite class number formula for `d > 0`.**
`h R = -(1/2) ∑_{m=1}^{d-1} (d/m) log sin(πm/d)`. -/
@[kb "davenport1980" "Ch 6, p. 51"]
theorem classNumber_mul_regulator_eq_sum_of_discr_pos (hF : QuadraticFieldDiscriminants)
    (hI : QuadraticIdealCount) (hK : finrank ℚ K = 2) (hD : 0 < discr K) :
    ((classNumber K * regulator K : ℝ) : ℂ) = -(1 / 2) *
      ∑ m ∈ Ico 1 (discr K).natAbs,
        kroneckerChar (discr K) m * (Real.log (Real.sin (π * m / discr K)) : ℂ) := by
  have h2 := two_mul_classNumber_mul_regulator_eq_of_discr_pos hF hI hK hD
  rw [LFunction_one_kroneckerChar_of_pos (hF.isFundamental K hK) (one_lt_discr_of_pos hK hD)]
    at h2
  have hs : (√(discr K : ℝ) : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by exact_mod_cast hD)).ne'
  rw [← mul_assoc, mul_neg, mul_inv_cancel₀ hs, neg_one_mul] at h2
  have h2' : ((classNumber K * regulator K : ℝ) : ℂ) =
      ((2 * classNumber K * regulator K : ℝ) : ℂ) / 2 := by push_cast; ring
  rw [h2', h2]
  ring

/-- **Davenport §6, p. 51, with the fundamental unit**: for a fundamental unit `ε` and an infinite
place `w` of a real quadratic field,
`h · |log w(ε)| = -(1/2) ∑_{m=1}^{d-1} (d/m) log sin(πm/d)`. -/
@[kb "davenport1980" "Ch 6, p. 51"]
theorem classNumber_mul_log_eq_sum_of_discr_pos (hF : QuadraticFieldDiscriminants)
    (hI : QuadraticIdealCount) (hK : finrank ℚ K = 2) (hD : 0 < discr K) (ε : (𝓞 K)ˣ)
    (hε : Subgroup.closure {ε} ⊔ torsion K = ⊤) (w : InfinitePlace K) :
    ((classNumber K * |Real.log (w (ε : K))| : ℝ) : ℂ) = -(1 / 2) *
      ∑ m ∈ Ico 1 (discr K).natAbs,
        kroneckerChar (discr K) m * (Real.log (Real.sin (π * m / discr K)) : ℂ) := by
  rw [← regulator_eq_abs_log hK hD ε hε w, classNumber_mul_regulator_eq_sum_of_discr_pos hF hI hK hD]

/-- For an odd discriminant `D = -q`, `q` prime, `(D/m) = (m/q)`. -/
theorem kroneckerChar_natCast_eq_legendreSym {q : ℕ} [Fact q.Prime] {D : ℤ} (hDq : D = -q)
    (hodd : D % 2 = 1) [NeZero D.natAbs] (m : ℕ) :
    kroneckerChar D m = (legendreSym q m : ℂ) := by
  have hn : D.natAbs = q := by rw [hDq, Int.natAbs_neg, Int.natAbs_natCast]
  rw [kroneckerChar_eq_jacobiChar_of_odd hodd]
  have h := jacobiChar_intCast (m := D.natAbs) (m : ℤ)
  push_cast at h
  rw [h, hn, ← jacobiSym.legendreSym.to_jacobiSym]

/-- **Davenport §6, p. 51, (19): Jacobi's class number formula.** For a prime `q ≡ 3 (mod 4)`,
`q > 3`, the quadratic field of discriminant `-q` has class number
`h(-q) = -(1/q) ∑_{m=1}^{q-1} m (m/q)`. -/
@[kb "davenport1980" "Ch 6, p. 51, (19)"]
theorem classNumber_eq_jacobi (hF : QuadraticFieldDiscriminants) (hI : QuadraticIdealCount)
    {q : ℕ} [Fact q.Prime] (hq : q % 4 = 3) (hq3 : 3 < q) (hK : finrank ℚ K = 2)
    (hDq : discr K = -q) :
    (q : ℤ) * classNumber K = -∑ m ∈ Ico 1 q, (m : ℤ) * legendreSym q m := by
  have hD : discr K < 0 := by rw [hDq]; omega
  have hw := torsionOrder_eq_two_of_discr hK (by rw [hDq]; omega) (by rw [hDq]; omega)
  have hn : (discr K).natAbs = q := by rw [hDq, Int.natAbs_neg, Int.natAbs_natCast]
  have hodd : discr K % 2 = 1 := by rw [hDq]; omega
  have h := classNumber_eq_sum_of_discr_neg hF hI hK hD
  simp_rw [kroneckerChar_natCast_eq_legendreSym hDq hodd] at h
  rw [hw, hn] at h
  have hq1 : 1 ≤ q := (Fact.out : q.Prime).one_lt.le
  have hqq : legendreSym q q = 0 := by
    rw [legendreSym.eq_zero_iff]; simp
  rw [← Finset.Ico_add_one_right_eq_Icc, sum_Ico_succ_top hq1] at h
  push_cast [hqq] at h
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero
  apply Int.cast_injective (α := ℂ)
  push_cast
  rw [h]
  field_simp
  ring

end NTKB.Davenport
