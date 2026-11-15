/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.

The deduction of the residue of `ζ_K` from the factorization `ζ_K = ζ L(s, χ_D)` follows
`TauCeti.NumberField.dedekindZeta_residue_eq_LFunction_one` and
`TauCeti.NumberField.classNumber_eq_card_units_mul_LFunction_one` of Tau Ceti
(`TauCeti/NumberTheory/NumberField/Quadratic/DedekindZeta.lean`, Tau Ceti contributors, Apache 2.0),
rewritten for `NTKB.kroneckerChar`.
-/
import NTKB.Analytic.Davenport.Ch1to6.LOneOdd
import NTKB.Analytic.Davenport.Ch1to6.LOneEven
import NTKB.Analytic.Davenport.Ch1to6.LOnePos
import NTKB.Analytic.Davenport.ClassNumber.Torsion
import NTKB.Analytic.Davenport.ClassNumber.Regulator
import Mathlib.NumberTheory.NumberField.DedekindZeta

/-!
# Davenport, Chapter 6: the class number formula of a quadratic field

Davenport, *Multiplicative Number Theory*, §6. Let `K` be a quadratic number field of
discriminant `d` and `χ = (d/·)` its Kronecker character (`NTKB.kroneckerChar d`).

Two cited results are assumed as named statements (the closure of Tau Ceti's proof beyond Mathlib
is 185 files, about 41,600 lines, on another Mathlib commit):

* `QuadraticFieldDiscriminants`: the discriminant of a quadratic field is a fundamental
  discriminant, and every fundamental discriminant `d ≠ 1` is the discriminant of a quadratic
  field;
* `QuadraticIdealCount`: the number of ideals of `𝓞 K` of norm `n ≥ 1` is `∑_{m ∣ n} χ(m)`
  (the decomposition law of rational primes in `K`).

From them:

* `dedekindZeta_eq_riemannZeta_mul_LFunction` (§6, p. 52, (27)): `ζ_K(s) = ζ(s) L(s, χ)` for
  `Re s > 1`;
* `dedekindZeta_residue_eq_LFunction_one`: the residue of `ζ_K` at `1` is `L(1, χ)`;
* `classNumber_eq_of_discr_neg` (§6, p. 49, (15)): for `d < 0`, `h = w √|d| L(1, χ) / (2π)`,
  `w = torsionOrder K` the number of roots of unity (Davenport's number of automorphs);
* `two_mul_classNumber_mul_regulator_eq_of_discr_pos` (§6, p. 49, (16)): for `d > 0`,
  `2 h R = √d L(1, χ)` with `R` the regulator of `K`; `regulator_eq_abs_log` identifies `R` with
  `log ε` for a fundamental unit `ε` (`ε > 1` at a real place), so this is
  `h log ε = (√d / 2) L(1, χ)`. Davenport's `h(d) log ε` counts classes of forms under proper
  equivalence and `ε` is the least unit `> 1` of norm `+1`; their product is `2 h R`
  (§6, p. 55, row 6-24).
-/

noncomputable section

open Complex DirichletCharacter Filter Topology Module NumberField NumberField.InfinitePlace
  NumberField.Units Finset
open scoped Real

namespace NTKB.Davenport

/-! ### The two named statements -/

/-- **Named statement** (cited, assumed): quadratic fields and fundamental discriminants. The
discriminant of a quadratic number field is a fundamental discriminant, and every fundamental
discriminant `d ≠ 1` is the discriminant of a quadratic number field (`ℚ(√d)`). Classical
(Dedekind; Davenport §5, p. 41 and §6, p. 52); Tau Ceti `TauCeti.Multiquadratic.isFundamentalDiscr_discr`. -/
structure QuadraticFieldDiscriminants : Prop where
  isFundamental : ∀ (K : Type) [Field K] [NumberField K], finrank ℚ K = 2 →
    IsFundamentalDiscriminant (discr K)
  exists_field : ∀ D : ℤ, IsFundamentalDiscriminant D → D ≠ 1 →
    ∃ (K : Type) (_ : Field K) (_ : NumberField K), finrank ℚ K = 2 ∧ discr K = D

/-- **Named statement** (cited, assumed): the decomposition law of a quadratic field. In a
quadratic number field `K` of discriminant `d`, the number of ideals of `𝓞 K` of norm `n ≥ 1` is
`∑_{m ∣ n} (d/m)`. Davenport §6, p. 52 (the factorization (27)); Tau Ceti
`TauCeti.NumberField.dedekindZetaCoeff_eq_sum_divisors`. -/
structure QuadraticIdealCount : Prop where
  card_eq : ∀ (K : Type) [Field K] [NumberField K], finrank ℚ K = 2 → ∀ n : ℕ, n ≠ 0 →
    (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℂ) =
      ∑ m ∈ n.divisors, kroneckerChar (discr K) m

/-! ### Generalities -/

instance natAbs_discr_neZero (K : Type*) [Field K] [NumberField K] : NeZero (discr K).natAbs :=
  ⟨Int.natAbs_ne_zero.mpr (discr_ne_zero K)⟩

variable {K : Type} [Field K] [NumberField K]

/-- The Kronecker character of a quadratic field is not principal: it is primitive of conductor
`|d| > 2`. -/
theorem kroneckerChar_discr_ne_one (hF : QuadraticFieldDiscriminants) (hK : finrank ℚ K = 2) :
    kroneckerChar (discr K) ≠ 1 := by
  intro h
  have hprim := kroneckerChar_isPrimitive (hF.isFundamental K hK)
  rw [h, IsPrimitive, conductor_one] at hprim
  have h2 := abs_discr_gt_two (K := K) (by omega)
  have : ((discr K).natAbs : ℤ) = |discr K| := Int.natCast_natAbs _
  omega

/-- **Davenport §6, p. 52, (27).** `ζ_K(s) = ζ(s) L(s, χ)` for `Re s > 1`, from the ideal count. -/
@[kb "davenport1980" "Ch 6, p. 52, (27)"]
theorem dedekindZeta_eq_riemannZeta_mul_LFunction (hI : QuadraticIdealCount)
    (hK : finrank ℚ K = 2) {s : ℂ} (hs : 1 < s.re) :
    dedekindZeta K s = riemannZeta s * LFunction (kroneckerChar (discr K)) s := by
  set χ := kroneckerChar (discr K)
  have hcoeff : ∀ {n : ℕ}, n ≠ 0 →
      (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℂ) = χ.zetaMul n := by
    intro n hn
    rw [hI.card_eq K hK n hn, zetaMul, ArithmeticFunction.coe_zeta_mul_apply]
    refine sum_congr rfl fun m hm ↦ ?_
    rw [χ.apply_eq_toArithmeticFunction_apply (Nat.pos_of_mem_divisors hm).ne']
  rw [dedekindZeta, LSeries_congr hcoeff, zetaMul, ← ArithmeticFunction.coe_mul,
    LSeries_convolution']
  · rw [χ.LFunction_eq_LSeries hs]
    congr 1
    · simp_rw [← ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs, ← ArithmeticFunction.natCoe_apply]
    · exact (LSeries_congr χ.apply_eq_toArithmeticFunction_apply s).symm
  · exact ArithmeticFunction.LSeriesSummable_zeta_iff.mpr hs
  · exact (LSeriesSummable_congr _ fun h ↦ (χ.apply_eq_toArithmeticFunction_apply h).symm).mpr <|
      ZMod.LSeriesSummable_of_one_lt_re χ hs

/-- **The residue of `ζ_K` at `1` is `L(1, χ)`** (Davenport §6, p. 52): `(s - 1) ζ(s) → 1` and
`L(s, χ) → L(1, χ)` as `s → 1⁺`. -/
@[kb "davenport1980" "Ch 6, p. 52"]
theorem dedekindZeta_residue_eq_LFunction_one (hF : QuadraticFieldDiscriminants)
    (hI : QuadraticIdealCount) (hK : finrank ℚ K = 2) :
    (dedekindZeta_residue K : ℂ) = LFunction (kroneckerChar (discr K)) 1 := by
  have hζ : Tendsto (fun s : ℝ ↦ ((s : ℂ) - 1) * riemannZeta s) (𝓝[>] 1) (𝓝 1) :=
    riemannZeta_residue_one.comp <| tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      ((Complex.continuous_ofReal.tendsto' 1 1 Complex.ofReal_one).mono_left nhdsWithin_le_nhds)
      (eventually_nhdsWithin_of_forall fun s hs ↦ by simpa using (Set.mem_Ioi.mp hs).ne')
  have hL : Tendsto (fun s : ℝ ↦ (kroneckerChar (discr K)).LFunction s) (𝓝[>] 1)
      (𝓝 ((kroneckerChar (discr K)).LFunction 1)) :=
    (((differentiable_LFunction (kroneckerChar_discr_ne_one hF hK)).continuous.comp
      Complex.continuous_ofReal).tendsto' 1 _ (by simp)).mono_left nhdsWithin_le_nhds
  have hF' : Tendsto (fun s : ℝ ↦ ((s : ℂ) - 1) * dedekindZeta K s) (𝓝[>] 1)
      (𝓝 ((kroneckerChar (discr K)).LFunction 1)) := by
    refine (one_mul ((kroneckerChar (discr K)).LFunction 1) ▸ hζ.mul hL).congr'
      (eventually_nhdsWithin_of_forall fun s hs ↦ ?_)
    dsimp only
    rw [dedekindZeta_eq_riemannZeta_mul_LFunction hI hK (s := s) (by simpa using hs), mul_assoc]
  have hlim' := tendsto_sub_one_mul_dedekindZeta_nhdsGT K
  exact tendsto_nhds_unique hlim' hF'

/-! ### Signature, roots of unity and regulator of a quadratic field -/

/-- A quadratic field with `d < 0` has one complex place and no real place. -/
theorem nrComplexPlaces_eq_one_of_discr_neg (hK : finrank ℚ K = 2) (hD : discr K < 0) :
    nrRealPlaces K = 0 ∧ nrComplexPlaces K = 1 := by
  have h := card_add_two_mul_card_eq_rank K
  have hs := sign_discr K
  rw [Int.sign_eq_neg_one_of_neg hD] at hs
  rw [hK] at h
  rcases (by omega : nrComplexPlaces K = 0 ∨ nrComplexPlaces K = 1) with h0 | h1
  · rw [h0, pow_zero] at hs; norm_num at hs
  · omega

/-- A quadratic field with `d > 0` has two real places and no complex place. -/
theorem nrRealPlaces_eq_two_of_discr_pos (hK : finrank ℚ K = 2) (hD : 0 < discr K) :
    nrRealPlaces K = 2 ∧ nrComplexPlaces K = 0 := by
  have h := card_add_two_mul_card_eq_rank K
  have hs := sign_discr K
  rw [Int.sign_eq_one_of_pos hD] at hs
  rw [hK] at h
  rcases (by omega : nrComplexPlaces K = 0 ∨ nrComplexPlaces K = 1) with h0 | h1
  · omega
  · rw [h1, pow_one] at hs; norm_num at hs

/-- The unit rank of an imaginary quadratic field is `0`. -/
theorem rank_eq_zero_of_discr_neg (hK : finrank ℚ K = 2) (hD : discr K < 0) : rank K = 0 := by
  obtain ⟨h1, h2⟩ := nrComplexPlaces_eq_one_of_discr_neg hK hD
  rw [rank, card_eq_nrRealPlaces_add_nrComplexPlaces, h1, h2]

/-- The unit rank of a real quadratic field is `1`. -/
theorem rank_eq_one_of_discr_pos (hK : finrank ℚ K = 2) (hD : 0 < discr K) : rank K = 1 := by
  obtain ⟨h1, h2⟩ := nrRealPlaces_eq_two_of_discr_pos hK hD
  rw [rank, card_eq_nrRealPlaces_add_nrComplexPlaces, h1, h2]

/-- The regulator of an imaginary quadratic field is `1` (the determinant of an empty matrix). -/
theorem regulator_eq_one_of_discr_neg (hK : finrank ℚ K = 2) (hD : discr K < 0) :
    regulator K = 1 := by
  classical
  have h0 := rank_eq_zero_of_discr_neg hK hD
  rw [regulator_eq_det']
  have : IsEmpty (Fin (rank K)) := by rw [h0]; exact Fin.isEmpty'
  have := (equivFinRank K).symm.isEmpty
  rw [Matrix.det_isEmpty, abs_one]

/-! ### The class number formulas -/

/-- `L(1, χ)` is the residue of `ζ_K` at `1`, a positive real number. -/
theorem LFunction_one_eq_residue (hF : QuadraticFieldDiscriminants) (hI : QuadraticIdealCount)
    (hK : finrank ℚ K = 2) :
    LFunction (kroneckerChar (discr K)) 1 = (dedekindZeta_residue K : ℂ) :=
  (dedekindZeta_residue_eq_LFunction_one hF hI hK).symm

/-- The residue of `ζ_K` for `d < 0`: `2π h / (w √|d|)`. -/
theorem dedekindZeta_residue_of_discr_neg (hK : finrank ℚ K = 2) (hD : discr K < 0) :
    dedekindZeta_residue K =
      2 * π * classNumber K / (torsionOrder K * √|(discr K : ℝ)|) := by
  obtain ⟨h1, h2⟩ := nrComplexPlaces_eq_one_of_discr_neg hK hD
  rw [dedekindZeta_residue_def, h1, h2, regulator_eq_one_of_discr_neg hK hD]
  ring

/-- The residue of `ζ_K` for `d > 0`: `2 h R / √d`. -/
theorem dedekindZeta_residue_of_discr_pos (hK : finrank ℚ K = 2) (hD : 0 < discr K) :
    dedekindZeta_residue K = 2 * classNumber K * regulator K / √(discr K : ℝ) := by
  obtain ⟨h1, h2⟩ := nrRealPlaces_eq_two_of_discr_pos hK hD
  have hw := torsionOrder_eq_two_of_discr hK (by omega) (by omega)
  have habs : |(discr K : ℝ)| = discr K := abs_of_pos (by exact_mod_cast hD)
  have hs : 0 < √(discr K : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hD)
  rw [dedekindZeta_residue_def, h1, h2, hw, habs]
  field_simp
  ring

/-- **Davenport §6, p. 49, (15): the class number formula for `d < 0`.**
`h(d) = w √|d| L(1, χ) / (2π)`, `w` the number of roots of unity of `K`. -/
@[kb "davenport1980" "Ch 6, p. 49, (15)"]
theorem classNumber_eq_of_discr_neg (hF : QuadraticFieldDiscriminants) (hI : QuadraticIdealCount)
    (hK : finrank ℚ K = 2) (hD : discr K < 0) :
    (classNumber K : ℂ) =
      torsionOrder K * √|(discr K : ℝ)| * LFunction (kroneckerChar (discr K)) 1 / (2 * π) := by
  rw [LFunction_one_eq_residue hF hI hK, dedekindZeta_residue_of_discr_neg hK hD]
  have hs : (√|(discr K : ℝ)| : ℂ) ≠ 0 := ofReal_ne_zero.mpr
    (Real.sqrt_pos.mpr (abs_pos.mpr (Int.cast_ne_zero.mpr (discr_ne_zero K)))).ne'
  have hw : (torsionOrder K : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (torsionOrder_pos K).ne'
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_pos.ne'
  push_cast
  field_simp

/-- **Davenport §6, p. 49, (16): the class number formula for `d > 0`**, with the regulator:
`2 h R = √d L(1, χ)` (Davenport's `h(d) log ε` is `2 h R`, row 6-24). -/
@[kb "davenport1980" "Ch 6, p. 49, (16)"]
theorem two_mul_classNumber_mul_regulator_eq_of_discr_pos (hF : QuadraticFieldDiscriminants)
    (hI : QuadraticIdealCount) (hK : finrank ℚ K = 2) (hD : 0 < discr K) :
    ((2 * classNumber K * regulator K : ℝ) : ℂ) =
      √(discr K : ℝ) * LFunction (kroneckerChar (discr K)) 1 := by
  rw [LFunction_one_eq_residue hF hI hK, dedekindZeta_residue_of_discr_pos hK hD]
  have hs : 0 < √(discr K : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hD)
  rw [← ofReal_mul, mul_div_cancel₀ _ hs.ne']

/-- **Davenport §6, p. 49, (16), with the fundamental unit**: for a fundamental unit `ε` and an
infinite place `w` of a real quadratic field, `h · |log w(ε)| = √d L(1, χ) / 2`. -/
@[kb "davenport1980" "Ch 6, p. 49, (16)"]
theorem classNumber_mul_log_eq_of_discr_pos (hF : QuadraticFieldDiscriminants)
    (hI : QuadraticIdealCount) (hK : finrank ℚ K = 2) (hD : 0 < discr K) (ε : (𝓞 K)ˣ)
    (hε : Subgroup.closure {ε} ⊔ torsion K = ⊤) (w : InfinitePlace K) :
    ((classNumber K * |Real.log (w (ε : K))| : ℝ) : ℂ) =
      √(discr K : ℝ) * LFunction (kroneckerChar (discr K)) 1 / 2 := by
  rw [← regulator_eq_abs_log hK hD ε hε w, ← two_mul_classNumber_mul_regulator_eq_of_discr_pos
    hF hI hK hD]
  push_cast
  ring

end NTKB.Davenport
