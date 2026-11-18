/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Davenport.Zeros.ArgVariation
import NTKB.Analytic.Davenport.Zeros.RiemannVonMangoldt

/-!
# The zeros of `ζ` in the book's form: argument changes, infinitude, symmetry

**Davenport, Ch. 15, p. 97 (rows 15-1, 15-2).** For `T > 0` not the ordinate of a zero,
`2π N(T) = Δ_R arg ξ(s)`, `R` the rectangle with vertices `2, 2 + iT, -1 + iT, -1` described
counterclockwise, the argument changing by continuous variation (`ArgVariation`); by the
symmetries of `ξ` the left half equals the right half, so `π N(T) = Δ_L arg ξ(s)`, `L` the path
`2 → 2 + iT → 1/2 + iT`. The library proved these as integrals of `ξ'/ξ`
(`Davenport.rectIntegral_logDeriv_riemannXi`, `Davenport.pi_mul_zetaZeroCount_eq`); here they are
stated as changes of argument, in the book's wording.

**Davenport, Ch. 8, p. 69 (rows 8-5, 8-6).** `ζ` has infinitely many zeros in the critical strip,
symmetric about the real axis and about the line `σ = 1/2`; von Mangoldt's
`N(T) = (T/2π) log(T/2π) - T/2π + O(log T)` (proved in Ch. 15: `Davenport.zetaZeroCount_sub_le`),
here also for the count with `0 < γ ≤ T` and together with the change of argument.
Source text unavailable: the statements follow the map's paraphrases.
-/

open Filter Topology Complex Set
open scoped Real Interval ComplexConjugate

namespace NTKB

/-- Along a vertical line on which `ξ` has no zero, the change of argument is `∫ Re ξ'/ξ`. -/
lemma argChange_riemannXi_vert {c : ℂ} (h0 : ∀ y : ℝ, riemannXi (c + y * I) ≠ 0) (a b : ℝ) :
    argChange (fun y : ℝ ↦ riemannXi (c + y * I)) a b =
      ∫ y in a..b, (logDeriv riemannXi (c + y * I)).re := by
  have hcd : Continuous (deriv riemannXi) := continuous_iff_continuousAt.2 fun s ↦
    (differentiable_riemannXi.analyticAt s).deriv.continuousAt
  have hd : ∀ y : ℝ, HasDerivAt (fun y : ℝ ↦ riemannXi (c + y * I))
      (deriv riemannXi (c + y * I) * I) y := fun y ↦ by
    have hp : HasDerivAt (fun y : ℝ ↦ c + (y : ℂ) * I) I y := by
      simpa using ((hasDerivAt_id y).ofReal_comp.mul_const I).const_add c
    exact (differentiable_riemannXi (c + y * I)).hasDerivAt.comp y hp
  rw [argChange_eq_im_integral (α := min a b - 1) (β := max a b + 1) (by linarith) (by linarith)
    (fun y _ ↦ hd y) ((((hcd.comp (by fun_prop : Continuous fun y : ℝ ↦ c + (y : ℂ) * I))).mul
      continuous_const).continuousOn) (fun y _ ↦ h0 y)]
  have e : ∀ y : ℝ, deriv riemannXi (c + y * I) * I / riemannXi (c + y * I) =
      logDeriv riemannXi (c + y * I) * I := fun y ↦ by rw [logDeriv_apply]; ring
  simp_rw [e]
  rw [intervalIntegral.integral_mul_const, Complex.mul_I_im]
  have hint : IntervalIntegrable (fun y : ℝ ↦ logDeriv riemannXi (c + y * I)) MeasureTheory.volume
      a b := (continuous_logDeriv_riemannXi_comp (by fun_prop) h0).intervalIntegrable a b
  exact (Complex.reCLM.intervalIntegral_comp_comm hint).symm

/-- Along a horizontal line on which `ξ` has no zero, the change of argument is `∫ Im ξ'/ξ`. -/
lemma argChange_riemannXi_horiz {c : ℂ} (h0 : ∀ x : ℝ, riemannXi (x + c) ≠ 0) (a b : ℝ) :
    argChange (fun x : ℝ ↦ riemannXi (x + c)) a b =
      ∫ x in a..b, (logDeriv riemannXi (x + c)).im := by
  have hcd : Continuous (deriv riemannXi) := continuous_iff_continuousAt.2 fun s ↦
    (differentiable_riemannXi.analyticAt s).deriv.continuousAt
  have hd : ∀ x : ℝ, HasDerivAt (fun x : ℝ ↦ riemannXi (x + c))
      (deriv riemannXi (x + c)) x := fun x ↦ by
    have hp : HasDerivAt (fun x : ℝ ↦ (x : ℂ) + c) 1 x := by
      simpa using (hasDerivAt_id x).ofReal_comp.add_const c
    have := (differentiable_riemannXi (x + c)).hasDerivAt.comp x hp
    rwa [mul_one] at this
  rw [argChange_eq_im_integral (α := min a b - 1) (β := max a b + 1) (by linarith) (by linarith)
    (fun x _ ↦ hd x) ((hcd.comp (by fun_prop : Continuous fun x : ℝ ↦ (x : ℂ) + c)).continuousOn)
    (fun x _ ↦ h0 x)]
  have e : ∀ x : ℝ, deriv riemannXi (x + c) / riemannXi (x + c) = logDeriv riemannXi (x + c) :=
    fun x ↦ by rw [logDeriv_apply]
  simp_rw [e]
  have hint : IntervalIntegrable (fun x : ℝ ↦ logDeriv riemannXi (x + c)) MeasureTheory.volume
      a b := (continuous_logDeriv_riemannXi_comp (by fun_prop) h0).intervalIntegrable a b
  exact (Complex.imCLM.intervalIntegral_comp_comm hint).symm

lemma logDeriv_riemannXi_horiz_im_symm {T : ℝ} (x : ℝ) :
    (logDeriv riemannXi (x + T * I)).im = (logDeriv riemannXi (((1 - x : ℝ) : ℂ) + T * I)).im := by
  have h1 : logDeriv riemannXi (x + T * I) = -logDeriv riemannXi (1 - (x + T * I)) := by
    rw [logDeriv_riemannXi_one_sub, neg_neg]
  have h2 : (1 : ℂ) - (x + T * I) = conj (((1 - x : ℝ) : ℂ) + T * I) := by
    apply Complex.ext <;> simp
  rw [h1, h2, logDeriv_riemannXi_conj]
  simp

lemma integral_im_logDeriv_riemannXi_horiz_double {T : ℝ}
    (hTz : ∀ ρ : ZeroIndex riemannXi, |ρ.val.im| ≠ T) (hT : 0 < T) :
    ∫ x in (-1 : ℝ)..2, (logDeriv riemannXi (x + T * I)).im =
      2 * ∫ x in (1 / 2 : ℝ)..2, (logDeriv riemannXi (x + T * I)).im := by
  have hcT := continuous_logDeriv_riemannXi_horiz hTz T (abs_of_pos hT)
  have hhim : Continuous fun x : ℝ ↦ (logDeriv riemannXi (x + T * I)).im :=
    Complex.continuous_im.comp hcT
  rw [← intervalIntegral.integral_add_adjacent_intervals (hhim.intervalIntegrable (-1) (1 / 2))
    (hhim.intervalIntegrable (1 / 2) 2)]
  have : ∫ x in (-1 : ℝ)..1 / 2, (logDeriv riemannXi (x + T * I)).im =
      ∫ x in (1 / 2 : ℝ)..2, (logDeriv riemannXi (x + T * I)).im := by
    have h1 : ∫ x in (-1 : ℝ)..1 / 2, (logDeriv riemannXi (x + T * I)).im =
        ∫ x in (-1 : ℝ)..1 / 2, (logDeriv riemannXi (((1 - x : ℝ) : ℂ) + T * I)).im :=
      intervalIntegral.integral_congr fun x _ ↦ logDeriv_riemannXi_horiz_im_symm x
    rw [h1, intervalIntegral.integral_comp_sub_left
      (fun x : ℝ ↦ (logDeriv riemannXi ((x : ℂ) + T * I)).im)]
    norm_num
  rw [this]; ring

lemma riemannXi_real_ne_zero (x : ℝ) : riemannXi x ≠ 0 := by
  intro h
  rcases riemannXi_eq_zero_iff.mp h with ⟨hz, h0, h1⟩
  have h0' : 0 < x := by simpa using h0
  have h1' : x < 1 := by simpa using h1
  have := (NTKB.Apostol.riemannZeta_neg_of_lt_one h0' h1').2
  rw [hz] at this
  simp at this

lemma riemannXi_real_im (x : ℝ) : (riemannXi x).im = 0 := by
  have h := riemannXi_conj (x : ℂ)
  rw [Complex.conj_ofReal] at h
  have := congrArg Complex.im h
  simp at this
  linarith

lemma riemannXi_real_re_pos (x : ℝ) : 0 < (riemannXi x).re := by
  have hc : Continuous fun t : ℝ ↦ (riemannXi t).re :=
    Complex.continuous_re.comp (differentiable_riemannXi.continuous.comp Complex.continuous_ofReal)
  have hne : ∀ t : ℝ, (riemannXi t).re ≠ 0 := fun t h0 ↦ riemannXi_real_ne_zero t
    (Complex.ext (by simpa using h0) (by simpa using riemannXi_real_im t))
  by_contra hle
  push Not at hle
  have hlt : (riemannXi x).re < 0 := lt_of_le_of_ne hle (hne x)
  have h1 : (riemannXi ((1 : ℝ) : ℂ)).re = 1 / 2 := by simp
  obtain ⟨s, -, hs⟩ := intermediate_value_uIcc (a := x) (b := 1) hc.continuousOn
    (show (0 : ℝ) ∈ Set.uIcc ((riemannXi x).re) ((riemannXi ((1 : ℝ) : ℂ)).re) from by
      rw [h1]; exact Set.mem_uIcc.mpr (Or.inl ⟨hlt.le, by norm_num⟩))
  exact hne s hs

lemma finite_zeroIndex_val_preimage {S : Set ℂ} (hS : S.Finite) :
    {ρ : ZeroIndex riemannXi | ρ.val ∈ S}.Finite := by
  refine Set.Finite.preimage' hS (f := fun ρ : ZeroIndex riemannXi ↦ ρ.val) fun b _ ↦ ?_
  refine (Set.finite_range
    (fun k : Fin (analyticOrderNatAt riemannXi b) ↦ (⟨b, k⟩ : ZeroIndex riemannXi))).subset ?_
  rintro ⟨z, k⟩ hz
  have hz' : z = b := hz
  subst hz'
  exact ⟨k, rfl⟩

lemma finite_zeroIndex_lt (T : ℝ) :
    {ρ : ZeroIndex riemannXi | 0 < ρ.val.im ∧ ρ.val.im < T}.Finite := by
  refine (zerosBelow T).finite_toSet.subset fun ρ hρ ↦ ?_
  rw [Finset.mem_coe, mem_zerosBelow, abs_of_pos hρ.1]
  exact hρ.2

/-- The number of zeros `ρ = β + iγ` of `ζ` in the critical strip with `0 < γ ≤ T`, counted with
multiplicity (the closed count; it differs from `zetaZeroCount T` only at ordinates). -/
noncomputable def zetaZeroCountLE (T : ℝ) : ℕ :=
  Nat.card {ρ : ZeroIndex riemannXi // 0 < ρ.val.im ∧ ρ.val.im ≤ T}

lemma nat_card_subtype_mono {p q : ZeroIndex riemannXi → Prop} (hq : {ρ | q ρ}.Finite)
    (h : ∀ ρ, p ρ → q ρ) : Nat.card {ρ // p ρ} ≤ Nat.card {ρ // q ρ} :=
  Nat.card_mono (s := {ρ | p ρ}) (t := {ρ | q ρ}) hq h

lemma zetaZeroCount_le_LE (T : ℝ) : zetaZeroCount T ≤ zetaZeroCountLE T := by
  refine nat_card_subtype_mono ?_ fun ρ hρ ↦ ⟨hρ.1, hρ.2.le⟩
  refine (finite_zeroIndex_lt (T + 1)).subset fun ρ hρ ↦ ?_
  exact ⟨hρ.1, by linarith [hρ.2]⟩

lemma zetaZeroCountLE_le (T : ℝ) : zetaZeroCountLE T ≤ zetaZeroCount (T + 1) :=
  nat_card_subtype_mono (finite_zeroIndex_lt (T + 1)) fun ρ hρ ↦ ⟨hρ.1, by linarith [hρ.2]⟩

/-- **Davenport, Ch. 15, p. 97 (row 15-2)**: for `T > 0` not an ordinate, `π N(T)` is the change
of argument of `ξ(s)` by continuous variation along `2 → 2 + iT → 1/2 + iT`. -/
@[kb "davenport1980" "Ch 15, p. 97"]
theorem Davenport.pi_mul_zetaZeroCount_eq_argChange {T : ℝ} (hT : 0 < T)
    (hTz : ∀ ρ : ZeroIndex riemannXi, |ρ.val.im| ≠ T) :
    π * zetaZeroCount T = argChange (fun y : ℝ ↦ riemannXi (2 + y * I)) 0 T +
      argChange (fun x : ℝ ↦ riemannXi (x + T * I)) 2 (1 / 2) := by
  have h0H : ∀ x : ℝ, riemannXi (x + T * I) ≠ 0 := fun x ↦
    riemannXi_ne_zero_of_abs_im hTz (by simp [abs_of_pos hT])
  rw [argChange_riemannXi_vert (c := 2) riemannXi_two_add_ne_zero,
    argChange_riemannXi_horiz (c := T * I) h0H, Davenport.pi_mul_zetaZeroCount_eq hT hTz,
    zetaRealZeroCount_eq_zero, intervalIntegral.integral_symm (1 / 2 : ℝ) 2]
  simp; ring

/-- **Davenport, Ch. 15, p. 97 (row 15-1)**, the argument principle in the book's form: for `T > 0`
not an ordinate, `2π N(T)` is the change of argument of `ξ(s)` by continuous variation around the
rectangle with vertices `2, 2 + iT, -1 + iT, -1`, the sum of the changes along its four sides
`2 → 2 + iT → -1 + iT → -1 → 2`. -/
@[kb "davenport1980" "Ch 15, p. 97"]
theorem Davenport.two_pi_mul_zetaZeroCount_eq_argChange {T : ℝ} (hT : 0 < T)
    (hTz : ∀ ρ : ZeroIndex riemannXi, |ρ.val.im| ≠ T) :
    2 * π * zetaZeroCount T =
      argChange (fun y : ℝ ↦ riemannXi (2 + y * I)) 0 T +
      argChange (fun x : ℝ ↦ riemannXi (x + T * I)) 2 (-1) +
      argChange (fun y : ℝ ↦ riemannXi (-1 + y * I)) T 0 +
      argChange (fun x : ℝ ↦ riemannXi x) (-1) 2 := by
  have h0H : ∀ x : ℝ, riemannXi (x + T * I) ≠ 0 := fun x ↦
    riemannXi_ne_zero_of_abs_im hTz (by simp [abs_of_pos hT])
  have h0L : ∀ y : ℝ, riemannXi (-1 + y * I) ≠ 0 := fun y h ↦ by
    have e : (-1 : ℂ) + y * I = 1 - (2 + ((-y : ℝ) : ℂ) * I) := by
      apply Complex.ext <;> simp <;> norm_num
    rw [e, riemannXi_one_sub] at h
    exact riemannXi_two_add_ne_zero _ h
  have hbase : argChange (fun x : ℝ ↦ riemannXi x) (-1) 2 = 0 :=
    argChange_eq (fun t _ ↦ riemannXi_real_ne_zero t)
      (isArgChange_zero_of_pos fun t _ ↦ ⟨riemannXi_real_re_pos t, riemannXi_real_im t⟩)
  have hre : ∀ y : ℝ, (logDeriv riemannXi (-1 + y * I)).re =
      -(logDeriv riemannXi (2 + y * I)).re := by
    intro y
    have e : (-1 : ℂ) + y * I = 1 - conj (2 + y * I) := by
      apply Complex.ext <;> simp <;> norm_num
    rw [e, logDeriv_riemannXi_one_sub, logDeriv_riemannXi_conj]; simp
  have hleft : argChange (fun y : ℝ ↦ riemannXi (-1 + y * I)) T 0 =
      ∫ y in (0 : ℝ)..T, (logDeriv riemannXi (2 + y * I)).re := by
    rw [argChange_riemannXi_vert h0L, intervalIntegral.integral_symm]
    simp_rw [hre]
    rw [intervalIntegral.integral_neg, neg_neg]
  have h15 := Davenport.pi_mul_zetaZeroCount_eq_argChange hT hTz
  rw [argChange_riemannXi_vert (c := 2) riemannXi_two_add_ne_zero,
    argChange_riemannXi_horiz (c := T * I) h0H, intervalIntegral.integral_symm (1 / 2 : ℝ) 2]
    at h15
  rw [argChange_riemannXi_vert (c := 2) riemannXi_two_add_ne_zero,
    argChange_riemannXi_horiz (c := T * I) h0H, hleft, hbase,
    intervalIntegral.integral_symm (-1 : ℝ) 2,
    integral_im_logDeriv_riemannXi_horiz_double hTz hT]
  linarith

/-- **Davenport, Ch. 8, p. 69 (row 8-6), von Mangoldt's formula in the book's form**: there is
`A > 0` such that for every `T ≥ 3`, with `N(T)` the number of zeros of `ζ` with `0 < γ < T` or with
`0 < γ ≤ T`, `|N(T) - ((T/2π) log(T/2π) - T/2π)| ≤ A log T`; and when `T` is not an ordinate,
`2π N(T)` is the change of argument of `ξ` around the rectangle `2, 2 + iT, -1 + iT, -1` (15-1). -/
@[kb "davenport1980" "Ch 8, p. 69"]
theorem Davenport.riemann_von_mangoldt_argChange :
    ∃ A : ℝ, 0 < A ∧ ∀ T : ℝ, 3 ≤ T →
      |(zetaZeroCount T : ℝ) - (T / (2 * π) * Real.log (T / (2 * π)) - T / (2 * π))| ≤
          A * Real.log T ∧
      |(zetaZeroCountLE T : ℝ) - (T / (2 * π) * Real.log (T / (2 * π)) - T / (2 * π))| ≤
          A * Real.log T ∧
      ((∀ ρ : ZeroIndex riemannXi, |ρ.val.im| ≠ T) →
        2 * π * zetaZeroCount T =
          argChange (fun y : ℝ ↦ riemannXi (2 + y * I)) 0 T +
          argChange (fun x : ℝ ↦ riemannXi (x + T * I)) 2 (-1) +
          argChange (fun y : ℝ ↦ riemannXi (-1 + y * I)) T 0 +
          argChange (fun x : ℝ ↦ riemannXi x) (-1) 2) := by
  obtain ⟨A₀, hA₀, hA⟩ := Davenport.zetaZeroCount_sub_le
  have hlog3 : 1 ≤ Real.log 3 := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    have := Real.exp_one_lt_d9; linarith
  refine ⟨2 * A₀ + 6, by positivity, fun T hT ↦ ?_⟩
  have hlogT : 1 ≤ Real.log T := hlog3.trans (Real.log_le_log (by norm_num) hT)
  have hT2 : 2 ≤ T := by linarith
  have hl1 : Real.log (T + 1) ≤ 2 * Real.log T := by
    rw [← Real.log_rpow (by linarith)]
    exact Real.log_le_log (by linarith) (by norm_num; nlinarith)
  have e0 := hA T hT
  have e1 := hA (T + 1) (by linarith)
  have m1 := abs_zetaZeroCountMain_sub_le hT2 (le_add_of_nonneg_right zero_le_one) le_rfl
  have n1 : (zetaZeroCount T : ℝ) ≤ zetaZeroCountLE T := by exact_mod_cast zetaZeroCount_le_LE T
  have n2 : (zetaZeroCountLE T : ℝ) ≤ zetaZeroCount (T + 1) := by
    exact_mod_cast zetaZeroCountLE_le T
  change |(zetaZeroCount T : ℝ) - zetaZeroCountMain T| ≤ _ at e0
  change |(zetaZeroCount (T + 1) : ℝ) - zetaZeroCountMain (T + 1)| ≤ _ at e1
  refine ⟨?_, ?_, fun hTz ↦ Davenport.two_pi_mul_zetaZeroCount_eq_argChange (by linarith) hTz⟩
  · change |(zetaZeroCount T : ℝ) - zetaZeroCountMain T| ≤ _
    rw [abs_le] at e0 ⊢
    constructor <;> nlinarith
  · change |(zetaZeroCountLE T : ℝ) - zetaZeroCountMain T| ≤ _
    rw [abs_le] at e0 e1 m1 ⊢
    constructor <;> nlinarith

/-- **Davenport, Ch. 8, p. 69 (row 8-6)** in `O`-form:
`N(T) - ((T/2π) log(T/2π) - T/2π) = O(log T)` as `T → ∞`. -/
@[kb "davenport1980" "Ch 8, p. 69"]
theorem Davenport.zetaZeroCount_sub_isBigO :
    (fun T : ℝ ↦ (zetaZeroCount T : ℝ) - (T / (2 * π) * Real.log (T / (2 * π)) - T / (2 * π)))
      =O[atTop] Real.log := by
  obtain ⟨A, -, hA⟩ := Davenport.zetaZeroCount_sub_le
  refine Asymptotics.IsBigO.of_bound A ?_
  filter_upwards [eventually_ge_atTop (3 : ℝ)] with T hT
  have hlog : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hlog]
  exact hA T hT

/-- **Davenport, Ch. 8, p. 69 (row 8-5)**, the symmetries: if `ρ` is a zero of `ζ` in the critical
strip, so are `ρ̄` (symmetry about the real axis), `1 - ρ` and `1 - ρ̄` (symmetry about `σ = 1/2`). -/
@[kb "davenport1980" "Ch 8, p. 69"]
theorem Davenport.riemannZeta_zero_symm {ρ : ℂ} (hρ : riemannZeta ρ = 0) (h0 : 0 < ρ.re)
    (h1 : ρ.re < 1) :
    (riemannZeta (conj ρ) = 0 ∧ 0 < (conj ρ).re ∧ (conj ρ).re < 1) ∧
      (riemannZeta (1 - ρ) = 0 ∧ 0 < (1 - ρ).re ∧ (1 - ρ).re < 1) ∧
      (riemannZeta (1 - conj ρ) = 0 ∧ 0 < (1 - conj ρ).re ∧ (1 - conj ρ).re < 1) := by
  have hξ : riemannXi ρ = 0 := riemannXi_eq_zero_iff.mpr ⟨hρ, h0, h1⟩
  have hc : riemannXi (conj ρ) = 0 := by rw [riemannXi_conj, hξ, map_zero]
  have h1c : riemannXi (1 - ρ) = 0 := by rw [riemannXi_one_sub, hξ]
  have h2c : riemannXi (1 - conj ρ) = 0 := by rw [riemannXi_one_sub, hc]
  exact ⟨riemannXi_eq_zero_iff.mp hc, riemannXi_eq_zero_iff.mp h1c,
    riemannXi_eq_zero_iff.mp h2c⟩

/-- **Davenport, Ch. 8, p. 69 (row 8-5)**: `ζ` has infinitely many zeros in the critical strip
`0 < σ < 1` (here from von Mangoldt's formula; Riemann's route is the order of `ξ`), indeed
infinitely many with `γ > 0`. -/
@[kb "davenport1980" "Ch 8, p. 69"]
theorem Davenport.riemannZeta_zeros_infinite :
    {ρ : ℂ | riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im}.Infinite := by
  intro hfin
  obtain ⟨A, hA, hB⟩ := Davenport.zetaZeroCount_sub_le
  have hfZ : {ρ : ZeroIndex riemannXi | 0 < ρ.val.im}.Finite := by
    refine (finite_zeroIndex_val_preimage hfin).subset fun ρ hρ ↦ ?_
    have h := riemannXi_zero_mem ρ
    exact ⟨h.1, h.2.1, h.2.2, hρ⟩
  set C : ℕ := Nat.card {ρ : ZeroIndex riemannXi // 0 < ρ.val.im} with hC
  have hbd : ∀ T : ℝ, zetaZeroCount T ≤ C := fun T ↦
    nat_card_subtype_mono hfZ fun ρ hρ ↦ hρ.1
  set c : ℝ := 3 * A + C + 3 with hc
  have hCnn : (0 : ℝ) ≤ C := Nat.cast_nonneg _
  have hc0 : 0 < c := by positivity
  set x : ℝ := Real.exp c with hx
  have hx1 : c + 1 ≤ x := by have := Real.add_one_le_exp c; linarith
  have hxpos : 0 < x := Real.exp_pos c
  have hlogx : Real.log x = c := Real.log_exp c
  have hπ := Real.pi_pos
  have hπ3 := Real.pi_gt_three
  set T : ℝ := 2 * π * x with hT
  have hT3 : 3 ≤ T := by nlinarith
  have hTx : T / (2 * π) = x := by rw [hT]; field_simp
  have hlogT : Real.log T = Real.log (2 * π) + c := by
    rw [hT, Real.log_mul (by positivity) hxpos.ne', hlogx]
  have hl2π : Real.log (2 * π) ≤ 2 := by
    rw [Real.log_le_iff_le_exp (by positivity)]
    have h := Real.exp_one_gt_d9
    have e2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    have hee : 7 < Real.exp 2 := by rw [e2]; nlinarith
    have := Real.pi_lt_d2
    linarith
  have hl2π' : 0 ≤ Real.log (2 * π) := Real.log_nonneg (by linarith)
  have h1 := hB T hT3
  rw [hTx, hlogx, hlogT] at h1
  have h2 := (abs_le.mp h1).1
  have h3' : (zetaZeroCount T : ℝ) ≤ C := by exact_mod_cast hbd T
  have h4 := mul_le_mul_of_nonneg_left hl2π hA.le
  nlinarith [mul_le_mul_of_nonneg_left hx1 (by linarith : (0:ℝ) ≤ c - 1)]

end NTKB
