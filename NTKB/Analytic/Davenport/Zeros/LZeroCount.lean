/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Davenport.Zeros.LZeroCountVertical
import NTKB.Analytic.Davenport.Zeros.ZeroCountHoriz
import NTKB.Analytic.Davenport.Zeros.RiemannVonMangoldt

/-!
# `N(T, χ)`

**Davenport, Ch. 16, pp. 101-102 (rows 16-2, 16-4).** For `χ` primitive mod `q > 1` and
`T ≥ 2`, `½ N(T, χ) = (T/2π) log(qT/2π) - T/2π + O(log qT)` with an absolute constant
(`Davenport.LZeroCount_sub_le`), where `N(T, χ)` counts the zeros of `L(s, χ)` in
`0 < σ < 1`, `|t| < T` with multiplicity.

The horizontal sides (`Davenport.abs_integral_im_logDeriv_dirichletXi_le`, the analogue of
`arg L(1/2 + iT, χ) = O(log qT)`, row 16-4) are estimated by 16-6 and 16-7 as for `ζ`.
-/

open Filter Topology Complex Set MeasureTheory DirichletCharacter
open scoped Real Interval

namespace NTKB

variable {N : ℕ} [NeZero N]

/-- **Davenport, Ch. 16, p. 102 (row 16-4, in integral form)**: for primitive `χ` mod `q > 1`,
`T ≥ 2` not an ordinate and `h = ±T`, `|∫_{1/2}^{3/2} Im ξ'/ξ(x + ih, χ) dx| ≤ A (log q + log(T + 2))`. -/
@[kb "davenport1980" "Ch 16, p. 102"]
theorem Davenport.abs_integral_im_logDeriv_dirichletXi_le :
    ∃ A : ℝ, 0 < A ∧ ∀ {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}, χ.IsPrimitive → N ≠ 1 →
      ∀ T : ℝ, 2 ≤ T → (∀ ρ : ZeroIndex (dirichletXi χ), |ρ.val.im| ≠ T) →
      ∀ h : ℝ, |h| = T →
      |∫ x in (1 / 2 : ℝ)..3 / 2, (logDeriv (dirichletXi χ) (x + h * I)).im| ≤
        A * (Real.log N + Real.log (T + 2)) := by
  classical
  obtain ⟨A₁, hA₁, h₁⟩ := Davenport.logDeriv_LFunction_local
  obtain ⟨A₂, hA₂, h₂⟩ := Davenport.card_L_zeros_near_le
  set B : ℝ := A₁ + 6 with hB
  refine ⟨π * A₂ + B, by positivity, fun {N} _ {χ} hχ hN T hT hTz h hh ↦ ?_⟩
  have hχ1 := ne_one_of_isPrimitive hχ hN
  have hT0 : 0 < T := by linarith
  have hlog4 : 1 ≤ Real.log (T + 2) := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9; linarith
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg hN1
  obtain ⟨hfin, hcard⟩ := h₂ hχ hN h
  rw [hh] at hcard
  set S := hfin.toFinset with hS
  have hSc : (S.card : ℝ) ≤ A₂ * (Real.log N + Real.log (T + 2)) := by
    rw [hS, ← Set.ncard_eq_toFinset_card _ hfin]
    exact hcard
  set f : ℝ → ℂ := fun x ↦ logDeriv (dirichletXi χ) (x + h * I) with hf
  set g : ℝ → ℂ := fun x ↦ ∑ ρ ∈ S, 1 / ((x : ℂ) + h * I - ρ.val) with hg
  have hξ : ∀ x : ℝ, dirichletXi χ (x + h * I) ≠ 0 := fun x ↦
    dirichletXi_ne_zero_of_abs_im hχ hN hTz (by simpa using hh)
  have hfc : Continuous f := continuous_logDeriv_dirichletXi_comp hχ1 (by fun_prop) hξ
  have hγ : ∀ ρ : ZeroIndex (dirichletXi χ), ρ.val.im ≠ h := fun ρ e ↦
    hTz ρ (by rw [e, hh])
  have hinv : ∀ ρ : ZeroIndex (dirichletXi χ), Continuous fun x : ℝ ↦ 1 / ((x : ℂ) + h * I - ρ.val) := by
    intro ρ
    have hg' : Continuous fun x : ℝ ↦ (x : ℂ) + h * I - ρ.val := by fun_prop
    have h0 : ∀ x : ℝ, (x : ℂ) + h * I - ρ.val ≠ 0 := fun x h' ↦
      hγ ρ (by have := congrArg Complex.im h'; simp at this; linarith)
    exact (hg'.inv₀ h0).congr fun x ↦ (one_div _).symm
  have hgc : Continuous g := continuous_finsetSum _ fun ρ _ ↦ hinv ρ
  -- the remainder bound
  have hR : ∀ x ∈ Set.Ioc (1 / 2 : ℝ) (3 / 2), ‖(f x - g x).im‖ ≤
      B * (Real.log N + Real.log (T + 2)) := by
    intro x hx
    set s : ℂ := x + h * I with hs
    have hsre : s.re = x := by simp [s]
    have hsim : s.im = h := by simp [s]
    have hpar : ∀ m : ℕ, s + dirichletParity χ ≠ -(2 * m) := by
      intro m e
      have := congrArg Complex.im e
      simp [dirichletParity_im, hsim] at this
      rw [this] at hh; simp at hh; linarith
    have hG : Gammaℝ (s + dirichletParity χ) ≠ 0 := by
      rw [Ne, Gammaℝ_eq_zero_iff, not_exists]; exact hpar
    have hL : LFunction χ s ≠ 0 := by
      intro e
      apply hξ x
      rw [dirichletXi_eq_mul_LFunction χ hN hG, e, mul_zero]
    have hxi := logDeriv_dirichletXi_eq hχ hN hpar hL (hξ x)
    have hloc := h₁ hχ hN s (by rw [hsre]; linarith [hx.1]) (by rw [hsre]; linarith [hx.2])
      (by rw [hsim, hh]; exact hT) hL
    have htsum : ∑' ρ : ZeroIndex (dirichletXi χ),
        (if |s.im - ρ.val.im| < 1 then 1 / (s - ρ.val) else 0) = g x := by
      rw [tsum_eq_sum (s := S)]
      · refine Finset.sum_congr rfl fun ρ hρ ↦ ?_
        rw [hS, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hρ
        rw [ite_eq_left_iff.mpr fun e ↦ absurd (by rw [hsim, abs_sub_comm]; exact hρ) e]
      · intro ρ hρ
        rw [hS, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hρ
        exact ite_eq_right_iff.mpr fun e ↦ absurd (by rw [hsim, abs_sub_comm] at e; exact e) hρ
    rw [htsum, hsim, hh] at hloc
    have hfx : f x - g x = (deriv (LFunction χ) s / LFunction χ s - g x) + Complex.log N / 2 -
        Complex.log π / 2 + Complex.digamma ((s + dirichletParity χ) / 2) / 2 := by
      simp only [hf]
      rw [hxi]; ring
    have h1 : ‖Complex.log N / 2‖ ≤ Real.log N := by
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_log (Nat.cast_nonneg N), norm_div,
        Complex.norm_real, Real.norm_of_nonneg hlogN, Complex.norm_ofNat]
      linarith
    have h2 : ‖Complex.log π / 2‖ ≤ 1 := by
      rw [← Complex.ofReal_log Real.pi_pos.le, norm_div, Complex.norm_real, Real.norm_of_nonneg
        (Real.log_nonneg (by linarith [Real.pi_gt_three])), Complex.norm_ofNat]
      have : Real.log π < 2 := by
        rw [Real.log_lt_iff_lt_exp Real.pi_pos]
        have h := Real.exp_one_gt_d9
        have e2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
        have hee : 7 < Real.exp 2 := by rw [e2]; nlinarith
        have := Real.pi_lt_d2
        linarith
      linarith
    have h3 : ‖Complex.digamma ((s + dirichletParity χ) / 2) / 2‖ ≤
        (6 + 4 * Real.log (T + 2)) / 2 := by
      rw [norm_div, Complex.norm_ofNat]
      have := norm_digamma_parity_le χ (z := s) (by rw [hsre]; linarith [hx.1])
        (by rw [hsre]; linarith [hx.2]) (by rw [hsim, hh]; exact hT)
      rw [hsim, hh] at this
      linarith
    calc ‖(f x - g x).im‖ ≤ ‖f x - g x‖ := by
          rw [Real.norm_eq_abs]; exact Complex.abs_im_le_norm _
      _ ≤ ‖deriv (LFunction χ) s / LFunction χ s - g x‖ + ‖Complex.log N / 2‖ +
          ‖Complex.log π / 2‖ + ‖Complex.digamma ((s + dirichletParity χ) / 2) / 2‖ := by
          rw [hfx]
          exact norm_add_sub_add_le _ _ _ _
      _ ≤ A₁ * (Real.log N + Real.log (T + 2)) + Real.log N + 1 +
          (6 + 4 * Real.log (T + 2)) / 2 := by
          linarith [hloc, h1, h2, h3]
      _ ≤ B * (Real.log N + Real.log (T + 2)) := by
          have e : B * (Real.log N + Real.log (T + 2)) =
              A₁ * (Real.log N + Real.log (T + 2)) + 6 * (Real.log N + Real.log (T + 2)) := by
            rw [hB]; ring
          linarith
  -- split the integral
  have i1 : IntervalIntegrable (fun x ↦ (g x).im) volume (1 / 2) (3 / 2) :=
    (Complex.continuous_im.comp hgc).intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun x ↦ (f x - g x).im) volume (1 / 2) (3 / 2) :=
    (Complex.continuous_im.comp (hfc.sub hgc)).intervalIntegrable _ _
  have hsplit : ∫ x in (1 / 2 : ℝ)..3 / 2, (f x).im =
      (∫ x in (1 / 2 : ℝ)..3 / 2, (g x).im) + ∫ x in (1 / 2 : ℝ)..3 / 2, (f x - g x).im := by
    rw [← intervalIntegral.integral_add i1 i2]
    refine intervalIntegral.integral_congr fun x _ ↦ ?_
    simp
  have hgi : |∫ x in (1 / 2 : ℝ)..3 / 2, (g x).im| ≤ π * S.card := by
    have : ∫ x in (1 / 2 : ℝ)..3 / 2, (g x).im =
        ∑ ρ ∈ S, ∫ x in (1 / 2 : ℝ)..3 / 2, (1 / ((x : ℂ) + h * I - ρ.val)).im := by
      rw [← intervalIntegral.integral_finsetSum]
      · refine intervalIntegral.integral_congr fun x _ ↦ ?_
        simp only [hg, Complex.im_sum]
      · intro ρ _
        exact (Complex.continuous_im.comp (hinv ρ)).intervalIntegrable _ _
    rw [this]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ ρ ∈ S, |∫ x in (1 / 2 : ℝ)..3 / 2, (1 / ((x : ℂ) + h * I - ρ.val)).im|
        ≤ ∑ ρ ∈ S, π := Finset.sum_le_sum fun ρ _ ↦ abs_integral_im_inv_sub_le (hγ ρ) _ _
      _ = π * S.card := by rw [Finset.sum_const, nsmul_eq_mul]; ring
  have hri : |∫ x in (1 / 2 : ℝ)..3 / 2, (f x - g x).im| ≤
      B * (Real.log N + Real.log (T + 2)) := by
    rw [← Real.norm_eq_abs]
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 1 / 2) (b := 3 / 2)
      (C := B * (Real.log N + Real.log (T + 2))) (f := fun x ↦ (f x - g x).im) (fun x hx ↦ by
        rw [uIoc_of_le (by norm_num)] at hx; exact hR x hx)
    refine this.trans (le_of_eq ?_)
    norm_num
  rw [show (∫ x in (1 / 2 : ℝ)..3 / 2, (logDeriv (dirichletXi χ) (x + h * I)).im) =
    ∫ x in (1 / 2 : ℝ)..3 / 2, (f x).im from rfl, hsplit]
  have hBpos : 0 ≤ B := by positivity
  calc |(∫ x in (1 / 2 : ℝ)..3 / 2, (g x).im) + ∫ x in (1 / 2 : ℝ)..3 / 2, (f x - g x).im|
      ≤ π * S.card + B * (Real.log N + Real.log (T + 2)) :=
        (abs_add_le _ _).trans (add_le_add hgi hri)
    _ ≤ π * (A₂ * (Real.log N + Real.log (T + 2))) + B * (Real.log N + Real.log (T + 2)) := by
        gcongr
    _ = (π * A₂ + B) * (Real.log N + Real.log (T + 2)) := by ring

/-- The main term `(T/π) log(qT/2π) - T/π` of `N(T, χ)`. -/
noncomputable def LZeroCountMain (q T : ℝ) : ℝ := T / π * Real.log (q * T / (2 * π)) - T / π

/-- `N(T, χ) = (T/π) log(qT/2π) - T/π + O(log q + log T)` for `T ≥ 2` not an ordinate. -/
lemma LZeroCount_sub_le_of_ne :
    ∃ A : ℝ, 0 < A ∧ ∀ {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}, χ.IsPrimitive → N ≠ 1 →
      ∀ T : ℝ, 2 ≤ T → (∀ ρ : ZeroIndex (dirichletXi χ), |ρ.val.im| ≠ T) →
      |(LZeroCount χ T : ℝ) - LZeroCountMain N T| ≤ A * (Real.log N + Real.log T) := by
  obtain ⟨A₁, hA₁, h₁⟩ := Davenport.integral_re_logDeriv_dirichletXi
  obtain ⟨A₂, hA₂, h₂⟩ := Davenport.abs_integral_im_logDeriv_dirichletXi_le
  refine ⟨(A₁ + 4 * A₂) / π, by positivity, fun {N} _ {χ} hχ hN T hT hTz ↦ ?_⟩
  have hT0 : 0 < T := by linarith
  have hπ : 0 < π := Real.pi_pos
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg hN1
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have hlogT2 : Real.log (T + 2) ≤ 2 * Real.log T := by
    rw [← Real.log_rpow hT0]
    exact Real.log_le_log (by linarith) (by norm_num; nlinarith)
  have hid := Davenport.pi_mul_LZeroCount_eq hχ hN hT0 hTz
  have hV := h₁ hχ hN T hT
  have hHp := h₂ hχ hN T hT hTz T (abs_of_pos hT0)
  have hHm := h₂ hχ hN T hT hTz (-T) (by rw [abs_neg, abs_of_pos hT0])
  have e : (∫ x in (1 / 2 : ℝ)..3 / 2, (logDeriv (dirichletXi χ) (x + (-T) * I)).im) =
      ∫ x in (1 / 2 : ℝ)..3 / 2, (logDeriv (dirichletXi χ) (x + ((-T : ℝ) : ℂ) * I)).im := by
    push_cast; rfl
  rw [e] at hid
  set V := ∫ y in (-T)..T, (logDeriv (dirichletXi χ) (3 / 2 + y * I)).re
  set Hm := ∫ x in (1 / 2 : ℝ)..3 / 2, (logDeriv (dirichletXi χ) (x + ((-T : ℝ) : ℂ) * I)).im
  set Hp := ∫ x in (1 / 2 : ℝ)..3 / 2, (logDeriv (dirichletXi χ) (x + (T : ℂ) * I)).im
  have hM : π * LZeroCountMain N T = T * Real.log (N * T / (2 * π)) - T := by
    rw [LZeroCountMain]; field_simp
  have hdiff : (LZeroCount χ T : ℝ) - LZeroCountMain N T =
      ((V - (T * Real.log (N * T / (2 * π)) - T)) + (Hm - Hp)) / π := by
    rw [← hM]; field_simp; linarith [hid]
  rw [hdiff, abs_div, abs_of_pos hπ, div_le_iff₀ hπ]
  have e2 : (A₁ + 4 * A₂) / π * (Real.log N + Real.log T) * π =
      (A₁ + 4 * A₂) * (Real.log N + Real.log T) := by field_simp
  rw [e2]
  have k1 := abs_add_le (V - (T * Real.log (N * T / (2 * π)) - T)) (Hm - Hp)
  have k2 := abs_sub Hm Hp
  have k3 : A₂ * (Real.log N + Real.log (T + 2)) ≤ 2 * A₂ * (Real.log N + Real.log T) := by
    nlinarith
  nlinarith

/-- There is a non-ordinate of the zeros of `L(s, χ)` in every open interval. -/
lemma exists_not_ordinate_L {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (hN : N ≠ 1)
    {a b : ℝ} (hab : a < b) :
    ∃ T ∈ Ioo a b, ∀ ρ : ZeroIndex (dirichletXi χ), |ρ.val.im| ≠ T := by
  classical
  obtain ⟨T, hT, hTn⟩ := (Set.Ioo_infinite hab).exists_notMem_finset
    ((zerosBelowL hχ hN (|b| + 1)).image fun ρ ↦ |ρ.val.im|)
  refine ⟨T, hT, fun ρ hρ ↦ hTn (Finset.mem_image.mpr ⟨ρ, mem_zerosBelowL.mpr ?_, hρ⟩)⟩
  rw [hρ]
  have := le_abs_self b
  linarith [hT.2]

lemma LZeroCount_mono {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (hN : N ≠ 1) {T T' : ℝ}
    (h : T ≤ T') : LZeroCount χ T ≤ LZeroCount χ T' := by
  rw [LZeroCount_eq_card hχ hN, LZeroCount_eq_card hχ hN]
  exact Finset.card_le_card fun ρ hρ ↦ mem_zerosBelowL.mpr ((mem_zerosBelowL.mp hρ).trans_le h)

/-- `|M(q, T') - M(q, T)| ≤ log q + log T + 5` for `2 ≤ T ≤ T' ≤ T + 1`, `q ≥ 1`. -/
lemma abs_LZeroCountMain_sub_le {q T T' : ℝ} (hq : 1 ≤ q) (hT : 2 ≤ T) (h1 : T ≤ T')
    (h2 : T' ≤ T + 1) :
    |LZeroCountMain q T' - LZeroCountMain q T| ≤ Real.log q + Real.log T + 5 := by
  have hπ : 0 < π := Real.pi_pos
  have hq0 : 0 < q := by linarith
  have hT0 : 0 < T := by linarith
  have hT'0 : 0 < T' := by linarith
  have hlq : 0 ≤ Real.log q := Real.log_nonneg hq
  set u := T' - T with hu
  have hu0 : 0 ≤ u := by linarith
  have hu1 : u ≤ 1 := by linarith
  have e : LZeroCountMain q T' - LZeroCountMain q T =
      (u * Real.log (q * T' / (2 * π)) + T * Real.log (T' / T) - u) / π := by
    rw [LZeroCountMain, LZeroCountMain,
      show Real.log (q * T' / (2 * π)) = Real.log (q * T / (2 * π)) + Real.log (T' / T) by
        rw [← Real.log_mul (by positivity) (by positivity)]; congr 1; field_simp]
    field_simp
    ring
  have hl1 : 0 ≤ Real.log (T' / T) := Real.log_nonneg (by rw [le_div_iff₀ hT0]; linarith)
  have hl2 : T * Real.log (T' / T) ≤ u := by
    have := Real.log_le_sub_one_of_pos (show 0 < T' / T by positivity)
    have e2 : T * (T' / T - 1) = u := by field_simp; ring
    nlinarith
  have hl3 : |Real.log (q * T' / (2 * π))| ≤ Real.log q + Real.log T + 3 := by
    have hπ3 := Real.pi_gt_three
    rw [Real.log_div (by positivity) (by positivity), Real.log_mul hq0.ne' hT'0.ne', abs_le]
    have hlT' : Real.log T' ≤ Real.log T + 1 := by
      have := Real.log_le_sub_one_of_pos (show 0 < T' / T by positivity)
      rw [Real.log_div hT'0.ne' hT0.ne'] at this
      have : T' / T - 1 ≤ 1 := by rw [div_sub_one hT0.ne', div_le_one hT0]; linarith
      linarith
    have hl2π : Real.log (2 * π) ≤ 2 := by
      rw [Real.log_le_iff_le_exp (by positivity)]
      have h := Real.exp_one_gt_d9
      have e2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
      have hee : 7 < Real.exp 2 := by rw [e2]; nlinarith
      have := Real.pi_lt_d2
      linarith
    have hl2π' : 0 ≤ Real.log (2 * π) := Real.log_nonneg (by linarith)
    have hlT : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
    have hlT'0 : 0 ≤ Real.log T' := Real.log_nonneg (by linarith)
    constructor <;> linarith
  rw [e, abs_div, abs_of_pos hπ, div_le_iff₀ hπ]
  have hab : |u * Real.log (q * T' / (2 * π)) + T * Real.log (T' / T) - u| ≤
      u * (Real.log q + Real.log T + 3) + u + u := by
    have h3 : |u * Real.log (q * T' / (2 * π))| ≤ u * (Real.log q + Real.log T + 3) := by
      rw [abs_mul, abs_of_nonneg hu0]; exact mul_le_mul_of_nonneg_left hl3 hu0
    rw [abs_le] at h3 ⊢
    constructor <;> nlinarith
  have hlT : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have : u * (Real.log q + Real.log T + 3) + u + u ≤ (Real.log q + Real.log T + 5) * 1 := by
    nlinarith
  nlinarith [Real.pi_gt_three]

/-- **Davenport, Ch. 16, p. 101 (row 16-2)**: there is an absolute `A` such that for `χ`
primitive mod `q > 1` and `T ≥ 3`,
`|N(T, χ) - ((T/π) log(qT/2π) - T/π)| ≤ A log(qT)`, i.e.
`½ N(T, χ) = (T/2π) log(qT/2π) - T/2π + O(log qT)`, where `N(T, χ)` counts the zeros of
`L(s, χ)` in `0 < σ < 1`, `|t| < T` with multiplicity. -/
@[kb "davenport1980" "Ch 16, p. 101"]
theorem Davenport.LZeroCount_sub_le :
    ∃ A : ℝ, 0 < A ∧ ∀ {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}, χ.IsPrimitive → N ≠ 1 →
      ∀ T : ℝ, 3 ≤ T →
      |(LZeroCount χ T : ℝ) - (T / π * Real.log (N * T / (2 * π)) - T / π)| ≤
        A * Real.log (N * T) := by
  obtain ⟨A, hA, h⟩ := LZeroCount_sub_le_of_ne
  have hlog3 : 1 ≤ Real.log 3 := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    have := Real.exp_one_lt_d9; linarith
  refine ⟨2 * A + 6, by positivity, fun {N} _ {χ} hχ hN T hT ↦ ?_⟩
  have hT2 : 2 ≤ T := by linarith
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg hN1
  have hlogT : 1 ≤ Real.log T := hlog3.trans (Real.log_le_log (by norm_num) hT)
  have hlogNT : Real.log (N * T) = Real.log N + Real.log T :=
    Real.log_mul (by positivity) (by positivity)
  obtain ⟨T₁, hT₁, hT₁z⟩ := exists_not_ordinate_L hχ hN (show T < T + 1 by linarith)
  obtain ⟨T₂, hT₂, hT₂z⟩ := exists_not_ordinate_L hχ hN (show T - 1 < T by linarith)
  have hN₁ : (LZeroCount χ T : ℝ) ≤ LZeroCount χ T₁ := by
    exact_mod_cast LZeroCount_mono hχ hN hT₁.1.le
  have hN₂ : (LZeroCount χ T₂ : ℝ) ≤ LZeroCount χ T := by
    exact_mod_cast LZeroCount_mono hχ hN hT₂.2.le
  have e1 := h hχ hN T₁ (by linarith [hT₁.1]) hT₁z
  have e2 := h hχ hN T₂ (by linarith [hT₂.1]) hT₂z
  have m1 := abs_LZeroCountMain_sub_le hN1 hT2 hT₁.1.le hT₁.2.le
  have m2 := abs_LZeroCountMain_sub_le hN1 (show 2 ≤ T₂ by linarith [hT₂.1]) hT₂.2.le
    (by linarith [hT₂.1])
  have hl1 : Real.log T₁ ≤ 2 * Real.log T := by
    rw [← Real.log_rpow (by linarith)]
    exact Real.log_le_log (by linarith [hT₁.1]) (by norm_num; nlinarith [hT₁.2])
  have hl2 : Real.log T₂ ≤ Real.log T := Real.log_le_log (by linarith [hT₂.1]) hT₂.2.le
  have hl2' : 0 ≤ Real.log T₂ := Real.log_nonneg (by linarith [hT₂.1])
  have hl1' : 0 ≤ Real.log T₁ := Real.log_nonneg (by linarith [hT₁.1])
  change |(LZeroCount χ T : ℝ) - LZeroCountMain N T| ≤ _
  rw [hlogNT]
  rw [abs_le] at e1 e2 m1 m2 ⊢
  constructor <;> nlinarith

end NTKB
