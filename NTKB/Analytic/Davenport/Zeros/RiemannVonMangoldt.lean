/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Davenport.Zeros.ZeroCountHoriz

/-!
# The Riemann-von Mangoldt formula

**Davenport, Ch. 15, pp. 97-98 (rows 15-3, 15-5; displayed (1) of Ch. 8):**
`N(T) = (T/2π) log(T/2π) - T/2π + O(log T)`, where `N(T)` is the number of zeros `ρ = β + iγ` of
`ζ` with `0 < β < 1`, `0 < γ < T`, counted with multiplicity
(`Davenport.zetaZeroCount_sub_le`).

The proof follows Davenport: the argument principle on the rectangle `[-1, 2] × [-T, T]`
(`ZeroCountArg`), the symmetry of `ξ` reducing to `2 → 2 + iT → 1/2 + iT`, the vertical side by
Stirling's formula (here in the form `Re ψ(w) = log |w| + O(1/|w|)`, `ZeroCountVertical`), and the
horizontal side `S(T) = O(log T)` by 15-9 (`ZeroCountHoriz`). Davenport's sharper
`7/8 + S(T) + O(1/T)` (15-3) needs Stirling's formula with error `O(1/|s|)` for `log Γ`
itself, which is not formalized; only the `O(log T)` form is proved.
-/

open Filter Topology Complex Set
open scoped Real

namespace NTKB

/-- The main term `(T/2π) log(T/2π) - T/2π`. -/
noncomputable def zetaZeroCountMain (T : ℝ) : ℝ := T / (2 * π) * Real.log (T / (2 * π)) - T / (2 * π)

/-- `N(T) = (T/2π) log(T/2π) - T/2π + O(log T)` for `T ≥ 2` not an ordinate. -/
lemma zetaZeroCount_sub_le_of_ne :
    ∃ A : ℝ, 0 < A ∧ ∀ T : ℝ, 2 ≤ T → (∀ ρ : ZeroIndex riemannXi, |ρ.val.im| ≠ T) →
      |(zetaZeroCount T : ℝ) - zetaZeroCountMain T| ≤ A * Real.log T := by
  obtain ⟨A₁, hA₁, h₁⟩ := Davenport.integral_re_logDeriv_riemannXi_two
  obtain ⟨A₂, hA₂, h₂⟩ := Davenport.abs_integral_im_logDeriv_riemannXi_le
  set N₀ : ℝ := (zetaRealZeroCount : ℝ)
  have hN₀ : 0 ≤ N₀ := Nat.cast_nonneg _
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨(A₁ + A₂) / π + N₀ / (2 * Real.log 2) + 1, by positivity, fun T hT hTz ↦ ?_⟩
  have hT0 : 0 < T := by linarith
  have hlogT : Real.log 2 ≤ Real.log T := Real.log_le_log (by norm_num) hT
  have hid := Davenport.pi_mul_zetaZeroCount_eq hT0 hTz
  have hV := h₁ T hT
  have hJ := h₂ T hT hTz
  set V := ∫ y in (0 : ℝ)..T, (logDeriv riemannXi (2 + y * I)).re
  set J := ∫ x in (1 / 2 : ℝ)..2, (logDeriv riemannXi (x + T * I)).im
  have hπ : 0 < π := Real.pi_pos
  have hM : π * zetaZeroCountMain T = T / 2 * Real.log (T / (2 * π)) - T / 2 := by
    rw [zetaZeroCountMain]; field_simp
  have hdiff : (zetaZeroCount T : ℝ) - zetaZeroCountMain T =
      ((V - (T / 2 * Real.log (T / (2 * π)) - T / 2)) - J) / π - N₀ / 2 := by
    rw [← hM]
    field_simp
    linarith [hid]
  rw [hdiff]
  have hlogpos : 0 ≤ Real.log T := hlog2.le.trans hlogT
  have h1 : |((V - (T / 2 * Real.log (T / (2 * π)) - T / 2)) - J) / π| ≤
      (A₁ + A₂) / π * Real.log T := by
    rw [abs_div, abs_of_pos hπ, div_le_iff₀ hπ]
    have := abs_sub (V - (T / 2 * Real.log (T / (2 * π)) - T / 2)) J
    have e : (A₁ + A₂) / π * Real.log T * π = A₁ * Real.log T + A₂ * Real.log T := by
      field_simp
    rw [e]; linarith
  have h2 : N₀ / 2 ≤ N₀ / (2 * Real.log 2) * Real.log T := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    nlinarith
  calc |((V - (T / 2 * Real.log (T / (2 * π)) - T / 2)) - J) / π - N₀ / 2|
      ≤ |((V - (T / 2 * Real.log (T / (2 * π)) - T / 2)) - J) / π| + |N₀ / 2| := abs_sub _ _
    _ ≤ (A₁ + A₂) / π * Real.log T + N₀ / (2 * Real.log 2) * Real.log T := by
        rw [abs_of_nonneg (show (0 : ℝ) ≤ N₀ / 2 by positivity)]; linarith
    _ ≤ ((A₁ + A₂) / π + N₀ / (2 * Real.log 2) + 1) * Real.log T := by nlinarith

/-- There is a non-ordinate in every open interval. -/
lemma exists_not_ordinate {a b : ℝ} (hab : a < b) :
    ∃ T ∈ Ioo a b, ∀ ρ : ZeroIndex riemannXi, |ρ.val.im| ≠ T := by
  classical
  obtain ⟨T, hT, hTn⟩ := (Set.Ioo_infinite hab).exists_notMem_finset
    ((zerosBelow (|b| + 1)).image fun ρ ↦ |ρ.val.im|)
  refine ⟨T, hT, fun ρ hρ ↦ hTn (Finset.mem_image.mpr ⟨ρ, mem_zerosBelow.mpr ?_, hρ⟩)⟩
  rw [hρ]
  have := le_abs_self b
  linarith [hT.2]

lemma zetaZeroCount_mono {T T' : ℝ} (h : T ≤ T') : zetaZeroCount T ≤ zetaZeroCount T' := by
  classical
  rw [zetaZeroCount_eq_card, zetaZeroCount_eq_card]
  refine Finset.card_le_card fun ρ hρ ↦ ?_
  rw [Finset.mem_filter, mem_zerosBelow] at hρ ⊢
  exact ⟨hρ.1.trans_le h, hρ.2⟩

/-- `|M(T') - M(T)| ≤ log T + 5` for `2 ≤ T ≤ T' ≤ T + 1`. -/
lemma abs_zetaZeroCountMain_sub_le {T T' : ℝ} (hT : 2 ≤ T) (h1 : T ≤ T') (h2 : T' ≤ T + 1) :
    |zetaZeroCountMain T' - zetaZeroCountMain T| ≤ Real.log T + 5 := by
  have hπ : 0 < π := Real.pi_pos
  have hT0 : 0 < T := by linarith
  have hT'0 : 0 < T' := by linarith
  set u := T' - T with hu
  have hu0 : 0 ≤ u := by linarith
  have hu1 : u ≤ 1 := by linarith
  have e : zetaZeroCountMain T' - zetaZeroCountMain T =
      (u * Real.log (T' / (2 * π)) + T * Real.log (T' / T) - u) / (2 * π) := by
    rw [zetaZeroCountMain, zetaZeroCountMain,
      show Real.log (T' / (2 * π)) = Real.log (T / (2 * π)) + Real.log (T' / T) by
        rw [← Real.log_mul (by positivity) (by positivity)]; congr 1; field_simp]
    field_simp
    ring
  have hl1 : 0 ≤ Real.log (T' / T) := Real.log_nonneg (by rw [le_div_iff₀ hT0]; linarith)
  have hl2 : T * Real.log (T' / T) ≤ u := by
    have := Real.log_le_sub_one_of_pos (show 0 < T' / T by positivity)
    have e2 : T * (T' / T - 1) = u := by field_simp; ring
    nlinarith
  have hl3 : |Real.log (T' / (2 * π))| ≤ Real.log T + 3 := by
    have hπ4 := Real.pi_lt_four
    have hπ3 := Real.pi_gt_three
    rw [Real.log_div hT'0.ne' (by positivity), abs_le]
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
  rw [e, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * π), div_le_iff₀ (by positivity)]
  have hab : |u * Real.log (T' / (2 * π)) + T * Real.log (T' / T) - u| ≤
      u * (Real.log T + 3) + u + u := by
    have h3 : |u * Real.log (T' / (2 * π))| ≤ u * (Real.log T + 3) := by
      rw [abs_mul, abs_of_nonneg hu0]; exact mul_le_mul_of_nonneg_left hl3 hu0
    rw [abs_le] at h3 ⊢
    constructor <;> nlinarith
  have hlT : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have : u * (Real.log T + 3) + u + u ≤ (Real.log T + 5) * 1 := by nlinarith
  nlinarith [Real.pi_gt_three]

/-- **The Riemann-von Mangoldt formula** (Davenport, Ch. 15, pp. 97-98, rows 15-3/15-5 in the
form `S(T) = O(log T)`; displayed (1) of Ch. 8, p. 59): for `T ≥ 3`,
`|N(T) - ((T/2π) log(T/2π) - T/2π)| ≤ A log T`, where `N(T)` counts the zeros of `ζ` with
`0 < γ < T` (with multiplicity). -/
@[kb "davenport1980" "Ch 15, p. 98"]
theorem Davenport.zetaZeroCount_sub_le :
    ∃ A : ℝ, 0 < A ∧ ∀ T : ℝ, 3 ≤ T →
      |(zetaZeroCount T : ℝ) - (T / (2 * π) * Real.log (T / (2 * π)) - T / (2 * π))| ≤
        A * Real.log T := by
  obtain ⟨A, hA, h⟩ := zetaZeroCount_sub_le_of_ne
  have hlog3 : 1 ≤ Real.log 3 := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    have := Real.exp_one_lt_d9; linarith
  refine ⟨2 * A + 6, by positivity, fun T hT ↦ ?_⟩
  have hT2 : 2 ≤ T := by linarith
  have hlogT : 1 ≤ Real.log T := hlog3.trans (Real.log_le_log (by norm_num) hT)
  obtain ⟨T₁, hT₁, hT₁z⟩ := exists_not_ordinate (show T < T + 1 by linarith)
  obtain ⟨T₂, hT₂, hT₂z⟩ := exists_not_ordinate (show T - 1 < T by linarith)
  have hN₁ : (zetaZeroCount T : ℝ) ≤ zetaZeroCount T₁ := by
    exact_mod_cast zetaZeroCount_mono hT₁.1.le
  have hN₂ : (zetaZeroCount T₂ : ℝ) ≤ zetaZeroCount T := by
    exact_mod_cast zetaZeroCount_mono hT₂.2.le
  have e1 := h T₁ (by linarith [hT₁.1]) hT₁z
  have e2 := h T₂ (by linarith [hT₂.1]) hT₂z
  have m1 := abs_zetaZeroCountMain_sub_le hT2 hT₁.1.le hT₁.2.le
  have m2 := abs_zetaZeroCountMain_sub_le (show 2 ≤ T₂ by linarith [hT₂.1]) hT₂.2.le
    (by linarith [hT₂.1])
  have hl1 : Real.log T₁ ≤ 2 * Real.log T := by
    rw [← Real.log_rpow (by linarith)]
    exact Real.log_le_log (by linarith [hT₁.1]) (by norm_num; nlinarith [hT₁.2])
  have hl2 : Real.log T₂ ≤ Real.log T := Real.log_le_log (by linarith [hT₂.1]) hT₂.2.le
  have hl2' : 0 ≤ Real.log T₂ := Real.log_nonneg (by linarith [hT₂.1])
  change |(zetaZeroCount T : ℝ) - zetaZeroCountMain T| ≤ _
  rw [abs_le] at e1 e2 m1 m2 ⊢
  constructor <;> nlinarith

end NTKB
