/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Davenport.Zeros.LExplicitPsi

/-!
# The constant `b(χ)`

**Davenport, Ch. 19, p. 118 (row 19-9).** Let `b(χ)` be the constant term of `L'/L(s, χ)` at
`s = 0`: `b(χ) = L'/L(0, χ)` for odd `χ`, and `L'/L(s, χ) = 1/s + b(χ) + O(s)` for even `χ`. Then
`b(χ) = L'/L(2, χ) - ∑_ρ (1/(2 - ρ) + 1/ρ) + κ` with `κ = 1` (odd) or `0` (even), by the
Hadamard formula (17) of Ch. 12 at `s = 0` and `s = 2` (the constant `B(χ)` cancels); hence
`b(χ) = -∑_{|γ|<1} 1/ρ + O(log q)`.
-/

open Filter Topology Complex Set DirichletCharacter
open scoped Real

namespace NTKB

variable {N : ℕ} [NeZero N]

open scoped Classical in
/-- **Davenport's `b(χ)`** (Ch. 19, p. 116): the constant term of `L'/L(s, χ)` at `s = 0`. -/
noncomputable def bChar (χ : DirichletCharacter ℂ N) : ℂ :=
  if dirichletParity χ = 1 then deriv (LFunction χ) 0 / LFunction χ 0 else bEven χ

open scoped Classical in
/-- The residue at `0` is `-(1 - a) log x - b(χ)`. -/
lemma residueZeroL_eq (χ : DirichletCharacter ℂ N) (x : ℝ) :
    residueZeroL χ x = -(if dirichletParity χ = 1 then 0 else (Real.log x : ℂ)) - bChar χ := by
  unfold residueZeroL bChar
  split_ifs <;> ring

/-- `∑_ρ (1/(0 - ρ) + 1/ρ) = 0`. -/
lemma tsum_inv_zero_sub_add_inv {ι : Type*} (a : ι → ℂ) :
    ∑' i, (1 / (0 - a i) + 1 / a i) = 0 := by
  have : ∀ i, 1 / (0 - a i) + 1 / a i = 0 := fun i ↦ by rw [zero_sub, div_neg]; ring
  simp [this]

/-- Odd `χ`: `L'/L(0, χ) = L'/L(2, χ) - ∑_ρ (1/(2 - ρ) + 1/ρ) + 1`. -/
lemma bChar_eq_odd {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (hN : N ≠ 1)
    (ha : dirichletParity χ = 1) :
    bChar χ = deriv (LFunction χ) 2 / LFunction χ 2 -
      ∑' ρ : ZeroIndex (dirichletXi χ), (1 / (2 - ρ.val) + 1 / ρ.val) + 1 := by
  have hχ1 := ne_one_of_isPrimitive hχ hN
  obtain ⟨A, B, hH⟩ := Davenport.dirichletXi_hadamard hχ hN
  have hp0 : ∀ m : ℕ, (0 : ℂ) + dirichletParity χ ≠ -(2 * m) := by
    intro m h; rw [ha] at h; have := congrArg Complex.re h; simp at this
    linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
  have hp2 : ∀ m : ℕ, (2 : ℂ) + dirichletParity χ ≠ -(2 * m) := by
    intro m h; rw [ha] at h; have := congrArg Complex.re h; simp at this
    linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
  have hL0 := LFunction_zero_ne_zero_of_odd hχ hN ha
  have hL2 : LFunction χ 2 ≠ 0 :=
    LFunction_ne_zero_of_one_le_re χ (Or.inl hχ1) (by norm_num)
  have h0 := Davenport.logDeriv_LFunction hχ hN hH hp0 hL0
  have h2 := Davenport.logDeriv_LFunction hχ hN hH hp2 hL2
  rw [tsum_inv_zero_sub_add_inv] at h0
  rw [ha] at h0 h2
  have hd : ∀ w : ℂ, deriv Complex.Gamma w / (2 * Complex.Gamma w) = Complex.digamma w / 2 :=
    fun w ↦ by rw [Complex.digamma_def, logDeriv_apply]; ring
  rw [hd] at h0 h2
  have hψ : Complex.digamma ((2 + 1) / 2) = Complex.digamma ((0 + 1) / 2) + 2 := by
    have hpole : ∀ m : ℕ, ((0 : ℂ) + 1) / 2 ≠ -m := by
      intro m h; have := congrArg Complex.re h; simp at this
      linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
    have := Complex.digamma_apply_add_one _ hpole
    rw [show ((2 : ℂ) + 1) / 2 = (0 + 1) / 2 + 1 by ring, this]
    norm_num
  simp only [bChar, ha, if_true]
  rw [h0, h2, hψ]
  ring

/-- `D(s) = 2 q^{s/2} π^{-s/2} Γ(s/2 + 1)` has `D(0) = 2` and `D'(0) = log q - log π + Γ'(1)`. -/
lemma hasDerivAt_evenDenom :
    HasDerivAt (fun s : ℂ ↦ 2 * (N : ℂ) ^ (s / 2) * (π : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2 + 1))
      (Complex.log N - Complex.log π + deriv Complex.Gamma 1) 0 := by
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h1 : HasDerivAt (fun s : ℂ ↦ s / 2) (1 / 2) 0 := by
    simpa using (hasDerivAt_id (0 : ℂ)).div_const 2
  have h2 : HasDerivAt (fun s : ℂ ↦ -s / 2) (-1 / 2) 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).neg).div_const 2
  have hN' := h1.const_cpow (c := (N : ℂ)) (Or.inl natCast_ne_zero')
  have hπ' := h2.const_cpow (c := (π : ℂ)) (Or.inl hπ)
  have h3 : HasDerivAt (fun s : ℂ ↦ s / 2 + 1) (1 / 2) 0 := h1.add_const 1
  have hΓ1 : DifferentiableAt ℂ Complex.Gamma ((0 : ℂ) / 2 + 1) := by
    apply Complex.differentiableAt_Gamma
    intro m h; have := congrArg Complex.re h; simp at this
    linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
  have hΓ := hΓ1.hasDerivAt.comp (0 : ℂ) h3
  have := (((hasDerivAt_const (0 : ℂ) (2 : ℂ)).mul hN').mul hπ').mul hΓ
  convert this using 1
  · funext s; simp only [Pi.mul_apply, Function.comp_apply]
  · simp only [Pi.mul_apply, Function.comp_apply, zero_div, zero_add, Complex.cpow_zero,
      neg_zero, Complex.Gamma_one, neg_div]
    ring

/-- Even `χ`: `b(χ) = L'/L(2, χ) - ∑_ρ (1/(2 - ρ) + 1/ρ)`. -/
lemma bChar_eq_even {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (hN : N ≠ 1)
    (ha : dirichletParity χ = 0) :
    bChar χ = deriv (LFunction χ) 2 / LFunction χ 2 -
      ∑' ρ : ZeroIndex (dirichletXi χ), (1 / (2 - ρ.val) + 1 / ρ.val) := by
  have hχ1 := ne_one_of_isPrimitive hχ hN
  have ha1 : dirichletParity χ ≠ 1 := by rw [ha]; exact zero_ne_one
  obtain ⟨A, B, hH⟩ := Davenport.dirichletXi_hadamard hχ hN
  -- `logDeriv ξ(0) = B`
  have hξ0 := logDeriv_eq_of_hadamard (differentiable_dirichletXi hχ1)
    (dirichletXi_zero_ne_zero hχ hN) (Davenport.entireOrder_dirichletXi_le_one hχ hN) hH
    (s := 0) (dirichletXi_zero_ne_zero hχ hN)
  rw [tsum_inv_zero_sub_add_inv, add_zero] at hξ0
  -- `ξ = D k` near `0`
  set D : ℂ → ℂ := fun s ↦ 2 * (N : ℂ) ^ (s / 2) * (π : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2 + 1)
  have hD0 : D 0 = 2 := by simp [D]
  have hDd := hasDerivAt_evenDenom (N := N)
  have hk := analyticAt_evenFactor hχ hN (s := 0) (by simp)
  have hk0 : evenFactor χ 0 ≠ 0 := by
    rw [evenFactor_zero]; exact div_ne_zero (dirichletXi_zero_ne_zero hχ hN) two_ne_zero
  have hev : dirichletXi χ =ᶠ[𝓝 0] fun s ↦ D s * evenFactor χ s := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) one_pos] with s hs
    have hd := evenFactor_denom_ne_zero (N := N) (s := s) (by simpa using hs)
    simp only [D, evenFactor]
    rw [mul_div_assoc', eq_div_iff hd]; ring
  have hlog : logDeriv (dirichletXi χ) 0 = logDeriv D 0 + logDeriv (evenFactor χ) 0 := by
    rw [logDeriv_congr_nhds hev |>.eq_of_nhds]
    exact logDeriv_mul 0 (by rw [hD0]; norm_num) hk0 hDd.differentiableAt hk.differentiableAt
  have hlD : logDeriv D 0 = (Complex.log N - Complex.log π + deriv Complex.Gamma 1) / 2 := by
    rw [logDeriv_apply, hDd.deriv, hD0]
  -- Hadamard at `2`
  have hp2 : ∀ m : ℕ, (2 : ℂ) + dirichletParity χ ≠ -(2 * m) := by
    intro m h; rw [ha] at h; have := congrArg Complex.re h; simp at this
    linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
  have hL2 : LFunction χ 2 ≠ 0 :=
    LFunction_ne_zero_of_one_le_re χ (Or.inl hχ1) (by norm_num)
  have h2 := Davenport.logDeriv_LFunction hχ hN hH hp2 hL2
  rw [ha] at h2
  simp only [add_zero, show (2 : ℂ) / 2 = 1 by norm_num, Complex.Gamma_one, mul_one] at h2
  have hb : bChar χ = logDeriv (evenFactor χ) 0 := by
    simp only [bChar, ha1, if_false, bEven, logDeriv_apply]
  rw [hb, h2]
  have := hlog
  rw [hξ0, hlD] at this
  linear_combination -this

/-- `b(χ) = L'/L(2, χ) - ∑_ρ (1/(2 - ρ) + 1/ρ) + κ` with `‖κ‖ ≤ 1`. -/
lemma bChar_eq {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (hN : N ≠ 1) :
    ∃ κ : ℂ, ‖κ‖ ≤ 1 ∧ bChar χ = deriv (LFunction χ) 2 / LFunction χ 2 -
      ∑' ρ : ZeroIndex (dirichletXi χ), (1 / (2 - ρ.val) + 1 / ρ.val) + κ := by
  rcases dirichletParity_eq_zero_or_one χ with ha | ha
  · exact ⟨0, by simp, by rw [bChar_eq_even hχ hN ha, add_zero]⟩
  · exact ⟨1, by simp, bChar_eq_odd hχ hN ha⟩

/-- **Davenport, Ch. 19, p. 118, (row 19-9)**: there is an absolute `A` with
`|b(χ) + ∑_{|γ|<1} 1/ρ| ≤ A (log q + 1)` for primitive `χ` mod `q > 1`. -/
@[kb "davenport1980" "Ch 19, p. 118"]
theorem Davenport.norm_bChar_add_sum_le :
    ∃ A : ℝ, 0 < A ∧ ∀ {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive)
      (hN : N ≠ 1), ‖bChar χ + ∑ ρ ∈ zerosBelowL hχ hN 1, 1 / ρ.val‖ ≤ A * (Real.log N + 1) := by
  classical
  obtain ⟨A₅, hA₅, h₅⟩ := Davenport.sum_L_zeros_inv_one_add_sq_le
  obtain ⟨A₆, hA₆, h₆⟩ := Davenport.card_L_zeros_near_le
  have hC := zetaLogDerivTwo_nonneg
  refine ⟨zetaLogDerivTwo + 1 + A₆ + 4 * A₅, by positivity, ?_⟩
  intro N _ χ hχ hN
  have hl2 : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
  have hlN : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  obtain ⟨κ, hκ, hb⟩ := bChar_eq hχ hN
  set f : ZeroIndex (dirichletXi χ) → ℂ := fun ρ ↦ 1 / (2 - ρ.val) + 1 / ρ.val with hf
  obtain ⟨ha, ha0⟩ := summable_dirichletXi_zeros hχ hN
  have hne2 : ∀ ρ : ZeroIndex (dirichletXi χ), ρ.val ≠ 2 := fun ρ h ↦ by
    have := (dirichletXi_zero_mem hχ hN ρ).2.2; rw [h] at this; norm_num at this
  have hfs : Summable f := summable_inv_sub_add_inv ha ha0 hne2
  set Z := zerosBelowL hχ hN 1
  set f₁ : ZeroIndex (dirichletXi χ) → ℂ := fun ρ ↦ if |ρ.val.im| < 1 then f ρ else 0
  set g : ZeroIndex (dirichletXi χ) → ℂ := fun ρ ↦ if |ρ.val.im| < 1 then 0 else f ρ
  have hf₁ : ∑' ρ, f₁ ρ = ∑ ρ ∈ Z, f ρ := by
    rw [tsum_eq_sum (s := Z) fun ρ hρ ↦ by
      simp only [f₁, Z, mem_zerosBelowL] at hρ ⊢; simp [hρ]]
    refine Finset.sum_congr rfl fun ρ hρ ↦ ?_
    simp only [f₁, Z, mem_zerosBelowL] at hρ ⊢; simp [hρ]
  have hs₁ : Summable f₁ := summable_of_ne_finset_zero (s := Z) fun ρ hρ ↦ by
    simp only [f₁, Z, mem_zerosBelowL] at hρ ⊢; simp [hρ]
  have hgs : Summable g := (hfs.sub hs₁).congr fun ρ ↦ by
    simp only [f₁, g]; split_ifs <;> ring
  have hsplit : ∑' ρ, f ρ = ∑ ρ ∈ Z, f ρ + ∑' ρ, g ρ := by
    rw [← hf₁, ← hs₁.tsum_add hgs]
    exact tsum_congr fun ρ ↦ by simp only [f₁, g]; split_ifs <;> ring
  -- the identity
  have hid : bChar χ + ∑ ρ ∈ Z, 1 / ρ.val = deriv (LFunction χ) 2 / LFunction χ 2 + κ -
      ∑ ρ ∈ Z, 1 / (2 - ρ.val) - ∑' ρ, g ρ := by
    rw [hb, hsplit]
    simp only [f, Finset.sum_add_distrib]
    ring
  rw [hid]
  -- bounds
  have b0 : ‖deriv (LFunction χ) 2 / LFunction χ 2‖ ≤ zetaLogDerivTwo := by
    have := norm_logDeriv_LFunction_two_add χ 0
    simpa using this
  obtain ⟨hfin, hcard⟩ := h₆ hχ hN 0
  have hZ : Z = hfin.toFinset := by
    ext ρ; simp [Z, mem_zerosBelowL]
  have b1 : ‖∑ ρ ∈ Z, 1 / (2 - ρ.val)‖ ≤ A₆ * (Real.log N + 1) := by
    refine (norm_sum_le _ _).trans ?_
    have h1 : ∀ ρ ∈ Z, ‖1 / (2 - ρ.val)‖ ≤ 1 := by
      intro ρ _
      have hβ := (dirichletXi_zero_mem hχ hN ρ).2.2
      rw [norm_div, norm_one, div_le_one (by
        have := Complex.re_le_norm (2 - ρ.val); simp at this; linarith)]
      have := Complex.re_le_norm (2 - ρ.val); simp at this; linarith
    calc ∑ ρ ∈ Z, ‖1 / (2 - ρ.val)‖ ≤ ∑ ρ ∈ Z, (1 : ℝ) := Finset.sum_le_sum h1
      _ = Z.card := by simp
      _ ≤ A₆ * (Real.log N + Real.log (|0| + 2)) := by
          rw [hZ, ← Set.ncard_eq_toFinset_card _ hfin]; exact hcard
      _ ≤ A₆ * (Real.log N + 1) := by gcongr; simp; linarith
  obtain ⟨hS5, hle5⟩ := h₅ hχ hN 0
  have b2 : ‖∑' ρ, g ρ‖ ≤ 4 * A₅ * (Real.log N + 1) := by
    have hgb : ∀ ρ, ‖g ρ‖ ≤ 4 * (1 / (1 + (0 - ρ.val.im) ^ 2)) := by
      intro ρ
      simp only [g]
      split_ifs with hρ
      · simp; positivity
      · push Not at hρ
        have hβ := dirichletXi_zero_mem hχ hN ρ
        have hρ0 : ρ.val ≠ 0 := ha0 ρ
        have h2ρ : 2 - ρ.val ≠ 0 := sub_ne_zero.mpr (hne2 ρ).symm
        have e : f ρ = 2 / (ρ.val * (2 - ρ.val)) := by
          simp only [f]; field_simp; ring
        rw [e, norm_div, norm_mul]
        have n1 : |ρ.val.im| ≤ ‖ρ.val‖ := Complex.abs_im_le_norm _
        have n2 : |ρ.val.im| ≤ ‖2 - ρ.val‖ := by
          have := Complex.abs_im_le_norm (2 - ρ.val); simpa using this
        have hγ2 : 1 ≤ ρ.val.im ^ 2 := by nlinarith [sq_abs ρ.val.im]
        rw [Complex.norm_two, div_le_iff₀ (by positivity)]
        have hp : ρ.val.im ^ 2 ≤ ‖ρ.val‖ * ‖2 - ρ.val‖ := by
          rw [← sq_abs]; nlinarith [abs_nonneg ρ.val.im]
        have : (0 - ρ.val.im) ^ 2 = ρ.val.im ^ 2 := by ring
        rw [this]
        rw [mul_one_div, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
        nlinarith
    refine (tsum_of_norm_bounded (hS5.mul_left 4).hasSum hgb).trans ?_
    rw [tsum_mul_left, mul_assoc]
    gcongr
    refine hle5.trans ?_
    gcongr; simp; linarith
  calc ‖deriv (LFunction χ) 2 / LFunction χ 2 + κ - ∑ ρ ∈ Z, 1 / (2 - ρ.val) - ∑' ρ, g ρ‖
      ≤ ‖deriv (LFunction χ) 2 / LFunction χ 2‖ + ‖κ‖ + ‖∑ ρ ∈ Z, 1 / (2 - ρ.val)‖ +
          ‖∑' ρ, g ρ‖ :=
        (norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans
          (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)
    _ ≤ zetaLogDerivTwo + 1 + A₆ * (Real.log N + 1) + 4 * A₅ * (Real.log N + 1) := by
        gcongr
    _ ≤ (zetaLogDerivTwo + 1 + A₆ + 4 * A₅) * (Real.log N + 1) := by
        nlinarith

/-- **Davenport, Ch. 19, p. 118, (9) (row 19-10)**, integer form: for primitive `χ` mod `q > 1`,
integers `N ≥ 3`, `T ≥ 2`, `ℓ = log q + log N + log T`,
`|ψ₀(N, χ) - (∑_{|γ|<1} 1/ρ - ∑_{|γ|<T} N^ρ/ρ)| ≤ A (N ℓ²/T + T ℓ N^{-1/2} + ℓ)`. -/
@[kb "davenport1980" "Ch 19, p. 118"]
theorem Davenport.explicit_formula_psi0L' :
    ∃ A : ℝ, 0 < A ∧ ∀ {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
      (hq : q ≠ 1), ∀ N : ℕ, 3 ≤ N → ∀ T : ℝ, 2 ≤ T →
      ‖psi0L χ N - (∑ ρ ∈ zerosBelowL hχ hq 1, 1 / ρ.val -
          ∑ ρ ∈ zerosBelowL hχ hq T, perronKernel N ρ.val)‖ ≤
        A * (N * (Real.log q + Real.log N + Real.log T) ^ 2 / T +
          T * (Real.log q + Real.log N + Real.log T) * (N : ℝ) ^ (-1 / 2 : ℝ) +
          (Real.log q + Real.log N + Real.log T)) := by
  obtain ⟨A₁, hA₁, h₁⟩ := Davenport.explicit_formula_psi0L
  obtain ⟨A₂, hA₂, h₂⟩ := Davenport.norm_bChar_add_sum_le
  refine ⟨A₁ + 2 * A₂ + 2, by positivity, ?_⟩
  intro q _ χ hχ hq N hN T hT
  have e1 := h₁ hχ hq N hN T hT
  have e2 := h₂ hχ hq
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlN : 1 < Real.log N := by
    rw [Real.lt_log_iff_exp_lt hN0]
    have := Real.exp_one_lt_d9
    have : (3 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hlq : 0 ≤ Real.log q := Real.log_natCast_nonneg q
  have hlT : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  set ℓ := Real.log q + Real.log N + Real.log T
  set M := ∑ ρ ∈ zerosBelowL hχ hq T, perronKernel N ρ.val
  set S := ∑ ρ ∈ zerosBelowL hχ hq 1, 1 / ρ.val
  have hsplit : psi0L χ N - (S - M) = (psi0L χ N - (residueZeroL χ N - M)) +
      (residueZeroL χ N + bChar χ) - (bChar χ + S) := by ring
  rw [hsplit]
  have hr : ‖residueZeroL χ N + bChar χ‖ ≤ Real.log N := by
    rw [residueZeroL_eq]
    split_ifs
    · simp; linarith
    · simp only [sub_add_cancel, norm_neg, Complex.norm_real, Real.norm_eq_abs]
      rw [abs_of_pos (by linarith)]
  have hP : 0 ≤ (N : ℝ) * ℓ ^ 2 / T + T * ℓ * (N : ℝ) ^ (-1 / 2 : ℝ) := by positivity
  calc ‖psi0L χ N - (residueZeroL χ N - M) + (residueZeroL χ N + bChar χ) - (bChar χ + S)‖
      ≤ ‖psi0L χ N - (residueZeroL χ N - M)‖ + ‖residueZeroL χ N + bChar χ‖ + ‖bChar χ + S‖ :=
        (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ A₁ * ((N : ℝ) * ℓ ^ 2 / T + T * ℓ * (N : ℝ) ^ (-1 / 2 : ℝ)) + Real.log N +
          A₂ * (Real.log q + 1) := by
        gcongr
    _ ≤ (A₁ + 2 * A₂ + 2) * ((N : ℝ) * ℓ ^ 2 / T + T * ℓ * (N : ℝ) ^ (-1 / 2 : ℝ) + ℓ) := by
        have h1 : Real.log N ≤ ℓ := by simp only [ℓ]; linarith
        have h2 : Real.log q + 1 ≤ 2 * ℓ := by simp only [ℓ]; linarith
        have h3 : A₂ * (Real.log q + 1) ≤ A₂ * (2 * ℓ) := by gcongr
        have hℓ : 0 ≤ ℓ := by simp only [ℓ]; linarith
        nlinarith

end NTKB
