/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.NumberTheory.LSeries.Nonvanishing
import NTKB.Analytic.Apostol.Zeta.LBounds
import NTKB.Analytic.Davenport.Hadamard.Xi

/-!
# The entire function `ξ(s, χ)` and its product (Davenport, Chapter 12, p. 82–83)

For a primitive character `χ` mod `q` (`q > 1`), Davenport sets (Ch. 12, (12))
`ξ(s, χ) = (q/π)^{(s+a)/2} Γ((s+a)/2) L(s, χ)`, `a = 0` or `1` as `χ(-1) = 1` or `-1`;
it is entire, satisfies `ξ(1 - s, χ̄) = (i^a q^{1/2}/τ(χ)) ξ(s, χ)` (13), has order `1`, and
`ξ(s, χ) = e^{A(χ) + B(χ)s} ∏_ρ (1 - s/ρ) e^{s/ρ}` (16).

## Main definitions

* `NTKB.dirichletParity χ`: Davenport's `a` (`0` for even, `1` for odd `χ`).
* `NTKB.dirichletXi χ s = q^{(s+a)/2} Λ(s, χ)` with Mathlib's completed L-function
  `Λ(s, χ) = π^{-(s+a)/2} Γ((s+a)/2) L(s, χ)` (`DirichletCharacter.completedLFunction`).

The bound for `L(s, χ)` on `σ ≥ 1/2` reuses Apostol's Theorems 12.23 and 12.24 (NTKB) with an
absolute constant in place of Davenport's `2q|s|`.
-/

open Complex Filter Topology Asymptotics Bornology HurwitzZeta DirichletCharacter
open scoped ENNReal NNReal Real

namespace NTKB

variable {N : ℕ} [NeZero N]

open scoped Classical in
/-- Davenport's `a`: `0` if `χ(-1) = 1`, `1` if `χ(-1) = -1`. -/
noncomputable def dirichletParity (χ : DirichletCharacter ℂ N) : ℂ := if χ.Even then 0 else 1

omit [NeZero N] in
lemma gammaFactor_eq (χ : DirichletCharacter ℂ N) (s : ℂ) :
    gammaFactor χ s = Gammaℝ (s + dirichletParity χ) := by
  classical
  rcases χ.even_or_odd with h | h
  · rw [h.gammaFactor_def]; simp [dirichletParity, h]
  · rw [h.gammaFactor_def]; simp [dirichletParity, h.not_even]

omit [NeZero N] in
lemma dirichletParity_inv (χ : DirichletCharacter ℂ N) :
    dirichletParity χ⁻¹ = dirichletParity χ := by
  classical
  have : χ⁻¹.Even ↔ χ.Even := by
    simp only [DirichletCharacter.Even, MulChar.inv_apply_eq_inv']
    constructor
    · intro h; simpa using congrArg (·⁻¹) h
    · intro h; simp [h]
  simp only [dirichletParity, this]

omit [NeZero N] in
lemma dirichletParity_re_nonneg (χ : DirichletCharacter ℂ N) : 0 ≤ (dirichletParity χ).re := by
  classical
  unfold dirichletParity; split_ifs <;> simp

omit [NeZero N] in
lemma dirichletParity_re_le_one (χ : DirichletCharacter ℂ N) : (dirichletParity χ).re ≤ 1 := by
  classical
  unfold dirichletParity; split_ifs <;> simp

omit [NeZero N] in
lemma dirichletParity_im (χ : DirichletCharacter ℂ N) : (dirichletParity χ).im = 0 := by
  classical
  unfold dirichletParity; split_ifs <;> simp

/-- **Davenport's `ξ(s, χ)`** (Ch. 12, (12)): `q^{(s+a)/2} Λ(s, χ)`, where Mathlib's completed
L-function is `Λ(s, χ) = π^{-(s+a)/2} Γ((s+a)/2) L(s, χ)` (see `dirichletXi_eq`). -/
noncomputable def dirichletXi (χ : DirichletCharacter ℂ N) (s : ℂ) : ℂ :=
  (N : ℂ) ^ ((s + dirichletParity χ) / 2) * completedLFunction χ s

lemma natCast_ne_zero' : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N

lemma ne_one_of_isPrimitive {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (hN : N ≠ 1) :
    χ ≠ 1 := by
  rintro rfl
  exact hN (by rw [IsPrimitive, conductor_one] at hχ; exact hχ.symm)

/-- `ξ(s, χ)` is entire for a nontrivial character. -/
lemma differentiable_dirichletXi {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) :
    Differentiable ℂ (dirichletXi χ) := by
  have h1 : Differentiable ℂ fun s : ℂ ↦ (N : ℂ) ^ ((s + dirichletParity χ) / 2) := fun s ↦
    ((((differentiableAt_id.add_const _).div_const 2)).const_cpow (Or.inl natCast_ne_zero'))
  exact h1.mul (differentiable_completedLFunction hχ)

/-- `ξ(s, χ) = q^{(s+a)/2} Γℝ(s + a) L(s, χ)` where `Γℝ(s + a) ≠ 0`. -/
lemma dirichletXi_eq_mul_LFunction (χ : DirichletCharacter ℂ N) (hN : N ≠ 1) {s : ℂ}
    (hG : Gammaℝ (s + dirichletParity χ) ≠ 0) :
    dirichletXi χ s =
      (N : ℂ) ^ ((s + dirichletParity χ) / 2) * Gammaℝ (s + dirichletParity χ) * LFunction χ s := by
  rw [dirichletXi, LFunction_eq_completed_div_gammaFactor χ s (Or.inr hN), gammaFactor_eq]
  field_simp

/-- **Davenport, Ch. 12, (12)**: `ξ(s, χ) = (q/π)^{(s+a)/2} Γ((s+a)/2) L(s, χ)`, written as
`q^{(s+a)/2} π^{-(s+a)/2} Γ((s+a)/2) L(s, χ)` (away from the poles of `Γ((s+a)/2)`). -/
@[kb "davenport1980" "Ch 12, p. 82"]
theorem dirichletXi_eq (χ : DirichletCharacter ℂ N) (hN : N ≠ 1) {s : ℂ}
    (hs : ∀ n : ℕ, s + dirichletParity χ ≠ -(2 * n)) :
    dirichletXi χ s = (N : ℂ) ^ ((s + dirichletParity χ) / 2) *
      (π : ℂ) ^ (-(s + dirichletParity χ) / 2) * Complex.Gamma ((s + dirichletParity χ) / 2) *
        LFunction χ s := by
  have hG : Gammaℝ (s + dirichletParity χ) ≠ 0 := by
    rw [Ne, Gammaℝ_eq_zero_iff, not_exists]; exact hs
  rw [dirichletXi_eq_mul_LFunction χ hN hG, Gammaℝ_def]
  ring

/-- **Davenport, Ch. 12, (13) (row 12-13)**, Mathlib's form: for primitive `χ`,
`ξ(1 - s, χ) = ε(χ) ξ(s, χ⁻¹)` with the root number `ε(χ) = τ(χ)/(i^a q^{1/2})` of absolute
value `1` (`DirichletCharacter.norm_rootNumber`); `χ⁻¹ = χ̄`. -/
@[kb "davenport1980" "Ch 12, p. 82"]
theorem dirichletXi_one_sub {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (s : ℂ) :
    dirichletXi χ (1 - s) = rootNumber χ * dirichletXi χ⁻¹ s := by
  rw [dirichletXi, dirichletXi, IsPrimitive.completedLFunction_one_sub hχ, dirichletParity_inv]
  have hN := natCast_ne_zero' (N := N)
  have : (N : ℂ) ^ ((1 - s + dirichletParity χ) / 2) * (N : ℂ) ^ (s - 1 / 2) =
      (N : ℂ) ^ ((s + dirichletParity χ) / 2) := by
    rw [← Complex.cpow_add _ _ hN]; ring_nf
  rw [← this]
  ring

/-- `ξ(0, χ) ≠ 0` for primitive `χ` mod `q > 1` (`ξ(0, χ) = ε(χ) ξ(1, χ̄)` and `L(1, χ̄) ≠ 0`). -/
lemma dirichletXi_zero_ne_zero {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (hN : N ≠ 1) :
    dirichletXi χ 0 ≠ 0 := by
  have h := dirichletXi_one_sub hχ 1
  rw [sub_self] at h
  rw [h]
  have hχ1 : χ⁻¹ ≠ 1 := fun h1 ↦ ne_one_of_isPrimitive hχ hN (inv_eq_one.mp h1)
  have hε : rootNumber χ ≠ 0 := by
    rw [← norm_ne_zero_iff, norm_rootNumber hχ]; norm_num
  refine mul_ne_zero hε ?_
  have hG : Gammaℝ (1 + dirichletParity χ⁻¹) ≠ 0 :=
    Gammaℝ_ne_zero_of_re_pos (by simp; linarith [dirichletParity_re_nonneg χ⁻¹])
  rw [dirichletXi_eq_mul_LFunction χ⁻¹ hN hG]
  refine mul_ne_zero (mul_ne_zero ?_ hG) (LFunction_apply_one_ne_zero hχ1)
  rw [Ne, Complex.cpow_eq_zero_iff]; push Not; intro h; exact absurd h natCast_ne_zero'

/-! ### Growth -/

/-- **Davenport, Ch. 12, (14)** with an absolute constant: there is `C` such that for every
character `χ` mod `q`, `|L(s, χ)| ≤ C q |s|` for `σ ≥ 1/2` and `|s| ≥ 3`. -/
@[kb "davenport1980" "Ch 12, p. 82"]
theorem Davenport.norm_LFunction_le_mul :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
      1 / 2 ≤ s.re → 3 ≤ ‖s‖ → ‖LFunction χ s‖ ≤ C * N * ‖s‖ := by
  obtain ⟨A, hA, hAb⟩ := NTKB.Apostol.apostol_thm_12_24 (δ := 1 / 2) (by norm_num) (by norm_num)
  set E := (riemannZeta ((1 + 1 / 2 : ℝ) : ℂ)).re
  refine ⟨A + 1 + |E|, by positivity, fun N _ χ s hσ hs ↦ ?_⟩
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast NeZero.one_le
  have hs1 : 1 ≤ ‖s‖ := by linarith
  rcases le_or_gt s.re (3 / 2) with h2 | h2
  · -- strip: Apostol 12.24 (`|t| ≥ 1` since `|s| ≥ 3`)
    have ht : 1 ≤ |s.im| := by
      have hn : ‖s‖ ^ 2 = s.re ^ 2 + s.im ^ 2 := by
        rw [← Complex.normSq_add_mul_I s.re s.im, Complex.re_add_im, Complex.sq_norm,
          Complex.normSq_apply]
      have : 9 ≤ s.re ^ 2 + s.im ^ 2 := by rw [← hn]; nlinarith
      have : s.re ^ 2 ≤ 9 / 4 := by nlinarith
      have : 1 ≤ s.im ^ 2 := by linarith
      rw [← abs_one, ← sq_le_sq]; simpa using this
    have h := (hAb N χ s ht).1 (by linarith) (by linarith)
    have hNt : 1 ≤ (N : ℝ) * |s.im| := by nlinarith
    have hle : ((N : ℝ) * |s.im|) ^ (1 / 2 : ℝ) ≤ N * ‖s‖ :=
      (Real.rpow_le_self_of_one_le hNt (by norm_num)).trans
        (mul_le_mul_of_nonneg_left (Complex.abs_im_le_norm s) (by positivity))
    calc ‖LFunction χ s‖ ≤ A * ((N : ℝ) * |s.im|) ^ (1 / 2 : ℝ) := h
      _ ≤ A * (N * ‖s‖) := by gcongr
      _ ≤ (A + 1 + |E|) * N * ‖s‖ := by
          have : 0 ≤ (N : ℝ) * ‖s‖ := by positivity
          nlinarith [abs_nonneg E]
  · -- `σ > 3/2`: absolutely convergent region, via Apostol's decomposition
    have hE : ∀ j : ZMod N, ‖hurwitzZeta (((NTKB.Apostol.zmodRep j : ℝ) / N : ℝ)) s -
        ((((NTKB.Apostol.zmodRep j : ℝ) / N : ℝ)) : ℂ) ^ (-s)‖ ≤ |E| := by
      intro j
      have hpos : (0 : ℝ) < NTKB.Apostol.zmodRep j / N :=
        div_pos (by exact_mod_cast NTKB.Apostol.zmodRep_pos j) (by linarith)
      have hle : (NTKB.Apostol.zmodRep j : ℝ) / N ≤ 1 :=
        (div_le_one (by linarith)).mpr (by exact_mod_cast NTKB.Apostol.zmodRep_le j)
      exact (NTKB.Apostol.apostol_thm_12_23_a hpos hle (δ := 1 / 2) (by norm_num)
        (by linarith)).trans (le_abs_self _)
    have h := NTKB.Apostol.norm_LFunction_le χ s hE
    have hsum : ∑ n ∈ Finset.range N, ((n : ℝ) + 1) ^ (-s.re) ≤ N := by
      calc ∑ n ∈ Finset.range N, ((n : ℝ) + 1) ^ (-s.re) ≤ ∑ n ∈ Finset.range N, (1 : ℝ) :=
            Finset.sum_le_sum fun n _ ↦ Real.rpow_le_one_of_one_le_of_nonpos
              (by linarith [n.cast_nonneg (α := ℝ)]) (by linarith)
        _ = N := by simp
    have hNs : (N : ℝ) ^ (-s.re) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)
    calc ‖LFunction χ s‖ ≤ N + N * (1 * |E|) := by
          refine h.trans (add_le_add hsum ?_)
          gcongr
      _ ≤ (A + 1 + |E|) * N * ‖s‖ := by
          have h1 : (N : ℝ) * (1 + |E|) ≤ (N : ℝ) * (1 + |E|) * ‖s‖ :=
            le_mul_of_one_le_right (by positivity) hs1
          have hA' : 0 ≤ A * N * ‖s‖ := by positivity
          linarith [show (A + 1 + |E|) * N * ‖s‖ = A * N * ‖s‖ + N * (1 + |E|) * ‖s‖ by ring,
            show (N : ℝ) + N * (1 * |E|) = N * (1 + |E|) by ring]

/-- A growth bound of the shape `K B^{|s|} (|s| + 5)^{|s| + 7}` gives `exp(C |s| log |s|)`. -/
lemma exists_exp_bound_of_le {f : ℂ → ℂ} {K B : ℝ} (hK : 0 < K) (hB : 1 ≤ B)
    (h : ∀ s : ℂ, 4 ≤ ‖s‖ → ‖f s‖ ≤ K * B ^ ‖s‖ * (‖s‖ + 5) ^ (‖s‖ + 7)) :
    ∃ C : ℝ, ∀ s : ℂ, 4 ≤ ‖s‖ → ‖f s‖ ≤ Real.exp (C * ‖s‖ * Real.log ‖s‖) := by
  refine ⟨|Real.log K| + Real.log B + 6, fun s hs ↦ (h s hs).trans ?_⟩
  set x := ‖s‖
  have hx0 : 0 < x := by linarith
  have hlogx : 1 ≤ Real.log x := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
  have hlog5 : Real.log (x + 5) ≤ 2 * Real.log x := by
    rw [← Real.log_rpow hx0]
    refine Real.log_le_log (by linarith) ?_
    norm_num
    nlinarith
  have hlogB : 0 ≤ Real.log B := Real.log_nonneg hB
  have hexp : K * B ^ x * (x + 5) ^ (x + 7) =
      Real.exp (Real.log K + x * Real.log B + Real.log (x + 5) * (x + 7)) := by
    rw [Real.exp_add, Real.exp_add, Real.exp_log hK, Real.rpow_def_of_pos (by linarith),
      Real.rpow_def_of_pos (by linarith), mul_comm x]
  rw [hexp]
  refine Real.exp_le_exp.mpr ?_
  have hxl : 1 ≤ x * Real.log x := by nlinarith
  have h1 : Real.log (x + 5) * (x + 7) ≤ 6 * (x * Real.log x) := by
    have hl : 0 ≤ Real.log (x + 5) := Real.log_nonneg (by linarith)
    calc Real.log (x + 5) * (x + 7) ≤ Real.log (x + 5) * (3 * x) := by
          gcongr; linarith
      _ ≤ 2 * Real.log x * (3 * x) := by gcongr
      _ = 6 * (x * Real.log x) := by ring
  have h2 : x * Real.log B ≤ Real.log B * (x * Real.log x) := by
    have : x ≤ x * Real.log x := le_mul_of_one_le_right hx0.le hlogx
    nlinarith
  have h3 : Real.log K ≤ |Real.log K| * (x * Real.log x) :=
    (le_abs_self _).trans (le_mul_of_one_le_right (abs_nonneg _) hxl)
  nlinarith

/-- An entire function with `|f(s)| ≤ exp(C |s| log |s|)` for `|s| ≥ 4` has order at most `1`. -/
lemma entireOrder_le_one_of_exp_bound {f : ℂ → ℂ} {C : ℝ}
    (hC : ∀ s : ℂ, 4 ≤ ‖s‖ → ‖f s‖ ≤ Real.exp (C * ‖s‖ * Real.log ‖s‖)) :
    entireOrder f ≤ 1 := by
  have : entireOrder f ≤ ((1 : ℝ≥0) : ℝ≥0∞) := by
    refine entireOrder_le_of_eventually fun a ha ↦ ?_
    simp only [NNReal.coe_one] at ha
    set ε := (a - 1) / 2
    have hε : 0 < ε := by simp only [ε]; linarith
    have hev : ∀ᶠ r : ℝ in atTop, (|C| / ε) * r ^ (1 + ε) + 0 ≤ r ^ a :=
      eventually_mul_rpow_add_le_rpow (by linarith) (by simp only [ε]; linarith) _ _
    have hev' := (tendsto_norm_cobounded_atTop (E := ℂ)).eventually
      (hev.and (eventually_ge_atTop 4))
    filter_upwards [hev'] with s hs
    obtain ⟨hs1, hs4⟩ := hs
    refine (hC s hs4).trans (Real.exp_le_exp.mpr ?_)
    have hlog : Real.log ‖s‖ ≤ ‖s‖ ^ ε / ε := Real.log_le_rpow_div (norm_nonneg _) hε
    have hlog0 : 0 ≤ Real.log ‖s‖ := Real.log_nonneg (by linarith)
    have hpow : ‖s‖ * ‖s‖ ^ ε = ‖s‖ ^ (1 + ε) := by
      rw [Real.rpow_add (by linarith), Real.rpow_one]
    have hxl : 0 ≤ ‖s‖ * Real.log ‖s‖ := mul_nonneg (norm_nonneg _) hlog0
    calc C * ‖s‖ * Real.log ‖s‖ ≤ |C| * ‖s‖ * Real.log ‖s‖ := by
          rw [mul_assoc, mul_assoc]; exact mul_le_mul_of_nonneg_right (le_abs_self C) hxl
      _ ≤ |C| * ‖s‖ * (‖s‖ ^ ε / ε) := by gcongr
      _ = |C| / ε * ‖s‖ ^ (1 + ε) := by rw [← hpow]; field_simp
      _ ≤ ‖s‖ ^ a := by linarith
  simpa using this

/-- Growth of `ξ(s, χ)` on `σ ≥ 1/2` for any character mod `q > 1`. -/
lemma norm_dirichletXi_le_of_half_le_re (hN : N ≠ 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ (χ : DirichletCharacter ℂ N) (s : ℂ), 1 / 2 ≤ s.re → 3 ≤ ‖s‖ →
      ‖dirichletXi χ s‖ ≤ K * (N : ℝ) ^ ‖s‖ * (‖s‖ + 4) ^ (‖s‖ + 6) := by
  obtain ⟨C, hC, hCb⟩ := Davenport.norm_LFunction_le_mul
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast NeZero.one_le
  refine ⟨20 * C * N, by positivity, fun χ s hσ hs ↦ ?_⟩
  set a := dirichletParity χ
  have ha0 := dirichletParity_re_nonneg χ
  have ha1 := dirichletParity_re_le_one χ
  have hre : (s + a).re = s.re + a.re := by simp
  have hG : Gammaℝ (s + a) ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by rw [hre]; linarith)
  rw [dirichletXi_eq_mul_LFunction χ hN hG, Gammaℝ_def]
  set x := ‖s‖
  have hσx : s.re ≤ x := Complex.re_le_norm s
  have hNpow : ‖(N : ℂ) ^ ((s + a) / 2)‖ ≤ (N : ℝ) ^ x := by
    rw [show (N : ℂ) = ((N : ℝ) : ℂ) by norm_cast,
      Complex.norm_cpow_eq_rpow_re_of_pos (by linarith)]
    refine Real.rpow_le_rpow_of_exponent_le hN1 ?_
    simp; linarith
  have hpi : ‖(π : ℂ) ^ (-(s + a) / 2)‖ ≤ 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    refine Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.pi_gt_three]) ?_
    have : (-(s + a) / 2).re = -(s.re + a.re) / 2 := by simp
    rw [this]; linarith
  have hΓ : ‖Complex.Gamma ((s + a) / 2)‖ ≤ 20 * (x + 4) ^ (x + 5) := by
    have hre2 : ((s + a) / 2).re = (s.re + a.re) / 2 := by simp
    refine (norm_Gamma_le_Gamma_re (by rw [hre2]; linarith)).trans ?_
    rw [hre2]
    refine (Gamma_le_rpow (by linarith)).trans ?_
    gcongr
    exact rpow_le_rpow_of_le_of_le (by linarith) (by linarith) (by linarith) (by linarith)
  have hL := hCb N χ s hσ hs
  have hx4 : (x + 4) ^ (x + 6) = (x + 4) ^ (x + 5) * (x + 4) := by
    rw [show x + 6 = (x + 5) + 1 by ring, Real.rpow_add_one (by linarith)]
  have hx5 : 0 ≤ (x + 4) ^ (x + 5) := by positivity
  have hNx : 0 ≤ (N : ℝ) ^ x := by positivity
  calc ‖(N : ℂ) ^ ((s + a) / 2) * ((π : ℂ) ^ (-(s + a) / 2) * Complex.Gamma ((s + a) / 2)) *
        LFunction χ s‖
      = ‖(N : ℂ) ^ ((s + a) / 2)‖ * (‖(π : ℂ) ^ (-(s + a) / 2)‖ *
          ‖Complex.Gamma ((s + a) / 2)‖) * ‖LFunction χ s‖ := by
        simp only [norm_mul]
    _ ≤ (N : ℝ) ^ x * (1 * (20 * (x + 4) ^ (x + 5))) * (C * N * x) := by gcongr
    _ ≤ 20 * C * N * (N : ℝ) ^ x * (x + 4) ^ (x + 6) := by
        rw [hx4]
        have : x ≤ x + 4 := by linarith
        have hpos : 0 ≤ 20 * C * N * (N : ℝ) ^ x * (x + 4) ^ (x + 5) := by positivity
        nlinarith [mul_le_mul_of_nonneg_left this hpos]

/-- **Davenport, Ch. 12, (15) (row 12-14)**: for primitive `χ` mod `q > 1`,
`|ξ(s, χ)| < exp(C |s| log |s|)` for `|s|` large (here `|s| ≥ 4`; `C` depends on `q`). -/
@[kb "davenport1980" "Ch 12, p. 82"]
theorem Davenport.norm_dirichletXi_le_exp {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive)
    (hN : N ≠ 1) :
    ∃ C : ℝ, ∀ s : ℂ, 4 ≤ ‖s‖ → ‖dirichletXi χ s‖ ≤ Real.exp (C * ‖s‖ * Real.log ‖s‖) := by
  obtain ⟨K, hK, hKb⟩ := norm_dirichletXi_le_of_half_le_re hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast NeZero.one_le
  refine exists_exp_bound_of_le (K := K * N) (B := N) (by positivity) hN1 fun s hs ↦ ?_
  set x := ‖s‖
  rcases le_or_gt (1 / 2) s.re with hσ | hσ
  · refine (hKb χ s hσ (by linarith)).trans ?_
    have : (N : ℝ) ^ x ≤ N * (N : ℝ) ^ x := le_mul_of_one_le_left (by positivity) hN1
    have h45 : (x + 4) ^ (x + 6) ≤ (x + 5) ^ (x + 7) :=
      rpow_le_rpow_of_le_of_le (by linarith) (by linarith) (by linarith) (by linarith)
    calc K * (N : ℝ) ^ x * (x + 4) ^ (x + 6) ≤ K * (N * (N : ℝ) ^ x) * (x + 5) ^ (x + 7) := by
          gcongr
      _ = K * N * (N : ℝ) ^ x * (x + 5) ^ (x + 7) := by ring
  · -- reflect: `ξ(s, χ) = ε(χ) ξ(1 - s, χ⁻¹)`
    have hfe := dirichletXi_one_sub hχ (1 - s)
    rw [sub_sub_cancel] at hfe
    rw [hfe, norm_mul, norm_rootNumber hχ, one_mul]
    have h1 : 1 / 2 ≤ (1 - s).re := by simp; linarith
    have hn1 : ‖1 - s‖ ≤ x + 1 := by simpa [add_comm] using norm_sub_le (1 : ℂ) s
    have hn2 : x - 1 ≤ ‖1 - s‖ := by
      have := norm_sub_norm_le s 1
      rw [norm_sub_rev] at this; simpa using this
    refine (hKb χ⁻¹ (1 - s) h1 (by linarith)).trans ?_
    have hpow1 : (N : ℝ) ^ ‖1 - s‖ ≤ (N : ℝ) ^ (x + 1) :=
      Real.rpow_le_rpow_of_exponent_le hN1 hn1
    have hpow2 : (N : ℝ) ^ (x + 1) = N * (N : ℝ) ^ x := by
      rw [Real.rpow_add_one (by positivity), mul_comm]
    have hpow3 : (‖1 - s‖ + 4) ^ (‖1 - s‖ + 6) ≤ (x + 5) ^ (x + 7) :=
      rpow_le_rpow_of_le_of_le (by linarith [norm_nonneg (1 - s)]) (by linarith)
        (by linarith [norm_nonneg (1 - s)]) (by linarith)
    calc K * (N : ℝ) ^ ‖1 - s‖ * (‖1 - s‖ + 4) ^ (‖1 - s‖ + 6)
        ≤ K * (N * (N : ℝ) ^ x) * (x + 5) ^ (x + 7) := by
          rw [← hpow2]; gcongr
      _ = K * N * (N : ℝ) ^ x * (x + 5) ^ (x + 7) := by ring

/-- **Davenport, Ch. 12, p. 82**: `ξ(s, χ)` has order at most `1`. -/
@[kb "davenport1980" "Ch 12, p. 82"]
theorem Davenport.entireOrder_dirichletXi_le_one {χ : DirichletCharacter ℂ N}
    (hχ : χ.IsPrimitive) (hN : N ≠ 1) : entireOrder (dirichletXi χ) ≤ 1 := by
  obtain ⟨C, hC⟩ := Davenport.norm_dirichletXi_le_exp hχ hN
  exact entireOrder_le_one_of_exp_bound hC

/-- **Davenport, Ch. 12, (16) (row 12-16)**: for primitive `χ` mod `q > 1`,
`ξ(s, χ) = e^{A(χ) + B(χ)s} ∏_ρ (1 - s/ρ) e^{s/ρ}` over the zeros of `ξ(s, χ)` with
multiplicity. -/
@[kb "davenport1980" "Ch 12, p. 82"]
theorem Davenport.dirichletXi_hadamard {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive)
    (hN : N ≠ 1) :
    ∃ A B : ℂ, ∀ s, dirichletXi χ s = Complex.exp (A + B * s) *
      ∏' ρ : ZeroIndex (dirichletXi χ), (1 - s / ρ.val) * Complex.exp (s / ρ.val) :=
  Davenport.hadamard_factorization_order_one
    (differentiable_dirichletXi (ne_one_of_isPrimitive hχ hN)) (dirichletXi_zero_ne_zero hχ hN)
    (Davenport.entireOrder_dirichletXi_le_one hχ hN)

/-- **Davenport, Ch. 12, p. 83 (row 12-16)**: in the product, `e^{A(χ)} = ξ(0, χ)`, which equals
`ε(χ) ξ(1, χ̄) = ε(χ) q^{(1+a)/2} Γℝ(1 + a) L(1, χ̄)`. -/
@[kb "davenport1980" "Ch 12, p. 83"]
theorem Davenport.dirichletXi_hadamard_exp_A {χ : DirichletCharacter ℂ N}
    (hχ : χ.IsPrimitive) (hN : N ≠ 1) {A B : ℂ}
    (h : ∀ s, dirichletXi χ s = Complex.exp (A + B * s) *
      ∏' ρ : ZeroIndex (dirichletXi χ), (1 - s / ρ.val) * Complex.exp (s / ρ.val)) :
    Complex.exp A = dirichletXi χ 0 ∧
      dirichletXi χ 0 = rootNumber χ * (N : ℂ) ^ ((1 + dirichletParity χ) / 2) *
        Gammaℝ (1 + dirichletParity χ) * LFunction χ⁻¹ 1 := by
  constructor
  · have h0 := h 0
    simp only [zero_div, sub_zero, Complex.exp_zero, mul_one, tprod_one, mul_zero,
      add_zero] at h0
    exact h0.symm
  · have hfe := dirichletXi_one_sub hχ 1
    rw [sub_self] at hfe
    have hG : Gammaℝ (1 + dirichletParity χ⁻¹) ≠ 0 :=
      Gammaℝ_ne_zero_of_re_pos (by simp; linarith [dirichletParity_re_nonneg χ⁻¹])
    rw [hfe, dirichletXi_eq_mul_LFunction χ⁻¹ hN hG, dirichletParity_inv]
    ring

/-- `ξ(s, χ) ≠ 0` for `σ ≥ 1`. -/
lemma dirichletXi_ne_zero_of_one_le_re {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) (hN : N ≠ 1)
    {s : ℂ} (hs : 1 ≤ s.re) : dirichletXi χ s ≠ 0 := by
  have hG : Gammaℝ (s + dirichletParity χ) ≠ 0 :=
    Gammaℝ_ne_zero_of_re_pos (by simp; linarith [dirichletParity_re_nonneg χ])
  rw [dirichletXi_eq_mul_LFunction χ hN hG]
  refine mul_ne_zero (mul_ne_zero ?_ hG) (LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) hs)
  rw [Ne, Complex.cpow_eq_zero_iff]; push Not; intro h; exact absurd h natCast_ne_zero'

/-- **Davenport, Ch. 12, p. 82**: the zeros of `ξ(s, χ)` are exactly the zeros of `L(s, χ)` in
the critical strip `0 < σ < 1` (the nontrivial zeros). -/
@[kb "davenport1980" "Ch 12, p. 82"]
theorem dirichletXi_eq_zero_iff {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (hN : N ≠ 1)
    {s : ℂ} : dirichletXi χ s = 0 ↔ LFunction χ s = 0 ∧ 0 < s.re ∧ s.re < 1 := by
  have hχ1 := ne_one_of_isPrimitive hχ hN
  have hχ1' : χ⁻¹ ≠ 1 := fun h1 ↦ hχ1 (inv_eq_one.mp h1)
  have ha0 := dirichletParity_re_nonneg χ
  constructor
  · intro h
    have hlt : s.re < 1 := by
      by_contra hle; exact dirichletXi_ne_zero_of_one_le_re hχ1 hN (not_lt.mp hle) h
    have hgt : 0 < s.re := by
      by_contra hle
      have hfe := dirichletXi_one_sub hχ (1 - s)
      rw [sub_sub_cancel] at hfe
      rw [hfe] at h
      have hε : rootNumber χ ≠ 0 := by
        rw [← norm_ne_zero_iff, norm_rootNumber hχ]; norm_num
      exact dirichletXi_ne_zero_of_one_le_re hχ1' hN (by simp; linarith [not_lt.mp hle])
        ((mul_eq_zero.mp h).resolve_left hε)
    have hG : Gammaℝ (s + dirichletParity χ) ≠ 0 :=
      Gammaℝ_ne_zero_of_re_pos (by simp; linarith)
    rw [dirichletXi_eq_mul_LFunction χ hN hG] at h
    refine ⟨?_, hgt, hlt⟩
    rcases mul_eq_zero.mp h with h | h
    · exfalso
      rcases mul_eq_zero.mp h with h | h
      · rw [Complex.cpow_eq_zero_iff] at h; exact natCast_ne_zero' h.1
      · exact hG h
    · exact h
  · rintro ⟨hz, hgt, -⟩
    have hG : Gammaℝ (s + dirichletParity χ) ≠ 0 :=
      Gammaℝ_ne_zero_of_re_pos (by simp; linarith)
    rw [dirichletXi_eq_mul_LFunction χ hN hG, hz, mul_zero]

/-- Summability facts for the zeros of `ξ(s, χ)`. -/
lemma summable_dirichletXi_zeros {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive)
    (hN : N ≠ 1) :
    (Summable fun ρ : ZeroIndex (dirichletXi χ) ↦ ‖ρ.val‖⁻¹ ^ 2) ∧
      (∀ ρ : ZeroIndex (dirichletXi χ), ρ.val ≠ 0) :=
  summable_of_entireOrder_le_one (differentiable_dirichletXi (ne_one_of_isPrimitive hχ hN))
    (dirichletXi_zero_ne_zero hχ hN) (Davenport.entireOrder_dirichletXi_le_one hχ hN)

/-- **Davenport, Ch. 12, p. 82 (row 12-15, first part)**: the zeros `ρ` of `ξ(s, χ)` are the zeros
of `L(s, χ)` in `0 < σ < 1`, and `∑ |ρ|^{-1-ε}` converges for every `ε > 0`. -/
@[kb "davenport1980" "Ch 12, p. 82"]
theorem Davenport.dirichletXi_zeros {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive)
    (hN : N ≠ 1) :
    (∀ ρ : ZeroIndex (dirichletXi χ), LFunction χ ρ.val = 0 ∧ 0 < ρ.val.re ∧ ρ.val.re < 1) ∧
    (∀ ε : ℝ, 0 < ε → Summable fun ρ : ZeroIndex (dirichletXi χ) ↦ ‖ρ.val‖ ^ (-1 - ε)) := by
  have hd := differentiable_dirichletXi (ne_one_of_isPrimitive hχ hN)
  refine ⟨fun ρ ↦ (dirichletXi_eq_zero_iff hχ hN).mp
    (ZeroIndex.apply_val_eq_zero (hd.analyticAt _)), ?_⟩
  exact (Davenport.entire_order_one_summary hd (dirichletXi_zero_ne_zero hχ hN)
    (Davenport.entireOrder_dirichletXi_le_one hχ hN)).2.1

/-- Logarithmic derivative of an entire function of order at most one from its Hadamard product:
`f'(s)/f(s) = B + ∑_ρ (1/(s - ρ) + 1/ρ)`. -/
theorem logDeriv_eq_of_hadamard {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hf0 : f 0 ≠ 0)
    (hord : entireOrder f ≤ 1) {A B : ℂ}
    (h : ∀ s, f s = Complex.exp (A + B * s) *
      ∏' ρ : ZeroIndex f, (1 - s / ρ.val) * Complex.exp (s / ρ.val))
    {s : ℂ} (hs : f s ≠ 0) :
    logDeriv f s = B + ∑' ρ : ZeroIndex f, (1 / (s - ρ.val) + 1 / ρ.val) := by
  obtain ⟨ha, ha0⟩ := summable_of_entireOrder_le_one hf hf0 hord
  have hfun : f = fun z ↦ Complex.exp (A + B * z) *
      canonicalProductOne (fun ρ : ZeroIndex f ↦ ρ.val) z := funext h
  have := logDeriv_exp_mul_canonicalProductOne ha ha0 A B fun ρ ↦
    ZeroIndex.val_ne_of_ne_zero (hf.analyticAt _) hs
  rw [← hfun] at this
  exact this

/-- **Davenport, Ch. 12, (17) (row 12-17)**: for primitive `χ` mod `q > 1` and `L(s, χ) ≠ 0`
(away from the poles of `Γ((s+a)/2)`),
`L'(s, χ)/L(s, χ) = -½ log(q/π) - ½ Γ'((s+a)/2)/Γ((s+a)/2) + B(χ) + ∑_ρ (1/(s - ρ) + 1/ρ)`. -/
@[kb "davenport1980" "Ch 12, p. 83"]
theorem Davenport.logDeriv_LFunction {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive)
    (hN : N ≠ 1) {A B : ℂ}
    (h : ∀ s, dirichletXi χ s = Complex.exp (A + B * s) *
      ∏' ρ : ZeroIndex (dirichletXi χ), (1 - s / ρ.val) * Complex.exp (s / ρ.val))
    {s : ℂ} (hs : ∀ m : ℕ, s + dirichletParity χ ≠ -(2 * m)) (hL : LFunction χ s ≠ 0) :
    deriv (LFunction χ) s / LFunction χ s =
      B - Complex.log N / 2 + Complex.log π / 2 -
        deriv Complex.Gamma ((s + dirichletParity χ) / 2) /
          (2 * Complex.Gamma ((s + dirichletParity χ) / 2)) +
        ∑' ρ : ZeroIndex (dirichletXi χ), (1 / (s - ρ.val) + 1 / ρ.val) := by
  have hχ1 := ne_one_of_isPrimitive hχ hN
  set a := dirichletParity χ
  have hpole : ∀ m : ℕ, (s + a) / 2 ≠ -m := by
    intro m hm
    exact hs m (by linear_combination 2 * hm)
  have hΓs : Complex.Gamma ((s + a) / 2) ≠ 0 := Complex.Gamma_ne_zero hpole
  have hπ0 : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hπs : (π : ℂ) ^ (-(s + a) / 2) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]; push Not; intro h; exact absurd h hπ0
  have hNs : (N : ℂ) ^ ((s + a) / 2) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]; push Not; intro h; exact absurd h natCast_ne_zero'
  -- derivatives of the factors
  have hdΓ : HasDerivAt (fun w ↦ Complex.Gamma ((w + a) / 2))
      (deriv Complex.Gamma ((s + a) / 2) * (1 / 2)) s := by
    have hin : HasDerivAt (fun w : ℂ ↦ (w + a) / 2) (1 / 2) s := by
      simpa using ((hasDerivAt_id s).add_const a).div_const 2
    exact (Complex.differentiableAt_Gamma _ hpole).hasDerivAt.comp s hin
  have hdπ : HasDerivAt (fun w : ℂ ↦ (π : ℂ) ^ (-(w + a) / 2))
      ((π : ℂ) ^ (-(s + a) / 2) * Complex.log π * (-1 / 2)) s := by
    have hin : HasDerivAt (fun w : ℂ ↦ -(w + a) / 2) (-1 / 2) s := by
      simpa using (((hasDerivAt_id s).add_const a).neg).div_const 2
    exact hin.const_cpow (Or.inl hπ0)
  have hdN : HasDerivAt (fun w : ℂ ↦ (N : ℂ) ^ ((w + a) / 2))
      ((N : ℂ) ^ ((s + a) / 2) * Complex.log N * (1 / 2)) s := by
    have hin : HasDerivAt (fun w : ℂ ↦ (w + a) / 2) (1 / 2) s := by
      simpa using ((hasDerivAt_id s).add_const a).div_const 2
    exact hin.const_cpow (Or.inl natCast_ne_zero')
  have hdL : HasDerivAt (LFunction χ) (deriv (LFunction χ) s) s :=
    (differentiable_LFunction hχ1 s).hasDerivAt
  set g : ℂ → ℂ := fun w ↦ (N : ℂ) ^ ((w + a) / 2) * (π : ℂ) ^ (-(w + a) / 2) *
    Complex.Gamma ((w + a) / 2) * LFunction χ w
  have hdg : HasDerivAt g _ s := ((hdN.mul hdπ).mul hdΓ).mul hdL
  -- `ξ(·, χ) = g` near `s`
  have hev : dirichletXi χ =ᶠ[𝓝 s] g := by
    have hc : ContinuousAt (fun w ↦ Complex.Gamma ((w + a) / 2)) s := hdΓ.continuousAt
    filter_upwards [hc.eventually_ne hΓs] with w hw
    have hG : Gammaℝ (w + a) ≠ 0 := by
      rw [Gammaℝ_def]
      refine mul_ne_zero ?_ hw
      rw [Ne, Complex.cpow_eq_zero_iff]; push Not; intro h; exact absurd h hπ0
    rw [dirichletXi_eq_mul_LFunction χ hN hG, Gammaℝ_def]
    simp only [g]; ring
  have hξs : dirichletXi χ s ≠ 0 := by
    rw [hev.eq_of_nhds]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero hNs hπs) hΓs) hL
  have hlog := logDeriv_eq_of_hadamard
    (differentiable_dirichletXi hχ1) (dirichletXi_zero_ne_zero hχ hN)
    (Davenport.entireOrder_dirichletXi_le_one hχ hN) h hξs
  rw [logDeriv_apply, hev.deriv_eq, hev.eq_of_nhds, hdg.deriv] at hlog
  set T := ∑' ρ : ZeroIndex (dirichletXi χ), (1 / (s - ρ.val) + 1 / ρ.val)
  rw [show B - Complex.log N / 2 + Complex.log π / 2 -
      deriv Complex.Gamma ((s + a) / 2) / (2 * Complex.Gamma ((s + a) / 2)) + T =
      (B + T) - Complex.log N / 2 + Complex.log π / 2 -
      deriv Complex.Gamma ((s + a) / 2) / (2 * Complex.Gamma ((s + a) / 2)) by ring, ← hlog]
  simp only [g, Pi.mul_apply]
  generalize Complex.Gamma ((s + a) / 2) = G at *
  generalize (π : ℂ) ^ (-(s + a) / 2) = P at *
  generalize (N : ℂ) ^ ((s + a) / 2) = M at *
  generalize LFunction χ s = Z at *
  field_simp
  ring

/-! ### Growth on the real axis and the zeros of `L(s, χ)` -/

lemma tsum_inv_add_two_pow_three_le : ∑' n : ℕ, ((n : ℝ) + 2)⁻¹ ^ 3 ≤ 1 / 2 := by
  refine Real.tsum_le_of_sum_range_le (fun n ↦ by positivity) fun K ↦ ?_
  have hterm : ∀ n : ℕ, ((n : ℝ) + 2)⁻¹ ^ 3 ≤
      (-(1 / (2 * (((n + 1 : ℕ) : ℝ) + 1)))) - (-(1 / (2 * ((n : ℝ) + 1)))) := by
    intro n
    push_cast
    have h0 : (0 : ℝ) ≤ n := n.cast_nonneg
    rw [inv_pow, ← one_div]
    rw [div_le_iff₀ (by positivity)]
    field_simp
    nlinarith [sq_nonneg (n : ℝ)]
  calc ∑ n ∈ Finset.range K, ((n : ℝ) + 2)⁻¹ ^ 3
      ≤ ∑ n ∈ Finset.range K, ((-(1 / (2 * (((n + 1 : ℕ) : ℝ) + 1)))) -
          (-(1 / (2 * ((n : ℝ) + 1))))) := Finset.sum_le_sum fun n _ ↦ hterm n
    _ = -(1 / (2 * ((K : ℝ) + 1))) - (-(1 / (2 * (((0 : ℕ) : ℝ) + 1)))) :=
        Finset.sum_range_sub (fun n : ℕ ↦ -(1 / (2 * ((n : ℝ) + 1)))) K
    _ ≤ 1 / 2 := by
        have : 0 ≤ 1 / (2 * ((K : ℝ) + 1)) := by positivity
        simp; linarith

/-- `|L(s, χ)| ≥ 1/2` for `σ ≥ 3`. -/
lemma half_le_norm_LFunction (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 3 ≤ s.re) :
    1 / 2 ≤ ‖LFunction χ s‖ := by
  rw [LFunction_eq_LSeries χ (by linarith), LSeries]
  have hsum := LSeriesSummable_of_one_lt_re χ (s := s) (by linarith)
  have hsum1 : Summable fun n ↦ LSeries.term (fun n ↦ χ n) s (n + 1) :=
    (summable_nat_add_iff 1).mpr hsum
  rw [hsum.tsum_eq_zero_add, hsum1.tsum_eq_zero_add]
  simp only [LSeries.term_zero, zero_add]
  have h1 : LSeries.term (fun n ↦ χ n) s 1 = 1 := by
    simp
  rw [h1]
  have hR : ‖∑' n : ℕ, LSeries.term (fun n ↦ χ n) s (n + 1 + 1)‖ ≤ 1 / 2 := by
    have hg : HasSum (fun n : ℕ ↦ ((n : ℝ) + 2)⁻¹ ^ 3) (∑' n : ℕ, ((n : ℝ) + 2)⁻¹ ^ 3) := by
      refine Summable.hasSum ?_
      have := (Real.summable_nat_pow_inv (p := 3)).mpr (by norm_num)
      have h2 := (summable_nat_add_iff 2).mpr this
      refine h2.congr fun n ↦ ?_
      push_cast; rw [inv_pow]
    refine (tsum_of_norm_bounded hg fun n ↦ ?_).trans tsum_inv_add_two_pow_three_le
    simp only [LSeries.norm_term_eq, Nat.add_one_ne_zero, ↓reduceIte]
    have hpos : (0 : ℝ) < ((n + 1 + 1 : ℕ) : ℝ) := by positivity
    have hχ : ‖χ ((n + 1 + 1 : ℕ) : ZMod N)‖ ≤ 1 := χ.norm_le_one _
    calc ‖χ ((n + 1 + 1 : ℕ) : ZMod N)‖ / ((n + 1 + 1 : ℕ) : ℝ) ^ s.re
        ≤ 1 / ((n + 1 + 1 : ℕ) : ℝ) ^ s.re := by gcongr
      _ ≤ 1 / ((n + 1 + 1 : ℕ) : ℝ) ^ (3 : ℝ) := by
          gcongr
          push_cast; linarith
      _ = ((n : ℝ) + 2)⁻¹ ^ 3 := by
          rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
          push_cast; rw [inv_pow, one_div]; ring_nf
  have := norm_sub_norm_le (1 : ℂ) (-∑' n : ℕ, LSeries.term (fun n ↦ χ n) s (n + 1 + 1))
  rw [sub_neg_eq_add, norm_neg, norm_one] at this
  linarith

/-- On the real axis, `|ξ(2n + 2 - a, χ)| ≥ n! / (2 π^{n+1})` for `n ≥ 1`. -/
lemma norm_dirichletXi_nat_ge (χ : DirichletCharacter ℂ N) (hN : N ≠ 1) {n : ℕ} (hn : 1 ≤ n) :
    (n.factorial : ℝ) / (2 * π ^ (n + 1)) ≤
      ‖dirichletXi χ (2 * n + 2 - dirichletParity χ)‖ := by
  set a := dirichletParity χ
  set s : ℂ := 2 * n + 2 - a
  have hsa : s + a = 2 * n + 2 := by simp only [s]; ring
  have hs2 : (s + a) / 2 = (n : ℂ) + 1 := by rw [hsa]; ring
  have hpole : ∀ m : ℕ, s + a ≠ -(2 * m) := fun m h ↦ by
    rw [hsa] at h
    have := congrArg Complex.re h; simp at this
    linarith [n.cast_nonneg (α := ℝ), m.cast_nonneg (α := ℝ)]
  have hs3 : -(s + a) / 2 = -((n : ℂ) + 1) := by rw [hsa]; ring
  rw [dirichletXi_eq χ hN hpole, hs2, hs3]
  have hsre : 3 ≤ s.re := by
    have : s.re = 2 * n + 2 - a.re := by simp [s]
    rw [this]
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith [dirichletParity_re_le_one χ]
  have hL := half_le_norm_LFunction χ hsre
  have hΓ : Complex.Gamma ((n : ℂ) + 1) = n.factorial := Complex.Gamma_nat_eq_factorial n
  have hpi : ‖(π : ℂ) ^ (-((n : ℂ) + 1))‖ = (π ^ (n + 1))⁻¹ := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    have : (-((n : ℂ) + 1)).re = -((n : ℝ) + 1) := by simp
    rw [this, Real.rpow_neg Real.pi_pos.le]
    norm_cast
  have hN1 : (1 : ℝ) ≤ ‖(N : ℂ) ^ ((n : ℂ) + 1)‖ := by
    rw [show (N : ℂ) ^ ((n : ℂ) + 1) = (N : ℂ) ^ (n + 1 : ℕ) by norm_cast, norm_pow,
      Complex.norm_natCast]
    exact one_le_pow₀ (by exact_mod_cast NeZero.one_le)
  simp only [norm_mul, hΓ, hpi, Complex.norm_natCast]
  have hπ : 0 < π ^ (n + 1) := by positivity
  have hfac : (0 : ℝ) ≤ n.factorial := by positivity
  rw [div_le_iff₀ (by positivity)]
  calc (n.factorial : ℝ) = 1 * (π ^ (n + 1))⁻¹ * n.factorial * (1 / 2) * (2 * π ^ (n + 1)) := by
        field_simp
    _ ≤ ‖(N : ℂ) ^ ((n : ℂ) + 1)‖ * (π ^ (n + 1))⁻¹ * n.factorial * ‖LFunction χ s‖ *
          (2 * π ^ (n + 1)) := by gcongr

/-- **Davenport, Ch. 12, p. 82**: the bound (15) is essentially best possible as `s → +∞`:
`ξ(s, χ)` is not of exponential type. -/
@[kb "davenport1980" "Ch 12, p. 82"]
theorem Davenport.dirichletXi_not_exponential_type (χ : DirichletCharacter ℂ N) (hN : N ≠ 1) :
    ¬ ∃ C R₀ : ℝ, ∀ s : ℂ, R₀ ≤ ‖s‖ → ‖dirichletXi χ s‖ ≤ Real.exp (C * ‖s‖) := by
  rintro ⟨C, R₀, hC⟩
  set D := |C|
  set q : ℝ := π * Real.exp (2 * D)
  set c : ℝ := 2 * π * Real.exp (2 * D)
  have hc : 0 < c := by positivity
  have hlim := FloorSemiring.tendsto_pow_div_factorial_atTop q
  have hev := hlim.eventually (gt_mem_nhds (inv_pos.mpr hc))
  obtain ⟨M, hM⟩ := (hev.and (eventually_ge_atTop (⌈R₀⌉₊ + 1))).exists_forall_of_atTop
  obtain ⟨hlt, hR⟩ := hM M le_rfl
  set a := dirichletParity χ
  set s : ℂ := 2 * M + 2 - a
  have ha_im : a.im = 0 := dirichletParity_im χ
  have ha_re : a.re ≤ 1 := dirichletParity_re_le_one χ
  have hsre : s.re = 2 * M + 2 - a.re := by simp [s]
  have hsim : s.im = 0 := by simp [s, ha_im]
  have hnn : 0 ≤ 2 * (M : ℝ) + 2 - a.re := by
    have := M.cast_nonneg (α := ℝ)
    linarith
  have hsn : ‖s‖ = 2 * M + 2 - a.re := by
    rw [← Complex.re_add_im s, hsim, Complex.ofReal_zero, zero_mul, add_zero, Complex.norm_real,
      Real.norm_eq_abs, hsre, abs_of_nonneg hnn]
  have hM1 : 1 ≤ M := by omega
  have hR₀ : R₀ ≤ ‖s‖ := by
    rw [hsn]
    have := Nat.le_ceil R₀
    have : ((⌈R₀⌉₊ + 1 : ℕ) : ℝ) ≤ M := by exact_mod_cast hR
    push_cast at this
    linarith [dirichletParity_re_le_one χ]
  have hup := hC s hR₀
  have hlow := norm_dirichletXi_nat_ge χ hN hM1
  have hsle : ‖s‖ ≤ 2 * M + 2 := by rw [hsn]; linarith [dirichletParity_re_nonneg χ]
  have hexp : Real.exp (C * ‖s‖) ≤ Real.exp (2 * D) * Real.exp (2 * D) ^ M := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have hCD : C ≤ D := le_abs_self C
    have hD : 0 ≤ D := abs_nonneg C
    have : C * ‖s‖ ≤ D * ‖s‖ := mul_le_mul_of_nonneg_right hCD (norm_nonneg _)
    have : D * ‖s‖ ≤ D * (2 * M + 2) := mul_le_mul_of_nonneg_left hsle hD
    nlinarith
  have hfac : (M.factorial : ℝ) ≤ c * q ^ M := by
    have h := hlow.trans (hup.trans hexp)
    rw [div_le_iff₀ (by positivity)] at h
    calc (M.factorial : ℝ) ≤ Real.exp (2 * D) * Real.exp (2 * D) ^ M * (2 * π ^ (M + 1)) := h
      _ = c * q ^ M := by simp only [c, q]; rw [mul_pow, pow_succ]; ring
  have hpos : (0 : ℝ) < M.factorial := by positivity
  have : c⁻¹ ≤ q ^ M / M.factorial := by
    rw [le_div_iff₀ hpos, inv_mul_le_iff₀ hc]; linarith
  linarith

/-- **Davenport, Ch. 12, p. 82 (row 12-15)**: for primitive `χ` mod `q > 1`, `ξ(s, χ)` has order
exactly `1` and infinitely many zeros `ρ`, the zeros of `L(s, χ)` in `0 < σ < 1`; `∑ |ρ|^{-1-ε}`
converges for every `ε > 0` and `∑ |ρ|⁻¹` diverges. -/
@[kb "davenport1980" "Ch 12, p. 82"]
theorem Davenport.dirichletXi_zeros_infinite {χ : DirichletCharacter ℂ N}
    (hχ : χ.IsPrimitive) (hN : N ≠ 1) :
    entireOrder (dirichletXi χ) = 1 ∧ Infinite (ZeroIndex (dirichletXi χ)) ∧
    (∀ ρ : ZeroIndex (dirichletXi χ), LFunction χ ρ.val = 0 ∧ 0 < ρ.val.re ∧ ρ.val.re < 1) ∧
    (∀ ε : ℝ, 0 < ε → Summable fun ρ : ZeroIndex (dirichletXi χ) ↦ ‖ρ.val‖ ^ (-1 - ε)) ∧
    ¬ Summable fun ρ : ZeroIndex (dirichletXi χ) ↦ ‖ρ.val‖⁻¹ := by
  have hd := differentiable_dirichletXi (ne_one_of_isPrimitive hχ hN)
  have hsum := Davenport.entire_order_one_summary hd (dirichletXi_zero_ne_zero hχ hN)
    (Davenport.entireOrder_dirichletXi_le_one hχ hN)
  have hdiv : ¬ Summable fun ρ : ZeroIndex (dirichletXi χ) ↦ ‖ρ.val‖⁻¹ := fun h ↦ by
    obtain ⟨C, hC⟩ := hsum.2.2 h
    exact Davenport.dirichletXi_not_exponential_type χ hN ⟨C, 1, hC⟩
  refine ⟨?_, ?_, (Davenport.dirichletXi_zeros hχ hN).1, hsum.2.1, hdiv⟩
  · refine le_antisymm (Davenport.entireOrder_dirichletXi_le_one hχ hN) (not_lt.mp fun hlt ↦ ?_)
    obtain ⟨ρ, hρ1, hρ⟩ : ∃ ρ : ℝ≥0, (ρ : ℝ≥0∞) < 1 ∧ entireOrder (dirichletXi χ) ≤ ρ :=
      ⟨(entireOrder (dirichletXi χ)).toNNReal, by
        rwa [ENNReal.coe_toNNReal (ne_top_of_lt hlt)],
        ENNReal.coe_toNNReal (ne_top_of_lt hlt) ▸ le_rfl⟩
    have hρ1' : (ρ : ℝ) < 1 := by exact_mod_cast hρ1
    have hev := eventually_norm_le_exp_of_entireOrder_le hρ (a := 1) hρ1'
    obtain ⟨R₀, hR₀⟩ := (Metric.hasBasis_cobounded_compl_closedBall (0 : ℂ)).eventually_iff.mp
      hev |>.imp fun r hr ↦ hr.2
    refine Davenport.dirichletXi_not_exponential_type χ hN ⟨1, R₀ + 1, fun s hs ↦ ?_⟩
    have : s ∈ (Metric.closedBall (0 : ℂ) R₀)ᶜ := by
      simp only [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le]; linarith
    simpa using hR₀ this
  · by_contra hfin
    rw [not_infinite_iff_finite] at hfin
    exact hdiv Summable.of_finite

end NTKB
