/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Davenport.Zeros.LPartialFraction
import NTKB.Analytic.Davenport.Zeros.ZetaZeroFree

/-!
# Zero-free region for `L(s, χ)`, `χ` complex

**Davenport, Ch. 14, pp. 88-90.** With `𝔏 = log q + log(|t| + 2)`: there is an absolute
constant `c > 0` such that for every complex character `χ` (that is, `χ² ≠ χ₀`) modulo `q`,
every zero `β + iγ` of `L(s, χ)` has `β ≤ 1 - c/(log q + log(|γ| + 2))` (Davenport's (D), (E)).
First for primitive `χ` (row 14-7), then for all complex `χ` (row 14-8): the extra zeros of an
imprimitive `L(s, χ)` lie on `σ = 0`.

Our constants: `δ = 1/102`, `c = 1/714`.
-/

open Filter Topology Complex Set DirichletCharacter
open scoped Real

namespace NTKB

variable {N : ℕ} [NeZero N]

lemma re_sub_le_norm (a b : ℂ) : a.re - b.re ≤ ‖a - b‖ := by
  rw [← Complex.sub_re]; exact Complex.re_le_norm _

/-- The principal character against `ζ`: `-Re L'/L(s, χ₀) ≤ -Re ζ'/ζ(s) + log q` for `σ > 1`. -/
lemma neg_re_logDeriv_one_le {s : ℂ} (hs : 1 < s.re) :
    -(deriv (LFunction (1 : DirichletCharacter ℂ N)) s /
        LFunction (1 : DirichletCharacter ℂ N) s).re ≤
      -(deriv riemannZeta s / riemannZeta s).re + Real.log N := by
  have h := Davenport.norm_logDeriv_LFunction_changeLevel_sub_le (one_dvd N)
    (1 : DirichletCharacter ℂ 1) hs
  rw [changeLevel_one] at h
  have hz : LFunction (1 : DirichletCharacter ℂ 1) = riemannZeta := by
    exact LFunction_modOne_eq
  rw [hz] at h
  have := re_sub_le_norm (deriv riemannZeta s / riemannZeta s)
    (deriv (LFunction (1 : DirichletCharacter ℂ N)) s / LFunction (1 : DirichletCharacter ℂ N) s)
  rw [norm_sub_rev] at this
  linarith

/-- The principal character: `-L'/L(σ, χ₀) ≤ 1/(σ - 1) + 5 log 2 + log q` for `1 < σ ≤ 2`. -/
lemma neg_logDeriv_one_real_le {σ : ℝ} (h1 : 1 < σ) (h2 : σ ≤ 2) :
    -(deriv (LFunction (1 : DirichletCharacter ℂ N)) σ /
        LFunction (1 : DirichletCharacter ℂ N) σ).re ≤
      1 / (σ - 1) + 5 * Real.log 2 + Real.log N := by
  have := neg_re_logDeriv_one_le (N := N) (s := σ) (by simpa using h1)
  have := Davenport.neg_logDeriv_riemannZeta_real_le h1 h2
  linarith

lemma conductor_ne_one_of_ne_one {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) : χ.conductor ≠ 1 :=
  fun h ↦ hχ ((eq_one_iff_conductor_eq_one).mpr h)

/-- A nonprincipal character, primitive or not: for `1 < σ ≤ 2`,
`-Re L'/L(s, χ) ≤ 7 (log q + log(|t| + 2))`. -/
lemma neg_re_logDeriv_LFunction_le_of_ne_one {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) {s : ℂ}
    (h1 : 1 < s.re) (h2 : s.re ≤ 2) :
    -(deriv (LFunction χ) s / LFunction χ s).re ≤ 7 * (Real.log N + Real.log (|s.im| + 2)) := by
  have : NeZero χ.conductor := ⟨conductor_ne_zero χ⟩
  have hM1 := conductor_ne_one_of_ne_one hχ
  have hprim := primitiveCharacter_isPrimitive χ
  have hb := Davenport.neg_re_logDeriv_LFunction_le hprim hM1 h1 h2
  have hn := tsum_re_inv_sub_dirichletXi_nonneg hprim hM1 h1.le
  have hc := Davenport.norm_logDeriv_LFunction_changeLevel_sub_le (conductor_dvd_level χ)
    χ.primitiveCharacter h1
  rw [changeLevel_primitiveCharacter] at hc
  have := re_sub_le_norm (deriv (LFunction χ.primitiveCharacter) s / LFunction χ.primitiveCharacter s)
    (deriv (LFunction χ) s / LFunction χ s)
  rw [norm_sub_rev] at this
  have hMN : Real.log χ.conductor ≤ Real.log N :=
    Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero (conductor_ne_zero χ))
      (by exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne N)) (conductor_dvd_level χ))
  have hl2 : 0 ≤ Real.log (|s.im| + 2) := Real.log_nonneg (by linarith [abs_nonneg s.im])
  have hlN : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  linarith

/-- The term of one zero: for primitive `χ` mod `q > 1`, a zero `ρ = β + iγ` and `1 < σ ≤ 2`,
`-Re L'/L(σ + iγ, χ) ≤ 6 (log q + log(|γ| + 2)) - 1/(σ - β)`. -/
lemma neg_re_logDeriv_LFunction_le_zero {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive)
    (hN : N ≠ 1) (ρ : ZeroIndex (dirichletXi χ)) {σ : ℝ} (h1 : 1 < σ) (h2 : σ ≤ 2) :
    -(deriv (LFunction χ) (σ + ρ.val.im * I) / LFunction χ (σ + ρ.val.im * I)).re ≤
      6 * (Real.log N + Real.log (|ρ.val.im| + 2)) - 1 / (σ - ρ.val.re) := by
  set s : ℂ := σ + ρ.val.im * I
  have hsre : s.re = σ := by simp [s]
  have hsim : s.im = ρ.val.im := by simp [s]
  have h := Davenport.neg_re_logDeriv_LFunction_le hχ hN (s := s) (by rw [hsre]; exact h1)
    (by rw [hsre]; exact h2)
  have hsum := summable_re_inv_sub_dirichletXi_zeros hχ hN (s := s) fun ρ' h ↦ by
    have := congrArg Complex.re h
    rw [hsre] at this
    linarith [(dirichletXi_zero_mem hχ hN ρ').2.2]
  have hle : (1 / (s - ρ.val)).re ≤ ∑' ρ' : ZeroIndex (dirichletXi χ), (1 / (s - ρ'.val)).re :=
    hsum.le_tsum ρ fun ρ' _ ↦
      (re_one_div_sub_pos (by rw [hsre]; linarith [(dirichletXi_zero_mem hχ hN ρ').2.2])).le
  have heq : (1 / (s - ρ.val)).re = 1 / (σ - ρ.val.re) := by
    have : s - ρ.val = ((σ - ρ.val.re : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [s]
    rw [this, ← Complex.ofReal_one, ← Complex.ofReal_div, Complex.ofReal_re]
  rw [hsim] at h
  linarith

/-- **Davenport, Ch. 14, p. 90, (D) (row 14-7)**: for a complex primitive character `χ`
mod `q` (`χ² ≠ χ₀`), every zero `β + iγ` of `L(s, χ)` has
`β ≤ 1 - c/(log q + log(|γ| + 2))`, with the absolute constant `c = 1/714`. -/
@[kb "davenport1980" "Ch 14, p. 90"]
theorem Davenport.LFunction_zero_free_complex_primitive {χ : DirichletCharacter ℂ N}
    (hχ : χ.IsPrimitive) (hχ2 : χ ^ 2 ≠ 1) {s : ℂ} (hs : LFunction χ s = 0) :
    s.re ≤ 1 - 1 / 714 / (Real.log N + Real.log (|s.im| + 2)) := by
  have hN : N ≠ 1 := by
    rintro rfl
    exact hχ2 (Subsingleton.elim _ _)
  have hN2 : (2 : ℝ) ≤ N := by
    have := NeZero.ne N
    exact_mod_cast (show 2 ≤ N by omega)
  have hl2 := log_two_gt_two_thirds
  obtain ⟨L, hLdef⟩ : ∃ L, L = Real.log N + Real.log (|s.im| + 2) := ⟨_, rfl⟩
  rw [← hLdef]
  have hlN : Real.log 2 ≤ Real.log N := Real.log_le_log two_pos hN2
  have hlT : Real.log 2 ≤ Real.log (|s.im| + 2) :=
    Real.log_le_log two_pos (by linarith [abs_nonneg s.im])
  have hL : 4 / 3 < L := by linarith
  rcases le_or_gt s.re 0 with h0 | h0
  · have : 1 / 714 / L ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    linarith
  obtain ⟨ρ, rfl⟩ := exists_zeroIndex_dirichletXi hχ hN hs h0
  have hβ := dirichletXi_zero_mem hχ hN ρ
  obtain ⟨σ, hσ⟩ : ∃ σ : ℝ, σ = 1 + 1 / 102 / L := ⟨_, rfl⟩
  have hσ1 : 1 < σ := by
    rw [hσ]; have : 0 < 1 / 102 / L := by have : 0 < L := by linarith
                                          positivity
    linarith
  have hσ2 : σ ≤ 2 := by
    rw [hσ]
    have : 1 / 102 / L ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    linarith
  have hχ1 : χ ≠ 1 := fun h ↦ hχ2 (by rw [h, one_pow])
  -- the three estimates
  have e1 := neg_logDeriv_one_real_le (N := N) hσ1 hσ2
  have e2 := neg_re_logDeriv_LFunction_le_zero hχ hN ρ hσ1 hσ2
  have e3 := neg_re_logDeriv_LFunction_le_of_ne_one hχ2 (s := σ + (2 * ρ.val.im : ℝ) * I)
    (by simpa using hσ1) (by simpa using hσ2)
  have key := Davenport.three_four_one_LFunction χ hσ1 ρ.val.im
  simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero, zero_add,
    add_zero] at e3
  have hlog2T : Real.log (|2 * ρ.val.im| + 2) ≤ 2 * Real.log (|ρ.val.im| + 2) := by
    rw [show (2 : ℝ) * Real.log (|ρ.val.im| + 2) = ((2 : ℕ) : ℝ) * Real.log (|ρ.val.im| + 2) by
      norm_num, ← Real.log_pow, abs_mul, abs_two]
    have := abs_nonneg ρ.val.im
    exact Real.log_le_log (by linarith) (by nlinarith)
  have hσm1 : 1 / (σ - 1) = 102 * L := by
    rw [hσ]; have : L ≠ 0 := by linarith
    field_simp; ring
  have hu : 0 < σ - ρ.val.re := by linarith [hβ.2.2]
  have hneg : ∀ (ψ : DirichletCharacter ℂ N) (z : ℂ), (-deriv (LFunction ψ) z / LFunction ψ z).re =
      -(deriv (LFunction ψ) z / LFunction ψ z).re := fun ψ z ↦ by rw [neg_div, Complex.neg_re]
  rw [hneg, hneg, hneg] at key
  have hcomb : 4 * (1 / (σ - ρ.val.re)) ≤ 357 * L := by nlinarith
  have hLu : 4 / 357 ≤ L * (σ - ρ.val.re) := by
    rw [mul_one_div, div_le_iff₀ hu] at hcomb
    nlinarith
  have hLσ : L * σ = L + 1 / 102 := by
    rw [hσ]; have : L ≠ 0 := by linarith
    field_simp
  have hL0 : 0 < L := by linarith
  rw [show 1 / 714 / L = 1 / (714 * L) by ring, le_sub_iff_add_le, ← le_sub_iff_add_le',
    div_le_iff₀ (by positivity)]
  nlinarith

/-- For `σ > 0` the Euler factors `1 - χ₁(p) p^{-s}` do not vanish. -/
lemma euler_factor_ne_zero_of_re_pos {p : ℕ} (hp : p.Prime) {c : ℂ} (hc : ‖c‖ ≤ 1) {s : ℂ}
    (hs : 0 < s.re) : 1 - c * (p : ℂ) ^ (-s) ≠ 0 := by
  intro h
  have h1 : c * (p : ℂ) ^ (-s) = 1 := by linear_combination -h
  have h2 : ‖c * (p : ℂ) ^ (-s)‖ < 1 := by
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos hp.pos]
    have : (p : ℝ) ^ (-s).re < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (by simp; linarith)
    calc ‖c‖ * (p : ℝ) ^ (-s).re ≤ 1 * (p : ℝ) ^ (-s).re := by gcongr
      _ < 1 := by linarith
  rw [h1, norm_one] at h2
  exact lt_irrefl _ h2

/-- For `σ > 0`, a zero of `L(s, χ)` is a zero of `L(s, χ₁)`, `χ₁` the primitive character
inducing `χ` (Davenport, Ch. 5, (C)). -/
lemma LFunction_primitiveCharacter_eq_zero {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) {s : ℂ}
    (hs : LFunction χ s = 0) (h0 : 0 < s.re) :
    have : NeZero χ.conductor := ⟨conductor_ne_zero χ⟩
    LFunction χ.primitiveCharacter s = 0 := by
  have : NeZero χ.conductor := ⟨conductor_ne_zero χ⟩
  have hχ1 : χ.primitiveCharacter ≠ 1 := by
    intro h
    apply hχ
    rw [← changeLevel_primitiveCharacter χ, h, changeLevel_one]
  have h := LFunction_changeLevel (conductor_dvd_level χ) χ.primitiveCharacter (s := s)
    (Or.inl hχ1)
  rw [changeLevel_primitiveCharacter, hs] at h
  have hP : ∏ p ∈ N.primeFactors, (1 - χ.primitiveCharacter p * (p : ℂ) ^ (-s)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun p hp ↦ euler_factor_ne_zero_of_re_pos
      (Nat.prime_of_mem_primeFactors hp) (χ.primitiveCharacter.norm_le_one _) h0
  exact (mul_eq_zero.mp h.symm).resolve_right hP

/-- **Davenport, Ch. 14, p. 90, (D), (E) (row 14-8)**: for every complex character `χ`
mod `q` (`χ² ≠ χ₀`, primitive or not), every zero `β + iγ` of `L(s, χ)` has
`β ≤ 1 - c/(log q + log(|γ| + 2))`, `c = 1/714`. -/
@[kb "davenport1980" "Ch 14, p. 90"]
theorem Davenport.LFunction_zero_free_complex {χ : DirichletCharacter ℂ N} (hχ2 : χ ^ 2 ≠ 1)
    {s : ℂ} (hs : LFunction χ s = 0) :
    s.re ≤ 1 - 1 / 714 / (Real.log N + Real.log (|s.im| + 2)) := by
  have hN : N ≠ 1 := by
    rintro rfl
    exact hχ2 (Subsingleton.elim _ _)
  have hN2 : (2 : ℝ) ≤ N := by
    have := NeZero.ne N
    exact_mod_cast (show 2 ≤ N by omega)
  have hl2 := log_two_gt_two_thirds
  have hlN : Real.log 2 ≤ Real.log N := Real.log_le_log two_pos hN2
  have hlT : Real.log 2 ≤ Real.log (|s.im| + 2) :=
    Real.log_le_log two_pos (by linarith [abs_nonneg s.im])
  rcases le_or_gt s.re 0 with h0 | h0
  · have : 1 / 714 / (Real.log N + Real.log (|s.im| + 2)) ≤ 1 := by
      rw [div_le_one (by linarith)]; linarith
    linarith
  have hχ1 : χ ≠ 1 := fun h ↦ hχ2 (by rw [h, one_pow])
  have : NeZero χ.conductor := ⟨conductor_ne_zero χ⟩
  have hz := LFunction_primitiveCharacter_eq_zero hχ1 hs h0
  have hc2 : χ.primitiveCharacter ^ 2 ≠ 1 := by
    intro h
    apply hχ2
    rw [← changeLevel_primitiveCharacter χ, ← map_pow, h, map_one]
  have hb := Davenport.LFunction_zero_free_complex_primitive
    (primitiveCharacter_isPrimitive χ) hc2 hz
  have hMN : Real.log χ.conductor ≤ Real.log N :=
    Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero (conductor_ne_zero χ))
      (by exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne N)) (conductor_dvd_level χ))
  have hM0 : 0 ≤ Real.log χ.conductor := Real.log_natCast_nonneg _
  have hpos : 0 < Real.log χ.conductor + Real.log (|s.im| + 2) := by linarith
  have : 1 / 714 / (Real.log N + Real.log (|s.im| + 2)) ≤
      1 / 714 / (Real.log χ.conductor + Real.log (|s.im| + 2)) :=
    div_le_div_of_nonneg_left (by norm_num) hpos (by linarith)
  linarith

end NTKB
