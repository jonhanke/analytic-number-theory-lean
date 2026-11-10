/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Davenport.Hadamard.XiCharConj
import NTKB.Analytic.Davenport.Zeros.ZetaPartialFraction

/-!
# The real part of `L'/L` from the Hadamard product

**Davenport, Ch. 14, p. 89.** For a primitive character `χ` mod `q > 1`, from (17) and (18) of
Chapter 12:
`-Re L'/L(s, χ) = ½ log(q/π) + ½ Re ψ((s + a)/2) - ∑_ρ Re 1/(s - ρ)`, hence (B):
`-Re L'/L(s, χ) ≤ 6 𝔏 - ∑_ρ Re 1/(s - ρ)` for `1 < σ ≤ 2`, `𝔏 = log q + log(|t| + 2)`.
-/

open Filter Topology Complex Set DirichletCharacter
open scoped Real

namespace NTKB

variable {N : ℕ} [NeZero N]

lemma dirichletXi_zero_mem {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (hN : N ≠ 1)
    (ρ : ZeroIndex (dirichletXi χ)) :
    LFunction χ ρ.val = 0 ∧ 0 < ρ.val.re ∧ ρ.val.re < 1 :=
  (Davenport.dirichletXi_zeros hχ hN).1 ρ

/-- A zero of `L(s, χ)` (primitive `χ`, `q > 1`) with `0 < σ` occurs in `ZeroIndex (dirichletXi χ)`. -/
lemma exists_zeroIndex_dirichletXi {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive)
    (hN : N ≠ 1) {s : ℂ} (hs : LFunction χ s = 0) (h0 : 0 < s.re) :
    ∃ ρ : ZeroIndex (dirichletXi χ), ρ.val = s := by
  have hχ1 := ne_one_of_isPrimitive hχ hN
  have h1 : s.re < 1 := by
    by_contra h
    exact LFunction_ne_zero_of_one_le_re χ (Or.inl hχ1) (not_lt.mp h) hs
  exact exists_zeroIndex_val_eq (differentiable_dirichletXi hχ1) (dirichletXi_zero_ne_zero hχ hN)
    ((dirichletXi_eq_zero_iff hχ hN).mpr ⟨hs, h0, h1⟩)

lemma summable_re_inv_dirichletXi_zeros {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive)
    (hN : N ≠ 1) : Summable fun ρ : ZeroIndex (dirichletXi χ) ↦ (1 / ρ.val).re := by
  obtain ⟨ha, ha0⟩ := summable_dirichletXi_zeros hχ hN
  refine Summable.of_norm_bounded ha fun ρ ↦ ?_
  have h := dirichletXi_zero_mem hχ hN ρ
  have hρ : ρ.val ≠ 0 := ha0 ρ
  rw [Real.norm_eq_abs, one_div, Complex.inv_re, abs_div, abs_of_pos h.2.1,
    abs_of_pos (Complex.normSq_pos.mpr hρ), ← Complex.sq_norm, inv_pow, div_eq_mul_inv]
  exact mul_le_of_le_one_left (by positivity) h.2.2.le

lemma summable_re_inv_sub_dirichletXi_zeros {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive)
    (hN : N ≠ 1) {s : ℂ} (hs : ∀ ρ : ZeroIndex (dirichletXi χ), ρ.val ≠ s) :
    Summable fun ρ : ZeroIndex (dirichletXi χ) ↦ (1 / (s - ρ.val)).re := by
  obtain ⟨ha, ha0⟩ := summable_dirichletXi_zeros hχ hN
  have h := ((summable_inv_sub_add_inv ha ha0 hs).mapL Complex.reCLM).sub
    (summable_re_inv_dirichletXi_zeros hχ hN)
  refine h.congr fun ρ ↦ ?_
  simp

lemma tsum_re_inv_sub_dirichletXi_nonneg {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive)
    (hN : N ≠ 1) {s : ℂ} (h1 : 1 ≤ s.re) :
    0 ≤ ∑' ρ : ZeroIndex (dirichletXi χ), (1 / (s - ρ.val)).re :=
  tsum_nonneg fun ρ ↦
    (re_one_div_sub_pos (by linarith [(dirichletXi_zero_mem hχ hN ρ).2.2])).le

/-- **Davenport, Ch. 14, p. 89**: for primitive `χ` mod `q > 1`, `s` not a trivial zero and
`L(s, χ) ≠ 0`, `-Re L'/L(s, χ) = ½ log q - ½ log π + ½ Re ψ((s + a)/2) - ∑_ρ Re 1/(s - ρ)`. -/
@[kb "davenport1980" "Ch 14, p. 89"]
theorem Davenport.neg_re_logDeriv_LFunction_eq {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive)
    (hN : N ≠ 1) {s : ℂ} (hs : ∀ m : ℕ, s + dirichletParity χ ≠ -(2 * m))
    (hL : LFunction χ s ≠ 0) :
    -(deriv (LFunction χ) s / LFunction χ s).re =
      Real.log N / 2 - Real.log π / 2 +
        (Complex.digamma ((s + dirichletParity χ) / 2)).re / 2 -
        ∑' ρ : ZeroIndex (dirichletXi χ), (1 / (s - ρ.val)).re := by
  obtain ⟨A, B, h⟩ := Davenport.dirichletXi_hadamard hχ hN
  have hB := Davenport.re_B_eq_neg_tsum hχ hN h
  rw [Davenport.logDeriv_LFunction hχ hN h hs hL]
  obtain ⟨ha, ha0⟩ := summable_dirichletXi_zeros hχ hN
  have hne : ∀ ρ : ZeroIndex (dirichletXi χ), ρ.val ≠ s := fun ρ h' ↦
    hL (h' ▸ (dirichletXi_zero_mem hχ hN ρ).1)
  have hS := summable_inv_sub_add_inv ha ha0 hne
  have hS1 := summable_re_inv_sub_dirichletXi_zeros hχ hN hne
  have hS2 := summable_re_inv_dirichletXi_zeros hχ hN
  have hre : (∑' ρ : ZeroIndex (dirichletXi χ), (1 / (s - ρ.val) + 1 / ρ.val)).re =
      ∑' ρ : ZeroIndex (dirichletXi χ), (1 / (s - ρ.val)).re +
        ∑' ρ : ZeroIndex (dirichletXi χ), (1 / ρ.val).re := by
    rw [Complex.re_tsum hS, ← hS1.tsum_add hS2]
    exact tsum_congr fun ρ ↦ by simp
  have hd : deriv Complex.Gamma ((s + dirichletParity χ) / 2) /
      (2 * Complex.Gamma ((s + dirichletParity χ) / 2)) =
      Complex.digamma ((s + dirichletParity χ) / 2) / 2 := by
    rw [Complex.digamma_def, logDeriv_apply]; ring
  have hlogN : (Complex.log (N : ℂ)).re = Real.log N := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_log N.cast_nonneg, Complex.ofReal_re]
  rw [hd]
  simp only [Complex.add_re, Complex.sub_re, hre, hB, Complex.div_ofNat_re, re_log_pi, hlogN]
  ring

/-- `‖ψ(w)‖ ≤ 5 + 2 log(‖w‖ + 1)` for `Re w ≥ 0`, `‖w‖ ≥ 1/2`. -/
lemma norm_digamma_le_of_half {w : ℂ} (hw : 0 ≤ w.re) (hw1 : 1 / 2 ≤ ‖w‖) :
    ‖Complex.digamma w‖ ≤ 5 + 2 * Real.log (‖w‖ + 1) := by
  have hw0 : w ≠ 0 := fun h ↦ by simp [h] at hw1; linarith
  have h := norm_digamma_add_inv_le hw hw0
  have h1 : ‖1 / w‖ ≤ 2 := by
    rw [norm_div, norm_one, div_le_iff₀ (by linarith)]; linarith
  calc ‖Complex.digamma w‖ = ‖(Complex.digamma w + 1 / w) - 1 / w‖ := by ring_nf
    _ ≤ ‖Complex.digamma w + 1 / w‖ + ‖1 / w‖ := norm_sub_le _ _
    _ ≤ 5 + 2 * Real.log (‖w‖ + 1) := by linarith

omit [NeZero N] in
/-- The Gamma term for `L`: `½ Re ψ((s + a)/2) ≤ 6 log(|t| + 2)` for `1 ≤ σ ≤ 2`. -/
lemma re_digamma_parity_le (χ : DirichletCharacter ℂ N) {s : ℂ} (h0 : 1 ≤ s.re)
    (h2 : s.re ≤ 2) :
    (Complex.digamma ((s + dirichletParity χ) / 2)).re / 2 ≤ 6 * Real.log (|s.im| + 2) := by
  set w := (s + dirichletParity χ) / 2
  have ha0 := dirichletParity_re_nonneg χ
  have ha1 := dirichletParity_re_le_one χ
  have hai := dirichletParity_im χ
  have hwre : w.re = (s.re + (dirichletParity χ).re) / 2 := by simp [w]
  have hwim : w.im = s.im / 2 := by simp [w, hai]
  have hw1 : 1 / 2 ≤ ‖w‖ := by
    have := Complex.re_le_norm w; linarith
  have hwn : ‖w‖ ≤ |s.im| + 2 := by
    have := Complex.norm_le_abs_re_add_abs_im w
    rw [hwre, hwim, abs_of_nonneg (by linarith), abs_div, abs_two] at this
    linarith [abs_nonneg s.im]
  have hT : 0 ≤ |s.im| := abs_nonneg _
  have hlogw : Real.log (‖w‖ + 1) ≤ 2 * Real.log (|s.im| + 2) := by
    rw [show (2 : ℝ) * Real.log (|s.im| + 2) = ((2 : ℕ) : ℝ) * Real.log (|s.im| + 2) by norm_num,
      ← Real.log_pow]
    exact Real.log_le_log (by linarith) (by nlinarith)
  have hlog2 : Real.log 2 ≤ Real.log (|s.im| + 2) := Real.log_le_log two_pos (by linarith)
  have hψ := norm_digamma_le_of_half (by rw [hwre]; linarith) hw1
  have := Complex.re_le_norm (Complex.digamma w)
  have := log_two_gt_two_thirds
  linarith

/-- **Davenport, Ch. 14, p. 89, (B) (row 14-5)**: for primitive `χ` mod `q > 1` and
`1 < σ ≤ 2`, `-Re L'/L(s, χ) ≤ 6 (log q + log(|t| + 2)) - ∑_ρ Re 1/(s - ρ)`, the terms of the
sum being positive. -/
@[kb "davenport1980" "Ch 14, p. 89"]
theorem Davenport.neg_re_logDeriv_LFunction_le {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive)
    (hN : N ≠ 1) {s : ℂ} (h1 : 1 < s.re) (h2 : s.re ≤ 2) :
    -(deriv (LFunction χ) s / LFunction χ s).re ≤
      6 * (Real.log N + Real.log (|s.im| + 2)) -
        ∑' ρ : ZeroIndex (dirichletXi χ), (1 / (s - ρ.val)).re := by
  have hs : ∀ m : ℕ, s + dirichletParity χ ≠ -(2 * m) := by
    intro m h
    have := congrArg Complex.re h
    simp only [Complex.add_re, Complex.neg_re, Complex.mul_re] at this
    have h0 := dirichletParity_re_nonneg χ
    norm_num at this
    nlinarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
  have hL := LFunction_ne_zero_of_one_le_re χ (Or.inr (fun h ↦ by rw [h] at h1; simp at h1))
    h1.le
  rw [Davenport.neg_re_logDeriv_LFunction_eq hχ hN hs hL]
  have := re_digamma_parity_le χ h1.le h2
  have hπ : 0 ≤ Real.log π := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have hNl : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  linarith

/-- One Euler factor `1 - c p^{-z}` (`‖c‖ ≤ 1`) at `σ > 1`: nonvanishing, and its logarithmic
derivative has norm at most `log p`. -/
lemma euler_factor_bounds {p : ℕ} (hp : p.Prime) {c : ℂ} (hc : ‖c‖ ≤ 1) {s : ℂ}
    (hs : 1 < s.re) :
    HasDerivAt (fun z : ℂ ↦ 1 - c * (p : ℂ) ^ (-z)) (c * (p : ℂ) ^ (-s) * Complex.log p) s ∧
      1 - c * (p : ℂ) ^ (-s) ≠ 0 ∧
      ‖c * (p : ℂ) ^ (-s) * Complex.log p / (1 - c * (p : ℂ) ^ (-s))‖ ≤ Real.log p := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hd : HasDerivAt (fun z : ℂ ↦ (p : ℂ) ^ (-z)) ((p : ℂ) ^ (-s) * Complex.log p * (-1)) s :=
    (hasDerivAt_neg s).const_cpow (Or.inl hp0)
  refine ⟨by simpa [mul_comm, mul_assoc, mul_left_comm] using (hd.const_mul c).const_sub 1, ?_⟩
  have hx : ‖c * (p : ℂ) ^ (-s)‖ ≤ 1 / 2 := by
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos hp.pos]
    have h1 : (p : ℝ) ^ (-s).re ≤ (p : ℝ) ^ (-1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by simp; linarith)
    have h2 : (p : ℝ) ^ (-1 : ℝ) ≤ 1 / 2 := by
      rw [Real.rpow_neg_one, ← one_div]
      exact one_div_le_one_div_of_le two_pos hp2
    have h3 : 0 ≤ (p : ℝ) ^ (-s).re := Real.rpow_nonneg (by linarith) _
    calc ‖c‖ * (p : ℝ) ^ (-s).re ≤ 1 * (p : ℝ) ^ (-s).re := by gcongr
      _ ≤ 1 / 2 := by linarith
  have hlow : 1 / 2 ≤ ‖1 - c * (p : ℂ) ^ (-s)‖ := by
    have := norm_sub_norm_le (1 : ℂ) (c * (p : ℂ) ^ (-s))
    rw [norm_one] at this
    linarith
  have hne : 1 - c * (p : ℂ) ^ (-s) ≠ 0 := fun h ↦ by rw [h, norm_zero] at hlow; linarith
  refine ⟨hne, ?_⟩
  have hlog : ‖Complex.log p‖ = Real.log p := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_log (by linarith), Complex.norm_real,
      Real.norm_of_nonneg (Real.log_nonneg (by linarith))]
  rw [norm_div, norm_mul, hlog, div_le_iff₀ (by linarith)]
  have hl : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
  nlinarith

/-- **Davenport, Ch. 14, p. 89 (row 14-6)**: if `χ` mod `q` is induced by `χ₁` mod `q₁ ∣ q`, then
for `σ > 1`, `|L'/L(s, χ) - L'/L(s, χ₁)| ≤ ∑_{p ∣ q} log p ≤ log q`. -/
@[kb "davenport1980" "Ch 14, p. 89"]
theorem Davenport.norm_logDeriv_LFunction_changeLevel_sub_le {M : ℕ} [NeZero M] (hMN : M ∣ N)
    (χ : DirichletCharacter ℂ M) {s : ℂ} (hs : 1 < s.re) :
    ‖deriv (LFunction (changeLevel hMN χ)) s / LFunction (changeLevel hMN χ) s -
      deriv (LFunction χ) s / LFunction χ s‖ ≤ Real.log N := by
  have hs1 : s ≠ 1 := fun h ↦ by rw [h] at hs; simp at hs
  set P : ℂ → ℂ := fun z ↦ ∏ p ∈ N.primeFactors, (1 - χ p * (p : ℂ) ^ (-z)) with hP
  have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have heq : LFunction (changeLevel hMN χ) =ᶠ[𝓝 s] fun z ↦ LFunction χ z * P z := by
    filter_upwards [hopen.mem_nhds hs] with z hz
    exact LFunction_changeLevel hMN χ (Or.inr fun h ↦ by rw [h] at hz; simp at hz)
  have hfac : ∀ p ∈ N.primeFactors,
      HasDerivAt (fun z : ℂ ↦ 1 - χ p * (p : ℂ) ^ (-z)) (χ p * (p : ℂ) ^ (-s) * Complex.log p) s ∧
      1 - χ p * (p : ℂ) ^ (-s) ≠ 0 ∧
      ‖χ p * (p : ℂ) ^ (-s) * Complex.log p / (1 - χ p * (p : ℂ) ^ (-s))‖ ≤ Real.log p :=
    fun p hp ↦ euler_factor_bounds (Nat.prime_of_mem_primeFactors hp) (χ.norm_le_one _) hs
  have hP0 : P s ≠ 0 := Finset.prod_ne_zero_iff.mpr fun p hp ↦ (hfac p hp).2.1
  have hPd : DifferentiableAt ℂ P s := by
    rw [hP]
    exact DifferentiableAt.fun_finsetProd fun p hp ↦ (hfac p hp).1.differentiableAt
  have hL0 : LFunction χ s ≠ 0 :=
    LFunction_ne_zero_of_one_le_re χ (Or.inr hs1) hs.le
  have hLd := differentiableAt_LFunction χ s (Or.inl hs1)
  have hlog : deriv (LFunction (changeLevel hMN χ)) s / LFunction (changeLevel hMN χ) s =
      deriv (LFunction χ) s / LFunction χ s + logDeriv P s := by
    rw [heq.deriv_eq, heq.eq_of_nhds, ← logDeriv_apply, ← logDeriv_apply]
    exact logDeriv_mul (f := LFunction χ) (g := P) s hL0 hP0 hLd hPd
  have hPsum : logDeriv P s = ∑ p ∈ N.primeFactors,
      χ p * (p : ℂ) ^ (-s) * Complex.log p / (1 - χ p * (p : ℂ) ^ (-s)) := by
    rw [hP, logDeriv_fun_prod (fun p hp ↦ (hfac p hp).2.1)
      (fun p hp ↦ (hfac p hp).1.differentiableAt)]
    exact Finset.sum_congr rfl fun p hp ↦ by rw [logDeriv_apply, (hfac p hp).1.deriv]
  rw [hlog, add_sub_cancel_left, hPsum]
  calc ‖∑ p ∈ N.primeFactors, χ p * (p : ℂ) ^ (-s) * Complex.log p / (1 - χ p * (p : ℂ) ^ (-s))‖
      ≤ ∑ p ∈ N.primeFactors, Real.log p :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun p hp ↦ (hfac p hp).2.2)
    _ = Real.log (∏ p ∈ N.primeFactors, p : ℕ) := by
        push_cast
        rw [Real.log_prod]
        intro p hp
        exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero
    _ ≤ Real.log N := by
        apply Real.log_le_log
        · have : 0 < ∏ p ∈ N.primeFactors, p :=
            Finset.prod_pos fun p hp ↦ (Nat.prime_of_mem_primeFactors hp).pos
          exact_mod_cast this
        · exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne N))
            (Nat.prod_primeFactors_dvd N)

end NTKB
