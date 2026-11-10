/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import NTKB.Attr

/-!
# Pólya's inequality (Apostol, Theorems 8.20 and 8.21)

* **Theorem 8.20** (finite Fourier expansion of a primitive character):
  `χ(m) = (G(1,χ)/k) ∑_{n mod k} χ̄(-n) e^{2πimn/k}` (from Mathlib's discrete Fourier inversion
  `ZMod.dft_dft` and `DirichletCharacter.IsPrimitive.fourierTransform_eq_inv_mul_gaussSum`).
* **Theorem 8.21** (Pólya): for a primitive character `χ` mod `k > 1` and every real `x`,
  `|∑_{1 ≤ m ≤ x} χ(m)| < √k log k`. (For `k = 1` the trivial character is primitive and the
  inequality fails, so `k > 1`.)

Apostol's proof: summing the Fourier expansion, `√k |∑_{m ≤ x} χ(m)| ≤ ∑_{n=1}^{k-1} |f(n)|`,
`f(n) = ∑_{m ≤ x} e^{2πimn/k}`, with `|f(n)| ≤ 1/sin(πn/k)` (geometric sum), `f(k-n) = f̄(n)`,
and `sin t ≥ 2t/π` on `[0, π/2]`. The final estimate `∑_{n < k/2} 1/n + (1/k if k is even) < log k`
is proved from `1/n < log((2n+1)/(2n-1))` (the series of `log((1+y)/(1-y))`).
-/

open Finset Real ZMod

namespace NTKB.Apostol

/-! ### The harmonic estimate -/

theorem two_mul_lt_log_sub_log {y : ℝ} (h0 : 0 < y) (h1 : y < 1) :
    2 * y < log (1 + y) - log (1 - y) := by
  have hs := hasSum_log_sub_log_of_abs_lt_one (abs_lt.2 ⟨by linarith, h1⟩)
  have hle := sum_le_hasSum (range 2) (fun k _ ↦ by positivity) hs
  simp only [sum_range_succ, sum_range_zero] at hle
  norm_num at hle
  have : 0 < 2 * (1 / 3) * y ^ 3 := by positivity
  linarith

/-- `∑_{n=1}^M 1/n ≤ log(2M + 1)`, strictly for `M ≥ 1`. -/
theorem sum_inv_le_log_two_mul_add_one (M : ℕ) :
    ∑ n ∈ Icc 1 M, (1 : ℝ) / n ≤ log (2 * M + 1) ∧
      (1 ≤ M → ∑ n ∈ Icc 1 M, (1 : ℝ) / n < log (2 * M + 1)) := by
  induction M with
  | zero => simp
  | succ M ih =>
    have hstep : ∑ n ∈ Icc 1 (M + 1), (1 : ℝ) / n < log (2 * ((M + 1 : ℕ) : ℝ) + 1) := by
      rw [sum_Icc_succ_top (by omega)]
      have hy : (1 : ℝ) / (2 * M + 2) < 1 := by
        rw [div_lt_one (by positivity)]; linarith [M.cast_nonneg (α := ℝ)]
      have := two_mul_lt_log_sub_log (y := 1 / (2 * M + 2)) (by positivity) hy
      have e1 : 1 + 1 / (2 * (M : ℝ) + 2) = (2 * M + 3) / (2 * M + 2) := by
        field_simp; try ring
      have e2 : 1 - 1 / (2 * (M : ℝ) + 2) = (2 * M + 1) / (2 * M + 2) := by
        field_simp; try ring
      rw [e1, e2, log_div (by positivity) (by positivity), log_div (by positivity) (by positivity)]
        at this
      have e3 : 2 * (1 / (2 * (M : ℝ) + 2)) = 1 / ((M : ℝ) + 1) := by
        field_simp; try ring
      rw [e3] at this
      push_cast
      have e4 : 2 * ((M : ℝ) + 1) + 1 = 2 * M + 3 := by ring
      rw [e4]
      linarith [ih.1]
    exact ⟨hstep.le, fun _ ↦ hstep⟩

/-! ### The sum `∑ 1/sin(πn/k)` -/

theorem one_div_sin_le {N j : ℕ} (hj : 1 ≤ j) (h2j : 2 * j ≤ N) :
    1 / sin (π * j / N) ≤ N / (2 * j) := by
  have hN : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hj' : (0 : ℝ) < j := by exact_mod_cast hj
  have hle : π * j / N ≤ π / 2 := by
    rw [div_le_div_iff₀ hN (by norm_num)]
    have : (2 * j : ℝ) ≤ N := by exact_mod_cast h2j
    nlinarith [pi_pos]
  have hsin := mul_le_sin (by positivity) hle
  have hpos : 0 < 2 / π * (π * j / N) := by positivity
  have : 2 / π * (π * j / N) = 2 * j / N := by field_simp
  rw [this] at hsin
  have hs0 : 0 < sin (π * j / N) := lt_of_lt_of_le (by positivity) hsin
  rw [div_le_div_iff₀ hs0 (by positivity)]
  linarith [(div_le_iff₀ hN).1 hsin]

/-- `∑_{n=1}^{k-1} 1/sin(πn/k) < k log k` for `k ≥ 2`. -/
theorem sum_one_div_sin_lt {N : ℕ} (hN : 2 ≤ N) :
    ∑ j ∈ Icc 1 (N - 1), 1 / sin (π * j / N) < N * log N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  obtain ⟨s, hs⟩ : ∃ s : ℕ → ℝ, s = fun j : ℕ ↦ 1 / sin (π * (j : ℝ) / N) := ⟨_, rfl⟩
  rw [show (∑ j ∈ Icc 1 (N - 1), 1 / sin (π * j / N)) = ∑ j ∈ Icc 1 (N - 1), s j by rw [hs]]
  obtain ⟨M, hM⟩ : ∃ M, M = (N - 1) / 2 := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A : Finset ℕ, A = (Icc 1 (N - 1)).filter (fun j ↦ 2 * j < N) := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : Finset ℕ,
      B = (Icc 1 (N - 1)).filter (fun j ↦ ¬ 2 * j < N ∧ ¬ 2 * j = N) := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C : Finset ℕ,
      C = (Icc 1 (N - 1)).filter (fun j ↦ ¬ 2 * j < N ∧ 2 * j = N) := ⟨_, rfl⟩
  have hsplit : ∑ j ∈ Icc 1 (N - 1), s j = ∑ j ∈ A, s j + ∑ j ∈ B, s j + ∑ j ∈ C, s j := by
    have h1 := sum_filter_add_sum_filter_not (Icc 1 (N - 1)) (fun j ↦ 2 * j < N) s
    have h2 := sum_filter_add_sum_filter_not ((Icc 1 (N - 1)).filter fun j ↦ ¬ 2 * j < N)
      (fun j ↦ 2 * j = N) s
    rw [filter_filter, filter_filter] at h2
    rw [hA, hB, hC, ← h1, ← h2]
    ring
  have hAM : A = Icc 1 M := by
    ext j; simp only [hA, hM, mem_filter, mem_Icc]; omega
  have hsA : ∑ j ∈ A, s j ≤ N / 2 * ∑ n ∈ Icc 1 M, (1 : ℝ) / n := by
    rw [hAM, mul_sum]
    refine sum_le_sum fun j hj ↦ ?_
    have hj := mem_Icc.1 hj
    have := one_div_sin_le (N := N) hj.1 (by omega)
    rw [hs]
    calc 1 / sin (π * j / N) ≤ N / (2 * j) := this
      _ = N / 2 * (1 / j) := by field_simp
  have hBA : ∑ j ∈ B, s j = ∑ j ∈ A, s j := by
    refine sum_nbij' (fun j ↦ N - j) (fun j ↦ N - j) ?_ ?_ ?_ ?_ ?_
    · intro j hj; simp only [hA, hB, mem_filter, mem_Icc] at hj ⊢; omega
    · intro j hj; simp only [hA, hB, mem_filter, mem_Icc] at hj ⊢; omega
    · intro j hj; simp only [hB, mem_filter, mem_Icc] at hj; omega
    · intro j hj; simp only [hA, mem_filter, mem_Icc] at hj; omega
    · intro j hj
      simp only [hB, mem_filter, mem_Icc] at hj
      rw [hs]
      dsimp only
      rw [Nat.cast_sub (by omega), mul_sub, sub_div, mul_div_cancel_right₀ _ hN0.ne',
        sin_pi_sub]
  have hCc : ∑ j ∈ C, s j = #C := by
    rw [card_eq_sum_ones, Nat.cast_sum]
    refine sum_congr rfl fun j hj ↦ ?_
    simp only [hC, mem_filter] at hj
    have : (π * j / N) = π / 2 := by
      have : (N : ℝ) = 2 * j := by exact_mod_cast hj.2.2.symm
      have hj0 : (j : ℝ) ≠ 0 := by
        have := (mem_Icc.1 hj.1).1; exact_mod_cast (by omega : j ≠ 0)
      rw [this]; field_simp
    simp [hs, this]
  have hH := sum_inv_le_log_two_mul_add_one M
  rw [hsplit, hBA, hCc]
  rcases Nat.even_or_odd N with ⟨K, hK⟩ | ⟨K, hK⟩
  · -- `N = 2M + 2` even
    have hcard : #C ≤ 1 := by
      rw [card_le_one]
      intro a ha b hb
      simp only [hC, mem_filter] at ha hb
      omega
    have hNM : (N : ℝ) = 2 * M + 2 := by
      have : N = 2 * M + 2 := by omega
      exact_mod_cast this
    have hlog : 1 / (N : ℝ) < log N - log (2 * M + 1) := by
      have hx : (0 : ℝ) < (2 * M + 1) / N := by positivity
      have hx1 : (2 * M + 1 : ℝ) / N ≠ 1 := by
        rw [hNM]; intro h; field_simp at h; linarith
      have := log_lt_sub_one_of_pos hx hx1
      rw [log_div (by positivity) hN0.ne'] at this
      have e : (2 * M + 1 : ℝ) / N - 1 = -(1 / N) := by
        rw [hNM]; field_simp; ring
      linarith
    have hc1 : (#C : ℝ) ≤ 1 := by exact_mod_cast hcard
    have h3 := mul_lt_mul_of_pos_left hlog hN0
    have hmul : (N : ℝ) * (1 / N) = 1 := by field_simp
    have h4 : (N : ℝ) * ∑ n ∈ Icc 1 M, (1 : ℝ) / n ≤ N * log (2 * M + 1) :=
      mul_le_mul_of_nonneg_left hH.1 hN0.le
    nlinarith
  · -- `N = 2M + 1` odd
    have hM1 : 1 ≤ M := by omega
    have hC0 : C = ∅ := by
      ext j; simp only [hC, mem_filter, mem_Icc, notMem_empty, iff_false]; omega
    have hNM : (N : ℝ) = 2 * M + 1 := by
      have : N = 2 * M + 1 := by omega
      exact_mod_cast this
    rw [hC0, card_empty, Nat.cast_zero, add_zero]
    have h4 : (N : ℝ) * ∑ n ∈ Icc 1 M, (1 : ℝ) / n < N * log N := by
      rw [hNM]; exact mul_lt_mul_of_pos_left (hH.2 hM1) (by positivity)
    nlinarith

/-! ### The Fourier expansion and Pólya's inequality -/

variable {N : ℕ} [NeZero N]

/-- **Apostol, Theorem 8.20**: the finite Fourier expansion of a primitive character,
`χ(m) = (G(1,χ)/k) ∑_{n mod k} χ̄(-n) e^{2πinm/k}`. -/
@[kb "apostol1976" "Thm 8.20, p. 172"]
theorem eq_fourier_of_isPrimitive {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive)
    (m : ZMod N) :
    χ m = gaussSum χ stdAddChar / N *
      ∑ k : ZMod N, χ⁻¹ (-k) * stdAddChar (k * m) := by
  have h := congrFun (dft_dft (χ : ZMod N → ℂ)) (-m)
  rw [dft_apply] at h
  simp_rw [DirichletCharacter.IsPrimitive.fourierTransform_eq_inv_mul_gaussSum hχ,
    smul_eq_mul, mul_neg, neg_neg] at h
  have hN : (N : ℂ) ≠ 0 := NeZero.ne _
  rw [div_mul_eq_mul_div, eq_div_iff hN, mul_sum]
  rw [mul_comm, ← h]
  refine sum_congr rfl fun k _ ↦ ?_
  ring

/-- The geometric sum: `‖∑_{m=1}^r e^{imθ}‖ ≤ 1/sin(θ/2)` when `sin(θ/2) > 0`. -/
theorem norm_sum_exp_le {θ : ℝ} (hθ : 0 < sin (θ / 2)) (r : ℕ) :
    ‖∑ m ∈ Icc 1 r, Complex.exp (Complex.I * θ) ^ m‖ ≤ 1 / sin (θ / 2) := by
  set z := Complex.exp (Complex.I * θ)
  have hz1 : ‖z‖ = 1 := by
    simp only [z]; rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I θ
  have hzn : ‖z - 1‖ = 2 * sin (θ / 2) := by
    rw [Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs, abs_of_pos (by linarith)]
  have hz : z ≠ 1 := by
    intro h; rw [h, sub_self, norm_zero] at hzn; linarith
  have hsum : ∑ m ∈ Icc 1 r, z ^ m = z * ((z ^ r - 1) / (z - 1)) := by
    rw [← geom_sum_eq hz, mul_sum, ← Finset.Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range,
      Nat.add_sub_cancel]
    exact sum_congr rfl fun m _ ↦ by ring
  rw [hsum, norm_mul, hz1, one_mul, norm_div, hzn]
  have : ‖z ^ r - 1‖ ≤ 2 := by
    calc ‖z ^ r - 1‖ ≤ ‖z ^ r‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, hz1]; norm_num
  calc ‖z ^ r - 1‖ / (2 * sin (θ / 2)) ≤ 2 / (2 * sin (θ / 2)) := by gcongr
    _ = 1 / sin (θ / 2) := by field_simp

theorem stdAddChar_mul_natCast (j m : ℕ) :
    stdAddChar ((j : ZMod N) * (m : ZMod N)) =
      Complex.exp (Complex.I * ((2 * π * j / N : ℝ) : ℂ)) ^ m := by
  have : (j : ZMod N) * (m : ZMod N) = (((j * m : ℕ) : ℤ) : ZMod N) := by push_cast; ring
  rw [this, stdAddChar_coe, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- `‖∑_{m=1}^r e^{2πijm/k}‖ ≤ 1/sin(πj/k)` for `1 ≤ j ≤ k - 1`. -/
theorem norm_sum_stdAddChar_le {j : ℕ} (hj : 1 ≤ j) (hjN : j < N) (r : ℕ) :
    ‖∑ m ∈ Icc 1 r, stdAddChar ((j : ZMod N) * (m : ZMod N))‖ ≤ 1 / sin (π * j / N) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  simp_rw [stdAddChar_mul_natCast]
  have e : 2 * π * j / N / 2 = π * j / N := by ring
  have hpos : 0 < sin (2 * π * j / N / 2) := by
    rw [e]
    apply sin_pos_of_pos_of_lt_pi (by have : (0 : ℝ) < j := by exact_mod_cast hj
                                      positivity)
    rw [div_lt_iff₀ hN0]
    have : (j : ℝ) < N := by exact_mod_cast hjN
    nlinarith [pi_pos]
  have := norm_sum_exp_le hpos r
  rwa [e] at this

theorem sum_zmod_eq_sum_range {M : Type*} [AddCommMonoid M] (F : ZMod N → M) :
    ∑ k : ZMod N, F k = ∑ j ∈ range N, F j := by
  refine sum_nbij' (fun k ↦ k.val) (fun j ↦ (j : ZMod N)) ?_ ?_ ?_ ?_ ?_
  · intro k _; exact mem_range.2 (ZMod.val_lt k)
  · intro j _; exact mem_univ _
  · intro k _; exact ZMod.natCast_zmod_val k
  · intro j hj; exact ZMod.val_natCast_of_lt (mem_range.1 hj)
  · intro k _; rw [ZMod.natCast_zmod_val]

/-- **Apostol, Theorem 8.21** (Pólya's inequality): for a primitive character `χ` modulo
`k > 1` and every real `x`, `|∑_{1 ≤ m ≤ x} χ(m)| < √k log k`. -/
@[kb "apostol1976" "Thm 8.21, p. 173"]
theorem polya {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (hN : 1 < N) (x : ℝ) :
    ‖∑ m ∈ Icc 1 ⌊x⌋₊, χ m‖ < √N * log N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  set r := ⌊x⌋₊
  set G := gaussSum χ stdAddChar
  set E : ZMod N → ℂ := fun k ↦ ∑ m ∈ Icc 1 r, stdAddChar (k * (m : ZMod N))
  have hexp : ∑ m ∈ Icc 1 r, χ m = G / N * ∑ k : ZMod N, χ⁻¹ (-k) * E k := by
    simp_rw [eq_fourier_of_isPrimitive hχ, ← mul_sum, E, mul_sum]
    rw [sum_comm]
  have hG : ‖G / N‖ = √N / N := by
    rw [norm_div, DirichletCharacter.norm_gaussSum_stdAddChar hχ, Complex.norm_natCast]
  -- bound each Fourier coefficient
  set B : ℕ → ℝ := fun j ↦ if j = 0 then 0 else 1 / sin (π * j / N)
  have hterm : ∀ j ∈ range N, ‖χ⁻¹ (-(j : ZMod N)) * E j‖ ≤ B j := by
    intro j hj
    have hj := mem_range.1 hj
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · have : ¬ IsUnit (0 : ZMod N) := by
        rw [isUnit_zero_iff]; have : Fact (1 < N) := ⟨hN⟩; exact zero_ne_one
      simp [B, MulChar.map_nonunit _ this]
    · simp only [B, hj0.ne', ite_false, norm_mul]
      calc ‖χ⁻¹ (-(j : ZMod N))‖ * ‖E j‖ ≤ 1 * ‖E j‖ := by
            gcongr; exact DirichletCharacter.norm_le_one _ _
        _ ≤ 1 / sin (π * j / N) := by
            rw [one_mul]; exact norm_sum_stdAddChar_le hj0 hj r
  have hsumB : ∑ j ∈ range N, B j = ∑ j ∈ Icc 1 (N - 1), 1 / sin (π * j / N) := by
    rw [range_eq_Ico, sum_eq_sum_Ico_succ_bot (by omega : 0 < N)]
    have hI : Ico (0 + 1) N = Icc 1 (N - 1) := by ext j; simp only [mem_Ico, mem_Icc]; omega
    rw [hI]
    simp only [B, ite_true, zero_add]
    exact sum_congr rfl fun j hj ↦ by rw [ite_eq_right_iff.2 (fun h ↦ by have := (mem_Icc.1 hj).1; omega)]
  have hbound : ‖∑ k : ZMod N, χ⁻¹ (-k) * E k‖ ≤ ∑ j ∈ Icc 1 (N - 1), 1 / sin (π * j / N) := by
    rw [sum_zmod_eq_sum_range, ← hsumB]
    exact (norm_sum_le _ _).trans (sum_le_sum hterm)
  rw [hexp, norm_mul, hG]
  have hlt := sum_one_div_sin_lt (show 2 ≤ N by omega)
  have hsq : 0 < √(N : ℝ) / N := by positivity
  calc √(N : ℝ) / N * ‖∑ k : ZMod N, χ⁻¹ (-k) * E k‖
      ≤ √(N : ℝ) / N * ∑ j ∈ Icc 1 (N - 1), 1 / sin (π * j / N) := by gcongr
    _ < √(N : ℝ) / N * (N * log N) := by gcongr
    _ = √N * log N := by field_simp

end NTKB.Apostol
