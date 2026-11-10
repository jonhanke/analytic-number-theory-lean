/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Davenport.Zeros.ZetaLocal

/-!
# Local distribution of the zeros of `L(s, χ)`

**Davenport, Ch. 16, p. 102.** For `χ` primitive mod `q > 1`, with `𝔏 = log q + log(|t| + 2)`:

* (row 16-5, Lemma) `∑_ρ 1/(1 + (t - γ)²) ≤ A 𝔏` for every real `t`, from (B) of Ch. 14 at
  `s = 2 + it`;
* (row 16-6) the number of zeros with `|γ - t| < 1` is at most `A 𝔏`;
* (row 16-7) for `-1 ≤ σ ≤ 2`, `|t| ≥ 2`, `L(s, χ) ≠ 0`:
  `L'/L(s, χ) = ∑_{|t - γ| < 1} 1/(s - ρ) + O(𝔏)`.

Davenport states (D) for every `t` not an ordinate; for `|t|` small and `σ ≤ 0` the trivial zero
at `s = 0` or `s = -1` contributes a pole of `L'/L` not in the sum, so we take `|t| ≥ 2`, which is
how (D) is used in Ch. 19 (on the lines `t = ±T`, `T ≥ 2`).
-/

open Filter Topology Complex Set DirichletCharacter
open scoped Real

namespace NTKB

variable {N : ℕ} [NeZero N]

/-- `‖ψ(w)‖ ≤ 6 + 2 log(‖w‖ + 2)` for `Re w ≥ -1/2` and `|Im w| ≥ 1`. -/
lemma norm_digamma_le_of_im {w : ℂ} (hre : -1 / 2 ≤ w.re) (him : 1 ≤ |w.im|) :
    ‖Complex.digamma w‖ ≤ 6 + 2 * Real.log (‖w‖ + 2) := by
  have hpole : ∀ m : ℕ, w ≠ -m := fun m h ↦ by
    have := congrArg Complex.im h; simp at this; rw [this] at him; norm_num at him
  have hw0 : w ≠ 0 := by simpa using hpole 0
  have hrec := Complex.digamma_apply_add_one w hpole
  have hw1 : 1 ≤ ‖w‖ := him.trans (Complex.abs_im_le_norm w)
  have hb := norm_digamma_le_of_half (w := w + 1) (by simp; linarith)
    (by have := Complex.abs_im_le_norm (w + 1); simp at this; linarith)
  have hn : ‖w + 1‖ ≤ ‖w‖ + 1 := by
    have := norm_add_le w 1; simpa using this
  have hl : Real.log (‖w + 1‖ + 1) ≤ Real.log (‖w‖ + 2) :=
    Real.log_le_log (by positivity) (by linarith)
  have hinv : ‖w⁻¹‖ ≤ 1 := by
    rw [norm_inv]; exact inv_le_one_of_one_le₀ hw1
  have : Complex.digamma w = Complex.digamma (w + 1) - w⁻¹ := by rw [hrec]; ring
  rw [this]
  calc ‖Complex.digamma (w + 1) - w⁻¹‖ ≤ ‖Complex.digamma (w + 1)‖ + ‖w⁻¹‖ := norm_sub_le _ _
    _ ≤ 6 + 2 * Real.log (‖w‖ + 2) := by linarith

omit [NeZero N] in
/-- `‖ψ((s + a)/2)‖ ≤ 6 + 4 log(|t| + 2)` for `-1 ≤ σ ≤ 2`, `|t| ≥ 2`. -/
lemma norm_digamma_parity_le (χ : DirichletCharacter ℂ N) {z : ℂ} (h1 : -1 ≤ z.re)
    (h2 : z.re ≤ 2) (ht : 2 ≤ |z.im|) :
    ‖Complex.digamma ((z + dirichletParity χ) / 2)‖ ≤ 6 + 4 * Real.log (|z.im| + 2) := by
  set w := (z + dirichletParity χ) / 2
  have ha0 := dirichletParity_re_nonneg χ
  have ha1 := dirichletParity_re_le_one χ
  have hai := dirichletParity_im χ
  have hwre : w.re = (z.re + (dirichletParity χ).re) / 2 := by simp [w]
  have hwim : w.im = z.im / 2 := by simp [w, hai]
  have him : 1 ≤ |w.im| := by rw [hwim, abs_div, abs_two]; linarith
  have hwn : ‖w‖ ≤ |z.im| + 2 := by
    have := Complex.norm_le_abs_re_add_abs_im w
    rw [hwre, hwim] at this
    have h3 : |(z.re + (dirichletParity χ).re) / 2| ≤ 3 / 2 := by
      rw [abs_le]; constructor <;> linarith
    have h4 : |z.im / 2| = |z.im| / 2 := by rw [abs_div, abs_two]
    linarith [abs_nonneg z.im]
  have hl : Real.log (‖w‖ + 2) ≤ 2 * Real.log (|z.im| + 2) := by
    rw [show (2 : ℝ) * Real.log (|z.im| + 2) = ((2 : ℕ) : ℝ) * Real.log (|z.im| + 2) by norm_num,
      ← Real.log_pow]
    exact Real.log_le_log (by positivity) (by nlinarith [abs_nonneg z.im])
  have := norm_digamma_le_of_im (w := w) (by rw [hwre]; linarith) him
  linarith

/-- `|L'/L(2 + it, χ)| ≤ -ζ'/ζ(2)`. -/
lemma norm_logDeriv_LFunction_two_add (χ : DirichletCharacter ℂ N) (t : ℝ) :
    ‖deriv (LFunction χ) (2 + t * I) / LFunction χ (2 + t * I)‖ ≤ zetaLogDerivTwo := by
  have h := norm_logDeriv_LFunction_le χ (s := 2 + t * I) (by simp)
  simpa [zetaLogDerivTwo] using h

/-- **Davenport, Ch. 16, p. 102, Lemma (row 16-5)**: there is an absolute `A` such that for
primitive `χ` mod `q > 1` and every real `t`,
`∑_ρ 1/(1 + (t - γ)²) ≤ A (log q + log(|t| + 2))`. -/
@[kb "davenport1980" "Ch 16, p. 102"]
theorem Davenport.sum_L_zeros_inv_one_add_sq_le :
    ∃ A : ℝ, 0 < A ∧ ∀ {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}, χ.IsPrimitive → N ≠ 1 →
      ∀ t : ℝ, Summable (fun ρ : ZeroIndex (dirichletXi χ) ↦ 1 / (1 + (t - ρ.val.im) ^ 2)) ∧
        ∑' ρ : ZeroIndex (dirichletXi χ), 1 / (1 + (t - ρ.val.im) ^ 2) ≤
          A * (Real.log N + Real.log (|t| + 2)) := by
  have hl2 := log_two_gt_two_thirds
  have hC := zetaLogDerivTwo_nonneg
  refine ⟨4 * (6 + zetaLogDerivTwo / Real.log 2), by positivity, ?_⟩
  intro N _ χ hχ hN t
  set s : ℂ := 2 + t * I with hs
  have hsre : s.re = 2 := by simp [s]
  have hsim : s.im = t := by simp [s]
  have hne : ∀ ρ : ZeroIndex (dirichletXi χ), ρ.val ≠ s := fun ρ h ↦ by
    have := congrArg Complex.re h; rw [hsre] at this
    linarith [(dirichletXi_zero_mem hχ hN ρ).2.2]
  have hS := summable_re_inv_sub_dirichletXi_zeros hχ hN hne
  have hle : ∀ ρ : ZeroIndex (dirichletXi χ), 1 / (1 + (t - ρ.val.im) ^ 2) ≤
      4 * (1 / (s - ρ.val)).re := fun ρ ↦
    inv_one_add_sq_le_four_re (dirichletXi_zero_mem hχ hN ρ).2.1
      (dirichletXi_zero_mem hχ hN ρ).2.2 t
  have hS' : Summable (fun ρ : ZeroIndex (dirichletXi χ) ↦ 1 / (1 + (t - ρ.val.im) ^ 2)) :=
    Summable.of_nonneg_of_le (fun ρ ↦ by positivity) hle (hS.mul_left 4)
  refine ⟨hS', ?_⟩
  have hpar : ∀ m : ℕ, s + dirichletParity χ ≠ -(2 * m) := by
    intro m h
    have := congrArg Complex.re h
    simp only [Complex.add_re, Complex.neg_re, Complex.mul_re] at this
    have h0 := dirichletParity_re_nonneg χ
    rw [hsre] at this
    norm_num at this
    nlinarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
  have hL := LFunction_ne_zero_of_one_le_re χ (Or.inr (fun h ↦ by
    have := congrArg Complex.re h; rw [hsre] at this; norm_num at this)) (s := s)
    (by rw [hsre]; norm_num)
  have hid := Davenport.neg_re_logDeriv_LFunction_eq hχ hN hpar hL
  have hψ := re_digamma_parity_le χ (s := s) (by rw [hsre]; norm_num) (by rw [hsre])
  have hz2 : -(deriv (LFunction χ) s / LFunction χ s).re ≥ -zetaLogDerivTwo := by
    have := norm_logDeriv_LFunction_two_add χ t
    have := Complex.re_le_norm (deriv (LFunction χ) s / LFunction χ s)
    linarith
  have hπ : 0 ≤ Real.log π := Real.log_nonneg (by linarith [Real.pi_gt_three])
  rw [hsim] at hψ
  have hlT : Real.log 2 ≤ Real.log (|t| + 2) := Real.log_le_log two_pos (by linarith [abs_nonneg t])
  have hlN : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  have hsum : ∑' ρ : ZeroIndex (dirichletXi χ), (1 / (s - ρ.val)).re ≤
      (6 + zetaLogDerivTwo / Real.log 2) * (Real.log N + Real.log (|t| + 2)) := by
    have h1 : ∑' ρ : ZeroIndex (dirichletXi χ), (1 / (s - ρ.val)).re ≤
        Real.log N / 2 + zetaLogDerivTwo + 6 * Real.log (|t| + 2) := by linarith
    have h2 : zetaLogDerivTwo ≤ zetaLogDerivTwo / Real.log 2 * (Real.log N + Real.log (|t| + 2)) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
      exact mul_le_mul_of_nonneg_left (by linarith) hC
    nlinarith
  calc ∑' ρ : ZeroIndex (dirichletXi χ), 1 / (1 + (t - ρ.val.im) ^ 2)
      ≤ ∑' ρ : ZeroIndex (dirichletXi χ), 4 * (1 / (s - ρ.val)).re :=
        hS'.tsum_le_tsum hle (hS.mul_left 4)
    _ = 4 * ∑' ρ : ZeroIndex (dirichletXi χ), (1 / (s - ρ.val)).re := tsum_mul_left
    _ ≤ 4 * (6 + zetaLogDerivTwo / Real.log 2) * (Real.log N + Real.log (|t| + 2)) := by
        rw [mul_assoc]; gcongr

lemma norm_dirichletXi_zero_le {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (hN : N ≠ 1)
    (ρ : ZeroIndex (dirichletXi χ)) : ‖ρ.val‖ ≤ 1 + |ρ.val.im| := by
  have h := dirichletXi_zero_mem hχ hN ρ
  have := Complex.norm_le_abs_re_add_abs_im ρ.val
  rw [abs_of_pos h.2.1] at this
  linarith [h.2.2]

/-- **Davenport, Ch. 16, p. 102 (row 16-6)**: for primitive `χ` mod `q > 1`, the number of zeros
(with multiplicity) with `|γ - t| < 1` is finite and at most `A (log q + log(|t| + 2))`. -/
@[kb "davenport1980" "Ch 16, p. 102"]
theorem Davenport.card_L_zeros_near_le :
    ∃ A : ℝ, 0 < A ∧ ∀ {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}, χ.IsPrimitive → N ≠ 1 →
      ∀ t : ℝ, {ρ : ZeroIndex (dirichletXi χ) | |ρ.val.im - t| < 1}.Finite ∧
      ({ρ : ZeroIndex (dirichletXi χ) | |ρ.val.im - t| < 1}.ncard : ℝ) ≤
        A * (Real.log N + Real.log (|t| + 2)) := by
  obtain ⟨A, hA, h⟩ := Davenport.sum_L_zeros_inv_one_add_sq_le
  refine ⟨2 * A, by positivity, ?_⟩
  intro N _ χ hχ hN t
  obtain ⟨hS, hle⟩ := h hχ hN t
  have hfin : {ρ : ZeroIndex (dirichletXi χ) | |ρ.val.im - t| < 1}.Finite := by
    have hF := finite_zeroIndex_closedBall (differentiable_dirichletXi (ne_one_of_isPrimitive hχ hN))
      (|t| + 2)
    refine (Set.finite_coe_iff.mp ?_).subset
      (s := {ρ : ZeroIndex (dirichletXi χ) | ‖ρ.val‖ ≤ |t| + 2}) fun ρ hρ ↦ ?_
    · exact hF
    simp only [Set.mem_ofPred_eq] at hρ ⊢
    have := norm_dirichletXi_zero_le hχ hN ρ
    have : |ρ.val.im| ≤ |t| + 1 := by
      have := abs_sub_abs_le_abs_sub ρ.val.im t
      linarith
    linarith
  refine ⟨hfin, ?_⟩
  rw [Set.ncard_eq_toFinset_card _ hfin]
  have hsum := hS.sum_le_tsum hfin.toFinset (fun ρ _ ↦ by positivity)
  have hcard : (hfin.toFinset.card : ℝ) * (1 / 2) ≤
      ∑ ρ ∈ hfin.toFinset, 1 / (1 + (t - ρ.val.im) ^ 2) := by
    rw [← nsmul_eq_mul]
    refine Finset.card_nsmul_le_sum _ _ _ fun ρ hρ ↦ ?_
    rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hρ
    have : (t - ρ.val.im) ^ 2 < 1 := by
      rw [← sq_abs, abs_sub_comm]; nlinarith [abs_nonneg (ρ.val.im - t)]
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]
    linarith
  linarith

/-- **Davenport, Ch. 16, p. 102, (D) (row 16-7)**: there is an absolute `A` such that for
primitive `χ` mod `q > 1`, `-1 ≤ σ ≤ 2`, `|t| ≥ 2` and `L(s, χ) ≠ 0`,
`|L'/L(s, χ) - ∑_{|t - γ| < 1} 1/(s - ρ)| ≤ A (log q + log(|t| + 2))`. -/
@[kb "davenport1980" "Ch 16, p. 102"]
theorem Davenport.logDeriv_LFunction_local :
    ∃ A : ℝ, 0 < A ∧ ∀ {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}, χ.IsPrimitive → N ≠ 1 →
      ∀ s : ℂ, -1 ≤ s.re → s.re ≤ 2 → 2 ≤ |s.im| → LFunction χ s ≠ 0 →
      ‖deriv (LFunction χ) s / LFunction χ s -
        ∑' ρ : ZeroIndex (dirichletXi χ),
          (if |s.im - ρ.val.im| < 1 then 1 / (s - ρ.val) else 0)‖ ≤
        A * (Real.log N + Real.log (|s.im| + 2)) := by
  classical
  obtain ⟨A₀, hA₀, h₀⟩ := Davenport.sum_L_zeros_inv_one_add_sq_le
  have hC := zetaLogDerivTwo_nonneg
  refine ⟨zetaLogDerivTwo + 10 + 6 * A₀, by positivity, ?_⟩
  intro N _ χ hχ hN s hσ1 hσ2 ht hz
  obtain ⟨Aa, Ba, hH⟩ := Davenport.dirichletXi_hadamard hχ hN
  set t := s.im with ht_def
  set s₀ : ℂ := 2 + t * I with hs₀
  have hs₀re : s₀.re = 2 := by simp [s₀]
  have hs₀im : s₀.im = t := by simp [s₀]
  have hpar : ∀ z : ℂ, z.im ≠ 0 → ∀ m : ℕ, z + dirichletParity χ ≠ -(2 * m) := by
    intro z hz m h
    have := congrArg Complex.im h
    simp [dirichletParity_im] at this
    exact hz this
  have ht0 : t ≠ 0 := fun h ↦ by rw [h] at ht; norm_num at ht
  have hz₀ := LFunction_ne_zero_of_one_le_re χ (Or.inr (fun h ↦ by
    have := congrArg Complex.re h; rw [hs₀re] at this; norm_num at this)) (s := s₀)
    (by rw [hs₀re]; norm_num)
  obtain ⟨ha, ha0⟩ := summable_dirichletXi_zeros hχ hN
  have hne : ∀ ρ : ZeroIndex (dirichletXi χ), ρ.val ≠ s := fun ρ h' ↦
    hz (h' ▸ (dirichletXi_zero_mem hχ hN ρ).1)
  have hne₀ : ∀ ρ : ZeroIndex (dirichletXi χ), ρ.val ≠ s₀ := fun ρ h' ↦
    hz₀ (h' ▸ (dirichletXi_zero_mem hχ hN ρ).1)
  have hS := summable_inv_sub_add_inv ha ha0 hne
  have hS₀ := summable_inv_sub_add_inv ha ha0 hne₀
  have hF := Davenport.logDeriv_LFunction hχ hN hH (hpar s ht0) hz
  have hF₀ := Davenport.logDeriv_LFunction hχ hN hH (hpar s₀ (by rw [hs₀im]; exact ht0)) hz₀
  have hd : ∀ w : ℂ, deriv Complex.Gamma w / (2 * Complex.Gamma w) =
      Complex.digamma w / 2 := fun w ↦ by
    rw [Complex.digamma_def, logDeriv_apply]; ring
  rw [hd] at hF hF₀
  set n₁ : ZeroIndex (dirichletXi χ) → ℂ :=
    fun ρ ↦ if |t - ρ.val.im| < 1 then 1 / (s - ρ.val) else 0
  set g : ZeroIndex (dirichletXi χ) → ℂ := fun ρ ↦ 1 / (s - ρ.val) - 1 / (s₀ - ρ.val)
  have hg : Summable g := (hS.sub hS₀).congr fun ρ ↦ by simp only [g]; ring
  have hfin : {ρ : ZeroIndex (dirichletXi χ) | |ρ.val.im - t| < 1}.Finite := by
    obtain ⟨A₁, -, h₁⟩ := Davenport.card_L_zeros_near_le
    exact (h₁ hχ hN t).1
  have hn₁ : Summable n₁ := by
    refine summable_of_ne_finset_zero (s := hfin.toFinset) fun ρ hρ ↦ ?_
    rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, abs_sub_comm] at hρ
    simp [n₁, hρ]
  set r : ZeroIndex (dirichletXi χ) → ℂ := fun ρ ↦ g ρ - n₁ ρ
  have hr : Summable r := hg.sub hn₁
  obtain ⟨hS1, hle1⟩ := h₀ hχ hN t
  have hrb : ∀ ρ : ZeroIndex (dirichletXi χ), ‖r ρ‖ ≤ 6 * (1 / (1 + (t - ρ.val.im) ^ 2)) := by
    intro ρ
    have hβ := dirichletXi_zero_mem hχ hN ρ
    have hd₀ : 1 ≤ ‖s₀ - ρ.val‖ := by
      have := Complex.re_le_norm (s₀ - ρ.val)
      simp only [sub_re, hs₀re] at this
      linarith [hβ.2.2]
    simp only [r, g, n₁]
    split_ifs with hnear
    · have : (t - ρ.val.im) ^ 2 < 1 := by
        rw [← sq_abs]; nlinarith [abs_nonneg (t - ρ.val.im)]
      rw [sub_sub_cancel_left, norm_neg, norm_div, norm_one]
      calc 1 / ‖s₀ - ρ.val‖ ≤ 1 := by rw [div_le_one (by linarith)]; exact hd₀
        _ ≤ 6 * (1 / (1 + (t - ρ.val.im) ^ 2)) := by
            rw [mul_one_div, le_div_iff₀ (by positivity)]; linarith
    · push Not at hnear
      have hsq : 1 ≤ (t - ρ.val.im) ^ 2 := by rw [← sq_abs]; nlinarith
      have hsρ : |t - ρ.val.im| ≤ ‖s - ρ.val‖ := by
        have := Complex.abs_im_le_norm (s - ρ.val); simpa [← ht_def] using this
      have hs₀ρ : |t - ρ.val.im| ≤ ‖s₀ - ρ.val‖ := by
        have := Complex.abs_im_le_norm (s₀ - ρ.val); simpa [hs₀im] using this
      have hne1 : s - ρ.val ≠ 0 := sub_ne_zero.mpr (hne ρ).symm
      have hne2 : s₀ - ρ.val ≠ 0 := sub_ne_zero.mpr (hne₀ ρ).symm
      have heq : 1 / (s - ρ.val) - 1 / (s₀ - ρ.val) - 0 =
          (s₀ - s) / ((s - ρ.val) * (s₀ - ρ.val)) := by field_simp; ring
      have hss : ‖s₀ - s‖ ≤ 3 := by
        have : s₀ - s = ((2 - s.re : ℝ) : ℂ) := by
          apply Complex.ext <;> simp [s₀, ← ht_def]
        rw [this, Complex.norm_real, Real.norm_eq_abs, abs_le]; constructor <;> linarith
      rw [heq, norm_div, norm_mul]
      have hp : 0 < |t - ρ.val.im| := by linarith
      calc ‖s₀ - s‖ / (‖s - ρ.val‖ * ‖s₀ - ρ.val‖) ≤ 3 / (|t - ρ.val.im| * |t - ρ.val.im|) :=
            div_le_div₀ (by norm_num) hss (by positivity) (mul_le_mul hsρ hs₀ρ hp.le
              (norm_nonneg _))
        _ = 3 / (t - ρ.val.im) ^ 2 := by rw [abs_mul_abs_self, sq]
        _ ≤ 6 * (1 / (1 + (t - ρ.val.im) ^ 2)) := by
            rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]; linarith
  have hrsum : ‖∑' ρ, r ρ‖ ≤ 6 * A₀ * (Real.log N + Real.log (|t| + 2)) := by
    refine (tsum_of_norm_bounded (hS1.mul_left 6).hasSum hrb).trans ?_
    rw [tsum_mul_left, mul_assoc]; gcongr
  have hsplit : ∑' ρ : ZeroIndex (dirichletXi χ), (1 / (s - ρ.val) + 1 / ρ.val) -
      ∑' ρ : ZeroIndex (dirichletXi χ), (1 / (s₀ - ρ.val) + 1 / ρ.val) =
      ∑' ρ, n₁ ρ + ∑' ρ, r ρ := by
    rw [← hS.tsum_sub hS₀, ← hn₁.tsum_add hr]
    exact tsum_congr fun ρ ↦ by simp only [r, g]; ring
  have hn₁eq : ∑' ρ : ZeroIndex (dirichletXi χ),
      (if |s.im - ρ.val.im| < 1 then 1 / (s - ρ.val) else 0) = ∑' ρ, n₁ ρ := rfl
  rw [hn₁eq]
  have hkey : deriv (LFunction χ) s / LFunction χ s - ∑' ρ, n₁ ρ =
      deriv (LFunction χ) s₀ / LFunction χ s₀ -
        Complex.digamma ((s + dirichletParity χ) / 2) / 2 +
        Complex.digamma ((s₀ + dirichletParity χ) / 2) / 2 + ∑' ρ, r ρ := by
    rw [hF, hF₀]
    linear_combination hsplit
  rw [hkey]
  have b0 := norm_logDeriv_LFunction_two_add χ t
  have b3 := norm_digamma_parity_le χ hσ1 hσ2 ht
  have b4 := norm_digamma_parity_le χ (z := s₀) (by rw [hs₀re]; norm_num)
    (by rw [hs₀re]) (by rw [hs₀im]; exact ht)
  rw [hs₀im] at b4
  have hL : 1 ≤ Real.log (|t| + 2) := by
    have h4 : Real.log 4 ≤ Real.log (|t| + 2) := Real.log_le_log (by norm_num) (by linarith)
    have : (1 : ℝ) ≤ Real.log 4 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      have := log_two_gt_two_thirds; push_cast; linarith
    linarith
  have hlN : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  have tri : ‖deriv (LFunction χ) s₀ / LFunction χ s₀ -
      Complex.digamma ((s + dirichletParity χ) / 2) / 2 +
      Complex.digamma ((s₀ + dirichletParity χ) / 2) / 2 + ∑' ρ, r ρ‖ ≤
      ‖deriv (LFunction χ) s₀ / LFunction χ s₀‖ +
        ‖Complex.digamma ((s + dirichletParity χ) / 2)‖ / 2 +
        ‖Complex.digamma ((s₀ + dirichletParity χ) / 2)‖ / 2 + ‖∑' ρ, r ρ‖ := by
    have e1 : ‖Complex.digamma ((s + dirichletParity χ) / 2) / 2‖ =
        ‖Complex.digamma ((s + dirichletParity χ) / 2)‖ / 2 := by rw [norm_div]; simp
    have e2 : ‖Complex.digamma ((s₀ + dirichletParity χ) / 2) / 2‖ =
        ‖Complex.digamma ((s₀ + dirichletParity χ) / 2)‖ / 2 := by rw [norm_div]; simp
    rw [← e1, ← e2]
    refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
    refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
    exact norm_sub_le _ _
  have hC0 : zetaLogDerivTwo ≤ zetaLogDerivTwo * (Real.log N + Real.log (|t| + 2)) := by
    nlinarith
  nlinarith

end NTKB
