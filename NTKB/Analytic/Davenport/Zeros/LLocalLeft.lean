/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Davenport.Zeros.LLocal

/-!
# `L'/L(s, χ)` on the line `σ = -1/2`

**Davenport, Ch. 16, p. 102, (D) (row 16-7)**, in the form needed for the contour of Ch. 19:
the local formula `L'/L(s, χ) = ∑_{|t-γ|<1} 1/(s - ρ) + O(log q(|t| + 2))` holds for
`-1 ≤ σ ≤ 2` and every `t` at which `(s + a)/2` stays away from the poles of `ψ`
(16-7 itself was stated for `|t| ≥ 2`). On `σ = -1/2` every `|s - ρ| ≥ 1/2`, so
`|L'/L(-1/2 + it, χ)| ≪ log q(|t| + 2)`.
-/

open Filter Topology Complex Set DirichletCharacter
open scoped Real

namespace NTKB

lemma logDeriv_LFunction_local_of :
    ∃ A : ℝ, 0 < A ∧ ∀ {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}, χ.IsPrimitive → N ≠ 1 →
      ∀ s : ℂ, -1 ≤ s.re → s.re ≤ 2 → (∀ m : ℕ, s + dirichletParity χ ≠ -(2 * m)) →
      ‖Complex.digamma ((s + dirichletParity χ) / 2)‖ ≤ 10 + 4 * Real.log (|s.im| + 2) →
      LFunction χ s ≠ 0 →
      ‖deriv (LFunction χ) s / LFunction χ s -
        ∑' ρ : ZeroIndex (dirichletXi χ),
          (if |s.im - ρ.val.im| < 1 then 1 / (s - ρ.val) else 0)‖ ≤
        A * (Real.log N + Real.log (|s.im| + 2)) := by
  classical
  obtain ⟨A₀, hA₀, h₀⟩ := Davenport.sum_L_zeros_inv_one_add_sq_le
  have hC := zetaLogDerivTwo_nonneg
  refine ⟨2 * (zetaLogDerivTwo + 10 + 6 * A₀), by positivity, ?_⟩
  intro N _ χ hχ hN s hσ1 hσ2 hpar_s hdig hz
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
  have hpar0 : ∀ m : ℕ, s₀ + dirichletParity χ ≠ -(2 * m) := by
    intro m h
    have := congrArg Complex.re h
    rw [Complex.add_re, hs₀re] at this
    simp at this
    linarith [dirichletParity_re_nonneg χ, (m.cast_nonneg : (0 : ℝ) ≤ m)]
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
  have hF := Davenport.logDeriv_LFunction hχ hN hH hpar_s hz
  have hF₀ := Davenport.logDeriv_LFunction hχ hN hH hpar0 hz₀
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
  have b3 := hdig
  have b4 : ‖Complex.digamma ((s₀ + dirichletParity χ) / 2)‖ ≤ 6 + 4 * Real.log (|t| + 2) := by
    set w := (s₀ + dirichletParity χ) / 2 with hw
    have ha0 := dirichletParity_re_nonneg χ
    have ha1 := dirichletParity_re_le_one χ
    have hai := dirichletParity_im χ
    have hwre : w.re = (2 + (dirichletParity χ).re) / 2 := by simp [w, hs₀re]
    have hwim : w.im = t / 2 := by simp [w, hs₀im, hai]
    have hw1 : 1 ≤ ‖w‖ := by
      have := Complex.re_le_norm w; rw [hwre] at this; linarith
    have hb := norm_digamma_le_of_half (w := w) (by rw [hwre]; linarith) (by linarith)
    have hwn : ‖w‖ ≤ |t| + 2 := by
      have := Complex.norm_le_abs_re_add_abs_im w
      rw [hwre, hwim] at this
      have h3 : |(2 + (dirichletParity χ).re) / 2| ≤ 3 / 2 := by
        rw [abs_le]; constructor <;> linarith
      have h4 : |t / 2| = |t| / 2 := by rw [abs_div, abs_two]
      linarith [abs_nonneg t]
    have hl : Real.log (‖w‖ + 1) ≤ 2 * Real.log (|t| + 2) := by
      rw [show (2 : ℝ) * Real.log (|t| + 2) = ((2 : ℕ) : ℝ) * Real.log (|t| + 2) by norm_num,
        ← Real.log_pow]
      exact Real.log_le_log (by positivity) (by nlinarith [abs_nonneg t])
    linarith
  have hL : 2 / 3 ≤ Real.log (|t| + 2) := by
    have h4 : Real.log 2 ≤ Real.log (|t| + 2) := Real.log_le_log (by norm_num)
      (by linarith [abs_nonneg t])
    have := log_two_gt_two_thirds
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
  have hsum1 : 1 ≤ 2 * (Real.log N + Real.log (|t| + 2)) := by linarith
  have hC0 : zetaLogDerivTwo ≤ zetaLogDerivTwo * (2 * (Real.log N + Real.log (|t| + 2))) := by
    nlinarith
  nlinarith


variable {N : ℕ} [NeZero N]

/-- Away from the trivial zeros, `L(s, χ)` does not vanish for `σ ≤ 0` (primitive `χ`, `q > 1`). -/
lemma LFunction_ne_zero_of_re_nonpos {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (hN : N ≠ 1)
    {s : ℂ} (hs : ∀ n : ℕ, s + dirichletParity χ ≠ -(2 * n)) (hre : s.re ≤ 0) :
    LFunction χ s ≠ 0 := by
  intro hL
  have hG : Gammaℝ (s + dirichletParity χ) ≠ 0 := by
    rw [Ne, Gammaℝ_eq_zero_iff, not_exists]; exact hs
  have hξ : dirichletXi χ s = 0 := by rw [dirichletXi_eq_mul_LFunction χ hN hG, hL, mul_zero]
  have := ((dirichletXi_eq_zero_iff hχ hN).mp hξ).2.1
  linarith

omit [NeZero N] in
lemma dirichletParity_eq_zero_or_one (χ : DirichletCharacter ℂ N) :
    dirichletParity χ = 0 ∨ dirichletParity χ = 1 := by
  classical
  unfold dirichletParity; split_ifs <;> simp

omit [NeZero N] in
/-- On `σ = -1/2`, `s + a` is never `-2n`. -/
lemma ne_trivial_of_re_eq (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : s.re = -1 / 2) (n : ℕ) :
    s + dirichletParity χ ≠ -(2 * n) := by
  intro h
  have := congrArg Complex.re h
  rcases dirichletParity_eq_zero_or_one χ with ha | ha <;> rw [ha] at this <;> simp [hs] at this
  · have : (n : ℝ) = 1 / 4 := by linarith
    have h4 : (4 * n : ℝ) = 1 := by linarith
    have : 4 * n = 1 := by exact_mod_cast h4
    omega
  · have : (n : ℝ) = -1 / 4 := by linarith
    linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]

omit [NeZero N] in
/-- `‖ψ((s + a)/2)‖ ≤ 10 + 4 log(|t| + 2)` on `σ = -1/2`. -/
lemma norm_digamma_parity_left (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : s.re = -1 / 2) :
    ‖Complex.digamma ((s + dirichletParity χ) / 2)‖ ≤ 10 + 4 * Real.log (|s.im| + 2) := by
  set w := (s + dirichletParity χ) / 2 with hw
  have ha0 := dirichletParity_re_nonneg χ
  have ha1 := dirichletParity_re_le_one χ
  have hai := dirichletParity_im χ
  have hwre : w.re = (s.re + (dirichletParity χ).re) / 2 := by simp [w]
  have hwim : w.im = s.im / 2 := by simp [w, hai]
  have hwre' : |w.re| = 1 / 4 := by
    rw [hwre, hs]
    rcases dirichletParity_eq_zero_or_one χ with ha | ha <;> rw [ha] <;> norm_num [abs_of_neg,
      abs_of_pos]
  have hpole : ∀ m : ℕ, w ≠ -m := by
    intro m h
    have := congrArg Complex.re h
    simp at this
    rw [this] at hwre'
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp at hwre'
    · have : (1 : ℝ) ≤ m := by exact_mod_cast hm
      rw [abs_neg, abs_of_nonneg (by positivity)] at hwre'
      linarith
  have hrec := Complex.digamma_apply_add_one w hpole
  have hw14 : 1 / 4 ≤ ‖w‖ := hwre'.symm.le.trans (Complex.abs_re_le_norm w)
  have hinv : ‖w⁻¹‖ ≤ 4 := by
    rw [norm_inv]; rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
  have hw1re : 0 ≤ (w + 1).re := by
    simp only [add_re, one_re]; linarith [(abs_le.mp hwre'.le).1]
  have hw1n : 1 / 2 ≤ ‖w + 1‖ := by
    have := Complex.re_le_norm (w + 1)
    simp only [add_re, one_re] at this
    linarith [(abs_le.mp hwre'.le).1]
  have hb := norm_digamma_le_of_half hw1re hw1n
  have hn : ‖w + 1‖ ≤ |s.im| + 2 := by
    have := Complex.norm_le_abs_re_add_abs_im (w + 1)
    simp only [add_re, one_re, add_im, one_im, add_zero] at this
    rw [hwim, abs_div, abs_two] at this
    have : |w.re + 1| ≤ 5 / 4 := by
      rw [abs_le]; constructor <;> linarith [(abs_le.mp hwre'.le).1, (abs_le.mp hwre'.le).2]
    linarith [abs_nonneg s.im]
  have hl : Real.log (‖w + 1‖ + 1) ≤ 2 * Real.log (|s.im| + 2) := by
    rw [show (2 : ℝ) * Real.log (|s.im| + 2) = ((2 : ℕ) : ℝ) * Real.log (|s.im| + 2) by norm_num,
      ← Real.log_pow]
    exact Real.log_le_log (by positivity) (by nlinarith [abs_nonneg s.im])
  have : Complex.digamma w = Complex.digamma (w + 1) - w⁻¹ := by rw [hrec]; ring
  rw [this]
  calc ‖Complex.digamma (w + 1) - w⁻¹‖ ≤ ‖Complex.digamma (w + 1)‖ + ‖w⁻¹‖ := norm_sub_le _ _
    _ ≤ 10 + 4 * Real.log (|s.im| + 2) := by linarith

/-- **Davenport, Ch. 16, p. 102 (row 16-7)**, consequence on `σ = -1/2`: there is an absolute `A`
with `|L'/L(-1/2 + it, χ)| ≤ A (log q + log(|t| + 2))` for primitive `χ` mod `q > 1`. -/
@[kb "davenport1980" "Ch 16, p. 102"]
theorem Davenport.norm_logDeriv_LFunction_left :
    ∃ A : ℝ, 0 < A ∧ ∀ {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}, χ.IsPrimitive → N ≠ 1 →
      ∀ s : ℂ, s.re = -1 / 2 → LFunction χ s ≠ 0 ∧
      ‖deriv (LFunction χ) s / LFunction χ s‖ ≤ A * (Real.log N + Real.log (|s.im| + 2)) := by
  classical
  obtain ⟨A₁, hA₁, h₁⟩ := logDeriv_LFunction_local_of
  obtain ⟨A₂, hA₂, h₂⟩ := Davenport.card_L_zeros_near_le
  refine ⟨A₁ + 2 * A₂, by positivity, ?_⟩
  intro N _ χ hχ hN s hs
  have hpar := ne_trivial_of_re_eq χ hs
  have hz : LFunction χ s ≠ 0 := LFunction_ne_zero_of_re_nonpos hχ hN hpar (by rw [hs]; norm_num)
  refine ⟨hz, ?_⟩
  have hloc := h₁ hχ hN s (by rw [hs]; norm_num) (by rw [hs]; norm_num) hpar
    (norm_digamma_parity_left χ hs) hz
  obtain ⟨hfin, hcard⟩ := h₂ hχ hN s.im
  have hsum : ∑' ρ : ZeroIndex (dirichletXi χ),
      (if |s.im - ρ.val.im| < 1 then 1 / (s - ρ.val) else 0) =
      ∑ ρ ∈ hfin.toFinset, (if |s.im - ρ.val.im| < 1 then 1 / (s - ρ.val) else 0) := by
    refine tsum_eq_sum fun ρ hρ ↦ ?_
    rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, abs_sub_comm] at hρ
    simp [hρ]
  have hnear : ‖∑ ρ ∈ hfin.toFinset, (if |s.im - ρ.val.im| < 1 then 1 / (s - ρ.val) else 0)‖ ≤
      hfin.toFinset.card * 2 := by
    refine (norm_sum_le _ _).trans ?_
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_le_sum fun ρ _ ↦ ?_
    split_ifs
    · rw [norm_div, norm_one]
      have hβ := (dirichletXi_zero_mem hχ hN ρ).2.1
      have : 1 / 2 ≤ ‖s - ρ.val‖ := by
        have := Complex.abs_re_le_norm (s - ρ.val)
        rw [Complex.sub_re, hs, abs_of_neg (by linarith)] at this
        linarith
      rw [div_le_iff₀ (by linarith)]; linarith
    · simp
  rw [← Set.ncard_eq_toFinset_card _ hfin] at hnear
  rw [hsum] at hloc
  have hlN : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  have hlt : 0 ≤ Real.log (|s.im| + 2) := Real.log_nonneg (by linarith [abs_nonneg s.im])
  calc ‖deriv (LFunction χ) s / LFunction χ s‖
      ≤ ‖deriv (LFunction χ) s / LFunction χ s -
          ∑ ρ ∈ hfin.toFinset, (if |s.im - ρ.val.im| < 1 then 1 / (s - ρ.val) else 0)‖ +
        ‖∑ ρ ∈ hfin.toFinset, (if |s.im - ρ.val.im| < 1 then 1 / (s - ρ.val) else 0)‖ := by
        have := norm_add_le (deriv (LFunction χ) s / LFunction χ s -
          ∑ ρ ∈ hfin.toFinset, (if |s.im - ρ.val.im| < 1 then 1 / (s - ρ.val) else 0))
          (∑ ρ ∈ hfin.toFinset, (if |s.im - ρ.val.im| < 1 then 1 / (s - ρ.val) else 0))
        rwa [sub_add_cancel] at this
    _ ≤ A₁ * (Real.log N + Real.log (|s.im| + 2)) + 2 * (A₂ * (Real.log N +
          Real.log (|s.im| + 2))) := by
        refine add_le_add hloc (hnear.trans ?_)
        linarith
    _ = (A₁ + 2 * A₂) * (Real.log N + Real.log (|s.im| + 2)) := by ring

end NTKB
