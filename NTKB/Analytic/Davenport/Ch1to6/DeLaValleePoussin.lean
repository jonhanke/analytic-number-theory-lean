/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Davenport.Siegel.Hecke

/-!
# De la Vallée Poussin's proof that `L(1, χ) ≠ 0` for real `χ` (Davenport, Chapter 4, pp. 33–34)

Mathlib proves `L(1, χ) ≠ 0` (`DirichletCharacter.LFunction_apply_one_ne_zero`) by a different
route. This file follows de la Vallée Poussin's argument as Davenport gives it. Suppose `χ ≠ χ₀` is
real and `L(1, χ) = 0`. Then
`ψ(s) = ζ(s) L(s, χ) / ζ(2s)`
(Davenport writes `L(s, χ) L(s, χ₀) / L(2s, χ₀)`; with `ζ` in place of `L(·, χ₀)` the argument is the
same) is regular for `σ > 1/2`, since the zero of `L(s, χ)` at `1` cancels the pole of `ζ(s)` and
`ζ(2s) ≠ 0` for `σ ≥ 1/2`, `s ≠ 1/2`. For `σ > 1` it is the Dirichlet series of
`a_n = ∑_{d ∣ n} μ(d)² χ(n/d) ≥ 0`, `a_1 = 1` (`deLaValleePoussinCoeff`, `…_nonneg`,
`hasSum_deLaValleePoussinCoeff`). Its Taylor series at `s = 2` has radius at least `3/2` and
coefficients `(-1)^m ψ^{(m)}(2) ≥ 0`, so `ψ(σ) ≥ ψ(2) ≥ 1` for `1/2 < σ < 2`
(`one_le_deLaValleePoussin`); but `ψ(σ) → 0` as `σ → 1/2+`, since `ζ(2σ)` has a pole there
(`tendsto_deLaValleePoussin_zero`). Hence `L(1, χ) ≠ 0` (`LFunction_one_ne_zero_of_isQuadratic`).
-/

open Complex Filter Topology Set Metric
open scoped ArithmeticFunction.Moebius ComplexOrder Nat

namespace NTKB.Davenport

variable {N : ℕ} [NeZero N]

/-- The coefficients `a_n = ∑_{d ∣ n} μ(d)² χ(n/d)` of `ζ(s) L(s, χ)/ζ(2s)`. -/
noncomputable def deLaValleePoussinCoeff (χ : DirichletCharacter ℂ N) (n : ℕ) : ℂ :=
  ∑ d ∈ n.divisors, (((μ d : ℤ) ^ 2 : ℤ) : ℂ) * χ (n / d : ℕ)

/-- squarefree indicator `μ²` as an arithmetic function. -/
noncomputable def mu2 : ArithmeticFunction ℂ :=
  ⟨fun n ↦ if n = 0 then 0 else (((μ n : ℤ) ^ 2 : ℤ) : ℂ), by simp⟩

lemma mu2_apply {n : ℕ} (hn : n ≠ 0) : mu2 n = (((μ n : ℤ) ^ 2 : ℤ) : ℂ) := by
  simp [mu2, hn]

lemma isMultiplicative_mu2 : mu2.IsMultiplicative := by
  refine ArithmeticFunction.IsMultiplicative.iff_ne_zero.mpr ⟨?_, fun {m} {n} hm hn hmn ↦ ?_⟩
  · simp [mu2_apply]
  · rw [mu2_apply hm, mu2_apply hn, mu2_apply (mul_ne_zero hm hn),
      ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hmn]
    push_cast; ring

lemma mu2_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) :
    mu2 (p ^ k) = if k ≤ 1 then 1 else 0 := by
  rw [mu2_apply (pow_ne_zero _ hp.ne_zero)]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · rw [ArithmeticFunction.moebius_apply_prime_pow hp hk.ne']
    by_cases h1 : k = 1
    · simp [h1]
    · simp [h1, show ¬ k ≤ 1 by omega]

/-- the arithmetic function `a = μ² * χ`. -/
noncomputable def dlvpFun (χ : DirichletCharacter ℂ N) : ArithmeticFunction ℂ :=
  mu2 * _root_.toArithmeticFunction (χ ·)

omit [NeZero N] in
lemma dlvpFun_eq (χ : DirichletCharacter ℂ N) (n : ℕ) :
    dlvpFun χ n = deLaValleePoussinCoeff χ n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [deLaValleePoussinCoeff]
  rw [dlvpFun, ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal
    (fun i j ↦ mu2 i * _root_.toArithmeticFunction (χ ·) j), deLaValleePoussinCoeff]
  refine Finset.sum_congr rfl fun d hd ↦ ?_
  have hd0 : d ≠ 0 := (Nat.pos_of_mem_divisors hd).ne'
  have hn' : n / d ≠ 0 := (Nat.div_pos (Nat.divisor_le hd) (Nat.pos_of_ne_zero hd0)).ne'
  rw [mu2_apply hd0, _root_.toArithmeticFunction, ArithmeticFunction.coe_mk, if_neg hn']

omit [NeZero N] in
lemma isMultiplicative_dlvpFun (χ : DirichletCharacter ℂ N) : (dlvpFun χ).IsMultiplicative :=
  isMultiplicative_mu2.mul (DirichletCharacter.isMultiplicative_toArithmeticFunction χ)

lemma dlvpFun_prime_pow (χ : DirichletCharacter ℂ N) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    dlvpFun χ (p ^ (k + 1)) = χ p ^ (k + 1) + χ p ^ k := by
  rw [dlvpFun_eq, deLaValleePoussinCoeff, Nat.sum_divisors_prime_pow hp,
    Finset.sum_range_succ', Finset.sum_range_succ']
  have h0 : ∑ i ∈ Finset.range k, (((μ (p ^ (i + 1 + 1)) : ℤ) ^ 2 : ℤ) : ℂ) *
      χ ((p ^ (k + 1) / p ^ (i + 1 + 1) : ℕ)) = 0 := by
    refine Finset.sum_eq_zero fun i _ ↦ ?_
    rw [ArithmeticFunction.moebius_apply_prime_pow hp (by omega)]
    simp
  rw [h0]
  have e1 : p ^ (k + 1) / p ^ (0 + 1) = p ^ k := by
    rw [Nat.pow_div (by omega) hp.pos]; simp
  have e2 : p ^ (k + 1) / p ^ 0 = p ^ (k + 1) := by simp
  rw [e1, e2, ArithmeticFunction.moebius_apply_prime_pow hp (by omega)]
  simp [map_pow]
  ring


lemma dlvpFun_nonneg {χ : DirichletCharacter ℂ N} (hχ : χ.IsQuadratic) (n : ℕ) :
    0 ≤ dlvpFun χ n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [ArithmeticFunction.IsMultiplicative.multiplicative_factorization (dlvpFun χ) (isMultiplicative_dlvpFun χ) hn]
  refine Finset.prod_nonneg fun p hp ↦ ?_
  have hpp := Nat.prime_of_mem_primeFactors hp
  rcases (n.factorization p).eq_zero_or_pos with h0 | hpos
  · simp [h0, (isMultiplicative_dlvpFun χ).map_one]
  obtain ⟨k, hk⟩ : ∃ k, n.factorization p = k + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hpos).symm⟩
  simp only [hk]
  rw [dlvpFun_prime_pow χ hpp]
  rcases hχ p with h | h | h
  · rw [h]; rcases k with _ | k <;> simp
  · rw [h]; simp only [one_pow]; norm_num
  · rw [h, pow_succ]; simp

/-- the indicator of the nonzero squares. -/
noncomputable def sqInd : ArithmeticFunction ℂ :=
  ⟨fun n ↦ if n ≠ 0 ∧ IsSquare n then 1 else 0, by simp⟩

lemma sqInd_apply (n : ℕ) : sqInd n = if n ≠ 0 ∧ IsSquare n then 1 else 0 := rfl

lemma isSquare_mul_iff_of_coprime {m n : ℕ} (h : m.Coprime n) :
    IsSquare (m * n) ↔ IsSquare m ∧ IsSquare n := by
  constructor
  · rintro ⟨r, hr⟩
    have hr' : m * n = r ^ 2 := by rw [hr]; ring
    have hu : IsUnit (gcd m n) := by rw [Nat.isUnit_iff]; exact h
    obtain ⟨a, ha⟩ := exists_eq_pow_of_mul_eq_pow hu hr'
    obtain ⟨b, hb⟩ := exists_eq_pow_of_mul_eq_pow (a := n) (b := m) (by
      rw [Nat.isUnit_iff]; exact h.symm) (by rw [mul_comm]; exact hr')
    exact ⟨⟨a, by rw [ha]; ring⟩, ⟨b, by rw [hb]; ring⟩⟩
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    exact ⟨a * b, by rw [ha, hb]; ring⟩

lemma isSquare_prime_pow_iff {p : ℕ} (hp : p.Prime) (k : ℕ) : IsSquare (p ^ k) ↔ Even k := by
  constructor
  · rintro ⟨r, hr⟩
    have hd : r ∣ p ^ k := ⟨r, hr⟩
    obtain ⟨a, -, rfl⟩ := (Nat.dvd_prime_pow hp).mp hd
    rw [← pow_add] at hr
    have := Nat.pow_right_injective hp.two_le hr
    exact ⟨a, this⟩
  · intro h; exact h.isSquare_pow p

lemma sqInd_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) :
    sqInd (p ^ k) = if Even k then 1 else 0 := by
  rw [sqInd_apply]
  simp [hp.ne_zero, isSquare_prime_pow_iff hp]

lemma isMultiplicative_sqInd : sqInd.IsMultiplicative := by
  refine ArithmeticFunction.IsMultiplicative.iff_ne_zero.mpr ⟨by simp [sqInd_apply], fun {m} {n} hm hn hmn ↦ ?_⟩
  simp only [sqInd_apply, isSquare_mul_iff_of_coprime hmn, ne_eq, mul_eq_zero, hm, hn, or_self,
    not_false_eq_true, true_and]
  by_cases h1 : IsSquare m <;> by_cases h2 : IsSquare n <;> simp [h1, h2]

lemma sqInd_mul_mu2 : sqInd * mu2 = ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℂ) := by
  rw [ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers _
    (isMultiplicative_sqInd.mul isMultiplicative_mu2) _
    (ArithmeticFunction.isMultiplicative_zeta.natCast)]
  intro p k hp
  rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal
    (fun i j ↦ sqInd i * mu2 j), Nat.sum_divisors_prime_pow hp]
  have hz : ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℂ) (p ^ k) = 1 := by
    simp [hp.ne_zero]
  rw [hz]
  have hcongr : ∀ i ∈ Finset.range (k + 1), sqInd (p ^ i) * mu2 (p ^ k / p ^ i) =
      sqInd (p ^ i) * mu2 (p ^ (k - i)) := fun i hi ↦ by
    rw [Nat.pow_div (by simpa [Nat.lt_succ_iff] using hi) hp.pos]
  rw [Finset.sum_congr rfl hcongr]
  rcases k with _ | _ | k
  · simp only [zero_add, Finset.sum_range_one]
    simp [isMultiplicative_sqInd.map_one, isMultiplicative_mu2.map_one]
  · rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero,
      sqInd_prime_pow hp, sqInd_prime_pow hp, mu2_prime_pow hp, mu2_prime_pow hp]
    norm_num
  · rw [Finset.sum_range_succ, Finset.sum_range_succ]
    have h0 : ∑ i ∈ Finset.range (k + 1), sqInd (p ^ i) * mu2 (p ^ (k + 1 + 1 - i)) = 0 := by
      refine Finset.sum_eq_zero fun i hi ↦ ?_
      rw [mu2_prime_pow hp, if_neg (by have := Finset.mem_range.mp hi; omega)]
      simp
    rw [h0, mu2_prime_pow hp, mu2_prime_pow hp, sqInd_prime_pow hp, sqInd_prime_pow hp]
    simp only [Nat.sub_self, show k + 1 + 1 - (k + 1) = 1 by omega,
      show k + 1 + 1 - (k + 1 + 1) = 0 by omega, zero_add]
    rcases Nat.even_or_odd k with he | ho
    · have : ¬ Even (k + 1) := by simpa [Nat.even_add_one] using he
      simp [he, this, Nat.even_add_one]
    · have : Even (k + 1) := ho.add_one
      have h2 : ¬ Even k := Nat.not_even_iff_odd.mpr ho
      simp [this, h2, Nat.even_add_one]


lemma LSeriesHasSum_sqInd {s : ℂ} (hs : 1 < s.re) :
    LSeriesHasSum (fun n ↦ sqInd n) s (riemannZeta (2 * s)) := by
  have h2 : 1 < (2 * s).re := by simp; linarith
  have hz := ArithmeticFunction.LSeriesHasSum_zeta h2
  unfold LSeriesHasSum at hz ⊢
  have hinj : Function.Injective (fun m : ℕ ↦ m ^ 2) := fun a b h ↦ by
    simpa using Nat.pow_left_injective (n := 2) (by norm_num) h
  rw [← hinj.hasSum_iff]
  · convert hz using 1
    ext m
    rcases eq_or_ne m 0 with rfl | hm
    · simp [LSeries.term]
    · have hm2 : m ^ 2 ≠ 0 := pow_ne_zero _ hm
      have hsq : sqInd (m ^ 2) = 1 := by
        rw [sqInd_apply, if_pos ⟨hm2, m, by ring⟩]
      simp only [Function.comp, LSeries.term_of_ne_zero hm2, LSeries.term_of_ne_zero hm, hsq]
      simp [ArithmeticFunction.zeta_apply, hm]
      rw [two_mul, Complex.cpow_add _ _ (Nat.cast_ne_zero.mpr hm),
        ← Complex.natCast_mul_natCast_cpow, pow_two]
  · intro n hn
    rw [LSeries.term_def]
    split_ifs with h0
    · rfl
    · have : ¬ IsSquare n := fun ⟨r, hr⟩ ↦ hn ⟨r, by rw [hr]; ring⟩
      simp [sqInd_apply, this]


lemma norm_mu2_le (n : ℕ) : ‖mu2 n‖ ≤ 1 := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [mu2_apply hn]
  have := ArithmeticFunction.moebius_sq (n := n)
  rw [this]
  split_ifs <;> simp

/-- `a_1 = 1`. -/
theorem deLaValleePoussinCoeff_one (χ : DirichletCharacter ℂ N) :
    deLaValleePoussinCoeff χ 1 = 1 := by
  rw [← dlvpFun_eq]
  exact (isMultiplicative_dlvpFun χ).map_one

/-- **Davenport, Ch. 4, p. 34**: `a_n ≥ 0` for real `χ`. -/
@[kb "davenport1980" "Ch 4, p. 34"]
theorem deLaValleePoussinCoeff_nonneg {χ : DirichletCharacter ℂ N} (hχ : χ.IsQuadratic) (n : ℕ) :
    0 ≤ deLaValleePoussinCoeff χ n := by
  rw [← dlvpFun_eq]
  exact dlvpFun_nonneg hχ n

/-- **Davenport, Ch. 4, p. 34**: for `σ > 1`, `ζ(s) L(s, χ) = ζ(2s) ∑ a_n n^{-s}`. -/
@[kb "davenport1980" "Ch 4, p. 34"]
theorem hasSum_deLaValleePoussinCoeff (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    LSeriesHasSum (deLaValleePoussinCoeff χ) s
      (riemannZeta s * χ.LFunction s / riemannZeta (2 * s)) := by
  have hm2 : LSeriesSummable (fun n ↦ mu2 n) s :=
    LSeriesSummable_of_bounded_of_one_lt_re (m := 1) (fun n _ ↦ norm_mu2_le n) hs
  have hχ : LSeriesSummable (fun n ↦ toArithmeticFunction (χ ·) n) s :=
    LSeriesSummable_of_bounded_of_one_lt_re (m := 1) (fun n hn ↦ by
      simp [toArithmeticFunction, hn, χ.norm_le_one]) hs
  have hχv : LSeries (fun n ↦ toArithmeticFunction (χ ·) n) s = χ.LFunction s := by
    rw [DirichletCharacter.LFunction_eq_LSeries χ hs]
    exact LSeries_congr (fun {n} hn ↦ by simp [toArithmeticFunction, hn]) s
  have h1 := ArithmeticFunction.LSeriesHasSum_mul hm2.LSeriesHasSum
    (hχv ▸ hχ.LSeriesHasSum)
  have h2 := ArithmeticFunction.LSeriesHasSum_mul (LSeriesHasSum_sqInd hs) hm2.LSeriesHasSum
  rw [sqInd_mul_mu2] at h2
  have h3 := ArithmeticFunction.LSeriesHasSum_zeta hs
  have h2' : LSeriesHasSum (fun n ↦ ((ArithmeticFunction.zeta n : ℕ) : ℂ)) s
      (riemannZeta (2 * s) * LSeries (fun n ↦ mu2 n) s) := by
    convert h2 using 2 with n
    exact (ArithmeticFunction.natCoe_apply (f := ArithmeticFunction.zeta) (x := n)).symm
  have h4 : riemannZeta s = riemannZeta (2 * s) * LSeries (fun n ↦ mu2 n) s :=
    (h3.unique h2')
  have h5 : riemannZeta (2 * s) ≠ 0 := riemannZeta_ne_zero_of_one_lt_re (by simp; linarith)
  have h6 : riemannZeta s * χ.LFunction s / riemannZeta (2 * s) =
      LSeries (fun n ↦ mu2 n) s * χ.LFunction s := by
    rw [h4]; field_simp
  rw [h6]
  have : (deLaValleePoussinCoeff χ) = fun n ↦ (mu2 * toArithmeticFunction (χ ·)) n := by
    funext n; exact (dlvpFun_eq χ n).symm
  rw [this]
  exact h1


lemma abscissa_deLaValleePoussinCoeff_le (χ : DirichletCharacter ℂ N) :
    LSeries.abscissaOfAbsConv (fun n ↦ deLaValleePoussinCoeff χ n) ≤ 1 := by
  refine LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy ↦ ?_
  exact (hasSum_deLaValleePoussinCoeff χ (s := (y : ℂ)) (by simpa using hy)).LSeriesSummable

/-- `ψ(s) = H(s)/ζ(2s)`, where `H = ζ L + dslope L 1` is entire. -/
noncomputable def dlvpPsi (χ : DirichletCharacter ℂ N) (s : ℂ) : ℂ :=
  heckeH χ s / riemannZeta (2 * s)

lemma dlvpPsi_eq {χ : DirichletCharacter ℂ N} (h0 : χ.LFunction 1 = 0) {s : ℂ} (hs : s ≠ 1) :
    dlvpPsi χ s = riemannZeta s * χ.LFunction s / riemannZeta (2 * s) := by
  rw [dlvpPsi, heckeH_eq hs, heckeF, h0]
  simp

lemma dlvpPsi_eq_LSeries {χ : DirichletCharacter ℂ N} (h0 : χ.LFunction 1 = 0) {s : ℂ}
    (hs : 1 < s.re) :
    dlvpPsi χ s = LSeries (fun n ↦ deLaValleePoussinCoeff χ n) s := by
  have hs1 : s ≠ 1 := by
    rintro rfl; simp at hs
  rw [dlvpPsi_eq h0 hs1]
  exact (hasSum_deLaValleePoussinCoeff χ hs).LSeries_eq.symm

lemma re_gt_half_of_mem_ball {s : ℂ} (hs : s ∈ ball (2 : ℂ) (3 / 2)) : 1 / 2 < s.re := by
  rw [mem_ball, dist_eq_norm] at hs
  have h1 : |s.re - 2| < 3 / 2 :=
    lt_of_le_of_lt (by simpa using Complex.abs_re_le_norm (s - 2)) hs
  rw [abs_lt] at h1
  linarith [h1.1]

lemma differentiableOn_dlvpPsi {χ : DirichletCharacter ℂ N} (h : χ ≠ 1) :
    DifferentiableOn ℂ (dlvpPsi χ) (ball (2 : ℂ) (3 / 2)) := by
  intro s hs
  have hre := re_gt_half_of_mem_ball hs
  have h2s : 1 < (2 * s).re := by simp; linarith
  have hne : 2 * s ≠ 1 := by
    intro e; rw [e] at h2s; simp at h2s
  refine ((differentiable_heckeH h s).differentiableWithinAt).div ?_
    (riemannZeta_ne_zero_of_one_lt_re h2s)
  exact ((differentiableAt_riemannZeta hne).comp s
    (differentiableAt_id.const_mul (2 : ℂ))).differentiableWithinAt

lemma iteratedDeriv_dlvpPsi_alternating {χ : DirichletCharacter ℂ N} (hq : χ.IsQuadratic)
    (h0 : χ.LFunction 1 = 0) (m : ℕ) :
    0 ≤ (-1) ^ m * iteratedDeriv m (dlvpPsi χ) 2 := by
  have hU : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const continuous_re
  have heq : EqOn (dlvpPsi χ) (LSeries (fun n ↦ deLaValleePoussinCoeff χ n))
      {s : ℂ | 1 < s.re} := fun s hs ↦ dlvpPsi_eq_LSeries h0 hs
  have h2 : (2 : ℂ) ∈ {s : ℂ | 1 < s.re} := by show (1 : ℝ) < (2 : ℂ).re; norm_num
  rw [heq.iteratedDeriv_of_isOpen hU m h2]
  have := LSeries.iteratedDeriv_alternating (a := fun n ↦ deLaValleePoussinCoeff χ n)
    (fun n ↦ deLaValleePoussinCoeff_nonneg hq n) (x := 2)
    ((abscissa_deLaValleePoussinCoeff_le χ).trans_lt
      (by exact_mod_cast (show (1 : ℝ) < 2 by norm_num))) m
  simpa using this

lemma one_le_dlvpPsi_two {χ : DirichletCharacter ℂ N} (hq : χ.IsQuadratic)
    (h0 : χ.LFunction 1 = 0) : 1 ≤ dlvpPsi χ 2 := by
  have hs : 1 < (2 : ℂ).re := by simp
  have h := hasSum_deLaValleePoussinCoeff χ hs
  rw [dlvpPsi_eq h0 (by norm_num)]
  have hnn : ∀ n, 0 ≤ LSeries.term (fun n ↦ deLaValleePoussinCoeff χ n) 2 n :=
    fun n ↦ LSeries.term_nonneg (deLaValleePoussinCoeff_nonneg hq n) 2
  have h1 : LSeries.term (fun n ↦ deLaValleePoussinCoeff χ n) 2 1 = 1 := by
    simp [LSeries.term, deLaValleePoussinCoeff_one]
  rw [← h1]
  exact le_hasSum h 1 (fun j _ ↦ hnn j)

/-- **Davenport, Ch. 4, p. 34**: if `L(1, χ) = 0` for real `χ ≠ χ₀`, then
`ψ(σ) = ζ(σ) L(σ, χ)/ζ(2σ) ≥ 1` for `1/2 < σ < 1`. -/
@[kb "davenport1980" "Ch 4, p. 34"]
theorem one_le_deLaValleePoussin {χ : DirichletCharacter ℂ N} (hq : χ.IsQuadratic) (hχ : χ ≠ 1)
    (h0 : χ.LFunction 1 = 0) {σ : ℝ} (hσ : 1 / 2 < σ) (hσ1 : σ < 1) :
    1 ≤ (riemannZeta σ * χ.LFunction σ / riemannZeta (2 * σ)).re := by
  set t : ℝ := 2 - σ with ht
  have hσt : (σ : ℂ) - 2 = -(t : ℂ) := by rw [ht]; push_cast; ring
  have hmem : (σ : ℂ) ∈ ball (2 : ℂ) (3 / 2) := by
    rw [mem_ball, dist_eq_norm, show (σ : ℂ) - 2 = ((σ - 2 : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith)]
    linarith
  have hT := Complex.hasSum_taylorSeries_on_ball (differentiableOn_dlvpPsi hχ) hmem
  set e : ℕ → ℝ := fun n ↦ ((-1) ^ n * iteratedDeriv n (dlvpPsi χ) 2).re with he
  have he0 : ∀ n, 0 ≤ e n := fun n ↦
    (Complex.le_def.mp (iteratedDeriv_dlvpPsi_alternating hq h0 n)).1
  have hfre : ∀ n, ((n ! : ℂ)⁻¹ • ((σ : ℂ) - 2) ^ n • iteratedDeriv n (dlvpPsi χ) 2).re =
      t ^ n / (n ! : ℝ) * e n := by
    intro n
    have : (n ! : ℂ)⁻¹ • ((σ : ℂ) - 2) ^ n • iteratedDeriv n (dlvpPsi χ) 2 =
        (((t ^ n / (n ! : ℝ) : ℝ)) : ℂ) * ((-1) ^ n * iteratedDeriv n (dlvpPsi χ) 2) := by
      simp only [smul_eq_mul]
      rw [hσt, neg_pow]
      push_cast
      ring
    rw [this, Complex.re_ofReal_mul]
  have hre := Complex.hasSum_re hT
  have hnn : ∀ j ≠ 0, 0 ≤ ((j ! : ℂ)⁻¹ • ((σ : ℂ) - 2) ^ j •
      iteratedDeriv j (dlvpPsi χ) 2).re := fun j _ ↦ by
    rw [hfre]
    have : 0 < t := by rw [ht]; linarith
    exact mul_nonneg (by positivity) (he0 j)
  have hle := le_hasSum hre 0 hnn
  rw [hfre 0] at hle
  have hσ1' : (σ : ℂ) ≠ 1 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have h2 : 1 ≤ e 0 := by
    have := one_le_dlvpPsi_two hq h0
    simp only [he, pow_zero, one_mul, iteratedDeriv_zero]
    exact (Complex.le_def.mp this).1
  have : t ^ 0 / ((0 : ℕ) ! : ℝ) * e 0 = e 0 := by simp
  rw [this, dlvpPsi_eq h0 hσ1'] at hle
  linarith

/-- **Davenport, Ch. 4, p. 34**: `ζ(σ) L(σ, χ)/ζ(2σ) → 0` as `σ → 1/2+` (`χ ≠ χ₀`). -/
@[kb "davenport1980" "Ch 4, p. 34"]
theorem tendsto_deLaValleePoussin_zero {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) :
    Tendsto (fun σ : ℝ ↦ riemannZeta σ * χ.LFunction σ / riemannZeta (2 * σ)) (𝓝[>] (1 / 2))
      (𝓝 0) := by
  have h12 : ((1 / 2 : ℝ) : ℂ) ≠ 1 := by
    intro h; have := congrArg Complex.re h; norm_num at this
  have hc : ContinuousAt (fun s : ℂ ↦ riemannZeta s * χ.LFunction s) ((1 / 2 : ℝ) : ℂ) :=
    (differentiableAt_riemannZeta h12).continuousAt.mul
      ((DirichletCharacter.differentiable_LFunction hχ) _).continuousAt
  have hnum : Tendsto (fun σ : ℝ ↦ riemannZeta σ * χ.LFunction σ) (𝓝[>] (1 / 2))
      (𝓝 (riemannZeta ((1 / 2 : ℝ) : ℂ) * χ.LFunction ((1 / 2 : ℝ) : ℂ))) :=
    (hc.comp Complex.continuous_ofReal.continuousAt).tendsto.mono_left nhdsWithin_le_nhds
  have hlin : Tendsto (fun σ : ℝ ↦ 2 * (σ : ℂ)) (𝓝[>] (1 / 2)) (𝓝 1) := by
    have : Tendsto (fun σ : ℝ ↦ 2 * (σ : ℂ)) (𝓝 (1 / 2)) (𝓝 (2 * ((1 / 2 : ℝ) : ℂ))) :=
      (continuous_const.mul Complex.continuous_ofReal).tendsto _
    have e : (2 : ℂ) * ((1 / 2 : ℝ) : ℂ) = 1 := by push_cast; ring
    rw [e] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hmap : Tendsto (fun σ : ℝ ↦ 2 * (σ : ℂ)) (𝓝[>] (1 / 2)) (𝓝[≠] 1) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨hlin, ?_⟩
    refine eventually_nhdsWithin_of_forall fun σ hσ ↦ ?_
    intro h
    have := congrArg Complex.re h
    simp at this
    have hσ' : (1 / 2 : ℝ) < σ := hσ
    linarith
  have hg := riemannZeta_residue_one.comp hmap
  have hlin0 : Tendsto (fun σ : ℝ ↦ 2 * (σ : ℂ) - 1) (𝓝[>] (1 / 2)) (𝓝 0) := by
    simpa using hlin.sub_const 1
  have hden : Tendsto (fun σ : ℝ ↦ (riemannZeta (2 * σ))⁻¹) (𝓝[>] (1 / 2)) (𝓝 0) := by
    have h1 := hlin0.mul (hg.inv₀ one_ne_zero)
    rw [inv_one, mul_one] at h1
    refine h1.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    have hσ' : (1 / 2 : ℝ) < σ := hσ
    have hne : 2 * (σ : ℂ) - 1 ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      simp at this
      linarith
    simp only [Function.comp_apply]
    rw [mul_inv, ← mul_assoc, mul_inv_cancel₀ hne, one_mul]
  have := hnum.mul hden
  simpa [div_eq_mul_inv] using this

/-- **De la Vallée Poussin (Davenport, Ch. 4, pp. 33–34)**: `L(1, χ) ≠ 0` for every real
character `χ ≠ χ₀`. -/
@[kb "davenport1980" "Ch 4, p. 34"]
theorem LFunction_one_ne_zero_of_isQuadratic {χ : DirichletCharacter ℂ N} (hq : χ.IsQuadratic)
    (hχ : χ ≠ 1) : χ.LFunction 1 ≠ 0 := by
  intro h0
  have hlim := (Complex.continuous_re.tendsto (0 : ℂ)).comp (tendsto_deLaValleePoussin_zero hχ)
  have hev : ∀ᶠ σ : ℝ in 𝓝[>] (1 / 2), 1 ≤ (riemannZeta σ * χ.LFunction σ /
      riemannZeta (2 * σ)).re := by
    filter_upwards [Ioo_mem_nhdsGT (show (1 / 2 : ℝ) < 1 by norm_num)] with σ hσ
    exact one_le_deLaValleePoussin hq hχ h0 hσ.1 hσ.2
  have := ge_of_tendsto hlim hev
  simp at this
  norm_num at this


end NTKB.Davenport
