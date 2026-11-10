/- Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license. -/
import NTKB.Attr
import NTKB.Analytic.Davenport.Sieve.TypeII
import NTKB.Analytic.Davenport.Sieve.MinSum
import NTKB.Analytic.Davenport.Sieve.PolyaVinogradov
import NTKB.Analytic.Davenport.Sieve.LargeSieve
import Mathlib.NumberTheory.Chebyshev

/-!
# Vinogradov's estimate for `∑ Λ(n) e(nα)` (Davenport, Chapter 25, pp. 153–154)

If `|α - a/q| ≤ q⁻²` with `(a, q) = 1`, then
`∑_{n ≤ N} Λ(n) e(nα) ≪ (N q^{-1/2} + N^{4/5} + N^{1/2} q^{1/2}) (log N)^4`.

The proof applies the estimate (F) of Chapter 24 with `U = V = ⌊N^{2/5}⌋`. The tail sums are
geometric sums, bounded by `min(N/t, 1/‖tα‖)` (`norm_sum_Icc_exp_le`), and the row sums are
bounded by `M + 2 ∑_{l ≤ N/M} min(N/l, 1/‖lα‖)`, which is estimated by `sum_minInv_le`.
-/

open Finset Real ComplexConjugate
open scoped ArithmeticFunction.vonMangoldt

namespace NTKB.Davenport

lemma vino_distInt_neg (x : ℝ) : distInt (-x) = distInt x := by
  have h1 : distInt x ≤ distInt (-x) := by
    unfold distInt
    have := round_le x (-round (-x))
    calc |x - round x| ≤ |x - ((-round (-x) : ℤ) : ℝ)| := this
      _ = |-x - round (-x)| := by
        rw [← abs_neg]; congr 1; push_cast; ring
  have h2 : distInt (-x) ≤ distInt x := by
    unfold distInt
    have := round_le (-x) (-round x)
    calc |-x - round (-x)| ≤ |-x - ((-round x : ℤ) : ℝ)| := this
      _ = |x - round x| := by
        rw [← abs_neg]; congr 1; push_cast; ring
  exact le_antisymm h2 h1

lemma vino_minInv_neg (A x : ℝ) : minInv A (-x) = minInv A x := by
  unfold minInv; rw [vino_distInt_neg]

lemma vino_minInv_nonneg {A : ℝ} (hA : 0 ≤ A) (x : ℝ) : 0 ≤ minInv A x := by
  unfold minInv
  split_ifs with h
  · exact hA
  · exact le_min hA (one_div_nonneg.2 (abs_nonneg _))

lemma vino_minInv_mono {A A' : ℝ} (h : A ≤ A') (x : ℝ) : minInv A x ≤ minInv A' x := by
  unfold minInv
  split_ifs
  · exact h
  · exact min_le_min h le_rfl

lemma vino_two_distInt_le_abs_sin (β : ℝ) : 2 * distInt β ≤ |sin (π * β)| := by
  have hx : |β - round β| ≤ 1 / 2 := abs_sub_round β
  have hd : distInt β = |β - round β| := rfl
  have hs : |sin (π * β)| = |sin (π * (β - round β))| := by
    have : π * β = π * (β - round β) + (round β : ℤ) * π := by ring
    rw [this, Real.sin_add_int_mul_pi]
    simp [abs_mul]
  rw [hs, hd]
  generalize β - round β = x at hx ⊢
  have hπ := Real.pi_pos
  rcases le_or_gt 0 x with h | h
  · rw [abs_of_nonneg h]
    have := Real.mul_le_sin (x := π * x) (by positivity) (by
      have := (abs_le.1 hx).2; nlinarith)
    have e : 2 / π * (π * x) = 2 * x := by field_simp
    rw [e] at this
    exact this.trans (le_abs_self _)
  · rw [abs_of_neg h]
    have := Real.mul_le_sin (x := π * (-x)) (by nlinarith) (by
      have := (abs_le.1 hx).1; nlinarith)
    have e : 2 / π * (π * (-x)) = 2 * (-x) := by field_simp
    rw [e, mul_neg, mul_neg, Real.sin_neg] at this
    linarith [neg_le_abs (sin (π * x))]

lemma vino_norm_e (n : ℕ) (β : ℝ) : ‖Complex.exp (2 * π * Complex.I * (n * β))‖ = 1 := by
  have := norm_exp_two_pi_I_mul ((n : ℝ) * β)
  push_cast at this
  exact this

lemma vino_geom_aux (w w' : ℕ) {A : ℝ} (hA : 0 ≤ A) (hw : (w' : ℝ) + 1 ≤ w + A) (β : ℝ) :
    ‖∑ n ∈ Icc w w', Complex.exp (2 * π * Complex.I * (n * β))‖ ≤ minInv A β := by
  set L := w' + 1 - w with hL
  have hLA : (L : ℝ) ≤ A := by
    rcases le_or_gt w (w' + 1) with h | h
    · have : (L : ℝ) = w' + 1 - w := by rw [hL, Nat.cast_sub h]; push_cast; ring
      linarith
    · have : L = 0 := by omega
      rw [this]; simpa using hA
  have hIcc : ∑ n ∈ Icc w w', Complex.exp (2 * π * Complex.I * (n * β)) =
      Complex.exp (2 * π * Complex.I * (w * β)) *
        ∑ j ∈ range L, Complex.exp (2 * π * Complex.I * (j * β)) := by
    have : Icc w w' = Ico w (w' + 1) := by
      ext; simp only [mem_Icc, mem_Ico]; omega
    rw [this, Finset.sum_Ico_eq_sum_range, mul_sum]
    refine sum_congr rfl fun j _ ↦ ?_
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  rw [hIcc, norm_mul, vino_norm_e, one_mul]
  have h1 : ‖∑ j ∈ range L, Complex.exp (2 * π * Complex.I * (j * β))‖ ≤ L := by
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    rw [sum_congr rfl fun j _ ↦ vino_norm_e j β]
    simp
  unfold minInv
  split_ifs with hd
  · exact h1.trans hLA
  · refine le_min (h1.trans hLA) ?_
    have hdpos : 0 < distInt β := lt_of_le_of_ne (abs_nonneg _) (Ne.symm hd)
    have hs := vino_two_distInt_le_abs_sin β
    have hsne : sin (π * β) ≠ 0 := by
      intro h; rw [h, abs_zero] at hs; linarith
    have hsq := norm_sum_range_exp_sq hsne L
    have hle : ‖∑ j ∈ range L, Complex.exp (2 * π * Complex.I * (j * β))‖ ≤
        1 / |sin (π * β)| := by
      rw [le_div_iff₀ (abs_pos.2 hsne)]
      have h2 : (‖∑ j ∈ range L, Complex.exp (2 * π * Complex.I * (j * β))‖ *
          |sin (π * β)|) ^ 2 ≤ 1 := by
        rw [mul_pow, hsq, sq_abs, div_mul_cancel₀ _ (pow_ne_zero 2 hsne)]
        exact Real.sin_sq_le_one _
      by_contra hc
      push_neg at hc
      nlinarith
    calc _ ≤ 1 / |sin (π * β)| := hle
      _ ≤ 1 / distInt β := one_div_le_one_div_of_le hdpos (by linarith)

/-- **Davenport, Ch. 25, (25-3)**: a geometric sum over `[w, w']` is at most
`min(w' - w + 1, 1/‖β‖)`. -/
@[kb "davenport1980" "Ch 25, p. 153"]
theorem norm_sum_Icc_exp_le {w w' : ℕ} (hw : w ≤ w') (β : ℝ) :
    ‖∑ n ∈ Icc w w', Complex.exp (2 * π * Complex.I * (n * β))‖ ≤
      minInv ((w' : ℝ) - w + 1) β := by
  have : (w : ℝ) ≤ w' := by exact_mod_cast hw
  exact vino_geom_aux w w' (by linarith) (by linarith) β

/-- Row sum bound: `∑_{m} e(mjα) conj e(mkα)` over an interval of length `≤ M`. -/
lemma vino_row_norm_le (α : ℝ) (f : ℕ → ℂ)
    (hf : ∀ n, f n = Complex.exp (2 * π * Complex.I * (n * α))) (N M j k : ℕ)
    (hj : 1 ≤ j) (hk : 1 ≤ k) :
    ‖∑ m ∈ (Ioc M (2 * M)).filter (fun m ↦ m * j ≤ N ∧ m * k ≤ N),
      f (m * j) * conj (f (m * k))‖ ≤ minInv M (((j : ℝ) - k) * α) := by
  have hterm : ∀ m : ℕ, f (m * j) * conj (f (m * k)) =
      Complex.exp (2 * π * Complex.I * (m * ((((j : ℝ) - k) * α : ℝ) : ℂ))) := by
    intro m
    have hk' : Complex.exp (2 * π * Complex.I * (((m * k : ℕ) : ℂ) * (α : ℂ))) =
        Complex.exp (2 * π * Complex.I * ((((m * k : ℕ) : ℝ) * α : ℝ) : ℂ)) := by
      congr 1; push_cast; ring
    rw [hf, hf, hk', exp_two_pi_I_mul_conj, ← Complex.exp_add]
    congr 1; push_cast; ring
  rw [sum_congr rfl fun m _ ↦ hterm m]
  have hfil : (Ioc M (2 * M)).filter (fun m ↦ m * j ≤ N ∧ m * k ≤ N) =
      Icc (M + 1) (min (2 * M) (min (N / j) (N / k))) := by
    ext m
    simp only [mem_filter, mem_Ioc, mem_Icc]
    rw [← Nat.le_div_iff_mul_le (show 0 < j by omega),
      ← Nat.le_div_iff_mul_le (show 0 < k by omega)]
    omega
  rw [hfil]
  refine vino_geom_aux (M + 1) _ (Nat.cast_nonneg M) ?_ _
  have h1 : min (2 * M) (min (N / j) (N / k)) + 1 ≤ M + 1 + M := by
    have := min_le_left (2 * M) (min (N / j) (N / k))
    omega
  exact_mod_cast h1

lemma vino_sum_shift (g : ℕ → ℝ) (hg : ∀ l, 0 ≤ g l) (S : Finset ℕ) (φ : ℕ → ℕ)
    (hinj : ∀ x ∈ S, ∀ y ∈ S, φ x = φ y → x = y) (K : ℕ)
    (hmem : ∀ k ∈ S, φ k ∈ Icc 1 K) :
    ∑ k ∈ S, g (φ k) ≤ ∑ l ∈ Icc 1 K, g l := by
  rw [← sum_image hinj]
  refine sum_le_sum_of_subset_of_nonneg (fun l hl ↦ ?_) (fun _ _ _ ↦ hg _)
  obtain ⟨k, hk, rfl⟩ := mem_image.1 hl
  exact hmem k hk

lemma vino_row_sum {α : ℝ} {q : ℕ} (hq : 1 ≤ q) {Cs : ℝ} (hCs : 0 < Cs)
    (hs : ∀ (Nr : ℝ) (T : ℕ), 1 ≤ Nr → 1 ≤ T →
      ∑ t ∈ Icc 1 T, minInv (Nr / t) (t * α) ≤
        Cs * (Nr / q + T + q) * Real.log (2 * q * T))
    (f : ℕ → ℂ) (hf : ∀ n, f n = Complex.exp (2 * π * Complex.I * (n * α)))
    (N U V M : ℕ) (hN : 1 ≤ N) (hU : 1 ≤ U) (hV : 1 ≤ V) (hUM : U ≤ M) (hMV : M ≤ N / V)
    (j : ℕ) (hj : j ∈ Ioc V (N / M)) :
    ∑ k ∈ Ioc V (N / M), ‖∑ m ∈ (Ioc M (2 * M)).filter (fun m ↦ m * j ≤ N ∧ m * k ≤ N),
        f (m * j) * conj (f (m * k))‖ ≤
      (N : ℝ) / V + 2 * Cs * ((N : ℝ) / q + N / U + q) * Real.log (2 * q * N) := by
  set K := N / M with hK
  set g : ℕ → ℝ := fun l ↦ minInv M ((l : ℝ) * α) with hg
  have hM1 : 1 ≤ M := le_trans hU hUM
  have hg0 : ∀ l, 0 ≤ g l := fun l ↦ vino_minInv_nonneg (Nat.cast_nonneg M) _
  have hjK := mem_Ioc.1 hj
  have hK1 : 1 ≤ K := by omega
  have hpt : ∀ k ∈ Ioc V K,
      ‖∑ m ∈ (Ioc M (2 * M)).filter (fun m ↦ m * j ≤ N ∧ m * k ≤ N),
        f (m * j) * conj (f (m * k))‖ ≤
      (if k < j then g (j - k) else 0) + (if j = k then (M : ℝ) else 0) +
        (if j < k then g (k - j) else 0) := by
    intro k hk
    have hk1 : 1 ≤ k := by have := (mem_Ioc.1 hk).1; omega
    have hrow := vino_row_norm_le α f hf N M j k (by omega) hk1
    rcases lt_trichotomy k j with h | h | h
    · have e : (j : ℝ) - k = ((j - k : ℕ) : ℝ) := by rw [Nat.cast_sub h.le]
      rw [e] at hrow
      rw [if_pos h, if_neg (by omega), if_neg (by omega)]
      have : minInv M (((j - k : ℕ) : ℝ) * α) = g (j - k) := rfl
      linarith
    · subst h
      rw [if_neg (lt_irrefl _), if_pos rfl]
      have := minSum_minInv_le_A M (((k : ℝ) - k) * α)
      linarith
    · have e : ((j : ℝ) - k) * α = -(((k - j : ℕ) : ℝ) * α) := by
        rw [Nat.cast_sub h.le]; ring
      rw [e, vino_minInv_neg] at hrow
      rw [if_neg (by omega), if_neg (by omega), if_pos h]
      have : minInv M (((k - j : ℕ) : ℝ) * α) = g (k - j) := rfl
      linarith
  have hA : ∑ k ∈ Ioc V K, (if k < j then g (j - k) else 0) ≤ ∑ l ∈ Icc 1 K, g l := by
    rw [← sum_filter]
    refine vino_sum_shift g hg0 _ (fun k ↦ j - k) ?_ K ?_
    · intro x hx y hy hxy
      simp only [mem_filter, mem_Ioc] at hx hy
      omega
    · intro k hk
      simp only [mem_filter, mem_Ioc] at hk
      simp only [mem_Icc]
      omega
  have hC : ∑ k ∈ Ioc V K, (if j < k then g (k - j) else 0) ≤ ∑ l ∈ Icc 1 K, g l := by
    rw [← sum_filter]
    refine vino_sum_shift g hg0 _ (fun k ↦ k - j) ?_ K ?_
    · intro x hx y hy hxy
      simp only [mem_filter, mem_Ioc] at hx hy
      omega
    · intro k hk
      simp only [mem_filter, mem_Ioc] at hk
      simp only [mem_Icc]
      omega
  have hB : ∑ k ∈ Ioc V K, (if j = k then (M : ℝ) else 0) ≤ M := by
    rw [sum_ite_eq]
    split_ifs <;> first | exact le_rfl | exact Nat.cast_nonneg M
  -- bounding `∑ g` by `sum_minInv_le`
  have hG1 : ∑ l ∈ Icc 1 K, g l ≤ ∑ l ∈ Icc 1 K, minInv ((N : ℝ) / l) (l * α) := by
    refine sum_le_sum fun l hl ↦ ?_
    have hl' := mem_Icc.1 hl
    refine vino_minInv_mono ?_ _
    have h1 : l * M ≤ N := (Nat.le_div_iff_mul_le (by omega)).1 hl'.2
    have hlpos : (0 : ℝ) < l := by exact_mod_cast hl'.1
    rw [le_div_iff₀ hlpos]
    have : ((l * M : ℕ) : ℝ) ≤ N := by exact_mod_cast h1
    push_cast at this
    linarith
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hG2 := hs (N : ℝ) K hN1 hK1
  have hKU : (K : ℝ) ≤ (N : ℝ) / U := by
    have h1 : K ≤ N / U := Nat.div_le_div_left hUM (by omega)
    exact (Nat.cast_le.2 h1).trans Nat.cast_div_le
  have hKN : (K : ℝ) ≤ N := by exact_mod_cast Nat.div_le_self N M
  have hK1r : (1 : ℝ) ≤ K := by exact_mod_cast hK1
  have hlogK : Real.log (2 * q * K) ≤ Real.log (2 * q * N) :=
    Real.log_le_log (by positivity) (by gcongr)
  have hlogK0 : 0 ≤ Real.log (2 * q * K) := Real.log_nonneg (by nlinarith)
  have hG3 : Cs * ((N : ℝ) / q + K + q) * Real.log (2 * q * K) ≤
      Cs * ((N : ℝ) / q + N / U + q) * Real.log (2 * q * N) := by
    refine mul_le_mul (by gcongr) hlogK hlogK0 (by positivity)
  have hMV' : (M : ℝ) ≤ (N : ℝ) / V := (Nat.cast_le.2 hMV).trans Nat.cast_div_le
  calc _ ≤ ∑ k ∈ Ioc V K, ((if k < j then g (j - k) else 0) + (if j = k then (M : ℝ) else 0) +
        (if j < k then g (k - j) else 0)) := sum_le_sum hpt
    _ = _ := by rw [sum_add_distrib, sum_add_distrib]
    _ ≤ _ := by linarith

lemma vino_alg1 (c L X : ℝ) (hc : 0 ≤ c) (hL : 0 ≤ L) (hLle : L ≤ 4 * L ^ 2) :
    c * L * (3 * X ^ 2) ≤ ((12 * c + 1) * L * X) ^ 2 := by
  have h1 : c * L * (3 * X ^ 2) ≤ c * (4 * L ^ 2) * (3 * X ^ 2) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hLle hc) (by positivity)
  have h2 : 0 ≤ (144 * c ^ 2 + 12 * c + 1) * (L * X) ^ 2 := by positivity
  nlinarith

set_option maxHeartbeats 1000000 in
/-- **Davenport, Ch. 25, (2)** (Vinogradov): if `|α - a/q| ≤ q⁻²`, `(a, q) = 1`, then
`∑_{n ≤ N} Λ(n) e(nα) ≪ (N q^{-1/2} + N^{4/5} + N^{1/2} q^{1/2}) (log N)⁴`. -/
@[kb "davenport1980" "Ch 25, p. 153, (2)"]
theorem norm_sum_vonMangoldt_exp_le : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (a : ℤ) (q : ℕ), 1 ≤ q →
    IsCoprime a q → |α - a / q| ≤ 1 / (q : ℝ) ^ 2 → ∀ N : ℕ, 2 ≤ N →
    ‖∑ n ∈ Icc 1 N, (Λ n : ℂ) * Complex.exp (2 * π * Complex.I * (n * α))‖ ≤
      C * (N / √q + (N : ℝ) ^ ((4 : ℝ) / 5) + √N * √q) * Real.log N ^ 4 := by
  obtain ⟨CF, hCF, hF⟩ := norm_sum_mul_vonMangoldt_le
  obtain ⟨Cs, hCs, hsum⟩ := sum_minInv_le
  refine ⟨CF * (65 + 156 * Cs) + 112, by positivity, ?_⟩
  intro α b q hq hcop hα N hN
  have hs := hsum α b q hq hcop hα
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  set L := Real.log (N : ℝ) with hLd
  have hL : (1 : ℝ) / 2 ≤ L := by
    have := Real.log_two_gt_d9
    have h2 : Real.log 2 ≤ Real.log N := Real.log_le_log (by norm_num) hN2
    linarith
  have hL0 : 0 ≤ L := by linarith
  have hL4 : 1 ≤ 16 * L ^ 4 := by
    have : ((1 : ℝ) / 2) ^ 4 ≤ L ^ 4 := pow_le_pow_left₀ (by norm_num) hL 4
    norm_num at this; linarith
  have hL2 : L ^ 2 ≤ 4 * L ^ 4 := by
    have h2 : 1 / 4 ≤ L ^ 2 := by nlinarith
    have : 0 ≤ L ^ 2 * (4 * L ^ 2 - 1) := mul_nonneg (sq_nonneg _) (by nlinarith)
    nlinarith
  have hLle : L ≤ 4 * L ^ 2 := by nlinarith
  set s := √(q : ℝ) with hsd
  have hs1 : 1 ≤ s := by
    rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt hq1
  have hss : s * s = q := Real.mul_self_sqrt (by positivity)
  have hrN : √(N : ℝ) * √(N : ℝ) = N := Real.mul_self_sqrt hN0
  have hrN0 : 0 ≤ √(N : ℝ) := Real.sqrt_nonneg _
  set X := (N : ℝ) / s + (N : ℝ) ^ ((4 : ℝ) / 5) + √(N : ℝ) * s with hXd
  have hs0 : 0 < s := by linarith
  have hX0 : 0 ≤ X := by
    have : 0 ≤ (N : ℝ) ^ ((4 : ℝ) / 5) := Real.rpow_nonneg hN0 _
    have : 0 ≤ (N : ℝ) / s := by positivity
    have : 0 ≤ √(N : ℝ) * s := by positivity
    linarith
  have hXL : 0 ≤ X * L ^ 4 := mul_nonneg hX0 (pow_nonneg hL0 4)
  have hXL' : X ≤ 16 * L ^ 4 * X := by
    have := mul_nonneg hX0 (sub_nonneg.2 hL4)
    nlinarith
  have hCp : 0 ≤ CF * (65 + 156 * Cs) * (X * L ^ 4) := by positivity
  rcases le_or_gt q N with hqN | hqN
  · -- main case `q ≤ N`
    have hex : ∃ a : ℝ, 1 ≤ a ∧ a ^ 5 = N ∧ (N : ℝ) ^ ((4 : ℝ) / 5) = a ^ 4 := by
      refine ⟨(N : ℝ) ^ ((1 : ℝ) / 5), Real.one_le_rpow hN1 (by norm_num), ?_, ?_⟩
      · rw [← Real.rpow_natCast, ← Real.rpow_mul hN0]; norm_num
      · rw [← Real.rpow_natCast, ← Real.rpow_mul hN0]; norm_num
    obtain ⟨a, ha1, ha5, ha4⟩ := hex
    have ha0 : 0 < a := by linarith
    have hXa : X = (N : ℝ) / s + a ^ 4 + √(N : ℝ) * s := by rw [hXd, ha4]
    have hqNr : (q : ℝ) ≤ N := by exact_mod_cast hqN
    -- the parameter `u`
    obtain ⟨u, hu⟩ : ∃ u : ℕ, u = ⌊a ^ 2⌋₊ := ⟨_, rfl⟩
    have hu1 : 1 ≤ u := by
      rw [hu]
      refine Nat.le_floor ?_
      have : (1 : ℝ) ≤ a ^ 2 := one_le_pow₀ ha1
      exact_mod_cast this
    have hur : (1 : ℝ) ≤ u := by exact_mod_cast hu1
    have hu_le : (u : ℝ) ≤ a ^ 2 := by rw [hu]; exact Nat.floor_le (by positivity)
    have hu_gt : a ^ 2 < u + 1 := by rw [hu]; exact Nat.lt_floor_add_one _
    have h2u : a ^ 2 ≤ 2 * u := by linarith
    have huu : (u : ℝ) * u ≤ a ^ 4 := by nlinarith
    have huuN : u * u ≤ N := by
      have : (u : ℝ) * u ≤ N := by
        rw [← ha5]
        calc (u : ℝ) * u ≤ a ^ 4 := huu
          _ ≤ a ^ 5 := pow_le_pow_right₀ ha1 (by norm_num)
      exact_mod_cast this
    have hu_pos : (0 : ℝ) < u := by linarith
    have hqN1 : (1 : ℝ) ≤ (q : ℝ) * N := one_le_mul_of_one_le_of_one_le hq1 hN1
    have hlog2 : 0 ≤ Real.log (2 * q * N) := Real.log_nonneg (by linarith)
    have hlog3 : Real.log (2 * q * N) ≤ 3 * L := by
      have h1 : (2 * q * N : ℝ) ≤ (N : ℝ) ^ 3 := by
        calc (2 * q * N : ℝ) ≤ 2 * N * N := by
              have := mul_le_mul_of_nonneg_right hqNr hN0; linarith
          _ ≤ (N : ℝ) ^ 3 := by
              have := mul_le_mul_of_nonneg_right hN2 (mul_nonneg hN0 hN0); linarith
      calc Real.log (2 * q * N) ≤ Real.log ((N : ℝ) ^ 3) := Real.log_le_log (by positivity) h1
        _ = 3 * L := by rw [Real.log_pow, hLd]; norm_num
    have hlogB0 : 0 ≤ Real.log (2 * q * ((u * u : ℕ) : ℝ)) :=
      Real.log_nonneg (by
        push_cast
        have := one_le_mul_of_one_le_of_one_le hur hur
        have := one_le_mul_of_one_le_of_one_le hq1 this
        linarith)
    have hlogB : Real.log (2 * q * ((u * u : ℕ) : ℝ)) ≤ 3 * L := by
      refine le_trans (Real.log_le_log (by push_cast; positivity) ?_) hlog3
      have : ((u * u : ℕ) : ℝ) ≤ N := by exact_mod_cast huuN
      have h2 : (0 : ℝ) ≤ 2 * q := by positivity
      exact mul_le_mul_of_nonneg_left this h2
    -- Δ
    set Δ : ℝ := (N : ℝ) / u + 2 * Cs * ((N : ℝ) / q + N / u + q) * Real.log (2 * q * N)
      with hΔd
    have hΔ0 : 0 ≤ Δ := by
      have : 0 ≤ (N : ℝ) / u + 0 := by positivity
      have h2 : 0 ≤ 2 * Cs * ((N : ℝ) / q + N / u + q) := by positivity
      have := mul_nonneg h2 hlog2
      have h3 : 0 ≤ (N : ℝ) / u := by positivity
      rw [hΔd]; linarith
    have hf : ∀ n : ℕ, (fun n : ℕ ↦ Complex.exp (2 * π * Complex.I * (n * α))) n =
        Complex.exp (2 * π * Complex.I * (n * α)) := fun n ↦ rfl
    have htail : ∀ t ∈ Icc 1 (u * u), ∀ w ∈ Icc 1 (N / t),
        ‖∑ h ∈ Icc w (N / t), Complex.exp (2 * π * Complex.I * (((t * h : ℕ) : ℂ) * α))‖ ≤
          minInv ((N : ℝ) / t) (t * α) := by
      intro t ht w hw
      have hw' := mem_Icc.1 hw
      have e : ∑ h ∈ Icc w (N / t), Complex.exp (2 * π * Complex.I * (((t * h : ℕ) : ℂ) * α)) =
          ∑ h ∈ Icc w (N / t),
            Complex.exp (2 * π * Complex.I * (h * (((t : ℝ) * α : ℝ) : ℂ))) := by
        refine sum_congr rfl fun h _ ↦ ?_
        congr 1; push_cast; ring
      rw [e]
      refine vino_geom_aux w (N / t) (by positivity) ?_ _
      have h1 : ((N / t : ℕ) : ℝ) ≤ (N : ℝ) / t := Nat.cast_div_le
      have h2 : (1 : ℝ) ≤ w := by exact_mod_cast hw'.1
      linarith
    have hrow : ∀ M : ℕ, u ≤ M → M ≤ N / u → ∀ j ∈ Ioc u (N / M), ∑ k ∈ Ioc u (N / M),
        ‖∑ m ∈ (Ioc M (2 * M)).filter (fun m ↦ m * j ≤ N ∧ m * k ≤ N),
          Complex.exp (2 * π * Complex.I * (((m * j : ℕ) : ℂ) * α)) *
            conj (Complex.exp (2 * π * Complex.I * (((m * k : ℕ) : ℂ) * α)))‖ ≤ Δ :=
      fun M hUM hMV j hj ↦ vino_row_sum hq hCs hs
        (fun n : ℕ ↦ Complex.exp (2 * π * Complex.I * (n * α))) (fun n ↦ rfl) N u u M
        (by omega) hu1 hu1 hUM hMV j hj
    have key := hF (fun n : ℕ ↦ Complex.exp (2 * π * Complex.I * (n * α))) N u u
      (fun t ↦ minInv ((N : ℝ) / t) (t * α)) Δ (fun n ↦ (vino_norm_e n α).le) hN hu1 hu1 huuN
      (fun t ↦ vino_minInv_nonneg (by positivity) _) hΔ0 htail hrow
    have hS : ∑ n ∈ Icc 1 N, (Λ n : ℂ) * Complex.exp (2 * π * Complex.I * (n * α)) =
        ∑ n ∈ Icc 1 N, Complex.exp (2 * π * Complex.I * (n * α)) * (Λ n : ℂ) :=
      sum_congr rfl fun n _ ↦ mul_comm _ _
    rw [hS]
    refine key.trans ?_
    -- real estimates
    have hsrN : s ≤ √(N : ℝ) := Real.sqrt_le_sqrt hqNr
    have hX1 : (N : ℝ) / q ≤ (N : ℝ) / s :=
      div_le_div_of_nonneg_left hN0 hs0
        (by have := mul_le_mul_of_nonneg_left hs1 hs0.le; linarith)
    have hqX : (q : ℝ) ≤ √(N : ℝ) * s := by
      rw [← hss]; exact mul_le_mul_of_nonneg_right hsrN (by linarith)
    have hA1 : (N : ℝ) / s ≤ X := by
      have : 0 ≤ a ^ 4 := by positivity
      have : 0 ≤ √(N : ℝ) * s := by positivity
      rw [hXa]; linarith
    have hA2 : a ^ 4 ≤ X := by
      have : 0 ≤ (N : ℝ) / s := by positivity
      have : 0 ≤ √(N : ℝ) * s := by positivity
      rw [hXa]; linarith
    have hA3 : √(N : ℝ) * s ≤ X := by
      have : 0 ≤ a ^ 4 := by positivity
      have : 0 ≤ (N : ℝ) / s := by positivity
      rw [hXa]; linarith
    -- the sum of `B`
    have hB := hs (N : ℝ) (u * u) hN1 (Nat.mul_pos hu1 hu1)
    have hB' : ∑ t ∈ Icc 1 (u * u), minInv ((N : ℝ) / t) (t * α) ≤ Cs * X * (3 * L) := by
      refine hB.trans ?_
      have h1 : Cs * ((N : ℝ) / q + ((u * u : ℕ) : ℝ) + q) ≤ Cs * X := by
        refine mul_le_mul_of_nonneg_left ?_ hCs.le
        push_cast
        linarith
      exact mul_le_mul h1 hlogB hlogB0 (by positivity)
    have hT2 : L * ∑ t ∈ Icc 1 (u * u), minInv ((N : ℝ) / t) (t * α) ≤ 12 * Cs * (X * L ^ 4) := by
      calc _ ≤ L * (Cs * X * (3 * L)) := mul_le_mul_of_nonneg_left hB' hL0
        _ = 3 * Cs * X * L ^ 2 := by ring
        _ ≤ 3 * Cs * X * (4 * L ^ 4) := by
            refine mul_le_mul_of_nonneg_left hL2 (by positivity)
        _ = _ := by ring
    have hT1 : (u : ℝ) ≤ 16 * (X * L ^ 4) := by
      have : a ^ 2 ≤ a ^ 4 := pow_le_pow_right₀ ha1 (by norm_num)
      linarith
    -- Δ
    set W : ℝ := (N : ℝ) / q + a ^ 3 + q with hWd
    have hW0 : 0 ≤ W := by positivity
    have hND : (N : ℝ) / u ≤ 2 * a ^ 3 := by
      rw [div_le_iff₀ hu_pos, ← ha5]
      linarith [mul_le_mul_of_nonneg_left h2u (pow_nonneg ha0.le 3)]
    have hD1 : (N : ℝ) / q + N / u + q ≤ 2 * W := by
      have : 0 ≤ (N : ℝ) / q := by positivity
      rw [hWd]; linarith
    have hD2 : Δ ≤ (4 + 12 * Cs) * L * W := by
      have h3 : 2 * Cs * ((N : ℝ) / q + N / u + q) * Real.log (2 * q * N) ≤
          2 * Cs * (2 * W) * (3 * L) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hD1 (by positivity)) hlog3 hlog2 (by positivity)
      have h4 : (N : ℝ) / u ≤ 4 * L * W := by
        have : a ^ 3 ≤ W := by
          have : 0 ≤ (N : ℝ) / q := by positivity
          rw [hWd]; linarith
        have := mul_nonneg (by linarith : (0 : ℝ) ≤ 4 * L - 2) hW0
        linarith
      linarith [hΔd]
    have hNW : (N : ℝ) * W ≤ 3 * X ^ 2 := by
      have e1 : (N : ℝ) * ((N : ℝ) / q) = ((N : ℝ) / s) ^ 2 := by
        rw [div_pow, sq s, hss]; field_simp
      have e2 : (N : ℝ) * a ^ 3 = (a ^ 4) ^ 2 := by rw [← ha5]; ring
      have e3 : (N : ℝ) * q = (√(N : ℝ) * s) ^ 2 := by
        rw [mul_pow, sq, sq, hrN, hss]
      have p1 : ((N : ℝ) / s) ^ 2 ≤ X ^ 2 :=
        pow_le_pow_left₀ (by positivity) hA1 2
      have p2 : (a ^ 4) ^ 2 ≤ X ^ 2 := pow_le_pow_left₀ (by positivity) hA2 2
      have p3 : (√(N : ℝ) * s) ^ 2 ≤ X ^ 2 := pow_le_pow_left₀ (by positivity) hA3 2
      calc (N : ℝ) * W = (N : ℝ) * ((N : ℝ) / q) + (N : ℝ) * a ^ 3 + (N : ℝ) * q := by
            rw [hWd]; ring
        _ ≤ 3 * X ^ 2 := by rw [e1, e2, e3]; linarith
    have hc1 : 0 ≤ 4 + 12 * Cs := by positivity
    have hNΔ : (N : ℝ) * Δ ≤ ((12 * (4 + 12 * Cs) + 1) * L * X) ^ 2 := by
      calc (N : ℝ) * Δ ≤ (N : ℝ) * ((4 + 12 * Cs) * L * W) := mul_le_mul_of_nonneg_left hD2 hN0
        _ = (4 + 12 * Cs) * L * ((N : ℝ) * W) := by ring
        _ ≤ (4 + 12 * Cs) * L * (3 * X ^ 2) :=
            mul_le_mul_of_nonneg_left hNW (by positivity)
        _ ≤ ((12 * (4 + 12 * Cs) + 1) * L * X) ^ 2 := vino_alg1 _ _ _ hc1 hL0 hLle
    have hsq : √((N : ℝ) * Δ) ≤ (12 * (4 + 12 * Cs) + 1) * L * X :=
      Real.sqrt_le_iff.2 ⟨by positivity, hNΔ⟩
    have hT3 : √(N : ℝ) * L ^ 3 * √Δ ≤ (12 * (4 + 12 * Cs) + 1) * (X * L ^ 4) := by
      have : √(N : ℝ) * L ^ 3 * √Δ = L ^ 3 * √((N : ℝ) * Δ) := by
        rw [Real.sqrt_mul hN0]; ring
      rw [this]
      calc L ^ 3 * √((N : ℝ) * Δ) ≤ L ^ 3 * ((12 * (4 + 12 * Cs) + 1) * L * X) :=
            mul_le_mul_of_nonneg_left hsq (by positivity)
        _ = _ := by ring
    rw [← hXd] at *
    calc CF * ((u : ℝ) + L * ∑ t ∈ Icc 1 (u * u), minInv ((N : ℝ) / t) (t * α) +
          √(N : ℝ) * L ^ 3 * √Δ)
        ≤ CF * ((16 + 12 * Cs + (12 * (4 + 12 * Cs) + 1)) * (X * L ^ 4)) := by
          refine mul_le_mul_of_nonneg_left ?_ hCF.le
          linarith
      _ ≤ _ := by linarith [hXL]
  · -- trivial case `q > N`
    have hS : ‖∑ n ∈ Icc 1 N, (Λ n : ℂ) * Complex.exp (2 * π * Complex.I * (n * α))‖ ≤
        (Real.log 4 + 4) * N := by
      have hpsi : Chebyshev.psi (N : ℝ) = ∑ n ∈ Icc 1 N, Λ n := by
        unfold Chebyshev.psi
        rw [Nat.floor_natCast]
        refine sum_congr ?_ fun _ _ ↦ rfl
        ext n; simp only [mem_Ioc, mem_Icc]; omega
      calc _ ≤ ∑ n ∈ Icc 1 N, ‖(Λ n : ℂ) * Complex.exp (2 * π * Complex.I * (n * α))‖ :=
            norm_sum_le _ _
        _ = ∑ n ∈ Icc 1 N, Λ n := by
            refine sum_congr rfl fun n _ ↦ ?_
            rw [norm_mul, vino_norm_e, mul_one, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
        _ = Chebyshev.psi N := hpsi.symm
        _ ≤ _ := Chebyshev.psi_le_const_mul_self hN0
    have hlog4 : Real.log 4 ≤ 3 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num)
      linarith
    have hqNr : (N : ℝ) ≤ q := by exact_mod_cast hqN.le
    have hNs : (N : ℝ) ≤ √(N : ℝ) * s := by
      calc (N : ℝ) = √(N : ℝ) * √(N : ℝ) := hrN.symm
        _ ≤ √(N : ℝ) * s := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hqNr) hrN0
    have hXs : √(N : ℝ) * s ≤ X := by
      have : 0 ≤ (N : ℝ) ^ ((4 : ℝ) / 5) := Real.rpow_nonneg hN0 _
      have : 0 ≤ (N : ℝ) / s := by positivity
      rw [hXd]; linarith
    nlinarith

end NTKB.Davenport
