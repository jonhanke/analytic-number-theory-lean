/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Apostol.Zeta.HurwitzEuler
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Bounds for `|ζ(s, a)|` (Apostol, Theorem 12.23 (a), (b))

For `0 < a ≤ 1`, `s = σ + it`:

* (a) (29): if `δ > 0` and `σ ≥ 1 + δ`, then `|ζ(s,a) - a^{-s}| ≤ ζ(1 + δ)`;
* (b) (30): if `0 < δ < 1` there is `A(δ)` (independent of `s` and `a`) with
  `|ζ(s,a) - a^{-s}| ≤ A(δ) |t|^δ` for `1 - δ ≤ σ ≤ 2`, `|t| ≥ 1`.

Proof of (b) as in Apostol: the representation of Theorem 12.21 with `N = 1 + [|t|]`.
-/

open Complex Filter Topology Finset HurwitzZeta

namespace NTKB.Apostol

/-- `∑_{n < N} (n+1)^{δ-1} ≤ N^δ/δ` for `0 < δ ≤ 1`. -/
lemma sum_range_rpow_le {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (N : ℕ) :
    ∑ n ∈ range N, ((n : ℝ) + 1) ^ (δ - 1) ≤ (N : ℝ) ^ δ / δ := by
  have hterm : ∀ n : ℕ, ((n : ℝ) + 1) ^ (δ - 1) ≤
      (((n : ℝ) + 1) ^ δ - (n : ℝ) ^ δ) / δ := by
    intro n
    have hm : (0 : ℝ) < n + 1 := by positivity
    -- Bernoulli: `(1 - 1/m)^δ ≤ 1 - δ/m`
    have hb := rpow_one_add_le_one_add_mul_self (s := -1 / ((n : ℝ) + 1))
      (by rw [neg_div, neg_le_neg_iff, div_le_one hm]; linarith [n.cast_nonneg (α := ℝ)])
      hδ.le hδ1
    have h1 : (1 + -1 / ((n : ℝ) + 1)) = (n : ℝ) / (n + 1) := by field_simp; ring
    rw [h1, Real.div_rpow (by positivity) hm.le] at hb
    rw [le_div_iff₀ hδ]
    have h2 : ((n : ℝ) + 1) ^ (δ - 1) * δ = δ * ((n : ℝ) + 1) ^ δ / ((n : ℝ) + 1) := by
      rw [Real.rpow_sub_one hm.ne']; ring
    rw [h2]
    have hpow : 0 < ((n : ℝ) + 1) ^ δ := by positivity
    rw [div_le_iff₀ hpow] at hb
    have : (n : ℝ) ^ δ ≤ ((n : ℝ) + 1) ^ δ - δ * ((n : ℝ) + 1) ^ δ / ((n : ℝ) + 1) := by
      calc (n : ℝ) ^ δ ≤ (1 + δ * (-1 / ((n : ℝ) + 1))) * ((n : ℝ) + 1) ^ δ := hb
        _ = _ := by ring
    linarith
  calc ∑ n ∈ range N, ((n : ℝ) + 1) ^ (δ - 1)
      ≤ ∑ n ∈ range N, ((((n + 1 : ℕ) : ℝ)) ^ δ - (n : ℝ) ^ δ) / δ :=
        sum_le_sum fun n _ ↦ by push_cast; exact hterm n
    _ = ((N : ℝ) ^ δ - (0 : ℝ) ^ δ) / δ := by
        rw [← sum_div, sum_range_sub (fun n : ℕ ↦ (n : ℝ) ^ δ)]
        simp
    _ = (N : ℝ) ^ δ / δ := by rw [Real.zero_rpow hδ.ne', sub_zero]

/-- `m^{-p-1} ≤ ((m-1)^{-p} - m^{-p})/p` for `0 < p ≤ 1`, `m > 1`. -/
lemma rpow_neg_sub_one_le {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) {m : ℝ} (hm : 1 < m) :
    m ^ (-p - 1) ≤ ((m - 1) ^ (-p) - m ^ (-p)) / p := by
  have hm0 : 0 < m := by linarith
  have hm1 : 0 < m - 1 := by linarith
  -- Bernoulli: `(m-1)^p ≤ m^p - p m^{p-1}`
  have hb := rpow_one_add_le_one_add_mul_self (s := -1 / m)
    (by rw [neg_div, neg_le_neg_iff, div_le_one hm0]; linarith) hp.le hp1
  have h1 : (1 + -1 / m) = (m - 1) / m := by field_simp; ring
  rw [h1, Real.div_rpow hm1.le hm0.le, div_le_iff₀ (by positivity)] at hb
  have hA : 0 < (m - 1) ^ p := by positivity
  have hB : 0 < m ^ p := by positivity
  have hle : (m - 1) ^ p ≤ m ^ p := Real.rpow_le_rpow hm1.le (by linarith) hp.le
  rw [Real.rpow_neg hm1.le, Real.rpow_neg hm0.le, Real.rpow_sub_one hm0.ne', Real.rpow_neg hm0.le,
    le_div_iff₀ hp]
  have key : p * m ^ p / m ≤ m ^ p - (m - 1) ^ p := by
    have : (1 + p * (-1 / m)) * m ^ p = m ^ p - p * m ^ p / m := by ring
    linarith
  rw [div_mul_eq_mul_div, inv_mul_eq_div, div_le_iff₀ hm0]
  rw [inv_sub_inv hA.ne' hB.ne']
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  have e : p / m ^ p * ((m - 1) ^ p * m ^ p) = p * (m - 1) ^ p := by field_simp
  rw [e]
  have k2 : p * m ^ p ≤ (m ^ p - (m - 1) ^ p) * m := by
    have := mul_le_mul_of_nonneg_right key hm0.le
    rwa [div_mul_cancel₀ _ hm0.ne'] at this
  nlinarith [mul_le_mul_of_nonneg_left hle hp.le]

/-- `∑_{n ≥ 0} (N+n)^{-p-1} ≤ (N-1)^{-p}/p` for `0 < p ≤ 1`, `N ≥ 2`. -/
lemma tsum_rpow_neg_sub_one_le {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) {N : ℕ} (hN : 2 ≤ N) :
    ∑' n : ℕ, ((N + n : ℝ)) ^ (-p - 1) ≤ ((N : ℝ) - 1) ^ (-p) / p := by
  refine Real.tsum_le_of_sum_range_le (fun n ↦ by positivity) fun M ↦ ?_
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  calc ∑ n ∈ range M, ((N + n : ℝ)) ^ (-p - 1)
      ≤ ∑ n ∈ range M, ((((N : ℝ) + n) - 1) ^ (-p) - ((N : ℝ) + n) ^ (-p)) / p :=
        sum_le_sum fun n _ ↦ rpow_neg_sub_one_le hp hp1 (by linarith [n.cast_nonneg (α := ℝ)])
    _ = (((N : ℝ) - 1) ^ (-p) - ((N : ℝ) - 1 + M) ^ (-p)) / p := by
        rw [← sum_div]
        congr 1
        have := sum_range_sub' (fun n : ℕ ↦ ((N : ℝ) - 1 + n) ^ (-p)) M
        simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, add_zero] at this
        rw [← this]
        refine sum_congr rfl fun n _ ↦ ?_
        ring_nf
    _ ≤ ((N : ℝ) - 1) ^ (-p) / p := by
        gcongr
        linarith [Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ (N : ℝ) - 1 + M) (-p)]

/-- `∑_{n ≥ 0} (n+1)^{-(1+δ)} = ζ(1+δ)` (real part; `ζ(1+δ)` is real). -/
lemma hasSum_rpow_riemannZeta {δ : ℝ} (hδ : 0 < δ) :
    HasSum (fun n : ℕ ↦ ((n : ℝ) + 1) ^ (-(1 + δ))) (riemannZeta (1 + δ : ℝ)).re := by
  have hs : 1 < ((1 + δ : ℝ) : ℂ).re := by simp; linarith
  have hsum : Summable (fun n : ℕ ↦ 1 / ((n : ℂ) + 1) ^ ((1 + δ : ℝ) : ℂ)) := by
    have := (summable_nat_add_iff 1).2 (Complex.summable_one_div_nat_cpow.2 hs)
    simpa [Nat.cast_add, Nat.cast_one] using this
  have hz := hsum.hasSum
  rw [← zeta_eq_tsum_one_div_nat_add_one_cpow hs] at hz
  have hre := Complex.hasSum_re hz
  convert hre using 1
  funext n
  rw [show ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) by push_cast; rfl, ← ofReal_cpow (by positivity),
    one_div, ← ofReal_inv, ofReal_re, Real.rpow_neg (by positivity)]

/-- **Apostol, Theorem 12.23 (a)** (29): for `δ > 0`, `σ ≥ 1 + δ`, `0 < a ≤ 1`:
`|ζ(s,a) - a^{-s}| ≤ ζ(1+δ)`. -/
@[kb "apostol1976" "Thm 12.23(a), p. 270"]
theorem apostol_thm_12_23_a {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1) {δ : ℝ} (hδ : 0 < δ) {s : ℂ}
    (hs : 1 + δ ≤ s.re) :
    ‖hurwitzZeta a s - ((a : ℝ) : ℂ) ^ (-s)‖ ≤ (riemannZeta (1 + δ : ℝ)).re := by
  have h := hasSum_hurwitz_shift ha0 ha1 0 (s := s) (by linarith) s rfl
  simp only [zero_add, range_one, sum_singleton, Nat.cast_zero] at h
  refine h.norm_le_of_bounded (hasSum_rpow_riemannZeta hδ) fun n ↦ ?_
  rw [norm_cpow_eq_rpow_re_of_pos (by positivity), neg_re]
  calc ((n : ℝ) + a + 1) ^ (-s.re) ≤ ((n : ℝ) + 1) ^ (-s.re) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
    _ ≤ ((n : ℝ) + 1) ^ (-(1 + δ)) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith [n.cast_nonneg (α := ℝ)]) (by linarith)

/-- **Apostol, Theorem 12.23 (b)** (30): for `0 < δ < 1` there is `A(δ) > 0` such that
`|ζ(s,a) - a^{-s}| ≤ A(δ) |t|^δ` whenever `0 < a ≤ 1`, `1 - δ ≤ σ ≤ 2`, `|t| ≥ 1`. -/
@[kb "apostol1976" "Thm 12.23(b), p. 270"]
theorem apostol_thm_12_23_b {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ∃ A : ℝ, 0 < A ∧ ∀ a : ℝ, 0 < a → a ≤ 1 → ∀ s : ℂ, 1 - δ ≤ s.re → s.re ≤ 2 →
      1 ≤ |s.im| → ‖hurwitzZeta a s - ((a : ℝ) : ℂ) ^ (-s)‖ ≤ A * |s.im| ^ δ := by
  have hA : 0 < 2 / δ + 3 + 6 / (1 - δ) := by
    have : 0 < 1 - δ := by linarith
    positivity
  refine ⟨2 / δ + 3 + 6 / (1 - δ), hA, ?_⟩
  intro a ha0 ha1 s hσ1 hσ2 ht
  set t := |s.im| with ht_def
  have hσ0 : 0 < s.re := by linarith
  have hs1 : s ≠ 1 := by
    intro h; rw [ht_def, h] at ht; simp at ht; linarith
  set N : ℕ := ⌊t⌋₊ + 1 with hN_def
  have ht0 : 0 < t := by linarith
  have hfl1 : 1 ≤ ⌊t⌋₊ := Nat.le_floor (by simpa using ht)
  have hN2 : 2 ≤ N := by omega
  have hNt : (N : ℝ) ≤ 2 * t := by
    have := Nat.floor_le ht0.le
    push_cast [hN_def]; linarith
  have hN1t : t / 2 ≤ (N : ℝ) - 1 := by
    have h1 : t < ⌊t⌋₊ + 1 := Nat.lt_floor_add_one t
    have h2 : (1 : ℝ) ≤ ⌊t⌋₊ := by exact_mod_cast hfl1
    push_cast [hN_def]; linarith
  have hδp : 0 < 1 - δ := by linarith
  -- the representation
  have hrep := hurwitzZeta_eq_J ha0 ha1 N hσ0 hs1
  rw [sum_range_succ'] at hrep
  simp only [Nat.cast_zero, zero_add] at hrep
  have hdecomp : hurwitzZeta a s - ((a : ℝ) : ℂ) ^ (-s) =
      ∑ n ∈ range N, ((((n + 1 : ℕ) : ℝ) + a : ℝ) : ℂ) ^ (-s) +
        ((N + a : ℝ) : ℂ) ^ (1 - s) / (s - 1) - hurwitzJSum a N s := by
    rw [hrep]; ring
  rw [hdecomp]
  -- the three bounds
  have tδ : 0 < t ^ δ := by positivity
  have T1 : ‖∑ n ∈ range N, ((((n + 1 : ℕ) : ℝ) + a : ℝ) : ℂ) ^ (-s)‖ ≤ 2 / δ * t ^ δ := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ n ∈ range N, ‖((((n + 1 : ℕ) : ℝ) + a : ℝ) : ℂ) ^ (-s)‖
        ≤ ∑ n ∈ range N, ((n : ℝ) + 1) ^ (δ - 1) := by
          refine sum_le_sum fun n _ ↦ ?_
          rw [norm_cpow_eq_rpow_re_of_pos (by positivity), neg_re]
          push_cast
          calc ((n : ℝ) + 1 + a) ^ (-s.re) ≤ ((n : ℝ) + 1) ^ (-s.re) :=
                Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
            _ ≤ ((n : ℝ) + 1) ^ (δ - 1) :=
                Real.rpow_le_rpow_of_exponent_le (by linarith [n.cast_nonneg (α := ℝ)])
                  (by linarith)
      _ ≤ (N : ℝ) ^ δ / δ := sum_range_rpow_le hδ0 hδ1.le N
      _ ≤ (2 * t) ^ δ / δ := by gcongr
      _ = 2 ^ δ * t ^ δ / δ := by rw [Real.mul_rpow (by norm_num) ht0.le]
      _ ≤ 2 * t ^ δ / δ := by
          gcongr
          calc (2 : ℝ) ^ δ ≤ 2 ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num) hδ1.le
            _ = 2 := Real.rpow_one 2
      _ = 2 / δ * t ^ δ := by ring
  have T2 : ‖((N + a : ℝ) : ℂ) ^ (1 - s) / (s - 1)‖ ≤ 3 * t ^ δ := by
    have hden : 1 ≤ ‖s - 1‖ := by
      calc (1 : ℝ) ≤ |(s - 1).im| := by simpa using ht
        _ ≤ ‖s - 1‖ := abs_im_le_norm _
    rw [norm_div]
    refine (div_le_of_le_mul₀ (norm_nonneg _) (by positivity) ?_)
    calc ‖((N + a : ℝ) : ℂ) ^ (1 - s)‖ = ((N : ℝ) + a) ^ (1 - s.re) := by
          rw [norm_cpow_eq_rpow_re_of_pos (by positivity)]; simp
      _ ≤ ((N : ℝ) + a) ^ δ := Real.rpow_le_rpow_of_exponent_le
          (by have : (2 : ℝ) ≤ N := by exact_mod_cast hN2
              linarith) (by linarith)
      _ ≤ (3 * t) ^ δ := Real.rpow_le_rpow (by positivity) (by linarith) hδ0.le
      _ = 3 ^ δ * t ^ δ := by rw [Real.mul_rpow (by norm_num) ht0.le]
      _ ≤ 3 * t ^ δ := by
          gcongr
          calc (3 : ℝ) ^ δ ≤ 3 ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num) hδ1.le
            _ = 3 := Real.rpow_one 3
      _ ≤ 3 * t ^ δ * ‖s - 1‖ := le_mul_of_one_le_right (by positivity) hden
  have T3 : ‖hurwitzJSum a N s‖ ≤ 6 / (1 - δ) * t ^ δ := by
    have hp : -(1 - δ) - 1 < -1 := by linarith
    have hsumN : HasSum (fun n : ℕ ↦ ‖s‖ * ((N + n : ℝ)) ^ (-(1 - δ) - 1))
        (‖s‖ * ∑' n : ℕ, ((N + n : ℝ)) ^ (-(1 - δ) - 1)) := by
      refine HasSum.mul_left _ (Summable.hasSum ?_)
      have := (summable_nat_add_iff N).mpr (Real.summable_nat_rpow.mpr hp)
      refine this.congr fun n ↦ ?_
      push_cast; ring_nf
    have hb : ‖hurwitzJSum a N s‖ ≤ ‖s‖ * ∑' n : ℕ, ((N + n : ℝ)) ^ (-(1 - δ) - 1) := by
      refine tsum_of_norm_bounded hsumN fun n ↦ ?_
      refine (norm_hurwitzJ_le (by positivity) hs1 (by linarith)).trans ?_
      gcongr
      have h2 : (2 : ℝ) ≤ N := by exact_mod_cast hN2
      calc ((N : ℝ) + n + a) ^ (-s.re - 1) ≤ ((N : ℝ) + n + a) ^ (-(1 - δ) - 1) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith [n.cast_nonneg (α := ℝ)]) (by linarith)
        _ ≤ ((N : ℝ) + n) ^ (-(1 - δ) - 1) :=
            Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
    have hnorm : ‖s‖ ≤ 3 * t := by
      calc ‖s‖ ≤ |s.re| + |s.im| := norm_le_abs_re_add_abs_im s
        _ ≤ 2 + t := by rw [abs_of_pos hσ0]; linarith
        _ ≤ 3 * t := by linarith
    have htail := tsum_rpow_neg_sub_one_le hδp (by linarith : 1 - δ ≤ 1) hN2
    have hN1 : ((N : ℝ) - 1) ^ (-(1 - δ)) ≤ 2 * t ^ δ / t := by
      have h2δ : 1 ≤ (2 : ℝ) ^ δ := Real.one_le_rpow (by norm_num) hδ0.le
      calc ((N : ℝ) - 1) ^ (-(1 - δ)) ≤ (t / 2) ^ (-(1 - δ)) :=
            Real.rpow_le_rpow_of_nonpos (by positivity) hN1t (by linarith)
        _ = (t ^ δ / t) / ((2 : ℝ) ^ δ / 2) := by
            rw [show -(1 - δ) = δ - 1 by ring, Real.div_rpow ht0.le (by norm_num : (0 : ℝ) ≤ 2),
              Real.rpow_sub_one ht0.ne', Real.rpow_sub_one (by norm_num : (2 : ℝ) ≠ 0)]
        _ ≤ 2 * t ^ δ / t := by
            rw [div_le_iff₀ (by positivity)]
            have : 0 < t ^ δ / t := div_pos tδ ht0
            have e : 2 * t ^ δ / t * ((2 : ℝ) ^ δ / 2) = t ^ δ / t * 2 ^ δ := by ring
            rw [e]
            exact le_mul_of_one_le_right this.le h2δ
    calc ‖hurwitzJSum a N s‖ ≤ ‖s‖ * ∑' n : ℕ, ((N + n : ℝ)) ^ (-(1 - δ) - 1) := hb
      _ ≤ (3 * t) * (((N : ℝ) - 1) ^ (-(1 - δ)) / (1 - δ)) := by
          gcongr
      _ ≤ (3 * t) * ((2 * t ^ δ / t) / (1 - δ)) := by gcongr
      _ = 6 / (1 - δ) * t ^ δ := by field_simp; ring
  calc ‖∑ n ∈ range N, ((((n + 1 : ℕ) : ℝ) + a : ℝ) : ℂ) ^ (-s) +
        ((N + a : ℝ) : ℂ) ^ (1 - s) / (s - 1) - hurwitzJSum a N s‖
      ≤ ‖∑ n ∈ range N, ((((n + 1 : ℕ) : ℝ) + a : ℝ) : ℂ) ^ (-s)‖ +
        ‖((N + a : ℝ) : ℂ) ^ (1 - s) / (s - 1)‖ + ‖hurwitzJSum a N s‖ :=
        (norm_sub_le _ _).trans (by gcongr; exact norm_add_le _ _)
    _ ≤ 2 / δ * t ^ δ + 3 * t ^ δ + 6 / (1 - δ) * t ^ δ := by gcongr
    _ = (2 / δ + 3 + 6 / (1 - δ)) * t ^ δ := by ring

lemma rpow_N_sub_one_le {δ t : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (ht0 : 0 < t) {N : ℝ}
    (hN : t / 2 ≤ N - 1) :
    (N - 1) ^ (-(1 - δ)) ≤ 2 * t ^ δ / t := by
  have h2δ : 1 ≤ (2 : ℝ) ^ δ := Real.one_le_rpow (by norm_num) hδ0.le
  have tδ : 0 < t ^ δ := by positivity
  calc (N - 1) ^ (-(1 - δ)) ≤ (t / 2) ^ (-(1 - δ)) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) hN (by linarith)
    _ = (t ^ δ / t) / ((2 : ℝ) ^ δ / 2) := by
        rw [show -(1 - δ) = δ - 1 by ring, Real.div_rpow ht0.le (by norm_num : (0 : ℝ) ≤ 2),
          Real.rpow_sub_one ht0.ne', Real.rpow_sub_one (by norm_num : (2 : ℝ) ≠ 0)]
    _ ≤ 2 * t ^ δ / t := by
        rw [div_le_iff₀ (by positivity)]
        have : 0 < t ^ δ / t := div_pos tδ ht0
        have e : 2 * t ^ δ / t * ((2 : ℝ) ^ δ / 2) = t ^ δ / t * 2 ^ δ := by ring
        rw [e]
        exact le_mul_of_one_le_right this.le h2δ

lemma rpow_le_mul_rpow {c x δ : ℝ} (hc : 1 ≤ c) (hx : 0 ≤ x) (_hδ0 : 0 ≤ δ) {m : ℝ}
    (hδm : δ ≤ m) : (c * x) ^ δ ≤ c ^ m * x ^ δ := by
  rw [Real.mul_rpow (by linarith) hx]
  gcongr

/-- **Apostol, Theorem 12.23 (b)** (31): for `0 < δ < 1` there is `A(δ) > 0` such that
`|ζ(s,a) - a^{-s}| ≤ A(δ) |t|^{1+δ}` whenever `0 < a ≤ 1`, `-δ ≤ σ ≤ δ`, `|t| ≥ 1`.
(Apostol's proof: the representation (27) of Theorem 12.22 with `N = 1 + [|t|]`, and (30) for
`ζ(s+1, a)`.) -/
@[kb "apostol1976" "Thm 12.23(b), p. 270"]
theorem apostol_thm_12_23_b' {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ∃ A : ℝ, 0 < A ∧ ∀ a : ℝ, 0 < a → a ≤ 1 → ∀ s : ℂ, -δ ≤ s.re → s.re ≤ δ →
      1 ≤ |s.im| → ‖hurwitzZeta a s - ((a : ℝ) : ℂ) ^ (-s)‖ ≤ A * |s.im| ^ (1 + δ) := by
  obtain ⟨B, hB, hBb⟩ := apostol_thm_12_23_b hδ0 hδ1
  have hδp : 0 < 1 - δ := by linarith
  have hA : 0 < 6 + 9 + B + 2 / δ + 6 / (1 - δ) := by positivity
  refine ⟨6 + 9 + B + 2 / δ + 6 / (1 - δ), hA, ?_⟩
  intro a ha0 ha1 s hσ1 hσ2 ht
  set t := |s.im| with ht_def
  have ht0 : 0 < t := by linarith
  have hs1 : s ≠ 1 := by
    intro h; rw [ht_def, h] at ht; simp at ht; linarith
  have hs0 : s ≠ 0 := by
    intro h; rw [ht_def, h] at ht; simp at ht; linarith
  set N : ℕ := ⌊t⌋₊ + 1 with hN_def
  have hfl1 : 1 ≤ ⌊t⌋₊ := Nat.le_floor (by simpa using ht)
  have hN2 : 2 ≤ N := by omega
  have hN2' : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hNt : (N : ℝ) ≤ 2 * t := by
    have := Nat.floor_le ht0.le
    push_cast [hN_def]; linarith
  have hN1t : t / 2 ≤ (N : ℝ) - 1 := by
    have h1 : t < ⌊t⌋₊ + 1 := Nat.lt_floor_add_one t
    have h2 : (1 : ℝ) ≤ ⌊t⌋₊ := by exact_mod_cast hfl1
    push_cast [hN_def]; linarith
  have tδ : 0 < t ^ δ := by positivity
  have t1δ : t ^ (1 + δ) = t * t ^ δ := by
    rw [Real.rpow_add ht0, Real.rpow_one]
  -- the representation (27)
  have hrep := hurwitzZeta_eq_L ha0 ha1 N (s := s) ⟨by simp; linarith, by simp [hs0, hs1]⟩
  rw [sum_range_succ' (fun n : ℕ ↦ ((n + a : ℝ) : ℂ) ^ (-s)) N,
    sum_range_succ' (fun n : ℕ ↦ ((n + a : ℝ) : ℂ) ^ (-s - 1)) N] at hrep
  simp only [Nat.cast_zero, zero_add] at hrep
  set X := ∑ n ∈ range N, ((((n + 1 : ℕ) : ℝ) + a : ℝ) : ℂ) ^ (-s)
  set Y := ((N + a : ℝ) : ℂ) ^ (1 - s) / (s - 1)
  set Z := hurwitzZeta a (s + 1) - ((a : ℝ) : ℂ) ^ (-(s + 1))
  set W := ∑ n ∈ range N, ((((n + 1 : ℕ) : ℝ) + a : ℝ) : ℂ) ^ (-s - 1)
  have hdecomp : hurwitzZeta a s - ((a : ℝ) : ℂ) ^ (-s) = X + Y - (s / 2 * Z - s / 2 * W) -
      hurwitzLSum a N s := by
    rw [hrep]
    simp only [X, Y, Z, W, neg_add']
    ring
  rw [hdecomp]
  have hnorm : ‖s‖ ≤ 2 * t := by
    calc ‖s‖ ≤ |s.re| + |s.im| := norm_le_abs_re_add_abs_im s
      _ ≤ δ + t := by gcongr; exact abs_le.mpr ⟨by linarith, hσ2⟩
      _ ≤ 2 * t := by linarith
  have hnorm1 : ‖s + 1‖ ≤ 3 * t := by
    calc ‖s + 1‖ ≤ ‖s‖ + 1 := by simpa using norm_add_le s 1
      _ ≤ 3 * t := by linarith
  have hs2 : ‖s / 2‖ ≤ t := by
    rw [norm_div]; simp; linarith
  -- the five bounds
  have TX : ‖X‖ ≤ 6 * t ^ (1 + δ) := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ n ∈ range N, ‖((((n + 1 : ℕ) : ℝ) + a : ℝ) : ℂ) ^ (-s)‖
        ≤ ∑ n ∈ range N, 3 * t ^ δ := by
          refine sum_le_sum fun n hn ↦ ?_
          have hn' : (n : ℝ) + 1 ≤ N := by
            have := mem_range.mp hn; exact_mod_cast this
          rw [norm_cpow_eq_rpow_re_of_pos (by positivity), neg_re]
          push_cast
          calc ((n : ℝ) + 1 + a) ^ (-s.re) ≤ ((n : ℝ) + 1 + a) ^ δ :=
                Real.rpow_le_rpow_of_exponent_le (by linarith [n.cast_nonneg (α := ℝ)])
                  (by linarith)
            _ ≤ (3 * t) ^ δ := Real.rpow_le_rpow (by positivity) (by linarith) hδ0.le
            _ ≤ 3 ^ (1 : ℝ) * t ^ δ := rpow_le_mul_rpow (by norm_num) ht0.le hδ0.le hδ1.le
            _ = 3 * t ^ δ := by rw [Real.rpow_one]
      _ = (N : ℝ) * (3 * t ^ δ) := by simp
      _ ≤ (2 * t) * (3 * t ^ δ) := by gcongr
      _ = 6 * t ^ (1 + δ) := by rw [t1δ]; ring
  have TY : ‖Y‖ ≤ 9 * t ^ (1 + δ) := by
    have hden : 1 ≤ ‖s - 1‖ := by
      calc (1 : ℝ) ≤ |(s - 1).im| := by simpa using ht
        _ ≤ ‖s - 1‖ := abs_im_le_norm _
    simp only [Y]
    rw [norm_div]
    refine (div_le_of_le_mul₀ (norm_nonneg _) (by positivity) ?_)
    calc ‖((N + a : ℝ) : ℂ) ^ (1 - s)‖ = ((N : ℝ) + a) ^ (1 - s.re) := by
          rw [norm_cpow_eq_rpow_re_of_pos (by positivity)]; simp
      _ ≤ ((N : ℝ) + a) ^ (1 + δ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      _ ≤ (3 * t) ^ (1 + δ) := Real.rpow_le_rpow (by positivity) (by linarith) (by linarith)
      _ ≤ 3 ^ (2 : ℝ) * t ^ (1 + δ) := rpow_le_mul_rpow (by norm_num) ht0.le (by linarith)
          (by linarith)
      _ = 9 * t ^ (1 + δ) := by norm_num
      _ ≤ 9 * t ^ (1 + δ) * ‖s - 1‖ := le_mul_of_one_le_right (by positivity) hden
  have TZ : ‖s / 2 * Z‖ ≤ B * t ^ (1 + δ) := by
    have hZ := hBb a ha0 ha1 (s + 1) (by simp; linarith) (by simp; linarith) (by simpa using ht)
    simp only [add_im, one_im, add_zero] at hZ
    rw [norm_mul]
    calc ‖s / 2‖ * ‖Z‖ ≤ t * (B * t ^ δ) := by gcongr
      _ = B * t ^ (1 + δ) := by rw [t1δ]; ring
  have TW : ‖s / 2 * W‖ ≤ 2 / δ * t ^ (1 + δ) := by
    rw [norm_mul]
    have hW : ‖W‖ ≤ 2 / δ * t ^ δ := by
      refine (norm_sum_le _ _).trans ?_
      calc ∑ n ∈ range N, ‖((((n + 1 : ℕ) : ℝ) + a : ℝ) : ℂ) ^ (-s - 1)‖
          ≤ ∑ n ∈ range N, ((n : ℝ) + 1) ^ (δ - 1) := by
            refine sum_le_sum fun n _ ↦ ?_
            rw [norm_cpow_eq_rpow_re_of_pos (by positivity)]
            simp only [sub_re, neg_re, one_re]
            push_cast
            calc ((n : ℝ) + 1 + a) ^ (-s.re - 1) ≤ ((n : ℝ) + 1) ^ (-s.re - 1) :=
                  Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
              _ ≤ ((n : ℝ) + 1) ^ (δ - 1) :=
                  Real.rpow_le_rpow_of_exponent_le (by linarith [n.cast_nonneg (α := ℝ)])
                    (by linarith)
        _ ≤ (N : ℝ) ^ δ / δ := sum_range_rpow_le hδ0 hδ1.le N
        _ ≤ (2 * t) ^ δ / δ := by gcongr
        _ ≤ 2 ^ (1 : ℝ) * t ^ δ / δ := by
            gcongr; exact rpow_le_mul_rpow (by norm_num) ht0.le hδ0.le hδ1.le
        _ = 2 / δ * t ^ δ := by rw [Real.rpow_one]; ring
    calc ‖s / 2‖ * ‖W‖ ≤ t * (2 / δ * t ^ δ) := by gcongr
      _ = 2 / δ * t ^ (1 + δ) := by rw [t1δ]; ring
  have TL : ‖hurwitzLSum a N s‖ ≤ 6 / (1 - δ) * t ^ (1 + δ) := by
    have hp : -(1 - δ) - 1 < -1 := by linarith
    have hsumN : HasSum (fun n : ℕ ↦ ‖s‖ * ‖s + 1‖ / 2 * ((N + n : ℝ)) ^ (-(1 - δ) - 1))
        (‖s‖ * ‖s + 1‖ / 2 * ∑' n : ℕ, ((N + n : ℝ)) ^ (-(1 - δ) - 1)) := by
      refine HasSum.mul_left _ (Summable.hasSum ?_)
      have := (summable_nat_add_iff N).mpr (Real.summable_nat_rpow.mpr hp)
      refine this.congr fun n ↦ ?_
      push_cast; ring_nf
    have hb : ‖hurwitzLSum a N s‖ ≤
        ‖s‖ * ‖s + 1‖ / 2 * ∑' n : ℕ, ((N + n : ℝ)) ^ (-(1 - δ) - 1) := by
      refine tsum_of_norm_bounded hsumN fun n ↦ ?_
      refine (norm_hurwitzL_le (by positivity) hs1 (by linarith)).trans ?_
      gcongr
      calc ((N : ℝ) + n + a) ^ (-s.re - 2) ≤ ((N : ℝ) + n + a) ^ (-(1 - δ) - 1) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith [n.cast_nonneg (α := ℝ)]) (by linarith)
        _ ≤ ((N : ℝ) + n) ^ (-(1 - δ) - 1) :=
            Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
    have htail := tsum_rpow_neg_sub_one_le hδp (by linarith : 1 - δ ≤ 1) hN2
    have hN1 := rpow_N_sub_one_le hδ0 hδ1.le ht0 hN1t
    calc ‖hurwitzLSum a N s‖ ≤ ‖s‖ * ‖s + 1‖ / 2 * ∑' n : ℕ, ((N + n : ℝ)) ^ (-(1 - δ) - 1) := hb
      _ ≤ (2 * t) * (3 * t) / 2 * (((N : ℝ) - 1) ^ (-(1 - δ)) / (1 - δ)) := by gcongr
      _ ≤ (2 * t) * (3 * t) / 2 * ((2 * t ^ δ / t) / (1 - δ)) := by gcongr
      _ = 6 / (1 - δ) * t ^ (1 + δ) := by rw [t1δ]; field_simp; ring
  calc ‖X + Y - (s / 2 * Z - s / 2 * W) - hurwitzLSum a N s‖
      ≤ ‖X‖ + ‖Y‖ + (‖s / 2 * Z‖ + ‖s / 2 * W‖) + ‖hurwitzLSum a N s‖ := by
        refine (norm_sub_le _ _).trans ?_
        gcongr
        refine (norm_sub_le _ _).trans ?_
        gcongr
        · exact norm_add_le _ _
        · exact norm_sub_le _ _
    _ ≤ 6 * t ^ (1 + δ) + 9 * t ^ (1 + δ) + (B * t ^ (1 + δ) + 2 / δ * t ^ (1 + δ)) +
        6 / (1 - δ) * t ^ (1 + δ) := by gcongr
    _ = (6 + 9 + B + 2 / δ + 6 / (1 - δ)) * t ^ (1 + δ) := by ring

end NTKB.Apostol
