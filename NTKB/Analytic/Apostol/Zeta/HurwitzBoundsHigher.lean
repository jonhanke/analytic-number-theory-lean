/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Apostol.Zeta.HurwitzBounds
import NTKB.Analytic.Apostol.Zeta.HurwitzEulerHigher

/-!
# Bounds for `|ζ(s, a)|` in the strips `-m - δ ≤ σ ≤ -m + δ` (Apostol, Theorem 12.23 (32))

For `0 < δ < 1` and `m = 1, 2, …` there is `A(δ, m)`, independent of `s` and `a ∈ (0, 1]`, with
`|ζ(s,a)| ≤ A |t|^{m+1+δ}` for `-m - δ ≤ σ ≤ -m + δ`, `|t| ≥ 1` (in the book the constant
depends on `m` as well; this is implicit there). Proof as in Apostol: the expansion (28) of
Theorem 12.22 (with `m + 1` terms) and `N = 1 + [|t|]`, by induction on `m` starting from (31).
-/

open Complex Filter Topology Finset HurwitzZeta

namespace NTKB.Apostol

/-- `∑_{n<N} (n+1+a)^p ≤ (N+1)^{e+1}` for `p ≤ e`, `e ≥ 0`, `0 < a ≤ 1`. -/
lemma sum_range_rpow_le_pow {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1) (N : ℕ) {p e : ℝ} (hpe : p ≤ e)
    (he : 0 ≤ e) : ∑ n ∈ range N, ((n : ℝ) + 1 + a) ^ p ≤ ((N : ℝ) + 1) ^ (e + 1) := by
  calc ∑ n ∈ range N, ((n : ℝ) + 1 + a) ^ p ≤ ∑ n ∈ range N, ((N : ℝ) + 1) ^ e := by
        refine sum_le_sum fun n hn ↦ ?_
        have hn' : (n : ℝ) + 1 ≤ N := by have := mem_range.mp hn; exact_mod_cast this
        calc ((n : ℝ) + 1 + a) ^ p ≤ ((n : ℝ) + 1 + a) ^ e :=
              Real.rpow_le_rpow_of_exponent_le (by linarith [n.cast_nonneg (α := ℝ)]) hpe
          _ ≤ ((N : ℝ) + 1) ^ e := Real.rpow_le_rpow (by positivity) (by linarith) he
    _ = (N : ℝ) * ((N : ℝ) + 1) ^ e := by simp
    _ ≤ ((N : ℝ) + 1) * ((N : ℝ) + 1) ^ e := by gcongr; linarith
    _ = ((N : ℝ) + 1) ^ (e + 1) := by
        rw [Real.rpow_add (by positivity), Real.rpow_one, mul_comm]

set_option maxHeartbeats 1000000 in
/-- The induction step for (32): bounds at the levels `M - r` (`1 ≤ r ≤ M + 1`; the level `-1`
being (30)) give a bound at level `M`. -/
lemma hurwitz_bound_step {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) (M : ℕ) {A' : ℝ} (hA' : 0 < A')
    (hlev : ∀ r ∈ Icc 1 (M + 1), ∀ a : ℝ, 0 < a → a ≤ 1 → ∀ s : ℂ,
      -(M : ℝ) + r - δ ≤ s.re → s.re ≤ -(M : ℝ) + r + δ → 1 ≤ |s.im| →
      ‖hurwitzZeta a s - ((a : ℝ) : ℂ) ^ (-s)‖ ≤ A' * |s.im| ^ ((M : ℝ) - r + 1 + δ)) :
    ∃ A : ℝ, 0 < A ∧ ∀ a : ℝ, 0 < a → a ≤ 1 → ∀ s : ℂ, -(M : ℝ) - δ ≤ s.re →
      s.re ≤ -(M : ℝ) + δ → 1 ≤ |s.im| →
      ‖hurwitzZeta a s - ((a : ℝ) : ℂ) ^ (-s)‖ ≤ A * |s.im| ^ ((M : ℝ) + 1 + δ) := by
  have hδp : 0 < 1 - δ := by linarith
  set K : ℝ := 2 * M + 4
  have hK : 1 ≤ K := by simp only [K]; linarith [M.cast_nonneg (α := ℝ)]
  set T : ℝ := (3 : ℝ) ^ ((M : ℝ) + 2)
  have hT : 0 < T := by positivity
  set A : ℝ := T + T + (M + 1) * (K ^ (M + 1) * (A' + (1 + 1 / δ) * T)) + 2 * K ^ (M + 2) / (1 - δ)
  have hA : 0 < A := by positivity
  refine ⟨A, hA, ?_⟩
  intro a ha0 ha1 s hσ1 hσ2 ht
  set t := |s.im| with ht_def
  have ht0 : 0 < t := by linarith
  have hM0 : (0 : ℝ) ≤ M := M.cast_nonneg
  -- `s` is not real, hence not a pole
  have hpole : ∀ r : ℕ, r ≤ M + 1 → s ≠ 1 - r := by
    intro r _ h
    have := congrArg im h
    simp at this
    rw [ht_def, this] at ht; simp at ht; linarith
  have hs1 : s ≠ 1 := by simpa using hpole 0 (Nat.zero_le _)
  set N : ℕ := ⌊t⌋₊ + 1 with hN_def
  have hfl1 : 1 ≤ ⌊t⌋₊ := Nat.le_floor (by simpa using ht)
  have hN2 : 2 ≤ N := by omega
  have hNt : (N : ℝ) ≤ 2 * t := by
    have := Nat.floor_le ht0.le
    push_cast [hN_def]; linarith
  have hN1 : (N : ℝ) + 1 ≤ 3 * t := by linarith
  have hN1t : t / 2 ≤ (N : ℝ) - 1 := by
    have h1 : t < ⌊t⌋₊ + 1 := Nat.lt_floor_add_one t
    have h2 : (1 : ℝ) ≤ ⌊t⌋₊ := by exact_mod_cast hfl1
    push_cast [hN_def]; linarith
  have hnorm : ‖s‖ ≤ (M + 2) * t := by
    calc ‖s‖ ≤ |s.re| + |s.im| := norm_le_abs_re_add_abs_im s
      _ ≤ (M + 1) + t := by
          gcongr; exact abs_le.mpr ⟨by linarith, by linarith⟩
      _ ≤ (M + 2) * t := by nlinarith
  have hsr : ∀ r : ℕ, r ≤ M + 2 → ‖s‖ + r ≤ K * t := by
    intro r hr
    have : (r : ℝ) ≤ M + 2 := by exact_mod_cast hr
    simp only [K]; nlinarith
  -- powers of `3t`
  have h3t : ∀ x : ℝ, 0 ≤ x → x ≤ (M : ℝ) + 2 → ((N : ℝ) + 1) ^ x ≤ T * t ^ x := by
    intro x hx hxM
    calc ((N : ℝ) + 1) ^ x ≤ (3 * t) ^ x := Real.rpow_le_rpow (by positivity) hN1 hx
      _ ≤ T * t ^ x := rpow_le_mul_rpow (by norm_num) ht0.le hx hxM
  -- the expansion (28) with `M + 1` terms
  have hrep := hurwitzZeta_eq_Lm ha0 ha1 N (M + 1) (s := s)
    ⟨by simp; push_cast; linarith, fun h ↦ by
      obtain ⟨r, hr, hr'⟩ := mem_hurwitzPoles.mp h
      exact hpole r hr hr'⟩
  rw [sum_range_succ' (fun n : ℕ ↦ ((n + a : ℝ) : ℂ) ^ (-s)) N] at hrep
  simp only [Nat.cast_zero, zero_add] at hrep
  set X := ∑ n ∈ range N, ((((n + 1 : ℕ) : ℝ) + a : ℝ) : ℂ) ^ (-s)
  set Y := ((N + a : ℝ) : ℂ) ^ (1 - s) / (s - 1)
  set S := ∑ r ∈ Icc 1 (M + 1), hurwitzCoeff r s *
    (hurwitzZeta a (s + r) - ∑ i ∈ range (N + 1), ((i + a : ℝ) : ℂ) ^ (-s - r))
  have hdecomp : hurwitzZeta a s - ((a : ℝ) : ℂ) ^ (-s) = X + Y - S - hurwitzLmSum a N (M + 1) s := by
    rw [hrep]; ring
  rw [hdecomp]
  have tpos : ∀ x : ℝ, 0 < t ^ x := fun x ↦ by positivity
  have tadd : ∀ x y : ℝ, t ^ (x + y) = t ^ x * t ^ y := fun x y ↦ Real.rpow_add ht0 x y
  -- the bounds
  have TX : ‖X‖ ≤ T * t ^ ((M : ℝ) + 1 + δ) := by
    refine (norm_sum_le _ _).trans ?_
    have : ∑ n ∈ range N, ‖((((n + 1 : ℕ) : ℝ) + a : ℝ) : ℂ) ^ (-s)‖ =
        ∑ n ∈ range N, ((n : ℝ) + 1 + a) ^ (-s.re) := by
      refine sum_congr rfl fun n _ ↦ ?_
      rw [norm_cpow_eq_rpow_re_of_pos (by positivity), neg_re]; push_cast; ring_nf
    rw [this]
    refine (sum_range_rpow_le_pow ha0 ha1 N (e := (M : ℝ) + δ) (by linarith) (by positivity)).trans ?_
    rw [show (M : ℝ) + δ + 1 = (M : ℝ) + 1 + δ by ring]
    exact h3t _ (by positivity) (by linarith)
  have TY : ‖Y‖ ≤ T * t ^ ((M : ℝ) + 1 + δ) := by
    have hden : 1 ≤ ‖s - 1‖ := by
      calc (1 : ℝ) ≤ |(s - 1).im| := by simpa using ht
        _ ≤ ‖s - 1‖ := abs_im_le_norm _
    simp only [Y]
    rw [norm_div]
    refine (div_le_of_le_mul₀ (norm_nonneg _) (by positivity) ?_)
    calc ‖((N + a : ℝ) : ℂ) ^ (1 - s)‖ = ((N : ℝ) + a) ^ (1 - s.re) := by
          rw [norm_cpow_eq_rpow_re_of_pos (by positivity)]; simp
      _ ≤ ((N : ℝ) + a) ^ ((M : ℝ) + 1 + δ) := Real.rpow_le_rpow_of_exponent_le
          (by have : (2 : ℝ) ≤ N := by exact_mod_cast hN2
              linarith) (by linarith)
      _ ≤ ((N : ℝ) + 1) ^ ((M : ℝ) + 1 + δ) := Real.rpow_le_rpow (by positivity) (by linarith)
          (by positivity)
      _ ≤ T * t ^ ((M : ℝ) + 1 + δ) := h3t _ (by positivity) (by linarith)
      _ ≤ T * t ^ ((M : ℝ) + 1 + δ) * ‖s - 1‖ := le_mul_of_one_le_right (by positivity) hden
  have TS : ‖S‖ ≤ (M + 1) * (K ^ (M + 1) * (A' + (1 + 1 / δ) * T)) * t ^ ((M : ℝ) + 1 + δ) := by
    refine (norm_sum_le _ _).trans ?_
    have hterm : ∀ r ∈ Icc 1 (M + 1), ‖hurwitzCoeff r s *
        (hurwitzZeta a (s + r) - ∑ i ∈ range (N + 1), ((i + a : ℝ) : ℂ) ^ (-s - r))‖ ≤
        K ^ (M + 1) * (A' + (1 + 1 / δ) * T) * t ^ ((M : ℝ) + 1 + δ) := by
      intro r hr
      have hr1 : 1 ≤ r := (mem_Icc.mp hr).1
      have hr2 : r ≤ M + 1 := (mem_Icc.mp hr).2
      have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr1
      have hrM : (r : ℝ) ≤ M + 1 := by exact_mod_cast hr2
      set e : ℝ := (M : ℝ) - r + 1 + δ
      have he : δ ≤ e := by simp only [e]; linarith
      -- the coefficient
      have hc : ‖hurwitzCoeff r s‖ ≤ K ^ r * t ^ (r : ℝ) := by
        rw [hurwitzCoeff, norm_div, Complex.norm_natCast]
        have hf1 : (1 : ℝ) ≤ ((r + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
        refine (div_le_self (norm_nonneg _) hf1).trans ?_
        refine (norm_cpoch_le r s).trans ?_
        calc (‖s‖ + r) ^ r ≤ (K * t) ^ r := by gcongr; exact hsr r (by omega)
          _ = K ^ r * t ^ (r : ℝ) := by rw [mul_pow, Real.rpow_natCast]
      -- the bracket
      rw [sum_range_succ' (fun i : ℕ ↦ ((i + a : ℝ) : ℂ) ^ (-s - r)) N]
      simp only [Nat.cast_zero, zero_add]
      have hZ := hlev r hr a ha0 ha1 (s + r) (by simp; linarith) (by simp; linarith)
        (by simpa using ht)
      simp only [add_im, natCast_im, add_zero, show -(s + r) = -s - r by ring] at hZ
      have hW : ‖∑ i ∈ range N, ((((i + 1 : ℕ) : ℝ) + a : ℝ) : ℂ) ^ (-s - r)‖ ≤
          (1 + 1 / δ) * T * t ^ e := by
        refine (norm_sum_le _ _).trans ?_
        have : ∑ i ∈ range N, ‖((((i + 1 : ℕ) : ℝ) + a : ℝ) : ℂ) ^ (-s - r)‖ =
            ∑ i ∈ range N, ((i : ℝ) + 1 + a) ^ (-s.re - r) := by
          refine sum_congr rfl fun i _ ↦ ?_
          rw [norm_cpow_eq_rpow_re_of_pos (by positivity)]; push_cast; simp
        rw [this]
        rcases lt_or_eq_of_le hr2 with hlt | heq
        · -- `r ≤ M`: crude bound
          have hrM' : (r : ℝ) ≤ M := by exact_mod_cast Nat.lt_succ_iff.mp hlt
          refine (sum_range_rpow_le_pow ha0 ha1 N (e := (M : ℝ) - r + δ) (by linarith)
            (by linarith)).trans ?_
          rw [show (M : ℝ) - r + δ + 1 = e by simp only [e]; ring]
          refine (h3t e (by linarith) (by simp only [e]; linarith)).trans ?_
          have : 0 ≤ T * t ^ e := by positivity
          nlinarith [show 0 ≤ 1 / δ from by positivity]
        · -- `r = M + 1`: `∑ (n+1)^{δ-1} ≤ N^δ/δ`
          have hrv : (r : ℝ) = M + 1 := by exact_mod_cast heq
          have he' : e = δ := by simp only [e]; rw [hrv]; ring
          calc ∑ i ∈ range N, ((i : ℝ) + 1 + a) ^ (-s.re - r)
              ≤ ∑ i ∈ range N, ((i : ℝ) + 1) ^ (δ - 1) := by
                refine sum_le_sum fun i _ ↦ ?_
                calc ((i : ℝ) + 1 + a) ^ (-s.re - r) ≤ ((i : ℝ) + 1) ^ (-s.re - r) :=
                      Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith)
                        (by rw [hrv]; linarith)
                  _ ≤ ((i : ℝ) + 1) ^ (δ - 1) := Real.rpow_le_rpow_of_exponent_le
                      (by linarith [i.cast_nonneg (α := ℝ)]) (by rw [hrv]; linarith)
            _ ≤ (N : ℝ) ^ δ / δ := sum_range_rpow_le hδ0 hδ1.le N
            _ ≤ ((N : ℝ) + 1) ^ δ / δ := by gcongr; linarith
            _ ≤ T * t ^ δ / δ := by gcongr; exact h3t δ hδ0.le (by linarith)
            _ ≤ (1 + 1 / δ) * T * t ^ e := by
                rw [he']
                have : 0 ≤ T * t ^ δ := by positivity
                have : T * t ^ δ / δ = 1 / δ * (T * t ^ δ) := by ring
                nlinarith
      rw [norm_mul]
      calc ‖hurwitzCoeff r s‖ * ‖hurwitzZeta a (s + r) - (
            ∑ i ∈ range N, ((((i + 1 : ℕ) : ℝ) + a : ℝ) : ℂ) ^ (-s - r) + ((a : ℝ) : ℂ) ^ (-s - r))‖
          ≤ (K ^ r * t ^ (r : ℝ)) * (A' * t ^ e + (1 + 1 / δ) * T * t ^ e) := by
            refine mul_le_mul hc ?_ (norm_nonneg _) (by positivity)
            rw [show ∀ x y z : ℂ, x - (y + z) = (x - z) - y from fun x y z ↦ by ring]
            exact (norm_sub_le _ _).trans (add_le_add hZ hW)
      _ = K ^ r * (A' + (1 + 1 / δ) * T) * (t ^ (r : ℝ) * t ^ e) := by ring
      _ = K ^ r * (A' + (1 + 1 / δ) * T) * t ^ ((M : ℝ) + 1 + δ) := by
          rw [← tadd]; congr 2; simp only [e]; ring
      _ ≤ K ^ (M + 1) * (A' + (1 + 1 / δ) * T) * t ^ ((M : ℝ) + 1 + δ) := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (pow_le_pow_right₀ hK hr2) (by positivity)) (by positivity)
    refine (sum_le_sum hterm).trans ?_
    rw [sum_const, Nat.card_Icc, nsmul_eq_mul]
    push_cast
    ring_nf; rfl
  have TL : ‖hurwitzLmSum a N (M + 1) s‖ ≤ 2 * K ^ (M + 2) / (1 - δ) * t ^ ((M : ℝ) + 1 + δ) := by
    have hp : -(1 - δ) - 1 < -1 := by linarith
    set P : ℝ := ‖cpoch (M + 1 + 1) s‖ / ((M + 1 + 1).factorial : ℝ)
    have hsumN : HasSum (fun n : ℕ ↦ P * ((N + n : ℝ)) ^ (-(1 - δ) - 1))
        (P * ∑' n : ℕ, ((N + n : ℝ)) ^ (-(1 - δ) - 1)) := by
      refine HasSum.mul_left _ (Summable.hasSum ?_)
      have := (summable_nat_add_iff N).mpr (Real.summable_nat_rpow.mpr hp)
      refine this.congr fun n ↦ ?_
      push_cast; ring_nf
    have hb : ‖hurwitzLmSum a N (M + 1) s‖ ≤ P * ∑' n : ℕ, ((N + n : ℝ)) ^ (-(1 - δ) - 1) := by
      refine tsum_of_norm_bounded hsumN fun n ↦ ?_
      refine (norm_hurwitzLm_le (by positivity) hs1 (M + 1) (by push_cast; linarith)).trans ?_
      gcongr
      have h2 : (2 : ℝ) ≤ N := by exact_mod_cast hN2
      push_cast
      calc ((N : ℝ) + n + a) ^ (-s.re - (M + 1) - 1) ≤ ((N : ℝ) + n + a) ^ (-(1 - δ) - 1) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith [n.cast_nonneg (α := ℝ)]) (by linarith)
        _ ≤ ((N : ℝ) + n) ^ (-(1 - δ) - 1) :=
            Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
    have htail := tsum_rpow_neg_sub_one_le hδp (by linarith : 1 - δ ≤ 1) hN2
    have hN1' := rpow_N_sub_one_le hδ0 hδ1.le ht0 hN1t
    have hP : P ≤ K ^ (M + 2) * t ^ ((M : ℝ) + 2) := by
      simp only [P]
      have hf1 : (1 : ℝ) ≤ ((M + 1 + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
      refine (div_le_self (norm_nonneg _) hf1).trans ?_
      refine (norm_cpoch_le (M + 1 + 1) s).trans ?_
      calc (‖s‖ + ((M + 1 + 1 : ℕ) : ℝ)) ^ (M + 1 + 1) ≤ (K * t) ^ (M + 1 + 1) := by
            gcongr; exact hsr _ le_rfl
        _ = K ^ (M + 2) * t ^ ((M : ℝ) + 2) := by
            rw [mul_pow, show ((M : ℝ) + 2) = ((M + 2 : ℕ) : ℝ) by push_cast; ring,
              Real.rpow_natCast]
    calc ‖hurwitzLmSum a N (M + 1) s‖ ≤ P * ∑' n : ℕ, ((N + n : ℝ)) ^ (-(1 - δ) - 1) := hb
      _ ≤ (K ^ (M + 2) * t ^ ((M : ℝ) + 2)) * ((2 * t ^ δ / t) / (1 - δ)) := by
          refine mul_le_mul hP ?_ (by positivity) (by positivity)
          exact htail.trans (div_le_div_of_nonneg_right hN1' hδp.le)
      _ = 2 * K ^ (M + 2) / (1 - δ) * (t ^ ((M : ℝ) + 2) * t ^ δ / t) := by ring
      _ = 2 * K ^ (M + 2) / (1 - δ) * t ^ ((M : ℝ) + 1 + δ) := by
          have e3 : t ^ ((M : ℝ) + 2) * t ^ δ = t ^ ((M : ℝ) + 1 + δ) * t := by
            rw [← tadd, ← Real.rpow_add_one ht0.ne']; ring_nf
          rw [e3, mul_div_assoc, mul_div_cancel_right₀ _ ht0.ne']
  calc ‖X + Y - S - hurwitzLmSum a N (M + 1) s‖
      ≤ ‖X‖ + ‖Y‖ + ‖S‖ + ‖hurwitzLmSum a N (M + 1) s‖ := by
        refine (norm_sub_le _ _).trans ?_
        gcongr
        refine (norm_sub_le _ _).trans ?_
        gcongr
        exact norm_add_le _ _
    _ ≤ T * t ^ ((M : ℝ) + 1 + δ) + T * t ^ ((M : ℝ) + 1 + δ) +
        (M + 1) * (K ^ (M + 1) * (A' + (1 + 1 / δ) * T)) * t ^ ((M : ℝ) + 1 + δ) +
        2 * K ^ (M + 2) / (1 - δ) * t ^ ((M : ℝ) + 1 + δ) := by gcongr
    _ = A * t ^ ((M : ℝ) + 1 + δ) := by simp only [A]; ring

/-- Bounds at all levels `m' ≤ m`: `|ζ(s,a) - a^{-s}| ≤ A |t|^{m'+1+δ}` for
`-m' - δ ≤ σ ≤ -m' + δ`, `|t| ≥ 1`. -/
theorem hurwitz_bound_levels {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) (m : ℕ) :
    ∃ A : ℝ, 0 < A ∧ ∀ m' ≤ m, ∀ a : ℝ, 0 < a → a ≤ 1 → ∀ s : ℂ, -(m' : ℝ) - δ ≤ s.re →
      s.re ≤ -(m' : ℝ) + δ → 1 ≤ |s.im| →
      ‖hurwitzZeta a s - ((a : ℝ) : ℂ) ^ (-s)‖ ≤ A * |s.im| ^ ((m' : ℝ) + 1 + δ) := by
  induction m with
  | zero =>
    obtain ⟨C, hC, hCb⟩ := apostol_thm_12_23_b' hδ0 hδ1
    refine ⟨C, hC, fun m' hm' a ha0 ha1 s h1 h2 ht ↦ ?_⟩
    obtain rfl : m' = 0 := by omega
    simpa using hCb a ha0 ha1 s (by simpa using h1) (by simpa using h2) ht
  | succ m ih =>
    obtain ⟨A, hA, hAb⟩ := ih
    obtain ⟨B, hB, hBb⟩ := apostol_thm_12_23_b hδ0 hδ1
    obtain ⟨A₂, hA₂, hA₂b⟩ := hurwitz_bound_step hδ0 hδ1 (m + 1) (A' := A + B) (by positivity)
      (fun r hr a ha0 ha1 s h1 h2 ht ↦ by
        have hr1 := (mem_Icc.mp hr).1
        have hr2 := (mem_Icc.mp hr).2
        have htp : 0 ≤ |s.im| ^ (((m + 1 : ℕ) : ℝ) - r + 1 + δ) := by positivity
        rcases lt_or_eq_of_le hr2 with hlt | heq
        · have hle : r ≤ m + 1 := Nat.lt_succ_iff.mp hlt
          have hcast : ((m + 1 - r : ℕ) : ℝ) = ((m + 1 : ℕ) : ℝ) - r := by
            rw [Nat.cast_sub hle]
          have h := hAb (m + 1 - r) (by omega) a ha0 ha1 s (by rw [hcast]; linarith)
            (by rw [hcast]; linarith) ht
          rw [hcast] at h
          nlinarith
        · have hrv : (r : ℝ) = ((m + 1 : ℕ) : ℝ) + 1 := by rw [heq]; push_cast; ring
          have h := hBb a ha0 ha1 s (by rw [hrv] at h1; linarith) (by rw [hrv] at h2; linarith) ht
          rw [show ((m + 1 : ℕ) : ℝ) - r + 1 + δ = δ by rw [hrv]; ring]
          have : 0 ≤ |s.im| ^ δ := by positivity
          nlinarith)
    refine ⟨A + A₂, by positivity, fun m' hm' a ha0 ha1 s h1 h2 ht ↦ ?_⟩
    have htp : 0 ≤ |s.im| ^ ((m' : ℝ) + 1 + δ) := by positivity
    rcases lt_or_eq_of_le hm' with hlt | rfl
    · have := hAb m' (Nat.lt_succ_iff.mp hlt) a ha0 ha1 s h1 h2 ht
      nlinarith
    · have := hA₂b a ha0 ha1 s h1 h2 ht
      nlinarith

/-- **Apostol, Theorem 12.23 (b)** (32): for `0 < δ < 1` and `m = 1, 2, …` there is `A > 0`
(depending on `δ` and `m`, not on `s` or `a`) such that `|ζ(s,a)| ≤ A |t|^{m+1+δ}` whenever
`0 < a ≤ 1`, `-m - δ ≤ σ ≤ -m + δ`, `|t| ≥ 1`. -/
@[kb "apostol1976" "Thm 12.23(b), p. 270"]
theorem apostol_thm_12_23_b'' {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) (m : ℕ) (hm : 1 ≤ m) :
    ∃ A : ℝ, 0 < A ∧ ∀ a : ℝ, 0 < a → a ≤ 1 → ∀ s : ℂ, -(m : ℝ) - δ ≤ s.re →
      s.re ≤ -(m : ℝ) + δ → 1 ≤ |s.im| → ‖hurwitzZeta a s‖ ≤ A * |s.im| ^ ((m : ℝ) + 1 + δ) := by
  obtain ⟨A, hA, hAb⟩ := hurwitz_bound_levels hδ0 hδ1 m
  refine ⟨A + 1, by positivity, fun a ha0 ha1 s h1 h2 ht ↦ ?_⟩
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have h := hAb m le_rfl a ha0 ha1 s h1 h2 ht
  have hpow : ‖((a : ℝ) : ℂ) ^ (-s)‖ ≤ 1 := by
    rw [norm_cpow_eq_rpow_re_of_pos ha0, neg_re]
    exact Real.rpow_le_one ha0.le ha1 (by linarith)
  have htp : 1 ≤ |s.im| ^ ((m : ℝ) + 1 + δ) := Real.one_le_rpow ht (by positivity)
  calc ‖hurwitzZeta a s‖ = ‖(hurwitzZeta a s - ((a : ℝ) : ℂ) ^ (-s)) + ((a : ℝ) : ℂ) ^ (-s)‖ := by
        ring_nf
    _ ≤ A * |s.im| ^ ((m : ℝ) + 1 + δ) + 1 := (norm_add_le _ _).trans (add_le_add h hpow)
    _ ≤ (A + 1) * |s.im| ^ ((m : ℝ) + 1 + δ) := by nlinarith

end NTKB.Apostol
