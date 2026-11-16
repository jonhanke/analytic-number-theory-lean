/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Davenport.Zeros.LExceptionalMain
import NTKB.Analytic.Davenport.Zeros.LExplicitReal

/-!
# The explicit formulas of Chapters 17 and 19 at real `x`: the remaining forms

**Davenport, Ch. 17, p. 110, (11) (row 17-15), Ch. 19, pp. 117-118, (F), (9), (11)-(14) (rows 19-7,
19-10, 19-12, 19-14).** The integer forms (`Davenport.explicit_formula_psi0L`,
`Davenport.explicit_formula_psi0L'`, `Davenport.psi0L_exceptional`) are kept; here they are restated
for real `x ≥ 2` with the extra term `log x · min(1, x/(T ⟨x⟩))` of the real Perron step, and at
integers `N ≥ 2` (where `⟨N⟩ ≥ 1`) in the book's form `x log²(xT)/T` (17-15, 19-7).
-/

open Filter Topology Complex Set DirichletCharacter
open scoped Real ComplexConjugate

namespace NTKB

variable {q : ℕ} [NeZero q]

/-- At an integer, the nearest other prime power is at distance at least `1`: `⟨N⟩ ≥ 1`. -/
lemma one_le_distPrimePow_natCast (N : ℕ) : 1 ≤ distPrimePow N := by
  unfold distPrimePow
  have hne : ((fun n : ℕ ↦ |(N : ℝ) - n|) '' {n : ℕ | IsPrimePow n ∧ (n : ℝ) ≠ N}).Nonempty := by
    by_cases h2 : N = 2
    · refine ⟨_, 4, ⟨?_, ?_⟩, rfl⟩
      · have := (Nat.prime_two.isPrimePow).pow (k := 2) (by norm_num)
        simpa using this
      · rw [h2]; norm_num
    · refine ⟨_, 2, ⟨Nat.prime_two.isPrimePow, ?_⟩, rfl⟩
      exact_mod_cast (Ne.symm h2)
  refine le_csInf hne ?_
  rintro _ ⟨n, ⟨_, hn⟩, rfl⟩
  have hn' : n ≠ N := fun h ↦ hn (by rw [h])
  show 1 ≤ |(N : ℝ) - n|
  rcases lt_or_gt_of_ne hn' with h | h
  · have : (n : ℝ) + 1 ≤ N := by exact_mod_cast h
    rw [abs_of_pos (by linarith)]; linarith
  · have : (N : ℝ) + 1 ≤ n := by exact_mod_cast h
    rw [abs_of_neg (by linarith)]; linarith

/-- **Davenport, Ch. 17, p. 110, (11) (row 17-15)**: for integers `N ≥ 2` and `T ≥ 2`,
`|ψ₀(N) - (N - ∑_{|γ| < T} N^ρ/ρ - ζ'(0)/ζ(0) - ½ log(1 - N^{-2}))| ≤ A N log²(NT)/T`. -/
@[kb "davenport1980" "Ch 17, p. 110"]
theorem Davenport.explicit_formula_psi0_nat :
    ∃ A : ℝ, 0 < A ∧ ∀ N : ℕ, 2 ≤ N → ∀ T : ℝ, 2 ≤ T →
      ‖(psi0 N : ℂ) - explicitMain N T‖ ≤ A * N * Real.log (N * T) ^ 2 / T := by
  obtain ⟨A, hA, h⟩ := Davenport.explicit_formula_psi0_real
  refine ⟨2 * A, by positivity, fun N hN T hT ↦ ?_⟩
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : 0 < (N : ℝ) := by linarith
  have hT0 : 0 < T := by linarith
  have e := h N hN2 T hT
  rw [psi0R_natCast] at e
  have hd := one_le_distPrimePow_natCast N
  have hl1 := one_lt_log_mul hN2 hT
  have hlN : Real.log N ≤ Real.log (N * T) := Real.log_le_log hN0 (by nlinarith)
  have hlN0 : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
  have hmin : min 1 ((N : ℝ) / (T * distPrimePow N)) ≤ N / T := by
    refine (min_le_right _ _).trans ?_
    exact div_le_div_of_nonneg_left hN0.le hT0 (by nlinarith)
  have h2 : Real.log N * min 1 ((N : ℝ) / (T * distPrimePow N)) ≤
      N * Real.log (N * T) ^ 2 / T := by
    calc Real.log N * min 1 ((N : ℝ) / (T * distPrimePow N)) ≤ Real.log (N * T) ^ 2 * (N / T) :=
          mul_le_mul (by nlinarith) hmin
            (le_min zero_le_one (div_nonneg hN0.le (mul_nonneg hT0.le (by linarith))))
            (by positivity)
      _ = N * Real.log (N * T) ^ 2 / T := by ring
  have hX : 0 ≤ (N : ℝ) * Real.log (N * T) ^ 2 / T := by positivity
  calc _ ≤ A * ((N : ℝ) * Real.log (N * T) ^ 2 / T +
          Real.log N * min 1 ((N : ℝ) / (T * distPrimePow N))) := e
    _ ≤ A * (2 * ((N : ℝ) * Real.log (N * T) ^ 2 / T)) := by gcongr; linarith
    _ = 2 * A * N * Real.log (N * T) ^ 2 / T := by ring

/-- **Davenport, Ch. 19, p. 117, (F) (row 19-7)**: for primitive `χ` mod `q > 1`, integers `N ≥ 2`,
`T ≥ 2`, with `ℓ = log q + log N + log T`,
`|ψ₀(N, χ) - (r₀ - ∑_{|γ|<T} N^ρ/ρ + ∑_{m ≥ 1} N^{a-2m}/(2m - a))| ≤ A N ℓ²/T`. -/
@[kb "davenport1980" "Ch 19, p. 117"]
theorem Davenport.explicit_formula_psi0L_nat :
    ∃ A : ℝ, 0 < A ∧ ∀ {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
      (hq : q ≠ 1), ∀ N : ℕ, 2 ≤ N → ∀ T : ℝ, 2 ≤ T →
      ‖psi0L χ N - (residueZeroL χ N - ∑ ρ ∈ zerosBelowL hχ hq T, perronKernel N ρ.val +
          trivialSumL χ N)‖ ≤
        A * (N * (Real.log q + Real.log N + Real.log T) ^ 2 / T) := by
  obtain ⟨A, hA, h⟩ := Davenport.explicit_formula_psi0L_real
  refine ⟨2 * A, by positivity, fun {q} _ {χ} hχ hq N hN T hT ↦ ?_⟩
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : 0 < (N : ℝ) := by linarith
  have hT0 : 0 < T := by linarith
  have e := h hχ hq N hN2 T hT
  rw [psi0LR_natCast] at e
  have hd := one_le_distPrimePow_natCast N
  have hl2 := log_two_gt_two_thirds
  have hlN2 : Real.log 2 ≤ Real.log N := Real.log_le_log two_pos hN2
  have hlT2 : Real.log 2 ≤ Real.log T := Real.log_le_log two_pos hT
  have hlq : 0 ≤ Real.log q := Real.log_natCast_nonneg q
  set ℓ := Real.log q + Real.log N + Real.log T with hℓ
  have hℓ1 : 1 ≤ ℓ := by rw [hℓ]; linarith
  have hlNℓ : Real.log N ≤ ℓ := by rw [hℓ]; linarith
  have hlN0 : 0 ≤ Real.log N := by linarith
  have hmin : min 1 ((N : ℝ) / (T * distPrimePow N)) ≤ N / T := by
    refine (min_le_right _ _).trans ?_
    exact div_le_div_of_nonneg_left hN0.le hT0 (by nlinarith)
  have h2 : Real.log N * min 1 ((N : ℝ) / (T * distPrimePow N)) ≤ N * ℓ ^ 2 / T := by
    calc Real.log N * min 1 ((N : ℝ) / (T * distPrimePow N)) ≤ ℓ ^ 2 * (N / T) :=
          mul_le_mul (by nlinarith) hmin
            (le_min zero_le_one (div_nonneg hN0.le (mul_nonneg hT0.le (by linarith))))
            (by positivity)
      _ = N * ℓ ^ 2 / T := by ring
  have hX : 0 ≤ (N : ℝ) * ℓ ^ 2 / T := by positivity
  calc _ ≤ A * ((N : ℝ) * ℓ ^ 2 / T + Real.log N * min 1 ((N : ℝ) / (T * distPrimePow N))) := e
    _ ≤ A * (2 * ((N : ℝ) * ℓ ^ 2 / T)) := by gcongr; linarith
    _ = 2 * A * (N * ℓ ^ 2 / T) := by ring

omit [NeZero q] in
/-- The trivial-zero sum is bounded by `4/3` for `x ≥ 2`. -/
lemma norm_trivialSumL_le (χ : DirichletCharacter ℂ q) {x : ℝ} (hx : 2 ≤ x) :
    ‖trivialSumL χ x‖ ≤ 4 / 3 := by
  classical
  have hx0 : 0 < x := by linarith
  have hb : ∀ n : ℕ, ‖(if trivialZeroL χ n = 0 then 0 else -perronKernel x (trivialZeroL χ n))‖ ≤
      (1 / 4 : ℝ) ^ n := by
    intro n
    split_ifs with h
    · simp
    · rw [norm_neg, norm_perronKernel hx0]
      have hre := trivialZeroL_re_lt h
      have hn1 : 1 ≤ ‖trivialZeroL χ n‖ := by
        have := Complex.abs_re_le_norm (trivialZeroL χ n)
        rw [abs_of_neg (by linarith)] at this; linarith
      have ha0 := dirichletParity_re_nonneg χ
      have h1 : x ^ (trivialZeroL χ n).re ≤ x ^ (-(2 * n : ℝ)) := by
        apply Real.rpow_le_rpow_of_exponent_le (by linarith)
        rw [trivialZeroL_re]; linarith
      have h2 : x ^ (-(2 * n : ℝ)) ≤ (1 / 4 : ℝ) ^ n := by
        rw [Real.rpow_neg hx0.le, show (2 * n : ℝ) = ((2 * n : ℕ) : ℝ) by push_cast; ring,
          Real.rpow_natCast, pow_mul, ← inv_pow, one_div]
        apply pow_le_pow_left₀ (by positivity)
        rw [inv_le_inv₀ (by positivity) (by norm_num)]
        nlinarith
      calc x ^ (trivialZeroL χ n).re / ‖trivialZeroL χ n‖ ≤ x ^ (trivialZeroL χ n).re / 1 :=
            div_le_div_of_nonneg_left (by positivity) one_pos hn1
        _ ≤ (1 / 4 : ℝ) ^ n := by rw [div_one]; exact h1.trans h2
  have hg := hasSum_geometric_of_lt_one (r := (1 / 4 : ℝ)) (by norm_num) (by norm_num)
  have := tsum_of_norm_bounded hg hb
  rw [trivialSumL]
  refine this.trans (le_of_eq ?_)
  norm_num

/-- **Davenport, Ch. 19, p. 117, (D)-(E) (row 19-6)** without the trivial zeros, for real `x`:
`|ψ₀(x, χ) - (r₀ - ∑_{|γ|<T} x^ρ/ρ)| ≤ A (x ℓ²/T + T ℓ x^{-1/2} + log x · min(1, x/(T ⟨x⟩)))`,
`ℓ = log q + log x + log T`. -/
@[kb "davenport1980" "Ch 19, p. 117"]
theorem Davenport.explicit_formula_psi0LR :
    ∃ A : ℝ, 0 < A ∧ ∀ {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
      (hq : q ≠ 1), ∀ x : ℝ, 2 ≤ x → ∀ T : ℝ, 2 ≤ T →
      ‖psi0LR χ x - (residueZeroL χ x - ∑ ρ ∈ zerosBelowL hχ hq T, perronKernel x ρ.val)‖ ≤
        A * (x * (Real.log q + Real.log x + Real.log T) ^ 2 / T +
          T * (Real.log q + Real.log x + Real.log T) * x ^ (-1 / 2 : ℝ) +
          Real.log x * min 1 (x / (T * distPrimePow x))) := by
  obtain ⟨A, hA, h⟩ := Davenport.explicit_formula_psi0L_real
  refine ⟨A + 1, by positivity, fun {q} _ {χ} hχ hq x hx T hT ↦ ?_⟩
  have hx0 : 0 < x := by linarith
  have hT0 : 0 < T := by linarith
  have e := h hχ hq x hx T hT
  have et := norm_trivialSumL_le χ hx
  have hl2 := log_two_gt_two_thirds
  have hlx2 : Real.log 2 ≤ Real.log x := Real.log_le_log two_pos hx
  have hlT2 : Real.log 2 ≤ Real.log T := Real.log_le_log two_pos hT
  have hlq : 0 ≤ Real.log q := Real.log_natCast_nonneg q
  set ℓ := Real.log q + Real.log x + Real.log T with hℓ
  have hℓ1 : 1 ≤ ℓ := by rw [hℓ]; linarith
  have hlx0 : 0 ≤ Real.log x := by linarith
  have hd := distPrimePow_pos x
  have hX6 : 0 ≤ Real.log x * min 1 (x / (T * distPrimePow x)) :=
    mul_nonneg hlx0 (le_min zero_le_one (div_nonneg hx0.le (mul_nonneg hT0.le hd.le)))
  set s := x ^ (-1 / 2 : ℝ) with hs
  have hs0 : 0 < s := Real.rpow_pos_of_pos hx0 _
  have hs1 : s ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
  have hs2 : s * s = x⁻¹ := by
    rw [hs, ← Real.rpow_add hx0, show (-1 / 2 : ℝ) + -1 / 2 = -1 by norm_num, Real.rpow_neg_one]
  have hxs : 1 ≤ x * s := by
    have : x * (s * s) = 1 := by rw [hs2]; field_simp
    nlinarith
  -- AM-GM: `X1 + X2 ≥ 2`
  have hamgm : 2 ≤ x * ℓ ^ 2 / T + T * ℓ * s := by
    set a := x * ℓ ^ 2 / T with ha
    set b := T * ℓ * s with hb
    have ha0 : 0 < a := by positivity
    have hb0 : 0 < b := by positivity
    have hab : a * b = ℓ ^ 3 * (x * s) := by
      rw [ha, hb]; field_simp
    have hab1 : 1 ≤ a * b := by
      rw [hab]
      have : 1 ≤ ℓ ^ 3 := one_le_pow₀ hℓ1
      nlinarith
    nlinarith [sq_nonneg (a - b), sq_nonneg (a + b - 2)]
  have e2 : ‖psi0LR χ x - (residueZeroL χ x - ∑ ρ ∈ zerosBelowL hχ hq T, perronKernel x ρ.val)‖ ≤
      ‖psi0LR χ x - (residueZeroL χ x - ∑ ρ ∈ zerosBelowL hχ hq T, perronKernel x ρ.val +
        trivialSumL χ x)‖ + ‖trivialSumL χ x‖ := by
    have : psi0LR χ x - (residueZeroL χ x - ∑ ρ ∈ zerosBelowL hχ hq T, perronKernel x ρ.val) =
        (psi0LR χ x - (residueZeroL χ x - ∑ ρ ∈ zerosBelowL hχ hq T, perronKernel x ρ.val +
          trivialSumL χ x)) + trivialSumL χ x := by ring
    rw [this]; exact norm_add_le _ _
  have hX1 : 0 ≤ x * ℓ ^ 2 / T := by positivity
  have hX2 : 0 ≤ T * ℓ * s := by positivity
  nlinarith [mul_nonneg hA.le hX1, mul_nonneg hA.le hX2, mul_nonneg hA.le hX6]

/-- **Davenport, Ch. 19, p. 118, (9) (row 19-10)** for real `x ≥ 2`:
`|ψ₀(x, χ) - (∑_{|γ|<1} 1/ρ - ∑_{|γ|<T} x^ρ/ρ)| ≤
A (x ℓ²/T + T ℓ x^{-1/2} + ℓ + log x · min(1, x/(T ⟨x⟩)))`. -/
@[kb "davenport1980" "Ch 19, p. 118"]
theorem Davenport.explicit_formula_psi0LR' :
    ∃ A : ℝ, 0 < A ∧ ∀ {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
      (hq : q ≠ 1), ∀ x : ℝ, 2 ≤ x → ∀ T : ℝ, 2 ≤ T →
      ‖psi0LR χ x - (∑ ρ ∈ zerosBelowL hχ hq 1, 1 / ρ.val -
          ∑ ρ ∈ zerosBelowL hχ hq T, perronKernel x ρ.val)‖ ≤
        A * (x * (Real.log q + Real.log x + Real.log T) ^ 2 / T +
          T * (Real.log q + Real.log x + Real.log T) * x ^ (-1 / 2 : ℝ) +
          (Real.log q + Real.log x + Real.log T) +
          Real.log x * min 1 (x / (T * distPrimePow x))) := by
  obtain ⟨A₁, hA₁, h₁⟩ := Davenport.explicit_formula_psi0LR
  obtain ⟨A₂, hA₂, h₂⟩ := Davenport.norm_bChar_add_sum_le
  refine ⟨A₁ + 2 * A₂ + 2, by positivity, ?_⟩
  intro q _ χ hχ hq x hx T hT
  have e1 := h₁ hχ hq x hx T hT
  have e2 := h₂ hχ hq
  have hx0 : 0 < x := by linarith
  have hT0 : 0 < T := by linarith
  have hl2 := log_two_gt_two_thirds
  have hlx2 : Real.log 2 ≤ Real.log x := Real.log_le_log two_pos hx
  have hlT2 : Real.log 2 ≤ Real.log T := Real.log_le_log two_pos hT
  have hlx : 0 < Real.log x := by linarith
  have hlq : 0 ≤ Real.log q := Real.log_natCast_nonneg q
  have hlT : 0 ≤ Real.log T := by linarith
  have hd := distPrimePow_pos x
  have hX6 : 0 ≤ Real.log x * min 1 (x / (T * distPrimePow x)) :=
    mul_nonneg hlx.le (le_min zero_le_one (div_nonneg hx0.le (mul_nonneg hT0.le hd.le)))
  set ℓ := Real.log q + Real.log x + Real.log T with hℓ
  set M := ∑ ρ ∈ zerosBelowL hχ hq T, perronKernel x ρ.val
  set S := ∑ ρ ∈ zerosBelowL hχ hq 1, 1 / ρ.val
  set X6 := Real.log x * min 1 (x / (T * distPrimePow x)) with hX6def
  have hsplit : psi0LR χ x - (S - M) = (psi0LR χ x - (residueZeroL χ x - M)) +
      (residueZeroL χ x + bChar χ) - (bChar χ + S) := by ring
  rw [hsplit]
  have hr : ‖residueZeroL χ x + bChar χ‖ ≤ Real.log x := by
    rw [residueZeroL_eq]
    split_ifs
    · simp; linarith
    · simp only [sub_add_cancel, norm_neg, Complex.norm_real, Real.norm_eq_abs]
      rw [abs_of_pos (by linarith)]
  set E := x ^ (-1 / 2 : ℝ) with hE
  have hE0 : 0 ≤ E := Real.rpow_nonneg hx0.le _
  have hℓ0 : 0 ≤ ℓ := by rw [hℓ]; linarith
  have hP : 0 ≤ x * ℓ ^ 2 / T + T * ℓ * E := by positivity
  have hℓx : Real.log x ≤ ℓ := by rw [hℓ]; linarith
  have hq' : Real.log q + 1 ≤ 2 * ℓ := by rw [hℓ]; linarith
  calc ‖psi0LR χ x - (residueZeroL χ x - M) + (residueZeroL χ x + bChar χ) - (bChar χ + S)‖
      ≤ ‖psi0LR χ x - (residueZeroL χ x - M)‖ + ‖residueZeroL χ x + bChar χ‖ + ‖bChar χ + S‖ :=
        (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ A₁ * (x * ℓ ^ 2 / T + T * ℓ * E + X6) + Real.log x + A₂ * (Real.log q + 1) := by
        gcongr
    _ ≤ (A₁ + 2 * A₂ + 2) * (x * ℓ ^ 2 / T + T * ℓ * E + ℓ + X6) := by
        have h3 : A₂ * (Real.log q + 1) ≤ A₂ * (2 * ℓ) := by gcongr
        nlinarith [mul_nonneg hA₁.le hP, mul_nonneg hA₂.le hP, mul_nonneg hA₂.le hX6,
          mul_nonneg hA₁.le hℓ0, mul_nonneg hA₂.le hℓ0]

open scoped Classical in
set_option maxHeartbeats 2000000 in
/-- **Davenport, Ch. 19, (11)-(14) (rows 19-12, 19-14)** for real `x ≥ 2`, `T ≥ 2`, with
`ℓ = log q + log x + log T`:
`|ψ₀(x, χ) + ∑_{exceptional ρ, |γ| < T} x^ρ/ρ| ≤ A (x ℓ²/T + T ℓ x^{-1/2} + ℓ² + ℓ x^{1/2} log x
  + x ℓ² exp(-c log x/log(qT)) + log x · min(1, x/(T ⟨x⟩)))`, `c = 1/16200`. -/
@[kb "davenport1980" "Ch 19, p. 119"]
theorem Davenport.psi0LR_exceptional :
    ∃ A : ℝ, 0 < A ∧ ∀ {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
      (hq : q ≠ 1), ∀ x : ℝ, 2 ≤ x → ∀ T : ℝ, 2 ≤ T →
      ‖psi0LR χ x + ∑ ρ ∈ (zerosBelowL hχ hq T).filter (fun ρ ↦ IsExcPoint q ρ.val),
          perronKernel x ρ.val‖ ≤
        A * (x * (Real.log q + Real.log x + Real.log T) ^ 2 / T +
          T * (Real.log q + Real.log x + Real.log T) * x ^ (-1 / 2 : ℝ) +
          (Real.log q + Real.log x + Real.log T) ^ 2 +
          (Real.log q + Real.log x + Real.log T) * x ^ (1 / 2 : ℝ) * Real.log x +
          x * (Real.log q + Real.log x + Real.log T) ^ 2 *
            Real.exp (-(1 / 16200 * Real.log x / logQT q T)) +
          Real.log x * min 1 (x / (T * distPrimePow x))) := by
  obtain ⟨A₁, hA₁, h₁⟩ := Davenport.explicit_formula_psi0LR'
  obtain ⟨A₆, hA₆, h₆⟩ := card_zerosBelowL_one_le
  obtain ⟨C₇, hC₇, h₇⟩ := Davenport.sum_L_zeros_inv_norm_le
  refine ⟨A₁ + 70000 * A₆ + C₇ + 1, by positivity, ?_⟩
  intro q _ χ hχ hq x hx T hT
  have hχ1 := ne_one_of_isPrimitive hχ hq
  have hq2 := two_le_of_ne_one hχ1
  have hx0 : (0 : ℝ) < x := by linarith
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hT0 : 0 < T := by linarith
  have hl2 := log_two_gt_two_thirds
  have hlx2 : Real.log 2 ≤ Real.log x := Real.log_le_log two_pos hx
  have hlT2 : Real.log 2 ≤ Real.log T := Real.log_le_log two_pos hT
  have hlx : 0 < Real.log x := by linarith
  have hlq : 0 < Real.log q := Real.log_pos (by linarith)
  have hlT : 0 < Real.log T := by linarith
  have hd := distPrimePow_pos x
  set ℓ := Real.log q + Real.log x + Real.log T with hℓ
  have hℓ1 : 1 ≤ ℓ := by linarith
  have hℓ0 : 0 ≤ ℓ := by linarith
  set Z1 := zerosBelowL hχ hq 1
  set ZT := zerosBelowL hχ hq T
  set E := Real.exp (-(1 / 16200 * Real.log x / logQT q T))
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  set P : ZeroIndex (dirichletXi χ) → Prop := fun ρ ↦ IsExcPoint q ρ.val with hP
  set M : ZeroIndex (dirichletXi χ) → Prop := fun ρ ↦ IsExcPoint q (1 - conj ρ.val) with hM
  set k : ZeroIndex (dirichletXi χ) → ℂ := fun ρ ↦ perronKernel x ρ.val with hk
  set iv : ZeroIndex (dirichletXi χ) → ℂ := fun ρ ↦ 1 / ρ.val with hiv
  have e₁ := h₁ hχ hq x hx T hT
  have hc1 := h₆ hχ hq
  set c1 : ℝ := (Z1.card : ℝ)
  set X6 := Real.log x * min 1 (x / (T * distPrimePow x)) with hX6def
  have hX6 : 0 ≤ X6 :=
    mul_nonneg hlx.le (le_min zero_le_one (div_nonneg hx0.le (mul_nonneg hT0.le hd.le)))
  -- structural facts
  have hPim : ∀ ρ, P ρ → ρ.val.im = 0 := fun ρ h ↦
    (Davenport.exceptional_zero_real hχ1 (dirichletXi_zero_mem hχ hq ρ).1 h).2
  have hMim : ∀ ρ, M ρ → ρ.val.im = 0 := fun ρ h ↦ (mirror_exc_real hχ hq ρ h).1
  -- the decomposition
  have hsT : ∑ ρ ∈ ZT, k ρ = ∑ ρ ∈ ZT.filter P, k ρ +
      (∑ ρ ∈ ZT.filter (fun ρ ↦ ¬ P ρ ∧ M ρ), k ρ +
        ∑ ρ ∈ ZT.filter (fun ρ ↦ ¬ P ρ ∧ ¬ M ρ), k ρ) := by
    have h1 := Finset.sum_filter_add_sum_filter_not ZT P k
    have h2 := Finset.sum_filter_add_sum_filter_not (ZT.filter (fun ρ ↦ ¬ P ρ)) M k
    rw [Finset.filter_filter, Finset.filter_filter] at h2
    rw [h2]; exact h1.symm
  have hs1 : ∑ ρ ∈ Z1, iv ρ = ∑ ρ ∈ Z1.filter P, iv ρ +
      (∑ ρ ∈ Z1.filter (fun ρ ↦ ¬ P ρ ∧ M ρ), iv ρ +
        ∑ ρ ∈ Z1.filter (fun ρ ↦ ¬ P ρ ∧ ¬ M ρ), iv ρ) := by
    have h1 := Finset.sum_filter_add_sum_filter_not Z1 P iv
    have h2 := Finset.sum_filter_add_sum_filter_not (Z1.filter (fun ρ ↦ ¬ P ρ)) M iv
    rw [Finset.filter_filter, Finset.filter_filter] at h2
    rw [h2]; exact h1.symm
  have hTM : ZT.filter (fun ρ ↦ ¬ P ρ ∧ M ρ) = Z1.filter (fun ρ ↦ ¬ P ρ ∧ M ρ) := by
    ext ρ
    simp only [Finset.mem_filter, ZT, Z1, mem_zerosBelowL]
    constructor
    · rintro ⟨-, h⟩; exact ⟨by rw [hMim ρ h.2]; simp, h⟩
    · rintro ⟨h1, h⟩; exact ⟨h1.trans_le (by linarith), h⟩
  have hid : psi0LR χ x + ∑ ρ ∈ ZT.filter P, k ρ =
      (psi0LR χ x - (∑ ρ ∈ Z1, iv ρ - ∑ ρ ∈ ZT, k ρ)) + ∑ ρ ∈ Z1.filter P, iv ρ +
        ∑ ρ ∈ Z1.filter (fun ρ ↦ ¬ P ρ ∧ M ρ), (iv ρ - k ρ) +
        ∑ ρ ∈ Z1.filter (fun ρ ↦ ¬ P ρ ∧ ¬ M ρ), iv ρ -
        ∑ ρ ∈ ZT.filter (fun ρ ↦ ¬ P ρ ∧ ¬ M ρ), k ρ := by
    rw [hsT, hs1, hTM, Finset.sum_sub_distrib]
    ring
  rw [hid]
  -- the bounds
  have B1 : ‖∑ ρ ∈ Z1.filter P, iv ρ‖ ≤ 2 * c1 := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ ρ ∈ Z1.filter P, ‖iv ρ‖ ≤ ∑ ρ ∈ Z1.filter P, (2 : ℝ) :=
          Finset.sum_le_sum fun ρ hρ ↦ norm_inv_le_of_exc hχ1 (Finset.mem_filter.mp hρ).2
      _ ≤ 2 * c1 := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
          gcongr; exact Nat.cast_le.mpr (Finset.card_filter_le _ _)
  have hxh : 0 ≤ x ^ (1 / 2 : ℝ) * Real.log x := mul_nonneg (Real.rpow_nonneg hx0.le _) hlx.le
  have B2 : ‖∑ ρ ∈ Z1.filter (fun ρ ↦ ¬ P ρ ∧ M ρ), (iv ρ - k ρ)‖ ≤
      c1 * (x ^ (1 / 2 : ℝ) * Real.log x) := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ ρ ∈ Z1.filter (fun ρ ↦ ¬ P ρ ∧ M ρ), ‖iv ρ - k ρ‖
        ≤ ∑ ρ ∈ Z1.filter (fun ρ ↦ ¬ P ρ ∧ M ρ), x ^ (1 / 2 : ℝ) * Real.log x :=
          Finset.sum_le_sum fun ρ hρ ↦
            norm_inv_sub_kernel_le_of_mirror hχ hq ρ (Finset.mem_filter.mp hρ).2.2 hx1
      _ ≤ c1 * (x ^ (1 / 2 : ℝ) * Real.log x) := by
          rw [Finset.sum_const, nsmul_eq_mul]
          gcongr; exact Nat.cast_le.mpr (Finset.card_filter_le _ _)
  have B3 : ‖∑ ρ ∈ Z1.filter (fun ρ ↦ ¬ P ρ ∧ ¬ M ρ), iv ρ‖ ≤ c1 * (16200 * Real.log q) := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ ρ ∈ Z1.filter (fun ρ ↦ ¬ P ρ ∧ ¬ M ρ), ‖iv ρ‖
        ≤ ∑ ρ ∈ Z1.filter (fun ρ ↦ ¬ P ρ ∧ ¬ M ρ), 16200 * Real.log q := by
          refine Finset.sum_le_sum fun ρ hρ ↦ ?_
          rw [Finset.mem_filter] at hρ
          exact norm_inv_le_of_not_mirror hχ1 (mem_zerosBelowL.mp hρ.1)
            (dirichletXi_zero_mem hχ hq ρ).2.1 hρ.2.2
      _ ≤ c1 * (16200 * Real.log q) := by
          rw [Finset.sum_const, nsmul_eq_mul]
          gcongr; exact Nat.cast_le.mpr (Finset.card_filter_le _ _)
  -- the remaining zeros up to `T`
  set u : ZeroIndex (dirichletXi χ) → ℝ := fun ρ ↦
    if |ρ.val.im| < 1 then 16200 * Real.log q else 0
  set w : ZeroIndex (dirichletXi χ) → ℝ := fun ρ ↦ if 1 ≤ |ρ.val.im| then 1 / ‖ρ.val‖ else 0
  have hu0 : ∀ ρ, 0 ≤ u ρ := fun ρ ↦ by simp only [u]; split_ifs <;> positivity
  have hw0 : ∀ ρ, 0 ≤ w ρ := fun ρ ↦ by simp only [w]; split_ifs <;> positivity
  have hsumu : ∑ ρ ∈ ZT, u ρ = c1 * (16200 * Real.log q) := by
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    have : ZT.filter (fun ρ ↦ |ρ.val.im| < 1) = Z1 := by
      ext ρ; simp only [Finset.mem_filter, ZT, Z1, mem_zerosBelowL]
      constructor
      · exact fun h ↦ h.2
      · exact fun h ↦ ⟨h.trans_le (by linarith), h⟩
    rw [this]
  have hsumw := h₇ hχ hq T hT
  have hxE : 0 ≤ x * E := mul_nonneg hx0.le hE0
  have B4 : ‖∑ ρ ∈ ZT.filter (fun ρ ↦ ¬ P ρ ∧ ¬ M ρ), k ρ‖ ≤
      x * E * (c1 * (16200 * Real.log q) + C₇ * (Real.log q + Real.log T) * Real.log T) := by
    refine (norm_sum_le _ _).trans ?_
    have hpt : ∀ ρ ∈ ZT.filter (fun ρ ↦ ¬ P ρ ∧ ¬ M ρ), ‖k ρ‖ ≤ x * E * (u ρ + w ρ) := by
      intro ρ hρ
      rw [Finset.mem_filter] at hρ
      have hβ := dirichletXi_zero_mem hχ hq ρ
      have hρ0 : 0 < ‖ρ.val‖ := by linarith [Complex.re_le_norm ρ.val, hβ.2.1]
      simp only [k]
      rw [norm_perronKernel hx0]
      have hc := norm_cpow_le_of_not_exc hχ1 hx1 (by linarith) (mem_zerosBelowL.mp hρ.1) hρ.2.1
      have hinv : 1 / ‖ρ.val‖ ≤ u ρ + w ρ := by
        simp only [u, w]
        by_cases h1 : |ρ.val.im| < 1
        · have := norm_inv_le_of_not_mirror hχ1 h1 hβ.2.1 hρ.2.2
          rw [norm_div, norm_one] at this
          rw [if_pos h1, if_neg (not_le.mpr h1)]; linarith
        · rw [if_neg h1, if_pos (not_lt.mp h1)]; linarith
      calc x ^ ρ.val.re / ‖ρ.val‖ = x ^ ρ.val.re * (1 / ‖ρ.val‖) := by ring
        _ ≤ (x * E) * (u ρ + w ρ) := by
            apply mul_le_mul hc hinv (by positivity) hxE
    calc ∑ ρ ∈ ZT.filter (fun ρ ↦ ¬ P ρ ∧ ¬ M ρ), ‖k ρ‖
        ≤ ∑ ρ ∈ ZT.filter (fun ρ ↦ ¬ P ρ ∧ ¬ M ρ), x * E * (u ρ + w ρ) := Finset.sum_le_sum hpt
      _ ≤ ∑ ρ ∈ ZT, x * E * (u ρ + w ρ) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          intro ρ _ _; exact mul_nonneg hxE (add_nonneg (hu0 ρ) (hw0 ρ))
      _ = x * E * (∑ ρ ∈ ZT, u ρ + ∑ ρ ∈ ZT, w ρ) := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib]
      _ ≤ x * E * (c1 * (16200 * Real.log q) + C₇ * (Real.log q + Real.log T) * Real.log T) := by
          rw [hsumu]; gcongr
  -- assemble
  have hc1' : c1 ≤ 2 * A₆ * ℓ := by
    have : Real.log q + 1 ≤ 2 * ℓ := by rw [hℓ]; linarith
    calc c1 ≤ A₆ * (Real.log q + 1) := hc1
      _ ≤ A₆ * (2 * ℓ) := by gcongr
      _ = 2 * A₆ * ℓ := by ring
  have hc10 : 0 ≤ c1 := by positivity
  have hlqℓ : Real.log q ≤ ℓ := by rw [hℓ]; linarith
  have hqTℓ : (Real.log q + Real.log T) * Real.log T ≤ ℓ ^ 2 := by
    have h1 : Real.log q + Real.log T ≤ ℓ := by rw [hℓ]; linarith
    have h2 : Real.log T ≤ ℓ := by rw [hℓ]; linarith
    nlinarith
  set X1 := x * ℓ ^ 2 / T
  set X2 := T * ℓ * x ^ (-1 / 2 : ℝ)
  set X3 := ℓ ^ 2
  set X4 := ℓ * x ^ (1 / 2 : ℝ) * Real.log x
  set X5 := x * ℓ ^ 2 * E
  have hX1 : 0 ≤ X1 := by positivity
  have hX2 : 0 ≤ X2 := mul_nonneg (mul_nonneg hT0.le hℓ0) (Real.rpow_nonneg hx0.le _)
  have hX3 : 0 ≤ X3 := by positivity
  have hX4 : 0 ≤ X4 := mul_nonneg (mul_nonneg hℓ0 (Real.rpow_nonneg hx0.le _)) hlx.le
  have hX5 : 0 ≤ X5 := mul_nonneg (mul_nonneg hx0.le (by positivity)) hE0
  have hℓ2 : ℓ ≤ ℓ ^ 2 := by nlinarith
  have b1 : ‖psi0LR χ x - (∑ ρ ∈ Z1, iv ρ - ∑ ρ ∈ ZT, k ρ)‖ ≤ A₁ * (X1 + X2 + X3 + X6) := by
    refine e₁.trans ?_
    gcongr
  have b2 : 2 * c1 ≤ 4 * A₆ * X3 := by nlinarith
  have b3 : c1 * (x ^ (1 / 2 : ℝ) * Real.log x) ≤ 2 * A₆ * X4 := by
    calc c1 * (x ^ (1 / 2 : ℝ) * Real.log x) ≤ 2 * A₆ * ℓ * (x ^ (1 / 2 : ℝ) *
          Real.log x) := by gcongr
      _ = 2 * A₆ * X4 := by simp only [X4]; ring
  have b4 : c1 * (16200 * Real.log q) ≤ 32400 * A₆ * X3 := by
    calc c1 * (16200 * Real.log q) ≤ 2 * A₆ * ℓ * (16200 * ℓ) := by gcongr
      _ = 32400 * A₆ * X3 := by simp only [X3]; ring
  have b5 : x * E * (c1 * (16200 * Real.log q) + C₇ * (Real.log q + Real.log T) * Real.log T) ≤
      (32400 * A₆ + C₇) * X5 := by
    have h1 : c1 * (16200 * Real.log q) + C₇ * (Real.log q + Real.log T) * Real.log T ≤
        (32400 * A₆ + C₇) * ℓ ^ 2 := by
      have : C₇ * ((Real.log q + Real.log T) * Real.log T) ≤ C₇ * ℓ ^ 2 := by gcongr
      nlinarith
    calc x * E * (c1 * (16200 * Real.log q) + C₇ * (Real.log q + Real.log T) * Real.log T)
        ≤ x * E * ((32400 * A₆ + C₇) * ℓ ^ 2) := by gcongr
      _ = (32400 * A₆ + C₇) * X5 := by simp only [X5]; ring
  have htri : ‖psi0LR χ x - (∑ ρ ∈ Z1, iv ρ - ∑ ρ ∈ ZT, k ρ) + ∑ ρ ∈ Z1.filter P, iv ρ +
        ∑ ρ ∈ Z1.filter (fun ρ ↦ ¬ P ρ ∧ M ρ), (iv ρ - k ρ) +
        ∑ ρ ∈ Z1.filter (fun ρ ↦ ¬ P ρ ∧ ¬ M ρ), iv ρ -
        ∑ ρ ∈ ZT.filter (fun ρ ↦ ¬ P ρ ∧ ¬ M ρ), k ρ‖
      ≤ ‖psi0LR χ x - (∑ ρ ∈ Z1, iv ρ - ∑ ρ ∈ ZT, k ρ)‖ + ‖∑ ρ ∈ Z1.filter P, iv ρ‖ +
        ‖∑ ρ ∈ Z1.filter (fun ρ ↦ ¬ P ρ ∧ M ρ), (iv ρ - k ρ)‖ +
        ‖∑ ρ ∈ Z1.filter (fun ρ ↦ ¬ P ρ ∧ ¬ M ρ), iv ρ‖ +
        ‖∑ ρ ∈ ZT.filter (fun ρ ↦ ¬ P ρ ∧ ¬ M ρ), k ρ‖ := by
    refine (norm_sub_le _ _).trans (add_le_add ?_ le_rfl)
    refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
    refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
    exact norm_add_le _ _
  refine htri.trans ?_
  have hsum := add_le_add (add_le_add (add_le_add (add_le_add b1 (B1.trans b2)) (B2.trans b3))
    (B3.trans b4)) (B4.trans b5)
  refine hsum.trans ?_
  nlinarith [mul_nonneg hA₁.le hX4, mul_nonneg hA₁.le hX5, mul_nonneg hA₆.le hX1,
    mul_nonneg hA₆.le hX2, mul_nonneg hA₆.le hX3, mul_nonneg hA₆.le hX4,
    mul_nonneg hA₆.le hX5, mul_nonneg hA₆.le hX6, mul_nonneg hC₇.le hX1, mul_nonneg hC₇.le hX2,
    mul_nonneg hC₇.le hX3, mul_nonneg hC₇.le hX4, mul_nonneg hC₇.le hX5, mul_nonneg hC₇.le hX6]

end NTKB
