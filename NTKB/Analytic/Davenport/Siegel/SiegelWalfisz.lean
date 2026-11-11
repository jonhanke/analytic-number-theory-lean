/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Davenport.Siegel.Siegel
import NTKB.Analytic.Davenport.Zeros.PNTCharacter
import NTKB.Analytic.Davenport.Zeros.APDecomp
import NTKB.Analytic.Davenport.Sieve.Bombieri
import NTKB.Analytic.Davenport.Sieve.BarbanDavenportHalberstam

/-!
# The Siegel–Walfisz theorem (Davenport, Chapter 22)

* `siegel_walfisz_char`: **Davenport, Ch. 22, (C)**: for every `N > 0` there are `c, C > 0` with
  `|ψ(x, χ)| ≤ C x exp(-c √log x)` for every nonprincipal `χ` mod `q ≤ (log x)^N`, `x ≥ 2`.
  Proof as in the book: (8) of §20 (`Davenport.psi0L_sub_exceptional_le`) for the primitive
  character inducing `χ`, the exceptional zero `β₁` bounded by Siegel's theorem
  (`siegel_real_zero_le` with `ε = 1/(2N)`), so that `x^{β₁} ≤ x exp(-C₃ √log x)`.
* `siegelWalfiszHypothesis`: the named input `SiegelWalfiszHypothesis` of the sieve chapters is
  proved (its first field is the prime number theorem with the classical error term,
  `Davenport.psi_sub_self_le`).
* `siegel_walfisz`: **Davenport, Ch. 22, (D)** (the Siegel–Walfisz theorem): uniformly for
  `q ≤ (log x)^N` and `(a, q) = 1`, `ψ(x; q, a) = x/φ(q) + O(x exp(-C₄(N) √log x))`.
* `bombieri_unconditional`, `barban_davenport_halberstam_unconditional`: Davenport, Ch. 28 and
  Ch. 29, now without hypothesis.
-/

open Finset Real
open scoped ArithmeticFunction.vonMangoldt

namespace NTKB.Davenport

/-- `ψ(x, χ)` of the sieve chapters is `ψ(x, χ)` of the zero chapters (`n = 0` contributes 0). -/
lemma psiChar_eq_psiL {q : ℕ} (χ : DirichletCharacter ℂ q) (x : ℝ) :
    psiChar χ x = NTKB.psiL χ x := by
  rw [psiChar, NTKB.psiL]
  refine sum_subset (Icc_subset_Icc_left zero_le_one) fun n hn hn' ↦ ?_
  have : n = 0 := by
    simp only [mem_Icc] at hn hn'
    omega
  simp [this]

/-- `|ψ(x, χ)| ≤ x log x` for `x ≥ 1`. -/
lemma norm_psiChar_le {q : ℕ} (χ : DirichletCharacter ℂ q) {x : ℝ} (hx : 1 ≤ x) :
    ‖psiChar χ x‖ ≤ x * Real.log x := by
  rw [psiChar]
  refine (norm_sum_le _ _).trans ?_
  have hb : ∀ n ∈ Icc 1 ⌊x⌋₊, ‖χ n * (Λ n : ℂ)‖ ≤ Real.log x := by
    intro n hn
    have hn := mem_Icc.1 hn
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    have h1 : ‖χ n‖ ≤ 1 := DirichletCharacter.norm_le_one χ _
    have h2 : Λ n ≤ Real.log x :=
      ArithmeticFunction.vonMangoldt_le_log.trans (Real.log_le_log (by exact_mod_cast hn.1)
        ((Nat.cast_le.2 hn.2).trans (Nat.floor_le (by linarith))))
    have h3 : 0 ≤ Λ n := ArithmeticFunction.vonMangoldt_nonneg
    nlinarith
  refine (sum_le_sum hb).trans ?_
  rw [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (Nat.floor_le (by linarith)) (Real.log_nonneg hx)

/-- `(log x)² ≤ 14 x exp(-√log x)` for `x ≥ 1`. -/
lemma log_sq_le_mul_exp {x : ℝ} (hx : 1 ≤ x) :
    Real.log x ^ 2 ≤ 14 * x * Real.exp (-√(Real.log x)) := by
  set L := Real.log x with hL
  have hL0 : 0 ≤ L := Real.log_nonneg hx
  have hxL : x = Real.exp L := (Real.exp_log (by linarith)).symm
  -- `√L ≤ (L + 1)/2` and `L² ≤ 8 exp(L/2)`
  have h1 : √L ≤ (L + 1) / 2 := by
    nlinarith [Real.sq_sqrt hL0, sq_nonneg (√L - 1), Real.sqrt_nonneg L]
  have h2 : L ^ 2 ≤ 8 * Real.exp (L / 2) := by
    have := Real.pow_div_factorial_le_exp (x := L / 2) (by positivity) 2
    norm_num [Nat.factorial] at this
    nlinarith
  have h3 : Real.exp (L / 2) * Real.exp (√L) ≤ Real.exp (1 / 2) * Real.exp L := by
    rw [← Real.exp_add, ← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith)
  have he : Real.exp (1 / 2) ≤ 7 / 4 := by
    have := Real.exp_bound' (x := 1 / 2) (by norm_num) (by norm_num) (n := 3) (by norm_num)
    norm_num [Finset.sum_range_succ, Nat.factorial] at this
    linarith
  have hpos : 0 < Real.exp (√L) := Real.exp_pos _
  rw [hxL, Real.exp_neg, ← hxL]
  rw [le_mul_inv_iff₀ hpos]
  calc L ^ 2 * Real.exp √L ≤ 8 * Real.exp (L / 2) * Real.exp √L := by gcongr
    _ ≤ 8 * (Real.exp (1 / 2) * Real.exp L) := by rw [mul_assoc]; gcongr
    _ ≤ 8 * (7 / 4 * x) := by rw [← hxL]; gcongr
    _ ≤ 14 * x := by linarith

open scoped Classical in
/-- The exceptional part of (8) of §20: if every real zero of `L(s, χ)` (for real `χ`) is at
most `1 - b`, then `|∑_{exceptional ρ} N^ρ/ρ| ≤ 2 N exp(-b log N)` (at most one exceptional zero,
`Davenport.LFunction_exceptional_zero_unique`). -/
lemma norm_sum_exceptional_le {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (hq : q ≠ 1) {N : ℕ} (hN : 1 ≤ N) {b : ℝ}
    (hb : χ ^ 2 = 1 → ∀ β : ℝ, χ.LFunction β = 0 → β ≤ 1 - b) :
    ‖∑ ρ ∈ (NTKB.zerosBelowL hχ hq 1).filter (fun ρ ↦ NTKB.IsExcPoint q ρ.val),
        NTKB.perronKernel N ρ.val‖ ≤ 2 * N * Real.exp (-(b * Real.log N)) := by
  have hχ1 := NTKB.ne_one_of_isPrimitive hχ hq
  have hq2 := NTKB.two_le_of_ne_one hχ1
  have hlq : 0 < Real.log q := Real.log_pos (by linarith)
  set S := (NTKB.zerosBelowL hχ hq 1).filter (fun ρ ↦ NTKB.IsExcPoint q ρ.val)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  -- each exceptional zero is real, a zero of `L`, with `β ∈ (1/2, 1 - b]`
  have hmem : ∀ ρ ∈ S, ρ.val.im = 0 ∧ 1 / 2 < ρ.val.re ∧ χ.LFunction ρ.val = 0 ∧
      NTKB.IsExcPoint q ρ.val := by
    intro ρ hρ
    have hexc := (mem_filter.mp hρ).2
    have hz := (NTKB.dirichletXi_zero_mem hχ hq ρ).1
    exact ⟨(Davenport.exceptional_zero_real hχ1 hz hexc).2, hexc.re_gt_half hχ1, hz, hexc⟩
  have hcard : S.card ≤ 1 := by
    refine Finset.card_le_one.mpr fun ρ₁ h₁ ρ₂ h₂ ↦ ?_
    have hnear : ∀ ρ ∈ S, NTKB.IsNearOne (1 / 16200) q ρ.val := by
      intro ρ hρ
      obtain ⟨him, -, -, hexc⟩ := hmem ρ hρ
      unfold NTKB.IsExcPoint at hexc
      rw [him, NTKB.logQT_of_lt_one (by linarith) (by simp)] at hexc
      exact ⟨by rw [him, abs_zero]; positivity, by linarith⟩
    exact Davenport.LFunction_exceptional_zero_unique hχ hχ1 (by norm_num) (by norm_num) ρ₁ ρ₂
      (hnear ρ₁ h₁) (hnear ρ₂ h₂)
  have hterm : ∀ ρ ∈ S, ‖NTKB.perronKernel N ρ.val‖ ≤ 2 * N * Real.exp (-(b * Real.log N)) := by
    intro ρ hρ
    obtain ⟨him, hre, hz, -⟩ := hmem ρ hρ
    have hρeq : ρ.val = (ρ.val.re : ℂ) := Complex.ext (by simp) (by simp [him])
    have hreal : χ ^ 2 = 1 := (Davenport.exceptional_zero_real hχ1 hz (hmem ρ hρ).2.2.2).1
    have hβ : ρ.val.re ≤ 1 - b := hb hreal _ (by rw [← hρeq]; exact hz)
    rw [NTKB.perronKernel, norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hN0]
    have hnorm : ρ.val.re ≤ ‖ρ.val‖ := Complex.re_le_norm _
    have hpow : (N : ℝ) ^ ρ.val.re ≤ N * Real.exp (-(b * Real.log N)) := by
      calc (N : ℝ) ^ ρ.val.re ≤ (N : ℝ) ^ (1 - b) :=
            Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) hβ
        _ = N * Real.exp (-(b * Real.log N)) := by
            rw [Real.rpow_def_of_pos hN0,
              show Real.log N * (1 - b) = Real.log N + -(b * Real.log N) by ring, Real.exp_add,
              Real.exp_log hN0]
    rw [div_le_iff₀ (by linarith)]
    have hp : 0 ≤ (N : ℝ) * Real.exp (-(b * Real.log N)) := by positivity
    nlinarith
  calc ‖∑ ρ ∈ S, NTKB.perronKernel N ρ.val‖ ≤ ∑ ρ ∈ S, ‖NTKB.perronKernel N ρ.val‖ :=
        norm_sum_le _ _
    _ ≤ S.card • (2 * N * Real.exp (-(b * Real.log N))) := sum_le_card_nsmul _ _ _ hterm
    _ ≤ 1 • (2 * N * Real.exp (-(b * Real.log N))) := by
        gcongr
    _ = _ := one_smul _ _

open scoped Classical in
/-- **Davenport, Ch. 22, p. 132, (C)**: for every `N > 0` (here `B`) there are `c, C > 0` such
that `|ψ(x, χ)| ≤ C x exp(-c √log x)` for `x ≥ 2` and every nonprincipal character `χ` modulo
`q ≤ (log x)^N`. -/
@[kb "davenport1980" "Ch 22, p. 132, (C)"]
theorem siegel_walfisz_char (B : ℝ) (hB : 0 < B) :
    ∃ c > 0, ∃ C > 0, ∀ x : ℝ, 2 ≤ x → ∀ q : ℕ, 0 < q →
      (q : ℝ) ≤ Real.log x ^ B → ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
        ‖psiChar χ x‖ ≤ C * x * Real.exp (-c * √(Real.log x)) := by
  obtain ⟨C₃, hC₃, hS⟩ := siegel_real_zero_le (ε := 1 / (2 * B)) (by positivity)
  obtain ⟨c₀, A₀, hc₀, hA₀, h20⟩ := Davenport.psi0L_sub_exceptional_le (3 * B) (by positivity)
  set c := min (min (c₀ / 2) (C₃ / 2)) 1 with hc
  have hc0 : 0 < c := lt_min (lt_min (by positivity) (by positivity)) one_pos
  have hc1 : c ≤ 1 := min_le_right _ _
  have hcc₀ : c ≤ c₀ / 2 := (min_le_left _ _).trans (min_le_left _ _)
  have hcC₃ : c ≤ C₃ / 2 := (min_le_left _ _).trans (min_le_right _ _)
  set C := A₀ + 2 + 14 * (1 + 2 * B) with hC
  refine ⟨c, hc0, C, by positivity, fun x hx q hq0 hqx χ hχ ↦ ?_⟩
  have : NeZero q := ⟨hq0.ne'⟩
  set L := Real.log x with hL
  have hx0 : 0 < x := by linarith
  have hL0 : 0 < L := Real.log_pos (by linarith)
  have hsL : 0 ≤ √L := Real.sqrt_nonneg _
  have hEpos : 0 < Real.exp (-c * √L) := Real.exp_pos _
  rcases lt_or_ge x 3 with hx3 | hx3
  · -- small `x`: `|ψ(x, χ)| ≤ x log x ≤ 2x ≤ C x e^{-2}`
    have h1 := norm_psiChar_le χ (by linarith : 1 ≤ x)
    have hL2 : L ≤ 2 := by
      have := Real.log_le_sub_one_of_pos hx0; rw [hL]; linarith
    have hsL2 : √L ≤ 2 := by
      rw [Real.sqrt_le_left (by norm_num)]; linarith
    have hc2 : c * √L ≤ 1 * 2 := mul_le_mul hc1 hsL2 hsL zero_le_one
    have he2 : Real.exp (-2) ≤ Real.exp (-c * √L) := Real.exp_le_exp.mpr (by linarith)
    have he8 : 1 / 8 ≤ Real.exp (-2) := by
      rw [Real.exp_neg, one_div]
      refine inv_anti₀ (by positivity) ?_
      have := Real.exp_one_lt_d9
      rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
      have he0 := Real.exp_pos 1
      have : Real.exp 1 * Real.exp 1 ≤ 2.7182818286 * 2.7182818286 :=
        mul_le_mul this.le this.le he0.le (by norm_num)
      linarith
    have hC16 : 16 ≤ C := by rw [hC]; linarith
    calc ‖psiChar χ x‖ ≤ x * L := h1
      _ ≤ x * 2 := by gcongr
      _ = 16 * x * (1 / 8) := by ring
      _ ≤ C * x * Real.exp (-c * √L) := by
          gcongr
          exact he8.trans he2
  -- main case `x ≥ 3`
  set N := ⌊x⌋₊ with hNdef
  have hN3 : 3 ≤ N := Nat.le_floor (by exact_mod_cast hx3)
  have hNx : (N : ℝ) ≤ x := Nat.floor_le hx0.le
  have hxN : x < N + 1 := Nat.lt_floor_add_one x
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  set LN := Real.log N with hLNdef
  have hLN : LN ≤ L := Real.log_le_log hN0 hNx
  have hLN2 : L ≤ 2 * LN := by
    have h3 : (3 : ℝ) ≤ N := by exact_mod_cast hN3
    have : x ≤ (N : ℝ) ^ 2 := by
      have : (N : ℝ) + 1 ≤ N * N := by nlinarith only [h3]
      rw [sq]; linarith
    calc L ≤ Real.log ((N : ℝ) ^ 2) := Real.log_le_log hx0 this
      _ = 2 * LN := by rw [Real.log_pow]; push_cast; ring
  have hsLN : √L ≤ 2 * √LN := by
    calc √L ≤ √(4 * LN) := Real.sqrt_le_sqrt (by linarith)
      _ = 2 * √LN := by
          rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
            Real.sqrt_sq (by norm_num)]
  have hL1 : 1 < L := by
    rw [hL]
    exact (by norm_num : (1 : ℝ) < 1.0986122885).trans
      (Real.log_three_gt_d9.trans_le (Real.log_le_log (by norm_num) hx3))
  -- the primitive character `χ*` modulo `d ∣ q`
  have : NeZero χ.conductor := ⟨DirichletCharacter.conductor_ne_zero χ⟩
  set d := χ.conductor with hd
  have hχ'1 : χ.primitiveCharacter ≠ 1 := NTKB.primitiveCharacter_ne_one hχ
  have hd1 : d ≠ 1 := by
    intro h
    exact hχ'1 (DirichletCharacter.level_one' _ h)
  have hd0 : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  have hdq : (d : ℝ) ≤ q := by
    exact_mod_cast Nat.le_of_dvd hq0 χ.conductor_dvd_level
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq0
  -- `log q ≤ B log L ≤ 2B √L`
  have hlogq : Real.log q ≤ B * Real.log L := by
    calc Real.log q ≤ Real.log (L ^ B) := Real.log_le_log (by linarith) hqx
      _ = B * Real.log L := Real.log_rpow hL0 B
  have hlogL : Real.log L ≤ 2 * √L := by
    have := Real.log_le_rpow_div hL0.le (by norm_num : (0 : ℝ) < 1 / 2)
    rw [← Real.sqrt_eq_rpow] at this; linarith
  have hlogd : Real.log d ≤ 3 * B * √LN := by
    have h1 : Real.log d ≤ Real.log q := Real.log_le_log hd0 hdq
    have h2 : √L ≤ 3 / 2 * √LN := by
      have : √L ≤ √(2 * LN) := Real.sqrt_le_sqrt hLN2
      rw [Real.sqrt_mul (by norm_num)] at this
      have hs2 : √(2 : ℝ) ≤ 3 / 2 := by
        rw [Real.sqrt_le_left (by norm_num)]; norm_num
      calc √L ≤ √2 * √LN := this
        _ ≤ 3 / 2 * √LN := mul_le_mul_of_nonneg_right hs2 (Real.sqrt_nonneg _)
    calc Real.log d ≤ Real.log q := h1
      _ ≤ B * Real.log L := hlogq
      _ ≤ B * (2 * √L) := mul_le_mul_of_nonneg_left hlogL hB.le
      _ ≤ B * (2 * (3 / 2 * √LN)) := by gcongr
      _ = 3 * B * √LN := by ring
  -- (8) of §20 for `χ*`
  set S := ∑ ρ ∈ (NTKB.zerosBelowL (DirichletCharacter.primitiveCharacter_isPrimitive χ) hd1
      1).filter (fun ρ ↦ NTKB.IsExcPoint d ρ.val), NTKB.perronKernel N ρ.val with hSdef
  have h8 := h20 (DirichletCharacter.primitiveCharacter_isPrimitive χ) hd1 N hN3 hlogd
  -- the exceptional zero: `β ≤ 1 - C₃ d^{-1/(2B)}`
  set b := C₃ * (d : ℝ) ^ (-(1 / (2 * B))) with hb
  have hexc := norm_sum_exceptional_le (DirichletCharacter.primitiveCharacter_isPrimitive χ) hd1
    (N := N) (by omega) (b := b) (fun hreal β hβ ↦
      hS (MulChar.isQuadratic_iff_sq_eq_one.mpr hreal) hχ'1 β hβ)
  have hbLN : C₃ / 2 * √L ≤ b * LN := by
    have hdq' : (q : ℝ) ^ (-(1 / (2 * B))) ≤ (d : ℝ) ^ (-(1 / (2 * B))) :=
      rpow_neg_le_of_le hd0 hdq (by positivity)
    have hqL : (L ^ B) ^ (-(1 / (2 * B))) ≤ (q : ℝ) ^ (-(1 / (2 * B))) :=
      rpow_neg_le_of_le (by linarith) hqx (by positivity)
    have hLpow : (L ^ B) ^ (-(1 / (2 * B))) = (√L)⁻¹ := by
      rw [← Real.rpow_mul hL0.le, show B * -(1 / (2 * B)) = -(1 / 2) by field_simp,
        Real.rpow_neg hL0.le, Real.sqrt_eq_rpow]
    have hsq : √L * √L = L := Real.mul_self_sqrt hL0.le
    have hsLpos : 0 < √L := Real.sqrt_pos.mpr hL0
    have hkey : C₃ * (√L)⁻¹ ≤ b := by
      rw [hb]; gcongr; rw [← hLpow]; exact hqL.trans hdq'
    have h' : (√L)⁻¹ * L = √L := by
      rw [inv_mul_eq_iff_eq_mul₀ hsLpos.ne']; exact hsq.symm
    have : C₃ / 2 * √L = C₃ * (√L)⁻¹ * (L / 2) := by
      rw [show C₃ * (√L)⁻¹ * (L / 2) = C₃ / 2 * ((√L)⁻¹ * L) by ring, h']
    rw [this]
    have hb0 : 0 ≤ b := by positivity
    exact mul_le_mul hkey (by linarith) (by positivity) hb0
  have hexc' : ‖S‖ ≤
      2 * x * Real.exp (-c * √L) := by
    refine hexc.trans ?_
    have hcb : c * √L ≤ b * LN :=
      (mul_le_mul_of_nonneg_right hcC₃ hsL).trans hbLN
    have : Real.exp (-(b * LN)) ≤ Real.exp (-c * √L) :=
      Real.exp_le_exp.mpr (by linarith)
    gcongr
  have h8' : ‖NTKB.psi0L χ.primitiveCharacter N‖ ≤ A₀ * x * Real.exp (-c * √L) +
      2 * x * Real.exp (-c * √L) := by
    have hm : A₀ * N * Real.exp (-(c₀ * √LN)) ≤ A₀ * x * Real.exp (-c * √L) := by
      have hcc : c * √L ≤ c₀ * √LN := by
        calc c * √L ≤ (c₀ / 2) * (2 * √LN) :=
              mul_le_mul hcc₀ hsLN hsL (by positivity)
          _ = c₀ * √LN := by ring
      have : Real.exp (-(c₀ * √LN)) ≤ Real.exp (-c * √L) :=
        Real.exp_le_exp.mpr (by linarith)
      gcongr
    have key : ‖NTKB.psi0L χ.primitiveCharacter N‖ ≤ ‖NTKB.psi0L χ.primitiveCharacter N + S‖ +
        ‖S‖ := by
      calc ‖NTKB.psi0L χ.primitiveCharacter N‖ = ‖(NTKB.psi0L χ.primitiveCharacter N + S) - S‖ := by
            rw [add_sub_cancel_right]
        _ ≤ _ := norm_sub_le _ _
    linarith
  -- from `ψ₀(N, χ*)` to `ψ(x, χ)`
  have hpsiN : psiChar χ.primitiveCharacter x = NTKB.psi0L χ.primitiveCharacter N +
      χ.primitiveCharacter N * Λ N / 2 := by
    rw [psiChar_eq_psiL, ← NTKB.psiL_natCast_eq]
    simp only [NTKB.psiL, Nat.floor_natCast, hNdef]
  have hlast : ‖χ.primitiveCharacter N * (Λ N : ℂ) / 2‖ ≤ L := by
    rw [norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    have h1 : ‖χ.primitiveCharacter N‖ ≤ 1 := DirichletCharacter.norm_le_one _ _
    have h2 : Λ N ≤ L := ArithmeticFunction.vonMangoldt_le_log.trans hLN
    have h3 : 0 ≤ Λ N := ArithmeticFunction.vonMangoldt_nonneg
    have e2 : ‖(2 : ℂ)‖ = 2 := by norm_num
    rw [e2]
    have := mul_le_of_le_one_left h3 h1
    linarith
  have hind := norm_psiChar'_sub_le χ (x := x) (by linarith)
  simp only [psiChar', if_neg hχ, if_neg hχ'1, sub_zero] at hind
  have hlogq2 : 2 * Real.log q * L ≤ 2 * B * L ^ 2 := by
    have : Real.log L ≤ L := (Real.log_le_sub_one_of_pos hL0).trans (by linarith)
    have hlq0 : 0 ≤ Real.log q := Real.log_nonneg hq1
    have h1 : Real.log q ≤ B * L := hlogq.trans (mul_le_mul_of_nonneg_left this hB.le)
    have h2 := mul_le_mul_of_nonneg_right h1 hL0.le
    rw [sq]; linarith
  have hLsq : L ≤ L ^ 2 := by rw [sq]; exact le_mul_of_one_le_left hL0.le hL1.le
  have h14 := log_sq_le_mul_exp (x := x) (by linarith)
  have he1 : Real.exp (-√L) ≤ Real.exp (-c * √L) :=
    Real.exp_le_exp.mpr (by linarith [mul_le_of_le_one_left hsL hc1])
  have hfinal : ‖psiChar χ x‖ ≤ (A₀ + 2) * x * Real.exp (-c * √L) + (1 + 2 * B) * L ^ 2 := by
    have := norm_le_norm_add_norm_sub' (psiChar χ x) (psiChar χ.primitiveCharacter x)
    have h2 : ‖psiChar χ.primitiveCharacter x‖ ≤ ‖NTKB.psi0L χ.primitiveCharacter N‖ +
        ‖χ.primitiveCharacter N * (Λ N : ℂ) / 2‖ := by
      rw [hpsiN]; exact norm_add_le _ _
    have h3 : ‖psiChar χ x - psiChar χ.primitiveCharacter x‖ ≤ 2 * Real.log q * L := hind
    have h4 : 0 ≤ x * Real.exp (-c * √L) := by positivity
    linarith
  calc ‖psiChar χ x‖ ≤ (A₀ + 2) * x * Real.exp (-c * √L) + (1 + 2 * B) * L ^ 2 := hfinal
    _ ≤ (A₀ + 2) * x * Real.exp (-c * √L) + (1 + 2 * B) * (14 * x * Real.exp (-c * √L)) := by
        gcongr
        exact h14.trans (by gcongr)
    _ = C * x * Real.exp (-c * √L) := by rw [hC]; ring

/-- **The named input `SiegelWalfiszHypothesis` is a theorem**: the prime number theorem with
the classical error term (Davenport §18, `Davenport.psi_sub_self_le`) and the Siegel–Walfisz
estimate (C) of §22 (`siegel_walfisz_char`). -/
theorem siegelWalfiszHypothesis : SiegelWalfiszHypothesis where
  pnt := by
    obtain ⟨c, C, hc, hC, h⟩ := Davenport.psi_sub_self_le
    exact ⟨c, hc, C, hC, fun x hx ↦ by simpa [neg_mul] using h x hx⟩
  sw := siegel_walfisz_char

/-- **The Siegel–Walfisz theorem, Davenport, Ch. 22, p. 133, (D)**: for every `N > 0` (here `B`)
there are `c = C₄(N) > 0` and `C` such that `|ψ(x; q, a) - x/φ(q)| ≤ C x exp(-c √log x)` for
`x ≥ 2`, `q ≤ (log x)^N` and `(a, q) = 1`. -/
@[kb "davenport1980" "Ch 22, p. 133, (D)"]
theorem siegel_walfisz (B : ℝ) (hB : 0 < B) :
    ∃ c > 0, ∃ C > 0, ∀ x : ℝ, 2 ≤ x → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.log x ^ B →
      ∀ a : ℤ, IsCoprime a q →
        |psiAP x q a - x / q.totient| ≤ C * x * Real.exp (-c * √(Real.log x)) := by
  obtain ⟨c, hc, C, hC, h⟩ := siegelWalfiszHypothesis.primitive_bound hB
  set c' := min c 1 with hc'
  refine ⟨c', lt_min hc one_pos, C + 28 * B, by positivity, fun x hx q hq0 hqx a ha ↦ ?_⟩
  have : NeZero q := ⟨hq0.ne'⟩
  set L := Real.log x with hL
  have hx0 : 0 < x := by linarith
  have hL0 : 0 < L := Real.log_pos (by linarith)
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq0
  have hsL : 0 ≤ √L := Real.sqrt_nonneg _
  -- each `ψ'(x, χ)` is small
  have hM : ∀ χ : DirichletCharacter ℂ q,
      ‖psiChar' χ x‖ ≤ (C + 28 * B) * x * Real.exp (-c' * √L) := by
    intro χ
    have : NeZero χ.conductor := ⟨DirichletCharacter.conductor_ne_zero χ⟩
    have hd0 : (0 : ℝ) < χ.conductor := by
      exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne χ.conductor)
    have hdq : (χ.conductor : ℝ) ≤ q := by
      exact_mod_cast Nat.le_of_dvd hq0 χ.conductor_dvd_level
    have hp := h x hx χ.conductor (by exact_mod_cast hd0) (hdq.trans hqx) χ.primitiveCharacter
      (DirichletCharacter.primitiveCharacter_isPrimitive χ)
    have hind := norm_psiChar'_sub_le χ (x := x) (by linarith)
    have hlogq : Real.log q ≤ B * L := by
      calc Real.log q ≤ Real.log (L ^ B) := Real.log_le_log (by linarith) hqx
        _ = B * Real.log L := Real.log_rpow hL0 B
        _ ≤ B * L := by
          gcongr; exact (Real.log_le_sub_one_of_pos hL0).trans (by linarith)
    have hlq0 : 0 ≤ Real.log q := Real.log_nonneg hq1
    have h14 := log_sq_le_mul_exp (x := x) (by linarith)
    have he1 : Real.exp (-√L) ≤ Real.exp (-c' * √L) := by
      refine Real.exp_le_exp.mpr ?_
      have : c' ≤ 1 := min_le_right _ _
      nlinarith
    have he2 : Real.exp (-c * √L) ≤ Real.exp (-c' * √L) := by
      refine Real.exp_le_exp.mpr ?_
      have : c' ≤ c := min_le_left _ _
      nlinarith
    have := norm_le_norm_add_norm_sub' (psiChar' χ x) (psiChar' χ.primitiveCharacter x)
    have hx14 : 2 * Real.log q * L ≤ 28 * B * x * Real.exp (-c' * √L) := by
      have : 2 * Real.log q * L ≤ 2 * B * L ^ 2 := by nlinarith
      have h' : L ^ 2 ≤ 14 * x * Real.exp (-c' * √L) := h14.trans (by gcongr)
      nlinarith
    have hCx : C * x * Real.exp (-c * √L) ≤ C * x * Real.exp (-c' * √L) := by gcongr
    nlinarith
  -- average over the characters
  have heq := psiAP_sub_eq x ha
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.2 hq0
  have hnorm : (q.totient : ℝ) * |psiAP x q a - x / q.totient| ≤
      q.totient * ((C + 28 * B) * x * Real.exp (-c' * √L)) := by
    have h1 : ‖(q.totient : ℂ) * ((psiAP x q a - x / q.totient : ℝ) : ℂ)‖ =
        (q.totient : ℝ) * |psiAP x q a - x / q.totient| := by
      rw [norm_mul, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs]
    rw [← h1, heq]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ χ : DirichletCharacter ℂ q, ‖χ⁻¹ a * psiChar' χ x‖
        ≤ ∑ _χ : DirichletCharacter ℂ q, (C + 28 * B) * x * Real.exp (-c' * √L) := by
          refine sum_le_sum fun χ _ ↦ ?_
          rw [norm_mul]
          have h1 : ‖χ⁻¹ (a : ZMod q)‖ ≤ 1 := DirichletCharacter.norm_le_one _ _
          have := hM χ
          calc ‖χ⁻¹ (a : ZMod q)‖ * ‖psiChar' χ x‖ ≤ 1 * ‖psiChar' χ x‖ := by gcongr
            _ ≤ _ := by rw [one_mul]; exact this
      _ = q.totient * ((C + 28 * B) * x * Real.exp (-c' * √L)) := by
          rw [sum_const, nsmul_eq_mul, card_univ, card_dirichletCharacter]
  exact le_of_mul_le_mul_left hnorm hφ

/-- **Bombieri's theorem (Davenport, Ch. 28, p. 161)**, unconditionally: the named input
`SiegelWalfiszHypothesis` of `bombieri` is `siegelWalfiszHypothesis`. -/
@[kb "davenport1980" "Ch 28, p. 161"]
theorem bombieri_unconditional {A : ℝ} (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 3 ≤ x → ∀ Q : ℝ, √x * Real.log x ^ (-A) ≤ Q → Q ≤ √x →
      ∀ (y : ℕ → ℝ) (a : ℕ → ℤ), (∀ q, 0 ≤ y q ∧ y q ≤ x) → (∀ q, IsCoprime (a q) q) →
        ∑ q ∈ Icc 1 ⌊Q⌋₊, |psiAP (y q) q (a q) - y q / q.totient| ≤
          C * √x * Q * Real.log x ^ 5 :=
  bombieri siegelWalfiszHypothesis hA

/-- **The Barban–Davenport–Halberstam theorem (Davenport, Ch. 29, p. 169, (1))**,
unconditionally. -/
@[kb "davenport1980" "Ch 29, p. 169, (1)"]
theorem barban_davenport_halberstam_unconditional {A : ℝ} (hA : 0 < A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 3 ≤ x → ∀ Q : ℝ, x * Real.log x ^ (-A) < Q → Q ≤ x →
      ∑ q ∈ Icc 1 ⌊Q⌋₊, ∑ a ∈ (Icc 1 q).filter (fun a ↦ Nat.Coprime a q),
        (psiAP x q a - x / q.totient) ^ 2 ≤ C * x * Q * Real.log x :=
  barban_davenport_halberstam siegelWalfiszHypothesis hA

end NTKB.Davenport
