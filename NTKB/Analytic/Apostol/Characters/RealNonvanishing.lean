/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Apostol.Characters.RealChar
import NTKB.Analytic.Apostol.Averages.DivisorSums
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# `L(1, χ) ≠ 0` for real nonprincipal `χ` (Apostol, Chapter 6, §6.10, Theorem 6.20)

For a real-valued nonprincipal character `χ` mod `k` let `A(n) = ∑_{d ∣ n} χ(d)` and
`B(x) = ∑_{n ≤ x} A(n)/√n`. Then
(a) `B(x) → ∞` (Theorem 6.19: `A(n) ≥ 0`, `A(m²) ≥ 1`, so `B(x) ≥ ∑_{m ≤ √x} 1/m`);
(b) `B(x) = 2√x L(1, χ) + O(1)` (hyperbola identity 3.17 with `a = b = √x`,
    `f(n) = χ(n)/√n`, `g(n) = 1/√n`, Theorem 3.2(b) for `s = 1/2` and Theorem 6.18);
hence `L(1, χ) ≠ 0`. Here `L(1, χ)` is `NTKB.Apostol.LOne χ`, the sum of `∑ χ(n)/n`.
-/

open Finset ArithmeticFunction Filter Topology

namespace NTKB.Apostol

variable {k : ℕ} [NeZero k]

/-- `f(n) = χ(n)/√n`. -/
noncomputable def charDivSqrt (χ : DirichletCharacter ℂ k) : ArithmeticFunction ℂ :=
  ⟨fun n ↦ χ n * ((1 / √(n : ℝ) : ℝ) : ℂ), by simp⟩

/-- `g(n) = 1/√n`. -/
noncomputable def invSqrtAF : ArithmeticFunction ℂ :=
  ⟨fun n ↦ ((1 / √(n : ℝ) : ℝ) : ℂ), by simp⟩

theorem charDivSqrt_mul_invSqrtAF_apply (χ : DirichletCharacter ℂ k) (n : ℕ) :
    (charDivSqrt χ * invSqrtAF) n = (∑ d ∈ n.divisors, χ d) * ((1 / √(n : ℝ) : ℝ) : ℂ) := by
  rw [mul_apply_eq_sum_divisors_aux, sum_mul]
  refine sum_congr rfl fun d hd ↦ ?_
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  obtain ⟨e, he⟩ := Nat.dvd_of_mem_divisors hd
  have hn0 : n ≠ 0 := (Nat.mem_divisors.1 hd).2
  simp only [charDivSqrt, invSqrtAF, coe_mk]
  have : ((n / d : ℕ) : ℝ) = n / d := by
    rw [Nat.cast_div (Nat.dvd_of_mem_divisors hd)]
    exact_mod_cast Nat.ne_of_gt (Nat.pos_of_mem_divisors hd)
  rw [this, mul_assoc, ← Complex.ofReal_mul]
  congr 2
  have hdpos : (0 : ℝ) < √(d : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast Nat.pos_of_mem_divisors hd)
  have hnpos : (0 : ℝ) < √(n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast Nat.pos_of_ne_zero hn0)
  rw [Real.sqrt_div' _ hd0]
  field_simp
where
  mul_apply_eq_sum_divisors_aux {f g : ArithmeticFunction ℂ} {n : ℕ} :
      (f * g) n = ∑ d ∈ n.divisors, f d * g (n / d) := by
    rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal (fun x y ↦ f x * g y)]

/-- `B(x) = ∑_{n ≤ x} A(n)/√n` for a real character (Apostol, Theorem 6.20). -/
noncomputable def realCharB (χ : DirichletCharacter ℂ k) (x : ℝ) : ℝ :=
  ∑ n ∈ Ioc 0 ⌊x⌋₊, (∑ d ∈ n.divisors, (χ d).re) * (1 / √(n : ℝ))

/-- **Apostol, Theorem 6.20 (a).** `B(x) → ∞` for a real character `χ`. -/
@[kb "apostol1976" "Thm 6.20(a), p. 142"]
theorem tendsto_realCharB {χ : DirichletCharacter ℂ k} (hχ : χ.IsQuadratic) :
    Tendsto (realCharB χ) atTop atTop := by
  -- `B(x) ≥ ∑_{m ≤ ⌊√x⌋} 1/m ≥ log(⌊√x⌋ + 1)`
  have hlow : ∀ x : ℝ, 1 ≤ x → Real.log (⌊√x⌋₊ + 1) ≤ realCharB χ x := by
    intro x hx
    set M := ⌊√x⌋₊
    have hM : M ^ 2 ≤ ⌊x⌋₊ := by
      apply Nat.le_floor
      push_cast
      have h1 := Nat.floor_le (Real.sqrt_nonneg x)
      have h2 : (√x) ^ 2 = x := Real.sq_sqrt (by linarith)
      nlinarith [Nat.cast_nonneg (α := ℝ) M]
    have himg : (Ioc 0 M).image (fun m : ℕ ↦ m ^ 2) ⊆ Ioc 0 ⌊x⌋₊ := by
      intro n hn
      simp only [mem_image, mem_Ioc] at hn ⊢
      obtain ⟨m, ⟨hm0, hmM⟩, rfl⟩ := hn
      exact ⟨by positivity, le_trans (Nat.pow_le_pow_left hmM 2) hM⟩
    have hnn : ∀ n ∈ Ioc 0 ⌊x⌋₊, 0 ≤ (∑ d ∈ n.divisors, (χ d).re) * (1 / √(n : ℝ)) :=
      fun n _ ↦ mul_nonneg (sum_divisors_char_nonneg hχ n).1 (by positivity)
    calc Real.log (M + 1) ≤ harmonic M := by exact_mod_cast log_add_one_le_harmonic M
      _ = ∑ m ∈ Ioc 0 M, (1 / m : ℝ) := (sum_Ioc_inv_eq_harmonic M).symm
      _ ≤ ∑ m ∈ Ioc 0 M, (∑ d ∈ (m ^ 2).divisors, (χ d).re) * (1 / √((m ^ 2 : ℕ) : ℝ)) := by
          refine sum_le_sum fun m hm ↦ ?_
          have hm0 : m ≠ 0 := (mem_Ioc.1 hm).1.ne'
          have h1 := (sum_divisors_char_nonneg hχ (m ^ 2)).2 (pow_ne_zero 2 hm0) ⟨m, sq m⟩
          have h2 : √((m ^ 2 : ℕ) : ℝ) = m := by push_cast; exact Real.sqrt_sq (Nat.cast_nonneg _)
          rw [h2]
          calc (1 / m : ℝ) = 1 * (1 / m) := (one_mul _).symm
            _ ≤ _ := mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = ∑ n ∈ ((Ioc 0 M).image (fun m : ℕ ↦ m ^ 2) : Finset ℕ),
            (∑ d ∈ n.divisors, (χ d).re) * (1 / √(n : ℝ)) := by
          rw [sum_image]
          intro a _ b _ hab
          exact Nat.pow_left_injective two_ne_zero hab
      _ ≤ realCharB χ x := sum_le_sum_of_subset_of_nonneg himg fun n hn _ ↦ hnn n hn
  rw [tendsto_atTop]
  intro b
  have hlim : Tendsto (fun x : ℝ ↦ Real.log (⌊√x⌋₊ + 1)) atTop atTop := by
    refine Real.tendsto_log_atTop.comp ?_
    refine tendsto_atTop_add_const_right _ 1 ?_
    exact tendsto_natCast_atTop_atTop.comp
      (tendsto_nat_floor_atTop.comp Real.tendsto_sqrt_atTop)
  filter_upwards [hlim.eventually_ge_atTop b, eventually_ge_atTop 1] with x hx hx1
  exact hx.trans (hlow x hx1)

theorem realCharB_eq {χ : DirichletCharacter ℂ k} (hχ : χ.IsQuadratic) (x : ℝ) :
    ((realCharB χ x : ℝ) : ℂ) = ∑ n ∈ Ioc 0 ⌊x⌋₊, (charDivSqrt χ * invSqrtAF) n := by
  rw [realCharB, Complex.ofReal_sum]
  refine sum_congr rfl fun n _ ↦ ?_
  rw [Complex.ofReal_mul, charDivSqrt_mul_invSqrtAF_apply, sum_divisors_char_eq_re hχ]

theorem norm_charDivSqrt_le (χ : DirichletCharacter ℂ k) (n : ℕ) :
    ‖charDivSqrt χ n‖ ≤ 1 / √(n : ℝ) := by
  simp only [charDivSqrt, coe_mk, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_nonneg (by positivity)]
  calc ‖χ n‖ * (1 / √(n : ℝ)) ≤ 1 * (1 / √(n : ℝ)) :=
        mul_le_mul_of_nonneg_right (DirichletCharacter.norm_le_one χ _) (by positivity)
    _ = 1 / √(n : ℝ) := one_mul _

/-- `(1/√n) · (c/√(x/n)) = c/√x`. -/
theorem one_div_sqrt_mul_div_sqrt_div {x : ℝ} (hx : 0 < x) {n : ℕ} (hn : 0 < n) (c : ℝ) :
    1 / √(n : ℝ) * (c / √(x / n)) = c / √x := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 : 0 < √(n : ℝ) := Real.sqrt_pos.2 hn'
  have h2 : 0 < √x := Real.sqrt_pos.2 hx
  rw [Real.sqrt_div' _ hn'.le]
  field_simp

/-- `∑_{n ≤ s} c/s ≤ c` for `s > 0`, `c ≥ 0`. -/
theorem sum_Ioc_floor_const_div_le {s c : ℝ} (hs : 0 < s) (hc : 0 ≤ c) :
    ∑ _n ∈ Ioc 0 ⌊s⌋₊, c / s ≤ c := by
  rw [sum_const, Nat.card_Ioc, Nat.sub_zero, nsmul_eq_mul]
  calc (⌊s⌋₊ : ℝ) * (c / s) ≤ s * (c / s) :=
        mul_le_mul_of_nonneg_right (Nat.floor_le hs.le) (div_nonneg hc hs.le)
    _ = c := by field_simp

/-- **Apostol, Theorem 6.20 (b).** For a real nonprincipal `χ`, `B(x) = 2√x L(1, χ) + O(1)`. -/
@[kb "apostol1976" "Thm 6.20(b), p. 142"]
theorem exists_norm_realCharB_sub_le {χ : DirichletCharacter ℂ k} (hχ1 : χ ≠ 1)
    (hχ : χ.IsQuadratic) :
    ∃ C, ∀ x : ℝ, 1 ≤ x → ‖((realCharB χ x : ℝ) : ℂ) - 2 * √x * LOne χ‖ ≤ C := by
  obtain ⟨A', hA'⟩ := exists_abs_sum_inv_sqrt_sub_le
  set LH := LHalf χ
  refine ⟨4 * k + |A'| * (‖LH‖ + 2 * k) + 4 + 2 * k + 4 * k, fun x hx ↦ ?_⟩
  have hx0 : 0 < x := by linarith
  set s := √x with hsdef
  have hs1 : 1 ≤ s := Real.one_le_sqrt.2 hx
  have hs0 : 0 < s := by linarith
  have hss : s * s = x := Real.mul_self_sqrt hx0.le
  have hhyp := sum_mul_eq_hyperbola (charDivSqrt χ) invSqrtAF hs0 hs0 hss
  rw [← realCharB_eq hχ] at hhyp
  set G : ℝ → ℝ := fun y ↦ ∑ m ∈ Ioc 0 ⌊y⌋₊, 1 / √(m : ℝ) with hG
  set F : ℝ → ℂ := fun y ↦ ∑ m ∈ Ioc 0 ⌊y⌋₊, charDivSqrt χ m with hF
  have hGsum : ∀ y, ∑ m ∈ Ioc 0 ⌊y⌋₊, invSqrtAF m = (G y : ℂ) := fun y ↦ by
    simp [invSqrtAF, G, Complex.ofReal_sum]
  simp only [hGsum] at hhyp
  set P := ∑ n ∈ Ioc 0 ⌊s⌋₊, χ n * ((1 / n : ℝ) : ℂ) with hP
  -- the decomposition
  have hterm1 : ∀ n ∈ Ioc 0 ⌊s⌋₊, charDivSqrt χ n * ((2 * √(x / n) : ℝ) : ℂ) =
      2 * s * (χ n * ((1 / n : ℝ) : ℂ)) := by
    intro n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast (mem_Ioc.1 hn).1
    have h1 : 0 < √(n : ℝ) := Real.sqrt_pos.2 hn'
    have h2 : √(n : ℝ) * √(n : ℝ) = n := Real.mul_self_sqrt hn'.le
    simp only [charDivSqrt, coe_mk]
    rw [Real.sqrt_div' _ hn'.le, ← hsdef]
    push_cast
    field_simp
    have h2' : ((√(n : ℝ) : ℝ) : ℂ) ^ 2 = (n : ℂ) := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt hn'.le, Complex.ofReal_natCast]
    rw [h2']
  have e1 : ∑ n ∈ Ioc 0 ⌊s⌋₊, charDivSqrt χ n * (G (x / n) : ℂ) =
      2 * s * P + A' * F s + ∑ n ∈ Ioc 0 ⌊s⌋₊, charDivSqrt χ n *
        ((G (x / n) - 2 * √(x / n) - A' : ℝ) : ℂ) := by
    rw [hP, mul_sum, ← sum_congr rfl hterm1, hF, mul_sum, ← sum_add_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun n _ ↦ ?_
    push_cast; ring
  have e2 : ∑ n ∈ Ioc 0 ⌊s⌋₊, invSqrtAF n * F (x / n) =
      LH * (G s : ℂ) + ∑ n ∈ Ioc 0 ⌊s⌋₊, invSqrtAF n * (F (x / n) - LH) := by
    rw [← hGsum s, mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun n _ ↦ ?_
    ring
  have hdecomp : ((realCharB χ x : ℝ) : ℂ) - 2 * s * LOne χ =
      2 * s * (P - LOne χ) + A' * F s +
        ∑ n ∈ Ioc 0 ⌊s⌋₊, charDivSqrt χ n * ((G (x / n) - 2 * √(x / n) - A' : ℝ) : ℂ) +
        ∑ n ∈ Ioc 0 ⌊s⌋₊, invSqrtAF n * (F (x / n) - LH) - (F s - LH) * (G s : ℂ) := by
    rw [hhyp, e1, e2]; ring
  rw [hdecomp]
  -- the five estimates
  have hFs : ‖F s - LH‖ ≤ 2 * k * (1 / √s) := norm_sum_char_div_sqrt_sub_LHalf_le hχ1 hs1
  have hsqs : 1 ≤ √s := Real.one_le_sqrt.2 hs1
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have hFs' : ‖F s - LH‖ ≤ 2 * k := by
    refine hFs.trans ?_
    calc 2 * k * (1 / √s) ≤ 2 * k * 1 := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [div_le_one (by linarith)]; exact hsqs
      _ = 2 * k := mul_one _
  have b1 : ‖2 * s * (P - LOne χ)‖ ≤ 4 * k := by
    have := norm_sum_char_div_sub_LOne_le hχ1 hs1
    rw [norm_mul, show ‖(2 : ℂ) * s‖ = 2 * s by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs0]; norm_num]
    calc 2 * s * ‖P - LOne χ‖ ≤ 2 * s * (2 * k * (1 / s)) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = 4 * k := by field_simp; ring
  have b2 : ‖(A' : ℂ) * F s‖ ≤ |A'| * (‖LH‖ + 2 * k) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    calc ‖F s‖ = ‖(F s - LH) + LH‖ := by ring_nf
      _ ≤ ‖F s - LH‖ + ‖LH‖ := norm_add_le _ _
      _ ≤ ‖LH‖ + 2 * k := by linarith
  have b3 : ‖∑ n ∈ Ioc 0 ⌊s⌋₊, charDivSqrt χ n * ((G (x / n) - 2 * √(x / n) - A' : ℝ) : ℂ)‖
      ≤ 4 := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ n ∈ Ioc 0 ⌊s⌋₊, ‖charDivSqrt χ n * ((G (x / n) - 2 * √(x / n) - A' : ℝ) : ℂ)‖
        ≤ ∑ n ∈ Ioc 0 ⌊s⌋₊, 4 / s := by
          refine sum_le_sum fun n hn ↦ ?_
          have hn0 := (mem_Ioc.1 hn).1
          have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
          have hns : (n : ℝ) ≤ s := by
            have : (n : ℝ) ≤ ⌊s⌋₊ := by exact_mod_cast (mem_Ioc.1 hn).2
            linarith [Nat.floor_le hs0.le]
          have hxn : 1 ≤ x / n := by rw [le_div_iff₀ hn']; nlinarith
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          calc ‖charDivSqrt χ n‖ * |G (x / n) - 2 * √(x / n) - A'| ≤
                1 / √(n : ℝ) * (4 / √(x / n)) :=
                mul_le_mul (norm_charDivSqrt_le χ n) (hA' _ hxn) (abs_nonneg _) (by positivity)
            _ = 4 / s := one_div_sqrt_mul_div_sqrt_div hx0 hn0 4
      _ ≤ 4 := sum_Ioc_floor_const_div_le hs0 (by norm_num)
  have b4 : ‖∑ n ∈ Ioc 0 ⌊s⌋₊, invSqrtAF n * (F (x / n) - LH)‖ ≤ 2 * k := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ n ∈ Ioc 0 ⌊s⌋₊, ‖invSqrtAF n * (F (x / n) - LH)‖
        ≤ ∑ n ∈ Ioc 0 ⌊s⌋₊, (2 * k) / s := by
          refine sum_le_sum fun n hn ↦ ?_
          have hn0 := (mem_Ioc.1 hn).1
          have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
          have hns : (n : ℝ) ≤ s := by
            have : (n : ℝ) ≤ ⌊s⌋₊ := by exact_mod_cast (mem_Ioc.1 hn).2
            linarith [Nat.floor_le hs0.le]
          have hxn : 1 ≤ x / n := by rw [le_div_iff₀ hn']; nlinarith
          have hb := norm_sum_char_div_sqrt_sub_LHalf_le hχ1 hxn
          rw [norm_mul]
          have hg : ‖invSqrtAF n‖ = 1 / √(n : ℝ) := by
            simp only [invSqrtAF, coe_mk, Complex.norm_real, Real.norm_eq_abs]
            exact abs_of_nonneg (by positivity)
          rw [hg]
          calc 1 / √(n : ℝ) * ‖F (x / n) - LH‖ ≤ 1 / √(n : ℝ) * (2 * k * (1 / √(x / n))) :=
                mul_le_mul_of_nonneg_left hb (by positivity)
            _ = 1 / √(n : ℝ) * ((2 * k) / √(x / n)) := by ring
            _ = (2 * k) / s := one_div_sqrt_mul_div_sqrt_div hx0 hn0 _
      _ ≤ 2 * k := sum_Ioc_floor_const_div_le hs0 (by positivity)
  have b5 : ‖(F s - LH) * (G s : ℂ)‖ ≤ 4 * k := by
    have hG0 : 0 ≤ G s := sum_nonneg fun _ _ ↦ by positivity
    have hG1 : G s ≤ 2 * √s := (sum_Ioc_inv_sqrt_le _).trans (by
      gcongr; exact Nat.floor_le hs0.le)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hG0]
    have hsq0 : 0 < √s := by linarith
    calc ‖F s - LH‖ * G s ≤ (2 * k * (1 / √s)) * (2 * √s) :=
          mul_le_mul hFs hG1 hG0 (by positivity)
      _ = 4 * k := by field_simp; ring
  calc _ ≤ ‖2 * s * (P - LOne χ)‖ + ‖(A' : ℂ) * F s‖ +
        ‖∑ n ∈ Ioc 0 ⌊s⌋₊, charDivSqrt χ n * ((G (x / n) - 2 * √(x / n) - A' : ℝ) : ℂ)‖ +
        ‖∑ n ∈ Ioc 0 ⌊s⌋₊, invSqrtAF n * (F (x / n) - LH)‖ + ‖(F s - LH) * (G s : ℂ)‖ := by
        refine (norm_sub_le _ _).trans ?_
        gcongr
        refine (norm_add_le _ _).trans ?_
        gcongr
        refine (norm_add_le _ _).trans ?_
        gcongr
        exact norm_add_le _ _
    _ ≤ 4 * k + |A'| * (‖LH‖ + 2 * k) + 4 + 2 * k + 4 * k := by gcongr

/-- **Apostol, Theorem 6.20.** For a real-valued nonprincipal character `χ`, `L(1, χ) ≠ 0`. -/
@[kb "apostol1976" "Thm 6.20, p. 142"]
theorem LOne_ne_zero_of_isQuadratic {χ : DirichletCharacter ℂ k} (hχ1 : χ ≠ 1)
    (hχ : χ.IsQuadratic) : LOne χ ≠ 0 := by
  intro h0
  obtain ⟨C, hC⟩ := exists_norm_realCharB_sub_le hχ1 hχ
  have hbd : ∀ x : ℝ, 1 ≤ x → realCharB χ x ≤ C := by
    intro x hx
    have := hC x hx
    rw [h0, mul_zero, sub_zero, Complex.norm_real, Real.norm_eq_abs] at this
    exact (le_abs_self _).trans this
  have hev := ((tendsto_realCharB hχ).eventually_gt_atTop C).and (eventually_ge_atTop (1 : ℝ))
  obtain ⟨x, hxC, hx1⟩ := hev.exists
  exact absurd (hbd x hx1) (not_le.2 hxC)

end NTKB.Apostol
