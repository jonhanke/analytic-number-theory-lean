/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Elementary.SpecialValues.KroneckerPrimitive
import NTKB.Elementary.SpecialValues.ValueAtOne

/-!
# Special values of `L(s, χ_D)` for a fundamental discriminant `D`

For a fundamental discriminant `D` (Kronecker character `χ_D`, primitive of conductor `|D|`,
`χ_D(-1) = sign D`, `χ̄_D = χ_D`, `τ(χ_D) = √D` or `i√|D|`), with `B_{k,χ_D} ∈ ℚ`:

* `L(1 - k, χ_D) = -B_{k,χ_D}/k ∈ ℚ` for every `k ≥ 1` (`NTKB.LFunction_kroneckerChar_one_sub_nat`);
* for `k ≥ 1` with `χ_D(-1) = (-1)^k` (that is, `k` even if `D > 0`, `k` odd if `D < 0`), with
  `δ = k mod 2`,
  $$L(k,\chi_D) = (-1)^{1+(k-\delta)/2}\,\frac{2^{k-1} B_{k,\chi_D}}{k!\,|D|^{k-1}}\cdot
    \frac{\pi^k}{\sqrt{|D|}},$$
  a rational multiple of `π^k/√|D|` (`NTKB.LFunction_kroneckerChar_natCast`,
  `NTKB.exists_rat_LFunction_kroneckerChar_natCast`).

For example `L(1, χ_{-4}) = π/4`, `L(2, χ_5) = 4π²/(25√5)`, `L(1, χ_{-3}) = π/(3√3)`.
-/

noncomputable section

open Complex DirichletCharacter
open scoped Real

namespace NTKB

/-! ### `χ_D` is quadratic and `χ_D(-1) = sign D` -/

private def IsSign (x : ℂ) : Prop := x = 0 ∨ x = 1 ∨ x = -1

private theorem IsSign.mul {x y : ℂ} (hx : IsSign x) (hy : IsSign y) : IsSign (x * y) := by
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;> simp [IsSign]

private theorem isSign_jacobiChar (m : ℕ) (a : ZMod m) : IsSign (jacobiChar m a) := by
  classical
  by_cases ha : IsUnit a
  · rw [jacobiChar_apply_of_isUnit ha]
    rcases jacobiSym.trichotomy (ZMod.cast a : ℤ) m with h | h | h <;> rw [h] <;> simp [IsSign]
  · rw [MulChar.map_nonunit _ ha]; simp [IsSign]

private theorem isSign_of_isQuadratic {n : ℕ} {χ : DirichletCharacter ℂ n} (hχ : χ.IsQuadratic)
    (a : ZMod n) : IsSign (χ a) := hχ a

/-- The Kronecker character of a fundamental discriminant is quadratic. -/
theorem kroneckerChar_isQuadratic {D : ℤ} (hD : IsFundamentalDiscriminant D) [NeZero D.natAbs] :
    (kroneckerChar D).IsQuadratic := by
  intro a
  show IsSign _
  rcases hD with ⟨h1, -⟩ | ⟨h0, h23, -⟩
  · rw [kroneckerChar, if_pos (by omega)]; exact isSign_jacobiChar _ a
  rcases h23 with h2 | h3
  · have h16 : D % 16 = 8 := by omega
    have hm : Odd (D / 8).natAbs := Nat.odd_iff.mpr (by omega)
    have : NeZero (D / 8).natAbs := ⟨by omega⟩
    have hN : D.natAbs = 8 * (D / 8).natAbs := natAbs_eq_eight_mul (by omega)
    have hcop : Nat.Coprime 8 (D / 8).natAbs :=
      Nat.Coprime.pow_left 3 (Nat.coprime_two_left.mpr hm)
    rw [kroneckerChar, if_neg (by omega), dif_neg (by omega), dif_pos h16]
    split_ifs
    · rw [changeLevel_mul_changeLevel_apply hN hcop]
      exact (isSign_of_isQuadratic (ZMod.isQuadratic_χ₈.comp _) _).mul (isSign_jacobiChar _ _)
    · rw [changeLevel_mul_changeLevel_apply hN hcop]
      exact (isSign_of_isQuadratic (ZMod.isQuadratic_χ₈'.comp _) _).mul (isSign_jacobiChar _ _)
  · have h8 : D % 8 = 4 := by omega
    have hm : Odd (D / 4).natAbs := Nat.odd_iff.mpr (by omega)
    have : NeZero (D / 4).natAbs := ⟨by omega⟩
    have hN : D.natAbs = 4 * (D / 4).natAbs := natAbs_eq_four_mul (by omega)
    have hcop : Nat.Coprime 4 (D / 4).natAbs :=
      Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr hm)
    rw [kroneckerChar, if_neg (by omega), dif_pos h8, changeLevel_mul_changeLevel_apply hN hcop]
    exact (isSign_of_isQuadratic (ZMod.isQuadratic_χ₄.comp _) _).mul (isSign_jacobiChar _ _)

/-- `χ_D` is real: `χ̄_D = χ_D⁻¹ = χ_D`. -/
theorem kroneckerChar_inv {D : ℤ} (hD : IsFundamentalDiscriminant D) [NeZero D.natAbs] :
    (kroneckerChar D)⁻¹ = kroneckerChar D :=
  (kroneckerChar_isQuadratic hD).inv

/-- `J(-1 | m)` through `jacobiChar`. -/
private theorem jacobiChar_neg_one {m : ℕ} [NeZero m] (hm : Odd m) :
    jacobiChar m (-1) = (ZMod.χ₄ (m : ZMod 4) : ℂ) := by
  rw [show (-1 : ZMod m) = ((-1 : ℤ) : ZMod m) by push_cast; rfl, jacobiChar_intCast,
    jacobiSym.at_neg_one hm]

/-- **`χ_D(-1) = sign D`**. -/
theorem kroneckerChar_neg_one {D : ℤ} (hD : IsFundamentalDiscriminant D) [NeZero D.natAbs] :
    kroneckerChar D (-1) = if 0 < D then 1 else -1 := by
  rcases hD with ⟨h1, -⟩ | ⟨h0, h23, -⟩
  · rw [kroneckerChar, if_pos (by omega), jacobiChar_neg_one (Nat.odd_iff.mpr (by omega))]
    split_ifs with hpos
    · rw [ZMod.χ₄_nat_one_mod_four (by omega)]; simp
    · rw [ZMod.χ₄_nat_three_mod_four (by omega)]; simp
  rcases h23 with h2 | h3
  · have h16 : D % 16 = 8 := by omega
    have hm : Odd (D / 8).natAbs := Nat.odd_iff.mpr (by omega)
    have : NeZero (D / 8).natAbs := ⟨by omega⟩
    have hN : D.natAbs = 8 * (D / 8).natAbs := natAbs_eq_eight_mul (by omega)
    have hcop : Nat.Coprime 8 (D / 8).natAbs :=
      Nat.Coprime.pow_left 3 (Nat.coprime_two_left.mpr hm)
    have hc8 : (ZMod.cast (-1 : ZMod D.natAbs) : ZMod 8) = -1 := by
      rw [ZMod.cast_neg ⟨_, hN⟩, ZMod.cast_one ⟨_, hN⟩]
    have hcm : (ZMod.cast (-1 : ZMod D.natAbs) : ZMod (D / 8).natAbs) = -1 := by
      rw [ZMod.cast_neg ⟨8, by rw [hN, mul_comm]⟩, ZMod.cast_one ⟨8, by rw [hN, mul_comm]⟩]
    rw [kroneckerChar, if_neg (by omega), dif_neg (by omega), dif_pos h16]
    split_ifs with hk1 hpos hpos
    · rw [changeLevel_mul_changeLevel_apply hN hcop, hc8, hcm, jacobiChar_neg_one hm,
        chi8, MulChar.ringHomComp_apply, show ZMod.χ₈ (-1 : ZMod 8) = 1 by decide,
        ZMod.χ₄_nat_one_mod_four (by omega)]
      simp
    · rw [changeLevel_mul_changeLevel_apply hN hcop, hc8, hcm, jacobiChar_neg_one hm,
        chi8, MulChar.ringHomComp_apply, show ZMod.χ₈ (-1 : ZMod 8) = 1 by decide,
        ZMod.χ₄_nat_three_mod_four (by omega)]
      simp
    · rw [changeLevel_mul_changeLevel_apply hN hcop, hc8, hcm, jacobiChar_neg_one hm,
        chi8', MulChar.ringHomComp_apply, show ZMod.χ₈' (-1 : ZMod 8) = -1 by decide,
        ZMod.χ₄_nat_three_mod_four (by omega)]
      simp
    · rw [changeLevel_mul_changeLevel_apply hN hcop, hc8, hcm, jacobiChar_neg_one hm,
        chi8', MulChar.ringHomComp_apply, show ZMod.χ₈' (-1 : ZMod 8) = -1 by decide,
        ZMod.χ₄_nat_one_mod_four (by omega)]
      simp
  · have h8 : D % 8 = 4 := by omega
    have hm : Odd (D / 4).natAbs := Nat.odd_iff.mpr (by omega)
    have : NeZero (D / 4).natAbs := ⟨by omega⟩
    have hN : D.natAbs = 4 * (D / 4).natAbs := natAbs_eq_four_mul (by omega)
    have hcop : Nat.Coprime 4 (D / 4).natAbs :=
      Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr hm)
    have hc4 : (ZMod.cast (-1 : ZMod D.natAbs) : ZMod 4) = -1 := by
      rw [ZMod.cast_neg ⟨_, hN⟩, ZMod.cast_one ⟨_, hN⟩]
    have hcm : (ZMod.cast (-1 : ZMod D.natAbs) : ZMod (D / 4).natAbs) = -1 := by
      rw [ZMod.cast_neg ⟨4, by rw [hN, mul_comm]⟩, ZMod.cast_one ⟨4, by rw [hN, mul_comm]⟩]
    rw [kroneckerChar, if_neg (by omega), dif_pos h8, changeLevel_mul_changeLevel_apply hN hcop,
      hc4, hcm, jacobiChar_neg_one hm, chi4, MulChar.ringHomComp_apply,
      show ZMod.χ₄ (-1 : ZMod 4) = -1 by decide]
    split_ifs with hpos
    · rw [ZMod.χ₄_nat_three_mod_four (by omega)]; simp
    · rw [ZMod.χ₄_nat_one_mod_four (by omega)]; simp

/-! ### Rationality of `B_{k,χ}` for a quadratic character -/

/-- For a quadratic character, `B_{k,χ}` is rational. -/
theorem exists_rat_generalizedBernoulli_of_isQuadratic {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsQuadratic) (k : ℕ) :
    ∃ q : ℚ, generalizedBernoulli χ k = q := by
  classical
  let r : ZMod N → ℚ := fun a ↦ if χ a = 1 then 1 else if χ a = -1 then -1 else 0
  have hr (a : ZMod N) : χ a = (r a : ℂ) := by
    rcases hχ a with h | h | h <;> simp [r, h] <;> norm_num
  refine ⟨(N : ℚ) ^ ((k : ℤ) - 1) * ∑ a : ZMod N, r a *
    (Polynomial.bernoulli k).eval (((if a = 0 then N else a.val : ℕ) : ℚ) / N), ?_⟩
  rw [generalizedBernoulli_def]
  simp only [hr, Rat.cast_mul, Rat.cast_sum]
  rfl

/-! ### The values -/

/-- **`L(1 - k, χ_D) = -B_{k,χ_D}/k`**, a rational number, for every `k ≥ 1`. -/
@[kb "washington1997" "Theorem 4.2 (quadratic case)"]
theorem LFunction_kroneckerChar_one_sub_nat {D : ℤ} (hD : IsFundamentalDiscriminant D)
    [NeZero D.natAbs] {k : ℕ} (hk : 1 ≤ k) :
    LFunction (kroneckerChar D) (1 - k) = -generalizedBernoulli (kroneckerChar D) k / k ∧
      ∃ q : ℚ, LFunction (kroneckerChar D) (1 - k) = q := by
  refine ⟨LFunction_one_sub_nat _ hk, ?_⟩
  obtain ⟨q, hq⟩ := exists_rat_generalizedBernoulli_of_isQuadratic (kroneckerChar_isQuadratic hD) k
  exact ⟨-q / k, by rw [LFunction_one_sub_nat _ hk, hq]; push_cast; ring⟩

/-- **`L(k, χ_D)` for `χ_D(-1) = (-1)^k`**: with `δ = k mod 2`,
`L(k, χ_D) = (-1)^{1+(k-δ)/2} 2^{k-1} B_{k,χ_D} / (k! |D|^{k-1}) · π^k / √|D|`. -/
@[kb "washington1997" "Ch. 4 (quadratic case of the value of L(n, χ))"]
theorem LFunction_kroneckerChar_natCast {D : ℤ} (hD : IsFundamentalDiscriminant D)
    [NeZero D.natAbs] {k : ℕ} (hk : 1 ≤ k) (hpar : kroneckerChar D (-1) = (-1) ^ k) :
    LFunction (kroneckerChar D) k =
      (-1) ^ (1 + (k - k % 2) / 2) * 2 ^ (k - 1) * generalizedBernoulli (kroneckerChar D) k /
        (k.factorial * (D.natAbs : ℂ) ^ (k - 1)) * (π ^ k / (√(D.natAbs : ℝ) : ℂ)) := by
  have hprim := kroneckerChar_isPrimitive hD
  rw [LFunction_natCast _ hprim hk hpar, kroneckerChar_inv hD, gaussSum_kroneckerChar hD]
  have hN : (D.natAbs : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne _)
  have hNr : (0 : ℝ) < D.natAbs := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne _))
  have hs : ((√(D.natAbs : ℝ) : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hNr).ne'
  have hs2 : ((√(D.natAbs : ℝ) : ℝ) : ℂ) ^ 2 = D.natAbs := by
    rw [← ofReal_pow, Real.sq_sqrt hNr.le]; push_cast; rfl
  have hk1 : (D.natAbs : ℂ) ^ k = D.natAbs ^ (k - 1) * D.natAbs := by
    rw [← pow_succ, Nat.sub_add_cancel hk]
  have h2k : (2 : ℂ) ^ k = 2 ^ (k - 1) * 2 := by rw [← pow_succ, Nat.sub_add_cancel hk]
  -- `τ(χ_D) / i^δ = √|D|`
  have hneg := kroneckerChar_neg_one hD
  have hτ : (if 0 < D then ((√(D : ℝ) : ℝ) : ℂ) else I * √(-D : ℝ)) / I ^ (k % 2) =
      (√(D.natAbs : ℝ) : ℂ) := by
    split_ifs with hpos
    · have hk2 : k % 2 = 0 := by
        rw [hneg, if_pos hpos] at hpar
        rcases Nat.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
        · omega
        · rw [hj, pow_succ, pow_mul] at hpar; norm_num at hpar
      rw [hk2, pow_zero, div_one]
      congr 2
      rw [Nat.cast_natAbs, Int.cast_abs, abs_of_pos (by exact_mod_cast hpos)]
    · have hk2 : k % 2 = 1 := by
        rw [hneg, if_neg hpos] at hpar
        rcases Nat.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
        · rw [hj, ← two_mul, pow_mul] at hpar; norm_num at hpar
        · omega
      rw [hk2, pow_one, mul_div_cancel_left₀ _ I_ne_zero]
      congr 2
      have hD0 : D ≠ 0 := Int.natAbs_ne_zero.mp (NeZero.ne _)
      have hneg' : (D : ℝ) < 0 := by exact_mod_cast lt_of_le_of_ne (not_lt.mp hpos) hD0
      push_cast
      rw [Nat.cast_natAbs, Int.cast_abs, abs_of_neg hneg']
  calc (-1) ^ (1 + (k - k % 2) / 2) *
        (if 0 < D then ((√(D : ℝ) : ℝ) : ℂ) else I * √(-D : ℝ)) /
          (2 * I ^ (k % 2)) * (2 * π / D.natAbs) ^ k *
        generalizedBernoulli (kroneckerChar D) k / k.factorial
      = (-1) ^ (1 + (k - k % 2) / 2) *
          ((if 0 < D then ((√(D : ℝ) : ℝ) : ℂ) else I * √(-D : ℝ)) / I ^ (k % 2)) / 2 *
          (2 * π / D.natAbs) ^ k * generalizedBernoulli (kroneckerChar D) k / k.factorial := by
        have : I ^ (k % 2) ≠ 0 := pow_ne_zero _ I_ne_zero
        field_simp
    _ = _ := by
        rw [hτ, div_pow, mul_pow, hk1, h2k]
        field_simp
        linear_combination (generalizedBernoulli (kroneckerChar D) k * (k.factorial : ℂ)⁻¹) * hs2

/-- `L(k, χ_D)` is a rational multiple of `π^k / √|D|`. -/
theorem exists_rat_LFunction_kroneckerChar_natCast {D : ℤ} (hD : IsFundamentalDiscriminant D)
    [NeZero D.natAbs] {k : ℕ} (hk : 1 ≤ k) (hpar : kroneckerChar D (-1) = (-1) ^ k) :
    ∃ c : ℚ, LFunction (kroneckerChar D) k = c * (π ^ k / (√(D.natAbs : ℝ) : ℂ)) := by
  obtain ⟨q, hq⟩ := exists_rat_generalizedBernoulli_of_isQuadratic (kroneckerChar_isQuadratic hD) k
  refine ⟨(-1) ^ (1 + (k - k % 2) / 2) * 2 ^ (k - 1) * q / (k.factorial * D.natAbs ^ (k - 1)), ?_⟩
  rw [LFunction_kroneckerChar_natCast hD hk hpar, hq]
  push_cast
  ring

end NTKB
