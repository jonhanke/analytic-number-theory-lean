/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Elementary.SpecialValues.JacobiGaussSum

/-!
# The Kronecker character `χ_D` of a fundamental discriminant and its Gauss sum

A **fundamental discriminant** is an integer `D` with `D ≡ 1 (mod 4)` squarefree, or `D = 4k` with
`k ≡ 2, 3 (mod 4)` squarefree (`NTKB.IsFundamentalDiscriminant`; this includes `D = 1`). Its
**Kronecker character** `χ_D = (D/·)` is the Dirichlet character modulo `|D|` (`NTKB.kroneckerChar`):

* `D` odd: `χ_D = (·/|D|)`, the Jacobi character;
* `D = 4k`, `k` odd: `χ_D = χ_{-4} · (·/|k|)`;
* `D = 8k`, `k` odd: `χ_D = χ_8 · (·/|k|)` if `k ≡ 1 (mod 4)` and `χ_{-8} · (·/|k|)` if
  `k ≡ 3 (mod 4)`,

with Mathlib's `ZMod.χ₄`, `ZMod.χ₈`, `ZMod.χ₈'` for `χ_{-4}`, `χ_8`, `χ_{-8}`.
`NTKB.kroneckerChar_apply_odd` checks that `χ_D(n) = J(D | n)` (the Kronecker symbol) for odd
`n > 0`.

**Theorem** (`NTKB.gaussSum_kroneckerChar`). For a fundamental discriminant `D`,
`τ(χ_D) = √D` if `D > 0` and `τ(χ_D) = i √|D|` if `D < 0`.

Proof: the Chinese remainder theorem (`NTKB.gaussSum_eq_mul_of_coprime`), the Gauss sums
`τ(χ_{-4}) = 2i`, `τ(χ_8) = 2√2`, `τ(χ_{-8}) = 2√2 i` (direct computation with `e^{2πi/8}`), the
Jacobi case (`NTKB.gaussSum_jacobiChar`), and the supplementary laws `J(-1|m) = χ_{-4}(m)`,
`J(2|m) = χ_8(m)` to identify the twisting factors.
-/

noncomputable section

open Complex
open scoped Real

namespace NTKB

/-! ### The characters `χ_{-4}`, `χ_8`, `χ_{-8}` and their Gauss sums -/

/-- `χ_{-4}` as a complex Dirichlet character modulo `4` (Mathlib's `ZMod.χ₄`). -/
def chi4 : DirichletCharacter ℂ 4 := ZMod.χ₄.ringHomComp (Int.castRingHom ℂ)

/-- `χ_8` as a complex Dirichlet character modulo `8` (Mathlib's `ZMod.χ₈`). -/
def chi8 : DirichletCharacter ℂ 8 := ZMod.χ₈.ringHomComp (Int.castRingHom ℂ)

/-- `χ_{-8}` as a complex Dirichlet character modulo `8` (Mathlib's `ZMod.χ₈'`). -/
def chi8' : DirichletCharacter ℂ 8 := ZMod.χ₈'.ringHomComp (Int.castRingHom ℂ)

/-- `e(k/N) = e(1/N)^k`. -/
theorem stdAddChar_natCast_eq_pow (N k : ℕ) [NeZero N] :
    (ZMod.stdAddChar (k : ZMod N) : ℂ) = (ZMod.stdAddChar (1 : ZMod N)) ^ k := by
  rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, mul_one]

theorem stdAddChar_one_eq (N : ℕ) [NeZero N] :
    (ZMod.stdAddChar (1 : ZMod N) : ℂ) = cexp (2 * π * I / N) := by
  have h := ZMod.stdAddChar_coe (N := N) 1
  rw [Int.cast_one] at h
  rw [h]
  push_cast
  ring_nf

/-- A Gauss sum modulo `N` as a sum over `0 ≤ k < N`. -/
theorem gaussSum_eq_sum_range {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) :
    gaussSum χ ZMod.stdAddChar =
      ∑ k ∈ Finset.range N, χ (k : ZMod N) * (ZMod.stdAddChar (1 : ZMod N)) ^ k := by
  rw [gaussSum, ← sum_val_eq_sum_range (fun k ↦ χ (k : ZMod N) * (ZMod.stdAddChar (1 : ZMod N)) ^ k)]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [← stdAddChar_natCast_eq_pow, ZMod.natCast_zmod_val]

theorem gaussSum_chi4 : gaussSum chi4 ZMod.stdAddChar = 2 * I := by
  rw [gaussSum_eq_sum_range, stdAddChar_one_eq]
  have hζ : cexp (2 * π * I / (4 : ℕ)) = I := by
    rw [show 2 * (π : ℂ) * I / (4 : ℕ) = π / 2 * I by push_cast; ring, exp_pi_div_two_mul_I]
  rw [hζ]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, chi4, MulChar.ringHomComp_apply]
  have h0 : ZMod.χ₄ ((0 : ℕ) : ZMod 4) = 0 := by decide
  have h1 : ZMod.χ₄ ((1 : ℕ) : ZMod 4) = 1 := by decide
  have h2 : ZMod.χ₄ ((2 : ℕ) : ZMod 4) = 0 := by decide
  have h3 : ZMod.χ₄ ((3 : ℕ) : ZMod 4) = -1 := by decide
  rw [h0, h1, h2, h3]
  simp only [map_zero, map_one, map_neg]
  ring_nf
  rw [I_pow_three]
  ring

/-- `e(1/8) = (√2/2)(1 + i)`. -/
theorem cexp_two_pi_I_div_eight :
    cexp (2 * π * I / (8 : ℕ)) = (√2 / 2 : ℝ) * (1 + I) := by
  rw [show 2 * (π : ℂ) * I / (8 : ℕ) = ((π / 4 : ℝ) : ℂ) * I by push_cast; ring, exp_mul_I,
    ← ofReal_cos, ← ofReal_sin, Real.cos_pi_div_four, Real.sin_pi_div_four]
  ring

private theorem chi8_vals :
    ZMod.χ₈ ((0 : ℕ) : ZMod 8) = 0 ∧ ZMod.χ₈ ((1 : ℕ) : ZMod 8) = 1 ∧
    ZMod.χ₈ ((2 : ℕ) : ZMod 8) = 0 ∧ ZMod.χ₈ ((3 : ℕ) : ZMod 8) = -1 ∧
    ZMod.χ₈ ((4 : ℕ) : ZMod 8) = 0 ∧ ZMod.χ₈ ((5 : ℕ) : ZMod 8) = -1 ∧
    ZMod.χ₈ ((6 : ℕ) : ZMod 8) = 0 ∧ ZMod.χ₈ ((7 : ℕ) : ZMod 8) = 1 := by decide

private theorem chi8'_vals :
    ZMod.χ₈' ((0 : ℕ) : ZMod 8) = 0 ∧ ZMod.χ₈' ((1 : ℕ) : ZMod 8) = 1 ∧
    ZMod.χ₈' ((2 : ℕ) : ZMod 8) = 0 ∧ ZMod.χ₈' ((3 : ℕ) : ZMod 8) = 1 ∧
    ZMod.χ₈' ((4 : ℕ) : ZMod 8) = 0 ∧ ZMod.χ₈' ((5 : ℕ) : ZMod 8) = -1 ∧
    ZMod.χ₈' ((6 : ℕ) : ZMod 8) = 0 ∧ ZMod.χ₈' ((7 : ℕ) : ZMod 8) = -1 := by decide

private theorem sqrt_two_sq_complex : ((√2 : ℝ) : ℂ) ^ 2 = 2 := by
  rw [← ofReal_pow, Real.sq_sqrt (by norm_num)]; push_cast; ring

/-- `e(1/8)² = i`. -/
private theorem cexp_two_pi_I_div_eight_sq : cexp (2 * π * I / (8 : ℕ)) ^ 2 = I := by
  rw [← Complex.exp_nat_mul, show ((2 : ℕ) : ℂ) * (2 * π * I / (8 : ℕ)) = π / 2 * I by
    push_cast; ring, exp_pi_div_two_mul_I]

theorem gaussSum_chi8 : gaussSum chi8 ZMod.stdAddChar = 2 * √2 := by
  rw [gaussSum_eq_sum_range, stdAddChar_one_eq]
  have hζ2 := cexp_two_pi_I_div_eight_sq
  have hζ := cexp_two_pi_I_div_eight
  set ζ := cexp (2 * π * I / (8 : ℕ))
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, chi8, MulChar.ringHomComp_apply]
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := chi8_vals
  rw [h0, h1, h2, h3, h4, h5, h6, h7]
  simp only [map_zero, map_one, map_neg]
  have e3 : ζ ^ 3 = I * ζ := by rw [pow_succ, hζ2]
  have e5 : ζ ^ 5 = -ζ := by
    rw [show ζ ^ 5 = (ζ ^ 2) ^ 2 * ζ by ring, hζ2, I_sq]; ring
  have e7 : ζ ^ 7 = -(I * ζ) := by
    rw [show ζ ^ 7 = (ζ ^ 2) ^ 3 * ζ by ring, hζ2, I_pow_three, neg_mul]
  ring_nf
  rw [e3, e5, e7, hζ]
  push_cast
  ring_nf
  rw [I_sq]
  ring

theorem gaussSum_chi8' : gaussSum chi8' ZMod.stdAddChar = 2 * √2 * I := by
  rw [gaussSum_eq_sum_range, stdAddChar_one_eq]
  have hζ2 := cexp_two_pi_I_div_eight_sq
  have hζ := cexp_two_pi_I_div_eight
  set ζ := cexp (2 * π * I / (8 : ℕ))
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, chi8', MulChar.ringHomComp_apply]
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := chi8'_vals
  rw [h0, h1, h2, h3, h4, h5, h6, h7]
  simp only [map_zero, map_one, map_neg]
  have e3 : ζ ^ 3 = I * ζ := by rw [pow_succ, hζ2]
  have e5 : ζ ^ 5 = -ζ := by
    rw [show ζ ^ 5 = (ζ ^ 2) ^ 2 * ζ by ring, hζ2, I_sq]; ring
  have e7 : ζ ^ 7 = -(I * ζ) := by
    rw [show ζ ^ 7 = (ζ ^ 2) ^ 3 * ζ by ring, hζ2, I_pow_three, neg_mul]
  ring_nf
  rw [e3, e5, e7, hζ]
  push_cast
  ring_nf
  rw [I_sq]
  ring

/-! ### Fundamental discriminants and the Kronecker character -/

/-- A **fundamental discriminant**: `D ≡ 1 (mod 4)` squarefree, or `D = 4k` with
`k ≡ 2, 3 (mod 4)` squarefree. (This includes `D = 1`.) -/
def IsFundamentalDiscriminant (D : ℤ) : Prop :=
  (D % 4 = 1 ∧ Squarefree D) ∨ (D % 4 = 0 ∧ ((D / 4) % 4 = 2 ∨ (D / 4) % 4 = 3) ∧ Squarefree (D / 4))

theorem IsFundamentalDiscriminant.ne_zero {D : ℤ} (hD : IsFundamentalDiscriminant D) : D ≠ 0 := by
  rintro rfl
  rcases hD with ⟨h, _⟩ | ⟨_, h, _⟩ <;> omega

/-- `|D| = c |D / c|` when `c ∣ D`. -/
theorem natAbs_eq_mul_natAbs_div {D : ℤ} {c : ℕ} (h : (c : ℤ) ∣ D) :
    D.natAbs = c * (D / c).natAbs := by
  conv_lhs => rw [← Int.mul_ediv_cancel' h]
  rw [Int.natAbs_mul, Int.natAbs_natCast]

theorem natAbs_eq_four_mul {D : ℤ} (h : (4 : ℤ) ∣ D) : D.natAbs = 4 * (D / 4).natAbs := by
  simpa using natAbs_eq_mul_natAbs_div (c := 4) (by simpa using h)

theorem natAbs_eq_eight_mul {D : ℤ} (h : (8 : ℤ) ∣ D) : D.natAbs = 8 * (D / 8).natAbs := by
  simpa using natAbs_eq_mul_natAbs_div (c := 8) (by simpa using h)

/-- The **Kronecker character** `χ_D` modulo `|D|`, for `D` a fundamental discriminant (junk, the
trivial character, if `D` is even and not of the form `4k` or `8k` with `k` odd):
* `D` odd: the Jacobi character `(·/|D|)`;
* `D = 4k`, `k` odd: `χ_{-4} · (·/|k|)`;
* `D = 8k`, `k` odd: `χ_8 · (·/|k|)` if `k ≡ 1 (mod 4)`, `χ_{-8} · (·/|k|)` otherwise. -/
def kroneckerChar (D : ℤ) : DirichletCharacter ℂ D.natAbs :=
  if D % 2 = 1 then jacobiChar D.natAbs
  else if h4 : D % 8 = 4 then
    DirichletCharacter.changeLevel
        (⟨(D / 4).natAbs, natAbs_eq_four_mul (by omega)⟩ : 4 ∣ D.natAbs) chi4 *
      DirichletCharacter.changeLevel
        (⟨4, by rw [natAbs_eq_four_mul (by omega), mul_comm]⟩ :
          (D / 4).natAbs ∣ D.natAbs) (jacobiChar (D / 4).natAbs)
  else if h8 : D % 16 = 8 then
    (if (D / 8) % 4 = 1 then
      DirichletCharacter.changeLevel
        (⟨(D / 8).natAbs, natAbs_eq_eight_mul (by omega)⟩ : 8 ∣ D.natAbs) chi8
    else
      DirichletCharacter.changeLevel
        (⟨(D / 8).natAbs, natAbs_eq_eight_mul (by omega)⟩ : 8 ∣ D.natAbs) chi8') *
      DirichletCharacter.changeLevel
        (⟨8, by rw [natAbs_eq_eight_mul (by omega), mul_comm]⟩ :
          (D / 8).natAbs ∣ D.natAbs) (jacobiChar (D / 8).natAbs)
  else 1

/-- `√(c m) = √c √m` in `ℂ`. -/
private theorem ofReal_sqrt_mul_nat (c m : ℕ) :
    ((√((c * m : ℕ) : ℝ) : ℝ) : ℂ) = (√(c : ℝ) : ℂ) * (√(m : ℝ) : ℂ) := by
  rw [Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg _), ofReal_mul]

private theorem sqrt_four : √((4 : ℕ) : ℝ) = 2 := by
  rw [show ((4 : ℕ) : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

private theorem sqrt_eight : √((8 : ℕ) : ℝ) = 2 * √2 := by
  rw [show ((8 : ℕ) : ℝ) = 2 ^ 2 * 2 by norm_num, Real.sqrt_mul (by norm_num),
    Real.sqrt_sq (by norm_num)]

/-- The target value `√D` or `i√|D|`, written through `|D| = c m`. -/
private theorem target_eq {D : ℤ} {c m : ℕ} (hDcm : D.natAbs = c * m) :
    (if 0 < D then ((√(D : ℝ) : ℝ) : ℂ) else I * √(-D : ℝ)) =
      (if 0 < D then (1 : ℂ) else I) * (√(c : ℝ) : ℂ) * (√(m : ℝ) : ℂ) := by
  have habs : (|D| : ℤ) = ((c * m : ℕ) : ℤ) := by rw [← hDcm, Int.natCast_natAbs]
  split_ifs with h
  · have hD : (D : ℝ) = ((c * m : ℕ) : ℝ) := by
      have : D = ((c * m : ℕ) : ℤ) := by rw [← habs, abs_of_pos h]
      exact_mod_cast this
    rw [hD, ofReal_sqrt_mul_nat, one_mul]
  · have hD : (-D : ℝ) = ((c * m : ℕ) : ℝ) := by
      have : -D = ((c * m : ℕ) : ℤ) := by rw [← habs, abs_of_nonpos (not_lt.mp h)]
      exact_mod_cast this
    rw [hD, ofReal_sqrt_mul_nat, mul_assoc]

/-- For odd `m`, `χ_8(m)^2 = 1`. -/
private theorem chi8_nat_sq {m : ℕ} (hm : m % 2 = 1) : (ZMod.χ₈ (m : ZMod 8) : ℂ) ^ 2 = 1 := by
  rw [ZMod.χ₈_nat_eq_if_mod_eight, if_neg (by omega)]
  split_ifs <;> norm_num

/-- **Gauss's evaluation for the Kronecker character of a fundamental discriminant**:
`τ(χ_D) = √D` if `D > 0` and `τ(χ_D) = i √|D|` if `D < 0`. -/
@[kb "irelandrosen1990" "Ch. 6, §4 and Ch. 16 (Gauss sums of quadratic characters)"]
theorem gaussSum_kroneckerChar {D : ℤ} (hD : IsFundamentalDiscriminant D) [NeZero D.natAbs] :
    gaussSum (kroneckerChar D) ZMod.stdAddChar =
      if 0 < D then ((√(D : ℝ) : ℝ) : ℂ) else I * √(-D : ℝ) := by
  rcases hD with ⟨h1, hsq⟩ | ⟨h0, h23, hsq⟩
  · -- `D ≡ 1 (mod 4)`: the Jacobi character
    have hodd : Odd D.natAbs := by rw [Nat.odd_iff]; omega
    have hsqm : Squarefree D.natAbs := Int.squarefree_natAbs.mpr hsq
    rw [kroneckerChar, if_pos (by omega), gaussSum_jacobiChar hodd hsqm,
      target_eq (c := 1) (m := D.natAbs) (by ring), sqrtSign]
    simp only [Nat.cast_one, Real.sqrt_one, ofReal_one, mul_one]
    split_ifs with hpos hmod hmod <;> first | rfl | (exfalso; omega) | skip
    · rw [one_mul]
  rcases h23 with h2 | h3
  · -- `D = 8k`, `k` odd
    have h16 : D % 16 = 8 := by omega
    set k := D / 8 with hk
    have hkodd : k.natAbs % 2 = 1 := by omega
    have hD4 : D / 4 = 2 * k := by omega
    have hksq : Squarefree k := hsq.squarefree_of_dvd ⟨2, by rw [hD4]; ring⟩
    have hm : Odd k.natAbs := Nat.odd_iff.mpr hkodd
    have hmsq : Squarefree k.natAbs := Int.squarefree_natAbs.mpr hksq
    have : NeZero k.natAbs := ⟨by omega⟩
    have hN : D.natAbs = 8 * k.natAbs := natAbs_eq_eight_mul (by omega)
    have hcop : Nat.Coprime 8 k.natAbs :=
      Nat.Coprime.pow_left 3 (Nat.coprime_two_left.mpr hm)
    have hJ8 : jacobiChar k.natAbs ((8 : ℕ) : ZMod k.natAbs) =
        (ZMod.χ₈ (k.natAbs : ZMod 8) : ℂ) ^ 3 := by
      rw [show ((8 : ℕ) : ZMod k.natAbs) = ((2 ^ 3 : ℤ) : ZMod k.natAbs) by push_cast; ring,
        jacobiChar_intCast, jacobiSym.pow_left, jacobiSym.at_two hm]
      push_cast; rfl
    rw [target_eq hN, sqrt_eight]
    by_cases hk1 : k % 4 = 1
    · -- `χ_D = χ_8 · (·/|k|)`
      rw [kroneckerChar, if_neg (by omega), dif_neg (by omega), dif_pos h16, if_pos hk1]
      rw [gaussSum_eq_mul_of_coprime hN hcop chi8 (jacobiChar k.natAbs) _
        (changeLevel_mul_changeLevel_apply hN hcop _ _ _ _), gaussSum_chi8,
        gaussSum_jacobiChar hm hmsq, hJ8, sqrtSign]
      have hc : chi8 (k.natAbs : ZMod 8) = (ZMod.χ₈ (k.natAbs : ZMod 8) : ℂ) := rfl
      rw [hc, ← pow_succ', show 3 + 1 = 2 * 2 by rfl, pow_mul, chi8_nat_sq hkodd, one_pow, one_mul]
      split_ifs with hpos hmod hmod <;> first | (exfalso; omega) | (push_cast; ring)
    · -- `χ_D = χ_{-8} · (·/|k|)`
      rw [kroneckerChar, if_neg (by omega), dif_neg (by omega), dif_pos h16, if_neg hk1]
      rw [gaussSum_eq_mul_of_coprime hN hcop chi8' (jacobiChar k.natAbs) _
        (changeLevel_mul_changeLevel_apply hN hcop _ _ _ _), gaussSum_chi8',
        gaussSum_jacobiChar hm hmsq, hJ8, sqrtSign]
      have hc : chi8' (k.natAbs : ZMod 8) =
          (ZMod.χ₄ (k.natAbs : ZMod 4) : ℂ) * (ZMod.χ₈ (k.natAbs : ZMod 8) : ℂ) := by
        rw [chi8', MulChar.ringHomComp_apply, ZMod.χ₈'_eq_χ₄_mul_χ₈,
          ZMod.cast_natCast (by norm_num : 4 ∣ 8), map_mul]
        rfl
      rw [hc, mul_assoc (ZMod.χ₄ _ : ℂ), ← pow_succ', show 3 + 1 = 2 * 2 by rfl, pow_mul,
        chi8_nat_sq hkodd, one_pow, mul_one]
      by_cases hpos : 0 < D
      · have hm4 : k.natAbs % 4 = 3 := by omega
        rw [ZMod.χ₄_nat_three_mod_four hm4, if_pos hpos, if_neg (by omega)]
        push_cast
        ring_nf
        rw [I_sq]
        ring
      · have hm4 : k.natAbs % 4 = 1 := by omega
        rw [ZMod.χ₄_nat_one_mod_four hm4, if_neg hpos, if_pos hm4]
        push_cast
        ring
  · -- `D = 4k`, `k ≡ 3 (mod 4)`
    have h8 : D % 8 = 4 := by omega
    set k := D / 4 with hk
    have hkodd : k.natAbs % 2 = 1 := by omega
    have hm : Odd k.natAbs := Nat.odd_iff.mpr hkodd
    have hmsq : Squarefree k.natAbs := Int.squarefree_natAbs.mpr hsq
    have : NeZero k.natAbs := ⟨by omega⟩
    have hN : D.natAbs = 4 * k.natAbs := natAbs_eq_four_mul (by omega)
    have hcop : Nat.Coprime 4 k.natAbs :=
      Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr hm)
    have hJ4 : jacobiChar k.natAbs ((4 : ℕ) : ZMod k.natAbs) = 1 := by
      rw [show ((4 : ℕ) : ZMod k.natAbs) = ((4 : ℤ) : ZMod k.natAbs) by push_cast; rfl,
        jacobiChar_intCast, jacobiSym.at_four hm, Int.cast_one]
    rw [target_eq hN, sqrt_four, kroneckerChar, if_neg (by omega), dif_pos h8,
      gaussSum_eq_mul_of_coprime hN hcop chi4 (jacobiChar k.natAbs) _
        (changeLevel_mul_changeLevel_apply hN hcop _ _ _ _), gaussSum_chi4,
      gaussSum_jacobiChar hm hmsq, hJ4, sqrtSign]
    have hc : chi4 (k.natAbs : ZMod 4) = (ZMod.χ₄ (k.natAbs : ZMod 4) : ℂ) := rfl
    rw [hc]
    by_cases hpos : 0 < D
    · have hm4 : k.natAbs % 4 = 3 := by omega
      rw [ZMod.χ₄_nat_three_mod_four hm4, if_pos hpos, if_neg (by omega)]
      push_cast
      ring_nf
      rw [I_sq]
      ring
    · have hm4 : k.natAbs % 4 = 1 := by omega
      rw [ZMod.χ₄_nat_one_mod_four hm4, if_neg hpos, if_pos hm4]
      push_cast
      ring

end NTKB
