/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Elementary.SpecialValues.KroneckerSymbol

/-!
# Davenport, Chapter 5: multiplicativity of the Kronecker symbol in `d`

(§5, p. 40.) `(d₁ d₂ / n) = (d₁/n)(d₂/n)` for relatively prime `d₁, d₂`: for odd `n` this is the
multiplicativity of the Jacobi symbol in its upper argument, and for even `n` it follows from
Kronecker's definition (both sides vanish if one `dᵢ` is even; if both are odd the characters are
Jacobi symbols `(n/|dᵢ|)`, multiplicative in the lower argument).

Here `(d/n)` is `NTKB.kroneckerChar d` (the Kronecker character of a fundamental discriminant,
`(d/n) = J(d | n)` for odd `n`), and the statement is for fundamental `d₁, d₂, d₁ d₂` (which holds
for relatively prime fundamental `d₁, d₂`).
-/

namespace NTKB.Davenport

theorem kroneckerChar_eq_jacobiChar_of_odd {D : ℤ} (hD : D % 2 = 1) :
    kroneckerChar D = jacobiChar D.natAbs := by
  rw [kroneckerChar, if_pos hD]

theorem kroneckerChar_natCast_eq_zero_of_even {D : ℤ} (hD : D % 2 = 0) {n : ℕ} (hn : 2 ∣ n) :
    kroneckerChar D (n : ZMod D.natAbs) = 0 := by
  refine MulChar.map_nonunit _ ?_
  rw [ZMod.isUnit_iff_coprime]
  exact Nat.not_coprime_of_dvd_of_dvd (by norm_num) hn (by omega)

/-- **Davenport §5, p. 40.** `(d₁ d₂ / n) = (d₁/n)(d₂/n)` for fundamental discriminants
`d₁, d₂` with `d₁ d₂` fundamental (e.g. `d₁, d₂` relatively prime), for every `n ≥ 0`. -/
@[kb "davenport1980" "Ch 5, p. 40"]
theorem kroneckerChar_mul_apply {D₁ D₂ : ℤ} (h₁ : IsFundamentalDiscriminant D₁)
    (h₂ : IsFundamentalDiscriminant D₂) (h₁₂ : IsFundamentalDiscriminant (D₁ * D₂)) (n : ℕ) :
    kroneckerChar (D₁ * D₂) (n : ZMod (D₁ * D₂).natAbs) =
      kroneckerChar D₁ (n : ZMod D₁.natAbs) * kroneckerChar D₂ (n : ZMod D₂.natAbs) := by
  have : NeZero D₁.natAbs := ⟨Int.natAbs_ne_zero.mpr h₁.ne_zero⟩
  have : NeZero D₂.natAbs := ⟨Int.natAbs_ne_zero.mpr h₂.ne_zero⟩
  have : NeZero (D₁ * D₂).natAbs := ⟨Int.natAbs_ne_zero.mpr h₁₂.ne_zero⟩
  rcases Nat.even_or_odd n with hn | hn
  · have hn2 : 2 ∣ n := even_iff_two_dvd.mp hn
    rcases Int.emod_two_eq_zero_or_one D₁ with e₁ | e₁
    · rw [kroneckerChar_natCast_eq_zero_of_even e₁ hn2,
        kroneckerChar_natCast_eq_zero_of_even (by rw [Int.mul_emod, e₁]; simp) hn2, zero_mul]
    rcases Int.emod_two_eq_zero_or_one D₂ with e₂ | e₂
    · rw [kroneckerChar_natCast_eq_zero_of_even e₂ hn2,
        kroneckerChar_natCast_eq_zero_of_even (by rw [Int.mul_emod, e₂]; simp) hn2, mul_zero]
    have e₁₂ : D₁ * D₂ % 2 = 1 := by rw [Int.mul_emod, e₁, e₂]; rfl
    rw [kroneckerChar_eq_jacobiChar_of_odd e₁, kroneckerChar_eq_jacobiChar_of_odd e₂,
      kroneckerChar_eq_jacobiChar_of_odd e₁₂]
    have h := jacobiChar_intCast (m := (D₁ * D₂).natAbs) (n : ℤ)
    have h1 := jacobiChar_intCast (m := D₁.natAbs) (n : ℤ)
    have h2 := jacobiChar_intCast (m := D₂.natAbs) (n : ℤ)
    push_cast at h h1 h2
    rw [h, h1, h2, Int.natAbs_mul, jacobiSym.mul_right]
    push_cast; ring
  · rw [kroneckerChar_apply_odd h₁₂ hn, kroneckerChar_apply_odd h₁ hn,
      kroneckerChar_apply_odd h₂ hn, jacobiSym.mul_left]
    push_cast; ring

end NTKB.Davenport
