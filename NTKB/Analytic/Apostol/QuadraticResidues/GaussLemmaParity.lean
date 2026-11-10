/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.NumberTheory.LegendreSymbol.GaussEisensteinLemmas
import NTKB.Attr

/-!
# The parity of Gauss' count (Apostol, Theorem 9.7)

Let `p` be an odd prime, `p ∤ n`, and `m` the number of least positive residues of
`n, 2n, …, ((p-1)/2) n` exceeding `p/2` (Gauss' lemma: `(n|p) = (-1)^m`). **Theorem 9.7**:
`m ≡ ∑_{t ≤ (p-1)/2} ⌊tn/p⌋ + (n - 1)(p² - 1)/8 (mod 2)`; for odd `n` this is Mathlib's
`ZMod.eisenstein_lemma_aux`.

The key congruence `ncongr` (`∑ n t ≡ m + ∑ t + ∑ ⌊nt/p⌋ (mod 2)`, Apostol's two sum
equations) is Mathlib's private `ZMod.eisenstein_lemma_aux₁`, reproduced here (same proof, from
`Mathlib/NumberTheory/LegendreSymbol/GaussEisensteinLemmas.lean`, Apache 2.0) since private
declarations cannot be used outside their file.
-/

open Finset Nat ZMod

namespace NTKB.Apostol

/-- Copy of Mathlib's private `ZMod.eisenstein_lemma_aux₁` (credit: Mathlib). -/
lemma ncongr (p : ℕ) [Fact p.Prime] [hp2 : Fact (p % 2 = 1)] {a : ℕ}
    (hap : (a : ZMod p) ≠ 0) :
    ((∑ x ∈ Ico 1 (p / 2).succ, a * x : ℕ) : ZMod 2) =
      #{x ∈ Ico 1 (p / 2).succ | p / 2 < (a * x.cast : ZMod p).val} +
        ∑ x ∈ Ico 1 (p / 2).succ, x + (∑ x ∈ Ico 1 (p / 2).succ, a * x / p : ℕ) :=
  have hp2 : (p : ZMod 2) = (1 : ℕ) := (natCast_eq_natCast_iff _ _ _).2 hp2.1
  calc
    ((∑ x ∈ Ico 1 (p / 2).succ, a * x : ℕ) : ZMod 2) =
        ((∑ x ∈ Ico 1 (p / 2).succ, (a * x % p + p * (a * x / p)) : ℕ) : ZMod 2) := by
      simp only [mod_add_div]
    _ = (∑ x ∈ Ico 1 (p / 2).succ, ((a * x : ℕ) : ZMod p).val : ℕ) +
        (∑ x ∈ Ico 1 (p / 2).succ, a * x / p : ℕ) := by
      simp only [val_natCast]
      simp [sum_add_distrib, ← mul_sum, Nat.cast_add, Nat.cast_mul, Nat.cast_sum, hp2]
    _ = _ :=
      congr_arg (· + _) <|
        calc
          ((∑ x ∈ Ico 1 (p / 2).succ, ((a * x : ℕ) : ZMod p).val : ℕ) : ZMod 2) =
              ∑ x ∈ Ico 1 (p / 2).succ, (((a * x : ZMod p).valMinAbs +
                if (a * x : ZMod p).val ≤ p / 2 then 0 else p : ℤ) : ZMod 2) := by
            simp only [(val_eq_ite_valMinAbs _).symm]; simp [Nat.cast_sum]
          _ = #{x ∈ Ico 1 (p / 2).succ | p / 2 < (a * x.cast : ZMod p).val} +
              (∑ x ∈ Ico 1 (p / 2).succ, (a * x.cast : ZMod p).valMinAbs.natAbs : ℕ) := by
            simp [add_comm, sum_add_distrib, Finset.sum_ite, hp2, Nat.cast_sum]
          _ = _ := by
            rw [Finset.sum_eq_multiset_sum, Ico_map_valMinAbs_natAbs_eq_Ico_map_id p a hap, ←
              Finset.sum_eq_multiset_sum]

lemma sum_Ico_one_mul_two (m : ℕ) : (∑ x ∈ Ico 1 (m + 1), x) * 2 = m * (m + 1) := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_Ico_succ_top (by omega), add_mul, ih]; ring

lemma sum_Ico_one_half (p : ℕ) (hp : p % 2 = 1) :
    ∑ x ∈ Ico 1 (p / 2).succ, x = (p ^ 2 - 1) / 8 := by
  obtain ⟨m, rfl⟩ : ∃ m, p = 2 * m + 1 := ⟨p / 2, by omega⟩
  have h2 : (2 * m + 1) / 2 = m := by omega
  rw [h2]
  have hs := sum_Ico_one_mul_two m
  set S := ∑ x ∈ Ico 1 (m + 1), x
  have : (2 * m + 1) ^ 2 = 8 * S + 1 := by nlinarith
  omega

/-- **Theorem 9.7**: with `m` the number of `t ≤ (p-1)/2` whose `t n` has least positive residue
exceeding `p/2`, `m ≡ ∑_{t ≤ (p-1)/2} ⌊tn/p⌋ + (n - 1)(p² - 1)/8 (mod 2)`. -/
@[kb "apostol1976" "Thm 9.7, p. 183"]
theorem gauss_count_modEq {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {n : ℕ} (hn : (n : ZMod p) ≠ 0) :
    #{x ∈ Ico 1 (p / 2).succ | p / 2 < (n * x.cast : ZMod p).val} ≡
      ∑ x ∈ Ico 1 (p / 2).succ, x * n / p + (n - 1) * ((p ^ 2 - 1) / 8) [MOD 2] := by
  have hodd : p % 2 = 1 := Nat.odd_iff.mp ((Fact.out : p.Prime).odd_of_ne_two hp)
  have : Fact (p % 2 = 1) := ⟨hodd⟩
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · simp at hn
    · exact h
  have key := ncongr p hn
  rw [← ZMod.natCast_eq_natCast_iff]
  rw [← sum_Ico_one_half p hodd]
  have e1 : ((∑ x ∈ Ico 1 (p / 2).succ, n * x : ℕ) : ZMod 2) =
      (n : ZMod 2) * ∑ x ∈ Ico 1 (p / 2).succ, (x : ZMod 2) := by
    push_cast; rw [Finset.mul_sum]
  have e2 : (∑ x ∈ Ico 1 (p / 2).succ, x * n / p : ℕ) = ∑ x ∈ Ico 1 (p / 2).succ, n * x / p := by
    refine Finset.sum_congr rfl fun x _ => by rw [mul_comm]
  rw [e1] at key
  rw [e2]
  push_cast [Nat.cast_sub hn1] at key ⊢
  have h2 : (2 : ZMod 2) = 0 := rfl
  linear_combination (-1 : ZMod 2) * key -
    (∑ x ∈ Ico 1 (p / 2).succ, ((n * x / p : ℕ) : ZMod 2)) * h2

end NTKB.Apostol
