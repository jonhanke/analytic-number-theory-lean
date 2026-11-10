/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Apostol.Averages.Visible
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.NumberTheory.PrimeCounting

/-!
# Square gaps among visible lattice points (Apostol, Chapter 5, §5.8, Theorem 5.29)

**Theorem 5.29.** The set of lattice points visible from the origin contains arbitrarily large
square gaps: for every `k > 0` there is a lattice point `(a, b)` such that none of the points
`(a + r, b + s)`, `0 < r, s ≤ k`, is visible from the origin.

Apostol's proof: choose `k²` distinct primes `p_{rs}`; by the Chinese remainder theorem pick `a`
with `a ≡ -r (mod ∏_s p_{rs})` and `b` with `b ≡ -s (mod ∏_r p_{rs})`; then
`p_{rs} ∣ gcd(a + r, b + s)`, so `(a + r, b + s)` is not visible (Theorem 3.8).
-/

open Finset
open scoped Function

namespace NTKB.Apostol

/-- `k²` distinct primes `p(r, s)`, `r, s < k`. -/
noncomputable def gridPrime (k : ℕ) (r s : Fin k) : ℕ := Nat.nth Nat.Prime (r * k + s)

theorem gridPrime_prime (k : ℕ) (r s : Fin k) : (gridPrime k r s).Prime := Nat.prime_nth_prime _

theorem gridPrime_injective (k : ℕ) {r s r' s' : Fin k}
    (h : gridPrime k r s = gridPrime k r' s') : r = r' ∧ s = s' := by
  have := Nat.nth_injective Nat.infinite_setOf_prime h
  have hr := r.2; have hs := s.2; have hr' := r'.2; have hs' := s'.2
  have e1 : (r : ℕ) = r' := by
    have := congrArg (· / k) this
    rwa [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hs, zero_add,
      Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hs', zero_add] at this
  have e2 : (s : ℕ) = s' := by rw [e1] at this; omega
  exact ⟨Fin.ext e1, Fin.ext e2⟩

theorem coprime_prod_gridPrime_rows (k : ℕ) {r r' : Fin k} (h : r ≠ r') :
    (∏ s, gridPrime k r s).Coprime (∏ s, gridPrime k r' s) := by
  refine Nat.Coprime.prod_left fun s _ ↦ Nat.Coprime.prod_right fun s' _ ↦ ?_
  rw [Nat.coprime_primes (gridPrime_prime _ _ _) (gridPrime_prime _ _ _)]
  intro he
  exact h (gridPrime_injective k he).1

theorem coprime_prod_gridPrime_cols (k : ℕ) {s s' : Fin k} (h : s ≠ s') :
    (∏ r, gridPrime k r s).Coprime (∏ r, gridPrime k r s') := by
  refine Nat.Coprime.prod_left fun r _ ↦ Nat.Coprime.prod_right fun r' _ ↦ ?_
  rw [Nat.coprime_primes (gridPrime_prime _ _ _) (gridPrime_prime _ _ _)]
  intro he
  exact h (gridPrime_injective k he).2

/-- Chinese remainder: for pairwise coprime `m i` and targets `c i`, there is `x : ℕ` with
`m i ∣ x + c i` for every `i`. -/
theorem exists_nat_dvd_add {ι : Type*} [Fintype ι] (m : ι → ℕ) (hm : Pairwise (Nat.Coprime on m))
    (hm0 : ∀ i, m i ≠ 0) (c : ι → ℕ) : ∃ x : ℕ, ∀ i, m i ∣ x + c i := by
  have : NeZero (∏ i, m i) := ⟨Finset.prod_ne_zero_iff.2 fun i _ ↦ hm0 i⟩
  set e := ZMod.prodEquivPi m hm
  set y := e.symm fun i ↦ -(c i : ZMod (m i))
  refine ⟨y.val, fun i ↦ ?_⟩
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, ZMod.natCast_val]
  have h1 : (ZMod.cast y : ZMod (m i)) = e y i := by
    rw [ZMod.prodEquivPi_apply]; rfl
  rw [h1]
  simp [y]

/-- **Apostol, Theorem 5.29.** For every `k` there is a lattice point `(a, b)` such that no point
`(a + r, b + s)` with `0 < r, s ≤ k` is visible from the origin. -/
@[kb "apostol1976" "Thm 5.29, p. 119"]
theorem exists_square_gap_not_visible (k : ℕ) :
    ∃ a b : ℤ, ∀ r s : ℕ, 0 < r → r ≤ k → 0 < s → s ≤ k →
      ¬ MutuallyVisible (0, 0) (a + r, b + s) := by
  set p := gridPrime k
  have hp0 : ∀ r s, p r s ≠ 0 := fun r s ↦ (gridPrime_prime k r s).ne_zero
  -- `a ≡ -(r+1) (mod ∏_s p(r,s))`, `b ≡ -(s+1) (mod ∏_r p(r,s))`
  obtain ⟨a, ha⟩ := exists_nat_dvd_add (fun r : Fin k ↦ ∏ s, p r s)
    (fun _ _ h ↦ coprime_prod_gridPrime_rows k h)
    (fun r ↦ Finset.prod_ne_zero_iff.2 fun s _ ↦ hp0 r s) (fun r ↦ r + 1)
  obtain ⟨b, hb⟩ := exists_nat_dvd_add (fun s : Fin k ↦ ∏ r, p r s)
    (fun _ _ h ↦ coprime_prod_gridPrime_cols k h)
    (fun s ↦ Finset.prod_ne_zero_iff.2 fun r _ ↦ hp0 r s) (fun s ↦ s + 1)
  refine ⟨a, b, fun r s hr hrk hs hsk hvis ↦ ?_⟩
  rw [mutuallyVisible_iff_gcd_eq_one] at hvis
  set r' : Fin k := ⟨r - 1, by omega⟩
  set s' : Fin k := ⟨s - 1, by omega⟩
  have h1 : p r' s' ∣ a + r := by
    have := (Finset.dvd_prod_of_mem (fun s ↦ p r' s) (mem_univ s')).trans (ha r')
    simp only [r'] at this
    rwa [show r - 1 + 1 = r by omega] at this
  have h2 : p r' s' ∣ b + s := by
    have := (Finset.dvd_prod_of_mem (fun r ↦ p r s') (mem_univ r')).trans (hb s')
    simp only [s'] at this
    rwa [show s - 1 + 1 = s by omega] at this
  have hgcd : Int.gcd (0 - ((a : ℤ) + r)) (0 - ((b : ℤ) + s)) = Nat.gcd (a + r) (b + s) := by
    rw [show (0 : ℤ) - ((a : ℤ) + r) = -(((a + r : ℕ) : ℤ)) by push_cast; ring,
      show (0 : ℤ) - ((b : ℤ) + s) = -(((b + s : ℕ) : ℤ)) by push_cast; ring]
    simp only [Int.neg_gcd, Int.gcd_neg, Int.gcd_natCast_natCast]
  rw [hgcd] at hvis
  have hd := Nat.dvd_gcd h1 h2
  rw [hvis] at hd
  exact (gridPrime_prime k r' s').one_lt.ne' (Nat.dvd_one.1 hd)

end NTKB.Apostol
