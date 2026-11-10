/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.RingTheory.PowerSeries.Basic
import NTKB.Attr

/-!
# Power series of type `r` mod `q` (Apostol, §14, Exercise 13)

A power series `∑ aₙ xⁿ` is *of type `r` mod `q`* if `aₙ = 0` unless `n ≡ r (mod q)`
(Apostol writes it as `∑ a_n x^{nq + r}`). Types add under multiplication, and every power series
is the sum of its `q` components of types `0, 1, …, q-1`.
-/

open PowerSeries Finset

namespace NTKB.Apostol

variable {R : Type*} [CommSemiring R]

/-- A power series is of type `r` mod `q` if its `n`-th coefficient vanishes unless
`n ≡ r (mod q)`. -/
@[kb "apostol1976" "Exercise 14.13, p. 328"]
def IsOfTypeMod (f : PowerSeries R) (r q : ℕ) : Prop :=
  ∀ n, coeff n f ≠ 0 → n % q = r % q

lemma IsOfTypeMod.add {f g : PowerSeries R} {r q : ℕ} (hf : IsOfTypeMod f r q)
    (hg : IsOfTypeMod g r q) : IsOfTypeMod (f + g) r q := by
  intro n hn
  rw [map_add] at hn
  by_contra h
  exact hn (by rw [not_imp_comm.mp (hf n) h, not_imp_comm.mp (hg n) h, add_zero])

/-- The product of power series of types `r` and `r'` mod `q` is of type `r + r'` mod `q`. -/
@[kb "apostol1976" "Exercise 14.13, p. 328"]
lemma IsOfTypeMod.mul {f g : PowerSeries R} {r r' q : ℕ} (hf : IsOfTypeMod f r q)
    (hg : IsOfTypeMod g r' q) : IsOfTypeMod (f * g) (r + r') q := by
  intro n hn
  rw [coeff_mul] at hn
  obtain ⟨⟨i, j⟩, hij, hne⟩ := exists_ne_zero_of_sum_ne_zero hn
  rw [mem_antidiagonal] at hij
  have hi := hf i (left_ne_zero_of_mul hne)
  have hj := hg j (right_ne_zero_of_mul hne)
  rw [← hij, Nat.add_mod, hi, hj, ← Nat.add_mod]

/-- The component of type `r` mod `q` of a power series. -/
noncomputable def typeComponent (f : PowerSeries R) (r q : ℕ) : PowerSeries R :=
  mk fun n ↦ if n % q = r % q then coeff n f else 0

lemma isOfTypeMod_typeComponent (f : PowerSeries R) (r q : ℕ) :
    IsOfTypeMod (typeComponent f r q) r q := by
  intro n hn
  by_contra h
  exact hn (by simp [typeComponent, h])

/-- Every power series is the sum of its components of types `0, 1, …, q-1` mod `q`. -/
lemma sum_typeComponent (f : PowerSeries R) {q : ℕ} (hq : 0 < q) :
    ∑ r ∈ range q, typeComponent f r q = f := by
  ext n
  rw [map_sum]
  simp only [typeComponent, coeff_mk]
  rw [sum_eq_single (n % q)]
  · simp
  · intro r hr hne
    have : ¬ (n % q = r % q) := by
      rw [Nat.mod_eq_of_lt (mem_range.mp hr)]; exact fun h ↦ hne h.symm
    simp [this]
  · intro h
    exact absurd (mem_range.mpr (Nat.mod_lt n hq)) h

end NTKB.Apostol
