/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Algebra.Order.Group.Unbundled.Int
import Mathlib.Data.Int.Order.Lemmas
import Mathlib.Tactic.Ring
import Mathlib.Data.Nat.GCD.Basic
import NTKB.Attr

/-!
# The division algorithm and the subgroup criterion (Apostol, Theorems 1.14, 6.4)

* **Theorem 1.14** (division algorithm): for `b > 0` there are unique `q, r` with `a = bq + r`,
  `0 ≤ r < b`; and `r = 0` iff `b ∣ a`.
* **Theorem 1.15** (Euclidean algorithm): the remainder sequence `r₀ = a`, `r₁ = b`,
  `r_{i+1} = r_{i-1} mod r_i` reaches `0`, and the last nonzero remainder is `(a, b)`
  (`euclidPair`, `euclid_terminates`).
* **Theorem 6.4**: a nonempty subset of a group closed under products and inverses is a
  subgroup (`subgroupOfClosed`, with carrier the given set).
-/

namespace NTKB.Apostol

/-- **Theorem 1.14** (division algorithm). -/
@[kb "apostol1976" "Thm 1.14, p. 19"]
theorem division_algorithm (a : ℤ) {b : ℤ} (hb : 0 < b) :
    (∃! qr : ℤ × ℤ, a = b * qr.1 + qr.2 ∧ 0 ≤ qr.2 ∧ qr.2 < b) ∧ (a % b = 0 ↔ b ∣ a) := by
  refine ⟨⟨(a / b, a % b), ⟨(Int.mul_ediv_add_emod a b).symm, Int.emod_nonneg _ hb.ne',
    Int.emod_lt_of_pos _ hb⟩, ?_⟩, Int.dvd_iff_emod_eq_zero.symm⟩
  rintro ⟨q, r⟩ ⟨h1, h2, h3⟩
  simp only at h1 h2 h3
  have hq : q = a / b := by
    rw [h1, show b * q + r = r + q * b by ring, Int.add_mul_ediv_right _ _ hb.ne',
      Int.ediv_eq_zero_of_lt h2 h3, zero_add]
  have hr : r = a % b := by
    rw [h1, show b * q + r = r + q * b by ring, Int.add_mul_emod_self_right,
      Int.emod_eq_of_lt h2 h3]
  rw [hq, hr]

/-- **Theorem 6.4**: a nonempty subset `S` of a group closed under products and inverses is a
subgroup (with carrier `S`). -/
@[kb "apostol1976" "Thm 6.4, p. 131"]
def subgroupOfClosed {G : Type*} [Group G] (S : Set G) (hne : S.Nonempty)
    (hmul : ∀ a ∈ S, ∀ b ∈ S, a * b ∈ S) (hinv : ∀ a ∈ S, a⁻¹ ∈ S) : Subgroup G where
  carrier := S
  mul_mem' := fun ha hb => hmul _ ha _ hb
  one_mem' := by
    obtain ⟨a, ha⟩ := hne
    simpa using hmul a ha a⁻¹ (hinv a ha)
  inv_mem' := fun ha => hinv _ ha

/-- The pairs `(r_i, r_{i+1})` of the Euclidean algorithm started at `(a, b)`. -/
def euclidPair (a b : ℕ) : ℕ → ℕ × ℕ
  | 0 => (a, b)
  | i + 1 => ((euclidPair a b i).2, (euclidPair a b i).1 % (euclidPair a b i).2)

lemma gcd_euclidPair (a b i : ℕ) :
    Nat.gcd (euclidPair a b i).1 (euclidPair a b i).2 = Nat.gcd a b := by
  induction i with
  | zero => rfl
  | succ i ih =>
    simp only [euclidPair]
    rw [Nat.gcd_comm, ← Nat.gcd_rec, Nat.gcd_comm, ih]

lemma euclidPair_snd_lt (a b i : ℕ) (h : (euclidPair a b i).2 ≠ 0) :
    (euclidPair a b (i + 1)).2 < (euclidPair a b i).2 := by
  simp only [euclidPair]
  exact Nat.mod_lt _ (Nat.pos_of_ne_zero h)

/-- **Theorem 1.15** (Euclidean algorithm): after at most `b + 1` steps the remainder is `0`, and
then the last nonzero remainder `r_n` is `(a, b)`. -/
@[kb "apostol1976" "Thm 1.15, p. 20"]
theorem euclid_terminates (a b : ℕ) :
    ∃ n ≤ b, (euclidPair a b n).2 = 0 ∧ (euclidPair a b n).1 = Nat.gcd a b := by
  have hdec : ∀ i, (euclidPair a b i).2 + i ≤ b ∨ ∃ j ≤ i, (euclidPair a b j).2 = 0 := by
    intro i
    induction i with
    | zero => left; simp [euclidPair]
    | succ i ih =>
      rcases ih with h | ⟨j, hj, hj0⟩
      · by_cases h0 : (euclidPair a b i).2 = 0
        · right; exact ⟨i, by omega, h0⟩
        · left; have := euclidPair_snd_lt a b i h0; omega
      · right; exact ⟨j, by omega, hj0⟩
  obtain ⟨n, hn, hn0⟩ : ∃ n ≤ b, (euclidPair a b n).2 = 0 := by
    rcases hdec b with h | ⟨j, hj, hj0⟩
    · exact ⟨b, le_rfl, by omega⟩
    · exact ⟨j, hj, hj0⟩
  refine ⟨n, hn, hn0, ?_⟩
  have := gcd_euclidPair a b n
  rwa [hn0, Nat.gcd_zero_right] at this

end NTKB.Apostol
