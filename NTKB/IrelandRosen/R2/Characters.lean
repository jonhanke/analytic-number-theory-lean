/-
Ireland–Rosen, Chapter 8, §1: multiplicative characters of a finite field and the number of
solutions of `x ^ n = a` (Propositions 8.1.4, 8.1.5, Exercises 8.1, 8.2).

The book works over `𝔽_p`; Chapter 10, §3 notes that everything carries over to an arbitrary
finite field `F` with `q` elements ("replace p by q"), and we state the results in that
generality.

Convention. The book extends the trivial character `ε` by `ε(0) = 1` (and every nontrivial
character by `χ(0) = 0`). Mathlib's `MulChar` has `(1 : MulChar F R) 0 = 0`. We write
`bookChar χ` for the character extended by the book's convention; it differs from `χ` only at
`0` and only for the trivial character.
-/
import Mathlib.NumberTheory.MulChar.Duality
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Analysis.Complex.Polynomial.Basic
import NTKB.Attr

open Finset
open scoped Classical

set_option linter.unusedSectionVars false

namespace NTKB.IrelandRosen

variable {F : Type*} [Field F] [Fintype F]
variable {R : Type*} [CommRing R]

/-- A multiplicative character extended by the convention of Ireland–Rosen (Chapter 8, §1):
the trivial character takes the value `1` at `0`, every other character the value `0`. -/
noncomputable def bookChar (χ : MulChar F R) (t : F) : R :=
  if χ = 1 then 1 else χ t

lemma bookChar_one (t : F) : bookChar (1 : MulChar F R) t = 1 := by
  simp [bookChar]

lemma bookChar_of_ne_one {χ : MulChar F R} (hχ : χ ≠ 1) (t : F) : bookChar χ t = χ t := by
  simp [bookChar, hχ]

lemma bookChar_of_ne_zero (χ : MulChar F R) {t : F} (ht : t ≠ 0) : bookChar χ t = χ t := by
  unfold bookChar
  split_ifs with h
  · subst h; exact (MulChar.one_apply (Ne.isUnit ht)).symm
  · rfl

lemma bookChar_zero_of_ne_one {χ : MulChar F R} (hχ : χ ≠ 1) : bookChar χ 0 = 0 := by
  rw [bookChar_of_ne_one hχ, MulChar.map_zero]

lemma bookChar_mul_of_ne_zero (χ : MulChar F R) {s : F} (hs : s ≠ 0) (t : F) :
    bookChar χ (s * t) = χ s * bookChar χ t := by
  unfold bookChar
  split_ifs with h
  · subst h; rw [MulChar.one_apply (Ne.isUnit hs), one_mul]
  · rw [map_mul]

/-- `ε(0)=1`, so the sum of the trivial character is `q` (Proposition 8.1.2 with the book's
convention); for nontrivial characters it is `0`. -/
@[kb "irelandrosen1990" "Prop 8.1.2, p. 100"]
theorem sum_bookChar [IsDomain R] (χ : MulChar F R) :
    ∑ t, bookChar χ t = if χ = 1 then (Fintype.card F : R) else 0 := by
  split_ifs with h
  · subst h; simp [bookChar_one]
  · simp only [bookChar_of_ne_one h]; exact MulChar.sum_eq_zero_of_ne_one h

noncomputable instance : Fintype (MulChar F ℂ) := .ofFinite _

/-- Orthogonality over characters (corollary to Proposition 8.1.3): the sum of `χ a` over all
characters `χ` is `q - 1` if `a = 1` and `0` otherwise. -/
theorem sum_characters_eq (a : F) :
    ∑ χ : MulChar F ℂ, χ a = if a = 1 then (Fintype.card F - 1 : ℂ) else 0 := by
  split_ifs with ha
  · subst ha
    simp only [map_one, sum_const, card_univ, nsmul_eq_mul, mul_one]
    have := MulChar.card_eq_card_units_of_hasEnoughRootsOfUnity F ℂ
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_units] at this
    rw [this, Nat.cast_sub Fintype.card_pos, Nat.cast_one]
  · obtain ⟨χ, hχ⟩ := MulChar.exists_apply_ne_one_of_hasEnoughRootsOfUnity F ℂ ha
    refine eq_zero_of_mul_eq_self_left hχ ?_
    simp only [Finset.mul_sum, ← MulChar.mul_apply]
    exact Fintype.sum_bijective _ (Group.mulLeft_bijective χ) _ _ fun χ' ↦ rfl

/-- The number of solutions of `x ^ n = a` in `F`. -/
noncomputable def numSolPow (n : ℕ) (a : F) : ℕ := #{x : F | x ^ n = a}

/-- **Counting solutions of `x ^ n = a` by characters** (for every `n ≥ 1`):
`N(x^n = a) = ∑_{χ^n = ε} χ(a)`. This is Exercise 8.1 in the form needed for Proposition 8.1.5;
no divisibility hypothesis on `n` is needed. -/
theorem numSolPow_eq_sum {n : ℕ} (hn : n ≠ 0) (a : F) :
    (numSolPow n a : ℂ) = ∑ χ : MulChar F ℂ with χ ^ n = 1, bookChar χ a := by
  by_cases ha : a = 0
  · subst ha
    have h1 : numSolPow n (0 : F) = 1 := by
      unfold numSolPow
      rw [Finset.card_eq_one]
      exact ⟨0, by ext x; simp [pow_eq_zero_iff hn]⟩
    rw [h1, Finset.sum_eq_single_of_mem (1 : MulChar F ℂ) (by simp)]
    · simp [bookChar_one]
    · intro χ _ hχ; exact bookChar_zero_of_ne_one hχ
  · -- `(q - 1) N = ∑_{x ≠ 0} ∑_χ χ(x^n a⁻¹) = ∑_χ χ(a⁻¹) ∑_x χ^n(x)`.
    have hq : (Fintype.card F - 1 : ℂ) ≠ 0 := by
      rw [sub_ne_zero]; exact_mod_cast (Fintype.one_lt_card).ne'
    apply mul_left_cancel₀ hq
    have key : ∀ x : F, (if x ^ n = a then (Fintype.card F - 1 : ℂ) else 0) =
        ∑ χ : MulChar F ℂ, χ a⁻¹ * (χ ^ n) x := by
      intro x
      by_cases hx : x = 0
      · subst hx
        simp only [ne_eq, hn, not_false_eq_true, zero_pow, MulChar.map_zero, mul_zero,
          sum_const_zero, ite_eq_right_iff]
        intro h; exact absurd h.symm ha
      · simp_rw [MulChar.pow_apply' _ hn, ← map_pow, ← map_mul, sum_characters_eq]
        congr 1
        apply propext
        constructor
        · intro h; rw [h, inv_mul_cancel₀ ha]
        · intro h; field_simp at h; exact h
    calc (Fintype.card F - 1 : ℂ) * numSolPow n a
        = ∑ x : F, (if x ^ n = a then (Fintype.card F - 1 : ℂ) else 0) := by
          rw [Finset.sum_ite, sum_const_zero, add_zero, sum_const, nsmul_eq_mul, mul_comm]
          rfl
      _ = ∑ χ : MulChar F ℂ, χ a⁻¹ * ∑ x, (χ ^ n) x := by
          simp_rw [key, Finset.mul_sum]; exact Finset.sum_comm
      _ = ∑ χ : MulChar F ℂ with χ ^ n = 1, χ a⁻¹ * (Fintype.card F - 1 : ℂ) := by
          rw [Finset.sum_filter]
          refine Finset.sum_congr rfl fun χ _ => ?_
          split_ifs with h
          · rw [h, MulChar.sum_one_eq_card_units, Fintype.card_units, Nat.cast_sub
              Fintype.card_pos, Nat.cast_one]
          · rw [MulChar.sum_eq_zero_of_ne_one h, mul_zero]
      _ = (Fintype.card F - 1 : ℂ) * ∑ χ : MulChar F ℂ with χ ^ n = 1, bookChar χ a := by
          rw [Finset.mul_sum]
          refine Finset.sum_nbij' (fun χ => χ⁻¹) (fun χ => χ⁻¹) ?_ ?_ ?_ ?_ ?_
          · intro χ hχ; simp only [mem_filter, mem_univ, true_and] at hχ ⊢; rw [inv_pow, hχ, inv_one]
          · intro χ hχ; simp only [mem_filter, mem_univ, true_and] at hχ ⊢; rw [inv_pow, hχ, inv_one]
          · intro χ _; simp
          · intro χ _; simp
          · intro χ _
            rw [bookChar_of_ne_zero _ ha, MulChar.inv_apply', mul_comm]

/-- **Proposition 8.1.5.** If `n ∣ q - 1`, then `N(x^n = a) = ∑ χ(a)`, the sum over all characters
`χ` of order dividing `n`. -/
@[kb "irelandrosen1990" "Prop 8.1.5, p. 101"]
theorem numSolPow_eq_sum_of_dvd {n : ℕ} (hn : n ∣ Fintype.card F - 1) (a : F) :
    (numSolPow n a : ℂ) = ∑ χ : MulChar F ℂ with χ ^ n = 1, bookChar χ a := by
  refine numSolPow_eq_sum ?_ a
  rintro rfl
  rw [zero_dvd_iff, Nat.sub_eq_zero_iff_le] at hn
  exact absurd hn (not_le.mpr Fintype.one_lt_card)

lemma pow_eq_one_iff_pow_gcd_eq_one (χ : MulChar F ℂ) (m : ℕ) :
    χ ^ m = 1 ↔ χ ^ Nat.gcd m (Fintype.card F - 1) = 1 := by
  have hq : χ ^ (Fintype.card F - 1) = 1 := by
    rw [← Fintype.card_units]; exact MulChar.pow_card_eq_one χ
  constructor
  · intro h; exact pow_gcd_eq_one.mpr ⟨h, hq⟩
  · intro h
    obtain ⟨k, hk⟩ := Nat.gcd_dvd_left m (Fintype.card F - 1)
    rw [hk, pow_mul, h, one_pow]

/-- **Exercise 8.1.** With `d = gcd(m, q - 1)`, `N(x^m = a) = ∑_{χ^d = ε} χ(a)`. -/
@[kb "irelandrosen1990" "Exercise 8.1, p. 116"]
theorem numSolPow_eq_sum_gcd {m : ℕ} (hm : m ≠ 0) (a : F) :
    (numSolPow m a : ℂ) =
      ∑ χ : MulChar F ℂ with χ ^ Nat.gcd m (Fintype.card F - 1) = 1, bookChar χ a := by
  rw [numSolPow_eq_sum hm]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext χ
  simp only [mem_filter, mem_univ, true_and]
  exact pow_eq_one_iff_pow_gcd_eq_one χ m

/-- **Exercise 8.2.** With `d = gcd(m, q - 1)`, `N(x^m = a) = N(x^d = a)`. -/
@[kb "irelandrosen1990" "Exercise 8.2, p. 116"]
theorem numSolPow_eq_numSolPow_gcd {m : ℕ} (hm : m ≠ 0) (a : F) :
    numSolPow m a = numSolPow (Nat.gcd m (Fintype.card F - 1)) a := by
  have hd : Nat.gcd m (Fintype.card F - 1) ≠ 0 := Nat.gcd_ne_zero_left hm
  have h := (numSolPow_eq_sum_gcd hm a).trans (numSolPow_eq_sum hd a).symm
  exact_mod_cast h

/-- **Proposition 8.1.4.** If `n ∣ q - 1` and `x ^ n = a` has no solution (`a ≠ 0`), then there is
a character `χ` with `χ ^ n = ε` and `χ(a) ≠ 1`. -/
@[kb "irelandrosen1990" "Prop 8.1.4, p. 101"]
theorem exists_pow_eq_one_apply_ne_one {n : ℕ} (hn : n ∣ Fintype.card F - 1) {a : F}
    (ha : a ≠ 0) (hsol : ∀ x : F, x ^ n ≠ a) :
    ∃ χ : MulChar F ℂ, χ ^ n = 1 ∧ χ a ≠ 1 := by
  by_contra! hall
  have h := numSolPow_eq_sum_of_dvd hn a
  have h0 : numSolPow n a = 0 := by
    unfold numSolPow; rw [Finset.card_eq_zero]; ext x; simp [hsol x]
  rw [h0, Nat.cast_zero, Finset.sum_congr rfl (g := fun _ => (1 : ℂ))] at h
  · rw [sum_const, nsmul_eq_mul, mul_one] at h
    have : (1 : MulChar F ℂ) ∈ ({χ : MulChar F ℂ | χ ^ n = 1} : Finset _) := by simp
    have hpos := Finset.card_pos.mpr ⟨_, this⟩
    exact absurd h.symm (by exact_mod_cast hpos.ne')
  · intro χ hχ
    rw [bookChar_of_ne_zero _ ha]
    exact hall χ (by simpa using hχ)

/-- The characters of order dividing `n` number `N(x^n = 1)`. -/
lemma card_pow_eq_one_eq {n : ℕ} (hn : n ≠ 0) :
    #{χ : MulChar F ℂ | χ ^ n = 1} = numSolPow n (1 : F) := by
  have h := numSolPow_eq_sum hn (1 : F)
  rw [Finset.sum_congr rfl (g := fun _ => (1 : ℂ))] at h
  · rw [sum_const, nsmul_eq_mul, mul_one] at h; exact_mod_cast h.symm
  · intro χ _; rw [bookChar_of_ne_zero _ one_ne_zero, map_one]

lemma numSolPow_one_le {n : ℕ} (hn : n ≠ 0) : numSolPow n (1 : F) ≤ n := by
  unfold numSolPow
  have := IsCyclic.card_pow_eq_one_le (α := Fˣ) (Nat.pos_of_ne_zero hn)
  have himg : ({x : F | x ^ n = 1} : Finset F) =
      ({u : Fˣ | u ^ n = 1} : Finset Fˣ).image (fun u : Fˣ => (u : F)) := by
    ext x
    simp only [mem_filter, mem_univ, true_and, mem_image]
    constructor
    · intro hx
      have hx0 : x ≠ 0 := by rintro rfl; simp [hn] at hx
      exact ⟨Units.mk0 x hx0, by ext; simp [hx], rfl⟩
    · rintro ⟨u, hu, rfl⟩
      rw [← Units.val_pow_eq_pow_val, hu, Units.val_one]
  rw [himg]
  exact (card_image_le).trans this

/-- If `n ∣ q - 1` there is a character of order exactly `n`. -/
theorem exists_orderOf_eq {n : ℕ} (hn : n ∣ Fintype.card F - 1) :
    ∃ χ : MulChar F ℂ, orderOf χ = n := by
  obtain ⟨e⟩ := MulChar.mulEquiv_units F ℂ
  have hcyc : IsCyclic (MulChar F ℂ) := isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective
  have hcard : Nat.card (MulChar F ℂ) = Fintype.card F - 1 := by
    rw [MulChar.card_eq_card_units_of_hasEnoughRootsOfUnity, Nat.card_eq_fintype_card,
      Fintype.card_units]
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := MulChar F ℂ)
  obtain ⟨k, hk⟩ := hn
  refine ⟨g ^ k, ?_⟩
  have hpos : 0 < Fintype.card F - 1 := Nat.sub_pos_of_lt Fintype.one_lt_card
  rw [orderOf_pow' g (by rintro rfl; simp at hk; omega), hg, hcard, hk]
  have hk0 : k ≠ 0 := by rintro rfl; simp at hk; omega
  rw [Nat.gcd_mul_left_left, Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hk0)]

/-- If `χ` has order `n` with `n ∣ q - 1`, the characters of order dividing `n` are exactly
`ε, χ, …, χ^{n-1}`, and there are `n` of them. -/
theorem filter_pow_eq_one_eq_image {n : ℕ} (hn : n ∣ Fintype.card F - 1) {χ : MulChar F ℂ}
    (hχ : orderOf χ = n) :
    ({ψ : MulChar F ℂ | ψ ^ n = 1} : Finset _) = (range n).image (χ ^ ·) ∧
      Set.InjOn (χ ^ ·) (range n : Set ℕ) := by
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [zero_dvd_iff, Nat.sub_eq_zero_iff_le] at hn
    exact absurd hn (not_le.mpr Fintype.one_lt_card)
  have hinj : Set.InjOn (χ ^ ·) (range n : Set ℕ) := by
    intro i hi j hj hij
    simp only [coe_range, Set.mem_Iio] at hi hj
    exact pow_injOn_Iio_orderOf (by rw [hχ]; exact hi) (by rw [hχ]; exact hj) hij
  refine ⟨?_, hinj⟩
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro ψ hψ
    simp only [mem_image, mem_range] at hψ
    obtain ⟨i, _, rfl⟩ := hψ
    simp only [mem_filter, mem_univ, true_and]
    rw [← pow_mul, mul_comm, pow_mul, ← hχ, pow_orderOf_eq_one, one_pow]
  · rw [card_pow_eq_one_eq hn0, card_image_of_injOn hinj, card_range]
    exact numSolPow_one_le hn0

/-- **Proposition 8.1.5, in the form `∑_{i<n} χ^i(a)`.** If `χ` has order `n` with `n ∣ q - 1`,
then `N(x^n = a) = ∑_{i=0}^{n-1} χ^i(a)`. -/
@[kb "irelandrosen1990" "Prop 8.1.5, p. 101"]
theorem numSolPow_eq_sum_range {n : ℕ} (hn : n ∣ Fintype.card F - 1) {χ : MulChar F ℂ}
    (hχ : orderOf χ = n) (a : F) :
    (numSolPow n a : ℂ) = ∑ i ∈ range n, bookChar (χ ^ i) a := by
  obtain ⟨h1, h2⟩ := filter_pow_eq_one_eq_image hn hχ
  rw [numSolPow_eq_sum_of_dvd hn, h1, sum_image h2]

end NTKB.IrelandRosen
