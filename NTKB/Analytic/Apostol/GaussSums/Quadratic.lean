/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import NTKB.Attr

/-!
# Quadratic Gauss sums (Apostol, Exercise 8.16)

`G(k; n) = ∑_{r=1}^{n} e^{2πi k r²/n}` (`quadGaussSum`).
Exercise 8.16 (a): `G(k; mn) = G(km; n) G(kn; m)` for `(m, n) = 1` (`quadGaussSum_mul`).
-/

open Complex Finset
open scoped Real

namespace NTKB.Apostol

/-- The quadratic Gauss sum `G(k; n) = ∑_{r=1}^{n} e^{2πi k r²/n}` (Apostol, Exercise 8.16). -/
noncomputable def quadGaussSum (k : ℤ) (n : ℕ) : ℂ :=
  ∑ r ∈ Icc 1 n, exp (2 * π * I * k * (r : ℂ) ^ 2 / n)

lemma sum_Icc_one_eq_sum_range {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ)
    (h : f n = f 0) : ∑ r ∈ Icc 1 n, f r = ∑ r ∈ range n, f r := by
  have h1 : ∑ r ∈ Icc 1 n, f r = ∑ r ∈ range n, f (r + 1) := by
    rw [show Icc 1 n = Ico 1 (n + 1) by ext; simp, sum_Ico_eq_sum_range]
    simp [add_comm]
  rw [h1]
  cases n with
  | zero => simp
  | succ n =>
    rw [sum_range_succ, sum_range_succ', h]

/-- The summand only depends on `r` modulo `n`. -/
lemma quadGaussSum_eq_sum_range (k : ℤ) (n : ℕ) :
    quadGaussSum k n = ∑ r ∈ range n, exp (2 * π * I * k * (r : ℂ) ^ 2 / n) := by
  unfold quadGaussSum
  apply sum_Icc_one_eq_sum_range
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have : 2 * π * I * k * (n : ℂ) ^ 2 / n = (k * n : ℤ) * (2 * π * I) := by
    push_cast; field_simp
  rw [this, exp_int_mul_two_pi_mul_I]
  simp

/-- `G(k; n)` as a sum over `ZMod n` of the standard additive character. -/
lemma quadGaussSum_eq_sum_zmod (k : ℤ) (n : ℕ) [NeZero n] :
    quadGaussSum k n = ∑ x : ZMod n, ZMod.stdAddChar ((k : ZMod n) * x ^ 2) := by
  rw [quadGaussSum_eq_sum_range]
  refine sum_nbij' (fun r => (r : ZMod n)) (fun x => x.val) (by simp) (fun x _ => by
    simpa using ZMod.val_lt x) (fun r hr => ?_) (fun x _ => by simp) (fun r _ => ?_)
  · rw [ZMod.val_natCast, Nat.mod_eq_of_lt (mem_range.mp hr)]
  · have : ((k : ZMod n) * (r : ZMod n) ^ 2) = ((k * (r : ℤ) ^ 2 : ℤ) : ZMod n) := by
      push_cast; rfl
    rw [this, ZMod.stdAddChar_coe]
    push_cast
    ring_nf

lemma stdAddChar_mul_cast (m n : ℕ) [NeZero m] [NeZero n] (j : ℤ) :
    ZMod.stdAddChar (((n : ℤ) * j : ℤ) : ZMod (m * n)) = ZMod.stdAddChar (j : ZMod m) := by
  have : NeZero (m * n) := ⟨Nat.mul_ne_zero (NeZero.ne m) (NeZero.ne n)⟩
  rw [ZMod.stdAddChar_coe, ZMod.stdAddChar_coe]
  have hm : (m : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne m
  have hn : (n : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne n
  congr 1
  push_cast
  field_simp

lemma stdAddChar_mul_cast' (m n : ℕ) [NeZero m] [NeZero n] (j : ℤ) :
    ZMod.stdAddChar (((m : ℤ) * j : ℤ) : ZMod (m * n)) = ZMod.stdAddChar (j : ZMod n) := by
  have : NeZero (m * n) := ⟨Nat.mul_ne_zero (NeZero.ne m) (NeZero.ne n)⟩
  rw [ZMod.stdAddChar_coe, ZMod.stdAddChar_coe]
  have hm : (m : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne m
  have hn : (n : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne n
  congr 1
  push_cast
  field_simp

/-- **Exercise 8.16 (a)**: `G(k; mn) = G(km; n) G(kn; m)` whenever `(m, n) = 1`. -/
@[kb "apostol1976" "Exercise 8.16(a), p. 177"]
theorem quadGaussSum_mul (k : ℤ) {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hmn : m.Coprime n) :
    quadGaussSum k (m * n) = quadGaussSum (k * m) n * quadGaussSum (k * n) m := by
  have : NeZero m := ⟨hm.ne'⟩
  have : NeZero n := ⟨hn.ne'⟩
  have : NeZero (m * n) := ⟨Nat.mul_ne_zero hm.ne' hn.ne'⟩
  -- the map `(s, t) ↦ n s + m t` from `ZMod m × ZMod n` to `ZMod (mn)`
  let φ : ZMod m × ZMod n → ZMod (m * n) := fun p =>
    (((n : ℤ) * (p.1.val : ℤ) + (m : ℤ) * (p.2.val : ℤ) : ℤ) : ZMod (m * n))
  have hφ : Function.Injective φ := by
    rintro ⟨s, t⟩ ⟨s', t'⟩ h
    simp only [φ] at h
    have h1 := congrArg (ZMod.castHom (dvd_mul_right m n) (ZMod m)) h
    have h2 := congrArg (ZMod.castHom (dvd_mul_left n m) (ZMod n)) h
    simp only [map_intCast] at h1 h2
    push_cast at h1 h2
    simp only [ZMod.natCast_self, ZMod.natCast_val, ZMod.cast_id', id, zero_mul, add_zero,
      zero_add] at h1 h2
    have u1 : IsUnit (n : ZMod m) := (ZMod.isUnit_iff_coprime n m).mpr hmn.symm
    have u2 : IsUnit (m : ZMod n) := (ZMod.isUnit_iff_coprime m n).mpr hmn
    rw [u1.mul_right_inj] at h1
    rw [u2.mul_right_inj] at h2
    rw [h1, h2]
  have hbij : Function.Bijective φ := by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨hφ, by simp [ZMod.card]⟩
  rw [quadGaussSum_eq_sum_zmod, quadGaussSum_eq_sum_zmod, quadGaussSum_eq_sum_zmod,
    ← Fintype.sum_bijective φ hbij _ _ (fun _ => rfl), Fintype.sum_prod_type]
  conv_rhs => rw [mul_comm, sum_mul_sum]
  refine sum_congr rfl fun s _ => sum_congr rfl fun t _ => ?_
  simp only [φ]
  set a : ℤ := (s.val : ℤ)
  set b : ℤ := (t.val : ℤ)
  have hs : (s : ZMod m) = (a : ZMod m) := by simp [a]
  have ht : (t : ZMod n) = (b : ZMod n) := by simp [b]
  have e1 : ((k : ZMod (m * n)) * (((n : ℤ) * a + m * b : ℤ) : ZMod (m * n)) ^ 2) =
      (((n : ℤ) * (k * n * a ^ 2) : ℤ) : ZMod (m * n)) +
      (((m : ℤ) * (k * m * b ^ 2) : ℤ) : ZMod (m * n)) +
      (((m * n : ℕ) : ℤ) * (2 * k * a * b) : ℤ) := by
    push_cast; ring
  have e2 : ((((m * n : ℕ) : ℤ) * (2 * k * a * b) : ℤ) : ZMod (m * n)) = 0 := by
    rw [Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, zero_mul]
  rw [e1, e2, add_zero, AddChar.map_add_eq_mul, stdAddChar_mul_cast, stdAddChar_mul_cast', hs, ht]
  push_cast
  ring_nf

/-! ### Exercise 8.16 (b) -/

lemma sum_range_mul_eq {M : Type*} [AddCommMonoid M] (f : ℕ → M) (m n : ℕ) :
    ∑ r ∈ range (m * n), f r = ∑ i ∈ range m, ∑ j ∈ range n, f (j + n * i) := by
  rw [← Fin.sum_univ_eq_sum_range, ← finProdFinEquiv.sum_comp, Fintype.sum_prod_type,
    ← Fin.sum_univ_eq_sum_range (fun i => ∑ j ∈ range n, f (j + n * i))]
  refine Fintype.sum_congr _ _ fun i => ?_
  rw [← Fin.sum_univ_eq_sum_range (fun j => f (j + n * i))]
  rfl

/-- `∑_{v < p} e^{2πi c v/p}` is `p` if `p ∣ c` and `0` otherwise. -/
lemma sum_range_exp_mul (p : ℕ) [NeZero p] (c : ℤ) :
    ∑ v ∈ range p, exp (2 * π * I * c * (v : ℂ) / p) = if (c : ZMod p) = 0 then (p : ℂ) else 0 := by
  have h := AddChar.sum_mulShift (c : ZMod p) (ZMod.isPrimitive_stdAddChar p)
  rw [ZMod.card] at h
  have h' : ∑ x : ZMod p, ZMod.stdAddChar (x * (c : ZMod p)) =
      if (c : ZMod p) = 0 then (p : ℂ) else 0 := by
    rw [h]; split_ifs <;> simp
  rw [← h']
  refine (sum_nbij' (fun r => (r : ZMod p)) (fun x => x.val) (by simp) (fun x _ => by
    simpa using ZMod.val_lt x) (fun r hr => ?_) (fun x _ => by simp) (fun r _ => ?_))
  · rw [ZMod.val_natCast, Nat.mod_eq_of_lt (mem_range.mp hr)]
  · have : ((r : ZMod p) * (c : ZMod p)) = (((r : ℤ) * c : ℤ) : ZMod p) := by push_cast; rfl
    rw [this, ZMod.stdAddChar_coe]
    push_cast
    ring_nf

/-- **Exercise 8.16 (b)**: for an odd prime `p ∤ k` and `a ≥ 2`, `G(k; p^a) = p G(k; p^{a-2})`. -/
@[kb "apostol1976" "Exercise 8.16(b), p. 177"]
theorem quadGaussSum_prime_pow {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {k : ℤ} (hk : ¬ (p : ℤ) ∣ k)
    {a : ℕ} (ha : 2 ≤ a) : quadGaussSum k (p ^ a) = p * quadGaussSum k (p ^ (a - 2)) := by
  obtain ⟨b, rfl⟩ : ∃ b, a = b + 2 := ⟨a - 2, by omega⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  simp only [Nat.add_sub_cancel, quadGaussSum_eq_sum_range]
  -- `r = u + p^{b+1} v` with `u < p^{b+1}`, `v < p`
  rw [show p ^ (b + 2) = p * p ^ (b + 1) by ring, sum_range_mul_eq, sum_comm]
  have step1 : ∀ u ∈ range (p ^ (b + 1)), ∑ v ∈ range p,
      exp (2 * π * I * k * (((u + p ^ (b + 1) * v : ℕ) : ℂ)) ^ 2 / ((p * p ^ (b + 1) : ℕ) : ℂ)) =
      exp (2 * π * I * k * (u : ℂ) ^ 2 / ((p * p ^ (b + 1) : ℕ) : ℂ)) *
        (if ((2 * k * u : ℤ) : ZMod p) = 0 then (p : ℂ) else 0) := by
    intro u _
    rw [← sum_range_exp_mul, mul_sum]
    refine sum_congr rfl fun v _ => ?_
    rw [← exp_add]
    have : 2 * π * I * k * (((u + p ^ (b + 1) * v : ℕ) : ℂ)) ^ 2 / ((p * p ^ (b + 1) : ℕ) : ℂ) =
        2 * π * I * k * (u : ℂ) ^ 2 / ((p * p ^ (b + 1) : ℕ) : ℂ) +
        2 * π * I * ((2 * k * u : ℤ) : ℂ) * (v : ℂ) / p + (k * p ^ b * v ^ 2 : ℤ) * (2 * π * I) := by
      push_cast; field_simp; ring
    rw [this, exp_add, exp_int_mul_two_pi_mul_I, mul_one]
  rw [sum_congr rfl step1]
  have hdvd : ∀ u : ℕ, ((2 * k * u : ℤ) : ZMod p) = 0 ↔ p ∣ u := by
    intro u
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    constructor
    · intro h
      have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
      rcases hpz.dvd_or_dvd h with h | h
      · rcases hpz.dvd_or_dvd h with h | h
        · have : (p : ℤ) ∣ 2 := h
          have h2 : p ∣ 2 := by exact_mod_cast this
          exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2) hp2
        · exact absurd h hk
      · exact_mod_cast h
    · intro h
      exact Dvd.dvd.mul_left (by exact_mod_cast h) _
  simp_rw [hdvd]
  -- `u = j + p i` with `j < p`, `i < p^b`; only `j = 0` survives
  rw [show p ^ (b + 1) = p ^ b * p by ring, sum_range_mul_eq, mul_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [sum_eq_single 0]
  · simp only [zero_add, dvd_mul_right, ite_true]
    have : 2 * π * I * k * (((p * i : ℕ) : ℂ)) ^ 2 / ((p * (p ^ b * p) : ℕ) : ℂ) =
        2 * π * I * k * (i : ℂ) ^ 2 / ((p ^ b : ℕ) : ℂ) := by
      push_cast; field_simp
    rw [this, mul_comm]
  · intro j hj hj0
    have : ¬ p ∣ j + p * i := by
      rw [Nat.dvd_add_left (dvd_mul_right p i)]
      exact Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero hj0) (mem_range.mp hj)
    simp [this]
  · simp [NeZero.pos p]

lemma quadGaussSum_one (k : ℤ) : quadGaussSum k 1 = 1 := by
  rw [quadGaussSum_eq_sum_range]
  simp

/-- Exercise 8.16 (b), consequence: `G(k; p^{2b}) = p^b` and `G(k; p^{2b+1}) = p^b G(k; p)`. -/
@[kb "apostol1976" "Exercise 8.16(b), p. 177"]
theorem quadGaussSum_prime_pow_even_odd {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {k : ℤ}
    (hk : ¬ (p : ℤ) ∣ k) (b : ℕ) :
    quadGaussSum k (p ^ (2 * b)) = (p : ℂ) ^ b ∧
      quadGaussSum k (p ^ (2 * b + 1)) = (p : ℂ) ^ b * quadGaussSum k p := by
  induction b with
  | zero => simp [quadGaussSum_one]
  | succ b ih =>
    rw [quadGaussSum_prime_pow hp hp2 hk (a := 2 * (b + 1)) (by omega),
      quadGaussSum_prime_pow hp hp2 hk (a := 2 * (b + 1) + 1) (by omega),
      show 2 * (b + 1) - 2 = 2 * b by omega, show 2 * (b + 1) + 1 - 2 = 2 * b + 1 by omega,
      ih.1, ih.2]
    constructor <;> ring

end NTKB.Apostol
