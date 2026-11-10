/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.RingTheory.ZMod.UnitsCyclic
import Mathlib.FieldTheory.Finite.Basic
import NTKB.Attr

/-!
# Primitive roots modulo odd prime powers (Apostol, Theorem 10.6 (a) and Lemma 2 of §10.5)

Let `p` be an odd prime and `g` a primitive root modulo `p` (`g` has order `p - 1` mod `p`).

* **Lemma 2**: if `g^{p-1} ≢ 1 (mod p²)`, then `g^{p^{a-2}(p-1)} ≢ 1 (mod p^a)` for `a ≥ 2`.
* **Theorem 10.6 (a)**: `g` is a primitive root modulo `p^a` for every `a ≥ 1` iff
  `g^{p-1} ≢ 1 (mod p²)`.

Writing `g^{p-1} = 1 + p c` (Fermat), the hypothesis is `p ∤ c`, and then `g^{p-1}` has order
`p^{a-1}` modulo `p^a` (Mathlib's `ZMod.orderOf_one_add_mul_prime`, which packages Apostol's
induction of Lemma 2). Since the order of `g` mod `p^a` is a multiple of `p - 1`, it is
`(p-1) p^{a-1} = φ(p^a)`. (Part (b), existence of such `g`, is Mathlib's
`ZMod.isCyclic_units_of_prime_pow`.)
-/

namespace NTKB.Apostol

variable {p : ℕ}

/-- `g^{p-1} = 1 + p c` with `p ∤ c` when `g^{p-1} ≢ 1 (mod p²)` and `p ∤ g`. -/
lemma exists_pow_sub_one_eq (hp : p.Prime) {g : ℤ} (hg : ¬ (p : ℤ) ∣ g)
    (h2 : ¬ g ^ (p - 1) ≡ 1 [ZMOD p ^ 2]) :
    ∃ c : ℤ, g ^ (p - 1) = 1 + p * c ∧ ¬ (p : ℤ) ∣ c := by
  have hferm : (p : ℤ) ∣ g ^ (p - 1) - 1 := by
    have := Fact.mk hp
    have hg0 : (g : ZMod p) ≠ 0 := by rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    have h1 := ZMod.pow_card_sub_one_eq_one hg0
    rw [← Int.cast_pow, ← Int.cast_one, ZMod.intCast_eq_intCast_iff_dvd_sub] at h1
    rw [← dvd_neg, neg_sub]; exact h1
  obtain ⟨c, hc⟩ := hferm
  refine ⟨c, by linarith, fun hpc => h2 ?_⟩
  obtain ⟨e, rfl⟩ := hpc
  rw [Int.modEq_iff_dvd]
  exact ⟨-e, by rw [show (1 : ℤ) - g ^ (p - 1) = -(g ^ (p - 1) - 1) by ring, hc]; ring⟩

/-- The order of `g^{p-1}` modulo `p^{n+1}` is `p^n` when `g^{p-1} ≢ 1 (mod p²)`. -/
lemma orderOf_pow_sub_one (hp : p.Prime) (hp2 : p ≠ 2) {g : ℤ} (hg : ¬ (p : ℤ) ∣ g)
    (h2 : ¬ g ^ (p - 1) ≡ 1 [ZMOD p ^ 2]) (n : ℕ) :
    orderOf ((g : ZMod (p ^ (n + 1))) ^ (p - 1)) = p ^ n := by
  obtain ⟨c, hc, hpc⟩ := exists_pow_sub_one_eq hp hg h2
  have : ((g : ZMod (p ^ (n + 1))) ^ (p - 1)) = 1 + p * (c : ZMod (p ^ (n + 1))) := by
    rw [← Int.cast_pow, hc]; push_cast; ring
  rw [this]
  exact ZMod.orderOf_one_add_mul_prime hp hp2 c hpc n

/-- **Lemma 2 of §10.5**: if `g^{p-1} ≢ 1 (mod p²)` then `g^{p^{a-2}(p-1)} ≢ 1 (mod p^a)` for
`a ≥ 2`. -/
@[kb "apostol1976" "Ch. 10, Lemma 2, p. 210"]
theorem ch10_lemma_2 (hp : p.Prime) (hp2 : p ≠ 2) {g : ℤ} (hg : ¬ (p : ℤ) ∣ g)
    (h2 : ¬ g ^ (p - 1) ≡ 1 [ZMOD p ^ 2]) {a : ℕ} (ha : 2 ≤ a) :
    ¬ g ^ (p ^ (a - 2) * (p - 1)) ≡ 1 [ZMOD p ^ a] := by
  intro h
  obtain ⟨n, rfl⟩ : ∃ n, a = n + 1 := ⟨a - 1, by omega⟩
  have hord := orderOf_pow_sub_one hp hp2 hg h2 n
  have h' : g ^ (p ^ (n + 1 - 2) * (p - 1)) ≡ 1 [ZMOD ((p ^ (n + 1) : ℕ) : ℤ)] := by
    push_cast; exact h
  rw [← ZMod.intCast_eq_intCast_iff] at h'
  push_cast at h'
  have h := h'
  rw [mul_comm, pow_mul] at h
  have := orderOf_dvd_of_pow_eq_one h
  rw [hord, Nat.pow_dvd_pow_iff_le_right hp.one_lt] at this
  omega

/-- **Theorem 10.6 (a)**: a primitive root `g` modulo an odd prime `p` is a primitive root modulo
`p^a` for every `a ≥ 1` iff `g^{p-1} ≢ 1 (mod p²)`. -/
@[kb "apostol1976" "Thm 10.6, p. 209"]
theorem orderOf_prime_pow_eq_totient_iff (hp : p.Prime) (hp2 : p ≠ 2) {g : ℤ}
    (hg : orderOf (g : ZMod p) = p - 1) :
    (∀ a : ℕ, 1 ≤ a → orderOf (g : ZMod (p ^ a)) = (p ^ a).totient) ↔
      ¬ g ^ (p - 1) ≡ 1 [ZMOD p ^ 2] := by
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hgp : ¬ (p : ℤ) ∣ g := by
    intro h
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd] at h
    rw [h, orderOf_eq_zero_iff'.mpr] at hg
    · omega
    · intro n hn h0
      have := Fact.mk hp
      rw [zero_pow hn.ne'] at h0
      exact zero_ne_one h0
  constructor
  · intro h h1
    have h2 := h 2 (by norm_num)
    have h1' : g ^ (p - 1) ≡ 1 [ZMOD ((p ^ 2 : ℕ) : ℤ)] := by push_cast; exact h1
    rw [← ZMod.intCast_eq_intCast_iff] at h1'
    push_cast at h1'
    replace h1 := h1'
    have := orderOf_dvd_of_pow_eq_one h1
    rw [h2, Nat.totient_prime_pow_succ hp] at this
    have hle := Nat.le_of_dvd (by omega) this
    have : p ^ 1 * (p - 1) > p - 1 := by
      rw [pow_one]
      have h3 : 2 ≤ p - 1 := by omega
      nlinarith
    omega
  · intro h2 a ha
    obtain ⟨n, rfl⟩ : ∃ n, a = n + 1 := ⟨a - 1, by omega⟩
    set t := orderOf (g : ZMod (p ^ (n + 1)))
    have hcop : IsUnit (g : ZMod (p ^ (n + 1))) := by
      have : IsCoprime g ((p ^ (n + 1) : ℕ) : ℤ) := by
        push_cast
        exact ((Prime.coprime_iff_not_dvd (Nat.prime_iff_prime_int.mp hp)).mpr hgp).symm.pow_right
      obtain ⟨u, v, huv⟩ := this
      refine IsUnit.of_mul_eq_one_right (u : ZMod (p ^ (n + 1))) ?_
      have := congrArg (Int.cast : ℤ → ZMod (p ^ (n + 1))) huv
      push_cast at this
      rwa [← Nat.cast_pow, ZMod.natCast_self, mul_zero, add_zero] at this
    -- `t ∣ φ(p^{n+1})`
    have htdvd : t ∣ (p ^ (n + 1)).totient := by
      obtain ⟨u, hu⟩ := hcop
      apply orderOf_dvd_of_pow_eq_one
      rw [← hu, ← Units.val_pow_eq_pow_val, ZMod.pow_totient, Units.val_one]
    have htpos : 0 < t := Nat.pos_of_dvd_of_pos htdvd (Nat.totient_pos.mpr (by positivity))
    -- `p - 1 ∣ t`
    have hpt : p - 1 ∣ t := by
      rw [← hg]
      apply orderOf_dvd_of_pow_eq_one
      have h1 : (g : ZMod (p ^ (n + 1))) ^ t = 1 := pow_orderOf_eq_one _
      have := congrArg (ZMod.castHom (dvd_pow_self p (Nat.succ_ne_zero n)) (ZMod p)) h1
      simpa using this
    have hord := orderOf_pow_sub_one hp hp2 hgp h2 n
    rw [orderOf_pow' _ (by omega : p - 1 ≠ 0), Nat.gcd_eq_right hpt] at hord
    change t / (p - 1) = p ^ n at hord
    rw [Nat.totient_prime_pow_succ hp]
    obtain ⟨q, hq⟩ := hpt
    rw [hq, Nat.mul_div_cancel_left _ (by omega)] at hord
    rw [hq, hord, mul_comm]

end NTKB.Apostol
