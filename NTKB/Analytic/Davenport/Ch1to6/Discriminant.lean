/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Elementary.SpecialValues.FundamentalGaussSum

/-!
# Davenport, Chapter 5: fundamental discriminants and primitive forms

(§5, p. 41.) For `D ≡ 0, 1 (mod 4)`, every binary quadratic form `ax² + bxy + cy²` of
discriminant `b² - 4ac = D` is primitive (`(a, b, c) = 1`) if and only if `D` is a fundamental
discriminant: `D ≡ 1 (mod 4)` squarefree, or `D = 4N` with `N ≡ 2, 3 (mod 4)` squarefree
(`NTKB.IsFundamentalDiscriminant`).

The proof is the book's: a common divisor `m > 1` of `a, b, c` has `m² ∣ D`, which forces `m = 2`
and `D = 4N` with `N = b₁² - 4a₁c₁ ≡ 0, 1 (mod 4)`; conversely, if `D` is not fundamental the
forms `(m, m, ·)` or `(m, 0, ·)` with a suitable `m > 1` have discriminant `D`.
-/

namespace NTKB.Davenport

theorem sq_emod_four (x : ℤ) : x ^ 2 % 4 = 0 ∨ x ^ 2 % 4 = 1 := by
  rcases Int.even_or_odd x with ⟨y, rfl⟩ | ⟨y, rfl⟩
  · left; ring_nf; omega
  · right; ring_nf; omega

/-- `m² ∣ D` for a common divisor `m` of the coefficients of a form of discriminant `D`. -/
theorem mul_self_dvd_disc {a b c m : ℤ} (ha : m ∣ a) (hb : m ∣ b) (hc : m ∣ c) :
    m * m ∣ b ^ 2 - 4 * a * c := by
  refine dvd_sub ?_ ?_
  · rw [sq]; exact mul_dvd_mul hb hb
  · rw [mul_assoc]; exact dvd_mul_of_dvd_right (mul_dvd_mul ha hc) 4

/-- A prime `p` (as an integer) with `p² ∣ D` when `D ≠ 0` is not squarefree. -/
theorem exists_prime_sq_dvd {D : ℤ} (hD : ¬ Squarefree D) :
    ∃ p : ℕ, p.Prime ∧ ((p : ℤ) * p ∣ D) := by
  rw [← Int.squarefree_natAbs, Nat.squarefree_iff_prime_squarefree] at hD
  obtain ⟨p, hp, hpD⟩ : ∃ p : ℕ, p.Prime ∧ p * p ∣ D.natAbs := by
    by_contra h
    exact hD fun x hx hd ↦ h ⟨x, hx, hd⟩
  refine ⟨p, hp, ?_⟩
  rw [← Int.natAbs_dvd_natAbs]
  simpa [Int.natAbs_mul] using hpD

/-- **Davenport §5, p. 41.** For `D ≡ 0, 1 (mod 4)`: `D` is a fundamental discriminant if and
only if every form `ax² + bxy + cy²` with `b² - 4ac = D` is primitive. -/
@[kb "davenport1980" "Ch 5, p. 41"]
theorem isFundamentalDiscriminant_iff_forall_primitive {D : ℤ} (hD : D % 4 = 0 ∨ D % 4 = 1) :
    IsFundamentalDiscriminant D ↔
      ∀ a b c : ℤ, b ^ 2 - 4 * a * c = D → ∀ m : ℤ, m ∣ a → m ∣ b → m ∣ c → IsUnit m := by
  constructor
  · intro hF a b c hdisc m ha hb hc
    have hm2 : m * m ∣ D := hdisc ▸ mul_self_dvd_disc ha hb hc
    rcases hF with ⟨_, hsq⟩ | ⟨h0, h23, hsq⟩
    · exact hsq m hm2
    · by_cases h2 : (2 : ℤ) ∣ m
      · exfalso
        obtain ⟨a1, rfl⟩ := h2.trans ha
        obtain ⟨b1, rfl⟩ := h2.trans hb
        obtain ⟨c1, rfl⟩ := h2.trans hc
        have hN : D / 4 = b1 ^ 2 - 4 * a1 * c1 := by
          rw [← hdisc]
          have e : (2 * b1) ^ 2 - 4 * (2 * a1) * (2 * c1) = 4 * (b1 ^ 2 - 4 * a1 * c1) := by ring
          rw [e, Int.mul_ediv_cancel_left _ (by norm_num)]
        have hb := sq_emod_four b1
        rw [show 4 * a1 * c1 = 4 * (a1 * c1) by ring] at hN
        generalize b1 ^ 2 = B at hN hb
        generalize a1 * c1 = P at hN
        omega
      · have hcop : IsCoprime m 2 := (Int.prime_two.coprime_iff_not_dvd.mpr h2).symm
        have hcop4 : IsCoprime (m * m) 4 := by
          have := (hcop.mul_left hcop).mul_right (hcop.mul_left hcop)
          simpa [show (2 : ℤ) * 2 = 4 by norm_num] using this
        have hD4 : D = 4 * (D / 4) := by omega
        rw [hD4] at hm2
        exact hsq m (hcop4.dvd_of_dvd_mul_left hm2)
  · intro hall
    by_contra hF
    -- an imprimitive form of discriminant `D` with common divisor `m`
    have key : ∀ m a b c : ℤ, ¬ IsUnit m → m ∣ a → m ∣ b → m ∣ c → b ^ 2 - 4 * a * c = D →
        False := fun m a b c hm ha hb hc hd ↦ hm (hall a b c hd m ha hb hc)
    have hnu2 : ¬ IsUnit (2 : ℤ) := by decide
    rcases hD with h0 | h1
    · set N := D / 4 with hNdef
      have hD4 : D = 4 * N := by omega
      by_cases hN0 : N % 4 = 0
      · exact key 2 2 0 (-(N / 2)) hnu2 (dvd_refl _) (dvd_zero _)
          (dvd_neg.mpr ⟨N / 4, by omega⟩) (by rw [hD4]; ring_nf; omega)
      by_cases hN1 : N % 4 = 1
      · exact key 2 2 2 ((1 - N) / 2) hnu2 (dvd_refl _) (dvd_refl _)
          ⟨(1 - N) / 4, by omega⟩ (by rw [hD4]; ring_nf; omega)
      · have h23 : N % 4 = 2 ∨ N % 4 = 3 := by omega
        have hsq : ¬ Squarefree N := fun hs ↦ hF (Or.inr ⟨h0, h23, hs⟩)
        obtain ⟨p, hp, hpN⟩ := exists_prime_sq_dvd hsq
        obtain ⟨k, hk⟩ := hpN
        have hp2 : p ≠ 2 := by
          rintro rfl
          push_cast at hk
          omega
        have hpu : ¬ IsUnit (p : ℤ) := by
          rw [Int.isUnit_iff]; have := hp.two_le; omega
        exact key p p 0 (-(p * k)) hpu (dvd_refl _) (dvd_zero _)
          (dvd_neg.mpr (dvd_mul_right _ _)) (by rw [hD4, hk]; ring)
    · have hsq : ¬ Squarefree D := fun hs ↦ hF (Or.inl ⟨h1, hs⟩)
      obtain ⟨p, hp, hpD⟩ := exists_prime_sq_dvd hsq
      obtain ⟨k, hk⟩ := hpD
      have hpodd : (p : ℤ) % 2 = 1 := by
        rcases Nat.Prime.eq_two_or_odd hp with h | h
        · subst h; push_cast at hk; omega
        · exact_mod_cast (show (p : ℤ) % 2 = 1 by exact_mod_cast h)
      have hp4 : (p : ℤ) * p % 4 = 1 := by
        obtain ⟨t, ht⟩ : ∃ t, (p : ℤ) = 2 * t + 1 := ⟨(p : ℤ) / 2, by omega⟩
        rw [ht]; ring_nf; omega
      have hk4 : k % 4 = 1 := by
        have : D % 4 = ((p : ℤ) * p % 4) * (k % 4) % 4 := by rw [hk, Int.mul_emod]
        rw [hp4, one_mul, Int.emod_emod_of_dvd _ (dvd_refl _)] at this
        omega
      have hpu : ¬ IsUnit (p : ℤ) := by
        rw [Int.isUnit_iff]; have := hp.two_le; omega
      obtain ⟨j, hj⟩ : (4 : ℤ) ∣ 1 - k := ⟨(1 - k) / 4, by omega⟩
      exact key p p p (p * j) hpu (dvd_refl _) (dvd_refl _) (dvd_mul_right _ _)
        (by rw [hk]; linear_combination (p : ℤ) * p * hj)

end NTKB.Davenport
