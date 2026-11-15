/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.NumberTheory.NumberField.Units.Basic
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic

/-! # Roots of unity in a quadratic field (Davenport, Chapter 6, row 6-3)

A quadratic field has `2`, `4` or `6` roots of unity, and it has more than `2` of them exactly when
its discriminant is `-3` (six roots of unity) or `-4` (four roots of unity).
-/

namespace NTKB.Davenport
open NumberField NumberField.Units Module

variable {K : Type*} [Field K] [NumberField K]

/-- If `φ(w) ≤ 2` then `w ∈ {1, 2, 3, 4, 6}`. -/
private lemma eq_of_totient_le_two {w : ℕ} (hw : w ≠ 0) (h : w.totient ≤ 2) :
    w = 1 ∨ w = 2 ∨ w = 3 ∨ w = 4 ∨ w = 6 := by
  have hpos : 0 < w.totient := Nat.totient_pos.2 (Nat.pos_of_ne_zero hw)
  have hp : ∀ p : ℕ, p.Prime → p ∣ w → p = 2 ∨ p = 3 := by
    intro p hp hpw
    have h1 := Nat.le_of_dvd hpos ((Nat.totient_prime hp) ▸ Nat.totient_dvd_of_dvd hpw)
    have := hp.two_le
    omega
  have hfac : w = 2 ^ (w.factorization 2) * 3 ^ (w.factorization 3) := by
    apply Nat.eq_of_factorization_eq hw
    · positivity
    intro q
    by_cases hq : q.Prime
    · rw [Nat.factorization_mul (by positivity) (by positivity),
        Nat.factorization_pow, Nat.factorization_pow]
      simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul,
        Nat.Prime.factorization (Nat.prime_two), Nat.Prime.factorization (Nat.prime_three),
        Finsupp.single_apply]
      by_cases h2 : q = 2
      · subst h2; simp
      by_cases h3 : q = 3
      · subst h3; simp
      have : ¬ q ∣ w := fun hd => by rcases hp q hq hd with h | h <;> contradiction
      rw [Nat.factorization_eq_zero_of_not_dvd this]
      simp [Ne.symm h2, Ne.symm h3]
    · simp [Nat.factorization_eq_zero_of_not_prime _ hq]
  set a := w.factorization 2
  set b := w.factorization 3
  have ha : a ≤ 2 := by
    by_contra hcon
    have hd : 2 ^ 3 ∣ w := by
      rw [hfac]
      exact Dvd.dvd.mul_right (pow_dvd_pow 2 (by omega)) _
    have := Nat.le_of_dvd hpos (Nat.totient_dvd_of_dvd hd)
    rw [Nat.totient_prime_pow Nat.prime_two (by norm_num)] at this
    omega
  have hb : b ≤ 1 := by
    by_contra hcon
    have hd : 3 ^ 2 ∣ w := by
      rw [hfac]
      exact Dvd.dvd.mul_left (pow_dvd_pow 3 (by omega)) _
    have := Nat.le_of_dvd hpos (Nat.totient_dvd_of_dvd hd)
    rw [Nat.totient_prime_pow Nat.prime_three (by norm_num)] at this
    omega
  rw [hfac] at h ⊢
  interval_cases a <;> interval_cases b <;> simp_all <;> exact absurd h (by decide)

/-- `K` contains a primitive `torsionOrder K`-th root of unity. -/
private lemma exists_isPrimitiveRoot_torsionOrder :
    ∃ ζ : K, IsPrimitiveRoot ζ (torsionOrder K) := by
  obtain ⟨μ, hμ⟩ : ∃ μ : torsion K, orderOf μ = torsionOrder K := by
    exact IsCyclic.exists_ofOrder_eq_natCard
  rw [← IsPrimitiveRoot.iff_orderOf, ← IsPrimitiveRoot.coe_submonoidClass_iff,
    ← IsPrimitiveRoot.coe_units_iff] at hμ
  exact ⟨_, hμ.map_of_injective (FaithfulSMul.algebraMap_injective (𝓞 K) K)⟩

private lemma natDegree_minpoly_eq_totient {n : ℕ} [NeZero n] {ζ : K} (hζ : IsPrimitiveRoot ζ n) :
    (minpoly ℚ ζ).natDegree = n.totient := by
  rw [← Polynomial.cyclotomic_eq_minpoly_rat hζ (NeZero.pos n), Polynomial.natDegree_cyclotomic]

private lemma totient_torsionOrder_le (hK : finrank ℚ K = 2) :
    (torsionOrder K).totient ≤ 2 := by
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_torsionOrder (K := K)
  rw [← natDegree_minpoly_eq_totient hζ, ← hK]
  exact minpoly.natDegree_le ζ

private lemma isCyclotomicExtension_of_finrank {n : ℕ} [NeZero n] {ζ : K} (hζ : IsPrimitiveRoot ζ n)
    (hK : finrank ℚ K = n.totient) : IsCyclotomicExtension {n} ℚ K := by
  have hint : IsIntegral ℚ ζ := (hζ.isIntegral (NeZero.pos n)).tower_top
  have hfin : finrank ℚ (IntermediateField.adjoin ℚ {ζ}) = finrank ℚ K := by
    rw [IntermediateField.adjoin.finrank hint, natDegree_minpoly_eq_totient hζ, hK]
  have htop : IntermediateField.adjoin ℚ {ζ} = ⊤ := IntermediateField.eq_of_le_of_finrank_eq
    le_top (by simpa using hfin)
  have htop' : Algebra.adjoin ℚ {ζ} = ⊤ := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic (IsAlgebraic.of_finite ℚ ζ),
      htop, IntermediateField.top_toSubalgebra]
  rw [IsCyclotomicExtension.iff_singleton]
  refine ⟨⟨ζ, hζ⟩, fun x => ?_⟩
  have hx : x ∈ Algebra.adjoin ℚ {ζ} := by rw [htop']; trivial
  exact Algebra.adjoin_mono (by simpa using hζ.pow_eq_one) hx

/-- A quadratic field has 2, 4 or 6 roots of unity. -/
theorem torsionOrder_eq_two_or_four_or_six (hK : finrank ℚ K = 2) :
    torsionOrder K = 2 ∨ torsionOrder K = 4 ∨ torsionOrder K = 6 := by
  have h1 := eq_of_totient_le_two (torsionOrder_ne_zero K) (totient_torsionOrder_le hK)
  have h2 := even_torsionOrder K
  rcases h1 with h | h | h | h | h <;> rw [h] at h2 ⊢ <;> simp_all <;> exact absurd h2 (by decide)

/-- A quadratic field has only the roots of unity `±1` unless its discriminant is `-3` or `-4`. -/
theorem torsionOrder_eq_two_of_discr (hK : finrank ℚ K = 2) (h3 : discr K ≠ -3) (h4 : discr K ≠ -4) :
    torsionOrder K = 2 := by
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_torsionOrder (K := K)
  rcases torsionOrder_eq_two_or_four_or_six hK with h | h | h
  · exact h
  · exfalso
    rw [h] at hζ
    have : NeZero 4 := ⟨by norm_num⟩
    have hc : IsCyclotomicExtension {2 ^ 2} ℚ K :=
      isCyclotomicExtension_of_finrank (n := 4) hζ (by rw [hK]; decide)
    apply h4
    have := IsCyclotomicExtension.Rat.discr_prime_pow 2 2 K
    have ht : Nat.totient 4 = 2 := by decide
    rw [this]
    norm_num [ht]
  · exfalso
    rw [h] at hζ
    have hζ3 : IsPrimitiveRoot (ζ ^ 2) 3 := hζ.pow_of_dvd (by norm_num) (by norm_num)
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hc : IsCyclotomicExtension {3} ℚ K :=
      isCyclotomicExtension_of_finrank (n := 3) hζ3 (by rw [hK]; decide)
    apply h3
    have := IsCyclotomicExtension.Rat.discr_prime 3 K
    simpa using this

theorem torsionOrder_le_six (hK : finrank ℚ K = 2) : torsionOrder K ≤ 6 := by
  rcases torsionOrder_eq_two_or_four_or_six hK with h | h | h <;> omega

end NTKB.Davenport
