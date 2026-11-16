/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Elementary.QuadraticField.Decomposition
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# The number of ideals of norm `n` in a quadratic field

Let `a_K(n)` be the number of ideals of `𝓞 K` of norm `n` (`NTKB.QuadraticField.idealCount`).

* `NTKB.QuadraticField.idealCount_mul` (any number field): `a_K(mn) = a_K(m) a_K(n)` for
  relatively prime `m, n ≥ 1`; an ideal `𝔞` of norm `mn` is `(𝔞 + (m))(𝔞 + (n))`, the factors
  of norms `m` and `n`, and `𝔟 = 𝔟𝔠 + (m)` recovers the factors of a product.
* For a quadratic field of discriminant `D` and a prime `p`, from the decomposition law
  (`NTKB.QuadraticField.exists_split`, `isPrime_of_inert`, `exists_ramified`): every ideal of norm
  `p^k` divides `(p)^k`, so it is `𝔭^i 𝔭'^(k-i)` (split, `k + 1` ideals), `(p)^(k/2)` for even `k`
  (inert) or `𝔭^k` (ramified); in each case `a_K(p^k) = ∑_{i ≤ k} (D/p)^i`.
* `NTKB.QuadraticField.card_absNorm_eq` (Davenport §6, p. 52, before (27)): for `n ≥ 1`,
  `a_K(n) = ∑_{m ∣ n} (D/m)`, both sides being multiplicative and equal at prime powers.
-/

noncomputable section

set_option linter.unusedSectionVars false

open QuadraticAlgebra NumberField Module Ideal

namespace NTKB.QuadraticField

variable {K : Type*} [Field K] [NumberField K]

variable (K) in
/-- The number of ideals of `𝓞 K` of norm `n`. -/
def idealCount (n : ℕ) : ℕ := Nat.card {I : Ideal (𝓞 K) // absNorm I = n}

theorem idealCount_one : idealCount K 1 = 1 := by
  rw [idealCount, Nat.card_eq_one_iff_unique]
  refine ⟨⟨fun I J ↦ ?_⟩, ⟨⟨⊤, absNorm_top⟩⟩⟩
  exact Subtype.ext ((absNorm_eq_one_iff.mp I.2).trans (absNorm_eq_one_iff.mp J.2).symm)

/-! ### Multiplicativity -/

theorem span_natCast_sup_eq_top {m n : ℕ} (h : m.Coprime n) :
    span {(m : 𝓞 K)} ⊔ span {(n : 𝓞 K)} = ⊤ := by
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.mpr h
  rw [eq_top_iff_one]
  have : ((u * m + v * n : ℤ) : 𝓞 K) ∈ span {(m : 𝓞 K)} ⊔ span {(n : 𝓞 K)} := by
    push_cast
    exact add_mem (mem_sup_left (mul_mem_left _ _ (mem_span_singleton_self _)))
      (mem_sup_right (mul_mem_left _ _ (mem_span_singleton_self _)))
  rwa [huv, Int.cast_one] at this

theorem span_natCast_absNorm_le (I : Ideal (𝓞 K)) {m : ℕ} (hI : absNorm I = m) :
    span {(m : 𝓞 K)} ≤ I := hI ▸ span_singleton_absNorm_le I

/-- `𝔟 = 𝔟𝔠 + (m)` when `N 𝔟 = m` and `N 𝔠` is prime to `m`. -/
theorem eq_mul_sup_span {I J : Ideal (𝓞 K)} {m n : ℕ} (hmn : m.Coprime n) (hI : absNorm I = m)
    (hJ : absNorm J = n) : I = I * J ⊔ span {(m : 𝓞 K)} := by
  refine le_antisymm ?_ (sup_le Ideal.mul_le_left (span_natCast_absNorm_le I hI))
  have htop : J ⊔ span {(m : 𝓞 K)} = ⊤ := by
    rw [eq_top_iff, ← span_natCast_sup_eq_top hmn.symm]
    exact sup_le (le_sup_of_le_left (span_natCast_absNorm_le J hJ)) le_sup_right
  calc I = I * (J ⊔ span {(m : 𝓞 K)}) := by rw [htop, Ideal.mul_top]
    _ = I * J ⊔ I * span {(m : 𝓞 K)} := Ideal.mul_sup _ _ _
    _ ≤ I * J ⊔ span {(m : 𝓞 K)} := sup_le_sup_left Ideal.mul_le_right _

/-- From `a ∣ m`, `b ∣ n`, `a b = m n`, `m n ≠ 0`: `a = m` and `b = n`. -/
theorem eq_of_dvd_of_mul_eq {a b m n : ℕ} (ha : a ∣ m) (hb : b ∣ n) (h : a * b = m * n)
    (hm : m ≠ 0) (hn : n ≠ 0) : a = m ∧ b = n := by
  have h1 := Nat.le_of_dvd (Nat.pos_of_ne_zero hm) ha
  have h2 := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hb
  constructor
  · by_contra hne
    have : a * b < m * n :=
      Nat.mul_lt_mul_of_lt_of_le (lt_of_le_of_ne h1 hne) h2 (Nat.pos_of_ne_zero hn)
    omega
  · by_contra hne
    have : a * b < m * n :=
      Nat.mul_lt_mul_of_le_of_lt h1 (lt_of_le_of_ne h2 hne) (Nat.pos_of_ne_zero hm)
    omega

theorem idealCount_mul {m n : ℕ} (hmn : m.Coprime n) (hm : m ≠ 0) (hn : n ≠ 0) :
    idealCount K (m * n) = idealCount K m * idealCount K n := by
  rw [idealCount, idealCount, idealCount, ← Nat.card_prod]
  symm
  let F : {I : Ideal (𝓞 K) // absNorm I = m} × {J : Ideal (𝓞 K) // absNorm J = n} →
      {L : Ideal (𝓞 K) // absNorm L = m * n} :=
    fun x ↦ ⟨x.1.1 * x.2.1, by rw [map_mul, x.1.2, x.2.2]⟩
  refine Nat.card_eq_of_bijective F ⟨?_, ?_⟩
  · rintro ⟨⟨I, hI⟩, ⟨J, hJ⟩⟩ ⟨⟨I', hI'⟩, ⟨J', hJ'⟩⟩ h
    have h' : I * J = I' * J' := congrArg Subtype.val h
    have e1 := eq_mul_sup_span hmn hI hJ
    have e1' := eq_mul_sup_span hmn hI' hJ'
    have e2 := eq_mul_sup_span hmn.symm hJ hI
    have e2' := eq_mul_sup_span hmn.symm hJ' hI'
    rw [mul_comm] at e2 e2'
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · show I = I'
      rw [e1, e1', h']
    · show J = J'
      rw [e2, e2', h']
  · rintro ⟨L, hL⟩
    set M := span {(m : 𝓞 K)}
    set N := span {(n : 𝓞 K)}
    have hMN : M ⊔ N = ⊤ := span_natCast_sup_eq_top hmn
    have hmnL : M * N ≤ L := by
      rw [span_singleton_mul_span_singleton, ← Nat.cast_mul]
      exact span_natCast_absNorm_le L hL
    have hprod : (L ⊔ M) * (L ⊔ N) = L := by
      refine le_antisymm ?_ ?_
      · rw [Ideal.sup_mul, Ideal.mul_sup, Ideal.mul_sup]
        exact sup_le (sup_le Ideal.mul_le_left Ideal.mul_le_left) (sup_le Ideal.mul_le_right hmnL)
      · calc L = L * (M ⊔ N) := by rw [hMN, Ideal.mul_top]
          _ = L * M ⊔ L * N := Ideal.mul_sup _ _ _
          _ ≤ (L ⊔ M) * (L ⊔ N) := sup_le
              (by rw [mul_comm]; exact mul_mono le_sup_right le_sup_left)
              (mul_mono le_sup_left le_sup_right)
    have hnorm : absNorm (L ⊔ M) * absNorm (L ⊔ N) = m * n := by
      rw [← map_mul, hprod, hL]
    have hrank := absNorm_span_natCast (S := 𝓞 K) m
    have hrank' := absNorm_span_natCast (S := 𝓞 K) n
    have hdm : absNorm (L ⊔ M) ∣ m := by
      have h1 : absNorm (L ⊔ M) ∣ m ^ finrank ℤ (𝓞 K) := by
        rw [← hrank]; exact absNorm_dvd_absNorm_of_le le_sup_right
      have hc : (absNorm (L ⊔ M)).Coprime n :=
        Nat.Coprime.coprime_dvd_left h1 (Nat.Coprime.pow_left _ hmn)
      exact hc.dvd_of_dvd_mul_right ⟨_, hnorm.symm⟩
    have hdn : absNorm (L ⊔ N) ∣ n := by
      have h1 : absNorm (L ⊔ N) ∣ n ^ finrank ℤ (𝓞 K) := by
        rw [← hrank']; exact absNorm_dvd_absNorm_of_le le_sup_right
      have hc : (absNorm (L ⊔ N)).Coprime m :=
        Nat.Coprime.coprime_dvd_left h1 (Nat.Coprime.pow_left _ hmn.symm)
      exact hc.dvd_of_dvd_mul_left ⟨absNorm (L ⊔ M), by rw [← hnorm]; ring⟩
    obtain ⟨h1, h2⟩ := eq_of_dvd_of_mul_eq hdm hdn hnorm hm hn
    exact ⟨⟨⟨L ⊔ M, h1⟩, ⟨L ⊔ N, h2⟩⟩, Subtype.ext hprod⟩

/-! ### Prime powers -/

/-- An ideal of norm `p^k` divides `(p)^k`. -/
theorem dvd_span_pow {I : Ideal (𝓞 K)} {p k : ℕ} (hI : absNorm I = p ^ k) :
    I ∣ span {(p : 𝓞 K)} ^ k := by
  rw [Ideal.dvd_iff_le, span_singleton_pow, ← Nat.cast_pow]
  exact span_natCast_absNorm_le I hI

/-- The ideals dividing a power of a prime ideal are its powers. -/
theorem eq_pow_of_dvd_pow {P I : Ideal (𝓞 K)} (hP : P.IsPrime) (hP0 : P ≠ ⊥) {k : ℕ}
    (h : I ∣ P ^ k) : ∃ i ≤ k, I = P ^ i := by
  obtain ⟨i, hi, hassoc⟩ := (dvd_prime_pow (Ideal.prime_of_isPrime hP0 hP) k).mp h
  exact ⟨i, hi, associated_iff_eq.mp hassoc⟩

theorem ne_bot_of_absNorm_eq {P : Ideal (𝓞 K)} {p : ℕ} (hp : p.Prime) (hP : absNorm P = p) :
    P ≠ ⊥ := by
  rintro rfl; rw [absNorm_bot] at hP; exact hp.ne_zero hP.symm

theorem pow_injective {p : ℕ} (hp : p.Prime) {i j : ℕ} (h : p ^ i = p ^ j) : i = j :=
  Nat.pow_right_injective hp.two_le h

/-- **Ramified**: one ideal of norm `p^k`. -/
theorem idealCount_ramified {P : Ideal (𝓞 K)} {p : ℕ} (hp : p.Prime) (hP : P.IsPrime)
    (hPn : absNorm P = p) (hspan : span {(p : 𝓞 K)} = P ^ 2) (k : ℕ) :
    idealCount K (p ^ k) = 1 := by
  rw [idealCount, Nat.card_eq_one_iff_unique]
  have key : ∀ I : {I : Ideal (𝓞 K) // absNorm I = p ^ k}, I.1 = P ^ k := by
    rintro ⟨I, hI⟩
    have hdvd := dvd_span_pow hI
    rw [hspan, ← pow_mul] at hdvd
    obtain ⟨i, -, rfl⟩ := eq_pow_of_dvd_pow hP (ne_bot_of_absNorm_eq hp hPn) hdvd
    rw [map_pow, hPn] at hI
    show P ^ i = P ^ k
    rw [pow_injective hp hI]
  exact ⟨⟨fun I J ↦ Subtype.ext ((key I).trans (key J).symm)⟩,
    ⟨⟨P ^ k, by rw [map_pow, hPn]⟩⟩⟩

/-- **Inert**: one ideal of norm `p^k` for even `k`, none for odd `k`. -/
theorem idealCount_inert {p : ℕ} (hp : p.Prime) (hP : (span {(p : 𝓞 K)}).IsPrime)
    (hPn : absNorm (span {(p : 𝓞 K)}) = p ^ 2) (k : ℕ) :
    idealCount K (p ^ k) = if Even k then 1 else 0 := by
  set P := span {(p : 𝓞 K)}
  have hP0 : P ≠ ⊥ := by
    intro h; rw [h, absNorm_bot] at hPn; exact pow_ne_zero 2 hp.ne_zero hPn.symm
  have key : ∀ I : {I : Ideal (𝓞 K) // absNorm I = p ^ k}, ∃ i, k = 2 * i ∧ I.1 = P ^ i := by
    rintro ⟨I, hI⟩
    obtain ⟨i, -, rfl⟩ := eq_pow_of_dvd_pow hP hP0 (dvd_span_pow hI)
    rw [map_pow, hPn, ← pow_mul] at hI
    exact ⟨i, (pow_injective hp hI).symm, rfl⟩
  split_ifs with hk
  · rw [idealCount, Nat.card_eq_one_iff_unique]
    obtain ⟨j, hj⟩ := hk
    refine ⟨⟨fun I J ↦ Subtype.ext ?_⟩, ⟨⟨P ^ j, by rw [map_pow, hPn, ← pow_mul, hj, two_mul]⟩⟩⟩
    obtain ⟨i, hi, hI⟩ := key I
    obtain ⟨i', hi', hJ⟩ := key J
    rw [hI, hJ, show i = i' by omega]
  · rw [idealCount, Nat.card_eq_zero]
    left
    refine ⟨fun I ↦ ?_⟩
    obtain ⟨i, hi, -⟩ := key I
    exact hk ⟨i, by omega⟩

/-- `I = (I + A)(I + B)` when `A + B = 1` and `AB ⊆ I`. -/
theorem eq_sup_mul_sup {I A B : Ideal (𝓞 K)} (hAB : A ⊔ B = ⊤) (h : A * B ≤ I) :
    I = (I ⊔ A) * (I ⊔ B) := by
  refine le_antisymm ?_ ?_
  · calc I = I * (A ⊔ B) := by rw [hAB, Ideal.mul_top]
      _ = I * A ⊔ I * B := Ideal.mul_sup _ _ _
      _ ≤ (I ⊔ A) * (I ⊔ B) := sup_le
          (by rw [mul_comm]; exact mul_mono le_sup_right le_sup_left)
          (mul_mono le_sup_left le_sup_right)
  · rw [Ideal.sup_mul, Ideal.mul_sup, Ideal.mul_sup]
    exact sup_le (sup_le Ideal.mul_le_left Ideal.mul_le_left) (sup_le Ideal.mul_le_right h)

/-- **Split**: `k + 1` ideals of norm `p^k`. -/
theorem idealCount_split {P Q : Ideal (𝓞 K)} {p : ℕ} (hp : p.Prime) (hP : P.IsPrime)
    (hQ : Q.IsPrime) (hPQ : P ≠ Q) (hPn : absNorm P = p) (hQn : absNorm Q = p)
    (hspan : span {(p : 𝓞 K)} = P * Q) (k : ℕ) :
    idealCount K (p ^ k) = k + 1 := by
  have hP0 := ne_bot_of_absNorm_eq hp hPn
  have hQ0 := ne_bot_of_absNorm_eq hp hQn
  have hPm : P.IsMaximal := hP.isMaximal hP0
  have hQm : Q.IsMaximal := hQ.isMaximal hQ0
  have hcop : P ⊔ Q = ⊤ := by
    by_contra hne
    have h1 : P ⊔ Q = P := (hPm.eq_of_le hne le_sup_left).symm
    have h2 : P ⊔ Q = Q := (hQm.eq_of_le hne le_sup_right).symm
    exact hPQ (h1.symm.trans h2)
  have hcopk : P ^ k ⊔ Q ^ k = ⊤ :=
    isCoprime_iff_sup_eq.mp ((isCoprime_iff_sup_eq.mpr hcop).pow)
  let f : Fin (k + 1) → Ideal (𝓞 K) := fun i ↦ P ^ (i : ℕ) * Q ^ (k - i)
  have hf : Function.Injective f := by
    have aux : ∀ i j : ℕ, i < j → j ≤ k → P ^ i * Q ^ (k - i) ≠ P ^ j * Q ^ (k - j) := by
      intro i j hij hjk h
      have hPi : P ^ i ≠ 0 := pow_ne_zero _ hP0
      have : Q ^ (k - i) = P ^ (j - i) * Q ^ (k - j) := by
        apply mul_left_cancel₀ hPi
        rw [h, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hij.le]
      have hdvd : P ∣ Q ^ (k - i) := by
        rw [this]
        exact dvd_mul_of_dvd_left (dvd_pow_self P (by omega)) _
      have hPQ' : P ∣ Q := (Ideal.prime_of_isPrime hP0 hP).dvd_of_dvd_pow hdvd
      rw [Ideal.dvd_iff_le] at hPQ'
      exact hPQ (hQm.eq_of_le hPm.ne_top hPQ').symm
    intro i j h
    rcases lt_trichotomy (i : ℕ) j with hij | hij | hij
    · exact absurd h (aux i j hij (by omega))
    · exact Fin.ext hij
    · exact absurd h.symm (aux j i hij (by omega))
  have hrange : ∀ I : Ideal (𝓞 K), absNorm I = p ^ k ↔ I ∈ Set.range f := by
    intro I
    constructor
    · intro hI
      have hle : P ^ k * Q ^ k ≤ I := by
        rw [← mul_pow, ← hspan, ← Ideal.dvd_iff_le]; exact dvd_span_pow hI
      have hI' := eq_sup_mul_sup hcopk hle
      obtain ⟨i, hi, hiI⟩ := eq_pow_of_dvd_pow hP hP0
        (Ideal.dvd_iff_le.mpr (le_sup_right : P ^ k ≤ I ⊔ P ^ k))
      obtain ⟨j, hj, hjI⟩ := eq_pow_of_dvd_pow hQ hQ0
        (Ideal.dvd_iff_le.mpr (le_sup_right : Q ^ k ≤ I ⊔ Q ^ k))
      rw [hiI, hjI] at hI'
      have hn : absNorm I = p ^ (i + j) := by
        rw [hI', map_mul, map_pow, map_pow, hPn, hQn, pow_add]
      rw [hI, ] at hn
      have hij := pow_injective hp hn
      refine ⟨⟨i, by omega⟩, ?_⟩
      simp only [f]
      rw [hI', show k - i = j by omega]
    · rintro ⟨i, rfl⟩
      simp only [f]
      rw [map_mul, map_pow, map_pow, hPn, hQn, ← pow_add, Nat.add_sub_cancel' (by omega)]
  rw [idealCount]
  calc Nat.card {I : Ideal (𝓞 K) // absNorm I = p ^ k} = Nat.card (Set.range f) :=
        Nat.card_congr (Equiv.subtypeEquivRight hrange)
    _ = Nat.card (Fin (k + 1)) := Nat.card_range_of_injective hf
    _ = k + 1 := Nat.card_fin _

/-! ### The ideal count -/

variable (K) in
/-- `a_K` as a complex arithmetic function. -/
def idealCountFun : ArithmeticFunction ℂ :=
  ⟨fun n ↦ if n = 0 then 0 else (idealCount K n : ℂ), by simp⟩

theorem idealCountFun_apply {n : ℕ} (hn : n ≠ 0) : idealCountFun K n = idealCount K n := by
  simp [idealCountFun, hn]

theorem isMultiplicative_idealCountFun : (idealCountFun K).IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  refine ⟨by rw [idealCountFun_apply one_ne_zero, idealCount_one, Nat.cast_one], ?_⟩
  intro m n hm hn hmn
  rw [idealCountFun_apply (mul_ne_zero hm hn), idealCountFun_apply hm, idealCountFun_apply hn,
    idealCount_mul hmn hm hn, Nat.cast_mul]

/-- `∑_{i ≤ k} (D/p)^i` at a prime power. -/
theorem zetaMul_prime_pow {N : ℕ} (χ : DirichletCharacter ℂ N) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    χ.zetaMul (p ^ k) = ∑ i ∈ Finset.range (k + 1), χ p ^ i := by
  rw [DirichletCharacter.zetaMul, ArithmeticFunction.coe_zeta_mul_apply,
    Nat.sum_divisors_prime_pow hp]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← χ.apply_eq_toArithmeticFunction_apply (pow_ne_zero _ hp.ne_zero), Nat.cast_pow, map_pow]

/-- **The ideal count of a quadratic field** (Davenport §6, p. 52): for `n ≥ 1`, the number of
ideals of `𝓞 K` of norm `n` is `∑_{m ∣ n} (d_K/m)`. -/
theorem card_absNorm_eq (hK : finrank ℚ K = 2) {n : ℕ} (hn : n ≠ 0) :
    (Nat.card {I : Ideal (𝓞 K) // absNorm I = n} : ℂ) =
      ∑ m ∈ n.divisors, kroneckerChar (discr K) m := by
  set χ := kroneckerChar (discr K)
  have hfun : idealCountFun K = χ.zetaMul := by
    refine (ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers _
      isMultiplicative_idealCountFun _ χ.isMultiplicative_zetaMul).mpr fun p k hp ↦ ?_
    rw [idealCountFun_apply (pow_ne_zero _ hp.ne_zero), zetaMul_prime_pow χ hp]
    obtain ⟨hD, -, -⟩ := isFundamental_discr K hK
    rcases kroneckerChar_prime_eq hD hp with h | h | h
    · obtain ⟨P, hP, hPn, hspan⟩ :=
        exists_ramified hK hp (dvd_discr_of_kroneckerChar_eq_zero hK hp h)
      rw [idealCount_ramified hp hP hPn hspan, h, Finset.sum_range_succ', pow_zero]
      simp
    · obtain ⟨P, Q, hP, hQ, hPQ, hPn, hQn, hspan⟩ := exists_split hK hp h
      rw [idealCount_split hp hP hQ hPQ hPn hQn hspan, h]
      simp
    · obtain ⟨hP, hPn⟩ := isPrime_of_inert hK hp h
      rw [idealCount_inert hp hP hPn, h, neg_one_geom_sum]
      by_cases hk : Even k
      · rw [if_pos hk, if_neg (by rw [Nat.even_add_one]; exact not_not.mpr hk)]; simp
      · rw [if_neg hk, if_pos (by rw [Nat.even_add_one]; exact hk)]; simp
  have := congrArg (fun f : ArithmeticFunction ℂ ↦ f n) hfun
  simp only [idealCountFun_apply hn] at this
  rw [← idealCount, this, DirichletCharacter.zetaMul, ArithmeticFunction.coe_zeta_mul_apply]
  refine Finset.sum_congr rfl fun m hm ↦ ?_
  rw [χ.apply_eq_toArithmeticFunction_apply (Nat.pos_of_mem_divisors hm).ne']

end NTKB.QuadraticField
