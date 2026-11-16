/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Elementary.QuadraticField.Classification
import NTKB.Elementary.QuadraticField.KroneckerPrime
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.NumberTheory.NumberField.Basic

/-!
# The decomposition law in a quadratic number field

Let `K` be a quadratic number field of discriminant `D` and `𝓞 K = ℤ[ω]`,
`ω² = D / 4 + (D % 4) ω` (`NTKB.QuadraticField.nonempty_ringEquiv_order`); put
`f(t) = t² - (D % 4) t - D / 4`. For a prime `p` (`2` included) and an integer `t` with
`f(t) ≡ 0 (mod p)`, the ideal `𝔭_t = (p, ω - t)` (`NTKB.QuadraticField.primeOver`) is a prime of
norm `p` (it lies in the kernel of `ℤ[ω] → ℤ/p`, `ω ↦ t`, and is not `(p)`). Then:

* `p ∣ D` (`(D/p) = 0`): `f` has a double root `t`, and `(p) = 𝔭_t²` (ramified);
* `(D/p) = 1`: `f` has two distinct roots `t`, `t' = D % 4 - t`, and `(p) = 𝔭_t 𝔭_t'`,
  `𝔭_t ≠ 𝔭_t'` (split);
* `(D/p) = -1`: `f` has no root and `(p)` is prime, of norm `p²` (inert): a prime of norm `p`
  above `p` would give a root of `f` in `𝓞 K / 𝔭 ≅ ℤ/p`.

This is Ireland–Rosen, Propositions 13.1.3 (odd `p`) and 13.1.4 (`p = 2`), and Davenport §5,
p. 41 (row 5-18), stated with the Kronecker symbol `(D/p)` (`NTKB.kroneckerChar`).
-/

noncomputable section

set_option linter.unusedSectionVars false

open QuadraticAlgebra NumberField Module Ideal

namespace NTKB.QuadraticField

variable {K : Type*} [Field K] [NumberField K] {D : ℤ}

/-! ### Generalities on ideals of `𝓞 K` -/

/-- An ideal containing `I` with the same nonzero norm is `I`. -/
theorem eq_of_le_of_absNorm_eq {I J : Ideal (𝓞 K)} (h : I ≤ J) (hn : absNorm I = absNorm J)
    (h0 : absNorm I ≠ 0) : I = J := by
  obtain ⟨C, hC⟩ := (Ideal.dvd_iff_le).mpr h
  have hC1 : absNorm C = 1 := by
    have := congrArg absNorm hC
    rw [map_mul, ← hn] at this
    exact (Nat.mul_eq_left h0).mp this.symm
  rw [absNorm_eq_one_iff] at hC1
  rw [hC, hC1, Ideal.mul_top]

/-- An ideal `≠ ⊤` containing the prime `p` contains no integer prime to `p`. -/
theorem dvd_of_intCast_mem {P : Ideal (𝓞 K)} (hP : P ≠ ⊤) {p : ℕ} (hp : p.Prime)
    (hpP : (p : 𝓞 K) ∈ P) {m : ℤ} (hm : (m : 𝓞 K) ∈ P) : (p : ℤ) ∣ m := by
  by_contra hnd
  obtain ⟨u, v, huv⟩ :=
    (Prime.coprime_iff_not_dvd (Nat.prime_iff_prime_int.mp hp)).mpr hnd
  apply hP
  rw [eq_top_iff_one]
  have : ((u * p + v * m : ℤ) : 𝓞 K) ∈ P := by
    push_cast
    exact add_mem (mul_mem_left _ _ (by exact_mod_cast hpP)) (mul_mem_left _ _ hm)
  rwa [huv, Int.cast_one] at this

section order

variable (e : Order D ≃+* 𝓞 K)

/-- The generator `ω` of `𝓞 K`. -/
def gen : 𝓞 K := e ω

theorem order_omega_mul_omega :
    (ω * ω : Order D) = ((D / 4 : ℤ) : Order D) + ((D % 4 : ℤ) : Order D) * ω := by
  ext <;> simp

theorem gen_mul_gen :
    gen e * gen e = ((D / 4 : ℤ) : 𝓞 K) + ((D % 4 : ℤ) : 𝓞 K) * gen e := by
  rw [gen, ← map_mul, order_omega_mul_omega, map_add, map_mul, map_intCast, map_intCast]

theorem finrank_int (e : Order D ≃+* 𝓞 K) : finrank ℤ (𝓞 K) = 2 :=
  (LinearEquiv.finrank_eq e.toIntAlgEquiv.toLinearEquiv).symm.trans (finrank_eq_two _ _)

theorem absNorm_span_natCast' (e : Order D ≃+* 𝓞 K) (n : ℕ) : absNorm (span {(n : 𝓞 K)}) = n ^ 2 := by
  rw [absNorm_span_natCast, finrank_int e]

/-- `ω - t` is not divisible by `p > 1`. -/
theorem gen_sub_notMem (t : ℤ) {p : ℕ} (hp : 1 < p) :
    gen e - (t : 𝓞 K) ∉ span {(p : 𝓞 K)} := by
  rw [mem_span_singleton']
  rintro ⟨y, hy⟩
  have h := congrArg (fun z ↦ (e.symm z).im) hy
  simp only [map_mul, map_natCast, gen, map_sub, map_intCast, RingEquiv.symm_apply_apply,
    im_mul, re_natCast, im_natCast, im_sub, im_omega, im_intCast] at h
  have h' : (e.symm y).im * (p : ℤ) = 1 := by linear_combination h
  rcases Int.eq_one_or_neg_one_of_mul_eq_one' h' with ⟨-, h1⟩ | ⟨-, h1⟩ <;> omega

/-- The ring homomorphism `𝓞 K → ℤ/p`, `ω ↦ t`, for a root `t` of `f` modulo `p`. -/
def toZMod {p : ℕ} (t : ℤ) (ht : (p : ℤ) ∣ minpolyAt D t) : 𝓞 K →+* ZMod p :=
  ((lift ⟨(t : ZMod p), by
      have h0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr ht
      rw [minpolyAt_cast] at h0
      rw [zsmul_eq_mul, zsmul_eq_mul, mul_one]
      linear_combination h0⟩ : Order D →ₐ[ℤ] ZMod p) : Order D →+* ZMod p).comp
    e.symm.toRingHom

theorem toZMod_gen {p : ℕ} (t : ℤ) (ht : (p : ℤ) ∣ minpolyAt D t) :
    toZMod e t ht (gen e) = t := by
  simp [toZMod, gen]

/-- The ideal `𝔭_t = (p, ω - t)`. -/
def primeOver (p : ℕ) (t : ℤ) : Ideal (𝓞 K) := span {(p : 𝓞 K), gen e - (t : 𝓞 K)}

variable {e}

theorem span_le_primeOver (p : ℕ) (t : ℤ) : span {(p : 𝓞 K)} ≤ primeOver e p t :=
  span_mono (Set.singleton_subset_iff.mpr (Set.mem_insert _ _))

theorem natCast_mem_primeOver (p : ℕ) (t : ℤ) : (p : 𝓞 K) ∈ primeOver e p t :=
  subset_span (Set.mem_insert _ _)

theorem gen_sub_mem_primeOver (p : ℕ) (t : ℤ) : gen e - (t : 𝓞 K) ∈ primeOver e p t :=
  subset_span (Set.mem_insert_of_mem _ rfl)

variable {p : ℕ} {t : ℤ}

theorem primeOver_ne_top (hp : p.Prime) (ht : (p : ℤ) ∣ minpolyAt D t) :
    primeOver e p t ≠ ⊤ := by
  have : Fact p.Prime := ⟨hp⟩
  intro h
  have hle : primeOver e p t ≤ RingHom.ker (toZMod e t ht) := by
    rw [primeOver, span_le]
    intro x hx
    rcases hx with rfl | rfl
    · simp
    · simp [toZMod_gen]
  rw [h, top_le_iff] at hle
  exact RingHom.ker_ne_top _ hle

theorem primeOver_ne_span (hp : p.Prime) : primeOver e p t ≠ span {(p : 𝓞 K)} := fun h ↦
  gen_sub_notMem e t hp.one_lt (h ▸ gen_sub_mem_primeOver p t)

/-- `𝔭_t` has norm `p`. -/
theorem absNorm_primeOver (hp : p.Prime) (ht : (p : ℤ) ∣ minpolyAt D t) :
    absNorm (primeOver e p t) = p := by
  have hdvd : absNorm (primeOver e p t) ∣ p ^ 2 := by
    rw [← absNorm_span_natCast' e]
    exact absNorm_dvd_absNorm_of_le (span_le_primeOver p t)
  obtain ⟨i, hi, hEq⟩ := (Nat.dvd_prime_pow hp).mp hdvd
  interval_cases i
  · rw [pow_zero, absNorm_eq_one_iff] at hEq
    exact absurd hEq (primeOver_ne_top hp ht)
  · simpa using hEq
  · exfalso
    refine primeOver_ne_span (e := e) hp
      (eq_of_le_of_absNorm_eq (span_le_primeOver (e := e) p t) ?_ ?_).symm
    · rw [hEq, absNorm_span_natCast' e]
    · rw [absNorm_span_natCast' e]; exact pow_ne_zero _ hp.ne_zero

theorem isPrime_primeOver (hp : p.Prime) (ht : (p : ℤ) ∣ minpolyAt D t) :
    (primeOver e p t).IsPrime :=
  isPrime_of_irreducible_absNorm (by
    rw [absNorm_primeOver hp ht]; exact hp.prime.irreducible)

/-- **Ramified primes**: for a double root `t`, `(p) = 𝔭_t²`. -/
theorem primeOver_sq (hp : p.Prime) (ht : (p : ℤ) ∣ minpolyAt D t)
    (ht2 : (p : ℤ) ∣ 2 * t - D % 4) : primeOver e p t ^ 2 = span {(p : 𝓞 K)} := by
  have hle : primeOver e p t ^ 2 ≤ span {(p : 𝓞 K)} := by
    obtain ⟨u, hu⟩ := ht2
    obtain ⟨v, hv⟩ := ht
    rw [pow_two, primeOver, span_pair_mul_span_pair, span_le]
    simp only [Set.insert_subset_iff, Set.singleton_subset_iff, SetLike.mem_coe,
      mem_span_singleton]
    refine ⟨dvd_mul_right _ _, dvd_mul_right _ _, dvd_mul_left _ _,
      ⟨-(u : 𝓞 K) * gen e + (t : 𝓞 K) * u - v, ?_⟩⟩
    have hu' : (2 : 𝓞 K) * t - ((D % 4 : ℤ) : 𝓞 K) = p * u := by exact_mod_cast hu
    have hv' : (t : 𝓞 K) * t - ((D % 4 : ℤ) : 𝓞 K) * t - ((D / 4 : ℤ) : 𝓞 K) = p * v := by
      have := congrArg (Int.cast : ℤ → 𝓞 K) hv
      unfold minpolyAt at this
      push_cast at this
      exact this
    linear_combination gen_mul_gen e - (gen e - t) * hu' - hv'
  refine eq_of_le_of_absNorm_eq hle ?_ ?_
  · rw [map_pow, absNorm_primeOver hp ht, absNorm_span_natCast' e]
  · rw [map_pow, absNorm_primeOver hp ht]; exact pow_ne_zero _ hp.ne_zero

theorem minpolyAt_conj (t : ℤ) : minpolyAt D (D % 4 - t) = minpolyAt D t := by
  unfold minpolyAt; ring

/-- **Split primes**: `(p) = 𝔭_t 𝔭_t'` with `t' = D % 4 - t`. -/
theorem primeOver_mul_primeOver (hp : p.Prime) (ht : (p : ℤ) ∣ minpolyAt D t) :
    primeOver e p t * primeOver e p (D % 4 - t) = span {(p : 𝓞 K)} := by
  have ht' : (p : ℤ) ∣ minpolyAt D (D % 4 - t) := by rwa [minpolyAt_conj]
  have hle : primeOver e p t * primeOver e p (D % 4 - t) ≤ span {(p : 𝓞 K)} := by
    obtain ⟨v, hv⟩ := ht
    rw [primeOver, primeOver, span_pair_mul_span_pair, span_le]
    simp only [Set.insert_subset_iff, Set.singleton_subset_iff, SetLike.mem_coe,
      mem_span_singleton]
    refine ⟨dvd_mul_right _ _, dvd_mul_right _ _, dvd_mul_left _ _, ⟨-(v : 𝓞 K), ?_⟩⟩
    have hv' : (t : 𝓞 K) * t - ((D % 4 : ℤ) : 𝓞 K) * t - ((D / 4 : ℤ) : 𝓞 K) = p * v := by
      have := congrArg (Int.cast : ℤ → 𝓞 K) hv
      unfold minpolyAt at this
      push_cast at this
      exact this
    push_cast
    linear_combination gen_mul_gen e - hv'
  refine eq_of_le_of_absNorm_eq hle ?_ ?_
  · rw [map_mul, absNorm_primeOver hp ht, absNorm_primeOver hp ht', absNorm_span_natCast' e, sq]
  · rw [map_mul, absNorm_primeOver hp ht, absNorm_primeOver hp ht']
    exact mul_ne_zero hp.ne_zero hp.ne_zero

/-- For a simple root `t`, `𝔭_t ≠ 𝔭_t'`. -/
theorem primeOver_ne_primeOver (hp : p.Prime) (ht : (p : ℤ) ∣ minpolyAt D t)
    (ht2 : ¬ (p : ℤ) ∣ 2 * t - D % 4) : primeOver e p t ≠ primeOver e p (D % 4 - t) := by
  intro h
  have h1 := gen_sub_mem_primeOver (e := e) p t
  have h2 := gen_sub_mem_primeOver (e := e) p (D % 4 - t)
  rw [← h] at h2
  have h3 : ((2 * t - D % 4 : ℤ) : 𝓞 K) ∈ primeOver e p t := by
    have := sub_mem h2 h1
    convert this using 1
    push_cast; ring
  exact ht2 (dvd_of_intCast_mem (primeOver_ne_top hp ht) hp (natCast_mem_primeOver p t) h3)

/-- A maximal ideal of norm `p` gives a root of `f` modulo `p`. -/
theorem exists_root_of_absNorm_eq (e : Order D ≃+* 𝓞 K) (hp : p.Prime) {P : Ideal (𝓞 K)} [hPm : P.IsMaximal]
    (hP : absNorm P = p) : ∃ t : ℤ, (p : ℤ) ∣ minpolyAt D t := by
  have : Fact p.Prime := ⟨hp⟩
  have hfin : Finite (𝓞 K ⧸ P) := (absNorm_ne_zero_iff P).mp (by rw [hP]; exact hp.ne_zero)
  let _ : Fintype (𝓞 K ⧸ P) := Fintype.ofFinite _
  have hcard : Fintype.card (𝓞 K ⧸ P) = p := by
    rw [Fintype.card_eq_nat_card, ← hP, absNorm_apply, Submodule.cardQuot_apply]
  have : CharP (𝓞 K ⧸ P) p := charP_of_card_eq_prime hcard
  let φ : ZMod p ≃+* 𝓞 K ⧸ P := ZMod.ringEquiv _ hcard
  obtain ⟨t, htx⟩ := exists_intCast_eq (φ.symm (Ideal.Quotient.mk P (gen e)))
  have hmem : gen e - (t : 𝓞 K) ∈ P := by
    rw [← Ideal.Quotient.eq, map_intCast, ← map_intCast φ, htx, RingEquiv.apply_symm_apply]
  refine ⟨t, dvd_of_intCast_mem hPm.ne_top hp ?_ ?_⟩
  · rw [← hP]; exact absNorm_mem P
  · have : ((minpolyAt D t : ℤ) : 𝓞 K) =
        -(gen e - t) * ((t : 𝓞 K) - ((D % 4 : ℤ) : 𝓞 K) + gen e) := by
      unfold minpolyAt; push_cast
      linear_combination gen_mul_gen e
    rw [this]
    exact mul_mem_right _ _ (neg_mem hmem)

/-- **Inert primes**: if `f` has no root modulo `p`, then `(p)` is prime. -/
theorem isPrime_span_of_forall (e : Order D ≃+* 𝓞 K) (hp : p.Prime) (h : ∀ t : ℤ, ¬ (p : ℤ) ∣ minpolyAt D t) :
    (span {(p : 𝓞 K)}).IsPrime := by
  have hne : span {(p : 𝓞 K)} ≠ ⊤ := by
    intro h
    have := congrArg absNorm h
    rw [absNorm_top, absNorm_span_natCast' e] at this
    exact (Nat.one_lt_pow two_ne_zero hp.one_lt).ne' this
  obtain ⟨P, hPm, hle⟩ := exists_le_maximal _ hne
  have hdvd : absNorm P ∣ p ^ 2 := by
    rw [← absNorm_span_natCast' e]; exact absNorm_dvd_absNorm_of_le hle
  obtain ⟨i, hi, hEq⟩ := (Nat.dvd_prime_pow hp).mp hdvd
  interval_cases i
  · rw [pow_zero, absNorm_eq_one_iff] at hEq; exact absurd hEq hPm.ne_top
  · obtain ⟨t, ht⟩ := exists_root_of_absNorm_eq e hp (by simpa using hEq)
    exact absurd ht (h t)
  · have : span {(p : 𝓞 K)} = P := eq_of_le_of_absNorm_eq hle
      (by rw [hEq, absNorm_span_natCast' e])
      (by rw [absNorm_span_natCast' e]; exact pow_ne_zero _ hp.ne_zero)
    rw [this]; exact hPm.isPrime

end order

/-! ### The decomposition law with the Kronecker symbol -/

section field

variable (K)

/-- The three cases of a prime `p` in a quadratic field of fundamental discriminant `D`. -/
theorem kroneckerChar_prime_cases (hD : IsFundamentalDiscriminant D) {p : ℕ} (hp : p.Prime) :
    ((p : ℤ) ∣ D ∧ kroneckerChar D p = 0) ∨
    (¬ (p : ℤ) ∣ D ∧ (∃ t : ℤ, (p : ℤ) ∣ minpolyAt D t) ∧ kroneckerChar D p = 1) ∨
    (¬ (p : ℤ) ∣ D ∧ (∀ t : ℤ, ¬ (p : ℤ) ∣ minpolyAt D t) ∧ kroneckerChar D p = -1) := by
  by_cases hpD : (p : ℤ) ∣ D
  · exact Or.inl ⟨hpD, kroneckerChar_eq_zero_of_dvd hp hpD⟩
  · by_cases hr : ∃ t : ℤ, (p : ℤ) ∣ minpolyAt D t
    · obtain ⟨t, ht⟩ := hr
      exact Or.inr (Or.inl ⟨hpD, ⟨t, ht⟩, kroneckerChar_eq_one_of_root hD hp hpD ht⟩)
    · push Not at hr
      exact Or.inr (Or.inr ⟨hpD, hr, kroneckerChar_eq_neg_one_of_forall hD hp hpD hr⟩)

/-- At a prime, the Kronecker symbol of a fundamental discriminant is `0`, `1` or `-1`. -/
theorem kroneckerChar_prime_eq (hD : IsFundamentalDiscriminant D) {p : ℕ} (hp : p.Prime) :
    kroneckerChar D p = 0 ∨ kroneckerChar D p = 1 ∨ kroneckerChar D p = -1 := by
  rcases kroneckerChar_prime_cases hD hp with ⟨-, h⟩ | ⟨-, -, h⟩ | ⟨-, -, h⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

variable {K}

/-- **Split primes** (Ireland–Rosen 13.1.3 (a), 13.1.4 (a); Davenport §5, p. 41): if
`(d_K/p) = 1` then `(p) = 𝔭 𝔭'` with `𝔭 ≠ 𝔭'` primes of norm `p`. -/
theorem exists_split (hK : finrank ℚ K = 2) {p : ℕ} (hp : p.Prime)
    (hχ : kroneckerChar (discr K) p = 1) :
    ∃ P Q : Ideal (𝓞 K), P.IsPrime ∧ Q.IsPrime ∧ P ≠ Q ∧ absNorm P = p ∧ absNorm Q = p ∧
      span {(p : 𝓞 K)} = P * Q := by
  obtain ⟨hD, -, -⟩ := isFundamental_discr K hK
  obtain ⟨e⟩ := nonempty_ringEquiv_order K hK
  rcases kroneckerChar_prime_cases hD hp with ⟨-, h⟩ | ⟨hpD, ⟨t, ht⟩, -⟩ | ⟨-, -, h⟩
  · rw [h] at hχ; exact absurd hχ zero_ne_one
  · have ht' : (p : ℤ) ∣ minpolyAt (discr K) (discr K % 4 - t) := by rwa [minpolyAt_conj]
    exact ⟨primeOver e p t, primeOver e p (discr K % 4 - t), isPrime_primeOver hp ht,
      isPrime_primeOver hp ht',
      primeOver_ne_primeOver hp ht (not_dvd_two_mul_sub_of_root (emod_four_of_isFundamental hD)
        hpD ht), absNorm_primeOver hp ht, absNorm_primeOver hp ht',
      (primeOver_mul_primeOver hp ht).symm⟩
  · rw [h] at hχ; norm_num at hχ

/-- **Inert primes** (Ireland–Rosen 13.1.3 (b), 13.1.4 (b)): if `(d_K/p) = -1` then `(p)` is
prime, of norm `p²`. -/
theorem isPrime_of_inert (hK : finrank ℚ K = 2) {p : ℕ} (hp : p.Prime)
    (hχ : kroneckerChar (discr K) p = -1) :
    (span {(p : 𝓞 K)}).IsPrime ∧ absNorm (span {(p : 𝓞 K)}) = p ^ 2 := by
  obtain ⟨hD, -, -⟩ := isFundamental_discr K hK
  obtain ⟨e⟩ := nonempty_ringEquiv_order K hK
  rcases kroneckerChar_prime_cases hD hp with ⟨-, h⟩ | ⟨-, -, h⟩ | ⟨-, hr, -⟩
  · rw [h] at hχ; norm_num at hχ
  · rw [h] at hχ; norm_num at hχ
  · exact ⟨isPrime_span_of_forall e hp hr, absNorm_span_natCast' e p⟩

/-- **Ramified primes** (Ireland–Rosen 13.1.3 (c), 13.1.4 (c)): if `p ∣ d_K` (equivalently
`(d_K/p) = 0`) then `(p) = 𝔭²`, `𝔭` a prime of norm `p`. -/
theorem exists_ramified (hK : finrank ℚ K = 2) {p : ℕ} (hp : p.Prime)
    (hpD : (p : ℤ) ∣ discr K) :
    ∃ P : Ideal (𝓞 K), P.IsPrime ∧ absNorm P = p ∧ span {(p : 𝓞 K)} = P ^ 2 := by
  obtain ⟨hD, -, -⟩ := isFundamental_discr K hK
  obtain ⟨e⟩ := nonempty_ringEquiv_order K hK
  obtain ⟨t, ht, ht2⟩ := exists_double_root_of_dvd hD hp hpD
  exact ⟨primeOver e p t, isPrime_primeOver hp ht, absNorm_primeOver hp ht,
    (primeOver_sq hp ht ht2).symm⟩

theorem dvd_discr_of_kroneckerChar_eq_zero (hK : finrank ℚ K = 2) {p : ℕ} (hp : p.Prime)
    (hχ : kroneckerChar (discr K) p = 0) : (p : ℤ) ∣ discr K := by
  obtain ⟨hD, -, -⟩ := isFundamental_discr K hK
  rcases kroneckerChar_prime_cases hD hp with ⟨h, -⟩ | ⟨-, -, h⟩ | ⟨-, -, h⟩
  · exact h
  · rw [h] at hχ; norm_num at hχ
  · rw [h] at hχ; norm_num at hχ

end field

end NTKB.QuadraticField
