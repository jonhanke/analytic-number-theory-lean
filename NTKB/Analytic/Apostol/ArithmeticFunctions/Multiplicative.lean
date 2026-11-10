/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.ArithmeticFunction.Liouville
import Mathlib.Data.Finset.NatDivisors
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import NTKB.Attr

/-!
# Multiplicative functions and Dirichlet inverses (Apostol, Chapter 2, §§2.10–2.13)

Mathlib proves that the Dirichlet product of multiplicative functions is multiplicative
(`ArithmeticFunction.IsMultiplicative.mul`, Apostol's Theorem 2.14). This file adds:

* Theorem 2.15: if `g` and `f * g` are multiplicative, so is `f` (Apostol's minimal
  counterexample argument, as a strong induction on `m n`);
* Theorem 2.16: the Dirichlet inverse of a multiplicative function is multiplicative;
* the notion of a completely multiplicative arithmetical function (Mathlib has none for
  `ArithmeticFunction`) and Theorem 2.17: a multiplicative `f` is completely multiplicative iff
  `f⁻¹ = μ f`;
* Theorem 2.19: `∑_{d ∣ n} λ(d)` is the indicator of the squares, and `λ⁻¹ = |μ| = μ²`;
* Theorem 2.20: `σ_α⁻¹(n) = ∑_{d ∣ n} d^α μ(d) μ(n/d)` for complex `α`.
-/

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta ArithmeticFunction.sigma

namespace NTKB.Apostol

variable {R : Type*}

/-! ## Dirichlet products over coprime factors -/

/-- For coprime `m, n`, a sum over the divisors of `mn` is a double sum over the divisors of `m`
and `n` (every divisor of `mn` is uniquely `ab` with `a ∣ m`, `b ∣ n`). -/
theorem sum_divisors_mul_of_coprime {M : Type*} [AddCommMonoid M] {m n : ℕ} (hmn : m.Coprime n)
    (F : ℕ → M) :
    ∑ d ∈ (m * n).divisors, F d = ∑ p ∈ m.divisors ×ˢ n.divisors, F (p.1 * p.2) := by
  rw [Nat.Coprime.divisors_mul hmn, sum_map]
  exact sum_attach (m.divisors ×ˢ n.divisors) (fun p ↦ F (p.1 * p.2))

/-- `(f * g)(n) = ∑_{d ∣ n} f(d) g(n/d)`. -/
theorem mul_apply_eq_sum_divisors [Semiring R] (f g : ArithmeticFunction R) (n : ℕ) :
    (f * g) n = ∑ d ∈ n.divisors, f d * g (n / d) := by
  rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal (fun x y ↦ f x * g y)]

/-- **Apostol, Theorem 2.15.** If both `g` and `f * g` are multiplicative, then `f` is
multiplicative. -/
@[kb "apostol1976" "Thm 2.15, p. 35"]
theorem isMultiplicative_of_isMultiplicative_mul [CommRing R] {f g : ArithmeticFunction R}
    (hg : g.IsMultiplicative) (hfg : (f * g).IsMultiplicative) : f.IsMultiplicative := by
  -- `h(1) = f(1) g(1) = f(1)`
  have h1 : f 1 = 1 := by
    have := hfg.map_one
    rwa [mul_apply_one, hg.map_one, mul_one] at this
  refine IsMultiplicative.iff_ne_zero.2 ⟨h1, ?_⟩
  -- strong induction on the product `mn`
  suffices H : ∀ k m n : ℕ, m * n = k → m ≠ 0 → n ≠ 0 → m.Coprime n → f (m * n) = f m * f n by
    intro m n hm hn hmn
    exact H _ m n rfl hm hn hmn
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro m n hk hm hn hmn
  -- the terms of `h(mn)` with `(a, b) ≠ (m, n)` have `ab < mn`
  set T : ℕ × ℕ → R := fun p ↦ f (p.1 * p.2) * g (m / p.1 * (n / p.2)) with hT
  set U : ℕ × ℕ → R := fun p ↦ f p.1 * f p.2 * g (m / p.1 * (n / p.2)) with hU
  have hmem : (m, n) ∈ m.divisors ×ˢ n.divisors := by simp [hm, hn]
  have hsum_h : (f * g) (m * n) = ∑ p ∈ m.divisors ×ˢ n.divisors, T p := by
    rw [mul_apply_eq_sum_divisors, sum_divisors_mul_of_coprime hmn]
    refine sum_congr rfl fun p hp ↦ ?_
    simp only [mem_product, Nat.mem_divisors] at hp
    simp only [hT]
    rw [Nat.div_mul_div_comm hp.1.1 hp.2.1]
  have hsum_hh : (f * g) m * (f * g) n = ∑ p ∈ m.divisors ×ˢ n.divisors, U p := by
    rw [mul_apply_eq_sum_divisors, mul_apply_eq_sum_divisors, sum_mul_sum, sum_product]
    refine sum_congr rfl fun a ha ↦ sum_congr rfl fun b hb ↦ ?_
    simp only [Nat.mem_divisors] at ha hb
    have hcop : (m / a).Coprime (n / b) :=
      (hmn.coprime_dvd_left (Nat.div_dvd_of_dvd ha.1)).coprime_dvd_right (Nat.div_dvd_of_dvd hb.1)
    simp only [hU]
    rw [hg.map_mul_of_coprime hcop]
    ring
  have hoff : ∀ p ∈ (m.divisors ×ˢ n.divisors).erase (m, n), T p = U p := by
    intro p hp
    obtain ⟨hne, hp⟩ := mem_erase.1 hp
    simp only [mem_product, Nat.mem_divisors] at hp
    obtain ⟨⟨ha, -⟩, ⟨hb, -⟩⟩ := hp
    have ha0 : p.1 ≠ 0 := fun h ↦ hm (Nat.eq_zero_of_zero_dvd (h ▸ ha))
    have hb0 : p.2 ≠ 0 := fun h ↦ hn (Nat.eq_zero_of_zero_dvd (h ▸ hb))
    have hale : p.1 ≤ m := Nat.le_of_dvd (Nat.pos_of_ne_zero hm) ha
    have hble : p.2 ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hb
    have hlt : p.1 * p.2 < k := by
      rw [← hk]
      rcases lt_or_eq_of_le hale with h | h
      · exact Nat.mul_lt_mul_of_lt_of_le h hble (Nat.pos_of_ne_zero hn)
      · rcases lt_or_eq_of_le hble with h' | h'
        · rw [h]; exact Nat.mul_lt_mul_of_pos_left h' (Nat.pos_of_ne_zero hm)
        · exact absurd (Prod.ext h h') hne
    have hcop : p.1.Coprime p.2 := (hmn.coprime_dvd_left ha).coprime_dvd_right hb
    simp only [hT, hU, ih _ hlt p.1 p.2 rfl ha0 hb0 hcop]
  have hT' := add_sum_erase _ T hmem
  have hU' := add_sum_erase _ U hmem
  rw [sum_congr rfl hoff] at hT'
  have key : T (m, n) = U (m, n) := by
    have e1 := hfg.map_mul_of_coprime hmn
    rw [hsum_h, hsum_hh, ← hT', ← hU'] at e1
    exact add_right_cancel e1
  simpa [hT, hU, Nat.div_self (Nat.pos_of_ne_zero hm), Nat.div_self (Nat.pos_of_ne_zero hn),
    hg.map_one] using key

/-- **Apostol, Theorem 2.16.** If `g` is multiplicative, so is any Dirichlet inverse of `g`. -/
@[kb "apostol1976" "Thm 2.16, p. 36"]
theorem isMultiplicative_of_mul_eq_one [CommRing R] {g g' : ArithmeticFunction R}
    (hg : g.IsMultiplicative) (h : g * g' = 1) : g'.IsMultiplicative :=
  isMultiplicative_of_isMultiplicative_mul hg (by rw [mul_comm, h]; exact isMultiplicative_one)

/-- **Apostol, Theorem 2.16**, for Mathlib's `ArithmeticFunction.dirichletInverse`. -/
@[kb "apostol1976" "Thm 2.16, p. 36"]
theorem isMultiplicative_dirichletInverse [CommRing R] {g : ArithmeticFunction R}
    (hg : g.IsMultiplicative) (hinv : Invertible (g 1)) :
    (dirichletInverse g hinv).IsMultiplicative :=
  isMultiplicative_of_mul_eq_one hg (self_mul_dirichletInverse g hinv)

/-! ## Completely multiplicative functions -/

/-- An arithmetical function is *completely multiplicative* if `f(1) = 1` and
`f(mn) = f(m) f(n)` for all `m, n` (Apostol, §2.9). -/
def IsCompletelyMultiplicative [MonoidWithZero R] (f : ArithmeticFunction R) : Prop :=
  f 1 = 1 ∧ ∀ m n : ℕ, f (m * n) = f m * f n

theorem IsCompletelyMultiplicative.isMultiplicative [MonoidWithZero R]
    {f : ArithmeticFunction R} (hf : IsCompletelyMultiplicative f) : f.IsMultiplicative :=
  ⟨hf.1, fun {m n} _ ↦ hf.2 m n⟩

theorem IsCompletelyMultiplicative.map_pow [MonoidWithZero R] {f : ArithmeticFunction R}
    (hf : IsCompletelyMultiplicative f) (n k : ℕ) : f (n ^ k) = f n ^ k := by
  induction k with
  | zero => simp [hf.1]
  | succ k ih => rw [pow_succ, hf.2, ih, pow_succ]

/-- A multiplicative function is completely multiplicative as soon as `f(p^a) = f(p)^a` for all
primes `p` and all `a`. -/
theorem isCompletelyMultiplicative_of_prime_pow [CommMonoidWithZero R] {f : ArithmeticFunction R}
    (hf : f.IsMultiplicative) (h : ∀ p a : ℕ, p.Prime → f (p ^ a) = f p ^ a) :
    IsCompletelyMultiplicative f := by
  refine ⟨hf.map_one, fun m n ↦ ?_⟩
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  have key : ∀ k : ℕ, k ≠ 0 → f k = k.factorization.prod fun p a ↦ f p ^ a := by
    intro k hk
    rw [hf.multiplicative_factorization f hk]
    refine Finsupp.prod_congr fun p hp ↦ h p _ ?_
    exact Nat.prime_of_mem_primeFactors (by simpa using hp)
  rw [key _ (mul_ne_zero hm hn), key _ hm, key _ hn, Nat.factorization_mul hm hn,
    Finsupp.prod_add_index' (fun _ ↦ pow_zero _) (fun _ _ _ ↦ pow_add _ _ _)]

/-- `(μ f * f)(n) = ∑_{d ∣ n} μ(d) f(d) f(n/d)`, evaluated at a prime power `p^(a+1)`. -/
theorem pmul_moebius_mul_apply_prime_pow_succ [CommRing R] {f : ArithmeticFunction R}
    (hf1 : f 1 = 1) {p : ℕ} (hp : p.Prime) (a : ℕ) :
    ((μ : ArithmeticFunction R).pmul f * f) (p ^ (a + 1)) = f (p ^ (a + 1)) - f p * f (p ^ a) := by
  rw [mul_apply_eq_sum_divisors, Nat.sum_divisors_prime_pow hp, sum_range_succ', sum_range_succ']
  have hz : ∀ i ∈ range a, ((μ : ArithmeticFunction R).pmul f) (p ^ (i + 1 + 1)) *
      f (p ^ (a + 1) / p ^ (i + 1 + 1)) = 0 := by
    intro i _
    rw [pmul_apply, intCoe_apply, moebius_apply_prime_pow hp (by omega)]
    simp
  rw [sum_eq_zero hz, pmul_apply, pmul_apply, intCoe_apply, intCoe_apply, pow_zero,
    moebius_apply_one, pow_one, moebius_apply_prime hp, Nat.div_one]
  rw [show p ^ (a + 1) / p = p ^ a by
    rw [pow_succ, Nat.mul_div_cancel _ hp.pos]]
  push_cast
  rw [hf1]
  ring

/-- `∑_{d ∣ n} μ(d) = [n = 1]`, in any ring. -/
theorem sum_divisors_moebius [Ring R] (n : ℕ) :
    ∑ d ∈ n.divisors, (μ d : R) = (1 : ArithmeticFunction R) n := by
  have := congrArg (fun F : ArithmeticFunction R ↦ F n) (coe_moebius_mul_coe_zeta (R := R))
  simp only [coe_mul_zeta_apply] at this
  exact this

/-- **Apostol, Theorem 2.17.** A multiplicative function `f` is completely multiplicative if and
only if its Dirichlet inverse is `μ f`, i.e. `(μ f) * f = I`. -/
@[kb "apostol1976" "Thm 2.17, p. 36"]
theorem isCompletelyMultiplicative_iff_pmul_moebius_mul_eq_one [CommRing R]
    {f : ArithmeticFunction R} (hf : f.IsMultiplicative) :
    IsCompletelyMultiplicative f ↔ (μ : ArithmeticFunction R).pmul f * f = 1 := by
  constructor
  · intro hc
    ext n
    rw [mul_apply_eq_sum_divisors]
    have hterm : ∀ d ∈ n.divisors, ((μ : ArithmeticFunction R).pmul f) d * f (n / d) =
        (μ d : R) * f n := by
      intro d hd
      rw [pmul_apply, intCoe_apply, mul_assoc, ← hc.2,
        Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)]
    rw [sum_congr rfl hterm, ← sum_mul, sum_divisors_moebius, ArithmeticFunction.one_apply]
    split_ifs with h
    · rw [h, hc.1, one_mul]
    · rw [zero_mul]
  · intro h
    apply isCompletelyMultiplicative_of_prime_pow hf
    intro p a hp
    induction a with
    | zero => simp [hf.map_one]
    | succ a ih =>
      have e := congrArg (fun F : ArithmeticFunction R ↦ F (p ^ (a + 1))) h
      rw [pmul_moebius_mul_apply_prime_pow_succ hf.map_one hp,
        one_apply_ne (Nat.one_lt_pow (by omega) hp.one_lt).ne'] at e
      rw [sub_eq_zero.1 e, ih, pow_succ, mul_comm]

/-- The inverse of `f * u` for completely multiplicative `f` (the argument of Apostol's
Theorem 2.20): `(f * u)⁻¹ = (μ f) * μ`. -/
theorem IsCompletelyMultiplicative.mul_zeta_mul_inv [CommRing R] {f : ArithmeticFunction R}
    (hf : IsCompletelyMultiplicative f) :
    (f * ζ) * ((μ : ArithmeticFunction R).pmul f * μ) = 1 := by
  have h := (isCompletelyMultiplicative_iff_pmul_moebius_mul_eq_one hf.isMultiplicative).1 hf
  calc (f * ζ) * ((μ : ArithmeticFunction R).pmul f * μ)
      = ((μ : ArithmeticFunction R).pmul f * f) * ((ζ : ArithmeticFunction R) * μ) := by ring
    _ = 1 := by rw [h, coe_zeta_mul_coe_moebius, one_mul]

/-! ## Liouville's function (Apostol, §2.12) -/

theorem isCompletelyMultiplicative_liouville : IsCompletelyMultiplicative liouville :=
  ⟨liouville_apply_one, liouville_apply_mul⟩

/-- `∑_{d ∣ p^a} λ(d) = 1` if `a` is even and `0` otherwise. -/
theorem liouville_mul_zeta_apply_prime_pow {p : ℕ} (hp : p.Prime) (a : ℕ) :
    (liouville * ζ) (p ^ a) = if Even a then 1 else 0 := by
  rw [coe_mul_zeta_apply, Nat.sum_divisors_prime_pow hp]
  have : ∀ k ∈ range (a + 1), liouville (p ^ k) = (-1) ^ k := fun k _ ↦ by
    rw [liouville_apply (pow_ne_zero _ hp.ne_zero), cardFactors_apply_prime_pow hp]
  rw [sum_congr rfl this]
  induction a with
  | zero => simp
  | succ a ih =>
    rw [sum_range_succ, ih fun k _ ↦ by
      rw [liouville_apply (pow_ne_zero _ hp.ne_zero), cardFactors_apply_prime_pow hp]]
    rcases Nat.even_or_odd a with h | h
    · have h' : ¬ Even (a + 1) := by rw [Nat.even_add_one]; exact not_not.2 h
      simp [h, h', pow_succ, h.neg_one_pow]
    · have h' : Even (a + 1) := h.add_one
      simp [Nat.not_even_iff_odd.2 h, h', h'.neg_one_pow]

/-- **Apostol, Theorem 2.19**, first part: for `n ≥ 1`, `∑_{d ∣ n} λ(d)` is `1` if `n` is a
square and `0` otherwise. -/
@[kb "apostol1976" "Thm 2.19, p. 38"]
theorem sum_divisors_liouville {n : ℕ} (hn : n ≠ 0) :
    ∑ d ∈ n.divisors, liouville d = if IsSquare n then 1 else 0 := by
  rw [← coe_mul_zeta_apply,
    (isMultiplicative_liouville.mul isMultiplicative_zeta.natCast).multiplicative_factorization _ hn,
    Finsupp.prod, Nat.support_factorization,
    prod_congr rfl fun p hp ↦ liouville_mul_zeta_apply_prime_pow (Nat.prime_of_mem_primeFactors hp) _,
    prod_boole]
  have hsq : (∀ p ∈ n.primeFactors, Even (n.factorization p)) ↔ IsSquare n := by
    rw [Nat.isSquare_iff_even_factorization]
    refine ⟨fun h p hp ↦ ?_, fun h p hp ↦ h p (Nat.prime_of_mem_primeFactors hp)⟩
    by_cases hpn : p ∈ n.primeFactors
    · exact h p hpn
    · rw [← Nat.support_factorization, Finsupp.notMem_support_iff] at hpn
      rw [hpn]
      exact ⟨0, rfl⟩
  simp only [hsq]

/-- `μ(n)² = |μ(n)|`. -/
theorem pmul_moebius_moebius_apply (n : ℕ) :
    (μ : ArithmeticFunction ℤ).pmul μ n = |μ n| := by
  rw [pmul_apply, ← sq, moebius_sq, abs_moebius]

/-- **Apostol, Theorem 2.19**, second part: `λ⁻¹ = μ² = |μ|`, i.e. `μ² * λ = I`. -/
@[kb "apostol1976" "Thm 2.19, p. 38"]
theorem pmul_moebius_moebius_mul_liouville :
    (μ : ArithmeticFunction ℤ).pmul μ * liouville = 1 := by
  have h := (isCompletelyMultiplicative_iff_pmul_moebius_mul_eq_one isMultiplicative_liouville).1
    isCompletelyMultiplicative_liouville
  have e : (μ : ArithmeticFunction ℤ).pmul μ = (μ : ArithmeticFunction ℤ).pmul liouville := by
    ext n
    rw [pmul_apply, pmul_apply]
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    by_cases hsq : Squarefree n
    · rw [liouville_apply hn, moebius_apply_of_squarefree hsq]
    · simp [moebius_eq_zero_of_not_squarefree hsq]
  rw [e]
  simpa using h

/-! ## Divisor functions of complex order (Apostol, §2.13) -/

/-- The power function `N^α(n) = n^α` (`0` at `n = 0`), for complex `α` (Apostol, §2.9). -/
noncomputable def powC (α : ℂ) : ArithmeticFunction ℂ :=
  ⟨fun n ↦ if n = 0 then 0 else (n : ℂ) ^ α, by simp⟩

theorem powC_apply {α : ℂ} {n : ℕ} (hn : n ≠ 0) : powC α n = (n : ℂ) ^ α := by
  simp [powC, hn]

theorem isCompletelyMultiplicative_powC (α : ℂ) : IsCompletelyMultiplicative (powC α) := by
  refine ⟨by simp [powC], fun m n ↦ ?_⟩
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [powC_apply hm, powC_apply hn, powC_apply (mul_ne_zero hm hn), Nat.cast_mul,
    Complex.natCast_mul_natCast_cpow]

/-- The divisor function `σ_α(n) = ∑_{d ∣ n} d^α` for complex `α`, as `N^α * u`
(Mathlib's `ArithmeticFunction.sigma` has natural exponents only; see `sigmaC_natCast`). -/
noncomputable def sigmaC (α : ℂ) : ArithmeticFunction ℂ := powC α * ζ

theorem sigmaC_apply (α : ℂ) (n : ℕ) : sigmaC α n = ∑ d ∈ n.divisors, (d : ℂ) ^ α := by
  rw [sigmaC, coe_mul_zeta_apply]
  exact sum_congr rfl fun d hd ↦ powC_apply (Nat.ne_of_gt (Nat.pos_of_mem_divisors hd))

theorem sigmaC_natCast (k : ℕ) : sigmaC k = (σ k : ArithmeticFunction ℂ) := by
  ext n
  rw [sigmaC_apply, natCoe_apply, sigma_apply]
  push_cast
  simp

/-- **Apostol, Theorem 2.20.** `σ_α⁻¹(n) = ∑_{d ∣ n} d^α μ(d) μ(n/d)`: the function
`n ↦ ∑_{d ∣ n} d^α μ(d) μ(n/d)` is the Dirichlet inverse of `σ_α`. -/
@[kb "apostol1976" "Thm 2.20, p. 39"]
theorem sigmaC_mul_inv (α : ℂ) :
    sigmaC α * ((μ : ArithmeticFunction ℂ).pmul (powC α) * μ) = 1 :=
  (isCompletelyMultiplicative_powC α).mul_zeta_mul_inv

theorem pmul_moebius_powC_mul_moebius_apply (α : ℂ) (n : ℕ) :
    ((μ : ArithmeticFunction ℂ).pmul (powC α) * μ) n =
      ∑ d ∈ n.divisors, (d : ℂ) ^ α * μ d * μ (n / d) := by
  rw [mul_apply_eq_sum_divisors]
  refine sum_congr rfl fun d hd ↦ ?_
  rw [pmul_apply, intCoe_apply, intCoe_apply, powC_apply (Nat.ne_of_gt (Nat.pos_of_mem_divisors hd))]
  ring

end NTKB.Apostol
