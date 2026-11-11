/-
Copyright (c) 2026 The Tau Ceti contributors. Released under Apache 2.0 license.
Copied into NTKB with credit from Tau Ceti (`TauCeti/NumberTheory/LSeries/Quadratic/Pair/Basic.lean`,
`TauCeti/NumberTheory/LSeries/ZetaMul.lean`,
`TauCeti/NumberTheory/DirichletCharacter/ArithmeticFunction.lean`, `TauCeti/Data/Nat/GCD.lean`,
main `d2083f0f`, staged 2026-11-10); NTKB does not depend on Tau Ceti. Changes: namespace
`NTKB.DirichletCharacter` (so no dot notation for the new declarations), only the declarations
needed for the four-factor product, the `NeZero (lcm m n)` instance made local to this namespace.
-/
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# Four-factor coefficients for a pair of Dirichlet characters (port from Tau Ceti)

`zetaMulPairCoeffs χ ψ` is the Dirichlet convolution `1 * χ * ψ * (χ ψ)`, the coefficient
function of `ζ(s) L(s, χ) L(s, ψ) L(s, χ ψ)` (the product character at the least common multiple
of the levels). For quadratic characters its values are nonnegative real numbers: this is the
positivity in Estermann's proof of Siegel's theorem (Davenport, Ch. 21, p. 129).
-/

open ArithmeticFunction
open scoped ComplexOrder

namespace NTKB.DirichletCharacter

/-- The least common multiple of two nonzero natural numbers is nonzero. -/
instance neZero_lcm (m n : ℕ) [NeZero m] [NeZero n] : NeZero (Nat.lcm m n) :=
  ⟨Nat.lcm_ne_zero (NeZero.ne m) (NeZero.ne n)⟩

section CommMonoidWithZero

variable {R : Type*} [CommMonoidWithZero R] {M N : ℕ}

/-- Raising the level of a Dirichlet character does not change its value at a natural number
prime to the new level. -/
theorem changeLevel_natCast_of_coprime' {d n : ℕ} (h : d ∣ n)
    (χ : DirichletCharacter R d) {m : ℕ} (hm : m.Coprime n) :
    _root_.DirichletCharacter.changeLevel h χ m = χ m := by
  simpa using _root_.DirichletCharacter.changeLevel_eq_cast_of_dvd' χ h (a := (m : ℤ))
    (Nat.isCoprime_iff_coprime.mpr hm)

/-- The product character at the least common multiple of the levels is the pointwise product
on natural numbers, including the nonunits. -/
theorem mul_natCast (χ : DirichletCharacter R M) (ψ : DirichletCharacter R N) (n : ℕ) :
    χ.mul ψ n = χ n * ψ n := by
  by_cases hn : n.Coprime (Nat.lcm M N)
  · rw [_root_.DirichletCharacter.mul, MulChar.mul_apply,
      changeLevel_natCast_of_coprime' _ _ hn, changeLevel_natCast_of_coprime' _ _ hn]
  · have hzero : χ.mul ψ n = 0 :=
      (χ.mul ψ).map_nonunit (by rwa [ZMod.isUnit_iff_coprime])
    rw [hzero]
    have hbad : ¬ n.Coprime M ∨ ¬ n.Coprime N := by
      by_contra! h
      exact hn ((h.1.mul_right h.2).of_dvd_right (Nat.lcm_dvd_mul M N))
    rcases hbad with h | h
    · rw [χ.map_nonunit (by rwa [ZMod.isUnit_iff_coprime]), zero_mul]
    · rw [ψ.map_nonunit (by rwa [ZMod.isUnit_iff_coprime]), mul_zero]

/-- At a power of a nonzero natural number, a character's arithmetic function is the
corresponding power of its character value. -/
theorem toArithmeticFunction_apply_pow (χ : DirichletCharacter R M)
    {n : ℕ} (hn : n ≠ 0) (k : ℕ) : toArithmeticFunction (χ ·) (n ^ k) = χ n ^ k := by
  rw [← χ.apply_eq_toArithmeticFunction_apply (pow_ne_zero _ hn), Nat.cast_pow, map_pow]

/-- The product at the least common multiple of the levels corresponds to pointwise
multiplication of arithmetic functions. -/
theorem toArithmeticFunction_mul (χ : DirichletCharacter R M) (ψ : DirichletCharacter R N) :
    toArithmeticFunction (χ.mul ψ ·) =
      (toArithmeticFunction (χ ·)).pmul (toArithmeticFunction (ψ ·)) := by
  ext n
  rw [ArithmeticFunction.pmul_apply]
  by_cases hn : n = 0
  · simp [hn]
  · rw [← (χ.mul ψ).apply_eq_toArithmeticFunction_apply hn,
      ← χ.apply_eq_toArithmeticFunction_apply hn,
      ← ψ.apply_eq_toArithmeticFunction_apply hn]
    exact mul_natCast χ ψ n

end CommMonoidWithZero

variable {R : Type*} [CommSemiring R] {M : ℕ}

/-- Twisting by a Dirichlet character preserves Dirichlet convolution. -/
theorem toArithmeticFunction_pmul_mul (χ : DirichletCharacter R M)
    (f g : ArithmeticFunction R) :
    (toArithmeticFunction (χ ·)).pmul (f * g) =
      ((toArithmeticFunction (χ ·)).pmul f) * ((toArithmeticFunction (χ ·)).pmul g) := by
  ext n
  by_cases hn : n = 0
  · simp [hn]
  rw [pmul_apply, ArithmeticFunction.mul_apply, Finset.mul_sum, ArithmeticFunction.mul_apply]
  apply Finset.sum_congr rfl
  intro d hd
  have hdn := (Nat.mem_divisorsAntidiagonal.mp hd).1
  have hd0 := Nat.ne_zero_of_mem_divisorsAntidiagonal hd
  simp only [pmul_apply, ← χ.apply_eq_toArithmeticFunction_apply hn,
    ← χ.apply_eq_toArithmeticFunction_apply hd0.1,
    ← χ.apply_eq_toArithmeticFunction_apply hd0.2]
  rw [← hdn, Nat.cast_mul, map_mul]
  ring

/-- On `Re s > 1`, a character's arithmetic function has an absolutely convergent
Dirichlet series with sum equal to its L-function. -/
theorem LSeriesHasSum_toArithmeticFunction {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    LSeriesHasSum (toArithmeticFunction (χ ·)) s (χ.LFunction s) := by
  rw [χ.LFunction_eq_LSeries hs]
  exact (LSeriesHasSum_congr s _ χ.apply_eq_toArithmeticFunction_apply).mp
    (ZMod.LSeriesSummable_of_one_lt_re χ hs).LSeriesHasSum

/-- If `χ(p) = -1`, the coefficients of `ζ * χ` at powers of `p` are `1` at even exponents
and `0` at odd exponents. -/
theorem zetaMul_prime_pow_of_eq_neg_one {N : ℕ} {χ : DirichletCharacter ℂ N} {p : ℕ}
    (hp : p.Prime) (hχ : χ p = -1) (k : ℕ) :
    χ.zetaMul (p ^ k) = if Even k then 1 else 0 := by
  simp only [_root_.DirichletCharacter.zetaMul, ArithmeticFunction.coe_zeta_mul_apply,
    Nat.sum_divisors_prime_pow hp]
  simp_rw [← χ.apply_eq_toArithmeticFunction_apply (pow_ne_zero _ hp.ne_zero),
    Nat.cast_pow, map_pow, hχ, neg_one_geom_sum]
  simp only [Nat.even_add_one, ite_not]

/-- On `Re s > 1`, the convolution `ζ * χ` has an absolutely convergent Dirichlet series
with sum `ζ(s) L(s, χ)`. -/
theorem LSeriesHasSum_zetaMul {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {s : ℂ}
    (hs : 1 < s.re) :
    LSeriesHasSum χ.zetaMul s (riemannZeta s * χ.LFunction s) := by
  have h : LSeries χ.zetaMul s = riemannZeta s * χ.LFunction s := by
    rw [_root_.DirichletCharacter.zetaMul, ← ArithmeticFunction.coe_mul, LSeries_convolution',
      χ.LFunction_eq_LSeries hs]
    · congr 1
      · simp_rw [← ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs,
          ← ArithmeticFunction.natCoe_apply]
      · exact (LSeries_congr χ.apply_eq_toArithmeticFunction_apply s).symm
    · exact ArithmeticFunction.LSeriesSummable_zeta_iff.mpr hs
    · exact (LSeriesSummable_congr _ fun h ↦ (χ.apply_eq_toArithmeticFunction_apply h).symm).mpr <|
        ZMod.LSeriesSummable_of_one_lt_re χ hs
  rw [← h]
  exact (χ.LSeriesSummable_zetaMul hs).LSeriesHasSum

variable {M N : ℕ}

/-- The Dirichlet coefficients of `ζ(s) L(s, χ) L(s, ψ) L(s, χ.mul ψ)`, with the product
character at the least common multiple of the two levels. -/
noncomputable def zetaMulPairCoeffs (χ : DirichletCharacter ℂ M)
    (ψ : DirichletCharacter ℂ N) : ArithmeticFunction ℂ :=
  (χ.zetaMul * toArithmeticFunction (ψ ·)) * toArithmeticFunction (χ.mul ψ ·)

/-- Pairing the first two factors with their character twist gives the four-factor product. -/
theorem zetaMulPairCoeffs_eq_zetaMul_mul_pmul (χ : DirichletCharacter ℂ M)
    (ψ : DirichletCharacter ℂ N) :
    zetaMulPairCoeffs χ ψ = χ.zetaMul * (toArithmeticFunction (ψ ·)).pmul χ.zetaMul := by
  rw [zetaMulPairCoeffs, _root_.DirichletCharacter.zetaMul, toArithmeticFunction_pmul_mul,
    ArithmeticFunction.pmul_zeta, toArithmeticFunction_mul,
    ArithmeticFunction.pmul_comm (toArithmeticFunction (ψ ·)), mul_assoc]

/-- The prime-power coefficients are the convolution of `zetaMul` with its character twist. -/
theorem zetaMulPairCoeffs_prime_pow (χ : DirichletCharacter ℂ M)
    (ψ : DirichletCharacter ℂ N) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    zetaMulPairCoeffs χ ψ (p ^ k) = ∑ i ∈ Finset.range (k + 1),
      χ.zetaMul (p ^ i) * (toArithmeticFunction (ψ ·)).pmul χ.zetaMul (p ^ (k - i)) := by
  rw [zetaMulPairCoeffs_eq_zetaMul_mul_pmul, ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun a b ↦
      χ.zetaMul a * (toArithmeticFunction (ψ ·)).pmul χ.zetaMul b),
    Nat.sum_divisors_prime_pow hp]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [← pow_sub_mul_pow p (Nat.le_of_lt_succ (Finset.mem_range.mp hi)),
    Nat.mul_div_cancel _ (pow_pos hp.pos _)]

/-- The four-factor coefficient function is symmetric in the characters. -/
theorem zetaMulPairCoeffs_comm (χ : DirichletCharacter ℂ M) (ψ : DirichletCharacter ℂ N) :
    zetaMulPairCoeffs χ ψ = zetaMulPairCoeffs ψ χ := by
  simp only [zetaMulPairCoeffs, _root_.DirichletCharacter.zetaMul, toArithmeticFunction_mul]
  rw [ArithmeticFunction.pmul_comm (toArithmeticFunction (χ ·))]
  ring

/-- The coefficients of the four-factor product are multiplicative. -/
theorem isMultiplicative_zetaMulPairCoeffs (χ : DirichletCharacter ℂ M)
    (ψ : DirichletCharacter ℂ N) : (zetaMulPairCoeffs χ ψ).IsMultiplicative :=
  (χ.isMultiplicative_zetaMul.mul ψ.isMultiplicative_toArithmeticFunction).mul
    (χ.mul ψ).isMultiplicative_toArithmeticFunction

/-- The coefficient at `1` of the four-factor product is `1`. -/
@[simp] theorem zetaMulPairCoeffs_one (χ : DirichletCharacter ℂ M)
    (ψ : DirichletCharacter ℂ N) : zetaMulPairCoeffs χ ψ 1 = 1 :=
  (isMultiplicative_zetaMulPairCoeffs χ ψ).map_one

private theorem twist_zetaMul_prime_pow_nonneg {χ : DirichletCharacter ℂ M}
    {ψ : DirichletCharacter ℂ N} (hψ : ψ.IsQuadratic) {p : ℕ} (hp : p.Prime)
    (hχ : χ p = -1) (k : ℕ) :
    0 ≤ (toArithmeticFunction (ψ ·)).pmul χ.zetaMul (p ^ k) := by
  rw [ArithmeticFunction.pmul_apply, zetaMul_prime_pow_of_eq_neg_one hp hχ]
  split_ifs with hk
  · rw [mul_one, toArithmeticFunction_apply_pow ψ hp.ne_zero]
    rcases hψ p with h | h | h
    · simp [h, pow_nonneg]
    · simp [h]
    · simp [h, hk.neg_one_pow]
  · simp

private theorem zetaMulPairCoeffs_prime_pow_nonneg_of_eq_neg_one
    {χ : DirichletCharacter ℂ M} {ψ : DirichletCharacter ℂ N}
    (hχ : χ.IsQuadratic) (hψ : ψ.IsQuadratic) {p : ℕ} (hp : p.Prime)
    (hχp : χ p = -1) (k : ℕ) : 0 ≤ zetaMulPairCoeffs χ ψ (p ^ k) := by
  rw [zetaMulPairCoeffs_prime_pow χ ψ hp]
  refine Finset.sum_nonneg fun i _ ↦ ?_
  exact mul_nonneg (_root_.DirichletCharacter.zetaMul_prime_pow_nonneg
      (MulChar.isQuadratic_iff_sq_eq_one.mp hχ) hp i)
    (twist_zetaMul_prime_pow_nonneg hψ hp hχp (k - i))

/-- At every prime power the coefficients of the four-factor product of quadratic characters
are nonnegative real numbers. -/
theorem zetaMulPairCoeffs_prime_pow_nonneg {χ : DirichletCharacter ℂ M}
    {ψ : DirichletCharacter ℂ N} (hχ : χ.IsQuadratic) (hψ : ψ.IsQuadratic)
    {p : ℕ} (hp : p.Prime) (k : ℕ) : 0 ≤ zetaMulPairCoeffs χ ψ (p ^ k) := by
  by_cases hχp : χ p = -1
  · exact zetaMulPairCoeffs_prime_pow_nonneg_of_eq_neg_one hχ hψ hp hχp k
  by_cases hψp : ψ p = -1
  · rw [zetaMulPairCoeffs_comm]
    exact zetaMulPairCoeffs_prime_pow_nonneg_of_eq_neg_one hψ hχ hp hψp k
  have hψ0 : 0 ≤ ψ p := by rcases hψ p with h | h | h <;> simp_all
  have hχsq := MulChar.isQuadratic_iff_sq_eq_one.mp hχ
  rw [zetaMulPairCoeffs_prime_pow χ ψ hp]
  refine Finset.sum_nonneg fun i _ ↦ ?_
  rw [ArithmeticFunction.pmul_apply, toArithmeticFunction_apply_pow ψ hp.ne_zero]
  exact mul_nonneg (_root_.DirichletCharacter.zetaMul_nonneg hχsq _)
    (mul_nonneg (pow_nonneg hψ0 _) (_root_.DirichletCharacter.zetaMul_nonneg hχsq _))

/-- All Dirichlet coefficients of `ζ(s) L(s, χ) L(s, ψ) L(s, χ.mul ψ)` are nonnegative
real numbers for quadratic characters. -/
theorem zetaMulPairCoeffs_nonneg {χ : DirichletCharacter ℂ M}
    {ψ : DirichletCharacter ℂ N} (hχ : χ.IsQuadratic) (hψ : ψ.IsQuadratic) (n : ℕ) :
    0 ≤ zetaMulPairCoeffs χ ψ n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [(isMultiplicative_zetaMulPairCoeffs χ ψ).multiplicative_factorization _ hn]
  exact Finset.prod_nonneg fun p hp ↦
    zetaMulPairCoeffs_prime_pow_nonneg hχ hψ (Nat.prime_of_mem_primeFactors hp) _

/-- On `Re s > 1` the four-factor product is the absolutely convergent Dirichlet series
of `zetaMulPairCoeffs`. -/
theorem LSeriesHasSum_zetaMulPairCoeffs [NeZero M] [NeZero N]
    (χ : DirichletCharacter ℂ M) (ψ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    LSeriesHasSum (zetaMulPairCoeffs χ ψ) s
      (riemannZeta s * χ.LFunction s * ψ.LFunction s * (χ.mul ψ).LFunction s) :=
  ArithmeticFunction.LSeriesHasSum_mul
    (ArithmeticFunction.LSeriesHasSum_mul (LSeriesHasSum_zetaMul χ hs)
      (LSeriesHasSum_toArithmeticFunction ψ hs))
    (LSeriesHasSum_toArithmeticFunction (χ.mul ψ) hs)

end NTKB.DirichletCharacter
