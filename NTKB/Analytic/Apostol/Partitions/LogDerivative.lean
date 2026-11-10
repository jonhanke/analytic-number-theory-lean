/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.Analysis.Complex.Basic
import Mathlib.NumberTheory.Divisors
import NTKB.Attr

/-!
# Logarithmic differentiation of generating functions (Apostol, Theorem 14.8)

For a set `A` of positive integers and an arithmetical function `f`, Apostol (§14.10) considers
`F_A(x) = ∏_{n ∈ A} (1 - xⁿ)^{-f(n)/n} = ∑ p_{A,f}(n) xⁿ` and proves, by logarithmic
differentiation `x F_A'(x) = F_A(x) ∑_k f_A(k) x^k`, the recursion
`n p_{A,f}(n) = ∑_{k=1}^n f_A(k) p_{A,f}(n - k)` with `f_A(k) = ∑_{d ∣ k, d ∈ A} f(d)`.

We work with formal power series over `ℂ` (Mathlib's `PowerSeries.WithPiTopology` for the infinite
product). The complex power `(1 - X)^{-a}` is Mathlib's binomial series `(1 + X)^{-a}`
(`PowerSeries.binomialSeries`) with `X ↦ -X`, and `(1 - Xⁿ)^{-a}` is obtained by `X ↦ Xⁿ`
(`PowerSeries.expand`).

* `oneSubXRpowNeg a` = `(1 - X)^{-a}`; sanity checks `oneSubXRpowNeg_add`,
  `pow_mul_oneSubXRpowNeg_natCast` (`(1 - X)^d (1 - X)^{-d} = 1`).
* `oneSubXPowRpowNeg n a` = `(1 - Xⁿ)^{-a}`.
* Theorem 14.8 -> `apostol_thm_14_8` (the product is multipliable, `p_{A,f}(0) = 1`, and the recursion);
  the logarithmic-derivative identity for the product -> `X_mul_derivative_genFunA`.
-/

open PowerSeries Finset Filter
open scoped PowerSeries.WithPiTopology Topology

namespace NTKB.Apostol

/-- The formal power series `(1 - X)^{-a}` for complex `a`: the binomial series `(1 + X)^{-a}`
with `X` replaced by `-X`. -/
noncomputable def oneSubXRpowNeg (a : ℂ) : ℂ⟦X⟧ :=
  rescale (-1 : ℂ) (binomialSeries ℂ (-a))

/-- The formal power series `(1 - Xⁿ)^{-a}` (`n ≥ 1`; by convention `1` for `n = 0`). -/
noncomputable def oneSubXPowRpowNeg (n : ℕ) (a : ℂ) : ℂ⟦X⟧ :=
  if h : n = 0 then 1 else expand n h (oneSubXRpowNeg a)

theorem oneSubXPowRpowNeg_of_ne_zero {n : ℕ} (hn : n ≠ 0) (a : ℂ) :
    oneSubXPowRpowNeg n a = expand n hn (oneSubXRpowNeg a) := by
  simp [oneSubXPowRpowNeg, hn]

theorem coeff_oneSubXRpowNeg(a : ℂ) (k : ℕ) :
    coeff k (oneSubXRpowNeg a) = (-1) ^ k * Ring.choose (-a) k := by
  simp [oneSubXRpowNeg, coeff_rescale]

theorem oneSubXRpowNeg_add (a b : ℂ) :
    oneSubXRpowNeg (a + b) = oneSubXRpowNeg a * oneSubXRpowNeg b := by
  simp [oneSubXRpowNeg, binomialSeries_add, map_mul, mul_comm]

theorem oneSubXRpowNeg_zero : oneSubXRpowNeg 0 = 1 := by
  simp [oneSubXRpowNeg]

/-- Sanity check: for a natural number `d`, `(1 - X)^{-d}` is the inverse of `(1 - X)^d`. -/
theorem pow_mul_oneSubXRpowNeg_natCast (d : ℕ) :
    (1 - X : ℂ⟦X⟧) ^ d * oneSubXRpowNeg d = 1 := by
  have h : oneSubXRpowNeg (-(d : ℂ)) = (1 - X) ^ d := by
    simp only [oneSubXRpowNeg, neg_neg, binomialSeries_nat, map_pow, map_add, map_one,
      rescale_X, map_neg, map_one, neg_mul, one_mul, sub_eq_add_neg]
  rw [← h, ← oneSubXRpowNeg_add, neg_add_cancel, oneSubXRpowNeg_zero]

/-- `(k + 1) c_{k+1} = (a + k) c_k` for the coefficients `c_k` of `(1 - X)^{-a}`. -/
theorem succ_mul_coeff_oneSubXRpowNeg (a : ℂ) (k : ℕ) :
    ((k : ℂ) + 1) * coeff (k + 1) (oneSubXRpowNeg a) = (a + k) * coeff k (oneSubXRpowNeg a) := by
  rw [coeff_oneSubXRpowNeg, coeff_oneSubXRpowNeg, Ring.choose_eq_smul, Ring.choose_eq_smul,
    ← Polynomial.aeval_eq_smeval, ← Polynomial.aeval_eq_smeval, descPochhammer_succ_right, map_mul,
    map_sub, Polynomial.aeval_X,
    map_natCast, Nat.factorial_succ, Nat.cast_mul, smul_eq_mul, smul_eq_mul, pow_succ]
  have hk : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  have hk1 : ((k : ℂ) + 1) ≠ 0 := by exact_mod_cast k.succ_ne_zero
  push_cast
  field_simp
  ring


/-- `X φ'` has coefficients `m · coeff m φ`. -/
theorem coeff_X_mul_derivative (φ : ℂ⟦X⟧) (m : ℕ) :
    coeff m (X * derivative φ) = m * coeff m φ := by
  cases m with
  | zero => simp
  | succ k => rw [coeff_succ_X_mul, coeff_derivative]; push_cast; ring

/-- `(1 - X) · X h' = a X h` for `h = (1 - X)^{-a}`. -/
theorem one_sub_X_mul_X_mul_derivative_oneSubXRpowNeg (a : ℂ) :
    (1 - X) * (X * derivative (oneSubXRpowNeg a)) = C a * X * oneSubXRpowNeg a := by
  ext m
  rw [sub_mul, one_mul, map_sub, show C a * X * oneSubXRpowNeg a = X * (C a * oneSubXRpowNeg a) by
    ring]
  cases m with
  | zero => simp
  | succ k =>
    rw [coeff_succ_X_mul, coeff_succ_X_mul, coeff_succ_X_mul, coeff_C_mul, coeff_derivative,
      coeff_X_mul_derivative]
    rw [mul_comm, succ_mul_coeff_oneSubXRpowNeg]
    ring

/-- `X (φ(Xⁿ))' = n · (X φ')(Xⁿ)`. -/
theorem X_mul_derivative_expand (n : ℕ) (hn : n ≠ 0) (φ : ℂ⟦X⟧) :
    X * derivative (expand n hn φ) = C (n : ℂ) * expand n hn (X * derivative φ) := by
  ext m
  rw [coeff_X_mul_derivative, coeff_C_mul, coeff_expand, coeff_expand]
  split_ifs with h
  · obtain ⟨q, rfl⟩ := h
    rw [Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hn), coeff_X_mul_derivative]
    push_cast; ring
  · simp

/-- The series `X/(1 - X) = ∑_{j ≥ 1} X^j`. -/
noncomputable def geomTail : ℂ⟦X⟧ := mk fun m ↦ if m = 0 then 0 else 1

theorem one_sub_X_mul_geomTail : (1 - X) * geomTail = X := by
  ext m
  rw [sub_mul, one_mul, map_sub]
  cases m with
  | zero => simp [geomTail]
  | succ k =>
    rw [coeff_succ_X_mul, coeff_X]
    cases k <;> simp [geomTail]

theorem one_sub_X_pow_ne_zero {n : ℕ} (hn : n ≠ 0) : (1 - X ^ n : ℂ⟦X⟧) ≠ 0 := by
  intro h
  have := congrArg (constantCoeff (R := ℂ)) h
  simp [zero_pow hn] at this

/-- Logarithmic derivative of `(1 - Xⁿ)^{-a}`: `X g' = g · n a ∑_{j ≥ 1} X^{nj}`. -/
theorem X_mul_derivative_oneSubXPowRpowNeg (n : ℕ) (hn : n ≠ 0) (a : ℂ) :
    X * derivative (oneSubXPowRpowNeg n a) =
      oneSubXPowRpowNeg n a * (C ((n : ℂ) * a) * expand n hn geomTail) := by
  apply mul_left_cancel₀ (one_sub_X_pow_ne_zero hn)
  have e1 : (1 - X ^ n) * expand n hn (X * derivative (oneSubXRpowNeg a)) =
      C a * X ^ n * expand n hn (oneSubXRpowNeg a) := by
    have := congrArg (expand n hn) (one_sub_X_mul_X_mul_derivative_oneSubXRpowNeg a)
    rwa [map_mul (expand n hn) (1 - X), map_sub, map_one, expand_X,
      map_mul (expand n hn) (C a * X), map_mul (expand n hn) (C a), expand_C, expand_X] at this
  have e2 : (1 - X ^ n) * expand n hn geomTail = X ^ n := by
    have := congrArg (expand n hn) one_sub_X_mul_geomTail
    rwa [map_mul, map_sub, map_one, expand_X] at this
  rw [oneSubXPowRpowNeg_of_ne_zero hn, X_mul_derivative_expand]
  calc (1 - X ^ n) * (C (n : ℂ) * expand n hn (X * derivative (oneSubXRpowNeg a)))
      = C (n : ℂ) * ((1 - X ^ n) * expand n hn (X * derivative (oneSubXRpowNeg a))) := by ring
    _ = C (n : ℂ) * (C a * X ^ n * expand n hn (oneSubXRpowNeg a)) := by rw [e1]
    _ = expand n hn (oneSubXRpowNeg a) * C ((n : ℂ) * a) * ((1 - X ^ n) * expand n hn geomTail)
        := by rw [e2, map_mul]; ring
    _ = _ := by ring


/-! ### The product `F_A(x) = ∏_{n ∈ A} (1 - xⁿ)^{-f(n)/n}` -/

section Product

variable (A : Set ℕ) (f : ℕ → ℂ)

open scoped Classical in
/-- The factor `(1 - Xⁿ)^{-f(n)/n}` of `F_A` for `n ∈ A`, and `1` for `n ∉ A` (and for `n = 0`:
`A` is a set of positive integers in Apostol). -/
noncomputable def genFunFactor (n : ℕ) : ℂ⟦X⟧ :=
  if n ∈ A then oneSubXPowRpowNeg n (f n / n) else 1

/-- Apostol's `F_A(x) = ∏_{n ∈ A} (1 - xⁿ)^{-f(n)/n}` (§14.10 (23)), as an infinite product of formal
power series; its coefficients are `p_{A,f}(n)`. -/
noncomputable def genFunA : ℂ⟦X⟧ := ∏' n, genFunFactor A f n

open scoped Classical in
/-- `f_A(k) = ∑_{d ∣ k, d ∈ A} f(d)`. -/
noncomputable def fA (k : ℕ) : ℂ := ∑ d ∈ k.divisors with d ∈ A, f d

open scoped Classical in
/-- The logarithmic derivative `X g'/g = f(n) ∑_{j ≥ 1} X^{nj}` of the factor `g = genFunFactor A f n`. -/
noncomputable def logDerivTerm (n : ℕ) : ℂ⟦X⟧ :=
  if h : n ∈ A ∧ n ≠ 0 then C (f n) * expand n h.2 geomTail else 0

theorem X_mul_derivative_genFunFactor (n : ℕ) :
    X * derivative (genFunFactor A f n) = genFunFactor A f n * logDerivTerm A f n := by
  classical
  by_cases hA : n ∈ A
  · by_cases hn : n = 0
    · subst hn
      simp [genFunFactor, logDerivTerm, oneSubXPowRpowNeg]
    · have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
      simp only [genFunFactor, logDerivTerm, hA, if_true, ne_eq, hn, not_false_eq_true, and_self,
        dite_true]
      rw [X_mul_derivative_oneSubXPowRpowNeg n hn, mul_div_cancel₀ _ hn']
  · simp [genFunFactor, logDerivTerm, hA]

theorem coeff_genFunFactor_of_lt {n i : ℕ} (hi : i < n) :
    coeff i (genFunFactor A f n) = if i = 0 then 1 else 0 := by
  classical
  have hn : n ≠ 0 := by omega
  by_cases hA : n ∈ A
  · rw [genFunFactor, if_pos hA, oneSubXPowRpowNeg_of_ne_zero hn, coeff_expand]
    split_ifs with h1 h2 h2
    · subst h2; simp [coeff_oneSubXRpowNeg]
    · exact absurd (Nat.eq_zero_of_dvd_of_lt h1 hi) h2
    · subst h2; exact absurd (dvd_zero n) h1
    · rfl
  · rw [genFunFactor, if_neg hA, coeff_one]

theorem coeff_mul_genFunFactor_of_lt (φ : ℂ⟦X⟧) {k n : ℕ} (hk : k < n) :
    coeff k (φ * genFunFactor A f n) = coeff k φ := by
  rw [coeff_mul, Finset.sum_eq_single (k, 0)]
  · rw [coeff_genFunFactor_of_lt A f (by omega), if_pos rfl, mul_one]
  · intro p hp hne
    have h1 := mem_antidiagonal.mp hp
    rw [coeff_genFunFactor_of_lt A f (by omega), if_neg, mul_zero]
    intro h0
    exact hne (Prod.ext (by omega) h0)
  · intro h; exact absurd (mem_antidiagonal.mpr (by simp)) h

/-- Logarithmic differentiation of a finite product of factors. -/
theorem X_mul_derivative_prod_genFunFactor (s : Finset ℕ) :
    X * derivative (∏ n ∈ s, genFunFactor A f n) =
      (∏ n ∈ s, genFunFactor A f n) * ∑ n ∈ s, logDerivTerm A f n := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [prod_insert ha, sum_insert ha, Derivation.leibniz, smul_eq_mul, smul_eq_mul, mul_add,
      ← mul_assoc, mul_comm X (genFunFactor A f a), mul_assoc, ih, ← mul_assoc X,
      mul_comm X (∏ n ∈ s, genFunFactor A f n), mul_assoc, X_mul_derivative_genFunFactor]
    ring

theorem coeff_prod_range_genFunFactor (k : ℕ) {N : ℕ} (hN : k < N) :
    coeff k (∏ n ∈ range N, genFunFactor A f n) =
      coeff k (∏ n ∈ range (k + 1), genFunFactor A f n) := by
  induction N, hN using Nat.le_induction with
  | base => rfl
  | succ N hN ih => rw [prod_range_succ, coeff_mul_genFunFactor_of_lt A f _ hN, ih]

theorem multipliable_genFunFactor : Multipliable (genFunFactor A f) := by
  have h : genFunFactor A f = fun n ↦ 1 + (genFunFactor A f n - 1) := by
    funext n; ring
  rw [h]
  apply WithPiTopology.multipliable_one_add_of_tendsto_order_atTop_nhds_top
  refine ENat.tendsto_nhds_top_iff_natCast_lt.mpr fun m ↦ eventually_atTop.mpr ⟨m + 1, ?_⟩
  intro n hn
  refine lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self m) (nat_le_order _ (m + 1) ?_)
  intro i hi
  rw [map_sub, coeff_genFunFactor_of_lt A f (by omega), coeff_one]
  simp

theorem coeff_genFunA (k : ℕ) {N : ℕ} (hN : k < N) :
    coeff k (genFunA A f) = coeff k (∏ n ∈ range N, genFunFactor A f n) := by
  have ht := (multipliable_genFunFactor A f).hasProd.tendsto_prod_nat
  have h1 := ((WithPiTopology.continuous_coeff ℂ k).tendsto _).comp ht
  have h2 : Tendsto (fun N ↦ coeff k (∏ n ∈ range N, genFunFactor A f n)) atTop
      (𝓝 (coeff k (∏ n ∈ range (k + 1), genFunFactor A f n))) :=
    tendsto_const_nhds.congr' (eventually_atTop.mpr
      ⟨k + 1, fun N hN ↦ (coeff_prod_range_genFunFactor A f k hN).symm⟩)
  rw [coeff_prod_range_genFunFactor A f k hN]
  exact tendsto_nhds_unique h1 h2

theorem coeff_sum_logDerivTerm (j : ℕ) {N : ℕ} (hj : j < N) :
    coeff j (∑ n ∈ range N, logDerivTerm A f n) = fA A f j := by
  classical
  have hterm : ∀ n, coeff j (logDerivTerm A f n) =
      if n ∈ A ∧ n ∈ j.divisors then f n else 0 := by
    intro n
    rw [logDerivTerm]
    split_ifs with h1 h2 h2
    · rw [coeff_C_mul, coeff_expand]
      have hd := (Nat.mem_divisors.mp h2.2)
      rw [if_pos hd.1, geomTail, coeff_mk, if_neg, mul_one]
      intro h0
      exact hd.2 (by rw [← Nat.div_mul_cancel hd.1, h0, zero_mul])
    · rw [coeff_C_mul, coeff_expand]
      split_ifs with h3
      · rw [geomTail, coeff_mk, if_pos, mul_zero]
        by_contra h4
        have hj0 : j ≠ 0 := by
          rintro rfl; exact h4 (Nat.zero_div n)
        exact h2 ⟨h1.1, Nat.mem_divisors.mpr ⟨h3, hj0⟩⟩
      · rw [mul_zero]
    · exfalso
      have hd := (Nat.mem_divisors.mp h2.2)
      exact h1 ⟨h2.1, fun h0 ↦ by subst h0; exact hd.2 (Nat.eq_zero_of_zero_dvd hd.1)⟩
    · simp
  rw [map_sum, sum_congr rfl fun n _ ↦ hterm n, ← sum_filter, fA]
  apply sum_congr _ (fun _ _ ↦ rfl)
  ext d
  simp only [mem_filter, mem_range]
  constructor
  · rintro ⟨-, h1, h2⟩; exact ⟨h2, h1⟩
  · rintro ⟨h2, h1⟩
    exact ⟨lt_of_le_of_lt (Nat.divisor_le h2) hj, h1, h2⟩

/-- The coefficient identity behind Theorem 14.8: `n p_{A,f}(n) = ∑_{i + j = n} p_{A,f}(i) f_A(j)`. -/
theorem mul_coeff_genFunA (m : ℕ) :
    (m : ℂ) * coeff m (genFunA A f) =
      ∑ p ∈ antidiagonal m, coeff p.1 (genFunA A f) * fA A f p.2 := by
  have h := congrArg (coeff m) (X_mul_derivative_prod_genFunFactor A f (range (m + 1)))
  rw [coeff_X_mul_derivative, coeff_mul] at h
  rw [coeff_genFunA A f m (Nat.lt_succ_self m), h]
  refine sum_congr rfl fun p hp ↦ ?_
  have h1 := mem_antidiagonal.mp hp
  rw [coeff_genFunA A f p.1 (N := m + 1) (by omega), coeff_sum_logDerivTerm A f p.2 (by omega)]

/-- Apostol §14.10 (22): `x F_A'(x) = F_A(x) ∑_{k ≥ 1} f_A(k) x^k`. -/
theorem X_mul_derivative_genFunA :
    X * derivative (genFunA A f) = genFunA A f * mk (fA A f) := by
  ext m
  rw [coeff_X_mul_derivative, coeff_mul, mul_coeff_genFunA]
  simp only [coeff_mk]

theorem fA_zero : fA A f 0 = 0 := by
  simp [fA]

/-- **Theorem 14.8** (Apostol). For a set `A` of positive integers and an arithmetical function `f`,
the coefficients `p_{A,f}(n)` of `F_A(x) = ∏_{n ∈ A} (1 - xⁿ)^{-f(n)/n}` satisfy `p_{A,f}(0) = 1` and
`n p_{A,f}(n) = ∑_{k=1}^n f_A(k) p_{A,f}(n - k)` with `f_A(k) = ∑_{d ∣ k, d ∈ A} f(d)`. The product
converges in the topology of formal power series (`HasProd`). -/
@[kb "apostol1976" "Thm 14.8, p. 323"]
theorem apostol_thm_14_8 :
    HasProd (genFunFactor A f) (genFunA A f) ∧ coeff 0 (genFunA A f) = 1 ∧
      ∀ n : ℕ, (n : ℂ) * coeff n (genFunA A f) =
        ∑ k ∈ Icc 1 n, fA A f k * coeff (n - k) (genFunA A f) := by
  refine ⟨(multipliable_genFunFactor A f).hasProd, ?_, fun n ↦ ?_⟩
  · rw [coeff_genFunA A f 0 (N := 1) one_pos]
    simp [genFunFactor, oneSubXPowRpowNeg]
  · rw [mul_coeff_genFunA, ← Nat.sum_antidiagonal_swap]
    simp only [Prod.fst_swap, Prod.snd_swap]
    rw [Nat.sum_antidiagonal_eq_sum_range_succ (fun i j ↦ coeff j (genFunA A f) * fA A f i),
      sum_range_succ', fA_zero, mul_zero, add_zero, ← Finset.Ico_add_one_right_eq_Icc,
      sum_Ico_eq_sum_range]
    refine sum_congr (by simp) fun k _ ↦ ?_
    rw [add_comm 1 k, mul_comm]

end Product

end NTKB.Apostol
