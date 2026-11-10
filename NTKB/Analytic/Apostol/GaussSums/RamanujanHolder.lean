/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Apostol.GaussSums.RamanujanClosedForm
import NTKB.Analytic.Apostol.Averages.DivisorSums

/-!
# Theorem 8.8 of Apostol (main computation)

See `NTKB/Analytic/Apostol/GaussSums/RamanujanClosedForm.lean` for the statement and the plan.
-/

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

namespace NTKB.Apostol

variable {f h : ArithmeticFunction ℂ}

/-- `g(Ne) = g(N) g(e)` if `(N, e) = 1` and `0` otherwise, for `g = μ h`. -/
theorem pmul_moebius_apply_mul (hh : h.IsMultiplicative) (N e : ℕ) :
    ((μ : ArithmeticFunction ℂ).pmul h) (N * e) =
      if N.Coprime e then
        ((μ : ArithmeticFunction ℂ).pmul h) N * ((μ : ArithmeticFunction ℂ).pmul h) e
      else 0 := by
  split_ifs with hc
  · exact (isMultiplicative_moebius.intCast.pmul hh).map_mul_of_coprime hc
  · have : ¬ Squarefree (N * e) := fun hsq ↦ hc (Nat.squarefree_mul_iff.1 hsq).1
    rw [pmul_apply, intCoe_apply, moebius_eq_zero_of_not_squarefree this]
    simp

/-- `∏_{p ∣ a} (1 - [p ∤ N] r(p)) · ∏_{p ∣ N} (1 - r(p)) = ∏_{p ∣ aN} (1 - r(p))`. -/
theorem prod_ratioCoprime_mul_prod {a N : ℕ} (ha0 : a ≠ 0) (hN0 : N ≠ 0) :
    (∏ p ∈ a.primeFactors, (1 - ratioCoprime h f N p)) *
      ∏ p ∈ N.primeFactors, (1 - h p / f p) = ∏ p ∈ (a * N).primeFactors, (1 - h p / f p) := by
  have h1 : ∏ p ∈ a.primeFactors, (1 - ratioCoprime h f N p) =
      ∏ p ∈ a.primeFactors.filter (fun p ↦ p.Coprime N), (1 - h p / f p) := by
    rw [← prod_filter_mul_prod_filter_not a.primeFactors (fun p ↦ p.Coprime N)]
    have hi : ∏ p ∈ a.primeFactors.filter (fun p ↦ ¬ p.Coprime N),
        (1 - ratioCoprime h f N p) = 1 :=
      prod_eq_one fun p hp' ↦ by simp [ratioCoprime, (mem_filter.1 hp').2]
    rw [hi, mul_one]
    exact prod_congr rfl fun p hp' ↦ by simp [ratioCoprime, (mem_filter.1 hp').2]
  have hset : (a * N).primeFactors =
      a.primeFactors.filter (fun p ↦ p.Coprime N) ∪ N.primeFactors := by
    rw [Nat.primeFactors_mul ha0 hN0]
    ext p
    simp only [mem_union, mem_filter]
    constructor
    · rintro (hpa | hpN)
      · by_cases hc : p.Coprime N
        · exact Or.inl ⟨hpa, hc⟩
        · right
          have hpp := Nat.prime_of_mem_primeFactors hpa
          rw [Nat.Prime.coprime_iff_not_dvd hpp, not_not] at hc
          exact Nat.mem_primeFactors.2 ⟨hpp, hc, hN0⟩
      · exact Or.inr hpN
    · rintro (⟨hpa, -⟩ | hpN)
      · exact Or.inl hpa
      · exact Or.inr hpN
  have hdisj : Disjoint (a.primeFactors.filter (fun p ↦ p.Coprime N)) N.primeFactors := by
    rw [disjoint_left]
    intro p hp' hpN
    obtain ⟨hpa, hc⟩ := mem_filter.1 hp'
    exact (Nat.prime_of_mem_primeFactors hpa).one_lt.ne'
      (Nat.Coprime.eq_one_of_dvd hc (Nat.dvd_of_mem_primeFactors hpN))
  rw [h1, hset, prod_union hdisj]

/-- **Apostol, Theorem 8.8.** For `f` completely multiplicative with `f(p) ≠ 0`, `h`
multiplicative, `g = μ h`, `F = f * g` and `N = k/(n,k)`: `s_k(n) F(N) = F(k) g(N)`. -/
@[kb "apostol1976" "Thm 8.8, p. 163"]
theorem gcdSum_mul_eq (hh : h.IsMultiplicative) (hf : IsCompletelyMultiplicative f)
    (hp : ∀ p : ℕ, p.Prime → f p ≠ 0) {k : ℕ} (hk : k ≠ 0) (n : ℕ) :
    gcdSum f ((μ : ArithmeticFunction ℂ).pmul h) k n *
        (f * (μ : ArithmeticFunction ℂ).pmul h) (k / Nat.gcd n k) =
      (f * (μ : ArithmeticFunction ℂ).pmul h) k *
        ((μ : ArithmeticFunction ℂ).pmul h) (k / Nat.gcd n k) := by
  set g := (μ : ArithmeticFunction ℂ).pmul h with hg
  set a := Nat.gcd n k
  set N := k / a
  have ha : a ∣ k := Nat.gcd_dvd_right n k
  have ha0 : a ≠ 0 := Nat.gcd_ne_zero_right hk
  have hkaN : k = a * N := (Nat.mul_div_cancel' ha).symm
  have hN0 : N ≠ 0 := fun h0 ↦ hk (by rw [hkaN, h0, mul_zero])
  -- `s_k(n) = f(a) g(N) ∏_{p ∣ a} (1 - [p ∤ N] h(p)/f(p))`
  have hs : gcdSum f g k n =
      f a * g N * ∏ p ∈ a.primeFactors, (1 - ratioCoprime h f N p) := by
    rw [(isMultiplicative_ratioCoprime hh hf N).prodPrimeFactors_one_sub _ ha0, mul_sum, gcdSum,
      ← Nat.sum_div_divisors]
    refine sum_congr rfl fun e he ↦ ?_
    have hea := Nat.dvd_of_mem_divisors he
    have he0 : e ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors he)
    have hfe := hf.apply_ne_zero hp he0
    have hae : 0 < a / e :=
      Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero ha0) hea) (Nat.pos_of_ne_zero he0)
    have hk' : k / (a / e) = N * e := by
      have : k = (a / e) * (N * e) := by
        rw [show (a / e) * (N * e) = (a / e * e) * N by ring, Nat.div_mul_cancel hea]
        exact hkaN
      rw [this, Nat.mul_div_cancel_left _ hae]
    rw [hk', pmul_moebius_apply_mul hh]
    have hfa : f a = f (a / e) * f e := by rw [← hf.2, Nat.div_mul_cancel hea]
    simp only [ratioCoprime, coe_mk, hg, pmul_apply, intCoe_apply]
    by_cases hc : N.Coprime e
    · rw [if_pos hc, if_pos (Nat.Coprime.symm hc), hfa]
      field_simp
      ring
    · rw [if_neg hc, if_neg (fun h' ↦ hc (Nat.Coprime.symm h'))]
      simp
  have hFk := mul_pmul_moebius_apply hh hf hp hk
  have hFN := mul_pmul_moebius_apply hh hf hp hN0
  have hprod := prod_ratioCoprime_mul_prod (h := h) (f := f) ha0 hN0
  rw [hs, hFN, hFk]
  rw [← hkaN] at hprod
  have hfk : f k = f a * f N := by rw [hkaN, hf.2]
  rw [hfk, ← hprod]
  ring

/-- **Apostol, Theorem 8.8**, quotient form: if moreover `f(p) ≠ h(p)` for all primes, then
`F(N) ≠ 0` and `s_k(n) = F(k) g(N)/F(N)`. -/
@[kb "apostol1976" "Thm 8.8, p. 163"]
theorem gcdSum_eq_div (hh : h.IsMultiplicative) (hf : IsCompletelyMultiplicative f)
    (hp : ∀ p : ℕ, p.Prime → f p ≠ 0) (hfh : ∀ p : ℕ, p.Prime → f p ≠ h p) {k : ℕ} (hk : k ≠ 0)
    (n : ℕ) :
    gcdSum f ((μ : ArithmeticFunction ℂ).pmul h) k n =
      (f * (μ : ArithmeticFunction ℂ).pmul h) k *
        ((μ : ArithmeticFunction ℂ).pmul h) (k / Nat.gcd n k) /
          (f * (μ : ArithmeticFunction ℂ).pmul h) (k / Nat.gcd n k) := by
  have hN0 : k / Nat.gcd n k ≠ 0 :=
    (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hk) (Nat.gcd_dvd_right n k))
      (Nat.gcd_pos_of_pos_right _ (Nat.pos_of_ne_zero hk))).ne'
  have hF : (f * (μ : ArithmeticFunction ℂ).pmul h) (k / Nat.gcd n k) ≠ 0 := by
    rw [mul_pmul_moebius_apply hh hf hp hN0]
    refine mul_ne_zero (hf.apply_ne_zero hp hN0) (prod_ne_zero_iff.2 fun p hp' ↦ ?_)
    have hpp := Nat.prime_of_mem_primeFactors hp'
    rw [sub_ne_zero, ne_comm, Ne, div_eq_one_iff_eq (hp p hpp)]
    exact fun h' ↦ hfh p hpp h'.symm
  rw [eq_div_iff hF, gcdSum_mul_eq hh hf hp hk]

theorem isCompletelyMultiplicative_natCoe_id :
    IsCompletelyMultiplicative ((ArithmeticFunction.id : ArithmeticFunction ℕ) :
      ArithmeticFunction ℂ) :=
  ⟨by simp [natCoe_apply, ArithmeticFunction.id_apply],
    fun m n ↦ by simp [natCoe_apply, ArithmeticFunction.id_apply]⟩

/-- `(N * μ)(m) = φ(m)` (Theorem 2.3). -/
theorem natCoe_id_mul_moebius_apply {m : ℕ} (hm : m ≠ 0) :
    (((ArithmeticFunction.id : ArithmeticFunction ℕ) : ArithmeticFunction ℂ) *
      (μ : ArithmeticFunction ℂ)) m = m.totient := by
  rw [mul_comm, mul_apply_eq_sum_divisors]
  have := congrArg (fun z : ℤ ↦ (z : ℂ)) (totient_eq_sum_moebius_mul (Nat.pos_of_ne_zero hm))
  simp only [Int.cast_natCast, Int.cast_sum, Int.cast_mul] at this
  rw [this]
  refine sum_congr rfl fun d hd ↦ ?_
  simp [natCoe_apply, intCoe_apply, ArithmeticFunction.id_apply]

/-- **Apostol, §8.4, Example** (Hölder's formula): `c_k(n) = φ(k) μ(N)/φ(N)` with
`N = k/(n,k)`, `k ≥ 1`. -/
@[kb "apostol1976" "Thm 8.8, Example, p. 164"]
theorem ramanujanSum_eq_totient_mul_moebius_div {k : ℕ} (hk : k ≠ 0) (n : ℕ) :
    ramanujanSum k n =
      (k.totient : ℂ) * (μ (k / Nat.gcd n k) : ℂ) / ((k / Nat.gcd n k).totient : ℂ) := by
  have hN0 : k / Nat.gcd n k ≠ 0 :=
    (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hk) (Nat.gcd_dvd_right n k))
      (Nat.gcd_pos_of_pos_right _ (Nat.pos_of_ne_zero hk))).ne'
  have h := gcdSum_eq_div (f := ((ArithmeticFunction.id : ArithmeticFunction ℕ) :
      ArithmeticFunction ℂ)) (h := (ζ : ArithmeticFunction ℂ)) isMultiplicative_zeta.natCast
    isCompletelyMultiplicative_natCoe_id
    (fun p hp ↦ by simp [natCoe_apply, ArithmeticFunction.id_apply, hp.ne_zero])
    (fun p hp ↦ by
      simp only [natCoe_apply, ArithmeticFunction.id_apply, zeta_apply_ne hp.ne_zero,
        Nat.cast_one, Ne, Nat.cast_eq_one]
      exact hp.one_lt.ne')
    hk n
  rw [pmul_zeta, natCoe_id_mul_moebius_apply hk, natCoe_id_mul_moebius_apply hN0,
    intCoe_apply] at h
  rw [ramanujanSum_eq_gcdSum (Nat.pos_of_ne_zero hk), h]

end NTKB.Apostol
