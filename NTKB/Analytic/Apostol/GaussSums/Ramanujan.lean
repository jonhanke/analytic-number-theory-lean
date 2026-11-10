/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Apostol.ArithmeticFunctions.Multiplicative
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.NumberTheory.DirichletCharacter.Basic

/-!
# Ramanujan's sum and the sums `s_k(n)` (Apostol, Chapter 8, §§8.1–8.4, 8.7)

With `e(x) = e^{2πix}`:
* Theorem 8.1: `∑_{m=0}^{k-1} e(mn/k) = k` if `k ∣ n` and `0` otherwise;
* `s_k(n) = ∑_{d ∣ (n,k)} f(d) g(k/d)` (`NTKB.Apostol.gcdSum`) and Ramanujan's sum
  `c_k(n) = ∑_{m mod k, (m,k)=1} e(mn/k)` (`NTKB.Apostol.ramanujanSum`; not in Mathlib);
* Theorem 8.5: the finite Fourier expansion of `s_k(n)`, with coefficients
  `a_k(m) = ∑_{d ∣ (m,k)} g(d) f(k/d) d/k`;
* Theorem 8.6: `c_k(n) = ∑_{d ∣ (n,k)} d μ(k/d)`;
* Theorem 8.7: for multiplicative `f, g`, `s_{mk}(ab) = s_m(a) s_k(b)` when `(a,k) = (b,m) = 1`
  **and `(m,k) = 1`**. The book omits `(m,k) = 1`, which is needed: for Ramanujan's sum
  `c_4(1) = μ(4) = 0` but `c_2(1)² = μ(2)² = 1` (`ramanujanSum_four_one`, `ramanujanSum_two_one`);
* Theorem 8.14: every nonprincipal character modulo a prime is primitive.
-/

open Finset ArithmeticFunction Complex
open scoped ArithmeticFunction.Moebius Real

namespace NTKB.Apostol

/-- `e(x) = e^{2πix}`. -/
noncomputable def eC (x : ℝ) : ℂ := Complex.exp (2 * π * I * x)

theorem eC_add (x y : ℝ) : eC (x + y) = eC x * eC y := by
  rw [eC, eC, eC, ← Complex.exp_add]; push_cast; ring_nf

theorem eC_int (n : ℤ) : eC n = 1 := by
  rw [eC, Complex.exp_eq_one_iff]; exact ⟨n, by push_cast; ring⟩

theorem eC_nat_mul (m : ℕ) (x : ℝ) : eC (m * x) = eC x ^ m := by
  rw [eC, eC, ← Complex.exp_nat_mul]; push_cast; ring_nf

/-- `e(x) = 1` iff `x` is an integer. -/
theorem eC_eq_one_iff (x : ℝ) : eC x = 1 ↔ ∃ n : ℤ, x = n := by
  rw [eC, Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have h2 : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
    have : (x : ℂ) = n := by
      have := hn
      rw [show (2 * π * I * x : ℂ) = x * (2 * π * I) by ring] at this
      exact mul_right_cancel₀ h2 this
    exact_mod_cast this
  · rintro ⟨n, rfl⟩; exact ⟨n, by push_cast; ring⟩

/-- **Apostol, Theorem 8.1.** For `k ≥ 1`, `∑_{m=0}^{k-1} e(mn/k) = k` if `k ∣ n`, else `0`. -/
@[kb "apostol1976" "Thm 8.1, p. 157"]
theorem sum_range_eC (k : ℕ) (hk : 0 < k) (n : ℤ) :
    ∑ m ∈ range k, eC (m * n / k) = if (k : ℤ) ∣ n then (k : ℂ) else 0 := by
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  set z := eC (n / k)
  have hz : ∀ m : ℕ, eC (m * n / k) = z ^ m := fun m ↦ by rw [mul_div_assoc, eC_nat_mul]
  simp_rw [hz]
  split_ifs with hdvd
  · obtain ⟨q, hq⟩ := hdvd
    have : z = 1 := by
      rw [eC_eq_one_iff]; exact ⟨q, by rw [hq]; push_cast; field_simp⟩
    simp [this]
  · have hz1 : z ≠ 1 := by
      rw [Ne, eC_eq_one_iff]
      rintro ⟨q, hq⟩
      apply hdvd
      refine ⟨q, ?_⟩
      have : (n : ℝ) = k * q := by rw [div_eq_iff hk'] at hq; linarith
      exact_mod_cast this
    have hzk : z ^ k = 1 := by
      rw [← eC_nat_mul, mul_div_cancel₀ _ hk']; exact eC_int n
    rw [geom_sum_eq hz1, hzk, sub_self, zero_div]

/-! ## The sums `s_k(n)` and Ramanujan's sum -/

/-- `s_k(n) = ∑_{d ∣ (n,k)} f(d) g(k/d)` (Apostol, §8.3, (6)). -/
noncomputable def gcdSum (f g : ArithmeticFunction ℂ) (k n : ℕ) : ℂ :=
  ∑ d ∈ (Nat.gcd n k).divisors, f d * g (k / d)

/-- Ramanujan's sum `c_k(n) = ∑_{m mod k, (m,k) = 1} e(mn/k)` (Apostol, §8.3). -/
noncomputable def ramanujanSum (k n : ℕ) : ℂ :=
  ∑ m ∈ range k with m.Coprime k, eC (m * n / k)

/-- **Apostol, Theorem 8.5.** `s_k(n) = ∑_{m mod k} a_k(m) e(mn/k)` with
`a_k(m) = ∑_{d ∣ (m,k)} g(d) f(k/d) d/k`. -/
@[kb "apostol1976" "Thm 8.5, p. 161"]
theorem gcdSum_eq_fourier (f g : ArithmeticFunction ℂ) {k : ℕ} (hk : 0 < k) (n : ℕ) :
    gcdSum f g k n = ∑ m ∈ range k,
      (∑ d ∈ (Nat.gcd m k).divisors, g d * f (k / d) * ((d : ℂ) / k)) * eC (m * n / k) := by
  -- interchange: `∑_m ∑_{d ∣ (m,k)} = ∑_{d ∣ k} ∑_{j < k/d}` with `m = jd`
  have hk' : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  have step : ∀ d ∈ k.divisors, ∑ m ∈ range k with d ∣ m, eC (m * n / k) =
      if ((k / d : ℕ) : ℤ) ∣ (n : ℤ) then ((k / d : ℕ) : ℂ) else 0 := by
    intro d hd
    have hdk := Nat.dvd_of_mem_divisors hd
    have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
    have hkd : 0 < k / d := Nat.div_pos (Nat.le_of_dvd hk hdk) hd0
    rw [← sum_range_eC (k / d) hkd n]
    -- `m = d j`, `j < k/d`
    refine (sum_nbij' (fun m ↦ m / d) (fun j ↦ j * d) ?_ ?_ ?_ ?_ ?_)
    · intro m hm
      simp only [mem_filter, mem_range] at hm
      simp only [mem_range]
      exact Nat.div_lt_div_of_lt_of_dvd hdk hm.1
    · intro j hj
      simp only [mem_range] at hj
      simp only [mem_filter, mem_range]
      refine ⟨?_, dvd_mul_left d j⟩
      calc j * d < (k / d) * d := Nat.mul_lt_mul_of_pos_right hj hd0
        _ = k := Nat.div_mul_cancel hdk
    · intro m hm
      simp only [mem_filter] at hm
      exact Nat.div_mul_cancel hm.2
    · intro j _
      exact Nat.mul_div_cancel j hd0
    · intro m hm
      simp only [mem_filter] at hm
      obtain ⟨j, rfl⟩ := hm.2
      rw [Nat.mul_div_cancel_left j hd0]
      congr 1
      have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd0.ne'
      rw [Nat.cast_div hdk hd']
      push_cast
      field_simp
  -- expand the right side
  have hrhs : ∑ m ∈ range k,
      (∑ d ∈ (Nat.gcd m k).divisors, g d * f (k / d) * ((d : ℂ) / k)) * eC (m * n / k) =
      ∑ d ∈ k.divisors, g d * f (k / d) * ((d : ℂ) / k) *
        ∑ m ∈ range k with d ∣ m, eC (m * n / k) := by
    have hmem : ∀ m d, m ∈ range k ∧ d ∈ (Nat.gcd m k).divisors ↔
        m ∈ (range k).filter (d ∣ ·) ∧ d ∈ k.divisors := by
      intro m d
      simp only [mem_range, Nat.mem_divisors, mem_filter]
      constructor
      · rintro ⟨hm, hd, -⟩
        have := Nat.dvd_gcd_iff.1 hd
        exact ⟨⟨hm, this.1⟩, this.2, hk.ne'⟩
      · rintro ⟨⟨hm, hdm⟩, hdk, -⟩
        exact ⟨hm, Nat.dvd_gcd hdm hdk, (Nat.gcd_pos_of_pos_right _ hk).ne'⟩
    simp_rw [sum_mul, mul_sum]
    rw [sum_comm' hmem]
  have hrhs2 : ∑ d ∈ k.divisors, g d * f (k / d) * ((d : ℂ) / k) *
      ∑ m ∈ range k with d ∣ m, eC (m * n / k) = ∑ d ∈ k.divisors,
        g d * f (k / d) * ((d : ℂ) / k) *
          (if ((k / d : ℕ) : ℤ) ∣ (n : ℤ) then ((k / d : ℕ) : ℂ) else 0) :=
    sum_congr rfl fun d hd ↦ by rw [step d hd]
  rw [hrhs, hrhs2, gcdSum]
  -- `∑_{d ∣ k, (k/d) ∣ n} g(d) f(k/d) = ∑_{e ∣ (n,k)} f(e) g(k/e)` (`e = k/d`)
  simp only [mul_ite, mul_zero]
  rw [← sum_filter]
  refine sum_nbij' (fun e ↦ k / e) (fun d ↦ k / d) ?_ ?_ ?_ ?_ ?_
  · intro e he
    simp only [mem_coe, Nat.mem_divisors] at he
    have hek : e ∣ k := (Nat.dvd_gcd_iff.1 he.1).2
    have hen : e ∣ n := (Nat.dvd_gcd_iff.1 he.1).1
    have he0 : 0 < e := Nat.pos_of_dvd_of_pos hek hk
    simp only [mem_coe, mem_filter, Nat.mem_divisors]
    refine ⟨⟨Nat.div_dvd_of_dvd hek, hk.ne'⟩, ?_⟩
    rw [Nat.div_div_self hek hk.ne']
    exact_mod_cast hen
  · intro d hd
    simp only [mem_coe, mem_filter, Nat.mem_divisors] at hd
    simp only [mem_coe, Nat.mem_divisors]
    refine ⟨Nat.dvd_gcd (by exact_mod_cast hd.2) (Nat.div_dvd_of_dvd hd.1.1), ?_⟩
    exact (Nat.gcd_pos_of_pos_right _ hk).ne'
  · intro e he
    simp only [mem_coe, Nat.mem_divisors] at he
    exact Nat.div_div_self (Nat.dvd_gcd_iff.1 he.1).2 hk.ne'
  · intro d hd
    simp only [mem_coe, mem_filter, Nat.mem_divisors] at hd
    exact Nat.div_div_self hd.1.1 hk.ne'
  · intro e he
    simp only [Nat.mem_divisors] at he
    have hek : e ∣ k := (Nat.dvd_gcd_iff.1 he.1).2
    have he0 : 0 < e := Nat.pos_of_dvd_of_pos hek hk
    rw [Nat.div_div_self hek hk.ne']
    have hke : ((k / e : ℕ) : ℂ) = (k : ℂ) / e := by
      rw [Nat.cast_div hek (by exact_mod_cast he0.ne')]
    rw [hke]
    have he0' : (e : ℂ) ≠ 0 := by exact_mod_cast he0.ne'
    field_simp

/-- **Apostol, Theorem 8.6.** `c_k(n) = ∑_{d ∣ (n,k)} d μ(k/d)`. -/
@[kb "apostol1976" "Thm 8.6, p. 162"]
theorem ramanujanSum_eq {k : ℕ} (hk : 0 < k) (n : ℕ) :
    ramanujanSum k n = ∑ d ∈ (Nat.gcd n k).divisors, (d : ℂ) * μ (k / d) := by
  -- Apostol: Theorem 8.5 with `f = N`, `g = μ`; the Fourier coefficient is `[ (m,k) = 1 ]`
  have h := gcdSum_eq_fourier (ArithmeticFunction.id : ArithmeticFunction ℕ)
    (μ : ArithmeticFunction ℂ) hk n
  have hcoef : ∀ m ∈ range k, (∑ d ∈ (Nat.gcd m k).divisors, (μ : ArithmeticFunction ℂ) d *
      ((ArithmeticFunction.id : ArithmeticFunction ℕ) : ArithmeticFunction ℂ) (k / d) *
        ((d : ℂ) / k)) = if m.Coprime k then 1 else 0 := by
    intro m _
    have hk' : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
    have e : ∀ d ∈ (Nat.gcd m k).divisors, (μ : ArithmeticFunction ℂ) d *
        ((ArithmeticFunction.id : ArithmeticFunction ℕ) : ArithmeticFunction ℂ) (k / d) *
          ((d : ℂ) / k) = (μ d : ℂ) := by
      intro d hd
      have hdk : d ∣ k := (Nat.dvd_gcd_iff.1 (Nat.dvd_of_mem_divisors hd)).2
      have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mem_divisors hd).ne'
      simp only [intCoe_apply, natCoe_apply, ArithmeticFunction.id_apply]
      rw [Nat.cast_div hdk hd0]
      field_simp
    rw [sum_congr rfl e, sum_divisors_moebius, ArithmeticFunction.one_apply]
  rw [sum_congr rfl fun m hm ↦ by rw [hcoef m hm]] at h
  simp only [ite_mul, one_mul, zero_mul] at h
  rw [← sum_filter] at h
  rw [ramanujanSum, ← h, gcdSum]
  refine sum_congr rfl fun d _ ↦ ?_
  simp [natCoe_apply, intCoe_apply]

theorem ramanujanSum_two_one : ramanujanSum 2 1 = -1 := by
  rw [ramanujanSum_eq two_pos]
  simp [Nat.divisors_one, moebius_apply_prime Nat.prime_two]

theorem ramanujanSum_four_one : ramanujanSum 4 1 = 0 := by
  rw [ramanujanSum_eq (by norm_num)]
  have : μ 4 = 0 := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, moebius_apply_prime_pow Nat.prime_two two_ne_zero]
    simp
  simp [Nat.divisors_one, this]

/-- The book's Theorem 8.7 without `(m,k) = 1` fails: `c_{2·2}(1·1) ≠ c_2(1) c_2(1)`. -/
theorem ramanujanSum_counterexample_8_7 :
    ramanujanSum (2 * 2) (1 * 1) ≠ ramanujanSum 2 1 * ramanujanSum 2 1 := by
  rw [show (2 * 2 : ℕ) = 4 by norm_num, show (1 * 1 : ℕ) = 1 by norm_num, ramanujanSum_four_one,
    ramanujanSum_two_one]
  norm_num

/-! ## Theorem 8.7 -/

/-- **Apostol, Theorem 8.7**, corrected: for multiplicative `f, g`,
`s_{mk}(ab) = s_m(a) s_k(b)` whenever `(a,k) = (b,m) = 1` and `(m,k) = 1` (the last hypothesis is
missing in the book; see `ramanujanSum_counterexample_8_7`). -/
@[kb "apostol1976" "Thm 8.7, p. 162"]
theorem gcdSum_mul_mul {f g : ArithmeticFunction ℂ} (hf : f.IsMultiplicative)
    (hg : g.IsMultiplicative) {m k a b : ℕ} (hmk : m.Coprime k) (hak : a.Coprime k)
    (hbm : b.Coprime m) :
    gcdSum f g (m * k) (a * b) = gcdSum f g m a * gcdSum f g k b := by
  have hgcd : Nat.gcd (a * b) (m * k) = Nat.gcd a m * Nat.gcd b k := by
    rw [Nat.Coprime.gcd_mul _ hmk, Nat.Coprime.gcd_mul_right_cancel a hbm,
      Nat.Coprime.gcd_mul_left_cancel b hak]
  have hcop : (Nat.gcd a m).Coprime (Nat.gcd b k) :=
    (hmk.coprime_dvd_left (Nat.gcd_dvd_right a m)).coprime_dvd_right (Nat.gcd_dvd_right b k)
  rw [gcdSum, hgcd, sum_divisors_mul_of_coprime hcop, gcdSum, gcdSum, sum_mul_sum, sum_product]
  refine sum_congr rfl fun d1 hd1 ↦ sum_congr rfl fun d2 hd2 ↦ ?_
  have h1 : d1 ∣ m := (Nat.dvd_of_mem_divisors hd1).trans (Nat.gcd_dvd_right a m)
  have h2 : d2 ∣ k := (Nat.dvd_of_mem_divisors hd2).trans (Nat.gcd_dvd_right b k)
  have hd : d1.Coprime d2 := (hmk.coprime_dvd_left h1).coprime_dvd_right h2
  have hq : (m / d1).Coprime (k / d2) :=
    (hmk.coprime_dvd_left (Nat.div_dvd_of_dvd h1)).coprime_dvd_right (Nat.div_dvd_of_dvd h2)
  dsimp only
  rw [hf.map_mul_of_coprime hd, ← Nat.div_mul_div_comm h1 h2, hg.map_mul_of_coprime hq]
  ring

theorem ramanujanSum_eq_gcdSum {k : ℕ} (hk : 0 < k) (n : ℕ) :
    ramanujanSum k n = gcdSum ((ArithmeticFunction.id : ArithmeticFunction ℕ) :
      ArithmeticFunction ℂ) (μ : ArithmeticFunction ℂ) k n := by
  rw [ramanujanSum_eq hk, gcdSum]
  simp [natCoe_apply, intCoe_apply]

/-- **Apostol, §8.4, Example** (corrected as Theorem 8.7): `c_{mk}(ab) = c_m(a) c_k(b)` whenever
`(a,k) = (b,m) = (m,k) = 1`. -/
@[kb "apostol1976" "§8.4, Example, p. 163"]
theorem ramanujanSum_mul_mul {m k a b : ℕ} (hm : 0 < m) (hk : 0 < k) (hmk : m.Coprime k)
    (hak : a.Coprime k) (hbm : b.Coprime m) :
    ramanujanSum (m * k) (a * b) = ramanujanSum m a * ramanujanSum k b := by
  rw [ramanujanSum_eq_gcdSum (Nat.mul_pos hm hk), ramanujanSum_eq_gcdSum hm,
    ramanujanSum_eq_gcdSum hk]
  exact gcdSum_mul_mul (isMultiplicative_id.natCast) (isMultiplicative_moebius.intCast) hmk hak hbm

/-! ## Theorem 8.14 -/

/-- **Apostol, Theorem 8.14.** Every nonprincipal character modulo a prime `p` is primitive. -/
@[kb "apostol1976" "Thm 8.14, p. 168"]
theorem isPrimitive_of_ne_one_of_prime {R : Type*} [CommMonoidWithZero R] {p : ℕ}
    (hp : p.Prime) {χ : DirichletCharacter R p} (hχ : χ ≠ 1) : χ.IsPrimitive := by
  have : NeZero p := ⟨hp.ne_zero⟩
  rcases hp.eq_one_or_self_of_dvd _ χ.conductor_dvd_level with h | h
  · exact absurd (DirichletCharacter.eq_one_iff_conductor_eq_one.2 h) hχ
  · exact h

end NTKB.Apostol
