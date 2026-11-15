/- Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license. -/
import NTKB.Attr
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Data.Nat.Totient
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.NumberTheory.DirichletCharacter.GaussSum

/-!
# Ramanujan sums (Davenport, Chapter 26, pp. 148–149)

`c_q(n) = ∑_{a mod q, (a, q) = 1} e(an/q)` with `e(x) = exp(2πix)`.

* **26-14** (formula (F)): `c_q(n) = ∑_{d ∣ (q, n)} d μ(q/d)` (`ramanujanSum_eq_sum_dvd`);
* **26-15**: `c_q(n)` is multiplicative in `q` (`ramanujanSum_mul`), and
  `c_q(n) = μ(q/(q, n)) φ(q)/φ(q/(q, n))` (`ramanujanSum_eq_moebius_mul_totient_div`); in particular
  `|c_q(n)| ≤ φ(q)` and `c_q(n) = μ(q)` for `(n, q) = 1`.

The proof of (F) is Davenport's: the sum over all `a mod q` of `e(an/q)` is `q [q ∣ n]`, and Möbius
inversion over `d = (a, q)` removes the condition `(a, q) = 1`.
-/

open Finset Real
open scoped ArithmeticFunction.Moebius

namespace NTKB.Davenport

private lemma sum_moebius_divisors (k : ℕ) :
    ∑ d ∈ k.divisors, (μ d : ℤ) = if k = 1 then 1 else 0 := by
  have := congrArg (fun f : ArithmeticFunction ℤ ↦ f k) ArithmeticFunction.moebius_mul_coe_zeta
  rw [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at this
  exact this

private lemma exp_sum_range {m : ℕ} (hm : 0 < m) (n : ℤ) :
    ∑ b ∈ range m, Complex.exp (2 * π * Complex.I * ((b : ℂ) * n / m)) =
      if (m : ℤ) ∣ n then (m : ℂ) else 0 := by
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  set z : Complex := Complex.exp (2 * π * Complex.I * ((n : ℂ) / m)) with hz
  have h1 : ∀ b : ℕ, Complex.exp (2 * π * Complex.I * ((b : ℂ) * n / m)) = z ^ b := by
    intro b
    rw [hz, ← Complex.exp_nat_mul]
    congr 1
    ring
  simp_rw [h1]
  have hzm : z ^ m = 1 := by
    rw [hz, ← Complex.exp_nat_mul]
    have : (m : ℂ) * (2 * π * Complex.I * ((n : ℂ) / m)) = n * (2 * π * Complex.I) := by
      field_simp
    rw [this]
    exact Complex.exp_int_mul_two_pi_mul_I n
  by_cases hd : (m : ℤ) ∣ n
  · obtain ⟨k, hk⟩ := hd
    have : z = 1 := by
      rw [hz, Complex.exp_eq_one_iff]
      refine ⟨k, ?_⟩
      rw [hk]
      push_cast
      field_simp
    simp only [this, one_pow, sum_const, card_range, nsmul_eq_mul, mul_one]
    simp [show (m : ℤ) ∣ n from ⟨k, hk⟩]
  · have hz1 : z ≠ 1 := by
      intro h
      rw [hz, Complex.exp_eq_one_iff] at h
      obtain ⟨k, hk⟩ := h
      apply hd
      refine ⟨k, ?_⟩
      have : (n : ℂ) = (m * k : ℤ) := by
        push_cast
        have hpi : (2 * π * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
        field_simp at hk
        exact hk
      exact_mod_cast this
    rw [geom_sum_eq hz1, hzm]
    simp only [hd, ↓reduceIte]
    simp

/-- The Ramanujan sum `c_q(n) = ∑_{0 ≤ a < q, (a, q) = 1} e(an/q)`. -/
noncomputable def ramanujanSum (q : ℕ) (n : ℤ) : ℂ :=
  ∑ a ∈ (range q).filter (fun a ↦ Nat.Coprime a q),
    Complex.exp (2 * π * Complex.I * ((a : ℂ) * n / q))

private lemma exp_sum_dvd {d m : ℕ} (hd : 0 < d) (hm : 0 < m) (n : ℤ) :
    ∑ a ∈ (range (d * m)).filter (fun a ↦ d ∣ a),
      Complex.exp (2 * π * Complex.I * ((a : ℂ) * n / ((d * m : ℕ) : ℂ))) =
      if (m : ℤ) ∣ n then (m : ℂ) else 0 := by
  rw [← exp_sum_range hm n]
  have : (range (d * m)).filter (fun a ↦ d ∣ a) = (range m).image (fun b ↦ d * b) := by
    ext a
    simp only [mem_filter, mem_range, mem_image]
    constructor
    · rintro ⟨h1, k, rfl⟩
      exact ⟨k, by nlinarith, rfl⟩
    · rintro ⟨b, hb, rfl⟩
      exact ⟨by nlinarith, dvd_mul_right _ _⟩
  rw [this, sum_image (fun x _ y _ h ↦ Nat.eq_of_mul_eq_mul_left hd h)]
  refine sum_congr rfl fun b _ ↦ ?_
  congr 2
  have : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  push_cast
  field_simp

/-- **Davenport, Ch. 26, p. 148, (F) (row 26-14)**: `c_q(n) = ∑_{d ∣ q, d ∣ n} d μ(q/d)`. -/
@[kb "davenport1980" "Ch 26, p. 148, (F)"]
theorem ramanujanSum_eq_sum_dvd {q : ℕ} (hq : 0 < q) (n : ℤ) :
    ramanujanSum q n =
      ∑ d ∈ q.divisors.filter (fun d : ℕ ↦ (d : ℤ) ∣ n), (d : ℂ) * (μ (q / d) : ℂ) := by
  set E : ℕ → ℂ := fun a ↦ Complex.exp (2 * π * Complex.I * ((a : ℂ) * n / q)) with hE
  -- indicator of coprimality
  have hind : ∀ a : ℕ, (if Nat.Coprime a q then (1 : ℂ) else 0) =
      ∑ d ∈ q.divisors, if d ∣ a then (μ d : ℂ) else 0 := by
    intro a
    have h1 : ∑ d ∈ q.divisors, (if d ∣ a then (μ d : ℂ) else 0) =
        ∑ d ∈ (Nat.gcd a q).divisors, (μ d : ℂ) := by
      rw [← sum_filter]
      refine sum_congr ?_ fun _ _ ↦ rfl
      ext d
      simp [Nat.dvd_gcd_iff, hq.ne']
      tauto
    rw [h1]
    have h2 := sum_moebius_divisors (Nat.gcd a q)
    have h3 : (∑ d ∈ (Nat.gcd a q).divisors, (μ d : ℂ)) =
        ((∑ d ∈ (Nat.gcd a q).divisors, (μ d : ℤ) : ℤ) : ℂ) := by push_cast; rfl
    rw [h3, h2]
    unfold Nat.Coprime
    split_ifs <;> simp
  have step1 : ramanujanSum q n = ∑ a ∈ range q, E a * ∑ d ∈ q.divisors,
      if d ∣ a then (μ d : ℂ) else 0 := by
    unfold ramanujanSum
    rw [sum_filter]
    refine sum_congr rfl fun a _ ↦ ?_
    rw [← hind a]
    simp [hE]
  rw [step1]
  simp_rw [mul_sum]
  rw [sum_comm]
  have step2 : ∀ d ∈ q.divisors, ∑ a ∈ range q, E a * (if d ∣ a then (μ d : ℂ) else 0) =
      (if ((q / d : ℕ) : ℤ) ∣ n then ((q / d : ℕ) : ℂ) * (μ d : ℂ) else 0) := by
    intro d hd
    have hdq : d ∣ q := Nat.dvd_of_mem_divisors hd
    obtain ⟨m, rfl⟩ := hdq
    have hd0 : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; simp at hq)
    have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; simp at hq)
    have := exp_sum_dvd hd0 hm0 n
    rw [Nat.mul_div_cancel_left _ hd0]
    simp_rw [mul_ite, mul_zero]
    rw [← sum_filter, ← sum_mul]
    simp only [hE]
    rw [this]
    split_ifs <;> simp
  rw [sum_congr rfl step2]
  rw [sum_filter]
  rw [← Nat.sum_div_divisors q (fun d ↦ if (d : ℤ) ∣ n then (d : ℂ) * (μ (q / d) : ℂ) else 0)]
  refine sum_congr rfl fun d hd ↦ ?_
  have hdq : d ∣ q := Nat.dvd_of_mem_divisors hd
  have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdq hq
  rw [Nat.div_div_self hdq hq.ne']

/-- The arithmetic function `d ↦ d [d ∣ n]`. -/
private noncomputable def dvdWeight (n : ℤ) : ArithmeticFunction ℂ :=
  ⟨fun d ↦ if d ≠ 0 ∧ (d : ℤ) ∣ n then (d : ℂ) else 0, by simp⟩

private lemma isMultiplicative_dvdWeight (n : ℤ) : (dvdWeight n).IsMultiplicative := by
  refine ⟨by simp [dvdWeight], fun {a b} hab ↦ ?_⟩
  simp only [dvdWeight, ArithmeticFunction.coe_mk]
  by_cases ha : a = 0
  · simp [ha]
  by_cases hb : b = 0
  · simp [hb]
  have hdvd : (a : ℤ) * (b : ℤ) ∣ n ↔ (a : ℤ) ∣ n ∧ (b : ℤ) ∣ n := by
    constructor
    · intro h
      exact ⟨(dvd_mul_right _ _).trans h, (dvd_mul_left _ _).trans h⟩
    · rintro ⟨h1, h2⟩
      exact IsCoprime.mul_dvd (Nat.isCoprime_iff_coprime.mpr hab) h1 h2
  have hab0 : a * b ≠ 0 := mul_ne_zero ha hb
  by_cases h1 : (a : ℤ) ∣ n <;> by_cases h2 : (b : ℤ) ∣ n <;>
    simp [ha, hb, hab0, hdvd, h1, h2]

private lemma ramanujanSum_eq_mul_moebius {q : ℕ} (hq : 0 < q) (n : ℤ) :
    ramanujanSum q n = (dvdWeight n * (μ : ArithmeticFunction ℂ)) q := by
  rw [ramanujanSum_eq_sum_dvd hq, ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun x y ↦ (dvdWeight n) x * (μ : ArithmeticFunction ℂ) y),
    sum_filter]
  refine sum_congr rfl fun d hd ↦ ?_
  have hd0 : d ≠ 0 := (Nat.pos_of_mem_divisors hd).ne'
  simp [dvdWeight, hd0]

/-- **Davenport, Ch. 26, p. 149 (row 26-15)**: `c_q(n)` is multiplicative in `q`. -/
@[kb "davenport1980" "Ch 26, p. 149"]
theorem ramanujanSum_mul {q r : ℕ} (h : Nat.Coprime q r) (n : ℤ) :
    ramanujanSum (q * r) n = ramanujanSum q n * ramanujanSum r n := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · have : r = 1 := by simpa using h
    subst this
    simp [ramanujanSum]
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · have : q = 1 := by simpa using h
    subst this
    simp [ramanujanSum]
  rw [ramanujanSum_eq_mul_moebius hq, ramanujanSum_eq_mul_moebius hr,
    ramanujanSum_eq_mul_moebius (Nat.mul_pos hq hr)]
  exact ((isMultiplicative_dvdWeight n).mul
    ArithmeticFunction.isMultiplicative_moebius.intCast).2 h

private lemma ramanujanSum_prime_pow {p k : ℕ} (hp : p.Prime) (hk : 0 < k) (n : ℤ) :
    ramanujanSum (p ^ k) n = (μ (p ^ k / Nat.gcd (p ^ k) n.natAbs) : ℂ) * ((p ^ k).totient : ℂ) /
      ((p ^ k / Nat.gcd (p ^ k) n.natAbs).totient : ℂ) := by
  have hpk : 0 < p ^ k := pow_pos hp.pos k
  obtain ⟨v, hv, hg⟩ := (Nat.dvd_prime_pow hp).1 (Nat.gcd_dvd_left (p ^ k) n.natAbs)
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hv
  have hfilt : (p ^ (v + m)).divisors.filter (fun d : ℕ ↦ (d : ℤ) ∣ n) = (p ^ v).divisors := by
    ext d
    simp only [mem_filter, Nat.mem_divisors, Int.natCast_dvd]
    have key : d ∣ p ^ v ↔ d ∣ p ^ (v + m) ∧ d ∣ n.natAbs := by
      rw [← Nat.dvd_gcd_iff, hg]
    constructor
    · rintro ⟨⟨h1, _⟩, h2⟩
      exact ⟨key.2 ⟨h1, h2⟩, (pow_pos hp.pos v).ne'⟩
    · rintro ⟨h2, _⟩
      exact ⟨⟨(key.1 h2).1, hpk.ne'⟩, (key.1 h2).2⟩
  rw [ramanujanSum_eq_sum_dvd hpk, hfilt, hg, Nat.divisors_prime_pow hp, sum_map]
  simp only [Function.Embedding.coeFn_mk]
  have hdiv : ∀ j ∈ range (v + 1), p ^ (v + m) / p ^ j = p ^ (v + m - j) := fun j hj ↦
    Nat.pow_div (by have := mem_range.1 hj; omega) hp.pos
  rw [sum_congr rfl fun j hj ↦ by rw [hdiv j hj]]
  rw [Nat.pow_div (Nat.le_add_right v m) hp.pos, Nat.add_sub_cancel_left]
  have hzero : ∀ j, j < v → m ≥ 1 → (μ (p ^ (v + m - j)) : ℤ) = 0 := by
    intro j hj hm
    rw [ArithmeticFunction.moebius_apply_prime_pow hp (by omega)]
    rw [ite_eq_right_iff]
    intro h
    omega
  have hpm1 : ((p : ℂ) - 1) ≠ 0 := by
    intro h
    have : (p : ℂ) = 1 := by linear_combination h
    have : p = 1 := by exact_mod_cast this
    exact hp.one_lt.ne' this
  have hpc : ((p - 1 : ℕ) : ℂ) = (p : ℂ) - 1 := by
    rw [Nat.cast_sub hp.one_lt.le]; simp
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  rw [sum_range_succ]
  obtain rfl | rfl | hm : m = 0 ∨ m = 1 ∨ 2 ≤ m := by omega
  · obtain ⟨v', rfl⟩ : ∃ v', v = v' + 1 := ⟨v - 1, by omega⟩
    rw [sum_range_succ]
    have h0 : ∑ j ∈ range v', (p : ℂ) ^ j * (μ (p ^ (v' + 1 + 0 - j)) : ℂ) = 0 := by
      refine sum_eq_zero fun j hj ↦ ?_
      have hj' := mem_range.1 hj
      rw [ArithmeticFunction.moebius_apply_prime_pow hp (by omega), ite_eq_right_iff.2 (by omega)]
      simp
    simp only [Nat.add_zero, pow_zero, Nat.add_sub_cancel_left] at h0 ⊢
    push_cast
    rw [h0, Nat.sub_self, pow_zero, pow_one, ArithmeticFunction.moebius_apply_prime hp,
      Nat.totient_prime_pow_succ hp]
    simp only [ArithmeticFunction.moebius_apply_one, Nat.totient_one]
    push_cast
    rw [hpc]
    ring
  · have h0 : ∑ j ∈ range v, (p : ℂ) ^ j * (μ (p ^ (v + 1 - j)) : ℂ) = 0 := by
      refine sum_eq_zero fun j hj ↦ ?_
      have hj' := mem_range.1 hj
      rw [ArithmeticFunction.moebius_apply_prime_pow hp (by omega), ite_eq_right_iff.2 (by omega)]
      simp
    rw [show v + 1 - v = 1 by omega]
    push_cast
    rw [h0, pow_one, ArithmeticFunction.moebius_apply_prime hp,
      Nat.totient_prime_pow_succ hp, Nat.totient_prime hp, hpc]
    push_cast
    rw [hpc]
    field_simp
    ring
  · have h0 : ∑ j ∈ range v, (p : ℂ) ^ j * (μ (p ^ (v + m - j)) : ℂ) = 0 := by
      refine sum_eq_zero fun j hj ↦ ?_
      have hj' := mem_range.1 hj
      rw [ArithmeticFunction.moebius_apply_prime_pow hp (by omega), ite_eq_right_iff.2 (by omega)]
      simp
    have hmu : (μ (p ^ m) : ℤ) = 0 := by
      rw [ArithmeticFunction.moebius_apply_prime_pow hp (by omega)]
      exact ite_eq_right_iff.2 (by omega)
    push_cast
    rw [h0]
    simp [hmu]

/-- **Davenport, Ch. 26, p. 149 (row 26-15)**:
`c_q(n) = μ(q/(q, n)) φ(q)/φ(q/(q, n))`. -/
@[kb "davenport1980" "Ch 26, p. 149"]
theorem ramanujanSum_eq_moebius_mul_totient_div {q : ℕ} (hq : 0 < q) (n : ℤ) :
    ramanujanSum q n = (μ (q / Nat.gcd q n.natAbs) : ℂ) * (q.totient : ℂ) /
      ((q / Nat.gcd q n.natAbs).totient : ℂ) := by
  revert hq
  induction q using Nat.recOnPosPrimePosCoprime with
  | prime_pow p k hp hk => exact fun _ ↦ ramanujanSum_prime_pow hp hk n
  | zero => exact fun h ↦ absurd h (lt_irrefl 0)
  | one => intro _; simp [ramanujanSum]
  | coprime a b ha hb hab iha ihb =>
    intro _
    rw [ramanujanSum_mul hab, iha (by omega), ihb (by omega)]
    have hg : Nat.gcd (a * b) n.natAbs = Nat.gcd a n.natAbs * Nat.gcd b n.natAbs := by
      rw [Nat.gcd_comm, Nat.Coprime.gcd_mul _ hab, Nat.gcd_comm n.natAbs a,
        Nat.gcd_comm n.natAbs b]
    have hda : Nat.gcd a n.natAbs ∣ a := Nat.gcd_dvd_left _ _
    have hdb : Nat.gcd b n.natAbs ∣ b := Nat.gcd_dvd_left _ _
    have hdiv : a * b / (Nat.gcd a n.natAbs * Nat.gcd b n.natAbs) =
        (a / Nat.gcd a n.natAbs) * (b / Nat.gcd b n.natAbs) :=
      (Nat.div_mul_div_comm hda hdb).symm
    have hcop : Nat.Coprime (a / Nat.gcd a n.natAbs) (b / Nat.gcd b n.natAbs) :=
      Nat.Coprime.coprime_dvd_left (Nat.div_dvd_of_dvd hda)
        (Nat.Coprime.coprime_dvd_right (Nat.div_dvd_of_dvd hdb) hab)
    have hpa : 0 < (a / Nat.gcd a n.natAbs).totient :=
      Nat.totient_pos.2 (Nat.div_pos (Nat.le_of_dvd (by omega) hda) (Nat.gcd_pos_of_pos_left _ (by omega)))
    have hpb : 0 < (b / Nat.gcd b n.natAbs).totient :=
      Nat.totient_pos.2 (Nat.div_pos (Nat.le_of_dvd (by omega) hdb) (Nat.gcd_pos_of_pos_left _ (by omega)))
    rw [hg, hdiv, ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop,
      Nat.totient_mul hab, Nat.totient_mul hcop]
    have h1 : ((a / Nat.gcd a n.natAbs).totient : ℂ) ≠ 0 := by exact_mod_cast hpa.ne'
    have h2 : ((b / Nat.gcd b n.natAbs).totient : ℂ) ≠ 0 := by exact_mod_cast hpb.ne'
    push_cast
    field_simp

/-- `|c_q(n)| ≤ φ(q)`. -/
theorem norm_ramanujanSum_le (q : ℕ) (n : ℤ) : ‖ramanujanSum q n‖ ≤ q.totient := by
  unfold ramanujanSum
  refine (norm_sum_le _ _).trans ?_
  have : ∀ a ∈ (range q).filter (fun a ↦ Nat.Coprime a q),
      ‖Complex.exp (2 * π * Complex.I * ((a : ℂ) * n / q))‖ = 1 := by
    intro a _
    have : (2 * π * Complex.I * ((a : ℂ) * n / q)) =
        ((2 * π * ((a : ℝ) * n / q) : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [this, Complex.norm_exp_ofReal_mul_I]
  rw [sum_congr rfl this, Nat.totient_eq_card_coprime]
  simp only [sum_const, nsmul_eq_mul, mul_one, Nat.coprime_comm]
  exact le_of_eq (by simp)

/-- `c_q(n) = μ(q)` for `(n, q) = 1`. -/
theorem ramanujanSum_of_isCoprime {q : ℕ} (hq : 0 < q) {n : ℤ} (hn : IsCoprime n q) :
    ramanujanSum q n = μ q := by
  rw [ramanujanSum_eq_sum_dvd hq]
  have : q.divisors.filter (fun d : ℕ ↦ (d : ℤ) ∣ n) = {1} := by
    ext d
    simp only [mem_filter, Nat.mem_divisors, mem_singleton]
    constructor
    · rintro ⟨⟨h1, _⟩, h2⟩
      have : IsCoprime (d : ℤ) (q : ℤ) := hn.of_isCoprime_of_dvd_left h2
      exact Nat.Coprime.eq_one_of_dvd (Nat.isCoprime_iff_coprime.mp this) h1
    · rintro rfl
      exact ⟨⟨one_dvd _, hq.ne'⟩, by simp⟩
  rw [this]
  simp

/-- `c_q(-n) = c_q(n)`. -/
theorem ramanujanSum_neg (q : ℕ) (n : ℤ) : ramanujanSum q (-n) = ramanujanSum q n := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp [ramanujanSum]
  rw [ramanujanSum_eq_sum_dvd hq, ramanujanSum_eq_sum_dvd hq]
  simp only [dvd_neg]

/-- The Gauss sum of the principal character is the Ramanujan sum `c_q(1) = μ(q)`. -/
theorem gaussSum_one_stdAddChar (q : ℕ) [NeZero q] :
    gaussSum (1 : DirichletCharacter ℂ q) ZMod.stdAddChar = μ q := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  rw [← ramanujanSum_of_isCoprime hq (n := 1) isCoprime_one_left]
  unfold gaussSum ramanujanSum
  obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
  rw [sum_filter, ← Fin.sum_univ_eq_sum_range (fun a ↦ if Nat.Coprime a (q' + 1) then
      Complex.exp (2 * π * Complex.I * ((a : ℂ) * ((1 : ℤ) : ℂ) / ((q' + 1 : ℕ) : ℂ))) else 0)
      (q' + 1)]
  refine sum_congr rfl fun a _ ↦ ?_
  change (1 : DirichletCharacter ℂ (q' + 1)) a * ZMod.stdAddChar a =
    if Nat.Coprime a.val (q' + 1) then
      Complex.exp (2 * π * Complex.I * ((a.val : ℂ) * ((1 : ℤ) : ℂ) / ((q' + 1 : ℕ) : ℂ))) else 0
  have hcop : Nat.Coprime a.val (q' + 1) ↔ IsUnit a := by
    rw [← ZMod.isUnit_iff_coprime, ZMod.natCast_zmod_val]
  rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply]
  by_cases hu : IsUnit a
  · rw [MulChar.one_apply hu]
    split_ifs with h
    · push_cast
      ring_nf
    · exact absurd (hcop.2 hu) h
  · rw [MulChar.map_nonunit _ hu]
    split_ifs with h
    · exact absurd (hcop.1 h) hu
    · simp

end NTKB.Davenport
