/- Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license. -/
import NTKB.Analytic.Davenport.ThreePrimes.Ramanujan
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.PSeries

/-!
# The singular series of the ternary Goldbach problem (Davenport, Chapter 26, pp. 146, 149)

`G(N) = ∏_{p ∣ N} (1 - (p - 1)⁻²) ∏_{p ∤ N} (1 + (p - 1)⁻³)` (`singularSeries`).

* **26-16**: `∑_q μ(q) c_q(N)/φ(q)³` converges absolutely to `G(N)` (`hasSum_singularSeries`), the
  Euler product converges (`multipliable_singularFactor`), and the tail beyond `P` is
  `O(P^{-1/2})` uniformly in `N` (`norm_singularSeries_sub_sum_le`);
* `G(N) ≥ 1` for odd `N` and `G(N) = 0` for even `N` (row 26-5).

The tail bound uses `φ(q) ≥ 2⁻¹⁶ q^{3/4}` (`totient_ge`), where Davenport uses `φ(q) ≫ q^{1-ε}`.
-/

open Finset Real
open scoped ArithmeticFunction.Moebius

namespace NTKB.Davenport

/-- The Euler factor of `G(N)` at `p`: `1 - (p - 1)⁻²` if `p ∣ N`, `1 + (p - 1)⁻³` otherwise. -/
noncomputable def singularFactor (N : ℤ) (p : ℕ) : ℝ :=
  if (p : ℤ) ∣ N then 1 - 1 / ((p : ℝ) - 1) ^ 2 else 1 + 1 / ((p : ℝ) - 1) ^ 3

/-- The singular series `G(N) = ∏_p singularFactor N p` of Davenport, Ch. 26, p. 146. -/
noncomputable def singularSeries (N : ℤ) : ℝ :=
  ∏' p : Nat.Primes, singularFactor N p

/-- Auxiliary: `2 x^{3/4} ≤ x` for `x ≥ 16`. -/
lemma two_mul_rpow_le {x : ℝ} (hx : 16 ≤ x) : 2 * x ^ ((3:ℝ)/4) ≤ x := by
  have hx0 : 0 ≤ x := by linarith
  set y := x ^ ((1:ℝ)/4) with hy
  have hy0 : 0 ≤ y := Real.rpow_nonneg hx0 _
  have h4 : y ^ 4 = x := by
    rw [hy, ← Real.rpow_natCast, ← Real.rpow_mul hx0]; norm_num
  have h3 : x ^ ((3:ℝ)/4) = y ^ 3 := by
    rw [hy, ← Real.rpow_natCast, ← Real.rpow_mul hx0]; norm_num
  have hy2 : 2 ≤ y := by
    by_contra h
    push Not at h
    have : y ^ 4 < 2 ^ 4 := pow_lt_pow_left₀ h hy0 (by norm_num)
    linarith
  rw [h3, ← h4]
  nlinarith [pow_nonneg hy0 3]

lemma totient_aux (q : ℕ) :
    (q : ℝ) ^ ((3:ℝ)/4) ≤ 2 ^ ((q.primeFactors.filter (· < 16)).card) * q.totient := by
  induction q using Nat.recOnPosPrimePosCoprime with
  | zero => simp
  | one => simp
  | prime_pow p n hp hn =>
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [Nat.primeFactors_prime_pow (by omega) hp, Nat.totient_prime_pow_succ hp]
    have hp2 : (2:ℝ) ≤ p := by exact_mod_cast hp.two_le
    have hpm : (1:ℝ) ≤ (p:ℝ) ^ m := one_le_pow₀ (by linarith)
    have hxx : (1:ℝ) ≤ ((p ^ (m+1) : ℕ) : ℝ) := by push_cast; exact one_le_pow₀ (by linarith)
    have htot : ((p ^ m * (p - 1) : ℕ) : ℝ) = (p:ℝ) ^ m * ((p:ℝ) - 1) := by
      rw [Nat.cast_mul, Nat.cast_sub hp.one_le]; simp
    rw [htot]
    have hhalf : ((p ^ (m+1) : ℕ) : ℝ) ≤ 2 * ((p:ℝ) ^ m * ((p:ℝ) - 1)) := by
      push_cast; rw [pow_succ]; nlinarith
    by_cases h16 : p < 16
    · have : ({p} : Finset ℕ).filter (· < 16) = {p} := by simp [h16]
      rw [this]; simp only [card_singleton, pow_one]
      calc _ ≤ ((p ^ (m+1) : ℕ) : ℝ) := Real.rpow_le_self_of_one_le hxx (by norm_num)
        _ ≤ _ := hhalf
    · have : ({p} : Finset ℕ).filter (· < 16) = ∅ := by simp; omega
      rw [this]; simp only [card_empty, pow_zero, one_mul]
      have h16' : (16:ℝ) ≤ p := by exact_mod_cast (not_lt.mp h16)
      have : (16:ℝ) ≤ ((p ^ (m+1) : ℕ) : ℝ) := by
        push_cast; calc (16:ℝ) ≤ p := h16'
          _ = (p:ℝ)^1 := (pow_one _).symm
          _ ≤ _ := pow_le_pow_right₀ (by linarith) (by omega)
      have := two_mul_rpow_le this
      linarith
  | coprime a b ha hb hab iha ihb =>
    rw [Nat.primeFactors_mul (by omega) (by omega), Finset.filter_union,
      Finset.card_union_of_disjoint (Finset.disjoint_filter_filter hab.disjoint_primeFactors),
      Nat.totient_mul hab]
    push_cast
    rw [Real.mul_rpow (by positivity) (by positivity), pow_add]
    calc _ ≤ (2 ^ _ * (a.totient:ℝ)) * (2 ^ _ * (b.totient : ℝ)) :=
          mul_le_mul iha ihb (by positivity) (by positivity)
      _ = _ := by ring

/-- `φ(q) ≥ 2⁻¹⁶ q^{3/4}`. -/
theorem totient_ge (q : ℕ) : (q : ℝ) ^ ((3 : ℝ) / 4) / 2 ^ 16 ≤ q.totient := by
  have h := totient_aux q
  have hc : (q.primeFactors.filter (· < 16)).card ≤ 16 := by
    calc _ ≤ (range 16).card := card_le_card (by
            intro x hx; simp only [mem_filter] at hx; simp [hx.2])
      _ = 16 := card_range _
  have h2 : (2:ℝ) ^ ((q.primeFactors.filter (· < 16)).card) ≤ 2 ^ 16 :=
    pow_le_pow_right₀ (by norm_num) hc
  rw [div_le_iff₀ (by positivity)]
  calc _ ≤ _ := h
    _ ≤ 2 ^ 16 * (q.totient : ℝ) := mul_le_mul_of_nonneg_right h2 (by positivity)
    _ = _ := by ring


/-- The general term of the series of `G(N)`. -/
private noncomputable def sTerm (N : ℤ) (q : ℕ) : ℂ :=
  (μ q : ℂ) * ramanujanSum q N / (q.totient : ℂ) ^ 3

private lemma sTerm_zero (N : ℤ) : sTerm N 0 = 0 := by simp [sTerm]

private lemma sTerm_one (N : ℤ) : sTerm N 1 = 1 := by
  simp [sTerm, ramanujanSum]

private lemma ramanujanSum_prime {p : ℕ} (hp : p.Prime) (N : ℤ) :
    ramanujanSum p N = (if (p : ℤ) ∣ N then (p : ℂ) else 0) - 1 := by
  rw [ramanujanSum_eq_sum_dvd hp.pos, hp.divisors, Finset.sum_filter,
    Finset.sum_pair hp.one_lt.ne]
  simp [ArithmeticFunction.moebius_apply_prime hp, Nat.div_self hp.pos]
  split_ifs <;> ring

private lemma sTerm_prime (N : ℤ) {p : ℕ} (hp : p.Prime) :
    sTerm N p = ((singularFactor N p : ℝ) : ℂ) - 1 := by
  have h1 : (p : ℂ) - 1 ≠ 0 := by
    have : (1:ℝ) < p := by exact_mod_cast hp.one_lt
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  unfold sTerm singularFactor
  rw [ramanujanSum_prime hp, ArithmeticFunction.moebius_apply_prime hp, Nat.totient_prime hp]
  have hc : ((p - 1 : ℕ) : ℂ) = (p : ℂ) - 1 := by rw [Nat.cast_sub hp.one_le]; simp
  rw [hc]
  split_ifs with h
  · push_cast; field_simp; ring
  · push_cast; field_simp; ring

private lemma sTerm_pow {p e : ℕ} (hp : p.Prime) (he : 2 ≤ e) (N : ℤ) :
    sTerm N (p ^ e) = 0 := by
  simp [sTerm, ArithmeticFunction.moebius_apply_prime_pow hp (by omega : e ≠ 0),
    show e ≠ 1 by omega]

private lemma tsum_sTerm_pow (N : ℤ) (p : Nat.Primes) :
    ∑' e : ℕ, sTerm N ((p : ℕ) ^ e) = ((singularFactor N p : ℝ) : ℂ) := by
  rw [tsum_eq_sum (s := Finset.range 2)]
  · rw [Finset.sum_range_succ, Finset.sum_range_one, pow_zero, pow_one, sTerm_one,
      sTerm_prime N p.2]
    ring
  · intro e he
    simp only [Finset.mem_range, not_lt] at he
    exact sTerm_pow p.2 he N

private lemma sTerm_mul (N : ℤ) {m n : ℕ} (h : Nat.Coprime m n) :
    sTerm N (m * n) = sTerm N m * sTerm N n := by
  unfold sTerm
  rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime h, ramanujanSum_mul h,
    Nat.totient_mul h]
  push_cast
  ring

private lemma rpow_three_halves {x : ℝ} (hx : 0 ≤ x) : x ^ ((3:ℝ)/2) = (√x) ^ 3 := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hx]; norm_num

private lemma rpow_three_quarters_sq {x : ℝ} (hx : 0 ≤ x) :
    (x ^ ((3:ℝ)/4)) ^ 2 = x ^ ((3:ℝ)/2) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]; norm_num

private lemma norm_sTerm_le (N : ℤ) (q : ℕ) :
    ‖sTerm N q‖ ≤ 2 ^ 32 / (q : ℝ) ^ ((3:ℝ)/2) := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp [sTerm]
  have hφ : (0:ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
  have hX : 0 < (q:ℝ) ^ ((3:ℝ)/4) := Real.rpow_pos_of_pos (by exact_mod_cast hq) _
  have hge := totient_ge q
  have h1 : ‖sTerm N q‖ ≤ 1 / (q.totient : ℝ) ^ 2 := by
    unfold sTerm
    rw [norm_div, norm_mul, norm_pow, Complex.norm_natCast]
    have hμ : ‖(μ q : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_intCast]
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    have hc := norm_ramanujanSum_le q N
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    calc ‖(μ q : ℂ)‖ * ‖ramanujanSum q N‖ * (q.totient : ℝ) ^ 2
        ≤ 1 * q.totient * (q.totient : ℝ) ^ 2 := by gcongr
      _ = 1 * (q.totient : ℝ) ^ 3 := by ring
  refine h1.trans ?_
  rw [div_le_div_iff₀ (by positivity) (by positivity),
    ← rpow_three_quarters_sq (x := (q : ℝ)) (by positivity)]
  have : (q:ℝ) ^ ((3:ℝ)/4) ≤ 2 ^ 16 * q.totient := by
    rwa [div_le_iff₀ (by positivity), mul_comm] at hge
  calc 1 * ((q:ℝ) ^ ((3:ℝ)/4)) ^ 2 ≤ (2 ^ 16 * (q.totient : ℝ)) ^ 2 := by
        rw [one_mul]; exact pow_le_pow_left₀ hX.le this 2
    _ = _ := by ring

private lemma summable_bound : Summable (fun q : ℕ ↦ 2 ^ 32 / (q : ℝ) ^ ((3:ℝ)/2)) := by
  have := ((Real.summable_nat_rpow_inv (p := (3:ℝ)/2)).mpr (by norm_num)).mul_left (2 ^ 32)
  simpa [div_eq_mul_inv] using this

private lemma summable_norm_sTerm (N : ℤ) : Summable (fun q : ℕ ↦ ‖sTerm N q‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_sTerm_le N) summable_bound

private lemma sTerm_real (N : ℤ) (q : ℕ) : ∃ r : ℝ, sTerm N q = r := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · exact ⟨0, by simp [sTerm_zero]⟩
  · refine ⟨(μ q : ℝ) * ((μ (q / Nat.gcd q N.natAbs) : ℝ) * q.totient /
      ((q / Nat.gcd q N.natAbs).totient : ℝ)) / (q.totient : ℝ) ^ 3, ?_⟩
    unfold sTerm
    rw [ramanujanSum_eq_moebius_mul_totient_div hq]
    push_cast
    ring

private lemma hasProd_real (N : ℤ) : ∃ s : ℝ,
    HasProd (fun p : Nat.Primes ↦ singularFactor N p) s ∧
      HasSum (fun q ↦ sTerm N q) (s : ℂ) := by
  have hsum := summable_norm_sTerm N
  have hE := EulerProduct.eulerProduct_hasProd (f := fun q => sTerm N q) (sTerm_one N)
    (fun {m n} h => sTerm_mul N h) hsum (sTerm_zero N)
  have hE' : HasProd (fun p : Nat.Primes ↦ ((singularFactor N p : ℝ) : ℂ))
      (∑' n, sTerm N n) := by
    have : (fun p : Nat.Primes ↦ ∑' e : ℕ, sTerm N ((p : ℕ) ^ e)) =
        fun p : Nat.Primes ↦ ((singularFactor N p : ℝ) : ℂ) := funext (tsum_sTerm_pow N)
    rw [← this]; exact hE
  have hreal : ∀ q, sTerm N q = (((sTerm N q).re : ℝ) : ℂ) := fun q => by
    obtain ⟨r, hr⟩ := sTerm_real N q
    rw [hr]; simp
  have hS : ∑' n, sTerm N n = ((∑' n, (sTerm N n).re : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum]; exact tsum_congr hreal
  refine ⟨∑' n, (sTerm N n).re, ?_, ?_⟩
  · rw [hS] at hE'
    exact (Topology.IsInducing.hasProd_iff (g := Complex.ofRealHom)
      Complex.isometry_ofReal.isEmbedding.isInducing _ _).mp hE'
  · rw [← hS]; exact hsum.of_norm.hasSum

private lemma hasProd_singularFactor (N : ℤ) :
    HasProd (fun p : Nat.Primes ↦ singularFactor N p) (singularSeries N) := by
  obtain ⟨s, h1, -⟩ := hasProd_real N
  have : singularSeries N = s := h1.tprod_eq
  rw [this]; exact h1

/-- The Euler product of `G(N)` converges. -/
theorem multipliable_singularFactor (N : ℤ) :
    Multipliable (fun p : Nat.Primes ↦ singularFactor N p) :=
  (hasProd_singularFactor N).multipliable

/-- **Davenport, Ch. 26, p. 149 (row 26-16)**: `∑_q μ(q) c_q(N)/φ(q)³ = G(N)`, absolutely
convergent. -/
@[kb "davenport1980" "Ch 26, p. 149"]
theorem hasSum_singularSeries (N : ℤ) :
    HasSum (fun q : ℕ ↦ (μ q : ℂ) * ramanujanSum q N / (q.totient : ℂ) ^ 3)
      (singularSeries N : ℂ) := by
  obtain ⟨s, h1, h2⟩ := hasProd_real N
  have : singularSeries N = s := h1.tprod_eq
  rw [this]; exact h2

/-- The series of `G(N)` converges absolutely, uniformly in `N`. -/
theorem summable_norm_singularSeries_term (N : ℤ) :
    Summable (fun q : ℕ ↦ ‖(μ q : ℂ) * ramanujanSum q N / (q.totient : ℂ) ^ 3‖) :=
  summable_norm_sTerm N

private lemma telescope_term (x : ℝ) (hx : 1 ≤ x) :
    2 ^ 32 / (x + 1) ^ ((3:ℝ)/2) ≤ 2 ^ 33 * (1 / √x - 1 / √(x + 1)) := by
  rw [rpow_three_halves (by linarith)]
  have ha0 : 0 < √x := Real.sqrt_pos.mpr (by linarith)
  have hab : √x < √(x + 1) := Real.sqrt_lt_sqrt (by linarith) (by linarith)
  have ha2 : (√x) ^ 2 = x := Real.sq_sqrt (by linarith)
  have hb2 : (√(x + 1)) ^ 2 = x + 1 := Real.sq_sqrt (by linarith)
  generalize √x = a at *
  generalize √(x + 1) = b at *
  have hb0 : 0 < b := ha0.trans hab
  have e : 1 = (b - a) * (b + a) := by nlinarith
  have key : 1 * (a * b) ≤ 2 * (b - a) * b ^ 3 := by
    have : 2 * (b - a) * b ^ 3 - 1 * (a * b) = (b - a) ^ 2 * b * (2 * b + a) := by
      linear_combination (-(a * b)) * e
    have : 0 ≤ (b - a) ^ 2 * b * (2 * b + a) := by positivity
    linarith
  have key2 : 1 / b ^ 3 ≤ 2 * (1 / a - 1 / b) := by
    rw [show 2 * (1 / a - 1 / b) = 2 * (b - a) / (a * b) by field_simp,
      div_le_div_iff₀ (by positivity) (by positivity)]
    linarith
  calc 2 ^ 32 / b ^ 3 = 2 ^ 32 * (1 / b ^ 3) := by ring
    _ ≤ 2 ^ 32 * (2 * (1 / a - 1 / b)) := by gcongr
    _ = _ := by ring

private lemma tail_bound (N : ℤ) {M : ℕ} (hM : 1 ≤ M) :
    ‖∑' k : ℕ, sTerm N (k + (M + 1))‖ ≤ 2 ^ 33 / √(M : ℝ) := by
  have hM' : (1:ℝ) ≤ M := by exact_mod_cast hM
  have hs : Summable (fun k : ℕ => ‖sTerm N (k + (M + 1))‖) :=
    (summable_nat_add_iff (M + 1)).mpr (summable_norm_sTerm N)
  refine (norm_tsum_le_tsum_norm hs).trans ?_
  set u : ℕ → ℝ := fun k => 1 / √((M : ℝ) + k) with hu
  have hterm : ∀ k : ℕ, ‖sTerm N (k + (M + 1))‖ ≤ 2 ^ 33 * (u k - u (k + 1)) := by
    intro k
    refine (norm_sTerm_le N _).trans ?_
    have hx : 1 ≤ (M : ℝ) + k := by
      have : (0:ℝ) ≤ k := Nat.cast_nonneg k
      linarith
    have e1 : ((k + (M + 1) : ℕ) : ℝ) = ((M : ℝ) + k) + 1 := by push_cast; ring
    have e2 : (M : ℝ) + ((k + 1 : ℕ) : ℝ) = ((M : ℝ) + k) + 1 := by push_cast; ring
    rw [e1]
    simp only [hu]
    rw [e2]
    exact telescope_term _ hx
  refine Real.tsum_le_of_sum_range_le (fun _ => norm_nonneg _) (fun n => ?_)
  have hun : 0 ≤ u n := by simp only [hu]; positivity
  have hu0 : u 0 = 1 / √(M : ℝ) := by simp [hu]
  calc _ ≤ ∑ k ∈ range n, 2 ^ 33 * (u k - u (k + 1)) := sum_le_sum fun k _ => hterm k
    _ = 2 ^ 33 * (u 0 - u n) := by rw [← mul_sum, sum_range_sub']
    _ ≤ 2 ^ 33 * u 0 := by
        have := mul_nonneg (by norm_num : (0:ℝ) ≤ 2 ^ 33) hun
        linarith
    _ = 2 ^ 33 / √(M : ℝ) := by rw [hu0]; ring

/-- **Davenport, Ch. 26, p. 149 (row 26-16)**: the tail of the singular series beyond `P` is
`O(P^{-1/2})`, uniformly in `N`. -/
@[kb "davenport1980" "Ch 26, p. 149"]
theorem norm_singularSeries_sub_sum_le :
    ∃ C > 0, ∀ (N : ℤ) (P : ℝ), 1 ≤ P →
      ‖(singularSeries N : ℂ) - ∑ q ∈ Icc 1 ⌊P⌋₊,
          (μ q : ℂ) * ramanujanSum q N / (q.totient : ℂ) ^ 3‖ ≤ C / √P := by
  refine ⟨2 ^ 34, by norm_num, fun N P hP => ?_⟩
  set M := ⌊P⌋₊ with hM
  have hM1 : 1 ≤ M := Nat.le_floor (by simpa using hP)
  have hPM : P < M + 1 := Nat.lt_floor_add_one P
  have hsum := (summable_norm_sTerm N).of_norm
  have hS : (singularSeries N : ℂ) = ∑' q, sTerm N q := (hasSum_singularSeries N).tsum_eq.symm
  have hsub : ∑ q ∈ Icc 1 M, sTerm N q = ∑ q ∈ range (M + 1), sTerm N q := by
    apply Finset.sum_subset
    · intro x hx
      simp only [mem_Icc, mem_range] at hx ⊢
      omega
    · intro x hx hx'
      simp only [mem_Icc, mem_range] at hx hx'
      have : x = 0 := by omega
      subst this
      exact sTerm_zero N
  have heq : (singularSeries N : ℂ) - ∑ q ∈ Icc 1 M,
      (μ q : ℂ) * ramanujanSum q N / (q.totient : ℂ) ^ 3 = ∑' k, sTerm N (k + (M + 1)) := by
    change _ - ∑ q ∈ Icc 1 M, sTerm N q = _
    rw [hsub, hS, ← hsum.sum_add_tsum_nat_add (M + 1)]
    ring
  rw [heq]
  refine (tail_bound N hM1).trans ?_
  have hM' : (1:ℝ) ≤ M := by exact_mod_cast hM1
  have hMpos : (0:ℝ) < M := by linarith
  have hP0 : 0 < P := by linarith
  have h2 : √P ≤ 2 * √(M : ℝ) := by
    refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
    rw [mul_pow, Real.sq_sqrt hMpos.le]
    nlinarith
  rw [div_le_div_iff₀ (Real.sqrt_pos.mpr hMpos) (Real.sqrt_pos.mpr hP0)]
  nlinarith

/-- `|G(N)|` is bounded uniformly in `N`. -/
theorem abs_singularSeries_le : ∃ C > 0, ∀ N : ℤ, |singularSeries N| ≤ C := by
  refine ⟨(∑' q : ℕ, 2 ^ 32 / (q : ℝ) ^ ((3:ℝ)/2)) + 1, ?_, fun N => ?_⟩
  · have : 0 ≤ ∑' q : ℕ, 2 ^ 32 / (q : ℝ) ^ ((3:ℝ)/2) := tsum_nonneg fun q => by positivity
    linarith
  · have hS : (singularSeries N : ℂ) = ∑' q, sTerm N q :=
      (hasSum_singularSeries N).tsum_eq.symm
    have h1 : ‖(singularSeries N : ℂ)‖ ≤ ∑' q, ‖sTerm N q‖ := by
      rw [hS]; exact norm_tsum_le_tsum_norm (summable_norm_sTerm N)
    have h2 : ∑' q, ‖sTerm N q‖ ≤ ∑' q : ℕ, 2 ^ 32 / (q : ℝ) ^ ((3:ℝ)/2) :=
      (summable_norm_sTerm N).tsum_le_tsum (norm_sTerm_le N) summable_bound
    rw [Complex.norm_real, Real.norm_eq_abs] at h1
    linarith

private lemma factor_ge (N : ℤ) {p : ℕ} (hp : p.Prime) :
    1 - 1 / ((p : ℝ) - 1) ^ 2 ≤ singularFactor N p := by
  have h2 : (2:ℝ) ≤ p := by exact_mod_cast hp.two_le
  have h0 : 0 ≤ (p : ℝ) - 1 := by linarith
  unfold singularFactor
  split_ifs
  · exact le_rfl
  · have : 0 ≤ 1 / ((p:ℝ) - 1) ^ 2 := div_nonneg zero_le_one (pow_nonneg h0 _)
    have : 0 ≤ 1 / ((p:ℝ) - 1) ^ 3 := div_nonneg zero_le_one (pow_nonneg h0 _)
    linarith

private lemma prod_Icc_ge (K : ℕ) : 1 / 2 ≤ ∏ m ∈ Icc 2 K, (1 - 1 / (m : ℝ) ^ 2) := by
  have formula : ∀ K : ℕ, ∏ m ∈ Icc 2 (K + 1), (1 - 1 / (m : ℝ) ^ 2) =
      ((K : ℝ) + 2) / (2 * ((K : ℝ) + 1)) := by
    intro K
    induction K with
    | zero => norm_num
    | succ K ih =>
      rw [Finset.prod_Icc_succ_top (by omega), ih]
      push_cast
      have : ((K : ℝ) + 1 + 1) ≠ 0 := by positivity
      have : ((K : ℝ) + 1) ≠ 0 := by positivity
      field_simp
      ring
  rcases K with _ | K
  · norm_num
  · rw [formula K, div_le_div_iff₀ (by norm_num) (by positivity)]
    have : (0:ℝ) ≤ K := Nat.cast_nonneg K
    nlinarith

private lemma prod_subset_ge {T : Finset ℕ} {K : ℕ} (hT : T ⊆ Icc 2 K) :
    ∏ m ∈ Icc 2 K, (1 - 1 / (m : ℝ) ^ 2) ≤ ∏ m ∈ T, (1 - 1 / (m : ℝ) ^ 2) := by
  have h0 : ∀ m ∈ Icc 2 K, 0 ≤ 1 - 1 / (m : ℝ) ^ 2 ∧ 1 - 1 / (m : ℝ) ^ 2 ≤ 1 := by
    intro m hm
    have hm2 : (2:ℝ) ≤ m := by exact_mod_cast (mem_Icc.mp hm).1
    have h1 : (1:ℝ) ≤ (m:ℝ) ^ 2 := by nlinarith
    have h3 : 1 / (m:ℝ) ^ 2 ≤ 1 := (div_le_one (by linarith)).mpr h1
    have h4 : 0 ≤ 1 / (m:ℝ) ^ 2 := by positivity
    constructor <;> linarith
  rw [← Finset.prod_sdiff hT]
  have hT0 : 0 ≤ ∏ m ∈ T, (1 - 1 / (m : ℝ) ^ 2) := prod_nonneg fun m hm => (h0 m (hT hm)).1
  have : ∏ m ∈ Icc 2 K \ T, (1 - 1 / (m : ℝ) ^ 2) ≤ 1 :=
    Finset.prod_le_one₀ (fun m hm => (h0 m (sdiff_subset hm)).1) (fun m hm => (h0 m (sdiff_subset hm)).2)
  exact mul_le_of_le_one_left hT0 this

/-- **Davenport, Ch. 26, p. 146 (row 26-5)**: `G(N) ≥ 1` for odd `N`. -/
@[kb "davenport1980" "Ch 26, p. 146"]
theorem one_le_singularSeries_of_odd {N : ℤ} (hN : Odd N) : 1 ≤ singularSeries N := by
  have hP := hasProd_singularFactor N
  set two : Nat.Primes := ⟨2, Nat.prime_two⟩ with htwo
  have hF2 : singularFactor N two = 2 := by
    have : ¬ ((2:ℕ):ℤ) ∣ N := by
      intro h
      have h' : (2:ℤ) ∣ N := by exact_mod_cast h
      exact (Int.not_even_iff_odd.mpr hN) (even_iff_two_dvd.mpr h')
    show singularFactor N 2 = 2
    unfold singularFactor
    simp only [this, ↓reduceIte]
    norm_num
  refine ge_of_tendsto hP ?_
  filter_upwards [Filter.eventually_ge_atTop {two}] with s hs
  rw [← Finset.mul_prod_erase s _ (hs (mem_singleton_self two)), hF2]
  set T := s.erase two with hT
  set g : Nat.Primes → ℕ := fun p => p.1 - 1 with hg
  have hT3 : ∀ p ∈ T, 3 ≤ p.1 := by
    intro p hp
    have h1 := p.2.two_le
    have h2 : p ≠ two := (mem_erase.mp hp).1
    have h3 : p.1 ≠ 2 := fun h => h2 (Subtype.ext h)
    omega
  have hinj : Set.InjOn g T := by
    intro p _ q _ h
    have := p.2.two_le
    have := q.2.two_le
    exact Subtype.ext (by simp only [hg] at h; omega)
  set K := (T.image g).sup id with hK
  have hsub : T.image g ⊆ Icc 2 K := by
    intro m hm
    obtain ⟨p, hp, rfl⟩ := mem_image.mp hm
    have := hT3 p hp
    refine mem_Icc.mpr ⟨by simp only [hg]; omega, ?_⟩
    exact Finset.le_sup (f := id) hm
  have hbound : 1 / 2 ≤ ∏ p ∈ T, singularFactor N p := by
    calc (1:ℝ) / 2 ≤ ∏ m ∈ Icc 2 K, (1 - 1 / (m : ℝ) ^ 2) := prod_Icc_ge K
      _ ≤ ∏ m ∈ T.image g, (1 - 1 / (m : ℝ) ^ 2) := prod_subset_ge hsub
      _ = ∏ p ∈ T, (1 - 1 / (((p.1 - 1 : ℕ) : ℝ)) ^ 2) := prod_image hinj
      _ ≤ ∏ p ∈ T, singularFactor N p := by
        refine Finset.prod_le_prod₀ (fun p hp => ?_) (fun p hp => ?_)
        · have h3 := hT3 p hp
          have h2 : (2:ℝ) ≤ ((p.1 - 1 : ℕ) : ℝ) := by
            have : 2 ≤ p.1 - 1 := by omega
            exact_mod_cast this
          have h1 : (1:ℝ) ≤ ((p.1 - 1 : ℕ) : ℝ) ^ 2 := by nlinarith
          have h4 : 1 / ((p.1 - 1 : ℕ) : ℝ) ^ 2 ≤ 1 := (div_le_one (by linarith)).mpr h1
          have h5 : 0 ≤ 1 / ((p.1 - 1 : ℕ) : ℝ) ^ 2 := by positivity
          linarith
        · have : (((p.1 - 1 : ℕ)) : ℝ) = (p.1 : ℝ) - 1 := by
            rw [Nat.cast_sub p.2.one_le]; simp
          rw [this]
          exact factor_ge N p.2
  linarith

/-- **Davenport, Ch. 26, p. 146 (row 26-5)**: `G(N) = 0` for even `N`. -/
@[kb "davenport1980" "Ch 26, p. 146"]
theorem singularSeries_of_even {N : ℤ} (hN : Even N) : singularSeries N = 0 := by
  have hP := hasProd_singularFactor N
  set two : Nat.Primes := ⟨2, Nat.prime_two⟩ with htwo
  have hF : singularFactor N two = 0 := by
    have : ((2:ℕ):ℤ) ∣ N := by exact_mod_cast even_iff_two_dvd.mp hN
    show singularFactor N 2 = 0
    unfold singularFactor
    simp only [this, ↓reduceIte]
    norm_num
  have h0 : Filter.Tendsto (fun s : Finset Nat.Primes => ∏ p ∈ s, singularFactor N p)
      Filter.atTop (nhds 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop {two}] with s hs
    exact (Finset.prod_eq_zero (hs (mem_singleton_self two)) hF).symm
  exact tendsto_nhds_unique hP h0

end NTKB.Davenport
