/- Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license. -/
import NTKB.Analytic.Davenport.ThreePrimes.SingularSeries
import NTKB.Analytic.Davenport.ThreePrimes.MajorArcIntegral
import NTKB.Analytic.Davenport.ThreePrimes.MinorArc
import NTKB.Analytic.Davenport.Sieve.BarbanDavenportHalberstam
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Vinogradov's three primes theorem (Davenport, Chapter 26)

* **26-4** (Vinogradov): `r(N) = (1/2) G(N) N² + O(N² (log N)^{-A})` for every `A > 0`
  (`vinogradov_three_primes`);
* **26-5**: every sufficiently large odd `N` is a sum of three primes, in `≫ N² (log N)^{-3}` ways
  (`card_three_primes_ge`, `exists_three_primes_of_odd`).

The proof is Davenport's: `P = (log N)^B`, `Q = N (log N)^{-B}`, and the integral of formula (1)
over `(1/Q, 1 + 1/Q]` is split into the major arcs (pairwise disjoint and inside that interval
once `Q > 2P²`) and the rest, the minor arcs, where `|S| ≪ N (log N)^{4 - B/2}` and Parseval
bounds the integral of `|S|²` by `N log N` (26-17, 26-18, 26-20).
-/

open Finset Real
open scoped ArithmeticFunction.Moebius ArithmeticFunction.vonMangoldt

namespace NTKB.Davenport

/-! ### Decomposition of the circle into major and minor arcs -/

/-- Index set of the major arcs. -/
def arcIdx (M : ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  (Icc 1 M).sigma (fun q ↦ (Icc 1 q).filter (fun a ↦ Nat.Coprime a q))

/-- The major arc `|α - a/q| ≤ X`. -/
noncomputable def arc (X : ℝ) (p : Σ _ : ℕ, ℕ) : Set ℝ :=
  Set.Icc ((p.2 : ℝ) / p.1 - X) ((p.2 : ℝ) / p.1 + X)

lemma mem_arcIdx {M : ℕ} {p : Σ _ : ℕ, ℕ} :
    p ∈ arcIdx M ↔ (1 ≤ p.1 ∧ p.1 ≤ M) ∧ (1 ≤ p.2 ∧ p.2 ≤ p.1) ∧ Nat.Coprime p.2 p.1 := by
  simp only [arcIdx, Finset.mem_sigma, Finset.mem_Icc, Finset.mem_filter]

lemma nat_eq_of_coprime_cross {a q a' q' : ℕ} (ha : 1 ≤ a)
    (h : Nat.Coprime a q) (h' : Nat.Coprime a' q') (e : a * q' = a' * q) : a = a' ∧ q = q' := by
  have h1 : a ∣ a' := h.dvd_of_dvd_mul_right ⟨q', e.symm⟩
  have h2 : a' ∣ a := h'.dvd_of_dvd_mul_right ⟨q, e⟩
  have h3 : a = a' := Nat.dvd_antisymm h1 h2
  subst h3
  exact ⟨rfl, Nat.eq_of_mul_eq_mul_left ha e.symm⟩

lemma frac_sep {a q a' q' : ℕ} (hq : 0 < q) (hq' : 0 < q') (hne : a * q' ≠ a' * q) :
    1 / ((q : ℝ) * q') ≤ |(a : ℝ) / q - a' / q'| := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hq0' : (0 : ℝ) < q' := by exact_mod_cast hq'
  have h1 : (1 : ℝ) ≤ |(a : ℝ) * q' - a' * q| := by
    have h0 : (a : ℤ) * q' - a' * q ≠ 0 := by
      intro h; apply hne
      have : (a : ℤ) * q' = a' * q := by linarith
      exact_mod_cast this
    have h2 : 1 ≤ |(a : ℤ) * q' - a' * q| := Int.one_le_abs h0
    have h3 : (1 : ℝ) ≤ |(((a : ℤ) * q' - a' * q : ℤ) : ℝ)| := by exact_mod_cast h2
    simpa using h3
  have e : (a : ℝ) / q - a' / q' = ((a : ℝ) * q' - a' * q) / (q * q') := by
    field_simp
  rw [e, abs_div, abs_of_pos (show (0 : ℝ) < q * q' by positivity)]
  exact div_le_div_of_nonneg_right h1 (by positivity)

lemma arc_disjoint {X : ℝ} {M : ℕ} (h : 2 * X * (M : ℝ) ^ 2 < 1) :
    (arcIdx M : Set (Σ _ : ℕ, ℕ)).PairwiseDisjoint (arc X) := by
  rintro ⟨q, a⟩ hp ⟨q', a'⟩ hp' hne
  simp only [Finset.mem_coe, mem_arcIdx] at hp hp'
  rw [Function.onFun, Set.disjoint_left]
  intro x hx hx'
  simp only [arc, Set.mem_Icc] at hx hx'
  have hne' : a * q' ≠ a' * q := by
    intro e
    obtain ⟨h1, h2⟩ := nat_eq_of_coprime_cross hp.2.1.1 hp.2.2 hp'.2.2 e
    subst h1; subst h2; exact hne rfl
  have hsep := frac_sep (a := a) (a' := a') hp.1.1 hp'.1.1 hne'
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hp.1.1
  have hq0' : (0 : ℝ) < q' := by exact_mod_cast hp'.1.1
  have hqM : (q : ℝ) * q' ≤ (M : ℝ) ^ 2 := by
    have h1 : (q : ℝ) ≤ M := by exact_mod_cast hp.1.2
    have h2 : (q' : ℝ) ≤ M := by exact_mod_cast hp'.1.2
    nlinarith
  have hM : 1 / (M : ℝ) ^ 2 ≤ 1 / ((q : ℝ) * q') :=
    one_div_le_one_div_of_le (by positivity) hqM
  have hM2 : 2 * X < 1 / (M : ℝ) ^ 2 := by
    have : 0 < (M : ℝ) ^ 2 := by nlinarith [(by exact_mod_cast hp.1.2 : (q : ℝ) ≤ M)]
    rw [lt_div_iff₀ this]; exact h
  have : |(a : ℝ) / q - a' / q'| ≤ 2 * X := by
    rw [abs_le]; constructor <;> linarith [hx.1, hx.2, hx'.1, hx'.2]
  linarith

lemma arc_subset {X : ℝ} {M : ℕ} (hM : 1 ≤ M) (h : 2 * X * (M : ℝ) ^ 2 < 1)
    {p : Σ _ : ℕ, ℕ} (hp : p ∈ arcIdx M) : arc X p ⊆ Set.Ioc X (X + 1) := by
  rw [mem_arcIdx] at hp
  obtain ⟨⟨hq1, hqM⟩, ⟨ha1, haq⟩, -⟩ := hp
  intro x hx
  simp only [arc, Set.mem_Icc] at hx
  have hq0 : (0 : ℝ) < p.1 := by exact_mod_cast hq1
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hqM' : (p.1 : ℝ) ≤ M := by exact_mod_cast hqM
  have hX : 0 ≤ X := by
    by_contra hneg; push Not at hneg; nlinarith [sq_nonneg (M : ℝ)]
  have h1 : 1 / (p.1 : ℝ) ≤ (p.2 : ℝ) / p.1 := by
    apply div_le_div_of_nonneg_right _ hq0.le; exact_mod_cast ha1
  have h2 : (p.2 : ℝ) / p.1 ≤ 1 := by
    rw [div_le_one hq0]; exact_mod_cast haq
  have h3 : 2 * X * M < 1 := by nlinarith
  have h4 : 1 / (M : ℝ) ≤ 1 / (p.1 : ℝ) := one_div_le_one_div_of_le hq0 hqM'
  have h5 : 2 * X < 1 / (M : ℝ) := by
    rw [lt_div_iff₀ (by linarith)]; exact h3
  constructor <;> linarith [hx.1, hx.2]

lemma integral_decomp (f : ℝ → ℂ) (hf : Continuous f) {X : ℝ} {M : ℕ} (hM : 1 ≤ M)
    (h : 2 * X * (M : ℝ) ^ 2 < 1) (hX : 0 < X) :
    ∫ x in X..X + 1, f x =
      (∑ q ∈ Icc 1 M, ∑ a ∈ (Icc 1 q).filter (fun a ↦ Nat.Coprime a q),
        ∫ x in ((a : ℝ) / q - X)..((a : ℝ) / q + X), f x) +
      ∫ x in Set.Ioc X (X + 1) \ (⋃ p ∈ arcIdx M, arc X p), f x := by
  set U := ⋃ p ∈ arcIdx M, arc X p with hU
  have hUsub : U ⊆ Set.Ioc X (X + 1) :=
    Set.iUnion₂_subset (fun p hp ↦ arc_subset hM h hp)
  have hUmeas : MeasurableSet U :=
    Finset.measurableSet_biUnion _ (fun p _ ↦ measurableSet_Icc)
  have hfint : MeasureTheory.IntegrableOn f (Set.Ioc X (X + 1)) :=
    hf.continuousOn.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have hmain : ∫ x in U, f x = ∑ q ∈ Icc 1 M, ∑ a ∈ (Icc 1 q).filter (fun a ↦ Nat.Coprime a q),
        ∫ x in ((a : ℝ) / q - X)..((a : ℝ) / q + X), f x := by
    rw [hU, MeasureTheory.integral_biUnion_finset (s := arc X) _
      (fun p _ ↦ by unfold arc; exact measurableSet_Icc)
      (arc_disjoint h) (fun p _ ↦ by unfold arc; exact hf.continuousOn.integrableOn_Icc)]
    rw [arcIdx, Finset.sum_sigma]
    refine Finset.sum_congr rfl (fun q hq ↦ Finset.sum_congr rfl (fun a ha ↦ ?_))
    have hq' : 1 ≤ q := (Finset.mem_Icc.mp hq).1
    have hX2 : (a : ℝ) / q - X ≤ (a : ℝ) / q + X := by linarith
    rw [intervalIntegral.integral_of_le hX2, arc, MeasureTheory.integral_Icc_eq_integral_Ioc]
  rw [intervalIntegral.integral_of_le (by linarith),
    ← MeasureTheory.integral_inter_add_sdiff hUmeas hfint, Set.inter_eq_right.mpr hUsub, hmain]

lemma minor_cond {X P : ℝ} (hX : 0 < X) (hP : 1 ≤ P) (h : 2 * X * (⌊P⌋₊ : ℝ) ^ 2 < 1)
    {x : ℝ} (hx : x ∈ Set.Ioc X (X + 1) \ (⋃ p ∈ arcIdx ⌊P⌋₊, arc X p)) :
    ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ P → ∀ a : ℤ, X < |x - a / q| := by
  intro q hq hqP a
  by_contra hle
  push Not at hle
  obtain ⟨⟨hx1, hx2⟩, hx3⟩ := hx
  have hM : 1 ≤ ⌊P⌋₊ := Nat.le_floor (by simpa using hP)
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  set r : ℚ := (a : ℚ) / q with hr
  have hrR : (r : ℝ) = a / q := by simp [hr]
  have hden : r.den ≤ q := by
    have e : r = Rat.divInt a (q : ℤ) := by rw [Rat.divInt_eq_div]; simp [hr]
    have h1 : ((Rat.divInt a (q : ℤ)).den : ℤ) ∣ (q : ℤ) := Rat.den_dvd a q
    rw [← e] at h1
    exact_mod_cast Int.le_of_dvd (by exact_mod_cast hq) h1
  have hden1 : 1 ≤ r.den := r.den_pos
  have hdenM : r.den ≤ ⌊P⌋₊ := Nat.le_floor (by
    have : (r.den : ℝ) ≤ q := by exact_mod_cast hden
    linarith)
  have hrr : (r : ℝ) = r.num / r.den := Rat.cast_def r
  have hd0 : (0 : ℝ) < r.den := by exact_mod_cast hden1
  have habs : |x - (r : ℝ)| ≤ X := by rw [hrR]; exact hle
  rw [abs_le] at habs
  have hrpos : (0 : ℝ) < r := by linarith [habs.2]
  have hnum : 0 < r.num := by
    have : 0 < r := by exact_mod_cast hrpos
    exact Rat.num_pos.mpr this
  have hM1 : (1 : ℝ) ≤ ⌊P⌋₊ := by exact_mod_cast hM
  have hdM : (r.den : ℝ) ≤ ⌊P⌋₊ := by exact_mod_cast hdenM
  have h2X : 2 * X < 1 / (r.den : ℝ) := by
    rw [lt_div_iff₀ hd0]; nlinarith
  have hnd : (r.num : ℝ) < r.den + 1 := by
    have h1 : (r : ℝ) ≤ 1 + 2 * X := by linarith [habs.1]
    rw [hrr, div_le_iff₀ hd0] at h1
    have h3 : 2 * X * r.den < 1 := by rwa [lt_div_iff₀ hd0] at h2X
    nlinarith
  have hnd' : r.num ≤ r.den := by
    have : r.num < (r.den : ℤ) + 1 := by exact_mod_cast hnd
    omega
  apply hx3
  simp only [Set.mem_iUnion]
  refine ⟨⟨r.den, r.num.toNat⟩, ?_, ?_⟩
  · rw [mem_arcIdx]
    have hna : r.num.toNat = r.num.natAbs := by omega
    refine ⟨⟨hden1, hdenM⟩, ⟨?_, ?_⟩, ?_⟩
    · show 1 ≤ r.num.toNat
      omega
    · show r.num.toNat ≤ r.den
      omega
    · show Nat.Coprime r.num.toNat r.den
      rw [hna]; exact r.reduced
  · simp only [arc, Set.mem_Icc]
    have : ((r.num.toNat : ℕ) : ℝ) = r.num := by
      have : ((r.num.toNat : ℕ) : ℤ) = r.num := Int.toNat_of_nonneg hnum.le
      exact_mod_cast this
    rw [this, ← hrr]
    constructor <;> linarith [habs.1, habs.2]

lemma continuous_cubeIntegrand (N : ℕ) :
    Continuous (fun α : ℝ ↦ primeExpSum N α ^ 3 * Complex.exp (-(2 * π * Complex.I * (N * α)))) := by
  have := continuous_primeExpSum N
  fun_prop

lemma norm_cubeIntegrand (N : ℕ) (α : ℝ) :
    ‖primeExpSum N α ^ 3 * Complex.exp (-(2 * π * Complex.I * (N * α)))‖ =
      ‖primeExpSum N α‖ ^ 3 := by
  rw [norm_mul, norm_pow, Complex.norm_exp]
  have : (-(2 * π * Complex.I * (N * α))).re = 0 := by simp
  rw [this]; simp

lemma integral_Ioc_norm_sq (N : ℕ) (X : ℝ) :
    ∫ x in Set.Ioc X (X + 1), ‖primeExpSum N x‖ ^ 2 = ∑ n ∈ Icc 1 N, Λ n ^ 2 := by
  rw [← intervalIntegral.integral_of_le (by linarith)]
  have hper : Function.Periodic (fun x : ℝ ↦ ‖primeExpSum N x‖ ^ 2) 1 := by
    intro x
    have := primeExpSum_add_int N x 1
    simp only [Int.cast_one] at this
    simp only [this]
  rw [hper.intervalIntegral_add_eq X 0, zero_add]
  exact integral_norm_primeExpSum_sq N

lemma norm_integral_minor_le (N : ℕ) {X : ℝ} {K : ℝ} (hK : 0 ≤ K) (m : Set ℝ) (hm : m ⊆ Set.Ioc X (X + 1))
    (hmeas : MeasurableSet m) (hS : ∀ x ∈ m, ‖primeExpSum N x‖ ≤ K) :
    ‖∫ x in m, primeExpSum N x ^ 3 * Complex.exp (-(2 * π * Complex.I * (N * x)))‖ ≤
      K * ∑ n ∈ Icc 1 N, Λ n ^ 2 := by
  have hint : ∀ {g : ℝ → ℝ}, Continuous g → ∀ s ⊆ Set.Ioc X (X + 1),
      MeasureTheory.IntegrableOn g s := fun hg s hs ↦
    (hg.continuousOn.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self).mono_set hs
  have hcS : Continuous (fun x ↦ ‖primeExpSum N x‖) := (continuous_primeExpSum N).norm
  refine (MeasureTheory.norm_integral_le_integral_norm _).trans ?_
  simp_rw [norm_cubeIntegrand]
  calc ∫ x in m, ‖primeExpSum N x‖ ^ 3
      ≤ ∫ x in m, K * ‖primeExpSum N x‖ ^ 2 := by
        refine MeasureTheory.setIntegral_mono_on (hint (by fun_prop) m hm)
          ((hint (by fun_prop) m hm).const_mul K) hmeas (fun x hx ↦ ?_)
        have := hS x hx
        have h0 := norm_nonneg (primeExpSum N x)
        calc ‖primeExpSum N x‖ ^ 3 = ‖primeExpSum N x‖ * ‖primeExpSum N x‖ ^ 2 := by ring
          _ ≤ K * ‖primeExpSum N x‖ ^ 2 := by gcongr
    _ = K * ∫ x in m, ‖primeExpSum N x‖ ^ 2 := MeasureTheory.integral_const_mul _ _
    _ ≤ K * ∫ x in Set.Ioc X (X + 1), ‖primeExpSum N x‖ ^ 2 := by
        refine mul_le_mul_of_nonneg_left ?_ hK
        exact MeasureTheory.setIntegral_mono_set (hint (by fun_prop) _ subset_rfl)
          (Filter.Eventually.of_forall (fun x ↦ by positivity)) (Filter.Eventually.of_forall hm)
    _ = K * ∑ n ∈ Icc 1 N, Λ n ^ 2 := by rw [integral_Ioc_norm_sq]

lemma exists_log_rpow_le (s r c : ℝ) (hr : 0 < r) (hc : 0 < c) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Real.log N ^ s ≤ c * (N : ℝ) ^ r := by
  have h := (isLittleO_log_rpow_rpow_atTop s hr).def hc
  obtain ⟨x₀, hx₀⟩ := Filter.eventually_atTop.mp h
  refine ⟨⌈x₀⌉₊, fun N hN ↦ ?_⟩
  have hx : x₀ ≤ N := (Nat.le_ceil x₀).trans (by exact_mod_cast hN)
  have := hx₀ N hx
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (N : ℝ) ^ r)]
    at this
  exact (le_abs_self _).trans this

lemma exp_neg_sqrt_le {c : ℝ} (hc : 0 < c) (A : ℝ) :
    ∃ K > 0, ∀ L : ℝ, 1 ≤ L → Real.exp (-c * √L) ≤ K * L ^ (-A) := by
  obtain ⟨K, hK, h⟩ := pow_le_mul_exp_sqrt hc ⌈A⌉₊
  refine ⟨K, hK, fun L hL ↦ ?_⟩
  have hL0 : 0 < L := by linarith
  have h1 : L ^ A ≤ L ^ (⌈A⌉₊ : ℝ) := Real.rpow_le_rpow_of_exponent_le hL (Nat.le_ceil A)
  rw [Real.rpow_natCast] at h1
  have h2 := h1.trans (h L hL0.le)
  have hA0 : 0 < L ^ A := Real.rpow_pos_of_pos hL0 A
  rw [Real.rpow_neg hL0.le, ← div_eq_mul_inv, le_div_iff₀ hA0]
  have : Real.exp (-c * √L) * Real.exp (c * √L) = 1 := by rw [← Real.exp_add]; simp
  calc Real.exp (-c * √L) * L ^ A ≤ Real.exp (-c * √L) * (K * Real.exp (c * √L)) := by gcongr
    _ = K := by rw [← mul_assoc, mul_comm _ K, mul_assoc, this, mul_one]

lemma sum_coef_eq (N M : ℕ) (J : ℂ) :
    (∑ q ∈ Icc 1 M, (μ q : ℂ) * ramanujanSum q (N : ℤ) / (q.totient : ℂ) ^ 3) * J =
      ∑ q ∈ Icc 1 M, (μ q : ℂ) / (q.totient : ℂ) ^ 3 * ramanujanSum q (-N) * J := by
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun q _ ↦ ?_)
  rw [ramanujanSum_neg]; ring

set_option maxHeartbeats 1000000 in
lemma main_estimate (A : ℝ) (hA : 0 < A) :
    ∃ C > 0, ∃ N₁ : ℕ, ∀ N : ℕ, N₁ ≤ N →
      ‖(threePrimeRep N : ℂ) - ((singularSeries N * (N : ℝ) ^ 2 / 2 : ℝ) : ℂ)‖ ≤
        C * (N : ℝ) ^ 2 * Real.log N ^ (-A) := by
  set B : ℝ := 2 * A + 10 with hBdef
  have hB : 0 < B := by rw [hBdef]; linarith
  obtain ⟨C₁, hC₁, hmin⟩ := norm_primeExpSum_minor_le B hB
  obtain ⟨c, hc, C₂, hC₂, hmaj⟩ := norm_majorArcs_integral_sub_le B hB
  obtain ⟨C₃, hC₃, hsing⟩ := norm_singularSeries_sub_sum_le
  obtain ⟨CG, hCG, hG⟩ := abs_singularSeries_le
  obtain ⟨K, hK, hKexp⟩ := exp_neg_sqrt_le hc A
  obtain ⟨N₀, hN₀⟩ := exists_log_rpow_le (3 * B) 1 (1 / 4) one_pos (by norm_num)
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  refine ⟨C₁ * (Real.log 4 + 4) + C₂ * K + 2 * (CG + C₃) + C₃, by positivity, max N₀ 3,
    fun N hN ↦ ?_⟩
  have hN3 : 3 ≤ N := le_trans (le_max_right _ _) hN
  have hN0' : N₀ ≤ N := le_trans (le_max_left _ _) hN
  have hNr : (3 : ℝ) ≤ N := by exact_mod_cast hN3
  have hNpos : (0 : ℝ) < N := by linarith
  set L := Real.log N with hLdef
  have hL1 : 1 ≤ L := by
    rw [hLdef, Real.le_log_iff_exp_le hNpos]
    have := Real.exp_one_lt_d9
    linarith [this]
  have hL0 : 0 < L := by linarith
  set P : ℝ := L ^ B with hP
  have hP1 : 1 ≤ P := Real.one_le_rpow hL1 hB.le
  have hP3 : P ^ 3 ≤ N / 4 := by
    have h1 := hN₀ N hN0'
    rw [Real.rpow_one] at h1
    have h2 : P ^ 3 = L ^ (3 * B) := by
      rw [hP, ← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; congr 1; push_cast; ring
    rw [h2]; linarith
  have hP2 : 1 ≤ P ^ 2 := one_le_pow₀ hP1
  have hPP : P ≤ P ^ 3 := by nlinarith [mul_le_mul_of_nonneg_left hP2 (by linarith : (0 : ℝ) ≤ P)]
  set T : ℝ := L ^ A with hT
  have hT1 : 1 ≤ T := Real.one_le_rpow hL1 hA.le
  have hTP : T ≤ P := Real.rpow_le_rpow_of_exponent_le hL1 (by rw [hBdef]; linarith)
  have hT0 : 0 < T := by linarith
  have hLA : L ^ (-A) = T⁻¹ := Real.rpow_neg hL0.le A
  have hTsqrt : T ≤ √P := by
    calc T = √(T ^ 2) := (Real.sqrt_sq hT0.le).symm
      _ ≤ √P := by
        apply Real.sqrt_le_sqrt
        have : T ^ 2 = L ^ (2 * A) := by
          rw [hT, ← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; congr 1; push_cast; ring
        rw [this]
        exact Real.rpow_le_rpow_of_exponent_le hL1 (by rw [hBdef]; linarith)
  set X : ℝ := P / N with hX
  have hXpos : 0 < X := by positivity
  set M := ⌊P⌋₊ with hMdef
  have hM : 1 ≤ M := Nat.le_floor (by simpa using hP1)
  have hMP : (M : ℝ) ≤ P := Nat.floor_le (by linarith)
  have hcond : 2 * X * (M : ℝ) ^ 2 < 1 := by
    have h1 : (M : ℝ) ^ 2 ≤ P ^ 2 := by gcongr
    have h2 : 2 * X * (M : ℝ) ^ 2 ≤ 2 * (P / N) * P ^ 2 := by gcongr
    have h3 : 2 * (P / N) * P ^ 2 = 2 * P ^ 3 / N := by ring
    have h4 : 2 * P ^ 3 / N ≤ 1 / 2 := by
      rw [div_le_iff₀ hNpos]; linarith
    linarith
  have hQ : 2 ≤ (N : ℝ) / P := by
    rw [le_div_iff₀ (by linarith)]; linarith
  -- the integrand and the decomposition
  set f : ℝ → ℂ := fun α ↦
    primeExpSum N α ^ 3 * Complex.exp (-(2 * π * Complex.I * (N * α))) with hf
  have hr : (threePrimeRep N : ℂ) = ∫ α in X..X + 1, f α := threePrimeRep_eq_integral N X
  have hdec := integral_decomp f (continuous_cubeIntegrand N) hM hcond hXpos
  set U : Set ℝ := ⋃ p ∈ arcIdx M, arc X p with hU
  have hUmeas : MeasurableSet U :=
    Finset.measurableSet_biUnion _ (fun p _ ↦ measurableSet_Icc)
  set m : Set ℝ := Set.Ioc X (X + 1) \ U with hm
  have hmsub : m ⊆ Set.Ioc X (X + 1) := Set.sdiff_subset
  have hmmeas : MeasurableSet m := measurableSet_Ioc.diff hUmeas
  set Sarcs : ℂ := ∑ q ∈ Icc 1 M, ∑ a ∈ (Icc 1 q).filter (fun a ↦ Nat.Coprime a q),
    ∫ x in ((a : ℝ) / q - X)..((a : ℝ) / q + X), f x with hSarcs
  set J : ℂ := ∫ β in (-X)..X,
    linearExpSum N β ^ 3 * Complex.exp (-(2 * π * Complex.I * (N * β))) with hJ
  set s : ℂ := ∑ q ∈ Icc 1 M, (μ q : ℂ) * ramanujanSum q (N : ℤ) / (q.totient : ℂ) ^ 3 with hs
  set G : ℝ := singularSeries (N : ℤ) with hGdef
  have key : (threePrimeRep N : ℂ) - ((G * (N : ℝ) ^ 2 / 2 : ℝ) : ℂ) =
      (∫ x in m, f x) + (Sarcs - s * J) + s * (J - (N : ℂ) ^ 2 / 2) +
        (s - G) * ((N : ℂ) ^ 2 / 2) := by
    rw [hr, hdec]; push_cast; ring
  -- E1 : the minor arcs
  have hZ0 : 0 ≤ (N : ℝ) ^ 2 * L ^ (-A) := by positivity
  have E1 : ‖∫ x in m, f x‖ ≤ C₁ * (Real.log 4 + 4) * ((N : ℝ) ^ 2 * L ^ (-A)) := by
    have hS : ∀ x ∈ m, ‖primeExpSum N x‖ ≤ C₁ * N * L ^ (4 - B / 2) := by
      intro x hx
      refine hmin N (by omega) x ?_
      intro q hq hqP a
      exact minor_cond hXpos hP1 hcond hx q hq hqP a
    have hK1 : 0 ≤ C₁ * N * L ^ (4 - B / 2) := by positivity
    refine (norm_integral_minor_le N hK1 m hmsub hmmeas hS).trans ?_
    have hsq := sum_vonMangoldt_sq_le (x := (N : ℝ)) (by linarith)
    rw [Nat.floor_natCast] at hsq
    have hL4 : L ^ (4 - B / 2) * L = L ^ (-A) := by
      rw [← Real.rpow_add_one hL0.ne']; congr 1; rw [hBdef]; ring
    calc C₁ * N * L ^ (4 - B / 2) * ∑ n ∈ Icc 1 N, Λ n ^ 2
        ≤ C₁ * N * L ^ (4 - B / 2) * ((Real.log 4 + 4) * N * L) := by gcongr
      _ = C₁ * (Real.log 4 + 4) * ((N : ℝ) ^ 2 * (L ^ (4 - B / 2) * L)) := by ring
      _ = _ := by rw [hL4]
  -- E2 : the major arcs
  have E2 : ‖Sarcs - s * J‖ ≤ C₂ * K * ((N : ℝ) ^ 2 * L ^ (-A)) := by
    have h1 := hmaj N (by omega)
    rw [← sum_coef_eq N _ _] at h1
    refine h1.trans ?_
    have := hKexp L hL1
    calc C₂ * N ^ 2 * Real.exp (-c * √L) ≤ C₂ * N ^ 2 * (K * L ^ (-A)) := by gcongr
      _ = _ := by ring
  -- the singular series
  have hsG : ‖(G : ℂ) - s‖ ≤ C₃ / √P := hsing (N : ℤ) P hP1
  have hsn : ‖s‖ ≤ CG + C₃ := by
    have h1 : s = (G : ℂ) - ((G : ℂ) - s) := by ring
    have h2 : ‖(G : ℂ)‖ ≤ CG := by rw [Complex.norm_real, Real.norm_eq_abs]; exact hG N
    have h3 : C₃ / √P ≤ C₃ := div_le_self hC₃.le (by linarith)
    calc ‖s‖ = ‖(G : ℂ) - ((G : ℂ) - s)‖ := by rw [← h1]
      _ ≤ ‖(G : ℂ)‖ + ‖(G : ℂ) - s‖ := norm_sub_le _ _
      _ ≤ _ := by linarith
  have hTN : T ≤ N / 4 := by linarith
  have hJb : ‖J - (N : ℂ) ^ 2 / 2‖ ≤ 2 * ((N : ℝ) ^ 2 * L ^ (-A)) := by
    have h1 := norm_integral_linearExpSum_cube_sub_le N hQ
    rw [inv_div] at h1
    refine h1.trans ?_
    rw [hLA]
    have e1 : 2 * (N : ℝ) ≤ N ^ 2 * T⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ hT0]
      nlinarith [mul_le_mul_of_nonneg_left hTN hNpos.le]
    have e2 : ((N : ℝ) / P) ^ 2 ≤ N ^ 2 * T⁻¹ := by
      rw [div_pow, ← div_eq_mul_inv]
      refine div_le_div_of_nonneg_left (by positivity) hT0 ?_
      nlinarith
    linarith
  have E3 : ‖s * (J - (N : ℂ) ^ 2 / 2)‖ ≤ (CG + C₃) * (2 * ((N : ℝ) ^ 2 * L ^ (-A))) := by
    rw [norm_mul]; exact mul_le_mul hsn hJb (norm_nonneg _) (by positivity)
  have E4 : ‖(s - G) * ((N : ℂ) ^ 2 / 2)‖ ≤ C₃ * ((N : ℝ) ^ 2 * L ^ (-A)) := by
    rw [norm_mul]
    have h1 : ‖s - (G : ℂ)‖ ≤ C₃ * L ^ (-A) := by
      rw [norm_sub_rev]; refine hsG.trans ?_
      rw [hLA, ← div_eq_mul_inv]; exact div_le_div_of_nonneg_left hC₃.le hT0 hTsqrt
    have h2 : ‖((N : ℂ) ^ 2 / 2)‖ = (N : ℝ) ^ 2 / 2 := by
      rw [show ((N : ℂ) ^ 2 / 2) = (((N : ℝ) ^ 2 / 2 : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    rw [h2]
    have h3 : 0 ≤ C₃ * ((N : ℝ) ^ 2 * L ^ (-A)) := by positivity
    calc ‖s - (G : ℂ)‖ * ((N : ℝ) ^ 2 / 2) ≤ (C₃ * L ^ (-A)) * ((N : ℝ) ^ 2 / 2) := by gcongr
      _ = (1 / 2) * (C₃ * ((N : ℝ) ^ 2 * L ^ (-A))) := by ring
      _ ≤ _ := by linarith
  rw [key]
  have n1 := norm_add_le ((∫ x in m, f x) + (Sarcs - s * J) + s * (J - (N : ℂ) ^ 2 / 2))
    ((s - G) * ((N : ℂ) ^ 2 / 2))
  have n2 := norm_add_le ((∫ x in m, f x) + (Sarcs - s * J)) (s * (J - (N : ℂ) ^ 2 / 2))
  have n3 := norm_add_le (∫ x in m, f x) (Sarcs - s * J)
  calc _ ≤ C₁ * (Real.log 4 + 4) * ((N : ℝ) ^ 2 * L ^ (-A)) + C₂ * K * ((N : ℝ) ^ 2 * L ^ (-A)) +
        (CG + C₃) * (2 * ((N : ℝ) ^ 2 * L ^ (-A))) + C₃ * ((N : ℝ) ^ 2 * L ^ (-A)) := by
        linarith
    _ = _ := by ring

lemma vonMangoldt_le_log_of_le {n N : ℕ} (hn : 1 ≤ n) (hnN : n ≤ N) : Λ n ≤ Real.log N :=
  ArithmeticFunction.vonMangoldt_le_log.trans (Real.log_le_log (by exact_mod_cast hn)
    (by exact_mod_cast hnN))

lemma threePrimeRep_nonneg (N : ℕ) : 0 ≤ threePrimeRep N := by
  unfold threePrimeRep
  exact Finset.sum_nonneg (fun k _ ↦ by
    have := fun n : ℕ ↦ (ArithmeticFunction.vonMangoldt_nonneg (n := n))
    positivity)

lemma threePrimeRep_le (N : ℕ) : threePrimeRep N ≤ (N : ℝ) ^ 3 * Real.log N ^ 3 := by
  unfold threePrimeRep
  have hcard : ((Icc 1 N ×ˢ Icc 1 N ×ˢ Icc 1 N).filter
      (fun k : ℕ × ℕ × ℕ ↦ k.1 + k.2.1 + k.2.2 = N)).card ≤ N ^ 3 := by
    refine (Finset.card_le_card (Finset.filter_subset _ _)).trans ?_
    simp only [Finset.card_product, Nat.card_Icc, Nat.add_sub_cancel]
    exact le_of_eq (by ring)
  calc _ ≤ ∑ k ∈ (Icc 1 N ×ˢ Icc 1 N ×ˢ Icc 1 N).filter
          (fun k : ℕ × ℕ × ℕ ↦ k.1 + k.2.1 + k.2.2 = N), Real.log N ^ 3 := by
        refine Finset.sum_le_sum (fun k hk ↦ ?_)
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hk
        have h1 := vonMangoldt_le_log_of_le hk.1.1.1 hk.1.1.2
        have h2 := vonMangoldt_le_log_of_le hk.1.2.1.1 hk.1.2.1.2
        have h3 := vonMangoldt_le_log_of_le hk.1.2.2.1 hk.1.2.2.2
        have := fun n : ℕ ↦ (ArithmeticFunction.vonMangoldt_nonneg (n := n))
        calc Λ k.1 * Λ k.2.1 * Λ k.2.2 ≤ Real.log N * Real.log N * Real.log N := by
              gcongr
          _ = _ := by ring
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := by
        have hL : 0 ≤ Real.log N ^ 3 := by
          rcases Nat.eq_zero_or_pos N with rfl | hN
          · simp
          · exact pow_nonneg (Real.log_nonneg (by exact_mod_cast hN)) 3
        gcongr
        exact_mod_cast hcard

/-- **Vinogradov's theorem, Davenport, Ch. 26, p. 146 (row 26-4)**: for every `A > 0`,
`r(N) = (1/2) G(N) N² + O(N² (log N)^{-A})`, where
`r(N) = ∑_{k₁ + k₂ + k₃ = N} Λ(k₁) Λ(k₂) Λ(k₃)` and
`G(N) = ∏_{p ∣ N} (1 - (p - 1)⁻²) ∏_{p ∤ N} (1 + (p - 1)⁻³)`. -/
@[kb "davenport1980" "Ch 26, p. 146"]
theorem vinogradov_three_primes (A : ℝ) (hA : 0 < A) :
    ∃ C > 0, ∀ N : ℕ, 2 ≤ N →
      |threePrimeRep N - singularSeries N * N ^ 2 / 2| ≤ C * N ^ 2 * Real.log N ^ (-A) := by
  obtain ⟨C₀, hC₀, N₁, hN₁⟩ := main_estimate A hA
  obtain ⟨CG, hCG, hG⟩ := abs_singularSeries_le
  set R : ℝ := max (N₁ : ℝ) 2 with hR
  have hR2 : 2 ≤ R := le_max_right _ _
  have hlogR : 0 < Real.log R := Real.log_pos (by linarith)
  set D : ℝ := (R * Real.log R ^ 3 + CG) * Real.log R ^ A with hD
  have hD0 : 0 < D := by positivity
  refine ⟨max C₀ D, lt_max_of_lt_left hC₀, fun N hN ↦ ?_⟩
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hL0 : 0 < Real.log N := Real.log_pos (by linarith)
  have hZ0 : 0 ≤ (N : ℝ) ^ 2 * Real.log N ^ (-A) := by positivity
  by_cases hcase : N₁ ≤ N
  · have h := hN₁ N hcase
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at h
    refine h.trans ?_
    have : C₀ * (N : ℝ) ^ 2 * Real.log N ^ (-A) = C₀ * ((N : ℝ) ^ 2 * Real.log N ^ (-A)) := by ring
    rw [this]
    have : max C₀ D * (N : ℝ) ^ 2 * Real.log N ^ (-A) =
        max C₀ D * ((N : ℝ) ^ 2 * Real.log N ^ (-A)) := by ring
    rw [this]
    gcongr
    exact le_max_left _ _
  · push Not at hcase
    have hNR : (N : ℝ) ≤ R := le_trans (by exact_mod_cast hcase.le) (le_max_left _ _)
    have hLR : Real.log N ≤ Real.log R := Real.log_le_log (by linarith) hNR
    have hr0 := threePrimeRep_nonneg N
    have hr1 := threePrimeRep_le N
    have hG1 := hG (N : ℤ)
    have hr2 : (N : ℝ) ^ 3 * Real.log N ^ 3 ≤ (N : ℝ) ^ 2 * (R * Real.log R ^ 3) := by
      calc (N : ℝ) ^ 3 * Real.log N ^ 3 = (N : ℝ) ^ 2 * ((N : ℝ) * Real.log N ^ 3) := by ring
        _ ≤ (N : ℝ) ^ 2 * (R * Real.log R ^ 3) := by gcongr
    have hLA : Real.log N ^ A ≤ Real.log R ^ A := Real.rpow_le_rpow hL0.le hLR hA.le
    have hLA0 : 0 < Real.log N ^ A := Real.rpow_pos_of_pos hL0 A
    have hmul : Real.log N ^ (-A) * Real.log N ^ A = 1 := by
      rw [← Real.rpow_add hL0]; simp
    have habs : |threePrimeRep N - singularSeries N * N ^ 2 / 2| ≤
        (N : ℝ) ^ 2 * (R * Real.log R ^ 3 + CG) := by
      have h3 : |singularSeries N * (N : ℝ) ^ 2 / 2| ≤ CG * (N : ℝ) ^ 2 := by
        rw [abs_div, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (N : ℝ) ^ 2),
          abs_two]
        have : 0 ≤ (N : ℝ) ^ 2 := by positivity
        nlinarith [mul_le_mul_of_nonneg_right hG1 this]
      calc _ ≤ |threePrimeRep N| + |singularSeries N * (N : ℝ) ^ 2 / 2| := abs_sub _ _
        _ ≤ _ := by
          rw [abs_of_nonneg hr0]; nlinarith
    refine habs.trans ?_
    calc (N : ℝ) ^ 2 * (R * Real.log R ^ 3 + CG)
        = (N : ℝ) ^ 2 * (Real.log N ^ (-A) * Real.log N ^ A) * (R * Real.log R ^ 3 + CG) := by
          rw [hmul]; ring
      _ ≤ (N : ℝ) ^ 2 * (Real.log N ^ (-A) * Real.log R ^ A) * (R * Real.log R ^ 3 + CG) := by
          gcongr
      _ = D * ((N : ℝ) ^ 2 * Real.log N ^ (-A)) := by rw [hD]; ring
      _ ≤ max C₀ D * ((N : ℝ) ^ 2 * Real.log N ^ (-A)) := by
          gcongr; exact le_max_right _ _
      _ = _ := by ring

/-! ### Passing from prime powers to primes -/

/-- The set of triples `k₁ + k₂ + k₃ = N`, `kᵢ ≥ 1`. -/
def Tall (N : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (Icc 1 N ×ˢ Icc 1 N ×ˢ Icc 1 N).filter (fun k ↦ k.1 + k.2.1 + k.2.2 = N)

lemma mem_Tall {N : ℕ} {k : ℕ × ℕ × ℕ} : k ∈ Tall N ↔
    (1 ≤ k.1 ∧ k.1 ≤ N) ∧ (1 ≤ k.2.1 ∧ k.2.1 ≤ N) ∧ (1 ≤ k.2.2 ∧ k.2.2 ≤ N) ∧
      k.1 + k.2.1 + k.2.2 = N := by
  simp only [Tall, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  tauto

/-- `∑_{k₁ + k₂ + k₃ = N} f(k₁) g(k₂) h(k₃)`. -/
noncomputable def W (N : ℕ) (f g h : ℕ → ℝ) : ℝ := ∑ k ∈ Tall N, f k.1 * g k.2.1 * h k.2.2

lemma W_cyc (N : ℕ) (f g h : ℕ → ℝ) : W N f g h = W N g h f := by
  unfold W
  refine Finset.sum_nbij' (fun k ↦ (k.2.1, k.2.2, k.1)) (fun k ↦ (k.2.2, k.1, k.2.1))
    ?_ ?_ ?_ ?_ ?_
  · intro k hk
    simp only [Finset.mem_coe, mem_Tall] at hk ⊢
    omega
  · intro k hk
    simp only [Finset.mem_coe, mem_Tall] at hk ⊢
    omega
  · intro k _; rfl
  · intro k _; rfl
  · intro k _; ring

lemma W_le (N : ℕ) {f g h : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) (hg : ∀ n, 0 ≤ g n) {H : ℝ} (hH0 : 0 ≤ H)
    (hH : ∀ n ∈ Icc 1 N, h n ≤ H) :
    W N f g h ≤ H * ((∑ n ∈ Icc 1 N, f n) * (∑ n ∈ Icc 1 N, g n)) := by
  have h1 : W N f g h ≤ ∑ k ∈ Tall N, (f k.1 * g k.2.1) * H := by
    refine Finset.sum_le_sum (fun k hk ↦ ?_)
    rw [mem_Tall] at hk
    exact mul_le_mul_of_nonneg_left (hH _ (Finset.mem_Icc.mpr hk.2.2.1))
      (mul_nonneg (hf _) (hg _))
  have h2 : ∑ k ∈ Tall N, (f k.1 * g k.2.1) * H =
      ∑ p ∈ (Tall N).image (fun k ↦ (k.1, k.2.1)), (f p.1 * g p.2) * H := by
    rw [Finset.sum_image]
    intro k hk k' hk' e
    rw [Finset.mem_coe, mem_Tall] at hk hk'
    simp only [Prod.mk.injEq] at e
    obtain ⟨e1, e2⟩ := e
    ext
    · exact e1
    · exact e2
    · have := hk.2.2.2; have := hk'.2.2.2; omega
  have h3 : ∑ p ∈ (Tall N).image (fun k ↦ (k.1, k.2.1)), (f p.1 * g p.2) * H ≤
      ∑ p ∈ Icc 1 N ×ˢ Icc 1 N, (f p.1 * g p.2) * H := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun p _ _ ↦ by
      have := hf p.1; have := hg p.2; positivity)
    intro p hp
    simp only [Finset.mem_image, mem_Tall] at hp
    obtain ⟨k, hk, rfl⟩ := hp
    simp only [Finset.mem_product, Finset.mem_Icc]
    exact ⟨hk.1, hk.2.1⟩
  have h4 : ∑ p ∈ Icc 1 N ×ˢ Icc 1 N, (f p.1 * g p.2) * H =
      H * ((∑ n ∈ Icc 1 N, f n) * (∑ n ∈ Icc 1 N, g n)) := by
    rw [← Finset.sum_mul, Finset.sum_product, Finset.sum_mul_sum]
    ring
  linarith

/-- `Λ n` for non-prime `n`, and `0` for primes. -/
noncomputable def nonPrimeVM (n : ℕ) : ℝ := if n.Prime then 0 else Λ n

lemma nonPrimeVM_nonneg (n : ℕ) : 0 ≤ nonPrimeVM n := by
  unfold nonPrimeVM
  split_ifs
  · exact le_rfl
  · exact ArithmeticFunction.vonMangoldt_nonneg

lemma sum_nonPrimeVM_le {N : ℕ} (hN : 1 ≤ N) :
    ∑ n ∈ Icc 1 N, nonPrimeVM n ≤ 2 * √(N : ℝ) * Real.log N := by
  have h := Chebyshev.psi_sub_theta_le (x := (N : ℝ)) (by exact_mod_cast hN)
  rw [Chebyshev.psi_sub_theta_eq_sum_not_prime, Nat.floor_natCast] at h
  have e : Ioc 0 N = Icc 1 N := by ext; simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega
  rw [e] at h
  refine le_trans (le_of_eq ?_) h
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl (fun n _ ↦ ?_)
  unfold nonPrimeVM
  split_ifs <;> simp_all

lemma sum_vonMangoldt_le (N : ℕ) :
    ∑ n ∈ Icc 1 N, Λ n ≤ (Real.log 4 + 4) * N := by
  have h := Chebyshev.psi_le_const_mul_self (x := (N : ℝ)) (Nat.cast_nonneg N)
  unfold Chebyshev.psi at h
  rw [Nat.floor_natCast] at h
  have e : Ioc 0 N = Icc 1 N := by ext; simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega
  rw [e] at h
  exact h

lemma term_le {N : ℕ} {k : ℕ × ℕ × ℕ} (hk : k ∈ Tall N) :
    Λ k.1 * Λ k.2.1 * Λ k.2.2 ≤
      (if k.1.Prime ∧ k.2.1.Prime ∧ k.2.2.Prime then Real.log N ^ 3 else 0) +
      nonPrimeVM k.1 * Λ k.2.1 * Λ k.2.2 + Λ k.1 * nonPrimeVM k.2.1 * Λ k.2.2 +
      Λ k.1 * Λ k.2.1 * nonPrimeVM k.2.2 := by
  rw [mem_Tall] at hk
  have nn : ∀ n : ℕ, 0 ≤ Λ n := fun n ↦ ArithmeticFunction.vonMangoldt_nonneg
  have nn' := nonPrimeVM_nonneg
  have p1 := mul_nonneg (mul_nonneg (nn' k.1) (nn k.2.1)) (nn k.2.2)
  have p2 := mul_nonneg (mul_nonneg (nn k.1) (nn' k.2.1)) (nn k.2.2)
  have p3 := mul_nonneg (mul_nonneg (nn k.1) (nn k.2.1)) (nn' k.2.2)
  by_cases hp : k.1.Prime ∧ k.2.1.Prime ∧ k.2.2.Prime
  · rw [if_pos hp]
    have h1 := vonMangoldt_le_log_of_le hk.1.1 hk.1.2
    have h2 := vonMangoldt_le_log_of_le hk.2.1.1 hk.2.1.2
    have h3 := vonMangoldt_le_log_of_le hk.2.2.1.1 hk.2.2.1.2
    have : Λ k.1 * Λ k.2.1 * Λ k.2.2 ≤ Real.log N * Real.log N * Real.log N := by
      gcongr
    nlinarith
  · rw [if_neg hp]
    by_cases h1 : k.1.Prime
    · by_cases h2 : k.2.1.Prime
      · have h3 : ¬ k.2.2.Prime := fun h3 ↦ hp ⟨h1, h2, h3⟩
        have : nonPrimeVM k.2.2 = Λ k.2.2 := by simp [nonPrimeVM, h3]
        rw [this]; linarith
      · have : nonPrimeVM k.2.1 = Λ k.2.1 := by simp [nonPrimeVM, h2]
        rw [this]; linarith
    · have : nonPrimeVM k.1 = Λ k.1 := by simp [nonPrimeVM, h1]
      rw [this]; linarith

lemma threePrimeRep_le_good {N : ℕ} (hN : 1 ≤ N) :
    threePrimeRep N ≤ Real.log N ^ 3 * (((Icc 1 N ×ˢ Icc 1 N ×ˢ Icc 1 N).filter
        (fun k : ℕ × ℕ × ℕ ↦ k.1.Prime ∧ k.2.1.Prime ∧ k.2.2.Prime ∧
          k.1 + k.2.1 + k.2.2 = N)).card : ℝ) +
      3 * (Real.log N * ((2 * √(N : ℝ) * Real.log N) * ((Real.log 4 + 4) * N))) := by
  have hr : threePrimeRep N = ∑ k ∈ Tall N, Λ k.1 * Λ k.2.1 * Λ k.2.2 := rfl
  have hsum : ∑ k ∈ Tall N, (if k.1.Prime ∧ k.2.1.Prime ∧ k.2.2.Prime then Real.log N ^ 3 else 0)
      = Real.log N ^ 3 * (((Icc 1 N ×ˢ Icc 1 N ×ˢ Icc 1 N).filter
        (fun k : ℕ × ℕ × ℕ ↦ k.1.Prime ∧ k.2.1.Prime ∧ k.2.2.Prime ∧
          k.1 + k.2.1 + k.2.2 = N)).card : ℝ) := by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
    congr 3
    ext k
    simp only [Tall, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
    tauto
  have hle : threePrimeRep N ≤ ∑ k ∈ Tall N,
      ((if k.1.Prime ∧ k.2.1.Prime ∧ k.2.2.Prime then Real.log N ^ 3 else 0) +
      nonPrimeVM k.1 * Λ k.2.1 * Λ k.2.2 + Λ k.1 * nonPrimeVM k.2.1 * Λ k.2.2 +
      Λ k.1 * Λ k.2.1 * nonPrimeVM k.2.2) := by
    rw [hr]; exact Finset.sum_le_sum (fun k hk ↦ term_le hk)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib, hsum] at hle
  have nn : ∀ n : ℕ, 0 ≤ Λ n := fun n ↦ ArithmeticFunction.vonMangoldt_nonneg
  have hΛ : ∀ n ∈ Icc 1 N, Λ n ≤ Real.log N := fun n hn ↦
    vonMangoldt_le_log_of_le (Finset.mem_Icc.mp hn).1 (Finset.mem_Icc.mp hn).2
  have hL0 : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  have hΛ' : ∀ n ∈ Icc 1 N, nonPrimeVM n ≤ Real.log N := fun n hn ↦ by
    unfold nonPrimeVM
    split_ifs
    · exact hL0
    · exact hΛ n hn
  have s1 : ∑ n ∈ Icc 1 N, nonPrimeVM n ≤ 2 * √(N : ℝ) * Real.log N := sum_nonPrimeVM_le hN
  have s2 : ∑ n ∈ Icc 1 N, Λ n ≤ (Real.log 4 + 4) * N := sum_vonMangoldt_le N
  have hs1 : 0 ≤ ∑ n ∈ Icc 1 N, nonPrimeVM n := Finset.sum_nonneg (fun n _ ↦ nonPrimeVM_nonneg n)
  have hs2 : 0 ≤ ∑ n ∈ Icc 1 N, Λ n := Finset.sum_nonneg (fun n _ ↦ nn n)
  have b1 : W N nonPrimeVM Λ Λ ≤ Real.log N * ((∑ n ∈ Icc 1 N, nonPrimeVM n) *
      (∑ n ∈ Icc 1 N, Λ n)) := W_le N nonPrimeVM_nonneg nn hL0 (fun n hn ↦ hΛ n hn)
  have b1' : Real.log N * ((∑ n ∈ Icc 1 N, nonPrimeVM n) * (∑ n ∈ Icc 1 N, Λ n)) ≤
      Real.log N * ((2 * √(N : ℝ) * Real.log N) * ((Real.log 4 + 4) * N)) := by
    gcongr
  have c2 : W N Λ nonPrimeVM Λ = W N nonPrimeVM Λ Λ := W_cyc N Λ nonPrimeVM Λ
  have c3 : W N Λ Λ nonPrimeVM = W N Λ nonPrimeVM Λ := W_cyc N Λ Λ nonPrimeVM
  have e1 : ∑ k ∈ Tall N, nonPrimeVM k.1 * Λ k.2.1 * Λ k.2.2 = W N nonPrimeVM Λ Λ := rfl
  have e2 : ∑ k ∈ Tall N, Λ k.1 * nonPrimeVM k.2.1 * Λ k.2.2 = W N Λ nonPrimeVM Λ := rfl
  have e3 : ∑ k ∈ Tall N, Λ k.1 * Λ k.2.1 * nonPrimeVM k.2.2 = W N Λ Λ nonPrimeVM := rfl
  rw [e1, e2, e3] at hle
  linarith

/-- **Davenport, Ch. 26, p. 146 (row 26-5)**: every sufficiently large odd `N` is the sum of
three primes in `≫ N² (log N)^{-3}` ways (ordered triples). -/
@[kb "davenport1980" "Ch 26, p. 146"]
theorem card_three_primes_ge :
    ∃ c > 0, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Odd N →
      c * N ^ 2 / Real.log N ^ 3 ≤
        (((Icc 1 N ×ˢ Icc 1 N ×ˢ Icc 1 N).filter (fun k ↦ k.1.Prime ∧ k.2.1.Prime ∧
          k.2.2.Prime ∧ k.1 + k.2.1 + k.2.2 = N)).card : ℝ) := by
  obtain ⟨C, hC, N₁, h1⟩ := main_estimate 1 one_pos
  have hK : 0 < Real.log 4 + 4 := by
    have := Real.log_pos (by norm_num : (1 : ℝ) < 4); linarith
  obtain ⟨N₂, h2⟩ := exists_log_rpow_le 2 (1 / 2) (1 / (48 * (Real.log 4 + 4))) (by norm_num)
    (by positivity)
  refine ⟨1 / 8, by norm_num, max (max N₁ N₂) (max 3 ⌈Real.exp (4 * C)⌉₊), fun N hN hodd ↦ ?_⟩
  have hN1 : N₁ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hN2 : N₂ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hN3 : 3 ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hN4 : ⌈Real.exp (4 * C)⌉₊ ≤ N :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  have hNr : (3 : ℝ) ≤ N := by exact_mod_cast hN3
  have hNpos : (0 : ℝ) < N := by linarith
  have hL0 : 0 < Real.log N := Real.log_pos (by linarith)
  set L := Real.log N with hLdef
  have hLC : 4 * C ≤ L := by
    rw [hLdef, Real.le_log_iff_exp_le hNpos]
    exact (Nat.le_ceil _).trans (by exact_mod_cast hN4)
  have hG : 1 ≤ singularSeries (N : ℤ) := one_le_singularSeries_of_odd (by exact_mod_cast hodd)
  have h := h1 N hN1
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, Real.rpow_neg_one] at h
  have hr : (N : ℝ) ^ 2 / 4 ≤ threePrimeRep N := by
    have h3 := (abs_le.mp h).1
    have h4 : C * (N : ℝ) ^ 2 * L⁻¹ ≤ (N : ℝ) ^ 2 / 4 := by
      have : C * L⁻¹ ≤ 1 / 4 := by
        rw [← div_eq_mul_inv, div_le_iff₀ hL0]; linarith
      calc C * (N : ℝ) ^ 2 * L⁻¹ = (C * L⁻¹) * (N : ℝ) ^ 2 := by ring
        _ ≤ 1 / 4 * (N : ℝ) ^ 2 := by gcongr
        _ = _ := by ring
    have h5 : (N : ℝ) ^ 2 / 2 ≤ singularSeries (N : ℤ) * (N : ℝ) ^ 2 / 2 := by
      have : (N : ℝ) ^ 2 ≤ singularSeries (N : ℤ) * (N : ℝ) ^ 2 := by
        nlinarith [sq_nonneg (N : ℝ)]
      linarith
    linarith
  have hgood := threePrimeRep_le_good (N := N) (by omega)
  have hL2 : L ^ 2 ≤ 1 / (48 * (Real.log 4 + 4)) * √(N : ℝ) := by
    have := h2 N hN2
    rwa [Real.rpow_two, ← Real.sqrt_eq_rpow] at this
  have hsq : √(N : ℝ) * √(N : ℝ) = N := Real.mul_self_sqrt hNpos.le
  have hbad : 3 * (L * ((2 * √(N : ℝ) * L) * ((Real.log 4 + 4) * N))) ≤ (N : ℝ) ^ 2 / 8 := by
    have e : 3 * (L * ((2 * √(N : ℝ) * L) * ((Real.log 4 + 4) * N))) =
        6 * (Real.log 4 + 4) * N * √(N : ℝ) * L ^ 2 := by ring
    rw [e]
    calc 6 * (Real.log 4 + 4) * N * √(N : ℝ) * L ^ 2
        ≤ 6 * (Real.log 4 + 4) * N * √(N : ℝ) * (1 / (48 * (Real.log 4 + 4)) * √(N : ℝ)) := by
          gcongr
      _ = N * (√(N : ℝ) * √(N : ℝ)) / 8 := by field_simp; ring
      _ = _ := by rw [hsq]; ring
  have hcard : (N : ℝ) ^ 2 / 8 ≤ L ^ 3 * (((Icc 1 N ×ˢ Icc 1 N ×ˢ Icc 1 N).filter
      (fun k : ℕ × ℕ × ℕ ↦ k.1.Prime ∧ k.2.1.Prime ∧ k.2.2.Prime ∧
        k.1 + k.2.1 + k.2.2 = N)).card : ℝ) := by linarith
  rw [div_le_iff₀ (by positivity)]
  linarith

/-- **Vinogradov's three primes theorem, Davenport, Ch. 26, p. 146 (row 26-5)**: every
sufficiently large odd integer is the sum of three primes. -/
@[kb "davenport1980" "Ch 26, p. 146"]
theorem exists_three_primes_of_odd :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Odd N →
      ∃ p₁ p₂ p₃ : ℕ, p₁.Prime ∧ p₂.Prime ∧ p₃.Prime ∧ p₁ + p₂ + p₃ = N := by
  obtain ⟨c, hc, N₀, h⟩ := card_three_primes_ge
  refine ⟨max N₀ 3, fun N hN hodd ↦ ?_⟩
  have h1 := h N (le_trans (le_max_left _ _) hN) hodd
  have hN3 : (3 : ℝ) ≤ N := by exact_mod_cast le_trans (le_max_right _ _) hN
  have hL0 : 0 < Real.log N := Real.log_pos (by linarith)
  have hpos : 0 < c * (N : ℝ) ^ 2 / Real.log N ^ 3 := by positivity
  have hcard : 0 < (((Icc 1 N ×ˢ Icc 1 N ×ˢ Icc 1 N).filter (fun k ↦ k.1.Prime ∧ k.2.1.Prime ∧
      k.2.2.Prime ∧ k.1 + k.2.1 + k.2.2 = N)).card : ℝ) := lt_of_lt_of_le hpos h1
  obtain ⟨k, hk⟩ := Finset.card_pos.mp (by exact_mod_cast hcard)
  simp only [Finset.mem_filter] at hk
  exact ⟨k.1, k.2.1, k.2.2, hk.2.1, hk.2.2.1, hk.2.2.2.1, hk.2.2.2.2⟩

end NTKB.Davenport
