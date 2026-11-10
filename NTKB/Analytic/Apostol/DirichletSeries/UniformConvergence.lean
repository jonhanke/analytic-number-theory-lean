/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.LSeries.Deriv
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import NTKB.Attr

/-!
# Uniform convergence of Dirichlet series (Apostol, §§11.6–11.7)

* **Lemma 2 of Chapter 11** (`ch11_lemma_2`): if the partial sums of `∑ f(n) n^{-s₀}` are bounded
  by `M`, then for `σ > σ₀` and `0 < a ≤ b`,
  `|∑_{a<n≤b} f(n) n^{-s}| ≤ 2M a^{σ₀-σ} (1 + |s - s₀|/(σ - σ₀))`.
* **Theorem 11.8** (`tendsto_partialSums_of_re_lt`): convergence at `s₀` implies convergence for
  `Re s > Re s₀` (also in Tau Ceti; re-derived here from Lemma 2 since NTKB depends on Mathlib only).
* **Theorem 11.11** (`apostol_thm_11_11`): a Dirichlet series converging at `s₀` converges
  uniformly on every compact set lying in the half-plane `Re s > Re s₀`. Since the half-plane of
  convergence `σ > σ_c` is the union of these half-planes and a compact subset of it has
  `min Re > σ_c`, this is Apostol's statement.

Convergence here is that of the partial sums `∑_{n < N} f(n) n^{-s}` (the series need not
converge absolutely; Mathlib's `LSeries` is the absolutely convergent sum). Proofs follow
Apostol: Abel summation (Mathlib's `sum_mul_eq_sub_sub_integral_mul`) with `x^{s₀-s}`.
-/

open Complex Filter Topology Finset MeasureTheory LSeries

namespace NTKB.Apostol

/-- The partial sums `∑_{n < N} f(n) n^{-s}` of a Dirichlet series. -/
noncomputable def dirichletPartialSum (f : ℕ → ℂ) (s : ℂ) (N : ℕ) : ℂ :=
  ∑ n ∈ range N, term f s n

lemma hasDerivAt_ofReal_cpow' {t : ℝ} (ht : 0 < t) (w : ℂ) :
    HasDerivAt (fun y : ℝ => (y : ℂ) ^ w) (w * (t : ℂ) ^ (w - 1)) t :=
  (Complex.hasStrictDerivAt_cpow_const (ofReal_mem_slitPlane.mpr ht)).hasDerivAt.comp_ofReal

/-- **Lemma 2 of Chapter 11** (Apostol, p. 232). -/
@[kb "apostol1976" "Ch. 11, Lemma 2, p. 232"]
theorem ch11_lemma_2 {f : ℕ → ℂ} {s₀ s : ℂ} {M : ℝ}
    (hM : ∀ N : ℕ, ‖∑ k ∈ Icc 0 N, term f s₀ k‖ ≤ M) (hs : s₀.re < s.re) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    ‖∑ k ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, term f s k‖ ≤
      2 * M * a ^ (s₀.re - s.re) * (1 + ‖s - s₀‖ / (s.re - s₀.re)) := by
  set w : ℂ := s₀ - s with hw
  set φ : ℝ → ℂ := fun t => (t : ℂ) ^ w with hφ
  set A : ℝ → ℂ := fun t => ∑ k ∈ Icc 0 ⌊t⌋₊, term f s₀ k with hA
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hα : 0 < s.re - s₀.re := by linarith
  have hwre : w.re = s₀.re - s.re := by simp [hw]
  have hderiv : ∀ t, 0 < t → deriv φ t = w * (t : ℂ) ^ (w - 1) := fun t ht =>
    (hasDerivAt_ofReal_cpow' ht w).deriv
  have hcont : ContinuousOn (fun t : ℝ => w * (t : ℂ) ^ (w - 1)) (Set.Icc a b) := by
    intro t ht
    have ht0 : 0 < t := ha.trans_le ht.1
    exact ((continuousAt_const.mul ((continuousAt_cpow_const (ofReal_mem_slitPlane.mpr ht0)).comp
      continuous_ofReal.continuousAt))).continuousWithinAt
  have hint : IntegrableOn (deriv φ) (Set.Icc a b) := by
    refine (hcont.integrableOn_Icc).congr_fun (fun t ht => ?_) measurableSet_Icc
    exact (hderiv t (ha.trans_le ht.1)).symm
  have key := sum_mul_eq_sub_sub_integral_mul (term f s₀) ha.le hab
    (fun t ht => (hasDerivAt_ofReal_cpow' (ha.trans_le ht.1) w).differentiableAt) hint
  -- the left side is the sum of `f(n) n^{-s}`
  have hlhs : ∑ k ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, φ k * term f s₀ k = ∑ k ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, term f s k := by
    refine sum_congr rfl fun k hk => ?_
    have hk0 : k ≠ 0 := by have := (mem_Ioc.mp hk).1; omega
    have hk' : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hk0
    simp only [hφ, ofReal_natCast, term_of_ne_zero hk0, hw]
    have h0 : (k : ℂ) ^ s₀ ≠ 0 := by simp [hk0]
    have h1 : (k : ℂ) ^ s ≠ 0 := by simp [hk0]
    rw [cpow_sub _ _ hk']
    field_simp
  rw [hlhs] at key
  rw [key]
  -- bounds
  have hnormφ : ∀ t, 0 < t → ‖φ t‖ = t ^ (s₀.re - s.re) := fun t ht => by
    simp only [hφ]; rw [norm_cpow_eq_rpow_re_of_pos ht, hwre]
  have hPa : 0 ≤ a ^ (s₀.re - s.re) := Real.rpow_nonneg ha.le _
  have hQ : b ^ (s₀.re - s.re) ≤ a ^ (s₀.re - s.re) :=
    Real.rpow_le_rpow_of_nonpos ha hab (by linarith)
  have hb : 0 < b := ha.trans_le hab
  have h1 : ‖φ b * A b‖ ≤ b ^ (s₀.re - s.re) * M := by
    rw [norm_mul, hnormφ b hb]; exact mul_le_mul_of_nonneg_left (hM _) (Real.rpow_nonneg hb.le _)
  have h2 : ‖φ a * A a‖ ≤ a ^ (s₀.re - s.re) * M := by
    rw [norm_mul, hnormφ a ha]; exact mul_le_mul_of_nonneg_left (hM _) hPa
  have h3 : ‖∫ t in Set.Ioc a b, deriv φ t * A t‖ ≤
      ‖w‖ * M * ((a ^ (s₀.re - s.re) - b ^ (s₀.re - s.re)) / (s.re - s₀.re)) := by
    rw [← intervalIntegral.integral_of_le hab]
    have hr : (s₀.re - s.re - 1) ≠ -1 := by linarith
    have h0 : (0 : ℝ) ∉ Set.uIcc a b := by
      rw [Set.uIcc_of_le hab]; exact fun h => absurd h.1 (not_le.mpr ha)
    have hI : ∫ t in a..b, ‖w‖ * M * t ^ (s₀.re - s.re - 1) =
        ‖w‖ * M * ((a ^ (s₀.re - s.re) - b ^ (s₀.re - s.re)) / (s.re - s₀.re)) := by
      rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inr ⟨hr, h0⟩)]
      congr 1
      rw [show s₀.re - s.re - 1 + 1 = -(s.re - s₀.re) by ring, div_neg, ← neg_div]
      ring_nf
    rw [← hI]
    refine intervalIntegral.norm_integral_le_of_norm_le hab
      (Eventually.of_forall fun t ht => ?_) ?_
    · have ht0 : 0 < t := ha.trans ht.1
      rw [hderiv t ht0, norm_mul, norm_mul, norm_cpow_eq_rpow_re_of_pos ht0]
      have : (w - 1).re = s₀.re - s.re - 1 := by simp [hw]
      rw [this]
      calc ‖w‖ * t ^ (s₀.re - s.re - 1) * ‖A t‖ ≤ ‖w‖ * t ^ (s₀.re - s.re - 1) * M :=
            mul_le_mul_of_nonneg_left (hM _) (by positivity)
        _ = ‖w‖ * M * t ^ (s₀.re - s.re - 1) := by ring
    · exact (intervalIntegral.intervalIntegrable_rpow (Or.inr h0)).const_mul _
  have hwn : ‖w‖ = ‖s - s₀‖ := by rw [hw, norm_sub_rev]
  calc ‖φ b * A b - φ a * A a - ∫ t in Set.Ioc a b, deriv φ t * A t‖
      ≤ ‖φ b * A b‖ + ‖φ a * A a‖ + ‖∫ t in Set.Ioc a b, deriv φ t * A t‖ := by
        refine (norm_sub_le _ _).trans ?_
        gcongr
        exact norm_sub_le _ _
    _ ≤ b ^ (s₀.re - s.re) * M + a ^ (s₀.re - s.re) * M +
        ‖w‖ * M * ((a ^ (s₀.re - s.re) - b ^ (s₀.re - s.re)) / (s.re - s₀.re)) := by gcongr
    _ ≤ 2 * M * a ^ (s₀.re - s.re) * (1 + ‖s - s₀‖ / (s.re - s₀.re)) := by
        rw [hwn]
        have hQ0 : 0 ≤ b ^ (s₀.re - s.re) := Real.rpow_nonneg hb.le _
        have e : ‖s - s₀‖ * M * ((a ^ (s₀.re - s.re) - b ^ (s₀.re - s.re)) / (s.re - s₀.re)) ≤
            ‖s - s₀‖ * M * (a ^ (s₀.re - s.re) / (s.re - s₀.re)) := by
          gcongr; linarith
        have e2 : 0 ≤ ‖s - s₀‖ * M * (a ^ (s₀.re - s.re) / (s.re - s₀.re)) := by positivity
        calc _ ≤ a ^ (s₀.re - s.re) * M + a ^ (s₀.re - s.re) * M +
              ‖s - s₀‖ * M * (a ^ (s₀.re - s.re) / (s.re - s₀.re)) := by
              gcongr
          _ ≤ _ := by
              rw [mul_add, mul_one]
              have : 2 * M * a ^ (s₀.re - s.re) * (‖s - s₀‖ / (s.re - s₀.re)) =
                  2 * (‖s - s₀‖ * M * (a ^ (s₀.re - s.re) / (s.re - s₀.re))) := by ring
              rw [this]
              linarith

lemma Ico_eq_Ioc_pred {n m : ℕ} (hn : 1 ≤ n) :
    Ico n m = Ioc ⌊((n : ℝ) - 1)⌋₊ ⌊((m : ℝ) - 1)⌋₊ := by
  have h1 : ⌊((n : ℝ) - 1)⌋₊ = n - 1 := by
    rw [show ((n : ℝ) - 1) = ((n - 1 : ℕ) : ℝ) by push_cast [Nat.cast_sub hn]; ring, Nat.floor_natCast]
  have h2 : ⌊((m : ℝ) - 1)⌋₊ = m - 1 := by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp only [Nat.cast_zero, zero_sub]
      exact Nat.floor_of_nonpos (by norm_num)
    rw [show ((m : ℝ) - 1) = ((m - 1 : ℕ) : ℝ) by push_cast [Nat.cast_sub hm]; ring,
      Nat.floor_natCast]
  rw [h1, h2]
  ext k
  simp only [mem_Ico, mem_Ioc]
  omega

/-- Uniform Cauchy estimate behind Theorems 11.8 and 11.11: if the partial sums at `s₀` are
bounded by `M`, `Re s - Re s₀ ≥ δ > 0` and `|s - s₀| ≤ C`, then for `2 ≤ n ≤ m` the block
`∑_{n ≤ k < m} f(k) k^{-s}` is at most `2M (1 + C/δ) (n-1)^{-δ}`. -/
lemma norm_partialSum_sub_le {f : ℕ → ℂ} {s₀ s : ℂ} {M C δ : ℝ}
    (hM : ∀ N : ℕ, ‖∑ k ∈ Icc 0 N, term f s₀ k‖ ≤ M) (hδ : 0 < δ) (hsδ : δ ≤ s.re - s₀.re)
    (hC : ‖s - s₀‖ ≤ C) {n m : ℕ} (hn : 2 ≤ n) (hnm : n ≤ m) :
    ‖dirichletPartialSum f s m - dirichletPartialSum f s n‖ ≤
      2 * M * (1 + C / δ) * ((n : ℝ) - 1) ^ (-δ) := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hn1 : (1 : ℝ) ≤ (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hnm' : (n : ℝ) - 1 ≤ (m : ℝ) - 1 := by
    have : (n : ℝ) ≤ m := by exact_mod_cast hnm
    linarith
  have hα : 0 < s.re - s₀.re := hδ.trans_le hsδ
  rw [dirichletPartialSum, dirichletPartialSum, ← Finset.sum_range_add_sum_Ico _ hnm,
    add_sub_cancel_left, Ico_eq_Ioc_pred (by omega)]
  refine (ch11_lemma_2 hM (by linarith) (by linarith) hnm').trans ?_
  have e1 : ((n : ℝ) - 1) ^ (s₀.re - s.re) ≤ ((n : ℝ) - 1) ^ (-δ) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  have e2 : ‖s - s₀‖ / (s.re - s₀.re) ≤ C / δ := by
    have hC0 : 0 ≤ C := (norm_nonneg _).trans hC
    calc ‖s - s₀‖ / (s.re - s₀.re) ≤ C / (s.re - s₀.re) := by gcongr
      _ ≤ C / δ := by gcongr
  have e3 : 0 ≤ ((n : ℝ) - 1) ^ (s₀.re - s.re) := Real.rpow_nonneg (by linarith) _
  calc 2 * M * ((n : ℝ) - 1) ^ (s₀.re - s.re) * (1 + ‖s - s₀‖ / (s.re - s₀.re))
      ≤ 2 * M * ((n : ℝ) - 1) ^ (-δ) * (1 + C / δ) := by
        gcongr
    _ = 2 * M * (1 + C / δ) * ((n : ℝ) - 1) ^ (-δ) := by ring

/-- Bounded partial sums from convergence. -/
lemma exists_bound_partialSum {f : ℕ → ℂ} {s₀ L : ℂ}
    (h : Tendsto (dirichletPartialSum f s₀) atTop (𝓝 L)) :
    ∃ M, ∀ N : ℕ, ‖∑ k ∈ Icc 0 N, term f s₀ k‖ ≤ M := by
  obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.mp (Metric.isBounded_range_of_tendsto _ h)
  refine ⟨M, fun N => ?_⟩
  rw [← Nat.range_succ_eq_Icc_zero]
  exact hM _ ⟨N + 1, rfl⟩

/-- Theorem 11.11 with a fixed point of convergence `s₀` to the left of `K`. -/
theorem tendstoUniformlyOn_partialSum {f : ℕ → ℂ} {s₀ L : ℂ}
    (h : Tendsto (dirichletPartialSum f s₀) atTop (𝓝 L)) {K : Set ℂ} (hK : IsCompact K)
    (hKs : ∀ s ∈ K, s₀.re < s.re) :
    TendstoUniformlyOn (fun N s => dirichletPartialSum f s N)
      (fun s => limUnder atTop (dirichletPartialSum f s)) atTop K := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact tendstoUniformlyOn_empty
  obtain ⟨M, hM⟩ := exists_bound_partialSum h
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  obtain ⟨s₁, hs₁K, hs₁⟩ := hK.exists_isMinOn hne continuous_re.continuousOn
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn
    (f := fun s => s - s₀) (continuous_id.sub continuous_const).continuousOn
  set δ := s₁.re - s₀.re
  have hδ : 0 < δ := by have := hKs s₁ hs₁K; simp only [δ]; linarith
  have hbound : ∀ s ∈ K, ∀ n m : ℕ, 2 ≤ n → n ≤ m →
      ‖dirichletPartialSum f s m - dirichletPartialSum f s n‖ ≤
        2 * M * (1 + C / δ) * ((n : ℝ) - 1) ^ (-δ) := fun s hs n m hn hnm =>
    norm_partialSum_sub_le hM hδ (by have := hs₁ hs; simp only [δ]; simp at this; linarith)
      (hC s hs) hn hnm
  have hlim : Tendsto (fun n : ℕ => 2 * M * (1 + C / δ) * ((n : ℝ) - 1) ^ (-δ)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => (n : ℝ) - 1) atTop atTop :=
      tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
    simpa using ((tendsto_rpow_neg_atTop hδ).comp h1).const_mul (2 * M * (1 + C / δ))
  have hcauchy : UniformCauchySeqOn (fun N s => dirichletPartialSum f s N) atTop K := by
    rw [Metric.uniformCauchySeqOn_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := (eventually_atTop.mp ((tendsto_order.mp hlim).2 ε hε))
    refine ⟨max N 2, fun m hm n hn s hs => ?_⟩
    rw [dist_eq_norm]
    rcases le_total n m with hnm | hmn
    · exact (hbound s hs n m (le_of_max_le_right hn) hnm).trans_lt (hN n (le_of_max_le_left hn))
    · rw [norm_sub_rev]
      exact (hbound s hs m n (le_of_max_le_right hm) hmn).trans_lt (hN m (le_of_max_le_left hm))
  refine hcauchy.tendstoUniformlyOn_of_tendsto fun s hs => ?_
  obtain ⟨L', hL'⟩ := cauchySeq_tendsto_of_complete (hcauchy.cauchySeq hs)
  exact tendsto_nhds_limUnder ⟨L', hL'⟩

/-- **Theorem 11.8** (first statement): if `∑ f(n) n^{-s}` converges at `s₀`, it converges at
every `s` with `Re s > Re s₀`. -/
@[kb "apostol1976" "Thm 11.8, p. 233"]
theorem apostol_thm_11_8 {f : ℕ → ℂ} {s₀ L : ℂ}
    (h : Tendsto (dirichletPartialSum f s₀) atTop (𝓝 L)) {s : ℂ} (hs : s₀.re < s.re) :
    ∃ L', Tendsto (dirichletPartialSum f s) atTop (𝓝 L') :=
  ⟨_, (tendstoUniformlyOn_partialSum h isCompact_singleton (by simpa using hs)).tendsto_at
    (Set.mem_singleton s)⟩

/-- **Theorem 11.11**: a Dirichlet series converges uniformly on every compact set `K` interior
to its half-plane of convergence, i.e. such that each point of `K` lies strictly to the right of
some point where the series converges. -/
@[kb "apostol1976" "Thm 11.11, p. 235"]
theorem apostol_thm_11_11 {f : ℕ → ℂ} {K : Set ℂ} (hK : IsCompact K)
    (hKs : ∀ s ∈ K, ∃ s₀ : ℂ, s₀.re < s.re ∧ ∃ L, Tendsto (dirichletPartialSum f s₀) atTop (𝓝 L)) :
    TendstoUniformlyOn (fun N s => dirichletPartialSum f s N)
      (fun s => limUnder atTop (dirichletPartialSum f s)) atTop K := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact tendstoUniformlyOn_empty
  obtain ⟨s₁, hs₁K, hs₁⟩ := hK.exists_isMinOn hne continuous_re.continuousOn
  obtain ⟨s₀, hs₀, L, hL⟩ := hKs s₁ hs₁K
  exact tendstoUniformlyOn_partialSum hL hK fun s hs =>
    hs₀.trans_le (by simpa using hs₁ hs)

/-! ### Theorem 11.12 -/

/-- The half-plane of convergence `σ > σ_c` of `∑ f(n) n^{-s}`: the points lying strictly to the
right of some point where the series converges. -/
def halfPlaneOfConv (f : ℕ → ℂ) : Set ℂ :=
  {s | ∃ s₀ : ℂ, s₀.re < s.re ∧ ∃ L, Tendsto (dirichletPartialSum f s₀) atTop (𝓝 L)}

lemma isOpen_halfPlaneOfConv (f : ℕ → ℂ) : IsOpen (halfPlaneOfConv f) := by
  rw [isOpen_iff_forall_mem_open]
  rintro s ⟨s₀, hs₀, hL⟩
  refine ⟨{z | s₀.re < z.re}, fun z hz => ⟨s₀, hz, hL⟩,
    isOpen_lt continuous_const continuous_re, hs₀⟩

/-- The sum function `F(s) = ∑ f(n) n^{-s}` (limit of the partial sums) of a Dirichlet series. -/
noncomputable def dirichletSum (f : ℕ → ℂ) (s : ℂ) : ℂ :=
  limUnder atTop (dirichletPartialSum f s)

lemma hasDerivAt_dirichletPartialSum (f : ℕ → ℂ) (N : ℕ) (s : ℂ) :
    HasDerivAt (fun z => dirichletPartialSum f z N)
      (dirichletPartialSum (fun n => -logMul f n) s N) s := by
  unfold dirichletPartialSum
  have : ∑ n ∈ range N, term (fun n => -logMul f n) s n = ∑ n ∈ range N, -term (logMul f) s n := by
    refine sum_congr rfl fun n _ => ?_
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    rw [term_of_ne_zero hn, term_of_ne_zero hn, neg_div]
  rw [this]
  exact HasDerivAt.fun_sum fun n _ => hasDerivAt_term f n s

/-- **Theorem 11.12**: the sum function of a Dirichlet series is analytic in its half-plane of
convergence, and its derivative is the sum of the differentiated series
`F'(s) = -∑ f(n) log n · n^{-s}` (which converges there). -/
@[kb "apostol1976" "Thm 11.12, p. 236"]
theorem apostol_thm_11_12 (f : ℕ → ℂ) :
    DifferentiableOn ℂ (dirichletSum f) (halfPlaneOfConv f) ∧
      ∀ s ∈ halfPlaneOfConv f, Tendsto (dirichletPartialSum (fun n => -logMul f n) s) atTop
        (𝓝 (deriv (dirichletSum f) s)) := by
  have hU := isOpen_halfPlaneOfConv f
  have hloc : TendstoLocallyUniformlyOn (fun N s => dirichletPartialSum f s N) (dirichletSum f)
      atTop (halfPlaneOfConv f) :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).mpr fun K hKU hK =>
      apostol_thm_11_11 hK fun s hs => hKU hs
  have hdiff : ∀ᶠ N in atTop, DifferentiableOn ℂ (fun s => dirichletPartialSum f s N)
      (halfPlaneOfConv f) := Eventually.of_forall fun N s _ =>
    (hasDerivAt_dirichletPartialSum f N s).differentiableAt.differentiableWithinAt
  refine ⟨hloc.differentiableOn hdiff hU, fun s hs => ?_⟩
  refine ((hloc.deriv hdiff hU).tendsto_at hs).congr fun N => ?_
  exact (hasDerivAt_dirichletPartialSum f N s).deriv

end NTKB.Apostol
