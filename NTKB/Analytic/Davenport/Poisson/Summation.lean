/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Davenport.Poisson.SecondMean

/-!
# Poisson summation for a continuous piecewise monotone function (Davenport, Chapter 2)

For `A < B` and `f` continuous on `[A, B]` and monotone or antitone on each piece of a finite
partition of `[A, B]`,
`∑'_{A ≤ n ≤ B} f(n) = lim_{N → ∞} ∑_{|ν| ≤ N} ∫_A^B f(x) e(νx) dx`,
where `∑'` halves the terms `n = A` and `n = B` when these are integers (`halvedSum f A B`).
Mathlib has Poisson summation over all of `ℤ` with summability hypotheses
(`Real.tsum_eq_tsum_fourier`); this is the finite form with the Dirichlet–Jordan argument, the
form Davenport uses for the theta relation and the quadratic Gauss sum.

Route: `∑_{|ν| ≤ N} ∫_A^B f e(νx) = ∫_A^B f D_N` (`sum_exp_eq_dirichletKernel`); the limit is
additive in the interval, so it suffices to treat a monotone piece of length at most `1/2` with
at most one integer, at an end. With the integer at `0`: `∫_0^δ f D_N → f(0)/2` by
`∫_0^{1/2} D_N = 1/2`, the Riemann–Lebesgue lemma away from `0`, and near `0` the second mean
value bound with the uniform bound on the partial integrals of `D_N`.

Source text unavailable; written from the map row Davenport 2-6.
-/

open Real Finset MeasureTheory Filter Topology

namespace NTKB.Davenport.Poisson

/-- `∑'_{A ≤ n ≤ B} f(n)`: the sum over the integers of `[A, B]`, with the terms `n = A` and
`n = B` halved. -/
noncomputable def halvedSum (f : ℝ → ℝ) (A B : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc ⌈A⌉ ⌊B⌋, (if (n : ℝ) = A ∨ (n : ℝ) = B then (1 / 2 : ℝ) else 1) * f n

/-- `f` is monotone or antitone on each piece of a finite partition `A = x₀ < ⋯ < x_k = B`. -/
def PiecewiseMonotoneOn (f : ℝ → ℝ) (A B : ℝ) : Prop :=
  ∃ (k : ℕ) (x : Fin (k + 1) → ℝ), x 0 = A ∧ x (Fin.last k) = B ∧ StrictMono x ∧
    ∀ i : Fin k, MonotoneOn f (Set.Icc (x i.castSucc) (x i.succ)) ∨
      AntitoneOn f (Set.Icc (x i.castSucc) (x i.succ))

/-- The halved sum as a sum over any larger integer range, with explicit weights. -/
theorem halvedSum_eq_sum_Icc {f : ℝ → ℝ} {a b : ℝ} {L U : ℤ} (hL : L ≤ ⌈a⌉) (hU : ⌊b⌋ ≤ U) :
    halvedSum f a b = ∑ n ∈ Finset.Icc L U,
      (if a ≤ n ∧ (n : ℝ) ≤ b then (if (n : ℝ) = a ∨ (n : ℝ) = b then (1 / 2 : ℝ) else 1)
        else 0) * f n := by
  have hsub : Finset.Icc ⌈a⌉ ⌊b⌋ ⊆ Finset.Icc L U := Finset.Icc_subset_Icc hL hU
  unfold halvedSum
  rw [← Finset.sum_subset hsub]
  · refine Finset.sum_congr rfl fun n hn => ?_
    rw [Finset.mem_Icc] at hn
    have h1 : a ≤ n := Int.ceil_le.mp hn.1
    have h2 : (n : ℝ) ≤ b := Int.le_floor.mp hn.2
    have hc : a ≤ n ∧ (n : ℝ) ≤ b := ⟨h1, h2⟩
    simp only [hc, and_self, ↓reduceIte]
  · intro n _ hn
    rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hn
    have : ¬ (a ≤ n ∧ (n : ℝ) ≤ b) := by
      rintro ⟨h1, h2⟩
      rcases hn with hn | hn
      · exact absurd (Int.ceil_le.mpr h1) (not_le.mpr hn)
      · exact absurd (Int.le_floor.mpr h2) (not_le.mpr hn)
    simp only [this, ↓reduceIte, zero_mul]

/-- Additivity of the halved sum: `∑'_{[a, b]} = ∑'_{[a, c]} + ∑'_{[c, b]}` for `a < c < b`. -/
theorem halvedSum_add {f : ℝ → ℝ} {a b c : ℝ} (hac : a < c) (hcb : c < b) :
    halvedSum f a b = halvedSum f a c + halvedSum f c b := by
  rw [halvedSum_eq_sum_Icc (f := f) (a := a) (b := b) (L := ⌈a⌉) (U := ⌊b⌋) le_rfl le_rfl,
    halvedSum_eq_sum_Icc (f := f) (a := a) (b := c) (L := ⌈a⌉) (U := ⌊b⌋) le_rfl
      (Int.floor_mono hcb.le),
    halvedSum_eq_sum_Icc (f := f) (a := c) (b := b) (L := ⌈a⌉) (U := ⌊b⌋)
      (Int.ceil_mono hac.le) le_rfl, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [← add_mul]
  congr 1
  generalize (n : ℝ) = x
  have hab : a < b := hac.trans hcb
  rcases lt_trichotomy x a with h1 | h1 | h1 <;> rcases lt_trichotomy x c with h2 | h2 | h2 <;>
    rcases lt_trichotomy x b with h3 | h3 | h3 <;>
    (try subst_vars) <;> split_ifs <;> simp_all <;>
      first | linarith | (rcases ‹x = a ∨ x = b› with h | h <;> linarith)

theorem no_int_of_pos_le_half {η d : ℝ} (hη : 0 < η) (hd : d ≤ 1 / 2) :
    ∀ n : ℤ, (n : ℝ) ∉ Set.Icc η d := by
  intro n hn
  have h0 : (0 : ℤ) < n := by exact_mod_cast hη.trans_le hn.1
  have h1 : (1 : ℝ) ≤ n := by exact_mod_cast h0
  linarith [hn.2]

theorem tendsto_integral_dirichletKernel_zero_left_aux {η : ℝ} (hη : 0 < η) (hη' : η ≤ 1 / 2) :
    Tendsto (fun N : ℕ ↦ ∫ x in (0 : ℝ)..η, dirichletKernel N x) atTop (𝓝 (1 / 2)) := by
  have h := tendsto_integral_mul_dirichletKernel_of_forall_int_notMem (g := fun _ => (1 : ℝ))
    (a := η) (b := 1 / 2) hη' continuousOn_const (no_int_of_pos_le_half hη le_rfl)
  have h2 := (tendsto_const_nhds (x := (1 / 2 : ℝ))).sub h
  rw [sub_zero] at h2
  refine h2.congr (fun N => ?_)
  have hc := continuous_dirichletKernel N
  have := intervalIntegral.integral_add_adjacent_intervals (a := 0) (b := η) (c := 1 / 2)
    (f := dirichletKernel N) (μ := volume) (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)
  simp only [one_mul]
  linarith [integral_dirichletKernel_zero_half N]

/-- Near an integer, at the left end: `∫_0^δ f D_N → f(0)/2` for `0 < δ ≤ 1/2`. -/
theorem tendsto_integral_mul_dirichletKernel_zero_left {f : ℝ → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hδ' : δ ≤ 1 / 2) (hf : ContinuousOn f (Set.Icc 0 δ)) (hm : MonotoneOn f (Set.Icc 0 δ)) :
    Tendsto (fun N : ℕ ↦ ∫ x in (0 : ℝ)..δ, f x * dirichletKernel N x) atTop
      (𝓝 (f 0 / 2)) := by
  set h : ℝ → ℝ := fun x => f x - f 0 with hh
  have hcont : ContinuousOn h (Set.Icc 0 δ) := hf.sub continuousOn_const
  have hmono : MonotoneOn h (Set.Icc 0 δ) := fun x hx y hy hxy =>
    sub_le_sub_right (hm hx hy hxy) _
  have h0 : h 0 = 0 := by simp [hh]
  have hI : ∀ (N : ℕ) {u v : ℝ}, 0 ≤ u → u ≤ v → v ≤ δ →
      IntervalIntegrable (fun x => h x * dirichletKernel N x) volume u v := by
    intro N u v hu huv hv
    exact ((hcont.mono (Set.Icc_subset_Icc hu hv)).mul
      (continuous_dirichletKernel N).continuousOn).intervalIntegrable_of_Icc huv
  have key : Tendsto (fun N : ℕ ↦ ∫ x in (0 : ℝ)..δ, h x * dirichletKernel N x) atTop (𝓝 0) := by
    obtain ⟨C, hC⟩ := exists_abs_integral_dirichletKernel_le
    have hCpos : 0 < max C 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
    rw [Metric.tendsto_atTop]
    intro ε hε
    have hε1 : 0 < ε / (4 * max C 1) := by positivity
    obtain ⟨δ', hpos, hδ''⟩ := Metric.continuousWithinAt_iff.1 (hcont 0 ⟨le_rfl, hδ.le⟩)
      (ε / (4 * max C 1)) hε1
    set η := min (δ' / 2) δ with hη
    have hη0 : 0 < η := lt_min (by linarith) hδ
    have hηδ : η ≤ δ := min_le_right _ _
    have hηm : |h η| < ε / (4 * max C 1) := by
      have := hδ'' (x := η) ⟨hη0.le, hηδ⟩ (by
        rw [Real.dist_eq, sub_zero, abs_of_pos hη0]
        exact lt_of_le_of_lt (min_le_left _ _) (by linarith))
      rwa [Real.dist_eq, h0, sub_zero] at this
    have hsmall : ∀ N : ℕ, |∫ x in (0 : ℝ)..η, h x * dirichletKernel N x| ≤ ε / 4 := by
      intro N
      have := abs_intervalIntegral_mul_le_of_monotoneOn (h := h) (φ := dirichletKernel N)
        (a := 0) (b := η) (M := max C 1) hη0.le (hmono.mono (Set.Icc_subset_Icc le_rfl hηδ))
        (continuous_dirichletKernel N).continuousOn (fun c hc =>
          (hC N c η hc.1 hc.2 (hηδ.trans hδ')).trans (le_max_left _ _))
      refine this.trans ?_
      rw [h0, abs_zero, zero_add, sub_zero]
      calc max C 1 * h η ≤ max C 1 * (ε / (4 * max C 1)) :=
            mul_le_mul_of_nonneg_left ((le_abs_self _).trans hηm.le) hCpos.le
        _ = ε / 4 := by field_simp
    have htail := tendsto_integral_mul_dirichletKernel_of_forall_int_notMem (g := h) (a := η)
      (b := δ) hηδ (hcont.mono (Set.Icc_subset_Icc hη0.le le_rfl))
      (no_int_of_pos_le_half hη0 hδ')
    obtain ⟨N0, hN0⟩ := Metric.tendsto_atTop.1 htail (ε / 2) (by positivity)
    refine ⟨N0, fun N hN => ?_⟩
    have hsplit := intervalIntegral.integral_add_adjacent_intervals (hI N le_rfl hη0.le hηδ)
      (hI N hη0.le hηδ le_rfl)
    rw [← hsplit, Real.dist_eq, sub_zero]
    have h2 := hN0 N hN
    rw [Real.dist_eq, sub_zero] at h2
    calc _ ≤ |∫ x in (0 : ℝ)..η, h x * dirichletKernel N x| +
          |∫ x in η..δ, h x * dirichletKernel N x| := abs_add_le _ _
      _ < ε := by linarith [hsmall N]
  have hLB := tendsto_integral_dirichletKernel_zero_left_aux hδ hδ'
  have := (hLB.const_mul (f 0)).add key
  rw [add_zero] at this
  have e : f 0 * (1 / 2) = f 0 / 2 := by ring
  rw [e] at this
  refine this.congr (fun N => ?_)
  have hc := continuous_dirichletKernel N
  rw [← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_add (f := fun x => f 0 * dirichletKernel N x)
      (g := fun x => h x * dirichletKernel N x)
      ((continuous_const.mul hc).intervalIntegrable _ _) (hI N le_rfl hδ.le le_rfl)]
  refine intervalIntegral.integral_congr (fun x _ => ?_)
  simp only [hh]; ring

theorem tendsto_integral_mul_dirichletKernel_zero_left_of_antitoneOn {f : ℝ → ℝ} {δ : ℝ}
    (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) (hf : ContinuousOn f (Set.Icc 0 δ))
    (hm : AntitoneOn f (Set.Icc 0 δ)) :
    Tendsto (fun N : ℕ ↦ ∫ x in (0 : ℝ)..δ, f x * dirichletKernel N x) atTop
      (𝓝 (f 0 / 2)) := by
  have h := (tendsto_integral_mul_dirichletKernel_zero_left (f := fun x => -f x) hδ hδ' hf.neg
    (fun x hx y hy hxy => neg_le_neg (hm hx hy hxy))).neg
  simp only [neg_mul, intervalIntegral.integral_neg, neg_neg] at h
  convert h using 2
  ring

/-- The limit statement for `∫_a^b f D_N`. -/
def DKLimit (f : ℝ → ℝ) (a b : ℝ) : Prop :=
  Tendsto (fun N : ℕ ↦ ∫ x in a..b, f x * dirichletKernel N x) atTop (𝓝 (halvedSum f a b))

theorem DKLimit.add {f : ℝ → ℝ} {a b c : ℝ} (hac : a < c) (hcb : c < b)
    (hf : ContinuousOn f (Set.Icc a b)) (h1 : DKLimit f a c) (h2 : DKLimit f c b) :
    DKLimit f a b := by
  unfold DKLimit at *
  rw [halvedSum_add hac hcb]
  refine (h1.add h2).congr fun N => ?_
  have i1 : IntervalIntegrable (fun x => f x * dirichletKernel N x) volume a c :=
    ((hf.mono (Set.Icc_subset_Icc le_rfl hcb.le)).mul
      (continuous_dirichletKernel N).continuousOn).intervalIntegrable_of_Icc hac.le
  have i2 : IntervalIntegrable (fun x => f x * dirichletKernel N x) volume c b :=
    ((hf.mono (Set.Icc_subset_Icc hac.le le_rfl)).mul
      (continuous_dirichletKernel N).continuousOn).intervalIntegrable_of_Icc hcb.le
  exact intervalIntegral.integral_add_adjacent_intervals i1 i2

theorem halvedSum_eq_zero_of_no_int {f : ℝ → ℝ} {a b : ℝ}
    (h : ∀ n : ℤ, (n : ℝ) ∉ Set.Icc a b) : halvedSum f a b = 0 := by
  unfold halvedSum
  refine Finset.sum_eq_zero fun n hn => ?_
  rw [Finset.mem_Icc] at hn
  exact absurd ⟨Int.ceil_le.mp hn.1, Int.le_floor.mp hn.2⟩ (h n)

theorem halvedSum_left_int {f : ℝ → ℝ} {b : ℝ} (m : ℤ) (hb : (m : ℝ) < b) (hb' : b < m + 1) :
    halvedSum f m b = f m / 2 := by
  have hfl : ⌊b⌋ = m := Int.floor_eq_iff.2 ⟨hb.le, hb'⟩
  unfold halvedSum
  rw [Int.ceil_intCast, hfl]
  simp [div_eq_inv_mul]

theorem halvedSum_right_int {f : ℝ → ℝ} {a : ℝ} (m : ℤ) (ha : (m : ℝ) - 1 < a) (ha' : a < m) :
    halvedSum f a m = f m / 2 := by
  have hce : ⌈a⌉ = m := Int.ceil_eq_iff.2 ⟨ha, ha'.le⟩
  unfold halvedSum
  rw [Int.floor_intCast, hce]
  simp [div_eq_inv_mul]

theorem DKLimit_noint {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hf : ContinuousOn f (Set.Icc a b))
    (h : ∀ n : ℤ, (n : ℝ) ∉ Set.Icc a b) : DKLimit f a b := by
  unfold DKLimit
  rw [halvedSum_eq_zero_of_no_int h]
  exact tendsto_integral_mul_dirichletKernel_of_forall_int_notMem hab hf h

theorem DKLimit_left_int {f : ℝ → ℝ} {b : ℝ} (m : ℤ) (hb : (m : ℝ) < b) (hb' : b ≤ m + 1 / 2)
    (hf : ContinuousOn f (Set.Icc m b)) (hm : MonotoneOn f (Set.Icc m b)) : DKLimit f m b := by
  have hδ : 0 < b - m := sub_pos.2 hb
  have hsub : ∀ x ∈ Set.Icc (0 : ℝ) (b - m), x + m ∈ Set.Icc (m : ℝ) b := fun x hx =>
    ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have key := tendsto_integral_mul_dirichletKernel_zero_left (f := fun x => f (x + m)) hδ
    (by linarith) (hf.comp (by fun_prop) hsub)
    (fun x hx y hy hxy => hm (hsub x hx) (hsub y hy) (by linarith))
  unfold DKLimit
  rw [halvedSum_left_int m hb (by linarith)]
  simp only [zero_add] at key
  refine key.congr (fun N => ?_)
  have := intervalIntegral.integral_comp_add_right (fun x => f x * dirichletKernel N x) (m : ℝ)
    (a := 0) (b := b - m)
  simp only [zero_add, sub_add_cancel] at this
  refine (intervalIntegral.integral_congr fun x _ => ?_).trans this
  show f (x + m) * dirichletKernel N x = f (x + m) * dirichletKernel N (x + m)
  rw [dirichletKernel_add_int]

theorem DKLimit_right_int {f : ℝ → ℝ} {a : ℝ} (m : ℤ) (ha : (m : ℝ) - 1 / 2 ≤ a) (ha' : a < m)
    (hf : ContinuousOn f (Set.Icc a m)) (hm : MonotoneOn f (Set.Icc a m)) : DKLimit f a m := by
  have hδ : 0 < (m : ℝ) - a := sub_pos.2 ha'
  have hsub : ∀ x ∈ Set.Icc (0 : ℝ) (m - a), (m : ℝ) - x ∈ Set.Icc a (m : ℝ) := fun x hx =>
    ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have key := tendsto_integral_mul_dirichletKernel_zero_left_of_antitoneOn
    (f := fun x => f (m - x)) hδ (by linarith) (hf.comp (by fun_prop) hsub)
    (fun x hx y hy hxy => hm (hsub y hy) (hsub x hx) (by linarith))
  unfold DKLimit
  rw [halvedSum_right_int m (by linarith) ha']
  simp only [sub_zero] at key
  refine key.congr (fun N => ?_)
  have := intervalIntegral.integral_comp_sub_left (fun x => f x * dirichletKernel N x) (m : ℝ)
    (a := 0) (b := m - a)
  simp only [sub_zero, sub_sub_cancel] at this
  refine (intervalIntegral.integral_congr fun x _ => ?_).trans this
  show f (m - x) * dirichletKernel N x = f (m - x) * dirichletKernel N (m - x)
  rw [sub_eq_neg_add, dirichletKernel_add_int, dirichletKernel_neg]

theorem DKLimit_small {f : ℝ → ℝ} {a b : ℝ} (hab : a < b) (hf : ContinuousOn f (Set.Icc a b))
    (hm : MonotoneOn f (Set.Icc a b)) (hno : ∀ k : ℤ, ¬ (a < (k : ℝ) / 2 ∧ (k : ℝ) / 2 < b)) :
    DKLimit f a b := by
  by_cases hex : ∃ m : ℤ, (m : ℝ) ∈ Set.Icc a b
  · obtain ⟨m, hm1, hm2⟩ := hex
    rcases hm1.eq_or_lt with h1 | h1
    · subst h1
      refine DKLimit_left_int m hab ?_ hf hm
      by_contra hcon
      push Not at hcon
      exact hno (2 * m + 1) ⟨by push_cast; linarith, by push_cast; linarith⟩
    · rcases hm2.eq_or_lt with h2 | h2
      · subst h2
        refine DKLimit_right_int m ?_ h1 hf hm
        by_contra hcon
        push Not at hcon
        exact hno (2 * m - 1) ⟨by push_cast; linarith, by push_cast; linarith⟩
      · exact absurd ⟨by push_cast; linarith, by push_cast; linarith⟩ (hno (2 * m))
  · exact DKLimit_noint hab.le hf (fun n hn => hex ⟨n, hn⟩)

theorem DKLimit_of_monotoneOn_aux {f : ℝ → ℝ} :
    ∀ n : ℕ, ∀ {a b : ℝ}, a < b → ⌈2 * b⌉ - ⌊2 * a⌋ ≤ n → ContinuousOn f (Set.Icc a b) →
      MonotoneOn f (Set.Icc a b) → DKLimit f a b := by
  intro n
  induction n with
  | zero =>
    intro a b hab hn
    have h1 : (⌊2 * a⌋ : ℝ) ≤ 2 * a := Int.floor_le _
    have h2 : 2 * b ≤ (⌈2 * b⌉ : ℝ) := Int.le_ceil _
    have : ⌊2 * a⌋ < ⌈2 * b⌉ := by exact_mod_cast (by linarith : (⌊2 * a⌋ : ℝ) < ⌈2 * b⌉)
    push_cast at hn
    omega
  | succ n ih =>
    intro a b hab hn hf hm
    by_cases hk : ∃ k : ℤ, a < (k : ℝ) / 2 ∧ (k : ℝ) / 2 < b
    · obtain ⟨k, hk1, hk2⟩ := hk
      have h1 : (⌊2 * a⌋ : ℝ) ≤ 2 * a := Int.floor_le _
      have h2 : 2 * b ≤ (⌈2 * b⌉ : ℝ) := Int.le_ceil _
      have h3 : ⌊2 * a⌋ < k := by exact_mod_cast (by linarith : (⌊2 * a⌋ : ℝ) < k)
      have h4 : k < ⌈2 * b⌉ := by exact_mod_cast (by linarith : (k : ℝ) < ⌈2 * b⌉)
      have e : 2 * ((k : ℝ) / 2) = k := by ring
      refine DKLimit.add hk1 hk2 hf ?_ ?_
      · refine ih hk1 ?_ (hf.mono (Set.Icc_subset_Icc le_rfl hk2.le))
          (hm.mono (Set.Icc_subset_Icc le_rfl hk2.le))
        rw [e, Int.ceil_intCast]; push_cast at hn ⊢; omega
      · refine ih hk2 ?_ (hf.mono (Set.Icc_subset_Icc hk1.le le_rfl))
          (hm.mono (Set.Icc_subset_Icc hk1.le le_rfl))
        rw [e, Int.floor_intCast]; push_cast at hn ⊢; omega
    · push Not at hk
      exact DKLimit_small hab hf hm (fun k hk' => absurd hk'.2 (not_lt.mpr (hk k hk'.1)))

/-- **The monotone case**: for `a < b` and `f` continuous and monotone on `[a, b]`,
`∫_a^b f D_N → ∑'_{a ≤ n ≤ b} f(n)`. -/
theorem tendsto_integral_mul_dirichletKernel_of_monotoneOn {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Set.Icc a b)) (hm : MonotoneOn f (Set.Icc a b)) :
    Tendsto (fun N : ℕ ↦ ∫ x in a..b, f x * dirichletKernel N x) atTop
      (𝓝 (halvedSum f a b)) := by
  have h1 : (⌊2 * a⌋ : ℝ) ≤ 2 * a := Int.floor_le _
  have h2 : 2 * b ≤ (⌈2 * b⌉ : ℝ) := Int.le_ceil _
  have : ⌊2 * a⌋ < ⌈2 * b⌉ := by exact_mod_cast (by linarith : (⌊2 * a⌋ : ℝ) < ⌈2 * b⌉)
  exact DKLimit_of_monotoneOn_aux (⌈2 * b⌉ - ⌊2 * a⌋).toNat hab (Int.self_le_toNat _) hf hm

theorem halvedSum_neg (f : ℝ → ℝ) (a b : ℝ) :
    halvedSum (fun x => -f x) a b = -halvedSum f a b := by
  unfold halvedSum
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun n _ => by ring

theorem DKLimit_of_mono_or_anti {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Set.Icc a b))
    (hm : MonotoneOn f (Set.Icc a b) ∨ AntitoneOn f (Set.Icc a b)) : DKLimit f a b := by
  rcases hm with hm | hm
  · exact tendsto_integral_mul_dirichletKernel_of_monotoneOn hab hf hm
  · have h : DKLimit (fun x => -f x) a b := tendsto_integral_mul_dirichletKernel_of_monotoneOn hab
      hf.neg (fun x hx y hy hxy => neg_le_neg (hm hx hy hxy))
    unfold DKLimit at h ⊢
    rw [halvedSum_neg] at h
    have := h.neg
    simp only [neg_mul, intervalIntegral.integral_neg, neg_neg] at this
    exact this

theorem DKLimit_partition {f : ℝ → ℝ} : ∀ (k : ℕ) (x : Fin (k + 2) → ℝ), StrictMono x →
    ContinuousOn f (Set.Icc (x 0) (x (Fin.last (k + 1)))) →
    (∀ i : Fin (k + 1), MonotoneOn f (Set.Icc (x i.castSucc) (x i.succ)) ∨
      AntitoneOn f (Set.Icc (x i.castSucc) (x i.succ))) →
    DKLimit f (x 0) (x (Fin.last (k + 1))) := by
  intro k
  induction k with
  | zero =>
    intro x hx hf hp
    exact DKLimit_of_mono_or_anti (hx (by decide : (0 : Fin 2) < Fin.last 1)) hf (hp 0)
  | succ k ih =>
    intro x hx hf hp
    have hx0 : ∀ i, x 0 ≤ x i := fun i => hx.monotone (Fin.zero_le i)
    have hxl : ∀ i, x i ≤ x (Fin.last (k + 2)) := fun i => hx.monotone (Fin.le_last i)
    have hac : x 0 < x (Fin.succ (0 : Fin (k + 2))) := hx (Fin.succ_pos 0)
    have hcb : x (Fin.succ (0 : Fin (k + 2))) < x (Fin.last (k + 2)) :=
      hx (by rw [Fin.lt_def]; simp)
    refine DKLimit.add hac hcb hf ?_ ?_
    · have := hp 0
      simp only [Fin.castSucc_zero] at this
      exact DKLimit_of_mono_or_anti hac
        (hf.mono (Set.Icc_subset_Icc le_rfl (hxl _))) this
    · have := ih (fun i => x i.succ) (hx.comp (Fin.strictMono_succ))
        (by
          rw [Fin.succ_last]
          exact hf.mono (Set.Icc_subset_Icc (hx0 _) le_rfl))
        (fun i => by
          show MonotoneOn f (Set.Icc (x i.castSucc.succ) (x i.succ.succ)) ∨
            AntitoneOn f (Set.Icc (x i.castSucc.succ) (x i.succ.succ))
          rw [Fin.succ_castSucc]
          exact hp i.succ)
      simpa [Fin.succ_last] using this

/-- **Davenport, Chapter 2 (Poisson summation)**: for `A < B` and `f` continuous and piecewise
monotone on `[A, B]`, `∑'_{A ≤ n ≤ B} f(n) = ∑_ν ∫_A^B f(x) e(νx) dx`, the sum over `ν` taken
as the limit of the symmetric partial sums `|ν| ≤ N`, the terms `n = A`, `n = B` halved. -/
@[kb "davenport1980" "Ch 2, p. 14"]
theorem poisson_summation_piecewise_monotone {f : ℝ → ℝ} {A B : ℝ} (hAB : A < B)
    (hf : ContinuousOn f (Set.Icc A B)) (hpm : PiecewiseMonotoneOn f A B) :
    Tendsto (fun N : ℕ ↦ ∑ ν ∈ Finset.Icc (-(N : ℤ)) N,
        ∫ x in A..B, (f x : ℂ) * Complex.exp (2 * π * Complex.I * ν * x)) atTop
      (𝓝 (halvedSum f A B : ℂ)) := by
  obtain ⟨k, x, hx0, hxl, hx, hp⟩ := hpm
  have hreal : DKLimit f A B := by
    cases k with
    | zero =>
      exfalso
      have : x 0 = x (Fin.last 0) := rfl
      rw [hx0, hxl] at this
      exact hAB.ne this
    | succ k =>
      have := DKLimit_partition (f := f) k x hx (by rw [hx0, hxl]; exact hf) hp
      rwa [hx0, hxl] at this
  have h := (Complex.continuous_ofReal.tendsto _).comp hreal
  refine h.congr (fun N => ?_)
  simp only [Function.comp_apply]
  have hint : ∀ ν : ℤ, IntervalIntegrable
      (fun x : ℝ => (f x : ℂ) * Complex.exp (2 * π * Complex.I * ν * x)) volume A B := fun ν =>
    (Complex.continuous_ofReal.comp_continuousOn hf |>.mul
      (by fun_prop : Continuous fun x : ℝ => Complex.exp (2 * π * Complex.I * ν * x)).continuousOn
      ).intervalIntegrable_of_Icc hAB.le
  rw [← intervalIntegral.integral_finsetSum (fun ν _ => hint ν)]
  rw [← intervalIntegral.integral_ofReal]
  refine intervalIntegral.integral_congr (fun x _ => ?_)
  rw [← Finset.mul_sum, sum_exp_eq_dirichletKernel]
  push_cast; ring

end NTKB.Davenport.Poisson
