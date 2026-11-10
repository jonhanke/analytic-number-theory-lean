/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Port.DirichletCharacterPartialSum
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.Analysis.Complex.ExponentialBounds
import NTKB.Attr

/-!
# Sums involving Dirichlet characters (Apostol, Chapter 6, §6.9)

* Theorem 6.17: for a nonprincipal character `χ` mod `k` and `f ≥ 0` decreasing on `[x₀, ∞)`,
  `∑_{x < n ≤ y} χ(n) f(n) = O(f(x))` (explicitly `≤ 2k f(x)`); if moreover `f → 0`, the series
  `∑ χ(n) f(n)` converges and `∑_{n ≤ x} χ(n) f(n) = ∑_{n ≥ 1} χ(n) f(n) + O(f(x))`.
  Apostol assumes a continuous negative derivative and uses Abel's identity; here `f` is only
  assumed decreasing, and discrete partial summation replaces the integral.
* Theorem 6.18: the three cases `f(x) = 1/x`, `(log x)/x`, `1/√x`, which define `L(1, χ)`,
  `L'(1, χ)` (Apostol's notation: `L'(1, χ) = -∑ χ(n) log n / n`) and `L(1/2, χ)` as sums of
  conditionally convergent series (`NTKB.Apostol.LOne`, `LOneDeriv`, `LHalf`).

The series sum is `NTKB.Apostol.seriesSum c = lim_{N → ∞} ∑_{n ≤ N} c(n)` (a `limUnder`; the
theorems prove that the limit exists).
-/

open Finset Filter Topology

namespace NTKB.Apostol

variable {k : ℕ} [NeZero k]

/-- The sum of a (possibly only conditionally) convergent series `∑_{n ≥ 1} c(n)`, as the limit of
its partial sums. -/
noncomputable def seriesSum (c : ℕ → ℂ) : ℂ :=
  limUnder atTop fun N : ℕ ↦ ∑ n ∈ Ioc 0 N, c n

/-- Discrete partial summation: with `S(m) = ∑_{n ≤ m} c(n)`,
`∑_{a < n ≤ b} c(n) f(n) = S(b) f(b+1) - S(a) f(a+1) + ∑_{a < n ≤ b} S(n) (f(n) - f(n+1))`. -/
theorem sum_Ioc_mul_eq_abel (c : ℕ → ℂ) (f : ℕ → ℝ) {a b : ℕ} (hab : a ≤ b) :
    ∑ n ∈ Ioc a b, c n * (f n : ℂ) =
      (∑ n ∈ Ioc 0 b, c n) * (f (b + 1) : ℂ) - (∑ n ∈ Ioc 0 a, c n) * (f (a + 1) : ℂ) +
        ∑ n ∈ Ioc a b, (∑ m ∈ Ioc 0 n, c m) * ((f n - f (n + 1) : ℝ) : ℂ) := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    rw [sum_Ioc_succ_top hab, ih, sum_Ioc_succ_top hab, sum_Ioc_succ_top (Nat.zero_le _)]
    push_cast
    ring

theorem sum_Ioc_sub_succ (f : ℕ → ℝ) {a b : ℕ} (hab : a ≤ b) :
    ∑ n ∈ Ioc a b, (f n - f (n + 1)) = f (a + 1) - f (b + 1) := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih => rw [sum_Ioc_succ_top hab, ih]; ring

/-- If the partial sums of `c` are bounded by `K` and `f ≥ 0` decreases on `n ≥ a + 1`, then
`‖∑_{a < n ≤ b} c(n) f(n)‖ ≤ 2 K f(a + 1)`. -/
theorem norm_sum_Ioc_mul_le (c : ℕ → ℂ) {K : ℝ} (hK : ∀ m, ‖∑ n ∈ Ioc 0 m, c n‖ ≤ K)
    (f : ℕ → ℝ) {a b : ℕ} (hab : a ≤ b) (hf : ∀ n, a + 1 ≤ n → f (n + 1) ≤ f n)
    (hf0 : ∀ n, a + 1 ≤ n → 0 ≤ f n) :
    ‖∑ n ∈ Ioc a b, c n * (f n : ℂ)‖ ≤ 2 * K * f (a + 1) := by
  rw [sum_Ioc_mul_eq_abel c f hab]
  have hfb : 0 ≤ f (b + 1) := hf0 _ (by omega)
  have hfa : 0 ≤ f (a + 1) := hf0 _ le_rfl
  have hfab : f (b + 1) ≤ f (a + 1) := by
    have := sum_Ioc_sub_succ f hab
    have : 0 ≤ ∑ n ∈ Ioc a b, (f n - f (n + 1)) :=
      sum_nonneg fun n hn ↦ sub_nonneg.2 (hf n (by simp at hn; omega))
    linarith
  have h3 : ‖∑ n ∈ Ioc a b, (∑ m ∈ Ioc 0 n, c m) * ((f n - f (n + 1) : ℝ) : ℂ)‖ ≤
      K * (f (a + 1) - f (b + 1)) := by
    rw [← sum_Ioc_sub_succ f hab, mul_sum]
    refine (norm_sum_le _ _).trans (sum_le_sum fun n hn ↦ ?_)
    have hn : a + 1 ≤ n := by simp at hn; omega
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 (hf n hn))]
    exact mul_le_mul_of_nonneg_right (hK n) (sub_nonneg.2 (hf n hn))
  have h1 : ‖(∑ n ∈ Ioc 0 b, c n) * (f (b + 1) : ℂ)‖ ≤ K * f (b + 1) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hfb]
    exact mul_le_mul_of_nonneg_right (hK b) hfb
  have h2 : ‖(∑ n ∈ Ioc 0 a, c n) * (f (a + 1) : ℂ)‖ ≤ K * f (a + 1) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hfa]
    exact mul_le_mul_of_nonneg_right (hK a) hfa
  calc _ ≤ ‖(∑ n ∈ Ioc 0 b, c n) * (f (b + 1) : ℂ) - (∑ n ∈ Ioc 0 a, c n) * (f (a + 1) : ℂ)‖ +
        ‖∑ n ∈ Ioc a b, (∑ m ∈ Ioc 0 n, c m) * ((f n - f (n + 1) : ℝ) : ℂ)‖ := norm_add_le _ _
    _ ≤ (K * f (b + 1) + K * f (a + 1)) + K * (f (a + 1) - f (b + 1)) :=
        add_le_add ((norm_sub_le _ _).trans (add_le_add h1 h2)) h3
    _ = 2 * K * f (a + 1) := by ring

/-- The bound of Theorem 6.17 for `⌊x⌋ < n ≤ b`, any `b ≥ ⌊x⌋`. -/
theorem norm_sum_Ioc_floor_char_mul_le' {χ : DirichletCharacter ℂ k} (hχ : χ ≠ 1) {f : ℝ → ℝ}
    {x₀ : ℝ} (hf : AntitoneOn f (Set.Ici x₀)) (hf0 : ∀ t, x₀ ≤ t → 0 ≤ f t) {x : ℝ}
    (hx : x₀ ≤ x) {b : ℕ} (hb : ⌊x⌋₊ ≤ b) :
    ‖∑ n ∈ Ioc ⌊x⌋₊ b, χ n * (f n : ℂ)‖ ≤ 2 * k * f x := by
  have h1 := Nat.lt_floor_add_one x
  have hn : ∀ n : ℕ, ⌊x⌋₊ + 1 ≤ n → x₀ ≤ n := fun n hn ↦ by
    have h2 : ((⌊x⌋₊ + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
    push_cast at h2; linarith
  have := norm_sum_Ioc_mul_le (fun n ↦ χ n) (K := k)
    (NTKB.DirichletCharacter.norm_sum_Ioc_le_level χ hχ) (fun n ↦ f n) hb
    (fun n h ↦ hf (hn n h) (by have := hn n h; simp only [Set.mem_Ici]; push_cast; linarith)
      (by push_cast; linarith))
    (fun n h ↦ hf0 _ (hn n h))
  refine this.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  exact hf hx (hn _ le_rfl) (by push_cast; linarith)

/-- **Apostol, Theorem 6.17**, first part: for a nonprincipal `χ` mod `k` and `f ≥ 0` decreasing
on `[x₀, ∞)`, `‖∑_{x < n ≤ y} χ(n) f(n)‖ ≤ 2k f(x)` for `x₀ ≤ x ≤ y`. -/
@[kb "apostol1976" "Thm 6.17, p. 140"]
theorem norm_sum_Ioc_floor_char_mul_le {χ : DirichletCharacter ℂ k} (hχ : χ ≠ 1) {f : ℝ → ℝ}
    {x₀ : ℝ} (hf : AntitoneOn f (Set.Ici x₀)) (hf0 : ∀ t, x₀ ≤ t → 0 ≤ f t) {x y : ℝ}
    (hx : x₀ ≤ x) (hxy : x ≤ y) :
    ‖∑ n ∈ Ioc ⌊x⌋₊ ⌊y⌋₊, χ n * (f n : ℂ)‖ ≤ 2 * k * f x :=
  norm_sum_Ioc_floor_char_mul_le' hχ hf hf0 hx (Nat.floor_le_floor hxy)

/-- **Apostol, Theorem 6.17**, second part: if moreover `f → 0`, the series `∑ χ(n) f(n)`
converges, and `‖∑_{n ≤ x} χ(n) f(n) - ∑_{n ≥ 1} χ(n) f(n)‖ ≤ 2k f(x)` for `x ≥ x₀`. -/
@[kb "apostol1976" "Thm 6.17, p. 140"]
theorem tendsto_sum_char_mul_and_norm_sub_le {χ : DirichletCharacter ℂ k} (hχ : χ ≠ 1)
    {f : ℝ → ℝ} {x₀ : ℝ} (hf : AntitoneOn f (Set.Ici x₀)) (hf0 : ∀ t, x₀ ≤ t → 0 ≤ f t)
    (hlim : Tendsto f atTop (𝓝 0)) :
    Tendsto (fun N : ℕ ↦ ∑ n ∈ Ioc 0 N, χ n * (f n : ℂ)) atTop
        (𝓝 (seriesSum fun n ↦ χ n * (f n : ℂ))) ∧
      ∀ x, x₀ ≤ x → ‖∑ n ∈ Ioc 0 ⌊x⌋₊, χ n * (f n : ℂ) - seriesSum (fun n ↦ χ n * (f n : ℂ))‖
        ≤ 2 * k * f x := by
  set P : ℕ → ℂ := fun N ↦ ∑ n ∈ Ioc 0 N, χ n * (f n : ℂ) with hP
  -- `‖P M - P ⌊x⌋‖ ≤ 2k f(x)` for `x₀ ≤ x`, `⌊x⌋ ≤ M`
  have hdiff : ∀ x : ℝ, x₀ ≤ x → ∀ M : ℕ, ⌊x⌋₊ ≤ M → ‖P M - P ⌊x⌋₊‖ ≤ 2 * k * f x := by
    intro x hx M hM
    have := norm_sum_Ioc_floor_char_mul_le' hχ hf hf0 hx hM
    rw [hP]; dsimp only
    rwa [← sum_Ioc_consecutive _ (Nat.zero_le _) hM, add_sub_cancel_left]
  have hcauchy : CauchySeq P := by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    have hev : ∀ᶠ t in atTop, 2 * k * f t < ε := by
      have h := hlim.const_mul (2 * (k : ℝ))
      rw [mul_zero] at h
      exact h.eventually (gt_mem_nhds hε)
    obtain ⟨T, hT⟩ := eventually_atTop.1 hev
    obtain ⟨N, hN⟩ := exists_nat_ge (max T x₀)
    refine ⟨N, fun M hM ↦ ?_⟩
    rw [dist_eq_norm]
    have := hdiff N (le_trans (le_max_right _ _) hN) M (by rw [Nat.floor_natCast]; exact hM)
    rw [Nat.floor_natCast] at this
    exact this.trans_lt (hT N (le_trans (le_max_left _ _) hN))
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hS : seriesSum (fun n ↦ χ n * (f n : ℂ)) = L := hL.limUnder_eq
  refine ⟨hS ▸ hL, fun x hx ↦ ?_⟩
  rw [hS, norm_sub_rev]
  have hlim' : Tendsto (fun M ↦ ‖P M - P ⌊x⌋₊‖) atTop (𝓝 ‖L - P ⌊x⌋₊‖) :=
    (hL.sub_const _).norm
  refine le_of_tendsto hlim' ?_
  filter_upwards [eventually_ge_atTop ⌊x⌋₊] with M hM
  exact hdiff x hx M hM

/-! ## Theorem 6.18 -/

theorem tendsto_log_div_self : Tendsto (fun t : ℝ ↦ Real.log t / t) atTop (𝓝 0) := by
  simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero

/-- `L(1, χ) = ∑_{n ≥ 1} χ(n)/n` (Apostol, §6.10 and §7.3). -/
noncomputable def LOne (χ : DirichletCharacter ℂ k) : ℂ :=
  seriesSum fun n ↦ χ n * ((1 / n : ℝ) : ℂ)

/-- `L'(1, χ) = -∑_{n ≥ 1} χ(n) log n / n` (Apostol, §7.3). -/
noncomputable def LOneDeriv (χ : DirichletCharacter ℂ k) : ℂ :=
  -seriesSum fun n ↦ χ n * ((Real.log n / n : ℝ) : ℂ)

/-- `L(1/2, χ) = ∑_{n ≥ 1} χ(n)/√n` (Apostol, proof of Theorem 6.20). -/
noncomputable def LHalf (χ : DirichletCharacter ℂ k) : ℂ :=
  seriesSum fun n ↦ χ n * ((1 / √(n : ℝ) : ℝ) : ℂ)

theorem antitoneOn_one_div : AntitoneOn (fun t : ℝ ↦ 1 / t) (Set.Ici 1) := by
  intro a ha b hb hab
  simp only [Set.mem_Ici] at ha hb
  exact one_div_le_one_div_of_le (by linarith) hab

theorem antitoneOn_one_div_sqrt : AntitoneOn (fun t : ℝ ↦ 1 / √t) (Set.Ici 1) := by
  intro a ha b hb hab
  simp only [Set.mem_Ici] at ha hb
  exact one_div_le_one_div_of_le (Real.sqrt_pos.2 (by linarith)) (Real.sqrt_le_sqrt hab)

theorem antitoneOn_log_div : AntitoneOn (fun t : ℝ ↦ Real.log t / t) (Set.Ici 3) := by
  intro a ha b hb hab
  simp only [Set.mem_Ici] at ha hb
  have he : Real.exp 1 ≤ 3 := Real.exp_one_lt_three.le
  exact Real.log_div_self_antitoneOn (by simp only [Set.mem_Ici]; linarith)
    (by simp only [Set.mem_Ici]; linarith) hab

/-- **Apostol, Theorem 6.18** (9): `∑_{n ≤ x} χ(n)/n = L(1, χ) + O(1/x)` for `x ≥ 1`. -/
@[kb "apostol1976" "Thm 6.18, p. 141"]
theorem norm_sum_char_div_sub_LOne_le {χ : DirichletCharacter ℂ k} (hχ : χ ≠ 1) {x : ℝ}
    (hx : 1 ≤ x) :
    ‖∑ n ∈ Ioc 0 ⌊x⌋₊, χ n * ((1 / n : ℝ) : ℂ) - LOne χ‖ ≤ 2 * k * (1 / x) :=
  (tendsto_sum_char_mul_and_norm_sub_le hχ antitoneOn_one_div
    (fun t ht ↦ by positivity)
    (by simpa using tendsto_inv_atTop_zero)).2 x hx

theorem tendsto_LOne {χ : DirichletCharacter ℂ k} (hχ : χ ≠ 1) :
    Tendsto (fun N : ℕ ↦ ∑ n ∈ Ioc 0 N, χ n * ((1 / n : ℝ) : ℂ)) atTop (𝓝 (LOne χ)) :=
  (tendsto_sum_char_mul_and_norm_sub_le hχ antitoneOn_one_div
    (fun t ht ↦ by positivity)
    (by simpa using tendsto_inv_atTop_zero)).1

/-- **Apostol, Theorem 6.18** (10): `∑_{n ≤ x} χ(n) log n / n = -L'(1, χ) + O(log x / x)`, for
`x ≥ 3` (the book says `x ≥ 1`, but at `x = 1` the error term vanishes while the left side is `0`
and `L'(1, χ)` need not be). -/
@[kb "apostol1976" "Thm 6.18, p. 141"]
theorem norm_sum_char_log_div_add_LOneDeriv_le {χ : DirichletCharacter ℂ k} (hχ : χ ≠ 1)
    {x : ℝ} (hx : 3 ≤ x) :
    ‖∑ n ∈ Ioc 0 ⌊x⌋₊, χ n * ((Real.log n / n : ℝ) : ℂ) + LOneDeriv χ‖ ≤
      2 * k * (Real.log x / x) := by
  have h := (tendsto_sum_char_mul_and_norm_sub_le hχ antitoneOn_log_div
    (fun t ht ↦ div_nonneg (Real.log_nonneg (by linarith)) (by linarith))
    tendsto_log_div_self).2 x hx
  show ‖_ + -(seriesSum _)‖ ≤ _
  rwa [← sub_eq_add_neg]

theorem tendsto_LOneDeriv {χ : DirichletCharacter ℂ k} (hχ : χ ≠ 1) :
    Tendsto (fun N : ℕ ↦ ∑ n ∈ Ioc 0 N, χ n * ((Real.log n / n : ℝ) : ℂ)) atTop
      (𝓝 (-LOneDeriv χ)) := by
  rw [LOneDeriv, neg_neg]
  exact (tendsto_sum_char_mul_and_norm_sub_le hχ antitoneOn_log_div
    (fun t ht ↦ div_nonneg (Real.log_nonneg (by linarith)) (by linarith))
    tendsto_log_div_self).1

/-- **Apostol, Theorem 6.18** (11): `∑_{n ≤ x} χ(n)/√n = L(1/2, χ) + O(1/√x)` for `x ≥ 1`. -/
@[kb "apostol1976" "Thm 6.18, p. 141"]
theorem norm_sum_char_div_sqrt_sub_LHalf_le {χ : DirichletCharacter ℂ k} (hχ : χ ≠ 1) {x : ℝ}
    (hx : 1 ≤ x) :
    ‖∑ n ∈ Ioc 0 ⌊x⌋₊, χ n * ((1 / √(n : ℝ) : ℝ) : ℂ) - LHalf χ‖ ≤ 2 * k * (1 / √x) := by
  have hlim : Tendsto (fun t : ℝ ↦ 1 / √t) atTop (𝓝 0) := by
    have := Real.tendsto_sqrt_atTop.inv_tendsto_atTop
    exact this.congr fun t ↦ by simp [one_div]
  exact (tendsto_sum_char_mul_and_norm_sub_le hχ antitoneOn_one_div_sqrt
    (fun t ht ↦ by positivity) hlim).2 x hx

end NTKB.Apostol
