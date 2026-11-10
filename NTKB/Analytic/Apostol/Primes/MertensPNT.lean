/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Apostol.Primes.MertensFunction
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

/-!
# `M(x) = o(x)` implies the prime number theorem (Apostol, Theorems 4.15 and 4.16)

* Theorem 4.15: `M(x) = o(x)` implies `ψ(x) ~ x`. Apostol's proof: with
  `f = σ₀ - log - 2C` (`NTKB.Apostol.fDivLog`) one has `⌊x⌋ - ψ(x) - 2C = ∑_{qd ≤ x} μ(d) f(q)`;
  the partial sums `F` of `f` are `O(√x)` by Dirichlet's divisor theorem (3.3) and Theorem 3.15;
  the hyperbola identity (3.17) with `ab = x`, `a` large but fixed, shows the double sum is `o(x)`.
* Theorem 4.16: `∑_{n ≤ x} μ(n)/n → 0` implies `ψ(x) ~ x`, via `M(x) = o(x)` (partial summation
  and a Cesàro mean in place of Apostol's integral `∫₁ˣ A(t) dt`).
-/

open Finset ArithmeticFunction Real Chebyshev Filter Topology
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta ArithmeticFunction.sigma

namespace NTKB.Apostol

/-- The function `2C·I` (value `2C` at `1`, else `0`); `twoGammaI * u` is the constant `2C`. -/
noncomputable def twoGammaI : ArithmeticFunction ℝ :=
  ⟨fun n ↦ if n = 1 then 2 * eulerMascheroniConstant else 0, by simp⟩

/-- Apostol's `f = σ₀ - log - 2C` (proof of Theorem 4.15). -/
noncomputable def fDivLog : ArithmeticFunction ℝ :=
  ((σ 0 : ArithmeticFunction ℕ) : ArithmeticFunction ℝ) - ArithmeticFunction.log - twoGammaI * ζ

theorem twoGammaI_mul_zeta_apply {n : ℕ} (hn : n ≠ 0) :
    (twoGammaI * ζ) n = 2 * eulerMascheroniConstant := by
  rw [coe_mul_zeta_apply, sum_eq_single 1]
  · simp [twoGammaI]
  · intro b _ hb; simp [twoGammaI, hb]
  · intro h; simp [hn] at h

theorem fDivLog_apply {n : ℕ} (hn : n ≠ 0) :
    fDivLog n = σ 0 n - Real.log n - 2 * eulerMascheroniConstant := by
  simp only [fDivLog, sub_apply, natCoe_apply, log_apply, twoGammaI_mul_zeta_apply hn]

/-- `μ * f = u - Λ - 2C·I`. -/
theorem moebius_mul_fDivLog :
    (μ : ArithmeticFunction ℝ) * fDivLog = (ζ : ArithmeticFunction ℝ) - Λ - twoGammaI := by
  have h1 : (μ : ArithmeticFunction ℝ) * ((ζ : ArithmeticFunction ℝ) * ζ) = ζ := by
    rw [← mul_assoc, coe_moebius_mul_coe_zeta, one_mul]
  have h3 : (μ : ArithmeticFunction ℝ) * (twoGammaI * ζ) = twoGammaI := by
    rw [mul_comm twoGammaI, ← mul_assoc, coe_moebius_mul_coe_zeta, one_mul]
  rw [fDivLog, natCoe_sigma_zero_eq, mul_sub, mul_sub, h1, moebius_mul_log_eq_vonMangoldt, h3]

/-- `∑_{n ≤ x} (μ * f)(n) = ⌊x⌋ - ψ(x) - 2C` for `x ≥ 1` (Apostol's (38)). -/
theorem sum_moebius_mul_fDivLog {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ Ioc 0 ⌊x⌋₊, ((μ : ArithmeticFunction ℝ) * fDivLog) n =
      ⌊x⌋₊ - ψ x - 2 * eulerMascheroniConstant := by
  have hN1 : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
  rw [moebius_mul_fDivLog]
  simp only [sub_apply, sum_sub_distrib]
  rw [sum_Ioc_zeta_real]
  have : ∑ n ∈ Ioc 0 ⌊x⌋₊, twoGammaI n = 2 * eulerMascheroniConstant := by
    rw [sum_eq_single 1]
    · simp [twoGammaI]
    · intro b _ hb; simp [twoGammaI, hb]
    · intro h; simp [hN1] at h
  rw [this]
  rfl

/-- The partial sums of `f = σ₀ - log - 2C` are `O(√x)`: `|F(x)| ≤ 13 √x` for `x ≥ 1`
(Theorems 3.3 and 3.15). -/
theorem abs_sum_fDivLog_le {x : ℝ} (hx : 1 ≤ x) :
    |∑ n ∈ Ioc 0 ⌊x⌋₊, fDivLog n| ≤ 13 * √x := by
  have hx0 : 0 < x := by linarith
  have e : ∑ n ∈ Ioc 0 ⌊x⌋₊, fDivLog n = ∑ n ∈ Ioc 0 ⌊x⌋₊, (σ 0 n : ℝ) -
      ∑ n ∈ Ioc 0 ⌊x⌋₊, Real.log n - 2 * eulerMascheroniConstant * ⌊x⌋₊ := by
    rw [sum_congr rfl fun n hn ↦ fDivLog_apply (mem_Ioc.1 hn).1.ne', sum_sub_distrib,
      sum_sub_distrib, sum_const, Nat.card_Ioc, nsmul_eq_mul, Nat.sub_zero, mul_comm]
  rw [e]
  have h1 := abs_le.1 (abs_sum_sigma_zero_sub_le hx)
  have h2 := Real.sum_log_le hx
  have h3 := Real.le_sum_log hx
  have h4 := Nat.floor_le hx0.le
  have h5 := Nat.lt_floor_add_one x
  have hγ1 := eulerMascheroniConstant_lt_two_thirds
  have hγ0 : 0 < eulerMascheroniConstant := by
    have := one_half_lt_eulerMascheroniConstant; linarith
  have hs1 : 1 ≤ √x := Real.one_le_sqrt.2 hx
  have hlog : Real.log x ≤ 2 * √x := by
    have := Real.log_le_rpow_div hx0.le (show (0 : ℝ) < 1 / 2 by norm_num)
    rw [← Real.sqrt_eq_rpow] at this; linarith
  have hl0 : 0 ≤ Real.log x := Real.log_nonneg hx
  rw [abs_le]
  constructor <;> nlinarith

/-- The first sum of the hyperbola identity in the proof of 4.15:
`|∑_{n ≤ a} f(n) M(x/n)| ≤ δ x ∑_{n ≤ a} |f(n)|/n` once `|M(y)| ≤ δ y` for `y ≥ c` and
`x ≥ a c`. -/
theorem abs_sum_fDivLog_mul_mertens_le {a c x δ : ℝ} (ha0 : 0 < a) (hc1 : 1 ≤ c)
    (hx : a * c ≤ x) (hM : ∀ y, c ≤ y → |mertens y| ≤ δ * y) :
    |∑ n ∈ Ioc 0 ⌊a⌋₊, fDivLog n * ∑ m ∈ Ioc 0 ⌊x / n⌋₊, (μ : ArithmeticFunction ℝ) m| ≤
      (∑ n ∈ Ioc 0 ⌊a⌋₊, |fDivLog n| / n) * (δ * x) := by
  rw [sum_mul]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun n hn ↦ ?_)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (mem_Ioc.1 hn).1
  have hna : (n : ℝ) ≤ a := by
    have : (n : ℝ) ≤ ⌊a⌋₊ := by exact_mod_cast (mem_Ioc.1 hn).2
    linarith [Nat.floor_le ha0.le]
  have hn0 : (0 : ℝ) < n := by linarith
  have hxn : c ≤ x / n := by
    rw [le_div_iff₀ hn0]
    nlinarith
  have hMeq : ∑ m ∈ Ioc 0 ⌊x / n⌋₊, (μ : ArithmeticFunction ℝ) m = mertens (x / n) := by
    simp [mertens, intCoe_apply]
  rw [abs_mul, hMeq]
  calc |fDivLog n| * |mertens (x / n)| ≤ |fDivLog n| * (δ * (x / n)) :=
        mul_le_mul_of_nonneg_left (hM _ hxn) (abs_nonneg _)
    _ = |fDivLog n| / n * (δ * x) := by ring

/-- The second sum: `|∑_{n ≤ b} μ(n) F(x/n)| ≤ 26 √x √b` for `1 ≤ b ≤ x`. -/
theorem abs_sum_moebius_mul_sum_fDivLog_le {b x : ℝ} (hb1 : 1 ≤ b) (hbx : b ≤ x) :
    |∑ n ∈ Ioc 0 ⌊b⌋₊, (μ : ArithmeticFunction ℝ) n * ∑ m ∈ Ioc 0 ⌊x / n⌋₊, fDivLog m| ≤
      26 * (√x * √b) := by
  have hb0 : 0 < b := by linarith
  calc _ ≤ ∑ n ∈ Ioc 0 ⌊b⌋₊, |(μ : ArithmeticFunction ℝ) n *
        ∑ m ∈ Ioc 0 ⌊x / n⌋₊, fDivLog m| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ Ioc 0 ⌊b⌋₊, 13 * (√x * (1 / √(n : ℝ))) := by
        refine sum_le_sum fun n hn ↦ ?_
        have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (mem_Ioc.1 hn).1
        have hnb : (n : ℝ) ≤ b := by
          have : (n : ℝ) ≤ ⌊b⌋₊ := by exact_mod_cast (mem_Ioc.1 hn).2
          linarith [Nat.floor_le hb0.le]
        have hn0 : (0 : ℝ) < n := by linarith
        have hxn : 1 ≤ x / n := by rw [le_div_iff₀ hn0]; linarith
        rw [abs_mul]
        have hμ : |(μ : ArithmeticFunction ℝ) n| ≤ 1 := by
          rw [intCoe_apply]; exact_mod_cast abs_moebius_le_one
        calc |(μ : ArithmeticFunction ℝ) n| * |∑ m ∈ Ioc 0 ⌊x / n⌋₊, fDivLog m|
            ≤ 1 * (13 * √(x / n)) :=
              mul_le_mul hμ (abs_sum_fDivLog_le hxn) (abs_nonneg _) zero_le_one
          _ = 13 * (√x * (1 / √(n : ℝ))) := by
              rw [one_mul, Real.sqrt_div' _ hn0.le, mul_one_div]
    _ = 13 * √x * ∑ n ∈ Ioc 0 ⌊b⌋₊, 1 / √(n : ℝ) := by
        rw [mul_sum]; exact sum_congr rfl fun n _ ↦ by ring
    _ ≤ 13 * √x * (2 * √b) := by
        refine mul_le_mul_of_nonneg_left ((sum_Ioc_inv_sqrt_le _).trans ?_) (by positivity)
        gcongr; exact Nat.floor_le hb0.le
    _ = 26 * (√x * √b) := by ring

/-- `∑_{qd ≤ x} μ(d) f(q) = o(x)` under `M(x) = o(x)`: for every `ε > 0`,
`|⌊x⌋ - ψ(x) - 2C| ≤ ε x` for all large `x`. -/
theorem eventually_abs_floor_sub_psi_le (hM : Tendsto (fun x ↦ mertens x / x) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ X, ∀ x, X ≤ x → |(⌊x⌋₊ : ℝ) - ψ x - 2 * eulerMascheroniConstant| ≤ ε * x := by
  -- choose `a` with `26/√a ≤ ε/3`
  set a : ℝ := (78 / ε) ^ 2 + 1 with ha
  have ha1 : 1 ≤ a := by rw [ha]; nlinarith [sq_nonneg (78 / ε)]
  have ha0 : 0 < a := by linarith
  have hsa : 78 / ε ≤ √a := by
    rw [ha]; refine Real.le_sqrt_of_sq_le ?_; linarith
  have hsa0 : 0 < √a := Real.sqrt_pos.2 ha0
  have hsa' : 26 ≤ ε / 3 * √a := by
    rw [div_le_iff₀ hε] at hsa; linarith
  set Kf := ∑ n ∈ Ioc 0 ⌊a⌋₊, |fDivLog n| / n + 1 with hKf
  have hKf1 : ∑ n ∈ Ioc 0 ⌊a⌋₊, |fDivLog n| / n ≤ Kf := by rw [hKf]; linarith
  have hKf0 : 0 < Kf := by
    have : 0 ≤ ∑ n ∈ Ioc 0 ⌊a⌋₊, |fDivLog n| / n := sum_nonneg fun _ _ ↦ by positivity
    linarith
  set δ := ε / (3 * Kf) with hδ
  have hδ0 : 0 < δ := by positivity
  obtain ⟨c, hc⟩ := Metric.tendsto_atTop.1 hM δ hδ0
  set c' := max c 1
  have hc' : ∀ y, c' ≤ y → |mertens y| ≤ δ * y := by
    intro y hy
    have hy0 : 0 < y := lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) hy)
    have := hc y (le_trans (le_max_left _ _) hy)
    rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos hy0, div_lt_iff₀ hy0] at this
    exact this.le
  refine ⟨a * c', fun x hx ↦ ?_⟩
  have hac : a ≤ a * c' := le_mul_of_one_le_right ha0.le (le_max_right _ _)
  have hxa : a ≤ x := le_trans hac hx
  have hx1 : 1 ≤ x := le_trans ha1 hxa
  have hx0 : 0 < x := by linarith
  set b := x / a with hb
  have hb0 : 0 < b := div_pos hx0 ha0
  have hb1 : 1 ≤ b := by rw [hb, le_div_iff₀ ha0]; linarith
  have hbx : b ≤ x := by rw [hb, div_le_iff₀ ha0]; nlinarith
  have hab : a * b = x := by rw [hb]; field_simp
  have hhyp := sum_mul_eq_hyperbola fDivLog (μ : ArithmeticFunction ℝ) ha0 hb0 hab
  rw [mul_comm fDivLog, sum_moebius_mul_fDivLog hx1] at hhyp
  rw [hhyp]
  have hT1 := abs_sum_fDivLog_mul_mertens_le ha0 (le_max_right c 1) hx hc'
  have hT2 := abs_sum_moebius_mul_sum_fDivLog_le hb1 hbx
  have hMb : |∑ n ∈ Ioc 0 ⌊b⌋₊, (μ : ArithmeticFunction ℝ) n| ≤ b := by
    have := abs_mertens_le hb0.le
    simpa [mertens, intCoe_apply] using this
  have hT3 : |(∑ n ∈ Ioc 0 ⌊a⌋₊, fDivLog n) * ∑ n ∈ Ioc 0 ⌊b⌋₊, (μ : ArithmeticFunction ℝ) n| ≤
      13 * √a * b := by
    rw [abs_mul]
    exact mul_le_mul (abs_sum_fDivLog_le ha1) hMb (abs_nonneg _) (by positivity)
  -- `√x √b = x/√a` and `√a b = x/√a`
  have hsx : √x = √a * √b := by rw [← Real.sqrt_mul ha0.le, hab]
  have hsb : √b * √b = b := Real.mul_self_sqrt hb0.le
  have hsaa : √a * √a = a := Real.mul_self_sqrt ha0.le
  have hk1 : √a * (√x * √b) = x := by
    rw [hsx]; nlinarith
  have hk2 : √a * (√a * b) = x := by rw [← mul_assoc, hsaa, hab]
  have hT1' : (∑ n ∈ Ioc 0 ⌊a⌋₊, |fDivLog n| / n) * (δ * x) ≤ ε / 3 * x := by
    calc (∑ n ∈ Ioc 0 ⌊a⌋₊, |fDivLog n| / n) * (δ * x) ≤ Kf * (δ * x) :=
          mul_le_mul_of_nonneg_right hKf1 (by positivity)
      _ = ε / 3 * x := by rw [hδ]; field_simp
  have hP : 0 ≤ √x * √b := mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg b)
  have hT2' : 26 * (√x * √b) ≤ ε / 3 * x :=
    calc 26 * (√x * √b) ≤ (ε / 3 * √a) * (√x * √b) := mul_le_mul_of_nonneg_right hsa' hP
      _ = ε / 3 * (√a * (√x * √b)) := by ring
      _ = ε / 3 * x := by rw [hk1]
  have hT3' : 13 * √a * b ≤ ε / 3 * x :=
    calc 13 * √a * b = 13 * (√a * b) := by ring
      _ ≤ (ε / 3 * √a) * (√a * b) :=
          mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hsa0.le hb0.le)
      _ = ε / 3 * (√a * (√a * b)) := by ring
      _ = ε / 3 * x := by rw [hk2]
  calc |∑ n ∈ Ioc 0 ⌊a⌋₊, fDivLog n * ∑ m ∈ Ioc 0 ⌊x / n⌋₊, (μ : ArithmeticFunction ℝ) m +
        ∑ n ∈ Ioc 0 ⌊b⌋₊, (μ : ArithmeticFunction ℝ) n * ∑ m ∈ Ioc 0 ⌊x / n⌋₊, fDivLog m -
        (∑ n ∈ Ioc 0 ⌊a⌋₊, fDivLog n) * ∑ n ∈ Ioc 0 ⌊b⌋₊, (μ : ArithmeticFunction ℝ) n|
      ≤ |∑ n ∈ Ioc 0 ⌊a⌋₊, fDivLog n * ∑ m ∈ Ioc 0 ⌊x / n⌋₊, (μ : ArithmeticFunction ℝ) m| +
        |∑ n ∈ Ioc 0 ⌊b⌋₊, (μ : ArithmeticFunction ℝ) n * ∑ m ∈ Ioc 0 ⌊x / n⌋₊, fDivLog m| +
        |(∑ n ∈ Ioc 0 ⌊a⌋₊, fDivLog n) * ∑ n ∈ Ioc 0 ⌊b⌋₊, (μ : ArithmeticFunction ℝ) n| := by
        refine (abs_sub _ _).trans ?_
        gcongr
        exact abs_add_le _ _
    _ ≤ ε / 3 * x + ε / 3 * x + ε / 3 * x := by
        gcongr
        · exact hT1.trans hT1'
        · exact hT2.trans hT2'
        · exact hT3.trans hT3'
    _ = ε * x := by ring

/-- **Apostol, Theorem 4.15.** `M(x) = o(x)` implies `ψ(x) ~ x`. -/
@[kb "apostol1976" "Thm 4.15, p. 94"]
theorem tendsto_psi_div_of_mertens (hM : Tendsto (fun x ↦ mertens x / x) atTop (𝓝 0)) :
    Tendsto (fun x ↦ ψ x / x) atTop (𝓝 1) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨X, hX⟩ := eventually_abs_floor_sub_psi_le hM (half_pos hε)
  refine ⟨max X (max 1 (8 / ε)), fun x hx ↦ ?_⟩
  have hxX : X ≤ x := le_trans (le_max_left _ _) hx
  have hx1 : 1 ≤ x := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hx)
  have hxe : 8 / ε ≤ x := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hx)
  have hx0 : 0 < x := by linarith
  have h8 : 8 ≤ ε * x := by rw [div_le_iff₀ hε] at hxe; linarith
  have hS := abs_le.1 (hX x hxX)
  have h4 := Nat.floor_le hx0.le
  have h5 := Nat.lt_floor_add_one x
  have hγ1 := eulerMascheroniConstant_lt_two_thirds
  have hγ0 : 0 < eulerMascheroniConstant := by
    have := one_half_lt_eulerMascheroniConstant; linarith
  rw [Real.dist_eq, abs_lt]
  constructor
  · rw [lt_sub_iff_add_lt, lt_div_iff₀ hx0]; nlinarith
  · rw [sub_lt_iff_lt_add, div_lt_iff₀ hx0]; nlinarith

/-! ## Theorem 4.16 -/

/-- Partial summation: `M(N) = N A(N) - ∑_{n < N} A(n)` with `A(n) = ∑_{m ≤ n} μ(m)/m`. -/
theorem sum_moebius_eq_mul_sub (N : ℕ) :
    ∑ n ∈ Ioc 0 N, (μ n : ℝ) = N * ∑ n ∈ Ioc 0 N, (μ n : ℝ) / n -
      ∑ n ∈ range N, ∑ m ∈ Ioc 0 n, (μ m : ℝ) / m := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_Ioc_succ_top (Nat.zero_le _), ih, sum_Ioc_succ_top (Nat.zero_le _), sum_range_succ]
    have : ((N + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    field_simp
    push_cast
    ring

/-- **Apostol, Theorem 4.16.** If `A(x) = ∑_{n ≤ x} μ(n)/n → 0` then `ψ(x) ~ x`. -/
@[kb "apostol1976" "Thm 4.16, p. 97"]
theorem tendsto_psi_div_of_sum_moebius_div
    (hA : Tendsto (fun x : ℝ ↦ ∑ n ∈ Ioc 0 ⌊x⌋₊, (μ n : ℝ) / n) atTop (𝓝 0)) :
    Tendsto (fun x ↦ ψ x / x) atTop (𝓝 1) := by
  apply tendsto_psi_div_of_mertens
  -- along the integers: `M(N)/N = A(N) - (1/N) ∑_{n < N} A(n) → 0`
  set A : ℕ → ℝ := fun n ↦ ∑ m ∈ Ioc 0 n, (μ m : ℝ) / m
  have hAN : Tendsto A atTop (𝓝 0) := by
    have := hA.comp tendsto_natCast_atTop_atTop
    refine this.congr fun n ↦ ?_
    simp [A, Nat.floor_natCast]
  have hces := hAN.cesaro
  have hMN : Tendsto (fun N : ℕ ↦ (∑ n ∈ Ioc 0 N, (μ n : ℝ)) / N) atTop (𝓝 0) := by
    have := hAN.sub hces
    rw [sub_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_ne_atTop 0] with N hN
    have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN
    rw [sum_moebius_eq_mul_sub]
    field_simp
    simp only [A]
    ring
  -- back to real `x`: `|M(x)/x| ≤ |M(⌊x⌋)/⌊x⌋|`
  rw [Metric.tendsto_atTop] at hMN ⊢
  intro ε hε
  obtain ⟨N₀, hN₀⟩ := hMN ε hε
  refine ⟨N₀ + 1, fun x hx ↦ ?_⟩
  have hx0 : 0 < x := by have := Nat.cast_nonneg (α := ℝ) N₀; linarith
  have hfl : N₀ ≤ ⌊x⌋₊ := by
    apply Nat.le_floor; linarith
  have hN1 : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by have := Nat.cast_nonneg (α := ℝ) N₀; push_cast; linarith)
  have hN0 : (0 : ℝ) < ⌊x⌋₊ := by exact_mod_cast hN1
  have h := hN₀ ⌊x⌋₊ hfl
  rw [Real.dist_eq, sub_zero] at h ⊢
  calc |mertens x / x| = |∑ n ∈ Ioc 0 ⌊x⌋₊, (μ n : ℝ)| / x := by
        rw [mertens, abs_div, abs_of_pos hx0]
    _ ≤ |∑ n ∈ Ioc 0 ⌊x⌋₊, (μ n : ℝ)| / ⌊x⌋₊ :=
        div_le_div_of_nonneg_left (abs_nonneg _) hN0 (Nat.floor_le hx0.le)
    _ = |(∑ n ∈ Ioc 0 ⌊x⌋₊, (μ n : ℝ)) / ⌊x⌋₊| := by rw [abs_div, abs_of_pos hN0]
    _ < ε := h

end NTKB.Apostol
