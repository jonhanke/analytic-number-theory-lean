/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Davenport.Zeros.ZeroSum
import Mathlib.NumberTheory.Chebyshev

/-!
# The prime number theorem with the classical error term

**Davenport, Ch. 18, pp. 111-112, (1) (row 18-1).** `ψ(x) = x + O(x exp(-c √log x))`, from the
explicit formula (17-13), the zero-free region (13-12) and `∑_{|γ|<T} 1/|ρ| ≪ log² T`, with
`log T = √log x`.
-/

open Filter Topology Complex Set
open scoped Real ArithmeticFunction.vonMangoldt

namespace NTKB

/-- `ψ(N) = ψ₀(N) + Λ(N)/2` at integers. -/
lemma psi_natCast_eq_psi0 (N : ℕ) : Chebyshev.psi N = psi0 N + Λ N / 2 := by
  rw [Chebyshev.psi_eq_sum_Icc, Nat.floor_natCast, psi0]
  have : Finset.Icc 0 N = Finset.range (N + 1) := by
    ext n; simp [Finset.mem_Icc, Finset.mem_range, Nat.lt_succ_iff]
  rw [this, Finset.sum_range_succ]
  ring

/-- `|x^ρ| ≤ x exp(-c log x / log(T + 2))` for the zeros with `|γ| < T`. -/
lemma rpow_re_zero_le {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hzf : ∀ s : ℂ, riemannZeta s = 0 → s.re < 1 - c₀ / Real.log (|s.im| + 2))
    {x T : ℝ} (hx : 1 ≤ x) (ρ : ZeroIndex riemannXi) (hρ : |ρ.val.im| < T) :
    x ^ ρ.val.re ≤ x * Real.exp (-(c₀ * Real.log x / Real.log (T + 2))) := by
  have hx0 : 0 < x := by linarith
  have hβ := hzf _ (riemannXi_zero_mem ρ).1
  have hl1 : 0 < Real.log (|ρ.val.im| + 2) := Real.log_pos (by linarith [abs_nonneg ρ.val.im])
  have hl2 : Real.log (|ρ.val.im| + 2) ≤ Real.log (T + 2) :=
    Real.log_le_log (by positivity) (by linarith)
  have hβ' : ρ.val.re ≤ 1 - c₀ / Real.log (T + 2) := by
    have : c₀ / Real.log (T + 2) ≤ c₀ / Real.log (|ρ.val.im| + 2) :=
      div_le_div_of_nonneg_left hc₀.le hl1 hl2
    linarith
  calc x ^ ρ.val.re ≤ x ^ (1 - c₀ / Real.log (T + 2)) := Real.rpow_le_rpow_of_exponent_le hx hβ'
    _ = x * Real.exp (-(c₀ * Real.log x / Real.log (T + 2))) := by
      rw [Real.rpow_sub hx0, Real.rpow_one, Real.rpow_def_of_pos hx0, div_eq_mul_inv x,
        ← Real.exp_neg]
      congr 2; ring

/-- `u⁴ ≤ 24 (2/c)⁴ e^{cu/2}` for `u ≥ 0`, `c > 0`. -/
lemma pow_four_le_exp {c u : ℝ} (hc : 0 < c) (hu : 0 ≤ u) :
    u ^ 4 ≤ 24 * (2 / c) ^ 4 * Real.exp (c * u / 2) := by
  have h := Real.pow_div_factorial_le_exp (c * u / 2) (by positivity) 4
  have h4 : (Nat.factorial 4 : ℝ) = 24 := by norm_num [Nat.factorial]
  rw [h4, div_le_iff₀ (by norm_num)] at h
  have e : u ^ 4 = (2 / c) ^ 4 * (c * u / 2) ^ 4 := by field_simp
  rw [e]
  have : 0 ≤ (2 / c) ^ 4 := by positivity
  nlinarith

set_option maxHeartbeats 1000000 in
/-- **Davenport, Ch. 18, p. 112** at integers: there are `c, C > 0` with
`|ψ(N) - N| ≤ C N exp(-c √log N)` for `N ≥ 3`. -/
lemma psi_natCast_sub_le :
    ∃ c C : ℝ, 0 < c ∧ c ≤ 1 / 2 ∧ 0 < C ∧ ∀ N : ℕ, 3 ≤ N →
      |Chebyshev.psi N - N| ≤ C * N * Real.exp (-(c * √(Real.log N))) := by
  obtain ⟨A, hA, hexp⟩ := Davenport.explicit_formula_psi0
  obtain ⟨c₀, hc₀, hzf⟩ := Davenport.riemannZeta_zero_free_region_all
  obtain ⟨C₀, hC₀, hsum⟩ := Davenport.sum_zeros_inv_norm_le
  set c' := min 1 (c₀ / 2) with hc'
  have hc'0 : 0 < c' := lt_min one_pos (by positivity)
  have hc'1 : c' ≤ 1 := min_le_left _ _
  set Z := ‖deriv riemannZeta 0 / riemannZeta 0‖ with hZdef
  have hZ0 : 0 ≤ Z := norm_nonneg _
  set K := 24 * (2 / c') ^ 4 with hKdef
  have hK : 0 < K := by positivity
  have hcc : c' ≤ c₀ / 2 := min_le_right _ _
  have hp4 : ∀ v : ℝ, 0 ≤ v → v ^ 4 ≤ K * Real.exp (c' * v / 2) := fun v hv ↦ by
    rw [hKdef]; exact pow_four_le_exp hc'0 hv
  clear_value Z K c'
  refine ⟨c' / 2, (4 * A + C₀) * K + Z + 1 + K, by positivity, by linarith, by positivity,
    fun N hN ↦ ?_⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
  set L := Real.log N with hL
  have hL1 : 1 < L := by
    rw [hL, Real.lt_log_iff_exp_lt hN0]; have := Real.exp_one_lt_d9; linarith
  set u := √L with hu
  have hu2 : u ^ 2 = L := Real.sq_sqrt (by linarith)
  have hu1 : 1 < u := by rw [hu, Real.lt_sqrt zero_le_one]; linarith
  have hu0 : 0 < u := by linarith
  have huL : u ≤ L := by nlinarith
  set T := Real.exp u with hT
  have hT2 : 2 ≤ T := by
    have := Real.add_one_le_exp u; rw [← hT] at this; linarith
  have hlogT : Real.log T = u := Real.log_exp u
  have hNe : N = Real.exp L := (Real.exp_log hN0).symm
  clear_value T u L
  -- the explicit formula
  have e1 := hexp N hN T hT2
  have hsplit : (psi0 N : ℂ) - ((N : ℝ) : ℂ) = ((psi0 N : ℂ) - explicitMain N T) -
      ∑ ρ ∈ zerosBelow T, perronKernel N ρ.val - deriv riemannZeta 0 / riemannZeta 0 -
      ((1 / 2 * Real.log (1 - (N : ℝ) ^ (-2 : ℝ)) : ℝ) : ℂ) := by
    simp only [explicitMain]; ring
  -- `log(NT) ≤ 2 u²`
  have hNT : Real.log (N * T) ≤ 2 * u ^ 2 := by
    rw [Real.log_mul hN0.ne' (by positivity), hlogT, ← hL, ← hu2]; nlinarith
  have hNT0 : 0 ≤ Real.log (N * T) := Real.log_nonneg (by nlinarith)
  have b1 : ‖(psi0 N : ℂ) - explicitMain N T‖ ≤ 4 * A * N * u ^ 4 * Real.exp (-c' * u) := by
    refine e1.trans ?_
    rw [div_le_iff₀ (by positivity)]
    have hTe : Real.exp (-c' * u) * T ≥ 1 := by
      rw [hT, ← Real.exp_add]; apply Real.one_le_exp; nlinarith
    have h1 : Real.log (N * T) ^ 2 ≤ 4 * u ^ 4 := by nlinarith
    have h2 : A * N * Real.log (N * T) ^ 2 ≤ A * N * (4 * u ^ 4) := by gcongr
    have h3 : 0 ≤ 4 * A * N * u ^ 4 := by positivity
    nlinarith
  -- the sum over zeros
  have b2 : ‖∑ ρ ∈ zerosBelow T, perronKernel N ρ.val‖ ≤ C₀ * N * u ^ 4 * Real.exp (-c' * u) := by
    have hlT2 : Real.log (T + 2) ≤ 2 * u := by
      have : Real.log (T + 2) ≤ Real.log (T * T) := Real.log_le_log (by positivity) (by nlinarith)
      rw [Real.log_mul (by positivity) (by positivity), hlogT] at this; linarith
    have hE : Real.exp (-(c₀ * Real.log N / Real.log (T + 2))) ≤ Real.exp (-c' * u) := by
      apply Real.exp_le_exp.mpr
      have hlT2' : 0 < Real.log (T + 2) := Real.log_pos (by linarith)
      have : c' * u ≤ c₀ * Real.log N / Real.log (T + 2) := by
        rw [le_div_iff₀ hlT2', ← hL, ← hu2]
        have : c' * u * Real.log (T + 2) ≤ c' * u * (2 * u) := by gcongr
        nlinarith
      linarith
    calc ‖∑ ρ ∈ zerosBelow T, perronKernel N ρ.val‖
        ≤ ∑ ρ ∈ zerosBelow T, N * Real.exp (-c' * u) * (1 / ‖ρ.val‖) := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun ρ hρ ↦ ?_)
          rw [norm_perronKernel hN0, div_eq_mul_one_div]
          gcongr
          exact (rpow_re_zero_le hc₀ hzf (by linarith) ρ (mem_zerosBelow.mp hρ)).trans
            (mul_le_mul_of_nonneg_left hE hN0.le)
      _ = N * Real.exp (-c' * u) * ∑ ρ ∈ zerosBelow T, 1 / ‖ρ.val‖ := by rw [Finset.mul_sum]
      _ ≤ N * Real.exp (-c' * u) * (C₀ * u ^ 2) := by
          gcongr; rw [← hlogT]; exact hsum T hT2
      _ ≤ C₀ * N * u ^ 4 * Real.exp (-c' * u) := by
          have h1 : u ^ 2 ≤ u ^ 4 := pow_le_pow_right₀ hu1.le (by norm_num)
          have h2 : 0 ≤ C₀ * N * Real.exp (-c' * u) := by positivity
          have h3 := mul_le_mul_of_nonneg_left h1 h2
          have e1 : N * Real.exp (-c' * u) * (C₀ * u ^ 2) = C₀ * N * Real.exp (-c' * u) * u ^ 2 := by
            ring
          have e2 : C₀ * N * u ^ 4 * Real.exp (-c' * u) = C₀ * N * Real.exp (-c' * u) * u ^ 4 := by
            ring
          rw [e1, e2]; exact h3
  -- the constant terms
  have b3 : |1 / 2 * Real.log (1 - (N : ℝ) ^ (-2 : ℝ))| ≤ 1 := by
    have hy : (N : ℝ) ^ (-2 : ℝ) ≤ 1 / 2 := by
      rw [Real.rpow_neg hN0.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      rw [inv_le_comm₀ (by positivity) (by norm_num)]; nlinarith
    have hy0 : 0 < (N : ℝ) ^ (-2 : ℝ) := by positivity
    have hl : Real.log (1 - (N : ℝ) ^ (-2 : ℝ)) ≤ 0 := Real.log_nonpos (by linarith) (by linarith)
    have hl' : -1 ≤ Real.log (1 - (N : ℝ) ^ (-2 : ℝ)) := by
      have := Real.one_sub_inv_le_log_of_pos (show 0 < 1 - (N : ℝ) ^ (-2 : ℝ) by linarith)
      have h2 : (1 - (N : ℝ) ^ (-2 : ℝ))⁻¹ ≤ 2 := by
        rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
      linarith
    rw [abs_le]; constructor <;> linarith
  -- assemble `|ψ₀(N) - N|`
  have hψ0 : |psi0 N - N| ≤ (4 * A + C₀) * N * u ^ 4 * Real.exp (-c' * u) + Z + 1 := by
    have : |psi0 N - N| = ‖(psi0 N : ℂ) - ((N : ℝ) : ℂ)‖ := by
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    rw [this, hsplit]
    have h4 : ‖(((1 / 2 * Real.log (1 - (N : ℝ) ^ (-2 : ℝ)) : ℝ) : ℂ))‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs]; exact b3
    calc _ ≤ ‖(psi0 N : ℂ) - explicitMain N T‖ + ‖∑ ρ ∈ zerosBelow T, perronKernel N ρ.val‖ +
          ‖deriv riemannZeta 0 / riemannZeta 0‖ +
            ‖(((1 / 2 * Real.log (1 - (N : ℝ) ^ (-2 : ℝ)) : ℝ) : ℂ))‖ :=
          (norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans
            (add_le_add (norm_sub_le _ _) le_rfl)) le_rfl)
      _ ≤ 4 * A * N * u ^ 4 * Real.exp (-c' * u) + C₀ * N * u ^ 4 * Real.exp (-c' * u) + Z + 1 :=
          add_le_add (add_le_add (add_le_add b1 b2) hZdef.ge) h4
      _ = (4 * A + C₀) * N * u ^ 4 * Real.exp (-c' * u) + Z + 1 := by ring
  -- `u⁴ e^{-c'u} ≤ K e^{-c'u/2}` and `1 ≤ N e^{-c'u/2}`
  have hu4 : u ^ 4 * Real.exp (-c' * u) ≤ K * Real.exp (-(c' / 2 * u)) := by
    have h0 := hp4 u hu0.le
    have e : Real.exp (-c' * u) = Real.exp (c' * u / 2) * Real.exp (-c' * u) *
        Real.exp (-(c' / 2 * u)) := by
      rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    rw [e]
    have : Real.exp (c' * u / 2) * Real.exp (-c' * u) = Real.exp (-(c' / 2 * u)) := by
      rw [← Real.exp_add]; congr 1; ring
    calc u ^ 4 * (Real.exp (c' * u / 2) * Real.exp (-c' * u) * Real.exp (-(c' / 2 * u)))
        = u ^ 4 * Real.exp (-(c' / 2 * u)) * Real.exp (-(c' / 2 * u)) := by rw [this]; ring
      _ ≤ K * Real.exp (c' * u / 2) * Real.exp (-(c' / 2 * u)) * Real.exp (-(c' / 2 * u)) := by
          gcongr
      _ = K * Real.exp (-(c' / 2 * u)) := by
          rw [mul_assoc K, ← Real.exp_add, show c' * u / 2 + -(c' / 2 * u) = 0 by ring,
            Real.exp_zero, mul_one]
  have hNe1 : 1 ≤ N * Real.exp (-(c' / 2 * u)) := by
    rw [hNe, ← Real.exp_add]; apply Real.one_le_exp
    have := mul_le_mul_of_nonneg_right hc'1 hu0.le
    linarith
  have hΛ : Λ N / 2 ≤ K * N * Real.exp (-(c' / 2 * u)) := by
    have h1 : Λ N ≤ L := hL ▸ ArithmeticFunction.vonMangoldt_le_log
    have h2 : L ≤ u ^ 4 := by
      rw [← hu2]; exact pow_le_pow_right₀ hu1.le (by norm_num)
    have h3 : u ^ 4 ≤ K * Real.exp (c' * u / 2) := hp4 u hu0.le
    have h4 : Real.exp (c' * u / 2) ≤ N * Real.exp (-(c' / 2 * u)) := by
      have hNx : (N : ℝ) * Real.exp (-(c' / 2 * u)) = Real.exp (L + -(c' / 2 * u)) := by
        rw [Real.exp_add, hL, Real.exp_log hN0]
      rw [hNx]; apply Real.exp_le_exp.mpr
      have h5 : c' * u ≤ u := by
        have := mul_le_mul_of_nonneg_right hc'1 hu0.le; linarith
      have h6 : u ≤ L := huL
      linarith
    have hΛ0 := ArithmeticFunction.vonMangoldt_nonneg (n := N)
    have : K * Real.exp (c' * u / 2) ≤ K * (N * Real.exp (-(c' / 2 * u))) := by gcongr
    have e : K * (N * Real.exp (-(c' / 2 * u))) = K * N * Real.exp (-(c' / 2 * u)) := by ring
    linarith
  have hΛ0 := ArithmeticFunction.vonMangoldt_nonneg (n := N)
  rw [psi_natCast_eq_psi0, show psi0 N + Λ N / 2 - N = (psi0 N - N) + Λ N / 2 by ring]
  refine (abs_add_le _ _).trans ?_
  rw [abs_of_nonneg (by positivity : 0 ≤ Λ N / 2)]
  have hE0 : 0 ≤ (4 * A + C₀) * N := by positivity
  have hmain : (4 * A + C₀) * N * u ^ 4 * Real.exp (-c' * u) ≤
      (4 * A + C₀) * K * N * Real.exp (-(c' / 2 * u)) := by
    calc (4 * A + C₀) * N * u ^ 4 * Real.exp (-c' * u)
        = (4 * A + C₀) * N * (u ^ 4 * Real.exp (-c' * u)) := by ring
      _ ≤ (4 * A + C₀) * N * (K * Real.exp (-(c' / 2 * u))) := by gcongr
      _ = (4 * A + C₀) * K * N * Real.exp (-(c' / 2 * u)) := by ring
  have hZ : Z + 1 ≤ (Z + 1) * (N * Real.exp (-(c' / 2 * u))) := by
    have := mul_le_mul_of_nonneg_left hNe1 (add_nonneg hZ0 zero_le_one)
    linarith only [this]
  have e : ((4 * A + C₀) * K + Z + 1 + K) * N * Real.exp (-(c' / 2 * u)) =
      (4 * A + C₀) * K * N * Real.exp (-(c' / 2 * u)) +
        (Z + 1) * (N * Real.exp (-(c' / 2 * u))) + K * N * Real.exp (-(c' / 2 * u)) := by ring
  rw [e]
  linarith only [hψ0, hmain, hZ, hΛ]

/-- `√(a + 1) ≤ √a + 1`. -/
lemma sqrt_add_one_le (a : ℝ) (ha : 0 ≤ a) : √(a + 1) ≤ √a + 1 := by
  rw [Real.sqrt_le_left (by positivity)]
  have := Real.sq_sqrt ha
  have := Real.sqrt_nonneg a
  nlinarith

/-- **Davenport, Ch. 18, p. 111, (1) (row 18-1)**: the prime number theorem with the classical
error term, `ψ(x) = x + O(x exp(-c √log x))`: there are `c, C > 0` with
`|ψ(x) - x| ≤ C x exp(-c √log x)` for all `x ≥ 2`. -/
@[kb "davenport1980" "Ch 18, p. 111"]
theorem Davenport.psi_sub_self_le :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ x : ℝ, 2 ≤ x →
      |Chebyshev.psi x - x| ≤ C * x * Real.exp (-(c * √(Real.log x))) := by
  obtain ⟨c, C, hc, hc2, hC, h⟩ := psi_natCast_sub_le
  have he := Real.exp_one_lt_d9
  have he0 := Real.exp_one_gt_d9
  refine ⟨c, C * Real.exp 1 + 1 + 20, hc, by positivity, fun x hx ↦ ?_⟩
  have hx0 : 0 < x := by linarith
  have hψ0 := Chebyshev.psi_nonneg x
  set E := Real.exp (-(c * √(Real.log x))) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have hlx0 : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  rcases lt_or_ge x 3 with hx3 | hx3
  · -- `2 ≤ x < 3`
    have h1 : Chebyshev.psi x ≤ (Real.log 4 + 4) * x := Chebyshev.psi_le_const_mul_self hx0.le
    have hl4 : Real.log 4 < 2 := by
      rw [Real.log_lt_iff_lt_exp (by norm_num)]
      have := Real.add_one_le_exp 2; have := Real.exp_one_gt_d9
      calc (4 : ℝ) < 2 + 1 + 1.5 := by norm_num
        _ ≤ Real.exp 2 := by
          rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]; nlinarith
    have hlx : Real.log x ≤ 4 := by
      have := Real.log_le_sub_one_of_pos hx0; linarith
    have hs : √(Real.log x) ≤ 2 := (Real.sqrt_le_left (by norm_num)).mpr (by linarith)
    have hEge : Real.exp (-1) ≤ E := by
      rw [hE]; apply Real.exp_le_exp.mpr
      have := Real.sqrt_nonneg (Real.log x)
      nlinarith
    have hinv : 1 ≤ Real.exp 1 * E := by
      calc (1 : ℝ) = Real.exp 1 * Real.exp (-1) := by rw [← Real.exp_add]; norm_num
        _ ≤ Real.exp 1 * E := by gcongr
    have hE3 : 1 / 3 ≤ E := by nlinarith
    have hxE := mul_le_mul_of_nonneg_left hE3 hx0.le
    have h0 : 0 ≤ (C * Real.exp 1 + 1) * x * E := by positivity
    have e : (C * Real.exp 1 + 1 + 20) * x * E = (C * Real.exp 1 + 1) * x * E + 20 * (x * E) := by
      ring
    rw [e, abs_le]
    have h4x : Real.log 4 * x ≤ 2 * x := mul_le_mul_of_nonneg_right hl4.le hx0.le
    constructor
    · linarith
    · linarith
  · -- `x ≥ 3`
    set N := ⌊x⌋₊ with hN
    have hN3 : 3 ≤ N := Nat.le_floor (by exact_mod_cast hx3)
    have hNx : (N : ℝ) ≤ x := Nat.floor_le hx0.le
    have hxN : x < N + 1 := Nat.lt_floor_add_one x
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    have hN3' : (3 : ℝ) ≤ N := by exact_mod_cast hN3
    have hψ : Chebyshev.psi x = Chebyshev.psi N := Chebyshev.psi_eq_psi_coe_floor x
    have hb := h N hN3
    -- `exp(-c √log N) ≤ e · exp(-c √log x)`
    have hlogxN : Real.log x ≤ Real.log N + 1 := by
      have : x ≤ 2 * N := by linarith
      have h2 : Real.log x ≤ Real.log (2 * N) := Real.log_le_log hx0 this
      rw [Real.log_mul two_ne_zero hN0.ne'] at h2
      have := Real.log_two_lt_d9
      linarith
    have hlN0 : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
    have hsq : √(Real.log x) ≤ √(Real.log N) + 1 :=
      (Real.sqrt_le_sqrt hlogxN).trans (sqrt_add_one_le _ hlN0)
    have hEN : Real.exp (-(c * √(Real.log N))) ≤ Real.exp 1 * E := by
      rw [hE, ← Real.exp_add]; apply Real.exp_le_exp.mpr
      have : c * √(Real.log x) ≤ c * √(Real.log N) + c := by nlinarith
      linarith
    -- `1 ≤ x E`
    have hlx1 : 1 ≤ Real.log x := by
      rw [Real.le_log_iff_exp_le hx0]; linarith
    have hxE : 1 ≤ x * E := by
      have : c * √(Real.log x) ≤ Real.log x := by
        have h1 : √(Real.log x) ≤ Real.log x := Real.sqrt_le_self_iff.mpr (Or.inr hlx1)
        have h2 : 0 ≤ √(Real.log x) := Real.sqrt_nonneg _
        nlinarith
      rw [hE]
      calc (1 : ℝ) ≤ Real.exp (Real.log x - c * √(Real.log x)) := Real.one_le_exp (by linarith)
        _ = x * Real.exp (-(c * √(Real.log x))) := by
          rw [sub_eq_add_neg, Real.exp_add, Real.exp_log hx0]
    rw [hψ]
    have h1 : |Chebyshev.psi N - x| ≤ |Chebyshev.psi N - N| + (x - N) := by
      have := abs_sub_le (Chebyshev.psi N) N x
      rw [abs_sub_comm (N : ℝ) x, abs_of_nonneg (by linarith : (0 : ℝ) ≤ x - N)] at this
      exact this
    have h2 : C * N * Real.exp (-(c * √(Real.log N))) ≤ C * Real.exp 1 * x * E := by
      calc C * N * Real.exp (-(c * √(Real.log N))) ≤ C * x * (Real.exp 1 * E) := by gcongr
        _ = C * Real.exp 1 * x * E := by ring
    have h3 : 0 ≤ 20 * x * E := by positivity
    have e : (C * Real.exp 1 + 1 + 20) * x * E = C * Real.exp 1 * x * E + x * E + 20 * x * E := by
      ring
    rw [e]
    linarith

end NTKB
