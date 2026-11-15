/- Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license. -/
import NTKB.Analytic.Davenport.ThreePrimes.MajorArc

/-!
# The major arcs (Davenport, Chapter 26, p. 148)

**26-12** (formula (D)): with `P = (log N)^B`, `Q = N (log N)^{-B}`, the sum over the major arcs
`|α - a/q| ≤ 1/Q`, `1 ≤ a ≤ q ≤ P`, `(a, q) = 1`, of the integrals of `S(α)³ e(-Nα)` is
`∑_{q ≤ P} (μ(q)/φ(q)³) c_q(-N) ∫_{-1/Q}^{1/Q} T(β)³ e(-Nβ) dβ + O(N² exp(-c √log N))`
(`norm_majorArcs_integral_sub_le`): on each arc `S(α)³ = (μ(q)/φ(q))³ T(β)³ + O(N³ exp(-c √log N))`
by 26-11 (`norm_primeExpSum_major_sub_le`), the arcs have length `2/Q` and there are at most `P²`
of them, and `∑_{(a, q) = 1} e(-Na/q) = c_q(-N)`.
-/

open Finset Real
open scoped ArithmeticFunction.Moebius ArithmeticFunction.vonMangoldt

namespace NTKB.Davenport

lemma norm_primeExpSum_le_K (N : ℕ) (α : ℝ) : ‖primeExpSum N α‖ ≤ (Real.log 4 + 4) * N := by
  refine (norm_primeExpSum_le N α).trans ?_
  have h := Chebyshev.psi_le_const_mul_self (x := (N : ℝ)) (Nat.cast_nonneg N)
  have h2 : Chebyshev.psi (N : ℝ) = ∑ n ∈ Icc 1 N, Λ n := by
    unfold Chebyshev.psi
    rw [Nat.floor_natCast]
    rfl
  rw [h2] at h
  exact h

lemma sum_coprime_exp (q : ℕ) (hq : 0 < q) (N : ℕ) :
    ∑ a ∈ (Icc 1 q).filter (fun a ↦ Nat.Coprime a q),
      Complex.exp (-(2 * π * Complex.I * ((N : ℂ) * (((a : ℝ) / q : ℝ) : ℂ)))) =
    ramanujanSum q (-N) := by
  have hterm : ∀ a : ℕ, Complex.exp (-(2 * π * Complex.I * ((N : ℂ) * (((a : ℝ) / q : ℝ) : ℂ)))) =
      Complex.exp (2 * π * Complex.I * ((a : ℂ) * ((-(N : ℤ) : ℤ) : ℂ) / q)) := by
    intro a
    congr 1
    push_cast
    ring
  simp_rw [hterm]
  unfold ramanujanSum
  rcases Nat.lt_or_ge 1 q with h | h
  · congr 1
    ext a
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨lt_of_le_of_ne h2 ?_, h3⟩
      rintro rfl
      simp at h3
      omega
    · rintro ⟨h1, h3⟩
      refine ⟨⟨?_, h1.le⟩, h3⟩
      rcases Nat.eq_zero_or_pos a with rfl | h0
      · simp at h3; omega
      · exact h0
  · have : q = 1 := by omega
    subst this
    simp only [Nat.cast_one, div_one]
    have : Complex.exp (-(2 * π * Complex.I * (N : ℂ))) = 1 := by
      have := Complex.exp_int_mul_two_pi_mul_I (-(N : ℤ))
      rw [← this]; congr 1; push_cast; ring
    simpa using this

lemma poly_exp_bound (B b : ℝ) (hB : 0 < B) (hb : 0 < b) :
    ∃ D > 0, ∀ L : ℝ, 0 ≤ L → L ^ (3 * B) * (1 + L ^ B) * Real.exp (-b * √L) ≤ D := by
  set m : ℕ := ⌈4 * B⌉₊ with hm
  refine ⟨2 * ((2 * m).factorial / b ^ (2 * m) * Real.exp b) + 1, by positivity, ?_⟩
  intro L hL
  set x := √L with hx
  have hx0 : 0 ≤ x := Real.sqrt_nonneg _
  have hLx : L = x ^ 2 := (Real.sq_sqrt hL).symm
  have h1 : 1 ≤ 1 + L := by linarith
  have hLB : L ^ B ≤ (1 + L) ^ B := Real.rpow_le_rpow hL (by linarith) hB.le
  have hLB3 : L ^ (3 * B) ≤ (1 + L) ^ (3 * B) :=
    Real.rpow_le_rpow hL (by linarith) (by linarith)
  have h1B : 1 ≤ (1 + L) ^ B := Real.one_le_rpow h1 hB.le
  have hF : L ^ (3 * B) * (1 + L ^ B) ≤ 2 * (1 + L) ^ m := by
    have e1 : (1 + L) ^ (3 * B) * (1 + L) ^ B = (1 + L) ^ (4 * B) := by
      rw [← Real.rpow_add (by linarith)]; ring_nf
    have e2 : (1 + L) ^ (4 * B) ≤ (1 + L) ^ (m : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le h1 (Nat.le_ceil _)
    rw [Real.rpow_natCast] at e2
    have e3 : 1 ≤ (1 + L) ^ (3 * B) := Real.one_le_rpow h1 (by linarith)
    calc L ^ (3 * B) * (1 + L ^ B) ≤ (1 + L) ^ (3 * B) * (1 + (1 + L) ^ B) := by
          gcongr
      _ ≤ (1 + L) ^ (3 * B) * (2 * (1 + L) ^ B) := by gcongr; linarith
      _ = 2 * ((1 + L) ^ (3 * B) * (1 + L) ^ B) := by ring
      _ ≤ 2 * (1 + L) ^ m := by rw [e1]; linarith
  have h2 : (1 + L) ≤ (1 + x) ^ 2 := by nlinarith
  have h3 : (1 + L) ^ m ≤ (1 + x) ^ (2 * m) := by
    rw [pow_mul]; exact pow_le_pow_left₀ (by linarith) h2 m
  have h4 := Real.pow_div_factorial_le_exp (b * (1 + x)) (by positivity) (2 * m)
  have h5 : (1 + x) ^ (2 * m) ≤ (2 * m).factorial / b ^ (2 * m) * Real.exp (b * (1 + x)) := by
    rw [mul_pow, div_le_iff₀ (Nat.cast_pos.mpr (Nat.factorial_pos _))] at h4
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    calc (1 + x) ^ (2 * m) * b ^ (2 * m) = b ^ (2 * m) * (1 + x) ^ (2 * m) := by ring
      _ ≤ _ := by linarith
  have h6 : Real.exp (b * (1 + x)) * Real.exp (-b * x) = Real.exp b := by
    rw [← Real.exp_add]; ring_nf
  have hE : 0 < Real.exp (-b * x) := Real.exp_pos _
  calc L ^ (3 * B) * (1 + L ^ B) * Real.exp (-b * x)
      ≤ 2 * (1 + L) ^ m * Real.exp (-b * x) := mul_le_mul_of_nonneg_right hF hE.le
    _ ≤ 2 * ((2 * m).factorial / b ^ (2 * m) * Real.exp (b * (1 + x))) * Real.exp (-b * x) := by
        have := h3.trans h5
        gcongr
    _ = 2 * ((2 * m).factorial / b ^ (2 * m) * Real.exp b) := by
        rw [mul_assoc, mul_assoc, ← h6]
    _ ≤ _ := by linarith

lemma continuous_primeExpSum (N : ℕ) : Continuous (primeExpSum N) := by
  unfold primeExpSum
  fun_prop

lemma continuous_linearExpSum (N : ℕ) : Continuous (linearExpSum N) := by
  unfold linearExpSum
  fun_prop

lemma norm_mu_div_totient_le (q : ℕ) (hq : 0 < q) : ‖(μ q : ℂ) / (q.totient : ℂ)‖ ≤ 1 := by
  have h1 : (1 : ℝ) ≤ q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
  have h2 : |(μ q : ℝ)| ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  rw [norm_div]
  have : ‖(μ q : ℂ)‖ = |(μ q : ℝ)| := by simp
  rw [this]
  simp only [Complex.norm_natCast]
  rw [div_le_one (by linarith)]
  linarith

lemma arc_diff (N q a : ℕ) (hq : 0 < q) (X E : ℝ) (hX : 0 ≤ X)
    (hE : ∀ β : ℝ, |β| ≤ X →
      ‖primeExpSum N ((a : ℝ) / q + β) - (μ q : ℂ) / q.totient * linearExpSum N β‖ ≤ E) :
    ‖(∫ α in ((a : ℝ) / q - X)..((a : ℝ) / q + X),
        primeExpSum N α ^ 3 * Complex.exp (-(2 * π * Complex.I * (N * α)))) -
      Complex.exp (-(2 * π * Complex.I * ((N : ℂ) * (((a : ℝ) / q : ℝ) : ℂ)))) *
        ((μ q : ℂ) / (q.totient : ℂ)) ^ 3 *
        ∫ β in (-X)..X, linearExpSum N β ^ 3 * Complex.exp (-(2 * π * Complex.I * (N * β)))‖ ≤
      2 * X * (3 * (Real.log 4 + 4) ^ 2 * (N : ℝ) ^ 2 * E) := by
  set d : ℝ := (a : ℝ) / q with hd
  set c : ℂ := (μ q : ℂ) / (q.totient : ℂ) with hc
  set K : ℝ := Real.log 4 + 4 with hK
  have hK0 : 0 ≤ K := by have := Real.log_nonneg (show (1:ℝ) ≤ 4 by norm_num); rw [hK]; linarith
  have h1 : (∫ α in (d - X)..(d + X),
        primeExpSum N α ^ 3 * Complex.exp (-(2 * π * Complex.I * (N * α)))) =
      ∫ β in (-X)..X, primeExpSum N (d + β) ^ 3 *
        Complex.exp (-(2 * π * Complex.I * (N * ((d + β : ℝ) : ℂ)))) := by
    rw [intervalIntegral.integral_comp_add_left
      (fun α : ℝ => primeExpSum N α ^ 3 * Complex.exp (-(2 * π * Complex.I * (N * α)))) d]
    rw [← sub_eq_add_neg]
  have hcont1 : Continuous (fun β : ℝ => primeExpSum N (d + β) ^ 3 *
        Complex.exp (-(2 * π * Complex.I * (N * ((d + β : ℝ) : ℂ))))) := by
    have := continuous_primeExpSum N
    fun_prop
  have hcont2 : Continuous (fun β : ℝ => linearExpSum N β ^ 3 *
        Complex.exp (-(2 * π * Complex.I * (N * (β : ℂ))))) := by
    have := continuous_linearExpSum N
    fun_prop
  have hcont3 : Continuous (fun β : ℝ =>
      Complex.exp (-(2 * π * Complex.I * ((N : ℂ) * (d : ℂ)))) * c ^ 3 *
        (linearExpSum N β ^ 3 * Complex.exp (-(2 * π * Complex.I * (N * (β : ℂ)))))) :=
    continuous_const.mul hcont2
  rw [h1, ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub
    (hcont1.intervalIntegrable _ _) (hcont3.intervalIntegrable _ _)]
  have hb : ∀ β ∈ Set.uIoc (-X) X, ‖primeExpSum N (d + β) ^ 3 *
        Complex.exp (-(2 * π * Complex.I * (N * ((d + β : ℝ) : ℂ)))) -
      Complex.exp (-(2 * π * Complex.I * ((N : ℂ) * (d : ℂ)))) * c ^ 3 *
        (linearExpSum N β ^ 3 * Complex.exp (-(2 * π * Complex.I * (N * (β : ℂ)))))‖ ≤
      3 * K ^ 2 * (N : ℝ) ^ 2 * E := by
    intro β hβ
    have hβ' : |β| ≤ X := by
      rw [Set.uIoc_of_le (by linarith)] at hβ
      exact abs_le.mpr ⟨hβ.1.le, hβ.2⟩
    set S := primeExpSum N (d + β) with hS
    set V := c * linearExpSum N β with hV
    have hexp : Complex.exp (-(2 * π * Complex.I * (N * ((d + β : ℝ) : ℂ)))) =
        Complex.exp (-(2 * π * Complex.I * ((N : ℂ) * (d : ℂ)))) *
          Complex.exp (-(2 * π * Complex.I * (N * (β : ℂ)))) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    have hrw : primeExpSum N (d + β) ^ 3 *
        Complex.exp (-(2 * π * Complex.I * (N * ((d + β : ℝ) : ℂ)))) -
      Complex.exp (-(2 * π * Complex.I * ((N : ℂ) * (d : ℂ)))) * c ^ 3 *
        (linearExpSum N β ^ 3 * Complex.exp (-(2 * π * Complex.I * (N * (β : ℂ))))) =
        (S ^ 3 - V ^ 3) * Complex.exp (-(2 * π * Complex.I * (N * ((d + β : ℝ) : ℂ)))) := by
      rw [hexp, hV]; ring
    rw [hrw, norm_mul, Complex.norm_exp]
    have hre : (-(2 * π * Complex.I * ((N : ℂ) * ((d + β : ℝ) : ℂ)))).re = 0 := by
      simp
    rw [hre, Real.exp_zero, mul_one]
    have hSK : ‖S‖ ≤ K * N := norm_primeExpSum_le_K N _
    have hVN : ‖V‖ ≤ N := by
      rw [hV, norm_mul]
      calc ‖c‖ * ‖linearExpSum N β‖ ≤ 1 * N :=
            mul_le_mul (norm_mu_div_totient_le q hq) (norm_linearExpSum_le N β)
              (norm_nonneg _) zero_le_one
        _ = N := one_mul _
    have hN1 : (N : ℝ) ≤ K * N := by
      have : (1 : ℝ) ≤ K := by
        rw [hK]; have := Real.log_nonneg (show (1:ℝ) ≤ 4 by norm_num); linarith
      nlinarith [(Nat.cast_nonneg N : (0:ℝ) ≤ N)]
    have hVK : ‖V‖ ≤ K * N := hVN.trans hN1
    have hfac : S ^ 3 - V ^ 3 = (S - V) * (S ^ 2 + S * V + V ^ 2) := by ring
    rw [hfac, norm_mul]
    have hsum : ‖S ^ 2 + S * V + V ^ 2‖ ≤ 3 * (K * N) ^ 2 := by
      calc ‖S ^ 2 + S * V + V ^ 2‖ ≤ ‖S ^ 2 + S * V‖ + ‖V ^ 2‖ := norm_add_le _ _
        _ ≤ ‖S ^ 2‖ + ‖S * V‖ + ‖V ^ 2‖ := by gcongr; exact norm_add_le _ _
        _ ≤ (K * N) ^ 2 + (K * N) * (K * N) + (K * N) ^ 2 := by
          rw [norm_pow, norm_mul, norm_pow]
          gcongr
        _ = 3 * (K * N) ^ 2 := by ring
    have hSV := hE β hβ'
    have : ‖S - V‖ ≤ E := hSV
    calc ‖S - V‖ * ‖S ^ 2 + S * V + V ^ 2‖ ≤ E * (3 * (K * N) ^ 2) :=
          mul_le_mul this hsum (norm_nonneg _) ((norm_nonneg _).trans this)
      _ = 3 * K ^ 2 * (N : ℝ) ^ 2 * E := by ring
  have := intervalIntegral.norm_integral_le_of_norm_le_const hb
  calc _ ≤ _ := this
    _ = 2 * X * (3 * K ^ 2 * (N : ℝ) ^ 2 * E) := by
      rw [abs_of_nonneg (by linarith)]; ring

/-- **Davenport, Ch. 26, p. 148, (D) (row 26-12)**: with `P = (log N)^B`, `Q = N (log N)^{-B}`,
the sum over the major arcs of the integrals of `S(α)³ e(-Nα)` is
`∑_{q ≤ P} (μ(q)/φ(q)³) c_q(-N) ∫_{-1/Q}^{1/Q} T(β)³ e(-Nβ) dβ + O(N² exp(-c √log N))`. -/
@[kb "davenport1980" "Ch 26, p. 148, (D)"]
theorem norm_majorArcs_integral_sub_le (B : ℝ) (hB : 0 < B) :
    ∃ c > 0, ∃ C > 0, ∀ N : ℕ, 2 ≤ N →
      ‖(∑ q ∈ Icc 1 ⌊Real.log N ^ B⌋₊, ∑ a ∈ (Icc 1 q).filter (fun a ↦ Nat.Coprime a q),
          ∫ α in ((a : ℝ) / q - Real.log N ^ B / N)..((a : ℝ) / q + Real.log N ^ B / N),
            primeExpSum N α ^ 3 * Complex.exp (-(2 * π * Complex.I * (N * α)))) -
        ∑ q ∈ Icc 1 ⌊Real.log N ^ B⌋₊, (μ q : ℂ) / (q.totient : ℂ) ^ 3 * ramanujanSum q (-N) *
          ∫ β in (-(Real.log N ^ B / N))..(Real.log N ^ B / N),
            linearExpSum N β ^ 3 * Complex.exp (-(2 * π * Complex.I * (N * β)))‖ ≤
        C * N ^ 2 * Real.exp (-c * √(Real.log N)) := by
  obtain ⟨c, hc, C, hC, h⟩ := norm_primeExpSum_major_sub_le B hB
  obtain ⟨D, hD, hDb⟩ := poly_exp_bound B (c / 2) hB (by positivity)
  set K : ℝ := Real.log 4 + 4 with hK
  have hK0 : 0 ≤ K := by
    have := Real.log_nonneg (show (1:ℝ) ≤ 4 by norm_num); rw [hK]; linarith
  refine ⟨c / 2, by positivity, 6 * K ^ 2 * C * D, by positivity, ?_⟩
  intro N hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hL : 0 < Real.log N := Real.log_pos (by linarith)
  set L := Real.log N with hLdef
  set P : ℝ := L ^ B with hP
  have hP0 : 0 ≤ P := by positivity
  set M : ℕ := ⌊P⌋₊ with hM
  have hMP : (M : ℝ) ≤ P := Nat.floor_le hP0
  set x := √L with hx
  set E : ℝ := C * (1 + P) * N * Real.exp (-c * x) with hEdef
  set X : ℝ := P / N with hXdef
  have hX0 : 0 ≤ X := by positivity
  have hmu : ∀ q : ℕ, (μ q : ℂ) ^ 3 = μ q := by
    intro q
    rcases ArithmeticFunction.moebius_eq_or q with h | h | h <;> simp [h] <;> norm_num
  -- rewrite the main part
  have hmain : ∀ q ∈ Icc 1 M,
      (μ q : ℂ) / (q.totient : ℂ) ^ 3 * ramanujanSum q (-N) *
          ∫ β in (-(L ^ B / N))..(L ^ B / N),
            linearExpSum N β ^ 3 * Complex.exp (-(2 * π * Complex.I * (N * β))) =
      ∑ a ∈ (Icc 1 q).filter (fun a ↦ Nat.Coprime a q),
        Complex.exp (-(2 * π * Complex.I * ((N : ℂ) * (((a : ℝ) / q : ℝ) : ℂ)))) *
          ((μ q : ℂ) / (q.totient : ℂ)) ^ 3 *
          ∫ β in (-X)..X, linearExpSum N β ^ 3 * Complex.exp (-(2 * π * Complex.I * (N * β))) := by
    intro q hq
    have hq0 : 0 < q := (Finset.mem_Icc.mp hq).1
    have h3 : ((μ q : ℂ) / (q.totient : ℂ)) ^ 3 = (μ q : ℂ) / (q.totient : ℂ) ^ 3 := by
      rw [div_pow, hmu]
    rw [← sum_coprime_exp q hq0 N, ← Finset.sum_mul, ← Finset.sum_mul, hXdef, hP, h3]
    ring
  rw [Finset.sum_congr rfl hmain, ← Finset.sum_sub_distrib]
  have hterm : ∀ q ∈ Icc 1 M, ∀ a ∈ (Icc 1 q).filter (fun a ↦ Nat.Coprime a q),
      ‖(∫ α in ((a : ℝ) / q - L ^ B / N)..((a : ℝ) / q + L ^ B / N),
            primeExpSum N α ^ 3 * Complex.exp (-(2 * π * Complex.I * (N * α)))) -
        Complex.exp (-(2 * π * Complex.I * ((N : ℂ) * (((a : ℝ) / q : ℝ) : ℂ)))) *
          ((μ q : ℂ) / (q.totient : ℂ)) ^ 3 *
          ∫ β in (-X)..X, linearExpSum N β ^ 3 * Complex.exp (-(2 * π * Complex.I * (N * β)))‖ ≤
        2 * X * (3 * K ^ 2 * (N : ℝ) ^ 2 * E) := by
    intro q hq a ha
    have hq0 : 0 < q := (Finset.mem_Icc.mp hq).1
    have hqM : q ≤ M := (Finset.mem_Icc.mp hq).2
    have hqP : (q : ℝ) ≤ P := (Nat.cast_le.mpr hqM).trans hMP
    have hcop : IsCoprime (a : ℤ) (q : ℤ) :=
      Nat.isCoprime_iff_coprime.mpr (Finset.mem_filter.mp ha).2
    exact arc_diff N q a hq0 X E hX0 (fun β hβ => by
      have h1 := h N hN q hq0 hqP a hcop β
      simp only [Int.cast_natCast] at h1
      refine h1.trans ?_
      have : (N : ℝ) * |β| ≤ P := by
        calc (N : ℝ) * |β| ≤ N * X := by gcongr
          _ = P := by rw [hXdef]; field_simp
      rw [hEdef]
      gcongr)
  have hsum : ∑ q ∈ Icc 1 M, ∑ a ∈ (Icc 1 q).filter (fun a ↦ Nat.Coprime a q),
      ‖(∫ α in ((a : ℝ) / q - L ^ B / N)..((a : ℝ) / q + L ^ B / N),
            primeExpSum N α ^ 3 * Complex.exp (-(2 * π * Complex.I * (N * α)))) -
        Complex.exp (-(2 * π * Complex.I * ((N : ℂ) * (((a : ℝ) / q : ℝ) : ℂ)))) *
          ((μ q : ℂ) / (q.totient : ℂ)) ^ 3 *
          ∫ β in (-X)..X, linearExpSum N β ^ 3 * Complex.exp (-(2 * π * Complex.I * (N * β)))‖ ≤
      (M : ℝ) * M * (2 * X * (3 * K ^ 2 * (N : ℝ) ^ 2 * E)) := by
    have hB1 : 0 ≤ 2 * X * (3 * K ^ 2 * (N : ℝ) ^ 2 * E) := by positivity
    calc _ ≤ ∑ q ∈ Icc 1 M, ∑ a ∈ (Icc 1 q).filter (fun a ↦ Nat.Coprime a q),
          2 * X * (3 * K ^ 2 * (N : ℝ) ^ 2 * E) :=
          Finset.sum_le_sum (fun q hq => Finset.sum_le_sum (fun a ha => hterm q hq a ha))
      _ ≤ ∑ q ∈ Icc 1 M, (M : ℝ) * (2 * X * (3 * K ^ 2 * (N : ℝ) ^ 2 * E)) := by
          refine Finset.sum_le_sum (fun q hq => ?_)
          rw [Finset.sum_const, nsmul_eq_mul]
          refine mul_le_mul_of_nonneg_right ?_ hB1
          have h1 : ((Icc 1 q).filter (fun a ↦ Nat.Coprime a q)).card ≤ q := by
            calc _ ≤ (Icc 1 q).card := Finset.card_filter_le _ _
              _ = q := by simp
          exact_mod_cast h1.trans (Finset.mem_Icc.mp hq).2
      _ = (M : ℝ) * M * (2 * X * (3 * K ^ 2 * (N : ℝ) ^ 2 * E)) := by
          rw [Finset.sum_const, nsmul_eq_mul]; simp; ring
  simp only [← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_sum (fun q _ => norm_sum_le _ _)).trans ?_
  refine hsum.trans ?_
  -- final arithmetic
  have hDb' := hDb L hL.le
  have hP3 : L ^ (3 * B) = P ^ 3 := by
    rw [hP, ← Real.rpow_natCast, ← Real.rpow_mul hL.le]; ring_nf
  rw [hP3] at hDb'
  have he : Real.exp (-c * x) = Real.exp (-(c / 2) * x) * Real.exp (-(c / 2) * x) := by
    rw [← Real.exp_add]; ring_nf
  have he2 : 0 < Real.exp (-(c / 2) * x) := Real.exp_pos _
  have hMM : (M : ℝ) * M ≤ P * P := by gcongr
  have key : (M : ℝ) * M * (2 * X * (3 * K ^ 2 * (N : ℝ) ^ 2 * E)) =
      6 * K ^ 2 * C * (N : ℝ) ^ 2 * ((M : ℝ) * M * P * (1 + P)) * Real.exp (-c * x) := by
    rw [hEdef, hXdef]; field_simp; ring
  rw [key]
  have h3 : (M : ℝ) * M * P * (1 + P) ≤ P ^ 3 * (1 + P) := by
    have : (M : ℝ) * M * P ≤ P * P * P := by gcongr
    calc _ ≤ P * P * P * (1 + P) := by gcongr
      _ = _ := by ring
  have h4 : (M : ℝ) * M * P * (1 + P) * Real.exp (-c * x) ≤ D * Real.exp (-(c / 2) * x) := by
    rw [he, ← mul_assoc]
    calc _ ≤ (P ^ 3 * (1 + P)) * Real.exp (-(c / 2) * x) * Real.exp (-(c / 2) * x) := by gcongr
      _ ≤ D * Real.exp (-(c / 2) * x) := by gcongr
  calc 6 * K ^ 2 * C * (N : ℝ) ^ 2 * ((M : ℝ) * M * P * (1 + P)) * Real.exp (-c * x)
      = 6 * K ^ 2 * C * (N : ℝ) ^ 2 * ((M : ℝ) * M * P * (1 + P) * Real.exp (-c * x)) := by ring
    _ ≤ 6 * K ^ 2 * C * (N : ℝ) ^ 2 * (D * Real.exp (-(c / 2) * x)) := by gcongr
    _ = _ := by ring

end NTKB.Davenport
