/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.PSeries
import NTKB.Analytic.Davenport.Hadamard.LogDeriv
import NTKB.Attr

/-!
# The Weierstrass product for `Γ` and the digamma series

**Davenport, Ch. 10, p. 73 and Ch. 12, p. 80 (row 12-8).** Weierstrass' product
`1/Γ(s) = s e^{γ s} ∏_{n ≥ 1} (1 + s/n) e^{-s/n}`, and its logarithmic derivative
`Γ'(s)/Γ(s) = -γ - 1/s + ∑_{n ≥ 1} (1/n - 1/(s + n))`, hence Davenport's
`Γ'(s/2 + 1)/(2 Γ(s/2 + 1)) = -γ/2 + ∑_{n ≥ 1} (1/(2n) - 1/(2n + s))`.

The product is the genus-one canonical product `canonicalProductOne` (Chapter 11) with zeros
`-1, -2, …`; it is identified with `1/Γ` through Euler's limit formula (Mathlib's
`Complex.GammaSeq_tendsto_Gamma`), so no growth estimate for `1/Γ` is needed.

As a consequence, `‖ψ(w) + 1/w‖ ≤ 3 + 2 log(‖w‖ + 1)` for `Re w ≥ 0`, `w ≠ 0`
(`norm_digamma_add_inv_le`): this is the form of Stirling's estimate used in Chapters 13 to 16.
-/

open Filter Topology Complex Set

namespace NTKB

/-- The zeros `-1, -2, -3, …` of the Weierstrass product for `1/Γ` (other than `0`). -/
noncomputable def gammaZeros (n : ℕ) : ℂ := -((n : ℂ) + 1)

lemma gammaZeros_ne_zero (n : ℕ) : gammaZeros n ≠ 0 := by
  unfold gammaZeros
  rw [neg_ne_zero]
  exact_mod_cast Nat.succ_ne_zero n

lemma norm_gammaZeros (n : ℕ) : ‖gammaZeros n‖ = (n : ℝ) + 1 := by
  unfold gammaZeros
  rw [norm_neg]
  exact_mod_cast Complex.norm_natCast (n + 1)

lemma summable_gammaZeros : Summable fun n : ℕ ↦ ‖gammaZeros n‖⁻¹ ^ 2 := by
  simp_rw [norm_gammaZeros]
  have := (summable_nat_add_iff 1).mpr ((Real.summable_one_div_nat_pow (p := 2)).mpr one_lt_two)
  refine this.congr fun n ↦ ?_
  push_cast
  rw [one_div, inv_pow]

lemma weierstrassFactorOne_div_gammaZeros (s : ℂ) (n : ℕ) :
    weierstrassFactorOne (s / gammaZeros n) =
      (s + (n + 1)) / (n + 1) * Complex.exp (-(s / (n + 1))) := by
  have h : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  unfold weierstrassFactorOne gammaZeros
  rw [div_neg, sub_neg_eq_add]
  congr 1
  field_simp
  ring

/-- The partial products of the Weierstrass product. -/
lemma prod_weierstrassFactorOne_gammaZeros (s : ℂ) (n : ℕ) :
    s * ∏ k ∈ Finset.range n, weierstrassFactorOne (s / gammaZeros k) =
      (∏ j ∈ Finset.range (n + 1), (s + j)) / n.factorial *
        Complex.exp (-(s * ∑ k ∈ Finset.range n, 1 / ((k : ℂ) + 1))) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    have hf : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
    rw [Finset.prod_range_succ, ← mul_assoc, ih, weierstrassFactorOne_div_gammaZeros,
      Finset.prod_range_succ (fun j : ℕ ↦ s + j) (n + 1), Finset.sum_range_succ, Nat.factorial_succ]
    push_cast
    simp only [mul_add, neg_add, Complex.exp_add]
    field_simp

/-- `s · P_n(s) · e^{γ s} · Γ_n(s) = e^{s(γ + log n - H_n)}`, where `Γ_n` is Euler's sequence. -/
lemma mul_prod_mul_GammaSeq {s : ℂ} (hs : ∀ m : ℕ, s ≠ -m) {n : ℕ} (hn : n ≠ 0) :
    s * Complex.exp (Real.eulerMascheroniConstant * s) *
        (∏ k ∈ Finset.range n, weierstrassFactorOne (s / gammaZeros k)) * GammaSeq s n =
      Complex.exp (s * (Real.eulerMascheroniConstant + Real.log n -
        ∑ k ∈ Finset.range n, 1 / ((k : ℂ) + 1))) := by
  have hP : ∏ j ∈ Finset.range (n + 1), (s + j) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro j _ h
    exact hs j (by linear_combination h)
  have hf : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have hpow : (n : ℂ) ^ s = Complex.exp (s * Real.log n) := by
    rw [Complex.cpow_def_of_ne_zero hn', Complex.ofReal_log (Nat.cast_nonneg n), mul_comm]
    simp
  rw [mul_comm s (Complex.exp _), mul_assoc (Complex.exp _), prod_weierstrassFactorOne_gammaZeros,
    GammaSeq, hpow]
  have : Complex.exp (s * (Real.eulerMascheroniConstant + Real.log n -
      ∑ k ∈ Finset.range n, 1 / ((k : ℂ) + 1))) =
      Complex.exp (Real.eulerMascheroniConstant * s) *
        Complex.exp (-(s * ∑ k ∈ Finset.range n, 1 / ((k : ℂ) + 1))) *
        Complex.exp (s * Real.log n) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    ring
  rw [this]
  field_simp

lemma tendsto_harmonic_sub_log_complex :
    Tendsto (fun n : ℕ ↦ (Real.eulerMascheroniConstant : ℂ) + Real.log n -
      ∑ k ∈ Finset.range n, 1 / ((k : ℂ) + 1)) atTop (𝓝 0) := by
  have h := Real.tendsto_harmonic_sub_log
  have h' : Tendsto (fun n : ℕ ↦ ((Real.eulerMascheroniConstant - (harmonic n - Real.log n) : ℝ) :
      ℂ)) atTop (𝓝 ((Real.eulerMascheroniConstant - Real.eulerMascheroniConstant : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.tendsto _).comp (tendsto_const_nhds.sub h)
  rw [sub_self, Complex.ofReal_zero] at h'
  refine h'.congr fun n ↦ ?_
  simp only [harmonic, one_div]
  push_cast
  ring

/-- **Weierstrass' product for `Γ`** (Davenport, Ch. 10, p. 73):
`1/Γ(s) = s e^{γ s} ∏_{n ≥ 1} (1 + s/n) e^{-s/n}`, for every complex `s` (both sides vanish at
`0, -1, -2, …`). -/
@[kb "davenport1980" "Ch 10, p. 73"]
theorem Davenport.Gamma_inv_eq_product (s : ℂ) :
    (Complex.Gamma s)⁻¹ =
      s * Complex.exp (Real.eulerMascheroniConstant * s) * canonicalProductOne gammaZeros s := by
  have hprod : Tendsto (fun n ↦ ∏ k ∈ Finset.range n, weierstrassFactorOne (s / gammaZeros k))
      atTop (𝓝 (canonicalProductOne gammaZeros s)) :=
    (hasProd_canonicalProductOne summable_gammaZeros s).tendsto_prod_nat
  by_cases hs : ∀ m : ℕ, s ≠ -m
  · have hΓ := Complex.Gamma_ne_zero hs
    have hlim : Tendsto (fun n ↦ s * Complex.exp (Real.eulerMascheroniConstant * s) *
        (∏ k ∈ Finset.range n, weierstrassFactorOne (s / gammaZeros k)) * GammaSeq s n) atTop
        (𝓝 (s * Complex.exp (Real.eulerMascheroniConstant * s) *
          canonicalProductOne gammaZeros s * Complex.Gamma s)) :=
      (tendsto_const_nhds.mul hprod).mul (Complex.GammaSeq_tendsto_Gamma s)
    have hlim' : Tendsto (fun n ↦ s * Complex.exp (Real.eulerMascheroniConstant * s) *
        (∏ k ∈ Finset.range n, weierstrassFactorOne (s / gammaZeros k)) * GammaSeq s n) atTop
        (𝓝 1) := by
      have h0 := ((tendsto_const_nhds (x := s)).mul tendsto_harmonic_sub_log_complex).cexp
      rw [mul_zero, Complex.exp_zero] at h0
      refine h0.congr' ?_
      filter_upwards [eventually_ne_atTop 0] with n hn
      exact (mul_prod_mul_GammaSeq hs hn).symm
    have := tendsto_nhds_unique hlim hlim'
    exact (eq_inv_of_mul_eq_one_left this).symm
  · push Not at hs
    obtain ⟨m, rfl⟩ := hs
    rw [Complex.Gamma_neg_nat_eq_zero, inv_zero]
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · have h0 : Tendsto (fun n ↦ ∏ k ∈ Finset.range n,
          weierstrassFactorOne (-(m : ℂ) / gammaZeros k)) atTop (𝓝 0) := by
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [eventually_ge_atTop m] with n hn
        symm
        rw [Finset.prod_eq_zero_iff]
        refine ⟨m - 1, Finset.mem_range.mpr (by omega), ?_⟩
        rw [weierstrassFactorOne_eq_zero_iff]
        unfold gammaZeros
        have : ((m - 1 : ℕ) : ℂ) + 1 = m := by
          rw [Nat.cast_sub (by omega)]; push_cast; ring
        rw [this, neg_div_neg_eq, div_self]
        exact_mod_cast hm.ne'
      rw [tendsto_nhds_unique hprod h0, mul_zero]

/-- The Weierstrass product `E(s) = s e^{γ s} ∏ (1 + s/n) e^{-s/n} = 1/Γ(s)`. -/
noncomputable def gammaInvProduct (s : ℂ) : ℂ :=
  s * Complex.exp (Real.eulerMascheroniConstant * s) * canonicalProductOne gammaZeros s

lemma Gamma_eq_inv_gammaInvProduct : Complex.Gamma = fun s ↦ (gammaInvProduct s)⁻¹ := by
  funext s
  rw [gammaInvProduct, ← Davenport.Gamma_inv_eq_product, inv_inv]

lemma differentiable_gammaInvProduct : Differentiable ℂ gammaInvProduct :=
  (differentiable_id.mul ((differentiable_id.const_mul _).cexp)).mul
    (differentiable_canonicalProductOne summable_gammaZeros)

/-- **The digamma series** (Davenport, Ch. 12, p. 80): for `s ∉ {0, -1, -2, …}`,
`Γ'(s)/Γ(s) = -γ - 1/s + ∑_{k ≥ 0} (1/(k + 1) - 1/(s + k + 1))`. -/
@[kb "davenport1980" "Ch 12, p. 80"]
theorem Davenport.digamma_eq_tsum {s : ℂ} (hs : ∀ m : ℕ, s ≠ -m) :
    Complex.digamma s = -Real.eulerMascheroniConstant - 1 / s +
      ∑' k : ℕ, (1 / ((k : ℂ) + 1) - 1 / (s + k + 1)) := by
  have hs0 : s ≠ 0 := by simpa using hs 0
  have hgz : ∀ k, gammaZeros k ≠ s := by
    intro k h
    exact hs (k + 1) (by rw [← h, gammaZeros]; push_cast; ring)
  have hE : gammaInvProduct s ≠ 0 := by
    intro h
    have := Complex.Gamma_ne_zero hs
    rw [Gamma_eq_inv_gammaInvProduct] at this
    simp [h] at this
  have hEd := (differentiable_gammaInvProduct s).hasDerivAt
  have hinv := hEd.inv hE
  rw [Complex.digamma_def, Gamma_eq_inv_gammaInvProduct, logDeriv_apply,
    show (fun s ↦ (gammaInvProduct s)⁻¹) = gammaInvProduct⁻¹ from rfl, hinv.deriv]
  -- the logarithmic derivative of the product
  have hl : logDeriv gammaInvProduct s =
      1 / s + (Real.eulerMascheroniConstant +
        ∑' k, (1 / (s - gammaZeros k) + 1 / gammaZeros k)) := by
    have h1 := logDeriv_exp_mul_canonicalProductOne summable_gammaZeros gammaZeros_ne_zero 0
      (Real.eulerMascheroniConstant : ℂ) hgz
    simp only [zero_add] at h1
    set g : ℂ → ℂ := fun z ↦
      Complex.exp (Real.eulerMascheroniConstant * z) * canonicalProductOne gammaZeros z with hg
    have hfun : gammaInvProduct = id * g := by
      funext z; simp [gammaInvProduct, hg, mul_assoc]
    have hg0 : g s ≠ 0 :=
      mul_ne_zero (Complex.exp_ne_zero _) (canonicalProductOne_ne_zero summable_gammaZeros hgz)
    have hgd : DifferentiableAt ℂ g s :=
      ((differentiable_id.const_mul _).cexp.mul
        (differentiable_canonicalProductOne summable_gammaZeros)) s
    rw [hfun, logDeriv_mul (f := id) (g := g) s hs0 hg0 differentiableAt_id hgd, logDeriv_id, h1]
  rw [logDeriv_apply] at hl
  have hsum : ∑' k, (1 / (s - gammaZeros k) + 1 / gammaZeros k) =
      -∑' k : ℕ, (1 / ((k : ℂ) + 1) - 1 / (s + k + 1)) := by
    rw [← tsum_neg]
    refine tsum_congr fun k ↦ ?_
    simp only [gammaZeros, sub_neg_eq_add, div_neg]
    ring_nf
  have key : -deriv gammaInvProduct s / gammaInvProduct s ^ 2 / (gammaInvProduct s)⁻¹ =
      -(deriv gammaInvProduct s / gammaInvProduct s) := by
    field_simp
  rw [key, hl, hsum]
  ring

/-- Davenport's form (Ch. 12, (8), row 12-8):
`Γ'(s/2 + 1)/(2 Γ(s/2 + 1)) = -γ/2 + ∑_{n ≥ 1} (1/(2n) - 1/(2n + s))`, for `s ∉ {-2, -4, …}`. -/
@[kb "davenport1980" "Ch 12, p. 80"]
theorem Davenport.digamma_half_add_one {s : ℂ} (hs : ∀ m : ℕ, s ≠ -(2 * ((m : ℂ) + 1))) :
    deriv Complex.Gamma (s / 2 + 1) / (2 * Complex.Gamma (s / 2 + 1)) =
      -Real.eulerMascheroniConstant / 2 +
        ∑' k : ℕ, (1 / (2 * ((k : ℂ) + 1)) - 1 / (2 * ((k : ℂ) + 1) + s)) := by
  have hd : deriv Complex.Gamma (s / 2 + 1) / (2 * Complex.Gamma (s / 2 + 1)) =
      Complex.digamma (s / 2 + 1) / 2 := by
    rw [Complex.digamma_def, logDeriv_apply]; ring
  rw [hd]
  rcases eq_or_ne s 0 with rfl | hs0
  · simp [Complex.digamma_one]
  have hw : ∀ m : ℕ, s / 2 ≠ -m := by
    intro m hm
    rcases m with _ | m
    · exact hs0 (by simpa using hm)
    · exact hs m (by push_cast at hm ⊢; linear_combination 2 * hm)
  rw [Complex.digamma_apply_add_one _ hw, Davenport.digamma_eq_tsum hw]
  have hterm : ∀ k : ℕ, (1 / (2 * ((k : ℂ) + 1)) - 1 / (2 * ((k : ℂ) + 1) + s)) =
      (1 / 2 : ℂ) * (1 / ((k : ℂ) + 1) - 1 / (s / 2 + k + 1)) := by
    intro k
    have h1 : (k : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
    have h2 : 2 * ((k : ℂ) + 1) + s ≠ 0 := fun h ↦ hs k (by linear_combination h)
    rw [show s / 2 + k + 1 = (2 * ((k : ℂ) + 1) + s) / 2 by ring, one_div_div]
    field_simp
  simp_rw [hterm]
  rw [tsum_mul_left]
  field_simp
  ring

/-- The terms of the digamma series are summable. -/
lemma summable_digamma_terms {s : ℂ} (hs : ∀ m : ℕ, s ≠ -m) :
    Summable fun k : ℕ ↦ (1 / ((k : ℂ) + 1) - 1 / (s + k + 1)) := by
  have hgz : ∀ k, gammaZeros k ≠ s := by
    intro k h
    exact hs (k + 1) (by rw [← h, gammaZeros]; push_cast; ring)
  refine (summable_inv_sub_add_inv summable_gammaZeros gammaZeros_ne_zero hgz).neg.congr
    fun k ↦ ?_
  simp only [gammaZeros, sub_neg_eq_add, div_neg]
  ring_nf

/-- At a natural number: `∑_{k ≥ 0} (1/(k + 1) - 1/(N + k + 1)) = H_N`. -/
lemma tsum_digamma_terms_nat (N : ℕ) :
    ∑' k : ℕ, (1 / ((k : ℂ) + 1) - 1 / ((N : ℂ) + k + 1)) = harmonic N := by
  rcases N with _ | N
  · simp
  have hN : ∀ m : ℕ, ((N + 1 : ℕ) : ℂ) ≠ -m := by
    intro m h
    have : ((N + 1 + m : ℕ) : ℂ) = 0 := by push_cast at h ⊢; linear_combination h
    exact_mod_cast (Nat.succ_add N m ▸ Nat.succ_ne_zero _ : N + 1 + m ≠ 0) (by exact_mod_cast this)
  have h := Davenport.digamma_eq_tsum hN
  have h' := Complex.digamma_nat_add_one N
  push_cast at h h'
  rw [h'] at h
  have : ∑' k : ℕ, (1 / ((k : ℂ) + 1) - 1 / ((N : ℂ) + 1 + k + 1)) =
      harmonic N + 1 / ((N : ℂ) + 1) := by linear_combination -h
  push_cast
  rw [this, harmonic_succ]
  push_cast
  ring

lemma digamma_term_real_nonneg_le {x : ℝ} (hx : 0 ≤ x) (k : ℕ) :
    0 ≤ 1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + 1 + x) ∧
      1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + 1 + x) ≤ x * (1 / ((k : ℝ) + 1) ^ 2) := by
  have hk : (0 : ℝ) < k + 1 := by positivity
  have hkx : (0 : ℝ) < k + 1 + x := by positivity
  have heq : 1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + 1 + x) = x / ((k + 1) * (k + 1 + x)) := by
    field_simp; ring
  rw [heq]
  refine ⟨by positivity, ?_⟩
  rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
  have : (k + 1 : ℝ) ^ 2 ≤ (k + 1) * (k + 1 + x) := by nlinarith
  exact mul_le_mul_of_nonneg_left this hx

lemma summable_digamma_terms_real {x : ℝ} (hx : 0 ≤ x) :
    Summable fun k : ℕ ↦ (1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + 1 + x)) := by
  have hs : Summable fun k : ℕ ↦ 1 / ((k : ℝ) + 1) ^ 2 := by
    have := (summable_nat_add_iff 1).mpr ((Real.summable_one_div_nat_pow (p := 2)).mpr one_lt_two)
    exact this.congr fun n ↦ by push_cast; rfl
  exact Summable.of_nonneg_of_le (fun k ↦ (digamma_term_real_nonneg_le hx k).1)
    (fun k ↦ (digamma_term_real_nonneg_le hx k).2) (hs.mul_left x)

/-- For real `x ≥ 0`: `∑_{k ≥ 0} (1/(k + 1) - 1/(k + 1 + x)) ≤ 1 + log(x + 1)`. -/
lemma tsum_digamma_terms_real_le {x : ℝ} (hx : 0 ≤ x) :
    ∑' k : ℕ, (1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + 1 + x)) ≤ 1 + Real.log (x + 1) := by
  set N := ⌈x⌉₊
  have hxN : x ≤ N := Nat.le_ceil x
  have hNx : (N : ℝ) ≤ x + 1 := (Nat.ceil_lt_add_one hx).le
  have hN0 : (0 : ℝ) ≤ N := N.cast_nonneg
  have hval : ∑' k : ℕ, (1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + 1 + N)) = harmonic N := by
    have h1 := tsum_digamma_terms_nat N
    have h2 : ((∑' k : ℕ, (1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + 1 + N)) : ℝ) : ℂ) =
        ∑' k : ℕ, (1 / ((k : ℂ) + 1) - 1 / ((N : ℂ) + k + 1)) := by
      rw [Complex.ofReal_tsum]
      refine tsum_congr fun k ↦ ?_
      push_cast; ring_nf
    rw [h1] at h2
    exact_mod_cast h2
  calc ∑' k : ℕ, (1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + 1 + x))
      ≤ ∑' k : ℕ, (1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + 1 + N)) := by
        refine (summable_digamma_terms_real hx).tsum_le_tsum (fun k ↦ ?_)
          (summable_digamma_terms_real hN0)
        have : 1 / ((k : ℝ) + 1 + N) ≤ 1 / ((k : ℝ) + 1 + x) :=
          one_div_le_one_div_of_le (by positivity) (by linarith)
        linarith
    _ = harmonic N := hval
    _ ≤ 1 + Real.log N := harmonic_le_one_add_log N
    _ ≤ 1 + Real.log (x + 1) := by
        rcases eq_or_lt_of_le hN0 with h | h
        · rw [← h, Real.log_zero]
          linarith [Real.log_nonneg (by linarith : (1 : ℝ) ≤ x + 1)]
        · linarith [Real.log_le_log h hNx]

lemma norm_digamma_term_le {w : ℂ} (hw : 0 ≤ w.re) (k : ℕ) :
    ‖1 / ((k : ℂ) + 1) - 1 / (w + k + 1)‖ ≤
      2 * (1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + 1 + ‖w‖)) := by
  have hk : (0 : ℝ) < k + 1 := by positivity
  have hre : (k : ℝ) + 1 ≤ (w + k + 1).re := by simp; linarith
  have h1 : (k : ℝ) + 1 ≤ ‖w + k + 1‖ := hre.trans (Complex.re_le_norm _)
  have h2 : ‖w‖ ≤ ‖w + k + 1‖ := by
    rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), Complex.sq_norm, Complex.sq_norm,
      Complex.normSq_apply, Complex.normSq_apply]
    simp only [add_re, natCast_re, one_re, add_im, natCast_im, one_im, add_zero]
    nlinarith
  have hpos : 0 < ‖w + k + 1‖ := hk.trans_le h1
  have hw0 : w + k + 1 ≠ 0 := norm_pos_iff.mp hpos
  have hk0 : (k : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  have heq : 1 / ((k : ℂ) + 1) - 1 / (w + k + 1) = w / (((k : ℂ) + 1) * (w + k + 1)) := by
    field_simp; ring
  have heq' : 1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + 1 + ‖w‖) = ‖w‖ / ((k + 1) * (k + 1 + ‖w‖)) := by
    field_simp; ring
  have hk1 : ‖(k : ℂ) + 1‖ = (k : ℝ) + 1 := by
    rw [show ((k : ℂ) + 1) = ((k + 1 : ℕ) : ℂ) by push_cast; rfl, Complex.norm_natCast]
    push_cast; rfl
  rw [heq, heq', norm_div, norm_mul, hk1]
  calc ‖w‖ / ((k + 1) * ‖w + k + 1‖) ≤ ‖w‖ / ((k + 1) * (k + 1 + ‖w‖) / 2) :=
        div_le_div_of_nonneg_left (norm_nonneg _) (by positivity) (by nlinarith)
    _ = 2 * (‖w‖ / ((k + 1) * (k + 1 + ‖w‖))) := by field_simp

/-- **Stirling-type bound for the digamma function**: for `Re w ≥ 0`, `w ≠ 0`,
`‖ψ(w) + 1/w‖ ≤ 3 + 2 log(‖w‖ + 1)`. -/
theorem norm_digamma_add_inv_le {w : ℂ} (hw : 0 ≤ w.re) (hw0 : w ≠ 0) :
    ‖Complex.digamma w + 1 / w‖ ≤ 3 + 2 * Real.log (‖w‖ + 1) := by
  have hpole : ∀ m : ℕ, w ≠ -m := by
    intro m h
    rcases m with _ | m
    · exact hw0 (by simpa using h)
    · have := congrArg Complex.re h
      simp at this
      linarith
  rw [Davenport.digamma_eq_tsum hpole]
  have hγ := Real.eulerMascheroniConstant_lt_two_thirds
  have hγ0 : 0 ≤ Real.eulerMascheroniConstant := by
    linarith [Real.one_half_lt_eulerMascheroniConstant]
  have hS := summable_digamma_terms_real (norm_nonneg w)
  have hb : ‖∑' k : ℕ, (1 / ((k : ℂ) + 1) - 1 / (w + k + 1))‖ ≤
      2 * (1 + Real.log (‖w‖ + 1)) := by
    refine (tsum_of_norm_bounded (hS.mul_left 2).hasSum (norm_digamma_term_le hw)).trans ?_
    rw [tsum_mul_left]
    gcongr
    exact tsum_digamma_terms_real_le (norm_nonneg w)
  calc ‖-(Real.eulerMascheroniConstant : ℂ) - 1 / w +
        ∑' k : ℕ, (1 / ((k : ℂ) + 1) - 1 / (w + k + 1)) + 1 / w‖
      = ‖-(Real.eulerMascheroniConstant : ℂ) +
          ∑' k : ℕ, (1 / ((k : ℂ) + 1) - 1 / (w + k + 1))‖ := by ring_nf
    _ ≤ ‖(Real.eulerMascheroniConstant : ℂ)‖ +
          ‖∑' k : ℕ, (1 / ((k : ℂ) + 1) - 1 / (w + k + 1))‖ := by
        rw [← norm_neg (Real.eulerMascheroniConstant : ℂ)]; exact norm_add_le _ _
    _ ≤ 1 + 2 * (1 + Real.log (‖w‖ + 1)) := by
        gcongr
        rw [Complex.norm_real, Real.norm_of_nonneg hγ0]; linarith
    _ = 3 + 2 * Real.log (‖w‖ + 1) := by ring

end NTKB
