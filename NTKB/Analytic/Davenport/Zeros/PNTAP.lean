/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Davenport.Zeros.APDecomp

/-!
# The prime number theorem for arithmetic progressions

**Davenport, Ch. 20, p. 123, (9) (row 20-5).** For every `C > 0` there are `c, A > 0` such that,
uniformly for `log q ≤ C √log N` and `a` prime to `q`,
`ψ(N; q, a) = N/φ(q) - (1/φ(q)) ∑_χ χ̄(a) E(N, χ) + O(N exp(-c √log N))`,
where `E(N, χ) = ∑ N^ρ/ρ` over the exceptional zeros (14-11) of the primitive character `χ*`
inducing `χ` (empty unless `χ*` is real; by Landau, 14-13, at most one `χ` contributes, and then
`E = N^{β₁}/β₁`).
-/

open Filter Topology Complex Set DirichletCharacter
open scoped Real ArithmeticFunction.vonMangoldt

namespace NTKB

open scoped Classical in
/-- `E(N, χ) = ∑ N^ρ/ρ` over the exceptional zeros of the primitive character inducing `χ`. -/
noncomputable def excTerm {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (N : ℕ) : ℂ :=
  haveI : NeZero χ.conductor := ⟨conductor_ne_zero χ⟩
  if h : χ.conductor ≠ 1 then
    ∑ ρ ∈ (zerosBelowL (primitiveCharacter_isPrimitive χ) h 1).filter
      (fun ρ ↦ IsExcPoint χ.conductor ρ.val), perronKernel N ρ.val
  else 0

/-- `u⁴ ≤ K N e^{-c u}` for `u = √log N ≥ 1` and `0 < c ≤ 1/2`. -/
lemma pow_four_le_mul_exp {c u : ℝ} (hc : 0 < c) (hc2 : c ≤ 1 / 2) (hu : 1 ≤ u) :
    u ^ 4 ≤ 24 * (2 / c) ^ 4 * (Real.exp (u ^ 2) * Real.exp (-(c * u))) := by
  have h1 := pow_four_le_exp hc (by linarith : (0 : ℝ) ≤ u)
  refine h1.trans ?_
  gcongr
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith

open scoped Classical in
set_option maxHeartbeats 4000000 in
/-- **Davenport, Ch. 20, p. 123, (9) (row 20-5)**, for integers `N ≥ 3` (see the module docstring
for the form of the exceptional term). -/
@[kb "davenport1980" "Ch 20, p. 123"]
theorem Davenport.psiAP_sub_le (C : ℝ) (hC : 0 < C) :
    ∃ c A : ℝ, 0 < c ∧ 0 < A ∧ ∀ {q : ℕ} [NeZero q] {a : ZMod q}, IsUnit a →
      ∀ N : ℕ, 3 ≤ N → Real.log q ≤ C * √(Real.log N) →
      ‖(psiAP a N : ℂ) - N / q.totient +
          (q.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q, χ a⁻¹ * excTerm χ N‖ ≤
        A * N * Real.exp (-(c * √(Real.log N))) := by
  obtain ⟨c₁, C₁, hc₁, hC₁, h₁⟩ := Davenport.psi_sub_self_le
  obtain ⟨c₄, A₄, hc₄, hA₄, h₄⟩ := Davenport.psi0L_sub_exceptional_le C hC
  set c := min (min c₁ c₄) (1 / 2) with hcdef
  have hc0 : 0 < c := lt_min (lt_min hc₁ hc₄) one_half_pos
  have hcc₁ : c ≤ c₁ := (min_le_left _ _).trans (min_le_left _ _)
  have hcc₄ : c ≤ c₄ := (min_le_left _ _).trans (min_le_right _ _)
  have hc2 : c ≤ 1 / 2 := min_le_right _ _
  set K := 24 * (2 / c) ^ 4 with hK
  have hK0 : 0 < K := by positivity
  have hl2 := log_two_gt_two_thirds
  refine ⟨c, C₁ + A₄ + K * (3 * C + 2), hc0, by positivity, ?_⟩
  intro q _ a ha N hN hqN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast (by omega : 2 ≤ N)
  set L := Real.log N with hL
  have hL1 : 1 < L := by
    rw [hL, Real.lt_log_iff_exp_lt hN0]
    have := Real.exp_one_lt_d9
    have : (3 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  set u := √L with hu
  have hu2 : u ^ 2 = L := Real.sq_sqrt (by linarith)
  have hu1 : 1 < u := by rw [hu, Real.lt_sqrt zero_le_one]; linarith
  have hlq : 0 ≤ Real.log q := Real.log_natCast_nonneg q
  set E := Real.exp (-(c * u)) with hE
  have hE0 : 0 < E := Real.exp_pos _
  -- the common error `B`
  set B := L / Real.log 2 * Real.log q * 2 + L + (C₁ + A₄) * N * E with hB
  -- the principal character
  have hprin : ‖psiL (1 : DirichletCharacter ℂ q) N - N‖ ≤ B := by
    have h1 := Davenport.norm_psiL_one_sub_psi_le (q := q) hN1
    have h2 := h₁ N hN2
    have h3 : Real.exp (-(c₁ * u)) ≤ E := Real.exp_le_exp.mpr (by nlinarith)
    have h4 : ‖(Chebyshev.psi N : ℂ) - N‖ ≤ C₁ * N * E := by
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      refine h2.trans ?_
      rw [← hL, ← hu]
      gcongr
    have hsplit : psiL (1 : DirichletCharacter ℂ q) N - N =
        (psiL (1 : DirichletCharacter ℂ q) N - Chebyshev.psi N) + ((Chebyshev.psi N : ℂ) - N) := by
      ring
    rw [hsplit]
    refine (norm_add_le _ _).trans ?_
    have : 0 ≤ L / Real.log 2 * Real.log q := by
      have : 0 ≤ L := by linarith
      positivity
    have : 0 ≤ A₄ * N * E := by positivity
    have e : B = L / Real.log 2 * Real.log q * 2 + L + (C₁ + A₄) * N * E := rfl
    rw [e]
    have hL0 : 0 ≤ L := by linarith
    nlinarith
  -- the nonprincipal characters
  have hnon : ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → ‖psiL χ N + excTerm χ N‖ ≤ B := by
    intro χ hχ
    have hcond : χ.conductor ≠ 1 := fun h ↦ hχ (eq_one_iff_conductor_eq_one.mpr h)
    haveI : NeZero χ.conductor := ⟨conductor_ne_zero χ⟩
    have hprim := primitiveCharacter_isPrimitive χ
    have hcq : (χ.conductor : ℝ) ≤ q := by
      exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) χ.conductor_dvd_level
    have hlc : Real.log χ.conductor ≤ C * √(Real.log N) := by
      refine le_trans ?_ hqN
      apply Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero (conductor_ne_zero χ)) hcq
    have h1 := Davenport.norm_psiL_sub_primitive_le χ hN1
    have h2 := h₄ hprim hcond N hN hlc
    have hexc : excTerm χ N = ∑ ρ ∈ (zerosBelowL hprim hcond 1).filter
        (fun ρ ↦ IsExcPoint χ.conductor ρ.val), perronKernel N ρ.val := by
      simp only [excTerm, dif_pos hcond]
    have h3 := psiL_natCast_eq χ.primitiveCharacter N
    have hsplit : psiL χ N + excTerm χ N = (psiL χ N - psiL χ.primitiveCharacter N) +
        χ.primitiveCharacter N * Λ N / 2 +
        (psi0L χ.primitiveCharacter N + ∑ ρ ∈ (zerosBelowL hprim hcond 1).filter
          (fun ρ ↦ IsExcPoint χ.conductor ρ.val), perronKernel N ρ.val) := by
      rw [hexc, h3]; ring
    rw [hsplit]
    have hΛ : ‖χ.primitiveCharacter N * Λ N / 2‖ ≤ L := by
      rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg, Complex.norm_two]
      have := DirichletCharacter.norm_le_one χ.primitiveCharacter N
      have h5 : Λ N ≤ L := ArithmeticFunction.vonMangoldt_le_log
      have h6 := ArithmeticFunction.vonMangoldt_nonneg (n := N)
      have : ‖χ.primitiveCharacter N‖ * Λ N ≤ L := by nlinarith [norm_nonneg (χ.primitiveCharacter N)]
      linarith
    have h4 : A₄ * N * Real.exp (-(c₄ * √(Real.log N))) ≤ A₄ * N * E := by
      have h7 : Real.exp (-(c₄ * √(Real.log N))) ≤ E := by
        rw [hE, ← hL, ← hu]
        apply Real.exp_le_exp.mpr
        have := mul_le_mul_of_nonneg_right hcc₄ (le_of_lt (by linarith : (0 : ℝ) < u))
        linarith
      exact mul_le_mul_of_nonneg_left h7 (by positivity)
    calc ‖(psiL χ N - psiL χ.primitiveCharacter N) + χ.primitiveCharacter N * Λ N / 2 +
          (psi0L χ.primitiveCharacter N + ∑ ρ ∈ (zerosBelowL hprim hcond 1).filter
            (fun ρ ↦ IsExcPoint χ.conductor ρ.val), perronKernel N ρ.val)‖
        ≤ ‖psiL χ N - psiL χ.primitiveCharacter N‖ + ‖χ.primitiveCharacter N * Λ N / 2‖ +
          ‖psi0L χ.primitiveCharacter N + ∑ ρ ∈ (zerosBelowL hprim hcond 1).filter
            (fun ρ ↦ IsExcPoint χ.conductor ρ.val), perronKernel N ρ.val‖ :=
          (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ L / Real.log 2 * Real.log q + L + A₄ * N * E := by
          rw [← hL] at h1
          linarith
      _ ≤ B := by
          have : 0 ≤ L / Real.log 2 * Real.log q := by
            have : 0 ≤ L := by linarith
            positivity
          have : 0 ≤ C₁ * N * E := by positivity
          simp only [B]; nlinarith
  -- orthogonality
  set D : DirichletCharacter ℂ q → ℂ := fun χ ↦
    psiL χ N + excTerm χ N - (if χ = 1 then (N : ℂ) else 0) with hD
  have hD : ∀ χ, ‖D χ‖ ≤ B := by
    intro χ
    by_cases h : χ = 1
    · have he : excTerm χ N = 0 := by
        have hc1 : χ.conductor = 1 := eq_one_iff_conductor_eq_one.mp h
        simp [excTerm, hc1]
      simp only [D, h, if_true]
      rw [show excTerm (1 : DirichletCharacter ℂ q) N = 0 by rw [← h]; exact he, add_zero]
      exact hprin
    · simp only [D, h, if_false, sub_zero]
      exact hnon χ h
  have hsum1 : ∑ χ : DirichletCharacter ℂ q, χ a⁻¹ * (if χ = 1 then (N : ℂ) else 0) = N := by
    rw [Finset.sum_eq_single 1 (fun χ _ hχ ↦ by simp [hχ]) (by simp)]
    have hinv : IsUnit a⁻¹ := by
      rw [← ha.unit_spec, ZMod.inv_coe_unit]; exact Units.isUnit _
    simp [MulChar.one_apply hinv]
  have hφ : (q.totient : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))).ne'
  have hcard : (Finset.univ : Finset (DirichletCharacter ℂ q)).card = q.totient := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card,
      DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity]
  have hid : (psiAP a N : ℂ) - N / q.totient +
      (q.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q, χ a⁻¹ * excTerm χ N =
      (q.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q, χ a⁻¹ * D χ := by
    rw [Davenport.psiAP_eq ha]
    simp only [D, mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib, hsum1]
    have : (q.totient : ℂ) ≠ 0 := by exact_mod_cast hφ
    field_simp
    ring
  rw [hid]
  have hbound : ‖∑ χ : DirichletCharacter ℂ q, χ a⁻¹ * D χ‖ ≤ q.totient * B := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ χ : DirichletCharacter ℂ q, ‖χ a⁻¹ * D χ‖ ≤ ∑ χ : DirichletCharacter ℂ q, B := by
          refine Finset.sum_le_sum fun χ _ ↦ ?_
          rw [norm_mul]
          have := DirichletCharacter.norm_le_one χ a⁻¹
          calc ‖χ a⁻¹‖ * ‖D χ‖ ≤ 1 * B := mul_le_mul this (hD χ) (norm_nonneg _) zero_le_one
            _ = B := one_mul B
      _ = q.totient * B := by rw [Finset.sum_const, hcard, nsmul_eq_mul]
  have hφpos : (0 : ℝ) < q.totient := lt_of_le_of_ne (Nat.cast_nonneg _) (Ne.symm hφ)
  have h5 : ‖(q.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q, χ a⁻¹ * D χ‖ ≤ B := by
    rw [norm_mul, norm_inv, Complex.norm_natCast]
    calc (q.totient : ℝ)⁻¹ * ‖∑ χ : DirichletCharacter ℂ q, χ a⁻¹ * D χ‖
        ≤ (q.totient : ℝ)⁻¹ * (q.totient * B) := by gcongr
      _ = B := by field_simp
  refine h5.trans ?_
  -- `B ≤ A N e^{-c u}`
  have hu4 := pow_four_le_mul_exp hc0 hc2 hu1.le
  rw [← hK, hu2] at hu4
  have hNexp : Real.exp L = N := by rw [hL, Real.exp_log hN0]
  rw [hNexp] at hu4
  have hlogq : Real.log q ≤ C * u := hqN
  have hLu : L ≤ u ^ 4 := by rw [← hu2]; nlinarith
  have hLq : L / Real.log 2 * Real.log q * 2 ≤ 3 * C * u ^ 4 := by
    have h1 : L / Real.log 2 ≤ 1.5 * L := by
      rw [div_le_iff₀ (by linarith)]; nlinarith
    have h2 : L * (C * u) ≤ C * u ^ 4 := by
      rw [← hu2]; nlinarith
    calc L / Real.log 2 * Real.log q * 2 ≤ 1.5 * L * (C * u) * 2 := by
          gcongr
      _ = 3 * (L * (C * u)) := by ring
      _ ≤ 3 * (C * u ^ 4) := by gcongr
      _ = 3 * C * u ^ 4 := by ring
  have hNE : 0 ≤ (N : ℝ) * E := by positivity
  calc B = L / Real.log 2 * Real.log q * 2 + L + (C₁ + A₄) * N * E := rfl
    _ ≤ 3 * C * u ^ 4 + u ^ 4 + (C₁ + A₄) * N * E := by linarith
    _ = (3 * C + 1) * u ^ 4 + (C₁ + A₄) * N * E := by ring
    _ ≤ (3 * C + 1) * (K * (N * E)) + (C₁ + A₄) * N * E := by gcongr
    _ ≤ (C₁ + A₄ + K * (3 * C + 2)) * N * E := by nlinarith

end NTKB
