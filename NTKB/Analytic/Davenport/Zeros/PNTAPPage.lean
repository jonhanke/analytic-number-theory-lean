/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Davenport.Zeros.PNTAP
import NTKB.Analytic.Davenport.Zeros.Landau

/-!
# Page's form of the prime number theorem for progressions

**Davenport, Ch. 20, pp. 123-124, (13) (rows 20-8, 20-10).** Let `C > 0`, `z = max(3, e^{C √log N})`.
By Page's theorem (14-15) there is at most one modulus `q₁ ≤ z` of a real primitive character with
a real zero `β > 1 - c/log z` (`c = 1/800`). Unless `q` is a multiple of `q₁`,
`ψ(N; q, a) = N/φ(q) + O(N exp(-c' √log N))` uniformly for `log q ≤ C √log N`.
-/

open Filter Topology Complex Set DirichletCharacter
open scoped Real ArithmeticFunction.vonMangoldt

namespace NTKB

/-- A modulus `q' ≤ z` carrying a real primitive character with a real zero `β > 1 - 1/(800 log z)`. -/
def IsPageModulus (z : ℝ) (q' : ℕ) : Prop :=
  ∃ (_ : NeZero q') (χ' : DirichletCharacter ℂ q') (β : ℝ), χ'.IsPrimitive ∧ χ' ≠ 1 ∧
    χ' ^ 2 = 1 ∧ (q' : ℝ) ≤ z ∧ LFunction χ' β = 0 ∧ 1 - 1 / 800 / Real.log z < β

/-- **Davenport, Ch. 20, p. 124 (row 20-8)**: there is at most one such modulus (Page, 14-15). -/
@[kb "davenport1980" "Ch 20, p. 124"]
theorem Davenport.isPageModulus_unique {z : ℝ} (hz : 3 ≤ z) {q₁ q₂ : ℕ}
    (h₁ : IsPageModulus z q₁) (h₂ : IsPageModulus z q₂) : q₁ = q₂ := by
  obtain ⟨_, χ₁, β₁, hp₁, hn₁, hr₁, hq₁, hz₁, hb₁⟩ := h₁
  obtain ⟨_, χ₂, β₂, hp₂, hn₂, hr₂, hq₂, hz₂, hb₂⟩ := h₂
  exact (Davenport.page_exceptional_character hz hp₁ hp₂ hn₁ hn₂ hr₁ hr₂ hq₁ hq₂ hz₁ hz₂ hb₁
    hb₂).1

open scoped Classical in
/-- If the conductor of `χ` is not a Page modulus, the exceptional term is small:
`|E(N, χ)| ≤ A (log q + 1) N exp(-log N/(800 log z))`. -/
lemma norm_excTerm_le_of_not_page :
    ∃ A : ℝ, 0 < A ∧ ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (N : ℕ) (z : ℝ), 3 ≤ N →
      3 ≤ z → (q : ℝ) ≤ z → ¬ IsPageModulus z χ.conductor →
      ‖excTerm χ N‖ ≤ A * (Real.log q + 1) * (N * Real.exp (-(1 / 800 * Real.log N / Real.log z))) := by
  obtain ⟨A₆, hA₆, h₆⟩ := card_zerosBelowL_one_le
  refine ⟨2 * A₆, by positivity, ?_⟩
  intro q _ χ N z hN hz3 hqz hnp
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hN0 : (0 : ℝ) < N := by linarith
  have hlz : 0 < Real.log z := Real.log_pos (by linarith)
  have hlq : 0 ≤ Real.log q := Real.log_natCast_nonneg q
  set E := Real.exp (-(1 / 800 * Real.log N / Real.log z)) with hE
  have hE0 : 0 < E := Real.exp_pos _
  unfold excTerm
  split_ifs with hcond
  · haveI : NeZero χ.conductor := ⟨conductor_ne_zero χ⟩
    have hprim := primitiveCharacter_isPrimitive χ
    have hχ1 : χ.primitiveCharacter ≠ 1 := fun h ↦ hcond (by
      have := hprim; rw [h, IsPrimitive, conductor_one] at this; exact this.symm)
    have hcq : (χ.conductor : ℝ) ≤ q := by
      exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) χ.conductor_dvd_level
    have hc1 := h₆ hprim hcond
    have hlc : Real.log χ.conductor ≤ Real.log q :=
      Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero (conductor_ne_zero χ)) hcq
    refine (norm_sum_le _ _).trans ?_
    have hpt : ∀ ρ ∈ (zerosBelowL hprim hcond 1).filter (fun ρ ↦ IsExcPoint χ.conductor ρ.val),
        ‖perronKernel N ρ.val‖ ≤ 2 * (N * E) := by
      intro ρ hρ
      have hexc := (Finset.mem_filter.mp hρ).2
      have hz := (dirichletXi_zero_mem hprim hcond ρ).1
      obtain ⟨hsq, him⟩ := Davenport.exceptional_zero_real hχ1 hz hexc
      have hhalf := hexc.re_gt_half hχ1
      have hρr : ρ.val = (ρ.val.re : ℂ) := by apply Complex.ext <;> simp [him]
      have hβ : ρ.val.re ≤ 1 - 1 / 800 / Real.log z := by
        by_contra hlt
        push Not at hlt
        apply hnp
        refine ⟨inferInstance, χ.primitiveCharacter, ρ.val.re, hprim, hχ1, hsq, hcq.trans hqz, ?_, hlt⟩
        rw [← hρr]; exact hz
      rw [norm_perronKernel hN0]
      have h1 : (N : ℝ) ^ ρ.val.re ≤ N * E := by
        calc (N : ℝ) ^ ρ.val.re ≤ (N : ℝ) ^ (1 - 1 / 800 / Real.log z) :=
              Real.rpow_le_rpow_of_exponent_le hN1 hβ
          _ = N * E := by
              rw [Real.rpow_sub hN0, Real.rpow_one, Real.rpow_def_of_pos hN0, div_eq_mul_inv (N : ℝ),
                ← Real.exp_neg, hE]
              congr 2; ring
      have h2 : 1 / 2 ≤ ‖ρ.val‖ := by linarith [Complex.re_le_norm ρ.val]
      rw [div_le_iff₀ (by linarith)]
      have hNE : 0 ≤ (N : ℝ) * E := by positivity
      nlinarith [mul_le_mul_of_nonneg_left h2 hNE]
    calc ∑ ρ ∈ (zerosBelowL hprim hcond 1).filter (fun ρ ↦ IsExcPoint χ.conductor ρ.val),
          ‖perronKernel N ρ.val‖
        ≤ ∑ ρ ∈ (zerosBelowL hprim hcond 1).filter (fun ρ ↦ IsExcPoint χ.conductor ρ.val),
            2 * (N * E) := Finset.sum_le_sum hpt
      _ ≤ ((zerosBelowL hprim hcond 1).card : ℝ) * (2 * (N * E)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
          have hcard : (((zerosBelowL hprim hcond 1).filter
              (fun ρ ↦ IsExcPoint χ.conductor ρ.val)).card : ℝ) ≤ (zerosBelowL hprim hcond 1).card :=
            Nat.cast_le.mpr (Finset.card_filter_le _ _)
          have : 0 ≤ 2 * ((N : ℝ) * E) := by positivity
          exact mul_le_mul_of_nonneg_right hcard this
      _ ≤ A₆ * (Real.log q + 1) * (2 * (N * E)) := by
          gcongr
          exact hc1.trans (by gcongr)
      _ = 2 * A₆ * (Real.log q + 1) * (N * E) := by ring
  · rw [norm_zero]; positivity

open scoped Classical in
set_option maxHeartbeats 4000000 in
/-- **Davenport, Ch. 20, p. 124, (13) (row 20-10)**: for every `C > 0` there are `c, A > 0` such
that for every integer `N ≥ 3`, with `z = max(3, e^{C √log N})`, there is `q₁` (either `0`, or the
unique Page modulus `≤ z`) such that for all `q` with `log q ≤ C √log N` that are not multiples
of `q₁` and all `a` prime to `q`: `|ψ(N; q, a) - N/φ(q)| ≤ A N exp(-c √log N)`. -/
@[kb "davenport1980" "Ch 20, p. 124"]
theorem Davenport.psiAP_sub_le_page (C : ℝ) (hC : 0 < C) :
    ∃ c A : ℝ, 0 < c ∧ 0 < A ∧ ∀ N : ℕ, 3 ≤ N → ∃ q₁ : ℕ,
      (q₁ = 0 ∨ IsPageModulus (max 3 (Real.exp (C * √(Real.log N)))) q₁) ∧
      ∀ {q : ℕ} [NeZero q] {a : ZMod q}, IsUnit a → Real.log q ≤ C * √(Real.log N) → ¬ q₁ ∣ q →
        ‖(psiAP a N : ℂ) - N / q.totient‖ ≤ A * N * Real.exp (-(c * √(Real.log N))) := by
  obtain ⟨c₅, A₅, hc₅, hA₅, h₅⟩ := Davenport.psiAP_sub_le C hC
  obtain ⟨A₇, hA₇, h₇⟩ := norm_excTerm_le_of_not_page
  set c' := min (c₅) (1 / 800 / (Real.log 3 + C) / 2) with hc'
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hc'0 : 0 < c' := lt_min hc₅ (by positivity)
  have hc'1 : c' ≤ c₅ := min_le_left _ _
  have hc'2 : c' ≤ 1 / 800 / (Real.log 3 + C) / 2 := min_le_right _ _
  have hc'h : c' ≤ 1 / 2 := by
    have h3 : 2 / 3 < Real.log 3 :=
      log_two_gt_two_thirds.trans_le (Real.log_le_log two_pos (by norm_num))
    refine hc'2.trans ?_
    rw [div_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  set K := 24 * (2 / c') ^ 4 with hK
  have hK0 : 0 < K := by positivity
  refine ⟨c', A₅ + A₇ * (C + 1) * K + 1, hc'0, by positivity, ?_⟩
  intro N hN
  set z := max 3 (Real.exp (C * √(Real.log N))) with hz
  have hz3 : 3 ≤ z := le_max_left _ _
  refine ⟨if h : ∃ q', IsPageModulus z q' then h.choose else 0, ?_, ?_⟩
  · split_ifs with h
    · exact Or.inr h.choose_spec
    · exact Or.inl rfl
  intro q _ a ha hqN hndvd
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
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
  have hqz : (q : ℝ) ≤ z := by
    have hq0 : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
    calc (q : ℝ) = Real.exp (Real.log q) := (Real.exp_log hq0).symm
      _ ≤ Real.exp (C * u) := Real.exp_le_exp.mpr hqN
      _ ≤ z := le_max_right _ _
  -- the exceptional terms are small
  have hnp : ∀ χ : DirichletCharacter ℂ q, ¬ IsPageModulus z χ.conductor := by
    intro χ hp
    apply hndvd
    have hex : ∃ q', IsPageModulus z q' := ⟨_, hp⟩
    rw [dif_pos hex]
    have := Davenport.isPageModulus_unique hz3 hex.choose_spec hp
    rw [this]
    exact χ.conductor_dvd_level
  set E := Real.exp (-(1 / 800 * Real.log N / Real.log z))
  have hE : ∀ χ : DirichletCharacter ℂ q, ‖excTerm χ N‖ ≤ A₇ * (Real.log q + 1) * (N * E) :=
    fun χ ↦ h₇ χ N z hN hz3 hqz (hnp χ)
  -- `log z ≤ (log 3 + C) u`
  have hlz : Real.log z ≤ (Real.log 3 + C) * u := by
    rcases le_total 3 (Real.exp (C * u)) with h | h
    · rw [hz, max_eq_right h, Real.log_exp]; nlinarith
    · rw [hz, max_eq_left h]; nlinarith
  have hlz0 : 0 < Real.log z := Real.log_pos (by linarith)
  have hEu : E ≤ Real.exp (-(2 * c' * u)) := by
    apply Real.exp_le_exp.mpr
    rw [neg_le_neg_iff, le_div_iff₀ hlz0, ← hL, ← hu2]
    have h1 : 2 * c' * (Real.log 3 + C) ≤ 1 / 800 := by
      have := mul_le_mul_of_nonneg_right hc'2 (by positivity : (0 : ℝ) ≤ 2 * (Real.log 3 + C))
      have e : 1 / 800 / (Real.log 3 + C) / 2 * (2 * (Real.log 3 + C)) = 1 / 800 := by
        field_simp
      nlinarith
    calc 2 * c' * u * Real.log z ≤ 2 * c' * u * ((Real.log 3 + C) * u) := by gcongr
      _ = 2 * c' * (Real.log 3 + C) * u ^ 2 := by ring
      _ ≤ 1 / 800 * u ^ 2 := by gcongr
  -- the main estimate from 20-5
  have hmain := h₅ ha N hN hqN
  set S := (q.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q, χ a⁻¹ * excTerm χ N
  have hS : ‖S‖ ≤ A₇ * (Real.log q + 1) * (N * E) := by
    have hφ : (q.totient : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))).ne'
    have hcard : (Finset.univ : Finset (DirichletCharacter ℂ q)).card = q.totient := by
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card,
        DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity]
    have hφpos : (0 : ℝ) < q.totient := lt_of_le_of_ne (Nat.cast_nonneg _) (Ne.symm hφ)
    simp only [S]
    rw [norm_mul, norm_inv, Complex.norm_natCast]
    have hb : ‖∑ χ : DirichletCharacter ℂ q, χ a⁻¹ * excTerm χ N‖ ≤
        q.totient * (A₇ * (Real.log q + 1) * (N * E)) := by
      refine (norm_sum_le _ _).trans ?_
      calc ∑ χ : DirichletCharacter ℂ q, ‖χ a⁻¹ * excTerm χ N‖
          ≤ ∑ χ : DirichletCharacter ℂ q, A₇ * (Real.log q + 1) * (N * E) := by
            refine Finset.sum_le_sum fun χ _ ↦ ?_
            rw [norm_mul]
            have := DirichletCharacter.norm_le_one χ a⁻¹
            have h0 : 0 ≤ A₇ * (Real.log q + 1) * (N * E) := by positivity
            calc ‖χ a⁻¹‖ * ‖excTerm χ N‖ ≤ 1 * (A₇ * (Real.log q + 1) * (N * E)) :=
                  mul_le_mul this (hE χ) (norm_nonneg _) zero_le_one
              _ = A₇ * (Real.log q + 1) * (N * E) := one_mul _
        _ = q.totient * (A₇ * (Real.log q + 1) * (N * E)) := by
            rw [Finset.sum_const, hcard, nsmul_eq_mul]
    calc (q.totient : ℝ)⁻¹ * ‖∑ χ : DirichletCharacter ℂ q, χ a⁻¹ * excTerm χ N‖
        ≤ (q.totient : ℝ)⁻¹ * (q.totient * (A₇ * (Real.log q + 1) * (N * E))) := by gcongr
      _ = A₇ * (Real.log q + 1) * (N * E) := by field_simp
  have hsplit : (psiAP a N : ℂ) - N / q.totient = ((psiAP a N : ℂ) - N / q.totient + S) - S := by
    ring
  rw [hsplit]
  refine (norm_sub_le _ _).trans ?_
  -- final bookkeeping
  set F := Real.exp (-(c' * u)) with hF
  have hF0 : 0 < F := Real.exp_pos _
  have h1 : A₅ * N * Real.exp (-(c₅ * √(Real.log N))) ≤ A₅ * N * F := by
    have : Real.exp (-(c₅ * √(Real.log N))) ≤ F := by
      rw [hF, ← hL, ← hu]; apply Real.exp_le_exp.mpr
      have := mul_le_mul_of_nonneg_right hc'1 (le_of_lt (by linarith : (0 : ℝ) < u))
      linarith
    exact mul_le_mul_of_nonneg_left this (by positivity)
  have h2 : A₇ * (Real.log q + 1) * (N * E) ≤ A₇ * (C + 1) * K * (N * F) := by
    have hq1 : Real.log q + 1 ≤ (C + 1) * u := by
      have : Real.log q ≤ C * u := hqN
      nlinarith
    have hu4 : u ≤ K * Real.exp (c' * u) := by
      have := pow_four_le_exp hc'0 (le_of_lt (by linarith : (0 : ℝ) < u))
      have hu' : u ≤ u ^ 4 := by
        have : 1 ≤ u ^ 3 := one_le_pow₀ hu1.le
        nlinarith
      have h5 : Real.exp (c' * u / 2) ≤ Real.exp (c' * u) :=
        Real.exp_le_exp.mpr (by nlinarith)
      calc u ≤ u ^ 4 := hu'
        _ ≤ K * Real.exp (c' * u / 2) := this
        _ ≤ K * Real.exp (c' * u) := by gcongr
    have hEF : Real.exp (c' * u) * E ≤ F := by
      calc Real.exp (c' * u) * E ≤ Real.exp (c' * u) * Real.exp (-(2 * c' * u)) := by gcongr
        _ = F := by rw [← Real.exp_add, hF]; congr 1; ring
    have hNE : 0 ≤ (N : ℝ) * E := by positivity
    calc A₇ * (Real.log q + 1) * (N * E) ≤ A₇ * ((C + 1) * u) * (N * E) := by gcongr
      _ = A₇ * (C + 1) * (u * (N * E)) := by ring
      _ ≤ A₇ * (C + 1) * ((K * Real.exp (c' * u)) * (N * E)) := by gcongr
      _ = A₇ * (C + 1) * K * (N * (Real.exp (c' * u) * E)) := by ring
      _ ≤ A₇ * (C + 1) * K * (N * F) := by gcongr
  have hmain' := hmain.trans h1
  have hfin : ‖(psiAP a N : ℂ) - N / q.totient + S‖ + ‖S‖ ≤
      A₅ * N * F + A₇ * (C + 1) * K * (N * F) := add_le_add hmain' (hS.trans h2)
  refine hfin.trans ?_
  have : 0 ≤ (N : ℝ) * F := by positivity
  nlinarith

end NTKB
