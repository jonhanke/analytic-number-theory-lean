/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Davenport.Sieve.LargeSieve
import NTKB.Analytic.Davenport.Sieve.Gallagher

/-!
# Lower bounds for the large-sieve constant (Davenport, Chapter 27, p. 154)

Davenport considers inequalities `∑_r |S(α_r)|² ≤ A ∑_n |a_n|²` (his (E)) for
`S(α) = ∑_{M < n ≤ M + N} a_n e(nα)` and `δ`-separated points `α_r`, and shows that Theorem 2
(`A = N + 3/δ`, `large_sieve`) is essentially best possible:

* (F) for one point, Cauchy's inequality `|S(α)|² ≤ N ∑ |a_n|²` (`norm_sum_exp_sq_le`), with
  equality for `a_n = e(-nα)` (`norm_sum_exp_sq_eq`); hence `A ≥ N` (`le_of_isLargeSieveConstant`);
* `∫₀¹ ∑_r |S(α_r + β)|² dβ = R ∑ |a_n|²` (`integral_sum_norm_sq_shift`), so some shift `β` has
  `∑_r |S(α_r + β)|² ≥ R ∑ |a_n|²` (`exists_shift_sum_norm_sq_ge`); the points `r/R`,
  `R = ⌊1/δ⌋`, are `δ`-separated, so `A ≥ ⌊1/δ⌋ > 1/δ - 1` (`inv_sub_one_le_of_isLargeSieveConstant`).
-/

open Finset Real MeasureTheory

namespace NTKB.Davenport

/-- `A` is a large-sieve constant for length `N` and spacing `δ` (Davenport, Ch. 27, (E)): for every
finite family of points `δ`-separated modulo `1`, every `M` and all coefficients,
`∑_r |S(α_r)|² ≤ A ∑_n |a_n|²`. -/
def IsLargeSieveConstant (N : ℕ) (δ A : ℝ) : Prop :=
  ∀ (s : Finset ℕ) (α : ℕ → ℝ), (∀ r ∈ s, ∀ t ∈ s, r ≠ t → ∀ m : ℤ, δ ≤ |α r - α t - m|) →
    ∀ (M : ℤ) (a : ℤ → ℂ),
      ∑ r ∈ s, ‖∑ n ∈ Ioc M (M + N), a n * Complex.exp (2 * π * Complex.I * (n * α r))‖ ^ 2 ≤
        A * ∑ n ∈ Ioc M (M + N), ‖a n‖ ^ 2

/-- Theorem 2 in this language: `N + 3/δ` is a large-sieve constant. -/
theorem isLargeSieveConstant_large_sieve (N : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    IsLargeSieveConstant N δ (N + 3 / δ) := by
  intro s α hsep M a
  exact large_sieve s α hδ hsep M N a

/-- **Davenport, Ch. 27, (F)** (Cauchy's inequality): `|S(α)|² ≤ N ∑ |a_n|²`. -/
@[kb "davenport1980" "Ch 27, p. 154, (F)"]
theorem norm_sum_exp_sq_le (M : ℤ) (N : ℕ) (a : ℤ → ℂ) (α : ℝ) :
    ‖∑ n ∈ Ioc M (M + N), a n * Complex.exp (2 * π * Complex.I * (n * α))‖ ^ 2 ≤
      N * ∑ n ∈ Ioc M (M + N), ‖a n‖ ^ 2 := by
  set I := Ioc M (M + N)
  have h1 : ‖∑ n ∈ I, a n * Complex.exp (2 * π * Complex.I * (n * α))‖ ≤ ∑ n ∈ I, ‖a n‖ := by
    refine (norm_sum_le _ _).trans (le_of_eq (sum_congr rfl fun n _ ↦ ?_))
    rw [norm_mul, show (n : ℂ) * α = ((n * α : ℝ) : ℂ) by push_cast; ring,
      norm_exp_two_pi_I_mul, mul_one]
  have h2 := sq_sum_le_card_mul_sum_sq (s := I) (f := fun n ↦ ‖a n‖)
  have hI : (I.card : ℝ) = N := by simp [I]
  rw [hI] at h2
  calc _ ≤ (∑ n ∈ I, ‖a n‖) ^ 2 := by gcongr
    _ ≤ _ := h2

/-- **Davenport, Ch. 27, p. 154**: equality in (F) for `a_n = e(-nα)`. -/
@[kb "davenport1980" "Ch 27, p. 154"]
theorem norm_sum_exp_sq_eq (M : ℤ) (N : ℕ) (α : ℝ) :
    ‖∑ n ∈ Ioc M (M + N), Complex.exp (-(2 * π * Complex.I * (n * α))) *
        Complex.exp (2 * π * Complex.I * (n * α))‖ ^ 2 =
      N * ∑ n ∈ Ioc M (M + N), ‖Complex.exp (-(2 * π * Complex.I * (n * α)))‖ ^ 2 := by
  have h1 : ∀ n ∈ Ioc M (M + (N : ℤ)), Complex.exp (-(2 * π * Complex.I * (n * α))) *
      Complex.exp (2 * π * Complex.I * (n * α)) = 1 := by
    intro n _
    rw [← Complex.exp_add]; simp
  have h2 : ∀ n ∈ Ioc M (M + (N : ℤ)), ‖Complex.exp (-(2 * π * Complex.I * (n * α)))‖ ^ 2 = 1 := by
    intro n _
    rw [show -(2 * π * Complex.I * (n * α)) = ((-(2 * π * (n * α)) : ℝ) : ℂ) * Complex.I by
      push_cast; ring, Complex.norm_exp_ofReal_mul_I]; simp
  rw [sum_congr rfl h1, sum_congr rfl h2]
  simp; ring

/-- **Davenport, Ch. 27, p. 154**: `A ≥ N` (for `N ≥ 1`; for `N = 0` every sum vanishes). -/
@[kb "davenport1980" "Ch 27, p. 154"]
theorem le_of_isLargeSieveConstant {N : ℕ} (hN : 1 ≤ N) {δ A : ℝ}
    (hA : IsLargeSieveConstant N δ A) :
    (N : ℝ) ≤ A := by
  have h := hA {0} (fun _ ↦ 0) (by simp) 0
    (fun n ↦ Complex.exp (-(2 * π * Complex.I * (n * (0 : ℝ)))))
  rw [sum_singleton] at h
  simp only [zero_add] at h
  have h2 := norm_sum_exp_sq_eq 0 N 0
  simp only [zero_add] at h2
  rw [h2] at h
  have hs : ∑ n ∈ Ioc (0 : ℤ) N, ‖Complex.exp (-(2 * π * Complex.I * ((n : ℂ) * ((0 : ℝ) : ℂ))))‖ ^ 2
      = N := by simp
  rw [hs] at h
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  nlinarith

/-- **Davenport, Ch. 27, p. 154**: `∫₀¹ ∑_r |S(α_r + β)|² dβ = R ∑ |a_n|²`. -/
@[kb "davenport1980" "Ch 27, p. 154"]
theorem integral_sum_norm_sq_shift (s : Finset ℕ) (α : ℕ → ℝ) (M : ℤ) (N : ℕ) (a : ℤ → ℂ) :
    ∫ β in (0 : ℝ)..1, ∑ r ∈ s,
        ‖∑ n ∈ Ioc M (M + N), a n * Complex.exp (2 * π * Complex.I * (n * (α r + β)))‖ ^ 2 =
      s.card * ∑ n ∈ Ioc M (M + N), ‖a n‖ ^ 2 := by
  have hrw : ∀ (r : ℕ) (β : ℝ),
      ‖∑ n ∈ Ioc M (M + N), a n * Complex.exp (2 * π * Complex.I * (n * (α r + β)))‖ ^ 2 =
      ‖∑ n ∈ Ioc M (M + N), (a n * Complex.exp (2 * π * Complex.I * (n * α r))) *
        Complex.exp (2 * π * Complex.I * (n * β))‖ ^ 2 := by
    intro r β
    have e : ∀ n : ℤ, a n * Complex.exp (2 * π * Complex.I * (n * (α r + β))) =
        (a n * Complex.exp (2 * π * Complex.I * (n * α r))) *
        Complex.exp (2 * π * Complex.I * (n * β)) := by
      intro n
      rw [mul_assoc (a n), ← Complex.exp_add]
      congr 2
      push_cast; ring
    simp only [e]
  simp_rw [hrw]
  rw [intervalIntegral.integral_finsetSum]
  · have : ∀ r ∈ s, ∫ β in (0 : ℝ)..1, ‖∑ n ∈ Ioc M (M + N), (a n * Complex.exp (2 * π * Complex.I * (n * α r))) *
        Complex.exp (2 * π * Complex.I * (n * β))‖ ^ 2 = ∑ n ∈ Ioc M (M + N), ‖a n‖ ^ 2 := by
      intro r _
      rw [integral_norm_sum_exp_sq (Ioc M (M + N)) (fun n ↦ a n * Complex.exp (2 * π * Complex.I * (n * α r)))]
      refine sum_congr rfl fun n _ ↦ ?_
      rw [norm_mul, show (n : ℂ) * ((α r : ℝ) : ℂ) = ((n * α r : ℝ) : ℂ) by push_cast; ring,
        norm_exp_two_pi_I_mul, mul_one]
    rw [sum_congr rfl this]
    simp
  · intro r _
    apply Continuous.intervalIntegrable
    fun_prop

/-- **Davenport, Ch. 27, p. 154**: some shift `β` has `∑_r |S(α_r + β)|² ≥ R ∑ |a_n|²`. -/
@[kb "davenport1980" "Ch 27, p. 154"]
theorem exists_shift_sum_norm_sq_ge (s : Finset ℕ) (α : ℕ → ℝ) (M : ℤ) (N : ℕ) (a : ℤ → ℂ) :
    ∃ β : ℝ, s.card * ∑ n ∈ Ioc M (M + N), ‖a n‖ ^ 2 ≤ ∑ r ∈ s,
        ‖∑ n ∈ Ioc M (M + N), a n * Complex.exp (2 * π * Complex.I * (n * (α r + β)))‖ ^ 2 := by
  by_contra hcon
  push Not at hcon
  set F : ℝ → ℝ := fun β ↦ ∑ r ∈ s,
        ‖∑ n ∈ Ioc M (M + N), a n * Complex.exp (2 * π * Complex.I * (n * (α r + β)))‖ ^ 2 with hF
  have hcont : Continuous F := by rw [hF]; fun_prop
  obtain ⟨x0, _, hx0⟩ := isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.2 (zero_le_one' ℝ))
    hcont.continuousOn
  have hle : ∫ β in (0 : ℝ)..1, F β ≤ ∫ β in (0 : ℝ)..1, F x0 :=
    intervalIntegral.integral_mono_on zero_le_one (hcont.intervalIntegrable _ _)
      intervalIntegrable_const fun x hx ↦ hx0 hx
  have := integral_sum_norm_sq_shift s α M N a
  simp only [intervalIntegral.integral_const, sub_zero, one_smul] at hle
  have h3 := hcon x0
  have : ∫ β in (0 : ℝ)..1, F β = s.card * ∑ n ∈ Ioc M (M + N), ‖a n‖ ^ 2 := this
  linarith

lemma inv_R_le_abs {R r t : ℕ} (hR : 1 ≤ R) (hr : r < R) (ht : t < R) (hrt : r ≠ t) (m : ℤ) :
    1 / (R : ℝ) ≤ |(r : ℝ) / R - (t : ℝ) / R - m| := by
  have hRpos : (0 : ℝ) < R := by exact_mod_cast hR
  have hR' : (0 : ℤ) < R := by exact_mod_cast hR
  have hk : ((r : ℤ) - t - m * R) ≠ 0 := by
    intro h
    have h1 : (r : ℤ) - t = m * R := by linarith
    rcases lt_trichotomy m 0 with hm | hm | hm
    · have h2 : m * (R : ℤ) ≤ (-1) * R :=
        mul_le_mul_of_nonneg_right (by omega) hR'.le
      have : (r : ℤ) < R := by exact_mod_cast hr
      have : (t : ℤ) < R := by exact_mod_cast ht
      omega
    · subst hm
      have : (r : ℤ) = t := by simpa [sub_eq_zero] using h1
      exact hrt (by exact_mod_cast this)
    · have h2 : (1 : ℤ) * R ≤ m * R :=
        mul_le_mul_of_nonneg_right (by omega) hR'.le
      have : (r : ℤ) < R := by exact_mod_cast hr
      have : (t : ℤ) < R := by exact_mod_cast ht
      omega
  have h1 : (r : ℝ) / R - (t : ℝ) / R - m = (((r : ℤ) - t - m * R : ℤ) : ℝ) / R := by
    push_cast
    rw [eq_div_iff hRpos.ne', sub_mul, sub_mul, div_mul_cancel₀ _ hRpos.ne',
      div_mul_cancel₀ _ hRpos.ne']
  rw [h1, abs_div, abs_of_pos hRpos]
  refine div_le_div_of_nonneg_right ?_ hRpos.le
  have := Int.one_le_abs hk
  exact_mod_cast this

lemma card_le_of_isLargeSieveConstant {N : ℕ} (hN : 1 ≤ N) {δ A : ℝ} (hA : IsLargeSieveConstant N δ A)
    (s : Finset ℕ) (α : ℕ → ℝ) (hsep : ∀ r ∈ s, ∀ t ∈ s, r ≠ t → ∀ m : ℤ, δ ≤ |α r - α t - m|) :
    (s.card : ℝ) ≤ A := by
  obtain ⟨β, hβ⟩ := exists_shift_sum_norm_sq_ge s α 0 N (fun _ ↦ 1)
  have hsep' : ∀ r ∈ s, ∀ t ∈ s, r ≠ t → ∀ m : ℤ,
      δ ≤ |(α r + β) - (α t + β) - m| := by
    intro r hr t ht hrt m
    have := hsep r hr t ht hrt m
    rwa [add_sub_add_right_eq_sub]
  have h := hA s (fun r ↦ α r + β) hsep' 0 (fun _ ↦ 1)
  have hsum : ∑ n ∈ Ioc (0 : ℤ) N, ‖(1 : ℂ)‖ ^ 2 = N := by simp
  beta_reduce at h
  rw [zero_add, hsum] at hβ h
  push_cast at h
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have := hβ.trans h
  exact le_of_mul_le_mul_right this hN'

/-- **Davenport, Ch. 27, p. 154**: `A ≥ ⌊1/δ⌋` for `0 < δ ≤ 1` and `N ≥ 1`. -/
@[kb "davenport1980" "Ch 27, p. 154"]
theorem floor_inv_le_of_isLargeSieveConstant {N : ℕ} (hN : 1 ≤ N) {δ A : ℝ} (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) (hA : IsLargeSieveConstant N δ A) : (⌊δ⁻¹⌋₊ : ℝ) ≤ A := by
  set R := ⌊δ⁻¹⌋₊ with hR
  have hδinv : 1 ≤ δ⁻¹ := by rw [one_le_inv₀ hδ]; exact hδ1
  have hR1 : 1 ≤ R := Nat.le_floor (by simpa using hδinv)
  have hRpos : (0 : ℝ) < R := by exact_mod_cast hR1
  have hRle : (R : ℝ) ≤ δ⁻¹ := Nat.floor_le (by positivity)
  have hδR : δ ≤ 1 / R := by
    rw [le_div_iff₀ hRpos]
    have := mul_le_mul_of_nonneg_left hRle hδ.le
    rwa [mul_inv_cancel₀ hδ.ne'] at this
  have hsep : ∀ r ∈ range R, ∀ t ∈ range R, r ≠ t → ∀ m : ℤ,
      δ ≤ |(fun r : ℕ ↦ (r : ℝ) / R) r - (fun r : ℕ ↦ (r : ℝ) / R) t - m| := by
    intro r hr t ht hrt m
    exact hδR.trans (inv_R_le_abs hR1 (mem_range.1 hr) (mem_range.1 ht) hrt m)
  set α : ℕ → ℝ := fun r ↦ (r : ℝ) / R
  have := card_le_of_isLargeSieveConstant hN hA (range R) (fun r : ℕ ↦ (r : ℝ) / R) hsep
  simpa using this

/-- **Davenport, Ch. 27, p. 154**: `A > 1/δ - 1` for `0 < δ ≤ 1` and `N ≥ 1`. -/
@[kb "davenport1980" "Ch 27, p. 154"]
theorem inv_sub_one_le_of_isLargeSieveConstant {N : ℕ} (hN : 1 ≤ N) {δ A : ℝ} (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) (hA : IsLargeSieveConstant N δ A) : δ⁻¹ - 1 < A := by
  have := floor_inv_le_of_isLargeSieveConstant hN hδ hδ1 hA
  have h2 := Nat.lt_floor_add_one δ⁻¹
  linarith

end NTKB.Davenport
