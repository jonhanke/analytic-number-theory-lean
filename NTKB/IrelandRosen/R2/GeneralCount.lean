/-
Ireland–Rosen, Chapter 8, §7: the number of solutions of
`a_1 x_1^{l_1} + ⋯ + a_r x_r^{l_r} = b` (Theorem 5), over a finite field `F` with `q` elements.

We index the variables by `Fin (r + 1)`, i.e. the book's `r` is our `r + 1 ≥ 1`.
-/
import NTKB.IrelandRosen.R2.MultiJacobi

open Finset
open scoped Classical

set_option linter.unusedSectionVars false

namespace NTKB.IrelandRosen

variable {F : Type*} [Field F] [Fintype F]

/-- The number of solutions `x ∈ F^r` of `a_1 x_1^{l_1} + ⋯ + a_r x_r^{l_r} = b`. -/
noncomputable def numSolDiag {r : ℕ} (a : Fin r → F) (l : Fin r → ℕ) (b : F) : ℕ :=
  #{x : Fin r → F | ∑ i, a i * x i ^ l i = b}

/-- The `r`-tuples of characters `(χ_1, …, χ_r)` with `χ_i ^ {l_i} = ε`. -/
noncomputable def charTuples {r : ℕ} (l : Fin r → ℕ) : Finset (Fin r → MulChar F ℂ) :=
  Fintype.piFinset fun i => ({χ | χ ^ l i = 1} : Finset (MulChar F ℂ))

lemma norm_mulChar_apply (χ : MulChar F ℂ) {a : F} (ha : a ≠ 0) : ‖χ a‖ = 1 := by
  refine Complex.norm_eq_one_of_pow_eq_one (n := Fintype.card F - 1) ?_ ?_
  · rw [← map_pow, FiniteField.pow_card_sub_one_eq_one a ha, map_one]
  · exact (Nat.sub_pos_of_lt Fintype.one_lt_card).ne'

/-- Equation (4) of §7: `N = ∑_{a_1 u_1 + ⋯ + a_r u_r = b} ∏ N(x^{l_i} = u_i)`. -/
theorem numSolDiag_eq_sum {r : ℕ} (a : Fin r → F) (l : Fin r → ℕ) (b : F) :
    numSolDiag a l b = ∑ u : Fin r → F with ∑ i, a i * u i = b, ∏ i, numSolPow (l i) (u i) := by
  unfold numSolDiag
  rw [card_eq_sum_card_fiberwise (f := fun x : Fin r → F => fun i => x i ^ l i)
    (t := ({u : Fin r → F | ∑ i, a i * u i = b} : Finset _))]
  · refine Finset.sum_congr rfl fun u hu => ?_
    simp only [mem_filter, mem_univ, true_and] at hu
    have : ({x ∈ ({x : Fin r → F | ∑ i, a i * x i ^ l i = b} : Finset _) |
        (fun i => x i ^ l i) = u}) =
        Fintype.piFinset fun i => ({y : F | y ^ l i = u i} : Finset F) := by
      ext x
      simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset, funext_iff]
      constructor
      · rintro ⟨_, h⟩; exact h
      · intro h; refine ⟨?_, h⟩; simp_rw [h]; exact hu
    rw [this, Fintype.card_piFinset]
    rfl
  · intro x hx
    simpa using hx

/-- Substituting `t_i = a_i u_i`:
`∑_{∑ a_i u_i = b} ∏ χ_i(u_i) = ∏ χ_i(a_i⁻¹) · ∑_{∑ t_i = b} ∏ χ_i(t_i)`. -/
lemma sum_diag_eq {R : Type*} [CommRing R] {r : ℕ} (χ : Fin r → MulChar F R) {a : Fin r → F}
    (ha : ∀ i, a i ≠ 0) (b : F) :
    ∑ u : Fin r → F with ∑ i, a i * u i = b, ∏ i, bookChar (χ i) (u i) =
      (∏ i, χ i (a i)⁻¹) * multiJacobiSumAt χ b := by
  rw [multiJacobiSumAt, Finset.mul_sum]
  refine Finset.sum_nbij' (fun u => fun i => a i * u i) (fun t => fun i => (a i)⁻¹ * t i)
    ?_ ?_ ?_ ?_ ?_
  · intro u hu; simpa using hu
  · intro t ht
    simp only [mem_filter, mem_univ, true_and] at ht ⊢
    simp_rw [mul_inv_cancel_left₀ (ha _)]; exact ht
  · intro u _; ext i; simp [ha i]
  · intro t _; ext i; simp [ha i]
  · intro u _
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← bookChar_mul_of_ne_zero _ (inv_ne_zero (ha i)), inv_mul_cancel_left₀ (ha i)]

/-- Equation (5) of §7: `N = ∑_{χ_i^{l_i} = ε} ∏ χ_i(a_i⁻¹) · ∑_{∑ t_i = b} ∏ χ_i(t_i)`. -/
theorem numSolDiag_eq_sum_chars {r : ℕ} {a : Fin r → F} (ha : ∀ i, a i ≠ 0) {l : Fin r → ℕ}
    (hl : ∀ i, l i ∣ Fintype.card F - 1) (b : F) :
    (numSolDiag a l b : ℂ) =
      ∑ χ ∈ charTuples (F := F) l, (∏ i, χ i (a i)⁻¹) * multiJacobiSumAt χ b := by
  rw [numSolDiag_eq_sum]
  push_cast
  simp_rw [fun u : Fin r → F => fun i => numSolPow_eq_sum_of_dvd (hl i) (u i)]
  simp_rw [Finset.prod_univ_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun χ _ => ?_
  exact sum_diag_eq χ ha b

/-- The terms of Equation (5) with some but not all `χ_i` trivial vanish, and the all-trivial
term is `q^{r-1}`. -/
theorem numSolDiag_eq_main_add {r : ℕ} {a : Fin (r + 1) → F} (ha : ∀ i, a i ≠ 0)
    {l : Fin (r + 1) → ℕ} (hl : ∀ i, l i ∣ Fintype.card F - 1) (b : F) :
    (numSolDiag a l b : ℂ) = (Fintype.card F : ℂ) ^ r +
      ∑ χ ∈ charTuples (F := F) l with ∀ i, χ i ≠ 1, (∏ i, χ i (a i)⁻¹) * multiJacobiSumAt χ b := by
  rw [numSolDiag_eq_sum_chars ha hl, ← Finset.sum_filter_add_sum_filter_not _ (fun χ => χ = 1)]
  congr 1
  · have h1 : ({χ ∈ charTuples (F := F) l | χ = 1} : Finset _) = {1} := by
      ext χ
      simp only [mem_filter, mem_singleton, and_iff_right_iff_imp]
      rintro rfl
      simp [charTuples, Fintype.mem_piFinset]
    rw [h1, sum_singleton]
    rw [show (1 : Fin (r + 1) → MulChar F ℂ) = fun _ => 1 from rfl, multiJacobiSumAt_one]
    simp [MulChar.one_apply (Ne.isUnit (inv_ne_zero (ha _)))]
  · symm
    refine Finset.sum_subset ?_ ?_
    · intro χ hχ
      simp only [mem_filter] at hχ ⊢
      exact ⟨hχ.1, fun h1 => hχ.2 0 (by rw [h1]; rfl)⟩
    · intro χ hχ hχ'
      simp only [mem_filter, not_and] at hχ hχ'
      have hall := hχ' hχ.1
      push Not at hall
      obtain ⟨j, hj⟩ := hall
      have : ∃ k, χ k ≠ 1 := by
        by_contra! h; exact hχ.2 (funext h)
      obtain ⟨k, hk⟩ := this
      rw [multiJacobiSumAt_eq_zero b hj hk, mul_zero]

/-- **Theorem 5 (Chapter 8), the case `b = 0`.** If `a_i ≠ 0` and `l_i ∣ q - 1`, the number `N`
of solutions of `a_1 x_1^{l_1} + ⋯ + a_r x_r^{l_r} = 0` is
`q^{r-1} + ∑ χ_1(a_1⁻¹) ⋯ χ_r(a_r⁻¹) J_0(χ_1, …, χ_r)`, the sum over the tuples with
`χ_i^{l_i} = ε`, `χ_i ≠ ε` and `χ_1 ⋯ χ_r = ε`; and `|N - q^{r-1}| ≤ M (q - 1) q^{r/2 - 1}`
where `M` is the number of such tuples. (As printed, with `≤`; equality holds when `M = 0`.) -/
@[kb "irelandrosen1990" "Thm 5, p. 114"]
theorem numSolDiag_zero {r : ℕ} {a : Fin (r + 1) → F} (ha : ∀ i, a i ≠ 0)
    {l : Fin (r + 1) → ℕ} (hl : ∀ i, l i ∣ Fintype.card F - 1) :
    (numSolDiag a l 0 : ℂ) = (Fintype.card F : ℂ) ^ r +
      ∑ χ ∈ charTuples (F := F) l with (∀ i, χ i ≠ 1) ∧ ∏ i, χ i = 1,
        (∏ i, χ i (a i)⁻¹) * multiJacobiSumZero χ ∧
    ‖(numSolDiag a l 0 : ℂ) - (Fintype.card F : ℂ) ^ r‖ ≤
      #{χ ∈ charTuples (F := F) l | (∀ i, χ i ≠ 1) ∧ ∏ i, χ i = 1} * ((Fintype.card F : ℝ) - 1) *
        (Fintype.card F : ℝ) ^ (((r + 1 : ℕ) : ℝ) / 2 - 1) := by
  have heq : (numSolDiag a l 0 : ℂ) = (Fintype.card F : ℂ) ^ r +
      ∑ χ ∈ charTuples (F := F) l with (∀ i, χ i ≠ 1) ∧ ∏ i, χ i = 1,
        (∏ i, χ i (a i)⁻¹) * multiJacobiSumZero χ := by
    rw [numSolDiag_eq_main_add ha hl 0]
    congr 1
    rw [← Finset.filter_filter]
    symm
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun χ hχ => ?_
    simp only [mem_filter] at hχ
    split_ifs with h
    · rfl
    · rw [show multiJacobiSumAt χ 0 = multiJacobiSumZero χ from rfl,
        multiJacobiSumZero_eq_zero hχ.2 h, mul_zero]
  refine ⟨heq, ?_⟩
  rw [heq, add_sub_cancel_left]
  refine (norm_sum_le _ _).trans ?_
  rw [mul_assoc, ← nsmul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_le_sum fun χ hχ => ?_
  simp only [mem_filter] at hχ
  obtain ⟨_, hne, hprod⟩ := hχ
  rw [norm_mul, norm_prod]
  simp only [norm_mulChar_apply _ (inv_ne_zero (ha _)), prod_const_one, one_mul]
  cases r with
  | zero =>
    exfalso; apply hne 0
    simpa using hprod
  | succ r =>
    rw [(norm_multiJacobiSum_of_prod_eq_one hne hprod).1]
    have hq : (0 : ℝ) ≤ Fintype.card F := by positivity
    rw [show (((r + 1 + 1 : ℕ) : ℝ) / 2 - 1) = (r : ℝ) / 2 by push_cast; ring,
      Real.rpow_div_two_eq_sqrt _ hq, Real.rpow_natCast]

/-- **Theorem 5 (Chapter 8), the case `b ≠ 0`.** If `a_i ≠ 0` and `l_i ∣ q - 1`, the number `N`
of solutions of `a_1 x_1^{l_1} + ⋯ + a_r x_r^{l_r} = b` is
`q^{r-1} + ∑ (χ_1 ⋯ χ_r)(b) χ_1(a_1⁻¹) ⋯ χ_r(a_r⁻¹) J(χ_1, …, χ_r)`, the sum over the tuples with
`χ_i^{l_i} = ε` and `χ_i ≠ ε`; and `|N - q^{r-1}| ≤ M_0 q^{r/2-1} + M_1 q^{(r-1)/2}`, where `M_0`
(resp. `M_1`) counts those tuples with `χ_1 ⋯ χ_r = ε` (resp. `≠ ε`). -/
@[kb "irelandrosen1990" "Thm 5, p. 114"]
theorem numSolDiag_of_ne_zero {r : ℕ} {a : Fin (r + 1) → F} (ha : ∀ i, a i ≠ 0)
    {l : Fin (r + 1) → ℕ} (hl : ∀ i, l i ∣ Fintype.card F - 1) {b : F} (hb : b ≠ 0) :
    (numSolDiag a l b : ℂ) = (Fintype.card F : ℂ) ^ r +
      ∑ χ ∈ charTuples (F := F) l with ∀ i, χ i ≠ 1,
        (∏ i, χ i) b * (∏ i, χ i (a i)⁻¹) * multiJacobiSum χ ∧
    ‖(numSolDiag a l b : ℂ) - (Fintype.card F : ℂ) ^ r‖ ≤
      #{χ ∈ charTuples (F := F) l | (∀ i, χ i ≠ 1) ∧ ∏ i, χ i = 1} *
          (Fintype.card F : ℝ) ^ (((r + 1 : ℕ) : ℝ) / 2 - 1) +
        #{χ ∈ charTuples (F := F) l | (∀ i, χ i ≠ 1) ∧ ∏ i, χ i ≠ 1} *
          (Fintype.card F : ℝ) ^ ((r : ℝ) / 2) := by
  have heq : (numSolDiag a l b : ℂ) = (Fintype.card F : ℂ) ^ r +
      ∑ χ ∈ charTuples (F := F) l with ∀ i, χ i ≠ 1,
        (∏ i, χ i) b * (∏ i, χ i (a i)⁻¹) * multiJacobiSum χ := by
    rw [numSolDiag_eq_main_add ha hl b]
    congr 1
    refine Finset.sum_congr rfl fun χ _ => ?_
    rw [multiJacobiSumAt_of_ne_zero _ hb]; ring
  refine ⟨heq, ?_⟩
  rw [heq, add_sub_cancel_left]
  refine (norm_sum_le _ _).trans ?_
  rw [← Finset.sum_filter_add_sum_filter_not _ (fun χ => ∏ i, χ i = 1), Finset.filter_filter,
    Finset.filter_filter]
  have hq : (0 : ℝ) ≤ Fintype.card F := by positivity
  gcongr
  · rw [← nsmul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_le_sum fun χ hχ => ?_
    simp only [mem_filter] at hχ
    obtain ⟨_, hne, hprod⟩ := hχ
    rw [norm_mul, norm_mul, norm_prod, norm_mulChar_apply _ hb]
    simp only [norm_mulChar_apply _ (inv_ne_zero (ha _)), prod_const_one, one_mul]
    cases r with
    | zero =>
      exfalso; apply hne 0
      simpa using hprod
    | succ r =>
      rw [(norm_multiJacobiSum_of_prod_eq_one hne hprod).2]
      rw [show (((r + 1 + 1 : ℕ) : ℝ) / 2 - 1) = (r : ℝ) / 2 by push_cast; ring,
        Real.rpow_div_two_eq_sqrt _ hq, Real.rpow_natCast]
  · rw [← nsmul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_le_sum fun χ hχ => ?_
    simp only [mem_filter] at hχ
    obtain ⟨_, hne, hprod⟩ := hχ
    rw [norm_mul, norm_mul, norm_prod, norm_mulChar_apply _ hb]
    simp only [norm_mulChar_apply _ (inv_ne_zero (ha _)), prod_const_one, one_mul]
    rw [norm_multiJacobiSum hne hprod, Real.rpow_div_two_eq_sqrt _ hq, Real.rpow_natCast]

end NTKB.IrelandRosen
