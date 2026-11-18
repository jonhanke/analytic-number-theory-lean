/-
Ireland–Rosen, Chapter 8, §3 and §4: the equations `x^3 + y^3 = 1` and `x^n + y^n = 1` over a
finite field `F` with `q` elements, `q ≡ 1 (mod n)` (the book takes `F = 𝔽_p`).
-/
import NTKB.IrelandRosen.R2.GeneralCount

open Finset
open scoped Classical

set_option linter.unusedSectionVars false

namespace NTKB.IrelandRosen

variable {F : Type*} [Field F] [Fintype F]

/-- Sums over `t_1 + t_2 = b`. -/
lemma sum_filter_pair {R : Type*} [AddCommMonoid R] (G : (Fin 2 → F) → R) (b : F) :
    ∑ t : Fin 2 → F with ∑ i, t i = b, G t = ∑ a : F, G ![a, b - a] := by
  symm
  refine Finset.sum_nbij' (fun a => ![a, b - a]) (fun t => t 0) ?_ ?_ ?_ ?_ ?_
  · intro a _; simp [Fin.sum_univ_two]
  · intro t _; simp
  · intro a _; simp
  · intro t ht
    simp only [mem_coe, mem_filter, mem_univ, true_and, Fin.sum_univ_two] at ht
    ext i; fin_cases i <;> simp [← ht]
  · intro a _; rfl

/-- The Jacobi sum of two characters, written out (book convention). -/
lemma multiJacobiSum_pair {R : Type*} [CommRing R] (χ φ : MulChar F R) :
    multiJacobiSum ![χ, φ] = ∑ a : F, bookChar χ a * bookChar φ (1 - a) := by
  rw [multiJacobiSum, multiJacobiSumAt, sum_filter_pair]
  simp [Fin.prod_univ_two]

lemma multiJacobiSum_single {R : Type*} [CommRing R] (χ : Fin 1 → MulChar F R) :
    multiJacobiSum χ = 1 := by
  rw [multiJacobiSum, multiJacobiSumAt, sum_filter_sum_eq_snoc]
  simp [Fin.snoc, bookChar_of_ne_zero _ (one_ne_zero (α := F))]

/-- `N(x^n + y^n = 1) = ∑_{a + b = 1} N(x^n = a) N(y^n = b)`. -/
lemma numSolDiag_fermat (n : ℕ) :
    numSolDiag ![(1 : F), 1] ![n, n] 1 = ∑ a : F, numSolPow n a * numSolPow n (1 - a) := by
  rw [numSolDiag_eq_sum]
  have : ∀ u : Fin 2 → F, ∑ i, ![(1 : F), 1] i * u i = ∑ i, u i := by
    intro u; simp [Fin.sum_univ_two]
  simp_rw [this]
  rw [sum_filter_pair]
  simp [Fin.prod_univ_two]

/-- `N(x^n + y^n = 1) = ∑_{i,j=0}^{n-1} J(χ^i, χ^j)` for `χ` of order `n ∣ q - 1`. -/
theorem numSolDiag_fermat_eq_sum {n : ℕ} (hn : n ∣ Fintype.card F - 1) {χ : MulChar F ℂ}
    (hχ : orderOf χ = n) :
    (numSolDiag ![(1 : F), 1] ![n, n] 1 : ℂ) =
      ∑ i ∈ range n, ∑ j ∈ range n, multiJacobiSum ![χ ^ i, χ ^ j] := by
  rw [numSolDiag_fermat]
  push_cast
  simp_rw [numSolPow_eq_sum_range hn hχ, multiJacobiSum_pair, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]

lemma mulChar_neg_one_sq {R : Type*} [CommRing R] (χ : MulChar F R) : χ (-1) * χ (-1) = 1 := by
  rw [← map_mul]; simp

lemma mulChar_inv_neg_one {R : Type*} [CommRing R] (χ : MulChar F R) : χ⁻¹ (-1) = χ (-1) := by
  rw [MulChar.inv_apply', inv_neg, inv_one]

/-- If `-1` is an `n`-th power then `N(x^n = -1) = n`, otherwise it is `0` (`n ∣ q - 1`). -/
lemma numSolPow_neg_one {n : ℕ} (hn : n ∣ Fintype.card F - 1) :
    numSolPow n (-1 : F) = if ∃ x : F, x ^ n = -1 then n else 0 := by
  obtain ⟨χ, hχ⟩ := exists_orderOf_eq hn
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [orderOf_eq_zero_iff'] at hχ
    exact hχ (Fintype.card F - 1) (Nat.sub_pos_of_lt Fintype.one_lt_card)
      (by rw [← Fintype.card_units]; exact MulChar.pow_card_eq_one χ)
  have hcard : numSolPow n (1 : F) = n := by
    have h := (filter_pow_eq_one_eq_image hn hχ)
    rw [← card_pow_eq_one_eq hn0, h.1, card_image_of_injOn h.2, card_range]
  split_ifs with h
  · obtain ⟨x0, hx0⟩ := h
    have hx0' : x0 ≠ 0 := by
      rintro rfl
      rw [zero_pow hn0] at hx0; exact absurd hx0.symm (neg_ne_zero.mpr one_ne_zero)
    conv_rhs => rw [← hcard]
    unfold numSolPow
    refine Finset.card_nbij' (fun x => x0⁻¹ * x) (fun y => x0 * y) ?_ ?_ ?_ ?_
    · intro x hx
      simp only [mem_coe, mem_filter, mem_univ, true_and] at hx ⊢
      rw [mul_pow, hx, inv_pow, hx0]; simp
    · intro y hy
      simp only [mem_coe, mem_filter, mem_univ, true_and] at hy ⊢
      rw [mul_pow, hy, hx0, mul_one]
    · intro x _; simp [hx0']
    · intro y _; simp [hx0']
  · push Not at h
    unfold numSolPow
    rw [Finset.card_eq_zero]
    ext x; simp [h x]

/-- **Proposition 8.4.1.** If `n ∣ q - 1` (`n ≥ 1`), then
`|N(x^n + y^n = 1) + δ_n(-1) n - (q + 1)| ≤ (n - 1)(n - 2) √q`, where `δ_n(-1) = 1` if `-1` is an
`n`-th power in `F` and `0` otherwise. (As printed, with `≤`; equality holds for `n ≤ 2`.) -/
@[kb "irelandrosen1990" "Prop 8.4.1, p. 109"]
theorem norm_numSolDiag_fermat_sub_le {n : ℕ} (hn : n ∣ Fintype.card F - 1) :
    ‖(numSolDiag ![(1 : F), 1] ![n, n] 1 : ℂ) +
        (if ∃ x : F, x ^ n = -1 then (n : ℂ) else 0) - (Fintype.card F + 1)‖ ≤
      ((n : ℝ) - 1) * ((n : ℝ) - 2) * √(Fintype.card F) := by
  obtain ⟨χ, hχ⟩ := exists_orderOf_eq hn
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [orderOf_eq_zero_iff'] at hχ
    exact hχ (Fintype.card F - 1) (Nat.sub_pos_of_lt Fintype.one_lt_card)
      (by rw [← Fintype.card_units]; exact MulChar.pow_card_eq_one χ)
  have hpow : ∀ i, χ ^ i = 1 ↔ n ∣ i := fun i => by rw [← hχ, orderOf_dvd_iff_pow_eq_one]
  -- the explicit part and the remainder of each term
  set E : ℕ → ℕ → ℂ := fun i j => if i = 0 ∧ j = 0 then (Fintype.card F : ℂ) else
    if i = 0 ∨ j = 0 then 0 else if i + j = n then -(χ ^ j) (-1) else 0 with hE
  set Rm : ℕ → ℕ → ℂ := fun i j => if i ≠ 0 ∧ j ≠ 0 ∧ i + j ≠ n then
    multiJacobiSum ![χ ^ i, χ ^ j] else 0 with hRm
  have hsplit : ∀ i ∈ range n, ∀ j ∈ range n, multiJacobiSum ![χ ^ i, χ ^ j] = E i j + Rm i j := by
    intro i hi j hj
    simp only [mem_range] at hi hj
    simp only [hE, hRm]
    by_cases hi0 : i = 0 <;> by_cases hj0 : j = 0
    · subst hi0 hj0
      simp only [pow_zero, and_self, if_true, ne_eq, not_true_eq_false, false_and, if_false,
        add_zero]
      have h1 : (![1, 1] : Fin 2 → MulChar F ℂ) = fun _ => 1 := by
        funext k; fin_cases k <;> rfl
      rw [h1]
      have := multiJacobiSumAt_one (R := ℂ) (F := F) (r := 1) 1
      rw [pow_one] at this
      exact this
    · subst hi0
      simp only [true_and, hj0, if_false, true_or, if_true, ne_eq, not_true_eq_false, false_and,
        add_zero, pow_zero]
      exact multiJacobiSumAt_eq_zero (j := 0) (k := 1) 1 rfl (by
        simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one]
        rw [Ne, hpow]; intro h; exact hj0 (Nat.eq_zero_of_dvd_of_lt h hj))
    · subst hj0
      simp only [hi0, and_true, if_false, or_true, if_true, ne_eq, not_true_eq_false, and_false,
        false_and, add_zero, pow_zero]
      exact multiJacobiSumAt_eq_zero (j := 1) (k := 0) 1 rfl (by
        simp only [Matrix.cons_val_zero]
        rw [Ne, hpow]; intro h; exact hi0 (Nat.eq_zero_of_dvd_of_lt h hi))
    · have hne : ∀ k : Fin 2, ![χ ^ i, χ ^ j] k ≠ 1 := by
        intro k; fin_cases k
        · simp only [Fin.zero_eta, Matrix.cons_val_zero]
          rw [Ne, hpow]; intro h; exact hi0 (Nat.eq_zero_of_dvd_of_lt h hi)
        · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one]
          rw [Ne, hpow]; intro h; exact hj0 (Nat.eq_zero_of_dvd_of_lt h hj)
      simp only [hi0, hj0, and_false, if_false, or_self, ne_eq, not_false_eq_true, true_and]
      by_cases hij : i + j = n
      · simp only [hij, if_true, not_true_eq_false, if_false, add_zero]
        obtain ⟨ψ, hψ⟩ := exists_isPrimitive_addChar (F := F)
        have hprod : ∏ k, ![χ ^ i, χ ^ j] k = 1 := by
          rw [Fin.prod_univ_two]
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
          rw [← pow_add, hij, ← hχ, pow_orderOf_eq_one]
        rw [multiJacobiSum_eq_of_prod_eq_one (r := 0) hne hprod hψ, multiJacobiSum_single]
        simp
      · simp only [hij, if_false, not_false_eq_true, if_true, zero_add]
  have hsum := numSolDiag_fermat_eq_sum hn hχ
  rw [Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl (hsplit i hi)] at hsum
  simp only [Finset.sum_add_distrib] at hsum
  -- the explicit part
  have hE_sum : ∑ i ∈ range n, ∑ j ∈ range n, E i j =
      (Fintype.card F : ℂ) + 1 - (numSolPow n (-1 : F) : ℂ) := by
    have hrow : ∀ i ∈ range n, ∑ j ∈ range n, E i j =
        if i = 0 then (Fintype.card F : ℂ) else -(χ ^ i) (-1) := by
      intro i hi
      simp only [mem_range] at hi
      by_cases hi0 : i = 0
      · subst hi0
        rw [Finset.sum_eq_single_of_mem 0 (mem_range.mpr (Nat.pos_of_ne_zero hn0))]
        · simp [hE]
        · intro j _ hj; simp [hE, hj]
      · rw [Finset.sum_eq_single_of_mem (n - i) (mem_range.mpr (by omega))]
        · simp only [hE, hi0, false_and, if_false, false_or, if_neg hi0]
          rw [if_neg (by omega), if_pos (by omega)]
          congr 1
          have : χ ^ (n - i) = (χ ^ i)⁻¹ := by
            rw [eq_inv_iff_mul_eq_one, ← pow_add, Nat.sub_add_cancel hi.le, ← hχ,
              pow_orderOf_eq_one]
          rw [this, mulChar_inv_neg_one]
        · intro j _ hj
          simp only [hE, hi0, false_and, if_false, false_or]
          split_ifs with h1 h2 <;> first | rfl | omega
    rw [Finset.sum_congr rfl hrow, Finset.sum_ite, Finset.filter_eq' (range n) 0,
      if_pos (mem_range.mpr (Nat.pos_of_ne_zero hn0)), sum_singleton]
    have h1 := numSolPow_eq_sum_range hn hχ (-1 : F)
    rw [← Finset.add_sum_erase _ _ (mem_range.mpr (Nat.pos_of_ne_zero hn0))] at h1
    simp only [pow_zero, bookChar_one] at h1
    rw [h1, Finset.sum_neg_distrib]
    have : (range n).erase 0 = ({i ∈ range n | ¬i = 0} : Finset ℕ) := by ext; simp [and_comm]
    rw [← this]
    simp_rw [bookChar_of_ne_zero _ (neg_ne_zero.mpr (one_ne_zero (α := F)))]
    ring
  -- the remainder
  have hR_norm : ‖∑ i ∈ range n, ∑ j ∈ range n, Rm i j‖ ≤
      ((n : ℝ) - 1) * ((n : ℝ) - 2) * √(Fintype.card F) := by
    refine (norm_sum_le _ _).trans ?_
    have hrow : ∀ i ∈ range n, ‖∑ j ∈ range n, Rm i j‖ ≤
        (if i = 0 then 0 else ((n : ℝ) - 2) * √(Fintype.card F)) := by
      intro i hi
      simp only [mem_range] at hi
      refine (norm_sum_le _ _).trans ?_
      by_cases hi0 : i = 0
      · subst hi0; simp [hRm]
      · rw [if_neg hi0]
        have hterm : ∀ j ∈ range n, ‖Rm i j‖ =
            if j ≠ 0 ∧ i + j ≠ n then √(Fintype.card F) else 0 := by
          intro j hj
          simp only [mem_range] at hj
          simp only [hRm, hi0, ne_eq, not_false_eq_true, true_and]
          split_ifs with h
          · have hne : ∀ k : Fin 2, ![χ ^ i, χ ^ j] k ≠ 1 := by
              intro k; fin_cases k
              · simp only [Fin.zero_eta, Matrix.cons_val_zero]
                rw [Ne, hpow]; intro h'; exact hi0 (Nat.eq_zero_of_dvd_of_lt h' hi)
              · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one]
                rw [Ne, hpow]; intro h'; exact h.1 (Nat.eq_zero_of_dvd_of_lt h' hj)
            have hprod : ∏ k, ![χ ^ i, χ ^ j] k ≠ 1 := by
              rw [Fin.prod_univ_two]
              simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
              rw [← pow_add, Ne, hpow]
              rintro ⟨k, hk⟩
              rcases k with _ | _ | k
              · omega
              · exact h.2 (by omega)
              · nlinarith
            rw [norm_multiJacobiSum (r := 1) hne hprod, pow_one]
          · simp
        rw [Finset.sum_congr rfl hterm, Finset.sum_ite, sum_const_zero, add_zero, sum_const,
          nsmul_eq_mul]
        gcongr
        have hfilt : ({j ∈ range n | j ≠ 0 ∧ i + j ≠ n} : Finset ℕ) =
            ((range n).erase 0).erase (n - i) := by
          ext j; simp only [mem_filter, mem_range, mem_erase]; omega
        rw [hfilt, card_erase_of_mem (by simp; omega), card_erase_of_mem (by simp; omega),
          card_range]
        have : 2 ≤ n := by omega
        push_cast [Nat.sub_sub, this]
        exact le_rfl
    refine (Finset.sum_le_sum hrow).trans ?_
    rw [Finset.sum_ite, sum_const_zero, zero_add, sum_const, nsmul_eq_mul]
    have : ({i ∈ range n | ¬i = 0} : Finset ℕ) = (range n).erase 0 := by
      ext; simp [and_comm]
    rw [this, card_erase_of_mem (mem_range.mpr (Nat.pos_of_ne_zero hn0)), card_range,
      Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hn0), Nat.cast_one]
    ring_nf; rfl
  rw [hsum, hE_sum, numSolPow_neg_one hn]
  have : (((if ∃ x : F, x ^ n = -1 then n else 0 : ℕ) : ℂ)) =
      (if ∃ x : F, x ^ n = -1 then (n : ℂ) else 0) := by split_ifs <;> simp
  rw [this]
  convert hR_norm using 2
  ring

end NTKB.IrelandRosen
