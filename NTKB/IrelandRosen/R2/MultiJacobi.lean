/-
Ireland–Rosen, Chapter 8, §5: Jacobi sums of `r` characters.

`J(χ_1, …, χ_r) = ∑_{t_1 + ⋯ + t_r = 1} χ_1(t_1) ⋯ χ_r(t_r)` and
`J_0(χ_1, …, χ_r) = ∑_{t_1 + ⋯ + t_r = 0} χ_1(t_1) ⋯ χ_r(t_r)`, with the book's convention
`ε(0) = 1` for the trivial character (`bookChar`). Mathlib has only the binary `jacobiSum`
(with the other convention `ε(0) = 0`); `multiJacobiSum_two` compares the two.

Over an arbitrary finite field `F` with `q` elements (Chapter 10, §3: "replace p by q").
-/
import NTKB.IrelandRosen.R2.Characters
import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality

open Finset
open scoped Classical

set_option linter.unusedSectionVars false

namespace NTKB.IrelandRosen

variable {F : Type*} [Field F] [Fintype F]
variable {R : Type*} [CommRing R]

/-- `∑_{t_1 + ⋯ + t_r = b} χ_1(t_1) ⋯ χ_r(t_r)` (book convention `ε(0) = 1`). -/
noncomputable def multiJacobiSumAt {r : ℕ} (χ : Fin r → MulChar F R) (b : F) : R :=
  ∑ t : Fin r → F with ∑ i, t i = b, ∏ i, bookChar (χ i) (t i)

/-- **The Jacobi sum of `r` characters** (Ireland–Rosen, Chapter 8, §5):
`J(χ_1, …, χ_r) = ∑_{t_1 + ⋯ + t_r = 1} χ_1(t_1) ⋯ χ_r(t_r)`. -/
noncomputable def multiJacobiSum {r : ℕ} (χ : Fin r → MulChar F R) : R :=
  multiJacobiSumAt χ 1

/-- The companion sum `J_0(χ_1, …, χ_r) = ∑_{t_1 + ⋯ + t_r = 0} χ_1(t_1) ⋯ χ_r(t_r)`. -/
noncomputable def multiJacobiSumZero {r : ℕ} (χ : Fin r → MulChar F R) : R :=
  multiJacobiSumAt χ 0

/-! ### Auxiliary lemmas -/

lemma mulChar_prod_apply {ι : Type*} (s : Finset ι) (χ : ι → MulChar F R) {a : F} (ha : a ≠ 0) :
    (∏ i ∈ s, χ i) a = ∏ i ∈ s, χ i a := by
  induction s using Finset.cons_induction with
  | empty => simp [MulChar.one_apply (Ne.isUnit ha)]
  | cons j s hj ih => rw [prod_cons, prod_cons, MulChar.mul_apply, ih]

lemma addChar_sum {ι : Type*} (s : Finset ι) (ψ : AddChar F R) (t : ι → F) :
    ψ (∑ i ∈ s, t i) = ∏ i ∈ s, ψ (t i) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons j s hj ih => rw [sum_cons, prod_cons, AddChar.map_add_eq_mul, ih]

/-- Summing over `t_1 + ⋯ + t_{r+1} = b`: the coordinate `t_j` is determined by the others. -/
lemma sum_filter_sum_eq_insertNth {r : ℕ} (G : (Fin (r + 1) → F) → R) (b : F) (j : Fin (r + 1)) :
    ∑ t : Fin (r + 1) → F with ∑ i, t i = b, G t =
      ∑ u : Fin r → F, G (Fin.insertNth j (b - ∑ i, u i) u) := by
  have key : ∀ t : Fin (r + 1) → F, ∑ i, t i = b →
      Fin.insertNth j (b - ∑ i, Fin.removeNth j t i) (Fin.removeNth j t) = t := by
    intro t ht
    rw [Fin.sum_univ_succAbove _ j] at ht
    have : t j = b - ∑ i, Fin.removeNth j t i := by rw [← ht]; simp [Fin.removeNth]
    rw [← this]; simp
  refine Finset.sum_nbij' (fun t => Fin.removeNth j t) (fun u => Fin.insertNth j (b - ∑ i, u i) u)
    ?_ ?_ ?_ ?_ ?_
  · intro t _; simp
  · intro u _
    simp only [mem_filter, mem_univ, true_and]
    rw [Fin.sum_univ_succAbove _ j]
    simp
  · intro t ht
    simp only [mem_coe, mem_filter, mem_univ, true_and] at ht
    exact key t ht
  · intro u _; simp
  · intro t ht
    simp only [mem_filter, mem_univ, true_and] at ht
    rw [key t ht]

lemma sum_filter_sum_eq_snoc {r : ℕ} (G : (Fin (r + 1) → F) → R) (b : F) :
    ∑ t : Fin (r + 1) → F with ∑ i, t i = b, G t =
      ∑ u : Fin r → F, G (Fin.snoc u (b - ∑ i, u i)) := by
  rw [sum_filter_sum_eq_insertNth G b (Fin.last r)]
  simp [Fin.insertNth_last']

/-- `∑_{t} ∏ χ_i(t_i) ψ(∑ t_i)` regrouped by the value of `∑ t_i`. -/
lemma sum_eq_sum_multiJacobiSumAt {r : ℕ} (χ : Fin r → MulChar F R) (ψ : F → R) :
    ∑ t : Fin r → F, (∏ i, bookChar (χ i) (t i)) * ψ (∑ i, t i) =
      ∑ s : F, multiJacobiSumAt χ s * ψ s := by
  rw [← Finset.sum_fiberwise univ (fun t : Fin r → F => ∑ i, t i)]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [multiJacobiSumAt, Finset.sum_mul]
  refine Finset.sum_congr rfl fun t ht => ?_
  simp only [mem_filter, mem_univ, true_and] at ht
  rw [ht]

/-- Scaling: for `b ≠ 0`, `∑_{∑ t_i = b} ∏ χ_i(t_i) = (χ_1 ⋯ χ_r)(b) J(χ_1, …, χ_r)`. -/
theorem multiJacobiSumAt_of_ne_zero {r : ℕ} (χ : Fin r → MulChar F R) {b : F} (hb : b ≠ 0) :
    multiJacobiSumAt χ b = (∏ i, χ i) b * multiJacobiSum χ := by
  rw [multiJacobiSum, multiJacobiSumAt, multiJacobiSumAt, Finset.mul_sum]
  refine Finset.sum_nbij' (fun t => fun i => b⁻¹ * t i) (fun t => fun i => b * t i) ?_ ?_ ?_ ?_ ?_
  · intro t ht
    simp only [mem_filter, mem_univ, true_and] at ht ⊢
    rw [← Finset.mul_sum, ht, inv_mul_cancel₀ hb]
  · intro t ht
    simp only [mem_filter, mem_univ, true_and] at ht ⊢
    rw [← Finset.mul_sum, ht, mul_one]
  · intro t _; ext i; simp [hb]
  · intro t _; ext i; simp [hb]
  · intro t _
    simp only
    rw [mulChar_prod_apply _ _ hb, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← bookChar_mul_of_ne_zero _ hb, mul_inv_cancel_left₀ hb]

/-! ### Proposition 8.5.1 -/

/-- **Proposition 8.5.1 (a).** `J_0(ε, …, ε) = J(ε, …, ε) = q^{r-1}` (here with `r + 1`
characters; the same holds for the sum over `t_1 + ⋯ + t_{r+1} = b` for every `b`). -/
@[kb "irelandrosen1990" "Prop 8.5.1, p. 110"]
theorem multiJacobiSumAt_one {r : ℕ} (b : F) :
    multiJacobiSumAt (fun _ : Fin (r + 1) => (1 : MulChar F R)) b = (Fintype.card F : R) ^ r := by
  rw [multiJacobiSumAt, sum_filter_sum_eq_snoc]
  simp [bookChar_one, Fintype.card_fun, Fintype.card_fin]

@[kb "irelandrosen1990" "Prop 8.5.1, p. 110"]
theorem multiJacobiSum_one_one {r : ℕ} :
    multiJacobiSumZero (fun _ : Fin (r + 1) => (1 : MulChar F R)) = (Fintype.card F : R) ^ r ∧
      multiJacobiSum (fun _ : Fin (r + 1) => (1 : MulChar F R)) = (Fintype.card F : R) ^ r :=
  ⟨multiJacobiSumAt_one 0, multiJacobiSumAt_one 1⟩

/-- **Proposition 8.5.1 (b)**, for every right-hand side `b`: if some but not all of the `χ_i`
are trivial, the sum vanishes. -/
theorem multiJacobiSumAt_eq_zero [IsDomain R] {r : ℕ} {χ : Fin r → MulChar F R} (b : F)
    {j k : Fin r} (hj : χ j = 1) (hk : χ k ≠ 1) : multiJacobiSumAt χ b = 0 := by
  cases r with
  | zero => exact j.elim0
  | succ r =>
  rw [multiJacobiSumAt, sum_filter_sum_eq_insertNth _ b j]
  have hjk : k ≠ j := by rintro rfl; exact hk hj
  obtain ⟨k', rfl⟩ := Fin.exists_succAbove_eq hjk
  simp_rw [Fin.prod_univ_succAbove _ j, Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove,
    hj, bookChar_one, one_mul]
  rw [← Fintype.piFinset_univ, ← Finset.prod_univ_sum]
  refine Finset.prod_eq_zero (mem_univ k') ?_
  rw [sum_bookChar, if_neg hk]

@[kb "irelandrosen1990" "Prop 8.5.1, p. 110"]
theorem multiJacobiSum_eq_zero_of_some_trivial [IsDomain R] {r : ℕ} {χ : Fin r → MulChar F R}
    (hj : ∃ j, χ j = 1) (hk : ∃ k, χ k ≠ 1) :
    multiJacobiSumZero χ = 0 ∧ multiJacobiSum χ = 0 := by
  obtain ⟨j, hj⟩ := hj; obtain ⟨k, hk⟩ := hk
  exact ⟨multiJacobiSumAt_eq_zero 0 hj hk, multiJacobiSumAt_eq_zero 1 hj hk⟩

/-- **Proposition 8.5.1 (c).** If `χ_{r+1} ≠ ε`, then `J_0(χ_1, …, χ_{r+1})` is `0` if the
product `χ_1 ⋯ χ_{r+1}` is nontrivial and `χ_{r+1}(-1) (q - 1) J(χ_1, …, χ_r)` otherwise. -/
@[kb "irelandrosen1990" "Prop 8.5.1, p. 110"]
theorem multiJacobiSumZero_eq [IsDomain R] {r : ℕ} (χ : Fin (r + 1) → MulChar F R)
    (hχ : χ (Fin.last r) ≠ 1) :
    multiJacobiSumZero χ = if ∏ i, χ i = 1 then
      χ (Fin.last r) (-1) * ((Fintype.card F : R) - 1) * multiJacobiSum (Fin.init χ) else 0 := by
  set χr := χ (Fin.last r)
  have step1 : multiJacobiSumZero χ =
      ∑ u : Fin r → F, (∏ i, bookChar (Fin.init χ i) (u i)) * χr (-∑ i, u i) := by
    rw [multiJacobiSumZero, multiJacobiSumAt, sum_filter_sum_eq_snoc]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Fin.prod_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last, zero_sub, Fin.init]
    rw [bookChar_of_ne_one hχ]
  have step2 : multiJacobiSumZero χ =
      ∑ s : F, χr (-1) * (∏ i, χ i) s * multiJacobiSum (Fin.init χ) := by
    rw [step1, sum_eq_sum_multiJacobiSumAt (Fin.init χ) (fun s => χr (-s))]
    refine Finset.sum_congr rfl fun s _ => ?_
    by_cases hs : s = 0
    · subst hs; rw [MulChar.map_zero, neg_zero, MulChar.map_zero]; ring
    · rw [multiJacobiSumAt_of_ne_zero _ hs, Fin.prod_univ_castSucc, MulChar.mul_apply]
      rw [show -s = -1 * s by ring, map_mul]
      simp only [Fin.init]
      ring
  rw [step2, ← Finset.sum_mul, ← Finset.mul_sum]
  split_ifs with h
  · rw [h, MulChar.sum_one_eq_card_units, Fintype.card_units, Nat.cast_sub Fintype.card_pos,
      Nat.cast_one]
  · rw [MulChar.sum_eq_zero_of_ne_one h]; ring

/-- For nontrivial characters `bookChar` is the character itself. -/
lemma multiJacobiSumAt_eq_of_ne_one {r : ℕ} {χ : Fin r → MulChar F R} (hχ : ∀ i, χ i ≠ 1)
    (b : F) : multiJacobiSumAt χ b = ∑ t : Fin r → F with ∑ i, t i = b, ∏ i, χ i (t i) := by
  simp [multiJacobiSumAt, bookChar_of_ne_one (hχ _)]

/-- `J_0 = 0` if all `χ_i` and their product are nontrivial. -/
lemma multiJacobiSumZero_eq_zero [IsDomain R] {r : ℕ} {χ : Fin r → MulChar F R}
    (hχ : ∀ i, χ i ≠ 1) (hprod : ∏ i, χ i ≠ 1) : multiJacobiSumZero χ = 0 := by
  cases r with
  | zero => simp at hprod
  | succ r => rw [multiJacobiSumZero_eq χ (hχ _), if_neg hprod]

/-! ### Theorem 3 and its corollaries -/

lemma prod_gaussSum_eq_sum {r : ℕ} {χ : Fin r → MulChar F R} (hχ : ∀ i, χ i ≠ 1)
    (ψ : AddChar F R) :
    ∏ i, gaussSum (χ i) ψ = ∑ s : F, multiJacobiSumAt χ s * ψ s := by
  rw [← sum_eq_sum_multiJacobiSumAt χ ψ]
  simp only [gaussSum, Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [addChar_sum, ← Finset.prod_mul_distrib]
  simp [bookChar_of_ne_one (hχ _)]

/-- **Theorem 3 (Chapter 8).** If `χ_1, …, χ_r` and `χ_1 ⋯ χ_r` are nontrivial, then
`g(χ_1) ⋯ g(χ_r) = J(χ_1, …, χ_r) g(χ_1 ⋯ χ_r)`. (Any additive character `ψ` works.) -/
@[kb "irelandrosen1990" "Thm 3, p. 111"]
theorem prod_gaussSum_eq_multiJacobiSum_mul [IsDomain R] {r : ℕ} {χ : Fin r → MulChar F R}
    (hχ : ∀ i, χ i ≠ 1) (hprod : ∏ i, χ i ≠ 1) (ψ : AddChar F R) :
    ∏ i, gaussSum (χ i) ψ = multiJacobiSum χ * gaussSum (∏ i, χ i) ψ := by
  rw [prod_gaussSum_eq_sum hχ, gaussSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases hs : s = 0
  · subst hs
    rw [show multiJacobiSumAt χ 0 = multiJacobiSumZero χ from rfl,
      multiJacobiSumZero_eq_zero hχ hprod, MulChar.map_zero]
    ring
  · rw [multiJacobiSumAt_of_ne_zero _ hs]; ring

/-- `g(χ) g(χ⁻¹) = χ(-1) q` for `χ ≠ ε` and `ψ` primitive. -/
lemma gaussSum_mul_gaussSum_inv [IsDomain R] {χ : MulChar F R} (hχ : χ ≠ 1) {ψ : AddChar F R}
    (hψ : ψ.IsPrimitive) :
    gaussSum χ ψ * gaussSum χ⁻¹ ψ = χ (-1) * Fintype.card F := by
  have h := gaussSum_mul_gaussSum_eq_card hχ hψ
  rw [gaussSum_inv_right, MulChar.inv_apply', inv_neg, inv_one] at h
  have h1 : χ (-1) * χ (-1) = 1 := by rw [← map_mul]; simp
  calc gaussSum χ ψ * gaussSum χ⁻¹ ψ = χ (-1) * (gaussSum χ ψ * (χ (-1) * gaussSum χ⁻¹ ψ)) := by
        rw [mul_left_comm (χ (-1)), ← mul_assoc (χ (-1)), h1, one_mul]
    _ = χ (-1) * Fintype.card F := by rw [h]

/-- **Corollary 1 to Theorem 3.** If `χ_1, …, χ_{r+2}` are nontrivial and their product is
trivial, then `g(χ_1) ⋯ g(χ_{r+2}) = χ_{r+2}(-1) q J(χ_1, …, χ_{r+1})`. -/
@[kb "irelandrosen1990" "Thm 3, Cor 1, p. 111"]
theorem prod_gaussSum_eq_of_prod_eq_one [IsDomain R] {r : ℕ} {χ : Fin (r + 2) → MulChar F R}
    (hχ : ∀ i, χ i ≠ 1) (hprod : ∏ i, χ i = 1) {ψ : AddChar F R} (hψ : ψ.IsPrimitive) :
    ∏ i, gaussSum (χ i) ψ =
      χ (Fin.last _) (-1) * Fintype.card F * multiJacobiSum (Fin.init χ) := by
  have hinit : ∏ i, Fin.init χ i = (χ (Fin.last _))⁻¹ := by
    rw [Fin.prod_univ_castSucc] at hprod
    exact eq_inv_of_mul_eq_one_left hprod
  have hinit' : ∏ i, Fin.init χ i ≠ 1 := by rw [hinit]; exact inv_ne_one.mpr (hχ _)
  rw [Fin.prod_univ_castSucc]
  have h3 := prod_gaussSum_eq_multiJacobiSum_mul (χ := Fin.init χ)
    (fun i => hχ (Fin.castSucc i)) hinit' ψ
  change (∏ i, gaussSum (Fin.init χ i) ψ) * _ = _
  rw [h3, hinit, mul_assoc]
  have h4 := gaussSum_mul_gaussSum_inv (inv_ne_one.mpr (hχ (Fin.last _))) hψ
  rw [inv_inv, MulChar.inv_apply', inv_neg, inv_one] at h4
  rw [h4]; ring

/-- **Corollary 2 to Theorem 3.** Under the hypotheses of Corollary 1,
`J(χ_1, …, χ_{r+2}) = -χ_{r+2}(-1) J(χ_1, …, χ_{r+1})`. -/
@[kb "irelandrosen1990" "Thm 3, Cor 2, p. 111"]
theorem multiJacobiSum_eq_of_prod_eq_one [IsDomain R] {r : ℕ} {χ : Fin (r + 2) → MulChar F R}
    (hχ : ∀ i, χ i ≠ 1) (hprod : ∏ i, χ i = 1) {ψ : AddChar F R} (hψ : ψ.IsPrimitive) :
    multiJacobiSum χ = -χ (Fin.last _) (-1) * multiJacobiSum (Fin.init χ) := by
  have h1 := prod_gaussSum_eq_sum hχ ψ
  rw [prod_gaussSum_eq_of_prod_eq_one hχ hprod hψ] at h1
  have hsum : ∑ s : F, multiJacobiSumAt χ s * ψ s =
      multiJacobiSumZero χ + multiJacobiSum χ * (∑ s, ψ s - 1) := by
    rw [← Finset.add_sum_erase _ _ (mem_univ (0 : F))]
    have : ∀ s ∈ univ.erase (0 : F), multiJacobiSumAt χ s * ψ s = multiJacobiSum χ * ψ s := by
      intro s hs
      rw [multiJacobiSumAt_of_ne_zero _ (ne_of_mem_erase hs), hprod,
        MulChar.one_apply (Ne.isUnit (ne_of_mem_erase hs)), one_mul]
    rw [Finset.sum_congr rfl this, ← Finset.mul_sum, Finset.sum_erase_eq_sub (mem_univ 0),
      AddChar.map_zero_eq_one, mul_one]
    rfl
  have hψ1 : ψ ≠ 1 := by
    intro h; apply hψ one_ne_zero; ext x; simp [h]
  rw [hsum, AddChar.sum_eq_zero_of_ne_one hψ1, multiJacobiSumZero_eq χ (hχ _), if_pos hprod] at h1
  linear_combination h1

/-! ### Theorem 4: absolute values -/

/-- A nontrivial additive character of `F` with complex values (it is then primitive). -/
lemma exists_isPrimitive_addChar : ∃ ψ : AddChar F ℂ, ψ.IsPrimitive := by
  obtain ⟨ψ, hψ⟩ := AddChar.exists_apply_ne_zero.mpr (one_ne_zero : (1 : F) ≠ 0)
  exact ⟨ψ, AddChar.IsPrimitive.of_ne_one (fun h => hψ (by simp [h]))⟩

/-- `‖g(χ)‖ = √q` for `χ ≠ ε` and `ψ` primitive (Proposition 8.2.2; the four-line argument of
Tau Ceti's `TauCeti.norm_gaussSum`, reproved here). -/
lemma norm_gaussSum {χ : MulChar F ℂ} (hχ : χ ≠ 1) {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) :
    ‖gaussSum χ ψ‖ = √(Fintype.card F) := by
  have h := gaussSum_mul_gaussSum_eq_card hχ hψ
  rw [← star_gaussSum_eq, ← starRingEnd_apply, Complex.mul_conj'] at h
  rw [← Real.sqrt_sq (norm_nonneg _)]
  exact congrArg Real.sqrt (by exact_mod_cast h)

lemma norm_mulChar_neg_one (χ : MulChar F ℂ) : ‖χ (-1)‖ = 1 := by
  have h : χ (-1) * χ (-1) = 1 := by rw [← map_mul]; simp
  have := congrArg norm h
  rw [norm_mul, norm_one] at this
  nlinarith [norm_nonneg (χ (-1))]

/-- **Theorem 4 (a).** If `χ_1, …, χ_{r+1}` and their product are nontrivial, then
`|J(χ_1, …, χ_{r+1})| = q^{r/2}`. -/
@[kb "irelandrosen1990" "Thm 4, p. 112"]
theorem norm_multiJacobiSum {r : ℕ} {χ : Fin (r + 1) → MulChar F ℂ} (hχ : ∀ i, χ i ≠ 1)
    (hprod : ∏ i, χ i ≠ 1) : ‖multiJacobiSum χ‖ = √(Fintype.card F) ^ r := by
  obtain ⟨ψ, hψ⟩ := exists_isPrimitive_addChar (F := F)
  have h := congrArg norm (prod_gaussSum_eq_multiJacobiSum_mul hχ hprod ψ)
  rw [norm_prod, norm_mul, norm_gaussSum hprod hψ] at h
  simp only [norm_gaussSum (hχ _) hψ, prod_const, card_univ, Fintype.card_fin, pow_succ] at h
  have hq : 0 < √(Fintype.card F : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast Fintype.card_pos)
  exact (mul_right_cancel₀ hq.ne' h).symm

/-- **Theorem 4 (b).** If `χ_1, …, χ_{r+2}` are nontrivial and their product is trivial, then
`|J_0(χ_1, …, χ_{r+2})| = (q - 1) q^{r/2}` and `|J(χ_1, …, χ_{r+2})| = q^{r/2}`. -/
@[kb "irelandrosen1990" "Thm 4, p. 112"]
theorem norm_multiJacobiSum_of_prod_eq_one {r : ℕ} {χ : Fin (r + 2) → MulChar F ℂ}
    (hχ : ∀ i, χ i ≠ 1) (hprod : ∏ i, χ i = 1) :
    ‖multiJacobiSumZero χ‖ = (Fintype.card F - 1) * √(Fintype.card F) ^ r ∧
      ‖multiJacobiSum χ‖ = √(Fintype.card F) ^ r := by
  obtain ⟨ψ, hψ⟩ := exists_isPrimitive_addChar (F := F)
  have hinit : ∏ i, Fin.init χ i ≠ 1 := by
    rw [Fin.prod_univ_castSucc] at hprod
    change ∏ i, χ (Fin.castSucc i) ≠ 1
    rw [eq_inv_of_mul_eq_one_left hprod]; exact inv_ne_one.mpr (hχ _)
  have ha := norm_multiJacobiSum (χ := Fin.init χ) (fun i => hχ (Fin.castSucc i)) hinit
  refine ⟨?_, ?_⟩
  · rw [multiJacobiSumZero_eq χ (hχ _), if_pos hprod, norm_mul, norm_mul, norm_mulChar_neg_one,
      one_mul]
    rw [ha]
    congr 1
    have h1 : (1 : ℝ) ≤ Fintype.card F := by exact_mod_cast Fintype.card_pos
    rw [show ((Fintype.card F : ℂ) - 1) = (((Fintype.card F : ℝ) - 1 : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  · rw [multiJacobiSum_eq_of_prod_eq_one hχ hprod hψ, norm_mul, norm_neg, norm_mulChar_neg_one,
      one_mul]
    exact ha

/-- Comparison with Mathlib's binary Jacobi sum (which uses `ε(0) = 0`): for nontrivial
characters the two agree. -/
theorem multiJacobiSum_two {χ φ : MulChar F R} (hχ : χ ≠ 1) (hφ : φ ≠ 1) :
    multiJacobiSum ![χ, φ] = jacobiSum χ φ := by
  rw [multiJacobiSum, multiJacobiSumAt, sum_filter_sum_eq_snoc, jacobiSum]
  rw [← (Equiv.funUnique (Fin 1) F).symm.sum_comp]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp [Fin.prod_univ_two, bookChar_of_ne_one hχ, bookChar_of_ne_one hφ, Fin.snoc]

end NTKB.IrelandRosen
