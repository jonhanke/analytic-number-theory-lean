/-
Ireland–Rosen, Chapter 11: examples and remarks around the zeta function.
* §11.1: the zeta function of the hyperplane at infinity `x_0 = 0` in `P^n` is
  `(1 - q^{n-1}u)^{-1} ⋯ (1 - qu)^{-1} (1 - u)^{-1}`.
* Remark (2) after Theorem 2 of §11.3: the reciprocal roots `α_χ` of `P(u)` have absolute value
  `q^{(n-1)/2}`.
-/
import NTKB.IrelandRosen.R2.ZetaDiagonal

open Finset PowerSeries
open scoped Classical LinearAlgebra.Projectivization

set_option linter.unusedSectionVars false

namespace NTKB.IrelandRosen

variable {F : Type*} [Field F] [Fintype F]

/-- The number of points of the hyperplane at infinity `x_0 = 0` of `P^n(K)`. -/
noncomputable def numHyperplaneAtInfinity (K : Type*) [Field K] (n : ℕ) : ℕ :=
  Nat.card {P : ℙ K (Fin (n + 1) → K) // IsAtInfinity P}

lemma numHyperplaneAtInfinity_eq (K : Type*) [Field K] [Fintype K] (n : ℕ) :
    numHyperplaneAtInfinity K n = ∑ i ∈ range n, Fintype.card K ^ i := by
  rw [numHyperplaneAtInfinity, Nat.card_congr (infinityEquiv n), card_proj]

/-- **The zeta function of the hyperplane at infinity** (§11.1): with `N_s = #P^{n-1}(F_s)`,
`Z(u) (1 - u)(1 - qu) ⋯ (1 - q^{n-1}u) = 1`. -/
@[kb "irelandrosen1990" "§11.1, Z for x_0 = 0, p. 163"]
theorem zeta_hyperplaneAtInfinity (E : ℕ → Type*) [∀ s, Field (E s)] [∀ s, Fintype (E s)]
    [∀ s, Algebra F (E s)] (hE : ∀ s, 1 ≤ s → Module.finrank F (E s) = s) (n : ℕ) :
    zetaOfCounts (fun s => (numHyperplaneAtInfinity (E s) n : ℂ)) *
      ∏ k ∈ range n, (1 - C ((Fintype.card F : ℂ) ^ k) * X) = 1 := by
  have := (zetaOfCounts_mul_eq_iff (fun s => (numHyperplaneAtInfinity (E s) n : ℂ)) 0
    ((range n).val.map fun k => (Fintype.card F : ℂ) ^ k)).mpr (by
      intro s hs
      rw [numHyperplaneAtInfinity_eq, card_extension (F := F), hE s hs]
      simp only [Multiset.map_map, Function.comp_def, Multiset.map_zero, Multiset.sum_zero,
        sub_zero]
      rw [← Finset.sum_eq_multiset_sum]
      push_cast
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← pow_mul, ← pow_mul, mul_comm])
  simp only [Multiset.map_map, Function.comp_def, Multiset.map_zero, Multiset.prod_zero] at this
  rw [← Finset.prod_eq_multiset_prod] at this
  exact this

/-- **Remark (2) after Theorem 2 of §11.3.** The reciprocal roots `α_χ` of `P(u)` have absolute
value `q^{(n-1)/2}`, so the zeros of `Z_f(u)` have absolute value `q^{-(n-1)/2}`. -/
@[kb "irelandrosen1990" "Thm 2 (§11.3), Remark (2), p. 173"]
theorem norm_diagAlpha {n : ℕ} {a : Fin (n + 1) → F} (ha : ∀ i, a i ≠ 0) {m : ℕ}
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {χ : Fin (n + 1) → MulChar F ℂ}
    (hχ : χ ∈ diagTuples F n m) :
    ‖diagAlpha a ψ χ‖ = √(Fintype.card F) ^ (n - 1 : ℤ) := by
  simp only [diagTuples, mem_filter] at hχ
  obtain ⟨_, hne, _⟩ := hχ
  have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hsq : √(Fintype.card F : ℝ) ^ 2 = Fintype.card F := Real.sq_sqrt hq.le
  have hs0 : √(Fintype.card F : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hq).ne'
  rw [diagAlpha, norm_mul, norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
    norm_prod, norm_prod]
  simp only [norm_mulChar_apply _ (inv_ne_zero (ha _)), prod_const_one, mul_one,
    norm_gaussSum (hne _) hψ, prod_const, card_univ, Fintype.card_fin]
  rw [norm_div, norm_one, Complex.norm_natCast, zpow_sub₀ hs0, zpow_natCast, zpow_one]
  nth_rewrite 1 [← hsq]
  field_simp
  ring

end NTKB.IrelandRosen
