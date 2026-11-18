/-
Ireland–Rosen, Chapter 10, §3, Theorem 2: the number of points of the diagonal hypersurface
`a_0 y_0^m + a_1 y_1^m + ⋯ + a_n y_n^m = 0` in `P^n(F)`, `q ≡ 1 (mod m)`.
-/
import NTKB.IrelandRosen.R2.GeneralCount
import NTKB.IrelandRosen.R2.AffineProjective

open Finset
open scoped Classical LinearAlgebra.Projectivization

set_option linter.unusedSectionVars false

namespace NTKB.IrelandRosen

variable {F : Type*} [Field F] [Fintype F]

/-- Nonzero zeros of a homogeneous condition are the punctured lines through the projective
zeros: `{v ≠ 0 | Z v} ≃ {P ∈ P^n | Z P} × F^*`. -/
noncomputable def projZeroEquiv {n : ℕ} (Z : (Fin (n + 1) → F) → Prop)
    (hZ : ∀ (c : F) (v : Fin (n + 1) → F), c ≠ 0 → (Z (c • v) ↔ Z v)) :
    {P : ℙ F (Fin (n + 1) → F) // Z P.rep} × Fˣ ≃ {v : Fin (n + 1) → F // v ≠ 0 ∧ Z v} :=
  Equiv.ofBijective
    (fun p => ⟨(p.2 : F) • p.1.1.rep, smul_ne_zero p.2.ne_zero p.1.1.rep_ne_zero,
      (hZ _ _ p.2.ne_zero).mpr p.1.2⟩)
    (by
      constructor
      · rintro ⟨⟨P, hP⟩, c⟩ ⟨⟨P', hP'⟩, c'⟩ h
        simp only [Subtype.mk.injEq] at h
        have hPP' : P = P' := by
          have h1 : Projectivization.mk F ((c : F) • P.rep) (smul_ne_zero c.ne_zero P.rep_ne_zero) =
              Projectivization.mk F ((c' : F) • P'.rep)
                (smul_ne_zero c'.ne_zero P'.rep_ne_zero) := by simp_rw [h]
          have key : ∀ (Q : ℙ F (Fin (n + 1) → F)) (d : Fˣ),
              Projectivization.mk F ((d : F) • Q.rep) (smul_ne_zero d.ne_zero Q.rep_ne_zero) = Q := by
            intro Q d
            conv_rhs => rw [← Projectivization.mk_rep Q]
            exact (Projectivization.mk_eq_mk_iff' F _ _ _ _).mpr ⟨d, rfl⟩
          rwa [key, key] at h1
        subst hPP'
        have hcc : (c : F) = c' := smul_left_injective F P.rep_ne_zero h
        simp only [Prod.mk.injEq, Subtype.mk.injEq, true_and]
        exact Units.ext hcc
      · rintro ⟨v, hv, hZv⟩
        obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep F v hv
        refine ⟨⟨⟨Projectivization.mk F v hv, ?_⟩, a⁻¹⟩, ?_⟩
        · rw [← ha]; exact (hZ _ _ a.ne_zero).mpr hZv
        · simp only [Subtype.mk.injEq]
          rw [← ha]
          simp [Units.smul_def, smul_smul])

lemma card_nonzero_zeros {n : ℕ} (Z : (Fin (n + 1) → F) → Prop)
    (hZ : ∀ (c : F) (v : Fin (n + 1) → F), c ≠ 0 → (Z (c • v) ↔ Z v)) :
    Nat.card {v : Fin (n + 1) → F // v ≠ 0 ∧ Z v} =
      Nat.card {P : ℙ F (Fin (n + 1) → F) // Z P.rep} * (Fintype.card F - 1) := by
  rw [← Nat.card_congr (projZeroEquiv Z hZ), Nat.card_prod, Nat.card_eq_fintype_card (α := Fˣ),
    Fintype.card_units]

/-- The number of points of `a_0 y_0^m + ⋯ + a_n y_n^m = 0` in `P^n(F)`. -/
noncomputable def numProjDiag {n : ℕ} (a : Fin (n + 1) → F) (m : ℕ) : ℕ :=
  Nat.card {P : ℙ F (Fin (n + 1) → F) // ∑ i, a i * P.rep i ^ m = 0}

lemma numSolDiag_eq_one_add {n : ℕ} (a : Fin (n + 1) → F) {m : ℕ} (hm : m ≠ 0) :
    numSolDiag a (fun _ => m) 0 = 1 + numProjDiag a m * (Fintype.card F - 1) := by
  have hZ : ∀ (c : F) (v : Fin (n + 1) → F), c ≠ 0 →
      ((∑ i, a i * (c • v) i ^ m = 0) ↔ ∑ i, a i * v i ^ m = 0) := by
    intro c v hc
    simp only [Pi.smul_apply, smul_eq_mul, mul_pow]
    rw [show ∑ i, a i * (c ^ m * v i ^ m) = c ^ m * ∑ i, a i * v i ^ m by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring]
    exact ⟨fun h => (mul_eq_zero.mp h).resolve_left (pow_ne_zero _ hc), fun h => by rw [h, mul_zero]⟩
  have hc := card_nonzero_zeros (fun v : Fin (n + 1) → F => ∑ i, a i * v i ^ m = 0) hZ
  rw [numProjDiag, ← hc, numSolDiag, Nat.card_eq_fintype_card,
    Fintype.card_subtype, ← Finset.card_filter_add_card_filter_not (p := fun x => x = 0),
    Finset.filter_filter, Finset.filter_filter]
  congr 1
  · rw [Finset.card_eq_one]
    refine ⟨0, ?_⟩
    ext x
    simp only [mem_filter, mem_univ, true_and, mem_singleton]
    constructor
    · exact fun h => h.2
    · rintro rfl; simp [zero_pow hm]
  · congr 1; ext x; simp [and_comm]

/-- **Theorem 2 of Chapter 10, Equation (1).** If `q ≡ 1 (mod m)` and `a_i ∈ F^*`, the
hypersurface `a_0 y_0^m + ⋯ + a_n y_n^m = 0` has
`q^{n-1} + ⋯ + q + 1 + (q - 1)^{-1} ∑ χ_0(a_0⁻¹) ⋯ χ_n(a_n⁻¹) J_0(χ_0, …, χ_n)` points in `P^n(F)`,
the sum over `χ_i^m = ε`, `χ_i ≠ ε`, `χ_0 ⋯ χ_n = ε`. -/
@[kb "irelandrosen1990" "Thm 2 (§10.3), p. 158"]
theorem numProjDiag_eq {n : ℕ} {a : Fin (n + 1) → F} (ha : ∀ i, a i ≠ 0) {m : ℕ}
    (hm : m ∣ Fintype.card F - 1) :
    (numProjDiag a m : ℂ) = ∑ k ∈ range n, (Fintype.card F : ℂ) ^ k +
      (1 / ((Fintype.card F : ℂ) - 1)) *
        ∑ χ ∈ charTuples (F := F) (fun _ : Fin (n + 1) => m) with (∀ i, χ i ≠ 1) ∧ ∏ i, χ i = 1,
          (∏ i, χ i (a i)⁻¹) * multiJacobiSumZero χ := by
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [zero_dvd_iff, Nat.sub_eq_zero_iff_le] at hm
    exact absurd hm (not_le.mpr Fintype.one_lt_card)
  have h5 := (numSolDiag_zero (l := fun _ => m) ha (fun _ => hm)).1
  rw [numSolDiag_eq_one_add a hm0] at h5
  have hq1 : (1 : ℕ) ≤ Fintype.card F := Fintype.card_pos
  have hq : ((Fintype.card F : ℂ) - 1) ≠ 0 := by
    rw [sub_ne_zero]; exact_mod_cast (Fintype.one_lt_card).ne'
  push_cast [Nat.cast_sub hq1] at h5
  have hgeom : (∑ k ∈ range n, (Fintype.card F : ℂ) ^ k) * ((Fintype.card F : ℂ) - 1) =
      (Fintype.card F : ℂ) ^ n - 1 := geom_sum_mul _ _
  apply mul_right_cancel₀ hq
  rw [add_mul, mul_comm (1 / _) _, mul_assoc, one_div_mul_cancel hq, mul_one]
  linear_combination h5 - hgeom

/-- **Theorem 2 of Chapter 10, Equation (2).** If `χ_0, …, χ_n` (`n ≥ 1`) are nontrivial with
trivial product, then `(q - 1)^{-1} J_0(χ_0, …, χ_n) = q^{-1} g(χ_0) ⋯ g(χ_n)`. -/
@[kb "irelandrosen1990" "Thm 2 (§10.3), p. 158"]
theorem multiJacobiSumZero_eq_prod_gaussSum {r : ℕ} {χ : Fin (r + 2) → MulChar F ℂ}
    (hχ : ∀ i, χ i ≠ 1) (hprod : ∏ i, χ i = 1) {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) :
    (1 / ((Fintype.card F : ℂ) - 1)) * multiJacobiSumZero χ =
      (1 / (Fintype.card F : ℂ)) * ∏ i, gaussSum (χ i) ψ := by
  rw [prod_gaussSum_eq_of_prod_eq_one hχ hprod hψ, multiJacobiSumZero_eq χ (hχ _), if_pos hprod]
  have hq : ((Fintype.card F : ℂ) - 1) ≠ 0 := by
    rw [sub_ne_zero]; exact_mod_cast (Fintype.one_lt_card).ne'
  have hq' : (Fintype.card F : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp

/-- **Theorem 2 of Chapter 10**, with the Jacobi sums replaced by Gauss sums:
`N = q^{n-1} + ⋯ + 1 + q^{-1} ∑ χ_0(a_0⁻¹) ⋯ χ_n(a_n⁻¹) g(χ_0) ⋯ g(χ_n)`. -/
@[kb "irelandrosen1990" "Thm 2 (§10.3), p. 158"]
theorem numProjDiag_eq_gaussSum {n : ℕ} {a : Fin (n + 1) → F} (ha : ∀ i, a i ≠ 0) {m : ℕ}
    (hm : m ∣ Fintype.card F - 1) {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) :
    (numProjDiag a m : ℂ) = ∑ k ∈ range n, (Fintype.card F : ℂ) ^ k +
      (1 / (Fintype.card F : ℂ)) *
        ∑ χ ∈ charTuples (F := F) (fun _ : Fin (n + 1) => m) with (∀ i, χ i ≠ 1) ∧ ∏ i, χ i = 1,
          (∏ i, χ i (a i)⁻¹) * ∏ i, gaussSum (χ i) ψ := by
  rw [numProjDiag_eq ha hm, Finset.mul_sum, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun χ hχ => ?_
  simp only [mem_filter] at hχ
  obtain ⟨_, hne, hprod⟩ := hχ
  cases n with
  | zero =>
    exfalso; apply hne 0
    simpa using hprod
  | succ n =>
    rw [mul_left_comm, multiJacobiSumZero_eq_prod_gaussSum hne hprod hψ]; ring

end NTKB.IrelandRosen
