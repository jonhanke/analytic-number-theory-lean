/-
Ireland–Rosen, Chapter 11, §3: the zeta function of the diagonal hypersurface
`a_0 x_0^m + a_1 x_1^m + ⋯ + a_n x_n^m = 0` is rational (Theorem 2), with the lifting of characters
to extensions (Exercise 11.16) and the formula (6) for the number of points over `F_s`.

The extensions `F_s` of degree `s` are given as a family `E s` of finite fields with
`[E s : F] = s`; by Proposition 11.1.2 (`algEquiv_of_finrank_eq` below) the counts do not depend
on the choice.
-/
import NTKB.IrelandRosen.R2.Diagonal
import NTKB.IrelandRosen.R2.HasseDavenport
import NTKB.IrelandRosen.R2.ZetaSeries

open Finset PowerSeries
open scoped Classical

set_option linter.unusedSectionVars false

namespace NTKB.IrelandRosen

section Lift

variable {F : Type*} [Field F] [Fintype F] {E : Type*} [Field E] [Fintype E] [Algebra F E]

/-- The number of characters of order dividing `m` is `m` when `m ∣ q - 1`. -/
lemma card_filter_pow_eq_one {K : Type*} [Field K] [Fintype K] {m : ℕ}
    (hm : m ∣ Fintype.card K - 1) : #{χ : MulChar K ℂ | χ ^ m = 1} = m := by
  obtain ⟨χ, hχ⟩ := exists_orderOf_eq hm
  have h := filter_pow_eq_one_eq_image hm hχ
  rw [h.1, card_image_of_injOn h.2, card_range]

/-- `χ ↦ χ' = χ ∘ N_{E/F}` as a group homomorphism. -/
noncomputable def liftNormHom : MulChar F ℂ →* MulChar E ℂ where
  toFun := liftNorm
  map_one' := by
    refine MulChar.ext fun a => ?_
    rw [liftNorm_apply, MulChar.one_apply ((a.isUnit).map (Algebra.norm F)),
      MulChar.one_apply a.isUnit]
  map_mul' χ χ' := MulChar.ext fun a => by simp [liftNorm_apply]

lemma liftNormHom_apply (χ : MulChar F ℂ) : liftNormHom (E := E) χ = liftNorm χ := rfl

lemma liftNorm_injective : Function.Injective (liftNorm (E := E) (R := ℂ) (F := F)) := by
  intro χ₁ χ₂ h
  refine MulChar.ext fun u => ?_
  obtain ⟨a, ha⟩ := FiniteField.norm_surjective F E (u : F)
  have := congrArg (fun χ : MulChar E ℂ => χ a) h
  simp only [liftNorm_apply, ha] at this
  exact this

/-- **Exercise 11.16 (b).** `χ ≠ ε` implies `χ' ≠ ε`. -/
@[kb "irelandrosen1990" "Exercise 11.16, p. 170"]
theorem liftNorm_ne_one {χ : MulChar F ℂ} (hχ : χ ≠ 1) : liftNorm (E := E) χ ≠ 1 := by
  intro h
  apply hχ
  apply liftNorm_injective (E := E)
  rw [h, ← liftNormHom_apply, map_one]

/-- **Exercise 11.16 (c).** `χ^m = ε` implies `χ'^m = ε`. -/
@[kb "irelandrosen1990" "Exercise 11.16, p. 170"]
theorem liftNorm_pow_eq_one {χ : MulChar F ℂ} {m : ℕ} (hχ : χ ^ m = 1) :
    liftNorm (E := E) χ ^ m = 1 := by
  rw [← liftNormHom_apply, ← map_pow, hχ, map_one]

/-- **Exercise 11.16 (d).** `χ'(a) = χ(a)^s` for `a ∈ F`, `s = [E : F]`. -/
@[kb "irelandrosen1990" "Exercise 11.16, p. 170"]
theorem liftNorm_algebraMap (χ : MulChar F ℂ) (a : F) :
    liftNorm (E := E) χ (algebraMap F E a) = χ a ^ Module.finrank F E := by
  rw [liftNorm_apply, Algebra.norm_algebraMap, map_pow]

lemma card_extension : Fintype.card E = Fintype.card F ^ Module.finrank F E :=
  Module.card_eq_pow_finrank

lemma dvd_card_extension_sub_one {m : ℕ} (hm : m ∣ Fintype.card F - 1) :
    m ∣ Fintype.card E - 1 := by
  rw [card_extension (F := F)]
  refine hm.trans ?_
  simpa using Nat.sub_dvd_pow_sub_pow (Fintype.card F) 1 (Module.finrank F E)

/-- **Exercise 11.16 (e).** If `q ≡ 1 (mod m)`, then as `χ` runs over the characters of `F` of
order dividing `m`, `χ'` runs over the characters of `E` of order dividing `m`. -/
@[kb "irelandrosen1990" "Exercise 11.16, p. 170"]
theorem image_liftNorm {m : ℕ} (hm : m ∣ Fintype.card F - 1) :
    ({χ : MulChar F ℂ | χ ^ m = 1} : Finset _).image (liftNorm (E := E)) =
      ({χ : MulChar E ℂ | χ ^ m = 1} : Finset _) := by
  apply Finset.eq_of_subset_of_card_le
  · intro χ' hχ'
    simp only [mem_image, mem_filter, mem_univ, true_and] at hχ' ⊢
    obtain ⟨χ, hχ, rfl⟩ := hχ'
    exact liftNorm_pow_eq_one hχ
  · rw [card_filter_pow_eq_one (dvd_card_extension_sub_one hm),
      card_image_of_injective _ liftNorm_injective, card_filter_pow_eq_one hm]

/-- `ψ' = ψ ∘ tr_{E/F}` is nontrivial if `ψ` is. -/
lemma liftTrace_ne_one {ψ : AddChar F ℂ} (hψ : ψ ≠ 1) : liftTrace (E := E) ψ ≠ 1 := by
  obtain ⟨x, hx⟩ := AddChar.ne_one_iff.mp hψ
  obtain ⟨y, hy⟩ := Algebra.trace_surjective F E x
  intro h
  have := congrArg (fun φ : AddChar E ℂ => φ y) h
  simp only [liftTrace_apply, hy, AddChar.one_apply] at this
  exact hx this

/-- **Proposition 11.1.2.** Two fields containing `F` with the same (finite) degree over `F` are
isomorphic over `F`. -/
@[kb "irelandrosen1990" "Prop 11.1.2, p. 167"]
theorem algEquiv_of_finrank_eq (E' : Type*) [Field E'] [Fintype E'] [Algebra F E']
    (h : Module.finrank F E = Module.finrank F E') : Nonempty (E ≃ₐ[F] E') := by
  have hc : Fintype.card E = Fintype.card E' := by
    rw [card_extension (F := F), card_extension (F := F) (E := E'), h]
  have h1 := FiniteField.isSplittingField_sub E F
  have h2 := FiniteField.isSplittingField_sub E' F
  rw [hc] at h1
  exact ⟨(h1.algEquiv _).trans (h2.algEquiv _).symm⟩

end Lift

section Diagonal

variable {F : Type*} [Field F] [Fintype F]

/-- The tuples `(χ_0, …, χ_n)` with `χ_i^m = ε`, `χ_i ≠ ε`, `χ_0 ⋯ χ_n = ε`. -/
noncomputable def diagTuples (K : Type*) [Field K] [Fintype K] (n m : ℕ) :
    Finset (Fin (n + 1) → MulChar K ℂ) :=
  {χ ∈ charTuples (F := K) (fun _ : Fin (n + 1) => m) | (∀ i, χ i ≠ 1) ∧ ∏ i, χ i = 1}

lemma image_lift_diagTuples (E : Type*) [Field E] [Fintype E] [Algebra F E] {n m : ℕ}
    (hm : m ∣ Fintype.card F - 1) :
    (diagTuples F n m).image (fun χ => fun i => liftNorm (E := E) (χ i)) = diagTuples E n m := by
  have himg := image_liftNorm (E := E) hm
  ext χ'
  simp only [diagTuples, mem_image, mem_filter, charTuples, Fintype.mem_piFinset, mem_univ,
    true_and]
  constructor
  · rintro ⟨χ, ⟨hpow, hne, hprod⟩, rfl⟩
    refine ⟨fun i => liftNorm_pow_eq_one (hpow i), fun i => liftNorm_ne_one (hne i), ?_⟩
    have : ∏ i, liftNorm (E := E) (χ i) = liftNormHom (∏ i, χ i) := by
      rw [map_prod]; rfl
    rw [this, hprod, map_one]
  · rintro ⟨hpow, hne, hprod⟩
    have hex : ∀ i, ∃ χ : MulChar F ℂ, χ ^ m = 1 ∧ liftNorm χ = χ' i := by
      intro i
      have : χ' i ∈ ({χ : MulChar E ℂ | χ ^ m = 1} : Finset _) := by simpa using hpow i
      rw [← himg] at this
      simpa using this
    choose χ hχ using hex
    refine ⟨χ, ⟨fun i => (hχ i).1, fun i h => hne i ?_, ?_⟩, funext fun i => (hχ i).2⟩
    · rw [← (hχ i).2, h, ← liftNormHom_apply, map_one]
    · apply liftNorm_injective (E := E)
      rw [← liftNormHom_apply, map_prod, ← liftNormHom_apply, map_one]
      simp only [liftNormHom_apply, (hχ _).2]
      exact hprod

/-- `α_χ = (-1)^{n+1} q^{-1} χ_0(a_0⁻¹) ⋯ χ_n(a_n⁻¹) g(χ_0) ⋯ g(χ_n)`. -/
noncomputable def diagAlpha {n : ℕ} (a : Fin (n + 1) → F) (ψ : AddChar F ℂ)
    (χ : Fin (n + 1) → MulChar F ℂ) : ℂ :=
  (-1) ^ (n + 1) * (1 / (Fintype.card F : ℂ)) * (∏ i, χ i (a i)⁻¹) * ∏ i, gaussSum (χ i) ψ

/-- **Equation (6) of §11.3.** Over a field `E ⊇ F` of degree `s`, the diagonal hypersurface has
`N_s = ∑_{k<n} q^{ks} + (-1)^{n+1} ∑_χ α_χ^s` points in `P^n(E)`. -/
@[kb "irelandrosen1990" "§11.3 (6), p. 173"]
theorem numProjDiag_extension (E : Type*) [Field E] [Fintype E] [Algebra F E] {n : ℕ}
    {a : Fin (n + 1) → F} (ha : ∀ i, a i ≠ 0) {m : ℕ} (hm : m ∣ Fintype.card F - 1)
    {ψ : AddChar F ℂ} (hψ : ψ ≠ 1) :
    (numProjDiag (fun i => algebraMap F E (a i)) m : ℂ) =
      ∑ k ∈ range n, ((Fintype.card F : ℂ) ^ k) ^ Module.finrank F E +
        (-1) ^ (n + 1) * ∑ χ ∈ diagTuples F n m, diagAlpha a ψ χ ^ Module.finrank F E := by
  set s := Module.finrank F E
  have ha' : ∀ i, algebraMap F E (a i) ≠ 0 := fun i => by simpa using ha i
  have hψ' : (liftTrace (E := E) ψ).IsPrimitive :=
    AddChar.IsPrimitive.of_ne_one (liftTrace_ne_one hψ)
  rw [numProjDiag_eq_gaussSum ha' (dvd_card_extension_sub_one hm) hψ']
  have hT : ({χ ∈ charTuples (F := E) (fun _ : Fin (n + 1) => m) |
      (∀ i, χ i ≠ 1) ∧ ∏ i, χ i = 1} : Finset _) = diagTuples E n m := rfl
  rw [hT, ← image_lift_diagTuples E hm, Finset.sum_image]
  · rw [card_extension (F := F)]
    push_cast
    congr 1
    · refine Finset.sum_congr rfl fun k _ => ?_
      rw [← pow_mul, ← pow_mul, mul_comm]
    · rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun χ _ => ?_
      have hHD : ∀ i, gaussSum (liftNorm (E := E) (χ i)) (liftTrace ψ) =
          -(-gaussSum (χ i) ψ) ^ s := by
        intro i; rw [hasse_davenport (E := E) (χ i) hψ, neg_neg]
      simp only [hHD, ← map_inv₀, liftNorm_algebraMap]
      rw [diagAlpha, Finset.prod_neg, Finset.prod_pow, Finset.prod_pow, Finset.card_univ,
        Fintype.card_fin, Finset.prod_neg, Finset.card_univ, Fintype.card_fin]
      have hq : (Fintype.card F : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
      simp only [mul_pow, one_div, inv_pow]
      ring
  · intro χ _ χ' _ h
    funext i
    exact liftNorm_injective (congrFun h i)

/-- The zeta function of `a_0 x_0^m + ⋯ + a_n x_n^m = 0` over `F`, computed with the family of
extensions `E s` (`[E s : F] = s`). -/
noncomputable def zetaDiag (E : ℕ → Type*) [∀ s, Field (E s)] [∀ s, Fintype (E s)]
    [∀ s, Algebra F (E s)] {n : ℕ} (a : Fin (n + 1) → F) (m : ℕ) : ℂ⟦X⟧ :=
  zetaOfCounts fun s => (numProjDiag (fun i => algebraMap F (E s) (a i)) m : ℂ)

/-- **Theorem 2 of §11.3 (Weil).** Let `a_i ∈ F^*`, `q ≡ 1 (mod m)` and
`f = a_0 x_0^m + ⋯ + a_n x_n^m`. Then `Z_f(u) = P(u)^{(-1)^n} / ((1 - u)(1 - qu) ⋯ (1 - q^{n-1}u))`
with `P(u) = ∏_χ (1 - α_χ u)`, `α_χ = (-1)^{n+1} q^{-1} χ_0(a_0⁻¹) ⋯ χ_n(a_n⁻¹) g(χ_0) ⋯ g(χ_n)`,
the product over `χ_i^m = ε`, `χ_i ≠ ε`, `χ_0 ⋯ χ_n = ε`. Stated without division: for `n` even
`Z_f(u) ∏_{k<n} (1 - q^k u) = P(u)`, for `n` odd `Z_f(u) ∏_{k<n} (1 - q^k u) P(u) = 1`. -/
@[kb "irelandrosen1990" "Thm 2 (§11.3), p. 173"]
theorem zetaDiag_rational (E : ℕ → Type*) [∀ s, Field (E s)] [∀ s, Fintype (E s)]
    [∀ s, Algebra F (E s)] (hE : ∀ s, 1 ≤ s → Module.finrank F (E s) = s) {n : ℕ}
    {a : Fin (n + 1) → F} (ha : ∀ i, a i ≠ 0) {m : ℕ} (hm : m ∣ Fintype.card F - 1)
    {ψ : AddChar F ℂ} (hψ : ψ ≠ 1) :
    (Even n → zetaDiag E a m * ∏ k ∈ range n, (1 - C ((Fintype.card F : ℂ) ^ k) * X) =
        ∏ χ ∈ diagTuples F n m, (1 - C (diagAlpha a ψ χ) * X)) ∧
      (Odd n → zetaDiag E a m * (∏ k ∈ range n, (1 - C ((Fintype.card F : ℂ) ^ k) * X)) *
        ∏ χ ∈ diagTuples F n m, (1 - C (diagAlpha a ψ χ) * X) = 1) := by
  have hN : ∀ s, 1 ≤ s → (numProjDiag (fun i => algebraMap F (E s) (a i)) m : ℂ) =
      ∑ k ∈ range n, ((Fintype.card F : ℂ) ^ k) ^ s +
        (-1) ^ (n + 1) * ∑ χ ∈ diagTuples F n m, diagAlpha a ψ χ ^ s := by
    intro s hs
    rw [numProjDiag_extension (E s) ha hm hψ, hE s hs]
  constructor
  · intro hn
    have := (zetaOfCounts_mul_eq_iff
      (fun s => (numProjDiag (fun i => algebraMap F (E s) (a i)) m : ℂ))
      ((diagTuples F n m).val.map (diagAlpha a ψ))
      ((range n).val.map fun k => (Fintype.card F : ℂ) ^ k)).mpr (by
        intro s hs
        rw [hN s hs, pow_succ, hn.neg_one_pow]
        simp only [Multiset.map_map, Function.comp_def]
        rw [← Finset.sum_eq_multiset_sum, ← Finset.sum_eq_multiset_sum]
        ring)
    simp only [Multiset.map_map, Function.comp_def] at this
    rw [← Finset.prod_eq_multiset_prod, ← Finset.prod_eq_multiset_prod] at this
    exact this
  · intro hn
    have := (zetaOfCounts_mul_eq_iff
      (fun s => (numProjDiag (fun i => algebraMap F (E s) (a i)) m : ℂ)) 0
      ((range n).val.map (fun k => (Fintype.card F : ℂ) ^ k) +
        (diagTuples F n m).val.map (diagAlpha a ψ))).mpr (by
        intro s hs
        rw [hN s hs, pow_succ, hn.neg_one_pow]
        simp only [Multiset.map_add, Multiset.sum_add, Multiset.map_map, Function.comp_def,
          Multiset.map_zero, Multiset.sum_zero, sub_zero]
        rw [← Finset.sum_eq_multiset_sum, ← Finset.sum_eq_multiset_sum]
        ring)
    simp only [Multiset.map_add, Multiset.prod_add, Multiset.map_map, Function.comp_def,
      Multiset.map_zero, Multiset.prod_zero] at this
    rw [← Finset.prod_eq_multiset_prod, ← Finset.prod_eq_multiset_prod, ← mul_assoc] at this
    exact this

end Diagonal

end NTKB.IrelandRosen
