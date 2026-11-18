/-
Ireland–Rosen, Chapter 11, §1 (final example): for `p ≡ 1 (mod 3)` the zeta function of the cubic
curve `y_0^3 + y_1^3 + y_2^3 = 0` over `𝔽_p` is `(1 + Au + pu²) / ((1 - u)(1 - pu))`, where
`4p = A² + 27B²`, `A ≡ 1 (mod 3)` (Gauss's Theorem 2 of Chapter 8).
-/
import NTKB.IrelandRosen.R2.ZetaExamples
import NTKB.IrelandRosen.R2.Cubic

open Finset PowerSeries
open scoped Classical

set_option linter.unusedSectionVars false

namespace NTKB.IrelandRosen

variable {F : Type*} [Field F] [Fintype F]

lemma cubic_cases (h3 : 3 ∣ Fintype.card F - 1) {χ : MulChar F ℂ} (hχ : orderOf χ = 3)
    {ψ : MulChar F ℂ} (hψ3 : ψ ^ 3 = 1) (hψ1 : ψ ≠ 1) : ψ = χ ∨ ψ = χ ^ 2 := by
  have h := (filter_pow_eq_one_eq_image h3 hχ).1
  have : ψ ∈ ({φ : MulChar F ℂ | φ ^ 3 = 1} : Finset _) := by simpa using hψ3
  rw [h] at this
  simp only [mem_image, mem_range] at this
  obtain ⟨i, hi, rfl⟩ := this
  interval_cases i
  · exact absurd (pow_zero χ) hψ1
  · left; exact pow_one χ
  · right; rfl

lemma pow_eq_one_iff_three_dvd {χ : MulChar F ℂ} (hχ : orderOf χ = 3) (k : ℕ) :
    χ ^ k = 1 ↔ 3 ∣ k := by rw [← hχ, orderOf_dvd_iff_pow_eq_one]

/-- The tuples of nontrivial cubic characters with trivial product are `(χ, χ, χ)` and
`(χ², χ², χ²)`. -/
lemma diagTuples_cubic (h3 : 3 ∣ Fintype.card F - 1) {χ : MulChar F ℂ} (hχ : orderOf χ = 3) :
    diagTuples F 2 3 = {![χ, χ, χ], ![χ ^ 2, χ ^ 2, χ ^ 2]} := by
  have hp := pow_eq_one_iff_three_dvd hχ
  ext ψ
  simp only [diagTuples, mem_filter, charTuples, Fintype.mem_piFinset, mem_univ, true_and,
    mem_insert, mem_singleton]
  constructor
  · rintro ⟨hpow, hne, hprod⟩
    rw [Fin.prod_univ_three] at hprod
    have c : ∀ i, ∃ e, (e = 1 ∨ e = 2) ∧ ψ i = χ ^ e := by
      intro i
      rcases cubic_cases h3 hχ (hpow i) (hne i) with h | h
      · exact ⟨1, Or.inl rfl, by rw [h, pow_one]⟩
      · exact ⟨2, Or.inr rfl, h⟩
    obtain ⟨e0, he0, h0⟩ := c 0
    obtain ⟨e1, he1, h1⟩ := c 1
    obtain ⟨e2, he2, h2⟩ := c 2
    rw [h0, h1, h2, ← pow_add, ← pow_add, hp] at hprod
    have hψ : ψ = ![ψ 0, ψ 1, ψ 2] := by ext i; fin_cases i <;> rfl
    rcases he0 with rfl | rfl <;> rcases he1 with rfl | rfl <;> rcases he2 with rfl | rfl <;>
      norm_num at hprod
    · left; rw [hψ, h0, h1, h2, pow_one]
    · right; rw [hψ, h0, h1, h2]
  · have h1 : χ ≠ 1 := cubic_ne_one hχ
    have h2 : χ ^ 2 ≠ 1 := by rw [Ne, hp]; norm_num
    rintro (rfl | rfl)
    · refine ⟨fun i => ?_, fun i => ?_, ?_⟩
      · fin_cases i <;> simp [hp]
      · fin_cases i <;> simpa using h1
      · rw [Fin.prod_univ_three]; simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
        rw [← pow_two, ← pow_succ, hp]
        try norm_num
    · refine ⟨fun i => ?_, fun i => ?_, ?_⟩
      · fin_cases i <;> simp [← pow_mul, hp]
      · fin_cases i <;> simpa using h2
      · rw [Fin.prod_univ_three]; simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
        rw [← pow_add, ← pow_add, hp]
        try norm_num

/-- `g(χ)^3 = q J(χ, χ)` for a cubic character (corollary to Proposition 8.3.3). -/
lemma gaussSum_cube {χ : MulChar F ℂ} (hχ : orderOf χ = 3) {ψ : AddChar F ℂ}
    (hψ : ψ.IsPrimitive) : gaussSum χ ψ ^ 3 = Fintype.card F * multiJacobiSum ![χ, χ] := by
  have h1 := cubic_ne_one hχ
  have hsq := cubic_sq_eq_inv hχ
  have hne : ∀ k : Fin 2, ![χ, χ] k ≠ 1 := by intro k; fin_cases k <;> simpa using h1
  have hprod : ∏ k, ![χ, χ] k ≠ 1 := by
    rw [Fin.prod_univ_two]; simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
    rw [← pow_two, hsq]; exact inv_ne_one.mpr h1
  have h3 := prod_gaussSum_eq_multiJacobiSum_mul hne hprod ψ
  rw [Fin.prod_univ_two, Fin.prod_univ_two] at h3
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at h3
  rw [show χ * χ = χ⁻¹ by rw [← pow_two, hsq]] at h3
  have hinv := gaussSum_mul_gaussSum_inv h1 hψ
  rw [cubic_apply_neg_one hχ, one_mul] at hinv
  calc gaussSum χ ψ ^ 3 = gaussSum χ ψ ^ 2 * gaussSum χ ψ := by ring
    _ = multiJacobiSum ![χ, χ] * (gaussSum χ ψ * gaussSum χ⁻¹ ψ) := by rw [sq, h3]; ring
    _ = _ := by rw [hinv]; ring

/-- **The zeta function of `y_0^3 + y_1^3 + y_2^3 = 0` over `𝔽_p`** (§11.1, last example):
for `p ≡ 1 (mod 3)` prime and `4p = A² + 27B²` with `A ≡ 1 (mod 3)`,
`Z(u) (1 - u)(1 - pu) = 1 + Au + pu²`. -/
@[kb "irelandrosen1990" "§11.1, cubic curve example, p. 164"]
theorem zeta_fermat_cubic {p : ℕ} [Fact p.Prime] (hp : p % 3 = 1)
    (E : ℕ → Type*) [∀ s, Field (E s)] [∀ s, Fintype (E s)] [∀ s, Algebra (ZMod p) (E s)]
    (hE : ∀ s, 1 ≤ s → Module.finrank (ZMod p) (E s) = s) {A B : ℤ}
    (hAB : 4 * (p : ℤ) = A ^ 2 + 27 * B ^ 2) (hA : A ≡ 1 [ZMOD 3]) :
    zetaDiag E ![(1 : ZMod p), 1, 1] 3 * ((1 - X) * (1 - C (p : ℂ) * X)) =
      1 + C (A : ℂ) * X + C (p : ℂ) * X ^ 2 := by
  have h3 : 3 ∣ Fintype.card (ZMod p) - 1 := by rw [ZMod.card]; omega
  obtain ⟨χ, hχ⟩ := exists_orderOf_eq h3
  obtain ⟨ψ, hψ⟩ := exists_isPrimitive_addChar (F := ZMod p)
  have hψ1 : ψ ≠ 1 := fun h => by apply hψ one_ne_zero; ext x; simp [h]
  have ha : ∀ i, (![(1 : ZMod p), 1, 1] : Fin 3 → ZMod p) i ≠ 0 := by
    intro i; fin_cases i <;> simp
  have hZ := (zetaDiag_rational E hE ha h3 hψ1).1 (by decide)
  rw [diagTuples_cubic h3 hχ] at hZ
  -- the two reciprocal roots
  set J := multiJacobiSum ![χ, χ]
  have hq0 : (Fintype.card (ZMod p) : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hα1 : diagAlpha ![(1 : ZMod p), 1, 1] ψ ![χ, χ, χ] = -J := by
    rw [diagAlpha, Fin.prod_univ_three, Fin.prod_univ_three]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, inv_one, map_one, one_mul]
    rw [show gaussSum χ ψ * gaussSum χ ψ * gaussSum χ ψ = gaussSum χ ψ ^ 3 by ring,
      gaussSum_cube hχ hψ]
    field_simp
    ring
  have hχ2 : orderOf (χ ^ 2) = 3 := by
    rw [orderOf_pow' χ (by norm_num), hχ]; norm_num
  have hα2 : diagAlpha ![(1 : ZMod p), 1, 1] ψ ![χ ^ 2, χ ^ 2, χ ^ 2] =
      -starRingEnd ℂ J := by
    rw [diagAlpha, Fin.prod_univ_three, Fin.prod_univ_three]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, inv_one, map_one, one_mul]
    rw [show gaussSum (χ ^ 2) ψ * gaussSum (χ ^ 2) ψ * gaussSum (χ ^ 2) ψ =
      gaussSum (χ ^ 2) ψ ^ 3 by ring, gaussSum_cube hχ2 hψ, cubic_sq_eq_inv hχ,
      multiJacobiSum_pair_inv_inv]
    field_simp
    ring
  have hne : (![χ, χ, χ] : Fin 3 → MulChar (ZMod p) ℂ) ≠ ![χ ^ 2, χ ^ 2, χ ^ 2] := by
    intro h
    have := congrFun h 0
    simp only [Matrix.cons_val_zero] at this
    have h1 : χ ^ 1 = χ ^ 2 := by rw [pow_one]; exact this
    have := pow_injOn_Iio_orderOf (x := χ) (by rw [hχ]; norm_num : 1 ∈ Set.Iio (orderOf χ))
      (by rw [hχ]; norm_num : 2 ∈ Set.Iio (orderOf χ)) h1
    norm_num at this
  rw [Finset.prod_pair hne, hα1, hα2] at hZ
  simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul, pow_zero, pow_one,
    map_one] at hZ
  rw [ZMod.card] at hZ
  -- `J + J̄ = A` and `J J̄ = p`
  obtain ⟨A0, B0, hre, hAB0, hA0⟩ := cubic_four_mul_card_eq h3 hχ
  rw [ZMod.card] at hAB0
  have hAA : A = A0 := eq_of_four_mul_prime Fact.out hAB0 hAB hA0 hA |>.symm
  subst hAA
  have hsum : J + starRingEnd ℂ J = A := by
    rw [Complex.add_conj]; exact_mod_cast hre
  have hprodJ : J * starRingEnd ℂ J = p := by
    have h1 := cubic_ne_one hχ
    have hne2 : ∀ k : Fin 2, ![χ, χ] k ≠ 1 := by intro k; fin_cases k <;> simpa using h1
    have hprod2 : ∏ k, ![χ, χ] k ≠ 1 := by
      rw [Fin.prod_univ_two]; simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one]
      rw [← pow_two, cubic_sq_eq_inv hχ]; exact inv_ne_one.mpr h1
    have hn := norm_multiJacobiSum (r := 1) hne2 hprod2
    rw [pow_one, ZMod.card] at hn
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hn, Real.sq_sqrt (by positivity)]
    simp
  have e : (zetaDiag E ![(1 : ZMod p), 1, 1] 3 * ((1 - X) * (1 - C (p : ℂ) * X))) =
      (1 - C (-J) * X) * (1 - C (-starRingEnd ℂ J) * X) := by
    rw [← hZ]
  rw [e]
  have hA' : (C (A : ℂ) : ℂ⟦X⟧) = C J + C (starRingEnd ℂ J) := by rw [← map_add, hsum]
  have hp' : (C (p : ℂ) : ℂ⟦X⟧) = C J * C (starRingEnd ℂ J) := by rw [← map_mul, hprodJ]
  rw [hA', hp', map_neg, map_neg]
  ring

end NTKB.IrelandRosen
