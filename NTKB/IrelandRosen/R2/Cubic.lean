/-
Ireland–Rosen, Chapter 8, §3: the cubic Jacobi sum and Gauss's theorem `4p = A² + 27B²`,
`N(x³ + y³ = 1) = p - 2 + A` (Propositions 8.3.1 (second part), 8.3.2, 8.3.4 and its corollary,
Theorem 2, Exercise 8.13).

The congruences of Proposition 8.3.4 are obtained from Mathlib's
`exists_jacobiSum_eq_neg_one_add` (`J(χ, χ) = -1 + z (ω - 1)²` with `z ∈ ℤ[ω]`), which packages
the book's computation modulo `3` in the ring of algebraic integers.
-/
import NTKB.IrelandRosen.R2.FermatCurve
import Mathlib.RingTheory.RootsOfUnity.Complex

open Finset Complex
open scoped Classical

set_option linter.unusedSectionVars false

namespace NTKB.IrelandRosen

/-- `ω = e^{2πi/3}`. -/
noncomputable def omega3 : ℂ := Complex.exp (2 * Real.pi * Complex.I / (3 : ℕ))

lemma omega3_isPrimitiveRoot : IsPrimitiveRoot omega3 3 :=
  Complex.isPrimitiveRoot_exp 3 (by norm_num)

lemma omega3_sq : omega3 ^ 2 = -1 - omega3 := by
  have h := omega3_isPrimitiveRoot.geom_sum_eq_zero (by norm_num : 1 < 3)
  simp [Finset.sum_range_succ] at h
  linear_combination h

lemma omega3_re_im : omega3.re = -1 / 2 ∧ omega3.im ^ 2 = 3 / 4 := by
  have hn : ‖omega3‖ = 1 := omega3_isPrimitiveRoot.norm'_eq_one (by norm_num)
  have h1 : omega3.re ^ 2 + omega3.im ^ 2 = 1 := by
    have := Complex.normSq_eq_norm_sq omega3
    rw [Complex.normSq_apply, hn] at this; nlinarith
  have h2 := congrArg Complex.re omega3_sq
  have h3 := congrArg Complex.im omega3_sq
  simp [pow_two] at h2 h3
  have him : omega3.im ≠ 0 := by
    intro h; rw [h] at h1 h2; nlinarith
  have hre : 2 * omega3.re + 1 = 0 := by
    have : omega3.im * (2 * omega3.re + 1) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h him
    · exact h
  constructor
  · linarith
  · nlinarith

lemma omega3_im_ne_zero : omega3.im ≠ 0 := by
  intro h; have := omega3_re_im.2; rw [h] at this; norm_num at this

/-- The elements of `ℤ[ω]` are the `a + bω` with `a, b ∈ ℤ`. -/
lemma exists_eq_add_mul_omega3 {z : ℂ} (hz : z ∈ Algebra.adjoin ℤ ({omega3} : Set ℂ)) :
    ∃ a b : ℤ, z = a + b * omega3 := by
  induction hz using Algebra.adjoin_induction with
  | mem x hx => rw [Set.mem_singleton_iff.mp hx]; exact ⟨0, 1, by simp⟩
  | algebraMap r => exact ⟨r, 0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, b, rfl⟩ := hx; obtain ⟨c, d, rfl⟩ := hy
    exact ⟨a + c, b + d, by push_cast; ring⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a, b, rfl⟩ := hx; obtain ⟨c, d, rfl⟩ := hy
    exact ⟨a * c - b * d, a * d + b * c - b * d, by
      push_cast; linear_combination (b * d : ℂ) * omega3_sq⟩

lemma add_mul_omega3_inj {a b c d : ℤ} (h : (a : ℂ) + b * omega3 = c + d * omega3) :
    a = c ∧ b = d := by
  have him := congrArg Complex.im h
  simp at him
  rcases him with hbd | h0
  · have hbd' : b = d := by exact_mod_cast hbd
    subst hbd'
    have hre := congrArg Complex.re h
    simp at hre
    exact ⟨by exact_mod_cast hre, rfl⟩
  · exact absurd h0 omega3_im_ne_zero

lemma normSq_add_mul_omega3 (a b : ℤ) :
    Complex.normSq ((a : ℂ) + b * omega3) = a ^ 2 - a * b + b ^ 2 := by
  obtain ⟨hre, him⟩ := omega3_re_im
  rw [Complex.normSq_apply]
  simp [hre]
  nlinarith [him]

lemma re_add_mul_omega3 (a b : ℤ) : 2 * ((a : ℂ) + b * omega3).re = 2 * a - b := by
  simp [omega3_re_im.1]; ring

variable {F : Type*} [Field F] [Fintype F]

/-! ### Jacobi sums of two characters in the book's convention (Theorem 1 of Chapter 8) -/

lemma multiJacobiSum_pair_one_one :
    multiJacobiSum ![(1 : MulChar F ℂ), 1] = Fintype.card F := by
  have h1 : (![1, 1] : Fin 2 → MulChar F ℂ) = fun _ => 1 := by funext k; fin_cases k <;> rfl
  rw [h1]
  have := multiJacobiSumAt_one (R := ℂ) (F := F) (r := 1) 1
  rw [pow_one] at this; exact this

lemma multiJacobiSum_pair_one_left {ψ : MulChar F ℂ} (hψ : ψ ≠ 1) :
    multiJacobiSum ![1, ψ] = 0 :=
  multiJacobiSumAt_eq_zero (j := 0) (k := 1) 1 rfl (by simpa using hψ)

lemma multiJacobiSum_pair_one_right {ψ : MulChar F ℂ} (hψ : ψ ≠ 1) :
    multiJacobiSum ![ψ, 1] = 0 :=
  multiJacobiSumAt_eq_zero (j := 1) (k := 0) 1 rfl (by simpa using hψ)

lemma multiJacobiSum_pair_inv {ψ : MulChar F ℂ} (hψ : ψ ≠ 1) :
    multiJacobiSum ![ψ, ψ⁻¹] = -ψ (-1) := by
  obtain ⟨φ, hφ⟩ := exists_isPrimitive_addChar (F := F)
  have hne : ∀ k : Fin 2, ![ψ, ψ⁻¹] k ≠ 1 := by
    intro k; fin_cases k
    · simpa using hψ
    · simpa using hψ
  have hprod : ∏ k, ![ψ, ψ⁻¹] k = 1 := by simp [Fin.prod_univ_two]
  rw [multiJacobiSum_eq_of_prod_eq_one (r := 0) hne hprod hφ, multiJacobiSum_single]
  simp [mulChar_inv_neg_one]

lemma bookChar_inv (ψ : MulChar F ℂ) (t : F) :
    bookChar ψ⁻¹ t = starRingEnd ℂ (bookChar ψ t) := by
  by_cases hψ : ψ = 1
  · subst hψ; simp [bookChar_one]
  · rw [bookChar_of_ne_one hψ, bookChar_of_ne_one (inv_ne_one.mpr hψ), starRingEnd_apply,
      MulChar.star_apply']

lemma multiJacobiSum_pair_inv_inv (ψ : MulChar F ℂ) :
    multiJacobiSum ![ψ⁻¹, ψ⁻¹] = starRingEnd ℂ (multiJacobiSum ![ψ, ψ]) := by
  rw [multiJacobiSum_pair, multiJacobiSum_pair, map_sum]
  simp [bookChar_inv]

/-! ### The cubic case -/

variable {χ : MulChar F ℂ}

lemma cubic_ne_one (hχ : orderOf χ = 3) : χ ≠ 1 := by
  rintro rfl; simp at hχ

lemma cubic_sq_eq_inv (hχ : orderOf χ = 3) : χ ^ 2 = χ⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← pow_succ]
  have := pow_orderOf_eq_one χ
  rw [hχ] at this
  simpa using this

lemma cubic_apply_neg_one (hχ : orderOf χ = 3) : χ (-1) = 1 := by
  have h3 : χ (-1) ^ 3 = 1 := by
    rw [← MulChar.pow_apply' χ (by norm_num), ← hχ, pow_orderOf_eq_one, MulChar.one_apply]
    exact isUnit_neg_one
  have h2 := mulChar_neg_one_sq χ
  calc χ (-1) = χ (-1) * (χ (-1) * χ (-1)) := by rw [h2, mul_one]
    _ = χ (-1) ^ 3 := by ring
    _ = 1 := h3

/-- **`N(x³ + y³ = 1) = q - 2 + 2 Re J(χ, χ)`** for a cubic character `χ` (§3 of Chapter 8,
there over `𝔽_p` with `p ≡ 1 (mod 3)`). -/
@[kb "irelandrosen1990" "§8.3, N(x^3+y^3=1), p. 105"]
theorem numSolDiag_cubic (h3 : 3 ∣ Fintype.card F - 1) (hχ : orderOf χ = 3) :
    (numSolDiag ![(1 : F), 1] ![3, 3] 1 : ℂ) =
      Fintype.card F - 2 + 2 * (multiJacobiSum ![χ, χ]).re := by
  rw [numSolDiag_fermat_eq_sum h3 hχ]
  have h1 := cubic_ne_one hχ
  have h2 : χ ^ 2 ≠ 1 := by rw [cubic_sq_eq_inv hχ]; exact inv_ne_one.mpr h1
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add, pow_zero,
    pow_one]
  rw [multiJacobiSum_pair_one_one, multiJacobiSum_pair_one_left h1,
    multiJacobiSum_pair_one_left h2, multiJacobiSum_pair_one_right h1,
    multiJacobiSum_pair_one_right h2, cubic_sq_eq_inv hχ, multiJacobiSum_pair_inv h1,
    multiJacobiSum_pair_inv_inv]
  have : multiJacobiSum ![χ⁻¹, χ] = -χ⁻¹ (-1) := by
    have := multiJacobiSum_pair_inv (inv_ne_one.mpr h1)
    rwa [inv_inv] at this
  rw [this, mulChar_inv_neg_one, cubic_apply_neg_one hχ]
  have hc := Complex.add_conj (multiJacobiSum ![χ, χ])
  push_cast at hc
  linear_combination hc

/-- **The estimate of §8.3**: `|N(x³ + y³ = 1) - q + 2| ≤ 2 √q` when `q ≡ 1 (mod 3)`. (The book
writes `<`, which holds since `2√q` is irrational for `q = p`.) -/
@[kb "irelandrosen1990" "§8.3, N(x^3+y^3=1), p. 105"]
theorem abs_numSolDiag_cubic_sub_le (h3 : 3 ∣ Fintype.card F - 1) :
    |(numSolDiag ![(1 : F), 1] ![3, 3] 1 : ℝ) - Fintype.card F + 2| ≤
      2 * √(Fintype.card F) := by
  obtain ⟨χ, hχ⟩ := exists_orderOf_eq h3
  have h := numSolDiag_cubic h3 hχ
  have h1 := cubic_ne_one hχ
  have hne : ∀ k : Fin 2, ![χ, χ] k ≠ 1 := by intro k; fin_cases k <;> simpa using h1
  have hprod : ∏ k, ![χ, χ] k ≠ 1 := by
    rw [Fin.prod_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    rw [← pow_two, cubic_sq_eq_inv hχ]; exact inv_ne_one.mpr h1
  have hn := norm_multiJacobiSum (r := 1) hne hprod
  rw [pow_one] at hn
  have hre : (numSolDiag ![(1 : F), 1] ![3, 3] 1 : ℝ) - Fintype.card F + 2 =
      2 * (multiJacobiSum ![χ, χ]).re := by
    have := congrArg Complex.re h
    simp at this
    linarith
  rw [hre, abs_mul, abs_two, ← hn]
  gcongr
  exact Complex.abs_re_le_norm _

/-- **Propositions 8.3.1 (second part) and 8.3.4.** For a cubic character `χ` of `F`,
`J(χ, χ) = a + bω` with `a, b ∈ ℤ`, `q = a² - ab + b²`, `b ≡ 0` and `a ≡ -1 (mod 3)`. -/
@[kb "irelandrosen1990" "Prop 8.3.4, p. 107"]
theorem cubic_jacobiSum_eq (h3 : 3 ∣ Fintype.card F - 1) (hχ : orderOf χ = 3) :
    ∃ a b : ℤ, multiJacobiSum ![χ, χ] = a + b * omega3 ∧
      (Fintype.card F : ℤ) = a ^ 2 - a * b + b ^ 2 ∧ 3 ∣ b ∧ a ≡ -1 [ZMOD 3] := by
  have h1 := cubic_ne_one hχ
  have hχ3 : χ ^ 3 = 1 := by rw [← hχ]; exact pow_orderOf_eq_one χ
  obtain ⟨z, hz, hJ⟩ := exists_jacobiSum_eq_neg_one_add (by norm_num : 2 < 3) hχ3 hχ3 h3
    omega3_isPrimitiveRoot
  obtain ⟨c, d, rfl⟩ := exists_eq_add_mul_omega3 hz
  refine ⟨-1 + 3 * d, 3 * d - 3 * c, ?_, ?_, ⟨d - c, by ring⟩, ?_⟩
  · rw [multiJacobiSum_two h1 h1, hJ]
    push_cast
    linear_combination (c + d * (omega3 - 3)) * omega3_sq
  · have hprod : ∏ k, ![χ, χ] k ≠ 1 := by
      rw [Fin.prod_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      rw [← pow_two, cubic_sq_eq_inv hχ]; exact inv_ne_one.mpr h1
    have hne : ∀ k : Fin 2, ![χ, χ] k ≠ 1 := by intro k; fin_cases k <;> simpa using h1
    have hn := norm_multiJacobiSum (r := 1) hne hprod
    rw [pow_one] at hn
    have hJ' : multiJacobiSum ![χ, χ] = ((-1 + 3 * d : ℤ) : ℂ) + ((3 * d - 3 * c : ℤ) : ℂ) * omega3 := by
      rw [multiJacobiSum_two h1 h1, hJ]; push_cast
      linear_combination (c + d * (omega3 - 3)) * omega3_sq
    have := congrArg (· ^ 2) hn
    rw [← Complex.normSq_eq_norm_sq, hJ', normSq_add_mul_omega3,
      Real.sq_sqrt (by positivity)] at this
    exact_mod_cast this.symm
  · exact Int.ModEq.symm (Int.modEq_iff_dvd.mpr ⟨d, by ring⟩)

/-- **Corollary to Proposition 8.3.4.** With `A = 2a - b` and `B = b/3`: `A ≡ 1 (mod 3)` and
`4q = A² + 27B²`. -/
@[kb "irelandrosen1990" "Prop 8.3.4, Cor, p. 108"]
theorem cubic_four_mul_card_eq (h3 : 3 ∣ Fintype.card F - 1) (hχ : orderOf χ = 3) :
    ∃ A B : ℤ, 2 * (multiJacobiSum ![χ, χ]).re = A ∧
      4 * (Fintype.card F : ℤ) = A ^ 2 + 27 * B ^ 2 ∧ A ≡ 1 [ZMOD 3] := by
  obtain ⟨a, b, hJ, hq, ⟨k, rfl⟩, ha⟩ := cubic_jacobiSum_eq h3 hχ
  refine ⟨2 * a - 3 * k, k, ?_, ?_, ?_⟩
  · rw [hJ, re_add_mul_omega3]; push_cast; ring
  · rw [hq]; ring
  · unfold Int.ModEq at ha ⊢
    omega

/-! ### Gauss's theorem -/

/-- **Uniqueness up to sign** (Proposition 8.3.2): if `p` is a prime and
`4p = A² + 27B² = C² + 27D²`, then `A² = C²` and `B² = D²`. -/
theorem sq_eq_sq_of_four_mul_prime {p : ℕ} (hp : p.Prime) {A B C D : ℤ}
    (h1 : 4 * (p : ℤ) = A ^ 2 + 27 * B ^ 2) (h2 : 4 * (p : ℤ) = C ^ 2 + 27 * D ^ 2) :
    A ^ 2 = C ^ 2 ∧ B ^ 2 = D ^ 2 := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hp0 : (0 : ℤ) < p := by exact_mod_cast hp.pos
  -- the key step, for a fixed choice of sign of `D`
  have key : ∀ D' : ℤ, 4 * (p : ℤ) = C ^ 2 + 27 * D' ^ 2 → (p : ℤ) ∣ A * D' - B * C →
      A ^ 2 = C ^ 2 ∧ B ^ 2 = D' ^ 2 := by
    intro D' h2' hdvd
    have hid : 16 * (p : ℤ) ^ 2 = (A * C + 27 * B * D') ^ 2 + 27 * (A * D' - B * C) ^ 2 := by
      have : 16 * (p : ℤ) ^ 2 = (4 * p) * (4 * p) := by ring
      rw [this]; nth_rewrite 1 [h1]; rw [h2']; ring
    have hY : A * D' - B * C = 0 := by
      obtain ⟨k, hk⟩ := hdvd
      by_contra hne
      have hk0 : k ≠ 0 := by rintro rfl; simp at hk; exact hne hk
      have : 1 ≤ k ^ 2 := by
        have := sq_pos_of_ne_zero hk0; omega
      rw [hk] at hid
      nlinarith [sq_nonneg (A * C + 27 * B * D')]
    have hBD : B ^ 2 = D' ^ 2 := by
      have e1 : (4 * (p : ℤ)) * D' ^ 2 = (4 * p) * B ^ 2 := by
        nth_rewrite 1 [h1]; rw [h2']
        have : A * D' = B * C := by linarith
        linear_combination (A * D' + B * C) * this
      have := mul_left_cancel₀ (by positivity : (4 * (p : ℤ)) ≠ 0) e1
      exact this.symm
    refine ⟨?_, hBD⟩
    have : 4 * (p : ℤ) - 27 * B ^ 2 = 4 * p - 27 * D' ^ 2 := by rw [hBD]
    linarith
  -- `p ∣ (AD - BC)(AD + BC) = 4p(D² - B²)`
  have hprod : (p : ℤ) ∣ (A * D - B * C) * (A * (-D) - B * C) := by
    refine ⟨-(4 * (D ^ 2 - B ^ 2)), ?_⟩
    have : (A * D - B * C) * (A * (-D) - B * C) = -(A ^ 2 * D ^ 2 - B ^ 2 * C ^ 2) := by ring
    rw [this]
    have : A ^ 2 * D ^ 2 - B ^ 2 * C ^ 2 = (A ^ 2 + 27 * B ^ 2) * D ^ 2 -
        B ^ 2 * (C ^ 2 + 27 * D ^ 2) := by ring
    rw [this, ← h1, ← h2]; ring
  rcases hpZ.dvd_or_dvd hprod with h | h
  · exact key D h2 h
  · have := key (-D) (by rw [h2]; ring) h
    exact ⟨this.1, by rw [this.2]; ring⟩

/-- **Exercise 8.13.** If `p` is a prime, `4p = A² + 27B² = C² + 27D²` and
`A ≡ C ≡ 1 (mod 3)`, then `A = C`. -/
@[kb "irelandrosen1990" "Exercise 8.13, p. 117"]
theorem eq_of_four_mul_prime {p : ℕ} (hp : p.Prime) {A B C D : ℤ}
    (h1 : 4 * (p : ℤ) = A ^ 2 + 27 * B ^ 2) (h2 : 4 * (p : ℤ) = C ^ 2 + 27 * D ^ 2)
    (hA : A ≡ 1 [ZMOD 3]) (hC : C ≡ 1 [ZMOD 3]) : A = C := by
  have := (sq_eq_sq_of_four_mul_prime hp h1 h2).1
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp this with h | h
  · exact h
  · exfalso
    subst h
    unfold Int.ModEq at hA hC
    omega

lemma prime_ne_two_of_mod_three {p : ℕ} (hp : p % 3 = 1) : p ≠ 2 := by
  rintro rfl; norm_num at hp

/-- **Proposition 8.3.1, second part.** If `p ≡ 1 (mod 3)` is prime, then `p = a² - ab + b²`
for some integers `a, b`. -/
@[kb "irelandrosen1990" "Prop 8.3.1, p. 106"]
theorem exists_eq_sq_sub_mul_add_sq {p : ℕ} [Fact p.Prime] (hp : p % 3 = 1) :
    ∃ a b : ℤ, (p : ℤ) = a ^ 2 - a * b + b ^ 2 := by
  have h3 : 3 ∣ Fintype.card (ZMod p) - 1 := by rw [ZMod.card]; omega
  obtain ⟨χ, hχ⟩ := exists_orderOf_eq h3
  obtain ⟨a, b, -, hq, -⟩ := cubic_jacobiSum_eq h3 hχ
  rw [ZMod.card] at hq
  exact ⟨a, b, hq⟩

/-- **Proposition 8.3.2.** If `p ≡ 1 (mod 3)` is prime, then `4p = A² + 27B²` for some integers
`A, B`, and `A`, `B` are unique up to sign. -/
@[kb "irelandrosen1990" "Prop 8.3.2, p. 107"]
theorem exists_four_mul_eq {p : ℕ} [Fact p.Prime] (hp : p % 3 = 1) :
    ∃ A B : ℤ, 4 * (p : ℤ) = A ^ 2 + 27 * B ^ 2 ∧
      ∀ C D : ℤ, 4 * (p : ℤ) = C ^ 2 + 27 * D ^ 2 → (C = A ∨ C = -A) ∧ (D = B ∨ D = -B) := by
  have h3 : 3 ∣ Fintype.card (ZMod p) - 1 := by rw [ZMod.card]; omega
  obtain ⟨χ, hχ⟩ := exists_orderOf_eq h3
  obtain ⟨A, B, -, h, -⟩ := cubic_four_mul_card_eq h3 hχ
  rw [ZMod.card] at h
  refine ⟨A, B, h, fun C D h' => ?_⟩
  obtain ⟨hAC, hBD⟩ := sq_eq_sq_of_four_mul_prime Fact.out h h'
  exact ⟨sq_eq_sq_iff_eq_or_eq_neg.mp hAC.symm, sq_eq_sq_iff_eq_or_eq_neg.mp hBD.symm⟩

/-- **Theorem 2 of Chapter 8 (Gauss).** If `p ≡ 1 (mod 3)` is prime, there are integers `A, B`
with `4p = A² + 27B²`; requiring `A ≡ 1 (mod 3)` determines `A` uniquely, and then
`N(x³ + y³ = 1) = p - 2 + A` in `𝔽_p`. -/
@[kb "irelandrosen1990" "Thm 2, p. 108"]
theorem gauss_cubic {p : ℕ} [Fact p.Prime] (hp : p % 3 = 1) :
    ∃ A B : ℤ, 4 * (p : ℤ) = A ^ 2 + 27 * B ^ 2 ∧ A ≡ 1 [ZMOD 3] ∧
      (∀ C D : ℤ, 4 * (p : ℤ) = C ^ 2 + 27 * D ^ 2 → C ≡ 1 [ZMOD 3] → C = A) ∧
      (numSolDiag ![(1 : ZMod p), 1] ![3, 3] 1 : ℤ) = p - 2 + A := by
  have h3 : 3 ∣ Fintype.card (ZMod p) - 1 := by rw [ZMod.card]; omega
  obtain ⟨χ, hχ⟩ := exists_orderOf_eq h3
  obtain ⟨A, B, hre, h, hA⟩ := cubic_four_mul_card_eq h3 hχ
  rw [ZMod.card] at h
  refine ⟨A, B, h, hA, fun C D h' hC =>
    (eq_of_four_mul_prime Fact.out h h' hA hC).symm, ?_⟩
  have hN := numSolDiag_cubic h3 hχ
  have hre' : (2 : ℂ) * ((multiJacobiSum ![χ, χ]).re : ℂ) = A := by
    exact_mod_cast congrArg (fun x : ℝ => (x : ℂ)) hre
  rw [hre', ZMod.card] at hN
  have : ((numSolDiag ![(1 : ZMod p), 1] ![3, 3] 1 : ℤ) : ℂ) = ((p - 2 + A : ℤ) : ℂ) := by
    push_cast; rw [hN]
  exact_mod_cast this

end NTKB.IrelandRosen
