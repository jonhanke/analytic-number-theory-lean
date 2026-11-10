/- Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license. -/
import NTKB.Analytic.Davenport.Sieve.BombieriPieces

/-!
# Estimate (B) of Bombieri's theorem (Davenport, Chapter 28)

`∑_{q ≤ Q} (q/φ(q)) ∑*_χ max_{y ≤ x} |ψ'(y, χ)| ≪ (x + x^{5/6} Q + x^{1/2} Q²)(log x)⁴`
(Davenport p. 162, (B)), by Vaughan's identity (§24) and the bilinear large sieve (E).

The maximum over `y ≤ x` is an arbitrary choice `y(q, χ) ∈ [0, x]`. We first prove the bound for
general parameters `U, V` (`sum_psiChar'_le_UV`, the combination (7), (12)–(15) of p. 167), then
choose `U = V` as in the book.
-/

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

namespace NTKB.Davenport

lemma ne_one_of_isPrimitive {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) : χ ≠ 1 := by
  rintro rfl
  rw [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_one] at hχ
  omega

/-- The decomposition of `ψ(N, χ)` for a primitive character modulo `q ≥ 2` (Davenport (7)–(10)):
`|ψ(N, χ)| ≤ |S₁| + |S₂'| + |S₂''| + |S₃| + |S₄|` with the bounds of `BombieriPieces.lean`. -/
lemma norm_psi_prim_le {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) {X N : ℕ} (hNX : N ≤ X) (U : ℕ) {V : ℕ} (hV : 1 ≤ V) :
    ‖∑ n ∈ Icc 1 N, χ n * (Λ n : ℂ)‖ ≤
      (Real.log 4 + 4) * U + U * Real.log U * (2 * √q * Real.log q) +
        Real.log N * (V * (4 * √q * Real.log q)) +
        ‖∑ t ∈ Icc 1 X, ∑ r ∈ (Icc 1 X).filter (fun r ↦ t * r ≤ N),
          alphaS₂ U V t * 1 * χ ((t * r : ℕ) : ZMod q)‖ +
        ‖∑ m ∈ Icc 1 X, ∑ k ∈ (Icc 1 X).filter (fun k ↦ m * k ≤ N),
          alphaS₄ X U V m * betaS₄ X V k * χ ((m * k : ℕ) : ZMod q)‖ := by
  have hχ1 := ne_one_of_isPrimitive hq hχ
  have hdec := sum_mul_vonMangoldt_eq (fun n ↦ χ n) N U V
  rw [hdec, S₂_eq, ← sum_filter_add_sum_filter_not (Icc 1 N) (· ≤ U)
    (fun t ↦ (vaughanH U V t : ℂ) * ∑ r ∈ Icc 1 (N / t), χ ((t * r : ℕ) : ZMod q)), S₂''_eq χ hNX,
    S₄_eq_bilinear χ hNX U hV]
  have h1 := norm_S₁_le (fun n ↦ χ n) (fun n ↦ DirichletCharacter.norm_le_one χ _) N U
  have h2 := norm_S₂'_le hχ1 N U V
  have h3 := norm_S₃_char_le hχ1 N V
  set A1 := ∑ n ∈ Icc 1 N, χ n * (truncate Λ U n : ℂ)
  set A2 := ∑ t ∈ (Icc 1 N).filter (· ≤ U), (vaughanH U V t : ℂ) *
        ∑ r ∈ Icc 1 (N / t), χ ((t * r : ℕ) : ZMod q)
  set A3 := ∑ n ∈ Icc 1 N, χ n * ((log * truncate (μ : ArithmeticFunction ℝ) V) n : ℂ)
  set D2 := ∑ t ∈ Icc 1 X, ∑ r ∈ (Icc 1 X).filter (fun r ↦ t * r ≤ N),
          alphaS₂ U V t * 1 * χ ((t * r : ℕ) : ZMod q)
  set D4 := ∑ m ∈ Icc 1 X, ∑ k ∈ (Icc 1 X).filter (fun k ↦ m * k ≤ N),
          alphaS₄ X U V m * betaS₄ X V k * χ ((m * k : ℕ) : ZMod q)
  have : ‖A1 + -(A2 + D2) + A3 + -D4‖ ≤ ‖A1‖ + ‖A2‖ + ‖D2‖ + ‖A3‖ + ‖D4‖ := by
    calc _ ≤ ‖A1 + -(A2 + D2) + A3‖ + ‖-D4‖ := norm_add_le _ _
      _ ≤ ‖A1 + -(A2 + D2)‖ + ‖A3‖ + ‖-D4‖ := by gcongr; exact norm_add_le _ _
      _ ≤ ‖A1‖ + ‖-(A2 + D2)‖ + ‖A3‖ + ‖-D4‖ := by gcongr; exact norm_add_le _ _
      _ ≤ _ := by rw [norm_neg, norm_neg]; linarith [norm_add_le A2 D2]
  refine this.trans ?_
  linarith

open scoped Classical in
/-- `∑_{q ≤ Q} (q/φ(q)) · #{primitive χ mod q} ≤ Q²`. -/
lemma sum_weight_card_primitive_le {Q : ℝ} (hQ : 1 ≤ Q) :
    ∑ q ∈ Icc 1 ⌊Q⌋₊, ((q : ℝ) / q.totient) *
      (((univ : Finset (DirichletCharacter ℂ q)).filter (fun χ ↦ χ.IsPrimitive)).card : ℝ) ≤
      Q ^ 2 := by
  calc _ ≤ ∑ q ∈ Icc 1 ⌊Q⌋₊, ((⌊Q⌋₊ : ℕ) : ℝ) := by
        refine sum_le_sum fun q hq ↦ ?_
        have hq1 := (mem_Icc.1 hq).1
        have : NeZero q := ⟨by omega⟩
        have hφ : (0:ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.2 hq1
        calc ((q : ℝ) / q.totient) *
              (((univ : Finset (DirichletCharacter ℂ q)).filter (fun χ ↦ χ.IsPrimitive)).card : ℝ)
            ≤ ((q : ℝ) / q.totient) * q.totient := by
              refine mul_le_mul_of_nonneg_left ?_ (by positivity)
              rw [← card_dirichletCharacter q]
              exact_mod_cast card_filter_le _ _
          _ = q := by field_simp
          _ ≤ ⌊Q⌋₊ := by exact_mod_cast (mem_Icc.1 hq).2
    _ = (⌊Q⌋₊ : ℝ) ^ 2 := by rw [sum_const, Nat.card_Icc, nsmul_eq_mul]; push_cast; ring
    _ ≤ Q ^ 2 := by gcongr; exact Nat.floor_le (by linarith)

/-- The trivial bound `|ψ'(y, χ)| ≤ (log 4 + 5) y`. -/
lemma norm_psiChar'_le_trivial {q : ℕ} (χ : DirichletCharacter ℂ q) {y : ℝ} (hy : 0 ≤ y) :
    ‖psiChar' χ y‖ ≤ (Real.log 4 + 5) * y := by
  classical
  have h1 : ‖psiChar χ y‖ ≤ (Real.log 4 + 4) * y := by
    refine (norm_sum_le _ _).trans ?_
    have : ∀ n ∈ Icc 1 ⌊y⌋₊, ‖χ n * (Λ n : ℂ)‖ ≤ Λ n := by
      intro n _
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg vonMangoldt_nonneg]
      exact mul_le_of_le_one_left vonMangoldt_nonneg (DirichletCharacter.norm_le_one χ _)
    refine (sum_le_sum this).trans ?_
    have hsub : Icc 1 ⌊y⌋₊ ⊆ Ioc 0 ⌊y⌋₊ := fun n hn ↦ by
      simp only [mem_Icc, mem_Ioc] at hn ⊢; omega
    refine (sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ ↦ vonMangoldt_nonneg).trans ?_
    exact Chebyshev.psi_le_const_mul_self hy
  unfold psiChar'
  refine (norm_sub_le _ _).trans ?_
  have h2 : ‖(if χ = 1 then (y : ℂ) else 0)‖ ≤ y := by
    split_ifs
    · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hy]
    · simpa using hy
  linarith

open scoped Classical in
/-- **Davenport, Ch. 28, (B) for general `U, V`** (the combination of (7) and (12)–(15), p. 167):
for `1 ≤ Q ≤ X`, `U, V ≥ 1`, `UV ≤ X` and any choice `y(q, χ) ∈ [0, X + 1)`,
`∑_{q ≤ Q} (q/φ(q)) ∑*_χ |ψ'(y(q,χ), χ)| ≪ (X + Q² X^{1/2} + Q X^{1/2} (UV)^{1/2} + Q X U^{-1/2}
  + Q X V^{-1/2} + Q² U + Q^{5/2} (U + V)) (log 2X)⁴`. -/
@[kb "davenport1980" "Ch 28, p. 167"]
theorem sum_psiChar'_le_UV : ∃ C : ℝ, 0 < C ∧ ∀ (Q : ℝ), 1 ≤ Q → ∀ (X U V : ℕ), 1 ≤ X →
    Q ≤ X → 1 ≤ U → 1 ≤ V → U * V ≤ X →
    ∀ y : (q : ℕ) → DirichletCharacter ℂ q → ℝ, (∀ q χ, 0 ≤ y q χ ∧ y q χ < X + 1) →
    ∑ q ∈ Icc 1 ⌊Q⌋₊, ((q : ℝ) / q.totient) *
        ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ ↦ χ.IsPrimitive),
          ‖psiChar' χ (y q χ)‖ ≤
      C * (X + Q ^ 2 * √X + Q * √X * √(U * V) + Q * X / √U + Q * X / √V + Q ^ 2 * U +
        Q ^ 2 * √Q * (U + V)) * Real.log (2 * X) ^ 4 := by
  obtain ⟨Cβ, hCβ, hβ⟩ := sum_norm_betaS₄_sq_le
  set K₄ := √((Real.log 4 + 4) * Cβ) with hK₄
  have hK₄0 : 0 ≤ K₄ := Real.sqrt_nonneg _
  refine ⟨600 + 2000 * K₄, by positivity, ?_⟩
  intro Q hQ X U V hX hQX hU hV hUV y hy
  set prim : (q : ℕ) → Finset (DirichletCharacter ℂ q) :=
    fun q ↦ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ ↦ χ.IsPrimitive) with hprim
  set w : ℕ → ℝ := fun q ↦ (q : ℝ) / q.totient with hw
  have hw0 : ∀ q, 0 ≤ w q := fun q ↦ by positivity
  set Nf : (q : ℕ) → DirichletCharacter ℂ q → ℕ := fun q χ ↦ ⌊y q χ⌋₊ with hNf
  have hNfX : ∀ q χ, Nf q χ ≤ X := fun q χ ↦
    Nat.lt_add_one_iff.1 ((Nat.floor_lt (hy q χ).1).2 (by exact_mod_cast (hy q χ).2))
  set D2 : (q : ℕ) → DirichletCharacter ℂ q → ℝ := fun q χ ↦
    ‖∑ t ∈ Icc 1 X, ∑ r ∈ (Icc 1 X).filter (fun r ↦ t * r ≤ Nf q χ),
      alphaS₂ U V t * 1 * χ ((t * r : ℕ) : ZMod q)‖ with hD2
  set D4 : (q : ℕ) → DirichletCharacter ℂ q → ℝ := fun q χ ↦
    ‖∑ m ∈ Icc 1 X, ∑ k ∈ (Icc 1 X).filter (fun k ↦ m * k ≤ Nf q χ),
      alphaS₄ X U V m * betaS₄ X V k * χ ((m * k : ℕ) : ZMod q)‖ with hD4
  have hXr : (1:ℝ) ≤ X := by exact_mod_cast hX
  have hUr : (1:ℝ) ≤ U := by exact_mod_cast hU
  have hVr : (1:ℝ) ≤ V := by exact_mod_cast hV
  have hUVr : (U:ℝ) * V ≤ X := by exact_mod_cast hUV
  have hlX : 0 ≤ Real.log X := Real.log_nonneg hXr
  set E₁ := (Real.log 4 + 5) * (2 * (X : ℝ)) with hE₁
  set cU := (Real.log 4 + 4) * U + U * Real.log X * (2 * √Q * Real.log X) +
    Real.log X * (V * (4 * √Q * Real.log X)) with hcU
  -- the bound for each character
  have hterm : ∀ q ∈ Icc 1 ⌊Q⌋₊, ∀ χ ∈ prim q,
      ‖psiChar' χ (y q χ)‖ ≤ (if q = 1 then E₁ else 0) + cU + D2 q χ + D4 q χ := by
    intro q hq χ hχ
    have hq1 := (mem_Icc.1 hq).1
    have hqQ : (q : ℝ) ≤ Q := (Nat.cast_le.2 (mem_Icc.1 hq).2).trans (Nat.floor_le (by linarith))
    have hcU0 : 0 ≤ cU := by positivity
    by_cases hq1' : q = 1
    · subst hq1'
      rw [if_pos rfl]
      have := norm_psiChar'_le_trivial χ (hy 1 χ).1
      have h2 : (Real.log 4 + 5) * y 1 χ ≤ E₁ :=
        mul_le_mul_of_nonneg_left (by linarith [(hy 1 χ).2]) (by positivity)
      have : 0 ≤ D2 1 χ := norm_nonneg _
      have : 0 ≤ D4 1 χ := norm_nonneg _
      linarith
    · have hq2 : 2 ≤ q := by omega
      have : NeZero q := ⟨by omega⟩
      have hprimχ : χ.IsPrimitive := (mem_filter.1 hχ).2
      have hχ1 := ne_one_of_isPrimitive hq2 hprimχ
      rw [if_neg hq1', zero_add]
      have hψ : psiChar' χ (y q χ) = ∑ n ∈ Icc 1 (Nf q χ), χ n * (Λ n : ℂ) := by
        simp [psiChar', psiChar, hχ1, hNf]
      rw [hψ]
      refine (norm_psi_prim_le hq2 hprimχ (hNfX q χ) U hV).trans ?_
      have hlq : Real.log q ≤ Real.log X := Real.log_le_log (by positivity) (hqQ.trans hQX)
      have hlq0 : 0 ≤ Real.log q := Real.log_natCast_nonneg q
      have hsq : √(q : ℝ) ≤ √Q := Real.sqrt_le_sqrt hqQ
      have hlU : Real.log U ≤ Real.log X :=
        Real.log_le_log (by linarith) (by nlinarith)
      have hlU0 : 0 ≤ Real.log U := Real.log_natCast_nonneg U
      have hlN : Real.log (Nf q χ) ≤ Real.log X := by
        rcases Nat.eq_zero_or_pos (Nf q χ) with h0 | hpos
        · rw [h0]; simpa using hlX
        · exact Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast hNfX q χ)
      have hlN0 : 0 ≤ Real.log (Nf q χ) := Real.log_natCast_nonneg _
      have e1 : (U:ℝ) * Real.log U * (2 * √q * Real.log q) ≤
          U * Real.log X * (2 * √Q * Real.log X) := by gcongr
      have e2 : Real.log (Nf q χ) * (V * (4 * √q * Real.log q)) ≤
          Real.log X * (V * (4 * √Q * Real.log X)) := by gcongr
      simp only [hD2, hD4, hcU]
      linarith
  -- summing
  have hsum : ∑ q ∈ Icc 1 ⌊Q⌋₊, w q * ∑ χ ∈ prim q, ‖psiChar' χ (y q χ)‖ ≤
      E₁ + cU * Q ^ 2 + ∑ q ∈ Icc 1 ⌊Q⌋₊, w q * ∑ χ ∈ prim q, D2 q χ +
        ∑ q ∈ Icc 1 ⌊Q⌋₊, w q * ∑ χ ∈ prim q, D4 q χ := by
    calc _ ≤ ∑ q ∈ Icc 1 ⌊Q⌋₊, w q * ∑ χ ∈ prim q,
          ((if q = 1 then E₁ else 0) + cU + D2 q χ + D4 q χ) :=
          sum_le_sum fun q hq ↦ mul_le_mul_of_nonneg_left (sum_le_sum (hterm q hq)) (hw0 q)
      _ = ∑ q ∈ Icc 1 ⌊Q⌋₊, (if q = 1 then w q * (prim q).card * E₁ else 0) +
          cU * ∑ q ∈ Icc 1 ⌊Q⌋₊, w q * ((prim q).card : ℝ) +
          ∑ q ∈ Icc 1 ⌊Q⌋₊, w q * ∑ χ ∈ prim q, D2 q χ +
          ∑ q ∈ Icc 1 ⌊Q⌋₊, w q * ∑ χ ∈ prim q, D4 q χ := by
          rw [mul_sum, ← sum_add_distrib, ← sum_add_distrib, ← sum_add_distrib]
          refine sum_congr rfl fun q _ ↦ ?_
          rw [sum_add_distrib, sum_add_distrib, sum_add_distrib, sum_const, nsmul_eq_mul]
          split_ifs <;> simp [sum_const, nsmul_eq_mul] <;> ring
      _ ≤ E₁ + cU * Q ^ 2 + ∑ q ∈ Icc 1 ⌊Q⌋₊, w q * ∑ χ ∈ prim q, D2 q χ +
          ∑ q ∈ Icc 1 ⌊Q⌋₊, w q * ∑ χ ∈ prim q, D4 q χ := by
          have h1 : ∑ q ∈ Icc 1 ⌊Q⌋₊, (if q = 1 then w q * (prim q).card * E₁ else 0) ≤ E₁ := by
            rw [sum_ite_eq' (Icc 1 ⌊Q⌋₊) 1 (fun q ↦ w q * (prim q).card * E₁)]
            split_ifs
            · have hc : ((prim 1).card : ℝ) ≤ 1 := by
                have := card_dirichletCharacter 1
                simp only [Nat.totient_one, Nat.cast_one] at this
                rw [← this]; exact_mod_cast card_filter_le _ _
              have hw1 : w 1 = 1 := by simp [hw]
              rw [hw1, one_mul]
              have : 0 ≤ E₁ := by positivity
              nlinarith
            · positivity
          have h2 : cU * ∑ q ∈ Icc 1 ⌊Q⌋₊, w q * ((prim q).card : ℝ) ≤ cU * Q ^ 2 :=
            mul_le_mul_of_nonneg_left (sum_weight_card_primitive_le hQ) (by positivity)
          linarith
  -- the type II sums
  have hD2b := dyadic_bilinear_sieve hQ hX hU (Tm := U * V) (alphaS₂ U V) (fun _ ↦ 1)
    (A := Real.log X ^ 2) (B := 1) (by positivity) zero_le_one
    (fun t ht ↦ alphaS₂_eq_zero_of_le ht) (fun t ht ↦ alphaS₂_eq_zero_of_lt ht)
    (sum_norm_alphaS₂_sq_le hUV) (fun K ↦ by simp [sum_const, Nat.card_Icc]) Nf hNfX
  have hD4b := dyadic_bilinear_sieve hQ hX hU (Tm := X / V) (alphaS₄ X U V) (betaS₄ X V)
    (A := (Real.log 4 + 4) * Real.log X) (B := Cβ * (1 + Real.log X) ^ 3) (by positivity)
    (by positivity) (fun t ht ↦ alphaS₄_eq_zero_of_le ht) (fun t ht ↦ alphaS₄_eq_zero_of_lt ht)
    (sum_norm_alphaS₄_sq_le X U V) (fun K ↦ hβ X V K hX) Nf hNfX
  change ∑ q ∈ Icc 1 ⌊Q⌋₊, w q * ∑ χ ∈ prim q, D2 q χ ≤ _ at hD2b
  change ∑ q ∈ Icc 1 ⌊Q⌋₊, w q * ∑ χ ∈ prim q, D4 q χ ≤ _ at hD4b
  -- final bookkeeping
  set ℓ := Real.log (2 * X) with hℓ
  have hℓX : Real.log X ≤ ℓ := Real.log_le_log (by linarith) (by linarith)
  have hℓ1 : 1 ≤ 1.45 * ℓ := by
    have h2 : Real.log 2 ≤ ℓ := Real.log_le_log (by norm_num) (by linarith)
    have := Real.log_two_gt_d9
    linarith
  have hℓ0 : 0 ≤ ℓ := by linarith
  set Z := (X : ℝ) + Q ^ 2 * √X + Q * √X * √(U * V) + Q * X / √U + Q * X / √V + Q ^ 2 * U +
        Q ^ 2 * √Q * (U + V) with hZ
  have hQ0 : 0 ≤ Q := by linarith
  have hsX : 0 ≤ √(X:ℝ) := Real.sqrt_nonneg _
  have hsQ : 0 ≤ √Q := Real.sqrt_nonneg _
  have hsU : 0 < √(U:ℝ) := Real.sqrt_pos.2 (by linarith)
  have hsV : 0 < √(V:ℝ) := Real.sqrt_pos.2 (by linarith)
  have z1 : 0 ≤ Q ^ 2 * √(X:ℝ) := by positivity
  have z2 : 0 ≤ Q * √(X:ℝ) * √((U:ℝ) * V) := by positivity
  have z3 : 0 ≤ Q * X / √(U:ℝ) := by positivity
  have z4 : 0 ≤ Q * X / √(V:ℝ) := by positivity
  have z5 : 0 ≤ Q ^ 2 * (U:ℝ) := by positivity
  have z6 : 0 ≤ Q ^ 2 * √Q * ((U:ℝ) + V) := by positivity
  have hZ0 : 0 ≤ Z := by positivity
  have hZX : (X:ℝ) ≤ Z := by simp only [hZ]; linarith only [z1, z2, z3, z4, z5, z6]
  have hp0 : 0 ≤ ℓ ^ 4 := by positivity
  have hp1 : 1 ≤ 4.43 * ℓ ^ 4 := by
    have h := pow_le_pow_left₀ zero_le_one hℓ1 4
    rw [one_pow, mul_pow] at h
    norm_num at h
    linarith only [h, hp0]
  have hl3 : ℓ ^ 3 ≤ 1.45 * ℓ ^ 4 := by
    calc ℓ ^ 3 = ℓ ^ 3 * 1 := by ring
      _ ≤ ℓ ^ 3 * (1.45 * ℓ) := mul_le_mul_of_nonneg_left hℓ1 (by positivity)
      _ = _ := by ring
  have hl2 : ℓ ^ 2 ≤ 2.11 * ℓ ^ 4 := by
    have h := pow_le_pow_left₀ zero_le_one hℓ1 2
    rw [one_pow, mul_pow] at h
    norm_num at h
    calc ℓ ^ 2 = ℓ ^ 2 * 1 := by ring
      _ ≤ ℓ ^ 2 * (841 / 400 * ℓ ^ 2) := mul_le_mul_of_nonneg_left h (by positivity)
      _ ≤ _ := by nlinarith only [hp0]
  -- E₁
  have hlog4 : Real.log 4 < 1.3863 := by
    rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    have := Real.log_two_lt_d9; push_cast; linarith
  have t1 : E₁ ≤ 56.8 * Z * ℓ ^ 4 := by
    have h1 : E₁ ≤ 12.8 * Z := by
      have hX0 : (0:ℝ) ≤ 2 * X := by linarith only [hXr]
      calc E₁ = (Real.log 4 + 5) * (2 * X) := rfl
        _ ≤ 6.4 * (2 * X) := mul_le_mul_of_nonneg_right (by linarith only [hlog4]) hX0
        _ ≤ 12.8 * Z := by linarith only [hZX]
    calc E₁ ≤ 12.8 * Z * 1 := by linarith only [h1]
      _ ≤ 12.8 * Z * (4.43 * ℓ ^ 4) := mul_le_mul_of_nonneg_left hp1 (by positivity)
      _ ≤ _ := by nlinarith only [hp0, hZ0]
  -- cU Q²
  have t2 : cU * Q ^ 2 ≤ 32.5 * Z * ℓ ^ 4 := by
    have e : cU * Q ^ 2 = (Real.log 4 + 4) * (Q ^ 2 * U) +
        (2 * U + 4 * V) * (Q ^ 2 * √Q) * Real.log X ^ 2 := by simp only [hcU]; ring
    have hZU : Q ^ 2 * (U:ℝ) ≤ Z := by simp only [hZ]; linarith only [z1, z2, z3, z4, hXr, z6]
    have hZUV : Q ^ 2 * √Q * ((U:ℝ) + V) ≤ Z := by
      simp only [hZ]; linarith only [z1, z2, z3, z4, hXr, z5]
    have h1 : (Real.log 4 + 4) * (Q ^ 2 * U) ≤ 5.39 * Z := by
      calc (Real.log 4 + 4) * (Q ^ 2 * U) ≤ 5.39 * (Q ^ 2 * U) :=
            mul_le_mul_of_nonneg_right (by linarith only [hlog4]) z5
        _ ≤ 5.39 * Z := by linarith only [hZU]
    have h2 : (2 * (U:ℝ) + 4 * V) * (Q ^ 2 * √Q) ≤ 4 * Z := by
      have : 0 ≤ Q ^ 2 * √Q * (U:ℝ) := by positivity
      calc (2 * (U:ℝ) + 4 * V) * (Q ^ 2 * √Q) ≤ 4 * (Q ^ 2 * √Q * ((U:ℝ) + V)) := by
            nlinarith only [this]
        _ ≤ 4 * Z := by linarith only [hZUV]
    have h3 : Real.log X ^ 2 ≤ 2.11 * ℓ ^ 4 := (pow_le_pow_left₀ hlX hℓX 2).trans hl2
    have h4 : 0 ≤ (2 * (U:ℝ) + 4 * V) * (Q ^ 2 * √Q) := by positivity
    rw [e]
    have h5 := mul_le_mul h2 h3 (by positivity) (by positivity)
    have h6 : (Real.log 4 + 4) * (Q ^ 2 * U) ≤ 5.39 * Z * (4.43 * ℓ ^ 4) := by
      calc _ ≤ 5.39 * Z * 1 := by linarith only [h1]
        _ ≤ _ := mul_le_mul_of_nonneg_left hp1 (by positivity)
    nlinarith only [h5, h6, hZ0, hp0]
  -- D2
  have hY₂ : (X:ℝ) + Q ^ 2 * √X + Q * √X * √((U * V : ℕ) : ℝ) + Q * X / √U ≤ Z := by
    push_cast; simp only [hZ]; linarith only [z4, z5, z6]
  have t3 : ∑ q ∈ Icc 1 ⌊Q⌋₊, w q * ∑ χ ∈ prim q, D2 q χ ≤ 478.5 * Z * ℓ ^ 4 := by
    refine hD2b.trans ?_
    rw [mul_one, Real.sqrt_sq hlX]
    have hY0 : 0 ≤ (X:ℝ) + Q ^ 2 * √X + Q * √X * √((U * V : ℕ) : ℝ) + Q * X / √U := by
      positivity
    calc 330 * Real.log X * ((X:ℝ) + Q ^ 2 * √X + Q * √X * √((U * V : ℕ) : ℝ) + Q * X / √U) *
          ℓ ^ 2 ≤ 330 * ℓ * Z * ℓ ^ 2 := by gcongr
      _ = 330 * Z * ℓ ^ 3 := by ring
      _ ≤ 330 * Z * (1.45 * ℓ ^ 4) := by gcongr
      _ = _ := by ring
  -- D4
  have hY₄ : (X:ℝ) + Q ^ 2 * √X + Q * √X * √((X / V : ℕ) : ℝ) + Q * X / √U ≤ Z := by
    have h1 : √((X / V : ℕ) : ℝ) ≤ √X / √V := by
      rw [← Real.sqrt_div' _ (by linarith : (0:ℝ) ≤ V)]
      exact Real.sqrt_le_sqrt Nat.cast_div_le
    have h2 : Q * √(X:ℝ) * √((X / V : ℕ) : ℝ) ≤ Q * X / √V := by
      calc Q * √(X:ℝ) * √((X / V : ℕ) : ℝ) ≤ Q * √(X:ℝ) * (√X / √V) := by gcongr
        _ = Q * (√(X:ℝ) * √X) / √V := by ring
        _ = Q * X / √V := by rw [Real.mul_self_sqrt (by linarith)]
    simp only [hZ]; linarith only [h2, z2, z5, z6]
  have hAB : √((Real.log 4 + 4) * Real.log X * (Cβ * (1 + Real.log X) ^ 3)) ≤
      K₄ * (1 + Real.log X) ^ 2 := by
    rw [hK₄, ← Real.sqrt_sq (by positivity : (0:ℝ) ≤ (1 + Real.log X) ^ 2),
      ← Real.sqrt_mul (by positivity)]
    refine Real.sqrt_le_sqrt ?_
    have : Real.log X * (1 + Real.log X) ^ 3 ≤ ((1 + Real.log X) ^ 2) ^ 2 := by
      have : Real.log X ≤ 1 + Real.log X := by linarith
      calc Real.log X * (1 + Real.log X) ^ 3 ≤ (1 + Real.log X) * (1 + Real.log X) ^ 3 := by
            gcongr
        _ = _ := by ring
    have hc : 0 ≤ (Real.log 4 + 4) * Cβ := by positivity
    calc (Real.log 4 + 4) * Real.log X * (Cβ * (1 + Real.log X) ^ 3)
        = (Real.log 4 + 4) * Cβ * (Real.log X * (1 + Real.log X) ^ 3) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left this hc
  have t4 : ∑ q ∈ Icc 1 ⌊Q⌋₊, w q * ∑ χ ∈ prim q, D4 q χ ≤ 1984 * K₄ * Z * ℓ ^ 4 := by
    refine hD4b.trans ?_
    have hY0 : 0 ≤ (X:ℝ) + Q ^ 2 * √X + Q * √X * √((X / V : ℕ) : ℝ) + Q * X / √U := by
      positivity
    have h1 : (1 + Real.log X) ^ 2 ≤ 6.01 * ℓ ^ 2 := by
      have : 1 + Real.log X ≤ 2.45 * ℓ := by linarith only [hℓX, hℓ1]
      have h0 : 0 ≤ 1 + Real.log X := by linarith only [hlX]
      calc (1 + Real.log X) ^ 2 ≤ (2.45 * ℓ) ^ 2 := pow_le_pow_left₀ h0 this 2
        _ ≤ _ := by nlinarith only [sq_nonneg ℓ]
    calc 330 * √((Real.log 4 + 4) * Real.log X * (Cβ * (1 + Real.log X) ^ 3)) *
          ((X:ℝ) + Q ^ 2 * √X + Q * √X * √((X / V : ℕ) : ℝ) + Q * X / √U) * ℓ ^ 2
        ≤ 330 * (K₄ * (6.01 * ℓ ^ 2)) * Z * ℓ ^ 2 := by
          gcongr
          exact hAB.trans (mul_le_mul_of_nonneg_left h1 hK₄0)
      _ = 1983.3 * K₄ * Z * ℓ ^ 4 := by ring
      _ ≤ _ := by
        have : 0 ≤ K₄ * Z * ℓ ^ 4 := by positivity
        nlinarith only [this]
  have hfin : E₁ + cU * Q ^ 2 + ∑ q ∈ Icc 1 ⌊Q⌋₊, w q * ∑ χ ∈ prim q, D2 q χ +
      ∑ q ∈ Icc 1 ⌊Q⌋₊, w q * ∑ χ ∈ prim q, D4 q χ ≤ (600 + 2000 * K₄) * Z * ℓ ^ 4 := by
    have : 0 ≤ Z * ℓ ^ 4 := by positivity
    have : 0 ≤ K₄ * Z * ℓ ^ 4 := by positivity
    nlinarith only [t1, t2, t3, t4, this, hZ0, hp0]
  exact hsum.trans hfin

/-! ### The choice of `U = V` (Davenport, p. 168) -/

lemma Z_bound_small {R t X U : ℝ} (hR : 1 ≤ R) (ht1 : 1 ≤ t) (htR : t ≤ R ^ 2) (hX0 : 0 ≤ X)
    (hX : X ≤ R ^ 6) (hU1 : R ^ 2 / 2 ≤ U) (hU2 : U ≤ R ^ 2) :
    X + t ^ 2 * √X + t * √X * √(U * U) + t * X / √U + t * X / √U + t ^ 2 * U +
      t ^ 2 * √t * (U + U) ≤ 7 * (R ^ 6 + R ^ 5 * t + R ^ 3 * t ^ 2) := by
  have hR0 : 0 < R := by linarith
  have hU0 : 0 < U := lt_of_lt_of_le (by positivity) hU1
  have hsX : √X ≤ R ^ 3 := by
    rw [show R ^ 3 = √((R ^ 3) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hst : √t ≤ R := by
    rw [show R = √(R ^ 2) from (Real.sqrt_sq hR0.le).symm]; exact Real.sqrt_le_sqrt htR
  have hsU : 0 < √U := Real.sqrt_pos.2 hU0
  have hRU : R ≤ 1.5 * √U := by
    rw [show R = √(R ^ 2) from (Real.sqrt_sq hR0.le).symm,
      show (1.5:ℝ) * √U = √(2.25 * U) by
        rw [Real.sqrt_mul (by norm_num), show (2.25:ℝ) = 1.5 ^ 2 by norm_num,
          Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by linarith)
  have hUU : √(U * U) = U := Real.sqrt_mul_self hU0.le
  have ht0 : 0 ≤ t := by linarith
  have hsX0 : 0 ≤ √X := Real.sqrt_nonneg X
  have hst0 : 0 ≤ √t := Real.sqrt_nonneg t
  have a2 : t ^ 2 * √X ≤ R ^ 3 * t ^ 2 := by nlinarith [sq_nonneg t]
  have a3 : t * √X * √(U * U) ≤ R ^ 5 * t := by
    rw [hUU]
    calc t * √X * U ≤ t * R ^ 3 * R ^ 2 := by gcongr
      _ = R ^ 5 * t := by ring
  have a4 : t * X / √U ≤ 1.5 * (R ^ 5 * t) := by
    rw [div_le_iff₀ hsU]
    calc t * X ≤ t * R ^ 6 := by gcongr
      _ = R ^ 5 * t * R := by ring
      _ ≤ R ^ 5 * t * (1.5 * √U) := by gcongr
      _ = _ := by ring
  have a5 : t ^ 2 * U ≤ R ^ 5 * t := by
    calc t ^ 2 * U = t * t * U := by ring
      _ ≤ t * R ^ 2 * R ^ 2 := by gcongr
      _ = R ^ 4 * t := by ring
      _ ≤ R ^ 5 * t := by gcongr; nlinarith [pow_pos hR0 4]
  have a6 : t ^ 2 * √t * (U + U) ≤ 2 * (R ^ 3 * t ^ 2) := by
    calc t ^ 2 * √t * (U + U) ≤ t ^ 2 * R * (R ^ 2 + R ^ 2) := by gcongr
      _ = 2 * (R ^ 3 * t ^ 2) := by ring
  have p1 : 0 ≤ R ^ 6 := by positivity
  have p2 : 0 ≤ R ^ 5 * t := by positivity
  have p3 : 0 ≤ R ^ 3 * t ^ 2 := by positivity
  linarith

lemma Z_bound_large {R t X U : ℝ} (hR : 1 ≤ R) (htR : R ^ 2 ≤ t) (hX0 : 0 ≤ X)
    (hX : X ≤ R ^ 6) (hU1 : R ^ 4 / (2 * t) ≤ U) (hU2 : U ≤ R ^ 4 / t) :
    X + t ^ 2 * √X + t * √X * √(U * U) + t * X / √U + t * X / √U + t ^ 2 * U +
      t ^ 2 * √t * (U + U) ≤ 7 * (R ^ 6 + R ^ 5 * t + R ^ 3 * t ^ 2) := by
  have hR0 : 0 < R := by linarith
  have ht0 : 0 < t := lt_of_lt_of_le (by positivity) htR
  have hU0 : 0 < U := lt_of_lt_of_le (by positivity) hU1
  have hsX : √X ≤ R ^ 3 := by
    rw [show R ^ 3 = √((R ^ 3) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
    exact Real.sqrt_le_sqrt (by nlinarith)
  set s := √t with hs
  have hs2 : s ^ 2 = t := Real.sq_sqrt ht0.le
  have hRs : R ≤ s := by
    rw [show R = √(R ^ 2) from (Real.sqrt_sq hR0.le).symm]; exact Real.sqrt_le_sqrt htR
  have hs0 : 0 < s := lt_of_lt_of_le hR0 hRs
  have hsU : 0 < √U := Real.sqrt_pos.2 hU0
  have hR2U : R ^ 2 ≤ 1.5 * s * √U := by
    rw [show R ^ 2 = √((R ^ 2) ^ 2) from (Real.sqrt_sq (by positivity)).symm,
      show (1.5:ℝ) * s * √U = √(2.25 * t * U) by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by norm_num),
          show (2.25:ℝ) = 1.5 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    refine Real.sqrt_le_sqrt ?_
    have : R ^ 4 ≤ 2 * t * U := by
      rw [div_le_iff₀ (by positivity)] at hU1; linarith
    nlinarith
  have hUU : √(U * U) = U := Real.sqrt_mul_self hU0.le
  have hsX0 : 0 ≤ √X := Real.sqrt_nonneg X
  have htU : t * U ≤ R ^ 4 := by rw [le_div_iff₀ ht0] at hU2; linarith
  have hR4 : R ^ 4 ≤ t ^ 2 := by nlinarith
  have a2 : t ^ 2 * √X ≤ R ^ 3 * t ^ 2 := by nlinarith [sq_nonneg t]
  have a3 : t * √X * √(U * U) ≤ R ^ 3 * t ^ 2 := by
    rw [hUU]
    calc t * √X * U = √X * (t * U) := by ring
      _ ≤ R ^ 3 * R ^ 4 := by gcongr
      _ ≤ R ^ 3 * t ^ 2 := by gcongr
  have a4 : t * X / √U ≤ 1.5 * (R ^ 3 * t ^ 2) := by
    rw [div_le_iff₀ hsU]
    calc t * X ≤ t * R ^ 6 := by gcongr
      _ = t * R ^ 4 * R ^ 2 := by ring
      _ ≤ t * R ^ 4 * (1.5 * s * √U) := by gcongr
      _ = 1.5 * t * R ^ 3 * (R * s) * √U := by ring
      _ ≤ 1.5 * t * R ^ 3 * (s * s) * √U := by gcongr
      _ = 1.5 * (R ^ 3 * t ^ 2) * √U := by rw [← sq, hs2]; ring
  have a5 : t ^ 2 * U ≤ R ^ 5 * t := by
    calc t ^ 2 * U = t * (t * U) := by ring
      _ ≤ t * R ^ 4 := by gcongr
      _ ≤ t * R ^ 5 := by gcongr; nlinarith [pow_pos hR0 4]
      _ = _ := by ring
  have a6 : t ^ 2 * √t * (U + U) ≤ 2 * (R ^ 3 * t ^ 2) := by
    calc t ^ 2 * √t * (U + U) = 2 * s * t * (t * U) := by rw [← hs]; ring
      _ ≤ 2 * s * t * R ^ 4 := by gcongr
      _ = 2 * t * R ^ 3 * (R * s) := by ring
      _ ≤ 2 * t * R ^ 3 * (s * s) := by gcongr
      _ = 2 * (R ^ 3 * t ^ 2) := by rw [← sq, hs2]; ring
  have p1 : 0 ≤ R ^ 6 := by positivity
  have p2 : 0 ≤ R ^ 5 * t := by positivity
  have p3 : 0 ≤ R ^ 3 * t ^ 2 := by positivity
  linarith

open scoped Classical in
/-- **Davenport, Ch. 28, p. 162, estimate (B)**: for `x ≥ 3`, `1 ≤ Q ≤ x^{1/2}` and any choice
`y(q, χ) ∈ [0, x]`,
`∑_{q ≤ Q} (q/φ(q)) ∑*_χ |ψ'(y(q, χ), χ)| ≪ (x + x^{5/6} Q + x^{1/2} Q²)(log x)⁴`.
(The book states it for all `Q ≥ 1`; only `Q ≤ x^{1/2}` is used for the theorem.) -/
@[kb "davenport1980" "Ch 28, p. 162, (B)"]
theorem sum_psiChar'_le : ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 3 ≤ x → ∀ Q : ℝ, 1 ≤ Q → Q ≤ √x →
    ∀ y : (q : ℕ) → DirichletCharacter ℂ q → ℝ, (∀ q χ, 0 ≤ y q χ ∧ y q χ ≤ x) →
    ∑ q ∈ Icc 1 ⌊Q⌋₊, ((q : ℝ) / q.totient) *
        ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ ↦ χ.IsPrimitive),
          ‖psiChar' χ (y q χ)‖ ≤
      C * (x + x ^ ((5:ℝ) / 6) * Q + √x * Q ^ 2) * Real.log x ^ 4 := by
  obtain ⟨C₀, hC₀, hB⟩ := sum_psiChar'_le_UV
  refine ⟨112 * C₀, by positivity, ?_⟩
  intro x hx Q hQ hQx y hy
  have hx0 : 0 ≤ x := by linarith
  set X := ⌊x⌋₊ with hXdef
  have hXx : (X : ℝ) ≤ x := Nat.floor_le hx0
  have hxX : x < X + 1 := Nat.lt_floor_add_one x
  have hX1 : 1 ≤ X := Nat.le_floor (by norm_num; linarith)
  have hXr : (1:ℝ) ≤ X := by exact_mod_cast hX1
  have hsx2 : √x ^ 2 = x := Real.sq_sqrt hx0
  have hsx3 : (1.7:ℝ) ≤ √x := by
    rw [show (1.7:ℝ) = √(1.7 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by norm_num; linarith)
  have hQX : Q ≤ X := by nlinarith
  have hy' : ∀ q χ, 0 ≤ y q χ ∧ y q χ < X + 1 := fun q χ ↦ ⟨(hy q χ).1, by linarith [(hy q χ).2]⟩
  -- `R = x^{1/6}`
  set R := x ^ ((1:ℝ) / 6) with hRdef
  have hR1 : 1 ≤ R := Real.one_le_rpow (by linarith) (by norm_num)
  have hR0 : 0 < R := by linarith
  have hpow : ∀ n : ℕ, R ^ n = x ^ ((n : ℝ) / 6) := fun n ↦ by
    rw [hRdef, ← Real.rpow_natCast, ← Real.rpow_mul hx0]; ring_nf
  have hR6 : R ^ 6 = x := by rw [hpow]; norm_num
  have hR5 : R ^ 5 = x ^ ((5:ℝ) / 6) := by rw [hpow]; norm_num
  have hR3 : R ^ 3 = √x := by
    rw [← hR6, show R ^ 6 = (R ^ 3) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  have hXR : (X : ℝ) ≤ R ^ 6 := by rw [hR6]; exact hXx
  -- the logarithm
  have hlog : Real.log (2 * X) ^ 4 ≤ 16 * Real.log x ^ 4 := by
    have h1 : 0 ≤ Real.log (2 * X) := Real.log_nonneg (by linarith)
    have h2 : Real.log (2 * X) ≤ 2 * Real.log x := by
      rw [← Real.log_rpow (by linarith)]
      exact Real.log_le_log (by positivity) (by rw [Real.rpow_two]; nlinarith)
    calc Real.log (2 * X) ^ 4 ≤ (2 * Real.log x) ^ 4 := pow_le_pow_left₀ h1 h2 4
      _ = 16 * Real.log x ^ 4 := by ring
  have hT : 0 ≤ R ^ 6 + R ^ 5 * Q + R ^ 3 * Q ^ 2 := by positivity
  have hfinal : ∀ Z : ℝ, Z ≤ 7 * (R ^ 6 + R ^ 5 * Q + R ^ 3 * Q ^ 2) →
      C₀ * Z * Real.log (2 * X) ^ 4 ≤
        112 * C₀ * (x + x ^ ((5:ℝ) / 6) * Q + √x * Q ^ 2) * Real.log x ^ 4 := by
    intro Z hZ
    have e : 112 * C₀ * (x + x ^ ((5:ℝ) / 6) * Q + √x * Q ^ 2) =
        112 * C₀ * (R ^ 6 + R ^ 5 * Q + R ^ 3 * Q ^ 2) := by rw [hR6, hR5, hR3]
    rw [e]
    have hl0 : 0 ≤ Real.log (2 * X) ^ 4 := by positivity
    calc C₀ * Z * Real.log (2 * X) ^ 4
        ≤ C₀ * (7 * (R ^ 6 + R ^ 5 * Q + R ^ 3 * Q ^ 2)) * Real.log (2 * X) ^ 4 := by gcongr
      _ ≤ C₀ * (7 * (R ^ 6 + R ^ 5 * Q + R ^ 3 * Q ^ 2)) * (16 * Real.log x ^ 4) := by gcongr
      _ = _ := by ring
  rcases le_or_gt Q (R ^ 2) with hcase | hcase
  · -- `U = ⌊x^{1/3}⌋`
    have hR2 : (1:ℝ) ≤ R ^ 2 := one_le_pow₀ hR1
    set U := ⌊R ^ 2⌋₊ with hU
    have hU1 : 1 ≤ U := Nat.le_floor (by exact_mod_cast hR2)
    have hUa : R ^ 2 / 2 ≤ U := half_le_floor hR2
    have hUb : (U : ℝ) ≤ R ^ 2 := Nat.floor_le (by positivity)
    have hUU : U * U ≤ X := by
      refine Nat.le_floor ?_
      push_cast
      calc (U : ℝ) * U ≤ R ^ 2 * R ^ 2 := by gcongr
        _ = R ^ 4 := by ring
        _ ≤ R ^ 6 := pow_le_pow_right₀ hR1 (by norm_num)
        _ = x := hR6
    refine (hB Q hQ X U U hX1 hQX hU1 hU1 hUU y hy').trans (hfinal _ ?_)
    exact Z_bound_small hR1 hQ hcase (by positivity) hXR hUa hUb
  · -- `U = ⌊x^{2/3}/Q⌋`
    have hQ0 : 0 < Q := by linarith
    have hQR3 : Q ≤ R ^ 3 := hR3 ▸ hQx
    have hR4Q : 1 ≤ R ^ 4 / Q := by
      rw [le_div_iff₀ hQ0, one_mul]
      exact hQR3.trans (pow_le_pow_right₀ hR1 (by norm_num))
    set U := ⌊R ^ 4 / Q⌋₊ with hU
    have hU1 : 1 ≤ U := Nat.le_floor (by exact_mod_cast hR4Q)
    have hUa : R ^ 4 / (2 * Q) ≤ U := by
      have := half_le_floor hR4Q
      rw [div_div, mul_comm] at this; exact this
    have hUb : (U : ℝ) ≤ R ^ 4 / Q := Nat.floor_le (by positivity)
    have hUU : U * U ≤ X := by
      refine Nat.le_floor ?_
      push_cast
      have hQ2 : R ^ 4 ≤ Q ^ 2 := by
        have := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ R ^ 2) hcase.le 2
        rw [← pow_mul] at this; exact this
      have hUQ : (U : ℝ) * Q ≤ R ^ 4 := by rw [le_div_iff₀ hQ0] at hUb; exact hUb
      have hU0 : (0:ℝ) ≤ U := Nat.cast_nonneg U
      have h1 : ((U : ℝ) * Q) ^ 2 ≤ (R ^ 4) ^ 2 := pow_le_pow_left₀ (by positivity) hUQ 2
      have h2 : (R ^ 4) ^ 2 ≤ R ^ 4 * Q ^ 2 := by
        rw [sq]; exact mul_le_mul_of_nonneg_left hQ2 (by positivity)
      have h3 : (U : ℝ) * U * Q ^ 2 ≤ R ^ 4 * Q ^ 2 := by
        calc (U : ℝ) * U * Q ^ 2 = ((U : ℝ) * Q) ^ 2 := by ring
          _ ≤ _ := h1.trans h2
      calc (U : ℝ) * U ≤ R ^ 4 := le_of_mul_le_mul_right h3 (by positivity)
        _ ≤ R ^ 6 := pow_le_pow_right₀ hR1 (by norm_num)
        _ = x := hR6
    refine (hB Q hQ X U U hX1 hQX hU1 hU1 hUU y hy').trans (hfinal _ ?_)
    exact Z_bound_large hR1 hcase.le (by positivity) hXR hUa hUb

end NTKB.Davenport
