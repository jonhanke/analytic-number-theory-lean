/- Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license. -/
import NTKB.Analytic.Davenport.Sieve.BombieriB
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Bombieri's theorem (Davenport, Chapter 28)

For fixed `A > 0` and `x^{1/2} (log x)^{-A} ≤ Q ≤ x^{1/2}`,
`∑_{q ≤ Q} E*(x, q) ≪ x^{1/2} Q (log x)⁵`, where
`E*(x, q) = max_{y ≤ x} max_{(a, q) = 1} |ψ(y; q, a) - y/φ(q)|`.

The maxima are arbitrary choices `y(q) ∈ [0, x]`, `a(q)` coprime to `q`. The proof is the book's
(pp. 162–164): reduction to primitive characters (`psiAP_sub_eq`, `norm_psiChar'_sub_le`,
`sum_sum_primitiveCharacter_le`), small moduli by the Siegel–Walfisz estimate ((C) of §22, the named
input `SiegelWalfiszHypothesis` of `BarbanDavenportHalberstam.lean`), large moduli by (B)
(`sum_psiChar'_le`) and partial summation.
-/

open Finset

namespace NTKB.Davenport

/-! ### Partial summation -/

/-- Abel summation: `∑_{Q₁ < q ≤ Q} a_q/q ≤ S(Q)/Q + ∑_{Q₁ ≤ t < Q} S(t)/(t(t+1))`,
`S(t) = ∑_{q ≤ t} a_q`, for `a ≥ 0`, `1 ≤ Q₁ ≤ Q`. -/
lemma sum_div_le_abel (a : ℕ → ℝ) (ha : ∀ q, 0 ≤ a q) {Q₁ : ℕ} (hQ₁ : 1 ≤ Q₁) {Q : ℕ}
    (h : Q₁ ≤ Q) :
    ∑ q ∈ Ioc Q₁ Q, a q / q ≤ (∑ q ∈ Icc 1 Q, a q) / Q +
      ∑ t ∈ Ico Q₁ Q, (∑ q ∈ Icc 1 t, a q) / (t * (t + 1)) := by
  induction Q, h using Nat.le_induction with
  | base =>
    simp only [Ioc_self, sum_empty, Ico_self, add_zero]
    exact div_nonneg (sum_nonneg fun q _ ↦ ha q) (Nat.cast_nonneg _)
  | succ Q hQ ih =>
    have hQ1 : (1:ℝ) ≤ Q := by exact_mod_cast hQ₁.trans hQ
    rw [sum_Ioc_succ_top hQ, sum_Ico_succ_top hQ, sum_Icc_succ_top (by omega)]
    set S := ∑ q ∈ Icc 1 Q, a q
    set T := ∑ t ∈ Ico Q₁ Q, (∑ q ∈ Icc 1 t, a q) / (t * (t + 1))
    have key : S / Q + a (Q + 1) / ((Q + 1 : ℕ) : ℝ) =
        (S + a (Q + 1)) / ((Q + 1 : ℕ) : ℝ) + S / (Q * (Q + 1)) := by
      push_cast; field_simp; ring
    push_cast at key ⊢
    linarith

/-- `∑_{Q₁ ≤ t < Q} 1/(t(t+1)) ≤ 1/Q₁`. -/
lemma sum_Ico_inv_mul_succ_le {Q₁ : ℕ} (hQ₁ : 1 ≤ Q₁) (Q : ℕ) :
    ∑ t ∈ Ico Q₁ Q, (1 : ℝ) / (t * (t + 1)) ≤ 1 / Q₁ := by
  have key : ∀ Q, Q₁ ≤ Q → ∑ t ∈ Ico Q₁ Q, (1 : ℝ) / (t * (t + 1)) = 1 / Q₁ - 1 / Q := by
    intro Q h
    induction Q, h using Nat.le_induction with
    | base => simp
    | succ Q hQ ih =>
      have hQ1 : (1:ℝ) ≤ Q := by exact_mod_cast hQ₁.trans hQ
      rw [sum_Ico_succ_top hQ, ih]
      push_cast; field_simp; ring
  rcases le_or_gt Q₁ Q with h | h
  · rw [key Q h]
    have : (0:ℝ) ≤ 1 / Q := by positivity
    linarith
  · rw [Ico_eq_empty (by omega), sum_empty]; positivity

/-- `∑_{Q₁ ≤ t < Q} 1/(t+1) ≤ 1 + log Q`. -/
lemma sum_Ico_inv_succ_le (Q₁ Q : ℕ) :
    ∑ t ∈ Ico Q₁ Q, (1 : ℝ) / (t + 1) ≤ 1 + Real.log Q := by
  calc ∑ t ∈ Ico Q₁ Q, (1 : ℝ) / (t + 1) ≤ ∑ t ∈ range Q, (1 : ℝ) / (t + 1) := by
        refine sum_le_sum_of_subset_of_nonneg (fun t ht ↦ ?_) fun _ _ _ ↦ by positivity
        simp only [mem_Ico, mem_range] at ht ⊢; omega
    _ = (harmonic Q : ℝ) := by
        simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, one_div]
        refine sum_congr rfl fun t _ ↦ ?_
        push_cast; ring
    _ ≤ 1 + Real.log Q := harmonic_le_one_add_log Q

/-- Partial summation with `S(t) ≤ α + βt + γt²`:
`∑_{Q₁ < q ≤ Q} a_q/q ≤ 2α/Q₁ + β(2 + log Q) + 2γQ`. -/
lemma sum_div_le_of_sum_le (a : ℕ → ℝ) (ha : ∀ q, 0 ≤ a q) {Q₁ Q : ℕ} (hQ₁ : 1 ≤ Q₁)
    (h : Q₁ ≤ Q) {α β γ : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 ≤ γ)
    (hS : ∀ t ∈ Icc Q₁ Q, ∑ q ∈ Icc 1 t, a q ≤ α + β * t + γ * t ^ 2) :
    ∑ q ∈ Ioc Q₁ Q, a q / q ≤ 2 * α / Q₁ + β * (2 + Real.log Q) + 2 * γ * Q := by
  have hQ₁r : (1:ℝ) ≤ Q₁ := by exact_mod_cast hQ₁
  have hQr : (Q₁:ℝ) ≤ Q := by exact_mod_cast h
  refine (sum_div_le_abel a ha hQ₁ h).trans ?_
  have h1 : (∑ q ∈ Icc 1 Q, a q) / Q ≤ α / Q₁ + β + γ * Q := by
    rw [div_le_iff₀ (by linarith)]
    have := hS Q (mem_Icc.2 ⟨h, le_rfl⟩)
    have : α ≤ α / Q₁ * Q := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith)]; nlinarith
    nlinarith
  have h2 : ∑ t ∈ Ico Q₁ Q, (∑ q ∈ Icc 1 t, a q) / (t * (t + 1)) ≤
      ∑ t ∈ Ico Q₁ Q, (α * (1 / (t * (t + 1))) + β * (1 / (t + 1)) + γ) := by
    refine sum_le_sum fun t ht ↦ ?_
    have ht' := mem_Ico.1 ht
    have htr : (1:ℝ) ≤ t := by exact_mod_cast hQ₁.trans ht'.1
    have hSt := hS t (mem_Icc.2 ⟨ht'.1, ht'.2.le⟩)
    rw [div_le_iff₀ (by positivity)]
    have e : (α * (1 / (t * (t + 1))) + β * (1 / (t + 1)) + γ) * (t * (t + 1)) =
        α + β * t + γ * (t * (t + 1)) := by field_simp
    rw [e]
    nlinarith
  have h3 : ∑ t ∈ Ico Q₁ Q, (α * (1 / (t * (t + 1))) + β * (1 / (t + 1)) + γ) ≤
      α / Q₁ + β * (1 + Real.log Q) + γ * Q := by
    rw [sum_add_distrib, sum_add_distrib, ← mul_sum, ← mul_sum, sum_const, Nat.card_Ico,
      nsmul_eq_mul]
    have e1 := mul_le_mul_of_nonneg_left (sum_Ico_inv_mul_succ_le hQ₁ Q) hα
    have e2 := mul_le_mul_of_nonneg_left (sum_Ico_inv_succ_le Q₁ Q) hβ
    have e3 : ((Q - Q₁ : ℕ) : ℝ) * γ ≤ γ * Q := by
      rw [Nat.cast_sub h, mul_comm]
      exact mul_le_mul_of_nonneg_left (by linarith) hγ
    rw [mul_one_div] at e1
    linarith
  calc _ ≤ (α / Q₁ + β + γ * Q) + (α / Q₁ + β * (1 + Real.log Q) + γ * Q) :=
        add_le_add h1 (h2.trans h3)
    _ = _ := by ring

/-! ### The maximum over `y ≤ x` -/

/-- `max_{0 ≤ y ≤ x} |ψ'(y, χ)|` (a supremum; bounded by `(log 4 + 5) x`). -/
noncomputable def supPsi (x : ℝ) {d : ℕ} (χ : DirichletCharacter ℂ d) : ℝ :=
  ⨆ y : Set.Icc (0:ℝ) x, ‖psiChar' χ y‖

lemma supPsi_bdd (x : ℝ) {d : ℕ} (χ : DirichletCharacter ℂ d) :
    BddAbove (Set.range fun y : Set.Icc (0:ℝ) x ↦ ‖psiChar' χ y‖) := by
  refine ⟨(Real.log 4 + 5) * x, ?_⟩
  rintro _ ⟨⟨y, hy⟩, rfl⟩
  exact (norm_psiChar'_le_trivial χ hy.1).trans
    (mul_le_mul_of_nonneg_left hy.2 (by positivity))

lemma le_supPsi {x y : ℝ} (hy0 : 0 ≤ y) (hyx : y ≤ x) {d : ℕ} (χ : DirichletCharacter ℂ d) :
    ‖psiChar' χ y‖ ≤ supPsi x χ :=
  le_ciSup (supPsi_bdd x χ) ⟨y, hy0, hyx⟩

lemma supPsi_nonneg {x : ℝ} (hx : 0 ≤ x) {d : ℕ} (χ : DirichletCharacter ℂ d) :
    0 ≤ supPsi x χ :=
  (norm_nonneg _).trans (le_supPsi le_rfl hx χ)

lemma supPsi_le {x B : ℝ} (hx : 0 ≤ x) {d : ℕ} (χ : DirichletCharacter ℂ d)
    (h : ∀ y, 0 ≤ y → y ≤ x → ‖psiChar' χ y‖ ≤ B) : supPsi x χ ≤ B := by
  haveI : Nonempty (Set.Icc (0:ℝ) x) := ⟨⟨0, le_rfl, hx⟩⟩
  exact ciSup_le fun y ↦ h y y.2.1 y.2.2

lemma exists_lt_supPsi {x ε : ℝ} (hx : 0 ≤ x) (hε : 0 < ε) {d : ℕ} (χ : DirichletCharacter ℂ d) :
    ∃ y, 0 ≤ y ∧ y ≤ x ∧ supPsi x χ - ε < ‖psiChar' χ y‖ := by
  haveI : Nonempty (Set.Icc (0:ℝ) x) := ⟨⟨0, le_rfl, hx⟩⟩
  obtain ⟨⟨y, hy⟩, h⟩ := exists_lt_of_lt_ciSup (show supPsi x χ - ε < supPsi x χ by linarith)
  exact ⟨y, hy.1, hy.2, h⟩

open scoped Classical in
/-- (B) with the maximum over `y ≤ x`. -/
theorem sum_supPsi_le : ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 3 ≤ x → ∀ Q : ℝ, 1 ≤ Q → Q ≤ √x →
    ∑ q ∈ Icc 1 ⌊Q⌋₊, ((q : ℝ) / q.totient) *
        ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ ↦ χ.IsPrimitive),
          supPsi x χ ≤
      C * (x + x ^ ((5:ℝ) / 6) * Q + √x * Q ^ 2) * Real.log x ^ 4 := by
  obtain ⟨C, hC, hB⟩ := sum_psiChar'_le
  refine ⟨C, hC, fun x hx Q hQ hQx ↦ ?_⟩
  have hx0 : 0 ≤ x := by linarith
  have hQ2 : 0 < Q ^ 2 := by positivity
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  choose y hy0 hyx hlt using fun q (χ : DirichletCharacter ℂ q) ↦
    exists_lt_supPsi hx0 (div_pos hε hQ2) χ
  have h := hB x hx Q hQ hQx y fun q χ ↦ ⟨hy0 q χ, hyx q χ⟩
  have hcount := sum_weight_card_primitive_le hQ
  calc _ ≤ ∑ q ∈ Icc 1 ⌊Q⌋₊, ((q : ℝ) / q.totient) *
        ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ ↦ χ.IsPrimitive),
          (‖psiChar' χ (y q χ)‖ + ε / Q ^ 2) := by
        refine sum_le_sum fun q _ ↦ mul_le_mul_of_nonneg_left
          (sum_le_sum fun χ _ ↦ ?_) (by positivity)
        linarith [hlt q χ]
    _ = ∑ q ∈ Icc 1 ⌊Q⌋₊, ((q : ℝ) / q.totient) *
          ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ ↦ χ.IsPrimitive),
            ‖psiChar' χ (y q χ)‖ +
        ε / Q ^ 2 * ∑ q ∈ Icc 1 ⌊Q⌋₊, ((q : ℝ) / q.totient) *
          (((univ : Finset (DirichletCharacter ℂ q)).filter (fun χ ↦ χ.IsPrimitive)).card : ℝ) := by
        rw [mul_sum, ← sum_add_distrib]
        refine sum_congr rfl fun q _ ↦ ?_
        rw [sum_add_distrib, sum_const, nsmul_eq_mul]; ring
    _ ≤ C * (x + x ^ ((5:ℝ) / 6) * Q + √x * Q ^ 2) * Real.log x ^ 4 + ε / Q ^ 2 * Q ^ 2 := by
        gcongr
    _ = _ := by field_simp

/-! ### Reduction to primitive characters (Davenport, pp. 162–163) -/

/-- `|E(y; q, a)| ≤ 1 + 2 log q log x + φ(q)⁻¹ ∑_χ max_{y ≤ x} |ψ'(y, χ₁)|`, where `χ₁` is the
primitive character inducing `χ` (the `1` covers `y < 1`). -/
lemma abs_psiAP_sub_le {q : ℕ} [NeZero q] {x y : ℝ} (hx : 1 ≤ x) (hy0 : 0 ≤ y) (hyx : y ≤ x)
    {a : ℤ} (ha : IsCoprime a q) :
    |psiAP y q a - y / q.totient| ≤ 1 + 2 * Real.log q * Real.log x +
      1 / q.totient * ∑ χ : DirichletCharacter ℂ q, supPsi x χ.primitiveCharacter := by
  have hφ : (0:ℝ) < q.totient := by
    exact_mod_cast Nat.totient_pos.2 (Nat.pos_of_ne_zero (NeZero.ne q))
  have hlq : 0 ≤ Real.log q := Real.log_natCast_nonneg q
  have hlx : 0 ≤ Real.log x := Real.log_nonneg hx
  have hS : 0 ≤ ∑ χ : DirichletCharacter ℂ q, supPsi x χ.primitiveCharacter :=
    sum_nonneg fun χ _ ↦ supPsi_nonneg (by linarith) _
  have hrest : 0 ≤ 2 * Real.log q * Real.log x +
      1 / q.totient * ∑ χ : DirichletCharacter ℂ q, supPsi x χ.primitiveCharacter := by
    positivity
  rcases lt_or_ge y 1 with hy1 | hy1
  · have hpsi : psiAP y q a = 0 := by
      have : ⌊y⌋₊ = 0 := Nat.floor_eq_zero.2 hy1
      simp [psiAP, this]
    rw [hpsi, zero_sub, abs_neg, abs_of_nonneg (by positivity)]
    have : y / q.totient ≤ 1 := by
      rw [div_le_one hφ]
      have : (1:ℝ) ≤ q.totient := by exact_mod_cast Nat.totient_pos.2 (Nat.pos_of_ne_zero (NeZero.ne q))
      linarith
    linarith
  have hE := psiAP_sub_eq y ha
  have h1 : (q.totient : ℝ) * |psiAP y q a - y / q.totient| ≤
      ∑ χ : DirichletCharacter ℂ q, ‖psiChar' χ y‖ := by
    have := congrArg norm hE
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_natCast] at this
    rw [this]
    refine (norm_sum_le _ _).trans (sum_le_sum fun χ _ ↦ ?_)
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (DirichletCharacter.norm_le_one _ _)
  have h2 : ∀ χ : DirichletCharacter ℂ q, ‖psiChar' χ y‖ ≤
      supPsi x χ.primitiveCharacter + 2 * Real.log q * Real.log x := by
    intro χ
    have hd := norm_psiChar'_sub_le χ hy1
    have h3 : ‖psiChar' χ y‖ ≤ ‖psiChar' χ.primitiveCharacter y‖ + 2 * Real.log q * Real.log y := by
      have := norm_sub_norm_le (psiChar' χ y) (psiChar' χ.primitiveCharacter y)
      linarith
    have h4 : Real.log y ≤ Real.log x := Real.log_le_log (by linarith) hyx
    have h5 := le_supPsi hy0 hyx χ.primitiveCharacter
    nlinarith
  have h6 : ∑ χ : DirichletCharacter ℂ q, ‖psiChar' χ y‖ ≤
      ∑ χ : DirichletCharacter ℂ q, supPsi x χ.primitiveCharacter +
        q.totient * (2 * Real.log q * Real.log x) := by
    refine (sum_le_sum fun χ _ ↦ h2 χ).trans ?_
    rw [sum_add_distrib, sum_const, nsmul_eq_mul, card_univ, card_dirichletCharacter]
  have h7 : |psiAP y q a - y / q.totient| ≤
      1 / q.totient * ∑ χ : DirichletCharacter ℂ q, supPsi x χ.primitiveCharacter +
        2 * Real.log q * Real.log x := by
    refine le_of_mul_le_mul_left ?_ hφ
    calc (q.totient : ℝ) * |psiAP y q a - y / q.totient| ≤ _ := h1.trans h6
      _ = _ := by field_simp
  linarith

open scoped Classical in
/-- Collecting characters: `∑_{q ≤ Q} |E(y_q; q, a_q)| ≤ Q(1 + 2 (log x)²)
  + C (1 + log Q) ∑_{d ≤ Q} φ(d)⁻¹ ∑*_ψ max_{y ≤ x} |ψ'(y, ψ)|`. -/
lemma sum_abs_psiAP_sub_le : ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 1 ≤ x → ∀ Q : ℝ, 1 ≤ Q → Q ≤ x →
    ∀ (y : ℕ → ℝ) (a : ℕ → ℤ), (∀ q, 0 ≤ y q ∧ y q ≤ x) → (∀ q, IsCoprime (a q) q) →
    ∑ q ∈ Icc 1 ⌊Q⌋₊, |psiAP (y q) q (a q) - y q / q.totient| ≤
      Q * (1 + 2 * Real.log x ^ 2) + C * (1 + Real.log Q) *
        ∑ d ∈ Icc 1 ⌊Q⌋₊, 1 / (d.totient : ℝ) *
          ∑ ψ ∈ (univ : Finset (DirichletCharacter ℂ d)).filter (fun ψ ↦ ψ.IsPrimitive),
            supPsi x ψ := by
  obtain ⟨C₀, hC₀, hT⟩ := sum_inv_totient_le
  refine ⟨C₀, hC₀, fun x hx Q hQ hQx y a hy ha ↦ ?_⟩
  have hx0 : 0 ≤ x := by linarith
  have hlx : 0 ≤ Real.log x := Real.log_nonneg hx
  set F : (d : ℕ) → DirichletCharacter ℂ d → ℝ := fun d ψ ↦ supPsi x ψ with hF
  have step1 : ∀ q ∈ Icc 1 ⌊Q⌋₊, |psiAP (y q) q (a q) - y q / q.totient| ≤
      (1 + 2 * Real.log x ^ 2) + 1 / (q.totient : ℝ) *
        ∑ χ : DirichletCharacter ℂ q, F χ.conductor χ.primitiveCharacter := by
    intro q hq
    have : NeZero q := ⟨by have := (mem_Icc.1 hq).1; omega⟩
    have hqx : (q : ℝ) ≤ x :=
      (Nat.cast_le.2 (mem_Icc.1 hq).2).trans ((Nat.floor_le (by linarith)).trans hQx)
    have hlq : Real.log q ≤ Real.log x :=
      Real.log_le_log (by exact_mod_cast (mem_Icc.1 hq).1) hqx
    have h := abs_psiAP_sub_le hx (hy q).1 (hy q).2 (ha q)
    have : 2 * Real.log q * Real.log x ≤ 2 * Real.log x ^ 2 := by
      have := Real.log_natCast_nonneg q
      nlinarith
    simp only [hF]
    linarith
  have step2 := sum_sum_primitiveCharacter_le ⌊Q⌋₊ (fun q ↦ 1 / (q.totient : ℝ))
    (fun n ↦ by positivity) F (fun d ψ ↦ supPsi_nonneg hx0 ψ)
  have hlogQ : 0 ≤ Real.log Q := Real.log_nonneg hQ
  have step3 : ∀ d ∈ Icc 1 ⌊Q⌋₊, ∑ k ∈ Icc 1 (⌊Q⌋₊ / d), 1 / ((k * d).totient : ℝ) ≤
      C₀ * (1 + Real.log Q) * (1 / (d.totient : ℝ)) := by
    intro d hd
    have hd1 := (mem_Icc.1 hd).1
    have hK : 1 ≤ ⌊Q⌋₊ / d := (Nat.one_le_div_iff (by omega)).2 (mem_Icc.1 hd).2
    refine (sum_inv_totient_mul_le (by omega) _).trans ?_
    have h1 := hT _ hK
    have h2 : Real.log (⌊Q⌋₊ / d : ℕ) ≤ Real.log Q := by
      refine Real.log_le_log (by exact_mod_cast (show 0 < ⌊Q⌋₊ / d by omega)) ?_
      calc ((⌊Q⌋₊ / d : ℕ) : ℝ) ≤ ⌊Q⌋₊ := by exact_mod_cast Nat.div_le_self _ _
        _ ≤ Q := Nat.floor_le (by linarith)
    have h3 : (0:ℝ) ≤ 1 / d.totient := by positivity
    calc 1 / (d.totient : ℝ) * ∑ k ∈ Icc 1 (⌊Q⌋₊ / d), 1 / (k.totient : ℝ)
        ≤ 1 / (d.totient : ℝ) * (C₀ * (1 + Real.log (⌊Q⌋₊ / d : ℕ))) := by gcongr
      _ ≤ 1 / (d.totient : ℝ) * (C₀ * (1 + Real.log Q)) := by gcongr
      _ = _ := by ring
  calc ∑ q ∈ Icc 1 ⌊Q⌋₊, |psiAP (y q) q (a q) - y q / q.totient|
      ≤ ∑ q ∈ Icc 1 ⌊Q⌋₊, ((1 + 2 * Real.log x ^ 2) + 1 / (q.totient : ℝ) *
          ∑ χ : DirichletCharacter ℂ q, F χ.conductor χ.primitiveCharacter) := sum_le_sum step1
    _ = ⌊Q⌋₊ * (1 + 2 * Real.log x ^ 2) + ∑ q ∈ Icc 1 ⌊Q⌋₊, 1 / (q.totient : ℝ) *
          ∑ χ : DirichletCharacter ℂ q, F χ.conductor χ.primitiveCharacter := by
        rw [sum_add_distrib, sum_const, Nat.card_Icc, nsmul_eq_mul]; simp
    _ ≤ Q * (1 + 2 * Real.log x ^ 2) + ∑ d ∈ Icc 1 ⌊Q⌋₊,
          ∑ ψ ∈ (univ : Finset (DirichletCharacter ℂ d)).filter (fun ψ ↦ ψ.IsPrimitive),
            F d ψ * ∑ k ∈ Icc 1 (⌊Q⌋₊ / d), 1 / ((k * d).totient : ℝ) := by
        gcongr
        exact Nat.floor_le (by linarith)
    _ ≤ Q * (1 + 2 * Real.log x ^ 2) + ∑ d ∈ Icc 1 ⌊Q⌋₊,
          ∑ ψ ∈ (univ : Finset (DirichletCharacter ℂ d)).filter (fun ψ ↦ ψ.IsPrimitive),
            F d ψ * (C₀ * (1 + Real.log Q) * (1 / (d.totient : ℝ))) := by
        gcongr with d hd ψ _
        · exact supPsi_nonneg hx0 ψ
        · exact step3 d hd
    _ = _ := by
        congr 1
        rw [mul_sum]
        refine sum_congr rfl fun d _ ↦ ?_
        rw [mul_sum, mul_sum]
        refine sum_congr rfl fun ψ _ ↦ ?_
        simp only [hF]; ring

/-! ### Estimate (C): small and large moduli (Davenport, pp. 163–164) -/

/-- `(log x)^k ≤ K x^r` for `x ≥ 1`. -/
lemma log_pow_le_mul_rpow (k : ℕ) {r : ℝ} (hr : 0 < r) :
    ∃ K > 0, ∀ x : ℝ, 1 ≤ x → Real.log x ^ k ≤ K * x ^ r := by
  refine ⟨k.factorial / r ^ k, by positivity, fun x hx ↦ ?_⟩
  have hL := Real.log_nonneg hx
  have h := Real.pow_div_factorial_le_exp (x := r * Real.log x) (by positivity) k
  rw [show Real.exp (r * Real.log x) = x ^ r by
    rw [Real.rpow_def_of_pos (by linarith)]; ring_nf] at h
  rw [div_le_iff₀ (by positivity), mul_pow] at h
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  linarith

/-- The small moduli: for primitive `ψ` modulo `d ≤ (½ log x)^N`,
`max_{y ≤ x} |ψ'(y, ψ)| ≤ (log 4 + 5) x^{1/2} + C x exp(-c (½ log x)^{1/2})`
(trivially for `y ≤ x^{1/2}`, by the Siegel–Walfisz estimate for `y ≥ x^{1/2}`). -/
lemma SiegelWalfiszHypothesis.supPsi_le (hSW : SiegelWalfiszHypothesis) (N : ℕ) (hN : 1 ≤ N) :
    ∃ c > 0, ∃ C > 0, ∀ x : ℝ, 1 ≤ x → 4 ≤ Real.log x → ∀ d : ℕ, 1 ≤ d →
      (d : ℝ) ≤ (Real.log x / 2) ^ N → ∀ ψ : DirichletCharacter ℂ d, ψ.IsPrimitive →
        supPsi x ψ ≤ (Real.log 4 + 5) * √x + C * x * Real.exp (-c * √(Real.log x / 2)) := by
  obtain ⟨c, hc, C, hC, h⟩ := hSW.primitive_bound (B := N) (by exact_mod_cast hN)
  refine ⟨c, hc, C, hC, fun x hx1 hL d hd hdx ψ hψ ↦ ?_⟩
  have hx0 : 0 ≤ x := by linarith
  have hsx : √x * √x = x := Real.mul_self_sqrt hx0
  have hlsx : Real.log √x = Real.log x / 2 := by
    rw [Real.log_sqrt hx0]
  have hsx2 : 2 ≤ √x := by
    have : Real.log 2 < Real.log √x := by
      rw [hlsx]; have := Real.log_two_lt_d9; linarith
    exact (Real.log_lt_log_iff (by norm_num) (by positivity)).1 this |>.le
  refine NTKB.Davenport.supPsi_le hx0 ψ fun y hy0 hyx ↦ ?_
  have hR : 0 ≤ C * x * Real.exp (-c * √(Real.log x / 2)) := by positivity
  rcases le_or_gt y √x with hy | hy
  · have := norm_psiChar'_le_trivial ψ hy0
    have : (Real.log 4 + 5) * y ≤ (Real.log 4 + 5) * √x :=
      mul_le_mul_of_nonneg_left hy (by positivity)
    linarith
  · have hy2 : 2 ≤ y := by linarith
    have hly : Real.log x / 2 ≤ Real.log y := by
      rw [← hlsx]; exact Real.log_le_log (by positivity) hy.le
    have hdy : (d : ℝ) ≤ Real.log y ^ (N : ℝ) := by
      rw [Real.rpow_natCast]
      exact hdx.trans (pow_le_pow_left₀ (by linarith) hly N)
    have h1 := h y hy2 d hd hdy ψ hψ
    have e : Real.exp (-c * √(Real.log y)) ≤ Real.exp (-c * √(Real.log x / 2)) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonpos_left (Real.sqrt_le_sqrt hly) (by linarith))
    have h2 : C * y * Real.exp (-c * √(Real.log y)) ≤
        C * x * Real.exp (-c * √(Real.log x / 2)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hyx hC.le) e (Real.exp_pos _).le (by positivity)
    have : 0 ≤ (Real.log 4 + 5) * √x := by positivity
    linarith

open scoped Classical in
/-- **Davenport, Ch. 28, p. 164, estimate (C)** (conditional on the Siegel–Walfisz input): for
`x^{1/2} (log x)^{-N} ≤ Q ≤ x^{1/2}`,
`∑_{q ≤ Q} φ(q)⁻¹ ∑*_χ max_{y ≤ x} |ψ'(y, χ)| ≪ x^{1/2} Q (log x)⁴`. -/
@[kb "davenport1980" "Ch 28, p. 164, (C)"]
theorem sum_inv_totient_supPsi_le (hSW : SiegelWalfiszHypothesis) (N : ℕ) (hN : 1 ≤ N) :
    ∃ K > 0, ∀ x : ℝ, 3 ≤ x → 4 ≤ Real.log x → ∀ Q : ℝ, 1 ≤ Q → Q ≤ √x →
      √x ≤ Q * Real.log x ^ N →
      ∑ d ∈ Icc 1 ⌊Q⌋₊, 1 / (d.totient : ℝ) *
          ∑ ψ ∈ (univ : Finset (DirichletCharacter ℂ d)).filter (fun ψ ↦ ψ.IsPrimitive),
            supPsi x ψ ≤ K * √x * Q * Real.log x ^ 4 := by
  obtain ⟨c, hc, Cs, hCs, hsm⟩ := hSW.supPsi_le N hN
  obtain ⟨CB, hCB, hB⟩ := sum_supPsi_le
  obtain ⟨K₂, hK₂, hK₂b⟩ := pow_le_mul_exp_sqrt (c := c / √2) (by positivity) (2 * N)
  obtain ⟨K₃, hK₃, hK₃b⟩ := log_pow_le_mul_rpow (2 * N) (r := 1 / 2) (by norm_num)
  obtain ⟨K₄, hK₄, hK₄b⟩ := log_pow_le_mul_rpow (N + 1) (r := 1 / 6) (by norm_num)
  set K := (Real.log 4 + 5) * K₃ + Cs * K₂ + 2 ^ (N + 2) * CB + 3 * CB * K₄ + 2 * CB with hK
  refine ⟨K, by positivity, ?_⟩
  intro x hx3 hL Q hQ hQx hQlow
  set L := Real.log x with hLdef
  have hL1 : 1 ≤ L := by linarith
  have hx0 : 0 ≤ x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hsx : √x * √x = x := Real.mul_self_sqrt hx0
  have hsx1 : 1 ≤ √x := by rw [show (1:ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt hx1
  have hLN : 0 < L ^ N := by positivity
  have hL4 : 1 ≤ L ^ 4 := one_le_pow₀ hL1
  -- the key comparisons
  have k1 : x ≤ √x * Q * L ^ N := by
    calc x = √x * √x := hsx.symm
      _ ≤ √x * (Q * L ^ N) := by gcongr
      _ = _ := by ring
  have k1' : x / L ^ N ≤ √x * Q := by rw [div_le_iff₀ hLN]; exact k1
  have k2 : L ^ N * √x ≤ K₃ * √x * Q := by
    have h := hK₃b x hx1
    rw [← Real.sqrt_eq_rpow] at h
    refine le_of_mul_le_mul_right ?_ hLN
    calc L ^ N * √x * L ^ N = L ^ (2 * N) * √x := by ring
      _ ≤ K₃ * √x * √x := by gcongr
      _ ≤ K₃ * √x * (Q * L ^ N) := by gcongr
      _ = _ := by ring
  have k3 : L ^ N * x * Real.exp (-c * √(L / 2)) ≤ K₂ * √x * Q := by
    have h := hK₂b L (by linarith)
    have he : c / √2 * √L = c * √(L / 2) := by
      rw [Real.sqrt_div' _ (by norm_num : (0:ℝ) ≤ 2)]; ring
    rw [he] at h
    have h2 : L ^ (2 * N) * Real.exp (-c * √(L / 2)) ≤ K₂ := by
      have := mul_le_mul_of_nonneg_right h (Real.exp_pos (-c * √(L / 2))).le
      rwa [mul_assoc, ← Real.exp_add, show c * √(L / 2) + -c * √(L / 2) = 0 by ring,
        Real.exp_zero, mul_one] at this
    calc L ^ N * x * Real.exp (-c * √(L / 2))
        = L ^ (2 * N) * Real.exp (-c * √(L / 2)) * (x / L ^ N) := by
          field_simp; ring
      _ ≤ K₂ * (√x * Q) := by gcongr
      _ = _ := by ring
  have k4 : x ^ ((5:ℝ) / 6) * L ≤ K₄ * √x * Q := by
    have h := hK₄b x hx1
    refine le_of_mul_le_mul_right ?_ hLN
    calc x ^ ((5:ℝ) / 6) * L * L ^ N = x ^ ((5:ℝ) / 6) * L ^ (N + 1) := by ring
      _ ≤ x ^ ((5:ℝ) / 6) * (K₄ * x ^ ((1:ℝ) / 6)) := by gcongr
      _ = K₄ * x := by
          rw [mul_left_comm, ← Real.rpow_add (by linarith)]; norm_num
      _ ≤ K₄ * (√x * Q * L ^ N) := by gcongr
      _ = _ := by ring
  -- the cut `Q₁ = ⌊(L/2)^N⌋`
  have hL2 : 1 ≤ (L / 2) ^ N := one_le_pow₀ (by linarith)
  set Q₁ := ⌊(L / 2) ^ N⌋₊ with hQ₁
  have hQ₁1 : 1 ≤ Q₁ := Nat.le_floor (by exact_mod_cast hL2)
  have hQ₁le : (Q₁ : ℝ) ≤ (L / 2) ^ N := Nat.floor_le (by positivity)
  have hQ₁L : (Q₁ : ℝ) ≤ L ^ N :=
    hQ₁le.trans (pow_le_pow_left₀ (by linarith) (by linarith) N)
  have hQ₁half : (L / 2) ^ N / 2 ≤ Q₁ := half_le_floor hL2
  set m := min Q₁ ⌊Q⌋₊ with hm
  have hmQ : m ≤ ⌊Q⌋₊ := min_le_right _ _
  set G : ℕ → ℝ := fun d ↦ 1 / (d.totient : ℝ) *
    ∑ ψ ∈ (univ : Finset (DirichletCharacter ℂ d)).filter (fun ψ ↦ ψ.IsPrimitive), supPsi x ψ
    with hG
  have hG0 : ∀ d, 0 ≤ G d := fun d ↦
    mul_nonneg (by positivity) (sum_nonneg fun ψ _ ↦ supPsi_nonneg hx0 ψ)
  have hsplit : ∑ d ∈ Icc 1 ⌊Q⌋₊, G d = ∑ d ∈ Icc 1 m, G d + ∑ d ∈ Ioc m ⌊Q⌋₊, G d := by
    have e : ∀ n : ℕ, Icc 1 n = Ioc 0 n := fun n ↦ Finset.Icc_add_one_left_eq_Ioc 0 n
    rw [e, e, sum_Ioc_consecutive _ (Nat.zero_le m) hmQ]
  -- small moduli
  set Bs := (Real.log 4 + 5) * √x + Cs * x * Real.exp (-c * √(L / 2)) with hBs
  have hsmall : ∑ d ∈ Icc 1 m, G d ≤ ((Real.log 4 + 5) * K₃ + Cs * K₂) * √x * Q := by
    have h1 : ∀ d ∈ Icc 1 m, G d ≤ Bs := by
      intro d hd
      have hd1 := (mem_Icc.1 hd).1
      have : NeZero d := ⟨by omega⟩
      have hdm : (d : ℝ) ≤ (L / 2) ^ N :=
        (Nat.cast_le.2 ((mem_Icc.1 hd).2.trans (min_le_left _ _))).trans hQ₁le
      have hφ : (0:ℝ) < d.totient := by exact_mod_cast Nat.totient_pos.2 (by omega)
      have hBs0 : 0 ≤ Bs := by positivity
      calc G d ≤ 1 / (d.totient : ℝ) *
            ∑ ψ ∈ (univ : Finset (DirichletCharacter ℂ d)).filter (fun ψ ↦ ψ.IsPrimitive), Bs :=
            mul_le_mul_of_nonneg_left (sum_le_sum fun ψ hψ ↦
              hsm x hx1 hL d hd1 hdm ψ (mem_filter.1 hψ).2) (by positivity)
        _ ≤ 1 / (d.totient : ℝ) * (d.totient * Bs) := by
            rw [sum_const, nsmul_eq_mul]
            refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ?_ hBs0) (by positivity)
            rw [← card_dirichletCharacter d]
            exact_mod_cast card_filter_le _ _
        _ = Bs := by field_simp
    calc ∑ d ∈ Icc 1 m, G d ≤ ∑ d ∈ Icc 1 m, Bs := sum_le_sum h1
      _ = m * Bs := by rw [sum_const, Nat.card_Icc, nsmul_eq_mul]; simp
      _ ≤ L ^ N * Bs := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact (Nat.cast_le.2 (min_le_left _ _)).trans hQ₁L
      _ = (Real.log 4 + 5) * (L ^ N * √x) + Cs * (L ^ N * x * Real.exp (-c * √(L / 2))) := by
          simp only [hBs]; ring
      _ ≤ (Real.log 4 + 5) * (K₃ * √x * Q) + Cs * (K₂ * √x * Q) := by gcongr
      _ = _ := by ring
  -- large moduli
  have hlarge : ∑ d ∈ Ioc m ⌊Q⌋₊, G d ≤
      (2 ^ (N + 2) * CB + 3 * CB * K₄ + 2 * CB) * √x * Q * L ^ 4 := by
    have hR0 : 0 ≤ (2 ^ (N + 2) * CB + 3 * CB * K₄ + 2 * CB) * √x * Q * L ^ 4 := by positivity
    rcases le_or_gt ⌊Q⌋₊ m with hle | hlt
    · rw [Ioc_eq_empty (by omega), sum_empty]; exact hR0
    have hmQ₁ : m = Q₁ := by
      simp only [hm] at hlt ⊢; omega
    rw [hmQ₁]
    set a : ℕ → ℝ := fun d ↦ ((d : ℝ) / d.totient) *
      ∑ ψ ∈ (univ : Finset (DirichletCharacter ℂ d)).filter (fun ψ ↦ ψ.IsPrimitive), supPsi x ψ
      with ha
    have ha0 : ∀ d, 0 ≤ a d := fun d ↦
      mul_nonneg (by positivity) (sum_nonneg fun ψ _ ↦ supPsi_nonneg hx0 ψ)
    have hGa : ∀ d ∈ Ioc Q₁ ⌊Q⌋₊, G d = a d / d := by
      intro d hd
      have hd0 : (d : ℝ) ≠ 0 := by
        have := (mem_Ioc.1 hd).1; exact_mod_cast (show d ≠ 0 by omega)
      simp only [hG, ha]; field_simp
    rw [sum_congr rfl hGa]
    have hQ₁Q : Q₁ ≤ ⌊Q⌋₊ := by omega
    have hfloorQ : (⌊Q⌋₊ : ℝ) ≤ Q := Nat.floor_le (by linarith)
    have hab := sum_div_le_of_sum_le a ha0 hQ₁1 hQ₁Q (α := CB * x * L ^ 4)
      (β := CB * x ^ ((5:ℝ) / 6) * L ^ 4) (γ := CB * √x * L ^ 4) (by positivity) (by positivity)
      (by positivity) (fun t ht ↦ by
        have ht1 : (1:ℝ) ≤ t := by exact_mod_cast hQ₁1.trans (mem_Icc.1 ht).1
        have htx : (t:ℝ) ≤ √x :=
          ((Nat.cast_le.2 (mem_Icc.1 ht).2).trans hfloorQ).trans hQx
        have h := hB x hx3 (t : ℝ) ht1 htx
        rw [Nat.floor_natCast] at h
        calc ∑ q ∈ Icc 1 t, a q ≤ _ := h
          _ = _ := by ring)
    refine hab.trans ?_
    have hQ₁r : (0:ℝ) < Q₁ := by exact_mod_cast hQ₁1
    have e1 : 2 * (CB * x * L ^ 4) / Q₁ ≤ 2 ^ (N + 2) * CB * √x * Q * L ^ 4 := by
      have hinv : 1 / (Q₁ : ℝ) ≤ 2 ^ (N + 1) / L ^ N := by
        rw [div_le_div_iff₀ hQ₁r hLN, one_mul]
        have : (L / 2) ^ N = L ^ N / 2 ^ N := by rw [div_pow]
        rw [this] at hQ₁half
        have h2N : (0:ℝ) < 2 ^ N := by positivity
        rw [div_div, div_le_iff₀ (by positivity)] at hQ₁half
        calc L ^ N ≤ Q₁ * (2 ^ N * 2) := hQ₁half
          _ = 2 ^ (N + 1) * Q₁ := by ring
      calc 2 * (CB * x * L ^ 4) / Q₁ = 2 * CB * L ^ 4 * x * (1 / (Q₁ : ℝ)) := by ring
        _ ≤ 2 * CB * L ^ 4 * x * (2 ^ (N + 1) / L ^ N) := by gcongr
        _ = 2 ^ (N + 2) * CB * L ^ 4 * (x / L ^ N) := by ring
        _ ≤ 2 ^ (N + 2) * CB * L ^ 4 * (√x * Q) := by gcongr
        _ = _ := by ring
    have e2 : CB * x ^ ((5:ℝ) / 6) * L ^ 4 * (2 + Real.log ⌊Q⌋₊) ≤ 3 * CB * K₄ * √x * Q * L ^ 4 := by
      have hlQ : Real.log ⌊Q⌋₊ ≤ L := by
        refine Real.log_le_log (by exact_mod_cast (show 0 < ⌊Q⌋₊ by omega)) ?_
        calc (⌊Q⌋₊ : ℝ) ≤ Q := hfloorQ
          _ ≤ √x := hQx
          _ ≤ √x * √x := le_mul_of_one_le_right (by positivity) hsx1
          _ = x := hsx
      have h2 : 2 + Real.log ⌊Q⌋₊ ≤ 3 * L := by linarith
      calc CB * x ^ ((5:ℝ) / 6) * L ^ 4 * (2 + Real.log ⌊Q⌋₊)
          ≤ CB * x ^ ((5:ℝ) / 6) * L ^ 4 * (3 * L) := by gcongr
        _ = 3 * CB * L ^ 4 * (x ^ ((5:ℝ) / 6) * L) := by ring
        _ ≤ 3 * CB * L ^ 4 * (K₄ * √x * Q) := by gcongr
        _ = _ := by ring
    have e3 : 2 * (CB * √x * L ^ 4) * ⌊Q⌋₊ ≤ 2 * CB * √x * Q * L ^ 4 := by
      calc 2 * (CB * √x * L ^ 4) * ⌊Q⌋₊ ≤ 2 * (CB * √x * L ^ 4) * Q := by gcongr
        _ = _ := by ring
    linarith
  rw [hsplit]
  have hfin : ((Real.log 4 + 5) * K₃ + Cs * K₂) * √x * Q ≤
      ((Real.log 4 + 5) * K₃ + Cs * K₂) * √x * Q * L ^ 4 :=
    le_mul_of_one_le_right (by positivity) hL4
  calc _ ≤ ((Real.log 4 + 5) * K₃ + Cs * K₂) * √x * Q * L ^ 4 +
        (2 ^ (N + 2) * CB + 3 * CB * K₄ + 2 * CB) * √x * Q * L ^ 4 := by linarith
    _ = _ := by simp only [hK]; ring

open scoped ArithmeticFunction.vonMangoldt in
/-- `ψ(y; q, a) ≤ (log 4 + 4) y`. -/
lemma psiAP_le {y : ℝ} (hy : 0 ≤ y) (q : ℕ) (a : ℤ) : psiAP y q a ≤ (Real.log 4 + 4) * y := by
  have h1 : psiAP y q a ≤ ∑ n ∈ Icc 1 ⌊y⌋₊, Λ n :=
    sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
      fun _ _ _ ↦ ArithmeticFunction.vonMangoldt_nonneg
  have h2 : ∑ n ∈ Icc 1 ⌊y⌋₊, Λ n ≤ ∑ n ∈ Ioc 0 ⌊y⌋₊, Λ n :=
    sum_le_sum_of_subset_of_nonneg (fun n hn ↦ by simp only [mem_Icc, mem_Ioc] at hn ⊢; omega)
      fun _ _ _ ↦ ArithmeticFunction.vonMangoldt_nonneg
  exact h1.trans (h2.trans (Chebyshev.psi_le_const_mul_self hy))

lemma psiAP_nonneg (y : ℝ) (q : ℕ) (a : ℤ) : 0 ≤ psiAP y q a :=
  sum_nonneg fun _ _ ↦ ArithmeticFunction.vonMangoldt_nonneg

open scoped Classical in
/-- **Davenport, Ch. 28, p. 161, Bombieri's theorem** (conditional on the Siegel–Walfisz input
`SiegelWalfiszHypothesis`, i.e. Davenport §18 and (C) of §22, which belong to the zero theory):
for fixed `A > 0` and `x^{1/2} (log x)^{-A} ≤ Q ≤ x^{1/2}`,
`∑_{q ≤ Q} E*(x, q) ≪ x^{1/2} Q (log x)⁵`, where `E*(x, q) = max_{y ≤ x} max_{(a,q)=1}
|ψ(y; q, a) - y/φ(q)|`. The maxima are arbitrary choices `y(q) ∈ [0, x]` and `a(q)` coprime to
`q`. -/
@[kb "davenport1980" "Ch 28, p. 161"]
theorem bombieri (hSW : SiegelWalfiszHypothesis) {A : ℝ} (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 3 ≤ x → ∀ Q : ℝ, √x * Real.log x ^ (-A) ≤ Q → Q ≤ √x →
      ∀ (y : ℕ → ℝ) (a : ℕ → ℤ), (∀ q, 0 ≤ y q ∧ y q ≤ x) → (∀ q, IsCoprime (a q) q) →
        ∑ q ∈ Icc 1 ⌊Q⌋₊, |psiAP (y q) q (a q) - y q / q.totient| ≤
          C * √x * Q * Real.log x ^ 5 := by
  set N := ⌈A⌉₊ with hNdef
  have hN : 1 ≤ N := Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 hA).ne'
  obtain ⟨K, hK, hC⟩ := sum_inv_totient_supPsi_le hSW N hN
  obtain ⟨CE, hCE, hE⟩ := sum_abs_psiAP_sub_le
  refine ⟨51 + 2 * CE * K, by positivity, ?_⟩
  intro x hx Q hQlow hQx y a hy ha
  set L := Real.log x with hLdef
  have hx0 : 0 ≤ x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hL1 : 1 ≤ L := by
    rw [hLdef, Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9; linarith
  have hsx : √x * √x = x := Real.mul_self_sqrt hx0
  have hsx1 : 1 ≤ √x := by rw [show (1:ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt hx1
  have hL5 : 1 ≤ L ^ 5 := one_le_pow₀ hL1
  have hQ0 : 0 ≤ Q := le_trans (by positivity) hQlow
  have hR0 : 0 ≤ (51 + 2 * CE * K) * √x * Q * L ^ 5 := by positivity
  rcases lt_or_ge Q 1 with hQ1 | hQ1
  · rw [Nat.floor_eq_zero.2 hQ1, Icc_eq_empty (by omega), sum_empty]; exact hR0
  -- `√x ≤ Q (log x)^N`
  have hQlowN : √x ≤ Q * L ^ N := by
    have h1 : L ^ (-(N : ℝ)) ≤ L ^ (-A) :=
      Real.rpow_le_rpow_of_exponent_le hL1 (by linarith [Nat.le_ceil A])
    rw [Real.rpow_neg (by linarith), Real.rpow_natCast] at h1
    have hLN : 0 < L ^ N := by positivity
    have h2 : √x * (L ^ N)⁻¹ ≤ Q := (mul_le_mul_of_nonneg_left h1 (by positivity)).trans hQlow
    rw [← div_eq_mul_inv, div_le_iff₀ hLN] at h2
    exact h2
  rcases le_or_gt 4 L with hL4 | hL4
  · have hQxx : Q ≤ x := hQx.trans (by nlinarith)
    have h1 := hE x hx1 Q hQ1 hQxx y a hy ha
    have h2 := hC x hx hL4 Q hQ1 hQx hQlowN
    have hlQ : Real.log Q ≤ L := Real.log_le_log (by linarith) hQxx
    have hlQ0 : 0 ≤ Real.log Q := Real.log_nonneg hQ1
    have hS0 : 0 ≤ ∑ d ∈ Icc 1 ⌊Q⌋₊, 1 / (d.totient : ℝ) *
        ∑ ψ ∈ (univ : Finset (DirichletCharacter ℂ d)).filter (fun ψ ↦ ψ.IsPrimitive),
          supPsi x ψ :=
      sum_nonneg fun d _ ↦ mul_nonneg (by positivity) (sum_nonneg fun ψ _ ↦ supPsi_nonneg hx0 ψ)
    have e1 : Q * (1 + 2 * L ^ 2) ≤ 3 * √x * Q * L ^ 5 := by
      have : 1 + 2 * L ^ 2 ≤ 3 * L ^ 5 := by
        have : L ^ 2 ≤ L ^ 5 := pow_le_pow_right₀ hL1 (by norm_num)
        linarith
      calc Q * (1 + 2 * L ^ 2) ≤ Q * (3 * L ^ 5) := by gcongr
        _ = 1 * (3 * Q * L ^ 5) := by ring
        _ ≤ √x * (3 * Q * L ^ 5) := by gcongr
        _ = _ := by ring
    have e2 : CE * (1 + Real.log Q) * ∑ d ∈ Icc 1 ⌊Q⌋₊, 1 / (d.totient : ℝ) *
        ∑ ψ ∈ (univ : Finset (DirichletCharacter ℂ d)).filter (fun ψ ↦ ψ.IsPrimitive),
          supPsi x ψ ≤ 2 * CE * K * √x * Q * L ^ 5 := by
      calc _ ≤ CE * (2 * L) * (K * √x * Q * L ^ 4) := by
            gcongr
            linarith
        _ = _ := by ring
    calc _ ≤ _ := h1
      _ ≤ 3 * √x * Q * L ^ 5 + 2 * CE * K * √x * Q * L ^ 5 := by linarith
      _ ≤ _ := by
          have hpos : 0 ≤ √x * Q * L ^ 5 := by positivity
          linarith
  · -- small `x`: the trivial bound
    have hxe : x < Real.exp 4 := by
      rw [← Real.log_lt_iff_lt_exp (by linarith)]; exact hL4
    have hsxe : √x ≤ 7.39 := by
      have he2 : Real.exp 2 < 7.39 := by
        have := Real.exp_one_lt_d9
        rw [show (2:ℝ) = 1 + 1 by norm_num, Real.exp_add]
        nlinarith [Real.exp_pos 1]
      have : √x < Real.exp 2 := by
        have e4 : Real.exp 4 = Real.exp 2 ^ 2 := by
          rw [sq, ← Real.exp_add]; norm_num
        rw [show Real.exp 2 = √(Real.exp 4) by rw [e4, Real.sqrt_sq (Real.exp_pos 2).le]]
        exact Real.sqrt_lt_sqrt hx0 hxe
      linarith
    have hlog4 : Real.log 4 < 1.3863 := by
      rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      have := Real.log_two_lt_d9; push_cast; linarith
    have hterm : ∀ q ∈ Icc 1 ⌊Q⌋₊, |psiAP (y q) q (a q) - y q / q.totient| ≤ 6.4 * x := by
      intro q hq
      have hy0 := (hy q).1
      have h1 := psiAP_le hy0 q (a q)
      have h2 := psiAP_nonneg (y q) q (a q)
      have hφ : (1:ℝ) ≤ q.totient := by
        exact_mod_cast Nat.totient_pos.2 (by have := (mem_Icc.1 hq).1; omega)
      have h3 : y q / q.totient ≤ y q := div_le_self hy0 hφ
      have h4 : 0 ≤ y q / q.totient := by positivity
      rw [abs_le]
      constructor <;> nlinarith [(hy q).2]
    calc _ ≤ ∑ q ∈ Icc 1 ⌊Q⌋₊, 6.4 * x := sum_le_sum hterm
      _ = ⌊Q⌋₊ * (6.4 * x) := by rw [sum_const, Nat.card_Icc, nsmul_eq_mul]; simp
      _ ≤ Q * (6.4 * x) := by gcongr; exact Nat.floor_le hQ0
      _ = 6.4 * Q * √x * √x := by rw [mul_assoc _ √x, hsx]; ring
      _ ≤ 6.4 * Q * √x * 7.39 := by gcongr
      _ ≤ 51 * √x * Q * L ^ 5 := by
          have : 0 ≤ √x * Q := by positivity
          nlinarith
      _ ≤ _ := by
          have : 0 ≤ 2 * CE * K * √x * Q * L ^ 5 := by positivity
          nlinarith

open scoped Classical ArithmeticFunction.vonMangoldt in
/-- **Davenport, Ch. 28, p. 166** (the case `Q² ≥ x` of (B)): (E) with `M = 1`, `a₁ = 1`,
`b_n = Λ(n)`, `N = X` gives, for any choice `u(q, χ) ≤ X`,
`∑_{q ≤ Q} (q/φ(q)) ∑*_χ |ψ(u(q,χ), χ)| ≤ 48 Q² ((log 4 + 4) X log X)^{1/2} log 2X`. -/
@[kb "davenport1980" "Ch 28, p. 166"]
theorem sum_psiChar_le_of_sq_ge {Q : ℝ} (hQ : 1 ≤ Q) {X : ℕ} (hX : 1 ≤ X) (hXQ : (X : ℝ) ≤ Q ^ 2)
    (u : (q : ℕ) → DirichletCharacter ℂ q → ℕ) (hu : ∀ q χ, u q χ ≤ X) :
    ∑ q ∈ Icc 1 ⌊Q⌋₊, ((q : ℝ) / q.totient) *
        ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ ↦ χ.IsPrimitive),
          ‖psiChar χ (u q χ)‖ ≤
      48 * Q ^ 2 * √((Real.log 4 + 4) * X * Real.log X) * Real.log (2 * X) := by
  have h := bilinear_sieve_sup hQ 1 X (fun _ ↦ 1) (fun n ↦ (Λ n : ℂ)) u
  have hrw : ∀ q (χ : DirichletCharacter ℂ q),
      ∑ m ∈ Icc 1 1, ∑ n ∈ (Icc 1 X).filter (fun n ↦ m * n ≤ u q χ),
        (1 : ℂ) * (Λ n : ℂ) * χ ((m * n : ℕ) : ZMod q) = psiChar χ (u q χ) := by
    intro q χ
    rw [Icc_self, sum_singleton, psiChar, Nat.floor_natCast]
    have : (Icc 1 X).filter (fun n ↦ 1 * n ≤ u q χ) = Icc 1 (u q χ) := by
      ext n; simp only [mem_filter, mem_Icc, one_mul]; have := hu q χ; omega
    rw [this]
    refine sum_congr rfl fun n _ ↦ ?_
    rw [one_mul, one_mul, mul_comm]
  simp only [hrw] at h
  refine h.trans ?_
  have hXr : (1:ℝ) ≤ X := by exact_mod_cast hX
  have hL : 0 ≤ Real.log (2 * X) := Real.log_nonneg (by linarith)
  have hΛ : ∑ n ∈ Icc 1 X, ‖(Λ n : ℂ)‖ ^ 2 ≤ (Real.log 4 + 4) * X * Real.log X := by
    have := sum_vonMangoldt_sq_le hXr
    rw [Nat.floor_natCast] at this
    simpa [Complex.norm_real, Real.norm_eq_abs, sq_abs] using this
  have h1 : √(∑ m ∈ Icc 1 1, ‖(1 : ℂ)‖ ^ 2) = 1 := by simp
  have h2 : √((((1 : ℕ) : ℝ) + 3 * Q ^ 2) * ((X : ℝ) + 3 * Q ^ 2)) ≤ 4 * Q ^ 2 := by
    rw [show 4 * Q ^ 2 = √((4 * Q ^ 2) * (4 * Q ^ 2)) from
      (Real.sqrt_mul_self (by positivity)).symm]
    refine Real.sqrt_le_sqrt ?_
    have : (1:ℝ) ≤ Q ^ 2 := one_le_pow₀ hQ
    push_cast
    exact mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)
  rw [h1]
  push_cast at h2 ⊢
  calc 12 * √((1 + 3 * Q ^ 2) * (X + 3 * Q ^ 2)) * 1 *
        √(∑ n ∈ Icc 1 X, ‖(Λ n : ℂ)‖ ^ 2) * Real.log (2 * 1 * X)
      ≤ 12 * (4 * Q ^ 2) * 1 * √((Real.log 4 + 4) * X * Real.log X) * Real.log (2 * X) := by
        simp only [mul_one]; gcongr
    _ = _ := by ring

end NTKB.Davenport
