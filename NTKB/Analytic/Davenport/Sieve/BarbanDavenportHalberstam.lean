/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Davenport.Sieve.Induced
import NTKB.Analytic.Davenport.Sieve.Dyadic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Complex.Exponential

/-!
# The Barban–Davenport–Halberstam theorem (Davenport, Chapter 29)

**Theorem** (Gallagher's form, estimate (1)): for fixed `A > 0` and `x (log x)^{-A} < Q ≤ x`,
`∑_{q ≤ Q} ∑_{(a, q) = 1} (ψ(x; q, a) - x/φ(q))² ≪ x Q log x` (`barban_davenport_halberstam`).

The proof follows Davenport: Parseval over the reduced residues (`sum_sq_psiAP_sub_eq`), passage to
the primitive characters (`norm_psiChar'_sub_le`, `sum_sum_primitiveCharacter_le`,
`sum_inv_totient_le`), the large sieve for characters with `a_n = Λ(n)` (estimate (B),
`sum_mul_sum_primitive_psiChar_le`, from Theorem 4 and `∑_{n ≤ x} Λ(n)² ≪ x log x`), dyadic ranges
for the moduli `q > Q₁ = (log x)^{A+2}` (`sum_dyadic_le`), and for the small moduli `q ≤ Q₁` the
estimate (C) of §22.

**Named input.** Estimate (C) of §22 (the Siegel–Walfisz theorem: `ψ(x, χ) ≪ x exp(-c √log x)`
for nonprincipal `χ` modulo `q ≤ (log x)^B`, which rests on Siegel's theorem, §21) and the prime
number theorem with the classical error term (§18) belong to the zero theory of chapters 13–22 and
are not proved here: they are the fields of the structure `SiegelWalfiszHypothesis`, and the
theorem is proved conditionally on it.
-/

open Finset Real ComplexConjugate
open scoped ArithmeticFunction.vonMangoldt Chebyshev

namespace NTKB.Davenport

/-- **Named input (Davenport, §18 and §22, estimate (C))**: the prime number theorem with the
classical error term, `ψ(x) - x ≪ x exp(-c √log x)`, and the Siegel–Walfisz estimate: for every
`B > 0`, `ψ(x, χ) ≪_B x exp(-c_B √log x)` for every nonprincipal character `χ` modulo
`q ≤ (log x)^B`. -/
structure SiegelWalfiszHypothesis : Prop where
  pnt : ∃ c > 0, ∃ C > 0, ∀ x : ℝ, 2 ≤ x → |ψ x - x| ≤ C * x * exp (-c * √(Real.log x))
  sw : ∀ B : ℝ, 0 < B → ∃ c > 0, ∃ C > 0, ∀ x : ℝ, 2 ≤ x → ∀ q : ℕ, 0 < q →
    (q : ℝ) ≤ Real.log x ^ B → ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
      ‖psiChar χ x‖ ≤ C * x * exp (-c * √(Real.log x))

/-- `∑_{n ≤ x} Λ(n)² ≤ (log 4 + 4) x log x`. -/
lemma sum_vonMangoldt_sq_le {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ Icc 1 ⌊x⌋₊, Λ n ^ 2 ≤ (Real.log 4 + 4) * x * Real.log x := by
  have hlog : ∀ n ∈ Icc 1 ⌊x⌋₊, Λ n ≤ Real.log x := by
    intro n hn
    have hn := mem_Icc.1 hn
    refine ArithmeticFunction.vonMangoldt_le_log.trans (Real.log_le_log (by exact_mod_cast hn.1) ?_)
    exact (Nat.cast_le.2 hn.2).trans (Nat.floor_le (by linarith))
  have hpsi : ∑ n ∈ Icc 1 ⌊x⌋₊, Λ n = ψ x := by
    rw [Chebyshev.psi]; rfl
  calc ∑ n ∈ Icc 1 ⌊x⌋₊, Λ n ^ 2 ≤ ∑ n ∈ Icc 1 ⌊x⌋₊, Real.log x * Λ n := by
        refine sum_le_sum fun n hn ↦ ?_
        rw [sq]; gcongr
        exact hlog n hn
    _ = Real.log x * ψ x := by rw [← mul_sum, hpsi]
    _ ≤ Real.log x * ((Real.log 4 + 4) * x) := by
        gcongr
        · exact Real.log_nonneg hx
        · exact Chebyshev.psi_le_const_mul_self (by linarith)
    _ = _ := by ring

/-- `∑_{0 < n ≤ N} f(n) = ∑_{1 ≤ n ≤ N} f(n)` (integers versus naturals). -/
lemma sum_Ioc_zero_int_eq {M : Type*} [AddCommMonoid M] (f : ℤ → M) (N : ℕ) :
    ∑ n ∈ Ioc (0 : ℤ) (0 + N), f n = ∑ n ∈ Icc 1 N, f n := by
  rw [sum_Ioc_int_eq_sum_range, ← Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range]
  refine sum_congr (by simp) fun j _ ↦ ?_
  congr 1

open scoped Classical in
/-- **Davenport, Ch. 29, (B)** (the large sieve with `a_n = Λ(n)`): for `x ≥ 1` and `y ≥ 1`,
`∑_{q ≤ y} (q/φ(q)) ∑*_χ |ψ(x, χ)|² ≤ (x + 3y²)(log 4 + 4) x log x`. -/
@[kb "davenport1980" "Ch 29, p. 169, (B)"]
theorem sum_mul_sum_primitive_psiChar_le {x : ℝ} (hx : 1 ≤ x) {y : ℝ} (hy : 1 ≤ y) :
    ∑ q ∈ Icc 1 ⌊y⌋₊, ((q : ℝ) / q.totient) *
        ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ ↦ χ.IsPrimitive),
          ‖psiChar χ x‖ ^ 2 ≤
      (x + 3 * y ^ 2) * ((Real.log 4 + 4) * x * Real.log x) := by
  set c : ℤ → ℂ := fun n ↦ (Λ n.toNat : ℂ)
  have h := large_sieve_characters hy 0 ⌊x⌋₊ c
  have hT : ∀ (q : ℕ) (χ : DirichletCharacter ℂ q),
      ∑ n ∈ Ioc (0 : ℤ) (0 + ⌊x⌋₊), c n * χ n = psiChar χ x := by
    intro q χ
    rw [sum_Ioc_zero_int_eq (fun n ↦ c n * χ n), psiChar]
    refine sum_congr rfl fun n _ ↦ ?_
    simp only [c, Int.toNat_natCast]
    push_cast; ring
  have hc : ∑ n ∈ Ioc (0 : ℤ) (0 + ⌊x⌋₊), ‖c n‖ ^ 2 = ∑ n ∈ Icc 1 ⌊x⌋₊, Λ n ^ 2 := by
    rw [sum_Ioc_zero_int_eq (fun n ↦ ‖c n‖ ^ 2)]
    refine sum_congr rfl fun n _ ↦ ?_
    simp only [c, Int.toNat_natCast, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  simp_rw [hT] at h
  rw [hc] at h
  refine h.trans ?_
  have hN : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (by linarith)
  gcongr
  exact sum_vonMangoldt_sq_le hx

/-- Powers of `L` are dominated by `exp(c √L)`. -/
lemma pow_le_mul_exp_sqrt {c : ℝ} (hc : 0 < c) (E : ℕ) :
    ∃ K > 0, ∀ L : ℝ, 0 ≤ L → L ^ E ≤ K * exp (c * √L) := by
  refine ⟨(2 * E).factorial / c ^ (2 * E), by positivity, fun L hL ↦ ?_⟩
  have h := Real.pow_div_factorial_le_exp (x := c * √L) (by positivity) (2 * E)
  have hL' : L ^ E = √L ^ (2 * E) := by rw [pow_mul, Real.sq_sqrt hL]
  rw [hL']
  rw [div_le_iff₀ (by positivity), mul_pow] at h
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  linarith

/-- The small moduli: for primitive `χ` modulo `d ≤ (log x)^B`, `ψ'(x, χ) ≪ x exp(-c √log x)`
(from the prime number theorem with error term for `d = 1` and the Siegel–Walfisz estimate for
`d ≥ 2`). -/
lemma SiegelWalfiszHypothesis.primitive_bound (h : SiegelWalfiszHypothesis) {B : ℝ} (hB : 0 < B) :
    ∃ c > 0, ∃ C > 0, ∀ x : ℝ, 2 ≤ x → ∀ d : ℕ, 0 < d → (d : ℝ) ≤ Real.log x ^ B →
      ∀ χ : DirichletCharacter ℂ d, χ.IsPrimitive →
        ‖psiChar' χ x‖ ≤ C * x * exp (-c * √(Real.log x)) := by
  obtain ⟨c₁, hc₁, C₁, hC₁, h₁⟩ := h.pnt
  obtain ⟨c₂, hc₂, C₂, hC₂, h₂⟩ := h.sw B hB
  refine ⟨min c₁ c₂, lt_min hc₁ hc₂, max C₁ C₂, lt_max_of_lt_left hC₁, ?_⟩
  intro x hx d hd hdx χ hχ
  have hx0 : 0 ≤ x := by linarith
  have hmono : ∀ c' C', c' ≥ min c₁ c₂ → C' ≤ max C₁ C₂ → 0 ≤ C' →
      C' * x * exp (-c' * √(Real.log x)) ≤ max C₁ C₂ * x * exp (-min c₁ c₂ * √(Real.log x)) := by
    intro c' C' hc' hC' hC'0
    gcongr
  rcases Nat.lt_or_ge d 2 with hd2 | hd2
  · -- `d = 1`: `ψ'(x, 1) = ψ(x) - x`
    have hd1 : d = 1 := by omega
    subst hd1
    have h1 : χ = 1 := DirichletCharacter.level_one χ
    subst h1
    have hpsi : psiChar (1 : DirichletCharacter ℂ 1) x = (ψ x : ℂ) := by
      rw [psiChar, Chebyshev.psi]
      push_cast
      refine sum_congr rfl fun n _ ↦ ?_
      rw [MulChar.one_apply (isUnit_of_subsingleton _), one_mul]
    simp only [psiChar', if_true, hpsi]
    rw [show (ψ x : ℂ) - (x : ℂ) = ((ψ x - x : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs]
    exact (h₁ x hx).trans (hmono c₁ C₁ (min_le_left _ _) (le_max_left _ _) hC₁.le)
  · have : NeZero d := ⟨by omega⟩
    have hne : χ ≠ 1 := by
      rintro rfl
      have := hχ
      rw [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_one] at this
      omega
    simp only [psiChar', if_neg hne, sub_zero]
    exact (h₂ x hx d hd hdx χ hne).trans (hmono c₂ C₂ (min_le_right _ _) (le_max_right _ _)
      hC₂.le)

/-- `⌊y⌋ ≥ y/2` for `y ≥ 1`. -/
lemma half_le_floor {y : ℝ} (hy : 1 ≤ y) : y / 2 ≤ ⌊y⌋₊ := by
  have h1 : (1 : ℝ) ≤ ⌊y⌋₊ := by exact_mod_cast Nat.le_floor (by exact_mod_cast hy)
  have h2 := Nat.lt_floor_add_one y
  linarith

/-- The number of Dirichlet characters modulo `q` is `φ(q)`. -/
lemma card_dirichletCharacter (q : ℕ) [NeZero q] :
    (Fintype.card (DirichletCharacter ℂ q) : ℝ) = q.totient := by
  rw [← Nat.card_eq_fintype_card, DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity]

/-- `(log x)³ ≤ 27 x`. -/
lemma log_cube_le {x : ℝ} (hx : 0 < x) : Real.log x ^ 3 ≤ 27 * x := by
  rcases le_or_gt (Real.log x) 0 with h | h
  · have : Real.log x ^ 3 ≤ 0 := by
      have := pow_le_pow_left₀ (by linarith : (0:ℝ) ≤ -Real.log x) le_rfl 3
      nlinarith [sq_nonneg (Real.log x)]
    linarith
  have h1 := Real.log_le_rpow_div hx.le (by norm_num : (0 : ℝ) < 1 / 3)
  have h' : Real.log x ≤ 3 * x ^ ((1 : ℝ) / 3) := by linarith
  have hx3 : (x ^ ((1 : ℝ) / 3)) ^ 3 = x := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]; norm_num
  calc Real.log x ^ 3 ≤ (3 * x ^ ((1 : ℝ) / 3)) ^ 3 := by gcongr
    _ = 27 * x := by rw [mul_pow, hx3]; norm_num

open scoped Classical in
/-- **Davenport, Ch. 29, estimate (1)** (the Barban–Davenport–Halberstam theorem in Gallagher's
form), conditional on the named input `SiegelWalfiszHypothesis` (estimate (C) of §22 and the prime
number theorem with error term): for fixed `A > 0`, if `x (log x)^{-A} < Q ≤ x` then
`∑_{q ≤ Q} ∑_{1 ≤ a ≤ q, (a, q) = 1} (ψ(x; q, a) - x/φ(q))² ≪ x Q log x`. -/
@[kb "davenport1980" "Ch 29, p. 169, (1)"]
theorem barban_davenport_halberstam (hSW : SiegelWalfiszHypothesis) {A : ℝ} (hA : 0 < A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 3 ≤ x → ∀ Q : ℝ, x * Real.log x ^ (-A) < Q → Q ≤ x →
      ∑ q ∈ Icc 1 ⌊Q⌋₊, ∑ a ∈ (Icc 1 q).filter (fun a ↦ Nat.Coprime a q),
        (psiAP x q a - x / q.totient) ^ 2 ≤ C * x * Q * Real.log x := by
  obtain ⟨C₀, hC₀, hT⟩ := sum_inv_totient_le
  obtain ⟨Cd, hCd, hD⟩ := sum_dyadic_le
  obtain ⟨c, hc, Csw, hCsw, hSmall⟩ := hSW.primitive_bound (B := A + 2) (by linarith)
  obtain ⟨K₁, hK₁, hK₁b⟩ := pow_le_mul_exp_sqrt hc (2 * ⌈A⌉₊ + 4)
  have hCl : 0 < Real.log 4 + 4 := by positivity
  refine ⟨2 * C₀ * (2 * Csw ^ 2 * K₁ + 5 * Cd * (Real.log 4 + 4)) + 8 * 27, by positivity, ?_⟩
  intro x hx Q hQ hQx
  set Cl : ℝ := Real.log 4 + 4 with hCldef
  set L := Real.log x with hLdef
  have hx0 : 0 < x := by linarith
  have hL1 : 1 ≤ L := by
    rw [hLdef, ← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
  have hL0 : 0 < L := by linarith
  have hQ0 : 0 < Q := lt_trans (by positivity) hQ
  set Q' := ⌊Q⌋₊ with hQ'def
  have hQ'Q : (Q' : ℝ) ≤ Q := Nat.floor_le hQ0.le
  have hQ'x : (Q' : ℝ) ≤ x := hQ'Q.trans hQx
  have hlogQ' : ∀ d : ℕ, 1 ≤ d → Real.log ((Q' : ℝ) / d) ≤ L := by
    intro d hd
    rcases Nat.eq_zero_or_pos Q' with h0 | h0
    · rw [h0, Nat.cast_zero, zero_div, Real.log_zero]; exact hL0.le
    have : (Q' : ℝ) / d ≤ x :=
      (div_le_self (by positivity) (by exact_mod_cast hd)).trans hQ'x
    exact Real.log_le_log (by positivity) this
  have hxQ : x * L ^ (-A) < Q := hQ
  -- (P) Parseval over the reduced residues
  have hP : ∑ q ∈ Icc 1 Q', ∑ a ∈ (Icc 1 q).filter (fun a ↦ Nat.Coprime a q),
      (psiAP x q a - x / q.totient) ^ 2 = ∑ q ∈ Icc 1 Q', 1 / (q.totient : ℝ) *
        ∑ χ : DirichletCharacter ℂ q, ‖psiChar' χ x‖ ^ 2 := by
    refine sum_congr rfl fun q hq ↦ ?_
    have : NeZero q := ⟨by have := (mem_Icc.1 hq).1; omega⟩
    exact sum_sq_psiAP_sub_eq x
  -- (I) passing to the primitive characters
  have hI : ∀ q ∈ Icc 1 Q', 1 / (q.totient : ℝ) * ∑ χ : DirichletCharacter ℂ q, ‖psiChar' χ x‖ ^ 2
      ≤ 2 * (1 / (q.totient : ℝ) *
          ∑ χ : DirichletCharacter ℂ q, ‖psiChar' χ.primitiveCharacter x‖ ^ 2) + 8 * L ^ 4 := by
    intro q hq
    have : NeZero q := ⟨by have := (mem_Icc.1 hq).1; omega⟩
    have hφ : (0 : ℝ) < q.totient := by
      exact_mod_cast Nat.totient_pos.2 (by have := (mem_Icc.1 hq).1; omega)
    have hlogq : Real.log q ≤ L := by
      have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (mem_Icc.1 hq).1
      exact Real.log_le_log (by linarith) ((Nat.cast_le.2 (mem_Icc.1 hq).2).trans hQ'x)
    have hlogq0 : 0 ≤ Real.log q := Real.log_natCast_nonneg q
    have hχ : ∀ χ : DirichletCharacter ℂ q, ‖psiChar' χ x‖ ^ 2 ≤
        2 * ‖psiChar' χ.primitiveCharacter x‖ ^ 2 + 8 * L ^ 4 := by
      intro χ
      have h1 := norm_psiChar'_sub_le χ (by linarith : (1 : ℝ) ≤ x)
      have h2 : ‖psiChar' χ x‖ ≤ ‖psiChar' χ.primitiveCharacter x‖ + 2 * L ^ 2 := by
        have := norm_sub_norm_le (psiChar' χ x) (psiChar' χ.primitiveCharacter x)
        have : 2 * Real.log q * L ≤ 2 * L ^ 2 := by nlinarith
        linarith
      nlinarith [norm_nonneg (psiChar' χ x), norm_nonneg (psiChar' χ.primitiveCharacter x),
        sq_nonneg (‖psiChar' χ.primitiveCharacter x‖ - 2 * L ^ 2)]
    calc 1 / (q.totient : ℝ) * ∑ χ : DirichletCharacter ℂ q, ‖psiChar' χ x‖ ^ 2
        ≤ 1 / (q.totient : ℝ) * ∑ χ : DirichletCharacter ℂ q,
            (2 * ‖psiChar' χ.primitiveCharacter x‖ ^ 2 + 8 * L ^ 4) := by
          gcongr with χ; exact hχ χ
      _ = _ := by
          rw [sum_add_distrib, sum_const, card_univ, nsmul_eq_mul, card_dirichletCharacter,
            ← mul_sum]
          field_simp
  -- (G) collecting the characters by their primitive characters, and `∑ 1/φ(kd)`
  set W' : ℕ → ℝ := fun d ↦ ∑ η ∈ (univ : Finset (DirichletCharacter ℂ d)).filter
    (fun η ↦ η.IsPrimitive), ‖psiChar' η x‖ ^ 2 with hW'def
  set W : ℕ → ℝ := fun d ↦ ∑ η ∈ (univ : Finset (DirichletCharacter ℂ d)).filter
    (fun η ↦ η.IsPrimitive), ‖psiChar η x‖ ^ 2 with hWdef
  set g : ℕ → ℝ := fun d ↦ (1 + Real.log ((Q' : ℝ) / d)) / d.totient * W' d with hgdef
  have hG : ∑ q ∈ Icc 1 Q', 1 / (q.totient : ℝ) *
      ∑ χ : DirichletCharacter ℂ q, ‖psiChar' χ.primitiveCharacter x‖ ^ 2 ≤
        C₀ * ∑ d ∈ Icc 1 Q', g d := by
    refine (sum_sum_primitiveCharacter_le Q' (fun n ↦ 1 / (n.totient : ℝ)) (fun n ↦ by positivity)
      (fun d η ↦ ‖psiChar' η x‖ ^ 2) (fun _ _ ↦ by positivity)).trans ?_
    rw [mul_sum]
    refine sum_le_sum fun d hd ↦ ?_
    have hd1 := (mem_Icc.1 hd).1
    have hK : 1 ≤ Q' / d := (Nat.one_le_div_iff (by omega)).2 (mem_Icc.1 hd).2
    have hφ : (0 : ℝ) < d.totient := by exact_mod_cast Nat.totient_pos.2 (by omega)
    have hlogK : Real.log (Q' / d : ℕ) ≤ Real.log ((Q' : ℝ) / d) :=
      Real.log_le_log (by exact_mod_cast (by omega : 0 < Q' / d)) Nat.cast_div_le
    have hk : ∑ k ∈ Icc 1 (Q' / d), 1 / ((k * d).totient : ℝ) ≤
        C₀ * ((1 + Real.log ((Q' : ℝ) / d)) / d.totient) := by
      refine (sum_inv_totient_mul_le (by omega) _).trans ?_
      have := hT (Q' / d) hK
      calc 1 / (d.totient : ℝ) * ∑ k ∈ Icc 1 (Q' / d), 1 / (k.totient : ℝ)
          ≤ 1 / (d.totient : ℝ) * (C₀ * (1 + Real.log ((Q' : ℝ) / d))) := by
            gcongr; exact this.trans (by gcongr)
        _ = _ := by ring
    rw [← sum_mul]
    calc W' d * ∑ k ∈ Icc 1 (Q' / d), 1 / ((k * d).totient : ℝ)
        ≤ W' d * (C₀ * ((1 + Real.log ((Q' : ℝ) / d)) / d.totient)) := by
          gcongr
      _ = C₀ * g d := by simp only [hgdef]; ring
  -- (S) splitting the moduli at `Q₁ = (log x)^{A+2}`
  set Q₁ := ⌊L ^ (A + 2)⌋₊ with hQ₁def
  have hLA1 : 1 ≤ L ^ (A + 2) := Real.one_le_rpow hL1 (by linarith)
  have hQ₁1 : 1 ≤ Q₁ := Nat.le_floor (by exact_mod_cast hLA1)
  have hQ₁le : (Q₁ : ℝ) ≤ L ^ (A + 2) := Nat.floor_le (by linarith)
  have hQ₁ge : L ^ (A + 2) / 2 ≤ Q₁ := half_le_floor hLA1
  have hsplit : ∑ d ∈ Icc 1 Q', g d =
      ∑ d ∈ (Icc 1 Q').filter (fun d ↦ d ≤ Q₁), g d + ∑ d ∈ Ioc Q₁ Q', g d := by
    rw [← sum_filter_add_sum_filter_not (Icc 1 Q') (fun d ↦ d ≤ Q₁)]
    congr 1
    refine sum_congr ?_ fun _ _ ↦ rfl
    ext d; simp only [mem_filter, mem_Icc, mem_Ioc, not_le]; omega
  -- small moduli: estimate (C) of §22
  have hsmall : ∑ d ∈ (Icc 1 Q').filter (fun d ↦ d ≤ Q₁), g d ≤
      2 * Csw ^ 2 * K₁ * x * Q * L := by
    set e := Csw * x * exp (-c * √L) with hedef
    have he : 0 ≤ e := by positivity
    have hterm : ∀ d ∈ (Icc 1 Q').filter (fun d ↦ d ≤ Q₁), g d ≤ (1 + L) * e ^ 2 := by
      intro d hd
      simp only [mem_filter, mem_Icc] at hd
      have : NeZero d := ⟨by omega⟩
      have hφ : (0 : ℝ) < d.totient := by exact_mod_cast Nat.totient_pos.2 (by omega)
      have hdB : (d : ℝ) ≤ L ^ (A + 2) := (Nat.cast_le.2 hd.2).trans hQ₁le
      have hW : W' d ≤ d.totient * e ^ 2 := by
        calc W' d ≤ ∑ η ∈ (univ : Finset (DirichletCharacter ℂ d)).filter
              (fun η ↦ η.IsPrimitive), e ^ 2 := by
              refine sum_le_sum fun η hη ↦ ?_
              have := hSmall x (by linarith) d (by omega) hdB η (mem_filter.1 hη).2
              gcongr
          _ ≤ ∑ η : DirichletCharacter ℂ d, e ^ 2 :=
              sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ ↦ by positivity
          _ = d.totient * e ^ 2 := by
              rw [sum_const, card_univ, nsmul_eq_mul, card_dirichletCharacter]
      have hlog := hlogQ' d (by omega)
      have hdQ : (d : ℝ) ≤ Q' := by exact_mod_cast hd.1.2
      have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
      have hlog0 : 0 ≤ 1 + Real.log ((Q' : ℝ) / d) := by
        have : 0 ≤ Real.log ((Q' : ℝ) / d) :=
          Real.log_nonneg (by rw [le_div_iff₀ hd0]; linarith)
        linarith
      calc g d = (1 + Real.log ((Q' : ℝ) / d)) / d.totient * W' d := rfl
        _ ≤ (1 + Real.log ((Q' : ℝ) / d)) / d.totient * (d.totient * e ^ 2) := by gcongr
        _ = (1 + Real.log ((Q' : ℝ) / d)) * e ^ 2 := by field_simp
        _ ≤ (1 + L) * e ^ 2 := by gcongr
    have hcard : (((Icc 1 Q').filter (fun d ↦ d ≤ Q₁)).card : ℝ) ≤ L ^ (A + 2) := by
      refine le_trans ?_ hQ₁le
      have hsub : (Icc 1 Q').filter (fun d ↦ d ≤ Q₁) ⊆ Icc 1 Q₁ := by
        intro d hd; simp only [mem_filter, mem_Icc] at hd ⊢; omega
      have := card_le_card hsub
      simp only [Nat.card_Icc, add_tsub_cancel_right] at this
      exact_mod_cast this
    -- `L^{A+2} (2L) e^{-2c√L} ≤ 2 K₁ L^{-A}`
    have hexp : L ^ (A + 2) * (2 * L) * exp (-c * √L) ^ 2 ≤ 2 * K₁ * L ^ (-A) := by
      have hE : L ^ (2 * A + 3) ≤ L ^ (((2 * ⌈A⌉₊ + 4 : ℕ) : ℝ)) := by
        apply Real.rpow_le_rpow_of_exponent_le hL1
        push_cast
        have := Nat.le_ceil A; linarith
      have hK := hK₁b L hL0.le
      rw [← Real.rpow_natCast] at hK
      have hsq : exp (-c * √L) ^ 2 * exp (c * √L) ≤ 1 := by
        rw [sq, ← Real.exp_add, ← Real.exp_add]
        apply Real.exp_le_one_iff.2
        nlinarith [Real.sqrt_nonneg L]
      have e1 : L ^ (2 * A + 3) * L ^ (-A) = L ^ (A + 2) * L := by
        rw [← Real.rpow_add hL0, ← Real.rpow_add_one hL0.ne']; congr 1; ring
      have hsplitL : L ^ (A + 2) * (2 * L) = 2 * (L ^ (2 * A + 3) * L ^ (-A)) := by
        rw [e1]; ring
      rw [hsplitL]
      have hLA : 0 < L ^ (-A) := Real.rpow_pos_of_pos hL0 _
      calc 2 * (L ^ (2 * A + 3) * L ^ (-A)) * exp (-c * √L) ^ 2
          ≤ 2 * ((K₁ * exp (c * √L)) * L ^ (-A)) * exp (-c * √L) ^ 2 := by
            gcongr; exact hE.trans hK
        _ = 2 * K₁ * L ^ (-A) * (exp (-c * √L) ^ 2 * exp (c * √L)) := by ring
        _ ≤ 2 * K₁ * L ^ (-A) * 1 := by gcongr
        _ = _ := by ring
    have hLA0 : 0 ≤ L ^ (A + 2) := by positivity
    calc ∑ d ∈ (Icc 1 Q').filter (fun d ↦ d ≤ Q₁), g d
        ≤ ∑ d ∈ (Icc 1 Q').filter (fun d ↦ d ≤ Q₁), (1 + L) * e ^ 2 := sum_le_sum hterm
      _ = ((Icc 1 Q').filter (fun d ↦ d ≤ Q₁)).card * ((1 + L) * e ^ 2) := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ L ^ (A + 2) * ((1 + L) * e ^ 2) := by gcongr
      _ ≤ L ^ (A + 2) * ((2 * L) * e ^ 2) := by gcongr; linarith
      _ = L ^ (A + 2) * (2 * L) * exp (-c * √L) ^ 2 * (Csw ^ 2 * x ^ 2) := by
          rw [hedef]; ring
      _ ≤ 2 * K₁ * L ^ (-A) * (Csw ^ 2 * x ^ 2) := by gcongr
      _ = 2 * Csw ^ 2 * K₁ * x * (x * L ^ (-A)) := by ring
      _ ≤ 2 * Csw ^ 2 * K₁ * x * (Q * L) :=
          mul_le_mul_of_nonneg_left (hxQ.le.trans (le_mul_of_one_le_right hQ0.le hL1))
            (by positivity)
      _ = _ := by ring
  -- large moduli: the large sieve (B) and dyadic ranges
  have hlarge : ∑ d ∈ Ioc Q₁ Q', g d ≤ 5 * Cd * Cl * x * Q * L := by
    set a : ℕ → ℝ := fun d ↦ (d : ℝ) / d.totient * W d with hadef
    have ha : ∀ d, 0 ≤ a d := fun d ↦
      mul_nonneg (by positivity) (sum_nonneg fun _ _ ↦ by positivity)
    have hB : ∀ y : ℝ, 1 ≤ y → ∑ d ∈ Icc 1 ⌊y⌋₊, a d ≤ (x + 3 * y ^ 2) * (Cl * x * L) := by
      intro y hy
      have := sum_mul_sum_primitive_psiChar_le (by linarith : (1 : ℝ) ≤ x) hy
      simpa only [hadef, hWdef] using this
    have hgd : ∀ d ∈ Ioc Q₁ Q', g d = (1 + Real.log ((Q' : ℝ) / d)) / d * a d := by
      intro d hd
      have hd2 : 2 ≤ d := by have := (mem_Ioc.1 hd).1; omega
      have : NeZero d := ⟨by omega⟩
      have hφ : (0 : ℝ) < d.totient := by exact_mod_cast Nat.totient_pos.2 (by omega)
      have hWW : W' d = W d := by
        refine sum_congr rfl fun η hη ↦ ?_
        have hne : η ≠ 1 := by
          rintro rfl
          have := (mem_filter.1 hη).2
          rw [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_one] at this
          omega
        simp only [psiChar', if_neg hne, sub_zero]
      have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
      simp only [hgdef, hadef, hWW]
      field_simp
    rw [sum_congr rfl hgd]
    rcases le_or_gt Q' Q₁ with hQQ | hQQ
    · rw [Ioc_eq_empty (by omega), sum_empty]; positivity
    have hdy := hD a ha x (Cl * x * L) hx0.le (by positivity) hB Q₁ Q' hQ₁1 hQQ.le
    refine hdy.trans ?_
    have hlog1 : 1 + Real.log ((Q' : ℝ) / Q₁) ≤ 2 * L := by
      have := hlogQ' Q₁ hQ₁1; linarith
    have hQ₁pos : (0 : ℝ) < Q₁ := by exact_mod_cast hQ₁1
    have hLm : 0 < L ^ (-A - 1) := Real.rpow_pos_of_pos hL0 _
    have h1 : x * (1 + Real.log ((Q' : ℝ) / Q₁)) / Q₁ ≤ 4 * x * L ^ (-A - 1) := by
      rw [div_le_iff₀ hQ₁pos]
      have hpow : L ^ (-A - 1) * L ^ (A + 2) = L := by
        rw [← Real.rpow_add hL0, show -A - 1 + (A + 2) = 1 by ring, Real.rpow_one]
      calc x * (1 + Real.log ((Q' : ℝ) / Q₁)) ≤ x * (2 * L) := by gcongr
        _ = 2 * x * (L ^ (-A - 1) * L ^ (A + 2)) := by rw [hpow]; ring
        _ ≤ 2 * x * (L ^ (-A - 1) * (2 * Q₁)) := by gcongr; linarith
        _ = 4 * x * L ^ (-A - 1) * Q₁ := by ring
    have h2 : Cl * x * L * (4 * x * L ^ (-A - 1)) = 4 * Cl * x * (x * L ^ (-A)) := by
      have : L * L ^ (-A - 1) = L ^ (-A) := by
        rw [mul_comm, ← Real.rpow_add_one hL0.ne', show -A - 1 + 1 = -A by ring]
      calc Cl * x * L * (4 * x * L ^ (-A - 1)) = 4 * Cl * x * x * (L * L ^ (-A - 1)) := by ring
        _ = _ := by rw [this]; ring
    calc Cd * (Cl * x * L) * (x * (1 + Real.log ((Q' : ℝ) / Q₁)) / Q₁ + Q')
        ≤ Cd * (Cl * x * L) * (4 * x * L ^ (-A - 1) + Q) := by gcongr
      _ = Cd * (Cl * x * L * (4 * x * L ^ (-A - 1)) + Cl * x * L * Q) := by ring
      _ = Cd * (4 * Cl * x * (x * L ^ (-A)) + Cl * x * L * Q) := by rw [h2]
      _ ≤ Cd * (4 * Cl * x * (Q * L) + Cl * x * L * Q) := by
          have hh : x * L ^ (-A) ≤ Q * L := hxQ.le.trans (le_mul_of_one_le_right hQ0.le hL1)
          exact mul_le_mul_of_nonneg_left (add_le_add_left
            (mul_le_mul_of_nonneg_left hh (by positivity)) _) hCd.le
      _ = _ := by ring
  -- assembly
  have hL4 : L ^ 4 ≤ 27 * x * L := by
    have := log_cube_le hx0
    calc L ^ 4 = L ^ 3 * L := by ring
      _ ≤ 27 * x * L := by gcongr
  rw [hP]
  calc ∑ q ∈ Icc 1 Q', 1 / (q.totient : ℝ) * ∑ χ : DirichletCharacter ℂ q, ‖psiChar' χ x‖ ^ 2
      ≤ ∑ q ∈ Icc 1 Q', (2 * (1 / (q.totient : ℝ) *
          ∑ χ : DirichletCharacter ℂ q, ‖psiChar' χ.primitiveCharacter x‖ ^ 2) + 8 * L ^ 4) :=
        sum_le_sum hI
    _ = 2 * ∑ q ∈ Icc 1 Q', 1 / (q.totient : ℝ) *
          ∑ χ : DirichletCharacter ℂ q, ‖psiChar' χ.primitiveCharacter x‖ ^ 2 +
          Q' * (8 * L ^ 4) := by
        rw [sum_add_distrib, ← mul_sum, sum_const, Nat.card_Icc, nsmul_eq_mul]
        simp
    _ ≤ 2 * (C₀ * (2 * Csw ^ 2 * K₁ * x * Q * L + 5 * Cd * Cl * x * Q * L)) +
          Q * (8 * (27 * x * L)) := by
        gcongr
        · refine hG.trans ?_
          rw [hsplit]
          gcongr
    _ = _ := by ring

end NTKB.Davenport
