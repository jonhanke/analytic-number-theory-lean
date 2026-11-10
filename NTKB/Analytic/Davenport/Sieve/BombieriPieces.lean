/- Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license. -/
import NTKB.Analytic.Davenport.Sieve.BombieriBilinear
import NTKB.Analytic.Davenport.Sieve.TypeII
import NTKB.Analytic.Davenport.Sieve.PolyaVinogradov

/-!
# The pieces of Vaughan's identity with a character (Davenport, Chapter 28, (7)–(10))

For a nonprincipal character `χ` and `N ≤ X` we write `ψ(N, χ) = ∑_{n ≤ N} χ(n) Λ(n)` as
`S₁ + S₂ + S₃ + S₄` (`sum_mul_vonMangoldt_eq`) and put each piece in the form used in §28:

* `S₁`: `|S₁| ≤ (log 4 + 4) U` (`norm_S₁_le`);
* `S₂ = -(S₂' + S₂'')` split at `t = U`; `S₂'` is bounded by Pólya–Vinogradov
  (`norm_S₂'_le`), and `S₂''` is a bilinear sum `∑_{t, r ≤ X, tr ≤ N} α_t χ(tr)` with
  `α_t = (Λ_U * μ_V)(t) [t > U]` (`S₂''_eq`);
* `S₃`: Pólya–Vinogradov and partial summation (`norm_S₃_char_le`);
* `S₄ = -∑_{m, k ≤ X, mk ≤ N} α_m β_k χ(mk)` with `α_m = Λ(m) [U < m ≤ X/V]`,
  `β_k = (∑_{d ∣ k, d ≤ V} μ(d)) [V < k ≤ X]` (`S₄_eq_bilinear`).
-/

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

namespace NTKB.Davenport

/-- `{r ≤ X : tr ≤ N} = [1, N/t]` for `t ≥ 1`, `N ≤ X`. -/
lemma filter_Icc_mul_le {t N X : ℕ} (ht : 1 ≤ t) (hNX : N ≤ X) :
    (Icc 1 X).filter (fun r ↦ t * r ≤ N) = Icc 1 (N / t) := by
  ext r
  simp only [mem_filter, mem_Icc, Nat.le_div_iff_mul_le (by omega : 0 < t)]
  constructor
  · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, by rw [mul_comm]; exact h3⟩
  · rintro ⟨h1, h3⟩
    refine ⟨⟨h1, ?_⟩, by rw [mul_comm]; exact h3⟩
    calc r ≤ r * t := Nat.le_mul_of_pos_right r (by omega)
      _ ≤ N := h3
      _ ≤ X := hNX

section PolyaVinogradov

variable {q : ℕ} [NeZero q]

/-- Pólya–Vinogradov for `∑_{1 ≤ h ≤ R} χ(h)`. -/
lemma norm_sum_Icc_one_char_le {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) (R : ℕ) :
    ‖∑ h ∈ Icc 1 R, χ h‖ ≤ 2 * √q * Real.log q := by
  have h := norm_sum_Ioc_le hχ 0 R
  rw [sum_Ioc_zero_int_eq (fun n : ℤ ↦ χ n)] at h
  simpa using h

/-- Pólya–Vinogradov for `∑_{w ≤ h ≤ R} χ(h)`, `w ≥ 1`. -/
lemma norm_sum_Icc_char_le {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {w : ℕ} (hw : 1 ≤ w)
    (R : ℕ) : ‖∑ h ∈ Icc w R, χ h‖ ≤ 4 * √q * Real.log q := by
  have hl : 0 ≤ Real.log q := Real.log_natCast_nonneg q
  by_cases hwR : w ≤ R + 1
  · have hU : Icc 1 R = Icc 1 (w - 1) ∪ Icc w R := by
      ext a; simp only [mem_union, mem_Icc]; omega
    have hD : Disjoint (Icc 1 (w - 1)) (Icc w R) :=
      disjoint_left.2 fun a ha hb ↦ by simp only [mem_Icc] at ha hb; omega
    have hs : ∑ h ∈ Icc w R, χ h = ∑ h ∈ Icc 1 R, χ h - ∑ h ∈ Icc 1 (w - 1), χ h := by
      rw [hU, sum_union hD]; ring
    rw [hs]
    refine (norm_sub_le _ _).trans ?_
    have h1 := norm_sum_Icc_one_char_le hχ R
    have h2 := norm_sum_Icc_one_char_le hχ (w - 1)
    linarith
  · rw [Icc_eq_empty (by omega), sum_empty, norm_zero]
    positivity

end PolyaVinogradov

/-- `|S₁| ≤ (log 4 + 4) U` for `|f| ≤ 1`. -/
lemma norm_S₁_le (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1) (N U : ℕ) :
    ‖∑ n ∈ Icc 1 N, f n * (truncate Λ U n : ℂ)‖ ≤ (Real.log 4 + 4) * U := by
  refine (norm_sum_le _ _).trans ?_
  have : ∀ n ∈ Icc 1 N, ‖f n * (truncate Λ U n : ℂ)‖ ≤ if n ≤ U then Λ n else 0 := by
    intro n _
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, truncate_apply]
    split_ifs
    · rw [abs_of_nonneg vonMangoldt_nonneg]
      exact mul_le_of_le_one_left vonMangoldt_nonneg (hf n)
    · simp
  refine (sum_le_sum this).trans ?_
  rw [← sum_filter]
  have hsub : (Icc 1 N).filter (· ≤ U) ⊆ Ioc 0 ⌊(U : ℝ)⌋₊ := by
    intro n hn; rw [Nat.floor_natCast]; simp only [mem_filter, mem_Icc, mem_Ioc] at hn ⊢; omega
  refine (sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ ↦ vonMangoldt_nonneg).trans ?_
  exact Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg U)

/-- The truncated convolution `H = Λ_U * μ_V` of `S₂`. -/
noncomputable abbrev vaughanH (U V : ℕ) : ArithmeticFunction ℝ :=
  truncate Λ U * truncate (μ : ArithmeticFunction ℝ) V

/-- `S₂ = -∑_{t ≤ N} H(t) ∑_{r ≤ N/t} f(tr)`. -/
lemma S₂_eq (f : ℕ → ℂ) (N U V : ℕ) :
    ∑ n ∈ Icc 1 N, f n * (-((ζ : ArithmeticFunction ℝ) * truncate Λ U *
        truncate (μ : ArithmeticFunction ℝ) V) n : ℂ) =
      -∑ t ∈ Icc 1 N, (vaughanH U V t : ℂ) * ∑ r ∈ Icc 1 (N / t), f (t * r) := by
  have h : ∑ n ∈ Icc 1 N, f n * (-((ζ : ArithmeticFunction ℝ) * truncate Λ U *
        truncate (μ : ArithmeticFunction ℝ) V) n : ℂ) =
      -∑ t ∈ Icc 1 N, (vaughanH U V t : ℂ) * ∑ r ∈ Icc 1 (N / t), f (t * r) * 1 := by
    rw [← sum_mul_sum_divisors f (fun t ↦ (vaughanH U V t : ℂ)) (fun _ ↦ 1), ← sum_neg_distrib]
    refine sum_congr rfl fun n _ ↦ ?_
    rw [mul_assoc, coe_zeta_mul_apply]
    push_cast
    simp [vaughanH]
  simpa only [mul_one] using h

section Character

variable {q : ℕ} [NeZero q]

/-- `S₂'`: `|∑_{t ≤ min(N, U)} H(t) ∑_{r ≤ N/t} χ(tr)| ≤ U log U · 2 √q log q` (Pólya–Vinogradov). -/
lemma norm_S₂'_le {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) (N U V : ℕ) :
    ‖∑ t ∈ (Icc 1 N).filter (· ≤ U), (vaughanH U V t : ℂ) *
        ∑ r ∈ Icc 1 (N / t), χ ((t * r : ℕ) : ZMod q)‖ ≤
      U * Real.log U * (2 * √q * Real.log q) := by
  have hPV : 0 ≤ 2 * √q * Real.log q := by
    have := Real.log_natCast_nonneg q; positivity
  have hlU : 0 ≤ Real.log U := Real.log_natCast_nonneg U
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ t ∈ (Icc 1 N).filter (· ≤ U), ‖(vaughanH U V t : ℂ) *
      ∑ r ∈ Icc 1 (N / t), χ ((t * r : ℕ) : ZMod q)‖ ≤ Real.log U * (2 * √q * Real.log q) := by
    intro t ht
    simp only [mem_filter, mem_Icc] at ht
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have h1 : |vaughanH U V t| ≤ Real.log U :=
      (abs_trunc_mul_trunc_le U V t).1.trans
        (Real.log_le_log (by exact_mod_cast ht.1.1) (by exact_mod_cast ht.2))
    have h2 : ‖∑ r ∈ Icc 1 (N / t), χ ((t * r : ℕ) : ZMod q)‖ ≤ 2 * √q * Real.log q := by
      simp_rw [Nat.cast_mul, map_mul, ← mul_sum, norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (DirichletCharacter.norm_le_one χ _) |>.trans
        (norm_sum_Icc_one_char_le hχ _)
    exact mul_le_mul h1 h2 (norm_nonneg _) hlU
  refine (sum_le_sum hterm).trans ?_
  rw [sum_const, nsmul_eq_mul, ← mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  refine mul_le_mul_of_nonneg_right ?_ hlU
  have : ((Icc 1 N).filter (· ≤ U)).card ≤ U := by
    calc _ ≤ (Icc 1 U).card := card_le_card fun t ht ↦ by
            simp only [mem_filter, mem_Icc] at ht ⊢; omega
      _ = U := by simp
  exact_mod_cast this

/-- The coefficients of `S₂''`: `α_t = H(t) [t > U]`. -/
noncomputable def alphaS₂ (U V : ℕ) (t : ℕ) : ℂ := if U < t then (vaughanH U V t : ℂ) else 0

omit [NeZero q] in
/-- `S₂''` as a bilinear sum. -/
lemma S₂''_eq (χ : DirichletCharacter ℂ q) {N X : ℕ} (hNX : N ≤ X) (U V : ℕ) :
    ∑ t ∈ (Icc 1 N).filter (fun t ↦ ¬ t ≤ U), (vaughanH U V t : ℂ) *
        ∑ r ∈ Icc 1 (N / t), χ ((t * r : ℕ) : ZMod q) =
      ∑ t ∈ Icc 1 X, ∑ r ∈ (Icc 1 X).filter (fun r ↦ t * r ≤ N),
        alphaS₂ U V t * 1 * χ ((t * r : ℕ) : ZMod q) := by
  have h1 : ∀ t ∈ Icc 1 X, ∑ r ∈ (Icc 1 X).filter (fun r ↦ t * r ≤ N),
      alphaS₂ U V t * 1 * χ ((t * r : ℕ) : ZMod q) =
      alphaS₂ U V t * ∑ r ∈ Icc 1 (N / t), χ ((t * r : ℕ) : ZMod q) := by
    intro t ht
    rw [filter_Icc_mul_le (mem_Icc.1 ht).1 hNX, mul_sum]
    simp only [mul_one]
  rw [sum_congr rfl h1]
  rw [← sum_subset (Icc_subset_Icc_right hNX) fun t ht ht' ↦ ?_]
  · rw [sum_filter]
    refine sum_congr rfl fun t _ ↦ ?_
    simp only [alphaS₂, not_le]
    split_ifs <;> simp
  · have : N / t = 0 := by
      simp only [mem_Icc] at ht ht'
      exact Nat.div_eq_of_lt (by omega)
    rw [this, Icc_eq_empty (by omega), sum_empty, mul_zero]

/-- `S₃` for a nonprincipal character: `|S₃| ≤ (log N) V · 4 √q log q`. -/
lemma norm_S₃_char_le {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) (N V : ℕ) :
    ‖∑ n ∈ Icc 1 N, χ n * ((log * truncate (μ : ArithmeticFunction ℝ) V) n : ℂ)‖ ≤
      Real.log N * (V * (4 * √q * Real.log q)) := by
  have hPV : 0 ≤ 4 * √q * Real.log q := by
    have := Real.log_natCast_nonneg q; positivity
  have h := norm_S₃_le (fun n ↦ χ n) N V (fun _ ↦ 4 * √q * Real.log q) (fun _ ↦ hPV)
    (fun d _ w hw ↦ by
      simp only [Nat.cast_mul, map_mul, ← mul_sum, norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (DirichletCharacter.norm_le_one χ _) |>.trans
        (norm_sum_Icc_char_le hχ (mem_Icc.1 hw).1 _))
  simpa [sum_const, Nat.card_Icc, nsmul_eq_mul, mul_assoc] using h

/-- The coefficients of `S₄`. -/
noncomputable def alphaS₄ (X U V : ℕ) (m : ℕ) : ℂ :=
  if U < m ∧ m ≤ X / V then (Λ m : ℂ) else 0

/-- The coefficients of `S₄`: `β_k = ∑_{d ∣ k, d ≤ V} μ(d)` for `V < k ≤ X`. -/
noncomputable def betaS₄ (X V : ℕ) (k : ℕ) : ℂ :=
  if V < k ∧ k ≤ X then ((∑ d ∈ k.divisors.filter (· ≤ V), (μ d : ℝ) : ℝ) : ℂ) else 0

omit [NeZero q] in
/-- `S₄` as a bilinear sum. -/
lemma S₄_eq_bilinear (χ : DirichletCharacter ℂ q) {N X : ℕ} (hNX : N ≤ X) (U : ℕ) {V : ℕ}
    (hV : 1 ≤ V) :
    ∑ n ∈ Icc 1 N, χ n * (((Λ - truncate Λ U) *
        (1 - (ζ : ArithmeticFunction ℝ) * truncate (μ : ArithmeticFunction ℝ) V)) n : ℂ) =
      -∑ m ∈ Icc 1 X, ∑ k ∈ (Icc 1 X).filter (fun k ↦ m * k ≤ N),
        alphaS₄ X U V m * betaS₄ X V k * χ ((m * k : ℕ) : ZMod q) := by
  rw [S₄_eq (fun n ↦ χ n) N U V hV, neg_inj]
  set c : ℕ → ℂ := fun k ↦ ((∑ d ∈ k.divisors.filter (· ≤ V), (μ d : ℝ) : ℝ) : ℂ) with hc
  set G : ℕ → ℂ := fun m ↦ ∑ k ∈ Ioc V (N / m), c k * χ ((m * k : ℕ) : ZMod q) with hG
  have h1 : ∀ m ∈ Icc 1 X, ∑ k ∈ (Icc 1 X).filter (fun k ↦ m * k ≤ N),
      alphaS₄ X U V m * betaS₄ X V k * χ ((m * k : ℕ) : ZMod q) = alphaS₄ X U V m * G m := by
    intro m hm
    have hm1 := (mem_Icc.1 hm).1
    rw [filter_Icc_mul_le hm1 hNX, hG, mul_sum]
    have hsub : Ioc V (N / m) = (Icc 1 (N / m)).filter (fun k ↦ V < k ∧ k ≤ X) := by
      ext k
      simp only [mem_Ioc, mem_filter, mem_Icc]
      have : N / m ≤ X := (Nat.div_le_self N m).trans hNX
      omega
    rw [hsub, sum_filter]
    refine sum_congr rfl fun k _ ↦ ?_
    simp only [betaS₄, hc]
    split_ifs <;> ring
  rw [sum_congr rfl h1]
  set S := (Ioc U N).filter (fun m ↦ m ≤ X / V) with hS
  have hGz : ∀ m, X / V < m → G m = 0 := by
    intro m hm
    have hm0 : 0 < m := lt_of_le_of_lt (Nat.zero_le _) hm
    have h2 : X < m * V := (Nat.div_lt_iff_lt_mul (by omega)).1 hm
    have h3 : N / m < V := (Nat.div_lt_iff_lt_mul hm0).2 (by nlinarith)
    simp only [hG]
    rw [Ioc_eq_empty (by omega), sum_empty]
  have hGz' : ∀ m, N < m → G m = 0 := by
    intro m hm
    simp only [hG]
    rw [Nat.div_eq_of_lt hm, Ioc_eq_empty (by omega), sum_empty]
  have eR : ∑ m ∈ Ioc U N, (Λ m : ℂ) * G m = ∑ m ∈ S, (Λ m : ℂ) * G m := by
    refine (sum_subset (filter_subset _ _) fun m hm hmS ↦ ?_).symm
    have : X / V < m := by
      by_contra h; exact hmS (mem_filter.2 ⟨hm, by omega⟩)
    rw [hGz m this, mul_zero]
  have eL : ∑ m ∈ Icc 1 X, alphaS₄ X U V m * G m = ∑ m ∈ S, (Λ m : ℂ) * G m := by
    have : ∑ m ∈ Icc 1 X, alphaS₄ X U V m * G m =
        ∑ m ∈ (Icc 1 X).filter (fun m ↦ U < m ∧ m ≤ X / V), (Λ m : ℂ) * G m := by
      rw [sum_filter]
      refine sum_congr rfl fun m _ ↦ ?_
      simp only [alphaS₄]
      split_ifs <;> simp
    rw [this]
    refine (sum_subset (fun m hm ↦ ?_) fun m hm hmS ↦ ?_).symm
    · simp only [hS, mem_filter, mem_Ioc, mem_Icc] at hm ⊢
      exact ⟨⟨by omega, by omega⟩, hm.1.1, hm.2⟩
    · simp only [hS, mem_filter, mem_Ioc, mem_Icc] at hm hmS
      have : N < m := by
        by_contra h; exact hmS ⟨⟨hm.2.1, by omega⟩, hm.2.2⟩
      rw [hGz' m this, mul_zero]
  rw [eL, eR]

end Character

/-! ### Mean squares of the coefficients -/

lemma norm_alphaS₂_le {U V X : ℕ} (hUV : U * V ≤ X) (t : ℕ) :
    ‖alphaS₂ U V t‖ ≤ Real.log X := by
  have hX : 0 ≤ Real.log X := Real.log_natCast_nonneg X
  simp only [alphaS₂]
  split_ifs with h
  · rw [Complex.norm_real, Real.norm_eq_abs]
    obtain ⟨h1, h2⟩ := abs_trunc_mul_trunc_le U V t
    by_cases ht : U * V < t
    · rw [show vaughanH U V t = 0 from h2 ht, abs_zero]; exact hX
    · refine h1.trans (Real.log_le_log (by exact_mod_cast (show 0 < t by omega)) ?_)
      exact_mod_cast (show t ≤ X by omega)
  · simpa using hX

lemma sum_norm_alphaS₂_sq_le {U V X : ℕ} (hUV : U * V ≤ X) (T : ℕ) :
    ∑ t ∈ Icc 1 T, ‖alphaS₂ U V t‖ ^ 2 ≤ Real.log X ^ 2 * T := by
  calc _ ≤ ∑ t ∈ Icc 1 T, Real.log X ^ 2 :=
        sum_le_sum fun t _ ↦ pow_le_pow_left₀ (norm_nonneg _) (norm_alphaS₂_le hUV t) 2
    _ = _ := by rw [sum_const, Nat.card_Icc, nsmul_eq_mul]; push_cast; ring

lemma alphaS₂_eq_zero_of_le {U V t : ℕ} (h : t ≤ U) : alphaS₂ U V t = 0 := by
  simp [alphaS₂, not_lt.2 h]

lemma alphaS₂_eq_zero_of_lt {U V t : ℕ} (h : U * V < t) : alphaS₂ U V t = 0 := by
  simp only [alphaS₂]
  split_ifs
  · rw [show vaughanH U V t = 0 from (abs_trunc_mul_trunc_le U V t).2 h]; simp
  · rfl

lemma sum_norm_alphaS₄_sq_le (X U V T : ℕ) :
    ∑ t ∈ Icc 1 T, ‖alphaS₄ X U V t‖ ^ 2 ≤ (Real.log 4 + 4) * Real.log X * T := by
  have hX : 0 ≤ Real.log X := Real.log_natCast_nonneg X
  set m := min T X with hm
  have h1 : ∑ t ∈ Icc 1 T, ‖alphaS₄ X U V t‖ ^ 2 ≤ ∑ t ∈ Icc 1 m, Λ t ^ 2 := by
    rw [← sum_subset (Icc_subset_Icc_right (min_le_left T X)) fun t ht ht' ↦ ?_]
    · refine sum_le_sum fun t ht ↦ ?_
      simp only [alphaS₄]
      split_ifs
      · rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
      · simp
    · simp only [mem_Icc] at ht ht'
      have : X < t := by omega
      have h0 : ¬ (U < t ∧ t ≤ X / V) := fun h ↦ by
        have := Nat.div_le_self X V; omega
      simp [alphaS₄, h0]
  refine h1.trans ?_
  rcases Nat.eq_zero_or_pos m with h0 | hpos
  · rw [h0]; simp; positivity
  have hmr : (1:ℝ) ≤ m := by exact_mod_cast hpos
  have h2 := sum_vonMangoldt_sq_le hmr
  rw [Nat.floor_natCast] at h2
  refine h2.trans ?_
  have hmT : (m:ℝ) ≤ T := by exact_mod_cast min_le_left T X
  have hmX : Real.log m ≤ Real.log X :=
    Real.log_le_log (by linarith) (by exact_mod_cast min_le_right T X)
  have hlm : 0 ≤ Real.log m := Real.log_nonneg hmr
  have hc : 0 ≤ Real.log 4 + 4 := by positivity
  calc (Real.log 4 + 4) * m * Real.log m ≤ (Real.log 4 + 4) * T * Real.log X := by gcongr
    _ = _ := by ring

lemma alphaS₄_eq_zero_of_le {X U V t : ℕ} (h : t ≤ U) : alphaS₄ X U V t = 0 := by
  simp only [alphaS₄]; split_ifs with h' <;> [omega; rfl]

lemma alphaS₄_eq_zero_of_lt {X U V t : ℕ} (h : X / V < t) : alphaS₄ X U V t = 0 := by
  simp only [alphaS₄]; split_ifs with h' <;> [omega; rfl]

lemma sum_norm_betaS₄_sq_le : ∃ C : ℝ, 0 < C ∧ ∀ X V K : ℕ, 1 ≤ X →
    ∑ k ∈ Icc 1 K, ‖betaS₄ X V k‖ ^ 2 ≤ C * (1 + Real.log X) ^ 3 * K := by
  obtain ⟨C, hC, hd⟩ := sum_card_divisors_sq_le
  refine ⟨C, hC, fun X V K hX ↦ ?_⟩
  have hlX : 0 ≤ Real.log X := Real.log_natCast_nonneg X
  set m := min K X with hm
  have h1 : ∑ k ∈ Icc 1 K, ‖betaS₄ X V k‖ ^ 2 ≤ ∑ k ∈ Icc 1 m, ((k.divisors.card : ℝ)) ^ 2 := by
    rw [← sum_subset (Icc_subset_Icc_right (min_le_left K X)) fun k hk hk' ↦ ?_]
    · refine sum_le_sum fun k _ ↦ ?_
      simp only [betaS₄]
      split_ifs
      · rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
        have := abs_sum_moebius_le_card_divisors k V
        exact pow_le_pow_left₀ (abs_nonneg _) this 2 |>.trans' (by rw [sq_abs])
      · simp
    · simp only [mem_Icc] at hk hk'
      have : ¬ (V < k ∧ k ≤ X) := by omega
      simp [betaS₄, this]
  refine h1.trans ?_
  rcases Nat.eq_zero_or_pos m with h0 | hpos
  · rw [h0]; simp; positivity
  refine (hd m hpos).trans ?_
  have hmr : (1:ℝ) ≤ m := by exact_mod_cast hpos
  have hmK : (m:ℝ) ≤ K := by exact_mod_cast min_le_left K X
  have hmX : Real.log m ≤ Real.log X :=
    Real.log_le_log (by linarith) (by exact_mod_cast min_le_right K X)
  have hlm : 0 ≤ Real.log m := Real.log_nonneg hmr
  calc C * m * (1 + Real.log m) ^ 3 ≤ C * K * (1 + Real.log X) ^ 3 := by gcongr
    _ = _ := by ring

end NTKB.Davenport
