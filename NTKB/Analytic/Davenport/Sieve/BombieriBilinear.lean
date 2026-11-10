/- Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license. -/
import NTKB.Analytic.Davenport.Sieve.BilinearSieveSup

/-!
# Dyadic blocks for the type II sums of Bombieri's theorem (Davenport, Chapter 28)

The book applies (E) (`bilinear_sieve_sup`) to the sums `S₄` and `S₂''` after splitting the
variable `m` (resp. `t`) into dyadic ranges `M < m ≤ 2M` (p. 166, (11), (12), (13)). This file does
the splitting once for general coefficients: if `α_t` vanishes outside `(U, T_max]` and
`∑_{t ≤ T} |α_t|² ≤ A T`, `∑_{k ≤ K} |β_k|² ≤ B K`, then

`∑_{q ≤ Q} (q/φ(q)) ∑*_χ |∑_{t, k ≤ X, tk ≤ N(q,χ)} α_t β_k χ(tk)|
  ≪ (AB)^{1/2} (X + Q² X^{1/2} + Q X^{1/2} T_max^{1/2} + Q X U^{-1/2}) (log 2X)²`

for any choice of `N(q, χ) ≤ X`. (In each block the factor `√T_j` is bounded by `√T_max` and
`T_j^{-1/2}` by `U^{-1/2}`; the number of blocks is `≪ log 2X`.)
-/

open Finset Real

namespace NTKB.Davenport

/-- Restricting a double sum over `[1, a] × [1, b]` to `[1, m] × [1, n]` when the summand vanishes
outside. -/
lemma sum_Icc_Icc_restrict {R : Type*} [AddCommMonoid R] (g : ℕ → ℕ → R) {a b m n : ℕ}
    (hm : m ≤ a) (hn : n ≤ b)
    (h : ∀ t k, 1 ≤ t → 1 ≤ k → t ≤ a → k ≤ b → g t k ≠ 0 → t ≤ m ∧ k ≤ n) :
    ∑ t ∈ Icc 1 a, ∑ k ∈ Icc 1 b, g t k = ∑ t ∈ Icc 1 m, ∑ k ∈ Icc 1 n, g t k := by
  symm
  rw [← sum_subset (Icc_subset_Icc_right hm) fun t ht ht' ↦ ?_]
  · refine sum_congr rfl fun t ht ↦ ?_
    refine sum_subset (Icc_subset_Icc_right hn) fun k hk hk' ↦ ?_
    by_contra hne
    have ht := mem_Icc.1 ht; have hk := mem_Icc.1 hk
    exact hk' (mem_Icc.2 ⟨hk.1, (h t k ht.1 hk.1 (ht.2.trans hm) hk.2 hne).2⟩)
  · refine sum_eq_zero fun k hk ↦ ?_
    by_contra hne
    have ht := mem_Icc.1 ht; have hk := mem_Icc.1 hk
    exact ht' (mem_Icc.2 ⟨ht.1, (h t k ht.1 hk.1 ht.2 hk.2 hne).1⟩)

/-- The double sums of `[1, a] × [1, b]` and `[1, c] × [1, d]` agree when the summand vanishes
outside `[1, min a c] × [1, min b d]`. -/
lemma sum_Icc_Icc_eq {R : Type*} [AddCommMonoid R] (g : ℕ → ℕ → R) {a b c d : ℕ}
    (h : ∀ t k, 1 ≤ t → 1 ≤ k → g t k ≠ 0 → t ≤ min a c ∧ k ≤ min b d) :
    ∑ t ∈ Icc 1 a, ∑ k ∈ Icc 1 b, g t k = ∑ t ∈ Icc 1 c, ∑ k ∈ Icc 1 d, g t k := by
  rw [sum_Icc_Icc_restrict g (min_le_left a c) (min_le_left b d)
      fun t k ht hk _ _ hg ↦ h t k ht hk hg,
    sum_Icc_Icc_restrict g (min_le_right a c) (min_le_right b d)
      fun t k ht hk _ _ hg ↦ h t k ht hk hg]

/-- `√(2X)` bookkeeping: `((2T + 3Q²)(K + 3Q²))^{1/2} X^{1/2} ≤ 3 Y` where
`Y = X + Q² X^{1/2} + Q X^{1/2} T_max^{1/2} + Q X U^{-1/2}`, for `T K ≤ X`, `T ≤ T_max`, `K ≤ X/U`. -/
lemma block_sqrt_le {Q X T K Tm U : ℝ} (hQ : 0 ≤ Q) (hX : 0 ≤ X) (hT : 0 ≤ T) (hK : 0 ≤ K)
    (hU : 0 < U) (hTK : T * K ≤ X) (hTm : T ≤ Tm) (hKU : K ≤ X / U) :
    √((2 * T + 3 * Q ^ 2) * (K + 3 * Q ^ 2)) * √X ≤
      3 * (X + Q ^ 2 * √X + Q * √X * √Tm + Q * X / √U) := by
  have hTm0 : 0 ≤ Tm := hT.trans hTm
  set sx := √X with hsx
  set st := √Tm with hst
  set su := √U with hsu
  have hsx2 : sx ^ 2 = X := Real.sq_sqrt hX
  have hst2 : st ^ 2 = Tm := Real.sq_sqrt hTm0
  have hsu2 : su ^ 2 = U := Real.sq_sqrt hU.le
  have hsu0 : 0 < su := Real.sqrt_pos.2 hU
  have hsx0 : 0 ≤ sx := Real.sqrt_nonneg _
  have hst0 : 0 ≤ st := Real.sqrt_nonneg _
  set Y := X + Q ^ 2 * sx + Q * sx * st + Q * X / su with hY
  have hY0 : 0 ≤ Y := by positivity
  rw [← Real.sqrt_mul (by positivity)]
  rw [show 3 * Y = √((3 * Y) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
  refine Real.sqrt_le_sqrt ?_
  -- the inside
  have h1 : (2 * T + 3 * Q ^ 2) * (K + 3 * Q ^ 2) * X ≤
      (2 * X + 6 * Q ^ 2 * Tm + 3 * Q ^ 2 * (X / U) + 9 * Q ^ 4) * X := by
    refine mul_le_mul_of_nonneg_right ?_ hX
    have : 6 * Q ^ 2 * T ≤ 6 * Q ^ 2 * Tm := by gcongr
    have : 3 * Q ^ 2 * K ≤ 3 * Q ^ 2 * (X / U) := by gcongr
    nlinarith
  refine h1.trans ?_
  have e1 : X ^ 2 = X * X := by ring
  have hc : 3 * Q ^ 2 * (X / U) * X = 3 * (Q * X / su) ^ 2 := by
    rw [div_pow, mul_pow, hsu2]; field_simp
  have hd : 6 * Q ^ 2 * Tm * X = 6 * (Q * sx * st) ^ 2 := by
    rw [mul_pow, mul_pow, hsx2, hst2]; ring
  have he : 9 * Q ^ 4 * X = 9 * (Q ^ 2 * sx) ^ 2 := by
    rw [mul_pow, hsx2]; ring
  have hexp : (2 * X + 6 * Q ^ 2 * Tm + 3 * Q ^ 2 * (X / U) + 9 * Q ^ 4) * X =
      2 * X ^ 2 + 6 * (Q * sx * st) ^ 2 + 3 * (Q * X / su) ^ 2 + 9 * (Q ^ 2 * sx) ^ 2 := by
    rw [← hc, ← hd, ← he]; ring
  rw [hexp, hY]
  have ha : 0 ≤ Q ^ 2 * sx := by positivity
  have hb : 0 ≤ Q * sx * st := by positivity
  have hc' : 0 ≤ Q * X / su := by positivity
  nlinarith [mul_nonneg hX ha, mul_nonneg hX hb, mul_nonneg hX hc', mul_nonneg ha hb,
    mul_nonneg ha hc', mul_nonneg hb hc']

open scoped Classical in
/-- One dyadic block `T < t ≤ 2T` (Davenport, p. 166): (E) with `M = 2T`, `N = X/T`. -/
lemma block_sieve_le {Q : ℝ} (hQ : 1 ≤ Q) {X U Tm T : ℕ} (hX : 1 ≤ X) (hU : 1 ≤ U)
    (hUT : U ≤ T) (hTm : T ≤ Tm) (α β : ℕ → ℂ) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hα : ∀ t, α t ≠ 0 → T < t ∧ t ≤ 2 * T)
    (hαs : ∑ t ∈ Icc 1 (2 * T), ‖α t‖ ^ 2 ≤ A * (2 * T))
    (hβ : ∀ K : ℕ, ∑ k ∈ Icc 1 K, ‖β k‖ ^ 2 ≤ B * K)
    (Nf : (q : ℕ) → DirichletCharacter ℂ q → ℕ) (hNf : ∀ q χ, Nf q χ ≤ X) :
    ∑ q ∈ Icc 1 ⌊Q⌋₊, ((q : ℝ) / q.totient) *
        ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ ↦ χ.IsPrimitive),
          ‖∑ t ∈ Icc 1 X, ∑ k ∈ (Icc 1 X).filter (fun k ↦ t * k ≤ Nf q χ),
            α t * β k * χ ((t * k : ℕ) : ZMod q)‖ ≤
      110 * √(A * B) * (X + Q ^ 2 * √X + Q * √X * √Tm + Q * X / √U) * Real.log (2 * X) := by
  have hT1 : 1 ≤ T := hU.trans hUT
  set K := X / T with hK
  have hrw : ∀ q (χ : DirichletCharacter ℂ q),
      ∑ t ∈ Icc 1 X, ∑ k ∈ (Icc 1 X).filter (fun k ↦ t * k ≤ Nf q χ),
        α t * β k * χ ((t * k : ℕ) : ZMod q) =
      ∑ m ∈ Icc 1 (2 * T), ∑ n ∈ (Icc 1 K).filter (fun n ↦ m * n ≤ Nf q χ),
        α m * β n * χ ((m * n : ℕ) : ZMod q) := by
    intro q χ
    simp only [sum_filter]
    refine sum_Icc_Icc_eq _ fun t k ht hk hg ↦ ?_
    by_cases hc : t * k ≤ Nf q χ
    · simp only [hc, ↓reduceIte] at hg
      have hαt : α t ≠ 0 := fun h ↦ hg (by rw [h]; ring)
      obtain ⟨h1, h2⟩ := hα t hαt
      have htk : t * k ≤ X := hc.trans (hNf q χ)
      have htX : t ≤ X := le_trans (Nat.le_mul_of_pos_right t hk) htk
      have hkK : k ≤ K := by
        rw [hK, Nat.le_div_iff_mul_le (by omega)]
        calc k * T ≤ k * t := Nat.mul_le_mul_left k h1.le
          _ = t * k := mul_comm _ _
          _ ≤ X := htk
      have hKX : K ≤ X := Nat.div_le_self _ _
      exact ⟨le_min htX h2, le_min (hkK.trans hKX) hkK⟩
    · simp only [hc, ↓reduceIte] at hg; exact absurd rfl hg
  simp_rw [hrw]
  refine (bilinear_sieve_sup hQ (2 * T) K α β Nf).trans ?_
  have hXr : (1:ℝ) ≤ X := by exact_mod_cast hX
  have hUr : (0:ℝ) < U := by exact_mod_cast hU
  have hTr : (1:ℝ) ≤ T := by exact_mod_cast hT1
  have hUTr : (U:ℝ) ≤ T := by exact_mod_cast hUT
  have hTmr : (T:ℝ) ≤ Tm := by exact_mod_cast hTm
  have hTK : (T:ℝ) * K ≤ X := by
    have : K * T ≤ X := Nat.div_mul_le_self X T
    rw [mul_comm]; exact_mod_cast this
  have hKU : (K:ℝ) ≤ X / U := by
    calc (K:ℝ) ≤ X / T := Nat.cast_div_le
      _ ≤ X / U := div_le_div_of_nonneg_left (by positivity) hUr hUTr
  set a2 := ∑ t ∈ Icc 1 (2 * T), ‖α t‖ ^ 2
  set b2 := ∑ k ∈ Icc 1 K, ‖β k‖ ^ 2
  have hb2 : b2 ≤ B * K := hβ K
  have ha2 : a2 ≤ A * (2 * T) := hαs
  have hL0 : 0 ≤ Real.log (2 * X) := Real.log_nonneg (by linarith)
  set Y := (X : ℝ) + Q ^ 2 * √X + Q * √X * √Tm + Q * X / √U with hY
  have hY0 : 0 ≤ Y := by positivity
  have hP := block_sqrt_le (Q := Q) (X := X) (T := T) (K := K) (Tm := Tm) (U := U) (by linarith)
    (by linarith) (by linarith) (Nat.cast_nonneg _) hUr hTK hTmr hKU
  have hsq : √a2 * √b2 ≤ √2 * √(A * B) * √X := by
    rw [← Real.sqrt_mul (by positivity), ← Real.sqrt_mul (by positivity),
      ← Real.sqrt_mul (by positivity)]
    refine Real.sqrt_le_sqrt ?_
    calc a2 * b2 ≤ (A * (2 * T)) * (B * K) :=
          mul_le_mul ha2 hb2 (by positivity) (by positivity)
      _ = 2 * (A * B) * (T * K) := by ring
      _ ≤ 2 * (A * B) * X := by gcongr
  have hlog : Real.log (2 * ((2 * T : ℕ) : ℝ) * K) ≤ 2 * Real.log (2 * X) := by
    rcases Nat.eq_zero_or_pos K with h0 | hpos
    · rw [h0]; simp; linarith
    have hKr : (1:ℝ) ≤ K := by exact_mod_cast hpos
    rw [← Real.log_rpow (by positivity)]
    refine Real.log_le_log (by positivity) ?_
    push_cast
    calc 2 * (2 * (T:ℝ)) * K = 4 * (T * K) := by ring
      _ ≤ 4 * X := by gcongr
      _ ≤ (2 * X) ^ (2:ℝ) := by rw [Real.rpow_two]; nlinarith
  have hs2 : √2 ≤ 1.415 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hAB : 0 ≤ √(A * B) := Real.sqrt_nonneg _
  have hlogpos : 0 ≤ Real.log (2 * (2 * (T:ℝ)) * K) := by
    rcases Nat.eq_zero_or_pos K with h0 | hpos
    · rw [h0]; simp
    · have hKr : (1:ℝ) ≤ K := by exact_mod_cast hpos
      exact Real.log_nonneg (by nlinarith)
  push_cast
  calc 12 * √((2 * (T:ℝ) + 3 * Q ^ 2) * (K + 3 * Q ^ 2)) * √a2 * √b2 *
        Real.log (2 * (2 * (T:ℝ)) * K)
      = 12 * √((2 * (T:ℝ) + 3 * Q ^ 2) * (K + 3 * Q ^ 2)) * (√a2 * √b2) *
        Real.log (2 * (2 * (T:ℝ)) * K) := by ring
    _ ≤ 12 * √((2 * (T:ℝ) + 3 * Q ^ 2) * (K + 3 * Q ^ 2)) * (√2 * √(A * B) * √X) *
        (2 * Real.log (2 * X)) := by
          have := hlog; push_cast at this
          gcongr
    _ = 24 * √2 * √(A * B) * (√((2 * (T:ℝ) + 3 * Q ^ 2) * (K + 3 * Q ^ 2)) * √X) *
        Real.log (2 * X) := by ring
    _ ≤ 24 * 1.415 * √(A * B) * (3 * Y) * Real.log (2 * X) := by gcongr
    _ ≤ 110 * √(A * B) * Y * Real.log (2 * X) := by
        have : 0 ≤ √(A * B) * Y * Real.log (2 * X) := by positivity
        nlinarith

/-- `J + 1 ≤ 3 log 2X` for `J = ⌊log₂ X⌋`. -/
lemma log_two_add_one_le {X : ℕ} (hX : 1 ≤ X) :
    ((Nat.log 2 X : ℕ) : ℝ) + 1 ≤ 3 * Real.log (2 * X) := by
  have hXr : (1:ℝ) ≤ X := by exact_mod_cast hX
  have hpow : 2 ^ Nat.log 2 X ≤ X := Nat.pow_log_le_self 2 (by omega)
  have h1 : ((Nat.log 2 X : ℕ) : ℝ) * Real.log 2 ≤ Real.log X := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by positivity) (by exact_mod_cast hpow)
  have h2 : Real.log X ≤ Real.log (2 * X) := Real.log_le_log (by positivity) (by linarith)
  have h3 : Real.log 2 ≤ Real.log (2 * X) := Real.log_le_log (by norm_num) (by linarith)
  have hl2 := Real.log_two_gt_d9
  have hJ : (0:ℝ) ≤ (Nat.log 2 X : ℕ) := Nat.cast_nonneg _
  nlinarith

open scoped Classical in
/-- **Dyadic splitting for (E)** (Davenport, Ch. 28, p. 166): if `α_t = 0` unless
`U < t ≤ T_max`, `∑_{t ≤ T} |α_t|² ≤ A T` and `∑_{k ≤ K} |β_k|² ≤ B K`, then for any choice
`N(q, χ) ≤ X`,
`∑_{q ≤ Q} (q/φ(q)) ∑*_χ |∑_{t, k ≤ X, tk ≤ N(q,χ)} α_t β_k χ(tk)|
  ≤ 330 (AB)^{1/2} (X + Q² X^{1/2} + Q X^{1/2} T_max^{1/2} + Q X U^{-1/2}) (log 2X)²`. -/
@[kb "davenport1980" "Ch 28, p. 166"]
theorem dyadic_bilinear_sieve {Q : ℝ} (hQ : 1 ≤ Q) {X U Tm : ℕ} (hX : 1 ≤ X) (hU : 1 ≤ U)
    (α β : ℕ → ℂ) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hαU : ∀ t, t ≤ U → α t = 0) (hαT : ∀ t, Tm < t → α t = 0)
    (hαs : ∀ T : ℕ, ∑ t ∈ Icc 1 T, ‖α t‖ ^ 2 ≤ A * T)
    (hβ : ∀ K : ℕ, ∑ k ∈ Icc 1 K, ‖β k‖ ^ 2 ≤ B * K)
    (Nf : (q : ℕ) → DirichletCharacter ℂ q → ℕ) (hNf : ∀ q χ, Nf q χ ≤ X) :
    ∑ q ∈ Icc 1 ⌊Q⌋₊, ((q : ℝ) / q.totient) *
        ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ ↦ χ.IsPrimitive),
          ‖∑ t ∈ Icc 1 X, ∑ k ∈ (Icc 1 X).filter (fun k ↦ t * k ≤ Nf q χ),
            α t * β k * χ ((t * k : ℕ) : ZMod q)‖ ≤
      330 * √(A * B) * (X + Q ^ 2 * √X + Q * √X * √Tm + Q * X / √U) *
        Real.log (2 * X) ^ 2 := by
  set J := Nat.log 2 X with hJ
  set prim : (q : ℕ) → Finset (DirichletCharacter ℂ q) :=
    fun q ↦ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ ↦ χ.IsPrimitive) with hprim
  set w : ℕ → ℝ := fun q ↦ (q : ℝ) / q.totient with hw
  have hw0 : ∀ q, 0 ≤ w q := fun q ↦ by positivity
  set αj : ℕ → ℕ → ℂ := fun j t ↦ if 2 ^ j * U < t ∧ t ≤ 2 ^ (j + 1) * U then α t else 0
    with hαj
  set inner : (ℕ → ℂ) → (q : ℕ) → DirichletCharacter ℂ q → ℂ := fun a q χ ↦
    ∑ t ∈ Icc 1 X, ∑ k ∈ (Icc 1 X).filter (fun k ↦ t * k ≤ Nf q χ),
      a t * β k * χ ((t * k : ℕ) : ZMod q) with hinner
  -- the decomposition of `α`
  have hdecomp : ∀ t ∈ Icc 1 X, α t = ∑ j ∈ range (J + 1), αj j t := by
    intro t ht
    have ht := mem_Icc.1 ht
    set f : ℕ → ℂ := fun j ↦ if t ≤ 2 ^ j * U then α t else 0 with hf
    have hstep : ∀ j, f (j + 1) - f j = αj j t := by
      intro j
      have hmono : 2 ^ j * U ≤ 2 ^ (j + 1) * U := by
        rw [pow_succ]; nlinarith [Nat.one_le_two_pow (n := j)]
      simp only [hf, hαj]
      by_cases h1 : t ≤ 2 ^ j * U
      · rw [if_pos h1, if_pos (h1.trans hmono), if_neg (by omega), sub_self]
      · by_cases h2 : t ≤ 2 ^ (j + 1) * U
        · rw [if_pos h2, if_neg h1, if_pos ⟨by omega, h2⟩, sub_zero]
        · rw [if_neg h2, if_neg h1, if_neg (by omega), sub_zero]
    have htop : f (J + 1) = α t := by
      have hlt : X < 2 ^ (J + 1) := Nat.lt_pow_succ_log_self (by norm_num) X
      have : t ≤ 2 ^ (J + 1) * U := by nlinarith
      simp only [hf, if_pos this]
    have hbot : f 0 = 0 := by
      simp only [hf, pow_zero, one_mul]
      split_ifs with h
      · exact hαU t h
      · rfl
    rw [← sum_congr rfl fun j _ ↦ hstep j, sum_range_sub, htop, hbot, sub_zero]
  have hsplit : ∀ q (χ : DirichletCharacter ℂ q),
      inner α q χ = ∑ j ∈ range (J + 1), inner (αj j) q χ := by
    intro q χ
    simp only [hinner]
    calc _ = ∑ t ∈ Icc 1 X, ∑ k ∈ (Icc 1 X).filter (fun k ↦ t * k ≤ Nf q χ),
          ∑ j ∈ range (J + 1), αj j t * β k * χ ((t * k : ℕ) : ZMod q) := by
          refine sum_congr rfl fun t ht ↦ sum_congr rfl fun k _ ↦ ?_
          rw [hdecomp t ht, sum_mul, sum_mul]
      _ = ∑ t ∈ Icc 1 X, ∑ j ∈ range (J + 1), ∑ k ∈ (Icc 1 X).filter (fun k ↦ t * k ≤ Nf q χ),
          αj j t * β k * χ ((t * k : ℕ) : ZMod q) := sum_congr rfl fun t _ ↦ sum_comm
      _ = _ := sum_comm
  set Y := (X : ℝ) + Q ^ 2 * √X + Q * √X * √Tm + Q * X / √U with hY
  have hY0 : 0 ≤ Y := by positivity
  have hL0 : 0 ≤ Real.log (2 * X) := Real.log_nonneg (by
    have : (1:ℝ) ≤ X := by exact_mod_cast hX
    linarith)
  -- one block
  have hblock : ∀ j ∈ range (J + 1), ∑ q ∈ Icc 1 ⌊Q⌋₊, w q * ∑ χ ∈ prim q, ‖inner (αj j) q χ‖ ≤
      110 * √(A * B) * Y * Real.log (2 * X) := by
    intro j _
    by_cases hTj : 2 ^ j * U ≤ Tm
    · refine block_sieve_le hQ hX hU (T := 2 ^ j * U) ?_ hTj (αj j) β hA hB ?_ ?_ hβ Nf hNf
      · exact Nat.le_mul_of_pos_left U (Nat.two_pow_pos j)
      · intro t ht
        simp only [hαj] at ht
        split_ifs at ht with h
        · exact ⟨h.1, by rw [pow_succ] at h; linarith [h.2]⟩
        · exact absurd rfl ht
      · calc ∑ t ∈ Icc 1 (2 * (2 ^ j * U)), ‖αj j t‖ ^ 2
            ≤ ∑ t ∈ Icc 1 (2 * (2 ^ j * U)), ‖α t‖ ^ 2 := by
              refine sum_le_sum fun t _ ↦ ?_
              simp only [hαj]
              split_ifs
              · exact le_rfl
              · simp
          _ ≤ A * ((2 * (2 ^ j * U) : ℕ) : ℝ) := hαs _
          _ = A * (2 * ((2 ^ j * U : ℕ) : ℝ)) := by push_cast; ring
    · have hz : ∀ t, αj j t = 0 := by
        intro t
        simp only [hαj]
        split_ifs with h
        · exact hαT t (by omega)
        · rfl
      have : ∀ q (χ : DirichletCharacter ℂ q), inner (αj j) q χ = 0 := by
        intro q χ
        simp only [hinner, hz, zero_mul, sum_const_zero]
      simp only [this, norm_zero, sum_const_zero, mul_zero]
      positivity
  calc ∑ q ∈ Icc 1 ⌊Q⌋₊, w q * ∑ χ ∈ prim q, ‖inner α q χ‖
      ≤ ∑ q ∈ Icc 1 ⌊Q⌋₊, w q * ∑ χ ∈ prim q, ∑ j ∈ range (J + 1), ‖inner (αj j) q χ‖ := by
        refine sum_le_sum fun q _ ↦ mul_le_mul_of_nonneg_left (sum_le_sum fun χ _ ↦ ?_) (hw0 q)
        rw [hsplit q χ]; exact norm_sum_le _ _
    _ = ∑ j ∈ range (J + 1), ∑ q ∈ Icc 1 ⌊Q⌋₊, w q * ∑ χ ∈ prim q, ‖inner (αj j) q χ‖ := by
        rw [sum_comm]
        refine sum_congr rfl fun q _ ↦ ?_
        rw [sum_comm, mul_sum]
    _ ≤ ∑ j ∈ range (J + 1), 110 * √(A * B) * Y * Real.log (2 * X) := sum_le_sum hblock
    _ = ((J : ℝ) + 1) * (110 * √(A * B) * Y * Real.log (2 * X)) := by
        rw [sum_const, card_range, nsmul_eq_mul]; push_cast; ring
    _ ≤ (3 * Real.log (2 * X)) * (110 * √(A * B) * Y * Real.log (2 * X)) :=
        mul_le_mul_of_nonneg_right (log_two_add_one_le hX) (by positivity)
    _ = _ := by ring

end NTKB.Davenport
