/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Davenport.Zeros.LZeroCountImprimitive

/-!
# The zeros of the Euler factors of an imprimitive `L(s, χ)`

**Davenport, Ch. 16, p. 113 (row 16-10).** If `χ` mod `q` is induced by `χ₁` mod `q₁`, then
`L(s, χ) = L(s, χ₁) ∏_{p ∣ q} (1 - χ₁(p) p^{-s})`. A factor with `p ∤ q₁` vanishes exactly at the
points `s = i(arg χ₁(p) + 2πk)/log p`, `k ∈ ℤ`, on the line `σ = 0`, spaced `2π/log p` apart; there
are at most `T log p/π + 1` of them with `|t| < T`. So `L(s, χ)` has, besides the zeros of `L(s, χ₁)`,
extra zeros on `σ = 0` only, at most `(T/π) log q + ω(q)` of them (counted over the factors) with
`|t| < T`.
-/

open Filter Topology Complex Set DirichletCharacter
open scoped Real

namespace NTKB

/-- **Davenport, Ch. 16, p. 113 (row 16-10)**: for a prime `p` and `|c| = 1`, `1 - c p^{-s} = 0`
exactly at `s = i(arg c + 2πk)/log p`, `k ∈ ℤ`. -/
@[kb "davenport1980" "Ch 16, p. 113"]
theorem Davenport.one_sub_mul_cpow_eq_zero_iff {p : ℕ} (hp : p.Prime) {c : ℂ} (hc : ‖c‖ = 1)
    {s : ℂ} : 1 - c * (p : ℂ) ^ (-s) = 0 ↔
      ∃ k : ℤ, s = I * ((c.arg + 2 * π * k : ℝ) : ℂ) / (Real.log p : ℂ) := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hc' : c = exp (c.arg * I) := by
    have := Complex.norm_mul_exp_arg_mul_I c
    rw [hc] at this
    simpa using this.symm
  have hlog : Complex.log (p : ℂ) = (Real.log p : ℂ) := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_log (Nat.cast_nonneg _)]
  have hL : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hLc : (Real.log p : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  have h1 : c * (p : ℂ) ^ (-s) = exp (c.arg * I + -s * Real.log p) := by
    rw [Complex.cpow_def_of_ne_zero hp0, hlog, exp_add, ← hc', mul_comm (-s)]
  rw [h1, sub_eq_zero, eq_comm, Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨-n, ?_⟩
    rw [eq_div_iff hLc]
    push_cast
    rw [hlog]
    linear_combination (-1 : ℂ) * hn
  · rintro ⟨k, hk⟩
    refine ⟨-k, ?_⟩
    have h2 : s * (Real.log p : ℂ) = I * ((c.arg + 2 * π * k : ℝ) : ℂ) := by
      rw [hk]; exact div_mul_cancel₀ _ hLc
    push_cast at h2 ⊢
    linear_combination (-1 : ℂ) * h2

/-- The zeros of `1 - c p^{-s}` lie on `σ = 0`. -/
lemma re_eq_zero_of_one_sub_mul_cpow_eq_zero {p : ℕ} (hp : p.Prime) {c : ℂ} (hc : ‖c‖ = 1)
    {s : ℂ} (hs : 1 - c * (p : ℂ) ^ (-s) = 0) : s.re = 0 := by
  rw [Davenport.one_sub_mul_cpow_eq_zero_iff hp hc] at hs
  obtain ⟨k, hk⟩ := hs
  rw [hk, Complex.div_ofReal_re]
  simp

/-- **Davenport, Ch. 16, p. 113 (row 16-10)**: `1 - c p^{-s}` has at most `T log p/π + 1` zeros
with `|t| < T`. -/
@[kb "davenport1980" "Ch 16, p. 113"]
theorem Davenport.ncard_one_sub_mul_cpow_zeros_le {p : ℕ} (hp : p.Prime) {c : ℂ} (hc : ‖c‖ = 1)
    (T : ℝ) (hT : 0 ≤ T) :
    {s : ℂ | 1 - c * (p : ℂ) ^ (-s) = 0 ∧ |s.im| < T}.Finite ∧
      ({s : ℂ | 1 - c * (p : ℂ) ^ (-s) = 0 ∧ |s.im| < T}.ncard : ℝ) ≤ T * Real.log p / π + 1 := by
  have hL : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hLc : (Real.log p : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  set a : ℝ := (-T * Real.log p - c.arg) / (2 * π) with ha
  set b : ℝ := (T * Real.log p - c.arg) / (2 * π) with hb
  set g : ℤ → ℂ := fun k ↦ I * ((c.arg + 2 * π * k : ℝ) : ℂ) / (Real.log p : ℂ) with hg
  have hsub : {s : ℂ | 1 - c * (p : ℂ) ^ (-s) = 0 ∧ |s.im| < T} ⊆
      g '' ((Finset.Icc (⌊a⌋ + 1) (⌈b⌉ - 1) : Finset ℤ) : Set ℤ) := by
    rintro s ⟨hs, hsT⟩
    obtain ⟨k, hk⟩ := (Davenport.one_sub_mul_cpow_eq_zero_iff hp hc).mp hs
    refine ⟨k, ?_, hk.symm⟩
    have him : s.im = (c.arg + 2 * π * k) / Real.log p := by
      rw [hk, Complex.div_ofReal_im]
      simp
    rw [him, abs_lt, lt_div_iff₀ hL, div_lt_iff₀ hL] at hsT
    have hpi := Real.pi_pos
    have h1 : a < k := by
      rw [ha, div_lt_iff₀ (by positivity)]
      nlinarith [hsT.1]
    have h2 : (k : ℝ) < b := by
      rw [hb, lt_div_iff₀ (by positivity)]
      nlinarith [hsT.2]
    have h3 : ⌊a⌋ + 1 ≤ k := by
      have := Int.floor_lt.mpr (show a < k from h1)
      omega
    have h4 : k ≤ ⌈b⌉ - 1 := by
      have := Int.lt_ceil.mpr (show (k : ℝ) < b from h2)
      omega
    simp [h3, h4]
  have hfin : (g '' ((Finset.Icc (⌊a⌋ + 1) (⌈b⌉ - 1) : Finset ℤ) : Set ℤ)).Finite :=
    (Finset.finite_toSet _).image _
  refine ⟨hfin.subset hsub, ?_⟩
  have hcard := (Set.ncard_le_ncard hsub hfin).trans
    (Set.ncard_image_le (Finset.finite_toSet _))
  rw [Set.ncard_coe_finset, Int.card_Icc] at hcard
  have hcard' : (({s : ℂ | 1 - c * (p : ℂ) ^ (-s) = 0 ∧ |s.im| < T}.ncard : ℕ) : ℝ) ≤ (((⌈b⌉ - 1 + 1 - (⌊a⌋ + 1)).toNat : ℕ) : ℝ) := by
    exact_mod_cast hcard
  refine hcard'.trans ?_
  have hba : b - a = T * Real.log p / π := by
    rw [ha, hb]
    field_simp
    ring
  have hfl := Int.lt_floor_add_one a
  have hce := Int.ceil_lt_add_one b
  have hpos : 0 ≤ T * Real.log p / π := by positivity
  have hle : ((⌈b⌉ - 1 + 1 - (⌊a⌋ + 1) : ℤ) : ℝ) ≤ T * Real.log p / π + 1 := by
    push_cast
    have := Int.floor_le a
    linarith
  rcases le_total 0 (⌈b⌉ - 1 + 1 - (⌊a⌋ + 1)) with h | h
  · rw [← Int.cast_natCast, Int.toNat_of_nonneg h]
    exact hle
  · rw [Int.toNat_of_nonpos h]
    simp
    linarith

/-- **Davenport, Ch. 16, p. 113 (row 16-10)**: for `χ` induced by `χ₁` (`M ∣ N`) and `σ ≥ 0`,
`s ≠ 1`, `L(s, χ) = 0` exactly when `L(s, χ₁) = 0` or `s` is a zero of an Euler factor
`1 - χ₁(p) p^{-s}`, `p ∣ N`, `p ∤ M`; the latter lie on `σ = 0`. -/
@[kb "davenport1980" "Ch 16, p. 113"]
theorem Davenport.LFunction_changeLevel_eq_zero_iff {M N : ℕ} [NeZero M] [NeZero N] (hMN : M ∣ N)
    (χ : DirichletCharacter ℂ M) {s : ℂ} (hs1 : s ≠ 1) :
    LFunction (changeLevel hMN χ) s = 0 ↔
      LFunction χ s = 0 ∨ ∃ p ∈ N.primeFactors, ¬ p ∣ M ∧ 1 - χ p * (p : ℂ) ^ (-s) = 0 := by
  have hU := LFunction_changeLevel hMN χ (Or.inr hs1)
  rw [hU, mul_eq_zero]
  apply or_congr_right
  rw [Finset.prod_eq_zero_iff]
  constructor
  · rintro ⟨p, hp, h⟩
    refine ⟨p, hp, ?_, h⟩
    intro hpM
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hnu : ¬ IsUnit (p : ZMod M) := by
      rw [ZMod.isUnit_iff_coprime]
      intro hco
      have := Nat.Coprime.eq_one_of_dvd hco hpM
      exact hpp.one_lt.ne' this
    rw [MulChar.map_nonunit χ hnu] at h
    simp at h
  · rintro ⟨p, hp, _, h⟩
    exact ⟨p, hp, h⟩

/-- **Davenport, Ch. 16, p. 113 (row 16-10)**: the zeros with `|t| < T` of all the Euler factors
`1 - χ₁(p) p^{-s}`, `p ∣ N`, number at most `(T/π) log N + ω(N)` (each factor counted
separately). -/
@[kb "davenport1980" "Ch 16, p. 113"]
theorem Davenport.sum_ncard_eulerFactor_zeros_le {M N : ℕ} [NeZero M] [NeZero N]
    (χ : DirichletCharacter ℂ M) (T : ℝ) (hT : 0 ≤ T) :
    (∑ p ∈ N.primeFactors,
      ({s : ℂ | 1 - χ p * (p : ℂ) ^ (-s) = 0 ∧ |s.im| < T}.ncard : ℝ)) ≤
        T * Real.log N / π + N.primeFactors.card := by
  have hone : ∀ p ∈ N.primeFactors,
      ({s : ℂ | 1 - χ p * (p : ℂ) ^ (-s) = 0 ∧ |s.im| < T}.ncard : ℝ) ≤
        T * Real.log p / π + 1 := by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hL : 0 < Real.log p := Real.log_pos (by exact_mod_cast hpp.one_lt)
    by_cases hpM : p ∣ M
    · have hnu : ¬ IsUnit (p : ZMod M) := by
        rw [ZMod.isUnit_iff_coprime]
        intro hco
        exact hpp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hco hpM)
      have : {s : ℂ | 1 - χ p * (p : ℂ) ^ (-s) = 0 ∧ |s.im| < T} = ∅ := by
        ext s
        simp [MulChar.map_nonunit χ hnu]
      rw [this]
      simp
      positivity
    · have hu : IsUnit (p : ZMod M) := by
        rw [ZMod.isUnit_iff_coprime]
        have h := (Nat.Prime.coprime_iff_not_dvd hpp).mpr hpM
        exact h
      have hn : ‖χ p‖ = 1 := by
        have := χ.unit_norm_eq_one hu.unit
        simpa using this
      exact (Davenport.ncard_one_sub_mul_cpow_zeros_le hpp hn T hT).2
  refine (Finset.sum_le_sum hone).trans ?_
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hlog : ∑ p ∈ N.primeFactors, Real.log p ≤ Real.log N := by
    rw [← Real.log_prod (fun p hp ↦ by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero)]
    have hd := Nat.prod_primeFactors_dvd N
    have hle : (∏ p ∈ N.primeFactors, p) ≤ N := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne N)) hd
    have hpos : 0 < ∏ p ∈ N.primeFactors, (p : ℝ) :=
      Finset.prod_pos fun p hp ↦ by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos
    apply Real.log_le_log hpos
    rw [← Nat.cast_prod]
    exact_mod_cast hle
  have : ∑ p ∈ N.primeFactors, T * Real.log p / π = T / π * ∑ p ∈ N.primeFactors, Real.log p := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    ring
  rw [this]
  have hpi := Real.pi_pos
  have : T / π * ∑ p ∈ N.primeFactors, Real.log p ≤ T / π * Real.log N :=
    mul_le_mul_of_nonneg_left hlog (by positivity)
  have e : T / π * Real.log N = T * Real.log N / π := by ring
  linarith

end NTKB
