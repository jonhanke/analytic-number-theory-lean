/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.PSeries
import NTKB.Attr

/-!
# Davenport, Chapters 1 and 4: `log L(s, χ)` and the identities (A), (E) and inequality (C)

For a Dirichlet character `χ` modulo `q` and `Re s > 1` Davenport takes
$$\log L(s,\chi) = \sum_p\sum_{m\ge1} m^{-1}\chi(p)^m p^{-ms}$$
(§1, p. 3; §4, p. 31), the value of the logarithm given by the series
(`NTKB.Davenport.logL`). Then:

* `exp (log L(s, χ)) = L(s, χ)` (Euler's product; `NTKB.Davenport.exp_logL`);
* identity (A) of §1 / (E) of §4: for `(a, q) = 1`,
  `(1/φ(q)) ∑_χ χ̄(a) log L(s, χ) = ∑_{p^m ≡ a} m^{-1} p^{-ms}`
  (`NTKB.Davenport.sum_inv_mul_logL`);
* inequality (C) of §1: `∏_χ L(s, χ) ≥ 1` for real `s > 1`
  (`NTKB.Davenport.one_le_prod_LFunction`).
-/

noncomputable section

open Complex Finset DirichletCharacter
open scoped ComplexOrder

namespace NTKB.Davenport

variable {N : ℕ}

/-- The term `m^{-1} (χ(p) p^{-s})^m` of `log L(s, χ)`, indexed by `(p, m - 1)`. -/
def logLTerm (χ : DirichletCharacter ℂ N) (s : ℂ) (pm : Nat.Primes × ℕ) : ℂ :=
  (χ ((pm.1 : ℕ) : ZMod N) * ((pm.1 : ℕ) : ℂ) ^ (-s)) ^ (pm.2 + 1) / ((pm.2 : ℂ) + 1)

/-- **Davenport's `log L(s, χ)`** (§1, p. 3; §4, p. 31):
`∑_p ∑_{m ≥ 1} m^{-1} χ(p)^m p^{-ms}`. -/
def logL (χ : DirichletCharacter ℂ N) (s : ℂ) : ℂ := ∑' pm, logLTerm χ s pm

theorem norm_logLTerm_le (χ : DirichletCharacter ℂ N) {s : ℂ} (pm : Nat.Primes × ℕ) :
    ‖logLTerm χ s pm‖ ≤ (((pm.1 : ℕ) ^ (pm.2 + 1) : ℕ) : ℝ) ^ (-s.re) := by
  have hp : (0 : ℝ) < (pm.1 : ℕ) := by exact_mod_cast pm.1.prop.pos
  rw [logLTerm, norm_div, norm_pow, norm_mul]
  have h1 : ‖χ pm.1‖ ≤ 1 := DirichletCharacter.norm_le_one χ _
  have h2 : ‖((pm.1 : ℕ) : ℂ) ^ (-s)‖ = ((pm.1 : ℕ) : ℝ) ^ (-s.re) := by
    rw [norm_natCast_cpow_of_pos pm.1.prop.pos, neg_re]
  have h3 : (1 : ℝ) ≤ ‖((pm.2 : ℂ) + 1)‖ := by
    rw [show ((pm.2 : ℂ) + 1) = ((pm.2 + 1 : ℕ) : ℂ) by push_cast; ring, norm_natCast]
    exact_mod_cast Nat.succ_pos _
  rw [h2]
  have h4 : (‖χ pm.1‖ * ((pm.1 : ℕ) : ℝ) ^ (-s.re)) ^ (pm.2 + 1) ≤
      (((pm.1 : ℕ) : ℝ) ^ (-s.re)) ^ (pm.2 + 1) := by
    gcongr
    calc ‖χ pm.1‖ * ((pm.1 : ℕ) : ℝ) ^ (-s.re) ≤ 1 * ((pm.1 : ℕ) : ℝ) ^ (-s.re) := by
          gcongr
      _ = _ := one_mul _
  have h5 : (((pm.1 : ℕ) : ℝ) ^ (-s.re)) ^ (pm.2 + 1) =
      (((pm.1 : ℕ) ^ (pm.2 + 1) : ℕ) : ℝ) ^ (-s.re) := by
    rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul hp.le, ← Real.rpow_natCast,
      ← Real.rpow_mul hp.le, mul_comm]
  rw [← h5]
  calc (‖χ pm.1‖ * ((pm.1 : ℕ) : ℝ) ^ (-s.re)) ^ (pm.2 + 1) / ‖((pm.2 : ℂ) + 1)‖
      ≤ (‖χ pm.1‖ * ((pm.1 : ℕ) : ℝ) ^ (-s.re)) ^ (pm.2 + 1) / 1 :=
        div_le_div_of_nonneg_left (by positivity) one_pos h3
    _ ≤ _ := by rw [div_one]; exact h4

/-- The double series for `log L(s, χ)` converges absolutely for `Re s > 1`. -/
theorem summable_logLTerm (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    Summable (logLTerm χ s) := by
  set i : Nat.Primes × ℕ → ℕ := fun pm ↦ (pm.1 : ℕ) ^ (pm.2 + 1) with hi
  have hinj : Function.Injective i := by
    intro a b h
    obtain ⟨h1, h2⟩ := Nat.Prime.pow_inj a.1.prop b.1.prop h
    exact Prod.ext (Subtype.ext h1) h2
  have hsum : Summable (fun n : ℕ ↦ (n : ℝ) ^ (-s.re)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have hcomp : Summable (fun pm : Nat.Primes × ℕ ↦ ((i pm : ℕ) : ℝ) ^ (-s.re)) :=
    hsum.comp_injective hinj
  exact Summable.of_norm_bounded hcomp (norm_logLTerm_le χ)

/-- For each prime, `∑_{m ≥ 1} m^{-1} (χ(p) p^{-s})^m = -log(1 - χ(p) p^{-s})`. -/
theorem hasSum_logLTerm_prime (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re)
    (p : Nat.Primes) :
    HasSum (fun m ↦ logLTerm χ s (p, m))
      (-log (1 - χ ((p : ℕ) : ZMod N) * ((p : ℕ) : ℂ) ^ (-s))) := by
  have hz : ‖χ ((p : ℕ) : ZMod N) * ((p : ℕ) : ℂ) ^ (-s)‖ < 1 := ?_
  · have key := hasSum_taylorSeries_neg_log' hz
    refine key.congr_fun fun m ↦ ?_
    rfl
  rw [norm_mul]
  have hp : (1 : ℝ) < (p : ℕ) := by exact_mod_cast p.prop.one_lt
  have h2 : ‖((p : ℕ) : ℂ) ^ (-s)‖ < 1 := by
    rw [norm_natCast_cpow_of_pos p.prop.pos, neg_re]
    exact Real.rpow_lt_one_of_one_lt_of_neg hp (by linarith)
  calc ‖χ ((p : ℕ) : ZMod N)‖ * ‖((p : ℕ) : ℂ) ^ (-s)‖ ≤ 1 * ‖((p : ℕ) : ℂ) ^ (-s)‖ := by
        gcongr; exact DirichletCharacter.norm_le_one χ _
    _ < 1 := by rw [one_mul]; exact h2

/-- `log L(s, χ) = ∑_p -log(1 - χ(p) p^{-s})`. -/
theorem logL_eq_tsum_neg_log (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    logL χ s = ∑' p : Nat.Primes, -log (1 - χ ((p : ℕ) : ZMod N) * ((p : ℕ) : ℂ) ^ (-s)) :=
  (((summable_logLTerm χ hs).hasSum.prod_fiberwise
    (hasSum_logLTerm_prime χ hs)).tsum_eq).symm

/-- **Davenport §1, p. 3; §4, p. 31.** `exp(log L(s, χ)) = L(s, χ)` for `Re s > 1`: the series is
a logarithm of `L(s, χ)` (Euler's product). -/
@[kb "davenport1980" "Ch 1, p. 3; Ch 4, p. 31"]
theorem exp_logL (χ : DirichletCharacter ℂ N) [NeZero N] {s : ℂ} (hs : 1 < s.re) :
    exp (logL χ s) = LFunction χ s := by
  rw [logL_eq_tsum_neg_log χ hs, LSeries_eulerProduct_exp_log χ hs, LFunction_eq_LSeries χ hs]

/-- **Davenport §1, p. 4, (A); §4, p. 34, (E).** For `(a, q) = 1` and `Re s > 1`,
`(1/φ(q)) ∑_χ χ̄(a) log L(s, χ) = ∑_{p^m ≡ a (mod q)} m^{-1} p^{-ms}`
(here `χ̄(a) = χ(a⁻¹)`). -/
@[kb "davenport1980" "Ch 1, p. 4, (1); Ch 4, p. 34, (5)"]
theorem sum_inv_mul_logL [NeZero N] {a : ZMod N} (ha : IsUnit a) {s : ℂ} (hs : 1 < s.re) :
    (1 / N.totient : ℂ) * ∑ χ : DirichletCharacter ℂ N, χ a⁻¹ * logL χ s =
      ∑' pm : Nat.Primes × ℕ, if (((pm.1 : ℕ) ^ (pm.2 + 1) : ℕ) : ZMod N) = a then
        ((pm.1 : ℂ) ^ (-s)) ^ (pm.2 + 1) / (pm.2 + 1) else 0 := by
  have hφ : (N.totient : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos N)).ne'
  simp only [logL]
  simp_rw [← tsum_mul_left]
  rw [← Summable.tsum_finsetSum (fun χ _ ↦ (summable_logLTerm χ hs).mul_left _), ← tsum_mul_left]
  refine tsum_congr fun pm ↦ ?_
  have : ∑ χ : DirichletCharacter ℂ N, χ a⁻¹ * logLTerm χ s pm =
      (∑ χ : DirichletCharacter ℂ N, χ a⁻¹ * χ (((pm.1 : ℕ) ^ (pm.2 + 1) : ℕ) : ZMod N)) *
        (((pm.1 : ℂ) ^ (-s)) ^ (pm.2 + 1) / (pm.2 + 1)) := by
    rw [sum_mul]
    refine sum_congr rfl fun χ _ ↦ ?_
    rw [logLTerm, mul_pow, Nat.cast_pow, map_pow]
    ring
  rw [this, sum_char_inv_mul_char_eq ℂ ha]
  split_ifs with h1 h2 h2
  · field_simp
  · exact absurd h1.symm h2
  · exact absurd h2.symm h1
  · simp

/-- **Davenport §1, p. 5, (C).** `∏_χ L(s, χ) ≥ 1` for real `s > 1` (take `a = 1` in (A):
the right side is a sum of positive terms). -/
@[kb "davenport1980" "Ch 1, p. 5, (3)"]
theorem one_le_prod_LFunction [NeZero N] {s : ℝ} (hs : 1 < s) :
    (1 : ℂ) ≤ ∏ χ : DirichletCharacter ℂ N, LFunction χ s := by
  have hs' : 1 < (s : ℂ).re := by simpa using hs
  have hφ : (0 : ℝ) < N.totient := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos N)
  have hA := sum_inv_mul_logL (N := N) isUnit_one hs'
  simp only [ZMod.inv_one, map_one, one_mul] at hA
  -- the right side of (A) is a nonnegative real number
  set f : Nat.Primes × ℕ → ℝ := fun pm ↦ if (((pm.1 : ℕ) ^ (pm.2 + 1) : ℕ) : ZMod N) = 1 then
    (((pm.1 : ℕ) : ℝ) ^ (-s)) ^ (pm.2 + 1) / (pm.2 + 1) else 0
  have hf : ∀ pm, (0 : ℝ) ≤ f pm := by
    intro pm; simp only [f]; split_ifs
    · positivity
    · exact le_rfl
  have hreal : (∑' pm : Nat.Primes × ℕ, if (((pm.1 : ℕ) ^ (pm.2 + 1) : ℕ) : ZMod N) = 1 then
      (((pm.1 : ℕ) : ℂ) ^ (-(s : ℂ))) ^ (pm.2 + 1) / (pm.2 + 1) else 0) = ((∑' pm, f pm : ℝ) : ℂ) := by
    rw [ofReal_tsum]
    refine tsum_congr fun pm ↦ ?_
    simp only [f]
    split_ifs
    · rw [← ofReal_neg, ← ofReal_natCast, ← ofReal_cpow (Nat.cast_nonneg _)]
      push_cast; ring
    · simp
  rw [hreal] at hA
  have hsum : ∑ χ : DirichletCharacter ℂ N, logL χ s = ((N.totient * ∑' pm, f pm : ℝ) : ℂ) := by
    have := congrArg (fun z ↦ (N.totient : ℂ) * z) hA
    rw [← mul_assoc, mul_one_div_cancel (by exact_mod_cast hφ.ne'), one_mul] at this
    rw [this]; push_cast; ring
  rw [← prod_congr rfl fun χ _ ↦ exp_logL χ hs', ← exp_sum, hsum, ← ofReal_exp]
  have hpos : 0 ≤ (N.totient : ℝ) * ∑' pm, f pm := mul_nonneg hφ.le (tsum_nonneg hf)
  rw [Complex.le_def]
  simp only [one_re, ofReal_re, one_im, ofReal_im, and_true]
  exact Real.one_le_exp hpos

end NTKB.Davenport
