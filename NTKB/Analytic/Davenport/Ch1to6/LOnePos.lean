/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Davenport.Ch1to6.LOneOdd

/-!
# Davenport, Chapters 1 and 6: `L(1, χ) > 0` for a real character

* §1, p. 7: for a real nonprincipal character, `L(s) > 0` for `s > 1` by the Euler product and
  `L` is continuous at `1`, so `L(1) ≥ 0`; with `L(1) ≠ 0` this gives `L(1) > 0`
  (`NTKB.Davenport.LFunction_one_pos_of_isQuadratic`; §6, p. 50, deduces the same from
  `h(d) ≥ 1`).
* §6, p. 51: for a prime `q ≡ 3 (mod 4)`, `q > 3`, the number `H = -(1/q) ∑_{m<q} m (m/q)`
  of Jacobi's formula (19) is a positive integer.
-/

noncomputable section

open Complex DirichletCharacter Finset Filter Topology
open scoped Real ComplexOrder

namespace NTKB.Davenport

variable {N : ℕ} [NeZero N]

/-- For a real character and real `x > 1`, `L(x, χ)` is `exp` of a real number (Euler product). -/
theorem exists_LFunction_eq_exp_of_isQuadratic {χ : DirichletCharacter ℂ N}
    (hχ : χ.IsQuadratic) {x : ℝ} (hx : 1 < x) :
    ∃ r : ℝ, LFunction χ x = (Real.exp r : ℂ) := by
  have hs : 1 < (x : ℂ).re := by simpa using hx
  rw [LFunction_eq_LSeries χ hs, ← LSeries_eulerProduct_exp_log χ hs]
  refine ⟨∑' p : Nat.Primes, -Real.log (1 - (χ p).re * (p : ℝ) ^ (-x)), ?_⟩
  rw [ofReal_exp, ofReal_tsum]
  congr 1
  refine tsum_congr fun p ↦ ?_
  have hχp : χ p = ((χ p).re : ℂ) := by
    rcases hχ p with h | h | h <;> rw [h] <;> simp
  have hp1 : (1 : ℝ) < p := by exact_mod_cast p.prop.one_lt
  have hlt : (p : ℝ) ^ (-x) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)
  have hle : |(χ p).re| ≤ 1 := by
    rcases hχ p with h | h | h <;> rw [h] <;> simp
  have hpos : 0 < 1 - (χ p).re * (p : ℝ) ^ (-x) := by
    have h0 : 0 ≤ (p : ℝ) ^ (-x) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    have : (χ p).re * (p : ℝ) ^ (-x) ≤ |(χ p).re| * (p : ℝ) ^ (-x) :=
      mul_le_mul_of_nonneg_right (le_abs_self _) h0
    nlinarith
  rw [ofReal_neg, ofReal_log hpos.le, ofReal_sub, ofReal_one, ofReal_mul,
    ofReal_cpow (Nat.cast_nonneg _), ← hχp]
  push_cast
  rfl

/-- `L(x, χ) → L(1, χ)` as `x → 1⁺` along the reals, for `χ ≠ 1`. -/
theorem tendsto_LFunction_one {χ : DirichletCharacter ℂ N} (h1 : χ ≠ 1) :
    Tendsto (fun x : ℝ ↦ LFunction χ x) (𝓝[>] 1) (𝓝 (LFunction χ 1)) := by
  have hc : Tendsto (fun x : ℝ ↦ (x : ℂ)) (𝓝[>] 1) (𝓝 (1 : ℂ)) := by
    have := (continuous_ofReal.tendsto (1 : ℝ)).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 1))
    simpa using this
  exact ((differentiableAt_LFunction χ 1 (Or.inr h1)).continuousAt.tendsto).comp hc

/-- **Davenport §1, p. 7, and §6, p. 50.** `L(1, χ) > 0` for every real nonprincipal character:
`L(s, χ) > 0` for real `s > 1` by the Euler product, `L` is continuous at `1`, and
`L(1, χ) ≠ 0`. -/
@[kb "davenport1980" "Ch 1, p. 7; Ch 6, p. 50"]
theorem LFunction_one_pos_of_isQuadratic {χ : DirichletCharacter ℂ N} (hχ : χ.IsQuadratic)
    (h1 : χ ≠ 1) : 0 < LFunction χ 1 := by
  have hcont := tendsto_LFunction_one h1
  have hev : ∀ᶠ x : ℝ in 𝓝[>] 1, 0 < (LFunction χ x).re ∧ (LFunction χ x).im = 0 := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    obtain ⟨r, hr⟩ := exists_LFunction_eq_exp_of_isQuadratic hχ hx
    rw [hr, ofReal_re, ofReal_im]
    exact ⟨Real.exp_pos r, rfl⟩
  have him : (LFunction χ 1).im = 0 :=
    tendsto_nhds_unique ((continuous_im.tendsto _).comp hcont)
      (tendsto_const_nhds.congr' (hev.mono fun x hx ↦ hx.2.symm))
  have hre : 0 ≤ (LFunction χ 1).re :=
    ge_of_tendsto ((continuous_re.tendsto _).comp hcont) (hev.mono fun x hx ↦ hx.1.le)
  have hne := LFunction_apply_one_ne_zero h1
  rw [Complex.lt_def]
  refine ⟨lt_of_le_of_ne hre fun h ↦ hne ?_, by simpa using him.symm⟩
  exact Complex.ext (by simpa using h.symm) (by simpa using him)

/-- **Davenport §6, p. 51.** For a prime `q ≡ 3 (mod 4)`, `q > 3`, the number
`H = -(1/q) ∑_{m=1}^{q-1} m (m/q)` on the right of Jacobi's formula (19) is a positive integer. -/
@[kb "davenport1980" "Ch 6, p. 51"]
theorem exists_pos_int_sum_mul_legendreSym {q : ℕ} [Fact q.Prime] (hq : q % 4 = 3)
    (hq3 : 3 < q) :
    ∃ H : ℤ, 0 < H ∧ ∑ m ∈ Ico 1 q, (m : ℤ) * legendreSym q m = -(q * H) := by
  obtain ⟨H, hH⟩ := dvd_sum_mul_legendreSym (q := q) hq3
  refine ⟨-H, ?_, by rw [hH]; ring⟩
  have hL := LFunction_one_pos_of_isQuadratic (legendreChar_isQuadratic (q := q))
    (ne_one_of_odd (legendreChar_odd hq))
  rw [LFunction_one_legendreChar hq] at hL
  have hS : ∑ m ∈ Ico 1 q, (m : ℂ) * (legendreSym q m : ℂ) = ((q * H : ℤ) : ℂ) := by
    rw [← hH]; push_cast; rfl
  rw [hS] at hL
  have hpos : (0 : ℝ) < π / (q : ℝ) ^ ((3 : ℝ) / 2) :=
    div_pos Real.pi_pos (Real.rpow_pos_of_pos (by exact_mod_cast (Fact.out : q.Prime).pos) _)
  have hre : (0 : ℝ) < -(π / (q : ℝ) ^ ((3 : ℝ) / 2)) * (q * H : ℤ) := by
    rw [Complex.lt_def] at hL
    have := hL.1
    rw [← ofReal_intCast, ← ofReal_neg, ← ofReal_mul, ofReal_re, zero_re] at this
    exact this
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (Fact.out : q.Prime).pos
  push_cast at hre
  have hqH : (q : ℝ) * H < 0 := by nlinarith
  have : (H : ℝ) < 0 := by
    by_contra h
    nlinarith [not_lt.mp h]
  exact_mod_cast neg_pos.mpr this

end NTKB.Davenport
