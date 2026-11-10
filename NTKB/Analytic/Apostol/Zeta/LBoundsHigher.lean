/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Apostol.Zeta.LBounds
import NTKB.Analytic.Apostol.Zeta.HurwitzBoundsHigher

/-!
# Bounds for `|L(s, χ)|`, cases `m ≥ 1` (Apostol, Theorem 12.24)

For `0 < δ < 1`, `m = 1, 2, …` there is `A`, independent of `s`, `k` and `χ`, with
`|L(s, χ)| ≤ A |kt|^{m+1+δ}` for `-m - δ ≤ σ ≤ -m + δ`, `|t| ≥ 1`: from
`L(s,χ) = k^{-s} ∑_{r=1}^{k} χ(r) ζ(s, r/k)` and Theorem 12.23 (32).
-/

open Complex Finset HurwitzZeta

namespace NTKB.Apostol

/-- **Apostol, Theorem 12.24** (33), cases `m ≥ 1`. -/
@[kb "apostol1976" "Thm 12.24, p. 272"]
theorem apostol_thm_12_24_pos {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) (m : ℕ) :
    ∃ A : ℝ, 0 < A ∧ ∀ (k : ℕ) [NeZero k] (χ : DirichletCharacter ℂ k) (s : ℂ), 1 ≤ |s.im| →
      -(m : ℝ) - δ ≤ s.re → s.re ≤ -(m : ℝ) + δ →
      ‖χ.LFunction s‖ ≤ A * (k * |s.im|) ^ ((m : ℝ) + 1 + δ) := by
  obtain ⟨B, hB, hBb⟩ := hurwitz_bound_levels hδ0 hδ1 m
  refine ⟨1 + B, by positivity, fun k _ χ s ht hσ1 hσ2 ↦ ?_⟩
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast NeZero.one_le
  have hk0 : (0 : ℝ) < k := by linarith
  set t := |s.im| with ht_def
  have ht0 : 0 < t := by linarith
  set x : ℝ := (m : ℝ) + 1 + δ
  have hx : 0 ≤ x := by positivity
  have hamem : ∀ j : ZMod k, 0 < ((zmodRep j : ℝ) / k) ∧ ((zmodRep j : ℝ) / k) ≤ 1 := fun j ↦
    ⟨div_pos (by exact_mod_cast zmodRep_pos j) hk0,
      (div_le_one hk0).mpr (by exact_mod_cast zmodRep_le j)⟩
  have hL := norm_LFunction_le χ s (E := B * t ^ x) fun j ↦
    hBb m le_rfl _ (hamem j).1 (hamem j).2 s hσ1 hσ2 ht
  have h1 : ∑ n ∈ range k, ((n : ℝ) + 1) ^ (-s.re) ≤ (k : ℝ) ^ x := by
    calc ∑ n ∈ range k, ((n : ℝ) + 1) ^ (-s.re) ≤ ∑ n ∈ range k, (k : ℝ) ^ ((m : ℝ) + δ) := by
          refine sum_le_sum fun n hn ↦ ?_
          have hn' : (n : ℝ) + 1 ≤ k := by
            have := mem_range.mp hn; exact_mod_cast this
          calc ((n : ℝ) + 1) ^ (-s.re) ≤ ((n : ℝ) + 1) ^ ((m : ℝ) + δ) :=
                Real.rpow_le_rpow_of_exponent_le (by linarith [n.cast_nonneg (α := ℝ)])
                  (by linarith)
            _ ≤ (k : ℝ) ^ ((m : ℝ) + δ) := Real.rpow_le_rpow (by positivity) hn' (by positivity)
      _ = (k : ℝ) ^ x := by
          rw [sum_const, card_range, nsmul_eq_mul, show x = 1 + ((m : ℝ) + δ) by simp only [x]; ring,
            Real.rpow_add hk0 1, Real.rpow_one]
  have h2 : (k : ℝ) * (k : ℝ) ^ (-s.re) ≤ (k : ℝ) ^ x := by
    rw [show (k : ℝ) * (k : ℝ) ^ (-s.re) = (k : ℝ) ^ (1 + -s.re) by
      rw [Real.rpow_add hk0, Real.rpow_one]]
    exact Real.rpow_le_rpow_of_exponent_le hk1 (by simp only [x]; linarith)
  have htx : 1 ≤ t ^ x := Real.one_le_rpow ht hx
  have hkt : (k * t) ^ x = (k : ℝ) ^ x * t ^ x := Real.mul_rpow hk0.le ht0.le
  calc ‖χ.LFunction s‖ ≤ (k : ℝ) ^ x + (k : ℝ) * ((k : ℝ) ^ (-s.re) * (B * t ^ x)) :=
        hL.trans (by gcongr)
    _ = (k : ℝ) ^ x + ((k : ℝ) * (k : ℝ) ^ (-s.re)) * (B * t ^ x) := by ring
    _ ≤ (k : ℝ) ^ x * t ^ x + (k : ℝ) ^ x * (B * t ^ x) := by
        gcongr
        exact le_mul_of_one_le_right (by positivity) htx
    _ = (1 + B) * (k * t) ^ x := by rw [hkt]; ring

end NTKB.Apostol
