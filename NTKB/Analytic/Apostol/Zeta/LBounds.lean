/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import NTKB.Analytic.Apostol.Zeta.HurwitzBounds
import NTKB.Analytic.Apostol.Zeta.HurwitzFormula

/-!
# Bounds for `|L(s, χ)|` (Apostol, Theorem 12.24, cases `m = -1, 0`)

For `0 < δ < 1` there is `A(δ)`, independent of `s`, `k` and `χ`, such that for every Dirichlet
character `χ` mod `k` and `|t| ≥ 1`:
`|L(s, χ)| ≤ A(δ) |kt|^{δ}` for `1 - δ ≤ σ ≤ 1 + δ` (`m = -1`), and
`|L(s, χ)| ≤ A(δ) |kt|^{1+δ}` for `-δ ≤ σ ≤ δ` (`m = 0`).
Apostol's proof: `L(s, χ) = ∑_{r=1}^{k} χ(r) r^{-s} + k^{-s} ∑_{r=1}^{k} χ(r) (ζ(s, r/k) - (r/k)^{-s})`
and Theorem 12.23 (30), (31). (The cases `m ≥ 1` use (32), which needs the general `m` of
Theorem 12.22, not done.)
-/

open Complex Finset HurwitzZeta ZMod

namespace NTKB.Apostol

variable {k : ℕ} [NeZero k]

/-- The representative `r ∈ {1, …, k}` of `j mod k`. -/
def zmodRep (j : ZMod k) : ℕ := if j.val = 0 then k else j.val

lemma zmodRep_pos (j : ZMod k) : 0 < zmodRep j := by
  unfold zmodRep; split_ifs with h
  · exact NeZero.pos k
  · exact Nat.pos_of_ne_zero h

lemma zmodRep_le (j : ZMod k) : zmodRep j ≤ k := by
  unfold zmodRep; split_ifs
  · exact le_rfl
  · exact (ZMod.val_lt j).le

lemma toAddCircle_eq_zmodRep (j : ZMod k) :
    toAddCircle j = (((zmodRep j : ℝ) / k : ℝ) : UnitAddCircle) := by
  have hk : (k : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne k
  unfold zmodRep
  split_ifs with h
  · rw [(ZMod.val_eq_zero j).mp h, map_zero, div_self hk, AddCircle.coe_period]
  · exact toAddCircle_apply j

lemma sum_zmodRep_rpow (p : ℝ) :
    ∑ j : ZMod k, ((zmodRep j : ℕ) : ℝ) ^ p = ∑ n ∈ range k, ((n : ℝ) + 1) ^ p := by
  have h := sum_zmod_val_eq_sum_Icc k
    (fun m : ℕ ↦ (((if m = 0 then k else m : ℕ)) : ℝ) ^ p) (by simp [NeZero.ne k])
  have h1 : ∑ j : ZMod k, ((zmodRep j : ℕ) : ℝ) ^ p =
      ∑ j : ZMod k, (((if j.val = 0 then k else j.val : ℕ)) : ℝ) ^ p := rfl
  rw [h1, h, show Icc 1 k = Ico 1 (k + 1) by ext; simp, sum_Ico_eq_sum_range]
  refine sum_congr (by simp) fun n _ ↦ ?_
  simp [add_comm]

/-- The decomposition `L(s,χ) = ∑ χ(r) r^{-s} + k^{-s} ∑ χ(r) (ζ(s, r/k) - (r/k)^{-s})`, in norm. -/
lemma norm_LFunction_le (χ : DirichletCharacter ℂ k) (s : ℂ) {E : ℝ}
    (hE : ∀ j : ZMod k, ‖hurwitzZeta (((zmodRep j : ℝ) / k : ℝ)) s -
      ((((zmodRep j : ℝ) / k : ℝ)) : ℂ) ^ (-s)‖ ≤ E) :
    ‖χ.LFunction s‖ ≤ ∑ n ∈ range k, ((n : ℝ) + 1) ^ (-s.re) + k * ((k : ℝ) ^ (-s.re) * E) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast NeZero.pos k
  rw [DirichletCharacter.LFunction, ZMod.LFunction, mul_sum]
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ j : ZMod k, ‖(k : ℂ) ^ (-s) * (χ j * hurwitzZeta (toAddCircle j) s)‖ ≤
      ((zmodRep j : ℕ) : ℝ) ^ (-s.re) + (k : ℝ) ^ (-s.re) * E := by
    intro j
    set a : ℝ := (zmodRep j : ℝ) / k
    have ha0 : 0 < a := div_pos (by exact_mod_cast zmodRep_pos j) hk0
    have hsplit : (k : ℂ) ^ (-s) * hurwitzZeta (toAddCircle j) s =
        (((zmodRep j : ℕ) : ℝ) : ℂ) ^ (-s) + (k : ℂ) ^ (-s) * (hurwitzZeta a s - (a : ℂ) ^ (-s)) := by
      rw [toAddCircle_eq_zmodRep, mul_sub, ← add_sub_assoc, add_comm, add_sub_assoc]
      have : (k : ℂ) ^ (-s) * (a : ℂ) ^ (-s) = (((zmodRep j : ℕ) : ℝ) : ℂ) ^ (-s) := by
        have := mul_cpow_ofReal_nonneg hk0.le ha0.le (-s)
        rw [← ofReal_mul, show (k : ℝ) * a = (zmodRep j : ℝ) by simp only [a]; field_simp] at this
        simpa using this.symm
      rw [this]; ring
    rw [mul_left_comm, norm_mul, hsplit]
    calc ‖χ j‖ * ‖(((zmodRep j : ℕ) : ℝ) : ℂ) ^ (-s) +
          (k : ℂ) ^ (-s) * (hurwitzZeta a s - (a : ℂ) ^ (-s))‖
        ≤ 1 * (((zmodRep j : ℕ) : ℝ) ^ (-s.re) + (k : ℝ) ^ (-s.re) * E) := by
          gcongr
          · exact DirichletCharacter.norm_le_one χ j
          · refine (norm_add_le _ _).trans ?_
            gcongr
            · rw [norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast zmodRep_pos j), neg_re]
            · rw [norm_mul]
              gcongr
              · rw [show (k : ℂ) = ((k : ℝ) : ℂ) by simp,
                  norm_cpow_eq_rpow_re_of_pos hk0, neg_re]
              · exact hE j
      _ = _ := one_mul _
  refine (sum_le_sum fun j _ ↦ hterm j).trans ?_
  rw [sum_add_distrib, sum_zmodRep_rpow, sum_const, card_univ, ZMod.card, nsmul_eq_mul]

/-- **Apostol, Theorem 12.24** (33), cases `m = -1` and `m = 0`: for `0 < δ < 1` there is
`A(δ) > 0` such that for every Dirichlet character `χ` mod `k` and `s = σ + it` with `|t| ≥ 1`,
`|L(s,χ)| ≤ A(δ) |kt|^{δ}` if `1 - δ ≤ σ ≤ 1 + δ`, and `|L(s,χ)| ≤ A(δ) |kt|^{1+δ}` if
`-δ ≤ σ ≤ δ`. -/
@[kb "apostol1976" "Thm 12.24, p. 272"]
theorem apostol_thm_12_24 {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ∃ A : ℝ, 0 < A ∧ ∀ (k : ℕ) [NeZero k] (χ : DirichletCharacter ℂ k) (s : ℂ), 1 ≤ |s.im| →
      (1 - δ ≤ s.re → s.re ≤ 1 + δ → ‖χ.LFunction s‖ ≤ A * (k * |s.im|) ^ δ) ∧
      (-δ ≤ s.re → s.re ≤ δ → ‖χ.LFunction s‖ ≤ A * (k * |s.im|) ^ (1 + δ)) := by
  obtain ⟨B, hB, hBb⟩ := apostol_thm_12_23_b hδ0 hδ1
  obtain ⟨C, hC, hCb⟩ := apostol_thm_12_23_b' hδ0 hδ1
  refine ⟨1 / δ + B + 1 + C, by positivity, fun k _ χ s ht ↦ ⟨fun hσ1 hσ2 ↦ ?_, fun hσ1 hσ2 ↦ ?_⟩⟩
  all_goals
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast NeZero.one_le
    have hk0 : (0 : ℝ) < k := by linarith
    set t := |s.im| with ht_def
    have ht0 : 0 < t := by linarith
    have hamem : ∀ j : ZMod k, 0 < ((zmodRep j : ℝ) / k) ∧ ((zmodRep j : ℝ) / k) ≤ 1 := fun j ↦
      ⟨div_pos (by exact_mod_cast zmodRep_pos j) hk0,
        (div_le_one hk0).mpr (by exact_mod_cast zmodRep_le j)⟩
  · -- `m = -1`
    have hL := norm_LFunction_le χ s (E := B * t ^ δ) fun j ↦
      hBb _ (hamem j).1 (hamem j).2 s hσ1 (by linarith) ht
    have h1 : ∑ n ∈ range k, ((n : ℝ) + 1) ^ (-s.re) ≤ (k : ℝ) ^ δ / δ :=
      (sum_le_sum fun n _ ↦ Real.rpow_le_rpow_of_exponent_le
        (by linarith [n.cast_nonneg (α := ℝ)]) (by linarith)).trans
        (sum_range_rpow_le hδ0 hδ1.le k)
    have h2 : (k : ℝ) * (k : ℝ) ^ (-s.re) ≤ (k : ℝ) ^ δ := by
      rw [show (k : ℝ) * (k : ℝ) ^ (-s.re) = (k : ℝ) ^ (1 + -s.re) by
        rw [Real.rpow_add hk0, Real.rpow_one]]
      exact Real.rpow_le_rpow_of_exponent_le hk1 (by linarith)
    have htδ : 1 ≤ t ^ δ := Real.one_le_rpow ht hδ0.le
    have hkt : (k * t) ^ δ = (k : ℝ) ^ δ * t ^ δ := Real.mul_rpow hk0.le ht0.le
    calc ‖χ.LFunction s‖ ≤ (k : ℝ) ^ δ / δ + (k : ℝ) * ((k : ℝ) ^ (-s.re) * (B * t ^ δ)) :=
          hL.trans (by gcongr)
      _ = (k : ℝ) ^ δ / δ + ((k : ℝ) * (k : ℝ) ^ (-s.re)) * (B * t ^ δ) := by ring
      _ ≤ (k : ℝ) ^ δ / δ * t ^ δ + (k : ℝ) ^ δ * (B * t ^ δ) := by
          gcongr
          · exact le_mul_of_one_le_right (by positivity) htδ
      _ ≤ (1 / δ + B + 1 + C) * (k * t) ^ δ := by
          rw [hkt]
          have : 0 ≤ (k : ℝ) ^ δ * t ^ δ := by positivity
          have e : (k : ℝ) ^ δ / δ * t ^ δ + (k : ℝ) ^ δ * (B * t ^ δ) =
              (1 / δ + B) * ((k : ℝ) ^ δ * t ^ δ) := by ring
          rw [e]
          nlinarith
  · -- `m = 0`
    have hL := norm_LFunction_le χ s (E := C * t ^ (1 + δ)) fun j ↦
      hCb _ (hamem j).1 (hamem j).2 s hσ1 hσ2 ht
    have h1 : ∑ n ∈ range k, ((n : ℝ) + 1) ^ (-s.re) ≤ (k : ℝ) ^ (1 + δ) := by
      calc ∑ n ∈ range k, ((n : ℝ) + 1) ^ (-s.re) ≤ ∑ n ∈ range k, (k : ℝ) ^ δ := by
            refine sum_le_sum fun n hn ↦ ?_
            have hn' : (n : ℝ) + 1 ≤ k := by
              have := mem_range.mp hn; exact_mod_cast this
            calc ((n : ℝ) + 1) ^ (-s.re) ≤ ((n : ℝ) + 1) ^ δ :=
                  Real.rpow_le_rpow_of_exponent_le (by linarith [n.cast_nonneg (α := ℝ)])
                    (by linarith)
              _ ≤ (k : ℝ) ^ δ := Real.rpow_le_rpow (by positivity) hn' hδ0.le
        _ = (k : ℝ) ^ (1 + δ) := by
            rw [sum_const, card_range, nsmul_eq_mul, Real.rpow_add hk0, Real.rpow_one]
    have h2 : (k : ℝ) * (k : ℝ) ^ (-s.re) ≤ (k : ℝ) ^ (1 + δ) := by
      rw [show (k : ℝ) * (k : ℝ) ^ (-s.re) = (k : ℝ) ^ (1 + -s.re) by
        rw [Real.rpow_add hk0, Real.rpow_one]]
      exact Real.rpow_le_rpow_of_exponent_le hk1 (by linarith)
    have htδ : 1 ≤ t ^ (1 + δ) := Real.one_le_rpow ht (by linarith)
    have hkt : (k * t) ^ (1 + δ) = (k : ℝ) ^ (1 + δ) * t ^ (1 + δ) :=
      Real.mul_rpow hk0.le ht0.le
    calc ‖χ.LFunction s‖ ≤ (k : ℝ) ^ (1 + δ) +
          (k : ℝ) * ((k : ℝ) ^ (-s.re) * (C * t ^ (1 + δ))) := hL.trans (by gcongr)
      _ = (k : ℝ) ^ (1 + δ) + ((k : ℝ) * (k : ℝ) ^ (-s.re)) * (C * t ^ (1 + δ)) := by ring
      _ ≤ (k : ℝ) ^ (1 + δ) * t ^ (1 + δ) + (k : ℝ) ^ (1 + δ) * (C * t ^ (1 + δ)) := by
          gcongr
          · exact le_mul_of_one_le_right (by positivity) htδ
      _ ≤ (1 / δ + B + 1 + C) * (k * t) ^ (1 + δ) := by
          rw [hkt]
          have : 0 ≤ (k : ℝ) ^ (1 + δ) * t ^ (1 + δ) := by positivity
          have : 0 ≤ 1 / δ := by positivity
          nlinarith

end NTKB.Apostol
