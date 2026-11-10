/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Apostol.DirichletSeries.UniformConvergence
import Mathlib.NumberTheory.LSeries.Convergence

/-!
# The abscissa of convergence (Apostol, Theorems 11.9 and 11.10)

* Theorem 11.9 -> `apostol_thm_11_9`: if `∑ f(n) n^{-s}` neither converges everywhere nor diverges
  everywhere, there is a real `σ_c` with convergence for `σ > σ_c` and divergence for `σ < σ_c`
  (`σ_c` = `abscissaOfConv f`, the infimum of the real parts of points of convergence).
* Theorem 11.10 -> `apostol_thm_11_10`: `0 ≤ σ_a - σ_c ≤ 1`, with `σ_a` Mathlib's
  `LSeries.abscissaOfAbsConv`.
-/

open Filter Topology Finset LSeries

namespace NTKB.Apostol

/-- The Dirichlet series `∑ f(n) n^{-s}` converges at `s` (its partial sums have a limit). -/
def ConvergesAt (f : ℕ → ℂ) (s : ℂ) : Prop :=
  ∃ L, Tendsto (dirichletPartialSum f s) atTop (𝓝 L)

/-- Apostol's abscissa of convergence `σ_c`: the infimum of `Re s` over the points of convergence
(meaningful when the series converges somewhere but not everywhere). -/
noncomputable def abscissaOfConv (f : ℕ → ℂ) : ℝ := sInf {x : ℝ | ∃ s, s.re = x ∧ ConvergesAt f s}

theorem convergesAt_of_re_lt {f : ℕ → ℂ} {s₀ s : ℂ} (h : ConvergesAt f s₀) (hs : s₀.re < s.re) :
    ConvergesAt f s := by
  obtain ⟨L, hL⟩ := h
  exact apostol_thm_11_8 hL hs

/-- **Theorem 11.9** (Apostol). If the series converges at some point and diverges at some point,
there is a real `σ_c` such that it converges for `σ > σ_c` and diverges for `σ < σ_c`. -/
@[kb "apostol1976" "Thm 11.9, p. 233"]
theorem apostol_thm_11_9 {f : ℕ → ℂ} (h1 : ∃ s, ConvergesAt f s) (h2 : ∃ s, ¬ ConvergesAt f s) :
    (∀ s : ℂ, abscissaOfConv f < s.re → ConvergesAt f s) ∧
      ∀ s : ℂ, s.re < abscissaOfConv f → ¬ ConvergesAt f s := by
  obtain ⟨s₁, hs₁⟩ := h1
  obtain ⟨s₂, hs₂⟩ := h2
  set A := {x : ℝ | ∃ s, s.re = x ∧ ConvergesAt f s}
  have hne : A.Nonempty := ⟨s₁.re, s₁, rfl, hs₁⟩
  have hbdd : BddBelow A := by
    refine ⟨s₂.re, fun x ⟨s, hsx, hs⟩ ↦ ?_⟩
    by_contra hlt
    exact hs₂ (convergesAt_of_re_lt hs (by rw [hsx]; exact lt_of_not_ge hlt))
  refine ⟨fun s hs ↦ ?_, fun s hs hconv ↦ ?_⟩
  · obtain ⟨x, ⟨s₀, rfl, hs₀⟩, hlt⟩ := exists_lt_of_csInf_lt hne hs
    exact convergesAt_of_re_lt hs₀ hlt
  · exact absurd (csInf_le hbdd ⟨s, rfl, hconv⟩) (not_le.2 hs)

/-- Absolute convergence implies convergence. -/
theorem LSeriesSummable.convergesAt {f : ℕ → ℂ} {s : ℂ} (h : LSeriesSummable f s) :
    ConvergesAt f s :=
  ⟨_, h.hasSum.tendsto_sum_nat⟩

/-- At a point of convergence the terms are `O(n^{σ})`. -/
theorem isBigO_of_convergesAt {f : ℕ → ℂ} {x : ℝ} (h : ConvergesAt f x) :
    Asymptotics.IsBigO atTop f fun n : ℕ ↦ (n : ℝ) ^ x := by
  obtain ⟨L, hL⟩ := h
  have hterm : Tendsto (fun n ↦ term f x n) atTop (𝓝 0) := by
    have h1 := (hL.comp (tendsto_add_atTop_nat 1)).sub hL
    rw [sub_self] at h1
    refine h1.congr fun n ↦ ?_
    simp [dirichletPartialSum, Finset.sum_range_succ]
  refine Asymptotics.IsBigO.of_bound 1 ?_
  filter_upwards [(tendsto_iff_norm_sub_tendsto_zero.1 hterm).eventually
    (gt_mem_nhds one_pos), eventually_ge_atTop 1] with n hn hn1
  have hn0 : n ≠ 0 := by omega
  rw [sub_zero, term_of_ne_zero hn0, norm_div, Complex.norm_natCast_cpow_of_pos (by omega)] at hn
  have hpos : (0 : ℝ) < (n : ℝ) ^ x := Real.rpow_pos_of_pos (by exact_mod_cast hn0.bot_lt) _
  rw [Complex.ofReal_re, div_lt_one hpos] at hn
  rw [Real.norm_eq_abs, abs_of_pos hpos, one_mul]
  simpa using hn.le

/-- **Theorem 11.10** (Apostol). `0 ≤ σ_a - σ_c ≤ 1` (for a series that converges somewhere but not
everywhere). -/
@[kb "apostol1976" "Thm 11.10, p. 234"]
theorem apostol_thm_11_10 {f : ℕ → ℂ} (h1 : ∃ s, ConvergesAt f s) (h2 : ∃ s, ¬ ConvergesAt f s) :
    (abscissaOfConv f : EReal) ≤ abscissaOfAbsConv f ∧
      abscissaOfAbsConv f ≤ (abscissaOfConv f + 1 : ℝ) := by
  have h9 := apostol_thm_11_9 h1 h2
  refine ⟨le_sInf ?_, abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy ↦ ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    by_contra hlt
    exact h9.2 x (by simpa using lt_of_not_ge hlt) (LSeriesSummable.convergesAt hx)
  · set s₀ : ℝ := (abscissaOfConv f + (y - 1)) / 2
    have hs₀ : abscissaOfConv f < s₀ := by simp only [s₀]; linarith
    have hs₀' : s₀ + 1 < y := by simp only [s₀]; linarith
    have hconv := h9.1 s₀ (by simpa using hs₀)
    refine LSeriesSummable_of_isBigO_rpow (x := s₀ + 1) (by simpa using hs₀') ?_
    simpa using isBigO_of_convergesAt hconv

end NTKB.Apostol
