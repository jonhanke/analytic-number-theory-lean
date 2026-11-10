/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Davenport.Zeros.LContour

/-!
# The residue theorem for `-L'/L(s, χ) x^s/s`

**Davenport, Ch. 19, pp. 115-116.** See `LContour` for the conventions.
-/

open Filter Topology Complex Set DirichletCharacter MeasureTheory
open scoped Real Interval

namespace NTKB

variable {N : ℕ} [NeZero N]

open scoped Classical in
/-- The residue of `F(s, χ)` (odd `χ`), resp. of `F(s, χ) + 1/s²` (even `χ`), at `s = 0`:
`-L'/L(0, χ)`, resp. `-(log x + b(χ))`. -/
noncomputable def residueZeroL (χ : DirichletCharacter ℂ N) (x : ℝ) : ℂ :=
  if dirichletParity χ = 1 then -(deriv (LFunction χ) 0 / LFunction χ 0)
  else -((Real.log x : ℂ) + bEven χ)

open scoped Classical in
/-- `F(s, χ)`, plus `1/s²` when `χ` is even (so that all poles are simple). -/
noncomputable def explicitIntegrandL' (χ : DirichletCharacter ℂ N) (x : ℝ) (s : ℂ) : ℂ :=
  if dirichletParity χ = 1 then explicitIntegrandL χ x s
  else explicitIntegrandL χ x s + 1 / (s - 0) ^ 2

lemma differentiableAt_explicitIntegrandL {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) {x : ℝ}
    (hx : 0 < x) {s : ℂ} (hs0 : s ≠ 0) (hL : LFunction χ s ≠ 0) :
    DifferentiableAt ℂ (explicitIntegrandL χ x) s := by
  have han := analyticAt_LFunction hχ s
  exact ((han.deriv.differentiableAt.div han.differentiableAt hL).neg).mul
    (differentiableAt_perronKernel hx hs0)

lemma differentiableAt_explicitIntegrandL' {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) {x : ℝ}
    (hx : 0 < x) {s : ℂ} (hs0 : s ≠ 0) (hL : LFunction χ s ≠ 0) :
    DifferentiableAt ℂ (explicitIntegrandL' χ x) s := by
  have h1 := differentiableAt_explicitIntegrandL hχ hx hs0 hL
  by_cases ha : dirichletParity χ = 1
  · have e : explicitIntegrandL' χ x = explicitIntegrandL χ x :=
      funext fun s ↦ by simp only [explicitIntegrandL', ha, if_true]
    rw [e]; exact h1
  · have e : explicitIntegrandL' χ x = fun s ↦ explicitIntegrandL χ x s + 1 / (s - 0) ^ 2 :=
      funext fun s ↦ by simp only [explicitIntegrandL', ha, if_false]
    have h2 : DifferentiableAt ℂ (fun s : ℂ ↦ 1 / (s - 0) ^ 2) s := by
      simp only [sub_zero, one_div]
      exact ((differentiableAt_id (x := s)).pow 2).inv (pow_ne_zero 2 hs0)
    rw [e]; exact h1.add h2

/-- `L(s, χ) ≠ 0` for `-3/4 < σ ≤ 0`, `s ≠ 0` (primitive `χ` mod `q > 1`). -/
lemma LFunction_ne_zero_near_zero {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (hN : N ≠ 1)
    {s : ℂ} (hs0 : s ≠ 0) (h1 : -3 / 4 < s.re) (h2 : s.re ≤ 0) : LFunction χ s ≠ 0 := by
  refine LFunction_ne_zero_of_re_nonpos hχ hN (fun n hn ↦ ?_) h2
  have hre := congrArg Complex.re hn
  rcases dirichletParity_eq_zero_or_one χ with ha | ha
  · rw [ha] at hre hn
    simp at hre
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · simp at hn; exact hs0 hn
    · have : (1 : ℝ) ≤ n := by exact_mod_cast hn0
      linarith
  · rw [ha] at hre
    simp at hre
    linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]

/-- **The contour integral for `L`** (Davenport, Ch. 19, pp. 115-116): for primitive `χ` mod
`q > 1`, `x > 0`, `c > 1`, `T > 0` not an ordinate of a zero,
`∮ F'(s, χ) = 2πi (r₀ - ∑_{|γ|<T} x^ρ/ρ)` around the rectangle with corners `-1/2 - iT` and
`c + iT`, where `F' = F` for odd `χ` and `F' = F + 1/s²` for even `χ`. -/
theorem Davenport.rectIntegral_explicitIntegrandL' {χ : DirichletCharacter ℂ N}
    (hχ : χ.IsPrimitive) (hN : N ≠ 1) {x c T : ℝ} (hx : 0 < x) (hc : 1 < c) (hT : 0 < T)
    (hTz : ∀ ρ : ZeroIndex (dirichletXi χ), |ρ.val.im| ≠ T) :
    rectIntegral (explicitIntegrandL' χ x) (((-1 / 2 : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * I)
        ((c : ℂ) + (T : ℂ) * I) =
      2 * π * I * (residueZeroL χ x - ∑ ρ ∈ zerosBelowL hχ hN T, perronKernel x ρ.val) := by
  classical
  have hχ1 := ne_one_of_isPrimitive hχ hN
  set z₀ : ℂ := ((-1 / 2 : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * I with hz₀
  set w₀ : ℂ := (c : ℂ) + (T : ℂ) * I with hw₀
  have hz₀re : z₀.re = -1 / 2 := by simp [z₀]
  have hz₀im : z₀.im = -T := by simp [z₀]
  have hw₀re : w₀.re = c := by simp [w₀]
  have hw₀im : w₀.im = T := by simp [w₀]
  -- the poles
  set V : Finset ℂ := (zerosBelowL hχ hN T).image ZeroIndex.val with hV
  set P : Finset ℂ := insert 0 V with hP
  have hVre : ∀ p ∈ V, 0 < p.re ∧ p.re < 1 ∧ |p.im| < T := by
    intro p hp
    obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.mp hp
    exact ⟨(dirichletXi_zero_mem hχ hN ρ).2.1, (dirichletXi_zero_mem hχ hN ρ).2.2,
      mem_zerosBelowL.mp hρ⟩
  -- the open set `U`
  set Q : Finset ℂ := ((zerosBelowL hχ hN (T + 1)).image ZeroIndex.val) \ V with hQ
  set B : Set ℂ := {s : ℂ | -3 / 4 < s.re} ∩ {s : ℂ | s.re < c + 1} ∩
    {s : ℂ | |s.im| < T + 1} with hB
  have hBopen : IsOpen B :=
    ((isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)).inter
        (isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const)
  set U : Set ℂ := B \ ↑Q with hU
  have hUopen : IsOpen U := hBopen.sdiff Q.finite_toSet.isClosed
  have hRU : [[z₀.re, w₀.re]] ×ℂ [[z₀.im, w₀.im]] ⊆ U := by
    intro s hs
    rw [mem_reProdIm, hz₀re, hw₀re, hz₀im, hw₀im, uIcc_of_le (by linarith),
      uIcc_of_le (by linarith)] at hs
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · show -3 / 4 < s.re
      linarith [hs.1.1]
    · show s.re < c + 1
      linarith [hs.1.2]
    · show |s.im| < T + 1
      rw [abs_lt]; constructor <;> linarith [hs.2.1, hs.2.2]
    · intro hsQ
      rw [Finset.mem_coe, Finset.mem_sdiff, Finset.mem_image] at hsQ
      obtain ⟨⟨ρ, hρ, rfl⟩, hnV⟩ := hsQ
      apply hnV
      refine Finset.mem_image.mpr ⟨ρ, mem_zerosBelowL.mpr ?_, rfl⟩
      have h1 : |ρ.val.im| ≤ T := abs_le.mpr ⟨hs.2.1, hs.2.2⟩
      exact lt_of_le_of_ne h1 (hTz ρ)
  have hPin : ∀ p ∈ P, p ∈ Ioo z₀.re w₀.re ×ℂ Ioo z₀.im w₀.im := by
    intro p hp
    rw [mem_reProdIm, hz₀re, hw₀re, hz₀im, hw₀im]
    simp only [P, Finset.mem_insert] at hp
    rcases hp with rfl | hp
    · simp only [zero_re, zero_im, mem_Ioo]; exact ⟨⟨by norm_num, by linarith⟩, ⟨by linarith, hT⟩⟩
    · obtain ⟨h1, h2, h3⟩ := hVre p hp
      rw [abs_lt] at h3
      exact ⟨⟨by linarith, by linarith⟩, h3⟩
  -- holomorphy off the poles
  have hdiff : DifferentiableOn ℂ (explicitIntegrandL' χ x) (U \ ↑P) := by
    intro s ⟨⟨hsB, hsQ⟩, hsP⟩
    have hs0 : s ≠ 0 := fun h ↦ hsP (by simp [P, h])
    have hL : LFunction χ s ≠ 0 := by
      intro hz
      rcases le_or_gt s.re 0 with hre | hre
      · exact LFunction_ne_zero_near_zero hχ hN hs0 hsB.1.1 hre hz
      · obtain ⟨ρ, rfl⟩ := exists_zeroIndex_dirichletXi hχ hN hz hre
        have him : |ρ.val.im| < T + 1 := hsB.2
        by_cases hV' : ρ.val ∈ V
        · exact hsP (by simp [P, hV'])
        · exact hsQ (by
            rw [Finset.mem_coe, Finset.mem_sdiff]
            exact ⟨Finset.mem_image.mpr ⟨ρ, mem_zerosBelowL.mpr him, rfl⟩, hV'⟩)
    exact (differentiableAt_explicitIntegrandL' hχ1 hx hs0 hL).differentiableWithinAt
  -- the residues
  set r : ℂ → ℂ := fun p ↦ if p = 0 then residueZeroL χ x
    else -(analyticOrderNatAt (dirichletXi χ) p : ℂ) * perronKernel x p with hr
  have hres : ∀ p ∈ P, ∃ V' ∈ 𝓝 p, BddAbove (norm ∘ (fun s ↦ explicitIntegrandL' χ x s -
      r p / (s - p)) '' (V' \ {p})) := by
    intro p hp
    simp only [P, Finset.mem_insert] at hp
    rcases hp with rfl | hp
    · rcases dirichletParity_eq_zero_or_one χ with ha | ha
      · have := bddNear_explicitIntegrandL_origin_even hχ hN ha hx
        have e : ∀ s, explicitIntegrandL' χ x s = explicitIntegrandL χ x s + 1 / (s - 0) ^ 2 := by
          intro s; simp [explicitIntegrandL', ha]
        have er : r 0 = -((Real.log x : ℂ) + bEven χ) := by simp [r, residueZeroL, ha]
        simp only [e, er]
        exact this
      · have := bddNear_explicitIntegrandL_origin_odd hχ hN ha hx
        have e : ∀ s, explicitIntegrandL' χ x s = explicitIntegrandL χ x s := by
          intro s; simp [explicitIntegrandL', ha]
        have er : r 0 = -(deriv (LFunction χ) 0 / LFunction χ 0) := by
          simp [r, residueZeroL, ha]
        simp only [e, er]
        exact this
    · obtain ⟨ρ, -, rfl⟩ := Finset.mem_image.mp hp
      have h0 := (dirichletXi_zero_mem hχ hN ρ).2.1
      have hρ0 : ρ.val ≠ 0 := fun h ↦ by rw [h] at h0; simp at h0
      have h1 := bddNear_explicitIntegrandL_zero hχ hN hx ρ
      have er : r ρ.val =
          -(analyticOrderNatAt (dirichletXi χ) ρ.val : ℂ) * perronKernel x ρ.val := by
        simp [r, hρ0]
      rw [er]
      by_cases ha : dirichletParity χ = 1
      · have e : ∀ s, explicitIntegrandL' χ x s = explicitIntegrandL χ x s := fun s ↦ by
          simp only [explicitIntegrandL', ha, if_true]
        simp only [e]
        exact h1
      · have e : ∀ s, explicitIntegrandL' χ x s = explicitIntegrandL χ x s + 1 / (s - 0) ^ 2 :=
          fun s ↦ by simp only [explicitIntegrandL', ha, if_false]
        have h2 : BddNear (fun s : ℂ ↦ 1 / (s - 0) ^ 2) ρ.val := by
          apply bddNear_of_continuousAt
          simp only [sub_zero, one_div]
          exact (continuousAt_id.pow 2).inv₀ (pow_ne_zero 2 hρ0)
        simp only [e]
        refine (h1.add h2).congr (Eventually.of_forall fun s ↦ ?_)
        ring
  have hrect := rectIntegral_eq_sum_residues (z := z₀) (w := w₀) (by rw [hz₀re, hw₀re]; linarith)
    (by rw [hz₀im, hw₀im]; linarith) hUopen hRU r P hPin (explicitIntegrandL' χ x) hdiff hres
  rw [hrect]
  congr 1
  have h0V : (0 : ℂ) ∉ V := fun h ↦ by have := (hVre 0 h).1; norm_num at this
  rw [Finset.sum_insert h0V]
  have r0 : r 0 = residueZeroL χ x := by simp [r]
  have rV : ∑ p ∈ V, r p = -∑ ρ ∈ zerosBelowL hχ hN T, perronKernel x ρ.val := by
    rw [Finset.sum_comp (s := zerosBelowL hχ hN T) (f := perronKernel x) (g := ZeroIndex.val),
      ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun p hp ↦ ?_
    obtain ⟨h0, h1', h3⟩ := hVre p hp
    have hp0 : p ≠ 0 := fun h ↦ by rw [h] at h0; simp at h0
    rw [card_fiber_zerosBelowL h3]
    simp only [r, hp0, if_false, nsmul_eq_mul]
    ring
  rw [r0, rV]
  ring

end NTKB
