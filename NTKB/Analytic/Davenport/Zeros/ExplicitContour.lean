/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Davenport.Zeros.ZetaResidues
import NTKB.Analytic.Davenport.Zeros.Perron

/-!
# The contour integral of `-ζ'/ζ(s) x^s/s` around a rectangle

**Davenport, Ch. 17, pp. 107-108.** For `x > 0`, `c > 1`, `T > 0` not the ordinate of a zero and
`U = 2K + 1`, the integral of `F(s) = -ζ'(s)/ζ(s) · x^s/s` around the rectangle with vertices
`c ± iT`, `-U ± iT` is `2πi` times the sum of the residues
`x - ζ'(0)/ζ(0) - ∑_{|γ| < T} x^ρ/ρ + ∑_{k=1}^{K} x^{-2k}/(2k)`.
-/

open Filter Topology Complex Set
open scoped Real Interval

namespace NTKB

/-- `F(s) = -ζ'(s)/ζ(s) · x^s/s`. -/
noncomputable def explicitIntegrand (x : ℝ) (s : ℂ) : ℂ :=
  -(deriv riemannZeta s / riemannZeta s) * perronKernel x s

lemma bddNear_explicitIntegrand_zero {x : ℝ} (hx : 0 < x) (ρ : ZeroIndex riemannXi) :
    BddNear (fun s ↦ explicitIntegrand x s -
      (-(analyticOrderNatAt riemannXi ρ.val : ℂ)) * perronKernel x ρ.val / (s - ρ.val)) ρ.val := by
  have hρ := riemannXi_zero_mem ρ
  have hρ0 : ρ.val ≠ 0 := fun h ↦ by rw [h] at hρ; simp at hρ
  exact bddNear_mul_sub (bddNear_neg_logDeriv_riemannZeta_zero ρ)
    (differentiableAt_perronKernel hx hρ0)

lemma bddNear_explicitIntegrand_one {x : ℝ} (hx : 0 < x) :
    BddNear (fun s ↦ explicitIntegrand x s - 1 * perronKernel x 1 / (s - 1)) 1 :=
  bddNear_mul_sub bddNear_neg_logDeriv_riemannZeta_one
    (differentiableAt_perronKernel hx one_ne_zero)

lemma bddNear_explicitIntegrand_trivial {x : ℝ} (hx : 0 < x) (k : ℕ) :
    BddNear (fun s ↦ explicitIntegrand x s - (-1) * perronKernel x (-(2 * ((k : ℂ) + 1))) /
      (s - -(2 * ((k : ℂ) + 1)))) (-(2 * ((k : ℂ) + 1))) := by
  have h0 : -(2 * ((k : ℂ) + 1)) ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith [(k.cast_nonneg : (0 : ℝ) ≤ k)]
  exact bddNear_mul_sub (bddNear_neg_logDeriv_riemannZeta_trivial k)
    (differentiableAt_perronKernel hx h0)

lemma analyticAt_riemannZeta {s : ℂ} (hs : s ≠ 1) : AnalyticAt ℂ riemannZeta s :=
  DifferentiableOn.analyticAt (s := {1}ᶜ) (fun _ hz ↦ (differentiableAt_riemannZeta hz).differentiableWithinAt)
    (isOpen_compl_singleton.mem_nhds hs)

lemma bddNear_explicitIntegrand_origin {x : ℝ} (hx : 0 < x) :
    BddNear (fun s ↦ explicitIntegrand x s -
      (-(deriv riemannZeta 0 / riemannZeta 0)) / (s - 0)) 0 := by
  have han := analyticAt_riemannZeta (s := 0) zero_ne_one
  have hz0 : riemannZeta 0 ≠ 0 := by rw [riemannZeta_zero]; norm_num
  have hy' : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hG : DifferentiableAt ℂ (fun s ↦ -(deriv riemannZeta s / riemannZeta s) * (x : ℂ) ^ s) 0 :=
    ((han.deriv.differentiableAt.div han.differentiableAt hz0).neg).mul
      (differentiableAt_id.const_cpow (Or.inl hy'))
  have hh : BddNear (fun s : ℂ ↦ 1 / s - 1 / (s - 0)) 0 :=
    (bddNear_const 0 0).congr (Eventually.of_forall fun s ↦ by simp)
  refine (bddNear_mul_sub hh hG).congr ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  simp only [explicitIntegrand, perronKernel, Complex.cpow_zero, mul_one, one_mul, sub_zero]
  ring

/-- The zeros (with multiplicity) with `|γ| < T` are finitely many. -/
lemma finite_zeros_im_lt (T : ℝ) : {ρ : ZeroIndex riemannXi | |ρ.val.im| < T}.Finite := by
  have hF := finite_zeroIndex_closedBall differentiable_riemannXi (|T| + 1)
  refine (Set.finite_coe_iff.mp ?_).subset
    (s := {ρ : ZeroIndex riemannXi | ‖ρ.val‖ ≤ |T| + 1}) fun ρ hρ ↦ ?_
  · exact hF
  · simp only [Set.mem_ofPred_eq] at hρ ⊢
    have := norm_zeta_zero_le ρ
    linarith [le_abs_self T]

/-- The zeros `ρ` (with multiplicity) with `|γ| < T`. -/
noncomputable def zerosBelow (T : ℝ) : Finset (ZeroIndex riemannXi) :=
  (finite_zeros_im_lt T).toFinset

lemma mem_zerosBelow {T : ℝ} {ρ : ZeroIndex riemannXi} :
    ρ ∈ zerosBelow T ↔ |ρ.val.im| < T := by
  simp [zerosBelow]

/-- The fibre of `ZeroIndex.val` over a zero `p` has `m(p)` elements. -/
lemma card_fiber_zerosBelow {T : ℝ} {p : ℂ} (hp : |p.im| < T) :
    (Finset.filter (fun ρ : ZeroIndex riemannXi ↦ ρ.val = p) (zerosBelow T)).card =
      analyticOrderNatAt riemannXi p := by
  classical
  have : Finset.filter (fun ρ : ZeroIndex riemannXi ↦ ρ.val = p) (zerosBelow T) =
      Finset.univ.map ⟨fun i : Fin (analyticOrderNatAt riemannXi p) ↦ (⟨p, i⟩ : ZeroIndex riemannXi),
        fun i j h ↦ by simpa using h⟩ := by
    ext ρ
    simp only [Finset.mem_filter, mem_zerosBelow, Finset.mem_map, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨-, hρ⟩
      obtain ⟨z, i⟩ := ρ
      simp only [ZeroIndex.val] at hρ
      subst hρ
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨hp, rfl⟩
  rw [this, Finset.card_map, Finset.card_univ, Fintype.card_fin]

/-- The zeros of `ζ` are the trivial zeros and the zeros of `ξ`. -/
lemma riemannZeta_eq_zero_cases {s : ℂ} (hs : riemannZeta s = 0) (hs1 : s ≠ 1) :
    (∃ m : ℕ, s = -(2 * ((m : ℂ) + 1))) ∨ ∃ ρ : ZeroIndex riemannXi, ρ.val = s := by
  by_cases hΓ : ∀ m : ℕ, s / 2 + 1 ≠ -(m : ℂ)
  · right
    have hξ : riemannXi s = 0 := by
      rw [riemannXi_eq_mul_Gamma_add_one hs1 (Complex.Gamma_ne_zero hΓ), hs, mul_zero]
    exact exists_zeroIndex_val_eq differentiable_riemannXi (by simp) hξ
  · left
    push Not at hΓ
    obtain ⟨m, hm⟩ := hΓ
    exact ⟨m, by linear_combination 2 * hm⟩

/-- The residue of `F` at a pole `p`. -/
noncomputable def explicitResidue (x : ℝ) (p : ℂ) : ℂ :=
  if p = 1 then x else if p = 0 then -(deriv riemannZeta 0 / riemannZeta 0)
  else if 0 < p.re then -(analyticOrderNatAt riemannXi p : ℂ) * perronKernel x p
  else -perronKernel x p

lemma perronKernel_one (x : ℝ) : perronKernel x 1 = x := by simp [perronKernel]

/-- **The contour integral** (Davenport, Ch. 17, p. 107): for `x > 0`, `c > 1`, `T > 0` not an
ordinate of a zero, and `U = 2K + 1`,
`∮ F = 2πi (x - ζ'(0)/ζ(0) - ∑_{|γ| < T} x^ρ/ρ - ∑_{k < K} x^{-2(k+1)}/(-2(k+1)))`
around the rectangle with corners `-U - iT` and `c + iT`. -/
theorem Davenport.rectIntegral_explicitIntegrand {x c T : ℝ} (hx : 0 < x) (hc : 1 < c)
    (hT : 0 < T) (hTz : ∀ ρ : ZeroIndex riemannXi, |ρ.val.im| ≠ T) (K : ℕ) :
    rectIntegral (explicitIntegrand x) (((-(2 * K + 1) : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * I)
        ((c : ℂ) + (T : ℂ) * I) =
      2 * π * I * (x - deriv riemannZeta 0 / riemannZeta 0 -
        ∑ ρ ∈ zerosBelow T, perronKernel x ρ.val -
        ∑ k ∈ Finset.range K, perronKernel x (-(2 * ((k : ℂ) + 1)))) := by
  classical
  set z₀ : ℂ := ((-(2 * K + 1) : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * I with hz₀
  set w₀ : ℂ := (c : ℂ) + (T : ℂ) * I with hw₀
  have hz₀re : z₀.re = -(2 * K + 1) := by simp [z₀]
  have hz₀im : z₀.im = -T := by simp [z₀]
  have hw₀re : w₀.re = c := by simp [w₀]
  have hw₀im : w₀.im = T := by simp [w₀]
  have hK0 : (0 : ℝ) ≤ K := K.cast_nonneg
  -- the poles
  set V : Finset ℂ := (zerosBelow T).image ZeroIndex.val with hV
  set Ts : Finset ℂ := (Finset.range K).image fun k : ℕ ↦ -(2 * ((k : ℂ) + 1)) with hTs
  set P : Finset ℂ := insert 1 (insert 0 (V ∪ Ts)) with hP
  have hVre : ∀ p ∈ V, 0 < p.re ∧ p.re < 1 ∧ |p.im| < T := by
    intro p hp
    obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.mp hp
    exact ⟨(riemannXi_zero_mem ρ).2.1, (riemannXi_zero_mem ρ).2.2, mem_zerosBelow.mp hρ⟩
  have hTsre : ∀ p ∈ Ts, p.re < 0 ∧ -(2 * K) ≤ p.re ∧ p.im = 0 := by
    intro p hp
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hp
    have hk' : (k : ℝ) + 1 ≤ K := by exact_mod_cast Finset.mem_range.mp hk
    simp only [neg_re, mul_re, re_ofNat, add_re, natCast_re, one_re, im_ofNat, add_im, natCast_im,
      one_im, add_zero, mul_zero, sub_zero, neg_im, mul_im, zero_mul, neg_zero]
    refine ⟨by linarith [(k.cast_nonneg : (0 : ℝ) ≤ k)], by linarith, trivial⟩
  -- the open set `U`
  set Q : Finset ℂ := ((zerosBelow (T + 1)).image ZeroIndex.val) \ V with hQ
  set B : Set ℂ := {s : ℂ | -(2 * K + 1) - 1 / 2 < s.re} ∩ {s : ℂ | s.re < c + 1} ∩
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
    · show -(2 * (K : ℝ) + 1) - 1 / 2 < s.re
      linarith [hs.1.1]
    · show s.re < c + 1
      linarith [hs.1.2]
    · show |s.im| < T + 1
      rw [abs_lt]; constructor <;> linarith [hs.2.1, hs.2.2]
    · intro hsQ
      rw [Finset.mem_coe, Finset.mem_sdiff, Finset.mem_image] at hsQ
      obtain ⟨⟨ρ, hρ, rfl⟩, hnV⟩ := hsQ
      apply hnV
      refine Finset.mem_image.mpr ⟨ρ, mem_zerosBelow.mpr ?_, rfl⟩
      have h1 : |ρ.val.im| ≤ T := abs_le.mpr ⟨hs.2.1, hs.2.2⟩
      exact lt_of_le_of_ne h1 (hTz ρ)
  -- the poles lie in the open rectangle
  have hPin : ∀ p ∈ P, p ∈ Ioo z₀.re w₀.re ×ℂ Ioo z₀.im w₀.im := by
    intro p hp
    rw [mem_reProdIm, hz₀re, hw₀re, hz₀im, hw₀im]
    simp only [P, Finset.mem_insert, Finset.mem_union] at hp
    rcases hp with rfl | rfl | hp | hp
    · simp only [one_re, one_im, mem_Ioo]; exact ⟨⟨by linarith, hc⟩, ⟨by linarith, hT⟩⟩
    · simp only [zero_re, zero_im, mem_Ioo]; exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, hT⟩⟩
    · obtain ⟨h1, h2, h3⟩ := hVre p hp
      rw [abs_lt] at h3
      exact ⟨⟨by linarith, by linarith⟩, h3⟩
    · obtain ⟨h1, h2, h3⟩ := hTsre p hp
      rw [h3]
      exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, hT⟩⟩
  -- `F` is holomorphic on `U` minus the poles
  have hdiff : DifferentiableOn ℂ (explicitIntegrand x) (U \ ↑P) := by
    intro s ⟨⟨hsB, hsQ⟩, hsP⟩
    have hs1 : s ≠ 1 := fun h ↦ hsP (by simp [P, h])
    have hs0 : s ≠ 0 := fun h ↦ hsP (by simp [P, h])
    have hz : riemannZeta s ≠ 0 := by
      intro hz
      rcases riemannZeta_eq_zero_cases hz hs1 with ⟨m, rfl⟩ | ⟨ρ, rfl⟩
      · apply hsP
        have hre := hsB.1.1
        simp only [Set.mem_ofPred_eq, neg_re, mul_re, re_ofNat, add_re, natCast_re, one_re,
          im_ofNat, add_im, natCast_im, one_im, add_zero, mul_zero, sub_zero] at hre
        have hmK : m < K := by
          have : (m : ℝ) + 1 < K + 1 := by linarith
          exact_mod_cast (show (m : ℝ) < K by linarith)
        simp only [P, Finset.mem_coe, Finset.mem_insert, Finset.mem_union, Ts,
          Finset.mem_image, Finset.mem_range]
        exact Or.inr (Or.inr (Or.inr ⟨m, hmK, rfl⟩))
      · have him : |ρ.val.im| < T + 1 := hsB.2
        by_cases hV' : ρ.val ∈ V
        · exact hsP (by simp [P, hV'])
        · exact hsQ (by
            rw [Finset.mem_coe, Finset.mem_sdiff]
            exact ⟨Finset.mem_image.mpr ⟨ρ, mem_zerosBelow.mpr him, rfl⟩, hV'⟩)
    have han := analyticAt_riemannZeta hs1
    refine (((han.deriv.differentiableAt.div han.differentiableAt hz).neg).mul
      (differentiableAt_perronKernel hx hs0)).differentiableWithinAt
  -- the residues
  have hres : ∀ p ∈ P, ∃ V' ∈ 𝓝 p, BddAbove (norm ∘ (fun s ↦ explicitIntegrand x s -
      explicitResidue x p / (s - p)) '' (V' \ {p})) := by
    intro p hp
    simp only [P, Finset.mem_insert, Finset.mem_union] at hp
    rcases hp with rfl | rfl | hp | hp
    · have := bddNear_explicitIntegrand_one hx
      simp only [explicitResidue, ↓reduceIte, perronKernel_one, one_mul] at this ⊢
      exact this
    · have := bddNear_explicitIntegrand_origin hx
      simp only [explicitResidue, zero_ne_one, ite_false, ite_true] at this ⊢
      exact this
    · obtain ⟨ρ, -, rfl⟩ := Finset.mem_image.mp hp
      have h0 := (riemannXi_zero_mem ρ).2.1
      have h1 : ρ.val ≠ 1 := fun h ↦ by have := (riemannXi_zero_mem ρ).2.2; rw [h] at this; simp at this
      have h2 : ρ.val ≠ 0 := fun h ↦ by rw [h] at h0; simp at h0
      have := bddNear_explicitIntegrand_zero hx ρ
      simp only [explicitResidue, h1, h2, h0, ite_false, ite_true] at this ⊢
      exact this
    · obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hp
      have hre : (-(2 * ((k : ℂ) + 1))).re < 0 := by
        simp; linarith [(k.cast_nonneg : (0 : ℝ) ≤ k)]
      have h1 : -(2 * ((k : ℂ) + 1)) ≠ 1 := fun h ↦ by rw [h] at hre; norm_num at hre
      have h2 : -(2 * ((k : ℂ) + 1)) ≠ 0 := fun h ↦ by rw [h] at hre; norm_num at hre
      have := bddNear_explicitIntegrand_trivial hx k
      simp only [explicitResidue, h1, h2, not_lt.mpr hre.le, ite_false, neg_one_mul] at this ⊢
      exact this
  have hrect := rectIntegral_eq_sum_residues (z := z₀) (w := w₀) (by rw [hz₀re, hw₀re]; linarith)
    (by rw [hz₀im, hw₀im]; linarith) hUopen hRU (explicitResidue x) P hPin
    (explicitIntegrand x) hdiff hres
  rw [hrect]
  congr 1
  -- evaluate the sum of the residues
  have h1P : (1 : ℂ) ∉ insert 0 (V ∪ Ts) := by
    simp only [Finset.mem_insert, Finset.mem_union, not_or]
    refine ⟨one_ne_zero, fun h ↦ ?_, fun h ↦ ?_⟩
    · have := (hVre 1 h).2.1; norm_num at this
    · have := (hTsre 1 h).1; norm_num at this
  have h0P : (0 : ℂ) ∉ V ∪ Ts := by
    simp only [Finset.mem_union, not_or]
    refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · have := (hVre 0 h).1; norm_num at this
    · have := (hTsre 0 h).1; norm_num at this
  have hdisj : Disjoint V Ts := by
    rw [Finset.disjoint_left]
    intro p hpV hpT
    linarith [(hVre p hpV).1, (hTsre p hpT).1]
  rw [Finset.sum_insert h1P, Finset.sum_insert h0P, Finset.sum_union hdisj]
  have r1 : explicitResidue x 1 = x := by simp [explicitResidue]
  have r0 : explicitResidue x 0 = -(deriv riemannZeta 0 / riemannZeta 0) := by
    simp [explicitResidue]
  have rV : ∑ p ∈ V, explicitResidue x p = -∑ ρ ∈ zerosBelow T, perronKernel x ρ.val := by
    rw [Finset.sum_comp (s := zerosBelow T) (f := perronKernel x) (g := ZeroIndex.val),
      ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun p hp ↦ ?_
    obtain ⟨h0, h1', h3⟩ := hVre p hp
    have hp1 : p ≠ 1 := fun h ↦ by rw [h] at h1'; simp at h1'
    have hp0 : p ≠ 0 := fun h ↦ by rw [h] at h0; simp at h0
    rw [card_fiber_zerosBelow h3]
    simp only [explicitResidue, hp1, hp0, h0, ite_false, ite_true, nsmul_eq_mul]
    ring
  have rT : ∑ p ∈ Ts, explicitResidue x p =
      -∑ k ∈ Finset.range K, perronKernel x (-(2 * ((k : ℂ) + 1))) := by
    rw [Finset.sum_image (fun a _ b _ h ↦ by
      have : (a : ℂ) = b := by linear_combination -h / 2
      exact_mod_cast this), ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    have hre : (-(2 * ((k : ℂ) + 1))).re < 0 := by
      simp; linarith [(k.cast_nonneg : (0 : ℝ) ≤ k)]
    have h1 : -(2 * ((k : ℂ) + 1)) ≠ 1 := fun h ↦ by rw [h] at hre; norm_num at hre
    have h2 : -(2 * ((k : ℂ) + 1)) ≠ 0 := fun h ↦ by rw [h] at hre; norm_num at hre
    simp only [explicitResidue, h1, h2, not_lt.mpr hre.le, ite_false]
  rw [r1, r0, rV, rT]
  ring

end NTKB
