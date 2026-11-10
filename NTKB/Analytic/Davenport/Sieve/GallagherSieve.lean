/- Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license. -/
import NTKB.Analytic.Davenport.Sieve.Gallagher
import NTKB.Analytic.Davenport.Sieve.LargeSieve
import Mathlib.Analysis.Real.Pi.Bounds
import NTKB.Attr

/-!
# Gallagher's form of the large sieve
(Davenport, Multiplicative Number Theory, ch. 27, pp. 156–157)

For `S(α) = ∑_{M < n ≤ M + N} a_n e(nα)` and points `α_r` with `‖α_r - α_t‖ ≥ δ` (`r ≠ t`),
`∑_r |S(α_r)|² ≤ (πN + 1/δ) ∑_n |a_n|²` (`large_sieve_gallagher`).

Davenport's proof: the midpoint form of Gallagher's lemma
`|f(x)| ≤ δ⁻¹ ∫_{x-δ/2}^{x+δ/2} |f| + ½ ∫_{x-δ/2}^{x+δ/2} |f'|` (`norm_le_midpoint`) is applied to
`f = S²`; the intervals around the `α_r` (reduced mod 1) are disjoint and fit into one period
(`sum_integral_le_of_separated`), so the sum is at most `δ⁻¹ ∫₀¹ |S|² + ∫₀¹ |S S'|`; Parseval and
the arithmetic–geometric mean inequality finish, after recentring so that `|n| ≤ N/2`.
-/

namespace NTKB.Davenport

open Finset Real

/-- The trigonometric polynomial `∑_{n ∈ F} c_n e(nx)`. -/
noncomputable def trigPoly (F : Finset ℤ) (c : ℤ → ℂ) (x : ℝ) : ℂ :=
  ∑ n ∈ F, c n * Complex.exp (2 * π * Complex.I * (n * x))

lemma trigPoly_periodic (F : Finset ℤ) (c : ℤ → ℂ) : Function.Periodic (trigPoly F c) 1 := by
  intro x
  unfold trigPoly
  refine Finset.sum_congr rfl fun n _ => ?_
  congr 1
  rw [show 2 * (π : ℂ) * Complex.I * ((n : ℂ) * ((x + 1 : ℝ) : ℂ)) =
      2 * π * Complex.I * ((n : ℂ) * (x : ℂ)) + n * (2 * π * Complex.I) by push_cast; ring,
    Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

lemma trigPoly_continuous (F : Finset ℤ) (c : ℤ → ℂ) : Continuous (trigPoly F c) := by
  unfold trigPoly
  exact continuous_finsetSum _ fun n _ => by fun_prop

lemma trigPoly_hasDerivAt (F : Finset ℤ) (c : ℤ → ℂ) (x : ℝ) :
    HasDerivAt (trigPoly F c) (trigPoly F (fun n => 2 * π * Complex.I * n * c n) x) x := by
  unfold trigPoly
  have h : ∀ n ∈ F, HasDerivAt
      (fun x : ℝ => c n * Complex.exp (2 * π * Complex.I * ((n : ℂ) * (x : ℂ))))
      ((2 * π * Complex.I * n * c n) * Complex.exp (2 * π * Complex.I * ((n : ℂ) * (x : ℂ)))) x := by
    intro n _
    have h1 : HasDerivAt (fun x : ℝ => (x : ℂ)) 1 x := by
      simpa using (hasDerivAt_id x).ofReal_comp
    have h2 := ((h1.const_mul (n : ℂ)).const_mul (2 * π * Complex.I)).cexp.const_mul (c n)
    convert h2 using 1
    ring
  exact HasDerivAt.fun_sum h

lemma parseval_trig (F : Finset ℤ) (a : ℤ → ℂ) :
    ∫ x in (0 : ℝ)..1, ‖trigPoly F a x‖ ^ 2 = ∑ n ∈ F, ‖a n‖ ^ 2 :=
  integral_norm_sum_exp_sq F a

/-! ### The midpoint form of Gallagher's lemma -/

lemma gallagher_ibp_global {f f' : ℝ → ℂ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (hf' : Continuous f') (a b c : ℝ) :
    ∫ t in a..b, ((t : ℂ) - c) * f' t =
      ((b : ℂ) - c) * f b - ((a : ℂ) - c) * f a - ∫ t in a..b, f t := by
  have := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := a) (b := b)
    (u := fun t : ℝ => (t : ℂ) - c) (u' := fun _ => (1 : ℂ)) (v := f) (v' := f')
    (fun x _ => by
      have h := (hasDerivAt_id x).ofReal_comp
      simpa using h.sub_const (c : ℂ))
    (fun x _ => hf x)
    intervalIntegrable_const
    (hf'.intervalIntegrable _ _)
  simpa using this

/-- `|f(x)| ≤ δ⁻¹ ∫_{x-δ/2}^{x+δ/2} |f| + ½ ∫_{x-δ/2}^{x+δ/2} |f'|`. -/
lemma norm_le_midpoint {f f' : ℝ → ℂ} (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : Continuous f')
    {δ : ℝ} (hδ : 0 < δ) (x : ℝ) :
    ‖f x‖ ≤ δ⁻¹ * (∫ t in (x - δ / 2)..(x + δ / 2), ‖f t‖) +
      (1 / 2) * ∫ t in (x - δ / 2)..(x + δ / 2), ‖f' t‖ := by
  have hfc : Continuous f := continuous_iff_continuousAt.2 fun y => (hf y).continuousAt
  have h1 := gallagher_ibp_global hf hf' (x - δ / 2) x (x - δ / 2)
  have h2 := gallagher_ibp_global hf hf' x (x + δ / 2) (x + δ / 2)
  have hadd : (∫ t in (x - δ / 2)..x, f t) + ∫ t in x..(x + δ / 2), f t =
      ∫ t in (x - δ / 2)..(x + δ / 2), f t :=
    intervalIntegral.integral_add_adjacent_intervals (hfc.intervalIntegrable _ _)
      (hfc.intervalIntegrable _ _)
  have hgadd : (∫ t in (x - δ / 2)..x, ‖f' t‖) + ∫ t in x..(x + δ / 2), ‖f' t‖ =
      ∫ t in (x - δ / 2)..(x + δ / 2), ‖f' t‖ :=
    intervalIntegral.integral_add_adjacent_intervals (hf'.norm.intervalIntegrable _ _)
      (hf'.norm.intervalIntegrable _ _)
  have key : (δ : ℂ) * f x = (∫ t in (x - δ / 2)..(x + δ / 2), f t) +
      (∫ t in (x - δ / 2)..x, ((t : ℂ) - ((x - δ / 2 : ℝ) : ℂ)) * f' t) +
      ∫ t in x..(x + δ / 2), ((t : ℂ) - ((x + δ / 2 : ℝ) : ℂ)) * f' t := by
    rw [h1, h2, ← hadd]
    push_cast
    ring
  have bP : ‖∫ t in (x - δ / 2)..x, ((t : ℂ) - ((x - δ / 2 : ℝ) : ℂ)) * f' t‖ ≤
      (δ / 2) * ∫ t in (x - δ / 2)..x, ‖f' t‖ := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.norm_integral_le_of_norm_le (by linarith)
      (Filter.Eventually.of_forall (fun t ht => ?_))
      ((hf'.norm.const_mul _).intervalIntegrable _ _)
    have e : ((t : ℂ) - ((x - δ / 2 : ℝ) : ℂ)) = ((t - (x - δ / 2) : ℝ) : ℂ) := by
      push_cast; ring
    rw [norm_mul, e, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith [ht.1])]
    exact mul_le_mul_of_nonneg_right (by linarith [ht.2]) (norm_nonneg _)
  have bQ : ‖∫ t in x..(x + δ / 2), ((t : ℂ) - ((x + δ / 2 : ℝ) : ℂ)) * f' t‖ ≤
      (δ / 2) * ∫ t in x..(x + δ / 2), ‖f' t‖ := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.norm_integral_le_of_norm_le (by linarith)
      (Filter.Eventually.of_forall (fun t ht => ?_))
      ((hf'.norm.const_mul _).intervalIntegrable _ _)
    have e : ((t : ℂ) - ((x + δ / 2 : ℝ) : ℂ)) = ((t - (x + δ / 2) : ℝ) : ℂ) := by
      push_cast; ring
    rw [norm_mul, e, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith [ht.2])]
    exact mul_le_mul_of_nonneg_right (by linarith [ht.1]) (norm_nonneg _)
  have bI : ‖∫ t in (x - δ / 2)..(x + δ / 2), f t‖ ≤ ∫ t in (x - δ / 2)..(x + δ / 2), ‖f t‖ :=
    intervalIntegral.norm_integral_le_integral_norm (by linarith)
  have hnorm : δ * ‖f x‖ ≤ (∫ t in (x - δ / 2)..(x + δ / 2), ‖f t‖) +
      (δ / 2) * ∫ t in (x - δ / 2)..(x + δ / 2), ‖f' t‖ := by
    have e : δ * ‖f x‖ = ‖(δ : ℂ) * f x‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ]
    rw [e, key]
    calc _ ≤ ‖∫ t in (x - δ / 2)..(x + δ / 2), f t‖ +
          ‖∫ t in (x - δ / 2)..x, ((t : ℂ) - ((x - δ / 2 : ℝ) : ℂ)) * f' t‖ +
          ‖∫ t in x..(x + δ / 2), ((t : ℂ) - ((x + δ / 2 : ℝ) : ℂ)) * f' t‖ :=
          (norm_add_le _ _).trans (by gcongr; exact norm_add_le _ _)
      _ ≤ _ := by rw [← hgadd]; linarith
  calc ‖f x‖ = δ⁻¹ * (δ * ‖f x‖) := by field_simp
    _ ≤ δ⁻¹ * ((∫ t in (x - δ / 2)..(x + δ / 2), ‖f t‖) +
        (δ / 2) * ∫ t in (x - δ / 2)..(x + δ / 2), ‖f' t‖) :=
        mul_le_mul_of_nonneg_left hnorm (by positivity)
    _ = _ := by field_simp

/-! ### Disjoint intervals inside a period -/

lemma sum_integral_le_of_separated {ι : Type*} (s : Finset ι) (c : ι → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (u : ℝ) (G : ℝ → ℝ) (hG : Continuous G) (hG0 : ∀ x, 0 ≤ G x)
    (hsep : ∀ r ∈ s, ∀ t ∈ s, r ≠ t → δ ≤ |c r - c t|)
    (hsub : ∀ r ∈ s, u ≤ c r - δ / 2 ∧ c r + δ / 2 ≤ u + 1) :
    ∑ r ∈ s, ∫ x in (c r - δ / 2)..(c r + δ / 2), G x ≤ ∫ x in u..(u + 1), G x := by
  have hle : ∀ r, c r - δ / 2 ≤ c r + δ / 2 := fun r => by linarith
  have h1 : ∀ r ∈ s, ∫ x in (c r - δ / 2)..(c r + δ / 2), G x =
      ∫ x in Set.Ioc (c r - δ / 2) (c r + δ / 2), G x :=
    fun r _ => intervalIntegral.integral_of_le (hle r)
  rw [Finset.sum_congr rfl h1, intervalIntegral.integral_of_le (by linarith : u ≤ u + 1)]
  have hpair : Set.Pairwise (↑s : Set ι)
      (Function.onFun Disjoint fun r => Set.Ioc (c r - δ / 2) (c r + δ / 2)) := by
    intro r hr t ht hrt
    simp only [Function.onFun]
    rw [Set.disjoint_left]
    intro x hx hx'
    have := hsep r hr t ht hrt
    rcases le_abs.1 this with h | h
    · linarith [hx.1, hx.2, hx'.1, hx'.2]
    · linarith [hx.1, hx.2, hx'.1, hx'.2]
  have hU := MeasureTheory.integral_biUnion_finset s (f := G) (μ := MeasureTheory.volume)
    (s := fun r => Set.Ioc (c r - δ / 2) (c r + δ / 2)) (fun r _ => measurableSet_Ioc) hpair
    (fun r _ => hG.integrableOn_Ioc)
  rw [← hU]
  refine MeasureTheory.setIntegral_mono_set (μ := MeasureTheory.volume) hG.integrableOn_Ioc
    (Filter.Eventually.of_forall (fun x => hG0 x)) ?_
  refine Filter.Eventually.of_forall (fun x hx => ?_)
  obtain ⟨r, hr, hx⟩ := Set.mem_iUnion₂.1 hx
  exact ⟨lt_of_le_of_lt (hsub r hr).1 hx.1, hx.2.trans (hsub r hr).2⟩

/-! ### Estimates for trigonometric polynomials -/

lemma sq_norm_le_integral (F : Finset ℤ) (a : ℤ → ℂ) {δ : ℝ} (hδ : 0 < δ) (x : ℝ) :
    ‖trigPoly F a x‖ ^ 2 ≤ ∫ t in (x - δ / 2)..(x + δ / 2),
      (δ⁻¹ * ‖trigPoly F a t‖ ^ 2 +
        ‖trigPoly F a t‖ * ‖trigPoly F (fun n => 2 * π * Complex.I * n * a n) t‖) := by
  have hSc : Continuous (trigPoly F a) := trigPoly_continuous F a
  have hS'c : Continuous (trigPoly F (fun n => 2 * π * Complex.I * n * a n)) :=
    trigPoly_continuous F _
  have hd : ∀ y, HasDerivAt (fun y => trigPoly F a y * trigPoly F a y)
      (trigPoly F (fun n => 2 * π * Complex.I * n * a n) y * trigPoly F a y +
        trigPoly F a y * trigPoly F (fun n => 2 * π * Complex.I * n * a n) y) y :=
    fun y => (trigPoly_hasDerivAt F a y).mul (trigPoly_hasDerivAt F a y)
  have hf'c : Continuous fun y => trigPoly F (fun n => 2 * π * Complex.I * n * a n) y *
      trigPoly F a y + trigPoly F a y * trigPoly F (fun n => 2 * π * Complex.I * n * a n) y :=
    (hS'c.mul hSc).add (hSc.mul hS'c)
  have hm := norm_le_midpoint hd hf'c hδ x
  have e1 : ∀ y, ‖trigPoly F a y * trigPoly F a y‖ = ‖trigPoly F a y‖ ^ 2 :=
    fun y => by rw [norm_mul, sq]
  simp only [e1] at hm
  have hb : ∀ y, ‖trigPoly F (fun n => 2 * π * Complex.I * n * a n) y * trigPoly F a y +
      trigPoly F a y * trigPoly F (fun n => 2 * π * Complex.I * n * a n) y‖ ≤
      2 * (‖trigPoly F a y‖ * ‖trigPoly F (fun n => 2 * π * Complex.I * n * a n) y‖) :=
    fun y => by
      calc _ ≤ ‖trigPoly F (fun n => 2 * π * Complex.I * n * a n) y * trigPoly F a y‖ +
            ‖trigPoly F a y * trigPoly F (fun n => 2 * π * Complex.I * n * a n) y‖ :=
            norm_add_le _ _
        _ = _ := by rw [norm_mul, norm_mul]; ring
  have hI : ∫ t in (x - δ / 2)..(x + δ / 2),
      ‖trigPoly F (fun n => 2 * π * Complex.I * n * a n) t * trigPoly F a t +
        trigPoly F a t * trigPoly F (fun n => 2 * π * Complex.I * n * a n) t‖ ≤
      ∫ t in (x - δ / 2)..(x + δ / 2), 2 * (‖trigPoly F a t‖ *
        ‖trigPoly F (fun n => 2 * π * Complex.I * n * a n) t‖) :=
    intervalIntegral.integral_mono_on (μ := MeasureTheory.volume)
    (by linarith) (hf'c.norm.intervalIntegrable _ _)
    ((continuous_const.mul (hSc.norm.mul hS'c.norm)).intervalIntegrable _ _)
    (fun y _ => hb y)
  rw [intervalIntegral.integral_const_mul] at hI
  have hsplit : ∫ t in (x - δ / 2)..(x + δ / 2),
      (δ⁻¹ * ‖trigPoly F a t‖ ^ 2 +
        ‖trigPoly F a t‖ * ‖trigPoly F (fun n => 2 * π * Complex.I * n * a n) t‖) =
      δ⁻¹ * (∫ t in (x - δ / 2)..(x + δ / 2), ‖trigPoly F a t‖ ^ 2) +
      ∫ t in (x - δ / 2)..(x + δ / 2),
        ‖trigPoly F a t‖ * ‖trigPoly F (fun n => 2 * π * Complex.I * n * a n) t‖ := by
    rw [intervalIntegral.integral_add, intervalIntegral.integral_const_mul]
    · exact (continuous_const.mul (hSc.norm.pow 2)).intervalIntegrable _ _
    · exact (hSc.norm.mul hS'c.norm).intervalIntegrable _ _
  rw [hsplit]
  linarith

lemma integral_cross_le (K : ℕ) (a : ℤ → ℂ) :
    ∫ x in (0 : ℝ)..1, ‖trigPoly (Icc (-(K : ℤ)) K) a x‖ *
        ‖trigPoly (Icc (-(K : ℤ)) K) (fun n => 2 * π * Complex.I * n * a n) x‖ ≤
      2 * π * K * ∑ n ∈ Icc (-(K : ℤ)) K, ‖a n‖ ^ 2 := by
  have hSc : Continuous (trigPoly (Icc (-(K : ℤ)) K) a) := trigPoly_continuous _ a
  have hS'c : Continuous (trigPoly (Icc (-(K : ℤ)) K) (fun n => 2 * π * Complex.I * n * a n)) :=
    trigPoly_continuous _ _
  have hB : ∑ n ∈ Icc (-(K : ℤ)) K, ‖2 * π * Complex.I * n * a n‖ ^ 2 ≤
      (2 * π * K) ^ 2 * ∑ n ∈ Icc (-(K : ℤ)) K, ‖a n‖ ^ 2 := by
    rw [mul_sum]
    refine sum_le_sum fun n hn => ?_
    have hn' : |(n : ℝ)| ≤ K := by
      rw [abs_le]
      simp only [mem_Icc] at hn
      constructor
      · exact_mod_cast hn.1
      · exact_mod_cast hn.2
    have e : ‖2 * π * Complex.I * n * a n‖ = 2 * π * |(n : ℝ)| * ‖a n‖ := by
      simp [abs_of_pos Real.pi_pos]
    rw [e]
    have : 2 * π * |(n : ℝ)| ≤ 2 * π * K := by gcongr
    calc (2 * π * |(n : ℝ)| * ‖a n‖) ^ 2 = (2 * π * |(n : ℝ)|) ^ 2 * ‖a n‖ ^ 2 := by ring
      _ ≤ (2 * π * K) ^ 2 * ‖a n‖ ^ 2 := by gcongr
  have hB' : ∫ x in (0 : ℝ)..1,
      ‖trigPoly (Icc (-(K : ℤ)) K) (fun n => 2 * π * Complex.I * n * a n) x‖ ^ 2 ≤
      (2 * π * K) ^ 2 * ∑ n ∈ Icc (-(K : ℤ)) K, ‖a n‖ ^ 2 :=
    (parseval_trig _ _).le.trans hB
  have hA := parseval_trig (Icc (-(K : ℤ)) K) a
  rcases Nat.eq_zero_or_pos K with hK | hK
  · subst hK
    have h0 : ∀ x, trigPoly (Icc (-((0 : ℕ) : ℤ)) ((0 : ℕ) : ℤ))
        (fun n => 2 * π * Complex.I * n * a n) x = 0 := by
      intro x; simp [trigPoly]
    simp only [h0, norm_zero, mul_zero, intervalIntegral.integral_zero]
    simp
  · have ht : 0 < 2 * π * K := by positivity
    have hpt : ∀ x, ‖trigPoly (Icc (-(K : ℤ)) K) a x‖ *
        ‖trigPoly (Icc (-(K : ℤ)) K) (fun n => 2 * π * Complex.I * n * a n) x‖ ≤
        (2 * π * K / 2) * ‖trigPoly (Icc (-(K : ℤ)) K) a x‖ ^ 2 +
        (1 / (2 * (2 * π * K))) *
          ‖trigPoly (Icc (-(K : ℤ)) K) (fun n => 2 * π * Complex.I * n * a n) x‖ ^ 2 := by
      intro x
      rw [← sub_nonneg]
      have : (2 * π * K / 2) * ‖trigPoly (Icc (-(K : ℤ)) K) a x‖ ^ 2 +
          (1 / (2 * (2 * π * K))) *
            ‖trigPoly (Icc (-(K : ℤ)) K) (fun n => 2 * π * Complex.I * n * a n) x‖ ^ 2 -
          ‖trigPoly (Icc (-(K : ℤ)) K) a x‖ *
            ‖trigPoly (Icc (-(K : ℤ)) K) (fun n => 2 * π * Complex.I * n * a n) x‖ =
          (‖trigPoly (Icc (-(K : ℤ)) K) a x‖ * (2 * π * K) -
            ‖trigPoly (Icc (-(K : ℤ)) K) (fun n => 2 * π * Complex.I * n * a n) x‖) ^ 2 /
            (2 * (2 * π * K)) := by
        field_simp
        ring
      rw [this]
      positivity
    calc _ ≤ ∫ x in (0 : ℝ)..1,
          ((2 * π * K / 2) * ‖trigPoly (Icc (-(K : ℤ)) K) a x‖ ^ 2 +
          (1 / (2 * (2 * π * K))) *
            ‖trigPoly (Icc (-(K : ℤ)) K) (fun n => 2 * π * Complex.I * n * a n) x‖ ^ 2) :=
          intervalIntegral.integral_mono_on zero_le_one
            ((hSc.norm.mul hS'c.norm).intervalIntegrable _ _)
            (((continuous_const.mul (hSc.norm.pow 2)).add
              (continuous_const.mul (hS'c.norm.pow 2))).intervalIntegrable _ _)
            (fun x _ => hpt x)
      _ = (2 * π * K / 2) * (∫ x in (0 : ℝ)..1, ‖trigPoly (Icc (-(K : ℤ)) K) a x‖ ^ 2) +
          (1 / (2 * (2 * π * K))) * ∫ x in (0 : ℝ)..1,
            ‖trigPoly (Icc (-(K : ℤ)) K) (fun n => 2 * π * Complex.I * n * a n) x‖ ^ 2 := by
          rw [intervalIntegral.integral_add, intervalIntegral.integral_const_mul,
            intervalIntegral.integral_const_mul]
          · exact (continuous_const.mul (hSc.norm.pow 2)).intervalIntegrable _ _
          · exact (continuous_const.mul (hS'c.norm.pow 2)).intervalIntegrable _ _
      _ ≤ (2 * π * K / 2) * ∑ n ∈ Icc (-(K : ℤ)) K, ‖a n‖ ^ 2 +
          (1 / (2 * (2 * π * K))) * ((2 * π * K) ^ 2 * ∑ n ∈ Icc (-(K : ℤ)) K, ‖a n‖ ^ 2) := by
          rw [hA]
          gcongr
      _ = _ := by field_simp; ring

/-- Centred form of Gallagher's large sieve. -/
theorem large_sieve_gallagher_centred {ι : Type*} (s : Finset ι) (α : ι → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) (hsep : ∀ r ∈ s, ∀ t ∈ s, r ≠ t → ∀ m : ℤ, δ ≤ |α r - α t - m|)
    (K : ℕ) (a : ℤ → ℂ) :
    ∑ r ∈ s, ‖∑ k ∈ Icc (-(K : ℤ)) K, a k * Complex.exp (2 * π * Complex.I * (k * α r))‖ ^ 2 ≤
      (2 * π * K + 1 / δ) * ∑ k ∈ Icc (-(K : ℤ)) K, ‖a k‖ ^ 2 := by
  classical
  change ∑ r ∈ s, ‖trigPoly (Icc (-(K : ℤ)) K) a (α r)‖ ^ 2 ≤ _
  have hA0 : 0 ≤ ∑ n ∈ Icc (-(K : ℤ)) K, ‖a n‖ ^ 2 := by positivity
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp only [Finset.sum_empty]
    positivity
  obtain ⟨r0, hr0, hmin⟩ := s.exists_min_image (fun r => Int.fract (α r)) hs
  have hmin' : ∀ r ∈ s, Int.fract (α r0) ≤ Int.fract (α r) := hmin
  have hSc := trigPoly_continuous (Icc (-(K : ℤ)) K) a
  have hS'c := trigPoly_continuous (Icc (-(K : ℤ)) K) (fun n => 2 * π * Complex.I * n * a n)
  set G : ℝ → ℝ := fun t => δ⁻¹ * ‖trigPoly (Icc (-(K : ℤ)) K) a t‖ ^ 2 +
    ‖trigPoly (Icc (-(K : ℤ)) K) a t‖ *
      ‖trigPoly (Icc (-(K : ℤ)) K) (fun n => 2 * π * Complex.I * n * a n) t‖ with hG
  have hGc : Continuous G :=
    (continuous_const.mul (hSc.norm.pow 2)).add (hSc.norm.mul hS'c.norm)
  have hG0 : ∀ t, 0 ≤ G t := fun t => by simp only [hG]; positivity
  have hGp : Function.Periodic G 1 := by
    intro t
    simp only [hG, trigPoly_periodic (Icc (-(K : ℤ)) K) a t,
      trigPoly_periodic (Icc (-(K : ℤ)) K) (fun n => 2 * π * Complex.I * n * a n) t]
  have hpt : ∀ r, ‖trigPoly (Icc (-(K : ℤ)) K) a (α r)‖ ^ 2 ≤
      ∫ t in (Int.fract (α r) - δ / 2)..(Int.fract (α r) + δ / 2), G t := by
    intro r
    have hper : trigPoly (Icc (-(K : ℤ)) K) a (α r) =
        trigPoly (Icc (-(K : ℤ)) K) a (Int.fract (α r)) := by
      have := (trigPoly_periodic (Icc (-(K : ℤ)) K) a).int_mul ⌊α r⌋ (Int.fract (α r))
      rwa [mul_one, Int.fract_add_floor] at this
    rw [hper]
    exact sq_norm_le_integral _ a hδ _
  have hsepβ : ∀ r ∈ s, ∀ t ∈ s, r ≠ t → δ ≤ |Int.fract (α r) - Int.fract (α t)| := by
    intro r hr t ht hrt
    have := hsep r hr t ht hrt (⌊α r⌋ - ⌊α t⌋)
    have e : Int.fract (α r) - Int.fract (α t) = α r - α t - ((⌊α r⌋ - ⌊α t⌋ : ℤ) : ℝ) := by
      push_cast; simp only [Int.fract]; ring
    rw [e]
    exact this
  have hsub : ∀ r ∈ s, Int.fract (α r0) - δ / 2 ≤ Int.fract (α r) - δ / 2 ∧
      Int.fract (α r) + δ / 2 ≤ Int.fract (α r0) - δ / 2 + 1 := by
    intro r hr
    refine ⟨by linarith [hmin' r hr], ?_⟩
    by_cases hrr : r = r0
    · subst hrr; linarith
    · have := hsep r0 hr0 r hr (Ne.symm hrr) (⌊α r0⌋ - ⌊α r⌋ - 1)
      have e : α r0 - α r - ((⌊α r0⌋ - ⌊α r⌋ - 1 : ℤ) : ℝ) =
          Int.fract (α r0) - Int.fract (α r) + 1 := by
        push_cast; simp only [Int.fract]; ring
      rw [e, abs_of_nonneg (by linarith [Int.fract_lt_one (α r), Int.fract_nonneg (α r0)])]
        at this
      linarith
  have hQ : ∑ r ∈ s, ∫ x in (Int.fract (α r) - δ / 2)..(Int.fract (α r) + δ / 2), G x ≤
      ∫ x in (Int.fract (α r0) - δ / 2)..(Int.fract (α r0) - δ / 2 + 1), G x :=
    sum_integral_le_of_separated s (fun r => Int.fract (α r)) hδ _ G hGc hG0 hsepβ hsub
  have hrot : ∫ x in (Int.fract (α r0) - δ / 2)..(Int.fract (α r0) - δ / 2 + 1), G x =
      ∫ x in (0 : ℝ)..1, G x := by
    have := hGp.intervalIntegral_add_eq (Int.fract (α r0) - δ / 2) 0
    simpa using this
  have hint : ∫ x in (0 : ℝ)..1, G x = δ⁻¹ * ∑ n ∈ Icc (-(K : ℤ)) K, ‖a n‖ ^ 2 +
      ∫ x in (0 : ℝ)..1, ‖trigPoly (Icc (-(K : ℤ)) K) a x‖ *
        ‖trigPoly (Icc (-(K : ℤ)) K) (fun n => 2 * π * Complex.I * n * a n) x‖ := by
    simp only [hG]
    rw [intervalIntegral.integral_add, intervalIntegral.integral_const_mul,
      parseval_trig]
    · exact (continuous_const.mul (hSc.norm.pow 2)).intervalIntegrable _ _
    · exact (hSc.norm.mul hS'c.norm).intervalIntegrable _ _
  have hX := integral_cross_le K a
  calc ∑ r ∈ s, ‖trigPoly (Icc (-(K : ℤ)) K) a (α r)‖ ^ 2
      ≤ ∑ r ∈ s, ∫ t in (Int.fract (α r) - δ / 2)..(Int.fract (α r) + δ / 2), G t :=
        sum_le_sum fun r _ => hpt r
    _ ≤ _ := hQ
    _ = _ := hrot
    _ = _ := hint
    _ ≤ _ := by rw [one_div]; linarith

/-- **Davenport, Ch. 27 (Gallagher's form of the large sieve)**: let
`S(α) = ∑_{M < n ≤ M + N} a_n e(nα)` and let `α_1, …, α_R` satisfy `‖α_r - α_s‖ ≥ δ > 0` for
`r ≠ s`. Then `∑_r |S(α_r)|² ≤ (πN + 1/δ) ∑_n |a_n|²`. -/
@[kb "davenport1980" "Ch 27, p. 157"]
theorem large_sieve_gallagher {ι : Type*} (s : Finset ι) (α : ι → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ r ∈ s, ∀ t ∈ s, r ≠ t → ∀ m : ℤ, δ ≤ |α r - α t - m|) (M : ℤ) (N : ℕ)
    (a : ℤ → ℂ) :
    ∑ r ∈ s, ‖∑ n ∈ Ioc M (M + N), a n * Complex.exp (2 * π * Complex.I * (n * α r))‖ ^ 2 ≤
      (π * N + 1 / δ) * ∑ n ∈ Ioc M (M + N), ‖a n‖ ^ 2 := by
  classical
  set I := Ioc M (M + N)
  have hnn : 0 ≤ ∑ n ∈ I, ‖a n‖ ^ 2 := by positivity
  rcases le_or_gt s.card 1 with hs | hs
  · -- a single point: Cauchy's inequality
    have hcs : ∀ r, ‖∑ n ∈ I, a n * Complex.exp (2 * π * Complex.I * (n * α r))‖ ^ 2 ≤
        N * ∑ n ∈ I, ‖a n‖ ^ 2 := by
      intro r
      have h1 : ‖∑ n ∈ I, a n * Complex.exp (2 * π * Complex.I * (n * α r))‖ ≤
          ∑ n ∈ I, ‖a n‖ := by
        refine (norm_sum_le _ _).trans (le_of_eq (sum_congr rfl fun n _ ↦ ?_))
        rw [norm_mul, show (n : ℂ) * α r = ((n * α r : ℝ) : ℂ) by push_cast; ring,
          norm_exp_two_pi_I_mul, mul_one]
      have h2 := sq_sum_le_card_mul_sum_sq (s := I) (f := fun n ↦ ‖a n‖)
      have hI : (I.card : ℝ) = N := by simp [I]
      rw [hI] at h2
      calc _ ≤ (∑ n ∈ I, ‖a n‖) ^ 2 := by gcongr
        _ ≤ _ := h2
    have hN : (N : ℝ) ≤ π * N + 1 / δ := by
      have := one_div_pos.2 hδ
      nlinarith [pi_gt_three, (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
    calc _ ≤ ∑ r ∈ s, (N : ℝ) * ∑ n ∈ I, ‖a n‖ ^ 2 := sum_le_sum fun r _ ↦ hcs r
      _ = s.card * (N * ∑ n ∈ I, ‖a n‖ ^ 2) := by rw [sum_const, nsmul_eq_mul]
      _ ≤ 1 * (N * ∑ n ∈ I, ‖a n‖ ^ 2) := by gcongr; exact_mod_cast hs
      _ ≤ _ := by rw [one_mul]; exact mul_le_mul_of_nonneg_right hN hnn
  -- at least two points: `δ ≤ 1/2`
  have hδ2 : δ ≤ 1 / 2 := by
    obtain ⟨r, hr, t, ht, hrt⟩ := one_lt_card.1 hs
    have := hsep r hr t ht hrt (round (α r - α t))
    exact this.trans (abs_sub_round _)
  set K := N / 2
  set c : ℤ := M + 1 + K
  set a' : ℤ → ℂ := fun k ↦ if k + c ∈ I then a (k + c) else 0
  have hS : ∀ r, ‖∑ n ∈ I, a n * Complex.exp (2 * π * Complex.I * (n * α r))‖ =
      ‖∑ k ∈ Icc (-(K : ℤ)) K, a' k * Complex.exp (2 * π * Complex.I * (k * α r))‖ := by
    intro r
    have : ∑ k ∈ Icc (-(K : ℤ)) K, a' k * Complex.exp (2 * π * Complex.I * (k * α r)) =
        Complex.exp (2 * π * Complex.I * ((-c : ℤ) * α r)) *
          ∑ n ∈ I, a n * Complex.exp (2 * π * Complex.I * (n * α r)) := by
      rw [mul_sum, ← sum_Icc_recentre M N]
      refine sum_congr rfl fun k _ ↦ ?_
      simp only [a']
      split_ifs
      · simp only [c, K]
        have h1 : ∀ (m : ℤ) (x : ℝ), Complex.exp (2 * π * Complex.I * (((k + m : ℤ) : ℂ) * x)) =
            Complex.exp (2 * π * Complex.I * ((k : ℂ) * x)) *
              Complex.exp (2 * π * Complex.I * ((m : ℂ) * x)) := fun m x ↦ by
          rw [← Complex.exp_add]; congr 1; push_cast; ring
        have h2 : ∀ (m : ℤ) (x : ℝ), Complex.exp (2 * π * Complex.I * (((-m : ℤ) : ℂ) * x)) *
            Complex.exp (2 * π * Complex.I * ((m : ℂ) * x)) = 1 := fun m x ↦ by
          rw [← Complex.exp_add, ← Complex.exp_zero]; congr 1; push_cast; ring
        rw [h1]
        linear_combination (-(a (k + (M + 1 + ((N / 2 : ℕ) : ℤ))) *
          Complex.exp (2 * π * Complex.I * ((k : ℂ) * α r)))) *
            h2 (M + 1 + ((N / 2 : ℕ) : ℤ)) (α r)
      · rw [zero_mul]
    rw [this, norm_mul, show ((-c : ℤ) : ℂ) * α r = (((-c : ℤ) * α r : ℝ) : ℂ) by push_cast; ring,
      norm_exp_two_pi_I_mul, one_mul]
  have ha' : ∑ k ∈ Icc (-(K : ℤ)) K, ‖a' k‖ ^ 2 = ∑ n ∈ I, ‖a n‖ ^ 2 := by
    rw [← sum_Icc_recentre M N]
    refine sum_congr rfl fun k _ ↦ ?_
    simp only [a']
    split_ifs
    · rfl
    · simp
  simp_rw [hS]
  refine (large_sieve_gallagher_centred s α hδ (by linarith) hsep K a').trans ?_
  rw [ha']
  refine mul_le_mul_of_nonneg_right ?_ hnn
  have : (2 * K : ℝ) ≤ N := by
    have := Nat.mul_div_le N 2
    exact_mod_cast (by omega : 2 * K ≤ N)
  nlinarith [pi_pos]

end NTKB.Davenport
