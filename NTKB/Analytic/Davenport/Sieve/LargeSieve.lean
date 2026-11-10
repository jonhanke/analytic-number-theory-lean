/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Davenport.Sieve.Bessel
import NTKB.Analytic.Davenport.Sieve.PolyaVinogradov
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Chebyshev

/-!
# The large sieve inequality (Davenport, Chapter 27, Theorem 2)

For `S(α) = ∑_{M < n ≤ M + N} a_n e(nα)` and points `α_1, …, α_R` with `‖α_r - α_s‖ ≥ δ` for
`r ≠ s` (distance to the nearest integer),
`∑_r |S(α_r)|² ≤ (N + 3/δ) ∑_n |a_n|²` (`large_sieve`).

Davenport's proof: for a single point Cauchy's inequality gives the factor `N`; otherwise
`δ ≤ 1/2`, the frequencies are centred on `[-K, K]`, `2K ≤ N`, and Theorem 1 is applied with
`ξ = (a_k b_k^{-1/2})`, `φ_r = (b_k^{1/2} e(-kα_r))`, where `b_k` is `1` for `|k| ≤ K`, decreases
linearly to `0` over `K < |k| < K + L`. Fejér's identity
`∑_{|j| < J} (J - |j|) e(jα) = (sin πJα / sin πα)²` (`sum_fejer_eq`) gives
`b̂(α) = L⁻¹ ((sin π(K+L)α)² - (sin πKα)²)(sin πα)⁻²`, so `b̂(0) = 2K + L` and
`|b̂(α)| ≤ (4L‖α‖²)⁻¹`; the `h`-th nearest point on each side is at distance at least `hδ`
(`sum_le_sum_of_separated`) and `∑ h⁻² ≤ 2`; `L = ⌈δ⁻¹⌉` gives the row sums `≤ 2K + 3/δ`.
-/

open Finset Real ComplexConjugate
open scoped InnerProductSpace

namespace NTKB.Davenport

/-! ### Fejér's identity (27-8) -/

/-- `∑_{k ∈ [-J, J]} f(k) = f(0) + ∑_{j < J} (f(j+1) + f(-(j+1)))`. -/
lemma sum_Icc_neg_eq {M : Type*} [AddCommMonoid M] (f : ℤ → M) (J : ℕ) :
    ∑ k ∈ Icc (-(J : ℤ)) J, f k = f 0 + ∑ j ∈ range J, (f (j + 1) + f (-(j + 1))) := by
  induction J with
  | zero => simp
  | succ J ih =>
    have : Icc (-((J + 1 : ℕ) : ℤ)) (J + 1 : ℕ) =
        insert ((J : ℤ) + 1) (insert (-((J : ℤ) + 1)) (Icc (-(J : ℤ)) J)) := by
      ext k; simp only [mem_Icc, mem_insert]; push_cast; omega
    rw [this, sum_insert (by simp; omega), sum_insert (by simp), ih, sum_range_succ]
    abel

/-- The double sum `∑_{a, b < J} f(a - b) = ∑_{|k| ≤ J} (J - |k|) f(k)`. -/
lemma sum_range_sum_range_sub (f : ℤ → ℂ) (J : ℕ) :
    ∑ a ∈ range J, ∑ b ∈ range J, f ((a : ℤ) - b) =
      ∑ k ∈ Icc (-(J : ℤ)) J, ((J : ℂ) - |k|) * f k := by
  induction J with
  | zero => simp
  | succ J ih =>
    -- the right side
    have hR : ∑ k ∈ Icc (-((J + 1 : ℕ) : ℤ)) (J + 1 : ℕ), (((J + 1 : ℕ) : ℂ) - |k|) * f k =
        ∑ k ∈ Icc (-(J : ℤ)) J, ((J : ℂ) - |k|) * f k + ∑ k ∈ Icc (-(J : ℤ)) J, f k := by
      have hsub : Icc (-(J : ℤ)) J ⊆ Icc (-((J + 1 : ℕ) : ℤ)) (J + 1 : ℕ) := by
        intro k hk; simp only [mem_Icc] at hk ⊢; push_cast; omega
      rw [← sum_subset hsub (fun k hk hk' ↦ ?_), ← sum_add_distrib]
      · refine sum_congr rfl fun k _ ↦ ?_
        simp only [Nat.cast_add, Nat.cast_one]; ring
      · simp only [mem_Icc, not_and_or, not_le] at hk hk'
        have : |k| = (J : ℤ) + 1 := by
          push_cast at hk; rw [abs_eq (by omega)]; omega
        have : ((|k| : ℤ) : ℂ) = (J : ℂ) + 1 := by rw [this]; push_cast; ring
        simp only [Nat.cast_add, Nat.cast_one]; rw [this]; ring
    rw [hR, ← ih, sum_range_succ, sum_range_succ]
    simp_rw [sum_range_succ]
    rw [sum_add_distrib, sum_Icc_neg_eq]
    have h1 : ∑ x ∈ range J, f ((J : ℤ) - x) = ∑ j ∈ range J, f (j + 1) := by
      rw [← sum_range_reflect]
      refine sum_congr rfl fun j hj ↦ ?_
      congr 1; have := mem_range.1 hj; omega
    have h2 : ∑ x ∈ range J, f ((x : ℤ) - J) = ∑ j ∈ range J, f (-(j + 1)) := by
      rw [← sum_range_reflect]
      refine sum_congr rfl fun j hj ↦ ?_
      congr 1; have := mem_range.1 hj; omega
    rw [h1, h2, sum_add_distrib, sub_self]
    abel

/-- `e(x) = exp(2πix)`. -/
lemma norm_exp_two_pi_I_mul (x : ℝ) : ‖Complex.exp (2 * π * Complex.I * x)‖ = 1 := by
  rw [show 2 * π * Complex.I * x = ((2 * π * x : ℝ) : ℂ) * Complex.I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

lemma exp_two_pi_I_mul_conj (x : ℝ) :
    conj (Complex.exp (2 * π * Complex.I * x)) = Complex.exp (2 * π * Complex.I * (-x : ℝ)) := by
  rw [← Complex.exp_conj]; congr 1
  rw [map_mul, map_mul, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_I,
    map_ofNat]
  push_cast; ring

/-- **Davenport, Ch. 27 (Fejér's identity)**: `∑_{|j| ≤ J} (J - |j|) e(jα) = |∑_{a < J} e(aα)|²`;
when `sin πα ≠ 0` this is `(sin πJα / sin πα)²` (`norm_sum_range_exp_sq`). -/
@[kb "davenport1980" "Ch 27, p. 155"]
theorem sum_fejer_eq (J : ℕ) (α : ℝ) :
    ∑ k ∈ Icc (-(J : ℤ)) J, ((J : ℂ) - |k|) * Complex.exp (2 * π * Complex.I * (k * α)) =
      ((‖∑ a ∈ range J, Complex.exp (2 * π * Complex.I * (a * α))‖ ^ 2 : ℝ) : ℂ) := by
  rw [← sum_range_sum_range_sub (fun k : ℤ ↦ Complex.exp (2 * π * Complex.I * (k * α))) J]
  push_cast
  rw [← Complex.mul_conj', map_sum, sum_mul_sum]
  refine sum_congr rfl fun a _ ↦ sum_congr rfl fun b _ ↦ ?_
  rw [show conj (Complex.exp (2 * π * Complex.I * ((b : ℂ) * α))) =
      conj (Complex.exp (2 * π * Complex.I * (((b * α : ℝ)) : ℂ))) by push_cast; rfl,
    exp_two_pi_I_mul_conj, ← Complex.exp_add]
  congr 1; push_cast; ring

/-- `|∑_{a < J} e(aα)|² = (sin πJα)² / (sin πα)²` when `sin πα ≠ 0`. -/
theorem norm_sum_range_exp_sq {α : ℝ} (hα : sin (π * α) ≠ 0) (J : ℕ) :
    ‖∑ a ∈ range J, Complex.exp (2 * π * Complex.I * (a * α))‖ ^ 2 =
      sin (π * J * α) ^ 2 / sin (π * α) ^ 2 := by
  have h := norm_sum_Ioc_exp (θ := 2 * π * α) (by rwa [show 2 * π * α / 2 = π * α by ring]) (-1) J
  rw [sum_Ioc_int_eq_sum_range] at h
  have e : ∑ j ∈ range J, Complex.exp (Complex.I * ((2 * π * α : ℝ) : ℂ) * ((-1 + 1 + j : ℤ) : ℂ))
      = ∑ j ∈ range J, Complex.exp (2 * π * Complex.I * (j * α)) :=
    sum_congr rfl fun j _ ↦ by congr 1; push_cast; ring
  rw [e] at h
  rw [h, div_pow, sq_abs, sq_abs, show (J : ℝ) * (2 * π * α) / 2 = π * J * α by ring,
    show 2 * π * α / 2 = π * α by ring]

/-! ### Separated points (the counting step) -/

/-- If `T` is a finite set of reals `≥ δ`, pairwise at distance `≥ δ`, then its largest element is
at least `|T| δ`. -/
lemma card_mul_le_max' {δ : ℝ} (T : Finset ℝ) (hT : T.Nonempty) (hpos : ∀ x ∈ T, δ ≤ x)
    (hsep : ∀ x ∈ T, ∀ y ∈ T, x ≠ y → δ ≤ |x - y|) : (T.card : ℝ) * δ ≤ T.max' hT := by
  induction T using Finset.induction_on_max with
  | empty => exact absurd hT (by simp)
  | insert a s ha ih =>
    have hmax : (insert a s).max' hT = a := by
      refine le_antisymm (max'_le _ _ _ fun y hy ↦ ?_) (le_max' _ _ (mem_insert_self a s))
      rcases mem_insert.1 hy with rfl | hy
      · exact le_rfl
      · exact (ha y hy).le
    have has : a ∉ s := fun h ↦ lt_irrefl a (ha a h)
    rw [hmax, card_insert_of_notMem has]
    rcases s.eq_empty_or_nonempty with rfl | hs
    · simpa using hpos a (mem_insert_self a ∅)
    have ih' := ih hs (fun x hx ↦ hpos x (mem_insert_of_mem hx))
      (fun x hx y hy ↦ hsep x (mem_insert_of_mem hx) y (mem_insert_of_mem hy))
    have hm := s.max'_mem hs
    have hgap := hsep a (mem_insert_self a s) _ (mem_insert_of_mem hm) (ha _ hm).ne'
    rw [abs_of_pos (sub_pos.2 (ha _ hm))] at hgap
    push_cast
    linarith

/-- **Davenport, Ch. 27 (counting step)**: for `T` as above and `f` antitone on `[δ, ∞)`,
`∑_{x ∈ T} f(x) ≤ ∑_{h=1}^{|T|} f(hδ)`. -/
lemma sum_le_sum_of_separated {δ : ℝ} (hδ : 0 < δ) (f : ℝ → ℝ)
    (hf : AntitoneOn f (Set.Ici δ)) (T : Finset ℝ) (hpos : ∀ x ∈ T, δ ≤ x)
    (hsep : ∀ x ∈ T, ∀ y ∈ T, x ≠ y → δ ≤ |x - y|) :
    ∑ x ∈ T, f x ≤ ∑ h ∈ Icc 1 T.card, f (h * δ) := by
  induction T using Finset.induction_on_max with
  | empty => simp
  | insert a s ha ih =>
    have has : a ∉ s := fun h ↦ lt_irrefl a (ha a h)
    rw [sum_insert has, card_insert_of_notMem has, ← Ico_add_one_right_eq_Icc,
      sum_Ico_succ_top (by omega), Ico_add_one_right_eq_Icc, add_comm]
    have ih' := ih (fun x hx ↦ hpos x (mem_insert_of_mem hx))
      (fun x hx y hy ↦ hsep x (mem_insert_of_mem hx) y (mem_insert_of_mem hy))
    refine add_le_add ih' ?_
    -- `a ≥ (|s| + 1) δ`
    have hamax := card_mul_le_max' (insert a s) (insert_nonempty a s) hpos hsep
    have hmax : (insert a s).max' (insert_nonempty a s) = a := by
      refine le_antisymm (max'_le _ _ _ fun y hy ↦ ?_) (le_max' _ _ (mem_insert_self a s))
      rcases mem_insert.1 hy with rfl | hy
      · exact le_rfl
      · exact (ha y hy).le
    rw [hmax, card_insert_of_notMem has] at hamax
    have h1 : δ ≤ ((s.card + 1 : ℕ) : ℝ) * δ := by
      have : (1 : ℝ) ≤ ((s.card + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos _
      nlinarith
    exact hf (Set.mem_Ici.2 h1) (Set.mem_Ici.2 (h1.trans hamax)) hamax

/-- `∑_{h=1}^n h⁻² ≤ 2`. -/
lemma sum_Icc_inv_sq_le_two (n : ℕ) : ∑ h ∈ Icc 1 n, (1 : ℝ) / (h : ℝ) ^ 2 ≤ 2 := by
  have key : ∀ n : ℕ, 1 ≤ n → ∑ h ∈ Icc 1 n, (1 : ℝ) / (h : ℝ) ^ 2 ≤ 2 - 1 / n := by
    intro n hn
    induction n with
    | zero => omega
    | succ n ih =>
      rcases Nat.eq_zero_or_pos n with rfl | hn'
      · norm_num
      rw [← Ico_add_one_right_eq_Icc, sum_Ico_succ_top (by omega), Ico_add_one_right_eq_Icc]
      have := ih hn'
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn'
      have : (1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2 ≤ 1 / n - 1 / ((n + 1 : ℕ) : ℝ) := by
        push_cast
        rw [div_sub_div _ _ hn0.ne' (by positivity), div_le_div_iff₀ (by positivity)
          (by positivity)]
        nlinarith
      linarith
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have := key n hn
    have : (0 : ℝ) ≤ 1 / n := by positivity
    linarith

/-! ### Theorem 1 in coordinates -/

/-- Theorem 1 for vectors of `ℂ^F`, `F` a finite set of integers, with the usual inner product
`(ξ, φ) = ∑_k ξ_k φ̄_k`. -/
theorem sum_norm_sum_sq_le_of_rows {ι : Type*} (s : Finset ι) (F : Finset ℤ) (φ : ι → ℤ → ℂ)
    (ξ : ℤ → ℂ) {A : ℝ} (hA0 : 0 ≤ A)
    (hA : ∀ r ∈ s, ∑ t ∈ s, ‖∑ k ∈ F, φ t k * conj (φ r k)‖ ≤ A) :
    ∑ r ∈ s, ‖∑ k ∈ F, ξ k * conj (φ r k)‖ ^ 2 ≤ A * ∑ k ∈ F, ‖ξ k‖ ^ 2 := by
  let v : ι → EuclideanSpace ℂ F := fun r ↦ WithLp.toLp 2 (fun i : F ↦ φ r i)
  let w : EuclideanSpace ℂ F := WithLp.toLp 2 (fun i : F ↦ ξ i)
  have hinner : ∀ r t, ⟪v r, v t⟫_ℂ = ∑ k ∈ F, φ t k * conj (φ r k) := by
    intro r t
    simp only [v, EuclideanSpace.inner_toLp_toLp, dotProduct]
    rw [← sum_coe_sort F]; rfl
  have hinner' : ∀ r, ⟪v r, w⟫_ℂ = ∑ k ∈ F, ξ k * conj (φ r k) := by
    intro r
    simp only [v, w, EuclideanSpace.inner_toLp_toLp, dotProduct]
    rw [← sum_coe_sort F]; rfl
  have hnorm : ‖w‖ ^ 2 = ∑ k ∈ F, ‖ξ k‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, ← sum_coe_sort F]
  have := sum_norm_inner_sq_le s v hA0 (fun r hr ↦ by simpa only [hinner] using hA r hr) w
  simpa only [hinner', hnorm] using this

/-! ### Davenport's weights -/

/-- The weights `b_k`: `1` for `|k| ≤ K`, `1 - (|k| - K)/L` for `K < |k| < K + L`, `0` beyond. -/
noncomputable def sieveWeight (K L : ℕ) (k : ℤ) : ℝ :=
  (max (((K + L : ℕ) : ℝ) - |(k : ℝ)|) 0 - max ((K : ℝ) - |(k : ℝ)|) 0) / L

lemma sieveWeight_nonneg (K L : ℕ) (k : ℤ) : 0 ≤ sieveWeight K L k := by
  unfold sieveWeight
  apply div_nonneg _ (Nat.cast_nonneg _)
  have : (K : ℝ) ≤ ((K + L : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_right K L
  have := max_le_max_right 0 (sub_le_sub_right this |(k : ℝ)|)
  linarith

lemma sieveWeight_eq_one {K L : ℕ} (hL : 0 < L) {k : ℤ} (hk : k ∈ Icc (-(K : ℤ)) K) :
    sieveWeight K L k = 1 := by
  unfold sieveWeight
  have hk' : |(k : ℝ)| ≤ K := by
    rw [abs_le]; simp only [mem_Icc] at hk; constructor <;> exact_mod_cast (by omega)
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  push_cast
  rw [max_eq_left (by linarith), max_eq_left (by linarith)]
  field_simp
  ring

/-- `b̂(θ) = ∑ b_k e(kθ) = (|∑_{a < K+L} e(aθ)|² - |∑_{a < K} e(aθ)|²)/L`. -/
theorem sum_sieveWeight_exp (K L : ℕ) (θ : ℝ) :
    ∑ k ∈ Icc (-((K + L : ℕ) : ℤ)) (K + L : ℕ),
        (sieveWeight K L k : ℂ) * Complex.exp (2 * π * Complex.I * (k * θ)) =
      (((‖∑ a ∈ range (K + L), Complex.exp (2 * π * Complex.I * (a * θ))‖ ^ 2 -
        ‖∑ a ∈ range K, Complex.exp (2 * π * Complex.I * (a * θ))‖ ^ 2) / L : ℝ) : ℂ) := by
  rw [Complex.ofReal_div, Complex.ofReal_sub, ← sum_fejer_eq, ← sum_fejer_eq, sub_div, sum_div,
    sum_div, Complex.ofReal_natCast]
  have hsub : Icc (-(K : ℤ)) K ⊆ Icc (-((K + L : ℕ) : ℤ)) (K + L : ℕ) := by
    intro k hk; simp only [mem_Icc] at hk ⊢; push_cast; omega
  -- extend the second Fejér sum by zeros
  have h2 : ∑ k ∈ Icc (-(K : ℤ)) K, ((K : ℂ) - |k|) * Complex.exp (2 * π * Complex.I * (k * θ)) /
      L = ∑ k ∈ Icc (-((K + L : ℕ) : ℤ)) (K + L : ℕ),
        ((max ((K : ℝ) - |(k : ℝ)|) 0 : ℝ) : ℂ) * Complex.exp (2 * π * Complex.I * (k * θ)) / L := by
    rw [← sum_subset hsub (f := fun k : ℤ ↦ ((max ((K : ℝ) - |(k : ℝ)|) 0 : ℝ) : ℂ) *
      Complex.exp (2 * π * Complex.I * (k * θ)) / L) ?_]
    swap
    · intro k hk hk'
      simp only [mem_Icc, not_and_or, not_le] at hk'
      have : (K : ℝ) ≤ |(k : ℝ)| := by
        rcases hk' with h | h
        · rw [abs_of_neg (by exact_mod_cast (by omega : k < 0))]
          have : (k : ℝ) < -K := by exact_mod_cast h
          linarith
        · rw [abs_of_pos (by exact_mod_cast (by omega : 0 < k))]; exact_mod_cast h.le
      rw [max_eq_right (by linarith)]; simp
    refine sum_congr rfl fun k hk ↦ ?_
    · simp only [mem_Icc] at hk
      have : |(k : ℝ)| ≤ K := by rw [abs_le]; constructor <;> exact_mod_cast (by omega)
      rw [max_eq_left (by linarith)]
      push_cast [← Int.cast_abs]
      rfl
  have h1 : ∑ k ∈ Icc (-((K + L : ℕ) : ℤ)) (K + L : ℕ),
      (((K + L : ℕ) : ℂ) - |k|) * Complex.exp (2 * π * Complex.I * (k * θ)) / L =
      ∑ k ∈ Icc (-((K + L : ℕ) : ℤ)) (K + L : ℕ),
        ((max (((K + L : ℕ) : ℝ) - |(k : ℝ)|) 0 : ℝ) : ℂ) *
          Complex.exp (2 * π * Complex.I * (k * θ)) / L := by
    refine sum_congr rfl fun k hk ↦ ?_
    simp only [mem_Icc] at hk
    have : |(k : ℝ)| ≤ ((K + L : ℕ) : ℝ) := by
      rw [abs_le]; constructor <;> exact_mod_cast (by omega)
    rw [max_eq_left (by linarith)]
    push_cast [← Int.cast_abs]
    rfl
  rw [h1, h2, ← sum_sub_distrib]
  refine sum_congr rfl fun k _ ↦ ?_
  unfold sieveWeight
  push_cast
  ring

/-- `b̂(0) = 2K + L`. -/
theorem sum_sieveWeight (K L : ℕ) (hL : 0 < L) :
    ∑ k ∈ Icc (-((K + L : ℕ) : ℤ)) (K + L : ℕ), (sieveWeight K L k : ℂ) *
      Complex.exp (2 * π * Complex.I * (k * (0 : ℝ))) = ((2 * K + L : ℝ) : ℂ) := by
  rw [sum_sieveWeight_exp]
  congr 1
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, sum_const, card_range, nsmul_eq_mul,
    mul_one, Complex.norm_natCast]
  have hL' : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  push_cast
  field_simp
  ring

/-- `|b̂(θ)| ≤ (L sin² πθ)⁻¹` when `sin πθ ≠ 0`. -/
theorem norm_sum_sieveWeight_le (K L : ℕ) (hL : 0 < L) {θ : ℝ} (hθ : sin (π * θ) ≠ 0) :
    ‖∑ k ∈ Icc (-((K + L : ℕ) : ℤ)) (K + L : ℕ), (sieveWeight K L k : ℂ) *
      Complex.exp (2 * π * Complex.I * (k * θ))‖ ≤ 1 / (L * sin (π * θ) ^ 2) := by
  rw [sum_sieveWeight_exp, Complex.norm_real, Real.norm_eq_abs, norm_sum_range_exp_sq hθ,
    norm_sum_range_exp_sq hθ, abs_div, abs_of_pos (by exact_mod_cast hL : (0 : ℝ) < L)]
  have hs : 0 < sin (π * θ) ^ 2 := by positivity
  have h1 : sin (π * ((K + L : ℕ) : ℝ) * θ) ^ 2 / sin (π * θ) ^ 2 ∈ Set.Icc 0 (1 / sin (π * θ) ^ 2) :=
    ⟨by positivity, div_le_div_of_nonneg_right (sin_sq_le_one _) hs.le⟩
  have h2 : sin (π * (K : ℝ) * θ) ^ 2 / sin (π * θ) ^ 2 ∈ Set.Icc 0 (1 / sin (π * θ) ^ 2) :=
    ⟨by positivity, div_le_div_of_nonneg_right (sin_sq_le_one _) hs.le⟩
  have : |sin (π * ((K + L : ℕ) : ℝ) * θ) ^ 2 / sin (π * θ) ^ 2 -
      sin (π * (K : ℝ) * θ) ^ 2 / sin (π * θ) ^ 2| ≤ 1 / sin (π * θ) ^ 2 := by
    rw [abs_le]; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  rw [div_le_iff₀ (by exact_mod_cast hL : (0 : ℝ) < L)]
  calc _ ≤ 1 / sin (π * θ) ^ 2 := this
    _ = 1 / (L * sin (π * θ) ^ 2) * L := by
        have : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
        field_simp

/-! ### The row sums for separated points -/

/-- `sin² π(α - β) = sin² π {β - α}`. -/
lemma sin_sq_pi_sub_eq (α β : ℝ) : sin (π * (α - β)) ^ 2 = sin (π * Int.fract (β - α)) ^ 2 := by
  have : π * (α - β) = -(π * Int.fract (β - α)) - (⌊β - α⌋ : ℤ) * π := by
    rw [Int.fract]; ring
  have h1 : ((-1 : ℝ) ^ ⌊β - α⌋) ^ 2 = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]; norm_num
  rw [this, sin_sub_int_mul_pi, sin_neg, mul_pow, neg_sq, h1, one_mul]

/-- `1/sin² πx ≤ 1/(4x²)` on `(0, 1/2]`. -/
lemma one_div_sin_sq_le {x : ℝ} (hx : 0 < x) (hx' : x ≤ 1 / 2) :
    1 / sin (π * x) ^ 2 ≤ 1 / (4 * x ^ 2) := by
  have h := mul_le_sin (x := π * x) (by positivity) (by nlinarith [pi_pos])
  have e : 2 / π * (π * x) = 2 * x := by field_simp
  rw [e] at h
  have : 4 * x ^ 2 ≤ sin (π * x) ^ 2 := by nlinarith
  exact one_div_le_one_div_of_le (by positivity) this

/-- **Davenport, Ch. 27**: for `δ`-separated points `α_r` (mod 1), the row sums of `|b̂(α_r - α_s)|`
are at most `2K + L + 1/(L δ²)`. -/
theorem sum_norm_sieveWeight_le {ι : Type*} (s : Finset ι) (α : ι → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ r ∈ s, ∀ t ∈ s, r ≠ t → ∀ m : ℤ, δ ≤ |α r - α t - m|) (K L : ℕ) (hL : 0 < L)
    {r : ι} (hr : r ∈ s) :
    ∑ t ∈ s, ‖∑ k ∈ Icc (-((K + L : ℕ) : ℤ)) (K + L : ℕ), (sieveWeight K L k : ℂ) *
      Complex.exp (2 * π * Complex.I * (k * ((α r - α t : ℝ) : ℂ)))‖ ≤
        2 * K + L + 1 / (L * δ ^ 2) := by
  classical
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  set bh : ℝ → ℂ := fun θ ↦ ∑ k ∈ Icc (-((K + L : ℕ) : ℤ)) (K + L : ℕ), (sieveWeight K L k : ℂ) *
      Complex.exp (2 * π * Complex.I * (k * θ)) with hbh
  rw [← sum_erase_add _ _ hr, sub_self, add_comm]
  change ‖bh 0‖ + ∑ t ∈ s.erase r, ‖bh (α r - α t)‖ ≤ _
  have h0 : ‖bh 0‖ = 2 * K + L := by
    rw [hbh]; dsimp only; rw [sum_sieveWeight K L hL, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity)]
  suffices hS : ∑ t ∈ s.erase r, ‖bh (α r - α t)‖ ≤ 1 / (L * δ ^ 2) by rw [h0]; linarith
  -- the other points: `x_t = {α_t - α_r} ∈ [δ, 1 - δ]`
  set x : ι → ℝ := fun t ↦ Int.fract (α t - α r)
  have hx1 : ∀ t ∈ s.erase r, δ ≤ x t := by
    intro t ht
    have := hsep t (mem_of_mem_erase ht) r hr (ne_of_mem_erase ht) ⌊α t - α r⌋
    simp only [x, Int.fract]
    rwa [abs_of_nonneg (by linarith [Int.floor_le (α t - α r)])] at this
  have hx2 : ∀ t ∈ s.erase r, δ ≤ 1 - x t := by
    intro t ht
    have := hsep r hr t (mem_of_mem_erase ht) (ne_of_mem_erase ht).symm (-⌊α t - α r⌋ - 1)
    simp only [x, Int.fract]
    push_cast at this
    have e : α r - α t - (-(⌊α t - α r⌋ : ℝ) - 1) = 1 - (α t - α r - ⌊α t - α r⌋) := by ring
    rwa [e, abs_of_nonneg (by linarith [Int.lt_floor_add_one (α t - α r)])] at this
  have hxsep : ∀ t ∈ s.erase r, ∀ t' ∈ s.erase r, t ≠ t' → δ ≤ |x t - x t'| := by
    intro t ht t' ht' htt'
    have := hsep t (mem_of_mem_erase ht) t' (mem_of_mem_erase ht') htt'
      (⌊α t - α r⌋ - ⌊α t' - α r⌋)
    simp only [x, Int.fract]
    push_cast at this
    convert this using 2; ring
  -- termwise bound
  set f : ℝ → ℝ := fun y ↦ 1 / (L * (4 * y ^ 2))
  have hterm : ∀ t ∈ s.erase r, ‖bh (α r - α t)‖ ≤
      (if x t ≤ 1 / 2 then f (x t) else 0) + (if ¬ x t ≤ 1 / 2 then f (1 - x t) else 0) := by
    intro t ht
    have hsin_eq := sin_sq_pi_sub_eq (α r) (α t)
    have hpos := hx1 t ht
    have hpos' := hx2 t ht
    have hsin : sin (π * (α r - α t)) ≠ 0 := by
      intro h
      rw [h, zero_pow two_ne_zero] at hsin_eq
      have hx0 : 0 < x t := hδ.trans_le hpos
      have hx1' : x t < 1 := by linarith
      have := sin_pos_of_pos_of_lt_pi (x := π * x t) (by positivity) (by nlinarith [pi_pos])
      simp only [x] at this
      nlinarith
    have hb := norm_sum_sieveWeight_le K L hL hsin
    rw [hsin_eq] at hb
    by_cases hh : x t ≤ 1 / 2
    · rw [if_pos hh, if_neg (not_not.2 hh), add_zero]
      refine hb.trans ?_
      have := one_div_sin_sq_le (hδ.trans_le hpos) hh
      simp only [f]
      calc 1 / (L * sin (π * x t) ^ 2) = 1 / L * (1 / sin (π * x t) ^ 2) := by
            rw [one_div_mul_one_div]
        _ ≤ 1 / L * (1 / (4 * x t ^ 2)) := by gcongr
        _ = 1 / (L * (4 * x t ^ 2)) := by rw [one_div_mul_one_div]
    · rw [if_neg hh, if_pos hh, zero_add]
      refine hb.trans ?_
      have h1x : sin (π * x t) = sin (π * (1 - x t)) := by
        rw [show π * (1 - x t) = π - π * x t by ring, sin_pi_sub]
      have := one_div_sin_sq_le (hδ.trans_le hpos') (by push Not at hh; linarith)
      simp only [f]
      rw [h1x]
      calc 1 / (L * sin (π * (1 - x t)) ^ 2) = 1 / L * (1 / sin (π * (1 - x t)) ^ 2) := by
            rw [one_div_mul_one_div]
        _ ≤ 1 / L * (1 / (4 * (1 - x t) ^ 2)) := by gcongr
        _ = 1 / (L * (4 * (1 - x t) ^ 2)) := by rw [one_div_mul_one_div]
  refine (sum_le_sum hterm).trans ?_
  rw [sum_add_distrib, ← sum_filter, ← sum_filter]
  -- each half is a sum over a separated set
  have hf : AntitoneOn f (Set.Ici δ) := by
    intro a ha b hb hab
    simp only [f, Set.mem_Ici] at ha hb ⊢
    have : 0 < a := hδ.trans_le ha
    apply one_div_le_one_div_of_le (by positivity)
    gcongr
  have hfnn : ∀ y, 0 ≤ f y := fun y ↦ by simp only [f]; positivity
  have hsumf : ∑ h ∈ Icc 1 s.card, f (h * δ) ≤ 1 / (2 * L * δ ^ 2) := by
    have : ∑ h ∈ Icc 1 s.card, f (h * δ) =
        1 / (4 * L * δ ^ 2) * ∑ h ∈ Icc 1 s.card, (1 : ℝ) / (h : ℝ) ^ 2 := by
      rw [mul_sum]
      refine sum_congr rfl fun h hh ↦ ?_
      have : (0 : ℝ) < h := by exact_mod_cast (mem_Icc.1 hh).1
      simp only [f]; field_simp
    rw [this]
    calc _ ≤ 1 / (4 * L * δ ^ 2) * 2 := by gcongr; exact sum_Icc_inv_sq_le_two _
      _ = _ := by field_simp; ring
  have half : ∀ (P : ι → Prop) [DecidablePred P] (g : ι → ℝ), (∀ t ∈ (s.erase r).filter P, δ ≤ g t) →
      (∀ t ∈ (s.erase r).filter P, ∀ t' ∈ (s.erase r).filter P, t ≠ t' → δ ≤ |g t - g t'|) →
      ∑ t ∈ (s.erase r).filter P, f (g t) ≤ 1 / (2 * L * δ ^ 2) := by
    intro P _ g hg1 hg2
    have hinj : Set.InjOn g ((s.erase r).filter P) := by
      intro t ht t' ht' he
      by_contra hne
      have := hg2 t ht t' ht' hne
      rw [he, sub_self, abs_zero] at this
      linarith
    rw [← sum_image hinj]
    refine (sum_le_sum_of_separated hδ f hf _ ?_ ?_).trans ?_
    · intro y hy; obtain ⟨t, ht, rfl⟩ := mem_image.1 hy; exact hg1 t ht
    · intro y hy y' hy' hne
      obtain ⟨t, ht, rfl⟩ := mem_image.1 hy
      obtain ⟨t', ht', rfl⟩ := mem_image.1 hy'
      exact hg2 t ht t' ht' (fun h ↦ hne (h ▸ rfl))
    · refine le_trans ?_ hsumf
      apply sum_le_sum_of_subset_of_nonneg
      · intro h hh
        simp only [mem_Icc] at hh ⊢
        refine ⟨hh.1, hh.2.trans ?_⟩
        exact card_image_le.trans ((card_filter_le _ _).trans (card_erase_le))
      · intro _ _ _; exact hfnn _
  have hA := half (fun t ↦ x t ≤ 1 / 2) x (fun t ht ↦ hx1 t (mem_filter.1 ht).1)
    (fun t ht t' ht' h ↦ hxsep t (mem_filter.1 ht).1 t' (mem_filter.1 ht').1 h)
  have hB := half (fun t ↦ ¬ x t ≤ 1 / 2) (fun t ↦ 1 - x t)
    (fun t ht ↦ hx2 t (mem_filter.1 ht).1)
    (fun t ht t' ht' h ↦ by
      have := hxsep t (mem_filter.1 ht).1 t' (mem_filter.1 ht').1 h
      rwa [show 1 - x t - (1 - x t') = -(x t - x t') by ring, abs_neg])
  calc _ ≤ 1 / (2 * L * δ ^ 2) + 1 / (2 * L * δ ^ 2) := add_le_add hA hB
    _ = 1 / (L * δ ^ 2) := by field_simp; ring

/-! ### Theorem 2 -/

/-- **Davenport, Ch. 27 (centred form of Theorem 2)**: for `δ ≤ 1/2`, `δ`-separated points and
frequencies `|k| ≤ K`, `∑_r |∑_k a_k e(kα_r)|² ≤ (2K + 3/δ) ∑ |a_k|²`. -/
theorem large_sieve_centred {ι : Type*} (s : Finset ι) (α : ι → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hδ2 : δ ≤ 1 / 2) (hsep : ∀ r ∈ s, ∀ t ∈ s, r ≠ t → ∀ m : ℤ, δ ≤ |α r - α t - m|)
    (K : ℕ) (a : ℤ → ℂ) :
    ∑ r ∈ s, ‖∑ k ∈ Icc (-(K : ℤ)) K, a k * Complex.exp (2 * π * Complex.I * (k * α r))‖ ^ 2 ≤
      (2 * K + 3 / δ) * ∑ k ∈ Icc (-(K : ℤ)) K, ‖a k‖ ^ 2 := by
  classical
  set L : ℕ := ⌈1 / δ⌉₊ with hLdef
  have hinv : 2 ≤ 1 / δ := by rw [le_div_iff₀ hδ]; linarith
  have hL1 : 1 / δ ≤ L := Nat.le_ceil _
  have hL2 : (L : ℝ) < 1 / δ + 1 := Nat.ceil_lt_add_one (by positivity)
  have hL : 0 < L := by
    have : (0 : ℝ) < L := by linarith
    exact_mod_cast this
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  set F := Icc (-((K + L : ℕ) : ℤ)) (K + L : ℕ)
  have hKF : Icc (-(K : ℤ)) K ⊆ F := by
    intro k hk; simp only [F, mem_Icc] at hk ⊢; push_cast; omega
  set φ : ι → ℤ → ℂ := fun r k ↦ (√(sieveWeight K L k) : ℂ) *
    Complex.exp (2 * π * Complex.I * (k * ((-α r : ℝ) : ℂ)))
  set ξ : ℤ → ℂ := fun k ↦ if k ∈ Icc (-(K : ℤ)) K then a k else 0
  have hconj : ∀ r k, conj (φ r k) =
      (√(sieveWeight K L k) : ℂ) * Complex.exp (2 * π * Complex.I * (k * α r)) := by
    intro r k
    simp only [φ, map_mul, Complex.conj_ofReal]
    congr 1
    rw [show (k : ℂ) * ((-α r : ℝ) : ℂ) = (((k : ℝ) * (-α r) : ℝ) : ℂ) by push_cast; ring,
      exp_two_pi_I_mul_conj]
    congr 2; push_cast; ring
  have hξφ : ∀ r, ∑ k ∈ F, ξ k * conj (φ r k) =
      ∑ k ∈ Icc (-(K : ℤ)) K, a k * Complex.exp (2 * π * Complex.I * (k * α r)) := by
    intro r
    symm
    rw [← sum_subset hKF (fun k _ hk ↦ by simp only [ξ, if_neg hk, zero_mul])]
    refine sum_congr rfl fun k hk ↦ ?_
    rw [hconj, sieveWeight_eq_one hL hk, Real.sqrt_one, Complex.ofReal_one, one_mul]
    simp only [ξ, if_pos hk]
  have hφφ : ∀ r t, ∑ k ∈ F, φ t k * conj (φ r k) = ∑ k ∈ F, (sieveWeight K L k : ℂ) *
      Complex.exp (2 * π * Complex.I * (k * ((α r - α t : ℝ) : ℂ))) := by
    intro r t
    refine sum_congr rfl fun k _ ↦ ?_
    rw [hconj]
    simp only [φ]
    have hb : (√(sieveWeight K L k) : ℂ) * √(sieveWeight K L k) = sieveWeight K L k := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (sieveWeight_nonneg K L k)]
    calc _ = ((√(sieveWeight K L k) : ℂ) * √(sieveWeight K L k)) *
          (Complex.exp (2 * π * Complex.I * (k * ((-α t : ℝ) : ℂ))) *
            Complex.exp (2 * π * Complex.I * (k * α r))) := by ring
      _ = _ := by rw [hb, ← Complex.exp_add]; congr 2; push_cast; ring
  have hξ : ∑ k ∈ F, ‖ξ k‖ ^ 2 = ∑ k ∈ Icc (-(K : ℤ)) K, ‖a k‖ ^ 2 := by
    symm
    rw [← sum_subset hKF (fun k _ hk ↦ by simp only [ξ, if_neg hk, norm_zero]; norm_num)]
    refine sum_congr rfl fun k hk ↦ ?_
    simp only [ξ, if_pos hk]
  have hA0 : (0 : ℝ) ≤ 2 * K + L + 1 / (L * δ ^ 2) := by positivity
  have hrows := sum_norm_sum_sq_le_of_rows s F φ ξ hA0 (fun r hr ↦ by
    simp_rw [hφφ]; exact sum_norm_sieveWeight_le s α hδ hsep K L hL hr)
  simp_rw [hξφ, hξ] at hrows
  refine hrows.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
  have h3 : 1 / (L * δ ^ 2) ≤ 1 / δ := by
    rw [div_le_div_iff₀ (by positivity) hδ]
    have : 1 ≤ L * δ := by rwa [div_le_iff₀ hδ] at hL1
    nlinarith
  have : 3 / δ = 3 * (1 / δ) := by ring
  linarith

/-- Recentring an interval: `(M, M + N]` is `c + [-K, K]` intersected with itself, `K = ⌊N/2⌋`,
`c = M + 1 + K`. -/
lemma sum_Icc_recentre {R : Type*} [AddCommMonoid R] (M : ℤ) (N : ℕ) (g : ℤ → R) :
    ∑ k ∈ Icc (-((N / 2 : ℕ) : ℤ)) (N / 2 : ℕ),
        (if k + (M + 1 + (N / 2 : ℕ)) ∈ Ioc M (M + N) then g (k + (M + 1 + (N / 2 : ℕ))) else 0) =
      ∑ n ∈ Ioc M (M + N), g n := by
  rw [← sum_filter]
  refine sum_nbij' (fun k ↦ k + (M + 1 + (N / 2 : ℕ))) (fun n ↦ n - (M + 1 + (N / 2 : ℕ)))
    ?_ ?_ ?_ ?_ ?_
  · intro k hk; exact (mem_filter.1 hk).2
  · intro n hn
    rw [mem_Ioc] at hn
    rw [mem_filter, mem_Icc, mem_Ioc]
    refine ⟨⟨by omega, by omega⟩, by omega, by omega⟩
  · intro k _; simp
  · intro n _; simp
  · intro k _; rfl

/-- **Davenport, Ch. 27, Theorem 2** (the large sieve): let `S(α) = ∑_{M < n ≤ M + N} a_n e(nα)`
and let `α_1, …, α_R` satisfy `‖α_r - α_s‖ ≥ δ > 0` for `r ≠ s`. Then
`∑_r |S(α_r)|² ≤ (N + 3/δ) ∑_n |a_n|²`. -/
@[kb "davenport1980" "Ch 27, p. 154, Theorem 2"]
theorem large_sieve {ι : Type*} (s : Finset ι) (α : ι → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ r ∈ s, ∀ t ∈ s, r ≠ t → ∀ m : ℤ, δ ≤ |α r - α t - m|) (M : ℤ) (N : ℕ)
    (a : ℤ → ℂ) :
    ∑ r ∈ s, ‖∑ n ∈ Ioc M (M + N), a n * Complex.exp (2 * π * Complex.I * (n * α r))‖ ^ 2 ≤
      (N + 3 / δ) * ∑ n ∈ Ioc M (M + N), ‖a n‖ ^ 2 := by
  classical
  set I := Ioc M (M + N)
  have hnn : 0 ≤ ∑ n ∈ I, ‖a n‖ ^ 2 := by positivity
  rcases le_or_gt s.card 1 with hs | hs
  · -- a single point: Cauchy's inequality (6)
    have hcs : ∀ r, ‖∑ n ∈ I, a n * Complex.exp (2 * π * Complex.I * (n * α r))‖ ^ 2 ≤
        N * ∑ n ∈ I, ‖a n‖ ^ 2 := by
      intro r
      have h1 : ‖∑ n ∈ I, a n * Complex.exp (2 * π * Complex.I * (n * α r))‖ ≤ ∑ n ∈ I, ‖a n‖ := by
        refine (norm_sum_le _ _).trans (le_of_eq (sum_congr rfl fun n _ ↦ ?_))
        rw [norm_mul, show (n : ℂ) * α r = ((n * α r : ℝ) : ℂ) by push_cast; ring,
          norm_exp_two_pi_I_mul, mul_one]
      have h2 := sq_sum_le_card_mul_sum_sq (s := I) (f := fun n ↦ ‖a n‖)
      have hI : (I.card : ℝ) = N := by simp [I]
      rw [hI] at h2
      calc _ ≤ (∑ n ∈ I, ‖a n‖) ^ 2 := by gcongr
        _ ≤ _ := h2
    calc _ ≤ ∑ r ∈ s, (N : ℝ) * ∑ n ∈ I, ‖a n‖ ^ 2 := sum_le_sum fun r _ ↦ hcs r
      _ = s.card * (N * ∑ n ∈ I, ‖a n‖ ^ 2) := by rw [sum_const, nsmul_eq_mul]
      _ ≤ 1 * (N * ∑ n ∈ I, ‖a n‖ ^ 2) := by gcongr; exact_mod_cast hs
      _ ≤ _ := by rw [one_mul]; gcongr; linarith [show 0 < 3 / δ by positivity]
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
  refine (large_sieve_centred s α hδ hδ2 hsep K a').trans ?_
  rw [ha']
  gcongr
  have : (2 * K : ℝ) ≤ N := by
    have := Nat.mul_div_le N 2
    exact_mod_cast (by omega : 2 * K ≤ N)
  linarith

end NTKB.Davenport
