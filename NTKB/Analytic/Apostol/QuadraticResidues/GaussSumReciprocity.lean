/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Apostol.QuadraticResidues.SReciprocity
import NTKB.Analytic.Apostol.GaussSums.Quadratic

/-!
# Reciprocity law for quadratic Gauss sums (Apostol, Theorem 9.17) and Gauss' formula

* Theorem 9.17 -> `apostol_thm_9_17`: for `h, k > 0`, `h` odd,
  `G(h; k) = √(k/h) · (1 + i)/2 · (1 + e^{-πihk/2}) · conj G(k; h)`, from Theorem 9.16 with
  `a = 2h`, `m = k`, splitting `S(k, 2h)` into even and odd `r` as Apostol does.
* Gauss' formula (§9.10 (30)) -> `gauss_formula`: `G(1; m) = (1 + i)/2 · (1 + (-i)^m) · √m`, i.e.
  `(1 + i)√m, √m, 0, i√m` for `m ≡ 0, 1, 2, 3 (mod 4)` (Theorem 9.17 with `h = 1`).
-/

open Complex Finset
open scoped Real ComplexConjugate

namespace NTKB.Apostol

/-- `G(h; k) = S(2h, k)`. -/
theorem quadGaussSum_eq_quadSumS (h k : ℕ) : quadGaussSum h k = quadSumS (2 * h) k := by
  rw [quadGaussSum_eq_sum_range, quadSumS]
  refine sum_congr rfl fun r _ ↦ ?_
  congr 1
  push_cast
  ring

/-- Summing over `range (2h)` by even and odd `r`. -/
theorem sum_range_two_mul {M : Type*} [AddCommMonoid M] (f : ℕ → M) (h : ℕ) :
    ∑ r ∈ range (2 * h), f r = ∑ s ∈ range h, f (2 * s) + ∑ s ∈ range h, f (2 * s + 1) := by
  induction h with
  | zero => simp
  | succ h ih =>
    rw [show 2 * (h + 1) = 2 * h + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih,
      sum_range_succ, sum_range_succ]
    abel

/-- A sum over a full period is invariant under a shift. -/
theorem sum_range_add_of_periodic {M : Type*} [AddCommGroup M] {F : ℕ → M} {h : ℕ}
    (hF : ∀ s, F (s + h) = F s) (c : ℕ) :
    ∑ s ∈ range h, F (s + c) = ∑ s ∈ range h, F s := by
  induction c with
  | zero => simp
  | succ c ih =>
    have e : ∑ s ∈ range h, F (s + (c + 1)) + F c = ∑ s ∈ range h, F s + F c := by
      have e1 := sum_range_succ' (fun s ↦ F (s + c)) h
      have e2 := sum_range_succ (fun s ↦ F (s + c)) h
      simp only [zero_add] at e1
      rw [e1, ih, show h + c = c + h by ring, hF] at e2
      simpa [add_assoc, add_comm 1 c] using e2
    exact add_right_cancel e

/-- `S(k, 2h) = (1 + e^{πihk/2}) G(k; h)` for odd `h`. -/
theorem quadSumS_two_mul (k h : ℕ) (hh : Odd h) :
    quadSumS k (2 * h) = (1 + cexp (π * I * h * k / 2)) * quadGaussSum k h := by
  have hh0 : (h : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hh.pos.ne'
  obtain ⟨c, hc⟩ := hh
  set f : ℕ → ℂ := fun r ↦ cexp (π * I * k * r ^ 2 / ((2 * h : ℕ) : ℂ)) with hf
  have hper : ∀ r, f (r + 2 * h) = f r := by
    intro r
    simp only [hf]
    conv_rhs => rw [← cexp_add_int_mul_two_pi_I' _ (k * (r + h))]
    congr 1
    push_cast
    field_simp
    ring
  have hodd : ∀ s, f (2 * (s + c) + 1) = cexp (π * I * h * k / 2) *
      cexp (2 * π * I * k * (s : ℂ) ^ 2 / h) := by
    intro s
    simp only [hf]
    rw [← Complex.exp_add]
    conv_rhs => rw [← cexp_add_int_mul_two_pi_I' _ (k * s)]
    congr 1
    rw [show 2 * (s + c) + 1 = 2 * s + h by omega]
    push_cast
    field_simp
    ring
  have heven : ∀ s, f (2 * s) = cexp (2 * π * I * k * (s : ℂ) ^ 2 / h) := by
    intro s
    simp only [hf]
    congr 1
    push_cast
    field_simp
  rw [quadSumS, show (fun r : ℕ ↦ cexp (π * I * k * r ^ 2 / ((2 * h : ℕ) : ℂ))) = f from rfl,
    sum_range_two_mul, quadGaussSum_eq_sum_range]
  have hshift := sum_range_add_of_periodic (F := fun s ↦ f (2 * s + 1)) (h := h)
    (fun s ↦ by rw [show 2 * (s + h) + 1 = 2 * s + 1 + 2 * h by ring, hper]) c
  rw [← hshift, sum_congr rfl (fun s _ ↦ heven s), sum_congr rfl (fun s _ ↦ hodd s), ← mul_sum]
  have : ∀ x : ℕ, cexp (2 * π * I * k * (x : ℂ) ^ 2 / h) =
      cexp (2 * π * I * ((k : ℤ) : ℂ) * (x : ℂ) ^ 2 / h) := fun x ↦ by push_cast; rfl
  simp only [this]
  ring

/-- **Theorem 9.17** (Apostol). For `h, k > 0` with `h` odd,
`G(h; k) = √(k/h) · (1 + i)/2 · (1 + e^{-πihk/2}) · conj G(k; h)`. -/
@[kb "apostol1976" "Thm 9.17, p. 200"]
theorem apostol_thm_9_17 {h k : ℕ} (hh : 0 < h) (hk : 0 < k) (hodd : Odd h) :
    quadGaussSum h k = (√((k : ℝ) / h) : ℂ) * ((1 + I) / 2) *
      (1 + cexp (-(π * I * h * k / 2))) * conj (quadGaussSum k h) := by
  rw [quadGaussSum_eq_quadSumS, apostol_thm_9_16 (by omega) hk (by
    rw [show k * (2 * h) = 2 * (k * h) by ring]; exact even_two_mul _), quadSumS_two_mul k h hodd, map_mul, map_add, map_one, ← Complex.exp_conj]
  have hconj : conj (π * I * h * k / 2 : ℂ) = -(π * I * h * k / 2) := by
    simp only [map_div₀, map_mul, conj_ofReal, conj_I, map_natCast, map_ofNat]
    ring
  rw [hconj]
  have hR : (√((k : ℝ) / ((2 * h : ℕ) : ℝ)) : ℂ) / (√2 : ℝ) = (√((k : ℝ) / h) : ℂ) / 2 := by
    have h2 : (√2 : ℝ) ^ 2 = 2 := Real.sq_sqrt zero_le_two
    have hpos : (0 : ℝ) < √2 := Real.sqrt_pos.2 two_pos
    rw [div_eq_div_iff (ofReal_ne_zero.2 hpos.ne') two_ne_zero, ← ofReal_ofNat, ← ofReal_mul,
      ← ofReal_mul, ofReal_inj]
    push_cast
    rw [show (k : ℝ) / (2 * h) = (k / h) / 2 by ring, Real.sqrt_div' _ zero_le_two]
    field_simp
    rw [h2]
  rw [show (√((k : ℝ) / ((2 * h : ℕ) : ℝ)) : ℂ) * ((1 + I) / (√2 : ℝ)) =
    (√((k : ℝ) / ((2 * h : ℕ) : ℝ)) : ℂ) / (√2 : ℝ) * (1 + I) by ring, hR]
  ring

/-- **Gauss' formula** (Apostol §9.10 (30)): `G(1; m) = (1 + i)/2 · (1 + (-i)^m) · √m` for `m ≥ 1`, that
is `(1 + i)√m`, `√m`, `0`, `i√m` according as `m ≡ 0, 1, 2, 3 (mod 4)`. -/
@[kb "apostol1976" "§9.10 (30), p. 195"]
theorem gauss_formula {m : ℕ} (hm : 0 < m) :
    quadGaussSum 1 m = (1 + I) / 2 * (1 + (-I) ^ m) * (√(m : ℝ) : ℂ) := by
  have := apostol_thm_9_17 one_pos hm odd_one
  push_cast at this
  rw [this, quadGaussSum_one, map_one, mul_one, div_one]
  have hexp : cexp (-(π * I * m / 2)) = (-I) ^ m := by
    rw [← Complex.exp_neg_pi_div_two_mul_I, ← Complex.exp_nat_mul]
    ring_nf
  simp only [mul_one, hexp]
  ring

end NTKB.Apostol
