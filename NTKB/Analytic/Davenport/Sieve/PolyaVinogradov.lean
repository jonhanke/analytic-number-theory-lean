/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Apostol.PNT.PolyaGeneral
import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import NTKB.Elementary.SpecialValues.KroneckerChar
import NTKB.Elementary.SpecialValues.KroneckerPrimitive

/-!
# The Pólya–Vinogradov inequality (Davenport, Chapter 23)

Davenport's proof (Schur's argument), for a primitive character `χ` modulo `q > 1`:

* `χ(n) τ(χ̄) = ∑_a χ̄(a) e(an/q)` (§9), so an interval sum of `χ` is
  `τ(χ̄)⁻¹ ∑_a χ̄(a) ∑_n e(an/q)`, `|τ(χ̄)| = √q`, and the inner geometric series has modulus
  `|sin(πNa/q)/sin(πa/q)|` (`norm_sum_Ioc_char_le`);
* for a convex function `f(α) ≤ (1/2δ) ∫_{α-δ}^{α+δ} f` (`le_average_integral_of_convexOn`);
  with `f(α) = 1/sin(πα)` and `δ = 1/(2q)`, the sum `∑_{a=1}^{q-1} 1/sin(πa/q)` is at most
  `2q ∫_{1/(2q)}^{1/2} dβ/sin(πβ) < 2q ∫_{1/(2q)}^{1/2} dβ/(2β) = q log q`
  (`sum_one_div_sin_lt_mul_log`); this gives inequality (B) (`norm_sum_Ioc_lt_of_isPrimitive`);
* for `χ` induced by a primitive `χ₁` modulo `q₁`, `q = q₁ r`, the Möbius function removes the
  condition `(n, r) = 1` (`sum_Ioc_eq_sum_divisors`), and `d(r) ≤ 2√r` finishes the proof of the
  inequality (A) with the constant `2` (`norm_sum_Ioc_le`).

The corollary on quadratic residues in an interval is `abs_two_mul_card_residues_sub_le`.
-/

open Finset Real

namespace NTKB.Davenport

/-! ### Interval sums over the integers -/

/-- `∑_{a < n ≤ a + N} f(n) = ∑_{j < N} f(a + 1 + j)`. -/
lemma sum_Ioc_int_eq_sum_range {M : Type*} [AddCommMonoid M] (f : ℤ → M) (a : ℤ) (N : ℕ) :
    ∑ n ∈ Ioc a (a + N), f n = ∑ j ∈ range N, f (a + 1 + j) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ, ← ih]
    have : Ioc a (a + ((N + 1 : ℕ) : ℤ)) = insert (a + 1 + N) (Ioc a (a + N)) := by
      ext n; simp only [mem_Ioc, mem_insert]; push_cast; omega
    rw [this, sum_insert (by simp), add_comm]

/-! ### The geometric series (23-5) -/

/-- The geometric series over an interval: `|∑_{M < n ≤ M + N} e^{inθ}| = |sin(Nθ/2)|/|sin(θ/2)|`
when `sin(θ/2) ≠ 0`. -/
theorem norm_sum_Ioc_exp {θ : ℝ} (hθ : sin (θ / 2) ≠ 0) (M : ℤ) (N : ℕ) :
    ‖∑ n ∈ Ioc M (M + N), Complex.exp (Complex.I * θ * n)‖ = |sin (N * θ / 2)| / |sin (θ / 2)| := by
  set z := Complex.exp (Complex.I * θ)
  have hz1 : ‖z‖ = 1 := by simp only [z]; rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I θ
  have hzn : ‖z - 1‖ = 2 * |sin (θ / 2)| := by
    rw [Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs, abs_mul, abs_two]
  have hz : z ≠ 1 := by
    intro h; rw [h, sub_self, norm_zero] at hzn
    exact hθ (abs_eq_zero.1 (by linarith))
  have hzN : ‖z ^ N - 1‖ = 2 * |sin (N * θ / 2)| := by
    have : z ^ N = Complex.exp (Complex.I * ((N * θ : ℝ) : ℂ)) := by
      rw [← Complex.exp_nat_mul]; push_cast; ring_nf
    rw [this, Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs, abs_mul, abs_two]
  set w := Complex.exp (Complex.I * θ * (M + 1 : ℤ))
  have hw : ‖w‖ = 1 := by
    simp only [w]
    rw [show Complex.I * θ * ((M + 1 : ℤ) : ℂ) = (((θ * (M + 1 : ℤ)) : ℝ) : ℂ) * Complex.I by
      push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  have hsum : ∑ n ∈ Ioc M (M + N), Complex.exp (Complex.I * θ * n) =
      w * ((z ^ N - 1) / (z - 1)) := by
    rw [sum_Ioc_int_eq_sum_range, ← geom_sum_eq hz, mul_sum]
    refine sum_congr rfl fun j _ ↦ ?_
    simp only [w, z]
    rw [← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1; push_cast; ring
  rw [hsum, norm_mul, hw, one_mul, norm_div, hzN, hzn]
  have : 0 < |sin (θ / 2)| := abs_pos.2 hθ
  field_simp

/-! ### The convexity lemma (23-6) -/

/-- **Davenport, Ch. 23**: for a convex function, `f(α) ≤ (1/(2δ)) ∫_{α-δ}^{α+δ} f(β) dβ`. -/
@[kb "davenport1980" "Ch 23, p. 136"]
theorem le_average_integral_of_convexOn {f : ℝ → ℝ} {α δ : ℝ} (hδ : 0 < δ)
    (hf : ConvexOn ℝ (Set.Icc (α - δ) (α + δ)) f)
    (hint : IntervalIntegrable f MeasureTheory.volume (α - δ) (α + δ)) :
    f α ≤ 1 / (2 * δ) * ∫ β in (α - δ)..(α + δ), f β := by
  have hab : α - δ ≤ α + δ := by linarith
  have hrefl : ∫ β in (α - δ)..(α + δ), f (2 * α - β) = ∫ β in (α - δ)..(α + δ), f β := by
    rw [intervalIntegral.integral_comp_sub_left (fun β ↦ f β) (2 * α)]
    congr 1 <;> ring
  have hint' : IntervalIntegrable (fun β ↦ f (2 * α - β)) MeasureTheory.volume (α - δ) (α + δ) := by
    have := (hint.comp_sub_left (2 * α)).symm
    convert this using 1 <;> ring
  have hmono : ∫ β in (α - δ)..(α + δ), 2 * f α ≤
      ∫ β in (α - δ)..(α + δ), (f β + f (2 * α - β)) := by
    refine intervalIntegral.integral_mono_on hab intervalIntegrable_const (hint.add hint') ?_
    intro β hβ
    have hβ' : 2 * α - β ∈ Set.Icc (α - δ) (α + δ) := by
      constructor <;> linarith [hβ.1, hβ.2]
    have := hf.2 hβ hβ' (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)
    simp only [smul_eq_mul] at this
    have e : 1 / 2 * β + 1 / 2 * (2 * α - β) = α := by ring
    rw [e] at this
    linarith
  rw [intervalIntegral.integral_add hint hint', hrefl, intervalIntegral.integral_const,
    smul_eq_mul] at hmono
  rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity)]
  have : α + δ - (α - δ) = 2 * δ := by ring
  rw [this] at hmono
  linarith

/-- `1/sin(πβ)` is convex on `(0, 1)`. -/
theorem convexOn_one_div_sin_pi : ConvexOn ℝ (Set.Ioo 0 1) (fun β ↦ 1 / sin (π * β)) := by
  refine ⟨convex_Ioo 0 1, fun x hx y hy a b ha hb hab ↦ ?_⟩
  have hsx : 0 < sin (π * x) := sin_pos_of_pos_of_lt_pi (by nlinarith [pi_pos, hx.1])
    (by nlinarith [pi_pos, hx.2])
  have hsy : 0 < sin (π * y) := sin_pos_of_pos_of_lt_pi (by nlinarith [pi_pos, hy.1])
    (by nlinarith [pi_pos, hy.2])
  have hcon := strictConcaveOn_sin_Icc.concaveOn.2
    (⟨by nlinarith [pi_pos, hx.1], by nlinarith [pi_pos, hx.2]⟩ : π * x ∈ Set.Icc 0 π)
    (⟨by nlinarith [pi_pos, hy.1], by nlinarith [pi_pos, hy.2]⟩ : π * y ∈ Set.Icc 0 π) ha hb hab
  simp only [smul_eq_mul] at hcon ⊢
  have e : a * (π * x) + b * (π * y) = π * (a * x + b * y) := by ring
  rw [e] at hcon
  have hpos : 0 < a * sin (π * x) + b * sin (π * y) := by
    rcases ha.eq_or_lt with rfl | ha'
    · simp only [zero_add] at hab; subst hab; simpa using hsy
    · have := mul_pos ha' hsx; nlinarith [mul_nonneg hb hsy.le]
  have hinv := (convexOn_zpow (𝕜 := ℝ) (-1)).2 (Set.mem_Ioi.2 hsx) (Set.mem_Ioi.2 hsy) ha hb hab
  simp only [smul_eq_mul, zpow_neg, zpow_one] at hinv
  calc 1 / sin (π * (a * x + b * y)) ≤ 1 / (a * sin (π * x) + b * sin (π * y)) :=
        one_div_le_one_div_of_le hpos hcon
    _ ≤ a * (1 / sin (π * x)) + b * (1 / sin (π * y)) := by
        simp only [one_div]; exact hinv

/-- `∫_{1/(2q)}^{1/2} dβ/sin(πβ) < (1/2) log q` for `q ≥ 2`, from `sin(πβ) > 2β` on `(0, 1/2)`. -/
theorem integral_one_div_sin_pi_lt {q : ℝ} (hq : 1 < q) :
    ∫ β in (1 / (2 * q))..(1 / 2), 1 / sin (π * β) < 1 / 2 * log q := by
  have hq0 : 0 < q := by linarith
  have ha : 0 < 1 / (2 * q) := by positivity
  have hab : 1 / (2 * q) < 1 / 2 := by
    rw [div_lt_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hsin : ∀ β ∈ Set.Icc (1 / (2 * q)) (1 / 2), 0 < sin (π * β) := fun β hβ ↦
    sin_pos_of_pos_of_lt_pi (by nlinarith [pi_pos, hβ.1]) (by nlinarith [pi_pos, hβ.2])
  have hcont : ContinuousOn (fun β ↦ 1 / sin (π * β)) (Set.Icc (1 / (2 * q)) (1 / 2)) :=
    continuousOn_const.div (by fun_prop) fun β hβ ↦ (hsin β hβ).ne'
  have hcont' : ContinuousOn (fun β : ℝ ↦ 1 / (2 * β)) (Set.Icc (1 / (2 * q)) (1 / 2)) :=
    continuousOn_const.div (continuousOn_const.mul continuousOn_id) fun β hβ ↦
      (mul_pos two_pos (ha.trans_le hβ.1)).ne'
  have hle : ∀ β ∈ Set.Ioo (1 / (2 * q)) (1 / 2), 1 / sin (π * β) < 1 / (2 * β) := by
    intro β hβ
    have hβ0 : 0 < β := ha.trans hβ.1
    have h := mul_lt_sin (x := π * β) (by positivity) (by nlinarith [pi_pos, hβ.2])
    have e : 2 / π * (π * β) = 2 * β := by field_simp
    rw [e] at h
    exact one_div_lt_one_div_of_lt (by positivity) h
  have hle' : ∀ β ∈ Set.Ioc (1 / (2 * q)) (1 / 2), 1 / sin (π * β) ≤ 1 / (2 * β) := by
    intro β hβ
    have hβ0 : 0 < β := ha.trans hβ.1
    have h := mul_le_sin (x := π * β) (by positivity) (by nlinarith [pi_pos, hβ.2])
    have e : 2 / π * (π * β) = 2 * β := by field_simp
    rw [e] at h
    exact one_div_le_one_div_of_le (by positivity) h
  have hlt := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt hab hcont
    hcont' hle'
    ⟨(1 / (2 * q) + 1 / 2) / 2, ⟨by linarith, by linarith⟩, hle _ ⟨by linarith, by linarith⟩⟩
  have hval : ∫ β in (1 / (2 * q))..(1 / 2), 1 / (2 * β) = 1 / 2 * log q := by
    have : (fun β : ℝ ↦ 1 / (2 * β)) = fun β ↦ (1 / 2) * β⁻¹ := by
      ext β; rw [one_div, mul_inv, one_div]
    rw [this, intervalIntegral.integral_const_mul, integral_inv_of_pos ha (by norm_num)]
    congr 1
    rw [show (1 / 2 : ℝ) / (1 / (2 * q)) = q by field_simp]
  linarith

/-- **Davenport, Ch. 23**: `∑_{a=1}^{q-1} 1/sin(πa/q) < q log q` for `q ≥ 2`, by the convexity
lemma with `δ = 1/(2q)` and `sin πβ > 2β` on `(0, 1/2)`. -/
@[kb "davenport1980" "Ch 23, p. 136"]
theorem sum_one_div_sin_lt_mul_log {q : ℕ} (hq : 2 ≤ q) :
    ∑ a ∈ Icc 1 (q - 1), 1 / sin (π * (a / q)) < q * log q := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hq1 : (1 : ℝ) < q := by exact_mod_cast (show 1 < q by omega)
  set g : ℝ → ℝ := fun β ↦ 1 / sin (π * β) with hg
  have hgint : ∀ u v : ℝ, 0 < u → u ≤ v → v < 1 → IntervalIntegrable g MeasureTheory.volume u v := by
    intro u v hu huv hv
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le huv]
    refine continuousOn_const.div (by fun_prop) fun β hβ ↦ ?_
    exact (sin_pos_of_pos_of_lt_pi (by nlinarith [pi_pos, hβ.1])
      (by nlinarith [pi_pos, hβ.2])).ne'
  set c : ℕ → ℝ := fun i ↦ (i + 1 / 2) / q with hc
  have hc0 : 0 < c 0 := by simp only [c]; positivity
  have hcle : ∀ i j, i ≤ j → c i ≤ c j := fun i j h ↦ by
    simp only [c]; gcongr
  have hclt : ∀ i, i ≤ q - 1 → c i < 1 := fun i h ↦ by
    simp only [c]; rw [div_lt_one hq0]
    have : (i : ℝ) ≤ q - 1 := by
      have : ((q - 1 : ℕ) : ℝ) = q - 1 := by rw [Nat.cast_sub (by omega)]; norm_num
      rw [← this]; exact_mod_cast h
    linarith
  -- each term is at most `q` times an integral over an interval of length `1/q`
  have hterm : ∀ a ∈ Icc 1 (q - 1), g (a / q) ≤ q * ∫ β in (c (a - 1))..(c a), g β := by
    intro a ha
    have ha := mem_Icc.1 ha
    have hδ : (0 : ℝ) < 1 / (2 * q) := by positivity
    have e1 : (a : ℝ) / q - 1 / (2 * q) = c (a - 1) := by
      simp only [c]; rw [Nat.cast_sub ha.1]; field_simp; ring
    have e2 : (a : ℝ) / q + 1 / (2 * q) = c a := by simp only [c]; field_simp
    have hconv : ConvexOn ℝ (Set.Icc ((a : ℝ) / q - 1 / (2 * q)) (a / q + 1 / (2 * q))) g := by
      refine convexOn_one_div_sin_pi.subset ?_ (convex_Icc _ _)
      rw [e1, e2]
      intro β hβ
      exact ⟨lt_of_lt_of_le hc0 ((hcle 0 _ (Nat.zero_le _)).trans hβ.1),
        lt_of_le_of_lt hβ.2 (hclt a ha.2)⟩
    have hint : IntervalIntegrable g MeasureTheory.volume ((a : ℝ) / q - 1 / (2 * q))
        (a / q + 1 / (2 * q)) := by
      rw [e1, e2]
      exact hgint _ _ (lt_of_lt_of_le hc0 (hcle 0 _ (Nat.zero_le _))) (hcle _ _ (by omega))
        (hclt a ha.2)
    have := le_average_integral_of_convexOn hδ hconv hint
    rw [e1, e2] at this
    convert this using 2
    field_simp
  have hsum : ∑ a ∈ Icc 1 (q - 1), ∫ β in (c (a - 1))..(c a), g β = ∫ β in (c 0)..(c (q - 1)), g β := by
    rw [← intervalIntegral.sum_integral_adjacent_intervals (a := c) (n := q - 1)]
    · have : Icc 1 (q - 1) = (range (q - 1)).map ⟨(· + 1), add_left_injective 1⟩ := by
        ext a; simp only [mem_Icc, mem_map, mem_range, Function.Embedding.coeFn_mk]
        constructor
        · intro h; exact ⟨a - 1, by omega, by omega⟩
        · rintro ⟨b, hb, rfl⟩; omega
      rw [this, sum_map]
      rfl
    · intro k hk
      exact hgint _ _ (lt_of_lt_of_le hc0 (hcle 0 _ (Nat.zero_le _))) (hcle _ _ (by omega))
        (hclt _ (by omega))
  have hc0' : c 0 = 1 / (2 * q) := by simp only [c]; field_simp; ring
  have hcq : c (q - 1) = 1 - 1 / (2 * q) := by
    simp only [c]; rw [Nat.cast_sub (by omega)]; field_simp; ring
  have hsymm : ∫ β in (1 / (2 * q))..(1 - 1 / (2 * q)), g β =
      2 * ∫ β in (1 / (2 * q))..(1 / 2), g β := by
    have hmid : (1 : ℝ) / (2 * q) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
    have hpos' : 0 < 1 / (2 * (q : ℝ)) := by positivity
    rw [← intervalIntegral.integral_add_adjacent_intervals (b := 1 / 2)
      (hgint _ _ hpos' hmid (by norm_num))
      (hgint _ _ (by norm_num) (by linarith) (by linarith))]
    have hrefl : ∫ β in (1 / 2 : ℝ)..(1 - 1 / (2 * q)), g β = ∫ β in (1 / (2 * q))..(1 / 2), g β := by
      have := intervalIntegral.integral_comp_sub_left g (a := 1 / (2 * q)) (b := 1 / 2) 1
      rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num] at this
      rw [← this]
      refine intervalIntegral.integral_congr fun β _ ↦ ?_
      simp only [g]
      rw [show π * (1 - β) = π - π * β by ring, sin_pi_sub]
    rw [hrefl]; ring
  have hint_lt := integral_one_div_sin_pi_lt hq1
  calc ∑ a ∈ Icc 1 (q - 1), 1 / sin (π * (a / q)) = ∑ a ∈ Icc 1 (q - 1), g (a / q) := rfl
    _ ≤ ∑ a ∈ Icc 1 (q - 1), q * ∫ β in (c (a - 1))..(c a), g β := sum_le_sum hterm
    _ = q * (2 * ∫ β in (1 / (2 * q))..(1 / 2), g β) := by
        rw [← mul_sum, hsum, hc0', hcq, hsymm]
    _ < q * (2 * (1 / 2 * log q)) := by gcongr
    _ = q * log q := by ring

/-! ### Primitive characters: inequality (B) -/

variable {q : ℕ} [NeZero q]

/-- **Davenport, Ch. 23 (from §9)**: for a primitive character `χ` modulo `q` and every integer
`n`, `χ(n) τ(χ̄) = ∑_{a mod q} χ̄(a) e(an/q)`. -/
@[kb "davenport1980" "Ch 23, p. 135"]
theorem char_mul_gaussSum_inv {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (n : ℤ) :
    χ n * gaussSum χ⁻¹ ZMod.stdAddChar =
      ∑ a : ZMod q, χ⁻¹ a * ZMod.stdAddChar (a * (n : ZMod q)) := by
  have h := gaussSum_mulShift_of_isPrimitive ZMod.stdAddChar hχ.inv (n : ZMod q)
  rw [inv_inv] at h
  rw [← h, gaussSum]
  refine sum_congr rfl fun a _ ↦ ?_
  rw [AddChar.mulShift_apply, mul_comm (n : ZMod q)]

/-- `|∑_{M < n ≤ M + N} e(jn/q)| ≤ |sin(πNj/q)|/sin(πj/q)` for `0 < j < q`. -/
theorem norm_sum_Ioc_stdAddChar_le {j : ℕ} (hj : 1 ≤ j) (hjq : j < q) (M : ℤ) (N : ℕ) :
    ‖∑ n ∈ Ioc M (M + N), ZMod.stdAddChar ((j : ZMod q) * (n : ZMod q))‖ =
      |sin (π * (N * j / q))| / sin (π * (j / q)) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hpos : 0 < sin (π * (j / q)) := by
    apply sin_pos_of_pos_of_lt_pi (by have : (0 : ℝ) < j := by exact_mod_cast hj
                                      positivity)
    have : (j : ℝ) / q < 1 := by rw [div_lt_one hq0]; exact_mod_cast hjq
    nlinarith [pi_pos]
  have e : ∀ n : ℤ, ZMod.stdAddChar ((j : ZMod q) * (n : ZMod q)) =
      Complex.exp (Complex.I * ((2 * π * j / q : ℝ) : ℂ) * n) := by
    intro n
    have : (j : ZMod q) * n = (((j : ℤ) * n : ℤ) : ZMod q) := by push_cast; ring
    rw [this, ZMod.stdAddChar_coe]
    congr 1; push_cast; ring
  rw [sum_congr rfl (fun n _ ↦ e n)]
  have h2 : 2 * π * j / q / 2 = π * (j / q) := by ring
  have h3 : (N : ℝ) * (2 * π * j / q) / 2 = π * (N * j / q) := by ring
  rw [norm_sum_Ioc_exp (by rw [h2]; exact hpos.ne') M N, h2, h3, abs_of_pos hpos]

/-- **Davenport, Ch. 23**: for a primitive character `χ` modulo `q > 1`, an interval sum is
bounded by `q^{-1/2} ∑_{a=1}^{q-1} |sin(πNa/q)/sin(πa/q)|`. -/
@[kb "davenport1980" "Ch 23, p. 136"]
theorem norm_sum_Ioc_le_of_isPrimitive {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
    (hq : 1 < q) (M : ℤ) (N : ℕ) :
    ‖∑ n ∈ Ioc M (M + N), χ n‖ ≤
      1 / √q * ∑ a ∈ Icc 1 (q - 1), |sin (π * (N * a / q))| / sin (π * (a / q)) := by
  set τ := gaussSum χ⁻¹ ZMod.stdAddChar
  have hτ : ‖τ‖ = √q := DirichletCharacter.norm_gaussSum_stdAddChar hχ.inv
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hτ0 : τ ≠ 0 := by
    intro h; rw [h, norm_zero] at hτ; exact (Real.sqrt_pos.2 hq0).ne' hτ.symm
  have hexp : ∑ n ∈ Ioc M (M + N), χ n =
      τ⁻¹ * ∑ a : ZMod q, χ⁻¹ a * ∑ n ∈ Ioc M (M + N), ZMod.stdAddChar (a * (n : ZMod q)) := by
    rw [eq_inv_mul_iff_mul_eq₀ hτ0, mul_comm, sum_mul]
    simp only [τ, char_mul_gaussSum_inv hχ, mul_sum]
    exact sum_comm
  rw [hexp, norm_mul, norm_inv, hτ, one_div]
  gcongr
  rw [Apostol.sum_zmod_eq_sum_range, range_eq_Ico, sum_eq_sum_Ico_succ_bot (by omega : 0 < q)]
  have hz : ¬ IsUnit ((0 : ℕ) : ZMod q) := by
    rw [Nat.cast_zero, isUnit_zero_iff]; have : Fact (1 < q) := ⟨hq⟩; exact zero_ne_one
  rw [MulChar.map_nonunit _ hz, zero_mul, zero_add]
  have hI : Ico (0 + 1) q = Icc 1 (q - 1) := by ext j; simp only [mem_Ico, mem_Icc]; omega
  rw [hI]
  refine (norm_sum_le _ _).trans (sum_le_sum fun a ha ↦ ?_)
  have ha := mem_Icc.1 ha
  rw [norm_mul, norm_sum_Ioc_stdAddChar_le ha.1 (by omega)]
  calc ‖χ⁻¹ (a : ZMod q)‖ * (|sin (π * (N * a / q))| / sin (π * (a / q)))
      ≤ 1 * (|sin (π * (N * a / q))| / sin (π * (a / q))) := by
        gcongr
        · have : 0 < sin (π * (a / q)) := by
            apply sin_pos_of_pos_of_lt_pi (by have : (0 : ℝ) < a := by exact_mod_cast ha.1
                                              positivity)
            have : (a : ℝ) / q < 1 := by rw [div_lt_one hq0]; exact_mod_cast (show a < q by omega)
            nlinarith [pi_pos]
          positivity
        · exact DirichletCharacter.norm_le_one _ _
    _ = _ := one_mul _

/-- **Davenport, Ch. 23, inequality (B)**: for a primitive character `χ` modulo `q > 1`,
`|∑_{M < n ≤ M + N} χ(n)| < √q log q`. -/
@[kb "davenport1980" "Ch 23, p. 135"]
theorem norm_sum_Ioc_lt_of_isPrimitive {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
    (hq : 1 < q) (M : ℤ) (N : ℕ) :
    ‖∑ n ∈ Ioc M (M + N), χ n‖ < √q * log q := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  refine (norm_sum_Ioc_le_of_isPrimitive hχ hq M N).trans_lt ?_
  have hle : ∑ a ∈ Icc 1 (q - 1), |sin (π * (N * a / q))| / sin (π * (a / q)) ≤
      ∑ a ∈ Icc 1 (q - 1), 1 / sin (π * (a / q)) := by
    refine sum_le_sum fun a ha ↦ ?_
    have ha := mem_Icc.1 ha
    have : 0 < sin (π * (a / q)) := by
      apply sin_pos_of_pos_of_lt_pi (by have : (0 : ℝ) < a := by exact_mod_cast ha.1
                                        positivity)
      have : (a : ℝ) / q < 1 := by rw [div_lt_one hq0]; exact_mod_cast (show a < q by omega)
      nlinarith [pi_pos]
    gcongr
    exact abs_sin_le_one _
  have hlt := sum_one_div_sin_lt_mul_log (show 2 ≤ q by omega)
  have hs : 0 < √(q : ℝ) := Real.sqrt_pos.2 hq0
  calc 1 / √q * ∑ a ∈ Icc 1 (q - 1), |sin (π * (N * a / q))| / sin (π * (a / q))
      ≤ 1 / √q * ∑ a ∈ Icc 1 (q - 1), 1 / sin (π * (a / q)) := by gcongr
    _ < 1 / √q * (q * log q) := by gcongr
    _ = (√q * √q) / √q * log q := by rw [Real.mul_self_sqrt hq0.le]; ring
    _ = √q * log q := by field_simp

/-! ### Imprimitive characters: inequality (A) -/

/-- Multiples of `d > 0` in `(M, M + N]` are `d m` with `M / d < m ≤ (M + N) / d`. -/
lemma sum_Ioc_filter_dvd {R : Type*} [AddCommMonoid R] (f : ℤ → R) (M : ℤ) (N : ℕ) {d : ℕ}
    (hd : 0 < d) :
    ∑ n ∈ (Ioc M (M + N)).filter (fun n ↦ (d : ℤ) ∣ n), f n =
      ∑ m ∈ Ioc (M / d) ((M + N) / d), f (d * m) := by
  have hd' : (0 : ℤ) < d := by exact_mod_cast hd
  symm
  refine sum_nbij' (fun m ↦ d * m) (fun n ↦ n / d) ?_ ?_ ?_ ?_ ?_
  · intro m hm
    rw [mem_Ioc] at hm
    rw [mem_filter, mem_Ioc]
    refine ⟨⟨?_, ?_⟩, dvd_mul_right _ _⟩
    · have := (Int.ediv_lt_iff_lt_mul hd').1 hm.1; linarith
    · have := (Int.le_ediv_iff_mul_le hd').1 hm.2; linarith
  · intro n hn
    rw [mem_filter, mem_Ioc] at hn
    rw [mem_Ioc]
    obtain ⟨⟨h1, h2⟩, k, rfl⟩ := hn
    rw [Int.mul_ediv_cancel_left _ hd'.ne']
    constructor
    · rw [Int.ediv_lt_iff_lt_mul hd']; linarith
    · rw [Int.le_ediv_iff_mul_le hd']; linarith
  · intro m _; simp [Int.mul_ediv_cancel_left _ hd'.ne']
  · intro n hn
    rw [mem_filter] at hn
    exact Int.mul_ediv_cancel' hn.2
  · intro m _; rfl

/-- `μ` over common divisors: `∑_{d ∣ r, d ∣ n} μ(d) = [(n, r) = 1]`. -/
lemma sum_moebius_dvd_int {r : ℕ} (hr : r ≠ 0) (n : ℤ) :
    ∑ d ∈ r.divisors.filter (fun d : ℕ ↦ (d : ℤ) ∣ n),
        ((ArithmeticFunction.moebius d : ℤ) : ℂ) = if IsCoprime (r : ℤ) n then 1 else 0 := by
  have hfilt : r.divisors.filter (fun d : ℕ ↦ (d : ℤ) ∣ n) = (Nat.gcd r n.natAbs).divisors := by
    ext d
    simp only [mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff, Int.natCast_dvd]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨h1, h3⟩, Nat.gcd_ne_zero_left h2⟩
    · rintro ⟨⟨h1, h2⟩, -⟩; exact ⟨⟨h1, hr⟩, h2⟩
  rw [hfilt, Apostol.sum_divisors_moebius_complex]
  have : r.gcd n.natAbs = 1 ↔ IsCoprime (r : ℤ) n := by
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_eq_natAbs]; simp
  by_cases h : IsCoprime (r : ℤ) n
  · rw [if_pos (this.2 h), if_pos h]
  · rw [if_neg (mt this.1 h), if_neg h]

/-- An integer interval `(A, B]` with `A ≤ B` has the form `(A, A + N]`. -/
lemma Ioc_eq_Ioc_add (A B : ℤ) (h : A ≤ B) : Ioc A B = Ioc A (A + ((B - A).toNat : ℕ)) := by
  rw [Int.toNat_of_nonneg (by omega)]; congr 1; ring

/-- **Davenport, Ch. 23**: reduction to the primitive case. If `χ` modulo `q` is induced by the
primitive `χ₁` modulo `q₁` and `q = q₁ r`, then
`∑_{M < n ≤ M + N} χ(n) = ∑_{d ∣ r} μ(d) χ₁(d) ∑_{M/d < m ≤ (M+N)/d} χ₁(m)`. -/
@[kb "davenport1980" "Ch 23, p. 136"]
theorem sum_Ioc_changeLevel_eq {q₁ r : ℕ} [NeZero q₁] [NeZero r] (χ₁ : DirichletCharacter ℂ q₁)
    (M : ℤ) (N : ℕ) :
    ∑ n ∈ Ioc M (M + N), DirichletCharacter.changeLevel (dvd_mul_right q₁ r) χ₁ n =
      ∑ d ∈ r.divisors, ((ArithmeticFunction.moebius d : ℤ) : ℂ) * χ₁ d *
        ∑ m ∈ Ioc (M / d) ((M + N) / d), χ₁ m := by
  classical
  have hr : r ≠ 0 := NeZero.ne r
  -- `χ(n) = χ₁(n) [(n, r) = 1]`
  have hA : ∀ n : ℤ, DirichletCharacter.changeLevel (dvd_mul_right q₁ r) χ₁ n =
      ∑ d ∈ r.divisors.filter (fun d : ℕ ↦ (d : ℤ) ∣ n),
        ((ArithmeticFunction.moebius d : ℤ) : ℂ) * χ₁ n := by
    intro n
    rw [← sum_mul, sum_moebius_dvd_int hr]
    by_cases hc : IsCoprime n ((q₁ * r : ℕ) : ℤ)
    · have hcr : IsCoprime (r : ℤ) n := by
        push_cast at hc; exact (hc.of_mul_right_right).symm
      rw [if_pos hcr, one_mul]
      exact DirichletCharacter.changeLevel_eq_cast_of_dvd' χ₁ _ hc
    · rw [MulChar.map_nonunit _ (by rwa [ZMod.isUnit_intCast_iff_isCoprime, isCoprime_comm])]
      split_ifs with hcr
      · rw [one_mul]
        refine (MulChar.map_nonunit _ ?_).symm
        rw [ZMod.isUnit_intCast_iff_isCoprime]
        intro h1
        apply hc
        push_cast
        exact (IsCoprime.mul_left h1 hcr).symm
      · rw [zero_mul]
  simp_rw [hA]
  rw [sum_comm' (t' := r.divisors) (s' := fun d ↦ (Ioc M (M + N)).filter (fun n ↦ (d : ℤ) ∣ n))
    (by intro n d; simp only [mem_filter]; tauto)]
  refine sum_congr rfl fun d hd ↦ ?_
  have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
  rw [← mul_sum, sum_Ioc_filter_dvd (fun n : ℤ ↦ χ₁ (n : ZMod q₁)) M N hd0, mul_assoc]
  congr 1
  rw [mul_sum]
  refine sum_congr rfl fun m _ ↦ ?_
  rw [Int.cast_mul, map_mul]; push_cast; ring

/-- **Davenport, Ch. 23, inequality (A)** (Pólya–Vinogradov): for every nonprincipal character
`χ` modulo `q` and all integers `M`, `N ≥ 0`, `|∑_{M < n ≤ M + N} χ(n)| ≤ 2 √q log q`
(the numerical constant `2` from `d(r) ≤ 2√r`). -/
@[kb "davenport1980" "Ch 23, p. 135"]
theorem norm_sum_Ioc_le {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) (M : ℤ) (N : ℕ) :
    ‖∑ n ∈ Ioc M (M + N), χ n‖ ≤ 2 * √q * log q := by
  classical
  set c := χ.conductor
  have hcdvd : c ∣ q := χ.conductor_dvd_level
  have hq0 : q ≠ 0 := NeZero.ne q
  have hc0 : c ≠ 0 := fun h0 ↦ hq0 (Nat.eq_zero_of_zero_dvd (h0 ▸ hcdvd))
  have hc1 : c ≠ 1 := fun h1 ↦ hχ ((DirichletCharacter.eq_one_iff_conductor_eq_one).mpr h1)
  have hc : 1 < c := by omega
  have : NeZero c := ⟨hc0⟩
  obtain ⟨r, hr⟩ := hcdvd
  have hr0 : r ≠ 0 := by rintro rfl; simp at hr; exact hq0 hr
  have : NeZero r := ⟨hr0⟩
  set χ₁ := χ.primitiveCharacter
  have hχ₁ : χ₁.IsPrimitive := χ.primitiveCharacter_isPrimitive
  -- transport along `q = c * r`
  have key : ∀ (k : ℕ) [NeZero k] (hk : k = c * r) (ψ : DirichletCharacter ℂ k),
      DirichletCharacter.changeLevel (hk ▸ dvd_mul_right c r) χ₁ = ψ →
      ‖∑ n ∈ Ioc M (M + N), ψ n‖ ≤ 2 * √(c * r : ℕ) * log c := by
    intro k _ hk ψ hψ
    subst hk
    rw [← hψ, sum_Ioc_changeLevel_eq]
    have hbound : ∀ d ∈ r.divisors, ‖((ArithmeticFunction.moebius d : ℤ) : ℂ) * χ₁ d *
        ∑ m ∈ Ioc (M / d) ((M + N) / d), χ₁ m‖ ≤ √c * log c := by
      intro d hd
      have hd0 : (0 : ℤ) < d := by exact_mod_cast Nat.pos_of_mem_divisors hd
      have hAB : M / (d : ℤ) ≤ (M + N) / d := Int.ediv_le_ediv hd0 (by omega)
      rw [norm_mul, norm_mul, Ioc_eq_Ioc_add _ _ hAB]
      have h1 : ‖((ArithmeticFunction.moebius d : ℤ) : ℂ)‖ ≤ 1 := by
        rw [Complex.norm_intCast]; exact_mod_cast ArithmeticFunction.abs_moebius_le_one
      have h2 : ‖χ₁ (d : ZMod c)‖ ≤ 1 := DirichletCharacter.norm_le_one _ _
      have h3 := (norm_sum_Ioc_lt_of_isPrimitive hχ₁ hc (M / d) ((M + N) / d - M / d).toNat).le
      have hpos : 0 ≤ √(c : ℝ) * log c := by
        have : (1 : ℝ) ≤ c := by exact_mod_cast hc.le
        have := log_nonneg this; positivity
      calc _ ≤ 1 * 1 * (√c * log c) := by gcongr
        _ = √c * log c := by ring
    refine (norm_sum_le _ _).trans ((sum_le_sum hbound).trans ?_)
    rw [sum_const, nsmul_eq_mul]
    have hdiv := Apostol.card_divisors_le_two_sqrt r
    have hpos : 0 ≤ √(c : ℝ) * log c := by
      have : (1 : ℝ) ≤ c := by exact_mod_cast hc.le
      have := log_nonneg this; positivity
    calc (r.divisors.card : ℝ) * (√c * log c) ≤ 2 * √r * (√c * log c) := by gcongr
      _ = 2 * √(c * r : ℕ) * log c := by
        push_cast; rw [Real.sqrt_mul (by positivity)]; ring
  have h := key q hr χ χ.changeLevel_primitiveCharacter
  have hlog : log (c : ℝ) ≤ log q := by
    apply log_le_log (by exact_mod_cast (show 0 < c by omega))
    exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hq0) ⟨r, hr⟩
  rw [← hr] at h
  have : 0 ≤ 2 * √(q : ℝ) := by positivity
  exact h.trans (by gcongr)

/-! ### Quadratic residues in an interval -/

/-- **Davenport, Ch. 23**: for an odd prime `p` the interval `(M, M + N]` with `N ≤ p` contains
`N/2 + O(√p log p)` quadratic residues modulo `p`; precisely, twice their number differs from
`N` by at most `1 + √p log p`. -/
@[kb "davenport1980" "Ch 23, p. 135"]
theorem abs_two_mul_card_residues_sub_le (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2) (M : ℤ)
    {N : ℕ} (hN : N ≤ p) :
    |2 * (((Ioc M (M + N)).filter
        (fun n : ℤ ↦ IsSquare (n : ZMod p) ∧ (n : ZMod p) ≠ 0)).card : ℝ) - N| ≤
      1 + √p * log p := by
  classical
  have hprim : (legendreChar p).IsPrimitive := by
    rw [← jacobiChar_prime]; exact isPrimitive_jacobiChar_prime p hp2
  have hS := norm_sum_Ioc_lt_of_isPrimitive hprim hp.out.one_lt M N
  set I := Ioc M (M + N)
  set R := I.filter (fun n : ℤ ↦ IsSquare (n : ZMod p) ∧ (n : ZMod p) ≠ 0)
  set Z := I.filter (fun n : ℤ ↦ (n : ZMod p) = 0)
  set T := I.filter (fun n : ℤ ↦ ¬ IsSquare (n : ZMod p))
  -- values of the character
  have hval : ∀ n : ℤ, (legendreChar p n : ℂ) =
      (if IsSquare (n : ZMod p) ∧ (n : ZMod p) ≠ 0 then 1 else 0) -
        (if ¬ IsSquare (n : ZMod p) then 1 else 0) := by
    intro n
    rw [legendreChar_apply]
    by_cases h0 : (n : ZMod p) = 0
    · simp [h0]
    · by_cases hs : IsSquare (n : ZMod p)
      · rw [quadraticChar_one_iff_isSquare h0 |>.2 hs]; simp [hs, h0]
      · rw [quadraticChar_neg_one_iff_not_isSquare.2 hs]; simp [hs]
  have hsum : ∑ n ∈ I, legendreChar p n = (R.card : ℂ) - T.card := by
    simp_rw [hval, sum_sub_distrib, ← sum_filter, sum_const, nsmul_one]
    rfl
  -- every integer is a nonzero square, zero, or a nonsquare
  have hcard : R.card + Z.card + T.card = N := by
    have h1 : R.card + (I.filter (fun n : ℤ ↦ ¬ (IsSquare (n : ZMod p) ∧ (n : ZMod p) ≠ 0))).card
        = I.card := card_filter_add_card_filter_not _
    have h2 := card_filter_add_card_filter_not
      (s := I.filter (fun n : ℤ ↦ ¬ (IsSquare (n : ZMod p) ∧ (n : ZMod p) ≠ 0)))
      (fun n : ℤ ↦ (n : ZMod p) = 0)
    rw [filter_filter, filter_filter] at h2
    have eZ : I.filter (fun n : ℤ ↦ ¬ (IsSquare (n : ZMod p) ∧ (n : ZMod p) ≠ 0) ∧
        (n : ZMod p) = 0) = Z := by
      refine filter_congr fun n _ ↦ ?_; constructor
      · exact fun h ↦ h.2
      · intro h; exact ⟨fun h' ↦ h'.2 h, h⟩
    have eT : I.filter (fun n : ℤ ↦ ¬ (IsSquare (n : ZMod p) ∧ (n : ZMod p) ≠ 0) ∧
        ¬ (n : ZMod p) = 0) = T := by
      refine filter_congr fun n _ ↦ ?_; constructor
      · rintro ⟨h1, h2⟩ hs; exact h1 ⟨hs, h2⟩
      · intro h; exact ⟨fun h' ↦ h h'.1, fun h0 ↦ h (h0 ▸ ⟨0, by simp⟩)⟩
    rw [eZ, eT] at h2
    have hI : I.card = N := by simp only [I, Int.card_Ioc]; omega
    omega
  -- at most one multiple of `p` in an interval of length `N ≤ p`
  have hZ : Z.card ≤ 1 := by
    rw [card_le_one]
    intro a ha b hb
    simp only [Z, I, mem_filter, mem_Ioc, ZMod.intCast_zmod_eq_zero_iff_dvd] at ha hb
    obtain ⟨⟨ha1, ha2⟩, k, rfl⟩ := ha
    obtain ⟨⟨hb1, hb2⟩, l, rfl⟩ := hb
    have hp0 : (0 : ℤ) < p := by exact_mod_cast hp.out.pos
    have hN' : (N : ℤ) ≤ p := by exact_mod_cast hN
    have : k = l := by
      by_contra hkl
      rcases lt_or_gt_of_ne hkl with h | h
      · have : (p : ℤ) * k + p ≤ p * l := by nlinarith
        linarith
      · have : (p : ℤ) * l + p ≤ p * k := by nlinarith
        linarith
    rw [this]
  have hreal : |2 * (R.card : ℝ) - N| ≤ Z.card + ‖∑ n ∈ I, legendreChar p n‖ := by
    rw [hsum]
    have e : (R.card : ℂ) - T.card = ((R.card - T.card : ℝ) : ℂ) := by push_cast; ring
    rw [e, Complex.norm_real, Real.norm_eq_abs]
    have hN : (N : ℝ) = R.card + Z.card + T.card := by exact_mod_cast hcard.symm
    rw [hN]
    have : 2 * (R.card : ℝ) - (R.card + Z.card + T.card) = (R.card - T.card) - Z.card := by ring
    rw [this]
    refine (abs_sub _ _).trans ?_
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ Z.card)]
    linarith
  have hZ' : (Z.card : ℝ) ≤ 1 := by exact_mod_cast hZ
  linarith

end NTKB.Davenport
