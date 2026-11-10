/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.Nonvanishing
import NTKB.Attr

/-!
# Vaughan's identity (Davenport, Chapter 24)

With `F(s) = ∑_{m ≤ U} Λ(m) m^{-s}` and `G(s) = ∑_{d ≤ V} μ(d) d^{-s}`:

* identity (1): `-ζ'/ζ = F - ζFG - ζ'G + (-ζ'/ζ - F)(1 - ζG)` for `Re s > 1`
  (`vaughan_identity_LSeries`);
* its coefficient form `Λ = a₁ + a₂ + a₃ + a₄` as an identity of arithmetic functions
  (`vaughan_identity`), with `a₁ = Λ·[n ≤ U]`, `a₂ = -ζ * F * G`, `a₃ = log * G`,
  `a₄ = (Λ - F) * (1 - ζ * G)`, where `F = Λ·[m ≤ U]`, `G = μ·[d ≤ V]`; the factor
  `(1 - ζ * G)(k) = [k = 1] - ∑_{d ∣ k, d ≤ V} μ(d)` vanishes for `k ≤ V` (`one_sub_zeta_mul_trunc`);
* the decomposition `∑_{n ≤ N} f(n) Λ(n) = S₁ + S₂ + S₃ + S₄` (`sum_mul_vonMangoldt_eq`);
* the type I estimates (B) `|S₂| ≤ log(UV) ∑_{t ≤ UV} |∑_{r ≤ N/t} f(rt)|` (`norm_S₂_le`) and
  (C) `|S₃| ≤ log N ∑_{d ≤ V} max_w |∑_{w ≤ h ≤ N/d} f(dh)|` (`norm_S₃_le`), the latter by
  partial summation;
* the shape of `S₄ = -∑_{U < m} Λ(m) ∑_{V < k ≤ N/m} (∑_{d ∣ k, d ≤ V} μ(d)) f(mk)` (`S₄_eq`).
-/

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

namespace NTKB.Davenport

/-! ### The identity -/

set_option linter.unusedVariables false in
/-- **Davenport, Ch. 24, identity (1)**: for `Re s > 1` and any `U`, `V`,
`-ζ'/ζ = F - ζFG - ζ'G + (-ζ'/ζ - F)(1 - ζG)` with `F(s) = ∑_{m ≤ U} Λ(m) m^{-s}`,
`G(s) = ∑_{d ≤ V} μ(d) d^{-s}`. -/
@[kb "davenport1980" "Ch 24, p. 138, (1)"]
theorem vaughan_identity_LSeries {s : ℂ} (hs : 1 < s.re) (U V : ℕ) (F G : ℂ)
    (hF : F = ∑ m ∈ Icc 1 U, (Λ m : ℂ) * (m : ℂ) ^ (-s))
    (hG : G = ∑ d ∈ Icc 1 V, (moebius d : ℂ) * (d : ℂ) ^ (-s)) :
    -deriv riemannZeta s / riemannZeta s = F - riemannZeta s * F * G - deriv riemannZeta s * G +
      (-deriv riemannZeta s / riemannZeta s - F) * (1 - riemannZeta s * G) := by
  have hz : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs
  field_simp
  ring

/-- The truncation `f·[n ≤ U]` of an arithmetic function. -/
def truncate {R : Type*} [Zero R] (f : ArithmeticFunction R) (U : ℕ) : ArithmeticFunction R :=
  ⟨fun n ↦ if n ≤ U then f n else 0, by simp⟩

@[simp]
lemma truncate_apply {R : Type*} [Zero R] (f : ArithmeticFunction R) (U n : ℕ) :
    truncate f U n = if n ≤ U then f n else 0 := rfl

/-- **Davenport, Ch. 24**: Vaughan's identity in coefficient form,
`Λ = F - ζ * F * G + log * G + (Λ - F) * (1 - ζ * G)` with `F = Λ·[m ≤ U]`, `G = μ·[d ≤ V]`; the
four terms are Davenport's `a₁, a₂, a₃, a₄`. -/
@[kb "davenport1980" "Ch 24, p. 139"]
theorem vaughan_identity (U V : ℕ) :
    (Λ : ArithmeticFunction ℝ) =
      truncate Λ U - (ζ : ArithmeticFunction ℝ) * truncate Λ U * truncate (μ : ArithmeticFunction ℝ) V +
        log * truncate (μ : ArithmeticFunction ℝ) V +
        (Λ - truncate Λ U) * (1 - (ζ : ArithmeticFunction ℝ) * truncate (μ : ArithmeticFunction ℝ) V) := by
  have h : (Λ : ArithmeticFunction ℝ) * (ζ : ArithmeticFunction ℝ) = log := vonMangoldt_mul_zeta
  linear_combination truncate (μ : ArithmeticFunction ℝ) V * h

/-- `(ζ * G)(k) = ∑_{d ∣ k, d ≤ V} μ(d)`. -/
lemma zeta_mul_truncate_apply (V k : ℕ) :
    ((ζ : ArithmeticFunction ℝ) * truncate (μ : ArithmeticFunction ℝ) V) k =
      ∑ d ∈ k.divisors.filter (· ≤ V), (μ d : ℝ) := by
  rw [coe_zeta_mul_apply, sum_filter]
  rfl

/-- `(1 - ζ * G)(k) = 0` for `1 ≤ k ≤ V`: then `∑_{d ∣ k, d ≤ V} μ(d) = ∑_{d ∣ k} μ(d) = [k = 1]`. -/
lemma one_sub_zeta_mul_trunc {V k : ℕ} (hkV : k ≤ V) :
    (1 - (ζ : ArithmeticFunction ℝ) * truncate (μ : ArithmeticFunction ℝ) V) k = 0 := by
  rw [sub_apply, zeta_mul_truncate_apply]
  have : k.divisors.filter (· ≤ V) = k.divisors :=
    filter_true_of_mem fun d hd ↦ (Nat.divisor_le hd).trans hkV
  rw [this]
  have hμ := congrArg (fun f : ArithmeticFunction ℤ ↦ (f k : ℝ)) moebius_mul_coe_zeta
  simp only [coe_mul_zeta_apply, Int.cast_sum] at hμ
  rw [hμ, ArithmeticFunction.one_apply, ArithmeticFunction.one_apply]
  split_ifs <;> simp

/-- `(1 - ζ * G)(k) = -∑_{d ∣ k, d ≤ V} μ(d)` for `k > V ≥ 1`. -/
lemma one_sub_zeta_mul_trunc_of_lt {V k : ℕ} (hV : 1 ≤ V) (hk : V < k) :
    (1 - (ζ : ArithmeticFunction ℝ) * truncate (μ : ArithmeticFunction ℝ) V) k =
      -∑ d ∈ k.divisors.filter (· ≤ V), (μ d : ℝ) := by
  rw [sub_apply, zeta_mul_truncate_apply, ArithmeticFunction.one_apply, if_neg (by omega),
    zero_sub]

/-! ### Interchanging a divisor sum -/

/-- `∑_{n ≤ N} f(n) ∑_{d ∣ n} g(d) h(n/d) = ∑_{d ≤ N} g(d) ∑_{r ≤ N/d} f(dr) h(r)`. -/
lemma sum_mul_sum_divisors {R : Type*} [CommSemiring R] (f g h : ℕ → R) (N : ℕ) :
    ∑ n ∈ Icc 1 N, f n * ∑ d ∈ n.divisors, g d * h (n / d) =
      ∑ d ∈ Icc 1 N, g d * ∑ r ∈ Icc 1 (N / d), f (d * r) * h r := by
  simp_rw [mul_sum]
  rw [sum_comm' (t' := Icc 1 N) (s' := fun d ↦ (Icc 1 N).filter (d ∣ ·))]
  · refine sum_congr rfl fun d hd ↦ ?_
    have hd0 : 0 < d := (mem_Icc.1 hd).1
    refine sum_nbij' (fun n ↦ n / d) (fun r ↦ d * r) ?_ ?_ ?_ ?_ ?_
    · intro n hn
      rw [mem_filter, mem_Icc] at hn
      obtain ⟨⟨h1, h2⟩, k, rfl⟩ := hn
      rw [mem_Icc, Nat.mul_div_cancel_left _ hd0]
      refine ⟨Nat.pos_of_ne_zero (by rintro rfl; simp at h1), ?_⟩
      exact (Nat.le_div_iff_mul_le hd0).2 (by rw [mul_comm]; exact h2)
    · intro r hr
      rw [mem_Icc] at hr
      rw [mem_filter, mem_Icc]
      refine ⟨⟨(Nat.mul_pos hd0 hr.1 : 0 < d * r), ?_⟩, dvd_mul_right _ _⟩
      calc d * r ≤ d * (N / d) := Nat.mul_le_mul_left d hr.2
        _ ≤ N := Nat.mul_div_le N d
    · intro n hn
      rw [mem_filter] at hn
      exact Nat.mul_div_cancel' hn.2
    · intro r _; exact Nat.mul_div_cancel_left r hd0
    · intro n hn
      rw [mem_filter] at hn
      rw [Nat.mul_div_cancel' hn.2]
      ring
  · intro n d
    simp only [mem_Icc, mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      exact ⟨⟨⟨h1, h2⟩, h3⟩, Nat.pos_of_dvd_of_pos h3 h1, (Nat.le_of_dvd h1 h3).trans h2⟩
    · rintro ⟨⟨⟨h1, h2⟩, h3⟩, -⟩
      exact ⟨⟨h1, h2⟩, h3, by omega⟩

/-! ### The decomposition and the type I sums -/

/-- **Davenport, Ch. 24**: `∑_{n ≤ N} f(n) Λ(n) = S₁ + S₂ + S₃ + S₄` with `Sᵢ = ∑_{n ≤ N} f(n) aᵢ(n)`. -/
@[kb "davenport1980" "Ch 24, p. 139"]
theorem sum_mul_vonMangoldt_eq (f : ℕ → ℂ) (N U V : ℕ) :
    ∑ n ∈ Icc 1 N, f n * (Λ n : ℂ) =
      ∑ n ∈ Icc 1 N, f n * (truncate Λ U n : ℂ) +
      ∑ n ∈ Icc 1 N, f n * (-((ζ : ArithmeticFunction ℝ) * truncate Λ U *
          truncate (μ : ArithmeticFunction ℝ) V) n : ℂ) +
      ∑ n ∈ Icc 1 N, f n * ((log * truncate (μ : ArithmeticFunction ℝ) V) n : ℂ) +
      ∑ n ∈ Icc 1 N, f n * (((Λ - truncate Λ U) *
          (1 - (ζ : ArithmeticFunction ℝ) * truncate (μ : ArithmeticFunction ℝ) V)) n : ℂ) := by
  simp only [← sum_add_distrib, ← mul_add]
  refine sum_congr rfl fun n _ ↦ ?_
  congr 1
  have h := congrArg (fun f : ArithmeticFunction ℝ ↦ (f n : ℂ)) (vaughan_identity U V)
  simp only [add_apply, sub_apply] at h
  rw [h]; push_cast; ring

/-- `|(F * G)(t)| ≤ log t`, and `(F * G)(t) = 0` for `t > UV`. -/
lemma abs_trunc_mul_trunc_le (U V t : ℕ) :
    |(truncate Λ U * truncate (μ : ArithmeticFunction ℝ) V) t| ≤ Real.log t ∧
      (U * V < t → (truncate Λ U * truncate (μ : ArithmeticFunction ℝ) V) t = 0) := by
  rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal (fun a b ↦ truncate Λ U a *
    truncate (μ : ArithmeticFunction ℝ) V b)]
  constructor
  · refine (abs_sum_le_sum_abs _ _).trans ?_
    rw [← vonMangoldt_sum]
    refine sum_le_sum fun m _ ↦ ?_
    simp only [truncate_apply, intCoe_apply]
    split_ifs <;> simp [abs_mul, vonMangoldt_nonneg, abs_of_nonneg]
    exact mul_le_of_le_one_right vonMangoldt_nonneg (by exact_mod_cast abs_moebius_le_one)
  · intro ht
    refine sum_eq_zero fun m hm ↦ ?_
    simp only [truncate_apply]
    have hmt := Nat.div_mul_cancel (Nat.dvd_of_mem_divisors hm)
    split_ifs with h1 h2
    · exfalso
      have : t / m * m ≤ V * U := Nat.mul_le_mul h2 h1
      rw [hmt] at this; nlinarith
    · simp
    · simp
    · simp

/-- **Davenport, Ch. 24, (B)** (type I): for `U, V ≥ 1`,
`|S₂| ≤ log(UV) ∑_{t ≤ UV} |∑_{r ≤ N/t} f(rt)|`. -/
@[kb "davenport1980" "Ch 24, p. 139, (B)"]
theorem norm_S₂_le (f : ℕ → ℂ) (N U V : ℕ) :
    ‖∑ n ∈ Icc 1 N, f n * (-((ζ : ArithmeticFunction ℝ) * truncate Λ U *
          truncate (μ : ArithmeticFunction ℝ) V) n : ℂ)‖ ≤
      Real.log (U * V) * ∑ t ∈ Icc 1 (U * V), ‖∑ r ∈ Icc 1 (N / t), f (t * r)‖ := by
  set H := truncate Λ U * truncate (μ : ArithmeticFunction ℝ) V
  have hsum : ∑ n ∈ Icc 1 N, f n * (-((ζ : ArithmeticFunction ℝ) * truncate Λ U *
      truncate (μ : ArithmeticFunction ℝ) V) n : ℂ) =
      -∑ t ∈ Icc 1 N, (H t : ℂ) * ∑ r ∈ Icc 1 (N / t), f (t * r) * 1 := by
    rw [← sum_mul_sum_divisors f (fun t ↦ (H t : ℂ)) (fun _ ↦ 1), ← sum_neg_distrib]
    refine sum_congr rfl fun n _ ↦ ?_
    rw [mul_assoc, coe_zeta_mul_apply]
    push_cast
    simp [H]
  rw [hsum, norm_neg]
  simp_rw [mul_one]
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ t ∈ Icc 1 N, ‖(H t : ℂ) * ∑ r ∈ Icc 1 (N / t), f (t * r)‖ ≤
      if t ≤ U * V then Real.log (U * V) * ‖∑ r ∈ Icc 1 (N / t), f (t * r)‖ else 0 := by
    intro t ht
    obtain ⟨h1, h2⟩ := abs_trunc_mul_trunc_le U V t
    split_ifs with htUV
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      gcongr
      refine h1.trans (Real.log_le_log (by exact_mod_cast (mem_Icc.1 ht).1) ?_)
      exact_mod_cast htUV
    · rw [h2 (by omega)]; simp
  refine (sum_le_sum hterm).trans ?_
  rw [← sum_filter, mul_sum]
  refine le_trans (le_of_eq rfl) (sum_le_sum_of_subset_of_nonneg ?_ fun t _ _ ↦ ?_)
  · intro t ht; simp only [mem_filter, mem_Icc] at ht ⊢; omega
  · have : 0 ≤ Real.log (U * V) := by
      rcases Nat.eq_zero_or_pos (U * V) with h | h
      · have : (U : ℝ) * V = 0 := by exact_mod_cast h
        rw [this, Real.log_zero]
      · exact Real.log_nonneg (by exact_mod_cast h)
    positivity

/-- Partial summation: if every tail `∑_{w ≤ h ≤ H} g(h)` has modulus at most `B`, then
`|∑_{h ≤ H} g(h) log h| ≤ B log H`. -/
lemma norm_sum_mul_log_le (g : ℕ → ℂ) (H : ℕ) {B : ℝ}
    (hB : ∀ w ∈ Icc 1 H, ‖∑ h ∈ Icc w H, g h‖ ≤ B) :
    ‖∑ h ∈ Icc 1 H, g h * (Real.log h : ℂ)‖ ≤ Real.log H * B := by
  -- `log h = ∑_{2 ≤ j ≤ h} (log j - log (j - 1))`
  set c : ℕ → ℝ := fun j ↦ Real.log j - Real.log (j - 1 : ℕ)
  have htel : ∀ h : ℕ, 1 ≤ h → Real.log h = ∑ j ∈ Icc 2 h, c j := by
    intro h hh
    induction h with
    | zero => omega
    | succ h ih =>
      rcases Nat.eq_zero_or_pos h with rfl | hpos
      · simp
      rw [← Ico_add_one_right_eq_Icc, sum_Ico_succ_top (by omega), Ico_add_one_right_eq_Icc,
        ← ih hpos]
      simp only [c, Nat.add_sub_cancel]; ring
  have hc : ∀ j ∈ Icc 2 H, 0 ≤ c j := by
    intro j hj
    have hj := (mem_Icc.1 hj).1
    simp only [c, sub_nonneg]
    exact Real.log_le_log (by exact_mod_cast (by omega : 0 < j - 1)) (by exact_mod_cast Nat.sub_le j 1)
  have hswap : ∑ h ∈ Icc 1 H, g h * (Real.log h : ℂ) =
      ∑ j ∈ Icc 2 H, (c j : ℂ) * ∑ h ∈ Icc j H, g h := by
    have : ∀ h ∈ Icc 1 H, g h * (Real.log h : ℂ) = ∑ j ∈ Icc 2 h, (c j : ℂ) * g h := by
      intro h hh
      rw [htel h (mem_Icc.1 hh).1, ← sum_mul, mul_comm]; push_cast; rfl
    rw [sum_congr rfl this]
    simp_rw [mul_sum]
    rw [sum_comm' (t' := Icc 2 H) (s' := fun j ↦ Icc j H)]
    intro h j
    simp only [mem_Icc]
    omega
  rw [hswap]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ j ∈ Icc 2 H, ‖(c j : ℂ) * ∑ h ∈ Icc j H, g h‖ ≤ ∑ j ∈ Icc 2 H, c j * B := by
        refine sum_le_sum fun j hj ↦ ?_
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hc j hj)]
        gcongr
        · exact hc j hj
        · exact hB j (by simp only [mem_Icc] at hj ⊢; omega)
    _ = Real.log H * B := by
        rw [← sum_mul]
        rcases Nat.eq_zero_or_pos H with rfl | hH
        · simp
        · rw [← htel H hH]

/-- **Davenport, Ch. 24, (C)** (type I): if `|∑_{w ≤ h ≤ N/d} f(dh)| ≤ B_d` for all `w`, with
`B_d ≥ 0`, then `|S₃| ≤ log N ∑_{d ≤ V} B_d`. -/
@[kb "davenport1980" "Ch 24, p. 140, (C)"]
theorem norm_S₃_le (f : ℕ → ℂ) (N V : ℕ) (B : ℕ → ℝ) (hB0 : ∀ d, 0 ≤ B d)
    (hB : ∀ d ∈ Icc 1 V, ∀ w ∈ Icc 1 (N / d), ‖∑ h ∈ Icc w (N / d), f (d * h)‖ ≤ B d) :
    ‖∑ n ∈ Icc 1 N, f n * ((log * truncate (μ : ArithmeticFunction ℝ) V) n : ℂ)‖ ≤
      Real.log N * ∑ d ∈ Icc 1 V, B d := by
  set G := truncate (μ : ArithmeticFunction ℝ) V
  have hsum : ∑ n ∈ Icc 1 N, f n * ((log * G) n : ℂ) =
      ∑ d ∈ Icc 1 N, (G d : ℂ) * ∑ r ∈ Icc 1 (N / d), f (d * r) * (Real.log r : ℂ) := by
    rw [← sum_mul_sum_divisors f (fun d ↦ (G d : ℂ)) (fun r ↦ (Real.log r : ℂ))]
    refine sum_congr rfl fun n _ ↦ ?_
    rw [mul_comm log G, ArithmeticFunction.mul_apply,
      Nat.sum_divisorsAntidiagonal (fun a b ↦ G a * log b)]
    push_cast
    simp [log_apply]
  rw [hsum]
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ d ∈ Icc 1 N, ‖(G d : ℂ) * ∑ r ∈ Icc 1 (N / d), f (d * r) * (Real.log r : ℂ)‖ ≤
      if d ≤ V then Real.log N * B d else 0 := by
    intro d hd
    have hd1 := (mem_Icc.1 hd).1
    split_ifs with hdV
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have hG : |G d| ≤ 1 := by
        simp only [G, truncate_apply, if_pos hdV, intCoe_apply]
        exact_mod_cast abs_moebius_le_one
      have h1 := norm_sum_mul_log_le (fun h ↦ f (d * h)) (N / d) (hB d (by simp [mem_Icc]; omega))
      have hlog : Real.log (N / d : ℕ) ≤ Real.log N := by
        rcases Nat.eq_zero_or_pos (N / d) with h0 | h0
        · rw [h0, Nat.cast_zero, Real.log_zero]
          exact Real.log_natCast_nonneg N
        · exact Real.log_le_log (by exact_mod_cast h0) (by exact_mod_cast Nat.div_le_self N d)
      calc |G d| * ‖∑ r ∈ Icc 1 (N / d), f (d * r) * (Real.log r : ℂ)‖
          ≤ 1 * (Real.log (N / d : ℕ) * B d) := by gcongr
        _ ≤ Real.log N * B d := by rw [one_mul]; gcongr; exact hB0 d
    · simp [G, truncate_apply, hdV]
  refine (sum_le_sum hterm).trans ?_
  rw [← sum_filter, mul_sum]
  refine sum_le_sum_of_subset_of_nonneg ?_ fun d _ _ ↦ mul_nonneg (Real.log_natCast_nonneg N) (hB0 d)
  intro d hd; simp only [mem_filter, mem_Icc] at hd ⊢; omega

/-- **Davenport, Ch. 24**: the shape of `S₄`: for `V ≥ 1`,
`S₄ = -∑_{U < m ≤ N} Λ(m) ∑_{V < k ≤ N/m} (∑_{d ∣ k, d ≤ V} μ(d)) f(mk)` (the inner sums are empty
unless `m ≤ N/V`). -/
@[kb "davenport1980" "Ch 24, p. 140"]
theorem S₄_eq (f : ℕ → ℂ) (N U V : ℕ) (hV : 1 ≤ V) :
    ∑ n ∈ Icc 1 N, f n * (((Λ - truncate Λ U) *
        (1 - (ζ : ArithmeticFunction ℝ) * truncate (μ : ArithmeticFunction ℝ) V)) n : ℂ) =
      -∑ m ∈ Ioc U N, (Λ m : ℂ) * ∑ k ∈ Ioc V (N / m),
        ((∑ d ∈ k.divisors.filter (· ≤ V), (μ d : ℝ) : ℝ) : ℂ) * f (m * k) := by
  set A : ArithmeticFunction ℝ := Λ - truncate Λ U with hA
  set B : ArithmeticFunction ℝ :=
    1 - (ζ : ArithmeticFunction ℝ) * truncate (μ : ArithmeticFunction ℝ) V with hB
  have h1 : ∀ n, (((A * B) n : ℝ) : ℂ) = ∑ m ∈ n.divisors, (A m : ℂ) * (B (n / m) : ℂ) := by
    intro n
    rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal (fun a b ↦ A a * B b)]
    push_cast; rfl
  simp_rw [h1]
  rw [sum_mul_sum_divisors f (fun m ↦ (A m : ℂ)) (fun k ↦ (B k : ℂ)), ← sum_neg_distrib]
  have hsubm : Ioc U N ⊆ Icc 1 N := fun m hm ↦ by
    simp only [mem_Ioc, mem_Icc] at hm ⊢; omega
  rw [← sum_subset hsubm (fun m hm hm' ↦ by
    simp only [mem_Ioc, mem_Icc, not_and, not_le] at hm hm'
    have : m ≤ U := by by_contra h; exact absurd (hm' (by omega)) (by omega)
    simp [hA, truncate_apply, this])]
  refine sum_congr rfl fun m hm ↦ ?_
  have hmU : ¬ m ≤ U := by simp only [mem_Ioc] at hm; omega
  have hAm : A m = Λ m := by simp [hA, truncate_apply, hmU]
  rw [hAm]
  have hsubk : Ioc V (N / m) ⊆ Icc 1 (N / m) := fun k hk ↦ by
    simp only [mem_Ioc, mem_Icc] at hk ⊢; omega
  rw [← sum_subset hsubk (fun k hk hk' ↦ by
    simp only [mem_Ioc, mem_Icc, not_and, not_le] at hk hk'
    have : k ≤ V := by by_contra h; exact absurd (hk' (by omega)) (by omega)
    rw [hB, one_sub_zeta_mul_trunc this]; simp)]
  rw [← mul_neg, ← sum_neg_distrib]
  congr 1
  refine sum_congr rfl fun k hk ↦ ?_
  have hkV : V < k := (mem_Ioc.1 hk).1
  rw [hB, one_sub_zeta_mul_trunc_of_lt hV hkV]
  push_cast; ring

end NTKB.Davenport
