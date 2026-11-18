/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Davenport.Ch1to6.CubicPeriods

/-!
# Kummer's cubic: the three periods are the roots (Davenport, Chapter 3, rows 3-15, 3-18, 3-20)

For a prime `q ≡ 1 (mod 3)`, a primitive root `g` and a cubic character `χ` with
`J(χ, χ) = A + Bω`, put `a = 2A - B`, `τ = τ(χ)`, `θ = arg τ` and `z_j = 1 + 3η_j`
(`kummerPeriod g j`). The library proved (in 0.5.0) `z_j = ω^{-j}τ + ω^jτ̄`, `4q = a² + 27b²` and that each
`z_j` is a root of `z³ - 3qz - qa`. Here:

* **3-20 (headline)**: `z³ - 3qz - qa = (z - z_0)(z - z_1)(z - z_2)` for every `z`
  (`kummerPeriod_cubic_eq_prod`), and in the canonical form with `a ≡ 1 (mod 3)`,
  `4q = a² + 27b²` (`exists_cubic_eq_prod_kummerPeriod`);
* **3-15**: the `z_j` are real (`kummerPeriod_im`), `z_j = 2√q cos(θ + 4πkj/3)` with `ω = e(k/3)`,
  `k ∈ {1, 2}` (`kummerPeriod_eq_cos`), they are distinct (`kummerPeriod_injective`), and exactly
  one lies in each of `(-2√q, -√q)`, `(-√q, √q)`, `(√q, 2√q)` (`existsUnique_kummerPeriod_mem`);
* **3-18**: `q = A² - AB + B²` with `3 ∣ B` (`natCast_eq_jacobi_norm`), and
  `cos 3θ = a/(2√q)` (`cos_three_mul_arg_gaussSum`).

Source text unavailable; written from the map rows 3-15, 3-18, 3-20 (the map
notes that the exact shifts of `θ` were read uncertainly, so the shifts here are the ones the
computation gives) and the statements of `CubicPeriods.lean`.
-/

open Finset Complex
open scoped Real ComplexConjugate

namespace NTKB.Davenport

variable {q : ℕ} [Fact q.Prime]

/-- Kummer's period `z_j = 1 + 3η_j`, `η_j` the Gaussian period of index class `j` mod `3`. -/
noncomputable def kummerPeriod (g : (ZMod q)ˣ) (j : ℕ) : ℂ :=
  1 + 3 * gaussianPeriod g 3 j (cexp (2 * π * I / q))

/-- The factorization `(z - (u + v))(z - (ω²u + ωv))(z - (ωu + ω²v)) = z³ - 3uvz - (u³ + v³)`
for a primitive cube root of unity `ω`. -/
theorem cubic_factor {ω u v z : ℂ} (h : ω ^ 2 + ω + 1 = 0) :
    (z - (u + v)) * (z - (ω ^ 2 * u + ω * v)) * (z - (ω * u + ω ^ 2 * v)) =
      z ^ 3 - 3 * (u * v) * z - (u ^ 3 + v ^ 3) := by
  have h2 : ω ^ 2 = -1 - ω := by linear_combination h
  rw [h2]
  linear_combination (-(z - u - v) * (u - v) ^ 2) * h

section

variable (hq : q % 3 = 1) {g : (ZMod q)ˣ} (hg : ∀ x, x ∈ Subgroup.zpowers g)
  {χ : MulChar (ZMod q) ℂ} (hχ : orderOf χ = 3)
include hq hg hχ

omit hq in
theorem cubic_gen_sum : χ g ^ 2 + χ g + 1 = 0 := by
  have h3 : χ g ^ 3 = 1 := cubic_gen_cube hχ g
  have hne : χ g ≠ 1 := cubic_gen_ne_one hg hχ
  have : (χ g - 1) * (χ g ^ 2 + χ g + 1) = 0 := by linear_combination h3
  exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hne)

/-- `z_0 = τ + τ̄`, `z_1 = ω²τ + ωτ̄`, `z_2 = ωτ + ω²τ̄`. -/
theorem kummerPeriod_zero :
    kummerPeriod g 0 = gaussSum χ ZMod.stdAddChar + conj (gaussSum χ ZMod.stdAddChar) := by
  rw [kummerPeriod, one_add_three_mul_gaussianPeriod hq hg hχ 0]; simp

theorem kummerPeriod_one :
    kummerPeriod g 1 = χ g ^ 2 * gaussSum χ ZMod.stdAddChar +
      χ g * conj (gaussSum χ ZMod.stdAddChar) := by
  rw [kummerPeriod, one_add_three_mul_gaussianPeriod hq hg hχ 1]; simp

theorem kummerPeriod_two :
    kummerPeriod g 2 = χ g * gaussSum χ ZMod.stdAddChar +
      χ g ^ 2 * conj (gaussSum χ ZMod.stdAddChar) := by
  rw [kummerPeriod, one_add_three_mul_gaussianPeriod hq hg hχ 2]
  have h3 : χ g ^ 3 = 1 := cubic_gen_cube hχ g
  rw [show 2 * 2 = 3 + 1 by rfl, pow_add, h3, one_mul, pow_one]

/-- **Davenport, Ch. 3, p. 25 (row 3-20)**: the three periods `z_0, z_1, z_2` are the roots of
`z³ - 3qz - qa`, `a = 2A - B` where `J(χ, χ) = A + Bω`:
`z³ - 3qz - qa = (z - z_0)(z - z_1)(z - z_2)` for every `z`. -/
@[kb "davenport1980" "Ch 3, p. 25"]
theorem kummerPeriod_cubic_eq_prod {A B : ℤ}
    (hJ : NTKB.IrelandRosen.multiJacobiSum ![χ, χ] = A + B * NTKB.IrelandRosen.omega3) (z : ℂ) :
    z ^ 3 - 3 * q * z - q * (2 * A - B) =
      (z - kummerPeriod g 0) * (z - kummerPeriod g 1) * (z - kummerPeriod g 2) := by
  rw [kummerPeriod_zero hq hg hχ, kummerPeriod_one hq hg hχ, kummerPeriod_two hq hg hχ,
    cubic_factor (cubic_gen_sum hg hχ)]
  have hψ := ZMod.isPrimitive_stdAddChar q
  have g1 := NTKB.IrelandRosen.gaussSum_cube hχ hψ
  rw [ZMod.card, hJ] at g1
  set τ := gaussSum χ (ZMod.stdAddChar : AddChar (ZMod q) ℂ)
  have g2 : conj τ ^ 3 = q * conj (A + B * NTKB.IrelandRosen.omega3 : ℂ) := by
    rw [← map_pow, g1, map_mul, map_natCast]
  have g3 : τ * conj τ = q := by
    rw [Complex.mul_conj, ← Complex.sq_norm, norm_gaussSum_cubic_sq hχ]
    simp
  have hsum : (A + B * NTKB.IrelandRosen.omega3 : ℂ) +
      conj (A + B * NTKB.IrelandRosen.omega3 : ℂ) = 2 * A - B := by
    rw [Complex.add_conj]
    have := NTKB.IrelandRosen.re_add_mul_omega3 A B
    exact_mod_cast this
  rw [g3, g1, g2, ← hsum]
  ring

omit hq hg in
theorem conj_cubic_gen : conj (χ g) = χ g ^ 2 := by
  have h3 : χ g ^ 3 = 1 := cubic_gen_cube hχ g
  have hn : ‖χ g‖ = 1 := by
    have : ‖χ g‖ ^ 3 = 1 := by rw [← norm_pow, h3, norm_one]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).mp this
  have hm : χ g * conj (χ g) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hn]; simp
  have h0 : χ g ≠ 0 := by rintro h; rw [h] at hn; simp at hn
  apply mul_left_cancel₀ h0
  rw [hm]; linear_combination -h3

/-- `z_j = w + w̄` with `w = ω^{2j}τ`. -/
theorem kummerPeriod_eq_add_conj (j : ℕ) :
    kummerPeriod g j = χ g ^ (2 * j) * gaussSum χ ZMod.stdAddChar +
      conj (χ g ^ (2 * j) * gaussSum χ ZMod.stdAddChar) := by
  rw [kummerPeriod, one_add_three_mul_gaussianPeriod hq hg hχ j, map_mul, map_pow,
    conj_cubic_gen hχ]
  have h3 : χ g ^ 3 = 1 := cubic_gen_cube hχ g
  congr 2
  rw [← pow_mul, show 2 * (2 * j) = j + 3 * j by ring, pow_add, pow_mul, h3, one_pow, mul_one]

/-- **Davenport, Ch. 3, p. 23 (row 3-15)**: the periods `z_j` are real. -/
@[kb "davenport1980" "Ch 3, p. 23"]
theorem kummerPeriod_im (j : ℕ) : (kummerPeriod g j).im = 0 := by
  rw [kummerPeriod_eq_add_conj hq hg hχ j, Complex.add_conj, Complex.ofReal_im]

theorem kummerPeriod_eq_re (j : ℕ) : kummerPeriod g j = ((kummerPeriod g j).re : ℂ) :=
  Complex.ext (by simp) (by simp [kummerPeriod_im hq hg hχ j])

omit hq hg in
theorem norm_gaussSum_cubic : ‖gaussSum χ (ZMod.stdAddChar : AddChar (ZMod q) ℂ)‖ = √q := by
  rw [← norm_gaussSum_cubic_sq hχ, Real.sqrt_sq (norm_nonneg _)]

/-- **Davenport, Ch. 3, p. 23 (row 3-15)**: with `θ = arg τ` and `ω = χ(g) = e(k/3)`,
`k ∈ {1, 2}`, `z_j = 2√q cos(θ + 4πkj/3)`; so `z_0 = 2√q cos θ` and `z_1, z_2` are
`2√q cos(θ ± 2π/3)` in an order fixed by `k`. -/
@[kb "davenport1980" "Ch 3, p. 23"]
theorem kummerPeriod_eq_cos :
    ∃ k ∈ ({1, 2} : Finset ℕ), χ g = cexp (2 * π * I * k / 3) ∧ ∀ j : ℕ,
      kummerPeriod g j = ((2 * √q * Real.cos (arg (gaussSum χ ZMod.stdAddChar) +
        4 * π * k * j / 3) : ℝ) : ℂ) := by
  have h3 : χ g ^ 3 = 1 := cubic_gen_cube hχ g
  obtain ⟨k, hk3, hk⟩ := NTKB.IrelandRosen.omega3_isPrimitiveRoot.eq_pow_of_pow_eq_one h3
  have hk0 : k ≠ 0 := by
    rintro rfl; exact cubic_gen_ne_one hg hχ (by rw [← hk, pow_zero])
  have hω : χ g = cexp (2 * π * I * k / 3) := by
    rw [← hk, NTKB.IrelandRosen.omega3, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
  refine ⟨k, by simp; omega, hω, fun j ↦ ?_⟩
  rw [kummerPeriod_eq_add_conj hq hg hχ j, Complex.add_conj]
  congr 1
  set τ := gaussSum χ (ZMod.stdAddChar : AddChar (ZMod q) ℂ)
  set θ := arg τ with hθ
  have hτ : τ = (√q : ℂ) * cexp (θ * I) := by
    rw [← norm_gaussSum_cubic hχ, hθ]; exact (Complex.norm_mul_exp_arg_mul_I τ).symm
  have : χ g ^ (2 * j) * τ =
      (√q : ℂ) * cexp (((θ + 4 * π * k * j / 3 : ℝ) : ℂ) * I) := by
    rw [hτ, hω, ← Complex.exp_nat_mul, mul_left_comm, ← Complex.exp_add]
    congr 2; push_cast; ring
  rw [this, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  ring

omit hg in
/-- **Davenport, Ch. 3, p. 24 (row 3-18)**: if `J(χ, χ) = A + Bω` then `q = A² - AB + B²` and
`3 ∣ B`. -/
@[kb "davenport1980" "Ch 3, p. 24"]
theorem natCast_eq_jacobi_norm {A B : ℤ}
    (hJ : NTKB.IrelandRosen.multiJacobiSum ![χ, χ] = A + B * NTKB.IrelandRosen.omega3) :
    (q : ℤ) = A ^ 2 - A * B + B ^ 2 ∧ 3 ∣ B := by
  have h3 : 3 ∣ Fintype.card (ZMod q) - 1 := by rw [ZMod.card]; omega
  obtain ⟨a, b, hJ', hq', hb, -⟩ := NTKB.IrelandRosen.cubic_jacobiSum_eq h3 hχ
  rw [hJ] at hJ'
  obtain ⟨rfl, rfl⟩ := NTKB.IrelandRosen.add_mul_omega3_inj hJ'
  rw [ZMod.card] at hq'
  exact ⟨hq', hb⟩

omit hq hg in
/-- **Davenport, Ch. 3, p. 24 (row 3-18)**: `cos 3θ = a/(2√q)`, `θ = arg τ`, `a = 2A - B`. -/
@[kb "davenport1980" "Ch 3, p. 24"]
theorem cos_three_mul_arg_gaussSum {A B : ℤ}
    (hJ : NTKB.IrelandRosen.multiJacobiSum ![χ, χ] = A + B * NTKB.IrelandRosen.omega3) :
    Real.cos (3 * arg (gaussSum χ ZMod.stdAddChar)) = (2 * A - B) / (2 * √q) := by
  have hψ := ZMod.isPrimitive_stdAddChar q
  have g1 := NTKB.IrelandRosen.gaussSum_cube hχ hψ
  rw [ZMod.card, hJ] at g1
  set τ := gaussSum χ (ZMod.stdAddChar : AddChar (ZMod q) ℂ)
  set θ := arg τ with hθ
  have hτ : τ = (√q : ℂ) * cexp (θ * I) := by
    rw [← norm_gaussSum_cubic hχ, hθ]; exact (Complex.norm_mul_exp_arg_mul_I τ).symm
  have hc : τ ^ 3 = ((√q ^ 3 : ℝ) : ℂ) * cexp (((3 * θ : ℝ) : ℂ) * I) := by
    rw [hτ, mul_pow, ← Complex.exp_nat_mul]; push_cast; ring_nf
  have hre := congrArg Complex.re (hc.symm.trans g1)
  rw [Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re] at hre
  have hJre : ((q : ℂ) * (A + B * NTKB.IrelandRosen.omega3)).re = q * ((2 * A - B) / 2) := by
    have := NTKB.IrelandRosen.re_add_mul_omega3 A B
    have e : ((q : ℂ) * (A + B * NTKB.IrelandRosen.omega3)).re =
        q * ((A : ℂ) + B * NTKB.IrelandRosen.omega3).re := by simp [Complex.mul_re]
    rw [e]; congr 1; linarith
  rw [hJre] at hre
  have hq0 : (0 : ℝ) < √q := Real.sqrt_pos.mpr (by exact_mod_cast (Fact.out : q.Prime).pos)
  have hsq : √q ^ 2 = q := Real.sq_sqrt (Nat.cast_nonneg q)
  have hq1 : (0 : ℝ) < q := by exact_mod_cast (Fact.out : q.Prime).pos
  have e : √q ^ 3 = q * √q := by rw [pow_succ, hsq]
  rw [e, mul_assoc] at hre
  have h2 : √q * Real.cos (3 * θ) = (2 * A - B) / 2 :=
    mul_left_cancel₀ hq1.ne' hre
  rw [eq_div_iff (by positivity)]
  linarith

omit hg in
/-- `a² < 4q`: in `4q = a² + 27b²` the term `b` is not `0` (`q` is not a square). -/
theorem sq_lt_four_mul {A B : ℤ}
    (hJ : NTKB.IrelandRosen.multiJacobiSum ![χ, χ] = A + B * NTKB.IrelandRosen.omega3) :
    (2 * A - B) ^ 2 < 4 * (q : ℤ) := by
  obtain ⟨b, -, h4⟩ := four_mul_eq_sq_add hq hχ hJ
  rcases eq_or_ne b 0 with rfl | hb
  · exfalso
    have hp : (q : ℕ).Prime := Fact.out
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
      add_zero] at h4
    -- `4q = a²` forces `a = 2c` and `q = c²`
    have h2 : (2 : ℤ) ∣ 2 * A - B := by
      have : (2 : ℤ) ∣ (2 * A - B) ^ 2 := ⟨2 * q, by linarith⟩
      exact Int.Prime.dvd_pow' Nat.prime_two this
    obtain ⟨c, hc⟩ := h2
    rw [hc] at h4
    have hqc0 : (q : ℤ) = c * c := by linarith [h4, show (2 * c) ^ 2 = 4 * (c * c) by ring]
    have hqc : (q : ℤ) = c.natAbs * c.natAbs := by rw [Int.natAbs_mul_self']; exact hqc0
    have hqc' : q = c.natAbs * c.natAbs := by exact_mod_cast hqc
    rw [hqc'] at hp
    rcases Nat.prime_mul_iff.mp hp with ⟨h, h1⟩ | ⟨h, h1⟩ <;> rw [h1] at h <;>
      exact Nat.not_prime_one h
  · have : 0 < 27 * b ^ 2 := by positivity
    linarith

/-- The real form of the factorization: with `x_j = Re z_j`,
`x³ - 3qx - qa = (x - x_0)(x - x_1)(x - x_2)` for real `x`. -/
theorem kummerPeriod_re_cubic {A B : ℤ}
    (hJ : NTKB.IrelandRosen.multiJacobiSum ![χ, χ] = A + B * NTKB.IrelandRosen.omega3) (x : ℝ) :
    x ^ 3 - 3 * q * x - q * (2 * A - B) = (x - (kummerPeriod g 0).re) *
      (x - (kummerPeriod g 1).re) * (x - (kummerPeriod g 2).re) := by
  have h := kummerPeriod_cubic_eq_prod hq hg hχ hJ x
  rw [kummerPeriod_eq_re hq hg hχ 0, kummerPeriod_eq_re hq hg hχ 1,
    kummerPeriod_eq_re hq hg hχ 2] at h
  exact_mod_cast h

/-- One period in each of `(-2√q, -√q)`, `(-√q, √q)`, `(√q, 2√q)`, and every period is one of
these three. -/
theorem kummerPeriod_hits {A B : ℤ}
    (hJ : NTKB.IrelandRosen.multiJacobiSum ![χ, χ] = A + B * NTKB.IrelandRosen.omega3) :
    ∃ j₁ j₂ j₃ : Fin 3, (kummerPeriod g j₁).re ∈ Set.Ioo (-2 * √q) (-√q) ∧
      (kummerPeriod g j₂).re ∈ Set.Ioo (-√q) (√q) ∧
      (kummerPeriod g j₃).re ∈ Set.Ioo (√q) (2 * √q) ∧ ∀ j : Fin 3, j = j₁ ∨ j = j₂ ∨ j = j₃ := by
  set a : ℝ := 2 * A - B with ha_def
  set r : ℝ := √q with hr_def
  have hr : 0 < r := Real.sqrt_pos.mpr (by exact_mod_cast (Fact.out : q.Prime).pos)
  have hr2 : r ^ 2 = q := Real.sq_sqrt (Nat.cast_nonneg q)
  have hsq : a ^ 2 < (2 * r) ^ 2 := by
    have h := sq_lt_four_mul hq hχ hJ
    have h' : ((2 * A - B : ℤ) : ℝ) ^ 2 < 4 * (q : ℝ) := by exact_mod_cast h
    rw [mul_pow, hr2]; push_cast at h'; linarith
  have ha := abs_lt.mp (abs_lt_of_sq_lt_sq hsq (by positivity))
  set f : ℝ → ℝ := fun x ↦ x ^ 3 - 3 * q * x - q * a with hf_def
  have hfc : Continuous f := by rw [hf_def]; fun_prop
  have hroot : ∀ y, f y = 0 → ∃ j : Fin 3, (kummerPeriod g j).re = y := by
    intro y hy
    have h := kummerPeriod_re_cubic hq hg hχ hJ y
    simp only [hf_def] at hy
    rw [← ha_def, hy] at h
    rcases mul_eq_zero.mp h.symm with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact ⟨0, by simp; linarith⟩
      · exact ⟨1, by simp; linarith⟩
    · exact ⟨2, by simp; linarith⟩
  have f1 : f (-2 * r) < 0 := by
    simp only [hf_def]; rw [← hr2]; nlinarith [mul_pos (pow_pos hr 2) (by linarith : 0 < 2 * r + a)]
  have f2 : 0 < f (-r) := by
    simp only [hf_def]; rw [← hr2]; nlinarith [mul_pos (pow_pos hr 2) (by linarith : 0 < 2 * r - a)]
  have f3 : f r < 0 := by
    simp only [hf_def]; rw [← hr2]; nlinarith [mul_pos (pow_pos hr 2) (by linarith : 0 < 2 * r + a)]
  have f4 : 0 < f (2 * r) := by
    simp only [hf_def]; rw [← hr2]; nlinarith [mul_pos (pow_pos hr 2) (by linarith : 0 < 2 * r - a)]
  obtain ⟨y₁, hy₁, e₁⟩ := intermediate_value_Ioo (by linarith) hfc.continuousOn ⟨f1, f2⟩
  obtain ⟨y₂, hy₂, e₂⟩ := intermediate_value_Ioo' (by linarith) hfc.continuousOn ⟨f3, f2⟩
  obtain ⟨y₃, hy₃, e₃⟩ := intermediate_value_Ioo (by linarith) hfc.continuousOn ⟨f3, f4⟩
  obtain ⟨j₁, rfl⟩ := hroot y₁ e₁
  obtain ⟨j₂, rfl⟩ := hroot y₂ e₂
  obtain ⟨j₃, rfl⟩ := hroot y₃ e₃
  refine ⟨j₁, j₂, j₃, hy₁, hy₂, hy₃, fun j ↦ ?_⟩
  have d12 : j₁ ≠ j₂ := by rintro rfl; exact absurd hy₁.2 (not_lt.mpr hy₂.1.le)
  have d13 : j₁ ≠ j₃ := by rintro rfl; linarith [hy₁.2, hy₃.1]
  have d23 : j₂ ≠ j₃ := by rintro rfl; exact absurd hy₂.2 (not_lt.mpr hy₃.1.le)
  rw [Ne, Fin.ext_iff] at d12 d13 d23
  simp only [Fin.ext_iff]
  omega

/-- **Davenport, Ch. 3, p. 23 (row 3-15)**: exactly one of the periods lies in each of the
intervals `(-2√q, -√q)`, `(-√q, √q)`, `(√q, 2√q)`. -/
@[kb "davenport1980" "Ch 3, p. 23"]
theorem existsUnique_kummerPeriod_mem {A B : ℤ}
    (hJ : NTKB.IrelandRosen.multiJacobiSum ![χ, χ] = A + B * NTKB.IrelandRosen.omega3)
    (I : Set ℝ) (hI : I = Set.Ioo (-2 * √q) (-√q) ∨ I = Set.Ioo (-√q) (√q) ∨
      I = Set.Ioo (√q) (2 * √q)) :
    ∃! j : Fin 3, (kummerPeriod g j).re ∈ I := by
  obtain ⟨j₁, j₂, j₃, h₁, h₂, h₃, hall⟩ := kummerPeriod_hits hq hg hχ hJ
  rcases hI with rfl | rfl | rfl
  · refine ⟨j₁, h₁, fun j hj ↦ ?_⟩
    rcases hall j with rfl | rfl | rfl
    · rfl
    · exact absurd hj.2 (not_lt.mpr h₂.1.le)
    · exfalso; linarith [hj.2, h₃.1, Real.sqrt_nonneg (q : ℝ)]
  · refine ⟨j₂, h₂, fun j hj ↦ ?_⟩
    rcases hall j with rfl | rfl | rfl
    · exact absurd h₁.2 (not_lt.mpr hj.1.le)
    · rfl
    · exact absurd hj.2 (not_lt.mpr h₃.1.le)
  · refine ⟨j₃, h₃, fun j hj ↦ ?_⟩
    rcases hall j with rfl | rfl | rfl
    · exfalso; linarith [hj.1, h₁.2, Real.sqrt_nonneg (q : ℝ)]
    · exact absurd h₂.2 (not_lt.mpr hj.1.le)
    · rfl

/-- **Davenport, Ch. 3, p. 23 (row 3-15)**: the three periods are distinct. -/
@[kb "davenport1980" "Ch 3, p. 23"]
theorem kummerPeriod_injective {A B : ℤ}
    (hJ : NTKB.IrelandRosen.multiJacobiSum ![χ, χ] = A + B * NTKB.IrelandRosen.omega3) :
    Function.Injective (fun j : Fin 3 ↦ kummerPeriod g j) := by
  intro i j hij
  have hre : (kummerPeriod g i).re = (kummerPeriod g j).re := congrArg Complex.re hij
  obtain ⟨j₁, j₂, j₃, h₁, h₂, h₃, hall⟩ := kummerPeriod_hits hq hg hχ hJ
  have s12 : (kummerPeriod g j₁).re < (kummerPeriod g j₂).re := by linarith [h₁.2, h₂.1]
  have s23 : (kummerPeriod g j₂).re < (kummerPeriod g j₃).re := by linarith [h₂.2, h₃.1]
  rcases hall i with rfl | rfl | rfl <;> rcases hall j with rfl | rfl | rfl <;>
    first | rfl | (exfalso; linarith)

end

/-- **Davenport, Ch. 3, p. 25 (row 3-20), canonical form**: for a prime `q ≡ 1 (mod 3)` and a
primitive root `g`, there are integers `a ≡ 1 (mod 3)` and `b` with `4q = a² + 27b²` such that the
three periods `z_0, z_1, z_2` are the roots of `z³ - 3qz - qa`. -/
@[kb "davenport1980" "Ch 3, p. 25"]
theorem exists_cubic_eq_prod_kummerPeriod (hq : q % 3 = 1) {g : (ZMod q)ˣ}
    (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    ∃ a b : ℤ, 4 * (q : ℤ) = a ^ 2 + 27 * b ^ 2 ∧ a ≡ 1 [ZMOD 3] ∧ ∀ z : ℂ,
      z ^ 3 - 3 * q * z - q * a =
        (z - kummerPeriod g 0) * (z - kummerPeriod g 1) * (z - kummerPeriod g 2) := by
  have h3 : 3 ∣ Fintype.card (ZMod q) - 1 := by rw [ZMod.card]; omega
  obtain ⟨χ, hχ⟩ := NTKB.IrelandRosen.exists_orderOf_eq h3
  obtain ⟨A, B, hJ, -⟩ := NTKB.IrelandRosen.cubic_jacobiSum_eq h3 hχ
  obtain ⟨b, -, h4⟩ := four_mul_eq_sq_add hq hχ hJ
  refine ⟨2 * A - B, b, h4, two_mul_sub_modEq_one hq hχ hJ, fun z ↦ ?_⟩
  rw [← kummerPeriod_cubic_eq_prod hq hg hχ hJ z]
  push_cast; ring

end NTKB.Davenport
