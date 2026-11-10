/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.RingTheory.RootsOfUnity.Complex
import NTKB.Analytic.Davenport.Ch1to6.Periods

/-!
# Davenport, Chapter 3: cyclotomy

`q` is an odd prime and `ζ` a primitive `q`-th root of unity in `ℂ`.

* (§3, p. 17) Every integral polynomial in `ζ` can be written as `∑_{r=1}^{q-1} a_r ζ^r` with
  integers `a_r`, and uniquely so, since the cyclotomic polynomial is irreducible
  (`NTKB.Davenport.exists_aeval_eq_sum_units`, `NTKB.Davenport.eq_of_sum_units_eq`).
* (§3, pp. 18–19) If an integral polynomial `F` satisfies `F(ζ^m) = F(ζ)` whenever
  `ν(m) ≡ 0 (mod e)`, then `F(ζ)` is an integral linear combination of the Gaussian periods
  `η_0, …, η_{e-1}` (`NTKB.Davenport.aeval_eq_sum_gaussianPeriod`; the constant term `a_0` is
  allowed, the book takes `a_0 = 0`).
-/

noncomputable section

open Finset Complex Polynomial

namespace NTKB.Davenport

variable {q : ℕ} [Fact q.Prime]

omit [Fact q.Prime] in
/-- `z^q = 1` gives `z^{n mod q} = z^n`. -/
theorem pow_mod_of_pow_eq_one {R : Type*} [Monoid R] {z : R} (hz : z ^ q = 1) (n : ℕ) :
    z ^ (n % q) = z ^ n := by
  conv_rhs => rw [← Nat.mod_add_div n q, pow_add, pow_mul, hz, one_pow, mul_one]

/-- `(z^a)^b = z^{(a b) mod q}`, i.e. `(z^{m})^{x} = z^{m x}` for residues `m, x` modulo `q`. -/
theorem pow_val_pow_val {R : Type*} [CommMonoid R] {z : R} (hz : z ^ q = 1) (m x : ZMod q) :
    (z ^ m.val) ^ x.val = z ^ (m * x).val := by
  rw [← pow_mul, ZMod.val_mul, pow_mod_of_pow_eq_one hz]

/-! ### Uniqueness of the representation (§3, p. 17) -/

/-- **Davenport §3, p. 17 (uniqueness).** The only integral relation `∑_{x mod q} c_x ζ^x = 0`
among the `q`-th roots of unity is `1 + ζ + ⋯ + ζ^{q-1} = 0`: all `c_x` are equal. (The
cyclotomic polynomial is irreducible, so `ζ` satisfies no equation of degree `< q - 1`.) -/
@[kb "davenport1980" "Ch 3, p. 17"]
theorem eq_of_sum_mul_pow_eq_zero {ζ : ℂ} (hζ : IsPrimitiveRoot ζ q) (c : ZMod q → ℤ)
    (h : ∑ x : ZMod q, (c x : ℂ) * ζ ^ x.val = 0) (x : ZMod q) : c x = c 0 := by
  have hq := (Fact.out : q.Prime)
  set d : ℕ → ℚ := fun s ↦ ((c (s : ZMod q) - c 0 : ℤ) : ℚ) with hd
  -- `∑_{s < q} d_s ζ^s = 0`
  have h1 : ∑ s ∈ range q, (d s : ℂ) * ζ ^ s = 0 := by
    have hgeom := hζ.geom_sum_eq_zero hq.one_lt
    have : ∑ s ∈ range q, (d s : ℂ) * ζ ^ s =
        ∑ s ∈ range q, (c (s : ZMod q) : ℂ) * ζ ^ s - (c 0 : ℂ) * ∑ s ∈ range q, ζ ^ s := by
      rw [mul_sum, ← sum_sub_distrib]
      refine sum_congr rfl fun s _ ↦ ?_
      simp only [hd]; push_cast; ring
    rw [this, hgeom, mul_zero, sub_zero, ← h,
      ← sum_val_eq_sum_range (fun s ↦ (c (s : ZMod q) : ℂ) * ζ ^ s)]
    simp only [ZMod.natCast_zmod_val]
  -- drop the term `s = 0` and divide by `ζ`
  have hd0 : d 0 = 0 := by simp [hd]
  have h2 : ∑ s ∈ range (q - 1), (d (s + 1) : ℂ) * ζ ^ s = 0 := by
    have hq1 : q = q - 1 + 1 := by have := hq.two_le; omega
    rw [hq1, sum_range_succ'] at h1
    simp only [hd0, Rat.cast_zero, zero_mul, add_zero, pow_succ] at h1
    have hζ0 : ζ ≠ 0 := hζ.ne_zero hq.ne_zero
    have : (∑ s ∈ range (q - 1), (d (s + 1) : ℂ) * ζ ^ s) * ζ = 0 := by
      rw [sum_mul, ← h1]; refine sum_congr rfl fun s _ ↦ by ring
    exact (mul_eq_zero.mp this).resolve_right hζ0
  -- the polynomial `P = ∑_{s < q-1} d_{s+1} X^s` vanishes at `ζ` and has degree `< q - 1`
  set P : ℚ[X] := ∑ s ∈ range (q - 1), C (d (s + 1)) * X ^ s with hP
  have hPζ : aeval ζ P = 0 := by
    rw [hP, map_sum, ← h2]
    refine sum_congr rfl fun s _ ↦ ?_
    rw [map_mul, aeval_C, map_pow, aeval_X, eq_ratCast]
  have hP0 : P = 0 := by
    by_contra hne
    have hdvd := minpoly.dvd ℚ ζ hPζ
    rw [← cyclotomic_eq_minpoly_rat hζ hq.pos] at hdvd
    have hle := Polynomial.natDegree_le_of_dvd hdvd hne
    rw [natDegree_cyclotomic, Nat.totient_prime hq] at hle
    have hlt : P.natDegree ≤ q - 2 := by
      rw [hP]
      refine natDegree_sum_le_of_forall_le _ _ fun s hs ↦ ?_
      have := mem_range.mp hs
      exact (natDegree_C_mul_X_pow_le _ _).trans (by omega)
    have := hq.two_le
    omega
  -- hence all `d_{s+1} = 0`
  have hcoeff : ∀ s < q - 1, d (s + 1) = 0 := by
    intro s hs
    have := congrArg (fun p : ℚ[X] ↦ p.coeff s) hP0
    simp only [hP, finsetSum_coeff, coeff_C_mul_X_pow, coeff_zero] at this
    rw [sum_ite_eq, if_pos (mem_range.mpr hs)] at this
    exact this
  by_cases hx : x = 0
  · rw [hx]
  · have hv : x.val ≠ 0 := (ZMod.val_ne_zero x).mpr hx
    have hlt : x.val - 1 < q - 1 := by have := ZMod.val_lt x; omega
    have := hcoeff _ hlt
    rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hv)] at this
    simp only [hd, ZMod.natCast_zmod_val, Int.cast_eq_zero, sub_eq_zero] at this
    exact this

/-- **Davenport §3, p. 17 (uniqueness).** If `∑_{r=1}^{q-1} a_r ζ^r = ∑_{r=1}^{q-1} b_r ζ^r`
with integers `a_r, b_r` (indexed by the units `r` modulo `q`), then `a = b`. -/
@[kb "davenport1980" "Ch 3, p. 17"]
theorem eq_of_sum_units_eq {ζ : ℂ} (hζ : IsPrimitiveRoot ζ q) (a b : (ZMod q)ˣ → ℤ)
    (h : ∑ u : (ZMod q)ˣ, (a u : ℂ) * ζ ^ (u : ZMod q).val =
      ∑ u : (ZMod q)ˣ, (b u : ℂ) * ζ ^ (u : ZMod q).val) : a = b := by
  classical
  set c : ZMod q → ℤ := fun x ↦ if hx : x = 0 then 0 else a (Units.mk0 x hx) - b (Units.mk0 x hx)
    with hc
  have hsum : ∑ x : ZMod q, (c x : ℂ) * ζ ^ x.val = 0 := by
    rw [sum_zmod_eq_add_sum_units]
    simp only [hc, dif_pos, Int.cast_zero, zero_mul, zero_add]
    rw [← sub_eq_zero.mpr h, ← sum_sub_distrib]
    refine sum_congr rfl fun u _ ↦ ?_
    rw [dif_neg u.ne_zero]
    simp only [Units.mk0_val]
    push_cast; ring
  funext u
  have := eq_of_sum_mul_pow_eq_zero hζ c hsum u
  simp only [hc, dif_neg u.ne_zero, dif_pos, Units.mk0_val, sub_eq_zero] at this
  exact this

/-! ### Reduction of an integral polynomial modulo `X^q - 1` -/

/-- The sum of the coefficients of `P` at the exponents `i ≡ x (mod q)`. -/
def rho (x : ZMod q) (P : ℤ[X]) : ℤ :=
  ∑ i ∈ P.support.filter (fun i : ℕ ↦ (i : ZMod q) = x), P.coeff i

/-- `P(z) = ∑_{x mod q} ρ_x(P) z^x` when `z^q = 1`. -/
theorem aeval_eq_sum_rho {z : ℂ} (hz : z ^ q = 1) (P : ℤ[X]) :
    aeval z P = ∑ x : ZMod q, (rho x P : ℂ) * z ^ x.val := by
  rw [aeval_def, eval₂_eq_sum, Polynomial.sum_def,
    ← sum_fiberwise_of_maps_to (g := fun i : ℕ ↦ (i : ZMod q)) (t := univ)
      (fun _ _ ↦ mem_univ _)]
  refine sum_congr rfl fun x _ ↦ ?_
  rw [rho, Int.cast_sum, sum_mul]
  refine sum_congr rfl fun i hi ↦ ?_
  rw [(mem_filter.mp hi).2.symm, ZMod.val_natCast, pow_mod_of_pow_eq_one hz, eq_intCast]

/-- **Davenport §3, p. 17 (existence).** Every integral polynomial in `ζ` is
`∑_{r=1}^{q-1} a_r ζ^r` with integers `a_r` (using `1 = -(ζ + ⋯ + ζ^{q-1})`). -/
@[kb "davenport1980" "Ch 3, p. 17"]
theorem exists_aeval_eq_sum_units {ζ : ℂ} (hζ : IsPrimitiveRoot ζ q) (P : ℤ[X]) :
    ∃ a : (ZMod q)ˣ → ℤ, aeval ζ P = ∑ u : (ZMod q)ˣ, (a u : ℂ) * ζ ^ (u : ZMod q).val := by
  refine ⟨fun u ↦ rho (u : ZMod q) P - rho (0 : ZMod q) P, ?_⟩
  rw [aeval_eq_sum_rho (hζ.pow_eq_one) P, sum_zmod_eq_add_sum_units, ZMod.val_zero, pow_zero,
    mul_one]
  have hsum := sum_units_pow_val hζ
  simp only [Int.cast_sub, sub_mul, sum_sub_distrib, ← mul_sum, hsum]
  ring

/-- If `∑_x c_x ζ^{m x} = ∑_x c_x ζ^x` for a unit `m`, then `c_{m x} = c_x` for all `x`. -/
theorem eq_of_sum_mul_pow_mul_eq {ζ : ℂ} (hζ : IsPrimitiveRoot ζ q) (c : ZMod q → ℤ)
    (m : (ZMod q)ˣ)
    (h : ∑ x : ZMod q, (c x : ℂ) * ζ ^ ((m : ZMod q) * x).val =
      ∑ x : ZMod q, (c x : ℂ) * ζ ^ x.val) (x : ZMod q) : c (m * x) = c x := by
  -- reindex the left side by `y = m x`
  have hre : ∑ x : ZMod q, (c x : ℂ) * ζ ^ ((m : ZMod q) * x).val =
      ∑ y : ZMod q, (c ((m⁻¹ : (ZMod q)ˣ) * y) : ℂ) * ζ ^ y.val := by
    refine Fintype.sum_equiv (Units.mulLeft m) _ _ fun x ↦ ?_
    rw [Units.mulLeft_apply, ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
  rw [hre] at h
  have h0 : ∑ y : ZMod q, ((c ((m⁻¹ : (ZMod q)ˣ) * y) - c y : ℤ) : ℂ) * ζ ^ y.val = 0 := by
    simp only [Int.cast_sub, sub_mul, sum_sub_distrib, h, sub_self]
  have := eq_of_sum_mul_pow_eq_zero hζ _ h0 (m * x)
  simp only [mul_zero, sub_self, sub_eq_zero] at this
  rw [← this, ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]

/-! ### Invariant polynomials are combinations of the periods (§3, pp. 18–19) -/

/-- **Davenport §3, pp. 18–19.** Let `q - 1 = e f`. If an integral polynomial `F` satisfies
`F(ζ^m) = F(ζ)` whenever `ν(m) ≡ 0 (mod e)`, then the reduced coefficients `A_r` of `F`
(`F(z) = ∑_{r mod q} A_r z^r` for `z^q = 1`) depend only on the class of `ν(r)` modulo `e`, and
`F(z) = A_0 + A_{g^0} η_0(z) + ⋯ + A_{g^{e-1}} η_{e-1}(z)` for every `z` with `z^q = 1`
(in particular for `z = ζ`). -/
@[kb "davenport1980" "Ch 3, pp. 18-19"]
theorem aeval_eq_sum_gaussianPeriod {g : (ZMod q)ˣ} (hg : ∀ x, x ∈ Subgroup.zpowers g) {e f : ℕ}
    (hef : q - 1 = e * f) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ q) (P : ℤ[X])
    (hP : ∀ m : (ZMod q)ˣ, index g m ≡ 0 [MOD e] → aeval (ζ ^ (m : ZMod q).val) P = aeval ζ P)
    {z : ℂ} (hz : z ^ q = 1) :
    aeval z P = rho (0 : ZMod q) P + ∑ j ∈ range e, (rho ((g ^ j : (ZMod q)ˣ) : ZMod q) P : ℂ) *
      gaussianPeriod g e j z := by
  have he : 0 < e := by
    rcases Nat.eq_zero_or_pos e with h | h
    · have := one_le_card_sub_one (q := q); rw [hef, h, zero_mul] at this; omega
    · exact h
  have hζq : ζ ^ q = 1 := hζ.pow_eq_one
  -- invariance of the reduced coefficients
  have hinv : ∀ m : (ZMod q)ˣ, index g m ≡ 0 [MOD e] →
      ∀ x : ZMod q, rho ((m : ZMod q) * x) P = rho x P := by
    intro m hm
    refine eq_of_sum_mul_pow_mul_eq hζ (fun x ↦ rho x P) m ?_
    have h := hP m hm
    rw [aeval_eq_sum_rho (by rw [← pow_mul, mul_comm, pow_mul, hζq, one_pow]) P,
      aeval_eq_sum_rho hζq P] at h
    rw [← h]
    refine sum_congr rfl fun x _ ↦ ?_
    rw [pow_val_pow_val hζq]
  -- the coefficient at a unit `u` is the coefficient at `g^(ν(u) mod e)`
  have hclass : ∀ u : (ZMod q)ˣ,
      rho (u : ZMod q) P = rho ((g ^ (index g u % e) : (ZMod q)ˣ) : ZMod q) P := by
    intro u
    have hdvd : e ∣ q - 1 := ⟨f, hef⟩
    set m : (ZMod q)ˣ := g ^ (e * (index g u / e))
    have hm : index g m ≡ 0 [MOD e] := by
      rw [index_pow hg, Nat.ModEq, Nat.mod_mod_of_dvd _ hdvd, Nat.mul_mod_right, Nat.zero_mod]
    have hu : (u : ZMod q) = (m : ZMod q) * ((g ^ (index g u % e) : (ZMod q)ˣ) : ZMod q) := by
      rw [← Units.val_mul, ← pow_add, add_comm, Nat.mod_add_div, pow_index hg]
    rw [hu, hinv m hm]
  rw [aeval_eq_sum_rho hz P, sum_zmod_eq_add_sum_units, ZMod.val_zero, pow_zero, mul_one]
  congr 1
  rw [← sum_fiberwise_of_maps_to (g := fun n : (ZMod q)ˣ ↦ index g n % e) (t := range e)
    (fun n _ ↦ mem_range.mpr (Nat.mod_lt _ he))]
  refine sum_congr rfl fun j hj ↦ ?_
  rw [gaussianPeriod, mul_sum]
  refine sum_congr (filter_congr fun n _ ↦ ?_) fun n hn ↦ ?_
  · rw [Nat.ModEq, Nat.mod_eq_of_lt (mem_range.mp hj)]
  · rw [hclass n, (mem_filter.mp hn).2, Nat.mod_eq_of_lt (mem_range.mp hj)]

end NTKB.Davenport
