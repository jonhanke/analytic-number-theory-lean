/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Davenport.Ch1to6.Cyclotomy

/-!
# Davenport, Chapters 1 and 3: Gauss's factorization of the cyclotomic polynomial

For an odd prime `q`, `ζ = e(1/q)`, `R` the quadratic residues and `N` the nonresidues in
`1, …, q - 1`, and `ε √q = G` Gauss's sum (`√q` or `i √q` according as `q ≡ 1` or `3 (mod 4)`),
there are integral polynomials `Y, Z` with
$$2\prod_R (x-\zeta^R) = Y(x) - \varepsilon\sqrt q\,Z(x),\qquad
  2\prod_N (x-\zeta^N) = Y(x) + \varepsilon\sqrt q\,Z(x),$$
hence `Y² - q* Z² = 4(x^{q-1} + ⋯ + 1)` with `q* = ±q` (§3, p. 19; quoted in §1, p. 10).
For `q ≡ 1 (mod 4)`, `x = 1` gives integers with `Y² - q Z² = 4q`, `Z ≠ 0` and `q ∣ Y` (§1, p. 10).

The proof is the book's: the coefficients of `∏_R (x - ζ^R)` are invariant under `ζ ↦ ζ^m` for
residues `m`, hence integral combinations of `1, η_0, η_1` (`aeval_eq_sum_gaussianPeriod`), and
`η_0, η_1 = (-1 ± G)/2`; replacing `ζ` by `ζ^N` exchanges `η_0` and `η_1`.
-/

noncomputable section

open Finset Complex Polynomial
open scoped Real

namespace NTKB.Davenport

variable {q : ℕ} [Fact q.Prime]

/-- The quadratic residues among the units modulo `q`. -/
def residues (q : ℕ) [Fact q.Prime] : Finset (ZMod q)ˣ :=
  univ.filter (fun r : (ZMod q)ˣ ↦ quadraticChar (ZMod q) r = 1)

/-- The quadratic nonresidues among the units modulo `q`. -/
def nonresidues (q : ℕ) [Fact q.Prime] : Finset (ZMod q)ˣ :=
  univ.filter (fun r : (ZMod q)ˣ ↦ quadraticChar (ZMod q) r = -1)

/-- The generic product `∏_R (Y - X^R)` in `ℤ[X][Y]`. -/
def residueProduct (q : ℕ) [Fact q.Prime] : (ℤ[X])[X] :=
  ∏ r ∈ residues q, (X - C ((X : ℤ[X]) ^ (r : ZMod q).val))

theorem map_residueProduct (z : ℂ) :
    (residueProduct q).map (aeval z : ℤ[X] →ₐ[ℤ] ℂ).toRingHom =
      ∏ r ∈ residues q, (X - C (z ^ (r : ZMod q).val)) := by
  simp [residueProduct, Polynomial.map_prod]

theorem quadraticChar_unit_eq (u : (ZMod q)ˣ) :
    quadraticChar (ZMod q) u = 1 ∨ quadraticChar (ZMod q) u = -1 :=
  quadraticChar_dichotomy u.ne_zero

/-- Replacing `ζ` by `ζ^m` permutes the factors: for `χ(m) = 1` the residues go to the residues,
for `χ(m) = -1` to the nonresidues. -/
theorem prod_residues_pow {z : ℂ} (hz : z ^ q = 1) (m : (ZMod q)ˣ) (s : ℤ)
    (hm : quadraticChar (ZMod q) m = s) :
    ∏ r ∈ residues q, (X - C ((z ^ (m : ZMod q).val) ^ (r : ZMod q).val)) =
      ∏ r ∈ univ.filter (fun r : (ZMod q)ˣ ↦ quadraticChar (ZMod q) r = s),
        (X - C (z ^ (r : ZMod q).val)) := by
  refine Finset.prod_nbij' (fun r ↦ m * r) (fun r ↦ m⁻¹ * r) ?_ ?_ ?_ ?_ ?_
  · intro r hr
    simp only [residues, mem_filter, mem_univ, true_and] at hr ⊢
    rw [Units.val_mul, map_mul, hr, mul_one, hm]
  · intro r hr
    simp only [residues, mem_filter, mem_univ, true_and] at hr ⊢
    have h1 : quadraticChar (ZMod q) (m : ZMod q) * quadraticChar (ZMod q) ((m⁻¹ : (ZMod q)ˣ) : ZMod q) = 1 := by
      rw [← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one]
    rw [Units.val_mul, map_mul, hr]
    rcases quadraticChar_unit_eq m with h | h <;> rw [h] at hm h1 <;> subst hm <;> linarith
  · intro r _; simp
  · intro r _; simp
  · intro r _
    rw [pow_val_pow_val hz, Units.val_mul]

/-- `η_j(ζ^n) = η_{1-j}(ζ)` for a nonresidue `n` (`e = 2`). -/
theorem gaussianPeriod_two_pow_nonresidue {g : (ZMod q)ˣ} (hg : ∀ x, x ∈ Subgroup.zpowers g)
    (hq2 : q ≠ 2) {z : ℂ} (hz : z ^ q = 1) {n : (ZMod q)ˣ}
    (hn : quadraticChar (ZMod q) n = -1) (j : ℕ) (hj : j < 2) :
    gaussianPeriod g 2 j (z ^ (n : ZMod q).val) = gaussianPeriod g 2 (1 - j) z := by
  rw [gaussianPeriod_two_eq hg hq2 j hj, gaussianPeriod_two_eq hg hq2 (1 - j) (by omega)]
  refine Finset.sum_nbij' (fun r ↦ n * r) (fun r ↦ n⁻¹ * r) ?_ ?_ ?_ ?_ ?_
  · intro r hr
    simp only [mem_filter, mem_univ, true_and] at hr ⊢
    rw [Units.val_mul, map_mul, hr, hn]
    rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl <;> norm_num
  · intro r hr
    simp only [mem_filter, mem_univ, true_and] at hr ⊢
    have h1 : quadraticChar (ZMod q) ((n⁻¹ : (ZMod q)ˣ) : ZMod q) = -1 := by
      have : quadraticChar (ZMod q) (n : ZMod q) *
          quadraticChar (ZMod q) ((n⁻¹ : (ZMod q)ˣ) : ZMod q) = 1 := by
        rw [← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one]
      rw [hn] at this; linarith
    rw [Units.val_mul, map_mul, hr, h1]
    rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl <;> norm_num
  · intro r _; simp
  · intro r _; simp
  · intro r _
    rw [pow_val_pow_val hz, Units.val_mul]

theorem rho_zero_poly (x : ZMod q) : rho x (0 : ℤ[X]) = 0 := by simp [rho]

/-- The primitive root `g` is a nonresidue. -/
theorem quadraticChar_generator {g : (ZMod q)ˣ} (hg : ∀ x, x ∈ Subgroup.zpowers g)
    (hq2 : q ≠ 2) : quadraticChar (ZMod q) g = -1 := by
  have := quadraticChar_eq_neg_one_pow_index hg hq2 (g ^ 1)
  rw [index_pow hg, pow_one] at this
  rw [this, Nat.mod_eq_of_lt]
  · norm_num
  · have := (Fact.out : q.Prime).two_le
    have : q ≠ 2 := hq2
    omega

/-- `∏_{u unit} (x - ζ^u) = Φ_q(x)` for a primitive `q`-th root of unity `ζ`. -/
theorem prod_units_eq_cyclotomic {ζ : ℂ} (hζ : IsPrimitiveRoot ζ q) :
    ∏ u : (ZMod q)ˣ, (X - C (ζ ^ (u : ZMod q).val)) = cyclotomic q ℂ := by
  have hq := (Fact.out : q.Prime)
  rw [cyclotomic_eq_prod_X_sub_primitiveRoots hζ]
  refine Finset.prod_bij (fun u _ ↦ ζ ^ (u : ZMod q).val) ?_ ?_ ?_ (fun _ _ ↦ rfl)
  · intro u _
    rw [mem_primitiveRoots hq.pos]
    refine hζ.pow_of_coprime _ ?_
    have h0 : (u : ZMod q).val ≠ 0 := (ZMod.val_ne_zero _).mpr u.ne_zero
    exact (Nat.coprime_of_lt_prime h0 (ZMod.val_lt _) hq).symm
  · intro a _ b _ h
    exact Units.ext (ZMod.val_injective q (hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) h))
  · intro μ hμ
    rw [mem_primitiveRoots hq.pos] at hμ
    obtain ⟨i, hi, hiμ⟩ := hζ.eq_pow_of_pow_eq_one hμ.pow_eq_one
    have hi0 : i ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hiμ
      exact hμ.ne_one hq.one_lt hiμ.symm
    have hx : (i : ZMod q) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      exact fun h ↦ absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero hi0) h) (by omega)
    refine ⟨Units.mk0 (i : ZMod q) hx, mem_univ _, ?_⟩
    rw [Units.val_mk0, ZMod.val_natCast, Nat.mod_eq_of_lt hi, hiμ]

/-- `ε √q`: `√q` if `q ≡ 1 (mod 4)`, `i √q` otherwise (Gauss's sum `G`). -/
def epsSqrt (q : ℕ) : ℂ := if q % 4 = 1 then (√q : ℂ) else I * √q

omit [Fact q.Prime] in
theorem epsSqrt_sq : epsSqrt q ^ 2 = ((if q % 4 = 1 then (q : ℤ) else -q : ℤ) : ℂ) := by
  have h : ((√q : ℝ) : ℂ) ^ 2 = q := by
    rw [← ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _), ofReal_natCast]
  unfold epsSqrt
  split_ifs <;> push_cast
  · exact h
  · rw [mul_pow, h, I_sq]; ring

/-- A polynomial with prescribed coefficients `w k`, `k ≤ D`. -/
theorem coeff_sum_range_C_mul_X_pow (w : ℕ → ℤ) (D : ℕ) (hw : ∀ i, D < i → w i = 0) (i : ℕ) :
    (∑ k ∈ range (D + 1), C (w k) * (X : ℤ[X]) ^ k).coeff i = w i := by
  simp only [finsetSum_coeff, coeff_C_mul_X_pow, sum_ite_eq, mem_range]
  split_ifs with h
  · rfl
  · exact (hw i (by omega)).symm

/-- The coefficients of `∏_R (x - z^R)` for `z^q = 1`, in terms of the periods. -/
theorem aeval_coeff_residueProduct {g : (ZMod q)ˣ} (hg : ∀ x, x ∈ Subgroup.zpowers g)
    (hq2 : q ≠ 2) (k : ℕ) {z : ℂ} (hz : z ^ q = 1) :
    aeval z ((residueProduct q).coeff k) =
      rho (0 : ZMod q) ((residueProduct q).coeff k) +
        rho (1 : ZMod q) ((residueProduct q).coeff k) * gaussianPeriod g 2 0 z +
        rho (g : ZMod q) ((residueProduct q).coeff k) * gaussianPeriod g 2 1 z := by
  have hodd : q % 2 = 1 := Nat.odd_iff.mp ((Fact.out : q.Prime).odd_of_ne_two hq2)
  have hef : q - 1 = 2 * ((q - 1) / 2) := by omega
  have hζ := isPrimitiveRoot_cexp (q := q)
  rw [aeval_eq_sum_gaussianPeriod hg hef hζ _ ?_ hz]
  · rw [show range 2 = range (1 + 1) from rfl, sum_range_succ, sum_range_one, pow_zero, pow_one,
      Units.val_one]
    ring
  · intro m hm
    have hχ : quadraticChar (ZMod q) m = 1 := by
      rw [neg_one_pow_index hg hq2, if_pos (by simpa [Nat.ModEq] using hm)]
    have h := prod_residues_pow hζ.pow_eq_one m 1 hχ
    rw [← map_residueProduct] at h
    have h' : (∏ r ∈ univ.filter (fun r : (ZMod q)ˣ ↦ quadraticChar (ZMod q) r = 1),
        (X - C (cexp (2 * π * I / q) ^ (r : ZMod q).val))) =
        (residueProduct q).map (aeval (cexp (2 * π * I / q)) : ℤ[X] →ₐ[ℤ] ℂ).toRingHom := by
      rw [map_residueProduct]; rfl
    rw [h'] at h
    have := congrArg (fun p : ℂ[X] ↦ p.coeff k) h
    simpa only [coeff_map, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] using this

/-- **Davenport §3, p. 19 (Gauss), quoted in §1, p. 10.** For an odd prime `q` and
`ζ = e(1/q)` there are integral polynomials `Y, Z` with
`2 ∏_R (x - ζ^R) = Y(x) - ε√q Z(x)` and `2 ∏_N (x - ζ^N) = Y(x) + ε√q Z(x)`
(`R`, `N` the quadratic residues and nonresidues in `1, …, q - 1`, `ε√q = √q` or `i√q` according
as `q ≡ 1` or `3 (mod 4)`), and then `Y² - q* Z² = 4(x^{q-1} + ⋯ + x + 1)`, `q* = ±q`. -/
@[kb "davenport1980" "Ch 3, p. 19; Ch 1, p. 10"]
theorem exists_gauss_product (hq2 : q ≠ 2) :
    ∃ Y Z : ℤ[X],
      2 * ∏ r ∈ residues q, (X - C (cexp (2 * π * I / q) ^ (r : ZMod q).val)) =
        Y.map (Int.castRingHom ℂ) - C (epsSqrt q) * Z.map (Int.castRingHom ℂ) ∧
      2 * ∏ n ∈ nonresidues q, (X - C (cexp (2 * π * I / q) ^ (n : ZMod q).val)) =
        Y.map (Int.castRingHom ℂ) + C (epsSqrt q) * Z.map (Int.castRingHom ℂ) ∧
      Y ^ 2 - C (if q % 4 = 1 then (q : ℤ) else -q) * Z ^ 2 = 4 * ∑ i ∈ range q, X ^ i := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod q)ˣ)
  set ζ := cexp (2 * π * I / q) with hζdef
  have hζ : IsPrimitiveRoot ζ q := isPrimitiveRoot_cexp
  set PR := residueProduct q
  set D := PR.natDegree
  set a : ℕ → ℤ := fun k ↦ rho (0 : ZMod q) (PR.coeff k)
  set b : ℕ → ℤ := fun k ↦ rho (1 : ZMod q) (PR.coeff k)
  set c : ℕ → ℤ := fun k ↦ rho (g : ZMod q) (PR.coeff k)
  have hvan : ∀ x : ZMod q, ∀ i, D < i → rho x (PR.coeff i) = 0 := by
    intro x i hi
    rw [coeff_eq_zero_of_natDegree_lt hi, rho_zero_poly]
  set Y : ℤ[X] := ∑ k ∈ range (D + 1), C (2 * a k - b k - c k) * X ^ k
  set Z : ℤ[X] := ∑ k ∈ range (D + 1), C (c k - b k) * X ^ k
  have hY : ∀ i, Y.coeff i = 2 * a i - b i - c i := fun i ↦
    coeff_sum_range_C_mul_X_pow _ D (fun j hj ↦ by
      simp only [a, b, c, hvan _ j hj]; ring) i
  have hZ : ∀ i, Z.coeff i = c i - b i := fun i ↦
    coeff_sum_range_C_mul_X_pow _ D (fun j hj ↦ by simp only [b, c, hvan _ j hj]; ring) i
  have hη0 := gaussianPeriod_two_zero_eq hg hq2
  have hη1 := gaussianPeriod_two_one_eq hg hq2
  have hGdef : epsSqrt q = if q % 4 = 1 then (√q : ℂ) else I * √q := rfl
  rw [← hGdef] at hη0 hη1
  -- residues
  have h1 : 2 * ∏ r ∈ residues q, (X - C (ζ ^ (r : ZMod q).val)) =
      Y.map (Int.castRingHom ℂ) - C (epsSqrt q) * Z.map (Int.castRingHom ℂ) := by
    ext i
    rw [coeff_ofNat_mul, ← map_residueProduct, coeff_map, coeff_sub, coeff_C_mul, coeff_map,
      coeff_map, hY, hZ]
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    rw [aeval_coeff_residueProduct hg hq2 i hζ.pow_eq_one, hη0, hη1]
    simp only [eq_intCast, a, b, c]
    push_cast
    ring
  -- nonresidues: replace `ζ` by `ζ^g`
  have hg1 : quadraticChar (ZMod q) g = -1 := quadraticChar_generator hg hq2
  have hzq : (ζ ^ (g : ZMod q).val) ^ q = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  have h2 : 2 * ∏ n ∈ nonresidues q, (X - C (ζ ^ (n : ZMod q).val)) =
      Y.map (Int.castRingHom ℂ) + C (epsSqrt q) * Z.map (Int.castRingHom ℂ) := by
    have hperm := prod_residues_pow hζ.pow_eq_one g (-1) hg1
    have hN : ∏ n ∈ nonresidues q, (X - C (ζ ^ (n : ZMod q).val)) =
        (residueProduct q).map (aeval (ζ ^ (g : ZMod q).val) : ℤ[X] →ₐ[ℤ] ℂ).toRingHom := by
      rw [map_residueProduct, hperm]; rfl
    ext i
    rw [coeff_ofNat_mul, hN, coeff_map, coeff_add, coeff_C_mul, coeff_map, coeff_map, hY, hZ]
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    rw [aeval_coeff_residueProduct hg hq2 i hzq,
      gaussianPeriod_two_pow_nonresidue hg hq2 hζ.pow_eq_one hg1 0 two_pos,
      gaussianPeriod_two_pow_nonresidue hg hq2 hζ.pow_eq_one hg1 1 one_lt_two, hη0, hη1]
    simp only [eq_intCast, a, b, c]
    push_cast
    ring
  refine ⟨Y, Z, h1, h2, ?_⟩
  -- the product of the two identities
  apply Polynomial.map_injective (Int.castRingHom ℂ) (RingHom.injective_int _)
  have hprod : (∏ r ∈ residues q, (X - C (ζ ^ (r : ZMod q).val))) *
      ∏ n ∈ nonresidues q, (X - C (ζ ^ (n : ZMod q).val)) = cyclotomic q ℂ := by
    rw [← prod_units_eq_cyclotomic hζ, residues, nonresidues,
      ← prod_filter_mul_prod_filter_not univ (fun r : (ZMod q)ˣ ↦ quadraticChar (ZMod q) r = 1)]
    congr 1
    refine prod_congr (filter_congr fun u _ ↦ ?_) fun _ _ ↦ rfl
    rcases quadraticChar_unit_eq u with h | h <;> rw [h] <;> norm_num
  have hcyc : (4 * ∑ i ∈ range q, (X : ℤ[X]) ^ i).map (Int.castRingHom ℂ) =
      4 * cyclotomic q ℂ := by
    rw [cyclotomic_prime ℂ q]
    simp [Polynomial.map_sum]
  rw [hcyc, ← hprod]
  have hsq := epsSqrt_sq (q := q)
  have e1 := h1
  have e2 := h2
  calc (Y ^ 2 - C (if q % 4 = 1 then (q : ℤ) else -q) * Z ^ 2).map (Int.castRingHom ℂ)
      = (Y.map (Int.castRingHom ℂ) - C (epsSqrt q) * Z.map (Int.castRingHom ℂ)) *
          (Y.map (Int.castRingHom ℂ) + C (epsSqrt q) * Z.map (Int.castRingHom ℂ)) := by
        rw [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_pow,
          map_C, eq_intCast, ← hsq, C_pow]
        ring
    _ = 4 * ((∏ r ∈ residues q, (X - C (ζ ^ (r : ZMod q).val))) *
          ∏ n ∈ nonresidues q, (X - C (ζ ^ (n : ZMod q).val))) := by
        rw [← e1, ← e2]; ring

/-- **Davenport §1, p. 10.** For a prime `q ≡ 1 (mod 4)` there are integers `Y, Z` with
`Y² - q Z² = 4q`, `Z ≠ 0` and `q ∣ Y` (put `x = 1` in Gauss's identity); this solves the
negative Pell equation `q V² - Z² = 4`. -/
@[kb "davenport1980" "Ch 1, p. 10"]
theorem exists_sq_sub_mul_sq_eq (hq : q % 4 = 1) :
    ∃ Y Z : ℤ, Y ^ 2 - q * Z ^ 2 = 4 * q ∧ Z ≠ 0 ∧ (q : ℤ) ∣ Y := by
  obtain ⟨Y, Z, -, -, h⟩ := exists_gauss_product (q := q) (by omega)
  have h1 := congrArg (Polynomial.eval 1) h
  simp only [eval_sub, eval_mul, eval_pow, eval_C, if_pos hq, eval_finsetSum, eval_ofNat, eval_X,
    one_pow, sum_const, card_range, nsmul_eq_mul, mul_one] at h1
  have hp : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp Fact.out
  have hdvd : (q : ℤ) ∣ Y.eval 1 := by
    apply hp.dvd_of_dvd_pow (n := 2)
    have hY2 : Y.eval 1 ^ 2 = 4 * q + q * Z.eval 1 ^ 2 := by linarith
    exact ⟨4 + Z.eval 1 ^ 2, by rw [hY2]; ring⟩
  refine ⟨Y.eval 1, Z.eval 1, by linarith, ?_, hdvd⟩
  intro hZ
  rw [hZ] at h1
  obtain ⟨t, ht⟩ := hdvd
  have : (q : ℤ) * (q * t ^ 2) = q * 4 := by
    push_cast at h1; rw [ht] at h1; linarith
  have h4 : (q : ℤ) * t ^ 2 = 4 := mul_left_cancel₀ hp.ne_zero this
  have : (q : ℤ) ∣ 4 := ⟨t ^ 2, h4.symm⟩
  have : q ∣ 4 := by exact_mod_cast this
  have := Nat.le_of_dvd (by norm_num) this
  interval_cases q <;> simp_all

end NTKB.Davenport
