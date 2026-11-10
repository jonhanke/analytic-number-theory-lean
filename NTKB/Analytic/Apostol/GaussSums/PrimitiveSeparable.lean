/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Apostol.GaussSums.Separable
import NTKB.Analytic.Apostol.Congruences.ReducedResidues
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

/-!
# Primitivity and separable Gauss sums (Apostol, Theorem 8.19)

**Theorem 8.19**: `χ` mod `k` is primitive iff `G(n, χ)` is separable for every `n`.

The forward direction is Mathlib's `DirichletCharacter.gaussSum_mulShift_of_isPrimitive`
(Apostol's Theorem 8.15 (b)). For the converse Apostol shows: if `χ` is not primitive, with
conductor `c < k` and inducing primitive character `ψ` mod `c`, then for `r = k/c`
(`(r, k) > 1`) `G(r, χ) = (φ(k)/φ(c)) G(1, ψ)` (Theorem 5.33 (a), here
`card_fiber_unitsMap`), which is nonzero since `|G(1, ψ)| = √c` (Mathlib's
`DirichletCharacter.norm_gaussSum_stdAddChar`, Apostol's 8.15 (c)); by Theorem 8.10 `G(·, χ)` is
then not separable at `r`.
-/

open Finset ZMod

namespace NTKB.Apostol

/-- A sum `∑_x χ(x) f(x)` over `ZMod k` only involves the units. -/
lemma sum_mulChar_eq_sum_units {k : ℕ} [NeZero k] (χ : MulChar (ZMod k) ℂ) (f : ZMod k → ℂ) :
    ∑ x : ZMod k, χ x * f x = ∑ u : (ZMod k)ˣ, χ u * f u := by
  have e : ∑ x ∈ (univ : Finset (ZMod k)ˣ).map ⟨Units.val, Units.val_injective⟩, χ x * f x =
      ∑ u : (ZMod k)ˣ, χ u * f u := Finset.sum_map _ _ _
  rw [← e]
  refine (Finset.sum_subset (subset_univ _) fun x _ hx => ?_).symm
  have : ¬ IsUnit x := by
    rintro ⟨u, rfl⟩
    exact hx (mem_map.mpr ⟨u, mem_univ _, rfl⟩)
  rw [MulChar.map_nonunit _ this, zero_mul]

/-- `e_k(r u) = e_c(u mod c)` when `k = c r`. -/
lemma stdAddChar_mul_eq {k c r : ℕ} [NeZero k] [NeZero c] (hk : k = c * r) (u : ZMod k) :
    stdAddChar ((r : ZMod k) * u) = stdAddChar (ZMod.cast u : ZMod c) := by
  have hr : (r : ℂ) ≠ 0 := by
    have : r ≠ 0 := fun h => NeZero.ne k (by rw [hk, h, mul_zero])
    exact_mod_cast this
  have hc : (c : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne c
  conv_lhs => rw [← ZMod.natCast_zmod_val u, ← Nat.cast_mul]
  conv_rhs => rw [← ZMod.natCast_zmod_val u, ZMod.cast_natCast ⟨r, hk⟩]
  rw [stdAddChar_apply, stdAddChar_apply, toCircle_natCast, toCircle_natCast]
  congr 1
  have hk' : (k : ℂ) = c * r := by exact_mod_cast hk
  rw [hk']
  push_cast
  field_simp

/-- `G(r, χ) = (φ(k)/φ(c)) G(1, ψ)` for `χ` induced by `ψ` mod `c`, `k = c r`. -/
lemma gaussSum_changeLevel_mulShift {k c r : ℕ} [NeZero k] [NeZero c] (hk : k = c * r)
    (ψ : DirichletCharacter ℂ c) :
    gaussSum (DirichletCharacter.changeLevel ⟨r, hk⟩ ψ) (stdAddChar.mulShift (r : ZMod k)) =
      ((k.totient / c.totient : ℕ) : ℂ) * gaussSum ψ stdAddChar := by
  classical
  have hdvd : c ∣ k := ⟨r, hk⟩
  set F : (ZMod c)ˣ → ℂ := fun v => ψ v * stdAddChar (v : ZMod c)
  unfold gaussSum
  simp only [AddChar.mulShift_apply]
  rw [sum_mulChar_eq_sum_units _ (fun x => stdAddChar ((r : ZMod k) * x)),
    sum_mulChar_eq_sum_units ψ (fun x => stdAddChar x)]
  have hterm : ∀ u : (ZMod k)ˣ, (DirichletCharacter.changeLevel hdvd ψ) (u : ZMod k) *
      stdAddChar ((r : ZMod k) * (u : ZMod k)) = F (ZMod.unitsMap hdvd u) := by
    intro u
    rw [DirichletCharacter.changeLevel_eq_cast_of_dvd, stdAddChar_mul_eq hk]
    simp only [F, ZMod.unitsMap_val]
  simp_rw [hterm]
  rw [Finset.sum_comp F (ZMod.unitsMap hdvd)]
  have himage : (univ : Finset (ZMod k)ˣ).image (ZMod.unitsMap hdvd) = univ := by
    ext v
    simp only [mem_image, mem_univ, true_and, iff_true]
    exact ZMod.unitsMap_surjective hdvd v
  rw [himage, Finset.mul_sum]
  refine sum_congr rfl fun v _ => ?_
  rw [card_fiber_unitsMap hdvd v, nsmul_eq_mul]

/-- **Theorem 8.19**: a Dirichlet character `χ` mod `k` is primitive iff the Gauss sums
`G(n, χ)` are separable for all `n`. -/
@[kb "apostol1976" "Thm 8.19, p. 171"]
theorem isPrimitive_iff_forall_gaussSumSeparable {k : ℕ} [NeZero k] (χ : DirichletCharacter ℂ k) :
    χ.IsPrimitive ↔ ∀ n, GaussSumSeparable χ stdAddChar n := by
  constructor
  · intro hχ n
    exact gaussSum_mulShift_of_isPrimitive _ hχ n
  · intro h
    by_contra hχ
    rw [gaussSumSeparable_forall_iff] at h
    set c := χ.conductor
    have hcdvd : c ∣ k := χ.conductor_dvd_level
    have hck : c ≠ k := fun h' => hχ ((DirichletCharacter.isPrimitive_def χ).mpr h')
    have hc0 : c ≠ 0 := fun h0 => NeZero.ne k (Nat.eq_zero_of_zero_dvd (h0 ▸ hcdvd))
    have : NeZero c := ⟨hc0⟩
    obtain ⟨r, hr⟩ := hcdvd
    have hr0 : r ≠ 0 := by
      intro h0; rw [h0, mul_zero] at hr; exact NeZero.ne k hr
    have hr1 : r ≠ 1 := by
      intro h1; rw [h1, mul_one] at hr; exact hck hr.symm
    have hr2 : 2 ≤ r := by omega
    -- `r` is not a unit modulo `k`
    have hnu : ¬ IsUnit (r : ZMod k) := by
      rw [ZMod.isUnit_iff_coprime]
      intro hcop
      have hrk : r ∣ k := ⟨c, by rw [hr, mul_comm]⟩
      have := Nat.Coprime.eq_one_of_dvd hcop hrk
      omega
    have hG := h (r : ZMod k) hnu
    have hχeq : DirichletCharacter.changeLevel ⟨r, hr⟩ χ.primitiveCharacter = χ :=
      χ.changeLevel_primitiveCharacter
    rw [← hχeq, gaussSum_changeLevel_mulShift hr] at hG
    rcases mul_eq_zero.mp hG with h1 | h1
    · have hpos : 0 < k.totient / c.totient := Nat.div_pos
        (Nat.le_of_dvd (Nat.totient_pos.mpr (NeZero.pos k))
          (Nat.totient_dvd_of_dvd ⟨r, hr⟩)) (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hc0))
      exact absurd h1 (by exact_mod_cast hpos.ne')
    · have hn := DirichletCharacter.norm_gaussSum_stdAddChar χ.primitiveCharacter_isPrimitive
      rw [h1, norm_zero] at hn
      have : (0 : ℝ) < √(c : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast Nat.pos_of_ne_zero hc0)
      linarith

/-- **Theorem 8.11** (Apostol). If `G(n, χ)` is separable for every `n`, then `|G(1, χ)|² = k`.
(Here from Theorem 8.19, `χ` is then primitive, and Mathlib's `norm_gaussSum_stdAddChar`, instead of
Apostol's direct computation of `∑_n |G(n, χ)|²`.) -/
@[kb "apostol1976" "Thm 8.11, p. 166"]
theorem apostol_thm_8_11 {k : ℕ} [NeZero k] (χ : DirichletCharacter ℂ k)
    (h : ∀ n, GaussSumSeparable χ stdAddChar n) : ‖gaussSum χ stdAddChar‖ ^ 2 = k := by
  rw [DirichletCharacter.norm_gaussSum_stdAddChar ((isPrimitive_iff_forall_gaussSumSeparable χ).2 h),
    Real.sq_sqrt (Nat.cast_nonneg _)]

end NTKB.Apostol
