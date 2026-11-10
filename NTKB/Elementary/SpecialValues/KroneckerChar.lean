/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.NumberTheory.LegendreSymbol.ZModChar
import Mathlib.NumberTheory.DirichletCharacter.GaussSum
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import NTKB.Elementary.SpecialValues.QuadraticGaussSum

/-!
# Jacobi characters and Gauss sums of products of characters

* `NTKB.jacobiChar m`: the Dirichlet character `a ↦ J(a | m)` modulo `m` (Mathlib's `jacobiSym`
  in the upper argument), with values in `ℂ`. For a prime `p` it is the Legendre character, and
  `jacobiChar (m n)` is the product of `jacobiChar m` and `jacobiChar n`.
* `NTKB.gaussSum_eq_mul_of_coprime`: the Gauss sum of a character modulo `N = mn`, `m, n`
  coprime, whose values are `χ(a mod m) ψ(a mod n)`, is `χ(n) ψ(m) τ(χ) τ(ψ)`
  (Chinese remainder theorem).
-/

noncomputable section

open Complex
open scoped Real

namespace NTKB

/-! ### Jacobi characters -/

/-- `J(cast x | m)` only depends on `x : ZMod m`. -/
theorem jacobiSym_cast_eq {m : ℕ} (x : ZMod m) (z : ℤ) (h : (z : ZMod m) = x) :
    jacobiSym (ZMod.cast x : ℤ) m = jacobiSym z m :=
  jacobiSym.mod_left' ((ZMod.intCast_eq_intCast_iff' _ _ _).mp (by rw [ZMod.intCast_zmod_cast, h]))

open Classical in
/-- The Jacobi symbol `a ↦ J(a | m)` as a complex Dirichlet character modulo `m` (value `0` at
non-units). -/
def jacobiChar (m : ℕ) : DirichletCharacter ℂ m where
  toFun a := if IsUnit a then (jacobiSym (ZMod.cast a : ℤ) m : ℂ) else 0
  map_one' := by
    rw [if_pos isUnit_one, jacobiSym_cast_eq 1 1 Int.cast_one, jacobiSym.one_left, Int.cast_one]
  map_mul' a b := by
    by_cases ha : IsUnit a <;> by_cases hb : IsUnit b
    · rw [if_pos (ha.mul hb), if_pos ha, if_pos hb,
        jacobiSym_cast_eq (a * b) ((ZMod.cast a : ℤ) * ZMod.cast b) (by
          push_cast; simp only [ZMod.intCast_zmod_cast]),
        jacobiSym.mul_left, Int.cast_mul]
    · rw [if_neg (fun h ↦ hb (isUnit_of_mul_isUnit_right h)), if_neg hb, mul_zero]
    · rw [if_neg (fun h ↦ ha (isUnit_of_mul_isUnit_left h)), if_neg ha, zero_mul]
    · rw [if_neg (fun h ↦ ha (isUnit_of_mul_isUnit_left h)), if_neg ha, zero_mul]
  map_nonunit' a ha := by simp only [MonoidHom.coe_mk, OneHom.coe_mk, if_neg ha]

theorem jacobiChar_apply_of_isUnit {m : ℕ} {a : ZMod m} (ha : IsUnit a) :
    jacobiChar m a = (jacobiSym (ZMod.cast a : ℤ) m : ℂ) := by
  classical
  show (if IsUnit a then _ else _) = _
  rw [if_pos ha]

/-- For `m ≠ 0`, `jacobiChar m a = J(a | m)` for every `a` (the Jacobi symbol vanishes at
non-units). -/
theorem jacobiChar_apply {m : ℕ} [NeZero m] (a : ZMod m) :
    jacobiChar m a = (jacobiSym (ZMod.cast a : ℤ) m : ℂ) := by
  by_cases ha : IsUnit a
  · exact jacobiChar_apply_of_isUnit ha
  · rw [MulChar.map_nonunit _ ha]
    have hcop : ¬ (a.val.Coprime m) := by
      rw [← ZMod.isUnit_iff_coprime, ZMod.natCast_zmod_val]; exact ha
    have h0 : jacobiSym (ZMod.cast a : ℤ) m = 0 := by
      rw [jacobiSym.eq_zero_iff_not_coprime, ZMod.cast_eq_val, Int.gcd_natCast_natCast]
      exact hcop
    rw [h0, Int.cast_zero]

/-- `jacobiChar m` at the residue of an integer. -/
theorem jacobiChar_intCast {m : ℕ} [NeZero m] (z : ℤ) :
    jacobiChar m (z : ZMod m) = (jacobiSym z m : ℂ) := by
  rw [jacobiChar_apply, jacobiSym_cast_eq _ z rfl]

/-- For a prime `p`, the Jacobi character is the Legendre character. -/
theorem jacobiChar_prime (p : ℕ) [Fact p.Prime] : jacobiChar p = legendreChar p := by
  ext a
  rw [jacobiChar_apply, legendreChar_apply, ← jacobiSym.legendreSym.to_jacobiSym]
  simp only [legendreSym, ZMod.intCast_zmod_cast]

/-! ### Products of characters of coprime moduli -/

/-- Characters `χ` modulo `m` and `ψ` modulo `n` give the function `a ↦ χ(a mod m) ψ(a mod n)` on
`ZMod N`. -/
def crtProd {m n N : ℕ} (χ : DirichletCharacter ℂ m) (ψ : DirichletCharacter ℂ n) (a : ZMod N) :
    ℂ :=
  χ (ZMod.cast a) * ψ (ZMod.cast a)

/-- **The Gauss sum of a product of characters of coprime moduli** (Chinese remainder theorem): if
`N = m n` with `m, n` coprime and a character `Ξ` modulo `N` has the values
`Ξ(a) = χ(a mod m) ψ(a mod n)`, then `τ(Ξ) = χ(n) ψ(m) τ(χ) τ(ψ)`. -/
theorem gaussSum_eq_mul_of_coprime {m n N : ℕ} [NeZero m] [NeZero n] [NeZero N]
    (hN : N = m * n) (hmn : m.Coprime n) (χ : DirichletCharacter ℂ m)
    (ψ : DirichletCharacter ℂ n) (Ξ : DirichletCharacter ℂ N)
    (hΞ : ∀ a : ZMod N, Ξ a = χ (ZMod.cast a) * ψ (ZMod.cast a)) :
    gaussSum Ξ ZMod.stdAddChar =
      χ n * ψ m * gaussSum χ ZMod.stdAddChar * gaussSum ψ ZMod.stdAddChar := by
  classical
  -- the CRT parametrization `(x, y) ↦ x n + y m`
  set Φ : ZMod m × ZMod n → ZMod N := fun p ↦ ((p.1.val * n + p.2.val * m : ℕ) : ZMod N)
    with hΦ
  have hdm : m ∣ N := ⟨n, hN⟩
  have hdn : n ∣ N := ⟨m, by rw [hN, mul_comm]⟩
  have hcastm (p : ZMod m × ZMod n) : (ZMod.cast (Φ p) : ZMod m) = p.1 * n := by
    rw [hΦ, ZMod.cast_natCast hdm]
    push_cast
    simp
  have hcastn (p : ZMod m × ZMod n) : (ZMod.cast (Φ p) : ZMod n) = p.2 * m := by
    rw [hΦ, ZMod.cast_natCast hdn]
    push_cast
    simp
  have hinj : Function.Injective Φ := by
    intro p q hpq
    have h1 := hcastm p
    have h2 := hcastn p
    rw [hpq, hcastm q] at h1
    rw [hpq, hcastn q] at h2
    have hun : IsUnit (n : ZMod m) := (ZMod.isUnit_iff_coprime n m).mpr hmn.symm
    have hum : IsUnit (m : ZMod n) := (ZMod.isUnit_iff_coprime m n).mpr hmn
    exact Prod.ext (hun.mul_left_injective h1.symm) (hum.mul_left_injective h2.symm)
  have hbij : Function.Bijective Φ := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨hinj, ?_⟩
    simp [ZMod.card, hN]
  -- the additive character splits
  have hadd (p : ZMod m × ZMod n) :
      (ZMod.stdAddChar (Φ p) : ℂ) = ZMod.stdAddChar p.1 * ZMod.stdAddChar p.2 := by
    have e1 : (ZMod.stdAddChar p.1 : ℂ) = ZMod.stdAddChar (((p.1.val : ℕ) : ℤ) : ZMod m) := by
      simp
    have e2 : (ZMod.stdAddChar p.2 : ℂ) = ZMod.stdAddChar (((p.2.val : ℕ) : ℤ) : ZMod n) := by
      simp
    have e3 : (ZMod.stdAddChar (Φ p) : ℂ) =
        ZMod.stdAddChar (((p.1.val * n + p.2.val * m : ℕ) : ℤ) : ZMod N) := by
      simp [hΦ]
    rw [e1, e2, e3, ZMod.stdAddChar_coe, ZMod.stdAddChar_coe, ZMod.stdAddChar_coe,
      ← Complex.exp_add]
    congr 1
    have hm0 : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
    have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
    rw [hN]
    push_cast
    field_simp
  rw [gaussSum, ← Fintype.sum_bijective Φ hbij (fun p ↦ Ξ (Φ p) * ZMod.stdAddChar (Φ p)) _
    fun _ ↦ rfl, Fintype.sum_prod_type, gaussSum, gaussSum, mul_assoc, Finset.sum_mul_sum,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  rw [hΞ, hcastm, hcastn, hadd, map_mul, map_mul]
  ring

/-- The product of the level changes of characters of coprime moduli has the values
`χ(a mod m) ψ(a mod n)`. -/
theorem changeLevel_mul_changeLevel_apply {m n N : ℕ} [NeZero m] [NeZero n] [NeZero N]
    (hN : N = m * n) (hmn : m.Coprime n) (χ : DirichletCharacter ℂ m)
    (ψ : DirichletCharacter ℂ n) (hm : m ∣ N) (hn : n ∣ N) (a : ZMod N) :
    (DirichletCharacter.changeLevel hm χ * DirichletCharacter.changeLevel hn ψ) a =
      χ (ZMod.cast a) * ψ (ZMod.cast a) := by
  by_cases ha : IsUnit a
  · rw [MulChar.mul_apply, ← ha.unit_spec, DirichletCharacter.changeLevel_eq_cast_of_dvd,
      DirichletCharacter.changeLevel_eq_cast_of_dvd]
  · rw [MulChar.map_nonunit _ ha]
    -- `a` is not a unit modulo `mn`, so it is not a unit modulo `m` or modulo `n`
    by_contra hne
    have hu1 : IsUnit (ZMod.cast a : ZMod m) := by
      by_contra h
      exact hne (by rw [MulChar.map_nonunit _ h, zero_mul])
    have hu2 : IsUnit (ZMod.cast a : ZMod n) := by
      by_contra h
      exact hne (by rw [MulChar.map_nonunit _ h, mul_zero])
    apply ha
    have h1 : a.val.Coprime m := by
      rw [← ZMod.isUnit_iff_coprime]
      rwa [ZMod.cast_eq_val] at hu1
    have h2 : a.val.Coprime n := by
      rw [← ZMod.isUnit_iff_coprime]
      rwa [ZMod.cast_eq_val] at hu2
    have key : ∀ k : ℕ, k.Coprime m → k.Coprime n → k.Coprime N :=
      fun k h1 h2 ↦ hN ▸ Nat.Coprime.mul_right h1 h2
    rw [← ZMod.natCast_zmod_val a, ZMod.isUnit_iff_coprime]
    exact key _ h1 h2

end NTKB
