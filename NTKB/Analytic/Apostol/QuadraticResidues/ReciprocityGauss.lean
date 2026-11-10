/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import NTKB.Attr

/-!
# Quadratic reciprocity and the Gauss sum congruence (Apostol, Theorem 9.14)

Let `p, q` be distinct odd primes, `χ(r) = (r|p)` (as a complex character) and
`G = G(1, χ) = ∑_r (r|p) e^{2πir/p}`. Since `G² = (-1|p) p` (Theorem 9.13, Mathlib's
`gaussSum_sq`), `G^{q-1} = ((-1|p) p)^{(q-1)/2}` is an integer. **Theorem 9.14**: the reciprocity
law `(p|q)(q|p) = (-1)^{(p-1)(q-1)/4}` is equivalent to `G^{q-1} ≡ (q|p) (mod q)`.

Apostol's proof: by Euler's criterion, `G^{q-1} ≡ (-1)^{(p-1)(q-1)/4} (p|q) (mod q)` (22).
Mathlib's `legendreSym p a` is `(a|p)`. The reciprocity law itself is not used.
-/

open ZMod

namespace NTKB.Apostol

variable {p q : ℕ} [Fact p.Prime] [Fact q.Prime]

/-- The Legendre symbol `(·|p)` as a complex-valued character. -/
noncomputable def legendreCharC (p : ℕ) [Fact p.Prime] : MulChar (ZMod p) ℂ :=
  (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ)

lemma legendreCharC_apply (a : ℤ) : legendreCharC p a = (legendreSym p a : ℂ) := rfl

lemma legendreCharC_ne_one (hp2 : p ≠ 2) : legendreCharC p ≠ 1 :=
  (MulChar.ringHomComp_ne_one_iff (RingHom.injective_int _)).mpr
    (quadraticChar_ne_one (by rwa [ZMod.ringChar_zmod_n]))

lemma legendreCharC_isQuadratic : (legendreCharC p).IsQuadratic :=
  (quadraticChar_isQuadratic (ZMod p)).comp _

/-- `G(1, χ)^{q-1}` is the integer `((-1|p) p)^{(q-1)/2}`. -/
lemma gaussSum_pow_eq (hp2 : p ≠ 2) (hq : Odd q) :
    gaussSum (legendreCharC p) stdAddChar ^ (q - 1) =
      (((legendreSym p (-1) * p) ^ (q / 2) : ℤ) : ℂ) := by
  have hsq := gaussSum_sq (legendreCharC_ne_one hp2) legendreCharC_isQuadratic
    (ZMod.isPrimitive_stdAddChar p)
  change gaussSum (legendreCharC p) stdAddChar ^ 2 = legendreCharC p (-1) * _ at hsq
  obtain ⟨m, rfl⟩ := hq
  rw [show 2 * m + 1 - 1 = 2 * m by omega, show (2 * m + 1) / 2 = m by omega, pow_mul, hsq,
    ZMod.card]
  have : legendreCharC p (-1) = (legendreSym p (-1) : ℂ) := by
    rw [← legendreCharC_apply]; simp
  rw [this]
  push_cast
  ring

/-- Apostol (22): `G^{q-1} ≡ (-1)^{(p-1)(q-1)/4} (p|q) (mod q)` (Euler's criterion). -/
lemma gaussSum_pow_modEq (hp2 : p ≠ 2) :
    (legendreSym p (-1) * p) ^ (q / 2) ≡ (-1) ^ ((p / 2) * (q / 2)) * legendreSym q p
      [ZMOD q] := by
  rw [← ZMod.intCast_eq_intCast_iff]
  have he := legendreSym.eq_pow q (p : ℤ)
  have hm1 : legendreSym p (-1) = (-1) ^ (p / 2) := by
    rw [legendreSym.at_neg_one hp2, ZMod.χ₄_eq_neg_one_pow (Nat.odd_iff.mp
      ((Fact.out : p.Prime).eq_two_or_odd'.resolve_left hp2))]
  push_cast
  rw [he, hm1, mul_pow]
  simp only [Int.cast_pow, Int.cast_neg, Int.cast_one, ← pow_mul, Int.cast_natCast]

lemma eq_of_modEq_of_sq_eq_one {x y : ℤ} {q : ℕ} (hq : 2 < q) (hx : x = 1 ∨ x = -1)
    (hy : y = 1 ∨ y = -1) (h : x ≡ y [ZMOD q]) : x = y := by
  have hd := Int.ModEq.dvd h
  have hq' : (2 : ℤ) < q := by exact_mod_cast hq
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · rfl
  · have h2 : (q : ℤ) ∣ 2 := by
      have : (-1 : ℤ) - 1 = -2 := by norm_num
      rw [this, dvd_neg] at hd; exact hd
    have := Int.le_of_dvd (by norm_num) h2; linarith
  · have h2 : (q : ℤ) ∣ 2 := by
      have : (1 : ℤ) - -1 = 2 := by norm_num
      rwa [this] at hd
    have := Int.le_of_dvd (by norm_num) h2; linarith
  · rfl

/-- **Apostol, Theorem 9.14**: for distinct odd primes `p, q`, the quadratic reciprocity law
`(p|q)(q|p) = (-1)^{(p-1)(q-1)/4}` is equivalent to the congruence `G(1, χ)^{q-1} ≡ (q|p)
(mod q)` for the integer `G(1, χ)^{q-1}`. -/
@[kb "apostol1976" "Thm 9.14, p. 193"]
theorem apostol_thm_9_14 (hp2 : p ≠ 2) (hq2 : q ≠ 2) (hpq : p ≠ q) :
    (legendreSym q p * legendreSym p q = (-1) ^ ((p / 2) * (q / 2))) ↔
      ∃ g : ℤ, (g : ℂ) = gaussSum (legendreCharC p) stdAddChar ^ (q - 1) ∧
        g ≡ legendreSym p q [ZMOD q] := by
  have hq : Odd q := (Fact.out : q.Prime).eq_two_or_odd'.resolve_left hq2
  have hq3 : 2 < q := by
    have := (Fact.out : q.Prime).two_le; omega
  set g : ℤ := (legendreSym p (-1) * p) ^ (q / 2)
  have hg := gaussSum_pow_eq (p := p) hp2 hq
  have hcong := gaussSum_pow_modEq (p := p) (q := q) hp2
  have hpq' : (p : ZMod q) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro h
    exact hpq ((Nat.prime_dvd_prime_iff_eq (Fact.out : q.Prime) (Fact.out : p.Prime)).mp h).symm
  have hqp' : (q : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro h
    exact hpq ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) (Fact.out : q.Prime)).mp h)
  have hL1 : legendreSym q p = 1 ∨ legendreSym q p = -1 :=
    legendreSym.eq_one_or_neg_one q (by exact_mod_cast hpq')
  have hL2 : legendreSym p q = 1 ∨ legendreSym p q = -1 :=
    legendreSym.eq_one_or_neg_one p (by exact_mod_cast hqp')
  have hs : ((-1 : ℤ) ^ ((p / 2) * (q / 2))) = 1 ∨ ((-1 : ℤ) ^ ((p / 2) * (q / 2))) = -1 :=
    neg_one_pow_eq_or ℤ _
  have hL1sq : legendreSym q p * legendreSym q p = 1 := by
    rcases hL1 with h | h <;> rw [h] <;> norm_num
  constructor
  · intro hrec
    refine ⟨g, hg.symm, hcong.trans ?_⟩
    rw [← hrec]
    have : legendreSym q p * legendreSym p q * legendreSym q p = legendreSym p q := by
      linear_combination legendreSym p q * hL1sq
    rw [this]
  · rintro ⟨g', hg', hg'c⟩
    have hgg : g' = g := by exact_mod_cast hg'.trans hg
    rw [hgg] at hg'c
    have hm : (-1) ^ ((p / 2) * (q / 2)) * legendreSym q p ≡ legendreSym p q [ZMOD q] :=
      hcong.symm.trans hg'c
    have hx : (-1) ^ ((p / 2) * (q / 2)) * legendreSym q p = 1 ∨
        (-1) ^ ((p / 2) * (q / 2)) * legendreSym q p = -1 := by
      rcases hs with h | h <;> rcases hL1 with h' | h' <;> rw [h, h'] <;> norm_num
    have heq := eq_of_modEq_of_sq_eq_one hq3 hx hL2 hm
    rw [← heq]
    linear_combination (-1 : ℤ) ^ ((p / 2) * (q / 2)) * hL1sq

end NTKB.Apostol
