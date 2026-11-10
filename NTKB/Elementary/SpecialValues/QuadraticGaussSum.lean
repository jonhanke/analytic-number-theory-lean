/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.NumberTheory.GaussSum
import NTKB.Elementary.SpecialValues.GaussSumTheta
import NTKB.Elementary.SpecialValues.ValueAtZero

/-!
# Gauss's sign of the quadratic Gauss sum, prime modulus

For an odd prime `p`, the Gauss sum of the Legendre symbol `(·/p)` (Mathlib's
`quadraticChar (ZMod p)`, as a complex Dirichlet character modulo `p`) is
$$\tau\Bigl(\bigl(\tfrac{\cdot}{p}\bigr)\Bigr) = \sum_{a \bmod p}\Bigl(\frac{a}{p}\Bigr)e^{2\pi i a/p}
  = \begin{cases}\sqrt p & p\equiv 1 \pmod 4,\\ i\sqrt p & p \equiv 3 \pmod 4\end{cases}$$
(Gauss 1811; Ireland–Rosen, Chapter 6, Theorem 2 of §4). Mathlib has `gaussSum_sq`, the square
`τ² = (-1)^{(p-1)/2} p`; the sign is the content here.

Proof: `τ = ∑_{x mod p} e^{2πi x²/p}` (counting square roots with
`quadraticChar_card_sqrts`), and the latter is Gauss's quadratic sum, evaluated by the theta
function in `NTKB.sum_range_cexp_two_pi_I_sq_div` (ported from Tau Ceti).
-/

noncomputable section

open Complex
open scoped Real

namespace NTKB

/-- The Legendre symbol modulo `p` as a complex Dirichlet character (`quadraticChar (ZMod p)`
composed with `ℤ → ℂ`). -/
def legendreChar (p : ℕ) [Fact p.Prime] : DirichletCharacter ℂ p :=
  (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ)

theorem legendreChar_apply (p : ℕ) [Fact p.Prime] (a : ZMod p) :
    legendreChar p a = (quadraticChar (ZMod p) a : ℂ) := rfl

/-- `∑_{x mod N} e(x²/N) = ∑_{r < N} e^{2πi r²/N}`. -/
theorem sum_stdAddChar_sq_eq_sum_range (N : ℕ) [NeZero N] :
    ∑ x : ZMod N, (ZMod.stdAddChar (x ^ 2) : ℂ) =
      ∑ r ∈ Finset.range N, cexp (2 * π * I * r ^ 2 / N) := by
  rw [← sum_val_eq_sum_range (fun r ↦ cexp (2 * π * I * r ^ 2 / N))]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  have hx : x ^ 2 = (((x.val ^ 2 : ℕ) : ℤ) : ZMod N) := by push_cast; simp
  rw [hx, ZMod.stdAddChar_coe]
  push_cast
  rfl

/-- **The quadratic Gauss sum as a character sum**: for an odd prime `p`,
`∑_a (a/p) e(a/p) = ∑_x e(x²/p)`. -/
theorem gaussSum_legendreChar_eq_sum_sq (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    gaussSum (legendreChar p) ZMod.stdAddChar = ∑ x : ZMod p, (ZMod.stdAddChar (x ^ 2) : ℂ) := by
  classical
  have hF : ringChar (ZMod p) ≠ 2 := by rwa [ZMod.ringChar_zmod_n]
  -- group the `x` by the value of `x ^ 2`
  have hfib : ∑ x : ZMod p, (ZMod.stdAddChar (x ^ 2) : ℂ) =
      ∑ a : ZMod p, ((Finset.univ.filter fun x : ZMod p ↦ x ^ 2 = a).card : ℂ) *
        ZMod.stdAddChar a := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ)
      (g := fun x : ZMod p ↦ x ^ 2) (fun _ _ ↦ Finset.mem_univ _)]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [Finset.sum_congr rfl (g := fun _ ↦ (ZMod.stdAddChar a : ℂ)) (fun x hx ↦ by
      rw [(Finset.mem_filter.mp hx).2]), Finset.sum_const, nsmul_eq_mul]
  have hcard (a : ZMod p) : ((Finset.univ.filter fun x : ZMod p ↦ x ^ 2 = a).card : ℂ) =
      (quadraticChar (ZMod p) a : ℂ) + 1 := by
    have h := quadraticChar_card_sqrts hF a
    have he : {x : ZMod p | x ^ 2 = a}.toFinset = Finset.univ.filter fun x ↦ x ^ 2 = a := by
      ext x; simp
    rw [he] at h
    exact_mod_cast h
  have hsum : ∑ a : ZMod p, (ZMod.stdAddChar a : ℂ) = 0 :=
    AddChar.sum_eq_zero_of_ne_one (by
      have h := ZMod.isPrimitive_stdAddChar p (a := 1) one_ne_zero
      rwa [AddChar.mulShift_one] at h)
  rw [hfib]
  simp_rw [hcard, add_mul, one_mul]
  rw [Finset.sum_add_distrib, hsum, add_zero]
  rfl

/-- **Gauss's sign of the quadratic Gauss sum.** For an odd prime `p`, the Gauss sum of the
Legendre symbol is `√p` if `p ≡ 1 (mod 4)` and `i√p` if `p ≡ 3 (mod 4)`. -/
@[kb "irelandrosen1990" "Ch. 6, §4, Theorem 2 (Gauss)"]
theorem gaussSum_legendreChar (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    gaussSum (legendreChar p) ZMod.stdAddChar =
      if p % 4 = 1 then (√p : ℂ) else I * √p := by
  rw [gaussSum_legendreChar_eq_sum_sq p hp, sum_stdAddChar_sq_eq_sum_range,
    sum_range_cexp_two_pi_I_sq_div]
  have hodd : p % 2 = 1 := Nat.odd_iff.mp ((Fact.out : p.Prime).odd_of_ne_two hp)
  have h4 : p % 4 = 1 ∨ p % 4 = 3 := by omega
  obtain ⟨q, hq⟩ : ∃ q, p = 4 * q + p % 4 := ⟨p / 4, (Nat.div_add_mod p 4).symm⟩
  have hI4 : (-I) ^ 4 = (1 : ℂ) := by
    rw [show (-I) ^ 4 = I ^ 4 by ring, I_pow_four]
  rcases h4 with h | h
  · rw [if_pos h, hq, h, pow_add, pow_mul, hI4, one_pow, one_mul, pow_one]
    ring_nf
    rw [I_sq]
    ring
  · rw [if_neg (by omega), hq, h, pow_add, pow_mul, hI4, one_pow, one_mul]
    ring_nf
    rw [I_pow_three, I_pow_four]
    ring
