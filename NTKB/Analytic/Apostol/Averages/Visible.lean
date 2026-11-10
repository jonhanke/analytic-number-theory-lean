/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.Data.Int.GCD
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic
import NTKB.Attr

/-!
# Lattice points visible from each other (Apostol, Chapter 3, §3.8, Theorem 3.8)

Two lattice points `P, Q ∈ ℤ²` are *mutually visible* if the line segment joining them contains
no lattice point other than `P` and `Q` (Apostol's definition; the open segment
`{P + t (Q - P) : 0 < t < 1}` has no lattice point). Theorem 3.8: `(a, b)` and `(m, n)` are
mutually visible iff `gcd(a - m, b - n) = 1`.

Proof: reduce to `Q - P` seen from the origin. If `d = gcd > 1`, the point `(Q - P)/d` lies on
the segment. If `gcd = 1` and `t (c, e)` is a lattice point, Bezout `uc + ve = 1` shows that
`t = u (tc) + v (te)` is an integer, impossible for `0 < t < 1` (this replaces Apostol's
rationality argument by a one-line equivalent).
-/

namespace NTKB.Apostol

/-- `P` and `Q` are *mutually visible*: no lattice point lies on the open segment joining them
(Apostol, §3.8). -/
def MutuallyVisible (P Q : ℤ × ℤ) : Prop :=
  ∀ t : ℝ, 0 < t → t < 1 → ∀ R : ℤ × ℤ,
    ¬ ((R.1 : ℝ) = P.1 + t * (Q.1 - P.1) ∧ (R.2 : ℝ) = P.2 + t * (Q.2 - P.2))

/-- **Apostol, Theorem 3.8.** The lattice points `(a, b)` and `(m, n)` are mutually visible iff
`a - m` and `b - n` are relatively prime. -/
@[kb "apostol1976" "Thm 3.8, p. 62"]
theorem mutuallyVisible_iff_gcd_eq_one (a b m n : ℤ) :
    MutuallyVisible (a, b) (m, n) ↔ Int.gcd (a - m) (b - n) = 1 := by
  constructor
  · intro hvis
    by_contra hg
    set d := Int.gcd (a - m) (b - n) with hd
    -- the point `P + (Q - P)/d` (with `d = 0` meaning `P = Q`) lies on the segment
    rcases Nat.eq_zero_or_pos d with h0 | hpos
    · have h1 : a - m = 0 := Int.gcd_eq_zero_iff.1 h0 |>.1
      have h2 : b - n = 0 := Int.gcd_eq_zero_iff.1 h0 |>.2
      refine hvis (1 / 2) (by norm_num) (by norm_num) (a, b) ⟨?_, ?_⟩
      · have : (m : ℝ) = a := by exact_mod_cast (by omega : m = a)
        simp [this]
      · have : (n : ℝ) = b := by exact_mod_cast (by omega : n = b)
        simp [this]
    · have hd2 : 2 ≤ d := by omega
      obtain ⟨c, hc⟩ := Int.gcd_dvd_left (a := a - m) (b := b - n)
      obtain ⟨e, he⟩ := Int.gcd_dvd_right (a := a - m) (b := b - n)
      rw [← hd] at hc he
      have hdR : (0 : ℝ) < d := by exact_mod_cast hpos
      refine hvis (1 / d) (by positivity) ?_ (a - c, b - e) ⟨?_, ?_⟩
      · rw [div_lt_one hdR]; exact_mod_cast hd2
      · have : (a : ℝ) - m = d * c := by exact_mod_cast hc
        push_cast
        rw [show (m : ℝ) - a = -(d * c) by linarith]
        field_simp
        ring
      · have : (b : ℝ) - n = d * e := by exact_mod_cast he
        push_cast
        rw [show (n : ℝ) - b = -(d * e) by linarith]
        field_simp
        ring
  · intro hg t ht0 ht1 R ⟨h1, h2⟩
    -- Bezout: `1 = (a - m) u + (b - n) v`
    have hbez := Int.gcd_eq_gcd_ab (a - m) (b - n)
    rw [hg] at hbez
    set u := Int.gcdA (a - m) (b - n)
    set v := Int.gcdB (a - m) (b - n)
    -- `t = u (a - R.1) + v (b - R.2)` is an integer
    have ht : t = ((u * (a - R.1) + v * (b - R.2) : ℤ) : ℝ) := by
      have hb : ((a : ℝ) - m) * u + ((b : ℝ) - n) * v = 1 := by exact_mod_cast hbez.symm
      push_cast
      rw [h1, h2]
      linear_combination (-t) * hb
    set k := u * (a - R.1) + v * (b - R.2)
    rw [ht] at ht0 ht1
    have : (0 : ℤ) < k := by exact_mod_cast ht0
    have : k < (1 : ℤ) := by exact_mod_cast ht1
    omega

end NTKB.Apostol
