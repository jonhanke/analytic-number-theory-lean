/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import NTKB.Attr

/-!
# Kloosterman sums (Apostol, Exercise 8.15)

`K(m, n; k) = ∑_{h mod k, (h,k)=1} e^{2πi(mh + n h̄)/k}`, `h̄` the reciprocal of `h` mod `k`
(`kloosterman`, a sum over the units of `ZMod k`; `e^{2πi x/k}` is Mathlib's `ZMod.stdAddChar`).
Exercise 8.15 (a): `K(m, n; k) = K(n, m; k)`; (b): `K(m, n; k) = K(1, mn; k)` if `(m, k) = 1`.
-/

open ZMod

namespace NTKB.Apostol

variable {k : ℕ} [NeZero k]

/-- The Kloosterman sum `K(m, n; k)`. -/
noncomputable def kloosterman (k : ℕ) [NeZero k] (m n : ZMod k) : ℂ :=
  ∑ u : (ZMod k)ˣ, stdAddChar (m * (u : ZMod k) + n * ((u⁻¹ : (ZMod k)ˣ) : ZMod k))

/-- Exercise 8.15 (a): `K(m, n; k) = K(n, m; k)`. -/
@[kb "apostol1976" "Exercise 8.15(a), p. 176"]
theorem kloosterman_comm (m n : ZMod k) : kloosterman k m n = kloosterman k n m := by
  unfold kloosterman
  refine Fintype.sum_equiv (Equiv.inv _) _ _ fun u => ?_
  simp only [Equiv.inv_apply, inv_inv]
  rw [add_comm]

/-- Exercise 8.15 (b): `K(m, n; k) = K(1, mn; k)` for `m` prime to `k`. -/
@[kb "apostol1976" "Exercise 8.15(b), p. 176"]
theorem kloosterman_eq_one_mul {m : ZMod k} (hm : IsUnit m) (n : ZMod k) :
    kloosterman k m n = kloosterman k 1 (m * n) := by
  obtain ⟨w, rfl⟩ := hm
  unfold kloosterman
  refine Fintype.sum_equiv (Equiv.mulLeft w) _ _ fun u => ?_
  simp only [Equiv.coe_mulLeft, mul_inv_rev, Units.val_mul, one_mul]
  congr 1
  have hw : (w : ZMod k) * ((w⁻¹ : (ZMod k)ˣ) : ZMod k) = 1 := Units.mul_inv w
  linear_combination (-(n * ((u⁻¹ : (ZMod k)ˣ) : ZMod k))) * hw

end NTKB.Apostol
