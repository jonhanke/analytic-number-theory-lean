/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.DirichletCharacter.GaussSum
import NTKB.Attr

/-!
# Separable Gauss sums (Apostol, Chapter 8, §8.5, Theorems 8.9 and 8.10)

For a Dirichlet character `χ` mod `k` and an additive character `ψ` (Apostol: `ψ(m) = e(m/k)`),
the Gauss sum `G(n, χ) = ∑_{m mod k} χ(m) ψ(nm)` is Mathlib's `gaussSum χ (ψ.mulShift n)`.
`G(n, χ)` is **separable** if `G(n, χ) = χ̄(n) G(1, χ)` (`χ̄ = χ⁻¹`).

* Theorem 8.9: `G(n, χ)` is separable whenever `(n, k) = 1` (Mathlib's `gaussSum_mulShift_eq`);
* Theorem 8.10: `G(n, χ)` is separable for every `n` iff `G(n, χ) = 0` whenever `(n, k) > 1`.
-/

namespace NTKB.Apostol

variable {k : ℕ} [NeZero k] {R : Type*} [CommRing R]

/-- `G(n, χ)` is separable: `G(n, χ) = χ̄(n) G(1, χ)` (Apostol, §8.5, (12)). -/
def GaussSumSeparable (χ : DirichletCharacter R k) (ψ : AddChar (ZMod k) R) (n : ZMod k) : Prop :=
  gaussSum χ (ψ.mulShift n) = χ⁻¹ n * gaussSum χ ψ

/-- **Apostol, Theorem 8.9.** `G(n, χ)` is separable whenever `n` is a unit mod `k`. -/
@[kb "apostol1976" "Thm 8.9, p. 165"]
theorem gaussSumSeparable_of_isUnit (χ : DirichletCharacter R k) (ψ : AddChar (ZMod k) R)
    {n : ZMod k} (hn : IsUnit n) : GaussSumSeparable χ ψ n := by
  obtain ⟨u, rfl⟩ := hn
  exact gaussSum_mulShift_eq χ ψ u

/-- **Apostol, Theorem 8.10.** `G(n, χ)` is separable for every `n` iff `G(n, χ) = 0` for every
`n` with `(n, k) > 1` (i.e. every non-unit `n` mod `k`). -/
@[kb "apostol1976" "Thm 8.10, p. 166"]
theorem gaussSumSeparable_forall_iff (χ : DirichletCharacter R k) (ψ : AddChar (ZMod k) R) :
    (∀ n, GaussSumSeparable χ ψ n) ↔ ∀ n : ZMod k, ¬ IsUnit n → gaussSum χ (ψ.mulShift n) = 0 := by
  constructor
  · intro h n hn
    rw [h n, MulChar.map_nonunit _ hn, zero_mul]
  · intro h n
    by_cases hn : IsUnit n
    · exact gaussSumSeparable_of_isUnit χ ψ hn
    · rw [GaussSumSeparable, h n hn, MulChar.map_nonunit _ hn, zero_mul]

end NTKB.Apostol
