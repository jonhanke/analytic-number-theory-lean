/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Apostol.PNT.AnalyticPNT
import NTKB.Analytic.Apostol.PNT.DivisorBoundLower
import NTKB.Analytic.Apostol.Primes.ChebyshevForms

/-!
# The prime number theorem and its consequences in Apostol's book

From `prime_number_theorem_psi` (Apostol's analytic proof, Chapter 13) and the equivalences of
Theorem 4.4: `π(x) log x / x → 1`. This discharges the named input `PrimeNumberTheoremStatement`
of Theorem 13.12 (b).
-/

open Filter Topology Chebyshev

namespace NTKB.Apostol

/-- **The prime number theorem**: `π(x) ~ x / log x` (Apostol, Chapter 13 with Theorem 4.4). -/
@[kb "apostol1976" "Thm 4.4, p. 79"]
theorem prime_number_theorem :
    Tendsto (fun x : ℝ ↦ (Nat.primeCounting ⌊x⌋₊ : ℝ) * Real.log x / x) atTop (𝓝 1) :=
  apostol_thm_4_4.1.mpr (apostol_thm_4_4.2.mpr prime_number_theorem_psi)

theorem primeNumberTheoremStatement : PrimeNumberTheoremStatement := ⟨prime_number_theorem⟩

/-- **Apostol, Theorem 13.12 (b)**, unconditional: `d(n) > 2^{(1-ε) log n / log log n}` for
infinitely many `n`. -/
@[kb "apostol1976" "Thm 13.12, p. 294"]
theorem apostol_thm_13_12_b' {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ᶠ n : ℕ in atTop, (2 : ℝ) ^ ((1 - ε) * Real.log n / Real.log (Real.log n)) <
      (n.divisors.card : ℝ) :=
  apostol_thm_13_12_b primeNumberTheoremStatement hε hε1

end NTKB.Apostol
