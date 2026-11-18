/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
The argument follows Tau Ceti (`TauCeti/NumberTheory/SelbergSieve/Bounds.lean`, main `0642eae2`,
Apache 2.0, Arend Mellendijk and the Tau Ceti contributors), itself adapted from Arend Mellendijk's
PrimeNumberTheoremAnd `SelbergBounds.lean`. No Tau Ceti code is copied; NTKB does not depend on
Tau Ceti.
-/
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Data.Nat.Totient
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.NumberTheory.EulerProduct.Basic
import NTKB.Attr

/-!
# `log z ≤ ∑_{q ≤ z} μ(q)²/φ(q)` (after Tau Ceti)

The special case (density `1/p` on every prime `≤ z`, where `selbergTerms d = μ(d)²/φ(d)`) of Tau
Ceti's `BoundingSieve.log_le_sum_selbergTerms` (https://github.com/TauCetiProject/TauCeti, main
0642eae2, `TauCeti/NumberTheory/SelbergSieve/Bounds.lean`), by the same argument with a shorter
proof through Mathlib's Euler products
(`EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum`). Every `m ≤ z` is
`m = d k` with `d` the squarefree kernel of `m` and the prime factors of `k` dividing `d`, and the
finite sums of `1/(d k)` over such `k` are at most `1/φ(d)`, so
`∑_{m ≤ z} 1/m ≤ ∑_{d ≤ z} μ(d)²/φ(d)`; and `log z ≤ ∑_{m ≤ z} 1/m`
(Mathlib `log_le_harmonic_floor`).
-/

open Finset
open scoped ArithmeticFunction.Moebius

namespace NTKB.Port.SelbergBounds

/-- Partial sums of `∑ 1/k` over `s`-factored numbers are bounded by the Euler product
(Tau Ceti's `EulerProduct` helper, via Mathlib's `EulerProduct`). -/
private lemma sum_inv_le_prod (s : Finset ℕ) (T : Finset ℕ)
    (hT : ∀ k ∈ T, k ≠ 0 ∧ k.primeFactors ⊆ s) :
    ∑ k ∈ T, (k : ℝ)⁻¹ ≤ ∏ p ∈ s with p.Prime, (1 - (p : ℝ)⁻¹)⁻¹ := by
  classical
  let f : ℕ →*₀ ℝ :=
    { toFun := fun n => (n : ℝ)⁻¹
      map_zero' := by simp
      map_one' := by simp
      map_mul' := fun a b => by simp [mul_comm] }
  have hgeom : ∀ {p : ℕ}, p.Prime → ∑' n : ℕ, f (p ^ n) = (1 - (p : ℝ)⁻¹)⁻¹ := by
    intro p hp
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    have : ∀ n : ℕ, f (p ^ n) = ((p : ℝ)⁻¹) ^ n := fun n => by simp [f]
    simp only [this]
    exact tsum_geometric_of_lt_one (by positivity) (inv_lt_one_of_one_lt₀ hp1)
  have hsum : ∀ {p : ℕ}, p.Prime → Summable (fun n : ℕ ↦ ‖f (p ^ n)‖) := by
    intro p hp
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    have : ∀ n : ℕ, ‖f (p ^ n)‖ = ((p : ℝ)⁻¹) ^ n := fun n => by simp [f]
    simp only [this]
    exact summable_geometric_of_lt_one (by positivity) (inv_lt_one_of_one_lt₀ hp1)
  obtain ⟨_, hs⟩ := EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum
    (f := f) f.map_one (fun {m n} _ => f.map_mul m n) hsum s
  have hs' : HasSum (fun m : Nat.factoredNumbers s ↦ f m)
      (∏ p ∈ s with p.Prime, (1 - (p : ℝ)⁻¹)⁻¹) := by
    convert hs using 1
    exact (Finset.prod_congr rfl fun p hp => (hgeom (Finset.mem_filter.mp hp).2).symm)
  have hmem : ∀ k ∈ T, k ∈ Nat.factoredNumbers s := fun k hk =>
    Nat.mem_factoredNumbers_of_primeFactors_subset (hT k hk).1 (hT k hk).2
  have h1 := sum_le_hasSum (T.subtype (· ∈ Nat.factoredNumbers s))
    (fun x _ => by simp [f]) hs'
  rwa [Finset.sum_subtype_of_mem (fun k => f k) hmem] at h1

lemma totient_eq_prod_sub_one {d : ℕ} (hd : Squarefree d) :
    (d.totient : ℝ) = ∏ p ∈ d.primeFactors, ((p : ℝ) - 1) := by
  have h := Nat.totient_mul_prod_primeFactors d
  rw [Nat.prod_primeFactors_of_squarefree hd] at h
  have hd0 : d ≠ 0 := hd.ne_zero
  have h2 : d.totient = ∏ p ∈ d.primeFactors, (p - 1) := Nat.eq_of_mul_eq_mul_left
    (Nat.pos_of_ne_zero hd0) (by rw [mul_comm] at h; exact h)
  rw [h2, Nat.cast_prod]
  refine Finset.prod_congr rfl fun p hp => ?_
  rw [Nat.cast_sub (Nat.prime_of_mem_primeFactors hp).one_lt.le]; simp

private lemma fiber_bound {d : ℕ} (hd : Squarefree d) (n : ℕ) :
    ∑ m ∈ (Icc 1 n).filter (fun m => UniqueFactorizationMonoid.radical m = d), (m : ℝ)⁻¹ ≤
      (d.totient : ℝ)⁻¹ := by
  classical
  set F := (Icc 1 n).filter (fun m => UniqueFactorizationMonoid.radical m = d) with hF
  have hd0 : d ≠ 0 := hd.ne_zero
  have hdvd : ∀ m ∈ F, d ∣ m := fun m hm => by
    rw [← (Finset.mem_filter.mp hm).2]; exact UniqueFactorizationMonoid.radical_dvd_self
  have hm0 : ∀ m ∈ F, m ≠ 0 := fun m hm => by
    have := (Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1).1; omega
  have hpf : ∀ m ∈ F, m.primeFactors = d.primeFactors := fun m hm => by
    rw [← (Finset.mem_filter.mp hm).2, Nat.primeFactors_radical]
  have hinj : Set.InjOn (fun m => m / d) (F : Set ℕ) := fun a ha b hb hab => by
    have h1 := Nat.mul_div_cancel' (hdvd a ha)
    have h2 := Nat.mul_div_cancel' (hdvd b hb)
    simp only at hab
    rw [← h1, ← h2, hab]
  have hsum : ∑ m ∈ F, (m : ℝ)⁻¹ = (d : ℝ)⁻¹ * ∑ k ∈ F.image (· / d), (k : ℝ)⁻¹ := by
    rw [Finset.sum_image hinj, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    have h1 := Nat.mul_div_cancel' (hdvd m hm)
    conv_lhs => rw [← h1]
    push_cast
    rw [mul_inv]
  have hT : ∀ k ∈ F.image (· / d), k ≠ 0 ∧ k.primeFactors ⊆ d.primeFactors := by
    intro k hk
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hk
    have h1 := Nat.mul_div_cancel' (hdvd m hm)
    have hk0 : m / d ≠ 0 := fun h => hm0 m hm (by rw [← h1, h, mul_zero])
    refine ⟨hk0, ?_⟩
    rw [← hpf m hm]
    exact Nat.primeFactors_mono (Nat.div_dvd_of_dvd (hdvd m hm)) (hm0 m hm)
  have hb := sum_inv_le_prod d.primeFactors _ hT
  have hfilt : (d.primeFactors.filter Nat.Prime) = d.primeFactors :=
    Finset.filter_true_of_mem fun p hp => Nat.prime_of_mem_primeFactors hp
  rw [hfilt] at hb
  have hprod : ∏ p ∈ d.primeFactors, (1 - (p : ℝ)⁻¹)⁻¹ = (d : ℝ) * (d.totient : ℝ)⁻¹ := by
    rw [totient_eq_prod_sub_one hd]
    have hdR : (d : ℝ) = ∏ p ∈ d.primeFactors, (p : ℝ) := by
      rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hd]
    rw [hdR, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun p hp => ?_
    have hp1 : (1 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
    have : (p : ℝ) - 1 ≠ 0 := by linarith
    have : (p : ℝ) ≠ 0 := by linarith
    field_simp
  rw [hsum]
  calc (d : ℝ)⁻¹ * ∑ k ∈ F.image (· / d), (k : ℝ)⁻¹
      ≤ (d : ℝ)⁻¹ * ((d : ℝ) * (d.totient : ℝ)⁻¹) := by
        rw [← hprod]; gcongr
    _ = (d.totient : ℝ)⁻¹ := by
        have : (d : ℝ) ≠ 0 := by exact_mod_cast hd0
        field_simp

/-- `∑_{m ≤ z} 1/m ≤ ∑_{q ≤ z} μ(q)²/φ(q)`. -/
theorem sum_inv_le_sum_moebius_sq_div_totient (z : ℝ) :
    ∑ m ∈ Icc 1 ⌊z⌋₊, (m : ℝ)⁻¹ ≤ ∑ q ∈ Icc 1 ⌊z⌋₊, ((μ q : ℤ) : ℝ) ^ 2 / (q.totient : ℝ) := by
  classical
  have hmaps : ∀ m ∈ Icc 1 ⌊z⌋₊, UniqueFactorizationMonoid.radical m ∈ Icc 1 ⌊z⌋₊ := by
    intro m hm
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hm
    exact Finset.mem_Icc.mpr ⟨Nat.radical_pos m,
      (Nat.radical_le_self_iff.mpr (by omega)).trans h2⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_le_sum fun d _ => ?_
  by_cases hd : Squarefree d
  · have : ((μ d : ℤ) : ℝ) ^ 2 = 1 := by
      have h0 := ArithmeticFunction.moebius_ne_zero_iff_squarefree.mpr hd
      rcases ArithmeticFunction.moebius_eq_or d with h | h | h
      · exact absurd h h0
      · simp [h]
      · simp [h]
    rw [this]
    simpa using fiber_bound hd _
  · have : (Finset.filter (fun m => UniqueFactorizationMonoid.radical m = d) (Icc 1 ⌊z⌋₊)) = ∅ := by
      refine Finset.filter_eq_empty_iff.mpr fun m _ h => hd ?_
      rw [← h]; exact UniqueFactorizationMonoid.squarefree_radical
    rw [this]; simp only [Finset.sum_empty]
    positivity

/-- `log z ≤ ∑_{q ≤ z} μ(q)²/φ(q)` for `z ≥ 0`. -/
theorem log_le_sum_moebius_sq_div_totient {z : ℝ} (hz : 0 ≤ z) :
    Real.log z ≤ ∑ q ∈ Icc 1 ⌊z⌋₊, ((μ q : ℤ) : ℝ) ^ 2 / (q.totient : ℝ) := by
  refine le_trans ?_ (sum_inv_le_sum_moebius_sq_div_totient z)
  have h := log_le_harmonic_floor z hz
  have h2 : ((harmonic ⌊z⌋₊ : ℚ) : ℝ) = ∑ m ∈ Icc 1 ⌊z⌋₊, (m : ℝ)⁻¹ := by
    rw [harmonic_eq_sum_Icc]; push_cast; rfl
  rwa [h2] at h

end NTKB.Port.SelbergBounds
