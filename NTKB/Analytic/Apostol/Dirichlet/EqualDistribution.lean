/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import NTKB.Attr

/-!
# Equal distribution of primes among reduced residue classes (Apostol, Theorem 7.10)

Let `π_a(x)` count the primes `p ≤ x` with `p ≡ a (mod k)`. **Theorem 7.10**: the relation
`π_a(x) ~ π(x)/φ(k)` holds for every `a` prime to `k` iff `π_a(x) ~ π_b(x)` for all `a, b` prime
to `k`.

Apostol's proof: `π(x) = A(x) + ∑_{(a,k)=1} π_a(x)`, where `A(x) ≤ k + 1` counts the primes
`p ≤ x` dividing `k`; divide by `π_b(x) → ∞` (Dirichlet's theorem; Mathlib's
`Nat.forall_exists_prime_gt_and_eq_mod`).
-/

open Finset Filter Topology Asymptotics

namespace NTKB.Apostol

/-- `π_a(x)`: the number of primes `p ≤ x` with `p ≡ a (mod k)`. -/
noncomputable def primeCountAP (k : ℕ) (a : ZMod k) (x : ℕ) : ℕ :=
  #((Nat.primesLE x).filter fun p : ℕ => (p : ZMod k) = a)

lemma primeCountAP_mono (k : ℕ) (a : ZMod k) : Monotone (primeCountAP k a) := by
  intro x y hxy
  refine card_le_card (filter_subset_filter _ fun p hp => ?_)
  rw [Nat.mem_primesLE] at hp ⊢
  exact ⟨hp.1.trans hxy, hp.2⟩

/-- `π_a(x) → ∞` for `a` prime to `k` (Dirichlet's theorem). -/
lemma tendsto_primeCountAP {k : ℕ} [NeZero k] (u : (ZMod k)ˣ) :
    Tendsto (primeCountAP k u) atTop atTop := by
  refine (primeCountAP_mono k u).tendsto_atTop_atTop fun M => ?_
  induction M with
  | zero => exact ⟨0, Nat.zero_le _⟩
  | succ M ih =>
    obtain ⟨X, hX⟩ := ih
    obtain ⟨p, hpX, hp, hpu⟩ := Nat.forall_exists_prime_gt_and_eq_mod u.isUnit X
    refine ⟨p, ?_⟩
    have hsub : insert p ((Nat.primesLE X).filter fun q : ℕ => (q : ZMod k) = u) ⊆
        (Nat.primesLE p).filter fun q : ℕ => (q : ZMod k) = u := by
      intro q hq
      rcases mem_insert.mp hq with rfl | hq
      · exact mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨le_rfl, hp⟩, hpu⟩
      · obtain ⟨hq1, hq2⟩ := mem_filter.mp hq
        rw [Nat.mem_primesLE] at hq1
        exact mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨hq1.1.trans hpX.le, hq1.2⟩, hq2⟩
    have hnot : p ∉ (Nat.primesLE X).filter fun q : ℕ => (q : ZMod k) = u := fun h =>
      absurd (Nat.mem_primesLE.mp (mem_filter.mp h).1).1 (not_le.mpr hpX)
    have := card_le_card hsub
    rw [card_insert_of_notMem hnot] at this
    simp only [primeCountAP] at hX ⊢
    omega

/-- `π(x) = A(x) + ∑_{(a,k)=1} π_a(x)` with `A(x) ≤ k + 1`. -/
lemma primeCounting_eq_add_sum {k : ℕ} [NeZero k] (x : ℕ) :
    ∃ A : ℕ, A ≤ k + 1 ∧ Nat.primeCounting x = A + ∑ u : (ZMod k)ˣ, primeCountAP k u x := by
  classical
  set s := Nat.primesLE x
  refine ⟨#(s.filter fun p : ℕ => ¬ IsUnit (p : ZMod k)), ?_, ?_⟩
  · refine (card_le_card (show s.filter (fun p : ℕ => ¬ IsUnit (p : ZMod k)) ⊆ range (k + 1) from
      fun p hp => ?_)).trans (card_range _).le
    obtain ⟨hp1, hp2⟩ := mem_filter.mp hp
    have hpr := (Nat.mem_primesLE.mp hp1).2
    rw [ZMod.isUnit_iff_coprime, Nat.Prime.coprime_iff_not_dvd hpr, not_not] at hp2
    exact mem_range.mpr (Nat.lt_succ_of_le (Nat.le_of_dvd (NeZero.pos k) hp2))
  · rw [← Nat.primesLE_card_eq_primeCounting, ← card_filter_add_card_filter_not
      (fun p : ℕ => IsUnit (p : ZMod k)), add_comm]
    congr 1
    rw [card_eq_sum_card_fiberwise (f := fun p : ℕ => (p : ZMod k))
      (t := (univ : Finset (ZMod k)ˣ).map ⟨Units.val, Units.val_injective⟩)
      (fun p hp => by
        obtain ⟨u, hu⟩ := (mem_filter.mp hp).2
        exact mem_map.mpr ⟨u, mem_univ _, hu⟩), sum_map]
    refine sum_congr rfl fun u _ => ?_
    simp only [primeCountAP, filter_filter, Function.Embedding.coeFn_mk]
    congr 1
    ext p
    simp only [mem_filter]
    constructor
    · rintro ⟨h1, -, h2⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, h2 ▸ u.isUnit, h2⟩

/-- **Theorem 7.10**: `π_a(x) ~ π(x)/φ(k)` for every `a` prime to `k` iff `π_a(x) ~ π_b(x)` for all
`a, b` prime to `k` (`k ≥ 1`). -/
@[kb "apostol1976" "Thm 7.10, p. 154"]
theorem apostol_thm_7_10 {k : ℕ} [NeZero k] :
    (∀ a : (ZMod k)ˣ, (fun x : ℕ => (primeCountAP k a x : ℝ)) ~[atTop]
        fun x => (Nat.primeCounting x : ℝ) / k.totient) ↔
      ∀ a b : (ZMod k)ˣ, (fun x : ℕ => (primeCountAP k a x : ℝ)) ~[atTop]
        fun x => (primeCountAP k b x : ℝ) := by
  constructor
  · intro h a b
    exact (h a).trans (h b).symm
  · intro h b
    have hφ : (k.totient : ℝ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos k)).ne'
    have hb : Tendsto (fun x : ℕ => (primeCountAP k b x : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp (tendsto_primeCountAP b)
    have hbpos : ∀ᶠ x : ℕ in atTop, (0 : ℝ) < primeCountAP k b x := hb.eventually_gt_atTop 0
    -- `π(x)/π_b(x) → φ(k)`
    have hsum : Tendsto (fun x : ℕ => ∑ u : (ZMod k)ˣ, (primeCountAP k u x : ℝ) /
        primeCountAP k b x) atTop (𝓝 (∑ _u : (ZMod k)ˣ, (1 : ℝ))) := by
      refine tendsto_finsetSum _ fun u _ => ?_
      have := (isEquivalent_iff_tendsto_one (hbpos.mono fun x hx => hx.ne')).mp (h u b)
      exact this
    rw [sum_const, card_univ, ZMod.card_units_eq_totient, nsmul_eq_mul, mul_one] at hsum
    have hA : Tendsto (fun x : ℕ => ((Nat.primeCounting x : ℝ) - ∑ u : (ZMod k)ˣ,
        (primeCountAP k u x : ℝ)) / primeCountAP k b x) atTop (𝓝 0) := by
      have hK : Tendsto (fun x : ℕ => ((k : ℝ) + 1) / primeCountAP k b x) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop hb
      refine squeeze_zero_norm' ?_ hK
      filter_upwards [hbpos] with x hx
      obtain ⟨A, hAk, hAx⟩ := primeCounting_eq_add_sum (k := k) x
      rw [hAx, Real.norm_eq_abs]
      push_cast
      rw [add_sub_cancel_right, abs_div, abs_of_nonneg (by positivity), abs_of_pos hx]
      gcongr
      exact_mod_cast hAk
    have hratio : Tendsto (fun x : ℕ => (Nat.primeCounting x : ℝ) / primeCountAP k b x) atTop
        (𝓝 (k.totient : ℝ)) := by
      have := hA.add hsum
      rw [zero_add] at this
      refine this.congr' ?_
      filter_upwards [hbpos] with x hx
      rw [← sum_div, ← add_div, sub_add_cancel]
    refine isEquivalent_of_tendsto_one ?_
    have h1 : Tendsto (fun x : ℕ => (k.totient : ℝ) / ((Nat.primeCounting x : ℝ) /
        primeCountAP k b x)) atTop (𝓝 ((k.totient : ℝ) / k.totient)) :=
      tendsto_const_nhds.div hratio hφ
    rw [div_self hφ] at h1
    refine h1.congr' ?_
    filter_upwards [hbpos] with x hx
    simp only [Pi.div_apply]
    rw [div_div_eq_mul_div, div_div_eq_mul_div, mul_comm]

end NTKB.Apostol
