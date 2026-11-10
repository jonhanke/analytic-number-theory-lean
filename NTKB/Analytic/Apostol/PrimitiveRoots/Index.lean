/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import NTKB.Attr

/-!
# Indices with respect to a primitive root (Apostol, Chapter 10, §10.10, Theorem 10.10)

For a primitive root `g` mod `m` (a unit of `ZMod m` of order `φ(m)`) and a unit `a`, the index
`ind_g a` is the least `k ≥ 0` with `g^k = a` (`NTKB.Apostol.ind`; Mathlib has no discrete
logarithm). Theorem 10.10:
(a) `ind(ab) ≡ ind a + ind b (mod φ(m))`; (b) `ind aⁿ ≡ n ind a (mod φ(m))`;
(c) `ind 1 = 0` and `ind g ≡ 1 (mod φ(m))` (equal to `1` when `m > 2`);
(d) `ind(-1) = φ(m)/2` if `m > 2`; (e) for another primitive root `g'`,
`ind_g a ≡ ind_{g'} a · ind_g g' (mod φ(m))`.
-/

namespace NTKB.Apostol

variable {m : ℕ}

/-- `g` is a primitive root mod `m`: its order in `(ZMod m)ˣ` is `φ(m)` (Apostol, §10.1). -/
def IsPrimitiveRootMod (m : ℕ) (g : (ZMod m)ˣ) : Prop := orderOf g = m.totient

theorem IsPrimitiveRootMod.exists_pow_eq [NeZero m] {g : (ZMod m)ˣ} (hg : IsPrimitiveRootMod m g)
    (a : (ZMod m)ˣ) : ∃ k : ℕ, g ^ k = a := by
  have hcard : orderOf g = Nat.card (ZMod m)ˣ := by
    rw [hg, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
  have htop : Subgroup.zpowers g = ⊤ :=
    Subgroup.eq_top_of_card_eq _ (by rw [Nat.card_zpowers, hcard])
  have hz : a ∈ Subgroup.zpowers g := htop ▸ Subgroup.mem_top a
  rw [← mem_powers_iff_mem_zpowers] at hz
  obtain ⟨k, hk⟩ := hz
  exact ⟨k, hk⟩

open Classical in
/-- The index `ind_g a`: the least `k ≥ 0` with `g^k = a` (Apostol, §10.10). -/
noncomputable def ind [NeZero m] {g : (ZMod m)ˣ} (hg : IsPrimitiveRootMod m g)
    (a : (ZMod m)ˣ) : ℕ :=
  Nat.find (hg.exists_pow_eq a)

variable [NeZero m] {g : (ZMod m)ˣ} (hg : IsPrimitiveRootMod m g)
include hg

theorem pow_ind (a : (ZMod m)ˣ) : g ^ ind hg a = a := by
  classical
  exact Nat.find_spec (hg.exists_pow_eq a)

theorem ind_lt_totient (a : (ZMod m)ˣ) : ind hg a < m.totient := by
  classical
  have hpos : 0 < orderOf g := orderOf_pos g
  have : g ^ (ind hg a % orderOf g) = a := by rw [pow_mod_orderOf, pow_ind]
  calc ind hg a ≤ ind hg a % orderOf g := Nat.find_min' _ this
    _ < orderOf g := Nat.mod_lt _ hpos
    _ = m.totient := hg

theorem pow_eq_iff_modEq_ind {a : (ZMod m)ˣ} {k : ℕ} :
    g ^ k = a ↔ k ≡ ind hg a [MOD m.totient] := by
  rw [← hg, ← pow_eq_pow_iff_modEq, pow_ind]

/-- **Apostol, Theorem 10.10 (a).** `ind(ab) ≡ ind a + ind b (mod φ(m))`. -/
@[kb "apostol1976" "Thm 10.10(a), p. 214"]
theorem ind_mul (a b : (ZMod m)ˣ) :
    ind hg (a * b) ≡ ind hg a + ind hg b [MOD m.totient] := by
  have : g ^ (ind hg a + ind hg b) = a * b := by rw [pow_add, pow_ind, pow_ind]
  exact ((pow_eq_iff_modEq_ind hg).1 this).symm

/-- **Apostol, Theorem 10.10 (b).** `ind aⁿ ≡ n ind a (mod φ(m))`. -/
@[kb "apostol1976" "Thm 10.10(b), p. 214"]
theorem ind_pow (a : (ZMod m)ˣ) (n : ℕ) :
    ind hg (a ^ n) ≡ n * ind hg a [MOD m.totient] := by
  have : g ^ (n * ind hg a) = a ^ n := by rw [mul_comm, pow_mul, pow_ind]
  exact ((pow_eq_iff_modEq_ind hg).1 this).symm

/-- **Apostol, Theorem 10.10 (c).** `ind 1 = 0` and `ind g ≡ 1 (mod φ(m))`. -/
@[kb "apostol1976" "Thm 10.10(c), p. 214"]
theorem ind_one_and_ind_self : ind hg 1 = 0 ∧ ind hg g ≡ 1 [MOD m.totient] := by
  classical
  refine ⟨?_, ((pow_eq_iff_modEq_ind hg).1 (pow_one g)).symm⟩
  exact (Nat.find_eq_zero _).2 (pow_zero g)

/-- `ind g = 1` when `m > 2` (then `φ(m) ≥ 2`). -/
theorem ind_self_of_two_lt (hm : 2 < m) : ind hg g = 1 := by
  have h2 : 2 ≤ m.totient := by
    rcases Nat.totient_even hm with ⟨r, hr⟩
    have := Nat.totient_pos.2 (by omega : 0 < m)
    omega
  have h := (ind_one_and_ind_self hg).2
  have hlt := ind_lt_totient hg g
  rw [Nat.ModEq, Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt (by omega)] at h
  exact h

/-- **Apostol, Theorem 10.10 (d).** `ind(-1) = φ(m)/2` if `m > 2`. -/
@[kb "apostol1976" "Thm 10.10(d), p. 214"]
theorem ind_neg_one (hm : 2 < m) : ind hg (-1) = m.totient / 2 := by
  have hne : (-1 : (ZMod m)ˣ) ≠ 1 := by
    intro h
    have h' := congrArg (fun u : (ZMod m)ˣ ↦ (u : ZMod m)) h
    simp only [Units.val_neg, Units.val_one] at h'
    have : Fact (2 < m) := ⟨hm⟩
    exact ZMod.neg_one_ne_one h'
  set k := ind hg (-1)
  have hk : g ^ k = -1 := pow_ind hg (-1)
  have hklt : k < m.totient := ind_lt_totient hg (-1)
  -- `g^(2k) = 1`, so `φ(m) ∣ 2k`
  have h2k : m.totient ∣ 2 * k := by
    rw [← hg, orderOf_dvd_iff_pow_eq_one, mul_comm, pow_mul, hk]
    simp
  have hk0 : k ≠ 0 := by
    intro h0
    rw [h0, pow_zero] at hk
    exact hne hk.symm
  obtain ⟨c, hc⟩ := h2k
  have hφpos : 0 < m.totient := Nat.totient_pos.2 (by omega)
  have hc1 : c = 1 := by
    rcases Nat.lt_or_ge c 2 with h | h
    · interval_cases c
      · omega
      · rfl
    · nlinarith
  rw [hc1, mul_one] at hc
  omega

/-- **Apostol, Theorem 10.10 (e)** (change of base). If `g'` is another primitive root,
`ind_g a ≡ ind_{g'} a · ind_g g' (mod φ(m))`. -/
@[kb "apostol1976" "Thm 10.10(e), p. 214"]
theorem ind_change_base {g' : (ZMod m)ˣ} (hg' : IsPrimitiveRootMod m g') (a : (ZMod m)ˣ) :
    ind hg a ≡ ind hg' a * ind hg g' [MOD m.totient] := by
  have : g ^ (ind hg' a * ind hg g') = a := by
    rw [mul_comm, pow_mul, pow_ind, pow_ind]
  exact ((pow_eq_iff_modEq_ind hg).1 this).symm

end NTKB.Apostol
