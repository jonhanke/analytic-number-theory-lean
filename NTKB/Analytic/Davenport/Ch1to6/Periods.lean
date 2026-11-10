/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Subgroup
import NTKB.Analytic.Apostol.GaussSums.Quadratic
import NTKB.Analytic.Davenport.Ch1to6.LOneOdd

/-!
# Davenport, Chapter 3: Gaussian periods

Let `q` be an odd prime, `g` a primitive root modulo `q` and `ν(n)` the index of `n` relative to
`g` (`NTKB.Davenport.index`: the least `i ≥ 0` with `g^i = n`). For `q - 1 = e f` the **Gaussian
periods** of `f` terms are
$$\eta_j = \sum_{\substack{1\le n\le q-1\\ \nu(n)\equiv j \ (\mathrm{mod}\ e)}} \zeta^n$$
for a `q`-th root of unity `ζ` (`NTKB.Davenport.gaussianPeriod`; the sum runs over the units of
`ℤ/q`, `n` being represented by `0 < n < q`).

* `η_j` is periodic in `j` with period `e`, and `η_0 + ⋯ + η_{e-1} = -1` for primitive `ζ`.
* `η_j = ∑_{k < f} ζ^{g^{j + e k}}` (the `f` terms of a period).
* For `ζ = e(1/q)`: `η_0 = (1/e)(∑_{x=0}^{q-1} e(x^e/q) - 1)`.
* For `e = 2`: `η_0 = ∑ ζ^R`, `η_1 = ∑ ζ^N` (residues and nonresidues), `η_0 + η_1 = -1`,
  `η_0 - η_1 = ∑ (m/q) ζ^m`, and for `ζ = e(1/q)`: `η_0, η_1 = (-1 ± ε √q)/2`, `ε = 1` or `i`
  according as `q ≡ 1` or `3 (mod 4)` (Gauss's sum).
-/

noncomputable section

open Finset Complex
open scoped Real

namespace NTKB.Davenport

variable {q : ℕ} [Fact q.Prime]

/-! ### The index relative to a primitive root -/

open Classical in
/-- The **index** `ν(n)` of a unit `n` modulo `q` relative to `g`: the least `i ≥ 0` with
`g^i = n` (`0` if there is none, which does not happen when `g` is a primitive root). -/
def index (g n : (ZMod q)ˣ) : ℕ := if h : ∃ i : ℕ, g ^ i = n then Nat.find h else 0

section Index

variable {g : (ZMod q)ˣ} (hg : ∀ x, x ∈ Subgroup.zpowers g)
include hg

theorem exists_pow_eq (n : (ZMod q)ˣ) : ∃ i : ℕ, g ^ i = n :=
  mem_powers_iff_mem_zpowers.mpr (hg n)

theorem pow_index (n : (ZMod q)ˣ) : g ^ index g n = n := by
  classical
  have h := exists_pow_eq hg n
  rw [index, dif_pos h]
  exact Nat.find_spec h

theorem orderOf_eq_card : orderOf g = q - 1 := by
  rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, ZMod.card_units]

omit hg in
theorem one_le_card_sub_one : 1 ≤ q - 1 := by
  have := (Fact.out : q.Prime).two_le; omega

theorem index_lt (n : (ZMod q)ˣ) : index g n < q - 1 := by
  classical
  have h := exists_pow_eq hg n
  have hlt : index g n % (q - 1) < q - 1 := Nat.mod_lt _ (one_le_card_sub_one (q := q))
  have hpow : g ^ (index g n % (q - 1)) = n := by
    rw [← orderOf_eq_card hg, pow_mod_orderOf, pow_index hg]
  have key : ∀ i, g ^ i = n → index g n ≤ i := by
    intro i hi; rw [index, dif_pos h]; exact Nat.find_min' h hi
  exact lt_of_le_of_lt (key _ hpow) hlt

theorem index_pow (i : ℕ) : index g (g ^ i) = i % (q - 1) := by
  have h1 : g ^ index g (g ^ i) = g ^ i := pow_index hg _
  rw [pow_eq_pow_iff_modEq, orderOf_eq_card hg] at h1
  rw [← h1, Nat.mod_eq_of_lt (index_lt hg _)]

end Index

/-! ### Gaussian periods -/

/-- The **Gaussian period** `η_j = ∑_{1 ≤ n ≤ q-1, ν(n) ≡ j (mod e)} ζ^n` (Davenport §3), the sum
running over the units `n` of `ℤ/q`, represented by `0 < n < q`. -/
def gaussianPeriod {R : Type*} [CommRing R] (g : (ZMod q)ˣ) (e j : ℕ) (ζ : R) : R :=
  ∑ n : (ZMod q)ˣ with index g n ≡ j [MOD e], ζ ^ (n : ZMod q).val

variable {R : Type*} [CommRing R]

/-- **Davenport §3, p. 18.** `η_j` is periodic in `j` with period `e`. -/
@[kb "davenport1980" "Ch 3, p. 18"]
theorem gaussianPeriod_add (g : (ZMod q)ˣ) (e j : ℕ) (ζ : R) :
    gaussianPeriod g e (j + e) ζ = gaussianPeriod g e j ζ := by
  unfold gaussianPeriod
  refine sum_congr (filter_congr fun n _ ↦ ?_) fun _ _ ↦ rfl
  simp only [Nat.ModEq, Nat.add_mod_right]

/-- `∑_{x mod q} F(x) = F(0) + ∑_{u unit} F(u)`. -/
theorem sum_zmod_eq_add_sum_units {M : Type*} [AddCommMonoid M] (F : ZMod q → M) :
    ∑ x, F x = F 0 + ∑ u : (ZMod q)ˣ, F u := by
  rw [← Finset.add_sum_erase (s := univ) (f := F) (mem_univ (0 : ZMod q))]
  congr 1
  refine (Finset.sum_bij (s := (univ : Finset (ZMod q)ˣ)) (t := univ.erase (0 : ZMod q))
    (f := fun u ↦ F u) (g := F) (fun u _ ↦ (u : ZMod q)) ?_ ?_ ?_ ?_).symm
  · intro u _; simp [Units.ne_zero]
  · intro a _ b _ h; exact Units.ext h
  · intro x hx
    exact ⟨Units.mk0 x (Finset.mem_erase.mp hx).1, mem_univ _, rfl⟩
  · intro _ _; rfl

/-- For a primitive `q`-th root of unity, `∑_{n=1}^{q-1} ζ^n = -1`. -/
theorem sum_units_pow_val {R : Type*} [CommRing R] [IsDomain R] {ζ : R}
    (hζ : IsPrimitiveRoot ζ q) : ∑ u : (ZMod q)ˣ, ζ ^ (u : ZMod q).val = -1 := by
  have h := hζ.geom_sum_eq_zero (Fact.out : q.Prime).one_lt
  rw [← sum_val_eq_sum_range (fun m ↦ ζ ^ m), sum_zmod_eq_add_sum_units] at h
  rw [ZMod.val_zero, pow_zero] at h
  exact eq_neg_of_add_eq_zero_right h

/-- **Davenport §3, p. 18.** The `e` periods of `f` terms add up to `-1`: every root `ζ^n`,
`1 ≤ n ≤ q-1`, lies in exactly one class `ν(n) mod e`. -/
@[kb "davenport1980" "Ch 3, p. 18"]
theorem sum_gaussianPeriod {R : Type*} [CommRing R] [IsDomain R] (g : (ZMod q)ˣ) {e : ℕ}
    (he : 0 < e) {ζ : R} (hζ : IsPrimitiveRoot ζ q) :
    ∑ j ∈ range e, gaussianPeriod g e j ζ = -1 := by
  rw [← sum_units_pow_val hζ, ← Finset.sum_fiberwise_of_maps_to
    (g := fun n : (ZMod q)ˣ ↦ index g n % e) (t := range e)
    (fun n _ ↦ mem_range.mpr (Nat.mod_lt _ he))]
  refine sum_congr rfl fun j hj ↦ ?_
  unfold gaussianPeriod
  congr 1
  ext n
  simp only [mem_filter, mem_univ, true_and, Nat.ModEq, Nat.mod_eq_of_lt (mem_range.mp hj)]

section Generator

variable {g : (ZMod q)ˣ} (hg : ∀ x, x ∈ Subgroup.zpowers g)
include hg

/-- A sum over the units as a sum over the powers `g^i`, `0 ≤ i < q - 1`. -/
theorem sum_units_eq_sum_range {M : Type*} [AddCommMonoid M] (F : (ZMod q)ˣ → M) :
    ∑ u : (ZMod q)ˣ, F u = ∑ i ∈ range (q - 1), F (g ^ i) := by
  refine Finset.sum_nbij' (fun u ↦ index g u) (fun i ↦ g ^ i) ?_ ?_ ?_ ?_ ?_
  · intro u _; exact mem_range.mpr (index_lt hg u)
  · intro _ _; exact mem_univ _
  · intro u _; exact pow_index hg u
  · intro i hi
    rw [index_pow hg, Nat.mod_eq_of_lt (mem_range.mp hi)]
  · intro u _; rw [pow_index hg]

/-- **The `f` terms of a period** (Davenport §3, p. 18): for `q - 1 = e f`,
`∑_{ν(n) ≡ j (mod e)} F(n) = ∑_{k < f} F(g^{j' + e k})` with `j' = j mod e`. -/
theorem sum_index_modEq_eq_sum_range {M : Type*} [AddCommMonoid M] {e f : ℕ} (hef : q - 1 = e * f)
    (j : ℕ) (F : (ZMod q)ˣ → M) :
    ∑ n : (ZMod q)ˣ with index g n ≡ j [MOD e], F n =
      ∑ k ∈ range f, F (g ^ (j % e + e * k)) := by
  have he : 0 < e := by
    rcases Nat.eq_zero_or_pos e with h | h
    · have := one_le_card_sub_one (q := q); rw [hef, h, zero_mul] at this; omega
    · exact h
  have hlt : ∀ k < f, j % e + e * k < q - 1 := by
    intro k hk
    have h1 : j % e < e := Nat.mod_lt _ he
    have h2 : e * k + e ≤ e * f := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hk
    omega
  refine Finset.sum_nbij' (fun n ↦ index g n / e) (fun k ↦ g ^ (j % e + e * k)) ?_ ?_ ?_ ?_ ?_
  · intro n _
    refine mem_range.mpr ?_
    rw [Nat.div_lt_iff_lt_mul he, mul_comm, ← hef]
    exact index_lt hg n
  · intro k hk
    have hk' := mem_range.mp hk
    simp only [mem_filter, mem_univ, true_and]
    rw [index_pow hg, Nat.mod_eq_of_lt (hlt k hk'), Nat.ModEq, Nat.add_mul_mod_self_left,
      Nat.mod_mod]
  · intro n hn
    have hn' : index g n % e = j % e := (Finset.mem_filter.mp hn).2
    rw [← hn', Nat.mod_add_div, pow_index hg]
  · intro k hk
    have hk' := mem_range.mp hk
    rw [index_pow hg, Nat.mod_eq_of_lt (hlt k hk'), Nat.add_mul_div_left _ _ he,
      Nat.div_eq_of_lt (Nat.mod_lt _ he), zero_add]
  · intro n hn
    have hn' : index g n % e = j % e := (Finset.mem_filter.mp hn).2
    rw [← hn', Nat.mod_add_div, pow_index hg]

/-- **Davenport §3, p. 18.** `η_j = ∑_{k < f} ζ^{g^{j' + e k}}`, `j' = j mod e`: a period of `f`
terms. -/
@[kb "davenport1980" "Ch 3, p. 18"]
theorem gaussianPeriod_eq_sum_range {e f : ℕ} (hef : q - 1 = e * f) (j : ℕ) (ζ : R) :
    gaussianPeriod g e j ζ =
      ∑ k ∈ range f, ζ ^ ((g ^ (j % e + e * k) : (ZMod q)ˣ) : ZMod q).val :=
  sum_index_modEq_eq_sum_range hg hef j _

/-- `∑_{x unit} ζ^{x^e} = e η_0` for `e ∣ q - 1`: the map `x ↦ x^e` covers each `e`-th power
residue `e` times. -/
theorem sum_units_pow_eq {e f : ℕ} (hef : q - 1 = e * f) (ζ : R) :
    ∑ u : (ZMod q)ˣ, ζ ^ ((u ^ e : (ZMod q)ˣ) : ZMod q).val = e * gaussianPeriod g e 0 ζ := by
  rw [sum_units_eq_sum_range hg, gaussianPeriod_eq_sum_range hg hef, hef,
    NTKB.Apostol.sum_range_mul_eq]
  simp only [Nat.zero_mod, zero_add]
  have hgf : g ^ (e * f) = 1 := by rw [← hef, ← orderOf_eq_card hg, pow_orderOf_eq_one]
  have h : ∀ i ∈ range e, ∑ k ∈ range f, ζ ^ (((g ^ (k + f * i)) ^ e : (ZMod q)ˣ) : ZMod q).val =
      ∑ k ∈ range f, ζ ^ ((g ^ (e * k) : (ZMod q)ˣ) : ZMod q).val := by
    intro i _
    refine sum_congr rfl fun k _ ↦ ?_
    rw [← pow_mul, show (k + f * i) * e = e * k + (e * f) * i by ring, pow_add, pow_mul g (e * f) i,
      hgf, one_pow, mul_one]
  rw [sum_congr rfl h, sum_const, card_range, nsmul_eq_mul]

end Generator

/-! ### The case `ζ = e(1/q)` -/

omit [Fact q.Prime] in
/-- `ζ = e^{2πi/q}`, `ζ^n = e^{2πi n/q}`. -/
theorem cexp_pow (n : ℕ) : cexp (2 * π * I / q) ^ n = cexp (2 * π * I * n / q) := by
  rw [← Complex.exp_nat_mul]; ring_nf

theorem cexp_pow_mod (n : ℕ) : cexp (2 * π * I / q) ^ (n % q) = cexp (2 * π * I / q) ^ n := by
  have hζ : cexp (2 * π * I / q) ^ q = 1 := by
    rw [cexp_pow]
    have hq : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero
    rw [mul_div_assoc, div_self hq, mul_one, Complex.exp_two_pi_mul_I]
  conv_rhs => rw [← Nat.mod_add_div n q, pow_add, pow_mul, hζ, one_pow, mul_one]

/-- **Davenport §3, p. 18.** With `ζ = e(1/q)` and `q - 1 = e f`, the period `η_0` is uniquely
determined: `η_0 = (1/e)(∑_{x=0}^{q-1} e(x^e/q) - 1)`. -/
@[kb "davenport1980" "Ch 3, p. 18"]
theorem gaussianPeriod_zero_eq {g : (ZMod q)ˣ} (hg : ∀ x, x ∈ Subgroup.zpowers g) {e f : ℕ}
    (hef : q - 1 = e * f) :
    gaussianPeriod g e 0 (cexp (2 * π * I / q)) =
      (1 / e : ℂ) * (∑ x ∈ range q, cexp (2 * π * I * (x ^ e : ℕ) / q) - 1) := by
  have he : 0 < e := by
    rcases Nat.eq_zero_or_pos e with h | h
    · have := one_le_card_sub_one (q := q); rw [hef, h, zero_mul] at this; omega
    · exact h
  have hsum : ∑ x ∈ range q, cexp (2 * π * I * (x ^ e : ℕ) / q) =
      1 + e * gaussianPeriod g e 0 (cexp (2 * π * I / q)) := by
    rw [← sum_units_pow_eq hg hef]
    have : ∀ x ∈ range q, cexp (2 * π * I * (x ^ e : ℕ) / q) =
        (fun y : ZMod q ↦ cexp (2 * π * I / q) ^ (y ^ e).val) (x : ZMod q) := by
      intro x _
      simp only
      rw [← Nat.cast_pow, ZMod.val_natCast, cexp_pow_mod, cexp_pow]
    rw [sum_congr rfl this, ← sum_val_eq_sum_range
      (fun x ↦ (fun y : ZMod q ↦ cexp (2 * π * I / q) ^ (y ^ e).val) (x : ZMod q))]
    simp only [ZMod.natCast_zmod_val]
    rw [sum_zmod_eq_add_sum_units, zero_pow he.ne', ZMod.val_zero, pow_zero]
    simp only [Units.val_pow_eq_pow_val]
  rw [hsum]
  have : (e : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr he.ne'
  field_simp
  ring

/-! ### Two periods (`e = 2`) -/

section Quadratic

variable {g : (ZMod q)ˣ} (hg : ∀ x, x ∈ Subgroup.zpowers g)
include hg

/-- The quadratic character of a unit is `(-1)^{ν(n)}` (a primitive root is a nonresidue). -/
theorem quadraticChar_eq_neg_one_pow_index (hq2 : q ≠ 2) (n : (ZMod q)ˣ) :
    quadraticChar (ZMod q) n = (-1) ^ index g n := by
  have hg2 : quadraticChar (ZMod q) g = -1 := by
    rw [quadraticChar_neg_one_iff_not_isSquare]
    rintro ⟨r, hr⟩
    have hr0 : r ≠ 0 := by
      rintro rfl; simp at hr
    set u := Units.mk0 r hr0
    have hgu : g = u ^ 2 := Units.ext (by simp [u, hr, sq])
    have hodd : q % 2 = 1 := Nat.odd_iff.mp ((Fact.out : q.Prime).odd_of_ne_two hq2)
    have h1 : g ^ ((q - 1) / 2) = 1 := by
      rw [hgu, ← pow_mul, show 2 * ((q - 1) / 2) = q - 1 by omega,
        ← ZMod.card_units q, pow_card_eq_one]
    have := orderOf_dvd_of_pow_eq_one h1
    rw [orderOf_eq_card hg] at this
    have hpos : 0 < (q - 1) / 2 := by have := (Fact.out : q.Prime).two_le; omega
    have := Nat.le_of_dvd hpos this
    omega
  conv_lhs => rw [← pow_index hg n]
  rw [Units.val_pow_eq_pow_val, map_pow, hg2]

theorem neg_one_pow_index (hq2 : q ≠ 2) (n : (ZMod q)ˣ) :
    quadraticChar (ZMod q) n = if index g n % 2 = 0 then 1 else -1 := by
  rw [quadraticChar_eq_neg_one_pow_index hg hq2, neg_one_pow_eq_pow_mod_two]
  rcases Nat.mod_two_eq_zero_or_one (index g n) with h | h <;> simp [h]

/-- **Davenport §3, p. 18.** For `e = 2`: `η_0 = ∑ ζ^R` over the quadratic residues `R` and
`η_1 = ∑ ζ^N` over the nonresidues `N` (`1 ≤ R, N ≤ q - 1`). -/
@[kb "davenport1980" "Ch 3, p. 18"]
theorem gaussianPeriod_two_eq (hq2 : q ≠ 2) (j : ℕ) (hj : j < 2) (ζ : R) :
    gaussianPeriod g 2 j ζ =
      ∑ n ∈ (univ : Finset (ZMod q)ˣ).filter
        (fun n : (ZMod q)ˣ ↦ quadraticChar (ZMod q) n = (-1) ^ j), ζ ^ (n : ZMod q).val := by
  unfold gaussianPeriod
  refine sum_congr (filter_congr fun n _ ↦ ?_) fun _ _ ↦ rfl
  rw [Nat.ModEq, neg_one_pow_index hg hq2, Nat.mod_eq_of_lt hj]
  rcases Nat.mod_two_eq_zero_or_one (index g n) with h | h <;>
    rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl <;> simp [h]

/-- **Davenport §3, p. 18.** `η_0 - η_1 = ∑_{m=1}^{q-1} (m/q) ζ^m`. -/
@[kb "davenport1980" "Ch 3, p. 18"]
theorem gaussianPeriod_two_sub (hq2 : q ≠ 2) (ζ : R) :
    gaussianPeriod g 2 0 ζ - gaussianPeriod g 2 1 ζ =
      ∑ n : (ZMod q)ˣ, (quadraticChar (ZMod q) n : R) * ζ ^ (n : ZMod q).val := by
  simp_rw [neg_one_pow_index hg hq2]
  rw [← sum_filter_add_sum_filter_not univ (fun n ↦ index g n % 2 = 0)]
  unfold gaussianPeriod
  rw [sub_eq_add_neg, ← sum_neg_distrib]
  congr 1
  · refine sum_congr (filter_congr fun n _ ↦ by rw [Nat.ModEq, Nat.zero_mod]) fun n hn ↦ ?_
    rw [if_pos (Finset.mem_filter.mp hn).2, Int.cast_one, one_mul]
  · refine sum_congr (filter_congr fun n _ ↦ by rw [Nat.ModEq, Nat.one_mod]; omega)
      fun n hn ↦ ?_
    rw [if_neg (Finset.mem_filter.mp hn).2, Int.cast_neg, Int.cast_one, neg_one_mul]

/-- **Davenport §3, p. 18.** With `ζ = e(1/q)`, `η_0 - η_1 = G`, Gauss's sum. -/
@[kb "davenport1980" "Ch 3, p. 18"]
theorem gaussianPeriod_two_sub_eq_gaussSum (hq2 : q ≠ 2) :
    gaussianPeriod g 2 0 (cexp (2 * π * I / q)) - gaussianPeriod g 2 1 (cexp (2 * π * I / q)) =
      gaussSum (legendreChar q) ZMod.stdAddChar := by
  rw [gaussianPeriod_two_sub hg hq2, gaussSum, sum_zmod_eq_add_sum_units]
  have hq1 : q ≠ 1 := (Fact.out : q.Prime).one_lt.ne'
  rw [(legendreChar q).map_zero' hq1, zero_mul, zero_add]
  refine sum_congr rfl fun u _ ↦ ?_
  rw [legendreChar_apply, ← stdAddChar_one_eq, ← stdAddChar_natCast_eq_pow,
    ZMod.natCast_zmod_val]

omit hg in
/-- `e(1/q)` is a primitive `q`-th root of unity. -/
theorem isPrimitiveRoot_cexp : IsPrimitiveRoot (cexp (2 * π * I / q)) q :=
  Complex.isPrimitiveRoot_exp q (Fact.out : q.Prime).ne_zero

/-- **Davenport §3, p. 18.** With `ζ = e(1/q)`, `η_0 = (-1 + ε √q)/2`, where `ε = 1` if
`q ≡ 1 (mod 4)` and `ε = i` if `q ≡ 3 (mod 4)`. -/
@[kb "davenport1980" "Ch 3, p. 18"]
theorem gaussianPeriod_two_zero_eq (hq2 : q ≠ 2) :
    gaussianPeriod g 2 0 (cexp (2 * π * I / q)) =
      (-1 + if q % 4 = 1 then (√q : ℂ) else I * √q) / 2 := by
  have hsum := sum_gaussianPeriod g two_pos (isPrimitiveRoot_cexp (q := q))
  rw [show range 2 = range (1 + 1) from rfl, sum_range_succ, sum_range_one] at hsum
  have hdiff := gaussianPeriod_two_sub_eq_gaussSum hg hq2
  rw [gaussSum_legendreChar q hq2] at hdiff
  linear_combination (hsum + hdiff) / 2

/-- **Davenport §3, p. 18.** With `ζ = e(1/q)`, `η_1 = (-1 - ε √q)/2`. -/
@[kb "davenport1980" "Ch 3, p. 18"]
theorem gaussianPeriod_two_one_eq (hq2 : q ≠ 2) :
    gaussianPeriod g 2 1 (cexp (2 * π * I / q)) =
      (-1 - if q % 4 = 1 then (√q : ℂ) else I * √q) / 2 := by
  have hsum := sum_gaussianPeriod g two_pos (isPrimitiveRoot_cexp (q := q))
  rw [show range 2 = range (1 + 1) from rfl, sum_range_succ, sum_range_one] at hsum
  have hdiff := gaussianPeriod_two_sub_eq_gaussSum hg hq2
  rw [gaussSum_legendreChar q hq2] at hdiff
  linear_combination (hsum - hdiff) / 2

end Quadratic

end NTKB.Davenport
