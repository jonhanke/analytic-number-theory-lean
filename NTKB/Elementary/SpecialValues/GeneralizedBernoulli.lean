/-
Copyright (c) 2026 The Tau Ceti contributors (definition and the degree-zero, degree-one and parity
lemmas, adapted from Tau Ceti); the NTKB authors (the rest). Released under Apache 2.0 license.
-/
import Mathlib.NumberTheory.BernoulliPolynomials
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.Analysis.Complex.Basic
import NTKB.Attr

/-!
# Generalized Bernoulli numbers of a Dirichlet character

For a Dirichlet character `χ` modulo `N ≥ 1` with values in a commutative `ℚ`-algebra `R`,
$$B_{n,\chi} = N^{n-1}\sum_{a=1}^{N}\chi(a)\,B_n\!\left(\tfrac{a}{N}\right),$$
where `B_n(X)` is the Bernoulli polynomial (`Polynomial.bernoulli`). The residue `0` is represented
by `N`, so for the character modulo `1` this is `B_n(1)`, the Bernoulli number with
`B_1 = +1/2` (Mathlib's `bernoulli'`), which is the convention of Washington and Miyake.

This is equivalent to the generating-function definition (Washington §4.1, Miyake §3.3):
$$\sum_{a=1}^{N}\chi(a)\,\frac{t e^{at}}{e^{Nt}-1} = \sum_{n\ge 0} B_{n,\chi}\,\frac{t^n}{n!},$$
proved here as `NTKB.generalizedBernoulli_generating_function` (multiplied out by `e^{Nt} − 1`
in the ring of formal power series).

## Provenance

The definition, `generalizedBernoulli_def`, `map_generalizedBernoulli`,
`generalizedBernoulli_modOne`, the degree-zero and degree-one lemmas and
`generalizedBernoulli_eq_zero_of_apply_neg_one_eq_neg` are copied (with credit, Apache 2.0) from
Tau Ceti, `TauCeti/NumberTheory/DirichletCharacter/GeneralizedBernoulli.lean`, main `d7b4780`
(2026-11-07), which adapts them from Chris Birkbeck's AINTLIB `FltRegularBernoulli` project. The
declarations are renamed into the `NTKB` namespace (`NTKB.generalizedBernoulli χ n` for Tau Ceti's
`χ.generalizedBernoulli n`); statements and definition are unchanged. The generating function is
ported from modular-forms-lean (`ModularFormsKB/Miyake/GeneralizedBernoulli.lean`).
-/

noncomputable section

namespace NTKB

section Def

open Polynomial

variable {N : ℕ} {R : Type*} [CommRing R] [Algebra ℚ R]

/-- The generalized Bernoulli number `B_{n,χ}` attached to a Dirichlet character `χ` modulo `N`:
`B_{n,χ} = N^{n-1} ∑_{a : ZMod N} χ(a) B_n(ã / N)`, where `ã` is the representative of `a` in
`{1, …, N}`. The scalar `N^{n-1}` is formed in `ℚ` (so it is `N⁻¹` for `n = 0`).
(Tau Ceti's `DirichletCharacter.generalizedBernoulli`.) -/
@[kb "washington1997" "§4.1, definition of B_{n,χ} (p. 31), and Proposition 4.1"]
def generalizedBernoulli [NeZero N] (χ : DirichletCharacter R N) (n : ℕ) : R :=
  algebraMap ℚ R ((N : ℚ) ^ ((n : ℤ) - 1)) *
    ∑ a : ZMod N, χ a *
      algebraMap ℚ R
        ((Polynomial.bernoulli n).eval (((if a = 0 then N else a.val : ℕ) : ℚ) / N))

theorem generalizedBernoulli_def [NeZero N] (χ : DirichletCharacter R N) (n : ℕ) :
    generalizedBernoulli χ n =
      algebraMap ℚ R ((N : ℚ) ^ ((n : ℤ) - 1)) *
        ∑ a : ZMod N, χ a *
          algebraMap ℚ R
            ((Polynomial.bernoulli n).eval (((if a = 0 then N else a.val : ℕ) : ℚ) / N)) := by
  rw [generalizedBernoulli]

/-- Generalized Bernoulli numbers commute with extension of the coefficient ring. -/
theorem map_generalizedBernoulli [NeZero N] {S : Type*} [CommRing S] [Algebra ℚ S]
    (χ : DirichletCharacter R N) (f : R →ₐ[ℚ] S) (n : ℕ) :
    f (generalizedBernoulli χ n) =
      generalizedBernoulli (χ.ringHomComp (f : R →+* S) : DirichletCharacter S N) n := by
  simp only [generalizedBernoulli, map_mul, AlgHom.commutes, map_sum, MulChar.ringHomComp_apply,
    RingHom.coe_coe]

/-- At modulus one, generalized Bernoulli numbers are the Bernoulli numbers with `B_1 = +1/2`
(Mathlib's `bernoulli'`). -/
@[simp]
theorem generalizedBernoulli_modOne (χ : DirichletCharacter R 1) (n : ℕ) :
    generalizedBernoulli χ n = algebraMap ℚ R (_root_.bernoulli' n) := by
  rw [χ.level_one, generalizedBernoulli_def, Fintype.sum_subsingleton _ 1, map_one, one_mul]
  simp [Subsingleton.elim (1 : ZMod 1) 0, Polynomial.bernoulli_eval_one]

/-- The zeroth generalized Bernoulli number is `N⁻¹` times the sum of the character values. -/
theorem generalizedBernoulli_zero [NeZero N] (χ : DirichletCharacter R N) :
    generalizedBernoulli χ 0 =
      algebraMap ℚ R (N : ℚ)⁻¹ * ∑ a : ZMod N, χ a := by
  simp [generalizedBernoulli_def]

/-- The zeroth generalized Bernoulli number of a nontrivial character is zero. -/
theorem generalizedBernoulli_zero_of_ne_one [IsDomain R] [NeZero N]
    {χ : DirichletCharacter R N} (hχ : χ ≠ 1) : generalizedBernoulli χ 0 = 0 := by
  rw [generalizedBernoulli_zero, MulChar.sum_eq_zero_of_ne_one hχ, mul_zero]

/-- The first generalized Bernoulli number, from `B₁(X) = X - 1 / 2`. -/
theorem generalizedBernoulli_one [NeZero N] (χ : DirichletCharacter R N) :
    generalizedBernoulli χ 1 =
      (∑ a : ZMod N, χ a *
        algebraMap ℚ R (((if a = 0 then N else a.val : ℕ) : ℚ) / N)) -
        algebraMap ℚ R (2⁻¹ : ℚ) * ∑ a : ZMod N, χ a := by
  simp only [generalizedBernoulli_def, Nat.cast_one, sub_self, zpow_zero, map_one, one_mul,
    Polynomial.bernoulli_one, eval_sub, eval_X, eval_C, map_sub, mul_sub,
    Finset.sum_sub_distrib, Finset.sum_mul, mul_comm (algebraMap ℚ R 2⁻¹)]

/-- For a nontrivial character, `B_{1,χ} = ∑_a χ(a) a / N`. -/
theorem generalizedBernoulli_one_of_ne_one [IsDomain R] [NeZero N]
    {χ : DirichletCharacter R N} (hχ : χ ≠ 1) :
    generalizedBernoulli χ 1 =
      ∑ a : ZMod N, χ a * algebraMap ℚ R ((a.val : ℚ) / N) := by
  have hN : N ≠ 1 := fun hN ↦ hχ (χ.level_one' hN)
  rw [generalizedBernoulli_one, MulChar.sum_eq_zero_of_ne_one hχ, mul_zero, sub_zero]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  by_cases ha : a = 0
  · simp [ha, χ.map_zero' hN]
  · simp [ha]

/-- `N B_{1,χ} = ∑_a χ(a) a` for a nontrivial character. -/
theorem natCast_mul_generalizedBernoulli_one_of_ne_one [IsDomain R] [NeZero N]
    {χ : DirichletCharacter R N} (hχ : χ ≠ 1) :
    (N : R) * generalizedBernoulli χ 1 = ∑ a : ZMod N, χ a * (a.val : R) := by
  rw [generalizedBernoulli_one_of_ne_one hχ, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [← map_natCast (algebraMap ℚ R) N, mul_left_comm, ← map_mul,
    mul_div_cancel₀ _ (NeZero.ne _), map_natCast]

/-- **Parity vanishing.** `B_{k,χ} = 0` when `χ(-1) = -(-1)^k`, unless `k = 1` and `N = 1`
(for the character modulo one, `B_{1,χ} = 1/2`). -/
@[kb "washington1997" "§4.1, after Proposition 4.1 (B_{n,χ} = 0 if χ(-1) ≠ (-1)^n, n ≠ 1)"]
theorem generalizedBernoulli_eq_zero_of_apply_neg_one_eq_neg [NeZero N]
    {χ : DirichletCharacter R N} {k : ℕ} (hk : k ≠ 1 ∨ N ≠ 1) (hχ : χ (-1) = -(-1) ^ k) :
    generalizedBernoulli χ k = 0 := by
  have hN : (N : ℚ) ≠ 0 := NeZero.ne _
  set β : ZMod N → ℚ := fun a ↦
    (Polynomial.bernoulli k).eval (((if a = 0 then N else a.val : ℕ) : ℚ) / N) with hβ
  have hβneg (a : ZMod N) (ha : a ≠ 0 ∨ k ≠ 1) : β (-a) = (-1) ^ k * β a := by
    rcases eq_or_ne a 0 with rfl | ha'
    · simp only [hβ, neg_zero, ↓reduceIte]
      rw [div_self hN, ← bernoulli_eval_one_sub, sub_self, bernoulli_eval_zero,
        bernoulli_eval_one, bernoulli_eq_bernoulli'_of_ne_one (ha.resolve_left (by simp))]
    · have : NeZero a := ⟨ha'⟩
      simp only [hβ, neg_eq_zero, ha', ↓reduceIte]
      rw [ZMod.val_neg_of_ne_zero, Nat.cast_sub a.val_le, sub_div, div_self hN,
        bernoulli_eval_one_sub]
  have hodd : Function.Odd fun a ↦ χ a * algebraMap ℚ R (β a) := by
    intro a
    by_cases ha : a ≠ 0 ∨ k ≠ 1
    · dsimp only
      rw [hβneg a ha, neg_eq_neg_one_mul a, map_mul, hχ]
      rcases neg_one_pow_eq_or R k with h | h <;> simp [h]
    · obtain ⟨rfl, rfl⟩ : a = 0 ∧ k = 1 := by tauto
      simp [χ.map_zero' (hk.resolve_left (by simp))]
  have : HasUniqueDiv R := .of_module_rat R
  rw [generalizedBernoulli_def]
  exact mul_eq_zero_of_right _ hodd.sum_eq_zero

/-! ### The complex form: a sum over `a = 1, …, N` -/

/-- Over `ℂ`, `B_{n,χ} = N^{n-1} ∑_{a=1}^{N} χ(a) B_n(a/N)`, the form of Washington and Miyake. -/
theorem generalizedBernoulli_eq_sum_Icc [NeZero N] (χ : DirichletCharacter ℂ N) (n : ℕ) :
    generalizedBernoulli χ n = (N : ℂ) ^ ((n : ℤ) - 1) *
      ∑ a ∈ Finset.Icc 1 N, χ a *
        ((Polynomial.bernoulli n).map (algebraMap ℚ ℂ)).eval ((a : ℂ) / N) := by
  rw [generalizedBernoulli_def]
  congr 1
  · simp
  · -- reindex `ZMod N ≃ {1, …, N}` by `a ↦ ã`
    symm
    refine Finset.sum_bij (fun a _ ↦ (a : ZMod N)) (fun _ _ ↦ Finset.mem_univ _) ?_ ?_ ?_
    · intro a ha b hb hab
      rw [Finset.mem_Icc] at ha hb
      rw [ZMod.natCast_eq_natCast_iff'] at hab
      rcases Nat.lt_or_ge a N with h1 | h1 <;> rcases Nat.lt_or_ge b N with h2 | h2
      · rwa [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at hab
      · have : b = N := by omega
        subst this
        rw [Nat.mod_eq_of_lt h1, Nat.mod_self] at hab
        omega
      · have : a = N := by omega
        subst this
        rw [Nat.mod_eq_of_lt h2, Nat.mod_self] at hab
        omega
      · omega
    · intro j _
      by_cases h0 : j = 0
      · exact ⟨N, Finset.mem_Icc.mpr ⟨Nat.pos_of_ne_zero (NeZero.ne N), le_rfl⟩, by simp [h0]⟩
      · refine ⟨j.val, Finset.mem_Icc.mpr ⟨Nat.pos_of_ne_zero ((ZMod.val_ne_zero j).mpr h0),
          (ZMod.val_lt j).le⟩, by simp⟩
    · intro a ha
      rw [Finset.mem_Icc] at ha
      congr 1
      have hrep : ((if (a : ZMod N) = 0 then N else (a : ZMod N).val : ℕ) : ℚ) = a := by
        split_ifs with h
        · rw [ZMod.natCast_eq_zero_iff] at h
          obtain ⟨c, hc⟩ := h
          have : c = 1 := by
            rcases c with _ | _ | c
            · omega
            · rfl
            · nlinarith
          subst this
          simp [hc]
        · rw [ZMod.val_natCast, Nat.mod_eq_of_lt]
          rcases Nat.lt_or_ge a N with h1 | h1
          · exact h1
          · exact absurd (show (a : ZMod N) = 0 by
              rw [show a = N by omega, ZMod.natCast_self]) h
      rw [hrep, Polynomial.eval_map, ← Polynomial.eval₂_at_apply (algebraMap ℚ ℂ)]
      simp [Polynomial.eval₂_eq_eval_map]

end Def

/-! ### The generating function -/

variable {N : ℕ}

open PowerSeries in
/-- **The generating function of `B_{n,χ}`** (Washington §4.1; Miyake §3.3, p. 94): in `ℂ⟦t⟧`,
$$\Big(\sum_{n\ge0} B_{n,\chi}\frac{t^n}{n!}\Big)(e^{Nt} - 1) = \sum_{a=1}^{N}\chi(a)\,t\,e^{at}.$$
Since `e^{Nt} − 1 = t · (unit)`, this characterizes the `B_{n,χ}`
(`generalizedBernoulli_unique_of_generating_function`). Ported from modular-forms-lean. -/
@[kb "washington1997" "§4.1, definition of B_{n,χ} by the generating function (p. 30)"]
theorem generalizedBernoulli_generating_function [NeZero N] (χ : DirichletCharacter ℂ N) :
    PowerSeries.mk (fun n ↦ generalizedBernoulli χ n / n.factorial) *
        (rescale (N : ℂ) (exp ℂ) - 1) =
      ∑ a ∈ Finset.Icc 1 N, χ a • (X * rescale (a : ℂ) (exp ℂ)) := by
  have hm : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have key : ∀ a : ℕ, PowerSeries.mk (fun n : ℕ ↦ (N : ℂ) ^ ((n : ℤ) - 1) *
      ((Polynomial.bernoulli n).map (algebraMap ℚ ℂ)).eval ((a : ℂ) / N) / n.factorial) *
        (rescale (N : ℂ) (exp ℂ) - 1) = X * rescale (a : ℂ) (exp ℂ) := by
    intro a
    have h := Polynomial.bernoulli_generating_function (A := ℂ) ((a : ℂ) / N)
    have h2 := congrArg (rescale (N : ℂ)) h
    rw [map_mul, map_sub, map_one, map_mul, rescale_X, rescale_rescale, div_mul_cancel₀ _ hm,
      rescale_mk] at h2
    have h3 : (C (N : ℂ)) * (PowerSeries.mk (fun n : ℕ ↦ (N : ℂ) ^ ((n : ℤ) - 1) *
      ((Polynomial.bernoulli n).map (algebraMap ℚ ℂ)).eval ((a : ℂ) / N) / n.factorial) *
        (rescale (N : ℂ) (exp ℂ) - 1)) = C (N : ℂ) * (X * rescale (a : ℂ) (exp ℂ)) := by
      have hc : C (N : ℂ) * PowerSeries.mk (fun n : ℕ ↦ (N : ℂ) ^ ((n : ℤ) - 1) *
          ((Polynomial.bernoulli n).map (algebraMap ℚ ℂ)).eval ((a : ℂ) / N) / n.factorial) =
          PowerSeries.mk fun n => (N : ℂ) ^ n * (Polynomial.aeval ((a : ℂ) / N))
            ((1 / (n.factorial : ℚ)) • Polynomial.bernoulli n) := by
        ext n
        simp only [coeff_C_mul, coeff_mk]
        rw [zpow_sub₀ hm, zpow_natCast, zpow_one]
        rw [map_smul, Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
        simp only [Rat.smul_def, one_div, Rat.cast_inv, Rat.cast_natCast]
        field_simp
      rw [← mul_assoc, hc, h2, mul_assoc]
    exact mul_left_cancel₀ ((map_ne_zero_iff _ (C_injective)).mpr hm) h3
  have hsum : PowerSeries.mk (fun n ↦ generalizedBernoulli χ n / n.factorial) =
      ∑ a ∈ Finset.Icc 1 N, χ a • PowerSeries.mk (fun n : ℕ ↦ (N : ℂ) ^ ((n : ℤ) - 1) *
      ((Polynomial.bernoulli n).map (algebraMap ℚ ℂ)).eval ((a : ℂ) / N) / n.factorial) := by
    ext n
    simp only [coeff_mk, map_sum, coeff_smul, generalizedBernoulli_eq_sum_Icc, smul_eq_mul,
      Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    ring
  rw [hsum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [smul_mul_assoc, key a]

open PowerSeries in
/-- The generating function determines the generalized Bernoulli numbers: if a sequence `b`
satisfies the identity of `generalizedBernoulli_generating_function`, then `b = B_{·,χ}`. -/
theorem generalizedBernoulli_unique_of_generating_function [NeZero N]
    (χ : DirichletCharacter ℂ N) (b : ℕ → ℂ)
    (hb : PowerSeries.mk (fun n ↦ b n / n.factorial) * (rescale (N : ℂ) (exp ℂ) - 1) =
      ∑ a ∈ Finset.Icc 1 N, χ a • (X * rescale (a : ℂ) (exp ℂ))) :
    b = generalizedBernoulli χ := by
  have hm : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have h := hb.trans (generalizedBernoulli_generating_function χ).symm
  -- `e^{Nt} - 1` is not a zero divisor in `ℂ⟦t⟧`
  have hne : (rescale (N : ℂ) (exp ℂ) - 1) ≠ 0 := by
    intro h0
    have := congrArg (coeff 1) h0
    simp [coeff_rescale, hm] at this
  have h' := mul_right_cancel₀ hne h
  funext n
  have := congrArg (coeff n) h'
  simp only [coeff_mk] at this
  have hf : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  exact (div_left_inj' hf).mp this

end NTKB
