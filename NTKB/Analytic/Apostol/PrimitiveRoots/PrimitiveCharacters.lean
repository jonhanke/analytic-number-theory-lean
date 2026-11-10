/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.NumberTheory.MulChar.Lemmas
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.RingTheory.RootsOfUnity.Complex
import NTKB.Analytic.Apostol.PrimitiveRoots.Index

/-!
# Primitive characters modulo `p^a` (Apostol, §10.11 (21) and Theorem 10.14)

For a primitive root `g` mod `m` and an integer `h`, Apostol's character (21) is
`χ_h(n) = e^{2πi h ind_g(n)/φ(m)}` for `(n, m) = 1` (`NTKB.Apostol.charH`, value formula
`charH_apply`).

**Theorem 10.14**: for an odd prime `p`, `a ≥ 2` and a primitive root `g` mod `p^a`, `χ_h` is
primitive mod `p^a` iff `p ∤ h`.

Apostol's proof: `χ_h` is primitive iff `p^{a-1}` is not an induced modulus; `p^{a-1}` is an
induced modulus iff `χ_h(n) = 1` for all `n ≡ 1 (mod p^{a-1})`, and these `n` are the powers of
`g^{φ(p^{a-1})}`, on which `χ_h` is `e^{2πi h/p}`. Mathlib's `FactorsThrough` (with
`factorsThrough_iff_ker_unitsMap`) is the induced-modulus notion.
-/

open Complex
open scoped Real

namespace NTKB.Apostol

variable {m : ℕ} [NeZero m]

/-- `e^{2πi h/φ(m)}` as a unit of `ℂ`. -/
noncomputable def rootH (m h : ℕ) : ℂˣ :=
  Units.mk0 (exp (2 * π * I * h / m.totient)) (exp_ne_zero _)

theorem rootH_mem (h : ℕ) : rootH m h ∈ rootsOfUnity (Fintype.card (ZMod m)ˣ) ℂ := by
  rw [_root_.mem_rootsOfUnity, ZMod.card_units_eq_totient]
  apply Units.ext
  have ht : (m.totient : ℂ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.2 (NeZero.pos m)).ne'
  simp only [rootH, Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one, ← exp_nat_mul]
  rw [show (m.totient : ℂ) * (2 * π * I * h / m.totient) = (h : ℤ) * (2 * π * I) by
    push_cast; field_simp]
  exact exp_int_mul_two_pi_mul_I h

theorem IsPrimitiveRootMod.mem_zpowers {g : (ZMod m)ˣ} (hg : IsPrimitiveRootMod m g)
    (x : (ZMod m)ˣ) : x ∈ Subgroup.zpowers g := by
  obtain ⟨k, hk⟩ := hg.exists_pow_eq x
  exact ⟨k, by simpa using hk⟩

/-- Apostol's character (21): `χ_h(n) = e^{2πi h ind_g(n)/φ(m)}`. -/
noncomputable def charH {g : (ZMod m)ˣ} (hg : IsPrimitiveRootMod m g) (h : ℕ) :
    DirichletCharacter ℂ m :=
  MulChar.ofRootOfUnity (rootH_mem h) hg.mem_zpowers

theorem charH_gen {g : (ZMod m)ˣ} (hg : IsPrimitiveRootMod m g) (h : ℕ) :
    charH hg h g = exp (2 * π * I * h / m.totient) := by
  rw [charH, MulChar.ofRootOfUnity_spec]; simp [rootH]

theorem charH_pow {g : (ZMod m)ˣ} (hg : IsPrimitiveRootMod m g) (h k : ℕ) :
    charH hg h ((g ^ k : (ZMod m)ˣ) : ZMod m) = exp (2 * π * I * h * k / m.totient) := by
  rw [Units.val_pow_eq_pow_val, map_pow, charH_gen, ← exp_nat_mul]
  congr 1; ring

/-- The value formula (21): `χ_h(n) = e^{2πi h ind_g(n)/φ(m)}` for units `n`. -/
@[kb "apostol1976" "§10.11 (21), p. 219"]
theorem charH_apply {g : (ZMod m)ˣ} (hg : IsPrimitiveRootMod m g) (h : ℕ) (n : (ZMod m)ˣ) :
    charH hg h n = exp (2 * π * I * h * ind hg n / m.totient) := by
  conv_lhs => rw [← pow_ind hg n]
  exact charH_pow hg h _

/-- `χ` is primitive mod `p^a` iff `p^{a-1}` is not an induced modulus. -/
theorem isPrimitive_iff_not_factorsThrough {p a : ℕ} (hp : p.Prime) (ha : 1 ≤ a)
    (χ : DirichletCharacter ℂ (p ^ a)) :
    χ.IsPrimitive ↔ ¬ χ.FactorsThrough (p ^ (a - 1)) := by
  have : NeZero (p ^ a) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hlt : p ^ (a - 1) < p ^ a := Nat.pow_lt_pow_right hp.one_lt (by omega)
  have hdvd : p ^ (a - 1) ∣ p ^ a := pow_dvd_pow p (by omega)
  rw [DirichletCharacter.isPrimitive_def]
  constructor
  · intro hc hf
    have : χ.conductor ≤ p ^ (a - 1) := Nat.sInf_le hf
    omega
  · intro hf
    by_contra hc
    obtain ⟨i, hi, hci⟩ := (Nat.dvd_prime_pow hp).1 χ.conductor_dvd_level
    have hia : i ≠ a := fun h ↦ hc (by rw [hci, h])
    have hcd : χ.conductor ∣ p ^ (a - 1) := hci ▸ pow_dvd_pow p (by omega)
    exact hf (DirichletCharacter.FactorsThrough.mono χ χ.factorsThrough_conductor hcd hdvd)

/-- **Apostol, Theorem 10.14**: for an odd prime `p`, `a ≥ 2` and a primitive root `g` mod
`p^a`, the character `χ_h` is primitive mod `p^a` iff `p ∤ h`. -/
@[kb "apostol1976" "Thm 10.14, p. 221"]
theorem isPrimitive_charH_iff {p a : ℕ} (hp : p.Prime) (ha : 2 ≤ a) [NeZero (p ^ a)]
    {g : (ZMod (p ^ a))ˣ} (hg : IsPrimitiveRootMod (p ^ a) g) (h : ℕ) :
    (charH hg h).IsPrimitive ↔ ¬ p ∣ h := by
  set d := p ^ (a - 1)
  have hdvd : d ∣ p ^ a := pow_dvd_pow p (by omega)
  have : NeZero d := ⟨pow_ne_zero _ hp.ne_zero⟩
  obtain ⟨f, hf⟩ : ∃ f : (ZMod (p ^ a))ˣ →* (ZMod d)ˣ, f = ZMod.unitsMap hdvd := ⟨_, rfl⟩
  -- totients
  have htot : (p ^ a).totient = p * d.totient := by
    obtain ⟨b, rfl⟩ : ∃ b, a = b + 2 := ⟨a - 2, by omega⟩
    simp only [d, show b + 2 - 1 = b + 1 by omega]
    rw [Nat.totient_prime_pow_succ hp, Nat.totient_prime_pow_succ hp]
    ring
  -- the image of `g` generates `(ZMod d)ˣ`, so it has order `φ(d)`
  have hfg : orderOf (f g) = d.totient := by
    have htop : ∀ y, y ∈ Subgroup.zpowers (f g) := by
      intro y
      obtain ⟨x, rfl⟩ := ZMod.unitsMap_surjective hdvd y
      obtain ⟨k, rfl⟩ := hg.mem_zpowers x
      exact ⟨k, by rw [hf, map_zpow]⟩
    rw [orderOf_eq_card_of_forall_mem_zpowers htop, Nat.card_eq_fintype_card,
      ZMod.card_units_eq_totient]
  -- `χ_h` on the kernel generator `g^{φ(d)}`
  have hval : charH hg h ((g ^ d.totient : (ZMod (p ^ a))ˣ) : ZMod (p ^ a)) =
      exp (2 * π * I * h / p) := by
    rw [charH_pow, htot]
    congr 1
    have hd0 : (d.totient : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.totient_pos.2 (NeZero.pos d)).ne'
    push_cast
    field_simp
  have hroot : exp (2 * π * I * h / p) = 1 ↔ p ∣ h := by
    have hζ := Complex.isPrimitiveRoot_exp p hp.ne_zero
    rw [← hζ.pow_eq_one_iff_dvd, ← exp_nat_mul]
    congr! 2
    ring
  rw [isPrimitive_iff_not_factorsThrough hp (by omega),
    DirichletCharacter.factorsThrough_iff_ker_unitsMap hdvd, ← hf, ← hroot, ← hval, not_iff_not]
  constructor
  · intro hker
    have hmem : g ^ d.totient ∈ f.ker := by
      rw [MonoidHom.mem_ker, map_pow, ← hfg, pow_orderOf_eq_one]
    have := hker hmem
    rw [MonoidHom.mem_ker] at this
    have := congrArg Units.val this
    simpa using this
  · intro h1 x hx
    rw [MonoidHom.mem_ker] at hx ⊢
    obtain ⟨k, rfl⟩ : ∃ k, g ^ k = x := hg.exists_pow_eq x
    rw [map_pow, ← orderOf_dvd_iff_pow_eq_one, hfg] at hx
    obtain ⟨j, rfl⟩ := hx
    apply Units.ext
    simp only [MulChar.coe_toUnitHom, Units.val_one, pow_mul, Units.val_pow_eq_pow_val, map_pow]
    rw [Units.val_pow_eq_pow_val, map_pow] at h1
    rw [h1, one_pow]

end NTKB.Apostol
