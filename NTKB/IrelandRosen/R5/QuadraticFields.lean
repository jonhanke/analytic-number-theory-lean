/-
Ireland–Rosen, Chapter 13, §1: quadratic fields.
-/
import NTKB.Elementary.QuadraticField.IdealCount
import NTKB.Analytic.Davenport.ClassNumber.Torsion
import NTKB.Analytic.Davenport.ClassNumber.Formula

/-!
# Ireland–Rosen, Chapter 13, §1: the ring of integers, the discriminant and the decomposition law
of `ℚ(√d)`

For a squarefree integer `d ≠ 1`, `ℚ(√d)` is Mathlib's `QuadraticAlgebra ℚ d 0`
(`NTKB.IrelandRosen.QuadField d`, `ω = √d`).

* `isIntegral_iff_of_mod_four_ne_one`, `isIntegral_iff_of_mod_four_eq_one` (**Proposition
  13.1.1**): the integers of `ℚ(√d)` are `ℤ[√d]` if `d ≡ 2, 3 (mod 4)` and `ℤ[(1 + √d)/2]` if
  `d ≡ 1 (mod 4)`;
* `discr_quadField` (**Proposition 13.1.2**): the discriminant of `ℚ(√d)` is `d` if
  `d ≡ 1 (mod 4)` and `4d` otherwise;
* `ramified_of_dvd`, `split_of_legendreSym_eq_one`, `inert_of_legendreSym_eq_neg_one`
  (**Proposition 13.1.3**, `p` odd): `(p) = 𝔭²` if `p ∣ d`; `(p) = 𝔭𝔭'`, `𝔭 ≠ 𝔭'`, if
  `(d/p) = 1`; `(p)` prime if `(d/p) = -1`;
* `two_ramified`, `two_split`, `two_inert` (**Proposition 13.1.4**): `(2) = 𝔭²` if
  `d ≡ 2, 3 (mod 4)`; `(2) = 𝔭𝔭'` if `d ≡ 1 (mod 8)`; `(2)` prime if `d ≡ 5 (mod 8)`;
* `torsionOrder_quadField` (**Proposition 13.1.5**): for `d < 0` every unit is a root of unity,
  and there are `4` of them for `d = -1`, `6` for `d = -3`, and `2` otherwise.

The proofs go through `NTKB.QuadraticField`: `ℚ(√d) ≅ ℚ(√D)` for the fundamental discriminant
`D = d` or `4d`, `𝓞 = ℤ[ω]`, and the ideals `(p, ω - t)` for roots `t` of the minimal polynomial
of `ω` modulo `p`.
-/

noncomputable section

open QuadraticAlgebra NumberField Module Ideal NTKB.QuadraticField

namespace NTKB.IrelandRosen

/-- `ℚ(√d)`, with `ω = √d`. -/
abbrev QuadField (d : ℤ) := QuadraticAlgebra ℚ (d : ℚ) 0

theorem not_isSquare_of_squarefree {d : ℤ} (hd : Squarefree d) (h1 : d ≠ 1) :
    ¬ IsSquare (d : ℚ) := by
  rw [Rat.isSquare_intCast_iff]
  rintro ⟨r, rfl⟩
  rcases Int.isUnit_iff.mp (hd r dvd_rfl) with rfl | rfl <;> simp at h1

section

variable (d : ℤ) [hd : Fact (Squarefree d)] [h1 : Fact (d ≠ 1)]

instance factNotIsSquareQuadField : Fact (¬ IsSquare (d : ℚ)) :=
  ⟨not_isSquare_of_squarefree hd.out h1.out⟩

instance : NumberField (QuadField d) where
  to_charZero := inferInstance
  to_finiteDimensional := inferInstance

theorem finrank_quadField : finrank ℚ (QuadField d) = 2 := finrank_eq_two _ _

/-- `ℚ(√d) ≅ ℚ(√D)`, `D = d` or `4d` the fundamental discriminant. -/
theorem nonempty_algEquiv_model :
    Nonempty (QuadField d ≃ₐ[ℚ] Model (fundamentalOfSquarefree d)) :=
  nonempty_algEquiv_fundamentalOfSquarefree hd.out

/-- **Ireland–Rosen, Proposition 13.1.2**: the discriminant of `ℚ(√d)` is `d` if `d ≡ 1 (mod 4)`
and `4d` if `d ≡ 2, 3 (mod 4)`. -/
@[kb "irelandrosen1990" "Prop 13.1.2, p. 189"]
theorem discr_quadField : discr (QuadField d) = if d % 4 = 1 then d else 4 * d := by
  obtain ⟨e⟩ := nonempty_algEquiv_model d
  exact discr_eq_of_algEquiv _ (isFundamental_fundamentalOfSquarefree hd.out)
    (fundamentalOfSquarefree_ne_one h1.out) e

end

/-! ### Proposition 13.1.1 -/

/-- **Ireland–Rosen, Proposition 13.1.1, `d ≡ 2, 3 (mod 4)`**: the integers of `ℚ(√d)` are
`ℤ[√d]`. -/
@[kb "irelandrosen1990" "Prop 13.1.1, p. 189"]
theorem isIntegral_iff_of_mod_four_ne_one {d : ℤ} (hd : Squarefree d) (h4 : d % 4 ≠ 1)
    (z : QuadField d) :
    IsIntegral ℤ z ↔ ∃ m n : ℤ, z = (m : QuadField d) + (n : QuadField d) * ω := by
  have hD : IsFundamentalDiscriminant (4 * d) := by
    have := isFundamental_fundamentalOfSquarefree hd
    rwa [fundamentalOfSquarefree, if_neg h4] at this
  have hz := isIntegral_iff_mem_range_of_discr (a := d) (b := 0) (D := 4 * d)
    (by rw [discr_def]; ring) hD (z : QuadraticAlgebra ℚ ((d : ℤ) : ℚ) ((0 : ℤ) : ℚ))
  rw [hz]
  constructor
  · rintro ⟨⟨m, n⟩, hx⟩
    refine ⟨m, n, ?_⟩
    rw [← hx]
    ext
    · show ((m : ℤ) : ℚ) = _; simp
    · show ((n : ℤ) : ℚ) = _; simp
  · rintro ⟨m, n, rfl⟩
    refine ⟨⟨m, n⟩, ?_⟩
    ext
    · show ((m : ℤ) : ℚ) = _; simp
    · show ((n : ℤ) : ℚ) = _; simp

/-- `ω ↦ 2ω - 1`, the isomorphism `ℚ(√d) → ℚ((1 + √d)/2)` for `d ≡ 1 (mod 4)`. -/
def toModelOfModFour {d : ℤ} (h4 : d % 4 = 1) : QuadField d →ₐ[ℚ] Model d :=
  lift ⟨2 * ω - 1, by
    have hd : (d : ℚ) = 1 + 4 * ((d / 4 : ℤ) : ℚ) := by
      have : d = 1 + 4 * (d / 4) := by omega
      exact_mod_cast this
    have hb : ((d % 4 : ℤ) : ℚ) = 1 := by rw [h4]; simp
    ext
    · simp [hb]
      linear_combination -hd
    · simp [hb]; ring⟩

theorem toModelOfModFour_re {d : ℤ} (h4 : d % 4 = 1) (z : QuadField d) :
    (toModelOfModFour h4 z).re = z.re - z.im := by
  simp [toModelOfModFour]; ring

theorem toModelOfModFour_im {d : ℤ} (h4 : d % 4 = 1) (z : QuadField d) :
    (toModelOfModFour h4 z).im = 2 * z.im := by
  simp [toModelOfModFour]; ring

/-- **Ireland–Rosen, Proposition 13.1.1, `d ≡ 1 (mod 4)`**: the integers of `ℚ(√d)` are
`ℤ[(1 + √d)/2]`: `z` is integral iff `z = m + n (1 + √d)/2` with `m, n ∈ ℤ`. -/
@[kb "irelandrosen1990" "Prop 13.1.1, p. 189"]
theorem isIntegral_iff_of_mod_four_eq_one {d : ℤ} (hd : Squarefree d) (h1 : d ≠ 1)
    (h4 : d % 4 = 1) (z : QuadField d) :
    IsIntegral ℤ z ↔ ∃ m n : ℤ, z = ⟨m + n / 2, n / 2⟩ := by
  have : Fact (Squarefree d) := ⟨hd⟩
  have : Fact (d ≠ 1) := ⟨h1⟩
  have hD : IsFundamentalDiscriminant d := Or.inl ⟨h4, hd⟩
  have : Fact (IsFundamentalDiscriminant d) := ⟨hD⟩
  set ψ := toModelOfModFour h4
  have hinj : Function.Injective ψ := ψ.toRingHom.injective
  rw [← isIntegral_algHom_iff (ψ.toRingHom.toIntAlgHom) hinj]
  change IsIntegral ℤ (ψ z) ↔ _
  rw [isIntegral_iff_mem_range]
  constructor
  · rintro ⟨⟨m, n⟩, hx⟩
    have hre : (m : ℚ) = z.re - z.im := by rw [← toModelOfModFour_re h4 z, ← hx]; rfl
    have him : (n : ℚ) = 2 * z.im := by rw [← toModelOfModFour_im h4 z, ← hx]; rfl
    refine ⟨m, n, ?_⟩
    ext
    · show z.re = (m : ℚ) + n / 2; rw [hre, him]; ring
    · show z.im = (n : ℚ) / 2; rw [him]; ring
  · rintro ⟨m, n, rfl⟩
    refine ⟨⟨m, n⟩, ?_⟩
    ext
    · show ((m : ℤ) : ℚ) = _; rw [toModelOfModFour_re]; ring
    · show ((n : ℤ) : ℚ) = _; rw [toModelOfModFour_im]; ring

/-! ### Propositions 13.1.3 and 13.1.4 -/

section decomposition

variable {d : ℤ} [hd : Fact (Squarefree d)] [h1 : Fact (d ≠ 1)]

theorem isFundamental_discr_quadField : IsFundamentalDiscriminant (discr (QuadField d)) := by
  rw [discr_quadField, ← fundamentalOfSquarefree]
  exact isFundamental_fundamentalOfSquarefree hd.out

theorem legendreSym_discr_quadField {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    legendreSym p (discr (QuadField d)) = legendreSym p d := by
  rw [discr_quadField]
  split_ifs
  · rfl
  · rw [legendreSym.mul, show (4 : ℤ) = 2 ^ 2 by norm_num, legendreSym.sq_one']
    · ring
    · intro h
      have : (p : ℤ) ∣ 2 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp (by exact_mod_cast h)
      have := Int.le_of_dvd (by norm_num) this
      have := (Fact.out : p.Prime).two_le
      omega

/-- **Ireland–Rosen, Proposition 13.1.3 (a)**: an odd prime `p ∣ d` ramifies: `(p) = 𝔭²`. -/
@[kb "irelandrosen1990" "Prop 13.1.3, p. 190"]
theorem ramified_of_dvd {p : ℕ} (hp : p.Prime) (hpd : (p : ℤ) ∣ d) :
    ∃ P : Ideal (𝓞 (QuadField d)), P.IsPrime ∧ absNorm P = p ∧
      span {(p : 𝓞 (QuadField d))} = P ^ 2 := by
  refine exists_ramified (finrank_quadField d) hp ?_
  rw [discr_quadField]
  split_ifs
  · exact hpd
  · exact dvd_mul_of_dvd_right hpd 4

/-- **Ireland–Rosen, Proposition 13.1.3 (b)**: an odd prime `p` with `(d/p) = 1` splits:
`(p) = 𝔭 𝔭'`, `𝔭 ≠ 𝔭'`. -/
@[kb "irelandrosen1990" "Prop 13.1.3, p. 190"]
theorem split_of_legendreSym_eq_one {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hχ : legendreSym p d = 1) :
    ∃ P Q : Ideal (𝓞 (QuadField d)), P.IsPrime ∧ Q.IsPrime ∧ P ≠ Q ∧ absNorm P = p ∧
      absNorm Q = p ∧ span {(p : 𝓞 (QuadField d))} = P * Q := by
  refine exists_split (finrank_quadField d) hp.out ?_
  rw [kroneckerChar_prime_odd isFundamental_discr_quadField hp2, legendreSym_discr_quadField hp2,
    hχ]
  simp

/-- **Ireland–Rosen, Proposition 13.1.3 (c)**: an odd prime `p` with `(d/p) = -1` stays prime. -/
@[kb "irelandrosen1990" "Prop 13.1.3, p. 190"]
theorem inert_of_legendreSym_eq_neg_one {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hχ : legendreSym p d = -1) :
    (span {(p : 𝓞 (QuadField d))}).IsPrime ∧ absNorm (span {(p : 𝓞 (QuadField d))}) = p ^ 2 := by
  refine isPrime_of_inert (finrank_quadField d) hp.out ?_
  rw [kroneckerChar_prime_odd isFundamental_discr_quadField hp2, legendreSym_discr_quadField hp2,
    hχ]
  simp

/-- **Ireland–Rosen, Proposition 13.1.4 (a)**: `2` ramifies if `d ≡ 2, 3 (mod 4)`. -/
@[kb "irelandrosen1990" "Prop 13.1.4, p. 190"]
theorem two_ramified (h4 : d % 4 ≠ 1) :
    ∃ P : Ideal (𝓞 (QuadField d)), P.IsPrime ∧ absNorm P = 2 ∧
      span {((2 : ℕ) : 𝓞 (QuadField d))} = P ^ 2 := by
  refine exists_ramified (finrank_quadField d) Nat.prime_two ?_
  rw [discr_quadField, if_neg h4]
  exact ⟨2 * d, by ring⟩

/-- **Ireland–Rosen, Proposition 13.1.4 (b)**: `2` splits if `d ≡ 1 (mod 8)`. -/
@[kb "irelandrosen1990" "Prop 13.1.4, p. 190"]
theorem two_split (h8 : d % 8 = 1) :
    ∃ P Q : Ideal (𝓞 (QuadField d)), P.IsPrime ∧ Q.IsPrime ∧ P ≠ Q ∧ absNorm P = 2 ∧
      absNorm Q = 2 ∧ span {((2 : ℕ) : 𝓞 (QuadField d))} = P * Q := by
  have h4 : d % 4 = 1 := by omega
  have hdisc : discr (QuadField d) = d := by rw [discr_quadField, if_pos h4]
  refine exists_split (finrank_quadField d) Nat.prime_two ?_
  have := kroneckerChar_two (D := discr (QuadField d)) isFundamental_discr_quadField
    (by rw [hdisc]; omega)
  rw [this, hdisc, if_pos h8]

/-- **Ireland–Rosen, Proposition 13.1.4 (c)**: `2` stays prime if `d ≡ 5 (mod 8)`. -/
@[kb "irelandrosen1990" "Prop 13.1.4, p. 190"]
theorem two_inert (h8 : d % 8 = 5) :
    (span {((2 : ℕ) : 𝓞 (QuadField d))}).IsPrime ∧
      absNorm (span {((2 : ℕ) : 𝓞 (QuadField d))}) = 2 ^ 2 := by
  have h4 : d % 4 = 1 := by omega
  have hdisc : discr (QuadField d) = d := by rw [discr_quadField, if_pos h4]
  refine isPrime_of_inert (finrank_quadField d) Nat.prime_two ?_
  have := kroneckerChar_two (D := discr (QuadField d)) isFundamental_discr_quadField
    (by rw [hdisc]; omega)
  rw [this, hdisc, if_neg (by omega)]

end decomposition

/-! ### Proposition 13.1.5 -/

section units

open NumberField.Units

variable {K : Type} [Field K] [NumberField K]

/-- If the unit rank is `0`, every unit is a root of unity (Dirichlet's unit theorem). -/
theorem mem_torsion_of_rank_eq_zero (h : rank K = 0) (x : (𝓞 K)ˣ) : x ∈ torsion K := by
  obtain ⟨⟨ζ, f⟩, hx, -⟩ := exist_unique_eq_mul_prod K x
  have : IsEmpty (Fin (rank K)) := by rw [h]; infer_instance
  simp only [Finset.univ_eq_empty, Finset.prod_empty, mul_one] at hx
  rw [hx]
  exact ζ.2

theorem natCast_ne_zero_ringOfIntegers {n : ℕ} (hn : n ≠ 0) : (n : 𝓞 K) ≠ 0 :=
  Nat.cast_ne_zero.mpr hn

/-- `ℚ(i)`: a quadratic field of discriminant `-4` has `4` roots of unity. -/
theorem torsionOrder_eq_four (hK : finrank ℚ K = 2) (hD : discr K = -4) : torsionOrder K = 4 := by
  obtain ⟨e⟩ : Nonempty (Order (-4) ≃+* 𝓞 K) := hD ▸ nonempty_ringEquiv_order K hK
  set u := gen e
  have hu : u * u = -1 := by
    have := gen_mul_gen e
    norm_num at this
    exact this
  let U : (𝓞 K)ˣ := ⟨u, -u, by linear_combination -hu, by linear_combination -hu⟩
  have hU : U ∈ torsion K := mem_torsion_of_rank_eq_zero
    (Davenport.rank_eq_zero_of_discr_neg (K := K) hK (by rw [hD]; norm_num)) U
  have hpow := congrArg Units.val (pow_torsionOrder_eq_one K hU)
  rw [Units.val_pow_eq_pow_val, Units.val_one] at hpow
  change u ^ _ = 1 at hpow
  have h2 : ((2 : ℕ) : 𝓞 K) ≠ 0 := natCast_ne_zero_ringOfIntegers two_ne_zero
  rcases Davenport.torsionOrder_eq_two_or_four_or_six hK with h | h | h
  · rw [h] at hpow
    exact absurd (by push_cast; linear_combination hu - hpow) h2
  · exact h
  · rw [h] at hpow
    have : u ^ 6 = -1 := by
      rw [show u ^ 6 = (u * u) ^ 3 by ring, hu]; ring
    exact absurd (by push_cast; linear_combination this - hpow) h2

/-- `ℚ(√-3)`: a quadratic field of discriminant `-3` has `6` roots of unity. -/
theorem torsionOrder_eq_six (hK : finrank ℚ K = 2) (hD : discr K = -3) : torsionOrder K = 6 := by
  obtain ⟨e⟩ : Nonempty (Order (-3) ≃+* 𝓞 K) := hD ▸ nonempty_ringEquiv_order K hK
  set u := gen e
  have hu : u * u = -1 + u := by
    have := gen_mul_gen e
    norm_num at this
    exact this
  let U : (𝓞 K)ˣ := ⟨u, 1 - u, by linear_combination -hu, by linear_combination -hu⟩
  have hU : U ∈ torsion K := mem_torsion_of_rank_eq_zero
    (Davenport.rank_eq_zero_of_discr_neg (K := K) hK (by rw [hD]; norm_num)) U
  have hpow := congrArg Units.val (pow_torsionOrder_eq_one K hU)
  rw [Units.val_pow_eq_pow_val, Units.val_one] at hpow
  change u ^ _ = 1 at hpow
  have h3 : ((3 : ℕ) : 𝓞 K) ≠ 0 := natCast_ne_zero_ringOfIntegers (by norm_num)
  have hu3 : u ^ 3 = -1 := by
    rw [show u ^ 3 = u * (u * u) by ring, hu]; linear_combination hu
  rcases Davenport.torsionOrder_eq_two_or_four_or_six hK with h | h | h
  · rw [h] at hpow
    -- `u² = 1` gives `u = 2`, then `4 = 1`
    have hu2 : u = 2 := by linear_combination hpow - hu
    exact absurd (by push_cast; linear_combination hu - (u + 1) * hu2) h3
  · rw [h] at hpow
    -- `u⁴ = -u = 1` gives `u = -1`, then `1 = -2`
    have hu1 : u = -1 := by linear_combination -hpow + u * hu3
    exact absurd (by push_cast; linear_combination hu - (u - 2) * hu1) h3
  · exact h

/-- **Ireland–Rosen, Proposition 13.1.5**: for `d < 0` squarefree, every unit of `ℚ(√d)` is a
root of unity; there are `4` of them (`±1, ±i`) for `d = -1`, `6` (the sixth roots of unity) for
`d = -3`, and `2` (`±1`) otherwise. -/
@[kb "irelandrosen1990" "Prop 13.1.5, p. 191"]
theorem units_quadField {d : ℤ} [Fact (Squarefree d)] [Fact (d ≠ 1)] (hneg : d < 0) :
    (∀ x : (𝓞 (QuadField d))ˣ, x ∈ torsion (QuadField d)) ∧
      torsionOrder (QuadField d) = if d = -1 then 4 else if d = -3 then 6 else 2 := by
  have hK := finrank_quadField d
  have hdisc := discr_quadField d
  have hD : discr (QuadField d) < 0 := by rw [hdisc]; split_ifs <;> omega
  refine ⟨mem_torsion_of_rank_eq_zero (Davenport.rank_eq_zero_of_discr_neg hK hD), ?_⟩
  split_ifs with h1 h3
  · subst h1
    exact torsionOrder_eq_four hK (by rw [hdisc]; norm_num)
  · subst h3
    exact torsionOrder_eq_six hK (by rw [hdisc]; norm_num)
  · refine Davenport.torsionOrder_eq_two_of_discr hK ?_ ?_ <;> rw [hdisc] <;> split_ifs <;> omega

end units

end NTKB.IrelandRosen
