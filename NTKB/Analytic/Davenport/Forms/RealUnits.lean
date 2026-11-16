/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Davenport.Forms.Units
import NTKB.Analytic.Davenport.ClassNumber.Regulator
import NTKB.Analytic.Davenport.ClassNumber.Torsion

/-!
# Davenport, Chapter 6: Pell's equation `t² - d u² = 4` and the unit `ε` (rows 6-4, 6-24)

(§6, pp. 55, 62.) Let `d > 1` be a fundamental discriminant, `K` the real quadratic field of
discriminant `d`, and embed `ℤ[ω]` in `ℝ` by `ω ↦ (σ + √d)/2` (`NTKB.Davenport.realEmb`), so that
the unit `((t - σu)/2) + uω` of norm `1` attached to a solution of `t² - d u² = 4` is
`(t + u√d)/2`.

* **Row 6-4** (`NTKB.Davenport.exists_pellFour_generator`): there is a solution `(t₀, u₀)` with
  `t₀, u₀ > 0` such that, with `ε = (t₀ + u₀√d)/2 > 1`, every solution has
  `(t + u√d)/2 = ± εⁿ` (`n ∈ ℤ`); there are infinitely many automorphs.
* **Row 6-24** (`NTKB.Davenport.formClassNumber_mul_log_eq`): for this `ε`,
  `h(d) log ε = 2 h₁(d) log ε₁`, where `h₁(d)` is the class number of `K` and `log ε₁` its
  regulator: `ε = ε₁` if `N(ε₁) = 1` and `ε = ε₁²` if `N(ε₁) = -1` (with row 6-23).
-/

noncomputable section

open QuadraticAlgebra NTKB.QuadraticField NumberField NumberField.Units

namespace NTKB.Davenport

variable {D : ℤ}

/-! ### The real embedding -/

/-- `(σ + √D)/2`. -/
def rootPlus (D : ℤ) : ℝ := ((D % 4 : ℤ) + √(D : ℝ)) / 2

section emb

variable [Fact (IsFundamentalDiscriminant D)] [Fact (D ≠ 1)]

theorem rootPlus_mul_self (hD : 0 ≤ D) :
    rootPlus D * rootPlus D = ((D / 4 : ℤ) : ℝ) + ((D % 4 : ℤ) : ℝ) * rootPlus D := by
  have hσ : D % 4 * (D % 4) = D % 4 := emod_four_mul_self_of_fact
  have hq : D % 4 + 4 * (D / 4) = D := by omega
  have hσ' : ((D % 4 : ℤ) : ℝ) * ((D % 4 : ℤ) : ℝ) = ((D % 4 : ℤ) : ℝ) := by exact_mod_cast hσ
  have hq' : ((D % 4 : ℤ) : ℝ) + 4 * ((D / 4 : ℤ) : ℝ) = (D : ℝ) := by exact_mod_cast hq
  have hs : √(D : ℝ) * √(D : ℝ) = (D : ℝ) := Real.mul_self_sqrt (by exact_mod_cast hD)
  simp only [rootPlus]
  linear_combination hs / 4 - hσ' / 4 - hq' / 4

/-- The embedding `ℤ[ω] → ℝ`, `ω ↦ (σ + √D)/2`. -/
def realEmb (hD : 0 ≤ D) : Order D →+* ℝ :=
  ((lift ⟨rootPlus D, by rw [zsmul_eq_mul, zsmul_eq_mul, mul_one]; exact rootPlus_mul_self hD⟩ :
    Order D →ₐ[ℤ] ℝ) : Order D →+* ℝ)

theorem realEmb_apply (hD : 0 ≤ D) (z : Order D) : realEmb hD z = z.re + z.im * rootPlus D := by
  simp [realEmb, zsmul_eq_mul]

theorem realEmb_mul_star (hD : 0 ≤ D) (z : Order D) :
    realEmb hD z * realEmb hD (star z) = z.norm := by
  rw [← map_mul, ← intCast_norm, map_intCast]

theorem realEmb_star (hD : 0 ≤ D) (z : Order D) :
    realEmb hD (star z) = z.re + z.im * (((D % 4 : ℤ) : ℝ) - rootPlus D) := by
  rw [realEmb_apply]; simp [star_mk]; ring

/-- `(t - σu)/2 + uω ↦ (t + u√D)/2`. -/
theorem realEmb_normOneEquiv_symm (hD : 0 ≤ D) (p : PellFour D) :
    realEmb hD (normOneEquiv.symm p).1 = (p.1.1 + p.1.2 * √(D : ℝ)) / 2 := by
  have h2 : 2 ∣ p.1.1 - D % 4 * p.1.2 := by
    have := two_dvd_sub_of_pellFour (f := principalForm D)
      (formDisc_principalForm (emod_four_of_isFundamental Fact.out)) p.2
    simpa [principalForm] using this
  obtain ⟨r, hr⟩ := h2
  show realEmb hD ⟨(p.1.1 - D % 4 * p.1.2) / 2, p.1.2⟩ = _
  rw [realEmb_apply]
  simp only
  rw [hr, Int.mul_ediv_cancel_left _ two_ne_zero, rootPlus]
  have : (p.1.1 : ℝ) = 2 * r + (D % 4 : ℤ) * p.1.2 := by
    have : p.1.1 = 2 * r + D % 4 * p.1.2 := by linarith
    exact_mod_cast this
  rw [this]; ring

/-- Every ring homomorphism `ℤ[ω] → ℂ` is `realEmb` or `realEmb ∘ conjugation`. -/
theorem ringHom_cases (hD : 0 ≤ D) (χ : Order D →+* ℂ) :
    (∀ z, χ z = realEmb hD z) ∨ (∀ z, χ z = realEmb hD (star z)) := by
  have hz : ∀ z : Order D, z = (z.re : Order D) + (z.im : Order D) * ω := fun z ↦ by ext <;> simp
  have hc : χ ω * χ ω = ((D / 4 : ℤ) : ℂ) + ((D % 4 : ℤ) : ℂ) * χ ω := by
    rw [← map_mul, show (ω * ω : Order D) = ((D / 4 : ℤ) : Order D) + ((D % 4 : ℤ) : Order D) * ω
      by ext <;> simp, map_add, map_mul, map_intCast, map_intCast]
  have hr := rootPlus_mul_self hD
  have hr' : ((rootPlus D : ℝ) : ℂ) * (rootPlus D : ℂ) =
      ((D / 4 : ℤ) : ℂ) + ((D % 4 : ℤ) : ℂ) * (rootPlus D : ℂ) := by exact_mod_cast hr
  have hprod : (χ ω - rootPlus D) * (χ ω - (((D % 4 : ℤ) : ℂ) - rootPlus D)) = 0 := by
    linear_combination hc - hr'
  rcases mul_eq_zero.mp hprod with h | h
  · left; intro z
    rw [hz z, map_add, map_mul, map_intCast, map_intCast, sub_eq_zero.mp h, realEmb_apply]
    simp
  · right; intro z
    rw [hz z, map_add, map_mul, map_intCast, map_intCast, sub_eq_zero.mp h, realEmb_star]
    simp

end emb

/-! ### Places -/

section places

variable {K : Type*} [Field K] [NumberField K] [Fact (IsFundamentalDiscriminant D)] [Fact (D ≠ 1)]

theorem place_cases (hD : 0 ≤ D) (e : Order D ≃+* 𝓞 K) (w : InfinitePlace K) :
    (∀ z, w ((e z : 𝓞 K) : K) = |realEmb hD z|) ∨
      (∀ z, w ((e z : 𝓞 K) : K) = |realEmb hD (star z)|) := by
  let χ : Order D →+* ℂ := w.embedding.comp ((algebraMap (𝓞 K) K).comp e.toRingHom)
  have hw : ∀ z, w ((e z : 𝓞 K) : K) = ‖χ z‖ := fun z ↦ (w.norm_embedding_eq _).symm
  rcases ringHom_cases hD χ with h | h
  · left; intro z; rw [hw, h, Complex.norm_real, Real.norm_eq_abs]
  · right; intro z; rw [hw, h, Complex.norm_real, Real.norm_eq_abs]

theorem abs_realEmb_mul_abs_realEmb_star (hD : 0 ≤ D) (u : (Order D)ˣ) :
    |realEmb hD (u : Order D)| * |realEmb hD (star (u : Order D))| = 1 := by
  rw [← abs_mul, realEmb_mul_star]
  rcases Int.isUnit_iff.mp ((u.isUnit).map QuadraticAlgebra.norm) with h | h <;> rw [h] <;> simp

theorem abs_log_place_eq (hD : 0 ≤ D) (e : Order D ≃+* 𝓞 K) (w : InfinitePlace K)
    (u : (Order D)ˣ) :
    |Real.log (w ((e u : 𝓞 K) : K))| = |Real.log (abs (realEmb hD (u : Order D)))| := by
  have h1 := abs_realEmb_mul_abs_realEmb_star hD u
  have hpos : 0 < |realEmb hD (u : Order D)| := by
    rcases eq_or_lt_of_le (abs_nonneg (realEmb hD (u : Order D))) with h | h
    · rw [← h, zero_mul] at h1; norm_num at h1
    · exact h
  rcases place_cases hD e w with h | h
  · rw [h]
  · have hinv : |realEmb hD (star (u : Order D))| = (|realEmb hD (u : Order D)|)⁻¹ := by
      rw [eq_comm, inv_eq_iff_eq_inv, eq_comm]
      exact (eq_inv_of_mul_eq_one_left h1).symm
    rw [h, hinv, Real.log_inv, abs_neg]

end places

/-! ### The units of a real quadratic field -/

section unitgroup

variable {K : Type*} [Field K] [NumberField K]

theorem one_ne_neg_one_units : (1 : (𝓞 K)ˣ) ≠ -1 := by
  intro h
  have := congrArg (fun u : (𝓞 K)ˣ ↦ ((u : 𝓞 K) : K)) h
  simp only [Units.val_one, Units.val_neg, map_one, map_neg] at this
  norm_num at this

/-- In a real quadratic field the roots of unity are `±1`. -/
theorem eq_one_or_neg_one_of_mem_torsion (hK : Module.finrank ℚ K = 2) (hD : 0 < discr K)
    {ζ : (𝓞 K)ˣ} (hζ : ζ ∈ torsion K) : ζ = 1 ∨ ζ = -1 := by
  have h2 : Nat.card (torsion K) = 2 :=
    NTKB.Davenport.torsionOrder_eq_two_of_discr hK (by omega) (by omega)
  obtain ⟨x, y, hxy, huniv⟩ := Nat.card_eq_two_iff.mp h2
  have mem : ∀ t : torsion K, t = x ∨ t = y := fun t ↦ by
    have : t ∈ ({x, y} : Set (torsion K)) := huniv ▸ Set.mem_univ t
    simpa using this
  have h1 : (⟨1, one_mem _⟩ : torsion K) ≠ ⟨-1, neg_one_mem_torsion⟩ := fun h ↦
    one_ne_neg_one_units (congrArg Subtype.val h)
  by_contra hne
  push Not at hne
  have hζ1 : (⟨ζ, hζ⟩ : torsion K) ≠ ⟨1, one_mem _⟩ := fun h ↦ hne.1 (congrArg Subtype.val h)
  have hζ2 : (⟨ζ, hζ⟩ : torsion K) ≠ ⟨-1, neg_one_mem_torsion⟩ :=
    fun h ↦ hne.2 (congrArg Subtype.val h)
  rcases mem ⟨1, one_mem _⟩ with a | a <;> rcases mem ⟨-1, neg_one_mem_torsion⟩ with b | b <;>
    rcases mem ⟨ζ, hζ⟩ with c | c
  all_goals first
    | exact h1 (a.trans b.symm) | exact hζ1 (c.trans a.symm) | exact hζ2 (c.trans b.symm)

/-- Every unit is `± ηⁿ` for a fundamental unit `η`. -/
theorem eq_zpow_or_neg_zpow (hK : Module.finrank ℚ K = 2) (hD : 0 < discr K) {η : (𝓞 K)ˣ}
    (hη : Subgroup.closure {η} ⊔ torsion K = ⊤) (x : (𝓞 K)ˣ) :
    ∃ n : ℤ, x = η ^ n ∨ x = -η ^ n := by
  have hx : x ∈ Subgroup.closure {η} ⊔ torsion K := hη ▸ Subgroup.mem_top x
  obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup.mp hx
  obtain ⟨n, rfl⟩ := Subgroup.mem_closure_singleton.mp hy
  refine ⟨n, ?_⟩
  rcases eq_one_or_neg_one_of_mem_torsion hK hD hz with rfl | rfl
  · left; rw [mul_one]
  · right; rw [mul_neg_one]

end unitgroup

section order

variable {K : Type*} [Field K] [NumberField K] [Fact (IsFundamentalDiscriminant D)] [Fact (D ≠ 1)]

theorem neg_zpow_cases {G : Type*} [Group G] [HasDistribNeg G] (x : G) (n : ℤ) :
    (-x) ^ n = x ^ n ∨ (-x) ^ n = -x ^ n := by
  rcases Int.even_or_odd n with h | h
  · left; exact h.neg_zpow x
  · right; exact h.neg_zpow x

theorem realEmb_units_zpow (hD : 0 ≤ D) (u : (Order D)ˣ) (n : ℤ) :
    realEmb hD ((u ^ n : (Order D)ˣ) : Order D) = realEmb hD (u : Order D) ^ n := by
  calc realEmb hD ((u ^ n : (Order D)ˣ) : Order D)
      = ((Units.map (realEmb hD : Order D →* ℝ) (u ^ n) : ℝˣ) : ℝ) := rfl
    _ = (((Units.map (realEmb hD : Order D →* ℝ) u) ^ n : ℝˣ) : ℝ) := by rw [map_zpow]
    _ = ((Units.map (realEmb hD : Order D →* ℝ) u : ℝˣ) : ℝ) ^ n := Units.val_zpow_eq_zpow_val _ _
    _ = realEmb hD (u : Order D) ^ n := rfl

theorem realEmb_neg_units (hD : 0 ≤ D) (u : (Order D)ˣ) :
    realEmb hD ((-u : (Order D)ˣ) : Order D) = -realEmb hD (u : Order D) := by
  rw [Units.val_neg, map_neg]

/-- The norm on units, with values in `ℤˣ = {±1}`. -/
def normUnits (D : ℤ) : (Order D)ˣ →* ℤˣ := Units.map (QuadraticAlgebra.norm : Order D →* ℤ)

theorem val_normUnits (u : (Order D)ˣ) : ((normUnits D u : ℤˣ) : ℤ) = (u : Order D).norm := rfl

theorem normUnits_neg (u : (Order D)ˣ) : normUnits D (-u) = normUnits D u := by
  ext; rw [val_normUnits, val_normUnits, Units.val_neg, QuadraticAlgebra.norm_neg]

theorem norm_eq_one_iff (u : (Order D)ˣ) : (u : Order D).norm = 1 ↔ normUnits D u = 1 := by
  rw [← val_normUnits, Units.val_eq_one]

/-- Choosing `±v^{±1} > 1`. -/
theorem exists_gt_one (hD : 0 ≤ D) (v : (Order D)ˣ) (hv : Real.log |realEmb hD (v : Order D)| ≠ 0) :
    ∃ ε : (Order D)ˣ, 1 < realEmb hD (ε : Order D) ∧
      Real.log (realEmb hD (ε : Order D)) = |Real.log (abs (realEmb hD (v : Order D)))| ∧
      ∃ s : ℤ, (s = 1 ∨ s = -1) ∧ (v = ε ^ s ∨ v = -ε ^ s) := by
  set x := realEmb hD (v : Order D)
  have hx0 : x ≠ 0 := by intro h; rw [h, abs_zero, Real.log_zero] at hv; exact hv rfl
  have hxabs : |x| ≠ 1 := by intro h; rw [h, Real.log_one] at hv; exact hv rfl
  have hinv : realEmb hD ((v⁻¹ : (Order D)ˣ) : Order D) = x⁻¹ := by
    rw [← zpow_neg_one, realEmb_units_zpow, zpow_neg_one]
  rcases lt_or_gt_of_ne hxabs with hlt | hgt
  · -- `|x| < 1`: use `v⁻¹`
    have hlog : Real.log |x| < 0 := Real.log_neg (abs_pos.mpr hx0) hlt
    have hgt' : 1 < |x⁻¹| := by rw [abs_inv]; exact one_lt_inv_iff₀.mpr ⟨abs_pos.mpr hx0, hlt⟩
    rcases lt_or_gt_of_ne hx0 with hneg | hpos
    · refine ⟨-v⁻¹, ?_, ?_, -1, Or.inr rfl, Or.inr ?_⟩
      · rw [realEmb_neg_units, hinv]; rw [abs_of_neg (inv_lt_zero.mpr hneg)] at hgt'; exact hgt'
      · rw [realEmb_neg_units, hinv, abs_of_neg hlog, ← abs_of_neg (inv_lt_zero.mpr hneg), abs_inv,
          Real.log_inv]
      · rw [zpow_neg_one, inv_neg, inv_inv, neg_neg]
    · refine ⟨v⁻¹, ?_, ?_, -1, Or.inr rfl, Or.inl ?_⟩
      · rw [hinv]; rw [abs_of_pos (inv_pos.mpr hpos)] at hgt'; exact hgt'
      · rw [hinv, abs_of_neg hlog, ← abs_of_pos (inv_pos.mpr hpos), abs_inv, Real.log_inv]
      · rw [zpow_neg_one, inv_inv]
  · have hlog : 0 < Real.log |x| := Real.log_pos hgt
    rcases lt_or_gt_of_ne hx0 with hneg | hpos
    · refine ⟨-v, ?_, ?_, 1, Or.inl rfl, Or.inr ?_⟩
      · rw [realEmb_neg_units]; rw [abs_of_neg hneg] at hgt; exact hgt
      · rw [realEmb_neg_units, abs_of_pos hlog, abs_of_neg hneg]
      · rw [zpow_one, neg_neg]
    · refine ⟨v, ?_, ?_, 1, Or.inl rfl, Or.inl ?_⟩
      · rw [abs_of_pos hpos] at hgt; exact hgt
      · rw [abs_of_pos hlog, abs_of_pos hpos]
      · rw [zpow_one]

theorem generator_transfer {ε₁ ε : (Order D)ˣ} {s : ℤ} (hs : s = 1 ∨ s = -1)
    (hε : ε₁ = ε ^ s ∨ ε₁ = -ε ^ s) {u : (Order D)ˣ} {m : ℤ} (hu : u = ε₁ ^ m ∨ u = -ε₁ ^ m) :
    ∃ n : ℤ, u = ε ^ n ∨ u = -ε ^ n := by
  refine ⟨s * m, ?_⟩
  rcases hε with rfl | rfl
  · rw [← zpow_mul] at hu; exact hu
  · rcases neg_zpow_cases (ε ^ s) m with h | h <;> rw [h, ← zpow_mul] at hu
    · exact hu
    · rcases hu with hu | hu
      · right; exact hu
      · left; rw [hu, neg_neg]

/-- **Davenport §6, pp. 55, 62 (rows 6-4, 6-24).** For `D > 0` there is a unit `ε` of norm `1`
with `realEmb ε > 1` such that every unit of norm `1` is `± εⁿ`; `log ε` is twice the regulator
of `K` if there is a unit of norm `-1`, and the regulator otherwise. -/
theorem exists_normOne_generator (hK : Module.finrank ℚ K = 2) (e : Order D ≃+* 𝓞 K)
    (hD : 0 < D) (hDK : discr K = D) :
    ∃ ε : (Order D)ˣ, (ε : Order D).norm = 1 ∧ 1 < realEmb hD.le (ε : Order D) ∧
      (∀ u : (Order D)ˣ, (u : Order D).norm = 1 → ∃ n : ℤ, u = ε ^ n ∨ u = -ε ^ n) ∧
      ((∃ u : (Order D)ˣ, (u : Order D).norm = -1) →
        Real.log (realEmb hD.le (ε : Order D)) = 2 * regulator K) ∧
      ((¬ ∃ u : (Order D)ˣ, (u : Order D).norm = -1) →
        Real.log (realEmb hD.le (ε : Order D)) = regulator K) := by
  have hDK' : 0 < discr K := hDK ▸ hD
  obtain ⟨ηK, hηK⟩ := exists_fundamental_unit hK hDK'
  let E : (Order D)ˣ ≃* (𝓞 K)ˣ := Units.mapEquiv e.toMulEquiv
  set η₀ := E.symm ηK
  have hEη : E η₀ = ηK := E.apply_symm_apply ηK
  obtain ⟨w⟩ : Nonempty (InfinitePlace K) := inferInstance
  have hR : regulator K = |Real.log (abs (realEmb hD.le (η₀ : Order D)))| := by
    rw [regulator_eq_abs_log hK hDK' ηK hηK w, ← hEη, ← abs_log_place_eq hD.le e w η₀]; rfl
  have hRpos : 0 < regulator K :=
    lt_of_lt_of_le (Real.log_pos (by norm_num)) (log_three_halves_le_regulator hK hDK')
  -- every unit is `± η₀ⁿ`
  have hneg : ∀ x : (Order D)ˣ, E (-x) = -E x := fun x ↦ Units.ext (by simp [E])
  have hall : ∀ u : (Order D)ˣ, ∃ n : ℤ, u = η₀ ^ n ∨ u = -η₀ ^ n := by
    intro u
    obtain ⟨n, h⟩ := eq_zpow_or_neg_zpow hK hDK' hηK (E u)
    refine ⟨n, ?_⟩
    rcases h with h | h
    · left; apply E.injective; rw [h, map_zpow, hEη]
    · right; apply E.injective
      rw [h, hneg, map_zpow, hEη]
  have hnorm_pm : ∀ (u : (Order D)ˣ) (n : ℤ), (u = η₀ ^ n ∨ u = -η₀ ^ n) →
      normUnits D u = normUnits D η₀ ^ n := by
    rintro u n (rfl | rfl)
    · rw [map_zpow]
    · rw [normUnits_neg, map_zpow]
  rcases Int.units_eq_one_or (normUnits D η₀) with h1 | h1
  · -- `N(η₀) = 1`: `ε₁ = η₀`, no unit of norm `-1`
    have hlog0 : Real.log |realEmb hD.le (η₀ : Order D)| ≠ 0 := by
      intro h; rw [h, abs_zero] at hR; linarith
    obtain ⟨ε, hε1, hεlog, s, hs, hεs⟩ := exists_gt_one hD.le η₀ hlog0
    have hno : ¬ ∃ u : (Order D)ˣ, (u : Order D).norm = -1 := by
      rintro ⟨u, hu⟩
      obtain ⟨n, hn⟩ := hall u
      have := hnorm_pm u n hn
      rw [h1, one_zpow] at this
      have h' := congrArg (fun x : ℤˣ ↦ (x : ℤ)) this
      simp only [val_normUnits, Units.val_one] at h'
      rw [hu] at h'; norm_num at h'
    refine ⟨ε, ?_, hε1, fun u _ ↦ ?_, fun h ↦ absurd h hno, fun _ ↦ by rw [hεlog, ← hR]⟩
    · have : normUnits D η₀ = normUnits D ε ^ s := by
        rcases hεs with h | h
        · rw [h, map_zpow]
        · rw [h, normUnits_neg, map_zpow]
      rw [norm_eq_one_iff]
      rcases hs with rfl | rfl
      · rw [zpow_one] at this; rw [← this, h1]
      · rw [zpow_neg_one, h1] at this; rw [inv_eq_one.mp this.symm]
    · obtain ⟨n, hn⟩ := hall u
      exact generator_transfer hs hεs hn
  · -- `N(η₀) = -1`: `ε₁ = η₀²`
    have hlog0 : Real.log |realEmb hD.le ((η₀ ^ (2 : ℤ) : (Order D)ˣ) : Order D)| ≠ 0 := by
      rw [realEmb_units_zpow, abs_zpow, Real.log_zpow]
      intro h; rcases mul_eq_zero.mp h with h | h
      · norm_num at h
      · rw [h, abs_zero] at hR; linarith
    obtain ⟨ε, hε1, hεlog, s, hs, hεs⟩ := exists_gt_one hD.le (η₀ ^ (2 : ℤ)) hlog0
    have hyes : ∃ u : (Order D)ˣ, (u : Order D).norm = -1 :=
      ⟨η₀, by rw [← val_normUnits, h1]; rfl⟩
    refine ⟨ε, ?_, hε1, fun u hu ↦ ?_, fun _ ↦ ?_, fun h ↦ absurd hyes h⟩
    · have : normUnits D (η₀ ^ (2 : ℤ)) = normUnits D ε ^ s := by
        rcases hεs with h | h
        · rw [h, map_zpow]
        · rw [h, normUnits_neg, map_zpow]
      rw [map_zpow, h1] at this
      norm_num at this
      rw [norm_eq_one_iff]
      rcases hs with rfl | rfl
      · rw [zpow_one] at this; exact this.symm
      · rw [zpow_neg_one] at this; exact inv_eq_one.mp this.symm
    · obtain ⟨n, hn⟩ := hall u
      have hN := hnorm_pm u n hn
      rw [(norm_eq_one_iff u).mp hu, h1] at hN
      rcases Int.even_or_odd n with ⟨m, rfl⟩ | hodd
      · have hu' : u = (η₀ ^ (2 : ℤ)) ^ m ∨ u = -(η₀ ^ (2 : ℤ)) ^ m := by
          rw [← zpow_mul, show 2 * m = m + m by ring]; exact hn
        exact generator_transfer hs hεs hu'
      · rw [hodd.neg_one_zpow] at hN; exact absurd hN (by decide)
    · rw [hεlog, realEmb_units_zpow, abs_zpow, Real.log_zpow, hR, abs_mul]; norm_num

end order

end NTKB.Davenport
