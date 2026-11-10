/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import NTKB.Port.JacobiThetaNearCusp
import NTKB.Attr

/-!
# The reciprocity law for the sums `S(a, m)` (Apostol, Theorem 9.16)

For positive integers `a, m`, Apostol (§9.10) defines `S(a, m) = ∑_{r=0}^{m-1} e^{πi a r²/m}` and
proves, when `ma` is even, `S(a, m) = √(m/a) · (1 + i)/√2 · conj S(m, a)` (Theorem 9.16, (31)).

Apostol's proof is by residue calculus. We use the Jacobi theta function instead (the classical
route of Landsberg and Schaar; the special case `a = 2` along these lines is Tau Ceti's
`sum_range_cexp_two_pi_I_sq_div`). With `θ(τ) = ∑_n e^{πi n² τ}` (Mathlib's `jacobiTheta₂ 0`):

* splitting `n` into residue classes mod `m` and applying the functional equation
  `jacobiTheta₂_functional_equation` to each class gives, for `p m` even and `im w > 0`, the exact
  formula `jacobiTheta₂_zero_div_add`:
  `θ(p/m + w) = (-i m² w)^{-1/2} ∑_{r<m} e^{πi p r²/m} θ₂(r/m, -1/(m² w))`;
* at `τ = a/m + it` this expresses `θ(τ)` through `S(a, m)`; the functional equation
  `θ(τ) = (-iτ)^{-1/2} θ(-1/τ)` and the formula again at `-1/τ = -m/a + w'` express `θ(τ)` through
  `conj S(m, a)`. The square roots combine to the constant `√(m/a)(1 + i)/√2` exactly, for every
  `t > 0` (`sum_mul_jacobiTheta₂_eq`);
* as `t → 0⁺` the theta values tend to `1` (`NTKB.Port.tendsto_jacobiTheta₂_of_im_eq_zero`).
-/

open Complex Filter Topology Finset
open scoped Real ComplexConjugate

namespace NTKB.Apostol

/-- Apostol's sum `S(a, m) = ∑_{r=0}^{m-1} e^{πi a r²/m}` (§9.10). -/
noncomputable def quadSumS (a m : ℕ) : ℂ :=
  ∑ r ∈ range m, cexp (π * I * a * r ^ 2 / m)

/-- Splitting a summable series over `ℤ` into the residue classes modulo `m`. -/
theorem tsum_int_eq_sum_range_tsum {f : ℤ → ℂ} (hf : Summable f) (m : ℕ) [NeZero m] :
    ∑' n, f n = ∑ r ∈ range m, ∑' q : ℤ, f (q * m + r) := by
  set e : ℤ ≃ Fin m × ℤ := (Int.divModEquiv m).trans (Equiv.prodComm _ _) with he
  have hs : Summable (f ∘ e.symm) := e.symm.summable_iff.mpr hf
  have hslice (r : Fin m) : HasSum (fun q : ℤ ↦ (f ∘ e.symm) (r, q)) (∑' q : ℤ, f (q * m + r)) := by
    have := (hs.prod_factor r).hasSum
    simpa [he, Int.divModEquiv] using this
  have hfib := (e.symm.hasSum_iff.mpr hf.hasSum).prod_fiberwise hslice
  rw [← Fin.sum_univ_eq_sum_range (fun r ↦ ∑' q : ℤ, f (q * m + r))]
  exact (hfib.unique (hasSum_fintype _)).trans rfl

/-- Adding an integer multiple of `2πi` does not change `cexp`. -/
theorem cexp_add_int_mul_two_pi_I' (x : ℂ) (k : ℤ) :
    cexp (x + k * (2 * π * I)) = cexp x := by
  rw [Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- Splitting `θ(p/m + w)` into the residue classes of `n` modulo `m` (`p m` even): on the class of
`r` the factor `e^{πi n² p/m}` is the constant `e^{πi p r²/m}`, and the shifted theta series in
`T = m² w` is transformed by the functional equation. -/
theorem jacobiTheta₂_zero_div_add (m : ℕ) [NeZero m] (p : ℤ) (hp : Even (p * m)) {w : ℂ}
    (hw : 0 < w.im) :
    jacobiTheta₂ 0 (p / m + w) = 1 / (-I * (m ^ 2 * w)) ^ (1 / 2 : ℂ) *
      ∑ r ∈ range m, cexp (π * I * p * r ^ 2 / m) * jacobiTheta₂ (r / m) (-1 / (m ^ 2 * w)) := by
  have hm : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne m)
  have hw0 : w ≠ 0 := fun h ↦ by simp [h] at hw
  obtain ⟨c, hc⟩ := hp
  set T : ℂ := m ^ 2 * w with hT
  have hT0 : T ≠ 0 := mul_ne_zero (pow_ne_zero 2 hm) hw0
  have hτ : 0 < ((p : ℂ) / m + w).im := by
    rw [add_im, ← ofReal_intCast, ← ofReal_natCast, ← ofReal_div, ofReal_im, zero_add]
    exact hw
  rw [jacobiTheta₂, tsum_int_eq_sum_range_tsum ((summable_jacobiTheta₂_term_iff _ _).2 hτ) m,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ ↦ ?_
  set b : ℂ := (r : ℂ) / m with hb
  have hterm (q : ℤ) : jacobiTheta₂_term (q * m + r) 0 (p / m + w) =
      cexp (π * I * p * r ^ 2 / m) * cexp (π * I * T * b ^ 2) *
        jacobiTheta₂_term q (T * b) T := by
    rw [jacobiTheta₂_term, jacobiTheta₂_term, ← Complex.exp_add, ← Complex.exp_add,
      ← cexp_add_int_mul_two_pi_I' _ (-(c * q ^ 2 + p * q * r))]
    congr 1
    have hc' : ((p : ℂ) * m) = c + c := by exact_mod_cast hc
    rw [hT, hb]
    push_cast
    field_simp
    linear_combination ((q : ℂ) ^ 2 * m) * hc'
  rw [tsum_congr hterm, tsum_mul_left, ← jacobiTheta₂, jacobiTheta₂_functional_equation,
    mul_div_cancel_left₀ _ hT0]
  have hcancel : cexp (π * I * T * b ^ 2) * cexp (-π * I * (T * b) ^ 2 / T) = 1 := by
    rw [← Complex.exp_add, ← Complex.exp_zero]
    congr 1
    field_simp
    ring
  linear_combination (1 / (-I * T) ^ (1 / 2 : ℂ) * cexp (π * I * p * r ^ 2 / m) *
    jacobiTheta₂ b (-1 / T)) * hcancel


/-- The principal square root of `w ^ 2` is `w` when `w` lies in the right half-plane. -/
theorem cpow_one_div_two_eq_of_sq {w z : ℂ} (h : w ^ 2 = z) (hw : 0 < w.re) :
    z ^ (1 / 2 : ℂ) = w := by
  rw [← h, one_div]
  exact sq_cpow_two_inv hw

/-- The constant `√(m/a) · (1 + i)/√2` of the reciprocity law. -/
noncomputable def sReciprocityConst (a m : ℕ) : ℂ :=
  (√((m : ℝ) / a) : ℂ) * ((1 + I) / (√2 : ℝ))

/-- The two expansions of `θ(a/m + it)`, equated: for every `t > 0`,
`∑_{r<m} e^{πi a r²/m} θ₂(r/m, i/(m²t)) = √(m/a)(1 + i)/√2 · ∑_{r<a} e^{-πi m r²/a} θ₂(r/a, i/(m²t) - 1/(am))`. -/
theorem sum_mul_jacobiTheta₂_eq {a m : ℕ} (ha : 0 < a) (hm : 0 < m) (h : Even (m * a)) {t : ℝ}
    (ht : 0 < t) :
    ∑ r ∈ range m, cexp (π * I * a * r ^ 2 / m) * jacobiTheta₂ (r / m) (I / ((m : ℂ) ^ 2 * t)) =
      sReciprocityConst a m * ∑ r ∈ range a, cexp (π * I * ((-m : ℤ) : ℂ) * r ^ 2 / a) *
        jacobiTheta₂ (r / a) (I / ((m : ℂ) ^ 2 * t) - 1 / (a * m)) := by
  have : NeZero m := ⟨hm.ne'⟩
  have : NeZero a := ⟨ha.ne'⟩
  have hm0 : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
  have ha0 : (a : ℂ) ≠ 0 := Nat.cast_ne_zero.2 ha.ne'
  have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.2 ht.ne'
  have hmR : (0 : ℝ) < m := Nat.cast_pos.2 hm
  have haR : (0 : ℝ) < a := Nat.cast_pos.2 ha
  set τ : ℂ := a / m + I * t with hτ
  have hτre : τ.re = a / m := by simp [hτ]
  have hτim : τ.im = t := by simp [hτ]
  have hτ0 : τ ≠ 0 := fun h0 ↦ ht.ne' (by rw [← hτim, h0, zero_im])
  -- First expansion: residue classes mod `m`.
  have hA := jacobiTheta₂_zero_div_add m (a : ℤ) (by rw [mul_comm]; exact_mod_cast h)
    (w := I * t) (by simpa using ht)
  have hA1 : (-I * ((m : ℂ) ^ 2 * (I * t))) ^ (1 / 2 : ℂ) = (m : ℂ) * (√t : ℝ) := by
    refine cpow_one_div_two_eq_of_sq ?_ ?_
    · rw [mul_pow, ← ofReal_pow, Real.sq_sqrt ht.le]
      ring_nf
      rw [I_sq]
      ring
    · rw [← ofReal_natCast, ← ofReal_mul, ofReal_re]
      exact mul_pos hmR (Real.sqrt_pos.2 ht)
  have hA2 : -1 / ((m : ℂ) ^ 2 * (I * t)) = I / ((m : ℂ) ^ 2 * t) := by
    field_simp
    rw [I_sq]
  push_cast at hA
  rw [hA1, hA2] at hA
  -- Second expansion: the functional equation, then residue classes mod `a` at `-1/τ`.
  have hF := jacobiTheta₂_functional_equation 0 τ
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_div,
    Complex.exp_zero, mul_one] at hF
  set w' : ℂ := -1 / τ + m / a with hw'
  have hw'eq : w' = I * m * t / (a * τ) := by
    have hden : (a : ℂ) + m * I * t ≠ 0 := by
      have : (a : ℂ) + m * I * t = m * τ := by rw [hτ]; field_simp
      rw [this]; exact mul_ne_zero hm0 hτ0
    rw [hw', hτ]
    field_simp
    ring
  have hw'im : 0 < w'.im := by
    have : w'.im = (-1 / τ).im := by
      rw [hw', add_im, ← ofReal_natCast, ← ofReal_natCast, ← ofReal_div, ofReal_im, add_zero]
    rw [this, neg_div, neg_im, one_div, inv_im, neg_div, neg_neg, hτim]
    exact div_pos ht (normSq_pos.2 hτ0)
  have hmτ : -1 / τ = ((-m : ℤ) : ℂ) / a + w' := by
    rw [hw']; push_cast; ring
  have hB := jacobiTheta₂_zero_div_add a (-m : ℤ)
    (by rw [Int.neg_mul, even_neg]; exact_mod_cast h) hw'im
  rw [← hmτ] at hB
  have hB2 : -1 / ((a : ℂ) ^ 2 * w') = I / ((m : ℂ) ^ 2 * t) - 1 / (a * m) := by
    rw [hw'eq, hτ]
    field_simp
    ring_nf
    rw [I_sq]
    ring
  rw [hB2] at hB
  -- The square roots.
  set u : ℂ := (-I * τ) ^ (1 / 2 : ℂ) with hu
  have hu2 : u ^ 2 = -I * τ := by
    rw [hu, one_div]; exact cpow_ofNat_inv_pow _ 2
  have hIτre : (-I * τ).re = t := by simp [hτ]
  have hIτim : (-I * τ).im = -(a / m) := by simp [hτ]
  have hure : 0 < u.re := by
    rw [hu, one_div, cpow_inv_two_re, hIτre]
    refine Real.sqrt_pos.2 (div_pos ?_ two_pos)
    have := Complex.abs_re_le_norm (-I * τ)
    rw [hIτre, abs_of_pos ht] at this
    linarith
  have huim : u.im ≤ 0 := by
    have hneg : (-I * τ).im < 0 := by
      rw [hIτim]; exact neg_neg_of_pos (div_pos haR hmR)
    rw [hu, one_div, cpow_inv_two_im_eq_neg_sqrt hneg]
    exact neg_nonpos.2 (Real.sqrt_nonneg _)
  have hu0 : u ≠ 0 := fun h0 ↦ by simp [h0] at hure
  set sa : ℝ := √(a : ℝ)
  set sm : ℝ := √(m : ℝ)
  set st : ℝ := √t
  set s2 : ℝ := √2
  have hsa : sa ^ 2 = a := Real.sq_sqrt haR.le
  have hsm : sm ^ 2 = m := Real.sq_sqrt hmR.le
  have hst : st ^ 2 = t := Real.sq_sqrt ht.le
  have hs2 : s2 ^ 2 = 2 := Real.sq_sqrt zero_le_two
  have hsapos : 0 < sa := Real.sqrt_pos.2 haR
  have hsmpos : 0 < sm := Real.sqrt_pos.2 hmR
  have hstpos : 0 < st := Real.sqrt_pos.2 ht
  have hs2pos : 0 < s2 := Real.sqrt_pos.2 two_pos
  have hv : (-I * ((a : ℂ) ^ 2 * w')) ^ (1 / 2 : ℂ) =
      (sa : ℂ) * sm * st * (1 - I) / (s2 * u) := by
    refine cpow_one_div_two_eq_of_sq ?_ ?_
    · have e1 : ((sa : ℂ) * sm * st) ^ 2 = a * m * t := by
        rw [← ofReal_mul, ← ofReal_mul, ← ofReal_pow, mul_pow, mul_pow, hsa, hsm, hst]
        push_cast; ring
      have e2 : ((s2 : ℂ)) ^ 2 = 2 := by rw [← ofReal_pow, hs2]; push_cast; ring
      have e3 : (1 - I) ^ 2 = -2 * I := by ring_nf; rw [I_sq]; ring
      calc ((sa : ℂ) * sm * st * (1 - I) / (s2 * u)) ^ 2
          = ((sa : ℂ) * sm * st) ^ 2 * (1 - I) ^ 2 / ((s2 : ℂ) ^ 2 * u ^ 2) := by ring
        _ = a * m * t * (-2 * I) / (2 * (-I * τ)) := by rw [e1, e2, e3, hu2]
        _ = -I * ((a : ℂ) ^ 2 * w') := by
          rw [hw'eq]
          field_simp
          ring_nf
          rw [I_sq]
          ring
    · have hre : ((sa : ℂ) * sm * st * (1 - I) / (s2 * u)).re =
          sa * sm * st / s2 * ((u.re - u.im) / normSq u) := by
        rw [div_eq_mul_inv, mul_inv, ← ofReal_inv]
        simp only [mul_re, mul_im, ofReal_re, ofReal_im, sub_re, sub_im, one_re, one_im, I_re,
          I_im, inv_re, inv_im]
        field_simp
        ring
      rw [hre]
      refine mul_pos (by positivity) (div_pos (by linarith) (normSq_pos.2 hu0))
  rw [hv] at hB
  rw [hB] at hF
  rw [hA] at hF
  -- `hF` : (1/(m√t)) ΣA = (1/u) · (1/v) · ΣB; solve for ΣA.
  rw [sReciprocityConst, Real.sqrt_div' _ haR.le]
  generalize ∑ r ∈ range m, cexp (π * I * a * r ^ 2 / m) *
    jacobiTheta₂ (r / m) (I / ((m : ℂ) ^ 2 * t)) = SA at hF ⊢
  generalize ∑ r ∈ range a, cexp (π * I * ((-m : ℤ) : ℂ) * r ^ 2 / a) *
    jacobiTheta₂ (r / a) (I / ((m : ℂ) ^ 2 * t) - 1 / (a * m)) = SB at hF ⊢
  have h1I : (1 - I) ≠ 0 := fun h0 ↦ by simpa using congrArg im h0
  have hsa0 : (sa : ℂ) ≠ 0 := ofReal_ne_zero.2 hsapos.ne'
  have hsm0 : (sm : ℂ) ≠ 0 := ofReal_ne_zero.2 hsmpos.ne'
  have hst0 : (st : ℂ) ≠ 0 := ofReal_ne_zero.2 hstpos.ne'
  have hs20 : (s2 : ℂ) ≠ 0 := ofReal_ne_zero.2 hs2pos.ne'
  have hmC : (m : ℂ) = (sm : ℂ) ^ 2 := by rw [← ofReal_pow, hsm, ofReal_natCast]
  have h2C : (2 : ℂ) = (s2 : ℂ) ^ 2 := by rw [← ofReal_pow, hs2]; norm_num
  rw [hmC] at hF
  field_simp at hF ⊢
  have key : SA * s2 * sa = SB * sm * (1 + I) := by
    apply mul_left_cancel₀ hs20
    linear_combination (1 + I) * hF - SA * sa * h2C + SA * sa * I_sq
  change SA * (s2 : ℂ) = SB * ((sm / sa : ℝ) : ℂ) * (1 + I)
  rw [ofReal_div]
  field_simp
  linear_combination key


theorem conj_quadSumS (m a : ℕ) :
    conj (quadSumS m a) = ∑ r ∈ range a, cexp (π * I * ((-m : ℤ) : ℂ) * r ^ 2 / a) := by
  rw [quadSumS, map_sum]
  refine sum_congr rfl fun r _ ↦ ?_
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_div₀, map_mul, map_pow, conj_ofReal, conj_I, map_natCast]
  push_cast
  ring

/-- **Theorem 9.16** (Apostol). For positive integers `a, m` with `ma` even,
`S(a, m) = √(m/a) · (1 + i)/√2 · conj S(m, a)`, where `S(a, m) = ∑_{r=0}^{m-1} e^{πi a r²/m}`. -/
@[kb "apostol1976" "Thm 9.16, p. 196"]
theorem apostol_thm_9_16 {a m : ℕ} (ha : 0 < a) (hm : 0 < m) (h : Even (m * a)) :
    quadSumS a m = (√((m : ℝ) / a) : ℂ) * ((1 + I) / (√2 : ℝ)) * conj (quadSumS m a) := by
  have hmR : (0 : ℝ) < m := Nat.cast_pos.2 hm
  have hm2 : (0 : ℝ) < (m : ℝ) ^ 2 := by positivity
  have hI : Tendsto (fun t : ℝ ↦ I / ((m : ℂ) ^ 2 * t)) (𝓝[>] 0) (comap im atTop) := by
    have := NTKB.Port.tendsto_I_div_nhdsGT_zero ((m : ℝ) ^ 2) hm2
    refine this.congr fun t ↦ ?_
    push_cast; rfl
  have hI' : Tendsto (fun t : ℝ ↦ I / ((m : ℂ) ^ 2 * t) - 1 / (a * m)) (𝓝[>] 0)
      (comap im atTop) := by
    refine tendsto_comap_iff.2 ?_
    have h1 := tendsto_comap_iff.1 hI
    refine h1.congr fun t ↦ ?_
    simp only [Function.comp_apply, sub_im]
    have : (1 / ((a : ℂ) * m)).im = 0 := by
      rw [← ofReal_natCast, ← ofReal_natCast, ← ofReal_mul, ← ofReal_one, ← ofReal_div, ofReal_im]
    rw [this, sub_zero]
  have hθ (x : ℝ) (f : ℝ → ℂ) (hf : Tendsto f (𝓝[>] 0) (comap im atTop)) :
      Tendsto (fun t ↦ jacobiTheta₂ x (f t)) (𝓝[>] 0) (𝓝 1) :=
    (NTKB.Port.tendsto_jacobiTheta₂_of_im_eq_zero (z := (x : ℂ)) (by simp)).comp hf
  have hL : Tendsto (fun t : ℝ ↦ ∑ r ∈ range m, cexp (π * I * a * r ^ 2 / m) *
      jacobiTheta₂ (r / m) (I / ((m : ℂ) ^ 2 * t))) (𝓝[>] 0)
      (𝓝 (∑ r ∈ range m, cexp (π * I * a * r ^ 2 / m) * 1)) := by
    refine tendsto_finsetSum _ fun r _ ↦ Tendsto.const_mul _ ?_
    have := hθ ((r : ℝ) / m) _ hI
    push_cast at this
    exact this
  have hR : Tendsto (fun t : ℝ ↦ sReciprocityConst a m *
      ∑ r ∈ range a, cexp (π * I * ((-m : ℤ) : ℂ) * r ^ 2 / a) *
        jacobiTheta₂ (r / a) (I / ((m : ℂ) ^ 2 * t) - 1 / (a * m))) (𝓝[>] 0)
      (𝓝 (sReciprocityConst a m *
        ∑ r ∈ range a, cexp (π * I * ((-m : ℤ) : ℂ) * r ^ 2 / a) * 1)) := by
    refine Tendsto.const_mul _ (tendsto_finsetSum _ fun r _ ↦ Tendsto.const_mul _ ?_)
    have := hθ ((r : ℝ) / a) _ hI'
    push_cast at this
    exact this
  have heq := tendsto_nhds_unique (hL.congr' (eventually_nhdsWithin_of_forall (s := Set.Ioi 0)
    fun _ ht ↦ sum_mul_jacobiTheta₂_eq ha hm h ht)) hR
  simp only [mul_one] at heq
  rw [quadSumS, heq, conj_quadSumS, sReciprocityConst]

end NTKB.Apostol
