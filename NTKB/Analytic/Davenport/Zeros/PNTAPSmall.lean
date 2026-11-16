/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Davenport.Zeros.PNTAPPage
import NTKB.Analytic.Davenport.ClassNumber.Bounds
import NTKB.Analytic.Davenport.ClassNumber.Unconditional

/-!
# The prime number theorem for progressions with small modulus, effectively

**Davenport, Ch. 20, p. 123, (11) (row 20-7).** For fixed `δ > 0`, if `q ≤ (log x)^{1-δ}` then
`ψ(x; q, a) = x/φ(q) + O(x exp(-c √log x))`, with constants that can be computed: the possible
exceptional zero is kept away from `1` by the effective bound `β < 1 - c/(q^{1/2} log² q)` of
Chapter 14, (18) (`NTKB.Davenport.real_zero_lt_of_isQuadratic`), instead of Siegel's theorem.

The proof starts from Page's form 20-10 (`Davenport.psiAP_sub_le_page` with `C = 2`, since
`log q ≤ log log x ≤ 2 √log x`): the bound holds unless `q` is a multiple of the Page modulus `q₁`,
whose real zero satisfies `β > 1 - 1/(800 log z)`, `log z ≥ 2 √log x`. With 14-18 this gives
`800 c √log x < √q₁ log² q₁ ≤ (log x)^{(1-δ)/2} (log log x)²`, impossible once `x` is large in terms of
`δ`; small `x` are covered by the trivial bound `ψ(x; q, a) ≤ (x + 1) log x`.

That bound is proved here from the class number formula, which is conditional on the two named
inputs `QuadraticFieldDiscriminants` and `QuadraticIdealCount`;
so is this theorem. Both inputs are proved, and the theorem without them is `psiAP_sub_le_small_modulus_unconditional`.
-/

open Filter Topology Complex Set DirichletCharacter
open scoped Real

namespace NTKB

/-- `(log L)^2 ≤ c₀ L^{δ/2}` for large `L`. -/
lemma exists_log_sq_le_rpow {c₀ δ : ℝ} (hc₀ : 0 < c₀) (hδ : 0 < δ) :
    ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L : ℝ, L₀ ≤ L → Real.log L ^ 2 ≤ c₀ * L ^ (δ / 2) := by
  have h := (isLittleO_log_rpow_atTop (r := δ / 4) (by positivity)).bound
    (Real.sqrt_pos.mpr hc₀)
  obtain ⟨L₁, hL₁⟩ := Filter.eventually_atTop.mp h
  refine ⟨max L₁ 1, le_max_right _ _, fun L hL ↦ ?_⟩
  have hL1 : 1 ≤ L := (le_max_right _ _).trans hL
  have hb := hL₁ L ((le_max_left _ _).trans hL)
  have hlog : 0 ≤ Real.log L := Real.log_nonneg hL1
  have hr : 0 ≤ L ^ (δ / 4) := Real.rpow_nonneg (by linarith) _
  rw [Real.norm_of_nonneg hlog, Real.norm_of_nonneg hr] at hb
  have hsq : L ^ (δ / 2) = (L ^ (δ / 4)) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
    congr 1
    push_cast
    ring
  calc Real.log L ^ 2 ≤ (√c₀ * L ^ (δ / 4)) ^ 2 := pow_le_pow_left₀ hlog hb 2
    _ = c₀ * L ^ (δ / 2) := by rw [mul_pow, Real.sq_sqrt hc₀.le, hsq]

lemma psiAP_natCast_nonneg {q : ℕ} (a : ZMod q) (N : ℕ) : 0 ≤ psiAP a N :=
  Finset.sum_nonneg fun n _ ↦ ArithmeticFunction.vonMangoldt.residueClass_nonneg a n

/-- The trivial bound `ψ(N; q, a) ≤ (N + 1) log N`. -/
lemma psiAP_natCast_le {q : ℕ} (a : ZMod q) (N : ℕ) : psiAP a N ≤ (N + 1) * Real.log N := by
  unfold psiAP
  rw [Nat.floor_natCast]
  calc ∑ n ∈ Finset.Icc 0 N, ArithmeticFunction.vonMangoldt.residueClass a n
      ≤ ∑ n ∈ Finset.Icc 0 N, Real.log N := Finset.sum_le_sum fun n hn ↦ by
        have hn' := (Finset.mem_Icc.mp hn).2
        refine (ArithmeticFunction.vonMangoldt.residueClass_le a n).trans
          (ArithmeticFunction.vonMangoldt_le_log.trans ?_)
        rcases Nat.eq_zero_or_pos n with h | h
        · subst h
          simpa using Real.log_natCast_nonneg N
        · exact Real.log_le_log (by exact_mod_cast h) (by exact_mod_cast hn')
    _ = (N + 1) * Real.log N := by
        rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
        push_cast
        ring

/-- **Davenport, Ch. 20, p. 123, (11) (row 20-7)**, conditional on the inputs of the class number
formula: for every `δ > 0` there are `c, A > 0` such that for every integer `N ≥ 3`, every
`q ≤ (log N)^{1-δ}` and every `a` prime to `q`, `|ψ(N; q, a) - N/φ(q)| ≤ A N exp(-c √log N)`. -/
@[kb "davenport1980" "Ch 20, p. 123"]
theorem Davenport.psiAP_sub_le_small_modulus (hF : Davenport.QuadraticFieldDiscriminants)
    (hI : Davenport.QuadraticIdealCount) {δ : ℝ} (hδ : 0 < δ) :
    ∃ c A : ℝ, 0 < c ∧ 0 < A ∧ ∀ {q : ℕ} [NeZero q] {a : ZMod q}, IsUnit a →
      ∀ N : ℕ, 3 ≤ N → (q : ℝ) ≤ Real.log N ^ (1 - δ) →
      ‖(psiAP a N : ℂ) - N / q.totient‖ ≤ A * N * Real.exp (-(c * √(Real.log N))) := by
  obtain ⟨c₀, hc₀, h14⟩ := Davenport.real_zero_lt_of_isQuadratic hF hI
  obtain ⟨c, A₁, hc, hA₁, hP⟩ := Davenport.psiAP_sub_le_page 2 two_pos
  set δ' := min δ (1 / 2) with hδ'
  have hδ'0 : 0 < δ' := lt_min hδ (by norm_num)
  have hδ'1 : δ' ≤ δ := min_le_left _ _
  have hδ'2 : δ' ≤ 1 / 2 := min_le_right _ _
  obtain ⟨L₀, hL₀1, hL₀⟩ := exists_log_sq_le_rpow (c₀ := 800 * c₀) (by positivity) hδ'0
  set N₀ : ℕ := ⌈Real.exp L₀⌉₊ with hN₀
  have hN₀0 : (0 : ℝ) ≤ N₀ := Nat.cast_nonneg _
  have hl0 : 0 ≤ Real.log (N₀ + 3) := Real.log_nonneg (by linarith)
  set B := (2 * Real.log (N₀ + 3) + 1) * Real.exp (c * √(Real.log (N₀ + 3))) with hB
  have hB0 : 0 ≤ B := mul_nonneg (by linarith) (Real.exp_pos _).le
  refine ⟨c, A₁ + B, hc, add_pos_of_pos_of_nonneg hA₁ hB0, ?_⟩
  intro q _ a ha N hN hqN
  obtain ⟨q₁, hq₁, hbound⟩ := hP N hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
  set L := Real.log N with hL
  have hL1 : 1 ≤ L := by
    rw [hL, Real.le_log_iff_exp_le hN0]
    linarith [Real.exp_one_lt_d9]
  have hE0 : 0 < Real.exp (-(c * √L)) := Real.exp_pos _
  rcases lt_or_ge (N : ℝ) (N₀ + 3) with hsmall | hlarge
  · -- small `N`: the trivial bound
    have hψ0 := psiAP_natCast_nonneg a N
    have hψ := psiAP_natCast_le a N
    have hφ : (1 : ℝ) ≤ q.totient := by
      exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
    have h1 : ‖(psiAP a N : ℂ) - N / q.totient‖ ≤ (N + 1) * L + N := by
      refine (norm_sub_le _ _).trans ?_
      rw [Complex.norm_real, Real.norm_of_nonneg hψ0, norm_div, Complex.norm_natCast,
        Complex.norm_natCast]
      have : (N : ℝ) / q.totient ≤ N := div_le_self hN0.le hφ
      linarith
    have hlogN : L ≤ Real.log (N₀ + 3) := Real.log_le_log hN0 hsmall.le
    have hexp : 1 ≤ Real.exp (c * √(Real.log (N₀ + 3))) * Real.exp (-(c * √L)) := by
      rw [← Real.exp_add]
      apply Real.one_le_exp
      have := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hlogN) hc.le
      linarith
    have hL0 : 0 ≤ L := by linarith
    have h2 : (N + 1) * L + N ≤ N * (2 * Real.log (N₀ + 3) + 1) := by
      have := mul_le_mul_of_nonneg_left hlogN hN0.le
      nlinarith
    have hpos : 0 ≤ (N : ℝ) * (2 * Real.log (N₀ + 3) + 1) := by positivity
    calc ‖(psiAP a N : ℂ) - N / q.totient‖ ≤ (N + 1) * L + N := h1
      _ ≤ N * (2 * Real.log (N₀ + 3) + 1) := h2
      _ ≤ N * (2 * Real.log (N₀ + 3) + 1) *
          (Real.exp (c * √(Real.log (N₀ + 3))) * Real.exp (-(c * √L))) :=
          le_mul_of_one_le_right hpos hexp
      _ = B * N * Real.exp (-(c * √L)) := by rw [hB]; ring
      _ ≤ (A₁ + B) * N * Real.exp (-(c * √L)) := by
          have : 0 ≤ (N : ℝ) * Real.exp (-(c * √L)) := by positivity
          nlinarith
  · -- large `N`: no Page modulus divides `q`
    have hLL₀ : L₀ ≤ L := by
      rw [hL, Real.le_log_iff_exp_le hN0]
      have := Nat.le_ceil (Real.exp L₀)
      rw [← hN₀] at this
      linarith
    have hq1 : (q : ℝ) ≤ L ^ (1 - δ') :=
      hqN.trans (Real.rpow_le_rpow_of_exponent_le hL1 (by linarith))
    have hqL : (q : ℝ) ≤ L := by
      have := Real.rpow_le_rpow_of_exponent_le hL1 (by linarith : 1 - δ' ≤ 1)
      rw [Real.rpow_one] at this
      linarith
    have hq0 : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
    have hsL : 0 < √L := Real.sqrt_pos.mpr (by linarith)
    have hlogq : Real.log q ≤ 2 * √L := by
      have h1 := Real.log_le_log hq0 hqL
      have h2 := Real.log_le_rpow_div (x := L) (by linarith) (by norm_num : (0 : ℝ) < 1 / 2)
      rw [← Real.sqrt_eq_rpow] at h2
      linarith
    have hnd : ¬ q₁ ∣ q := by
      intro hdvd
      rcases hq₁ with h0 | hpage
      · subst h0
        exact NeZero.ne q (Nat.eq_zero_of_zero_dvd hdvd)
      · obtain ⟨hnz, χ', β, hprim, hne1, hsq, hq₁z, hLβ, hβ⟩ := hpage
        have := hnz
        have hq₁3 : (3 : ℝ) ≤ q₁ := by exact_mod_cast Davenport.three_le_of_ne_one hne1
        have hq₁q : (q₁ : ℝ) ≤ q := by
          exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) hdvd
        have hquad : χ'.IsQuadratic := MulChar.isQuadratic_iff_sq_eq_one.mpr hsq
        have hβ2 := h14 hquad hne1 β hLβ
        set z := max 3 (Real.exp (2 * √L)) with hzdef
        have hz : 2 * √L ≤ Real.log z := by
          have : Real.exp (2 * √L) ≤ z := le_max_right _ _
          calc 2 * √L = Real.log (Real.exp (2 * √L)) := (Real.log_exp _).symm
            _ ≤ Real.log z := Real.log_le_log (Real.exp_pos _) this
        have hlz : 0 < Real.log z := by linarith
        set D := √(q₁ : ℝ) * Real.log q₁ ^ 2 with hDdef
        have hlq₁ : 0 < Real.log q₁ := Real.log_pos (by linarith)
        have hD : 0 < D := by positivity
        have hlt : c₀ / D < 1 / 800 / Real.log z := by linarith
        have hlt2 : 800 * c₀ * Real.log z < D := by
          rw [div_lt_div_iff₀ hD hlz] at hlt
          linarith
        have hsqrt : √(q₁ : ℝ) ≤ L ^ ((1 - δ') / 2) := by
          rw [Real.sqrt_eq_rpow, show (1 - δ') / 2 = (1 - δ') * (1 / 2) by ring,
            Real.rpow_mul (by linarith)]
          exact Real.rpow_le_rpow (by positivity) (hq₁q.trans hq1) (by norm_num)
        have hlq₁L : Real.log q₁ ≤ Real.log L := Real.log_le_log (by linarith) (hq₁q.trans hqL)
        have hv : 0 < L ^ ((1 - δ') / 2) := Real.rpow_pos_of_pos (by linarith) _
        have hD2 : D ≤ L ^ ((1 - δ') / 2) * Real.log L ^ 2 :=
          mul_le_mul hsqrt (pow_le_pow_left₀ hlq₁.le hlq₁L 2) (by positivity) hv.le
        have hsplit : √L = L ^ ((1 - δ') / 2) * L ^ (δ' / 2) := by
          rw [← Real.rpow_add (by linarith), Real.sqrt_eq_rpow]
          congr 1
          ring
        have hkey := hL₀ L hLL₀
        have h3 : L ^ ((1 - δ') / 2) * Real.log L ^ 2 ≤
            L ^ ((1 - δ') / 2) * (800 * c₀ * L ^ (δ' / 2)) :=
          mul_le_mul_of_nonneg_left hkey hv.le
        have e : L ^ ((1 - δ') / 2) * (800 * c₀ * L ^ (δ' / 2)) = 800 * c₀ * √L := by
          rw [hsplit]; ring
        have h4 : 800 * c₀ * (2 * √L) ≤ 800 * c₀ * Real.log z :=
          mul_le_mul_of_nonneg_left hz (by positivity)
        have h5 := mul_pos hc₀ hsL
        linarith
    have hmain := hbound ha hlogq hnd
    have : 0 ≤ (N : ℝ) * Real.exp (-(c * √L)) := by positivity
    calc ‖(psiAP a N : ℂ) - N / q.totient‖ ≤ A₁ * N * Real.exp (-(c * √L)) := hmain
      _ ≤ (A₁ + B) * N * Real.exp (-(c * √L)) := by nlinarith

/-- **Davenport, Ch. 20, p. 123, (11) (row 20-7), unconditional**: the two inputs of the class number
formula are proved (`NTKB.Davenport.quadraticFieldDiscriminants`, `NTKB.Davenport.quadraticIdealCount`). -/
@[kb "davenport1980" "Ch 20, p. 123"]
theorem Davenport.psiAP_sub_le_small_modulus_unconditional {δ : ℝ} (hδ : 0 < δ) :
    ∃ c A : ℝ, 0 < c ∧ 0 < A ∧ ∀ {q : ℕ} [NeZero q] {a : ZMod q}, IsUnit a →
      ∀ N : ℕ, 3 ≤ N → (q : ℝ) ≤ Real.log N ^ (1 - δ) →
      ‖(psiAP a N : ℂ) - N / q.totient‖ ≤ A * N * Real.exp (-(c * √(Real.log N))) :=
  Davenport.psiAP_sub_le_small_modulus NTKB.Davenport.quadraticFieldDiscriminants
    NTKB.Davenport.quadraticIdealCount hδ

end NTKB
