/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Davenport.Sieve.PsiAP
import NTKB.Analytic.Davenport.Sieve.TotientSum

/-!
# Induced characters (Davenport, Chapters 28 and 29)

* if `χ` modulo `q` is induced by the primitive `χ₁`, then
  `|ψ'(x, χ) - ψ'(x, χ₁)| ≤ 2 (log q)(log x)` (`norm_psiChar'_sub_le`; Davenport: `≪ (log qx)²`);
* collecting the characters modulo `q ≤ Q` by the primitive characters inducing them
  (`sum_sum_primitiveCharacter_le`): a primitive character modulo `d` induces at most one character
  modulo each multiple `kd`.
-/

open Finset Real ComplexConjugate
open scoped ArithmeticFunction.vonMangoldt

namespace NTKB.Davenport

/-- `∑_{n ≤ N, p ∣ n} Λ(n) ≤ log N` for a prime `p`. -/
lemma sum_vonMangoldt_dvd_le {p : ℕ} (hp : p.Prime) {N : ℕ} (hN : 1 ≤ N) :
    ∑ n ∈ (Icc 1 N).filter (fun n ↦ p ∣ n), Λ n ≤ Real.log N := by
  set K := Nat.log p N
  have hpK : p ^ K ≤ N := Nat.pow_log_le_self p (by omega)
  have hpK0 : p ^ K ≠ 0 := pow_ne_zero _ hp.ne_zero
  calc ∑ n ∈ (Icc 1 N).filter (fun n ↦ p ∣ n), Λ n
      = ∑ n ∈ ((Icc 1 N).filter (fun n ↦ p ∣ n)).filter (fun n ↦ Λ n ≠ 0), Λ n := by
        rw [sum_filter_ne_zero]
    _ ≤ ∑ n ∈ (p ^ K).divisors, Λ n := by
        refine sum_le_sum_of_subset_of_nonneg (fun n hn ↦ ?_)
          (fun _ _ _ ↦ ArithmeticFunction.vonMangoldt_nonneg)
        simp only [mem_filter, mem_Icc] at hn
        obtain ⟨⟨⟨hn1, hnN⟩, hpn⟩, hΛ⟩ := hn
        obtain ⟨r, k, hr, hk, rfl⟩ := ArithmeticFunction.vonMangoldt_ne_zero_iff.1 hΛ
        have hr' := hr.nat_prime
        have hpr : p = r := (Nat.prime_dvd_prime_iff_eq hp hr').1 (hp.dvd_of_dvd_pow hpn)
        subst hpr
        rw [Nat.mem_divisors]
        refine ⟨pow_dvd_pow p (Nat.le_log_of_pow_le hp.one_lt hnN), hpK0⟩
    _ = Real.log (p ^ K : ℕ) := ArithmeticFunction.vonMangoldt_sum
    _ ≤ Real.log N := by
        apply Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hpK0)
        exact_mod_cast hpK

/-- `ω(q) log 2 ≤ log q`. -/
lemma card_primeFactors_mul_log_two_le (q : ℕ) (hq : q ≠ 0) :
    (q.primeFactors.card : ℝ) * Real.log 2 ≤ Real.log q := by
  have h1 : 2 ^ q.primeFactors.card ≤ ∏ p ∈ q.primeFactors, p :=
    Finset.pow_card_le_prod _ _ _ fun p hp ↦ (Nat.prime_of_mem_primeFactors hp).two_le
  have h2 : ∏ p ∈ q.primeFactors, p ≤ q :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero hq) (Nat.prod_primeFactors_dvd q)
  rw [← Real.log_pow]
  apply Real.log_le_log (by positivity)
  exact_mod_cast h1.trans h2

/-- `∑_{n ≤ N, (n, q) > 1} Λ(n) ≤ ω(q) log N`. -/
lemma sum_vonMangoldt_not_coprime_le {q N : ℕ} (hq : q ≠ 0) (hN : 1 ≤ N) :
    ∑ n ∈ (Icc 1 N).filter (fun n ↦ ¬ Nat.Coprime n q), Λ n ≤
      q.primeFactors.card * Real.log N := by
  calc ∑ n ∈ (Icc 1 N).filter (fun n ↦ ¬ Nat.Coprime n q), Λ n
      ≤ ∑ n ∈ (Icc 1 N).filter (fun n ↦ ¬ Nat.Coprime n q),
          ∑ p ∈ q.primeFactors, if p ∣ n then Λ n else 0 := by
        refine sum_le_sum fun n hn ↦ ?_
        have hn' := (mem_filter.1 hn).2
        rw [Nat.Prime.not_coprime_iff_dvd] at hn'
        obtain ⟨p, hp, hpn, hpq⟩ := hn'
        have hpf : p ∈ q.primeFactors := Nat.mem_primeFactors.2 ⟨hp, hpq, hq⟩
        rw [← sum_erase_add _ _ hpf, if_pos hpn]
        have : 0 ≤ ∑ x ∈ q.primeFactors.erase p, if x ∣ n then Λ n else 0 :=
          sum_nonneg fun _ _ ↦ by split_ifs <;> simp [ArithmeticFunction.vonMangoldt_nonneg]
        linarith
    _ = ∑ p ∈ q.primeFactors, ∑ n ∈ ((Icc 1 N).filter (fun n ↦ ¬ Nat.Coprime n q)).filter
          (fun n ↦ p ∣ n), Λ n := by
        rw [sum_comm]
        refine sum_congr rfl fun p _ ↦ ?_
        rw [← sum_filter]
    _ ≤ ∑ p ∈ q.primeFactors, Real.log N := by
        refine sum_le_sum fun p hp ↦ ?_
        refine le_trans ?_ (sum_vonMangoldt_dvd_le (Nat.prime_of_mem_primeFactors hp) hN)
        refine sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ ↦ ArithmeticFunction.vonMangoldt_nonneg)
        intro n hn
        simp only [mem_filter] at hn ⊢
        exact ⟨hn.1.1, hn.2⟩
    _ = _ := by rw [sum_const, nsmul_eq_mul]

variable {q : ℕ} [NeZero q]

/-- A character is principal iff its primitive character is. -/
lemma primitiveCharacter_eq_one_iff (χ : DirichletCharacter ℂ q) :
    χ.primitiveCharacter = 1 ↔ χ = 1 := by
  constructor
  · intro h
    rw [← χ.changeLevel_primitiveCharacter, h, DirichletCharacter.changeLevel_one]
  · rintro rfl; exact DirichletCharacter.primitiveCharacter_one

/-- **Davenport, Ch. 28 and 29** (induced characters): if `χ` modulo `q` is induced by the
primitive character `χ₁`, then `|ψ'(x, χ) - ψ'(x, χ₁)| ≤ 2 (log q)(log x)` for `x ≥ 1`. -/
@[kb "davenport1980" "Ch 28, p. 163"]
theorem norm_psiChar'_sub_le (χ : DirichletCharacter ℂ q) {x : ℝ} (hx : 1 ≤ x) :
    ‖psiChar' χ x - psiChar' χ.primitiveCharacter x‖ ≤ 2 * Real.log q * Real.log x := by
  classical
  have hq0 : q ≠ 0 := NeZero.ne q
  have hN : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
  -- the main terms cancel
  have hmain : (if χ = 1 then (x : ℂ) else 0) =
      if χ.primitiveCharacter = 1 then (x : ℂ) else 0 := by
    simp only [primitiveCharacter_eq_one_iff]
  simp only [psiChar', hmain, sub_sub_sub_cancel_right, psiChar, ← sum_sub_distrib, ← sub_mul]
  -- only `n` not coprime to `q` contribute
  have hterm : ∀ n ∈ Icc 1 ⌊x⌋₊, ‖(χ n - χ.primitiveCharacter n) * (Λ n : ℂ)‖ ≤
      if Nat.Coprime n q then 0 else Λ n := by
    intro n _
    split_ifs with hc
    · have : χ.primitiveCharacter ((n : ℤ) : ZMod χ.conductor) = χ ((n : ℤ) : ZMod q) :=
        χ.primitiveCharacter_apply_of_isCoprime (Nat.isCoprime_iff_coprime.2 hc)
      push_cast at this
      rw [this, sub_self, zero_mul, norm_zero]
    · have h0 : χ n = 0 := MulChar.map_nonunit _ (by rwa [ZMod.isUnit_iff_coprime])
      rw [h0, zero_sub, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      calc ‖χ.primitiveCharacter n‖ * Λ n ≤ 1 * Λ n := by
            gcongr
            exact DirichletCharacter.norm_le_one _ _
        _ = Λ n := one_mul _
  refine (norm_sum_le _ _).trans ((sum_le_sum hterm).trans ?_)
  rw [sum_ite, sum_const_zero, zero_add]
  refine (sum_vonMangoldt_not_coprime_le hq0 hN).trans ?_
  have hlogN : Real.log ⌊x⌋₊ ≤ Real.log x :=
    Real.log_le_log (by exact_mod_cast hN) (Nat.floor_le (by linarith))
  have hω := card_primeFactors_mul_log_two_le q hq0
  have hlog2 : (1 : ℝ) / 2 < Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx
  have hω' : (q.primeFactors.card : ℝ) ≤ 2 * Real.log q := by
    have hc : (0 : ℝ) ≤ q.primeFactors.card := by positivity
    nlinarith
  calc (q.primeFactors.card : ℝ) * Real.log ⌊x⌋₊ ≤ (2 * Real.log q) * Real.log x := by
        gcongr
    _ = _ := by ring

omit [NeZero q] in
lemma changeLevel_congr_heq {d d' : ℕ} (hd : d ∣ q) (hd' : d' ∣ q) (h : d = d')
    {ψ : DirichletCharacter ℂ d} {ψ' : DirichletCharacter ℂ d'} (hψ : HEq ψ ψ') :
    DirichletCharacter.changeLevel hd ψ = DirichletCharacter.changeLevel hd' ψ' := by
  subst h; rw [eq_of_heq hψ]

omit [NeZero q] in
open Classical in
/-- **Davenport, Ch. 28 and 29** (collecting characters by the primitive characters inducing them):
for nonnegative `w` and `F`,
`∑_{q ≤ Q} w(q) ∑_{χ mod q} F(χ₁) ≤ ∑_{d ≤ Q} ∑*_{ψ mod d} F(ψ) ∑_{k ≤ Q/d} w(kd)`,
where `χ₁` is the primitive character inducing `χ`. -/
@[kb "davenport1980" "Ch 28, p. 163"]
theorem sum_sum_primitiveCharacter_le (Q : ℕ) (w : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n)
    (F : (d : ℕ) → DirichletCharacter ℂ d → ℝ) (hF : ∀ d ψ, 0 ≤ F d ψ) :
    ∑ q ∈ Icc 1 Q, w q * ∑ χ : DirichletCharacter ℂ q, F χ.conductor χ.primitiveCharacter ≤
      ∑ d ∈ Icc 1 Q, ∑ ψ ∈ (univ : Finset (DirichletCharacter ℂ d)).filter (fun ψ ↦ ψ.IsPrimitive),
        F d ψ * ∑ k ∈ Icc 1 (Q / d), w (k * d) := by
  set D := (Icc 1 Q).sigma (fun q ↦ (univ : Finset (DirichletCharacter ℂ q)))
  set S2 := (Icc 1 Q).sigma
    (fun d ↦ (univ : Finset (DirichletCharacter ℂ d)).filter (fun ψ ↦ ψ.IsPrimitive))
  set S3 := S2.sigma (fun y ↦ Icc 1 (Q / y.1))
  set g : (Σ _ : (Σ d : ℕ, DirichletCharacter ℂ d), ℕ) → ℝ := fun z ↦ F z.1.1 z.1.2 * w (z.2 * z.1.1)
  set i : (Σ q : ℕ, DirichletCharacter ℂ q) → (Σ _ : (Σ d : ℕ, DirichletCharacter ℂ d), ℕ) :=
    fun x ↦ ⟨⟨x.2.conductor, x.2.primitiveCharacter⟩, x.1 / x.2.conductor⟩
  have hL : ∑ q ∈ Icc 1 Q, w q * ∑ χ : DirichletCharacter ℂ q, F χ.conductor χ.primitiveCharacter =
      ∑ x ∈ D, g (i x) := by
    rw [sum_sigma]
    refine sum_congr rfl fun q hq ↦ ?_
    rw [mul_sum]
    refine sum_congr rfl fun χ _ ↦ ?_
    simp only [g, i]
    rw [Nat.div_mul_cancel χ.conductor_dvd_level, mul_comm]
  have hR : ∑ d ∈ Icc 1 Q, ∑ ψ ∈ (univ : Finset (DirichletCharacter ℂ d)).filter
      (fun ψ ↦ ψ.IsPrimitive), F d ψ * ∑ k ∈ Icc 1 (Q / d), w (k * d) = ∑ z ∈ S3, g z := by
    rw [sum_sigma, sum_sigma]
    refine sum_congr rfl fun d _ ↦ sum_congr rfl fun ψ _ ↦ ?_
    rw [mul_sum]
  rw [hL, hR]
  have hinj : Set.InjOn i D := by
    rintro ⟨q, χ⟩ hx ⟨q', χ'⟩ hx' h
    simp only [i, Sigma.mk.inj_iff] at h
    obtain ⟨⟨hc, hψ⟩, hk⟩ := h
    have hk' := eq_of_heq hk
    simp only [D, coe_sigma, Set.mem_sigma_iff, coe_Icc, Set.mem_Icc] at hx hx'
    have hqq : q = q' := by
      rw [← Nat.div_mul_cancel χ.conductor_dvd_level, ← Nat.div_mul_cancel χ'.conductor_dvd_level,
        hk', hc]
    subst hqq
    have : χ = χ' := by
      rw [← χ.changeLevel_primitiveCharacter, ← χ'.changeLevel_primitiveCharacter]
      exact changeLevel_congr_heq _ _ hc hψ
    rw [this]
  rw [← sum_image hinj]
  refine sum_le_sum_of_subset_of_nonneg ?_ (fun z _ _ ↦ mul_nonneg (hF _ _) (hw _))
  intro z hz
  obtain ⟨⟨q, χ⟩, hx, rfl⟩ := mem_image.1 hz
  simp only [D, mem_sigma, mem_Icc, mem_univ, and_true] at hx
  have : NeZero q := ⟨by omega⟩
  have hc0 : 0 < χ.conductor := Nat.pos_of_ne_zero χ.conductor_ne_zero
  have hcq : χ.conductor ≤ q := Nat.le_of_dvd (by omega) χ.conductor_dvd_level
  simp only [S3, S2, i, mem_sigma, mem_Icc, mem_filter, mem_univ, true_and]
  refine ⟨⟨⟨by omega, by omega⟩, χ.primitiveCharacter_isPrimitive⟩, ?_, ?_⟩
  · exact Nat.div_pos hcq hc0
  · exact Nat.div_le_div_right hx.2

end NTKB.Davenport
