/- Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license. -/
import NTKB.Analytic.Davenport.ThreePrimes.Ramanujan
import NTKB.Analytic.Davenport.ThreePrimes.Circle
import NTKB.Analytic.Davenport.Siegel.SiegelWalfisz

/-!
# `S(α)` on a major arc (Davenport, Chapter 26, pp. 146–147)

For `α = a/q + β` with `(a, q) = 1` and `q ≤ (log N)^B`:

* **26-7**: `φ(q)⁻¹ ∑_χ τ(χ̄) χ(h) = e(h/q)` for `(h, q) = 1` and `0` otherwise
  (`sum_gaussSum_inv_mul_char`), for every character mod `q`, primitive or not;
* **26-8** (formula (B)): `S(a/q + β) = φ(q)⁻¹ ∑_χ τ(χ̄) χ(a) ∑_{k ≤ N} χ(k) Λ(k) e(kβ) + O(log q log N)`
  (`norm_primeExpSum_sub_charExpansion_le`);
* **26-9**: partial summation,
  `∑_{k ≤ N} χ(k) Λ(k) e(kβ) = e(Nβ) ψ(N, χ) - 2πiβ ∫_1^N e(uβ) ψ(u, χ) du` (`twistedExpSum_eq`);
* **26-10**: for `χ ≠ χ₀`, `∑_{k ≤ N} χ(k) Λ(k) e(kβ) ≪ (1 + N|β|) N exp(-c √log N)`, from the
  Siegel–Walfisz estimate (C) of §22 (`siegel_walfisz_char`) (`norm_twistedExpSum_le`);
* **26-11**: `S(a/q + β) = (μ(q)/φ(q)) T(β) + O((1 + N|β|) N exp(-c √log N))`, the principal
  character giving the main term by the prime number theorem with error term
  (`norm_primeExpSum_major_sub_le`).
-/

open Finset Real
open scoped ArithmeticFunction.Moebius ArithmeticFunction.vonMangoldt

namespace NTKB.Davenport

/-- `∑_{k ≤ N} χ(k) Λ(k) e(kβ)`. -/
noncomputable def twistedExpSum {q : ℕ} (χ : DirichletCharacter ℂ q) (N : ℕ) (β : ℝ) : ℂ :=
  ∑ n ∈ Icc 1 N, χ n * (Λ n : ℂ) * Complex.exp (2 * π * Complex.I * (n * β))

lemma sum_Icc_zero_eq {M : Type*} [AddCommMonoid M] (g : ℕ → M) (hg : g 0 = 0) (m : ℕ) :
    ∑ k ∈ Icc 0 m, g k = ∑ k ∈ Icc 1 m, g k := by
  symm
  refine Finset.sum_subset (Icc_subset_Icc_left zero_le_one) fun k hk hk' => ?_
  have : k = 0 := by simp at hk hk'; omega
  subst this; exact hg

lemma abel_exp (a : ℕ → ℂ) (ha : a 0 = 0) {N : ℕ} (hN : 1 ≤ N) (β : ℝ) :
    ∑ n ∈ Icc 1 N, a n * Complex.exp (2 * π * Complex.I * (n * β)) =
      Complex.exp (2 * π * Complex.I * (N * β)) * ∑ k ∈ Icc 1 N, a k -
      2 * π * Complex.I * β *
        ∫ u in (1 : ℝ)..N, Complex.exp (2 * π * Complex.I * (u * β)) *
          ∑ k ∈ Icc 1 ⌊u⌋₊, a k := by
  set f : ℝ → ℂ := fun t => Complex.exp (2 * π * Complex.I * (t * β)) with hf
  have hd : ∀ t : ℝ, HasDerivAt f (2 * π * Complex.I * β * f t) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => (2 * π * Complex.I * ((t:ℂ) * β)))
        (2 * π * Complex.I * β) t := by
      have := ((Complex.ofRealCLM.hasDerivAt (x := t)).mul_const (β:ℂ)).const_mul
        (2 * π * Complex.I)
      simpa using this
    have := h1.cexp
    simpa [hf, mul_comm] using this
  have hder : deriv f = fun t => 2 * π * Complex.I * β * f t := funext fun t => (hd t).deriv
  have hcont : Continuous f := by simp only [hf]; fun_prop
  have hint : MeasureTheory.IntegrableOn (deriv f) (Set.Icc (1 : ℝ) N) := by
    rw [hder]
    exact (continuous_const.mul hcont).continuousOn.integrableOn_Icc
  have key := sum_mul_eq_sub_integral_mul₀' (f := f) (c := a) ha N
    (fun t _ => (hd t).differentiableAt) hint
  rw [sum_Icc_zero_eq (fun k => f k * a k) (by simp [ha]) N,
    sum_Icc_zero_eq a ha N] at key
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  rw [intervalIntegral.integral_of_le hN']
  have e1 : ∀ n : ℕ, a n * Complex.exp (2 * π * Complex.I * (n * β)) = f n * a n := fun n => by
    simp only [hf]; push_cast; ring_nf
  simp_rw [e1]
  rw [key]
  simp only [hder]
  have : ∫ t in Set.Ioc (1 : ℝ) N, 2 * π * Complex.I * β * f t * ∑ k ∈ Icc 0 ⌊t⌋₊, a k =
      2 * π * Complex.I * β * ∫ t in Set.Ioc (1 : ℝ) N, f t * ∑ k ∈ Icc 1 ⌊t⌋₊, a k := by
    rw [← MeasureTheory.integral_const_mul]
    congr 1
    ext t
    rw [sum_Icc_zero_eq a ha ⌊t⌋₊]
    ring
  rw [this]
  simp only [hf, Complex.ofReal_natCast]

/-- Bound for an Abel-summed exponential sum, given a uniform bound for the partial sums. -/
lemma norm_abel_le (a : ℕ → ℂ) (ha : a 0 = 0) {N : ℕ} (hN : 1 ≤ N) (β : ℝ) (M : ℝ)
    (hM : ∀ u : ℝ, 1 ≤ u → u ≤ N → ‖∑ k ∈ Icc 1 ⌊u⌋₊, a k‖ ≤ M) :
    ‖∑ n ∈ Icc 1 N, a n * Complex.exp (2 * π * Complex.I * (n * β))‖ ≤
      2 * π * (1 + N * |β|) * M := by
  rw [abel_exp a ha hN β]
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 1 le_rfl hN')
  have h1 : ‖∑ k ∈ Icc 1 N, a k‖ ≤ M := by
    have := hM N hN' le_rfl
    simpa using this
  have h2 : ‖∫ u in (1 : ℝ)..N, Complex.exp (2 * π * Complex.I * (u * β)) *
          ∑ k ∈ Icc 1 ⌊u⌋₊, a k‖ ≤ M * (N - 1) := by
    have := intervalIntegral.norm_integral_le_of_norm_le (a := 1) (b := (N : ℝ)) hN'
      (f := fun u : ℝ => Complex.exp (2 * π * Complex.I * (u * β)) * ∑ k ∈ Icc 1 ⌊u⌋₊, a k)
      (g := fun _ => M)
      (Filter.Eventually.of_forall fun u hu => by
        rw [norm_mul]
        have : ‖Complex.exp (2 * π * Complex.I * (u * β))‖ = 1 := by
          rw [Complex.norm_exp]; simp
        rw [this, one_mul]
        exact hM u hu.1.le hu.2)
      (intervalIntegrable_const :
        IntervalIntegrable (fun _ : ℝ => M) MeasureTheory.volume 1 N)
    have h' : ‖∫ u in (1 : ℝ)..N, Complex.exp (2 * π * Complex.I * (u * β)) *
          ∑ k ∈ Icc 1 ⌊u⌋₊, a k‖ ≤ (N - 1) * M := by simpa using this
    exact h'.trans_eq (mul_comm _ _)
  calc _ ≤ ‖Complex.exp (2 * π * Complex.I * (N * β)) * ∑ k ∈ Icc 1 N, a k‖ +
        ‖2 * π * Complex.I * β * ∫ u in (1 : ℝ)..N, Complex.exp (2 * π * Complex.I * (u * β)) *
          ∑ k ∈ Icc 1 ⌊u⌋₊, a k‖ := norm_sub_le _ _
    _ ≤ M + 2 * π * |β| * (M * (N - 1)) := by
        have hn : ‖(2 * π * Complex.I * β : ℂ)‖ = 2 * π * |β| := by
          rw [norm_mul, norm_mul, norm_mul]
          simp [abs_of_pos Real.pi_pos]
        have : ‖Complex.exp (2 * π * Complex.I * (N * β))‖ = 1 := by
          rw [Complex.norm_exp]; simp
        gcongr
        · rw [norm_mul, this, one_mul]; exact h1
        · rw [norm_mul, hn]
          exact mul_le_mul_of_nonneg_left h2 (by positivity)
    _ ≤ _ := by
        have := Real.pi_gt_three
        have hb := abs_nonneg β
        nlinarith [mul_nonneg hM0 hb, mul_nonneg (mul_nonneg hM0 hb) (by linarith : (0:ℝ) ≤ N)]

/-- Uniform bound from a trivial bound for small `u` and an exponentially small bound for
`u ≥ √N`. -/
lemma unif_bound {c C K : ℝ} (hc : 0 < c) (hC : 0 < C) (hK : 0 < K) (N : ℕ) (hN : 2 ≤ N)
    (f : ℝ → ℝ)
    (hf1 : ∀ u : ℝ, 1 ≤ u → u ≤ N → f u ≤ K * u)
    (hf2 : ∀ u : ℝ, 1 ≤ u → u ≤ N → (N : ℝ) ≤ u ^ 2 → 4 ≤ Real.log N →
      f u ≤ C * u * Real.exp (-c * √(Real.log u))) :
    ∀ u : ℝ, 1 ≤ u → u ≤ N →
      f u ≤ (C + K * Real.exp 2) * N * Real.exp (-(min c 1 / 2) * √(Real.log N)) := by
  intro u hu1 huN
  set L := Real.log N with hL
  set s := √L with hs
  set c' := min c 1 / 2 with hc'
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hL0 : 0 < L := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = L := Real.sq_sqrt hL0.le
  have hc'0 : 0 < c' := by rw [hc']; have := lt_min hc one_pos; positivity
  have hc'1 : c' ≤ 1 / 2 := by rw [hc']; have := min_le_right c 1; linarith
  have hc'c : 2 * c' ≤ c := by rw [hc']; have := min_le_left c 1; linarith
  set E := Real.exp (-c' * s) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have hKE : 0 ≤ K * Real.exp 2 := by positivity
  have hNE : 0 < (N : ℝ) * E := by positivity
  have hu0 : 0 < u := by linarith
  have hfinal : ∀ y : ℝ, y ≤ C * N * E ∨ y ≤ K * Real.exp 2 * N * E →
      y ≤ (C + K * Real.exp 2) * N * E := by
    intro y hy
    have h1 : 0 ≤ C * N * E := by positivity
    have h2 : 0 ≤ K * Real.exp 2 * N * E := by positivity
    rcases hy with hy | hy <;> nlinarith
  have hexpE : Real.exp (c' * s) * E = 1 := by
    rw [hE, ← Real.exp_add]; simp
  apply hfinal
  by_cases hL4 : 4 ≤ L
  · by_cases hu2 : (N : ℝ) ≤ u ^ 2
    · left
      refine (hf2 u hu1 huN hu2 hL4).trans ?_
      have hlog : L ≤ 2 * Real.log u := by
        have := Real.log_le_log hN0 hu2
        rw [Real.log_pow] at this
        push_cast at this
        linarith
      have hsq : s / 2 ≤ √(Real.log u) := by
        apply Real.le_sqrt_of_sq_le
        nlinarith
      have hexp : Real.exp (-c * √(Real.log u)) ≤ E := by
        apply Real.exp_le_exp.mpr
        have := Real.sqrt_nonneg (Real.log u)
        nlinarith
      exact mul_le_mul (mul_le_mul_of_nonneg_left huN hC.le) hexp (Real.exp_pos _).le
        (by positivity)
    · right
      replace hu2 := not_le.mp hu2
      refine (hf1 u hu1 huN).trans ?_
      have hs2' : 2 ≤ s := by nlinarith
      have h2c : 2 * c' * s ≤ L := by nlinarith
      have hexp2 : Real.exp (c' * s) ^ 2 ≤ N := by
        rw [← Real.exp_nat_mul]
        calc Real.exp (((2 : ℕ) : ℝ) * (c' * s)) ≤ Real.exp L :=
              Real.exp_le_exp.mpr (by push_cast; linarith)
          _ = N := Real.exp_log hN0
      have hsq : (u * Real.exp (c' * s)) ^ 2 ≤ (N : ℝ) ^ 2 := by
        rw [mul_pow, sq (N : ℝ)]
        exact mul_le_mul hu2.le hexp2 (by positivity) hN0.le
      have hule : u * Real.exp (c' * s) ≤ N :=
        (pow_le_pow_iff_left₀ (by positivity) hN0.le two_ne_zero).mp hsq
      have he2 : 1 ≤ Real.exp 2 := Real.one_le_exp (by norm_num)
      calc K * u = K * (u * Real.exp (c' * s)) * E := by
            rw [mul_assoc K, mul_assoc u, hexpE]; ring
        _ ≤ K * N * E := by gcongr
        _ ≤ K * Real.exp 2 * N * E := by
            have : 0 ≤ K * N * E := by positivity
            nlinarith
  · right
    replace hL4 := not_le.mp hL4
    refine (hf1 u hu1 huN).trans ?_
    have hs2' : s < 2 := by nlinarith
    have : 1 ≤ Real.exp 2 * E := by
      rw [hE, ← Real.exp_add]
      exact Real.one_le_exp (by nlinarith)
    have h0 : 0 ≤ K * N := by positivity
    calc K * u ≤ K * N := by gcongr
      _ ≤ K * N * (Real.exp 2 * E) := by nlinarith
      _ = K * Real.exp 2 * N * E := by ring

lemma card_primeFactors_le (q : ℕ) (hq : q ≠ 0) :
    (q.primeFactors.card : ℝ) ≤ 2 * Real.log q := by
  have h1 : 2 ^ q.primeFactors.card ≤ q := by
    calc 2 ^ q.primeFactors.card = ∏ p ∈ q.primeFactors, 2 := by simp
      _ ≤ ∏ p ∈ q.primeFactors, p :=
          Finset.prod_le_prod
            (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)
      _ ≤ q := Nat.le_of_dvd (Nat.pos_of_ne_zero hq) (Nat.prod_primeFactors_dvd q)
  have h2 : (q.primeFactors.card : ℝ) * Real.log 2 ≤ Real.log q := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by positivity) (by exact_mod_cast h1)
  have h3 := Real.log_two_gt_d9
  have h4 : (q.primeFactors.card : ℝ) * (1 / 2) ≤ q.primeFactors.card * Real.log 2 :=
    mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)
  linarith

lemma sum_vonMangoldt_filter_dvd_le {p : ℕ} (hp : p.Prime) (N : ℕ) :
    ∑ n ∈ (Icc 1 N).filter (p ∣ ·), Λ n ≤ Real.log N := by
  set K := Nat.log p N with hK
  have hsub : ((Icc 1 N).filter (p ∣ ·)).filter (fun n => Λ n ≠ 0) ⊆
      (Icc 1 K).image (p ^ ·) := by
    intro n hn
    simp only [mem_filter, mem_Icc] at hn
    obtain ⟨⟨⟨h1, h2⟩, hpn⟩, hne⟩ := hn
    rw [ArithmeticFunction.vonMangoldt_ne_zero_iff] at hne
    obtain ⟨p', k, hp', hk, rfl⟩ := (isPrimePow_nat_iff n).mp hne
    have : p = p' := (Nat.prime_dvd_prime_iff_eq hp hp').mp (hp.dvd_of_dvd_pow hpn)
    subst this
    simp only [mem_image, mem_Icc]
    exact ⟨k, ⟨hk, Nat.le_log_of_pow_le hp.one_lt h2⟩, rfl⟩
  have hinj : Set.InjOn (p ^ ·) (Icc 1 K : Set ℕ) := fun a _ b _ h =>
    Nat.pow_right_injective hp.two_le h
  calc ∑ n ∈ (Icc 1 N).filter (p ∣ ·), Λ n
      = ∑ n ∈ ((Icc 1 N).filter (p ∣ ·)).filter (fun n => Λ n ≠ 0), Λ n := by
        rw [Finset.sum_filter_ne_zero]
    _ ≤ ∑ n ∈ (Icc 1 K).image (p ^ ·), Λ n :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => ArithmeticFunction.vonMangoldt_nonneg)
    _ = ∑ k ∈ Icc 1 K, Λ (p ^ k) := Finset.sum_image hinj
    _ = K * Real.log p := by
        rw [Finset.sum_congr rfl (g := fun _ => Real.log p)]
        · simp
        · intro k hk
          rw [ArithmeticFunction.vonMangoldt_apply_pow (by simp at hk; omega),
            ArithmeticFunction.vonMangoldt_apply_prime hp]
    _ ≤ Real.log N := by
        rcases Nat.eq_zero_or_pos N with h0 | h0
        · simp [hK, h0]
        · rw [← Real.log_pow]
          exact Real.log_le_log (by have := hp.pos; positivity)
            (by exact_mod_cast Nat.pow_log_le_self p h0.ne')

lemma sum_vonMangoldt_noncoprime_le (q N : ℕ) [NeZero q] :
    ∑ n ∈ (Icc 1 N).filter (fun n => ¬ Nat.Coprime n q), Λ n ≤
      2 * Real.log q * Real.log N := by
  have hq : q ≠ 0 := NeZero.ne q
  classical
  have h1 : ∀ n ∈ (Icc 1 N).filter (fun n => ¬ Nat.Coprime n q),
      Λ n ≤ ∑ p ∈ q.primeFactors, if p ∣ n then Λ n else 0 := by
    intro n hn
    simp only [mem_filter] at hn
    obtain ⟨p, hp, hpn, hpq⟩ := Nat.Prime.not_coprime_iff_dvd.mp hn.2
    have hpm : p ∈ q.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpq, hq⟩
    have := Finset.single_le_sum (f := fun p => if p ∣ n then Λ n else 0)
      (fun p _ => by split_ifs <;> simp [ArithmeticFunction.vonMangoldt_nonneg]) hpm
    simpa [hpn] using this
  calc ∑ n ∈ (Icc 1 N).filter (fun n => ¬ Nat.Coprime n q), Λ n
      ≤ ∑ n ∈ (Icc 1 N).filter (fun n => ¬ Nat.Coprime n q),
          ∑ p ∈ q.primeFactors, if p ∣ n then Λ n else 0 := Finset.sum_le_sum h1
    _ ≤ ∑ n ∈ Icc 1 N, ∑ p ∈ q.primeFactors, if p ∣ n then Λ n else 0 :=
        Finset.sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun n _ _ =>
          Finset.sum_nonneg fun p _ => by
            split_ifs <;> simp [ArithmeticFunction.vonMangoldt_nonneg]
    _ = ∑ p ∈ q.primeFactors, ∑ n ∈ (Icc 1 N).filter (p ∣ ·), Λ n := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [Finset.sum_filter]
    _ ≤ ∑ p ∈ q.primeFactors, Real.log N :=
        Finset.sum_le_sum fun p hp => sum_vonMangoldt_filter_dvd_le (Nat.prime_of_mem_primeFactors hp) N
    _ = q.primeFactors.card * Real.log N := by simp
    _ ≤ 2 * Real.log q * Real.log N :=
        mul_le_mul_of_nonneg_right (card_primeFactors_le q hq) (Real.log_natCast_nonneg N)

/-- **Davenport, Ch. 26, p. 146, (A) (row 26-7)**: `φ(q)⁻¹ ∑_χ τ(χ̄) χ(h) = e(h/q)` if `(h, q) = 1`,
and `0` otherwise. -/
@[kb "davenport1980" "Ch 26, p. 146"]
theorem sum_gaussSum_inv_mul_char {q : ℕ} [NeZero q] (h : ZMod q) :
    (q.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q, gaussSum χ⁻¹ ZMod.stdAddChar * χ h =
      if IsUnit h then ZMod.stdAddChar h else 0 := by
  have hφ : (q.totient : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))).ne'
  have e1 : ∑ χ : DirichletCharacter ℂ q, gaussSum χ⁻¹ ZMod.stdAddChar * χ h =
      ∑ m : ZMod q, ZMod.stdAddChar m *
        ∑ χ : DirichletCharacter ℂ q, χ⁻¹ m * χ h := by
    simp only [gaussSum, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun χ _ => ?_
    ring
  rw [e1]
  simp_rw [sum_char_inv_mul_char]
  by_cases hh : IsUnit h
  · simp only [hh, ite_true]
    rw [Finset.sum_eq_single h]
    · simp [hh]
      field_simp
    · intro m _ hm
      simp [hm]
    · simp
  · simp only [hh, ite_false]
    rw [Finset.sum_eq_zero, mul_zero]
    intro m _
    have : ¬(IsUnit m ∧ m = h) := fun ⟨hm, e⟩ => hh (e ▸ hm)
    simp [this]

/-- **Davenport, Ch. 26, p. 147, (B) (row 26-8)**: on `α = a/q + β`, `(a, q) = 1`,
`S(α) = φ(q)⁻¹ ∑_χ τ(χ̄) χ(a) ∑_{k ≤ N} χ(k) Λ(k) e(kβ) + O(log q log N)`. -/
@[kb "davenport1980" "Ch 26, p. 147, (B)"]
theorem norm_primeExpSum_sub_charExpansion_le {q : ℕ} [NeZero q] {a : ℤ} (ha : IsCoprime a q)
    (N : ℕ) (β : ℝ) :
    ‖primeExpSum N (a / q + β) - (q.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q,
        gaussSum χ⁻¹ ZMod.stdAddChar * χ a * twistedExpSum χ N β‖ ≤
      2 * Real.log q * Real.log N := by
  classical
  have hau : IsUnit (a : ZMod q) := (ZMod.isUnit_intCast_iff_isCoprime a q).mpr ha.symm
  set X : ℕ → ℂ := fun n => (Λ n : ℂ) * Complex.exp (2 * π * Complex.I * (n * (a / q + β)))
    with hX
  have hterm : ∀ n : ℕ, X n - (q.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q,
      gaussSum χ⁻¹ ZMod.stdAddChar * χ a *
        (χ n * (Λ n : ℂ) * Complex.exp (2 * π * Complex.I * (n * β))) =
      if ¬ Nat.Coprime n q then X n else 0 := by
    intro n
    have h := sum_gaussSum_inv_mul_char ((a : ZMod q) * (n : ZMod q))
    have h2 : (q.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q,
        gaussSum χ⁻¹ ZMod.stdAddChar * χ a *
          (χ n * (Λ n : ℂ) * Complex.exp (2 * π * Complex.I * (n * β))) =
        ((q.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q,
          gaussSum χ⁻¹ ZMod.stdAddChar * χ ((a : ZMod q) * (n : ZMod q))) *
          ((Λ n : ℂ) * Complex.exp (2 * π * Complex.I * (n * β))) := by
      simp only [map_mul, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun χ _ => by ring
    rw [h2, h]
    by_cases hn : Nat.Coprime n q
    · have hu : IsUnit ((a : ZMod q) * (n : ZMod q)) :=
        hau.mul ((ZMod.isUnit_iff_coprime n q).mpr hn)
      have hr : (if ¬ Nat.Coprime n q then X n else 0) = 0 := by simp [hn]
      rw [hr]
      simp only [hu, ite_true]
      have := ZMod.stdAddChar_coe (N := q) (a * (n : ℤ))
      push_cast at this
      rw [this, hX, sub_eq_zero]
      simp only
      rw [mul_left_comm (Complex.exp _) (Λ n : ℂ), ← Complex.exp_add]
      congr 2
      ring
    · have hu : ¬ IsUnit ((a : ZMod q) * (n : ZMod q)) := fun hu =>
        hn ((ZMod.isUnit_iff_coprime n q).mp ((IsUnit.mul_iff.mp hu).2))
      simp [hu, hn]
  have hsum : primeExpSum N (a / q + β) - (q.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q,
        gaussSum χ⁻¹ ZMod.stdAddChar * χ a * twistedExpSum χ N β =
      ∑ n ∈ (Icc 1 N).filter (fun n => ¬ Nat.Coprime n q), X n := by
    have e1 : primeExpSum N (a / q + β) = ∑ n ∈ Icc 1 N, X n := by
      simp only [primeExpSum, hX]; push_cast; rfl
    have e2 : (q.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q,
        gaussSum χ⁻¹ ZMod.stdAddChar * χ a * twistedExpSum χ N β =
        ∑ n ∈ Icc 1 N, (q.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q,
          gaussSum χ⁻¹ ZMod.stdAddChar * χ a *
            (χ n * (Λ n : ℂ) * Complex.exp (2 * π * Complex.I * (n * β))) := by
      simp_rw [twistedExpSum, Finset.mul_sum]
      exact Finset.sum_comm
    have e3 : ∑ n ∈ (Icc 1 N).filter (fun n => ¬ Nat.Coprime n q), X n =
        ∑ n ∈ Icc 1 N, (X n - (q.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q,
          gaussSum χ⁻¹ ZMod.stdAddChar * χ a *
            (χ n * (Λ n : ℂ) * Complex.exp (2 * π * Complex.I * (n * β)))) := by
      rw [Finset.sum_filter]
      exact Finset.sum_congr rfl fun n _ => (hterm n).symm
    rw [e1, e2, e3, Finset.sum_sub_distrib]
  rw [hsum]
  calc _ ≤ ∑ n ∈ (Icc 1 N).filter (fun n => ¬ Nat.Coprime n q), ‖X n‖ := norm_sum_le _ _
    _ = ∑ n ∈ (Icc 1 N).filter (fun n => ¬ Nat.Coprime n q), Λ n := by
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [hX]; simp only
        rw [norm_mul, Complex.norm_exp]
        simp [abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    _ ≤ _ := sum_vonMangoldt_noncoprime_le q N

/-- **Davenport, Ch. 26, p. 147 (row 26-9)**: partial summation,
`∑_{k ≤ N} χ(k) Λ(k) e(kβ) = e(Nβ) ψ(N, χ) - 2πiβ ∫_1^N e(uβ) ψ(u, χ) du`. -/
@[kb "davenport1980" "Ch 26, p. 147"]
theorem twistedExpSum_eq {q : ℕ} (χ : DirichletCharacter ℂ q) {N : ℕ} (hN : 1 ≤ N) (β : ℝ) :
    twistedExpSum χ N β = Complex.exp (2 * π * Complex.I * (N * β)) * psiChar χ N -
      2 * π * Complex.I * β *
        ∫ u in (1 : ℝ)..N, Complex.exp (2 * π * Complex.I * (u * β)) * psiChar χ u := by
  have := abel_exp (fun n => χ n * (Λ n : ℂ)) (by simp) hN β
  simp only [twistedExpSum, psiChar, Nat.floor_natCast]
  exact this

lemma psi_eq_sum_Icc_one (u : ℝ) : Chebyshev.psi u = ∑ n ∈ Icc 1 ⌊u⌋₊, Λ n := by
  unfold Chebyshev.psi
  have : Ioc 0 ⌊u⌋₊ = Icc 1 ⌊u⌋₊ := by ext; simp; omega
  rw [this]

lemma pow_le_exp_mul {c : ℝ} (hc : 0 < c) (n : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ x : ℝ, 0 ≤ x → x ^ n ≤ K * Real.exp (c * x / 2) := by
  refine ⟨n.factorial / (c / 2) ^ n, by positivity, fun x hx => ?_⟩
  have h := Real.pow_div_factorial_le_exp (c * x / 2) (by positivity) n
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  rw [div_le_iff₀ hf] at h
  calc x ^ n * (c / 2) ^ n = (c * x / 2) ^ n := by rw [← mul_pow]; ring_nf
    _ ≤ _ := h.trans (le_of_eq (mul_comm _ _))

lemma absorb_rpow {c B : ℝ} (hc : 0 < c) (hB : 0 < B) :
    ∃ K : ℝ, 0 < K ∧ ∀ L : ℝ, 0 ≤ L →
      L ^ B * Real.exp (-c * √L) ≤ K * Real.exp (-(c / 2) * √L) := by
  obtain ⟨K0, hK0, h0⟩ := pow_le_exp_mul hc (2 * ⌈B⌉₊)
  refine ⟨1 + K0, by positivity, fun L hL => ?_⟩
  set s := √L with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = L := Real.sq_sqrt hL
  have h1 : L ^ B ≤ 1 + K0 * Real.exp (c * s / 2) := by
    have h2 : L ^ ⌈B⌉₊ = s ^ (2 * ⌈B⌉₊) := by rw [pow_mul, hs2]
    have h3 := h0 s hs0
    rcases le_or_gt 1 L with h | h
    · have : L ^ B ≤ L ^ (⌈B⌉₊ : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le h (Nat.le_ceil B)
      rw [Real.rpow_natCast, h2] at this
      linarith
    · have := Real.rpow_le_one hL h.le hB.le
      have : 0 ≤ K0 * Real.exp (c * s / 2) := by positivity
      linarith
  have e1 : Real.exp (-c * s) ≤ Real.exp (-(c / 2) * s) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have e2 : Real.exp (c * s / 2) * Real.exp (-c * s) = Real.exp (-(c / 2) * s) := by
    rw [← Real.exp_add]; ring_nf
  calc L ^ B * Real.exp (-c * s) ≤ (1 + K0 * Real.exp (c * s / 2)) * Real.exp (-c * s) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = Real.exp (-c * s) + K0 * (Real.exp (c * s / 2) * Real.exp (-c * s)) := by ring
    _ ≤ (1 + K0) * Real.exp (-(c / 2) * s) := by rw [e2]; nlinarith [Real.exp_pos (-(c / 2) * s)]

lemma pow_log_le {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (k : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ N : ℕ, 1 ≤ N →
      Real.log N ^ k ≤ K * N * Real.exp (-c * √(Real.log N)) := by
  refine ⟨2 ^ k * k.factorial * Real.exp (1 / 2), by positivity, fun N hN => ?_⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hL0 : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  set L := Real.log N with hL
  set s := √L with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = L := Real.sq_sqrt hL0
  have h := Real.pow_div_factorial_le_exp (L / 2) (by positivity) k
  have hf : (0 : ℝ) < k.factorial := by exact_mod_cast k.factorial_pos
  rw [div_le_iff₀ hf] at h
  have h1 : L ^ k ≤ 2 ^ k * k.factorial * Real.exp (L / 2) := by
    have : L ^ k = 2 ^ k * (L / 2) ^ k := by rw [← mul_pow]; ring_nf
    rw [this]
    have h2 : (0 : ℝ) < 2 ^ k := by positivity
    nlinarith
  have h3 : Real.exp (L / 2) ≤ Real.exp (1 / 2) * (N * Real.exp (-c * s)) := by
    rw [← Real.exp_log hN0, ← hL, ← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [sq_nonneg (s - 1)]
  calc L ^ k ≤ _ := h1
    _ ≤ 2 ^ k * k.factorial * (Real.exp (1 / 2) * (N * Real.exp (-c * s))) := by gcongr
    _ = _ := by ring

lemma norm_psiChar_le_psi {q : ℕ} (χ : DirichletCharacter ℂ q) (u : ℝ) :
    ‖psiChar χ u‖ ≤ Chebyshev.psi u := by
  unfold psiChar
  refine (norm_sum_le _ _).trans ?_
  rw [psi_eq_sum_Icc_one]
  refine Finset.sum_le_sum fun n _ => ?_
  rw [norm_mul]
  have h1 := DirichletCharacter.norm_le_one χ n
  have h2 : ‖(Λ n : ℂ)‖ = Λ n := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  rw [h2]
  nlinarith [ArithmeticFunction.vonMangoldt_nonneg (n := n)]

/-- **Davenport, Ch. 26, p. 147 (row 26-10)**: for every `B > 0` there are `c, C > 0` with
`|∑_{k ≤ N} χ(k) Λ(k) e(kβ)| ≤ C (1 + N|β|) N exp(-c √log N)` for `N ≥ 2`, `q ≤ (log N)^B` and
`χ ≠ χ₀` mod `q`. -/
@[kb "davenport1980" "Ch 26, p. 147"]
theorem norm_twistedExpSum_le (B : ℝ) (hB : 0 < B) :
    ∃ c > 0, ∃ C > 0, ∀ N : ℕ, 2 ≤ N → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.log N ^ B →
      ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → ∀ β : ℝ,
        ‖twistedExpSum χ N β‖ ≤ C * (1 + N * |β|) * N * Real.exp (-c * √(Real.log N)) := by
  obtain ⟨c, hc, C, hC, hSW⟩ := siegel_walfisz_char (2 * B) (by positivity)
  have hK : 0 < Real.log 4 + 4 := by have := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 4); linarith
  have hc' : 0 < min c 1 / 2 := by have := lt_min hc one_pos; positivity
  refine ⟨min c 1 / 2, hc', 2 * π * (C + (Real.log 4 + 4) * Real.exp 2), by positivity, ?_⟩
  intro N hN q hq hqL χ hχ β
  have hq' : NeZero q := ⟨hq.ne'⟩
  have hN1 : 1 ≤ N := by omega
  have hf1 : ∀ u : ℝ, 1 ≤ u → u ≤ N → ‖psiChar χ u‖ ≤ (Real.log 4 + 4) * u := fun u hu _ =>
    (norm_psiChar_le_psi χ u).trans (Chebyshev.psi_le_const_mul_self (by linarith))
  have hf2 : ∀ u : ℝ, 1 ≤ u → u ≤ N → (N : ℝ) ≤ u ^ 2 → 4 ≤ Real.log N →
      ‖psiChar χ u‖ ≤ C * u * Real.exp (-c * √(Real.log u)) := by
    intro u hu1 huN hNu hL4
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    have hN5 : (5 : ℝ) ≤ N := by
      have h1 := Real.add_one_le_exp 4
      calc (5 : ℝ) = 4 + 1 := by norm_num
        _ ≤ Real.exp 4 := h1
        _ ≤ Real.exp (Real.log N) := Real.exp_le_exp.mpr hL4
        _ = N := Real.exp_log hN0
    have hu2 : 2 ≤ u := by nlinarith
    have hlog : Real.log N / 2 ≤ Real.log u := by
      have := Real.log_le_log hN0 hNu
      rw [Real.log_pow] at this
      push_cast at this
      linarith
    have hq2 : (q : ℝ) ≤ Real.log u ^ (2 * B) := by
      refine hqL.trans ?_
      have h0 : 0 ≤ Real.log N / 2 := by linarith
      calc Real.log N ^ B ≤ ((Real.log N / 2) ^ (2 : ℝ)) ^ B := by
            apply Real.rpow_le_rpow (by linarith) _ hB.le
            rw [Real.rpow_two]; nlinarith
        _ = (Real.log N / 2) ^ (2 * B) := by
            rw [← Real.rpow_mul h0]
        _ ≤ Real.log u ^ (2 * B) :=
            Real.rpow_le_rpow h0 hlog (by positivity)
    exact hSW u hu2 q hq hq2 χ hχ
  have hM := unif_bound hc hC hK N hN (fun u => ‖psiChar χ u‖) hf1 hf2
  have h := norm_abel_le (fun n => χ n * (Λ n : ℂ)) (by simp) hN1 β _
    (fun u hu1 huN => by simpa [psiChar] using hM u hu1 huN)
  have hpi := Real.pi_pos
  unfold twistedExpSum
  simp only [neg_mul] at h ⊢
  exact h.trans_eq (by ring)

lemma principal_bound :
    ∃ c > 0, ∃ C > 0, ∀ N : ℕ, 2 ≤ N → ∀ β : ℝ,
      ‖primeExpSum N β - linearExpSum N β‖ ≤
        C * (1 + N * |β|) * N * Real.exp (-c * √(Real.log N)) := by
  obtain ⟨c2, C2, hc2, hC2, hpnt⟩ := Davenport.psi_sub_self_le
  set c' := min c2 1 with hc'
  have hc'0 : 0 < c' := lt_min hc2 one_pos
  have hc'1 : c' ≤ 1 := min_le_right _ _
  have hc'2 : c' ≤ c2 := min_le_left _ _
  have hK : 0 < Real.log 4 + 4 := by
    have := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 4); linarith
  have hmin : min c' 1 = c' := min_eq_left hc'1
  refine ⟨min c' 1 / 2, by positivity, 2 * π * ((C2 + 1) + (Real.log 4 + 4 + 1) * Real.exp 2),
    by positivity, ?_⟩
  intro N hN β
  have hN1 : 1 ≤ N := by omega
  set a : ℕ → ℂ := fun n => if n = 0 then 0 else (Λ n : ℂ) - 1 with ha
  have hA : ∀ u : ℝ, ∑ k ∈ Icc 1 ⌊u⌋₊, a k = ((Chebyshev.psi u - ⌊u⌋₊ : ℝ) : ℂ) := by
    intro u
    rw [psi_eq_sum_Icc_one]
    have : ∀ k ∈ Icc 1 ⌊u⌋₊, a k = (Λ k : ℂ) - 1 := fun k hk => by
      have : k ≠ 0 := by simp at hk; omega
      simp [ha, this]
    rw [Finset.sum_congr rfl this, Finset.sum_sub_distrib]
    push_cast; simp
  have hf1 : ∀ u : ℝ, 1 ≤ u → u ≤ N →
      ‖∑ k ∈ Icc 1 ⌊u⌋₊, a k‖ ≤ (Real.log 4 + 4 + 1) * u := by
    intro u hu _
    rw [hA, Complex.norm_real, Real.norm_eq_abs]
    have h1 := Chebyshev.psi_le_const_mul_self (x := u) (by linarith)
    have h2 := Chebyshev.psi_nonneg u
    have h3 : (⌊u⌋₊ : ℝ) ≤ u := Nat.floor_le (by linarith)
    have h4 : (0 : ℝ) ≤ ⌊u⌋₊ := Nat.cast_nonneg _
    rw [abs_le]; constructor <;> nlinarith
  have hf2 : ∀ u : ℝ, 1 ≤ u → u ≤ N → (N : ℝ) ≤ u ^ 2 → 4 ≤ Real.log N →
      ‖∑ k ∈ Icc 1 ⌊u⌋₊, a k‖ ≤ (C2 + 1) * u * Real.exp (-c' * √(Real.log u)) := by
    intro u hu1 huN hNu hL4
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    have hN5 : (5 : ℝ) ≤ N := by
      have h1 := Real.add_one_le_exp 4
      calc (5 : ℝ) = 4 + 1 := by norm_num
        _ ≤ Real.exp 4 := h1
        _ ≤ Real.exp (Real.log N) := Real.exp_le_exp.mpr hL4
        _ = N := Real.exp_log hN0
    have hu2 : 2 ≤ u := by nlinarith
    have hu0 : 0 < u := by linarith
    have hlog : Real.log N / 2 ≤ Real.log u := by
      have := Real.log_le_log hN0 hNu
      rw [Real.log_pow] at this
      push_cast at this
      linarith
    have hl2 : 2 ≤ Real.log u := by linarith
    set l := Real.log u with hl
    have hs0 : 0 ≤ √l := Real.sqrt_nonneg _
    have hs2 : √l ^ 2 = l := Real.sq_sqrt (by linarith)
    have hs1 : 1 ≤ √l := by nlinarith
    have h1 := hpnt u hu2
    have h3 : |u - ⌊u⌋₊| ≤ 1 := by
      have := Nat.floor_le (show 0 ≤ u by linarith)
      have := Nat.lt_floor_add_one u
      rw [abs_le]; constructor <;> linarith
    rw [hA, Complex.norm_real, Real.norm_eq_abs]
    have h4 : |Chebyshev.psi u - ⌊u⌋₊| ≤ |Chebyshev.psi u - u| + 1 :=
      (abs_sub_le (Chebyshev.psi u) u ⌊u⌋₊).trans (by linarith)
    have hexp : Real.exp (-(c2 * √l)) ≤ Real.exp (-c' * √l) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have h1le : 1 ≤ u * Real.exp (-c' * √l) := by
      have e : Real.exp l = u := Real.exp_log hu0
      calc (1 : ℝ) ≤ Real.exp (l + -c' * √l) := Real.one_le_exp (by nlinarith)
        _ = u * Real.exp (-c' * √l) := by rw [Real.exp_add, e]
    have h5 : C2 * u * Real.exp (-(c2 * √l)) ≤ C2 * u * Real.exp (-c' * √l) :=
      mul_le_mul_of_nonneg_left hexp (by positivity)
    nlinarith
  have hM := unif_bound hc'0 (by positivity : 0 < C2 + 1) (by positivity : 0 < Real.log 4 + 4 + 1)
    N hN (fun u => ‖∑ k ∈ Icc 1 ⌊u⌋₊, a k‖) hf1 hf2
  have h := norm_abel_le a (by simp [ha]) hN1 β _ (fun u hu huN => hM u hu huN)
  have hsum : primeExpSum N β - linearExpSum N β =
      ∑ n ∈ Icc 1 N, a n * Complex.exp (2 * π * Complex.I * (n * β)) := by
    unfold primeExpSum linearExpSum
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n hn => ?_
    have : n ≠ 0 := by simp at hn; omega
    simp [ha, this, sub_mul]
  rw [hsum, hmin]
  simp only [neg_mul] at h ⊢
  rw [hmin] at h
  exact h.trans_eq (by ring)

lemma norm_noncoprime_sum_le (q N : ℕ) [NeZero q] (Y : ℕ → ℂ) (hY : ∀ n, ‖Y n‖ ≤ Λ n) :
    ‖∑ n ∈ (Icc 1 N).filter (fun n => ¬ Nat.Coprime n q), Y n‖ ≤
      2 * Real.log q * Real.log N :=
  (norm_sum_le _ _).trans
    ((Finset.sum_le_sum fun n _ => hY n).trans (sum_vonMangoldt_noncoprime_le q N))

lemma norm_primeExpSum_sub_principal_le (q N : ℕ) [NeZero q] (β : ℝ) :
    ‖primeExpSum N β - twistedExpSum (1 : DirichletCharacter ℂ q) N β‖ ≤
      2 * Real.log q * Real.log N := by
  classical
  have : primeExpSum N β - twistedExpSum (1 : DirichletCharacter ℂ q) N β =
      ∑ n ∈ (Icc 1 N).filter (fun n => ¬ Nat.Coprime n q),
        (Λ n : ℂ) * Complex.exp (2 * π * Complex.I * (n * β)) := by
    rw [Finset.sum_filter]
    unfold primeExpSum twistedExpSum
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    by_cases hn : Nat.Coprime n q
    · have hu : IsUnit (n : ZMod q) := (ZMod.isUnit_iff_coprime n q).mpr hn
      simp [MulChar.one_apply hu, hn]
    · have hu : ¬ IsUnit (n : ZMod q) := fun h => hn ((ZMod.isUnit_iff_coprime n q).mp h)
      simp [MulChar.map_nonunit _ hu, hn]
  rw [this]
  refine norm_noncoprime_sum_le q N _ fun n => ?_
  rw [norm_mul, Complex.norm_exp]
  simp [abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]

lemma norm_gaussSum_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    ‖gaussSum χ ZMod.stdAddChar‖ ≤ q := by
  unfold gaussSum
  refine (norm_sum_le _ _).trans ?_
  have : ∀ m : ZMod q, ‖χ m * ZMod.stdAddChar m‖ ≤ 1 := fun m => by
    rw [norm_mul]
    have h1 := DirichletCharacter.norm_le_one χ m
    have h2 : ‖(ZMod.stdAddChar m : ℂ)‖ = 1 := by
      rw [ZMod.stdAddChar_apply]; exact Circle.norm_coe _
    rw [h2, mul_one]; exact h1
  calc ∑ m : ZMod q, ‖χ m * ZMod.stdAddChar m‖ ≤ ∑ m : ZMod q, (1 : ℝ) :=
        Finset.sum_le_sum fun m _ => this m
    _ = q := by simp

lemma card_dirichletCharacter_nat (q : ℕ) [NeZero q] :
    Fintype.card (DirichletCharacter ℂ q) = q.totient := by
  rw [← Nat.card_eq_fintype_card]
  exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q

/-- **Davenport, Ch. 26, p. 147 (row 26-11)**: for every `B > 0` there are `c, C > 0` with
`|S(a/q + β) - (μ(q)/φ(q)) T(β)| ≤ C (1 + N|β|) N exp(-c √log N)` for `N ≥ 2`, `q ≤ (log N)^B`,
`(a, q) = 1`. -/
@[kb "davenport1980" "Ch 26, p. 147"]
theorem norm_primeExpSum_major_sub_le (B : ℝ) (hB : 0 < B) :
    ∃ c > 0, ∃ C > 0, ∀ N : ℕ, 2 ≤ N → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.log N ^ B →
      ∀ a : ℤ, IsCoprime a q → ∀ β : ℝ,
        ‖primeExpSum N (a / q + β) - (μ q : ℂ) / q.totient * linearExpSum N β‖ ≤
          C * (1 + N * |β|) * N * Real.exp (-c * √(Real.log N)) := by
  classical
  obtain ⟨c1, hc1, C1, hC1, h10⟩ := norm_twistedExpSum_le B hB
  obtain ⟨c3, hc3, C3, hC3, hP⟩ := principal_bound
  obtain ⟨Ka, hKa, habs⟩ := absorb_rpow hc1 hB
  have hcf0 : 0 < min (min (c1 / 2) c3) 1 := lt_min (lt_min (by positivity) hc3) one_pos
  have hcf1 : min (min (c1 / 2) c3) 1 ≤ 1 := min_le_right _ _
  have hcf2 : min (min (c1 / 2) c3) 1 ≤ c1 / 2 := (min_le_left _ _).trans (min_le_left _ _)
  have hcf3 : min (min (c1 / 2) c3) 1 ≤ c3 := (min_le_left _ _).trans (min_le_right _ _)
  obtain ⟨cf, hcf⟩ : ∃ cf, cf = min (min (c1 / 2) c3) 1 := ⟨_, rfl⟩
  rw [← hcf] at hcf0 hcf1 hcf2 hcf3
  obtain ⟨Kp, hKp, hpoly⟩ := pow_log_le hcf0 hcf1 2
  refine ⟨cf, hcf0, 4 * B * Kp + C3 + C1 * Ka, by positivity, ?_⟩
  intro N hN q hq hqL a ha β
  have : NeZero q := ⟨hq.ne'⟩
  have hN1 : 1 ≤ N := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  obtain ⟨L, hL⟩ : ∃ L, L = Real.log N := ⟨_, rfl⟩
  have hL0 : 0 < L := by rw [hL]; exact Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  obtain ⟨s, hs⟩ : ∃ s, s = √L := ⟨_, rfl⟩
  have hs0 : 0 ≤ s := by rw [hs]; exact Real.sqrt_nonneg _
  have hqL0 := hqL
  rw [← hL] at hqL ⊢
  rw [← hs] at ⊢
  have hY0 : 0 < (N : ℝ) * Real.exp (-cf * s) := by positivity
  obtain ⟨Y, hY⟩ : ∃ Y, Y = (N : ℝ) * Real.exp (-cf * s) := ⟨_, rfl⟩
  rw [← hY] at hY0
  obtain ⟨X, hX⟩ : ∃ X, X = (1 + N * |β|) * Y := ⟨_, rfl⟩
  have hfac : 1 ≤ 1 + (N : ℝ) * |β| := le_add_of_nonneg_right (by positivity)
  have hYX : Y ≤ X := by rw [hX]; exact le_mul_of_one_le_left hY0.le hfac
  have hX0 : 0 ≤ X := hY0.le.trans hYX
  -- the logarithmic error
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hlogq : Real.log q ≤ B * L := by
    have h1 : Real.log q ≤ Real.log (L ^ B) := Real.log_le_log (by linarith) hqL
    rw [Real.log_rpow hL0] at h1
    have h2 : Real.log L ≤ L := Real.log_le_self hL0.le
    nlinarith
  have hlogq0 : 0 ≤ Real.log q := Real.log_nonneg hq1
  have hE1 : 2 * Real.log q * Real.log N ≤ 2 * B * Kp * X := by
    rw [← hL]
    have h2 : L ^ 2 ≤ Kp * Y := by
      have := hpoly N hN1
      rw [hY]; rw [← hL, ← hs] at this; linarith
    have h3 : 2 * Real.log q * L ≤ 2 * B * L ^ 2 := by nlinarith
    have h4 : 2 * B * L ^ 2 ≤ 2 * B * (Kp * Y) :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    have h5 : 2 * B * (Kp * Y) ≤ 2 * B * (Kp * X) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hYX hKp.le) (by positivity)
    nlinarith
  -- the principal part
  have hPb : ‖primeExpSum N β - linearExpSum N β‖ ≤ C3 * X := by
    have hP' := hP N hN β
    rw [← hL, ← hs] at hP'
    refine hP'.trans ?_
    have : Real.exp (-c3 * s) ≤ Real.exp (-cf * s) := Real.exp_le_exp.mpr (by nlinarith)
    rw [hX, hY]
    have h0 : 0 ≤ C3 * (1 + N * |β|) * N := by positivity
    calc C3 * (1 + N * |β|) * N * Real.exp (-c3 * s)
        ≤ C3 * (1 + N * |β|) * N * Real.exp (-cf * s) := mul_le_mul_of_nonneg_left this h0
      _ = _ := by ring
  -- the nonprincipal characters
  have hau : IsUnit (a : ZMod q) := (ZMod.isUnit_intCast_iff_isCoprime a q).mpr ha.symm
  obtain ⟨f, hf⟩ : ∃ f : DirichletCharacter ℂ q → ℂ, f = fun χ =>
      gaussSum χ⁻¹ ZMod.stdAddChar * χ a * twistedExpSum χ N β := ⟨_, rfl⟩
  have hsplit : (q.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q,
        gaussSum χ⁻¹ ZMod.stdAddChar * χ a * twistedExpSum χ N β =
      (μ q : ℂ) / q.totient * twistedExpSum (1 : DirichletCharacter ℂ q) N β +
        (q.totient : ℂ)⁻¹ * ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q), f χ := by
    have : ∑ χ : DirichletCharacter ℂ q,
        gaussSum χ⁻¹ ZMod.stdAddChar * χ a * twistedExpSum χ N β =
        ∑ χ : DirichletCharacter ℂ q, f χ := by rw [hf]
    rw [this, ← Finset.add_sum_erase Finset.univ f (Finset.mem_univ 1)]
    have h1 : f 1 = (μ q : ℂ) * twistedExpSum (1 : DirichletCharacter ℂ q) N β := by
      rw [hf]
      simp only [inv_one, gaussSum_one_stdAddChar, MulChar.one_apply hau, mul_one]
    rw [h1]; ring
  have hR' : ‖(q.totient : ℂ)⁻¹ * ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q), f χ‖ ≤
      C1 * Ka * X := by
    have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
    have hW0 : 0 ≤ C1 * (1 + N * |β|) * N * Real.exp (-c1 * s) := by positivity
    have hfχ : ∀ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
        ‖f χ‖ ≤ q * (C1 * (1 + N * |β|) * N * Real.exp (-c1 * s)) := by
      intro χ hχ
      have hχ1 : χ ≠ 1 := Finset.ne_of_mem_erase hχ
      rw [hf]
      simp only
      rw [norm_mul, norm_mul]
      have h1 := norm_gaussSum_le χ⁻¹
      have h2 := DirichletCharacter.norm_le_one χ a
      have h3 := h10 N hN q hq hqL0 χ hχ1 β
      rw [← hL, ← hs] at h3
      have h4 : 0 ≤ ‖twistedExpSum χ N β‖ := norm_nonneg _
      calc _ ≤ (q : ℝ) * 1 * (C1 * (1 + N * |β|) * N * Real.exp (-c1 * s)) := by
            gcongr
        _ = _ := by ring
    have hsum : ‖∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q), f χ‖ ≤
        q.totient * (q * (C1 * (1 + N * |β|) * N * Real.exp (-c1 * s))) := by
      refine (norm_sum_le _ _).trans ((Finset.sum_le_sum hfχ).trans ?_)
      rw [Finset.sum_const, nsmul_eq_mul]
      have hc : ((Finset.univ.erase (1 : DirichletCharacter ℂ q)).card : ℝ) ≤ q.totient := by
        have := Finset.card_erase_le (s := (Finset.univ : Finset (DirichletCharacter ℂ q)))
          (a := 1)
        rw [Finset.card_univ, card_dirichletCharacter_nat] at this
        exact_mod_cast this
      exact mul_le_mul_of_nonneg_right hc (by positivity)
    rw [norm_mul, norm_inv, Complex.norm_natCast]
    calc (q.totient : ℝ)⁻¹ * ‖∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q), f χ‖
        ≤ (q.totient : ℝ)⁻¹ * (q.totient * (q * (C1 * (1 + N * |β|) * N *
            Real.exp (-c1 * s)))) := mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = q * (C1 * (1 + N * |β|) * N * Real.exp (-c1 * s)) := by field_simp
      _ ≤ L ^ B * (C1 * (1 + N * |β|) * N * Real.exp (-c1 * s)) :=
          mul_le_mul_of_nonneg_right hqL hW0
      _ = C1 * (1 + N * |β|) * N * (L ^ B * Real.exp (-c1 * s)) := by ring
      _ ≤ C1 * (1 + N * |β|) * N * (Ka * Real.exp (-(c1 / 2) * s)) := by
          have := habs L hL0.le
          rw [← hs] at this
          exact mul_le_mul_of_nonneg_left this (by positivity)
      _ ≤ C1 * (1 + N * |β|) * N * (Ka * Real.exp (-cf * s)) := by
          have : Real.exp (-(c1 / 2) * s) ≤ Real.exp (-cf * s) :=
            Real.exp_le_exp.mpr (by nlinarith)
          gcongr
      _ = C1 * Ka * X := by rw [hX, hY]; ring
  -- assemble
  have hμ : ‖(μ q : ℂ) / q.totient‖ ≤ 1 := by
    rw [norm_div, Complex.norm_natCast]
    have h1 : ‖(μ q : ℂ)‖ ≤ 1 := by
      have := ArithmeticFunction.abs_moebius_le_one (n := q)
      rw [Complex.norm_intCast]
      exact_mod_cast this
    have h2 : (1 : ℝ) ≤ q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
    exact div_le_one_of_le₀ (h1.trans h2) (by linarith)
  have h26_8 := norm_primeExpSum_sub_charExpansion_le ha N β
  have h1' := norm_primeExpSum_sub_principal_le q N β
  rw [← hL] at h26_8 h1'
  have hident : primeExpSum N (a / q + β) - (μ q : ℂ) / q.totient * linearExpSum N β =
      (primeExpSum N (a / q + β) - (q.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q,
        gaussSum χ⁻¹ ZMod.stdAddChar * χ a * twistedExpSum χ N β) +
      (μ q : ℂ) / q.totient * ((twistedExpSum (1 : DirichletCharacter ℂ q) N β -
          primeExpSum N β) + (primeExpSum N β - linearExpSum N β)) +
      (q.totient : ℂ)⁻¹ * ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q), f χ := by
    rw [hsplit]; ring
  rw [hident]
  have e1 : ‖twistedExpSum (1 : DirichletCharacter ℂ q) N β - primeExpSum N β‖ ≤
      2 * Real.log q * L := by rw [norm_sub_rev]; exact h1'
  have hmid : ‖(μ q : ℂ) / q.totient * ((twistedExpSum (1 : DirichletCharacter ℂ q) N β -
          primeExpSum N β) + (primeExpSum N β - linearExpSum N β))‖ ≤
      2 * Real.log q * L + C3 * X := by
    rw [norm_mul]
    have h3 := (norm_add_le _ _).trans (add_le_add e1 hPb)
    calc _ ≤ 1 * (2 * Real.log q * L + C3 * X) :=
          mul_le_mul hμ h3 (norm_nonneg _) zero_le_one
      _ = _ := one_mul _
  rw [← hL] at hE1
  calc _ ≤ ‖(primeExpSum N (a / q + β) - (q.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q,
        gaussSum χ⁻¹ ZMod.stdAddChar * χ a * twistedExpSum χ N β)‖ +
      ‖(μ q : ℂ) / q.totient * ((twistedExpSum (1 : DirichletCharacter ℂ q) N β -
          primeExpSum N β) + (primeExpSum N β - linearExpSum N β))‖ +
      ‖(q.totient : ℂ)⁻¹ * ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q), f χ‖ :=
        norm_add₃_le
    _ ≤ (2 * B * Kp * X) + (2 * Real.log q * L + C3 * X) + C1 * Ka * X := by
        gcongr
        exact h26_8.trans hE1
    _ ≤ (4 * B * Kp + C3 + C1 * Ka) * X := by nlinarith
    _ = _ := by rw [hX, hY]; ring

end NTKB.Davenport
