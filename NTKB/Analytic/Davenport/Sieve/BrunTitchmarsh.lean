/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Davenport.Sieve.Montgomery
import NTKB.Port.SelbergBounds

/-!
# The Brun–Titchmarsh inequality from Montgomery's large sieve

A corollary of Montgomery's form of the large sieve (Davenport, Ch. 27, p. 159,
`card_le_montgomery`); not stated in Davenport. Take for `Z` the primes in `(M, M + N]` larger
than `Q`: modulo each prime `ℓ ≤ Q` the class `0` is empty, so `ω(ℓ) ≥ 1` and
`ω(ℓ)/(ℓ - ω(ℓ)) ≥ 1/(ℓ - 1)`; hence `L ≥ ∑_{q ≤ Q} μ(q)²/φ(q) ≥ log Q`
(`NTKB.Port.SelbergBounds.log_le_sum_moebius_sq_div_totient`, ported from Tau Ceti).

* `brun_titchmarsh`: `π(M + N) - π(M) ≤ (N + 3Q²)/log Q + Q` for every real `Q > 1`;
* `brun_titchmarsh_asymptotic`: for every `ε > 0`, `π(M + N) - π(M) ≤ (2 + ε) N/log N` for all
  `M` once `N` is large.
-/

open Finset Real
open scoped ArithmeticFunction.Moebius

namespace NTKB.Davenport

/-- For a prime `ℓ ≤ Q`, the class `0` modulo `ℓ` contains no prime larger than `Q`; hence for the
set `Z` of such primes (nonempty) `1 ≤ ω(ℓ) < ℓ`. -/
private lemma sieveOmega_bounds_of_primes (Z : Finset ℤ) (Q : ℝ) (hZ : Z.Nonempty)
    (hZp : ∀ n ∈ Z, ∃ p : ℕ, p.Prime ∧ Q < p ∧ n = p) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hℓQ : (ℓ : ℝ) ≤ Q) :
    1 ≤ sieveOmega Z ℓ ∧ sieveOmega Z ℓ < ℓ := by
  unfold sieveOmega
  constructor
  · rw [Nat.one_le_iff_ne_zero, Ne, Finset.card_eq_zero, ← Ne, ← Finset.nonempty_iff_ne_empty]
    refine ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hℓ.pos, ?_⟩⟩
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro n hn hmod
    obtain ⟨p, hp, hQp, rfl⟩ := hZp n hn
    have h1 : (ℓ : ℤ) ∣ (p : ℤ) :=
      (Int.modEq_zero_iff_dvd).mp (by simpa using hmod)
    have h2 : ℓ ∣ p := by exact_mod_cast h1
    have h3 := (Nat.prime_dvd_prime_iff_eq hℓ hp).mp h2
    have : (ℓ : ℝ) = p := by exact_mod_cast h3
    linarith
  · obtain ⟨z, hz⟩ := hZ
    have hℓ0 : (0 : ℤ) < ℓ := by exact_mod_cast hℓ.pos
    set h : ℕ := (z % ℓ).toNat with hh
    have h0 : 0 ≤ z % (ℓ : ℤ) := Int.emod_nonneg _ hℓ0.ne'
    have hhlt : h < ℓ := by
      have : z % (ℓ : ℤ) < ℓ := Int.emod_lt_of_pos _ hℓ0
      omega
    have hzh : z ≡ (h : ℤ) [ZMOD ℓ] := by
      have : (h : ℤ) = z % ℓ := by rw [hh]; exact Int.toNat_of_nonneg h0
      rw [this]; exact (Int.mod_modEq z ℓ).symm
    calc _ < (range ℓ).card := by
          refine Finset.card_lt_card ⟨Finset.filter_subset _ _, fun hsub => ?_⟩
          have := hsub (Finset.mem_range.mpr hhlt)
          rw [Finset.mem_filter, Finset.card_eq_zero, Finset.filter_eq_empty_iff] at this
          exact this.2 hz hzh
      _ = ℓ := Finset.card_range ℓ

/-- `L ≥ log Q` when `Z` is a nonempty set of primes larger than `Q`. -/
private lemma log_le_montgomeryL (Z : Finset ℤ) {Q : ℝ} (hQ : 1 ≤ Q) (hZ : Z.Nonempty)
    (hZp : ∀ n ∈ Z, ∃ p : ℕ, p.Prime ∧ Q < p ∧ n = p) :
    Real.log Q ≤ montgomeryL Z Q := by
  refine (NTKB.Port.SelbergBounds.log_le_sum_moebius_sq_div_totient (by linarith)).trans ?_
  unfold montgomeryL
  refine Finset.sum_le_sum fun q hq => ?_
  by_cases hsq : Squarefree q
  · have hμ : ((μ q : ℤ) : ℝ) ^ 2 = 1 := by
      have h0 := ArithmeticFunction.moebius_ne_zero_iff_squarefree.mpr hsq
      rcases ArithmeticFunction.moebius_eq_or q with h | h | h
      · exact absurd h h0
      · simp [h]
      · simp [h]
    rw [hμ, one_mul, one_div, NTKB.Port.SelbergBounds.totient_eq_prod_sub_one hsq,
      ← Finset.prod_inv_distrib]
    refine Finset.prod_le_prod₀ (fun p hp => ?_) (fun p hp => ?_)
    · have hp2 := (Nat.prime_of_mem_primeFactors hp).two_le
      have : (2 : ℝ) ≤ p := by exact_mod_cast hp2
      exact inv_nonneg.mpr (by linarith)
    · have hpp := Nat.prime_of_mem_primeFactors hp
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
      have hpq : p ≤ q := Nat.le_of_dvd (Finset.mem_Icc.mp hq).1 (Nat.dvd_of_mem_primeFactors hp)
      have hpQ : (p : ℝ) ≤ Q :=
        (Nat.cast_le.mpr (hpq.trans (Finset.mem_Icc.mp hq).2)).trans (Nat.floor_le (by linarith))
      obtain ⟨h1, h2⟩ := sieveOmega_bounds_of_primes Z Q hZ hZp hpp hpQ
      have h1' : (1 : ℝ) ≤ sieveOmega Z p := by exact_mod_cast h1
      have h2' : (sieveOmega Z p : ℝ) < p := by exact_mod_cast h2
      rw [inv_eq_one_div, div_le_div_iff₀ (by linarith) (by linarith)]
      nlinarith
  · have : μ q = 0 := ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq
    simp [this]

/-- **The Brun–Titchmarsh inequality, explicit form**: for real `Q > 1` and natural `M, N`, the
number of primes in `(M, M + N]` is at most `(N + 3Q²)/log Q + Q`. -/
@[kb "davenport1980" "Ch 27, p. 159"]
theorem brun_titchmarsh {Q : ℝ} (hQ : 1 < Q) (M N : ℕ) :
    (((Ioc M (M + N)).filter Nat.Prime).card : ℝ) ≤ (N + 3 * Q ^ 2) / Real.log Q + Q := by
  classical
  set P := (Ioc M (M + N)).filter Nat.Prime with hP
  have hlog : 0 < Real.log Q := Real.log_pos hQ
  have hnn : 0 ≤ (N + 3 * Q ^ 2) / Real.log Q := by positivity
  have hsplit := Finset.card_filter_add_card_filter_not (s := P) (fun p : ℕ => (p : ℝ) ≤ Q)
  -- small primes
  have hsmall : ((P.filter (fun p : ℕ => (p : ℝ) ≤ Q)).card : ℝ) ≤ Q := by
    have hsub : P.filter (fun p : ℕ => (p : ℝ) ≤ Q) ⊆ Icc 1 ⌊Q⌋₊ := by
      intro p hp
      rw [Finset.mem_filter, hP, Finset.mem_filter] at hp
      exact Finset.mem_Icc.mpr ⟨hp.1.2.one_lt.le, Nat.le_floor hp.2⟩
    have := Finset.card_le_card hsub
    rw [Nat.card_Icc] at this
    calc ((P.filter (fun p : ℕ => (p : ℝ) ≤ Q)).card : ℝ) ≤ ((⌊Q⌋₊ + 1 - 1 : ℕ) : ℝ) := by
          exact_mod_cast this
      _ ≤ Q := by simpa using Nat.floor_le (by linarith : (0 : ℝ) ≤ Q)
  -- large primes
  set P2 := P.filter (fun p : ℕ => ¬ (p : ℝ) ≤ Q) with hP2
  set Z : Finset ℤ := P2.image (fun p : ℕ => (p : ℤ)) with hZ
  have hZcard : Z.card = P2.card :=
    Finset.card_image_of_injective _ Nat.cast_injective
  have hcast : (P.card : ℝ) = (P.filter (fun p : ℕ => (p : ℝ) ≤ Q)).card + P2.card := by
    exact_mod_cast hsplit.symm
  rcases Finset.eq_empty_or_nonempty Z with hZe | hZne
  · have : P2.card = 0 := by rw [← hZcard, hZe]; rfl
    rw [hcast, this]
    simp only [Nat.cast_zero, add_zero]
    linarith
  · have hZsub : Z ⊆ Ioc (M : ℤ) ((M : ℤ) + N) := by
      intro n hn
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hn
      rw [hP2, hP, Finset.mem_filter, Finset.mem_filter, Finset.mem_Ioc] at hp
      rw [Finset.mem_Ioc]
      exact ⟨by exact_mod_cast hp.1.1.1, by exact_mod_cast hp.1.1.2⟩
    have hZp : ∀ n ∈ Z, ∃ p : ℕ, p.Prime ∧ Q < p ∧ n = p := by
      intro n hn
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hn
      rw [hP2, hP, Finset.mem_filter, Finset.mem_filter] at hp
      exact ⟨p, hp.1.2, not_le.mp hp.2, rfl⟩
    have hL := log_le_montgomeryL Z hQ.le hZne hZp
    have hmont := card_le_montgomery hQ.le (M : ℤ) N Z hZsub
    have hle : (Z.card : ℝ) ≤ (N + 3 * Q ^ 2) / Real.log Q :=
      hmont.trans (div_le_div_of_nonneg_left (by positivity) hlog hL)
    rw [hcast, ← hZcard]
    linarith

/-- **The Brun–Titchmarsh inequality** (Montgomery's constant `2`): for every `ε > 0` there is
`N₀` such that every interval `(M, M + N]` with `N ≥ N₀` contains at most `(2 + ε) N/log N`
primes. -/
@[kb "davenport1980" "Ch 27, p. 159"]
theorem brun_titchmarsh_asymptotic {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ M : ℕ,
      (((Ioc M (M + N)).filter Nat.Prime).card : ℝ) ≤ (2 + ε) * N / Real.log N := by
  set a : ℝ := 2 + ε / 2 with ha
  have ha2 : 2 < a := by rw [ha]; linarith
  set θ : ℝ := 1 / a with hθ
  have hθ0 : 0 < θ := by positivity
  have hθ1 : θ < 1 / 2 := by
    rw [hθ, div_lt_div_iff₀ (by linarith) (by norm_num)]; linarith
  set δ : ℝ := (1 - θ) / 2 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  set η : ℝ := ε / (2 * (3 * a + 1 / δ)) with hη
  have hη0 : 0 < η := by positivity
  have hK : η * (3 * a + 1 / δ) = ε / 2 := by
    rw [hη]; field_simp
  have e1 := (tendsto_rpow_neg_atTop (by linarith : 0 < 1 - 2 * θ)).eventually (gt_mem_nhds hη0)
  have e2 := (tendsto_rpow_neg_atTop (by linarith : 0 < (1 - θ) / 2)).eventually (gt_mem_nhds hη0)
  obtain ⟨X, hX⟩ := Filter.eventually_atTop.mp (e1.and e2)
  refine ⟨max 2 ⌈X⌉₊, fun N hN M => ?_⟩
  have hN2 : 2 ≤ N := (le_max_left _ _).trans hN
  have hNX : X ≤ N := (Nat.le_ceil X).trans (by exact_mod_cast (le_max_right _ _).trans hN)
  obtain ⟨hx1, hx2⟩ := hX N hNX
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (by omega : 1 < N)
  have hL : 0 < Real.log N := Real.log_pos hN1
  set Q : ℝ := (N : ℝ) ^ θ with hQdef
  have hQ1 : 1 < Q := Real.one_lt_rpow hN1 hθ0
  have hlogQ : Real.log Q = Real.log N / a := by
    rw [hQdef, Real.log_rpow hNpos, hθ]; ring
  have hQ2 : Q ^ 2 = (N : ℝ) ^ (2 * θ) := by
    rw [hQdef, ← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]; norm_num; ring_nf
  have hA : Q ^ 2 ≤ η * N := by
    rw [hQ2]
    have : (N : ℝ) ^ (2 * θ) = (N : ℝ) ^ (-(1 - 2 * θ)) * N := by
      rw [← Real.rpow_add_one hNpos.ne']; congr 1; ring
    rw [this]; nlinarith
  have hB : Q * Real.log N ≤ η / δ * N := by
    have hlog' := Real.log_le_rpow_div hNpos.le hδ0
    have h1 : Q * Real.log N ≤ Q * ((N : ℝ) ^ δ / δ) := by gcongr
    have h2 : Q * ((N : ℝ) ^ δ / δ) = (N : ℝ) ^ (θ + δ) / δ := by
      rw [hQdef, Real.rpow_add hNpos]; ring
    have h3 : (N : ℝ) ^ (θ + δ) = (N : ℝ) ^ (-((1 - θ) / 2)) * N := by
      rw [← Real.rpow_add_one hNpos.ne']; congr 1; rw [hδ]; ring
    rw [h2, h3] at h1
    refine h1.trans ((div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hx2.le hNpos.le) hδ0.le).trans_eq (by ring))
  have hbt := brun_titchmarsh hQ1 M N
  refine hbt.trans ?_
  rw [hlogQ]
  have hLa : (N + 3 * Q ^ 2) / (Real.log N / a) + Q
      = (a * (N + 3 * Q ^ 2) + Q * Real.log N) / Real.log N := by
    field_simp
  rw [hLa]
  refine div_le_div_of_nonneg_right ?_ hL.le
  have hK2 : (3 * a + 1 / δ) * (η * N) = ε / 2 * N := by rw [← hK]; ring
  have e : η / δ * N = (1 / δ) * (η * N) := by ring
  rw [e] at hB
  have h3 := mul_le_mul_of_nonneg_left hA (by linarith : (0:ℝ) ≤ 3 * a)
  have key : a * N + (3 * a + 1 / δ) * (η * N) = (2 + ε) * N := by rw [hK2, ha]; ring
  nlinarith

end NTKB.Davenport
