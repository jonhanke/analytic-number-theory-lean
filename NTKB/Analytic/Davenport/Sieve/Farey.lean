/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Davenport.Sieve.LargeSieve
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Mathlib.Analysis.Fourier.ZMod

/-!
# The large sieve at Farey fractions; Rényi's form; the sieve form (Davenport, Chapter 27)

* inequality (8): `∑_{q ≤ Q} ∑_{(a, q) = 1} |S(a/q)|² ≤ (N + 3Q²) ∑ |a_n|²`
  (`large_sieve_farey`), since distinct Farey fractions of order `Q` are `Q⁻²`-separated;
* the identity `q V(q) = ∑_{a=1}^{q-1} |S(a/q)|²` for the variance `V(q)` of the counts `Z(q, h)`
  of a set of integers in the residue classes modulo `q` (`mul_variance_eq`);
* inequality (9) (Rényi's form): `∑_{p ≤ Q} p V(p) ≤ (N + 3Q²) Z` (`sum_prime_mul_variance_le`);
* **Theorem 3** (the sieve form): if a set of `Z` integers in an interval of length `N` misses at
  least `τ p` residue classes modulo each prime `p` of a set of `P` primes `≤ Q`, then
  `Z ≤ (N + 3Q²)/(τ P)` (`card_le_of_sieve`).
-/

open Finset Real ComplexConjugate

namespace NTKB.Davenport

/-! ### Farey fractions are separated -/

/-- Distinct reduced fractions `a/q`, `a'/q'` with `1 ≤ a ≤ q ≤ Q`, `1 ≤ a' ≤ q' ≤ Q` satisfy
`‖a/q - a'/q'‖ ≥ Q⁻²`. -/
lemma farey_separated {Q : ℕ} (x y : Σ _ : ℕ, ℕ)
    (hx : x ∈ (Icc 1 Q).sigma (fun q ↦ (Icc 1 q).filter (fun b ↦ Nat.Coprime b q)))
    (hy : y ∈ (Icc 1 Q).sigma (fun q ↦ (Icc 1 q).filter (fun b ↦ Nat.Coprime b q)))
    (hxy : x ≠ y) (m : ℤ) :
    1 / (Q : ℝ) ^ 2 ≤ |(x.2 : ℝ) / x.1 - y.2 / y.1 - m| := by
  obtain ⟨q, b⟩ := x
  obtain ⟨q', b'⟩ := y
  simp only [mem_sigma, mem_Icc, mem_filter] at hx hy
  obtain ⟨⟨hq1, hqQ⟩, ⟨hb1, hbq⟩, hcop⟩ := hx
  obtain ⟨⟨hq1', hqQ'⟩, ⟨hb1', hbq'⟩, hcop'⟩ := hy
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
  have hq0' : (0 : ℝ) < q' := by exact_mod_cast hq1'
  set D : ℤ := b * q' - b' * q - m * q * q'
  have hD : (b : ℝ) / q - b' / q' - m = D / (q * q') := by
    simp only [D]; push_cast; field_simp
  -- `D ≠ 0`
  have hD0 : D ≠ 0 := by
    intro hD0
    have hm : m = 0 := by
      have h1 : (b : ℝ) / q - b' / q' = m := by
        have := hD; rw [hD0, Int.cast_zero, zero_div] at this; linarith
      have hlo : 0 < (b : ℝ) / q := by
        have : (0 : ℝ) < b := by exact_mod_cast hb1
        positivity
      have hhi : (b : ℝ) / q ≤ 1 := by rw [div_le_one hq0]; exact_mod_cast hbq
      have hlo' : 0 < (b' : ℝ) / q' := by
        have : (0 : ℝ) < b' := by exact_mod_cast hb1'
        positivity
      have hhi' : (b' : ℝ) / q' ≤ 1 := by rw [div_le_one hq0']; exact_mod_cast hbq'
      have h2 : (m : ℝ) < 1 := by linarith
      have h3 : (-1 : ℝ) < m := by linarith
      have : m < 1 := by exact_mod_cast h2
      have : -1 < m := by exact_mod_cast h3
      omega
    simp only [D, hm, zero_mul, sub_zero] at hD0
    have heq : b * q' = b' * q := by
      have : ((b * q' : ℕ) : ℤ) = ((b' * q : ℕ) : ℤ) := by push_cast; linarith
      exact_mod_cast this
    have h1 : q ∣ q' := by
      have : q ∣ b * q' := ⟨b', by rw [heq, mul_comm]⟩
      exact (Nat.Coprime.symm hcop).dvd_of_dvd_mul_left this
    have h2 : q' ∣ q := by
      have : q' ∣ b' * q := ⟨b, by rw [← heq, mul_comm]⟩
      exact (Nat.Coprime.symm hcop').dvd_of_dvd_mul_left this
    have hqq : q = q' := Nat.dvd_antisymm h1 h2
    subst hqq
    have hbb : b = b' := Nat.eq_of_mul_eq_mul_right (by omega) heq
    subst hbb
    exact hxy rfl
  rw [hD, abs_div, abs_of_pos (by positivity : (0 : ℝ) < q * q')]
  have hD1 : (1 : ℝ) ≤ |(D : ℝ)| := by
    rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hD0
  have hQq : (q : ℝ) * q' ≤ (Q : ℝ) ^ 2 := by
    rw [sq]; gcongr
  calc 1 / (Q : ℝ) ^ 2 ≤ 1 / (q * q') := one_div_le_one_div_of_le (by positivity) hQq
    _ ≤ |(D : ℝ)| / (q * q') := by gcongr

/-- **Davenport, Ch. 27, inequality (8)**: for real `Q ≥ 1`,
`∑_{q ≤ Q} ∑_{a ≤ q, (a, q) = 1} |S(a/q)|² ≤ (N + 3Q²) ∑_{M < n ≤ M + N} |a_n|²`. -/
@[kb "davenport1980" "Ch 27, p. 157, (8)"]
theorem large_sieve_farey {Q : ℝ} (hQ : 1 ≤ Q) (M : ℤ) (N : ℕ) (c : ℤ → ℂ) :
    ∑ q ∈ Icc 1 ⌊Q⌋₊, ∑ b ∈ (Icc 1 q).filter (fun b ↦ Nat.Coprime b q),
        ‖∑ n ∈ Ioc M (M + N), c n * Complex.exp (2 * π * Complex.I * (n * (((b : ℝ) / q : ℝ) : ℂ)))‖ ^ 2 ≤
      (N + 3 * Q ^ 2) * ∑ n ∈ Ioc M (M + N), ‖c n‖ ^ 2 := by
  set Q' := ⌊Q⌋₊
  have hQ' : 1 ≤ Q' := Nat.le_floor (by exact_mod_cast hQ)
  have hQ'r : (0 : ℝ) < Q' := by exact_mod_cast hQ'
  rw [← sum_sigma (Icc 1 Q') (fun q ↦ (Icc 1 q).filter (fun b ↦ Nat.Coprime b q))
    (fun x ↦ ‖∑ n ∈ Ioc M (M + N), c n *
      Complex.exp (2 * π * Complex.I * (n * (((x.2 : ℝ) / x.1 : ℝ) : ℂ)))‖ ^ 2)]
  have h := large_sieve ((Icc 1 Q').sigma (fun q ↦ (Icc 1 q).filter (fun b ↦ Nat.Coprime b q)))
    (fun x ↦ (x.2 : ℝ) / x.1) (δ := 1 / (Q' : ℝ) ^ 2) (by positivity)
    (fun x hx y hy hxy m ↦ farey_separated x y hx hy hxy m) M N c
  refine h.trans ?_
  gcongr
  have : 3 / (1 / (Q' : ℝ) ^ 2) = 3 * (Q' : ℝ) ^ 2 := by field_simp
  rw [this]
  have : (Q' : ℝ) ≤ Q := Nat.floor_le (by linarith)
  gcongr

/-! ### Rényi's variance -/

/-- Orthogonality of additive characters: `∑_{b < q} e(db/q) = q [q ∣ d]`. -/
lemma sum_range_exp_eq {q : ℕ} (hq : 0 < q) (d : ℤ) :
    ∑ b ∈ range q, Complex.exp (2 * π * Complex.I * (d * (((b : ℝ) / q : ℝ) : ℂ))) =
      if (q : ℤ) ∣ d then (q : ℂ) else 0 := by
  have : NeZero q := ⟨hq.ne'⟩
  have e : ∀ b : ℕ, Complex.exp (2 * π * Complex.I * (d * (((b : ℝ) / q : ℝ) : ℂ))) =
      ZMod.stdAddChar ((b : ZMod q) * (d : ZMod q)) := by
    intro b
    rw [show (b : ZMod q) * (d : ZMod q) = (((b : ℤ) * d : ℤ) : ZMod q) by push_cast; ring,
      ZMod.stdAddChar_coe]
    congr 1; push_cast; ring
  simp_rw [e]
  rw [← Apostol.sum_zmod_eq_sum_range (fun x : ZMod q ↦ ZMod.stdAddChar (x * (d : ZMod q))),
    AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar q), ZMod.card]
  by_cases hd : (q : ℤ) ∣ d
  · rw [if_pos ((ZMod.intCast_zmod_eq_zero_iff_dvd d q).2 hd), if_pos hd]
  · rw [if_neg (mt (ZMod.intCast_zmod_eq_zero_iff_dvd d q).1 hd), if_neg hd, Nat.cast_zero]

/-- The residue class counts: `∑_{m, n ∈ Z} [m ≡ n (mod q)] = ∑_{h < q} Z(q, h)²`. -/
lemma sum_sum_dvd_eq {q : ℕ} (hq : 0 < q) (Z : Finset ℤ) :
    ∑ m ∈ Z, ((Z.filter (fun n ↦ (q : ℤ) ∣ m - n)).card : ℝ) =
      ∑ h ∈ range q, ((Z.filter (fun n ↦ n ≡ h [ZMOD q])).card : ℝ) ^ 2 := by
  have hq' : (0 : ℤ) < q := by exact_mod_cast hq
  set key : ℤ → ℕ := fun m ↦ (m % (q : ℤ)).toNat
  have hkey : ∀ m, key m ∈ range q := by
    intro m; simp only [key, mem_range]
    have := Int.emod_lt_of_pos m hq'; have := Int.emod_nonneg m hq'.ne'; omega
  have hmod : ∀ (m : ℤ) (h : ℕ), h < q → (m ≡ h [ZMOD q] ↔ key m = h) := by
    intro m h hh
    simp only [key, Int.ModEq]
    have e : (h : ℤ) % q = h := Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hh)
    rw [e]
    have := Int.emod_nonneg m hq'.ne'; omega
  rw [← sum_fiberwise_of_maps_to (g := key) (t := range q) (fun m _ ↦ hkey m)]
  refine sum_congr rfl fun h hh ↦ ?_
  have hh := mem_range.1 hh
  have hfib : Z.filter (fun m ↦ key m = h) = Z.filter (fun n ↦ n ≡ h [ZMOD q]) :=
    filter_congr fun m _ ↦ (hmod m h hh).symm
  rw [hfib, sq, ← nsmul_eq_mul, ← sum_const]
  refine sum_congr rfl fun m hm ↦ ?_
  have hm := (mem_filter.1 hm).2
  congr 2
  refine filter_congr fun n _ ↦ ?_
  rw [← Int.modEq_iff_dvd]
  exact ⟨fun h1 ↦ h1.trans hm, fun h1 ↦ h1.trans hm.symm⟩

lemma exp_mul_conj_exp (m n : ℤ) (x : ℝ) :
    Complex.exp (2 * π * Complex.I * (m * (x : ℂ))) *
        conj (Complex.exp (2 * π * Complex.I * (n * (x : ℂ)))) =
      Complex.exp (2 * π * Complex.I * (((m - n : ℤ) : ℂ) * (x : ℂ))) := by
  rw [show (n : ℂ) * (x : ℂ) = (((n : ℝ) * x : ℝ) : ℂ) by push_cast; ring, exp_two_pi_I_mul_conj,
    ← Complex.exp_add]
  congr 1; push_cast; ring

/-- **Davenport, Ch. 27**: for a finite set `Z` of integers with `Z(q, h)` members in the class
`h` modulo `q`, the variance `V(q) = ∑_h (Z(q, h) - Z/q)²` satisfies
`q V(q) = ∑_{a=1}^{q-1} |S(a/q)|²` with `S(α) = ∑_{n ∈ Z} e(nα)`. -/
@[kb "davenport1980" "Ch 27, p. 158"]
theorem mul_variance_eq {q : ℕ} (hq : 0 < q) (Z : Finset ℤ) :
    (q : ℝ) * ∑ h ∈ range q, (((Z.filter (fun n ↦ n ≡ h [ZMOD q])).card : ℝ) - Z.card / q) ^ 2 =
      ∑ b ∈ Icc 1 (q - 1),
        ‖∑ n ∈ Z, Complex.exp (2 * π * Complex.I * (n * (((b : ℝ) / q : ℝ) : ℂ)))‖ ^ 2 := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  set Zh : ℕ → ℝ := fun h ↦ ((Z.filter (fun n ↦ n ≡ h [ZMOD q])).card : ℝ)
  set S : ℕ → ℂ := fun b ↦
    ∑ n ∈ Z, Complex.exp (2 * π * Complex.I * (n * (((b : ℝ) / q : ℝ) : ℂ)))
  -- (A) the full sum over `b < q`
  have hA : ∑ b ∈ range q, ‖S b‖ ^ 2 = q * ∑ h ∈ range q, Zh h ^ 2 := by
    apply Complex.ofReal_injective
    push_cast
    simp_rw [← Complex.mul_conj', S, map_sum, sum_mul_sum, exp_mul_conj_exp]
    rw [sum_comm]
    refine (sum_congr rfl fun m _ ↦ sum_comm).trans ?_
    rw [sum_congr rfl fun m _ ↦ sum_congr rfl fun n _ ↦ sum_range_exp_eq hq (m - n)]
    have := sum_sum_dvd_eq hq Z
    apply_fun ((↑) : ℝ → ℂ) at this
    push_cast at this
    simp only [Zh, Complex.ofReal_natCast]
    rw [← this, mul_sum]
    refine sum_congr rfl fun m _ ↦ ?_
    rw [← sum_filter, sum_const, nsmul_eq_mul, mul_comm]
  -- (B) the term `b = 0`
  have hB : ‖S 0‖ ^ 2 = (Z.card : ℝ) ^ 2 := by
    simp [S]
  -- (C) the counts add up
  have hC : ∑ h ∈ range q, Zh h = Z.card := by
    have := sum_sum_dvd_eq hq Z
    have hk : ∀ m ∈ Z, ((m % (q : ℤ)).toNat) ∈ range q := by
      intro m _; simp only [mem_range]
      have := Int.emod_lt_of_pos m (by exact_mod_cast hq : (0 : ℤ) < q)
      have := Int.emod_nonneg m (by exact_mod_cast hq.ne' : (q : ℤ) ≠ 0); omega
    rw [card_eq_sum_card_fiberwise hk]
    push_cast
    refine sum_congr rfl fun h hh ↦ ?_
    have hh := mem_range.1 hh
    simp only [Zh]
    congr 2
    refine filter_congr fun m _ ↦ ?_
    simp only [Int.ModEq]
    have e : (h : ℤ) % q = h := Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hh)
    rw [e]
    have := Int.emod_nonneg m (by exact_mod_cast hq.ne' : (q : ℤ) ≠ 0); omega
  have hsplit : ∑ b ∈ range q, ‖S b‖ ^ 2 = ‖S 0‖ ^ 2 + ∑ b ∈ Icc 1 (q - 1), ‖S b‖ ^ 2 := by
    rw [range_eq_Ico, sum_eq_sum_Ico_succ_bot hq]
    congr 1
  have : ∑ b ∈ Icc 1 (q - 1), ‖S b‖ ^ 2 = q * ∑ h ∈ range q, Zh h ^ 2 - (Z.card : ℝ) ^ 2 := by
    rw [← hA, hsplit, hB]; ring
  rw [this]
  simp only [sub_sq, sum_add_distrib, sum_sub_distrib, ← sum_mul, ← mul_sum, sum_const,
    card_range, nsmul_eq_mul]
  rw [hC]
  field_simp
  ring

/-- **Davenport, Ch. 27, inequality (9)** (Rényi's form of the large sieve): for a set `Z` of
integers in `(M, M + N]` and real `Q ≥ 1`, `∑_{p ≤ Q} p V(p) ≤ (N + 3Q²) |Z|`. -/
@[kb "davenport1980" "Ch 27, p. 158, (9)"]
theorem sum_prime_mul_variance_le {Q : ℝ} (hQ : 1 ≤ Q) (M : ℤ) (N : ℕ) (Z : Finset ℤ)
    (hZ : Z ⊆ Ioc M (M + N)) :
    ∑ p ∈ (Icc 1 ⌊Q⌋₊).filter Nat.Prime, (p : ℝ) *
        ∑ h ∈ range p, (((Z.filter (fun n ↦ n ≡ h [ZMOD p])).card : ℝ) - Z.card / p) ^ 2 ≤
      (N + 3 * Q ^ 2) * Z.card := by
  classical
  set c : ℤ → ℂ := fun n ↦ if n ∈ Z then 1 else 0
  have hS : ∀ x : ℝ, ∑ n ∈ Z, Complex.exp (2 * π * Complex.I * (n * (x : ℂ))) =
      ∑ n ∈ Ioc M (M + N), c n * Complex.exp (2 * π * Complex.I * (n * (x : ℂ))) := by
    intro x
    rw [← sum_subset hZ (fun n _ hn ↦ by simp [c, hn])]
    refine sum_congr rfl fun n hn ↦ ?_
    simp [c, hn]
  have hc : ∑ n ∈ Ioc M (M + N), ‖c n‖ ^ 2 = Z.card := by
    rw [← sum_subset hZ (fun n _ hn ↦ by simp [c, hn])]
    rw [card_eq_sum_ones, Nat.cast_sum]
    refine sum_congr rfl fun n hn ↦ ?_
    simp [c, hn]
  have h8 := large_sieve_farey hQ M N c
  rw [hc] at h8
  refine le_trans ?_ h8
  calc _ = ∑ p ∈ (Icc 1 ⌊Q⌋₊).filter Nat.Prime, ∑ b ∈ Icc 1 (p - 1),
        ‖∑ n ∈ Ioc M (M + N), c n *
          Complex.exp (2 * π * Complex.I * (n * (((b : ℝ) / p : ℝ) : ℂ)))‖ ^ 2 := by
        refine sum_congr rfl fun p hp ↦ ?_
        have hp0 : 0 < p := (mem_filter.1 hp).2.pos
        rw [mul_variance_eq hp0]
        refine sum_congr rfl fun b _ ↦ ?_
        rw [hS]
    _ ≤ ∑ q ∈ Icc 1 ⌊Q⌋₊, ∑ b ∈ (Icc 1 q).filter (fun b ↦ Nat.Coprime b q),
        ‖∑ n ∈ Ioc M (M + N), c n *
          Complex.exp (2 * π * Complex.I * (n * (((b : ℝ) / q : ℝ) : ℂ)))‖ ^ 2 := by
        refine (sum_le_sum fun p hp ↦ sum_le_sum_of_subset_of_nonneg ?_
          (fun _ _ _ ↦ by positivity)).trans
          (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ ↦ by positivity)
        intro b hb
        have hpp := (mem_filter.1 hp).2
        simp only [mem_Icc] at hb
        simp only [mem_filter, mem_Icc]
        refine ⟨⟨hb.1, by omega⟩, ?_⟩
        have hp2 := hpp.two_le
        exact Nat.coprime_comm.1 (Nat.coprime_of_lt_prime (by omega) (by omega) hpp)

/-- **Davenport, Ch. 27, Theorem 3** (the large sieve as a sieve): let `Z` be a set of integers in
`(M, M + N]`, let `P` be a nonempty set of primes `p ≤ Q`, let `τ > 0`, and suppose that for every
`p ∈ P` at least `τ p` residue classes modulo `p` contain no element of `Z`. Then
`|Z| ≤ (N + 3Q²)/(τ |P|)`. -/
@[kb "davenport1980" "Ch 27, p. 159, Theorem 3"]
theorem card_le_of_sieve {Q : ℝ} (M : ℤ) (N : ℕ) (Z : Finset ℤ) (hZ : Z ⊆ Ioc M (M + N))
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime ∧ (p : ℝ) ≤ Q) (hPne : P.Nonempty) {τ : ℝ} (hτ : 0 < τ)
    (hmiss : ∀ p ∈ P, τ * p ≤
      ((range p).filter (fun h : ℕ ↦ (Z.filter (fun n ↦ n ≡ h [ZMOD p])).card = 0)).card) :
    (Z.card : ℝ) ≤ (N + 3 * Q ^ 2) / (τ * P.card) := by
  classical
  obtain ⟨p₀, hp₀⟩ := hPne
  have hQ : 1 ≤ Q := by
    have := (hP p₀ hp₀).2
    have : (2 : ℝ) ≤ p₀ := by exact_mod_cast (hP p₀ hp₀).1.two_le
    linarith
  set V : ℕ → ℝ := fun p ↦
    ∑ h ∈ range p, (((Z.filter (fun n ↦ n ≡ h [ZMOD p])).card : ℝ) - Z.card / p) ^ 2
  -- `p V(p) ≥ τ |Z|²` for `p ∈ P`
  have hlow : ∀ p ∈ P, τ * (Z.card : ℝ) ^ 2 ≤ p * V p := by
    intro p hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (hP p hp).1.pos
    set E := (range p).filter (fun h : ℕ ↦ (Z.filter (fun n ↦ n ≡ h [ZMOD p])).card = 0)
    have h1 : ∑ h ∈ E, ((Z.card : ℝ) / p) ^ 2 ≤ V p := by
      calc ∑ h ∈ E, ((Z.card : ℝ) / p) ^ 2 = ∑ h ∈ E,
            (((Z.filter (fun n ↦ n ≡ h [ZMOD p])).card : ℝ) - Z.card / p) ^ 2 := by
            refine sum_congr rfl fun h hh ↦ ?_
            rw [(mem_filter.1 hh).2]; simp
        _ ≤ V p := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ ↦ sq_nonneg _
    rw [sum_const, nsmul_eq_mul] at h1
    have h2 := hmiss p hp
    calc τ * (Z.card : ℝ) ^ 2 = p * ((τ * p) * ((Z.card : ℝ) / p) ^ 2) := by
          field_simp
      _ ≤ p * ((E.card : ℝ) * ((Z.card : ℝ) / p) ^ 2) := by gcongr
      _ ≤ p * V p := by gcongr
  have hsum : τ * P.card * (Z.card : ℝ) ^ 2 ≤ (N + 3 * Q ^ 2) * Z.card := by
    calc τ * P.card * (Z.card : ℝ) ^ 2 = ∑ p ∈ P, τ * (Z.card : ℝ) ^ 2 := by
          rw [sum_const, nsmul_eq_mul]; ring
      _ ≤ ∑ p ∈ P, (p : ℝ) * V p := sum_le_sum hlow
      _ ≤ ∑ p ∈ (Icc 1 ⌊Q⌋₊).filter Nat.Prime, (p : ℝ) * V p := by
          refine sum_le_sum_of_subset_of_nonneg (fun p hp ↦ ?_) (fun p _ _ ↦ ?_)
          · obtain ⟨hpp, hpQ⟩ := hP p hp
            simp only [mem_filter, mem_Icc]
            exact ⟨⟨hpp.one_lt.le, Nat.le_floor hpQ⟩, hpp⟩
          · exact mul_nonneg (Nat.cast_nonneg _) (sum_nonneg fun _ _ ↦ sq_nonneg _)
      _ ≤ (N + 3 * Q ^ 2) * Z.card := sum_prime_mul_variance_le hQ M N Z hZ
  have hPc : (0 : ℝ) < P.card := by exact_mod_cast card_pos.2 ⟨p₀, hp₀⟩
  rcases (Nat.cast_nonneg (Z.card) : (0 : ℝ) ≤ Z.card).eq_or_lt with h0 | hpos
  · rw [← h0]; positivity
  rw [le_div_iff₀ (by positivity)]
  have : τ * P.card * (Z.card : ℝ) * Z.card ≤ (N + 3 * Q ^ 2) * Z.card := by nlinarith
  nlinarith

end NTKB.Davenport
