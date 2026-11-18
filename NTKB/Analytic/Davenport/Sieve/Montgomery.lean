/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Davenport.Sieve.Farey
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

/-!
# Montgomery's form of the arithmetic large sieve (Davenport, Chapter 27, p. 159)

Davenport (Ch. 27, p. 159) states without proof Montgomery's refinement of Theorem 3: if `Z` is a
set of `|Z|` integers in `(M, M + N]` and `ω(p)` is the number of residue classes `h` modulo `p`
containing no element of `Z`, then `|Z| ≤ (N + 3Q²)/L` with
`L = ∑_{q ≤ Q} μ(q)² ∏_{p ∣ q} ω(p)/(p - ω(p))`.

The proof is Montgomery's (Montgomery 1968; Montgomery, *Topics in multiplicative number theory*,
1971, Ch. 3): for coefficients `c_n` vanishing on `ω(p)` classes modulo each prime `p ∣ q`, `q`
squarefree,
`|S(0)|² ∏_{p ∣ q} ω(p)/(p - ω(p)) ≤ ∑_{(a, q) = 1} |S(a/q)|²` (`norm_expSum_zero_sq_mul_prod_le`).
For `q = p` prime this is Cauchy's inequality over the `p - ω(p)` classes that can be nonempty
(`norm_expSum_zero_sq_mul_le_prime`); for `q = p q'` it follows by applying the prime case to the
coefficients `c_n e(n b/q')` (`expSum_mul_exp`) and summing over `b`, since
`(a, b) ↦ a/p + b/q'` is a bijection onto the reduced fractions with denominator `p q'` modulo `1`
(`sum_reducedResidues_mul`). Summing over `q ≤ Q` and applying the Farey form (8) of the large
sieve (`large_sieve_farey`) to the indicator of `Z` gives the theorem
(`card_mul_montgomeryL_le`, `card_le_montgomery`).
-/

open Finset Real ComplexConjugate
open scoped ArithmeticFunction.Moebius

namespace NTKB.Davenport

/-- The exponential sum `S(x) = ∑_{n ∈ F} c_n e(n x)`. -/
noncomputable def expSum (F : Finset ℤ) (c : ℤ → ℂ) (x : ℝ) : ℂ :=
  ∑ n ∈ F, c n * Complex.exp (2 * π * Complex.I * (n * (x : ℂ)))

/-- The reduced residues `1 ≤ b ≤ q`, `(b, q) = 1` (the numerators of the Farey sum (8)). -/
def reducedResidues (q : ℕ) : Finset ℕ := (Icc 1 q).filter (fun b ↦ Nat.Coprime b q)

/-- `S(x)` has period `1`. -/
lemma expSum_add_intCast (F : Finset ℤ) (c : ℤ → ℂ) (x : ℝ) (k : ℤ) :
    expSum F c (x + k) = expSum F c x := by
  unfold expSum
  refine sum_congr rfl fun n _ ↦ ?_
  congr 1
  have h := Complex.exp_int_mul_two_pi_mul_I (n * k)
  push_cast at h ⊢
  rw [show 2 * (π : ℂ) * Complex.I * (n * (x + k)) = 2 * π * Complex.I * (n * x) +
    (n * k) * (2 * π * Complex.I) by ring, Complex.exp_add, h, mul_one]

/-- Twisting the coefficients shifts the argument: `∑ c_n e(nβ) e(nx) = S(x + β)`. -/
lemma expSum_mul_exp (F : Finset ℤ) (c : ℤ → ℂ) (β x : ℝ) :
    expSum F (fun n ↦ c n * Complex.exp (2 * π * Complex.I * (n * (β : ℂ)))) x =
      expSum F c (x + β) := by
  unfold expSum
  refine sum_congr rfl fun n _ ↦ ?_
  rw [mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast; ring



/-- `∑_{b < q} |S(b/q)|² = q ∑_{h < q} |∑_{n ≡ h} c_n|²`. -/
lemma sum_range_norm_expSum_sq {q : ℕ} (hq : 0 < q) (F : Finset ℤ) (c : ℤ → ℂ) :
    ∑ b ∈ range q, ‖expSum F c ((b : ℝ) / q)‖ ^ 2 =
      q * ∑ h ∈ range q, ‖∑ n ∈ F.filter (fun n ↦ n ≡ h [ZMOD q]), c n‖ ^ 2 := by
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
  apply Complex.ofReal_injective
  push_cast
  simp_rw [← Complex.mul_conj', expSum, map_sum, sum_mul_sum, map_mul]
  have h1 : ∀ (b : ℕ) (m n : ℤ), c m * Complex.exp (2 * ↑π * Complex.I * (↑m * (((b : ℝ) / q : ℝ) : ℂ))) *
      ((starRingEnd ℂ) (c n) * (starRingEnd ℂ) (Complex.exp (2 * ↑π * Complex.I * (↑n * (((b : ℝ) / q : ℝ) : ℂ))))) =
      (c m * conj (c n)) * Complex.exp (2 * π * Complex.I * (((m - n : ℤ) : ℂ) * (((b : ℝ) / q : ℝ) : ℂ))) := by
    intro b m n
    rw [← exp_mul_conj_exp]; ring
  simp_rw [h1]
  rw [sum_comm]
  refine (sum_congr rfl fun m _ ↦ sum_comm).trans ?_
  simp_rw [← mul_sum, sum_range_exp_eq hq]
  conv_lhs => rw [← sum_fiberwise_of_maps_to (g := key) (t := range q) (fun m _ ↦ hkey m)]
  rw [mul_sum]
  refine sum_congr rfl fun h hh ↦ ?_
  have hh := mem_range.1 hh
  have hfib : F.filter (fun m ↦ key m = h) = F.filter (fun n ↦ n ≡ h [ZMOD q]) :=
    filter_congr fun m _ ↦ (hmod m h hh).symm
  rw [hfib, mul_sum]
  refine sum_congr rfl fun m hm ↦ ?_
  have hm := (mem_filter.1 hm).2
  have : F.filter (fun n ↦ n ≡ h [ZMOD q]) = F.filter (fun n ↦ (q : ℤ) ∣ m - n) := by
    refine filter_congr fun n _ ↦ ?_
    rw [← Int.modEq_iff_dvd]
    exact ⟨fun h1 ↦ h1.trans hm.symm, fun h1 ↦ h1.trans hm⟩
  rw [this, sum_filter, mul_sum, mul_sum]
  refine sum_congr rfl fun n _ ↦ ?_
  split_ifs <;> simp [mul_comm]

lemma sum_eq_sum_filter_modEq {q : ℕ} (hq : 0 < q) (F : Finset ℤ) (f : ℤ → ℂ) :
    ∑ n ∈ F, f n = ∑ h ∈ range q, ∑ n ∈ F.filter (fun n ↦ n ≡ h [ZMOD q]), f n := by
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
  exact sum_congr (filter_congr fun m _ ↦ (hmod m h (mem_range.1 hh)).symm) fun _ _ ↦ rfl

lemma reducedResidues_prime {p : ℕ} (hp : p.Prime) : reducedResidues p = Ico 1 p := by
  ext b
  simp only [reducedResidues, mem_filter, mem_Icc, mem_Ico]
  rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨h1, lt_of_le_of_ne h2 ?_⟩
    rintro rfl; exact h3 dvd_rfl
  · rintro ⟨h1, h2⟩
    exact ⟨⟨h1, h2.le⟩, fun h ↦ absurd (Nat.le_of_dvd (by omega) h) (by omega)⟩

/-- **The prime case** (Montgomery): if `c_n = 0` whenever `n` lies in one of the classes
`h ∈ Ω` modulo the prime `p`, `|Ω| < p`, then
`|S(0)|² |Ω|/(p - |Ω|) ≤ ∑_{a=1}^{p-1} |S(a/p)|²`. -/
lemma norm_expSum_zero_sq_mul_le_prime {p : ℕ} (hp : p.Prime) (F : Finset ℤ) (c : ℤ → ℂ)
    (Ω : Finset ℕ) (hΩ : Ω ⊆ range p) (hΩp : Ω.card < p)
    (hc : ∀ n ∈ F, ∀ h ∈ Ω, n ≡ h [ZMOD p] → c n = 0) :
    ‖expSum F c 0‖ ^ 2 * ((Ω.card : ℝ) / ((p : ℝ) - Ω.card)) ≤
      ∑ b ∈ reducedResidues p, ‖expSum F c ((b : ℝ) / p)‖ ^ 2 := by
  have hp0 : 0 < p := hp.pos
  have hpr : (0 : ℝ) < p := by exact_mod_cast hp0
  have hd : (0 : ℝ) < (p : ℝ) - Ω.card := by
    have : (Ω.card : ℝ) < p := by exact_mod_cast hΩp
    linarith
  set T : ℕ → ℂ := fun h ↦ ∑ n ∈ F.filter (fun n ↦ n ≡ h [ZMOD p]), c n with hT
  set X : ℝ := ∑ h ∈ range p, ‖T h‖ ^ 2 with hX
  have hS0 : expSum F c 0 = ∑ h ∈ range p, T h := by
    simp only [expSum, Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one]
    exact sum_eq_sum_filter_modEq hp0 F c
  have hTΩ : ∀ h ∈ Ω, T h = 0 := by
    intro h hh
    refine sum_eq_zero fun n hn ↦ ?_
    have hn := mem_filter.1 hn
    exact hc n hn.1 h hh hn.2
  have hsplit : ∑ h ∈ range p, T h = ∑ h ∈ range p \ Ω, T h := by
    rw [← sum_sdiff hΩ, sum_eq_zero hTΩ, add_zero]
  have hcard : ((range p \ Ω).card : ℝ) = (p : ℝ) - Ω.card := by
    rw [card_sdiff_of_subset hΩ, card_range, Nat.cast_sub hΩp.le]
  have hCS : ‖expSum F c 0‖ ^ 2 ≤ ((p : ℝ) - Ω.card) * X := by
    rw [hS0, hsplit]
    calc ‖∑ h ∈ range p \ Ω, T h‖ ^ 2 ≤ (∑ h ∈ range p \ Ω, ‖T h‖) ^ 2 := by
          gcongr; exact norm_sum_le _ _
      _ ≤ ((range p \ Ω).card : ℝ) * ∑ h ∈ range p \ Ω, ‖T h‖ ^ 2 := by
          have := sq_sum_le_card_mul_sum_sq (s := range p \ Ω) (f := fun h ↦ ‖T h‖)
          simpa using this
      _ ≤ ((p : ℝ) - Ω.card) * X := by
          rw [hcard]
          gcongr
          exact sum_le_sum_of_subset_of_nonneg sdiff_subset fun _ _ _ ↦ by positivity
  have hall := sum_range_norm_expSum_sq hp0 F c
  have hR : ∑ b ∈ range p, ‖expSum F c ((b : ℝ) / p)‖ ^ 2 =
      ‖expSum F c 0‖ ^ 2 + ∑ b ∈ reducedResidues p, ‖expSum F c ((b : ℝ) / p)‖ ^ 2 := by
    rw [reducedResidues_prime hp, range_eq_Ico, sum_eq_sum_Ico_succ_bot hp0]
    simp
  have key : ‖expSum F c 0‖ ^ 2 * ((Ω.card : ℝ) / ((p : ℝ) - Ω.card)) =
      ‖expSum F c 0‖ ^ 2 * (p / ((p : ℝ) - Ω.card)) - ‖expSum F c 0‖ ^ 2 := by
    field_simp; ring
  rw [key]
  have : ‖expSum F c 0‖ ^ 2 * (p / ((p : ℝ) - Ω.card)) ≤ p * X := by
    rw [mul_div_assoc', div_le_iff₀ hd]
    nlinarith
  have h2 : (p : ℝ) * X = ∑ b ∈ range p, ‖expSum F c ((b : ℝ) / p)‖ ^ 2 := hall.symm
  linarith

lemma card_reducedResidues (q : ℕ) : (reducedResidues q).card = Nat.totient q := by
  rw [← Nat.filter_coprime_Ico_eq_totient q 1]
  unfold reducedResidues
  rw [add_comm 1 q]
  congr 1
  ext b; simp [Nat.coprime_comm]

/-- The CRT map. -/
def crtMap (m n a b : ℕ) : ℕ := (a * n + b * m - 1) % (m * n) + 1

lemma crtMap_spec {m n : ℕ} (hm : 0 < m) (hn : 0 < n) {a b : ℕ} (ha : 0 < a) :
    1 ≤ crtMap m n a b ∧ crtMap m n a b ≤ m * n ∧
      a * n + b * m = crtMap m n a b + m * n * ((a * n + b * m - 1) / (m * n)) ∧
      crtMap m n a b ≡ a * n + b * m [MOD m * n] := by
  have hmn : 0 < m * n := Nat.mul_pos hm hn
  have hs : 1 ≤ a * n + b * m := by
    have := Nat.mul_pos ha hn; omega
  have h1 := Nat.mod_lt (a * n + b * m - 1) hmn
  have h2 := Nat.div_add_mod (a * n + b * m - 1) (m * n)
  unfold crtMap
  refine ⟨by omega, by omega, by omega, ?_⟩
  have := (Nat.mod_modEq (a * n + b * m - 1) (m * n)).add_right 1
  rwa [Nat.sub_add_cancel hs] at this

lemma crtMap_mem {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) {a b : ℕ}
    (ha : a ∈ reducedResidues m) (hb : b ∈ reducedResidues n) :
    crtMap m n a b ∈ reducedResidues (m * n) := by
  simp only [reducedResidues, mem_filter, mem_Icc] at ha hb ⊢
  obtain ⟨h1, h2, -, h4⟩ := crtMap_spec hm hn (a := a) (b := b) (by omega)
  refine ⟨⟨h1, h2⟩, Nat.Coprime.mul_right ?_ ?_⟩
  · have e : crtMap m n a b ≡ a * n [MOD m] := by
      refine (h4.of_mul_right n).trans ?_
      unfold Nat.ModEq
      simp
    have hc : Nat.Coprime (a * n) m := Nat.Coprime.mul_left (show Nat.Coprime a m from ha.2) hmn.symm
    show Nat.gcd _ m = 1
    rw [e.gcd_eq]; exact hc
  · have e : crtMap m n a b ≡ b * m [MOD n] := by
      refine (h4.of_mul_left m).trans ?_
      unfold Nat.ModEq
      simp
    have hc : Nat.Coprime (b * m) n := Nat.Coprime.mul_left (show Nat.Coprime b n from hb.2) hmn
    show Nat.gcd _ n = 1
    rw [e.gcd_eq]; exact hc

lemma crtMap_inj {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) {a b a' b' : ℕ}
    (ha : a ∈ reducedResidues m) (hb : b ∈ reducedResidues n)
    (ha' : a' ∈ reducedResidues m) (hb' : b' ∈ reducedResidues n)
    (h : crtMap m n a b = crtMap m n a' b') : a = a' ∧ b = b' := by
  simp only [reducedResidues, mem_filter, mem_Icc] at ha hb ha' hb'
  obtain ⟨-, -, -, h4⟩ := crtMap_spec hm hn (a := a) (b := b) (by omega)
  obtain ⟨-, -, -, h4'⟩ := crtMap_spec hm hn (a := a') (b := b') (by omega)
  have hE : a * n + b * m ≡ a' * n + b' * m [MOD m * n] := h4.symm.trans (h ▸ h4')
  constructor
  · have e1 := hE.of_mul_right n
    have e2 : a * n ≡ a' * n [MOD m] := by
      have : a * n + b * m ≡ a * n [MOD m] := by
        unfold Nat.ModEq; simp
      have : a' * n + b' * m ≡ a' * n [MOD m] := by
        unfold Nat.ModEq; simp
      exact (by assumption : a * n + b * m ≡ a * n [MOD m]).symm.trans (e1.trans this)
    have e3 := Nat.ModEq.cancel_right_of_coprime hmn e2
    refine Nat.ModEq.eq_of_abs_lt e3 ?_
    rw [abs_lt]; constructor <;> omega
  · have e1 := hE.of_mul_left m
    have e2 : b * m ≡ b' * m [MOD n] := by
      have h5 : a * n + b * m ≡ b * m [MOD n] := by
        unfold Nat.ModEq; simp
      have h6 : a' * n + b' * m ≡ b' * m [MOD n] := by
        unfold Nat.ModEq; simp
      exact h5.symm.trans (e1.trans h6)
    have e3 := Nat.ModEq.cancel_right_of_coprime hmn.symm e2
    refine Nat.ModEq.eq_of_abs_lt e3 ?_
    rw [abs_lt]; constructor <;> omega

/-- **The Chinese remainder theorem for reduced fractions**: for coprime `m, n ≥ 1` and `f` of
period `1`, `∑_{(a, m) = 1} ∑_{(b, n) = 1} f(a/m + b/n) = ∑_{(r, mn) = 1} f(r/(mn))`. -/
lemma sum_reducedResidues_mul {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n)
    (f : ℝ → ℝ) (hf : Function.Periodic f 1) :
    ∑ a ∈ reducedResidues m, ∑ b ∈ reducedResidues n, f ((a : ℝ) / m + (b : ℝ) / n) =
      ∑ r ∈ reducedResidues (m * n), f ((r : ℝ) / (m * n : ℕ)) := by
  refine Eq.trans (sum_product' (reducedResidues m) (reducedResidues n)
    (fun a b ↦ f ((a : ℝ) / m + (b : ℝ) / n))).symm ?_
  have hinj : Set.InjOn (fun x : ℕ × ℕ ↦ crtMap m n x.1 x.2) ↑(reducedResidues m ×ˢ reducedResidues n) := by
    intro x hx y hy h
    simp only [coe_product, Set.mem_prod, mem_coe] at hx hy
    have := crtMap_inj hm hn hmn hx.1 hx.2 hy.1 hy.2 h
    exact Prod.ext this.1 this.2
  have hmaps : ∀ x ∈ reducedResidues m ×ˢ reducedResidues n,
      crtMap m n x.1 x.2 ∈ reducedResidues (m * n) := fun x hx ↦ by
    rw [mem_product] at hx
    exact crtMap_mem hm hn hmn hx.1 hx.2
  have himg : (reducedResidues m ×ˢ reducedResidues n).image (fun x : ℕ × ℕ ↦ crtMap m n x.1 x.2) =
      reducedResidues (m * n) := by
    refine eq_of_subset_of_card_le ?_ ?_
    · intro r hr
      obtain ⟨x, hx, rfl⟩ := mem_image.1 hr
      exact hmaps x hx
    · rw [card_image_of_injOn hinj, card_product, card_reducedResidues, card_reducedResidues,
        card_reducedResidues, Nat.totient_mul hmn]
  refine sum_bij (fun x _ ↦ crtMap m n x.1 x.2) hmaps hinj (fun r hr ↦ ?_) (fun x hx ↦ ?_)
  · rw [← himg] at hr
    obtain ⟨x, hx, rfl⟩ := mem_image.1 hr
    exact ⟨x, hx, rfl⟩
  · rw [mem_product] at hx
    have ha : 0 < x.1 := by
      have := hx.1; simp only [reducedResidues, mem_filter, mem_Icc] at this; omega
    obtain ⟨-, -, h3, -⟩ := crtMap_spec hm hn (a := x.1) (b := x.2) ha
    set k := (x.1 * n + x.2 * m - 1) / (m * n)
    have hm' : (0 : ℝ) < m := by exact_mod_cast hm
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have h3' : ((x.1 : ℝ) * n + x.2 * m) = crtMap m n x.1 x.2 + m * n * k := by exact_mod_cast h3
    have : (x.1 : ℝ) / m + (x.2 : ℝ) / n = (crtMap m n x.1 x.2 : ℝ) / ((m * n : ℕ) : ℝ) + k := by
      push_cast
      field_simp
      linarith
    rw [this]
    have := hf.nat_mul k
    simpa using this _

/-- **Montgomery's inequality**: for `q` squarefree and coefficients `c_n` vanishing on the classes
`Ω(p)` modulo each prime `p ∣ q` (`|Ω(p)| < p`),
`|S(0)|² ∏_{p ∣ q} |Ω(p)|/(p - |Ω(p)|) ≤ ∑_{(a, q) = 1} |S(a/q)|²`. -/
theorem norm_expSum_zero_sq_mul_prod_le {q : ℕ} (hq : Squarefree q) (F : Finset ℤ) (c : ℤ → ℂ)
    (Ω : ℕ → Finset ℕ) (hΩ : ∀ p ∈ q.primeFactors, Ω p ⊆ range p ∧ (Ω p).card < p)
    (hc : ∀ p ∈ q.primeFactors, ∀ n ∈ F, ∀ h ∈ Ω p, n ≡ h [ZMOD p] → c n = 0) :
    ‖expSum F c 0‖ ^ 2 * ∏ p ∈ q.primeFactors, (((Ω p).card : ℝ) / ((p : ℝ) - (Ω p).card)) ≤
      ∑ b ∈ reducedResidues q, ‖expSum F c ((b : ℝ) / q)‖ ^ 2 := by
  revert hq hΩ hc c
  induction q using Nat.strong_induction_on with
  | _ q ih =>
  intro hq c hΩ hc
  by_cases h1 : q = 1
  · subst h1
    have : reducedResidues 1 = {1} := by decide
    rw [this]
    simp only [Nat.primeFactors_one, prod_empty, mul_one, sum_singleton, Nat.cast_one, div_one]
    have e : expSum F c 0 = expSum F c 1 := by
      simpa using (expSum_add_intCast F c 0 1).symm
    exact le_of_eq (by rw [e])
  have h0 : q ≠ 0 := by rintro rfl; exact not_squarefree_zero hq
  obtain ⟨p, hp, hpq⟩ : ∃ p, p.Prime ∧ p ∣ q := ⟨_, Nat.minFac_prime h1, Nat.minFac_dvd q⟩
  obtain ⟨q', rfl⟩ := hpq
  have hp0 := hp.pos
  have hq'0 : 0 < q' := Nat.pos_of_ne_zero (by rintro rfl; simp at h0)
  have hcop : Nat.Coprime p q' := Nat.coprime_of_squarefree_mul hq
  have hsq' : Squarefree q' := hq.of_mul_right
  have hlt : q' < p * q' := by
    have := hp.two_le; nlinarith
  have hpf : (p * q').primeFactors = insert p q'.primeFactors := by
    rw [Nat.Coprime.primeFactors_mul hcop, hp.primeFactors]; rfl
  have hpn : p ∉ q'.primeFactors := by
    intro h
    have := (Nat.mem_primeFactors.1 h).2.1
    exact hp.one_lt.ne' (Nat.eq_one_of_dvd_coprimes hcop dvd_rfl this)
  have hsub : q'.primeFactors ⊆ (p * q').primeFactors := by
    rw [hpf]; exact subset_insert _ _
  have hpm : p ∈ (p * q').primeFactors := by rw [hpf]; exact mem_insert_self _ _
  have ih' := ih q' hlt hsq' c (fun r hr ↦ hΩ r (hsub hr)) (fun r hr ↦ hc r (hsub hr))
  rw [hpf, prod_insert hpn]
  set w : ℝ := ((Ω p).card : ℝ) / ((p : ℝ) - (Ω p).card) with hw
  have hw0 : 0 ≤ w := by
    have := (hΩ p hpm).2
    have h2 : (Ω p).card < p := this
    have : (Ω p).card ≤ p := h2.le
    have : ((Ω p).card : ℝ) ≤ p := by exact_mod_cast this
    exact div_nonneg (by positivity) (by linarith)
  set P' := ∏ r ∈ q'.primeFactors, (((Ω r).card : ℝ) / ((r : ℝ) - (Ω r).card)) with hP'
  have hper : Function.Periodic (fun x : ℝ ↦ ‖expSum F c x‖ ^ 2) 1 := by
    intro x
    have := expSum_add_intCast F c x 1
    push_cast at this
    show ‖expSum F c (x + 1)‖ ^ 2 = ‖expSum F c x‖ ^ 2
    rw [this]
  have hrhs := sum_reducedResidues_mul hp0 hq'0 hcop (fun x : ℝ ↦ ‖expSum F c x‖ ^ 2) hper
  rw [← hrhs]
  have hstep : ∀ b ∈ reducedResidues q', w * ‖expSum F c ((b : ℝ) / q')‖ ^ 2 ≤
      ∑ a ∈ reducedResidues p, ‖expSum F c ((a : ℝ) / p + (b : ℝ) / q')‖ ^ 2 := by
    intro b _
    have := norm_expSum_zero_sq_mul_le_prime hp F
      (fun n ↦ c n * Complex.exp (2 * π * Complex.I * (n * (((b : ℝ) / q' : ℝ) : ℂ))))
      (Ω p) (hΩ p hpm).1 (hΩ p hpm).2
      (fun n hn h hh hnh ↦ by rw [hc p hpm n hn h hh hnh, zero_mul])
    simp only [expSum_mul_exp, zero_add] at this
    linarith
  calc ‖expSum F c 0‖ ^ 2 * (w * P') = w * (‖expSum F c 0‖ ^ 2 * P') := by ring
    _ ≤ w * ∑ b ∈ reducedResidues q', ‖expSum F c ((b : ℝ) / q')‖ ^ 2 := by gcongr
    _ = ∑ b ∈ reducedResidues q', w * ‖expSum F c ((b : ℝ) / q')‖ ^ 2 := by rw [mul_sum]
    _ ≤ ∑ b ∈ reducedResidues q', ∑ a ∈ reducedResidues p,
          ‖expSum F c ((a : ℝ) / p + (b : ℝ) / q')‖ ^ 2 := sum_le_sum hstep
    _ = _ := sum_comm

/-- `ω(p)`: the number of residue classes `h` modulo `p` that contain no element of `Z`. -/
def sieveOmega (Z : Finset ℤ) (p : ℕ) : ℕ :=
  ((range p).filter (fun h : ℕ ↦ (Z.filter (fun n ↦ n ≡ h [ZMOD p])).card = 0)).card

/-- Montgomery's `L = ∑_{q ≤ Q} μ(q)² ∏_{p ∣ q} ω(p)/(p - ω(p))`. -/
noncomputable def montgomeryL (Z : Finset ℤ) (Q : ℝ) : ℝ :=
  ∑ q ∈ Icc 1 ⌊Q⌋₊, ((μ q : ℤ) : ℝ) ^ 2 *
    ∏ p ∈ q.primeFactors, ((sieveOmega Z p : ℝ) / ((p : ℝ) - sieveOmega Z p))

lemma sieveOmega_le (Z : Finset ℤ) (p : ℕ) : sieveOmega Z p ≤ p := by
  unfold sieveOmega
  exact (card_filter_le _ _).trans (by simp)

lemma montgomeryL_term_nonneg (Z : Finset ℤ) (q : ℕ) :
    0 ≤ ((μ q : ℤ) : ℝ) ^ 2 *
      ∏ p ∈ q.primeFactors, ((sieveOmega Z p : ℝ) / ((p : ℝ) - sieveOmega Z p)) := by
  refine mul_nonneg (sq_nonneg _) (prod_nonneg fun p _ ↦ ?_)
  have : (sieveOmega Z p : ℝ) ≤ p := by exact_mod_cast sieveOmega_le Z p
  exact div_nonneg (by positivity) (by linarith)

/-- `L ≥ 1` (the term `q = 1`; every term is nonnegative). -/
lemma one_le_montgomeryL (Z : Finset ℤ) {Q : ℝ} (hQ : 1 ≤ Q) : 1 ≤ montgomeryL Z Q := by
  have h1 : 1 ∈ Icc 1 ⌊Q⌋₊ := by
    simp only [mem_Icc, le_refl, true_and]
    exact Nat.le_floor (by exact_mod_cast hQ)
  have := single_le_sum (f := fun q : ℕ ↦ ((μ q : ℤ) : ℝ) ^ 2 *
    ∏ p ∈ q.primeFactors, ((sieveOmega Z p : ℝ) / ((p : ℝ) - sieveOmega Z p)))
    (fun q _ ↦ montgomeryL_term_nonneg Z q) h1
  simpa [montgomeryL] using this

/-- **Montgomery's large sieve (Davenport, Ch. 27, p. 159)**, multiplied out: for a set `Z` of
integers in `(M, M + N]` and real `Q ≥ 1`, `|Z| L ≤ N + 3Q²`. -/
@[kb "davenport1980" "Ch 27, p. 159"]
theorem card_mul_montgomeryL_le {Q : ℝ} (hQ : 1 ≤ Q) (M : ℤ) (N : ℕ) (Z : Finset ℤ)
    (hZ : Z ⊆ Ioc M (M + N)) :
    (Z.card : ℝ) * montgomeryL Z Q ≤ N + 3 * Q ^ 2 := by
  classical
  rcases Z.eq_empty_or_nonempty with rfl | hne
  · simp only [card_empty, Nat.cast_zero, zero_mul]; positivity
  have hZpos : (0 : ℝ) < Z.card := by exact_mod_cast hne.card_pos
  set c : ℤ → ℂ := fun n ↦ if n ∈ Z then 1 else 0
  set F : Finset ℤ := Ioc M (M + N)
  have hS : ∀ x : ℝ, ∑ n ∈ Z, Complex.exp (2 * π * Complex.I * (n * (x : ℂ))) =
      expSum F c x := by
    intro x
    unfold expSum
    rw [← sum_subset hZ (fun n _ hn ↦ by simp [c, hn])]
    refine sum_congr rfl fun n hn ↦ ?_
    simp [c, hn]
  have hc2 : ∑ n ∈ F, ‖c n‖ ^ 2 = Z.card := by
    rw [← sum_subset hZ (fun n _ hn ↦ by simp [c, hn])]
    rw [card_eq_sum_ones, Nat.cast_sum]
    refine sum_congr rfl fun n hn ↦ ?_
    simp [c, hn]
  have hS0 : ‖expSum F c 0‖ ^ 2 = (Z.card : ℝ) ^ 2 := by
    rw [← hS]; simp
  set Ω : ℕ → Finset ℕ := fun p ↦
    (range p).filter (fun h : ℕ ↦ (Z.filter (fun n ↦ n ≡ h [ZMOD p])).card = 0) with hΩdef
  have hΩ : ∀ p : ℕ, 0 < p → Ω p ⊆ range p ∧ (Ω p).card < p := by
    intro p hp
    refine ⟨filter_subset _ _, ?_⟩
    obtain ⟨z, hz⟩ := hne
    have hp' : (0 : ℤ) < p := by exact_mod_cast hp
    have hlt : (z % (p : ℤ)).toNat < p := by
      have := Int.emod_lt_of_pos z hp'; have := Int.emod_nonneg z hp'.ne'; omega
    have hnot : (z % (p : ℤ)).toNat ∉ Ω p := by
      simp only [hΩdef, mem_filter, not_and]
      intro _ h0
      have hzmem : z ∈ Z.filter (fun n ↦ n ≡ ((z % (p : ℤ)).toNat : ℕ) [ZMOD p]) := by
        refine mem_filter.2 ⟨hz, ?_⟩
        have := Int.emod_nonneg z hp'.ne'
        simp only [Int.ModEq]
        rw [Int.toNat_of_nonneg this, Int.emod_emod_of_dvd _ dvd_rfl]
      rw [card_eq_zero] at h0
      rw [h0] at hzmem
      exact notMem_empty _ hzmem
    have := card_lt_card (ssubset_iff_of_subset (filter_subset _ (range p)) |>.2
      ⟨_, mem_range.2 hlt, hnot⟩)
    rw [card_range] at this
    exact this
  have hcz : ∀ p : ℕ, ∀ n ∈ F, ∀ h ∈ Ω p, n ≡ h [ZMOD p] → c n = 0 := by
    intro p n hn h hh hnh
    simp only [hΩdef, mem_filter] at hh
    by_contra hne0
    have hnZ : n ∈ Z := by
      by_contra hnZ; exact hne0 (by simp [c, hnZ])
    have : n ∈ Z.filter (fun n ↦ n ≡ h [ZMOD p]) := mem_filter.2 ⟨hnZ, hnh⟩
    rw [card_eq_zero] at hh
    simp [hh.2] at this
  have h8 := large_sieve_farey hQ M N c
  rw [hc2] at h8
  have hterm : ∀ q ∈ Icc 1 ⌊Q⌋₊, ((μ q : ℤ) : ℝ) ^ 2 *
      (‖expSum F c 0‖ ^ 2 * ∏ p ∈ q.primeFactors, ((sieveOmega Z p : ℝ) / ((p : ℝ) - sieveOmega Z p))) ≤
      ∑ b ∈ (Icc 1 q).filter (fun b ↦ Nat.Coprime b q),
        ‖∑ n ∈ Ioc M (M + N), c n *
          Complex.exp (2 * π * Complex.I * (n * (((b : ℝ) / q : ℝ) : ℂ)))‖ ^ 2 := by
    intro q hq
    have hq1 : 0 < q := (mem_Icc.1 hq).1
    by_cases hsf : Squarefree q
    · have hmu : ((μ q : ℤ) : ℝ) ^ 2 = 1 := by
        have := ArithmeticFunction.moebius_sq_eq_one_of_squarefree hsf
        exact_mod_cast this
      rw [hmu, one_mul]
      exact norm_expSum_zero_sq_mul_prod_le hsf F c Ω
        (fun p hp ↦ hΩ p (Nat.pos_of_mem_primeFactors hp))
        (fun p _ ↦ hcz p)
    · have : μ q = 0 := ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsf
      rw [this]
      simp only [Int.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul]
      exact sum_nonneg fun _ _ ↦ by positivity
  have hmain : (Z.card : ℝ) ^ 2 * montgomeryL Z Q ≤ (N + 3 * Q ^ 2) * Z.card := by
    refine le_trans ?_ h8
    refine le_trans (le_of_eq ?_) (sum_le_sum hterm)
    rw [hS0, montgomeryL, mul_sum]
    refine sum_congr rfl fun q _ ↦ ?_
    ring
  have : (Z.card : ℝ) * ((Z.card : ℝ) * montgomeryL Z Q) ≤ (Z.card : ℝ) * (N + 3 * Q ^ 2) := by
    nlinarith
  exact le_of_mul_le_mul_left this hZpos

/-- **Montgomery's large sieve (Davenport, Ch. 27, p. 159)**: for a set `Z` of integers in
`(M, M + N]` and real `Q ≥ 1`, `|Z| ≤ (N + 3Q²)/L`,
`L = ∑_{q ≤ Q} μ(q)² ∏_{p ∣ q} ω(p)/(p - ω(p))`, `ω(p)` the number of classes modulo `p` that
contain no element of `Z`. -/
@[kb "davenport1980" "Ch 27, p. 159"]
theorem card_le_montgomery {Q : ℝ} (hQ : 1 ≤ Q) (M : ℤ) (N : ℕ) (Z : Finset ℤ)
    (hZ : Z ⊆ Ioc M (M + N)) :
    (Z.card : ℝ) ≤ (N + 3 * Q ^ 2) / montgomeryL Z Q := by
  have h1 := one_le_montgomeryL Z hQ
  rw [le_div_iff₀ (by linarith)]
  exact card_mul_montgomeryL_le hQ M N Z hZ

end NTKB.Davenport
