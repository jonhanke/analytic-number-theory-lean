/-
Ireland–Rosen, Chapter 11, §3 and §4: the Hasse–Davenport relation `(-g(χ))^s = -g(χ')`
(Theorem 1 of §11.3), with Monsky's proof from §11.4.

Let `F` be a finite field with `q` elements, `E ⊇ F` a field with `q^s` elements, `χ` a
multiplicative and `ψ` a nontrivial additive character of `F`, `χ' = χ ∘ N_{E/F}` and
`ψ' = ψ ∘ tr_{E/F}`. For a monic `f = x^n - c_1 x^{n-1} + ⋯ + (-1)^n c_n ∈ F[x]` put
`λ(f) = ψ(c_1) χ(c_n)` (Lemma 1: `λ` is multiplicative).

The book takes the logarithmic derivative of the Euler product `∑_f λ(f) t^{deg f} = ∏_f
(1 - λ(f) t^{deg f})^{-1}` (identity (7)). We use the equivalent finite identity obtained by
comparing coefficients: with `a_n = ∑_{deg f = n} λ(f)` and
`c_n = ∑_{d ∣ n} ∑_{deg P = d, P irreducible} d λ(P)^{n/d}`,
`n a_n = ∑_{k=1}^n c_k a_{n-k}` (`hdNewton`), which follows from unique factorization
(`deg f = ∑_{P^j ∣ f} deg P`) and the multiplicativity of `λ`. Since `a_0 = 1`, `a_1 = g(χ)` and
`a_n = 0` for `n ≥ 2`, this gives `c_s = (-1)^{s-1} g(χ)^s`, and Lemma 3 identifies `c_s` with
`g(χ')`.
-/
import Mathlib.NumberTheory.GaussSum
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.RingTheory.Norm.Basic
import Mathlib.RingTheory.Trace.Basic
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import NTKB.Attr

open Polynomial Finset
open scoped Classical IntermediateField

set_option linter.unusedSectionVars false

namespace NTKB.IrelandRosen

section Lambda

variable {F : Type*} [Field F] [Fintype F] {R : Type*} [CommRing R]
variable (χ : MulChar F R) (ψ : AddChar F R)

/-- `λ(f) = ψ(c_1) χ(c_n)` for `f = x^n - c_1 x^{n-1} + ⋯ + (-1)^n c_n` (Ireland–Rosen §11.4). -/
noncomputable def hdLambda (f : F[X]) : R :=
  ψ (-f.nextCoeff) * χ ((-1) ^ f.natDegree * f.coeff 0)

/-- **Lemma 1 (§11.4).** `λ(fg) = λ(f) λ(g)` for monic `f, g`. -/
@[kb "irelandrosen1990" "Lemma 1 (§11.4), p. 175"]
theorem hdLambda_mul {f g : F[X]} (hf : f.Monic) (hg : g.Monic) :
    hdLambda χ ψ (f * g) = hdLambda χ ψ f * hdLambda χ ψ g := by
  unfold hdLambda
  rw [hf.nextCoeff_mul hg, hf.natDegree_mul hg, mul_coeff_zero, neg_add, AddChar.map_add_eq_mul,
    pow_add, show (-1 : F) ^ f.natDegree * (-1) ^ g.natDegree * (f.coeff 0 * g.coeff 0) =
      ((-1) ^ f.natDegree * f.coeff 0) * ((-1) ^ g.natDegree * g.coeff 0) by ring, map_mul]
  ring

lemma hdLambda_one : hdLambda χ ψ (1 : F[X]) = 1 := by
  simp [hdLambda, nextCoeff]

lemma hdLambda_pow {f : F[X]} (hf : f.Monic) (k : ℕ) :
    hdLambda χ ψ (f ^ k) = hdLambda χ ψ f ^ k := by
  induction k with
  | zero => simp [hdLambda_one]
  | succ k ih => rw [pow_succ, hdLambda_mul χ ψ (hf.pow k) hf, ih, pow_succ]

/-! ### Monic polynomials of a given degree -/

/-- `x^n + c_{n-1} x^{n-1} + ⋯ + c_0`. -/
noncomputable def monicOfCoeffs {n : ℕ} (c : Fin n → F) : F[X] :=
  X ^ n + ∑ i : Fin n, C (c i) * X ^ (i : ℕ)

omit [Fintype F] in
lemma monicOfCoeffs_monic {n : ℕ} (c : Fin n → F) : (monicOfCoeffs c).Monic :=
  monic_X_pow_add (degree_sum_fin_lt c)

omit [Fintype F] in
lemma natDegree_monicOfCoeffs {n : ℕ} (c : Fin n → F) : (monicOfCoeffs c).natDegree = n := by
  unfold monicOfCoeffs
  rw [natDegree_add_eq_left_of_degree_lt] <;> simp only [natDegree_X_pow, degree_X_pow]
  exact degree_sum_fin_lt c

omit [Fintype F] in
lemma coeff_monicOfCoeffs {n : ℕ} (c : Fin n → F) (i : Fin n) :
    (monicOfCoeffs c).coeff i = c i := by
  unfold monicOfCoeffs
  rw [coeff_add, coeff_X_pow, if_neg (Nat.ne_of_lt i.isLt), zero_add, finsetSum_coeff]
  simp_rw [coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj; rw [if_neg]; exact fun h => hj (Fin.ext h).symm
  · simp

omit [Fintype F] in
lemma monicOfCoeffs_injective {n : ℕ} : Function.Injective (monicOfCoeffs (F := F) (n := n)) := by
  intro c d h
  funext i
  rw [← coeff_monicOfCoeffs c i, ← coeff_monicOfCoeffs d i, h]

omit [Fintype F] in
lemma eq_monicOfCoeffs {f : F[X]} (hf : f.Monic) :
    f = monicOfCoeffs (fun i : Fin f.natDegree => f.coeff i) := by
  conv_lhs => rw [hf.as_sum]
  rw [monicOfCoeffs, Fin.sum_univ_eq_sum_range (fun i => C (f.coeff i) * X ^ i)]

variable (F) in
/-- The monic polynomials of degree `n`. -/
noncomputable def monicDeg (n : ℕ) : Finset F[X] := univ.image (monicOfCoeffs (F := F) (n := n))

lemma mem_monicDeg {n : ℕ} {f : F[X]} : f ∈ monicDeg F n ↔ f.Monic ∧ f.natDegree = n := by
  simp only [monicDeg, mem_image, mem_univ, true_and]
  constructor
  · rintro ⟨c, rfl⟩; exact ⟨monicOfCoeffs_monic c, natDegree_monicOfCoeffs c⟩
  · rintro ⟨hf, rfl⟩; exact ⟨_, (eq_monicOfCoeffs hf).symm⟩

lemma sum_monicDeg {M : Type*} [AddCommMonoid M] (n : ℕ) (G : F[X] → M) :
    ∑ f ∈ monicDeg F n, G f = ∑ c : Fin n → F, G (monicOfCoeffs c) :=
  sum_image fun c _ d _ h => monicOfCoeffs_injective h

/-- `a_n = ∑_{f monic, deg f = n} λ(f)`. -/
noncomputable def hdA (n : ℕ) : R := ∑ f ∈ monicDeg F n, hdLambda χ ψ f

lemma hdA_zero : hdA χ ψ 0 = 1 := by
  rw [hdA, sum_monicDeg]
  simp [monicOfCoeffs, hdLambda_one]

lemma hdA_one : hdA χ ψ 1 = gaussSum χ ψ := by
  rw [hdA, sum_monicDeg, gaussSum]
  rw [← (Equiv.funUnique (Fin 1) F).symm.sum_comp]
  rw [← Equiv.sum_comp (Equiv.neg F)]
  refine Finset.sum_congr rfl fun x _ => ?_
  have hm : monicOfCoeffs ((Equiv.funUnique (Fin 1) F).symm ((Equiv.neg F) x)) = X + C (-x) := by
    simp [monicOfCoeffs]
  rw [hm, hdLambda]
  have hnd : (X + C (-x)).natDegree = 1 := natDegree_X_add_C _
  rw [hnd, nextCoeff_of_natDegree_pos (by rw [hnd]; norm_num), hnd]
  simp [coeff_X, coeff_C]
  ring

lemma hdA_eq_zero [IsDomain R] (hψ : ψ ≠ 1) {n : ℕ} (hn : 2 ≤ n) : hdA χ ψ n = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [hdA, sum_monicDeg]
  have hterm : ∀ c : Fin (m + 2) → F, hdLambda χ ψ (monicOfCoeffs c) =
      ψ (-c (Fin.last _)) * χ ((-1) ^ (m + 2) * c 0) := by
    intro c
    rw [hdLambda, natDegree_monicOfCoeffs,
      nextCoeff_of_natDegree_pos (by rw [natDegree_monicOfCoeffs]; omega),
      natDegree_monicOfCoeffs]
    have h1 := coeff_monicOfCoeffs c (Fin.last _)
    have h0 := coeff_monicOfCoeffs c 0
    simp only [Fin.val_last, Fin.val_zero] at h1 h0
    rw [show m + 2 - 1 = m + 1 by omega, h1, h0]
  simp_rw [hterm]
  rw [← (Fin.snocEquiv fun _ : Fin (m + 2) => F).sum_comp, Fintype.sum_prod_type]
  simp only [Fin.snocEquiv_apply, Fin.snoc_last]
  have h0 : ∀ (x : F) (c : Fin (m + 1) → F), Fin.snoc (α := fun _ => F) c x 0 = c 0 := by
    intro x c
    exact Fin.snoc_castSucc (α := fun _ => F) (i := 0) ..
  simp_rw [h0, ← Finset.mul_sum, ← Finset.sum_mul]
  rw [show ∑ x : F, ψ (-x) = 0 from
    (Equiv.sum_comp (Equiv.neg F) (fun x => ψ x)).trans (AddChar.sum_eq_zero_of_ne_one hψ),
    zero_mul]

/-! ### Irreducible polynomials and the finite form of identity (7) -/

variable (F) in
/-- The monic irreducible polynomials of degree `d`. -/
noncomputable def irrDeg (d : ℕ) : Finset F[X] := {f ∈ monicDeg F d | Irreducible f}

lemma mem_irrDeg {d : ℕ} {f : F[X]} :
    f ∈ irrDeg F d ↔ f.Monic ∧ f.natDegree = d ∧ Irreducible f := by
  simp [irrDeg, mem_monicDeg, and_assoc]

/-- `c_k = ∑_{d ∣ k} ∑_{P monic irreducible of degree d} d λ(P)^{k/d}`. -/
noncomputable def hdC (k : ℕ) : R :=
  ∑ d ∈ k.divisors, ∑ P ∈ irrDeg F d, (d : R) * hdLambda χ ψ P ^ (k / d)

/-- `deg f = ∑_{P^j ∣ f} deg P` for monic `f` of degree `n`, the sum over monic irreducible `P`
of degree `d ≤ n` and `1 ≤ j ≤ n`. -/
lemma natDegree_eq_sum_dvd {n : ℕ} {f : F[X]} (hf : f.Monic) (hfn : f.natDegree = n) :
    (n : R) = ∑ d ∈ Icc 1 n, ∑ P ∈ irrDeg F d, ∑ j ∈ Icc 1 n,
      if P ^ j ∣ f then (d : R) else 0 := by
  have hf0 : f ≠ 0 := hf.ne_zero
  set nf := UniqueFactorizationMonoid.normalizedFactors f with hnf
  have hmon : ∀ P ∈ nf, P.Monic := by
    intro P hP
    have := UniqueFactorizationMonoid.normalize_normalized_factor P hP
    rw [← this]
    exact monic_normalize (UniqueFactorizationMonoid.irreducible_of_normalized_factor P hP).ne_zero
  have hpm : nf.prod.Monic := by
    have := monic_multiset_prod_of_monic nf id hmon
    rwa [Multiset.map_id] at this
  have hprod : nf.prod = f :=
    eq_of_monic_of_associated hpm hf (UniqueFactorizationMonoid.prod_normalizedFactors hf0)
  have hdeg : n = (nf.map natDegree).sum := by
    rw [← hfn, ← hprod, natDegree_multiset_prod_of_monic _ hmon]
  -- the number of `j ∈ [1, n]` with `P^j ∣ f` is the multiplicity of `P` in `f`
  have hcount : ∀ P : F[X], P.Monic → Irreducible P →
      #{j ∈ Icc 1 n | P ^ j ∣ f} = nf.count P := by
    intro P hPm hPi
    have hle : ∀ j, P ^ j ∣ f ↔ j ≤ nf.count P := by
      intro j
      rw [pow_dvd_iff_le_emultiplicity,
        UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors hPi hf0,
        hPm.normalize_eq_self]
      exact_mod_cast Iff.rfl
    have hcn : nf.count P ≤ n := by
      have h1 : P ^ nf.count P ∣ f := (hle _).mpr le_rfl
      have h2 := natDegree_le_of_dvd h1 hf0
      rw [hPm.natDegree_pow, hfn] at h2
      have h3 : 1 ≤ P.natDegree := hPi.natDegree_pos
      nlinarith
    have : ({j ∈ Icc 1 n | P ^ j ∣ f} : Finset ℕ) = Icc 1 (nf.count P) := by
      ext j; simp only [mem_filter, mem_Icc, hle]; omega
    rw [this, Nat.card_Icc, Nat.add_sub_cancel]
  -- rewrite the right side as a sum over the irreducible factors
  have hrhs : ∑ d ∈ Icc 1 n, ∑ P ∈ irrDeg F d, ∑ j ∈ Icc 1 n,
      (if P ^ j ∣ f then (d : R) else 0) =
      ∑ P ∈ (Icc 1 n).biUnion (irrDeg F), ((nf.count P * P.natDegree : ℕ) : R) := by
    rw [Finset.sum_biUnion]
    · refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun P hP => ?_
      obtain ⟨hPm, hPd, hPi⟩ := mem_irrDeg.mp hP
      rw [← Finset.sum_filter, sum_const, hcount P hPm hPi, hPd, nsmul_eq_mul]
      push_cast; ring
    · intro d _ d' _ hdd'
      simp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro P hP hP'
      exact hdd' ((mem_irrDeg.mp hP).2.1.symm.trans (mem_irrDeg.mp hP').2.1)
  rw [hrhs]
  conv_lhs => rw [hdeg, Finset.sum_multiset_map_count]
  push_cast
  rw [Finset.sum_subset (s₁ := nf.toFinset)]
  · refine Finset.sum_congr rfl fun P _ => ?_
    simp [nsmul_eq_mul]
  · intro P hP
    rw [Multiset.mem_toFinset] at hP
    rw [Finset.mem_biUnion]
    have hPi := UniqueFactorizationMonoid.irreducible_of_normalized_factor P hP
    refine ⟨P.natDegree, ?_, mem_irrDeg.mpr ⟨hmon P hP, rfl, hPi⟩⟩
    rw [mem_Icc]
    refine ⟨hPi.natDegree_pos, ?_⟩
    rw [hdeg]
    exact Multiset.le_sum_of_mem (Multiset.mem_map_of_mem _ hP)
  · intro P _ hP
    rw [Multiset.mem_toFinset, ← Multiset.count_eq_zero] at hP
    simp [hP]

/-- For `P` monic irreducible of degree `d ≥ 1` and `j d ≤ n`:
`∑_{f monic, deg f = n, P^j ∣ f} λ(f) = λ(P)^j a_{n - jd}`. -/
lemma sum_monicDeg_dvd {n d j : ℕ} {P : F[X]} (hP : P ∈ irrDeg F d) :
    ∑ f ∈ monicDeg F n, (if P ^ j ∣ f then hdLambda χ ψ f else 0) =
      if j * d ≤ n then hdLambda χ ψ P ^ j * hdA χ ψ (n - j * d) else 0 := by
  obtain ⟨hPm, hPd, hPi⟩ := mem_irrDeg.mp hP
  rw [← Finset.sum_filter]
  split_ifs with hjd
  · rw [hdA, Finset.mul_sum]
    symm
    refine Finset.sum_nbij' (fun g => P ^ j * g) (fun f => f /ₘ (P ^ j)) ?_ ?_ ?_ ?_ ?_
    · intro g hg
      obtain ⟨hgm, hgd⟩ := mem_monicDeg.mp hg
      simp only [mem_filter, mem_monicDeg]
      refine ⟨⟨(hPm.pow j).mul hgm, ?_⟩, dvd_mul_right _ _⟩
      rw [(hPm.pow j).natDegree_mul hgm, hPm.natDegree_pow, hgd, hPd]; omega
    · intro f hf
      simp only [mem_coe, mem_filter, mem_monicDeg] at hf
      obtain ⟨⟨hfm, hfd⟩, hdvd⟩ := hf
      have hpj := hPm.pow j
      have heq : P ^ j * (f /ₘ P ^ j) = f := by
        have := modByMonic_add_div f (P ^ j)
        rw [(modByMonic_eq_zero_iff_dvd hpj).mpr hdvd, zero_add] at this
        exact this
      have hqm : (f /ₘ P ^ j).Monic := by
        have := hfm
        rw [← heq] at this
        exact hpj.of_mul_monic_left this
      simp only [mem_coe, mem_monicDeg]
      refine ⟨hqm, ?_⟩
      have := congrArg natDegree heq
      rw [hpj.natDegree_mul hqm, hPm.natDegree_pow, hPd, hfd] at this
      omega
    · intro g _
      exact mul_divByMonic_cancel_left g (hPm.pow j)
    · intro f hf
      simp only [mem_coe, mem_filter] at hf
      have hpj := hPm.pow j
      have := modByMonic_add_div f (P ^ j)
      rw [(modByMonic_eq_zero_iff_dvd hpj).mpr hf.2, zero_add] at this
      exact this
    · intro g hg
      obtain ⟨hgm, _⟩ := mem_monicDeg.mp hg
      rw [hdLambda_mul χ ψ (hPm.pow j) hgm, hdLambda_pow χ ψ hPm]
  · refine Finset.sum_eq_zero fun f hf => ?_
    exfalso
    simp only [mem_filter, mem_monicDeg] at hf
    obtain ⟨⟨hfm, hfd⟩, hdvd⟩ := hf
    have := natDegree_le_of_dvd hdvd hfm.ne_zero
    rw [hPm.natDegree_pow, hPd, hfd] at this
    exact hjd this

/-- The divisor-sum reindexing `∑_{k=1}^n ∑_{d ∣ k} G(d, k/d) = ∑_{d=1}^n ∑_{j=1}^n [jd ≤ n] G(d, j)`. -/
lemma sum_divisors_reindex {M : Type*} [AddCommMonoid M] (n : ℕ) (G : ℕ → ℕ → M) :
    ∑ k ∈ Icc 1 n, ∑ d ∈ k.divisors, G d (k / d) =
      ∑ d ∈ Icc 1 n, ∑ j ∈ Icc 1 n, if j * d ≤ n then G d j else 0 := by
  rw [Finset.sum_comm' (t' := Icc 1 n) (s' := fun d => {k ∈ Icc 1 n | d ∣ k})]
  · refine Finset.sum_congr rfl fun d hd => ?_
    simp only [mem_Icc] at hd
    rw [← Finset.sum_filter]
    symm
    refine Finset.sum_nbij' (fun j => j * d) (fun k => k / d) ?_ ?_ ?_ ?_ ?_
    · intro j hj
      simp only [mem_filter, mem_Icc] at hj ⊢
      exact ⟨⟨by nlinarith, hj.2⟩, dvd_mul_left _ _⟩
    · intro k hk
      simp only [mem_coe, mem_filter, mem_Icc] at hk ⊢
      obtain ⟨⟨hk1, hkn⟩, ⟨m, rfl⟩⟩ := hk
      have hd0 : 0 < d := by omega
      rw [Nat.mul_div_cancel_left _ hd0]
      refine ⟨⟨?_, ?_⟩, by rw [mul_comm]; exact hkn⟩
      · rcases m with _ | m
        · simp at hk1
        · omega
      · nlinarith
    · intro j _; exact Nat.mul_div_cancel _ (by omega)
    · intro k hk
      simp only [mem_coe, mem_filter] at hk
      exact Nat.div_mul_cancel hk.2
    · intro j _; rw [Nat.mul_div_cancel _ (by omega)]
  · intro k d
    simp only [mem_Icc, Nat.mem_divisors, mem_filter]
    constructor
    · rintro ⟨⟨hk1, hkn⟩, hdk, -⟩
      have h1 := Nat.le_of_dvd (by omega) hdk
      have h2 : 1 ≤ d := Nat.pos_of_dvd_of_pos hdk (by omega)
      exact ⟨⟨⟨hk1, hkn⟩, hdk⟩, h2, by omega⟩
    · rintro ⟨⟨⟨hk1, hkn⟩, hdk⟩, -, -⟩
      exact ⟨⟨hk1, hkn⟩, hdk, by omega⟩

/-- **The finite form of identity (7)**: `n a_n = ∑_{k=1}^n c_k a_{n-k}`. -/
theorem hdNewton (n : ℕ) :
    (n : R) * hdA χ ψ n = ∑ k ∈ Icc 1 n, hdC χ ψ k * hdA χ ψ (n - k) := by
  -- left side
  have hL : (n : R) * hdA χ ψ n = ∑ d ∈ Icc 1 n, ∑ P ∈ irrDeg F d, ∑ j ∈ Icc 1 n,
      (d : R) * ∑ f ∈ monicDeg F n, (if P ^ j ∣ f then hdLambda χ ψ f else 0) := by
    rw [hdA, Finset.mul_sum]
    have : ∀ f ∈ monicDeg F n, (n : R) * hdLambda χ ψ f = ∑ d ∈ Icc 1 n, ∑ P ∈ irrDeg F d,
        ∑ j ∈ Icc 1 n, (if P ^ j ∣ f then (d : R) * hdLambda χ ψ f else 0) := by
      intro f hf
      obtain ⟨hfm, hfd⟩ := mem_monicDeg.mp hf
      rw [natDegree_eq_sum_dvd (R := R) hfm hfd, Finset.sum_mul]
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun P _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      split_ifs <;> simp
    rw [Finset.sum_congr rfl this, Finset.sum_comm]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun P _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun f _ => ?_
    split_ifs <;> simp
  rw [hL]
  -- right side
  have hR : ∑ k ∈ Icc 1 n, hdC χ ψ k * hdA χ ψ (n - k) =
      ∑ k ∈ Icc 1 n, ∑ d ∈ k.divisors, ∑ P ∈ irrDeg F d,
        (d : R) * hdLambda χ ψ P ^ (k / d) * hdA χ ψ (n - (k / d) * d) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hdC, Finset.sum_mul]
    refine Finset.sum_congr rfl fun d hd => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun P _ => ?_
    rw [Nat.div_mul_cancel (Nat.dvd_of_mem_divisors hd)]
  rw [hR, sum_divisors_reindex n (fun d j => ∑ P ∈ irrDeg F d,
    (d : R) * hdLambda χ ψ P ^ j * hdA χ ψ (n - j * d))]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_congr rfl fun P hP =>
    congrArg ((d : R) * ·) (sum_monicDeg_dvd χ ψ (n := n) (j := j) hP)]
  split_ifs with h
  · exact Finset.sum_congr rfl fun P _ => by ring
  · simp

/-- From identity (7): `c_1 = g(χ)` and `c_{n+1} = -g(χ) c_n`, hence `-c_s = (-g(χ))^s`. -/
theorem neg_hdC_eq [IsDomain R] (hψ : ψ ≠ 1) {s : ℕ} (hs : 1 ≤ s) :
    -hdC χ ψ s = (-gaussSum χ ψ) ^ s := by
  induction s, hs using Nat.le_induction with
  | base =>
    have h := hdNewton χ ψ 1
    simp only [Nat.cast_one, one_mul, Icc_self, sum_singleton, Nat.sub_self, hdA_zero,
      mul_one, hdA_one] at h
    rw [← h, pow_one]
  | succ n hn ih =>
    have h := hdNewton χ ψ (n + 1)
    rw [hdA_eq_zero χ ψ hψ (by omega), mul_zero] at h
    -- only `k = n` and `k = n + 1` contribute
    have hsub : ({n, n + 1} : Finset ℕ) ⊆ Icc 1 (n + 1) := by
      intro k hk; simp only [mem_insert, mem_singleton] at hk; rw [mem_Icc]; omega
    rw [← Finset.sum_subset hsub] at h
    · rw [sum_pair (by omega), Nat.sub_self, hdA_zero, show n + 1 - n = 1 by omega,
        hdA_one, mul_one] at h
      have : hdC χ ψ (n + 1) = -(hdC χ ψ n * gaussSum χ ψ) := by linear_combination -h
      rw [this, pow_succ, ← ih]; ring
    · intro k hk hk'
      simp only [mem_Icc] at hk
      simp only [mem_insert, mem_singleton, not_or] at hk'
      rw [hdA_eq_zero χ ψ hψ (by omega), mul_zero]

end Lambda

section Extension

variable {F : Type*} [Field F] [Fintype F] {E : Type*} [Field E] [Fintype E] [Algebra F E]
variable {R : Type*} [CommRing R]

/-- The lift `χ' = χ ∘ N_{E/F}` of a multiplicative character of `F` to `E`. -/
noncomputable def liftNorm (χ : MulChar F R) : MulChar E R where
  toFun a := χ (Algebra.norm F a)
  map_one' := by simp
  map_mul' a b := by simp
  map_nonunit' a ha := by
    have : a = 0 := by simpa [isUnit_iff_ne_zero] using ha
    subst this
    show χ (Algebra.norm F (0 : E)) = 0
    rw [Algebra.norm_zero]
    exact MulChar.map_zero χ

lemma liftNorm_apply (χ : MulChar F R) (a : E) : liftNorm χ a = χ (Algebra.norm F a) := rfl

/-- The lift `ψ' = ψ ∘ tr_{E/F}` of an additive character of `F` to `E`. -/
noncomputable def liftTrace (ψ : AddChar F R) : AddChar E R :=
  ψ.compAddMonoidHom (Algebra.trace F E).toAddMonoidHom

lemma liftTrace_apply (ψ : AddChar F R) (a : E) : liftTrace ψ a = ψ (Algebra.trace F E a) := rfl

/-- **Lemma 2 (§11.4).** If `α ∈ E` has minimal polynomial `f` of degree `d` over `F`, then
`λ(f)^{s/d} = χ'(α) ψ'(α)`, where `s = [E : F]`. -/
@[kb "irelandrosen1990" "Lemma 2 (§11.4), p. 175"]
theorem hdLambda_minpoly_pow (χ : MulChar F R) (ψ : AddChar F R) (α : E) :
    hdLambda χ ψ (minpoly F α) ^ (Module.finrank F E / (minpoly F α).natDegree) =
      liftNorm χ α * liftTrace ψ α := by
  have hint : IsIntegral F α := .of_finite F α
  set P := minpoly F α with hP
  have hfin : Module.finrank F F⟮α⟯ = P.natDegree := IntermediateField.adjoin.finrank hint
  have htower := Module.finrank_mul_finrank F F⟮α⟯ E
  have hd0 : 0 < P.natDegree := (minpoly.natDegree_pos hint)
  have hm : Module.finrank F⟮α⟯ E = Module.finrank F E / P.natDegree := by
    rw [← htower, hfin, Nat.mul_div_cancel_left _ hd0]
  have htr : Algebra.trace F E α = (Module.finrank F⟮α⟯ E : F) * -P.nextCoeff :=
    trace_eq_finrank_mul_minpoly_nextCoeff F α
  have hnorm : Algebra.norm F α = ((-1) ^ P.natDegree * P.coeff 0) ^ Module.finrank F⟮α⟯ E := by
    rw [Algebra.norm_eq_norm_adjoin F α]
    congr 1
    have := Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly (IntermediateField.adjoin.powerBasis hint)
    rw [IntermediateField.adjoin.powerBasis_gen, IntermediateField.adjoin.powerBasis_dim,
      IntermediateField.minpoly_gen] at this
    exact this
  rw [liftNorm_apply, liftTrace_apply, htr, hnorm, hdLambda, map_pow, ← nsmul_eq_mul,
    AddChar.map_nsmul_eq_pow, ← hm, mul_pow, mul_comm]

/-- An irreducible polynomial of degree `d ∣ [E : F]` has exactly `d` roots in `E`. -/
lemma card_minpoly_eq {d : ℕ} (hd : d ∣ Module.finrank F E) {P : F[X]} (hP : P ∈ irrDeg F d) :
    #{α : E | minpoly F α = P} = d := by
  obtain ⟨hPm, hPd, hPi⟩ := mem_irrDeg.mp hP
  have hfilt : ({α : E | minpoly F α = P} : Finset E) = (P.map (algebraMap F E)).roots.toFinset := by
    ext α
    simp only [mem_filter, mem_univ, true_and, Multiset.mem_toFinset]
    rw [mem_roots_map hPm.ne_zero]
    constructor
    · rintro rfl; rw [← aeval_def]; exact minpoly.aeval F α
    · intro h
      rw [← aeval_def] at h
      exact (minpoly.eq_of_irreducible_of_monic hPi h hPm).symm
  rw [hfilt]
  -- `P ∣ X^{q^s} - X` and `X^{q^s} - X = ∏_{a ∈ E} (X - a)` over `E`
  have hcardE : Fintype.card E = Fintype.card F ^ Module.finrank F E :=
    Module.card_eq_pow_finrank
  have hdvd : P ∣ X ^ Nat.card F ^ Module.finrank F E - X := by
    rw [← hPi.natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X, hPd]; exact hd
  set Q : E[X] := X ^ Fintype.card E - X
  have hQ0 : Q ≠ 0 := X_pow_sub_X_ne_zero Fintype.one_lt_card
  have hdvdE : P.map (algebraMap F E) ∣ Q := by
    have := Polynomial.map_dvd (algebraMap F E) hdvd
    simpa [Q, hcardE, Nat.card_eq_fintype_card] using this
  have hroots : (P.map (algebraMap F E)).roots ≤ Q.roots := roots.le_of_dvd hQ0 hdvdE
  have hnodup : (P.map (algebraMap F E)).roots.Nodup := by
    refine Multiset.nodup_of_le hroots ?_
    rw [FiniteField.roots_X_pow_card_sub_X]
    exact Finset.univ.nodup
  have hsplit : (Q.roots).card = Q.natDegree := by
    rw [FiniteField.roots_X_pow_card_sub_X, Finset.card_val, Finset.card_univ,
      natDegree_X_pow_sub_X Fintype.one_lt_card]
  have hPsplit : Splits (P.map (algebraMap F E)) :=
    (splits_iff_card_roots.mpr hsplit).of_dvd hQ0 hdvdE
  rw [Multiset.toFinset_card_of_nodup hnodup, ← hPsplit.natDegree_eq_card_roots,
    natDegree_map, hPd]

/-- **Lemma 3 (§11.4).** `g(χ') = ∑ (deg f) λ(f)^{s/deg f}`, the sum over the monic irreducible
polynomials `f ∈ F[x]` of degree dividing `s = [E : F]`. -/
@[kb "irelandrosen1990" "Lemma 3 (§11.4), p. 175"]
theorem gaussSum_liftNorm_eq (χ : MulChar F R) (ψ : AddChar F R) :
    gaussSum (liftNorm (E := E) χ) (liftTrace ψ) = hdC χ ψ (Module.finrank F E) := by
  set s := Module.finrank F E
  have hmaps : ∀ α ∈ (univ : Finset E), minpoly F α ∈ s.divisors.biUnion (irrDeg F) := by
    intro α _
    have hint : IsIntegral F α := .of_finite F α
    rw [mem_biUnion]
    refine ⟨(minpoly F α).natDegree, ?_, mem_irrDeg.mpr ⟨minpoly.monic hint, rfl,
      minpoly.irreducible hint⟩⟩
    rw [Nat.mem_divisors]
    refine ⟨?_, Module.finrank_pos.ne'⟩
    rw [← IntermediateField.adjoin.finrank hint]
    exact ⟨_, (Module.finrank_mul_finrank F F⟮α⟯ E).symm⟩
  rw [gaussSum, ← Finset.sum_fiberwise_of_maps_to hmaps, hdC, Finset.sum_biUnion]
  · refine Finset.sum_congr rfl fun d hd => Finset.sum_congr rfl fun P hP => ?_
    have hPd := (mem_irrDeg.mp hP).2.1
    have : ∀ α ∈ ({α ∈ (univ : Finset E) | minpoly F α = P} : Finset E),
        liftNorm χ α * liftTrace ψ α = hdLambda χ ψ P ^ (s / d) := by
      intro α hα
      simp only [mem_filter, mem_univ, true_and] at hα
      rw [← hdLambda_minpoly_pow, hα, hPd]
    rw [Finset.sum_congr rfl this, sum_const, card_minpoly_eq (Nat.dvd_of_mem_divisors hd) hP,
      nsmul_eq_mul]
  · intro d _ d' _ hdd'
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro P hP hP'
    exact hdd' ((mem_irrDeg.mp hP).2.1.symm.trans (mem_irrDeg.mp hP').2.1)

/-- **The Hasse–Davenport relation** (Theorem 1 of §11.3): if `ψ` is a nontrivial additive
character of `F`, `χ` a multiplicative character of `F`, and `E ⊇ F` is a finite field with
`[E : F] = s`, then `(-g(χ))^s = -g(χ')` with `χ' = χ ∘ N_{E/F}` and Gauss sums of `E` taken with
`ψ' = ψ ∘ tr_{E/F}`. -/
@[kb "irelandrosen1990" "Thm 1 (§11.3), p. 173"]
theorem hasse_davenport [IsDomain R] (χ : MulChar F R) {ψ : AddChar F R} (hψ : ψ ≠ 1) :
    (-gaussSum χ ψ) ^ Module.finrank F E = -gaussSum (liftNorm (E := E) χ) (liftTrace ψ) := by
  rw [gaussSum_liftNorm_eq, neg_hdC_eq χ ψ hψ Module.finrank_pos]

end Extension

end NTKB.IrelandRosen
