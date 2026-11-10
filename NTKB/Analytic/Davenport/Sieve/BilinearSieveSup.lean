/- Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license. -/
import NTKB.Analytic.Davenport.Sieve.BilinearSieve

/-!
# The bilinear large sieve with the truncation `mn ≤ u` (Davenport, Chapter 28, estimate (E))

For each modulus `q ≤ Q` and each primitive character `χ` modulo `q` let `u(q, χ)` be an arbitrary
natural number. Then
`∑_{q ≤ Q} (q/φ(q)) ∑*_χ |∑_{m ≤ M} ∑_{n ≤ N, mn ≤ u(q,χ)} a_m b_n χ(mn)|
  ≤ 12 ((M + 3Q²)(N + 3Q²))^{1/2} (∑ |a_m|²)^{1/2} (∑ |b_n|²)^{1/2} log 2MN`.
Since the inner sum only depends on `min(u, MN)`, the arbitrary choice `u(q, χ)` is the book's
maximum over `u`. The proof is the book's: the truncated Perron integral (`perron_truncated_sine`) with
`β = log(u + 1/2)`, `T = (MN)²`, then (F6) (`bilinear_large_sieve`) under the integral.
-/

open Finset Real MeasureTheory

namespace NTKB.Davenport

/-- `|log(u + 1/2) - log k| ≥ 1/(4P)` for integers `1 ≤ k ≤ P`, `u ≤ P`. -/
lemma sup_log_sep {k u P : ℕ} (hk : 1 ≤ k) (hkP : k ≤ P) (huP : u ≤ P) :
    1 / (4 * (P : ℝ)) ≤ |Real.log (u + 1 / 2) - Real.log k| := by
  have hk0 : (0:ℝ) < k := by exact_mod_cast hk
  have hP1 : (1:ℝ) ≤ P := by exact_mod_cast hk.trans hkP
  have hkP' : (k:ℝ) ≤ P := by exact_mod_cast hkP
  have huP' : (u:ℝ) ≤ P := by exact_mod_cast huP
  have hu0 : (0:ℝ) < u + 1/2 := by positivity
  rcases le_or_gt k u with h | h
  · have h' : (k:ℝ) ≤ u := by exact_mod_cast h
    have hl := Real.one_sub_inv_le_log_of_pos (x := (u + 1/2) / k) (by positivity)
    rw [Real.log_div hu0.ne' hk0.ne', inv_div] at hl
    have e : 1 - k / (u + 1/2 : ℝ) = (u + 1/2 - k) / (u + 1/2) := by field_simp
    rw [e] at hl
    have h2 : 1 / (4 * P) ≤ (u + 1/2 - k : ℝ) / (u + 1/2) := by
      rw [div_le_div_iff₀ (by positivity) hu0]; nlinarith
    exact le_abs.2 (Or.inl (by linarith))
  · have h' : (u:ℝ) + 1 ≤ k := by exact_mod_cast h
    have hl := Real.one_sub_inv_le_log_of_pos (x := k / (u + 1/2)) (by positivity)
    rw [Real.log_div hk0.ne' hu0.ne', inv_div] at hl
    have e : 1 - (u + 1/2) / (k : ℝ) = (k - u - 1/2) / k := by field_simp; ring
    rw [e] at hl
    have h2 : 1 / (4 * P) ≤ (k - u - 1/2 : ℝ) / k := by
      rw [div_le_div_iff₀ (by positivity) hk0]; nlinarith
    exact le_abs.2 (Or.inr (by linarith))

/-- The majorant `min(L, 1/|t|)` of `|sin(tβ)/t|` for `0 ≤ β ≤ L`. -/
noncomputable def supKernel (L t : ℝ) : ℝ := min L |t|⁻¹

lemma supKernel_nonneg {L : ℝ} (hL : 0 ≤ L) (t : ℝ) : 0 ≤ supKernel L t :=
  le_min hL (inv_nonneg.2 (abs_nonneg t))

lemma supKernel_le {L : ℝ} (t : ℝ) : supKernel L t ≤ L := min_le_left _ _

lemma supKernel_measurable (L : ℝ) : Measurable (supKernel L) := by
  unfold supKernel; fun_prop

lemma supKernel_ii {L : ℝ} (hL : 0 ≤ L) (a b : ℝ) : IntervalIntegrable (supKernel L) volume a b :=
  bil_ii _ (supKernel_measurable L).aestronglyMeasurable L
    (fun t ↦ by rw [Real.norm_eq_abs, abs_of_nonneg (supKernel_nonneg hL t)]; exact supKernel_le t)
    a b

lemma abs_sin_div_le_supKernel {β L : ℝ} (hβ : 0 ≤ β) (hβL : β ≤ L) (t : ℝ) :
    |sin (t * β) / t| ≤ supKernel L t := by
  refine le_min ((bil_g_bound β t).trans ?_) ?_
  · rw [abs_of_nonneg hβ]; exact hβL
  · rw [abs_div]
    by_cases ht : t = 0
    · simp [ht]
    rw [div_eq_mul_inv]
    exact mul_le_of_le_one_left (inv_nonneg.2 (abs_nonneg _)) (abs_sin_le_one _)

lemma integral_supKernel_half_le {L T c : ℝ} (hL : 0 < L) (hT : 0 ≤ T) (hc : 1 ≤ c)
    (hTc : T * L ≤ c) : ∫ t in (0:ℝ)..T, supKernel L t ≤ 1 + Real.log c := by
  have hlc : 0 ≤ Real.log c := Real.log_nonneg hc
  rcases le_or_gt T (1 / L) with h | h
  · have h1 : ∫ t in (0:ℝ)..T, supKernel L t ≤ ∫ t in (0:ℝ)..T, L :=
      intervalIntegral.integral_mono_on hT (supKernel_ii hL.le 0 T) intervalIntegrable_const
        fun t _ ↦ supKernel_le t
    rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at h1
    have : T * L ≤ 1 := by rw [le_div_iff₀ hL] at h; exact h
    linarith
  · have hL' : 0 < 1 / L := by positivity
    rw [← intervalIntegral.integral_add_adjacent_intervals (supKernel_ii hL.le 0 (1 / L))
      (supKernel_ii hL.le (1 / L) T)]
    have h1 : ∫ t in (0:ℝ)..(1 / L), supKernel L t ≤ ∫ t in (0:ℝ)..(1 / L), L :=
      intervalIntegral.integral_mono_on hL'.le (supKernel_ii hL.le _ _) intervalIntegrable_const
        fun t _ ↦ supKernel_le t
    rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero, one_div_mul_cancel hL.ne'] at h1
    have hinv : IntervalIntegrable (fun t : ℝ ↦ t⁻¹) volume (1 / L) T := by
      refine intervalIntegral.intervalIntegrable_inv (f := id) (fun x hx ↦ ?_) continuousOn_id
      rw [Set.uIcc_of_le h.le] at hx
      exact (lt_of_lt_of_le hL' hx.1).ne'
    have h2 : ∫ t in (1 / L)..T, supKernel L t ≤ ∫ t in (1 / L)..T, t⁻¹ := by
      refine intervalIntegral.integral_mono_on h.le (supKernel_ii hL.le _ _) hinv fun t ht ↦ ?_
      have ht0 : 0 < t := lt_of_lt_of_le hL' ht.1
      exact (min_le_right _ _).trans (by rw [abs_of_pos ht0])
    rw [integral_inv_of_pos hL' (lt_trans hL' h), div_div_eq_mul_div, div_one] at h2
    have h3 : Real.log (T * L) ≤ Real.log c :=
      Real.log_le_log (by have := lt_trans hL' h; positivity) hTc
    linarith

lemma integral_supKernel_le {L T c : ℝ} (hL : 0 < L) (hT : 0 ≤ T) (hc : 1 ≤ c)
    (hTc : T * L ≤ c) : ∫ t in (-T)..T, supKernel L t ≤ 2 * (1 + Real.log c) := by
  rw [bil_sym (supKernel L) (supKernel_ii hL.le)
    (fun a b ↦ by
      have e : (fun t ↦ supKernel L (-t)) = supKernel L := funext fun t ↦ by simp [supKernel]
      rw [e]; exact supKernel_ii hL.le a b) T]
  have he : ∀ t, supKernel L t + supKernel L (-t) = 2 * supKernel L t := fun t ↦ by
    simp [supKernel, abs_neg]; ring
  simp_rw [he]
  rw [intervalIntegral.integral_const_mul]
  have := integral_supKernel_half_le hL hT hc hTc
  linarith

/-- `A(t, χ) = ∑_{m ≤ M} a_m m^{-it} χ(m)`. -/
noncomputable def supA {q : ℕ} (a : ℕ → ℂ) (χ : DirichletCharacter ℂ q) (M : ℕ) (t : ℝ) : ℂ :=
  ∑ m ∈ Icc 1 M, (a m * Complex.exp (t * (-Real.log m) * Complex.I)) * χ m

lemma norm_exp_mul_mul_I (t x : ℝ) : ‖Complex.exp (t * x * Complex.I)‖ = 1 := by
  rw [show (t:ℂ) * x * Complex.I = ((t * x : ℝ) : ℂ) * Complex.I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

lemma norm_supA_le {q : ℕ} (a : ℕ → ℂ) (χ : DirichletCharacter ℂ q) (M : ℕ) (t : ℝ) :
    ‖supA a χ M t‖ ≤ ∑ m ∈ Icc 1 M, ‖a m‖ := by
  refine (norm_sum_le _ _).trans (sum_le_sum fun m _ ↦ ?_)
  have he : ‖Complex.exp (t * (-Real.log m) * Complex.I)‖ = 1 := by
    rw [show (t : ℂ) * (-(Real.log m : ℂ)) * Complex.I = ((t * -Real.log m : ℝ) : ℂ) * Complex.I
      by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  rw [norm_mul, norm_mul, he, mul_one]
  exact mul_le_of_le_one_right (norm_nonneg _) (DirichletCharacter.norm_le_one χ _)

lemma supA_continuous {q : ℕ} (a : ℕ → ℂ) (χ : DirichletCharacter ℂ q) (M : ℕ) :
    Continuous (supA a χ M) := by
  unfold supA; fun_prop

/-- `∑_{m ≤ M} |a_m| ≤ M^{1/2} (∑ |a_m|²)^{1/2}`. -/
lemma sum_norm_le_sqrt_mul (a : ℕ → ℂ) (M : ℕ) :
    ∑ m ∈ Icc 1 M, ‖a m‖ ≤ √M * √(∑ m ∈ Icc 1 M, ‖a m‖ ^ 2) := by
  rw [← Real.sqrt_mul (Nat.cast_nonneg M)]
  refine Real.le_sqrt_of_sq_le ?_
  have := sq_sum_le_card_mul_sum_sq (s := Icc 1 M) (f := fun m ↦ ‖a m‖)
  simpa using this

lemma supIntegrand_ii {q : ℕ} (a b : ℕ → ℂ) (χ : DirichletCharacter ℂ q) (M N : ℕ) {L : ℝ}
    (hL : 0 ≤ L) (x y : ℝ) :
    IntervalIntegrable (fun t ↦ ‖supA a χ M t‖ * ‖supA b χ N t‖ * supKernel L t) volume x y := by
  refine bil_ii _ ?_ ((∑ m ∈ Icc 1 M, ‖a m‖) * (∑ n ∈ Icc 1 N, ‖b n‖) * L) (fun t ↦ ?_) x y
  · exact ((((supA_continuous a χ M).norm.mul (supA_continuous b χ N).norm).measurable).mul
      (supKernel_measurable L)).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity) (supKernel_nonneg hL t))]
    exact mul_le_mul (mul_le_mul (norm_supA_le a χ M t) (norm_supA_le b χ N t) (norm_nonneg _)
      (sum_nonneg fun _ _ ↦ norm_nonneg _)) (supKernel_le t) (supKernel_nonneg hL t)
      (mul_nonneg (sum_nonneg fun _ _ ↦ norm_nonneg _) (sum_nonneg fun _ _ ↦ norm_nonneg _))

/-- The step of (E) for one character: Perron's integral with `β = log(u + 1/2)`, `T = (MN)²`. -/
lemma norm_sum_trunc_le {q : ℕ} (χ : DirichletCharacter ℂ q) {M N : ℕ} (hM : 1 ≤ M) (hN : 1 ≤ N)
    (a b : ℕ → ℂ) (u : ℕ) :
    ‖∑ m ∈ Icc 1 M, ∑ n ∈ (Icc 1 N).filter (fun n ↦ m * n ≤ u),
        a m * b n * χ ((m * n : ℕ) : ZMod q)‖ ≤
      π⁻¹ * (∫ t in (-(((M * N : ℕ) : ℝ) ^ 2))..(((M * N : ℕ) : ℝ) ^ 2),
          ‖supA a χ M t‖ * ‖supA b χ N t‖ * supKernel (Real.log (2 * (M * N : ℕ))) t) +
        π⁻¹ * (16 * √(∑ m ∈ Icc 1 M, ‖a m‖ ^ 2) * √(∑ n ∈ Icc 1 N, ‖b n‖ ^ 2)) := by
  set P := M * N with hP
  have hP1 : 1 ≤ P := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  set T : ℝ := (P : ℝ) ^ 2 with hT
  set L : ℝ := Real.log (2 * P) with hLdef
  have hPr : (1:ℝ) ≤ P := by exact_mod_cast hP1
  have hL : 0 < L := Real.log_pos (by linarith)
  have hT0 : 0 < T := by positivity
  set F : ℝ → ℝ := fun t ↦ ‖supA a χ M t‖ * ‖supA b χ N t‖ * supKernel L t with hF
  have hF0 : 0 ≤ ∫ t in (-T)..T, F t :=
    intervalIntegral.integral_nonneg (by linarith) fun t _ ↦
      mul_nonneg (by positivity) (supKernel_nonneg hL.le t)
  set u' := min u P with hu'
  have hS : (∑ m ∈ Icc 1 M, ∑ n ∈ (Icc 1 N).filter (fun n ↦ m * n ≤ u),
        a m * b n * χ ((m * n : ℕ) : ZMod q)) =
      ∑ m ∈ Icc 1 M, ∑ n ∈ Icc 1 N,
        if m * n ≤ u' then a m * b n * χ ((m * n : ℕ) : ZMod q) else 0 := by
    refine sum_congr rfl fun m hm ↦ ?_
    rw [sum_filter]
    refine sum_congr rfl fun n hn ↦ ?_
    have h1 : m * n ≤ P := Nat.mul_le_mul (mem_Icc.1 hm).2 (mem_Icc.1 hn).2
    have h2 : m * n ≤ u ↔ m * n ≤ u' := by
      rw [hu', le_min_iff]; exact ⟨fun h ↦ ⟨h, h1⟩, fun h ↦ h.1⟩
    simp only [h2]
  rw [hS]
  have hpos : ∀ m ∈ Icc 1 M, ∀ n ∈ Icc 1 N, 1 ≤ m * n := fun m hm n hn ↦
    Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by have := (mem_Icc.1 hm).1; omega)
      (by have := (mem_Icc.1 hn).1; omega))
  rcases Nat.eq_zero_or_pos u' with hu0 | hu0
  · rw [sum_eq_zero fun m hm ↦ sum_eq_zero fun n hn ↦ (ite_eq_right_iff.2 fun h ↦ absurd h (by have := hpos m hm n hn; omega)),
      norm_zero]
    exact add_nonneg (mul_nonneg (inv_nonneg.2 Real.pi_pos.le) hF0) (by positivity)
  set β := Real.log (u' + 1 / 2) with hβdef
  have hu1 : (1:ℝ) ≤ u' := by exact_mod_cast hu0
  have huP : u' ≤ P := min_le_right _ _
  have huP' : (u':ℝ) ≤ P := by exact_mod_cast huP
  have hβ : 0 < β := Real.log_pos (by linarith)
  have hβL : β ≤ L := Real.log_le_log (by positivity) (by linarith)
  set g : ℝ → ℂ := fun t ↦ ((Real.sin (t * β) / t : ℝ) : ℂ) with hg
  set c : ℕ → ℕ → ℂ := fun m n ↦ a m * b n * χ ((m * n : ℕ) : ZMod q) with hc
  set I : ℕ → ℕ → ℂ := fun m n ↦ ∫ t in (-T)..T, bil_h (-Real.log (m * n : ℕ)) β t with hI
  set E : ℕ → ℕ → ℂ := fun m n ↦ I m n - ((if m * n ≤ u' then π else 0 : ℝ) : ℂ) with hE
  -- the Perron error
  have hEb : ∀ m ∈ Icc 1 M, ∀ n ∈ Icc 1 N, ‖E m n‖ ≤ 16 * P / T := by
    intro m hm n hn
    have hmn := hpos m hm n hn
    have hmnP : m * n ≤ P := Nat.mul_le_mul (mem_Icc.1 hm).2 (mem_Icc.1 hn).2
    have hsep := sup_log_sep hmn hmnP huP
    have hlog0 : 0 ≤ Real.log (m * n : ℕ) := Real.log_natCast_nonneg _
    have habs : |-Real.log (m * n : ℕ)| = Real.log (m * n : ℕ) := by
      rw [abs_neg, abs_of_nonneg hlog0]
    have hne : |-Real.log (m * n : ℕ)| ≠ β := by
      rw [habs]; intro h; rw [h, sub_self, abs_zero] at hsep
      have : (0:ℝ) < 1 / (4 * P) := by positivity
      linarith
    have hiff : |-Real.log (m * n : ℕ)| < β ↔ m * n ≤ u' := by
      rw [habs, hβdef, Real.log_lt_log_iff (by exact_mod_cast hmn) (by positivity)]
      constructor
      · intro h; by_contra h'; push Not at h'
        have : (u' : ℝ) + 1 ≤ ((m * n : ℕ) : ℝ) := by exact_mod_cast h'
        linarith
      · intro h; have : ((m * n : ℕ) : ℝ) ≤ u' := by exact_mod_cast h
        linarith
    have hp := perron_truncated_sine hT0 hβ hne
    have hite : (if |-Real.log (m * n : ℕ)| < β then π else 0 : ℝ) =
        (if m * n ≤ u' then π else 0 : ℝ) := by simp only [hiff]
    rw [hite] at hp
    calc ‖E m n‖ ≤ 4 / (T * abs (β - |-Real.log (m * n : ℕ)|)) := hp
      _ ≤ 4 / (T * (1 / (4 * P))) := by
          refine div_le_div_of_nonneg_left (by norm_num) (by positivity) ?_
          refine mul_le_mul_of_nonneg_left ?_ hT0.le
          rw [habs]; exact hsep
      _ = 16 * P / T := by field_simp; ring
  -- each term
  have hterm : ∀ m ∈ Icc 1 M, ∀ n ∈ Icc 1 N,
      (if m * n ≤ u' then c m n else 0) = π⁻¹ * (c m n * I m n) - π⁻¹ * (c m n * E m n) := by
    intro m _ n _
    rw [← mul_sub, ← mul_sub, hE, sub_sub_cancel]
    have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    split_ifs
    · push_cast; field_simp
    · simp
  -- the integral identity
  have hident : (∫ t in (-T)..T, supA a χ M t * supA b χ N t * g t) =
      ∑ m ∈ Icc 1 M, ∑ n ∈ Icc 1 N, c m n * I m n := by
    have hpt : ∀ t, supA a χ M t * supA b χ N t * g t =
        ∑ m ∈ Icc 1 M, ∑ n ∈ Icc 1 N, c m n * bil_h (-Real.log (m * n : ℕ)) β t := by
      intro t
      simp only [supA]
      rw [sum_mul_sum, sum_mul]
      refine sum_congr rfl fun m hm ↦ ?_
      rw [sum_mul]
      refine sum_congr rfl fun n hn ↦ ?_
      have hm0 : (m : ℝ) ≠ 0 := by have := (mem_Icc.1 hm).1; positivity
      have hn0 : (n : ℝ) ≠ 0 := by have := (mem_Icc.1 hn).1; positivity
      simp only [hc, bil_h, hg]
      have he : Complex.exp (t * (-Real.log m) * Complex.I) * Complex.exp (t * (-Real.log n) *
          Complex.I) = Complex.exp (t * (-Real.log (m * n : ℕ) : ℝ) * Complex.I) := by
        rw [← Complex.exp_add]; congr 1
        push_cast; rw [Real.log_mul hm0 hn0]; push_cast; ring
      rw [Nat.cast_mul (α := ZMod q), map_mul, ← he]
      ring
    simp_rw [hpt]
    have hii : ∀ m n, IntervalIntegrable (fun t ↦ c m n * bil_h (-Real.log (m * n : ℕ)) β t)
        volume (-T) T := fun m n ↦ (bil_h_ii _ _ _ _).const_mul _
    have hii2 : ∀ m, IntervalIntegrable
        (fun t ↦ ∑ n ∈ Icc 1 N, c m n * bil_h (-Real.log (m * n : ℕ)) β t) volume (-T) T := by
      intro m
      have := IntervalIntegrable.sum (Icc 1 N) (fun n _ ↦ hii m n)
      rwa [Finset.sum_fn] at this
    rw [intervalIntegral.integral_finsetSum fun m _ ↦ hii2 m]
    refine sum_congr rfl fun m _ ↦ ?_
    rw [intervalIntegral.integral_finsetSum fun n _ ↦ hii m n]
    refine sum_congr rfl fun n _ ↦ ?_
    rw [intervalIntegral.integral_const_mul]
  have hint : ‖∫ t in (-T)..T, supA a χ M t * supA b χ N t * g t‖ ≤ ∫ t in (-T)..T, F t := by
    refine intervalIntegral.norm_integral_le_of_norm_le (by linarith) (ae_of_all _ fun t _ ↦ ?_)
      (supIntegrand_ii a b χ M N hL.le _ _)
    simp only [hF, hg, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (abs_sin_div_le_supKernel hβ.le hβL t) (by positivity)
  have herr : ‖∑ m ∈ Icc 1 M, ∑ n ∈ Icc 1 N, c m n * E m n‖ ≤
      16 * √(∑ m ∈ Icc 1 M, ‖a m‖ ^ 2) * √(∑ n ∈ Icc 1 N, ‖b n‖ ^ 2) := by
    calc _ ≤ ∑ m ∈ Icc 1 M, ∑ n ∈ Icc 1 N, ‖a m‖ * ‖b n‖ * (16 * P / T) := by
          refine (norm_sum_le _ _).trans (sum_le_sum fun m hm ↦ ?_)
          refine (norm_sum_le _ _).trans (sum_le_sum fun n hn ↦ ?_)
          rw [norm_mul]
          refine mul_le_mul ?_ (hEb m hm n hn) (norm_nonneg _) (by positivity)
          rw [hc, norm_mul, norm_mul]
          exact mul_le_of_le_one_right (by positivity) (DirichletCharacter.norm_le_one χ _)
      _ = (∑ m ∈ Icc 1 M, ‖a m‖) * (∑ n ∈ Icc 1 N, ‖b n‖) * (16 * P / T) := by
          rw [sum_mul_sum, sum_mul]
          refine sum_congr rfl fun m _ ↦ by rw [sum_mul]
      _ ≤ (√M * √(∑ m ∈ Icc 1 M, ‖a m‖ ^ 2)) * (√N * √(∑ n ∈ Icc 1 N, ‖b n‖ ^ 2)) *
            (16 * P / T) := by
          gcongr
          · exact sum_norm_le_sqrt_mul a M
          · exact sum_norm_le_sqrt_mul b N
      _ = 16 * (√P * P / T) * √(∑ m ∈ Icc 1 M, ‖a m‖ ^ 2) * √(∑ n ∈ Icc 1 N, ‖b n‖ ^ 2) := by
          rw [hP, Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg _)]; ring
      _ ≤ 16 * 1 * √(∑ m ∈ Icc 1 M, ‖a m‖ ^ 2) * √(∑ n ∈ Icc 1 N, ‖b n‖ ^ 2) := by
          gcongr
          rw [div_le_one hT0, hT]
          have : √(P:ℝ) ≤ P := by
            calc √(P:ℝ) ≤ √((P:ℝ) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
              _ = P := Real.sqrt_sq (by positivity)
          nlinarith
      _ = _ := by ring
  have hsum : (∑ m ∈ Icc 1 M, ∑ n ∈ Icc 1 N, if m * n ≤ u' then c m n else 0) =
      π⁻¹ * (∫ t in (-T)..T, supA a χ M t * supA b χ N t * g t) -
        π⁻¹ * ∑ m ∈ Icc 1 M, ∑ n ∈ Icc 1 N, c m n * E m n := by
    rw [hident, mul_sum, mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun m hm ↦ ?_
    rw [mul_sum, mul_sum, ← sum_sub_distrib]
    exact sum_congr rfl fun n hn ↦ hterm m hm n hn
  have hπ : (0:ℝ) < π⁻¹ := inv_pos.2 Real.pi_pos
  calc ‖∑ m ∈ Icc 1 M, ∑ n ∈ Icc 1 N, if m * n ≤ u' then c m n else 0‖
      ≤ ‖π⁻¹ * (∫ t in (-T)..T, supA a χ M t * supA b χ N t * g t)‖ +
          ‖π⁻¹ * ∑ m ∈ Icc 1 M, ∑ n ∈ Icc 1 N, c m n * E m n‖ := by
        rw [hsum]; exact norm_sub_le _ _
    _ ≤ π⁻¹ * (∫ t in (-T)..T, F t) +
          π⁻¹ * (16 * √(∑ m ∈ Icc 1 M, ‖a m‖ ^ 2) * √(∑ n ∈ Icc 1 N, ‖b n‖ ^ 2)) := by
        simp only [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, 
          abs_of_pos Real.pi_pos]
        gcongr

open scoped Classical in
/-- **Davenport, Ch. 28, p. 164, (E)**: for `Q ≥ 1` and any choice of truncation points
`u(q, χ)`,
`∑_{q ≤ Q} (q/φ(q)) ∑*_χ |∑_{m ≤ M} ∑_{n ≤ N, mn ≤ u(q,χ)} a_m b_n χ(mn)|
  ≤ 12 ((M + 3Q²)(N + 3Q²))^{1/2} (∑ |a_m|²)^{1/2} (∑ |b_n|²)^{1/2} log 2MN`.
(The inner sum depends only on `min(u, MN)`, so this is the book's maximum over `u`.) -/
@[kb "davenport1980" "Ch 28, p. 164, (E)"]
theorem bilinear_sieve_sup {Q : ℝ} (hQ : 1 ≤ Q) (M N : ℕ) (a b : ℕ → ℂ)
    (u : (q : ℕ) → DirichletCharacter ℂ q → ℕ) :
    ∑ q ∈ Icc 1 ⌊Q⌋₊, ((q : ℝ) / q.totient) *
        ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ ↦ χ.IsPrimitive),
          ‖∑ m ∈ Icc 1 M, ∑ n ∈ (Icc 1 N).filter (fun n ↦ m * n ≤ u q χ),
            a m * b n * χ ((m * n : ℕ) : ZMod q)‖ ≤
      12 * √((M + 3 * Q ^ 2) * (N + 3 * Q ^ 2)) * √(∑ m ∈ Icc 1 M, ‖a m‖ ^ 2) *
        √(∑ n ∈ Icc 1 N, ‖b n‖ ^ 2) * Real.log (2 * M * N) := by
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · simp
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  set P := M * N with hP
  have hP1 : 1 ≤ P := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  have hPr : (1:ℝ) ≤ P := by exact_mod_cast hP1
  set T : ℝ := (P : ℝ) ^ 2 with hT
  set L : ℝ := Real.log (2 * P) with hLdef
  have hL : 0 < L := Real.log_pos (by linarith)
  have hT0 : 0 < T := by positivity
  set A2 := ∑ m ∈ Icc 1 M, ‖a m‖ ^ 2 with hA2
  set B2 := ∑ n ∈ Icc 1 N, ‖b n‖ ^ 2 with hB2
  set K := √((M + 3 * Q ^ 2) * (N + 3 * Q ^ 2)) * √A2 * √B2 with hK
  have hK0 : 0 ≤ K := by positivity
  set prim : (q : ℕ) → Finset (DirichletCharacter ℂ q) :=
    fun q ↦ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ ↦ χ.IsPrimitive) with hprim
  set w : ℕ → ℝ := fun q ↦ (q : ℝ) / q.totient with hw
  have hw0 : ∀ q, 0 ≤ w q := fun q ↦ by positivity
  set F : (q : ℕ) → DirichletCharacter ℂ q → ℝ → ℝ :=
    fun q χ t ↦ ‖supA a χ M t‖ * ‖supA b χ N t‖ * supKernel L t with hF
  have hFii : ∀ q (χ : DirichletCharacter ℂ q), IntervalIntegrable (F q χ) volume (-T) T :=
    fun q χ ↦ supIntegrand_ii a b χ M N hL.le _ _
  have hMN : ((M * N : ℕ) : ℝ) = P := rfl
  -- step 1: the per-character bound
  have step1 : ∑ q ∈ Icc 1 ⌊Q⌋₊, w q * ∑ χ ∈ prim q,
        ‖∑ m ∈ Icc 1 M, ∑ n ∈ (Icc 1 N).filter (fun n ↦ m * n ≤ u q χ),
          a m * b n * χ ((m * n : ℕ) : ZMod q)‖ ≤
      ∑ q ∈ Icc 1 ⌊Q⌋₊, w q * ∑ χ ∈ prim q,
        (π⁻¹ * (∫ t in (-T)..T, F q χ t) + π⁻¹ * (16 * √A2 * √B2)) := by
    refine sum_le_sum fun q _ ↦ mul_le_mul_of_nonneg_left (sum_le_sum fun χ _ ↦ ?_) (hw0 q)
    exact norm_sum_trunc_le χ hM hN a b (u q χ)
  -- step 2: interchange
  have hswap : ∑ q ∈ Icc 1 ⌊Q⌋₊, w q * ∑ χ ∈ prim q, (∫ t in (-T)..T, F q χ t) =
      ∫ t in (-T)..T, ∑ q ∈ Icc 1 ⌊Q⌋₊, w q * ∑ χ ∈ prim q, F q χ t := by
    have hi1 : ∀ q, IntervalIntegrable (fun t ↦ ∑ χ ∈ prim q, F q χ t) volume (-T) T := by
      intro q
      have := IntervalIntegrable.sum (prim q) (fun χ _ ↦ hFii q χ)
      rwa [Finset.sum_fn] at this
    have hi2 : ∀ q, IntervalIntegrable (fun t ↦ w q * ∑ χ ∈ prim q, F q χ t) volume (-T) T :=
      fun q ↦ (hi1 q).const_mul _
    rw [intervalIntegral.integral_finsetSum fun q _ ↦ hi2 q]
    refine sum_congr rfl fun q _ ↦ ?_
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_finsetSum fun χ _ ↦ hFii q χ]
  -- step 3: (F6) under the integral
  have hpt : ∀ t, ∑ q ∈ Icc 1 ⌊Q⌋₊, w q * ∑ χ ∈ prim q, F q χ t ≤ K * supKernel L t := by
    intro t
    set a' : ℕ → ℂ := fun m ↦ a m * Complex.exp (t * (-Real.log m) * Complex.I)
    set b' : ℕ → ℂ := fun n ↦ b n * Complex.exp (t * (-Real.log n) * Complex.I)
    have hn : ∀ x : ℕ, ‖Complex.exp (t * (-Real.log x) * Complex.I)‖ = 1 := fun x ↦ by
      rw [show (t : ℂ) * (-(Real.log x : ℂ)) * Complex.I = ((t * -Real.log x : ℝ) : ℂ) *
        Complex.I by push_cast; ring]
      exact Complex.norm_exp_ofReal_mul_I _
    have ha' : ∑ m ∈ Icc 1 M, ‖a' m‖ ^ 2 = A2 :=
      sum_congr rfl fun m _ ↦ by simp only [a', norm_mul, hn, mul_one]
    have hb' : ∑ n ∈ Icc 1 N, ‖b' n‖ ^ 2 = B2 :=
      sum_congr rfl fun n _ ↦ by simp only [b', norm_mul, hn, mul_one]
    have h6 := bilinear_large_sieve hQ M N a' b'
    rw [ha', hb'] at h6
    have hk := supKernel_nonneg hL.le t
    calc ∑ q ∈ Icc 1 ⌊Q⌋₊, w q * ∑ χ ∈ prim q, F q χ t
        = (∑ q ∈ Icc 1 ⌊Q⌋₊, w q * ∑ χ ∈ prim q,
            ‖∑ m ∈ Icc 1 M, a' m * χ m‖ * ‖∑ n ∈ Icc 1 N, b' n * χ n‖) * supKernel L t := by
          rw [sum_mul]
          refine sum_congr rfl fun q _ ↦ ?_
          rw [mul_assoc, sum_mul]
          rfl
      _ ≤ K * supKernel L t := by
          refine mul_le_mul_of_nonneg_right ?_ hk
          simpa [hK, mul_assoc] using h6
  have hint : ∫ t in (-T)..T, ∑ q ∈ Icc 1 ⌊Q⌋₊, w q * ∑ χ ∈ prim q, F q χ t ≤
      K * (2 * (1 + 3 * L)) := by
    have hi := supKernel_ii hL.le (-T) T
    calc _ ≤ ∫ t in (-T)..T, K * supKernel L t := by
          refine intervalIntegral.integral_mono_on (by linarith) ?_ (hi.const_mul K)
            fun t _ ↦ hpt t
          have hi1 : ∀ q, IntervalIntegrable (fun t ↦ ∑ χ ∈ prim q, F q χ t) volume (-T) T := by
            intro q
            have := IntervalIntegrable.sum (prim q) (fun χ _ ↦ hFii q χ)
            rwa [Finset.sum_fn] at this
          have := IntervalIntegrable.sum (Icc 1 ⌊Q⌋₊) (fun q _ ↦ (hi1 q).const_mul (w q))
          rwa [Finset.sum_fn] at this
      _ = K * ∫ t in (-T)..T, supKernel L t := intervalIntegral.integral_const_mul _ _
      _ ≤ K * (2 * (1 + Real.log ((2 * P) ^ 3))) := by
          refine mul_le_mul_of_nonneg_left (integral_supKernel_le hL hT0.le ?_ ?_) hK0
          · have : (1:ℝ) ≤ 2 * P := by linarith
            exact one_le_pow₀ this
          · have hl : L ≤ 2 * P := (Real.log_le_sub_one_of_pos (by positivity)).trans (by linarith)
            calc T * L ≤ P ^ 2 * (2 * P) := by rw [hT]; gcongr
              _ ≤ (2 * P) ^ 3 := by nlinarith [pow_pos (show (0:ℝ) < P by linarith) 3]
      _ = K * (2 * (1 + 3 * L)) := by
          rw [Real.log_pow]; push_cast; ring
  -- step 4: the count of characters
  have hcount : ∑ q ∈ Icc 1 ⌊Q⌋₊, w q * ∑ χ ∈ prim q, (1 : ℝ) ≤ Q ^ 2 := by
    calc _ ≤ ∑ q ∈ Icc 1 ⌊Q⌋₊, ((⌊Q⌋₊ : ℕ) : ℝ) := by
          refine sum_le_sum fun q hq ↦ ?_
          have hq1 := (mem_Icc.1 hq).1
          have : NeZero q := ⟨by omega⟩
          have hφ : (0:ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.2 hq1
          rw [sum_const, nsmul_eq_mul, mul_one]
          calc w q * ((prim q).card : ℝ) ≤ w q * q.totient := by
                refine mul_le_mul_of_nonneg_left ?_ (hw0 q)
                rw [← card_dirichletCharacter q]
                exact_mod_cast card_filter_le _ _
            _ = q := by simp only [hw]; field_simp
            _ ≤ ⌊Q⌋₊ := by exact_mod_cast (mem_Icc.1 hq).2
      _ = (⌊Q⌋₊ : ℝ) ^ 2 := by rw [sum_const, Nat.card_Icc, nsmul_eq_mul]; push_cast; ring
      _ ≤ Q ^ 2 := by gcongr; exact Nat.floor_le (by linarith)
  have hQK : Q ^ 2 * (√A2 * √B2) ≤ K := by
    rw [hK, mul_assoc]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    refine le_of_eq_of_le (Real.sqrt_mul_self (by positivity : (0:ℝ) ≤ Q ^ 2)).symm
      (Real.sqrt_le_sqrt ?_)
    have h1 : Q ^ 2 ≤ M + 3 * Q ^ 2 := by have := sq_nonneg Q; linarith [(Nat.cast_nonneg M : (0:ℝ) ≤ M)]
    have h2 : Q ^ 2 ≤ N + 3 * Q ^ 2 := by have := sq_nonneg Q; linarith [(Nat.cast_nonneg N : (0:ℝ) ≤ N)]
    exact mul_le_mul h1 h2 (by positivity) (by positivity)
  have hLge : 1 ≤ 1.45 * L := by
    have h2 : Real.log 2 ≤ L := Real.log_le_log (by norm_num) (by linarith)
    have := Real.log_two_gt_d9
    linarith
  have hπ := Real.pi_gt_three
  have hlog : Real.log (2 * M * N) = L := by
    rw [hLdef, hP]; push_cast; ring_nf
  rw [hlog]
  calc _ = ∑ q ∈ Icc 1 ⌊Q⌋₊, w q * ∑ χ ∈ prim q,
        ‖∑ m ∈ Icc 1 M, ∑ n ∈ (Icc 1 N).filter (fun n ↦ m * n ≤ u q χ),
          a m * b n * χ ((m * n : ℕ) : ZMod q)‖ := rfl
    _ ≤ _ := step1
    _ = π⁻¹ * (∑ q ∈ Icc 1 ⌊Q⌋₊, w q * ∑ χ ∈ prim q, (∫ t in (-T)..T, F q χ t)) +
          π⁻¹ * (16 * √A2 * √B2) * ∑ q ∈ Icc 1 ⌊Q⌋₊, w q * ∑ χ ∈ prim q, (1 : ℝ) := by
        rw [mul_sum, mul_sum, ← sum_add_distrib]
        refine sum_congr rfl fun q _ ↦ ?_
        rw [sum_add_distrib, ← mul_sum, ← mul_sum, ← mul_sum]
        simp only [sum_const, nsmul_eq_mul, mul_one]
        ring
    _ ≤ π⁻¹ * (K * (2 * (1 + 3 * L))) + π⁻¹ * (16 * √A2 * √B2) * Q ^ 2 := by
        rw [hswap]
        gcongr
    _ ≤ 12 * K * L := by
        have hπi : π⁻¹ ≤ 1 / 3 := by rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) hπ.le
        have h16 : π⁻¹ * (16 * √A2 * √B2) * Q ^ 2 ≤ π⁻¹ * (16 * K) := by
          have := hQK
          have hp : 0 ≤ π⁻¹ := by positivity
          nlinarith
        have hmain : π⁻¹ * (K * (2 * (1 + 3 * L))) + π⁻¹ * (16 * K) = π⁻¹ * (K * (18 + 6 * L)) := by
          ring
        have hb : K * (18 + 6 * L) ≤ K * (32.1 * L) := by
          refine mul_le_mul_of_nonneg_left ?_ hK0; linarith
        have hb2 : π⁻¹ * (K * (32.1 * L)) ≤ 1 / 3 * (K * (32.1 * L)) :=
          mul_le_mul_of_nonneg_right hπi (by positivity)
        have hp : 0 ≤ π⁻¹ := by positivity
        nlinarith [mul_le_mul_of_nonneg_left hb hp]
    _ = _ := by rw [hK]; ring

end NTKB.Davenport
