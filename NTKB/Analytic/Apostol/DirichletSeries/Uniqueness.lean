/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.NumberTheory.LSeries.Linearity
import Mathlib.NumberTheory.LSeries.Convergence
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import NTKB.Attr

/-!
# The sum function of an absolutely convergent Dirichlet series (Apostol, §11.3)

* **Lemma 1 of Chapter 11** (`ch11_lemma_1`): for `N ≥ 1` and `σ ≥ c` (absolute convergence at
  `c`), `|∑_{n ≥ N} f(n) n^{-s}| ≤ N^{-(σ-c)} ∑_{n ≥ N} |f(n)| n^{-c}`.
* **Theorem 11.2** (`apostol_thm_11_2`): `F(σ+it) → f(1)` as `σ → +∞`, uniformly in `t`.
* **Theorem 11.3** (`apostol_thm_11_3`, uniqueness): if `F(s_k) = G(s_k)` along a sequence of
  complex numbers with `σ_k → +∞`, then `f(n) = g(n)` for all `n ≥ 1`.
* **Theorem 11.4** (`apostol_thm_11_4`): if `F(s) ≠ 0` for some `s`, then `F` has no zeros in
  some half-plane `σ > c > σ_a`.

Mathlib has the real-variable forms (`LSeries.tendsto_atTop`,
`LSeries_eq_iff_of_abscissaOfAbsConv_lt_top`); Apostol's statements are for complex `s` (uniform in
`t`, arbitrary complex sequences). Proofs follow Apostol, through Lemma 1.
-/

open Complex Filter Topology Finset LSeries

namespace NTKB.Apostol

lemma norm_term_le_of_le {f : ℕ → ℂ} {c : ℝ} {s : ℂ} (hs : c ≤ s.re) {N m : ℕ} (hN : 1 ≤ N)
    (hm : N ≤ m) : ‖term f s m‖ ≤ (N : ℝ) ^ (-(s.re - c)) * ‖term f c m‖ := by
  have hm0 : m ≠ 0 := by omega
  have hmpos : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm0
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  rw [norm_term_eq, norm_term_eq, ite_eq_right hm0, ite_eq_right hm0, ofReal_re]
  have e : (m : ℝ) ^ s.re = (m : ℝ) ^ c * (m : ℝ) ^ (s.re - c) := by
    rw [← Real.rpow_add hmpos]; ring_nf
  have h1 : (N : ℝ) ^ (s.re - c) ≤ (m : ℝ) ^ (s.re - c) :=
    Real.rpow_le_rpow hNpos.le (by exact_mod_cast hm) (by linarith)
  have h2 : 0 < (m : ℝ) ^ c := Real.rpow_pos_of_pos hmpos _
  have h3 : 0 < (N : ℝ) ^ (s.re - c) := Real.rpow_pos_of_pos hNpos _
  rw [e, Real.rpow_neg hNpos.le]
  calc ‖f m‖ / ((m : ℝ) ^ c * (m : ℝ) ^ (s.re - c)) = (‖f m‖ / (m : ℝ) ^ c) / (m : ℝ) ^ (s.re - c) := by
        rw [div_div]
    _ ≤ (‖f m‖ / (m : ℝ) ^ c) / (N : ℝ) ^ (s.re - c) :=
        div_le_div_of_nonneg_left (by positivity) h3 h1
    _ = ((N : ℝ) ^ (s.re - c))⁻¹ * (‖f m‖ / (m : ℝ) ^ c) := by rw [div_eq_inv_mul]

/-- **Lemma 1 of Chapter 11** (Apostol, p. 226). -/
@[kb "apostol1976" "Ch. 11, Lemma 1, p. 226"]
theorem ch11_lemma_1 {f : ℕ → ℂ} {c : ℝ} (hc : LSeriesSummable f c) {N : ℕ} (hN : 1 ≤ N)
    {s : ℂ} (hs : c ≤ s.re) :
    ‖∑' n, term f s (n + N)‖ ≤ (N : ℝ) ^ (-(s.re - c)) * ∑' n, ‖term f c (n + N)‖ := by
  have hcs : Summable fun n => ‖term f c (n + N)‖ :=
    (summable_nat_add_iff N).mpr (summable_norm_iff.mpr hc)
  have hss : Summable fun n => ‖term f s (n + N)‖ :=
    (summable_nat_add_iff N).mpr (summable_norm_iff.mpr (hc.of_re_le_re (by simpa using hs)))
  refine (norm_tsum_le_tsum_norm hss).trans ?_
  rw [← tsum_mul_left]
  exact hss.tsum_le_tsum (fun n => norm_term_le_of_le hs hN (by omega)) (hcs.mul_left _)

lemma LSeries_eq_add_tail {f : ℕ → ℂ} {s : ℂ} (hf : LSeriesSummable f s) :
    LSeries f s = f 1 + ∑' n, term f s (n + 2) := by
  rw [LSeries, ← hf.sum_add_tsum_nat_add 2]
  simp [Finset.sum_range_succ]

lemma exists_LSeriesSummable_real {f : ℕ → ℂ} (ha : abscissaOfAbsConv f < ⊤) :
    ∃ c : ℝ, LSeriesSummable f c := by
  obtain ⟨y, hay, hyt⟩ := exists_between ha
  lift y to ℝ using ⟨hyt.ne, ((OrderBot.bot_le _).trans_lt hay).ne'⟩
  exact ⟨y, LSeriesSummable_of_abscissaOfAbsConv_lt_re (by simpa using hay)⟩

/-- `b^{x - c} → 0` as `x → ∞` for `0 ≤ b < 1`. -/
lemma tendsto_rpow_sub_atTop {b c : ℝ} (hb0 : 0 ≤ b) (hb1 : b < 1) :
    Tendsto (fun x : ℝ => b ^ (x - c)) atTop (𝓝 0) :=
  (tendsto_rpow_atTop_of_base_lt_one b (by linarith) hb1).comp (tendsto_atTop_add_const_right _ _
    tendsto_id)

/-- **Theorem 11.2**: if `∑ f(n) n^{-s}` converges absolutely somewhere, then
`F(σ + it) → f(1)` as `σ → +∞`, uniformly for `t ∈ ℝ`. -/
@[kb "apostol1976" "Thm 11.2, p. 226"]
theorem apostol_thm_11_2 {f : ℕ → ℂ} (ha : abscissaOfAbsConv f < ⊤) :
    TendstoUniformly (fun (σ : ℝ) (t : ℝ) => LSeries f (σ + t * I)) (fun _ => f 1) atTop := by
  obtain ⟨c, hc⟩ := exists_LSeriesSummable_real ha
  set K := ∑' n, ‖term f c (n + 2)‖
  have hK : 0 ≤ K := tsum_nonneg fun _ => norm_nonneg _
  have hbound : ∀ σ : ℝ, c ≤ σ → ∀ t : ℝ, ‖f 1 - LSeries f (σ + t * I)‖ ≤ (1 / 2) ^ (σ - c) * K := by
    intro σ hσ t
    have hre : c ≤ ((σ : ℂ) + t * I).re := by simpa using hσ
    rw [LSeries_eq_add_tail (hc.of_re_le_re (by simpa using hre)), sub_add_cancel_left, norm_neg]
    refine (ch11_lemma_1 hc (by norm_num) hre).trans (le_of_eq ?_)
    simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, mul_zero, I_im, mul_one, sub_self,
      add_zero, Nat.cast_ofNat]
    rw [Real.rpow_neg (by norm_num), ← Real.inv_rpow (by norm_num), one_div]
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  have hlim : Tendsto (fun σ : ℝ => (1 / 2 : ℝ) ^ (σ - c) * K) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_sub_atTop (c := c) (by norm_num) (by norm_num)).mul_const K
  filter_upwards [(tendsto_order.mp hlim).2 ε hε, eventually_ge_atTop c] with σ h1 h2 t
  rw [dist_eq_norm]
  exact (hbound σ h2 t).trans_lt h1

/-- The core of Theorem 11.3: a Dirichlet series absolutely convergent at `c` that vanishes along
a sequence `s_k` with `Re s_k → +∞` has all coefficients `h(n)`, `n ≥ 1`, equal to zero. -/
theorem eq_zero_of_LSeries_eq_zero_seq {h : ℕ → ℂ} {c : ℝ} (hc : LSeriesSummable h c)
    {s : ℕ → ℂ} (hs : Tendsto (fun k => (s k).re) atTop atTop)
    (h0 : ∀ᶠ k in atTop, LSeries h (s k) = 0) : ∀ n, n ≠ 0 → h n = 0 := by
  classical
  by_contra hcon
  push Not at hcon
  set N := Nat.find hcon with hNdef
  obtain ⟨hN0, hNh⟩ := Nat.find_spec hcon
  have hmin : ∀ m < N, m ≠ 0 → h m = 0 := fun m hm hm0 => by
    have := Nat.find_min hcon hm
    push Not at this
    exact this hm0
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN0
  set K := ∑' n, ‖term h c (n + (N + 1))‖
  have hK : 0 ≤ K := tsum_nonneg fun _ => norm_nonneg _
  -- for `σ_k ≥ c`: `|h(N)| ≤ N^c K (N/(N+1))^{σ_k - c}`
  have hbound : ∀ z : ℂ, c ≤ z.re → LSeries h z = 0 →
      ‖h N‖ ≤ (N : ℝ) ^ c * K * ((N : ℝ) / (N + 1)) ^ (z.re - c) := by
    intro z hz hz0
    have hsz : LSeriesSummable h z := hc.of_re_le_re (by simpa using hz)
    have hsplit := hsz.sum_add_tsum_nat_add (N + 1)
    rw [Finset.sum_range_succ, Finset.sum_eq_zero (fun m hm => ?_), zero_add] at hsplit
    swap
    · rcases eq_or_ne m 0 with rfl | hm0
      · simp
      · rw [term_of_ne_zero hm0, hmin m (Finset.mem_range.mp hm) hm0, zero_div]
    rw [← LSeries, hz0, ← eq_neg_iff_add_eq_zero] at hsplit
    have h1 := ch11_lemma_1 hc (N := N + 1) (by omega) hz
    rw [show ∑' n, term h z (n + (N + 1)) = -term h z N by rw [hsplit, neg_neg], norm_neg,
      norm_term_eq, ite_eq_right hN0] at h1
    have hNz : 0 < (N : ℝ) ^ z.re := Real.rpow_pos_of_pos hNpos _
    rw [div_le_iff₀ hNz] at h1
    refine h1.trans (le_of_eq ?_)
    push_cast
    have hN1 : (0 : ℝ) < N + 1 := by linarith
    rw [Real.div_rpow hNpos.le hN1.le, Real.rpow_neg hN1.le]
    have : (N : ℝ) ^ z.re = (N : ℝ) ^ c * (N : ℝ) ^ (z.re - c) := by
      rw [← Real.rpow_add hNpos]; ring_nf
    rw [this]
    field_simp
    rfl
  have hlim : Tendsto (fun k => (N : ℝ) ^ c * K * ((N : ℝ) / (N + 1)) ^ ((s k).re - c)) atTop
      (𝓝 0) := by
    have hb1 : (N : ℝ) / (N + 1) < 1 := (div_lt_one (by linarith)).mpr (by linarith)
    simpa using ((tendsto_rpow_sub_atTop (c := c) (by positivity) hb1).comp hs).const_mul
      ((N : ℝ) ^ c * K)
  have hle : ‖h N‖ ≤ 0 := by
    refine ge_of_tendsto hlim ?_
    filter_upwards [h0, hs.eventually_ge_atTop c] with k hk1 hk2
    exact hbound (s k) hk2 hk1
  exact hNh (norm_le_zero_iff.mp hle)

/-- **Theorem 11.3** (uniqueness theorem): if `F(s) = ∑ f(n) n^{-s}` and `G(s) = ∑ g(n) n^{-s}`
both converge absolutely somewhere and `F(s_k) = G(s_k)` for a sequence with `σ_k → +∞`, then
`f(n) = g(n)` for every `n ≥ 1`. -/
@[kb "apostol1976" "Thm 11.3, p. 227"]
theorem apostol_thm_11_3 {f g : ℕ → ℂ} (hf : abscissaOfAbsConv f < ⊤)
    (hg : abscissaOfAbsConv g < ⊤) {s : ℕ → ℂ} (hs : Tendsto (fun k => (s k).re) atTop atTop)
    (hfg : ∀ k, LSeries f (s k) = LSeries g (s k)) : ∀ n, n ≠ 0 → f n = g n := by
  obtain ⟨c₁, hc₁⟩ := exists_LSeriesSummable_real hf
  obtain ⟨c₂, hc₂⟩ := exists_LSeriesSummable_real hg
  have hc : LSeriesSummable (f - g) (max c₁ c₂ : ℝ) :=
    (hc₁.of_re_le_re (by simp)).sub (hc₂.of_re_le_re (by simp))
  have h := eq_zero_of_LSeries_eq_zero_seq hc hs (by
    filter_upwards [hs.eventually_ge_atTop (max c₁ c₂)] with k hk
    rw [LSeries_sub (hc₁.of_re_le_re (by simpa using (le_max_left _ _).trans hk))
      (hc₂.of_re_le_re (by simpa using (le_max_right _ _).trans hk)), hfg k, sub_self])
  exact fun n hn => sub_eq_zero.mp (h n hn)

/-- **Theorem 11.4**: if `F(s) = ∑ f(n) n^{-s}` converges absolutely somewhere and `F(s) ≠ 0`
for some `s`, then there is a half-plane `σ > c > σ_a` in which `F` never vanishes. -/
@[kb "apostol1976" "Thm 11.4, p. 227"]
theorem apostol_thm_11_4 {f : ℕ → ℂ} (ha : abscissaOfAbsConv f < ⊤) {s : ℂ}
    (hs : LSeries f s ≠ 0) :
    ∃ c : ℝ, abscissaOfAbsConv f < c ∧ ∀ z : ℂ, c < z.re → LSeries f z ≠ 0 := by
  obtain ⟨c₀, hc₀⟩ := exists_LSeriesSummable_real ha
  obtain ⟨y, hay, hyt⟩ := exists_between ha
  lift y to ℝ using ⟨hyt.ne, ((OrderBot.bot_le _).trans_lt hay).ne'⟩
  by_contra hcon
  push Not at hcon
  -- zeros `s_k` with `Re s_k > max(y, k)`
  have hz : ∀ k : ℕ, ∃ z : ℂ, max y k < z.re ∧ LSeries f z = 0 := fun k =>
    hcon (max y k) (hay.trans_le (by exact_mod_cast le_max_left _ _))
  choose z hz1 hz2 using hz
  have hre : Tendsto (fun k => (z k).re) atTop atTop :=
    tendsto_atTop_mono (fun k => ((le_max_right _ _).trans (hz1 k).le))
      tendsto_natCast_atTop_atTop
  have h := eq_zero_of_LSeries_eq_zero_seq hc₀ hre (Eventually.of_forall hz2)
  exact hs (by rw [LSeries_congr (g := 0) (fun {n} hn => by simpa using h n hn) s, LSeries_zero,
    Pi.zero_apply])

end NTKB.Apostol
