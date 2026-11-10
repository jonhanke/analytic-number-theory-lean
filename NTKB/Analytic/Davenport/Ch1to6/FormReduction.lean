/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Group.Int.Even
import Mathlib.Data.Int.Interval
import Mathlib.Order.Interval.Finset.Box
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import NTKB.Attr

/-!
# Davenport, Chapter 6: Lagrange's reduction of binary quadratic forms

(§6, pp. 43–44.) A binary quadratic form `ax² + bxy + cy²` is recorded by its coefficients
`(a, b, c)`; its discriminant is `b² - 4ac`. A unimodular substitution `x ↦ αx + βy`,
`y ↦ γx + δy` (`αδ - βγ = 1`) gives an equivalent form (`NTKB.Davenport.FormEquiv`), with the same
discriminant.

* Lagrange: if the discriminant `d` is not a square, every form is equivalent to one with
  `|b| ≤ |a| ≤ |c|` (`NTKB.Davenport.exists_formEquiv_reduced`);
* such a form has `3a² ≤ |d|`, so there are finitely many of them, and the number of classes of
  forms of discriminant `d` is finite (`NTKB.Davenport.exists_finset_formEquiv`).

This is a self-contained elementary treatment (Tau Ceti has a general theory of binary quadratic
forms with the `SL(2, ℤ)` action; it is not copied here).
-/

namespace NTKB.Davenport

/-- The discriminant `b² - 4ac` of the form `(a, b, c)`. -/
def formDisc (f : ℤ × ℤ × ℤ) : ℤ := f.2.1 ^ 2 - 4 * f.1 * f.2.2

/-- The form `a(αx + βy)² + b(αx + βy)(γx + δy) + c(γx + δy)²`. -/
def formSubst (f : ℤ × ℤ × ℤ) (α β γ δ : ℤ) : ℤ × ℤ × ℤ :=
  (f.1 * α ^ 2 + f.2.1 * α * γ + f.2.2 * γ ^ 2,
   2 * f.1 * α * β + f.2.1 * (α * δ + β * γ) + 2 * f.2.2 * γ * δ,
   f.1 * β ^ 2 + f.2.1 * β * δ + f.2.2 * δ ^ 2)

/-- `g` is obtained from `f` by a unimodular substitution (Davenport's equivalence). -/
def FormEquiv (f g : ℤ × ℤ × ℤ) : Prop :=
  ∃ α β γ δ : ℤ, α * δ - β * γ = 1 ∧ g = formSubst f α β γ δ

theorem formDisc_formSubst (f : ℤ × ℤ × ℤ) (α β γ δ : ℤ) :
    formDisc (formSubst f α β γ δ) = (α * δ - β * γ) ^ 2 * formDisc f := by
  simp only [formDisc, formSubst]; ring

theorem formSubst_formSubst (f : ℤ × ℤ × ℤ) (α β γ δ α' β' γ' δ' : ℤ) :
    formSubst (formSubst f α β γ δ) α' β' γ' δ' =
      formSubst f (α * α' + β * γ') (α * β' + β * δ') (γ * α' + δ * γ') (γ * β' + δ * δ') := by
  simp only [formSubst, Prod.mk.injEq]; refine ⟨by ring, by ring, by ring⟩

theorem FormEquiv.refl (f : ℤ × ℤ × ℤ) : FormEquiv f f :=
  ⟨1, 0, 0, 1, by ring, by simp only [formSubst]; ext <;> simp⟩

theorem FormEquiv.trans {f g h : ℤ × ℤ × ℤ} (hfg : FormEquiv f g) (hgh : FormEquiv g h) :
    FormEquiv f h := by
  obtain ⟨α, β, γ, δ, h1, rfl⟩ := hfg
  obtain ⟨α', β', γ', δ', h2, rfl⟩ := hgh
  refine ⟨_, _, _, _, ?_, formSubst_formSubst f α β γ δ α' β' γ' δ'⟩
  linear_combination (α' * δ' - β' * γ') * h1 + h2

theorem FormEquiv.formDisc_eq {f g : ℤ × ℤ × ℤ} (h : FormEquiv f g) : formDisc g = formDisc f := by
  obtain ⟨α, β, γ, δ, h1, rfl⟩ := h
  rw [formDisc_formSubst, h1, one_pow, one_mul]

/-- `a ≠ 0` and `c ≠ 0` when the discriminant is not a square. -/
theorem fst_ne_zero_of_not_isSquare {f : ℤ × ℤ × ℤ} (hd : ¬ IsSquare (formDisc f)) : f.1 ≠ 0 := by
  intro h; apply hd; exact ⟨f.2.1, by simp [formDisc, h, sq]⟩

theorem snd_snd_ne_zero_of_not_isSquare {f : ℤ × ℤ × ℤ} (hd : ¬ IsSquare (formDisc f)) :
    f.2.2 ≠ 0 := by
  intro h; apply hd; exact ⟨f.2.1, by simp [formDisc, h, sq]⟩

/-- For `a ≠ 0` there is `k` with `|b + 2ak| ≤ |a|`. -/
theorem exists_abs_add_two_mul_le (a b : ℤ) (ha : a ≠ 0) : ∃ k : ℤ, |b + 2 * a * k| ≤ |a| := by
  have h2a : 2 * a ≠ 0 := by omega
  set r := b % (2 * a)
  set q := b / (2 * a)
  have hr0 : 0 ≤ r := Int.emod_nonneg _ h2a
  have hr1 : r < |2 * a| := by
    have := Int.emod_lt b h2a; rwa [Int.natCast_natAbs] at this
  have hb : r + 2 * a * q = b := by simp only [r, q]; rw [Int.emod_def]; ring
  rw [abs_mul, abs_two] at hr1
  by_cases hle : r ≤ |a|
  · refine ⟨-q, ?_⟩
    rw [show b + 2 * a * -q = r by linarith, abs_of_nonneg hr0]; exact hle
  · rcases lt_or_gt_of_ne ha with hneg | hpos
    · refine ⟨-q + 1, ?_⟩
      rw [abs_of_neg hneg] at hle hr1 ⊢
      rw [show b + 2 * a * (-q + 1) = r + 2 * a by linarith, abs_le]
      constructor <;> linarith
    · refine ⟨-q - 1, ?_⟩
      rw [abs_of_pos hpos] at hle hr1 ⊢
      rw [show b + 2 * a * (-q - 1) = r - 2 * a by linarith, abs_le]
      constructor <;> linarith

/-- **Davenport §6, p. 43 (Lagrange).** If the discriminant of `f` is not a square, `f` is
equivalent to a form `(a, b, c)` with `|b| ≤ |a| ≤ |c|`. -/
@[kb "davenport1980" "Ch 6, p. 43"]
theorem exists_formEquiv_reduced (f : ℤ × ℤ × ℤ) (hd : ¬ IsSquare (formDisc f)) :
    ∃ g, FormEquiv f g ∧ |g.2.1| ≤ |g.1| ∧ |g.1| ≤ |g.2.2| := by
  induction hn : f.1.natAbs using Nat.strong_induction_on generalizing f with
  | _ n ih =>
  have ha := fst_ne_zero_of_not_isSquare hd
  obtain ⟨k, hk⟩ := exists_abs_add_two_mul_le f.1 f.2.1 ha
  -- `x ↦ x + ky`
  set f' := formSubst f 1 k 0 1 with hf'
  have hf'e : FormEquiv f f' := ⟨1, k, 0, 1, by ring, rfl⟩
  have hd' : ¬ IsSquare (formDisc f') := by rwa [hf'e.formDisc_eq]
  have ha' : f'.1 = f.1 := by simp [hf', formSubst]
  have hb' : |f'.2.1| ≤ |f'.1| := by
    rw [ha']; simp only [hf', formSubst]
    convert hk using 2; ring
  by_cases hac : |f'.1| ≤ |f'.2.2|
  · exact ⟨f', hf'e, hb', hac⟩
  · -- swap `a` and `c`: `x ↦ -y`, `y ↦ x`
    set f'' := formSubst f' 0 (-1) 1 0 with hf''
    have hf''e : FormEquiv f' f'' := ⟨0, -1, 1, 0, by ring, rfl⟩
    have hd'' : ¬ IsSquare (formDisc f'') := by rwa [hf''e.formDisc_eq]
    have ha'' : f''.1 = f'.2.2 := by simp [hf'', formSubst]
    have hlt : f''.1.natAbs < n := by
      rw [← hn, ha'', ← ha']
      have h := not_le.mp hac
      have : ((f'.2.2.natAbs : ℕ) : ℤ) < ((f'.1.natAbs : ℕ) : ℤ) := by
        rw [Int.natCast_natAbs, Int.natCast_natAbs]; exact h
      exact_mod_cast this
    obtain ⟨g, hg, hg1, hg2⟩ := ih _ hlt f'' hd'' rfl
    exact ⟨g, (hf'e.trans hf''e).trans hg, hg1, hg2⟩

/-- A reduced form `|b| ≤ |a| ≤ |c|` of nonsquare discriminant `d` has `3a² ≤ |d|`. -/
theorem three_mul_sq_le_of_reduced {g : ℤ × ℤ × ℤ} (hd : ¬ IsSquare (formDisc g))
    (h1 : |g.2.1| ≤ |g.1|) (h2 : |g.1| ≤ |g.2.2|) : 3 * g.1 ^ 2 ≤ |formDisc g| := by
  obtain ⟨a, b, c⟩ := g
  simp only at h1 h2 ⊢
  have hb2 : b ^ 2 ≤ a ^ 2 := sq_le_sq.mpr h1
  have ha2 : a ^ 2 ≤ |a * c| := by
    rw [abs_mul, sq, ← abs_mul_abs_self a]
    exact mul_le_mul_of_nonneg_left h2 (abs_nonneg a)
  simp only [formDisc]
  rcases le_or_gt 0 (a * c) with hac | hac
  · rw [abs_of_nonneg hac] at ha2
    rw [abs_sub_comm]
    calc 3 * a ^ 2 ≤ 4 * a * c - b ^ 2 := by nlinarith
      _ ≤ |4 * a * c - b ^ 2| := le_abs_self _
  · rw [abs_of_neg hac] at ha2
    calc 3 * a ^ 2 ≤ b ^ 2 - 4 * a * c := by nlinarith [sq_nonneg b]
      _ ≤ |b ^ 2 - 4 * a * c| := le_abs_self _

/-- **Davenport §6, pp. 43–44.** For a nonsquare `d`, there is a finite set of forms of
discriminant `d` such that every form of discriminant `d` is equivalent to one of them: the number
of classes is finite. -/
@[kb "davenport1980" "Ch 6, pp. 43-44"]
theorem exists_finset_formEquiv {d : ℤ} (hd : ¬ IsSquare d) :
    ∃ S : Finset (ℤ × ℤ × ℤ), (∀ g ∈ S, formDisc g = d) ∧
      ∀ f, formDisc f = d → ∃ g ∈ S, FormEquiv f g := by
  classical
  set M := |d|
  set B : Finset (ℤ × ℤ × ℤ) := Finset.Icc (-M) M ×ˢ Finset.Icc (-M) M ×ˢ Finset.Icc (-(2 * M)) (2 * M)
  refine ⟨B.filter (fun g ↦ formDisc g = d), fun g hg ↦ (Finset.mem_filter.mp hg).2, ?_⟩
  intro f hf
  obtain ⟨g, hfg, h1, h2⟩ := exists_formEquiv_reduced f (by rwa [hf])
  have hgd : formDisc g = d := by rw [hfg.formDisc_eq, hf]
  refine ⟨g, Finset.mem_filter.mpr ⟨?_, hgd⟩, hfg⟩
  have h3 := three_mul_sq_le_of_reduced (by rwa [hgd]) h1 h2
  rw [hgd] at h3
  have ha0 := fst_ne_zero_of_not_isSquare (f := g) (by rwa [hgd])
  obtain ⟨a, b, c⟩ := g
  simp only at h1 h2 h3 ha0 hgd ⊢
  have haM : |a| ≤ M := by
    have h1a := Int.one_le_abs ha0
    have : |a| ≤ a ^ 2 := by nlinarith [sq_abs a]
    linarith
  have hbM : |b| ≤ M := h1.trans haM
  have hcM : |c| ≤ 2 * M := by
    have h4 : 4 * a * c = b ^ 2 - d := by simp only [formDisc] at hgd; linarith
    have hb2 : b ^ 2 ≤ M := by
      have : b ^ 2 ≤ a ^ 2 := sq_le_sq.mpr h1
      have h3' : 3 * a ^ 2 ≤ M := h3
      nlinarith [sq_nonneg a]
    have hca : |c| ≤ |4 * a * c| := by
      rw [abs_mul, abs_mul]
      have : (1 : ℤ) ≤ |4| * |a| := by
        have := Int.one_le_abs ha0; norm_num; linarith
      nlinarith [abs_nonneg c]
    rw [h4] at hca
    calc |c| ≤ |b ^ 2 - d| := hca
      _ ≤ |b ^ 2| + |d| := abs_sub _ _
      _ ≤ 2 * M := by rw [abs_of_nonneg (sq_nonneg b)]; linarith
  simp only [B, Finset.mem_product, Finset.mem_Icc]
  exact ⟨abs_le.mp haM, abs_le.mp hbM, abs_le.mp hcM⟩

/-- **Davenport §6, p. 55, (E).** A solution of `t² - d u² = 4` (`d = b² - 4ac`) gives an
automorph of the form `(a, b, c)`: the substitution with `α = (t - bu)/2`, `β = -cu`, `γ = au`,
`δ = (t + bu)/2` is unimodular and leaves the form unchanged. -/
@[kb "davenport1980" "Ch 6, p. 55, (E)"]
theorem formSubst_automorph (f : ℤ × ℤ × ℤ) {t u α δ : ℤ}
    (htu : t ^ 2 - formDisc f * u ^ 2 = 4) (hα : 2 * α = t - f.2.1 * u)
    (hδ : 2 * δ = t + f.2.1 * u) :
    α * δ - (-(f.2.2 * u)) * (f.1 * u) = 1 ∧ formSubst f α (-(f.2.2 * u)) (f.1 * u) δ = f := by
  obtain ⟨a, b, c⟩ := f
  simp only [formDisc] at htu hα hδ
  have hαδ : α * δ - -(c * u) * (a * u) = 1 := by
    have : 4 * (α * δ - -(c * u) * (a * u)) = 4 := by
      have e : 4 * (α * δ) = (2 * α) * (2 * δ) := by ring
      rw [mul_sub, e, hα, hδ]; linear_combination htu
    linarith
  refine ⟨hαδ, ?_⟩
  simp only [formSubst, Prod.mk.injEq]
  refine ⟨?_, ?_, ?_⟩
  · have : 4 * (a * α ^ 2 + b * α * (a * u) + c * (a * u) ^ 2) = 4 * a := by
      have e : 4 * (a * α ^ 2 + b * α * (a * u) + c * (a * u) ^ 2) =
          a * (2 * α) ^ 2 + 2 * b * (2 * α) * (a * u) + 4 * c * (a * u) ^ 2 := by ring
      rw [e, hα]; linear_combination a * htu
    linarith
  · have : 2 * (2 * a * α * -(c * u) + b * (α * δ + -(c * u) * (a * u)) + 2 * c * (a * u) * δ) =
        2 * b := by
      have e : 2 * (2 * a * α * -(c * u) + b * (α * δ + -(c * u) * (a * u)) + 2 * c * (a * u) * δ) =
          -2 * a * c * u * (2 * α) + b * (2 * (α * δ - -(c * u) * (a * u)) - 4 * a * c * u ^ 2) +
            2 * a * c * u * (2 * δ) := by ring
      rw [e, hα, hδ, hαδ]; ring
    linarith
  · have : 4 * (a * (-(c * u)) ^ 2 + b * -(c * u) * δ + c * δ ^ 2) = 4 * c := by
      have e : 4 * (a * (-(c * u)) ^ 2 + b * -(c * u) * δ + c * δ ^ 2) =
          4 * a * c ^ 2 * u ^ 2 - 2 * b * c * u * (2 * δ) + c * (2 * δ) ^ 2 := by ring
      rw [e, hδ]; linear_combination c * htu
    linarith

end NTKB.Davenport
