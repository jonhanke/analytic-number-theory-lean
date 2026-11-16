# Analytic number theory in Lean 4

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24119525.svg)](https://doi.org/10.5281/zenodo.24119525)

A Lean 4 library (built on Mathlib) that formalizes two texts of analytic number theory item by item: Apostol's
*Introduction to Analytic Number Theory* and Davenport's *Multiplicative Number Theory* (2nd edition, revised by
H. L. Montgomery). The repository is analytic-number-theory-lean; its Lean modules are in the namespace `NTKB`, as in
its companion [elementary-number-theory-lean](https://github.com/jonhanke/elementary-number-theory-lean), some of whose
files it ships unchanged (see *Dependencies and the companion library*).

- **Book maps**: for each book, a table from every result (theorem, lemma, formula of the text) to the Lean
  declaration that formalizes it and its status: [docs/results/books/](docs/results/books/README.md).
- **Literature statements**: each result from a book is a Lean declaration tagged `@[kb "<source key>" "<locator>"]`,
  with the keys of [`references.bib`](references.bib).
- **What is proved**: every theorem is checked by the Lean kernel; the only `sorry`s in the repository are the
  deliberate ones in the `Challenge_<book>.lean` files, which state the headline results without proofs. The CI
  workflow builds the library, checks that the headline theorems depend only on the standard axioms `propext`,
  `Classical.choice` and `Quot.sound` ([scripts/check_axioms.lean](scripts/check_axioms.lean)), checks that every Lean
  name of the book maps exists ([scripts/check_map_names.lean](scripts/check_map_names.lean)), and runs
  `lake comparator` once per book to check the proved statements against the `Challenge_<book>.lean` files.
- **Cited results are named**: where the library assumes a result it does not prove, the result is a named Lean
  structure, never assumed silently; a theorem that uses it has it as a hypothesis and the book maps mark the row
  *conditional*. Since 0.2.0 `NTKB.Davenport.SiegelWalfiszHypothesis`, the input of Davenport's Chapters 28 and 29,
  is proved (`NTKB.Davenport.siegelWalfiszHypothesis`). The two classical facts about quadratic fields that the
  class number formulas of 0.3.0 assumed are proved since 0.4.0. One named input is open: an inversion theorem for
  Dirichlet series, used by one form of Apostol's Theorem 11.14 (see *Conditional theorems*). Results under the
  generalized Riemann hypothesis take it as a named hypothesis; conjectures are stated, never assumed as true.
- **Comparison**: [docs/results/comparison.md](docs/results/comparison.md) says, for each headline, what Mathlib,
  [Tau Ceti](https://github.com/TauCetiProject/TauCeti) and
  [PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd) already have and what this library
  adds. This library depends on Mathlib only.

## The books

| book | rows | proved | proved in part | conditional | in Mathlib | other | proved here, also elsewhere |
|---|---|---|---|---|---|---|---|
| [T. M. Apostol, *Introduction to Analytic Number Theory* (1976)](docs/results/books/apostol.md) | 322 | 173 | 0 | 1 | 148 | 0 | 80 |
| [H. Davenport, *Multiplicative Number Theory* (2nd ed., revised by H. L. Montgomery, 1980)](docs/results/books/davenport.md) | 432 | 243 | 32 | 0 | 80 | 77 | 59 |

*Proved*: proved with only the standard axioms and no unproved input. *Proved in part*: a part, a special case, a weaker form or one instance is proved (the map's Lean column names it). *Conditional*: proved from a named unproved input (here Apostol's Theorem 11.14, from `NTKB.Apostol.DirichletInverseSummableInput`; the two inputs of the Davenport class number rows of 0.3.0, `NTKB.Davenport.QuadraticFieldDiscriminants` and `NTKB.Davenport.QuadraticIdealCount`, are proved since 0.4.0, and `SiegelWalfiszHypothesis`, the input of Davenport's Chapters 28 and 29 in 0.1.0, since 0.2.0). *In Mathlib*: Mathlib (a dependency) has the result; the map names the Mathlib declaration. *Other*: in Tau Ceti or PrimeNumberTheoremAnd only (not dependencies), partly formalized elsewhere, or not formalized (see each map). *Proved here, also elsewhere*: rows proved (in whole or in part) here whose result, a part of it or a closely related statement is also in Mathlib, Tau Ceti or PrimeNumberTheoremAnd; each map names those declarations in its column *Also in*. Rows that are not results (definitions, remarks, history) are omitted from the maps.

## What's new in 0.4.0

- **Quadratic fields with no assumed input** (Davenport, Chapters 5, 6, 14 and 21): the two named inputs of the class
  number formulas of 0.3.0 are proved (the discriminants of the quadratic number fields are exactly the fundamental
  discriminants; the number of ideals of norm $`n`$ is $`\sum_{m\mid n}(d/m)`$), from the ring of integers and the
  decomposition law of $`\mathbb Q(\sqrt D)`$ (proved from Mathlib's `QuadraticAlgebra`). So the finite class number
  formulas, Jacobi's formula and Siegel's lower bounds hold unconditionally: 5 new headlines, the unconditional copies
  of the 5 conditional headlines of 0.3.0 (which are kept unchanged).
- **Binary quadratic forms and ideal classes** (Davenport, Chapter 6): Davenport's class number $`h(d)`$ of forms,
  the automorphs (roots of unity for $`d < 0`$, Pell's equation $`t^2 - du^2 = 4`$ for $`d > 0`$), the bijection
  between proper classes of forms and narrow ideal classes, $`h(d) = h_1(d)`$ or $`2h_1(d)`$ by the norm of the
  fundamental unit, $`h(d)\log\varepsilon = 2h_1(d)\log\varepsilon_1`$, the class number formulas for Davenport's
  $`h(d)`$ and $`\varepsilon`$, and the basic theorem $`\sum_f R_f(n) = \sum_{m \mid n}(d/m)`$ (with no condition
  $`(n, d) = 1`$). 2 new headlines.
- **Explicit formulas for real $`x`$ and the Riemann–von Mangoldt formula** (Davenport, Chapters 15 to 20): the
  formula $`N(T) = \frac{T}{2\pi}\log\frac{T}{2\pi} - \frac{T}{2\pi} + \frac78 + S(T) + O(1/T)`$ with the error at most
  $`3/T`$, $`S(T) = O(\log T)`$; von Mangoldt's explicit formula for $`\psi_0(x)`$ for every real $`x \ge 2`$ and the
  explicit formulas for $`\psi_0(x,\chi)`$ for real $`x`$; zero counts for imprimitive characters; the effective prime
  number theorem for progressions to small moduli $`q \le (\log x)^{1-\delta}`$ (unconditional). On the way: Stirling's
  formula with error $`O(1/|s|)`$ in sectors (ported from Tau Ceti with credit). 2 new headlines.
- **Theta functions** (Davenport, Chapters 8 and 9): Riemann's integral for the completed zeta function, valid for
  every $`s`$, and the theta transformation formulas with a primitive character of either parity.
- The 31 headlines of 0.1.0 to 0.3.0 are unchanged (40 in all). Refreshed Davenport map (243 proved, was 198; 32 in
  part, was 47; none conditional, was 9).

## Conditional theorems

Theorems proved from a named input that the library does not prove. No headline of 0.4.0 needs one.

- **Apostol's Theorem 11.14** (uniqueness of Dirichlet series) is proved for absolutely convergent series; under the
  book's hypothesis only from the named input `NTKB.Apostol.DirichletInverseSummableInput` (an inversion theorem the
  book uses without proof).
- **The five class number headlines of 0.3.0** (`classNumber_eq_sum_of_discr_neg`,
  `classNumber_mul_log_eq_sum_of_discr_pos`, `classNumber_eq_jacobi`, `classNumber_gt_of_discr_neg`,
  `classNumber_mul_log_gt_of_discr_pos`) still take the named inputs `NTKB.Davenport.QuadraticFieldDiscriminants` and
  `NTKB.Davenport.QuadraticIdealCount` as hypotheses, so that their statements are unchanged; both inputs are now
  theorems (`NTKB.Davenport.quadraticFieldDiscriminants`, `NTKB.Davenport.quadraticIdealCount`), and the headlines
  `..._unconditional` state the same results without them.
- **Under the generalized Riemann hypothesis** (stated as a hypothesis, `NTKB.GeneralizedRiemannHypothesis`, never
  assumed): $`\psi(N;q,a) = N/\varphi(q) + O(N^{1/2}\log^2 N)`$ for $`q \le N`$
  (`NTKB.Davenport.psiAP_sub_le_of_GRH`, Chapter 20).

## Known restrictions

- **Von Mangoldt's explicit formula** (headline `explicit_formula_vonMangoldt`) is proved for real $`x \ge 2`$;
  Davenport states it for $`x > 1`$, and $`1 < x < 2`$ is not done.
- **The basic theorem on binary forms** (headline `basic_theorem_binary_forms`) counts representations up to
  automorphs; Davenport's primary representations (the fundamental domain of his (10) and (11) for $`d > 0`$, row 6-6)
  and his lattice-point route to the class number formula (rows 6-8, 6-9, 6-11) are not formalized.
- **Field class number and form class number.** The class number headlines use the class number and the regulator
  of the field ($`\log\varepsilon`$ for a fundamental unit of either norm); the library also states them for
  Davenport's class number of forms with $`\varepsilon`$ of norm $`+1`$ (not headlines). For even characters the extra
  factor $`\log q`$ in the bound for a real zero (row 14-18) is not proved.
- **Davenport, Chapters 15 to 19:** a few rows are proved only in part (the wording by change of argument, the bounds
  in the left half-plane, rows 19-4, 19-8 and 19-11); the book map marks them.
- **Constants are not effective** where the proofs use Siegel's theorem: the constants of Siegel's bounds, of the
  Siegel–Walfisz theorem and of Vinogradov's asymptotic formula, and the threshold beyond which every odd integer is a
  sum of three primes, exist but are not computed.

## Highlights

Every result listed here is a headline theorem of a `Challenge_<book>.lean` file: it is checked by the Lean kernel
with only the standard axioms and depends on no unproved input, except the class number statements new in 0.3.0,
which are marked *conditional* and take the two named inputs above as hypotheses (proved since 0.4.0; their
unconditional copies are headlines). Headlines are only results that are in none of
Mathlib, Tau Ceti and PrimeNumberTheoremAnd ([comparison](docs/results/comparison.md)); related results of those
libraries are cited next to each headline. The statements have **not yet been reviewed by a human** (see
Provenance).

**Davenport, *Multiplicative Number Theory*** ([`Challenge_Davenport.lean`](Challenge_Davenport.lean))

- **The Hadamard product for $`\xi(s,\chi)`$:** for primitive $`\chi`$ modulo $`q > 1`$,
  $`\xi(s,\chi) = e^{A+Bs}\prod_\rho (1 - s/\rho)e^{s/\rho}`$ over the zeros with multiplicity
  (`dirichletXi_hadamard`, Chapter 12), from Hadamard's factorization theorem for entire functions of order at most
  one (Chapter 11, proved here). Related: PrimeNumberTheoremAnd has Hadamard's theorem and the product for
  $`\xi(s)`$, not the product for $`\xi(s,\chi)`$.
- **The zero-free region for $`L(s,\chi)`$** (Chapter 14): no zero with
  $`\sigma > 1 - c/\log(q\max(1,|t|))`$, $`c = 1/16200`$, for complex $`\chi`$; for real $`\chi \ne 1`$ at most one,
  real and simple (`LFunction_zero_free_complex`, `LFunction_zero_free_real`, `LFunction_zero_free_real_simple`).
  **Landau's theorem** on the real zeros of two real characters and **Page's theorem** (at most one exceptional real
  primitive character to moduli $`q \le z`$) (`landau_real_zeros`, `page_exceptional_character`). Related: Mathlib has $`L(s,\chi) \ne 0`$ on $`\sigma \ge 1`$; PrimeNumberTheoremAnd has a zero-free
  region for $`\zeta`$.
- **Counting zeros:** the Riemann–von Mangoldt formula
  $`N(T) = \frac{T}{2\pi}\log\frac{T}{2\pi} - \frac{T}{2\pi} + O(\log T)`$ and its analogue
  $`N(T,\chi) = \frac{T}{\pi}\log\frac{qT}{2\pi} - \frac{T}{\pi} + O(\log qT)`$ for primitive $`\chi`$
  (`zetaZeroCount_sub_le`, `LZeroCount_sub_le`, Chapters 15 and 16).
- **The explicit formula for $`\psi(x,\chi)`$:** for primitive $`\chi`$ modulo $`q > 1`$ and integers $`N \ge 3`$,
  $`\psi_0(N,\chi) = -\sum_\rho N^\rho/\rho - L'/L(0,\chi) + \sum_{m\ge1} N^{1-2m}/(2m-1)`$ for odd $`\chi`$, and the
  analogue with $`\log N + b(\chi)`$ for even $`\chi`$, the sum over the zeros taken symmetrically
  (`explicit_formula_psi0L_odd`, `explicit_formula_psi0L_even`, Chapter 19).
- **The prime number theorem for arithmetic progressions with the classical error term:** for every $`C > 0`$,
  $`\psi(N;q,a) = N/\varphi(q) + O(N e^{-c\sqrt{\log N}})`$ uniformly for $`\log q \le C\sqrt{\log N}`$, except for the
  multiples of at most one exceptional (Page) modulus (`psiAP_sub_le_page`, Chapter 20). Related:
  PrimeNumberTheoremAnd has $`\psi(x;q,a) \sim x/\varphi(q)`$ without error term and the classical error term for
  $`\psi(x)`$.
- **Siegel's theorem** (new in 0.2.0, Chapter 21): for every $`\varepsilon > 0`$,
  $`L(1,\chi) > C(\varepsilon)q^{-\varepsilon}`$ for real primitive $`\chi \ne 1`$ modulo $`q`$, and in the second form
  $`L(\sigma,\chi) \ne 0`$ for $`\sigma > 1 - C(\varepsilon)q^{-\varepsilon}`$ for every real $`\chi \ne 1`$ (`siegel`,
  `siegel_second_form`; Estermann's proof, constants not effective). Related: Tau Ceti has parts of a proof (the
  nonnegative coefficients of $`\zeta(s)L(s,\chi)L(s,\psi)L(s,\chi\psi)`$, ported here with credit), not the theorem.
- **The Siegel–Walfisz theorem** (new in 0.2.0, Chapter 22): for every $`B > 0`$,
  $`\psi(x;q,a) = x/\varphi(q) + O(x e^{-c\sqrt{\log x}})`$ and
  $`\pi(x;q,a) = \operatorname{li}(x)/\varphi(q) + O(x e^{-c\sqrt{\log x}})`$ uniformly for $`q \le (\log x)^B`$ and
  $`(a,q) = 1`$ (`siegel_walfisz`, `siegel_walfisz_primeCounting`).
- **The Pólya–Vinogradov inequality** $`|\sum_{M<n\le M+N}\chi(n)| \le 2\sqrt q\log q`$ for nonprincipal $`\chi`$
  (`polya_vinogradov`, Chapter 23).
- **The large sieve** $`\sum_r|S(\alpha_r)|^2 \le (N + 3/\delta)\sum|a_n|^2`$ for $`\delta`$-separated points and its
  form for primitive characters
  $`\sum_{q\le Q}\frac{q}{\varphi(q)}\sum^*_\chi|\sum c_n\chi(n)|^2 \le (N + 3Q^2)\sum|c_n|^2`$ (`large_sieve`,
  `large_sieve_characters`, Chapter 27).
- **Vinogradov's estimate** $`\sum_{n\le N}\Lambda(n)e(n\alpha) \ll (Nq^{-1/2} + N^{4/5} + N^{1/2}q^{1/2})(\log N)^4`$
  for $`|\alpha - a/q| \le q^{-2}`$, by Vaughan's identity (`vinogradov_prime_exponential_sum`, Chapters 24 and 25).
- **The Bombieri–Vinogradov theorem** (unconditional since 0.2.0, Chapter 28): for every $`A > 0`$,
  $`\sum_{q\le Q}\max_{y\le x}\max_{(a,q)=1}|\psi(y;q,a) - y/\varphi(q)| \ll x^{1/2}Q(\log x)^5`$ for
  $`x^{1/2}(\log x)^{-A} \le Q \le x^{1/2}`$ (`bombieri_vinogradov`).
- **The Barban–Davenport–Halberstam theorem** (unconditional since 0.2.0, Chapter 29, Gallagher's form):
  $`\sum_{q\le Q}\sum_{(a,q)=1}(\psi(x;q,a) - x/\varphi(q))^2 \ll xQ\log x`$ for $`x(\log x)^{-A} < Q \le x`$
  (`barban_davenport_halberstam`).
- **The finite class number formulas** (new in 0.3.0, Chapter 6, *conditional*): for an imaginary quadratic field of
  discriminant $`d`$ with $`w`$ roots of unity, $`h(d) = -\frac{w}{2|d|}\sum_{m=1}^{|d|} m\left(\frac dm\right)`$; for a
  real quadratic field with fundamental unit $`\varepsilon`$,
  $`h(d)\log\varepsilon = -\frac12\sum_{m=1}^{d-1}\left(\frac dm\right)\log\sin\frac{\pi m}d`$
  (`classNumber_eq_sum_of_discr_neg`, `classNumber_mul_log_eq_sum_of_discr_pos`); **Jacobi's formula**
  $`q\,h(-q) = -\sum_{m=1}^{q-1} m\left(\frac mq\right)`$ for primes $`q \equiv 3 \pmod 4`$, $`q > 3`$
  (`classNumber_eq_jacobi`). Related: Tau Ceti has $`h(d) = w\sqrt{|d|}L(1,\chi)/(2\pi)`$ for $`d < 0`$, not the
  finite formulas.
- **Siegel's lower bounds for the class number** (new in 0.3.0, Chapter 21, *conditional*): for every
  $`\varepsilon > 0`$, $`h(d) > C(\varepsilon)|d|^{1/2-\varepsilon}`$ for $`d < 0`$ and
  $`h(d)\log\varepsilon > C(\varepsilon)d^{1/2-\varepsilon}`$ for $`d > 0`$ (`classNumber_gt_of_discr_neg`,
  `classNumber_mul_log_gt_of_discr_pos`; constants not effective). Related: Tau Ceti has the upper bound
  $`h(d) \ll \sqrt{|d|}\log|d|`$.
- **Vinogradov's three primes theorem** (new in 0.3.0, Chapter 26): for every $`A > 0`$,
  $`r(N) = \sum_{k_1+k_2+k_3=N}\Lambda(k_1)\Lambda(k_2)\Lambda(k_3) = \tfrac12\mathfrak S(N)N^2 + O(N^2(\log N)^{-A})`$
  with the singular series $`\mathfrak S(N)`$ (`vinogradov_three_primes`), and every sufficiently large odd integer
  is a sum of three primes (`exists_three_primes_of_odd`). Related: PrimeNumberTheoremAnd states the odd Goldbach
  conjecture up to a given height and checks it up to 33.
- **The class number formulas and Siegel's bounds, unconditional** (new in 0.4.0, Chapters 6 and 21): the five
  statements above without the two named inputs (`classNumber_eq_sum_of_discr_neg_unconditional`,
  `classNumber_mul_log_eq_sum_of_discr_pos_unconditional`, `classNumber_eq_jacobi_unconditional`,
  `classNumber_gt_of_discr_neg_unconditional`, `classNumber_mul_log_gt_of_discr_pos_unconditional`). Related: Tau Ceti
  has the analytic class number formula for $`d < 0`$ and the upper bound, not these.
- **The basic theorem on binary quadratic forms** (new in 0.4.0, Chapter 6): for a fundamental discriminant
  $`d \ne 1`$ and a complete system $`S`$ of representatives of the proper classes of forms of discriminant $`d`$
  (positive definite if $`d < 0`$), $`\sum_{f\in S} R_f(n) = \sum_{m\mid n}\left(\frac dm\right)`$ for $`n \ge 1`$,
  $`R_f(n)`$ the number of representations up to automorphs (`basic_theorem_binary_forms`); for $`d < 0`$ the total
  number of representations is $`w\sum_{m\mid n}\left(\frac dm\right)`$ (`total_representations_of_discr_neg`).
  Related: Tau Ceti has the correspondence between forms and ideal classes, not these counts.
- **The Riemann–von Mangoldt formula** (new in 0.4.0, Chapter 15): for $`T > 0`$ not the ordinate of a zero,
  $`\left|N(T) - \left(\frac{T}{2\pi}\log\frac{T}{2\pi} - \frac{T}{2\pi} + \frac78 + S(T)\right)\right| \le 3/T`$
  (`riemann_von_mangoldt`). Related: PrimeNumberTheoremAnd states a Riemann–von Mangoldt bound with `sorry` and
  proves $`N(T) \le AT^{3/2}`$.
- **Von Mangoldt's explicit formula** (new in 0.4.0, Chapter 17): for real $`x \ge 2`$,
  $`\psi_0(x) = x - \sum_\rho x^\rho/\rho - \log 2\pi - \tfrac12\log(1 - x^{-2})`$, the sum over the zeros taken
  symmetrically (`explicit_formula_vonMangoldt`). Related: PrimeNumberTheoremAnd has smoothed explicit formulas that
  depend on statements with `sorry`.

**Apostol, *Introduction to Analytic Number Theory*** ([`Challenge_Apostol.lean`](Challenge_Apostol.lean))

Most of Apostol's book is in Mathlib; the library proves the rest of it (the book map says which is which). The
results that none of the three libraries has, and that are not already headlines of elementary-number-theory-lean:

- **Pólya's inequality** $`|\sum_{m\le x}\chi(m)| < \sqrt k\log k`$ for primitive $`\chi`$ modulo $`k > 1`$
  (`polya`, Theorem 8.21).
- **The bound** $`p(n) < e^{\pi\sqrt{2n/3}}`$ for the partition function (`card_partition_lt_exp`, Theorem 14.5).
- **The mean square of a Dirichlet series:** $`\frac1{2T}\int_{-T}^T|F(\sigma+it)|^2\,dt \to \sum|f(n)|^2n^{-2\sigma}`$
  where the series converges absolutely (`mean_square_LSeries`, Theorem 11.16).

**Main statements.** To check what is claimed, read two files: [`Challenge_Davenport.lean`](Challenge_Davenport.lean)
and [`Challenge_Apostol.lean`](Challenge_Apostol.lean) state the results above, with a docstring for each and a list
of the library definitions the statements use; every proof there is a deliberate `sorry`. The matching
`Solution_<book>.lean` files prove the same statements by appeal to the library theorems, and `lake comparator`,
configured per book by `comparator/<book>.json` (the books are listed in [`comparator.json`](comparator.json)),
checks that each proved statement is exactly the one in the challenge file and uses only the standard axioms. The
check is run one book at a time. [`formalization.yaml`](formalization.yaml) records the scope, sources, divergences
from the literature, provenance and review status in the
[formalization.yaml](https://github.com/mathlib-initiative/formalization.yaml) format.

**No longer conditional (since 0.2.0 and 0.4.0):** in 0.1.0 Bombieri's theorem (`NTKB.Davenport.bombieri`) and the
Barban–Davenport–Halberstam theorem (`NTKB.Davenport.barban_davenport_halberstam`) took
`NTKB.Davenport.SiegelWalfiszHypothesis` as a hypothesis, because Siegel's theorem was not proved; that input is now
proved (`NTKB.Davenport.siegelWalfiszHypothesis`), and the headlines `bombieri_vinogradov` and
`barban_davenport_halberstam` are the unconditional forms (`NTKB.Davenport.bombieri_unconditional`,
`NTKB.Davenport.barban_davenport_halberstam_unconditional`). In 0.3.0 the class number results took two named
inputs about quadratic fields; since 0.4.0 they are proved (see *Conditional theorems*).

**Also proved here, not headlines because another library has them:** Hadamard's factorization theorem for entire
functions of order at most one and the product for $`\xi(s)`$ (PrimeNumberTheoremAnd has both, for every finite
order); the zero-free region for $`\zeta`$ and the prime number theorem with the classical error term
(`NTKB.Davenport.riemannZeta_zero_free_region`, `NTKB.Davenport.psi_sub_self_le`; PrimeNumberTheoremAnd has both);
Dirichlet's theorem and the nonvanishing of $`L(1,\chi)`$ in the book forms (Mathlib); since 0.3.0, Apostol's
zero-free region 13.10 (`NTKB.Apostol.apostol_thm_13_10`; PrimeNumberTheoremAnd has the same bound, `ZetaInvBnd`),
Landau's theorem 11.13 (ported from Tau Ceti), Perron's formula 11.18 (Tau Ceti has a truncated form), and the
analytic class number formula $`h(d) = w\sqrt{|d|}L(1,\chi)/(2\pi)`$ (`NTKB.Davenport.classNumber_eq_of_discr_neg`;
Tau Ceti proves it); since 0.4.0, the correspondence between classes of forms and narrow ideal classes
(`NTKB.Davenport.formClassNumber_eq_card_narrowClass`; Tau Ceti has it) and the number of ideals of norm $`n`$ of a
quadratic field (`NTKB.Davenport.quadraticIdealCount`; Tau Ceti has it). Each book map credits, in its
column *Also in*, the results proved here that Mathlib, Tau Ceti or PrimeNumberTheoremAnd also prove.

## Dependencies and the companion library

The library depends on Mathlib only. It ships 300 modules; 104 of them are byte-identical to files
of [elementary-number-theory-lean v0.4.0](https://github.com/jonhanke/elementary-number-theory-lean/releases/tag/v0.4.0)
(the `@[kb]` attribute `NTKB.Attr`, the special values of Dirichlet $`L`$-functions
`NTKB.Elementary.SpecialValues.*`, which the Davenport files use, and part of `NTKB.Analytic.Apostol.*`), with the
same Lean and Mathlib versions. They are copied rather than taken from that package as a Lake dependency, because
the two packages share the module namespace `NTKB` and the elementary library `NTKB` claims every `NTKB.*` module:
with that dependency, Lake looks for this library's modules in the elementary package and the build fails. For the
same reason a project cannot depend on both packages at once. The library `AnalyticNumberTheory` lists the modules
in `lakefile.toml`, and `AnalyticNumberTheory.lean` imports every one of them.

## Layout

```
Challenge_<book>.lean   the headline statements of one book (proofs: deliberate sorry); <book> = Apostol, Davenport
Solution_<book>.lean    the same statements, proved from the library
comparator.json         the books, each with its lake comparator configuration comparator/<book>.json
formalization.yaml      scope, sources, divergences, provenance, review (formalization.yaml v0.4)
docs/results/books/     the book maps; docs/results/comparison.md: comparison with Mathlib, Tau Ceti,
                        PrimeNumberTheoremAnd
AnalyticNumberTheory.lean   imports every module of the library
NTKB/
  Analytic/Apostol/         Apostol, by topic (ArithmeticFunctions, Averages, Primes, Congruences, Characters,
                            Dirichlet, GaussSums, QuadraticResidues, PrimitiveRoots, DirichletSeries, Zeta, PNT,
                            Partitions)
  Analytic/Davenport/       Davenport: Ch1to6 (primes in progressions, Gauss sums, class number formula),
                            ClassNumber (Chapters 5, 6, 14, 21), Forms (Chapter 6: binary quadratic forms and
                            ideal classes, new in 0.4.0), Hadamard (Chapters 11-12), Zeros (Chapters 13-20),
                            Siegel (Chapters 21-22), Sieve (Chapters 23-29), ThreePrimes (Chapters 9, 26), Theta
                            (Chapters 8, 9)
  Elementary/QuadraticField/ quadratic number fields: ring of integers, decomposition law, ideal count (new in 0.4.0,
                            as in elementary-number-theory-lean)
  Elementary/SpecialValues/ special values of Dirichlet L-functions (as in elementary-number-theory-lean)
  Port/                     files ported from Tau Ceti (Apache 2.0), with credit in their headers
  Attr.lean                 the @[kb] citation attribute
references.bib          bibliography; the keys used by @[kb]
scripts/check_axioms.lean       prints the axioms of the headline theorems (run in CI)
scripts/check_map_names.lean    checks that the Lean names of the book maps exist (run in CI)
scripts/verify-comparator.sh    runs lake comparator for one book with the toolchain's kernels (run in CI)
.github/workflows/build.yml  the CI workflow (build, axioms, map names, one comparator check per book)
```

## Usage

```bash
lake exe cache get       # once: download prebuilt Mathlib
lake build               # build and check everything
lake env lean scripts/check_axioms.lean          # axioms of the headline theorems
./scripts/verify-comparator.sh Davenport         # Solution_Davenport against Challenge_Davenport
                                                 # (Linux; needs bubblewrap); likewise Apostol
```

Mathlib comes prebuilt from its cache; this library is built from source (300 modules, about 72,000 lines; no file
imports all of Mathlib, so only the Mathlib modules it needs are loaded). On 8 cores and 31 GB (2026-11-16), with
Mathlib's cache in place, `lake build` took about 18 minutes, with at most 4.4 GB of memory in use and a largest
single Lean process of 4.2 GB. Each `lake comparator` check (one book: build, export, and the Lean, NanoDa and
con-ron kernels) took about 5 minutes (Apostol) and 13 minutes (Davenport), with at most 5.0 GB in use
and a largest single process of 5.0 GB (`leanexport`).

## Provenance

NTKB was written by AI, with Claude Code (Anthropic): almost entirely by Claude Opus 5.5, with a share by Claude
Sonnet 5.5, in November 2026. Jonathan Hanke designed and directed it: he chose the books, the results, the
conventions and the proof routes. The files under `NTKB/Port/` contain code ported from Tau Ceti (by the Tau Ceti
contributors, Apache 2.0). The proofs are checked by the Lean kernel, and CI checks that the headline theorems use
only the standard axioms. The 40 headline statements of this release (31 of 0.1.0 to 0.3.0, unchanged, and 9 new) in the `Challenge_<book>.lean` files, and the
definitions they use, have **not yet been reviewed** by a human. `lake comparator` checks that each
`Solution_<book>.lean` proves exactly the statements of its `Challenge_<book>.lean`. The rest of the library (its
other definitions and intermediate results, and the book maps) has not been reviewed by a human; as with any
AI-written formalization, treat it as untrustworthy until checked against the literature. Corrections and reports of
mis-formalizations are very welcome.

## Releases

Releases are tagged with semantic versions; `main` continues to develop. The DOI [10.5281/zenodo.24119525](https://doi.org/10.5281/zenodo.24119525) always resolves to the latest release. To cite a specific version, use its release page or the "Cite this repository" button.

- **[v0.1.0](https://github.com/jonhanke/analytic-number-theory-lean/releases/tag/v0.1.0)** (Lean v4.36.0-rc2, Mathlib `1b1ccf4`), archived on Zenodo as [doi:10.5281/zenodo.24119526](https://doi.org/10.5281/zenodo.24119526): the first release: the book maps of Apostol and Davenport and
  the 18 headline statements above.
- **[v0.2.0](https://github.com/jonhanke/analytic-number-theory-lean/releases/tag/v0.2.0)** (Lean v4.36.0-rc2, Mathlib `1b1ccf4`), archived on Zenodo as [doi:10.5281/zenodo.24131623](https://doi.org/10.5281/zenodo.24131623): Davenport's Chapters 21 and 22: Siegel's theorem (both forms)
  and the Siegel–Walfisz theorem (for $`\psi`$ and $`\pi`$); with them the Bombieri–Vinogradov and
  Barban–Davenport–Halberstam theorems are unconditional (Chapters 28 and 29). 6 new headline statements
  (`Challenge_Davenport.lean`, now 21); the 18 headlines of 0.1.0 unchanged. Refreshed Davenport map
  (432 results: 178 proved, was 163; 50 proved in part, was 45; none conditional, was 3; 80 in Mathlib). The comparator check stays one per book (Apostol and Davenport, a matrix in CI); no file imports all of
  Mathlib.
- **[v0.3.0](https://github.com/jonhanke/analytic-number-theory-lean/releases/tag/v0.3.0)** (Lean v4.36.0-rc2, Mathlib `1b1ccf4`), archived on Zenodo as [doi:10.5281/zenodo.24257525](https://doi.org/10.5281/zenodo.24257525):
  the class number formulas (Davenport Chapters 5, 6, 14, 21: the finite formulas, Jacobi's formula, Siegel's lower
  bounds; conditional on two named inputs about quadratic fields) and Vinogradov's three primes theorem (Chapter 26,
  unconditional); Apostol's book complete (Theorems 4.17, 11.13, 11.18, 13.10; 11.14 in part). 7 new headline
  statements (`Challenge_Davenport.lean`, now 28); the 24 headlines of 0.1.0 and 0.2.0 unchanged. Refreshed maps
  (Davenport, 432 results: 198 proved, was 178; 47 proved in part, was 50; 9 conditional, was 0; 80 in Mathlib.
  Apostol, 322 results: 173 proved, was 168; 1 conditional; 148 in Mathlib; none open).
- **[v0.4.0](https://github.com/jonhanke/analytic-number-theory-lean/releases/tag/v0.4.0)** (Lean v4.36.0-rc2, Mathlib `1b1ccf4`), archived on Zenodo as [doi:10.5281/zenodo.24285927](https://doi.org/10.5281/zenodo.24285927):
  quadratic fields with no assumed input (the class number formulas, Jacobi's formula and Siegel's bounds
  unconditional), binary quadratic forms and ideal classes (Davenport Chapter 6, the basic theorem), the
  Riemann–von Mangoldt formula with $`7/8 + S(T)`$, explicit formulas for real $`x`$, the effective prime number
  theorem for small moduli, theta functions with characters. 9 new headline statements (`Challenge_Davenport.lean`,
  now 37); the 31 headlines of 0.1.0 to 0.3.0 unchanged. Refreshed Davenport map (432 results: 243 proved, was 198;
  32 proved in part, was 47; none conditional, was 9; 80 in Mathlib). See *What's new in 0.4.0*, *Conditional
  theorems* and *Known restrictions*.

**Not in this release:** Davenport's lattice-point route to the class number formula (Chapter 6), von Mangoldt's
formula for $`1 < x < 2`$ and the other open rows of the Davenport map; Iwaniec and Kowalski's *Analytic Number
Theory*.

## License

Apache License 2.0; see [LICENSE](LICENSE). Files ported from Tau Ceti are Apache 2.0, copyright the Tau Ceti
contributors.
