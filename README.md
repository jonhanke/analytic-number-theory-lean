# Analytic number theory in Lean 4

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
  *conditional*. In this release one such input is open: `NTKB.Davenport.SiegelWalfiszHypothesis` (see below).
- **Comparison**: [docs/results/comparison.md](docs/results/comparison.md) says, for each headline, what Mathlib,
  [Tau Ceti](https://github.com/TauCetiProject/TauCeti) and
  [PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd) already have and what this library
  adds. This library depends on Mathlib only.

## The books

| book | rows | proved | proved in part | conditional | in Mathlib | other | proved here, also elsewhere |
|---|---|---|---|---|---|---|---|
| [T. M. Apostol, *Introduction to Analytic Number Theory* (1976)](docs/results/books/apostol.md) | 322 | 168 | 2 | 0 | 148 | 4 | 81 |
| [H. Davenport, *Multiplicative Number Theory* (2nd ed., revised by H. L. Montgomery, 1980)](docs/results/books/davenport.md) | 432 | 163 | 45 | 3 | 80 | 141 | 59 |

*Proved*: proved with only the standard axioms and no unproved input. *Proved in part*: a part, a special case, a weaker form or one instance is proved (the map's Lean column names it). *Conditional*: proved from a named unproved input (in this release only `SiegelWalfiszHypothesis`, the input of Davenport's Chapters 28 and 29). *In Mathlib*: Mathlib (a dependency) has the result; the map names the Mathlib declaration. *Other*: in Tau Ceti or PrimeNumberTheoremAnd only (not dependencies), partly formalized elsewhere, or not formalized (see each map). *Proved here, also elsewhere*: rows proved (in whole or in part) here whose result, a part of it or a closely related statement is also in Mathlib, Tau Ceti or PrimeNumberTheoremAnd; each map names those declarations in its column *Also in*. Rows that are not results (definitions, remarks, history) are omitted from the maps.

## Highlights

Every result listed here is a headline theorem of a `Challenge_<book>.lean` file: it is checked by the Lean kernel
with only the standard axioms and depends on no unproved input. Headlines are only results that are in none of
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
  primitive character to moduli $`q \le z`$) (`landau_real_zeros`, `page_exceptional_character`). Siegel's theorem
  is not proved. Related: Mathlib has $`L(s,\chi) \ne 0`$ on $`\sigma \ge 1`$; PrimeNumberTheoremAnd has a zero-free
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
- **The Pólya–Vinogradov inequality** $`|\sum_{M<n\le M+N}\chi(n)| \le 2\sqrt q\log q`$ for nonprincipal $`\chi`$
  (`polya_vinogradov`, Chapter 23).
- **The large sieve** $`\sum_r|S(\alpha_r)|^2 \le (N + 3/\delta)\sum|a_n|^2`$ for $`\delta`$-separated points and its
  form for primitive characters
  $`\sum_{q\le Q}\frac{q}{\varphi(q)}\sum^*_\chi|\sum c_n\chi(n)|^2 \le (N + 3Q^2)\sum|c_n|^2`$ (`large_sieve`,
  `large_sieve_characters`, Chapter 27).
- **Vinogradov's estimate** $`\sum_{n\le N}\Lambda(n)e(n\alpha) \ll (Nq^{-1/2} + N^{4/5} + N^{1/2}q^{1/2})(\log N)^4`$
  for $`|\alpha - a/q| \le q^{-2}`$, by Vaughan's identity (`vinogradov_prime_exponential_sum`, Chapters 24 and 25).

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

**Proved, but conditional on a named input (not headlines):** Bombieri's theorem (the Bombieri–Vinogradov theorem,
Davenport Chapter 28, `NTKB.Davenport.bombieri`) and the Barban–Davenport–Halberstam theorem (Chapter 29,
`NTKB.Davenport.barban_davenport_halberstam`) take `NTKB.Davenport.SiegelWalfiszHypothesis` as a hypothesis: the
prime number theorem with error $`x e^{-c\sqrt{\log x}}`$ (proved here, `NTKB.Davenport.psi_sub_self_le`) and the
Siegel–Walfisz bound for $`\psi(x,\chi)`$, $`q \le (\log x)^B`$, which rests on Siegel's theorem (Chapter 21, not
proved). **Proved under the generalized Riemann hypothesis** (stated as a hypothesis, `NTKB.GeneralizedRiemannHypothesis`):
$`\psi(N;q,a) = N/\varphi(q) + O(N^{1/2}\log^2 N)`$ for $`q \le N`$ (`NTKB.Davenport.psiAP_sub_le_of_GRH`, Chapter 20).

**Also proved here, not headlines because another library has them:** Hadamard's factorization theorem for entire
functions of order at most one and the product for $`\xi(s)`$ (PrimeNumberTheoremAnd has both, for every finite
order); the zero-free region for $`\zeta`$ and the prime number theorem with the classical error term
(`NTKB.Davenport.riemannZeta_zero_free_region`, `NTKB.Davenport.psi_sub_self_le`; PrimeNumberTheoremAnd has both);
Dirichlet's theorem and the nonvanishing of $`L(1,\chi)`$ in the book forms (Mathlib). Each book map credits, in its
column *Also in*, the results proved here that Mathlib, Tau Ceti or PrimeNumberTheoremAnd also prove.

## Dependencies and the companion library

The library depends on Mathlib only. It ships 240 modules; 35 of them are byte-identical to files
of [elementary-number-theory-lean v0.1.0](https://github.com/jonhanke/elementary-number-theory-lean/releases/tag/v0.1.0)
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
docs/results/books/     the book maps; docs/results/comparison.md: comparison with Mathlib, Tau Ceti, PNT+
AnalyticNumberTheory.lean   imports every module of the library
NTKB/
  Analytic/Apostol/         Apostol, by topic (ArithmeticFunctions, Averages, Primes, Congruences, Characters,
                            Dirichlet, GaussSums, QuadraticResidues, PrimitiveRoots, DirichletSeries, Zeta, PNT,
                            Partitions)
  Analytic/Davenport/       Davenport: Ch1to6 (primes in progressions, Gauss sums, class number formula),
                            Hadamard (Chapters 11-12), Zeros (Chapters 13-20), Sieve (Chapters 23-29)
  Elementary/SpecialValues/ special values of Dirichlet L-functions (as in elementary-number-theory-lean v0.1.0)
  Port/                     files ported from Tau Ceti (Apache 2.0), with credit in their headers
  Attr.lean                 the @[kb] citation attribute
references.bib          bibliography; the keys used by @[kb]
scripts/check_axioms.lean       prints the axioms of the headline theorems (run in CI)
scripts/check_map_names.lean    checks that the Lean names of the book maps exist (run in CI)
scripts/verify-comparator.sh    runs lake comparator for one book with the toolchain's kernels (run in CI)
ci/build.yml            the CI workflow (to be installed as .github/workflows/build.yml)
```

## Usage

```bash
lake exe cache get       # once: download prebuilt Mathlib
lake build               # build and check everything
lake env lean scripts/check_axioms.lean          # axioms of the headline theorems
./scripts/verify-comparator.sh Davenport         # Solution_Davenport against Challenge_Davenport
                                                 # (Linux; needs bubblewrap); likewise Apostol
```

Mathlib comes prebuilt from its cache; this library is built from source (240 modules, about 55,000 lines; no file
imports all of Mathlib, so only the Mathlib modules it needs are loaded). On 8 cores and 31 GB (2026-11-10), with
Mathlib's cache in place, `lake build` took about 17 minutes, with at most 4.2 GB of memory in use and a largest
single Lean process of 4.6 GB. Each `lake comparator` check (one book: build, export, and the Lean, NanoDa and
con-ron kernels) took about 5 minutes (Apostol) and 8 minutes (Davenport), with at most 4.1 GB in use and a largest
single process of 4.7 GB (`leanexport`).

## Provenance

NTKB was written by AI, with Claude Code (Anthropic): almost entirely by Claude Opus 5.5, with a share by Claude
Sonnet 5.5, in November 2026. Jonathan Hanke designed and directed it: he chose the books, the results, the
conventions and the proof routes. The files under `NTKB/Port/` contain code ported from Tau Ceti (by the Tau Ceti
contributors, Apache 2.0). The proofs are checked by the Lean kernel, and CI checks that the headline theorems use
only the standard axioms. The 18 headline statements of this release in the `Challenge_<book>.lean` files, and the
definitions they use, have **not yet been reviewed** by a human. `lake comparator` checks that each
`Solution_<book>.lean` proves exactly the statements of its `Challenge_<book>.lean`. The rest of the library (its
other definitions and intermediate results, and the book maps) has not been reviewed by a human; as with any
AI-written formalization, treat it as untrustworthy until checked against the literature. Corrections and reports of
mis-formalizations are very welcome.

## Releases

Releases are tagged with semantic versions; `main` continues to develop.

- **v0.1.0** (Lean v4.36.0-rc2, Mathlib `1b1ccf4`): the first release: the book maps of Apostol and Davenport and
  the 18 headline statements above.

**Not in this release:** Siegel's theorem (Davenport, Chapter 21) and what rests on it (Chapter 22, and
unconditional forms of Chapters 28 and 29); the ternary Goldbach problem (Chapter 26); Iwaniec and Kowalski's
*Analytic Number Theory*.

## License

Apache License 2.0; see [LICENSE](LICENSE). Files ported from Tau Ceti are Apache 2.0, copyright the Tau Ceti
contributors.
