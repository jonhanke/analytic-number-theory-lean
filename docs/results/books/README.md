# Book maps

> Item-by-item maps of books that are not openly licensed are kept privately until licensing is confirmed (2026-11-18). The Lean code and its citations to each book stay here; the counts below are from the full maps.

For each book of this release, a table from the results of the book to the Lean declarations and their status (generated from the coverage tables of the source repository and the kernel-level audit of its declarations).

| book | rows | proved | proved in part | conditional | in Mathlib | other | proved here, also elsewhere |
|---|---|---|---|---|---|---|---|
| T. M. Apostol, *Introduction to Analytic Number Theory* (1976) | 322 | 173 | 0 | 1 | 148 | 0 | 80 |
| H. Davenport, *Multiplicative Number Theory* (2nd ed., revised by H. L. Montgomery, 1980) | 432 | 297 | 12 | 0 | 80 | 43 | 70 |

*Proved*: proved with only the standard axioms and no unproved input. *Proved in part*: a part, a special case, a weaker form or one instance is proved (the map's Lean column names it). *Conditional*: proved from a named unproved input (here Apostol's Theorem 11.14, from `NTKB.Apostol.DirichletInverseSummableInput`; the two inputs of the Davenport class number rows of 0.3.0, `NTKB.Davenport.QuadraticFieldDiscriminants` and `NTKB.Davenport.QuadraticIdealCount`, are proved since 0.4.0, and `SiegelWalfiszHypothesis`, the input of Davenport's Chapters 28 and 29 in 0.1.0, since 0.2.0). *In Mathlib*: Mathlib (a dependency) has the result; the map names the Mathlib declaration. *Other*: in Tau Ceti or PrimeNumberTheoremAnd only (not dependencies), partly formalized elsewhere, or not formalized (see each map). *Proved here, also elsewhere*: rows proved (in whole or in part) here whose result, a part of it or a closely related statement is also in Mathlib, Tau Ceti or PrimeNumberTheoremAnd; each map names those declarations in its column *Also in*. Rows that are not results (definitions, remarks, history) are omitted from the maps.
