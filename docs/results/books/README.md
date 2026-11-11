# Book maps

For each book of this release, a table from the results of the book to the Lean declarations and their status (generated from the coverage tables of the source repository and the kernel-level audit of its declarations).

| book | rows | proved | proved in part | conditional | in Mathlib | other | proved here, also elsewhere |
|---|---|---|---|---|---|---|---|
| [T. M. Apostol, *Introduction to Analytic Number Theory* (1976)](apostol.md) | 322 | 168 | 2 | 0 | 148 | 4 | 81 |
| [H. Davenport, *Multiplicative Number Theory* (2nd ed., revised by H. L. Montgomery, 1980)](davenport.md) | 432 | 178 | 50 | 0 | 80 | 124 | 60 |

*Proved*: proved with only the standard axioms and no unproved input. *Proved in part*: a part, a special case, a weaker form or one instance is proved (the map's Lean column names it). *Conditional*: proved from a named unproved input (none in this release: `SiegelWalfiszHypothesis`, the input of Davenport's Chapters 28 and 29, is proved since 0.2.0). *In Mathlib*: Mathlib (a dependency) has the result; the map names the Mathlib declaration. *Other*: in Tau Ceti or PrimeNumberTheoremAnd only (not dependencies), partly formalized elsewhere, or not formalized (see each map). *Proved here, also elsewhere*: rows proved (in whole or in part) here whose result, a part of it or a closely related statement is also in Mathlib, Tau Ceti or PrimeNumberTheoremAnd; each map names those declarations in its column *Also in*. Rows that are not results (definitions, remarks, history) are omitted from the maps.
