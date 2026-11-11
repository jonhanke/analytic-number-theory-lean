# Comparison with Mathlib, Tau Ceti and PrimeNumberTheoremAnd

For each headline of this release, what the three libraries closest to it already have, and what this library adds.
Libraries searched (source trees of 2026-11-11, for every headline of 0.1.0 and 0.2.0; 0.1.0 used the trees of
2026-11-07): Mathlib master `dc2a600c` (this library is built on Mathlib `1b1ccf4`, an earlier commit), Tau Ceti main
`1c6a1a4e`, PrimeNumberTheoremAnd `127b50e` (unchanged since 2026-10-19; including its
`PrimeNumberTheoremAnd/Mathlib/` subtree, which is not in Mathlib). A result is a headline only if none of the three
has it; the related results are cited. The searches were by name and by content (statements read); "not found" means
that no declaration of that content was found, not a proof of absence.

## Headlines

| headline (Lean, namespace `NTKB.Headlines`) | Mathlib | Tau Ceti | PrimeNumberTheoremAnd |
|---|---|---|---|
| `Davenport.dirichletXi_hadamard` (Chapter 12) | the completed `L`-function `DirichletCharacter.completedLFunction` and its functional equation; no Hadamard factorization | the entire completion of `L(s, χ)`, its zeros and finite order (`dirichletData_entireCompletion_eq_zero_iff`, `isFiniteOrder_iff_exists_bound`); for entire functions of finite order, Jensen's zero count (`OrderLE.isBigO_sum_divisor`), the genus-one elementary factor and the zero-free case `exp(affine)` (`OrderLE.exists_eq_cexp_affine_of_forall_ne_zero`); no product | Hadamard's theorem for every finite order (`hadamard_factorization_of_order`) and the product for `ξ(s)` (`riemannXi_hadamard_factorization`); not applied to `ξ(s, χ)` |
| `Davenport.LFunction_zero_free_complex`, `LFunction_zero_free_real`, `LFunction_zero_free_real_simple` (Chapter 14) | `L(s, χ) ≠ 0` for `σ ≥ 1` (`DirichletCharacter.LFunction_ne_zero_of_one_le_re`) | not found | a zero-free region for `ζ` (`ZeroInequality`); not for `L(s, χ)` |
| `Davenport.landau_real_zeros`, `page_exceptional_character` (Chapter 14) | not found | not found | not found |
| `Davenport.zetaZeroCount_sub_le` (Chapter 15) | not found | not found | `N(T) ≪ T^{3/2}` (`Backlund.zetaCounting_crude_majorant`); the Riemann–von Mangoldt formula appears only as a hypothesis (`riemannZeta.Riemann_vonMangoldt_bound`) |
| `Davenport.LZeroCount_sub_le` (Chapter 16) | not found | not found | not found |
| `Davenport.explicit_formula_psi0L_odd`, `explicit_formula_psi0L_even` (Chapter 19) | not found | not found | Perron and Laplace inversion tools for explicit-formula arguments; no explicit formula for `ψ(x, χ)` |
| `Davenport.psiAP_sub_le_page` (Chapter 20) | Dirichlet's theorem (`Nat.forall_exists_prime_gt_and_eq_mod`), the von Mangoldt function of a residue class | not found | `ψ(x; q, a) ~ x/φ(q)` for fixed `q`, no error term (`WeakPNT_AP`); the classical error term for `ψ(x)` (`StrongPNT`) |
| `Davenport.polya_vinogradov` (Chapter 23) and `Apostol.polya` (Theorem 8.21) | Gauss sums of primitive characters (`DirichletCharacter.norm_gaussSum_stdAddChar`) | partial sums of a nonprincipal character are bounded by the modulus (`DirichletCharacter.norm_sum_Icc_le_level`) | not found |
| `Davenport.large_sieve`, `large_sieve_characters` (Chapter 27) | Selberg's sieve (`SelbergSieve`), unrelated | not found | not found |
| `Davenport.vinogradov_prime_exponential_sum` (Chapter 25) | not found | not found | not found |
| `Davenport.siegel`, `siegel_second_form` (Chapter 21; new in 0.2.0) | not found (`Mathlib.NumberTheory.SiegelsLemma` is Siegel's lemma on integer solutions of linear systems, unrelated) | parts of a proof: nonnegative coefficients of `ζ(s) L(s, χ) L(s, ψ) L(s, χψ)` (`DirichletCharacter.zetaMulPairCoeffs_nonneg`, ported here with credit), its residue at `1`, `F(β) ≤ 0` when there is no zero in `(β, 1)` (`pair_nonpos_of_forall_ne_zero`), `‖L(1, χ)‖ ≤ 2 + log q` (`norm_LFunction_one_le_two_add_log`), a zero-free interval for finitely many moduli (`exists_pos_real_zero_gap`); not the theorem | not found |
| `Davenport.siegel_walfisz`, `siegel_walfisz_primeCounting` (Chapter 22; new in 0.2.0) | Dirichlet's theorem only | `π(x; m, a) ~ li(x)/φ(m)` for fixed `m`, no error term (`NumberField.Chebotarev.primeCount_primesCongruent_isEquivalent_logIntegral`) | `ψ(x; q, a) ~ x/φ(q)` for fixed `q`, no error term (`WeakPNT_AP`) |
| `Davenport.bombieri_vinogradov` (Chapter 28; new in 0.2.0) | not found | not found | not found (its blueprint mentions an external project proving Bombieri–Vinogradov modulo Siegel–Walfisz) |
| `Davenport.barban_davenport_halberstam` (Chapter 29; new in 0.2.0) | not found | not found | not found |
| `Apostol.card_partition_lt_exp` (Theorem 14.5) | partitions (`Nat.Partition`), Euler's generating function; no bound | not found | not found |
| `Apostol.mean_square_LSeries` (Theorem 11.16) | `LSeries`, its convergence; no mean value | absolute convergence from mean-square bounds on the coefficients (`TauCeti.LSeriesSummable_of_sum_norm_sq_bigO`), a different statement | not found |

## Proved here, not headlines

| result (Lean) | where else |
|---|---|
| Hadamard's factorization theorem for entire functions of order at most one (`NTKB.Davenport.hadamard_factorization_order_one`, Davenport Chapter 11) | PrimeNumberTheoremAnd, every finite order (`hadamard_factorization_of_order`) |
| the product for `ξ(s)` (`NTKB.Davenport.riemannXi_hadamard`, Chapter 12) | PrimeNumberTheoremAnd (`riemannXi_hadamard_factorization`) |
| the zero-free region for `ζ` (`NTKB.Davenport.riemannZeta_zero_free_region`, Chapter 13) | PrimeNumberTheoremAnd (`ZeroInequality`) |
| `ψ(x) = x + O(x e^{-c√log x})` (`NTKB.Davenport.psi_sub_self_le`, Chapter 18) | PrimeNumberTheoremAnd (`StrongPNT`) |
| Dirichlet's theorem, `L(1, χ) ≠ 0`, the functional equation of `L(s, χ)` (Davenport Chapters 1 to 9, Apostol Chapters 6, 7, 12) | Mathlib |
| the forms of Bombieri's theorem and of the Barban–Davenport–Halberstam theorem with the named input `NTKB.Davenport.SiegelWalfiszHypothesis` as a hypothesis (`NTKB.Davenport.bombieri`, `NTKB.Davenport.barban_davenport_halberstam`; the 0.1.0 forms) | not found anywhere; since 0.2.0 the input is proved (`NTKB.Davenport.siegelWalfiszHypothesis`) and the unconditional forms are headlines |
